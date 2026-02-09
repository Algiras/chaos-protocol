// ============================================================================
// CHAOS Treasury Vault Validator
// Language: Aiken v1.1+
// Network: Cardano (Preprod → Mainnet)
//
// Manages ADA, DJED, and LP positions with:
// - Deposit/withdrawal validation
// - Rebalancing with oracle consensus
// - Governance parameter updates
// - Circuit breaker emergency controls
// - Allocation bounds enforcement
// ============================================================================

use aiken/collection/list
use aiken/interval.{Finite}
use cardano/address.{Script}
use cardano/assets
use cardano/transaction.{InlineDatum, OutputReference, Transaction,
  find_script_outputs, resolve_input}

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// DEX identifier for LP positions
pub type DEX {
  Minswap
  SundaeSwap
  WingRiders
}

/// LP position details
pub type LPPosition {
  dex: DEX,
  lp_token_policy: ByteArray,
  lp_token_name: ByteArray,
  lp_tokens: Int,
  value_lovelace: Int,
}

/// Historical price point (price in micro-USD: 1 USD = 1_000_000)
pub type PricePoint {
  timestamp: Int,
  price_usd: Int,
}

/// Treasury state stored in the UTXO
pub type TreasuryDatum {
  // Asset holdings (in smallest units)
  ada_lovelace: Int,
  djed_amount: Int,
  lp_positions: List<LPPosition>,

  // Strategy parameters (basis points: 10000 = 100%)
  target_ada_bps: Int,
  target_djed_bps: Int,
  target_lp_bps: Int,
  rebalance_threshold_bps: Int,

  // Moving average data
  ada_price_history: List<PricePoint>,
  ma_window: Int,

  // Authorization
  authorized_operators: List<ByteArray>,
  governance_pkh: ByteArray,

  // Safety bounds (basis points)
  min_ada_bps: Int,
  max_ada_bps: Int,
  circuit_breaker_active: Bool,
  last_rebalance_time: Int,

  // Metadata
  inception_time: Int,
  total_deposits: Int,
  total_withdrawals: Int,
  rebalance_count: Int,
}

/// Reason for rebalancing
pub type RebalanceReason {
  AllocationDrift { ada_drift_bps: Int }
  PriceBelowMA { discount_bps: Int }
  PriceAboveMA { premium_bps: Int }
  ManualRebalance
}

/// Trade action
pub type TradeAction {
  Buy
  Sell
}

/// Individual trade in a rebalance
pub type Trade {
  action: TradeAction,
  asset_in_policy: ByteArray,
  asset_in_name: ByteArray,
  amount_in: Int,
  asset_out_policy: ByteArray,
  asset_out_name: ByteArray,
  amount_out: Int,
  dex: DEX,
  max_slippage_bps: Int,
}

/// Target allocations after rebalancing
pub type Allocations {
  ada_bps: Int,
  djed_bps: Int,
  lp_bps: Int,
}

/// Oracle price source
pub type OracleSource {
  name: ByteArray,
  price_usd: Int,
  timestamp: Int,
}

/// Oracle prices for validation
pub type OraclePrices {
  ada_price_usd: Int,
  djed_price_usd: Int,
  sources: List<OracleSource>,
  timestamp: Int,
}

/// Actions that can be performed on the treasury
pub type TreasuryRedeemer {
  // Core operations
  Deposit {
    user_pkh: ByteArray,
    ada_lovelace: Int,
    chaos_to_mint: Int,
  }
  Withdraw {
    user_pkh: ByteArray,
    chaos_to_burn: Int,
    ada_to_return: Int,
    djed_to_return: Int,
  }
  Rebalance {
    reason: RebalanceReason,
    trades: List<Trade>,
    new_allocations: Allocations,
    oracle_prices: OraclePrices,
  }

  // Governance operations
  UpdateParameters {
    new_target_ada_bps: Int,
    new_target_djed_bps: Int,
    new_target_lp_bps: Int,
    new_threshold_bps: Int,
  }
  AddOperator { operator: ByteArray }
  RemoveOperator { operator: ByteArray }

  // Emergency operations
  TriggerCircuitBreaker
  ResetCircuitBreaker
}

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

/// Minimum deposit: 100 ADA (in lovelace)
const min_deposit_lovelace: Int = 100_000_000

/// Minimum CHAOS tokens to mint (prevent dust)
const min_chaos_mint: Int = 100

/// Maximum slippage allowed on any trade: 2% (200 bps)
const max_allowed_slippage_bps: Int = 200

/// Minimum time between rebalances: 1 hour (3600 seconds)
const min_rebalance_interval: Int = 3_600_000

/// Time-lock for governance parameter changes: 7 days (ms)
const governance_timelock_ms: Int = 604_800_000

/// Maximum operators allowed
const max_operators: Int = 5

/// Minimum DJED allocation: 20% (bps)
const min_djed_bps: Int = 2_000

/// Minimum LP allocation: 10% (bps)
const min_lp_bps: Int = 1_000

/// Oracle consensus threshold: 5% (500 bps)
const oracle_consensus_threshold_bps: Int = 500

/// Oracle freshness: 1 hour (ms)
const oracle_freshness_ms: Int = 3_600_000

/// MA buy threshold: price < 90% of MA (9000/10000)
const ma_buy_numerator: Int = 9_000

/// MA sell threshold: price > 110% of MA (11000/10000)
const ma_sell_numerator: Int = 11_000

/// MA denominator
const ma_denominator: Int = 10_000

/// Circuit breaker cooldown: 24 hours (ms)
const circuit_breaker_cooldown_ms: Int = 86_400_000

// ---------------------------------------------------------------------------
// Helper Functions
// ---------------------------------------------------------------------------

/// Check if a pubkey hash is in a list
fn has_pkh(pkhs: List<ByteArray>, target: ByteArray) -> Bool {
  list.any(pkhs, fn(p) { p == target })
}

/// Check if a transaction is signed by a given pubkey hash
fn signed_by(transaction: Transaction, pkh: ByteArray) -> Bool {
  list.has(transaction.extra_signatories, pkh)
}

/// Check if any authorized operator signed the transaction
fn operator_signed(
  transaction: Transaction,
  operators: List<ByteArray>,
) -> Bool {
  list.any(operators, fn(op) { signed_by(transaction, op) })
}

/// Get the current transaction validity lower bound (POSIX time ms)
fn tx_validity_start(transaction: Transaction) -> Int {
  when transaction.validity_range.lower_bound.bound_type is {
    Finite(t) -> t
    _ -> 0
  }
}

/// Calculate simple moving average from price history
fn calculate_ma(price_history: List<PricePoint>) -> Int {
  let count = list.length(price_history)
  if count == 0 {
    0
  } else {
    let total =
      list.foldl(price_history, 0, fn(point, acc) { acc + point.price_usd })
    total / count
  }
}

/// Check all oracle sources are within consensus threshold of each other
fn oracle_sources_agree(
  sources: List<OracleSource>,
  threshold_bps: Int,
) -> Bool {
  when sources is {
    [] -> False
    [_single] -> False
    _ -> {
      let prices = list.map(sources, fn(s) { s.price_usd })
      let min_price =
        list.foldl(
          prices,
          999_999_999_999,
          fn(p, acc) {
            if p < acc {
              p
            } else {
              acc
            }
          },
        )
      let max_price =
        list.foldl(
          prices,
          0,
          fn(p, acc) {
            if p > acc {
              p
            } else {
              acc
            }
          },
        )
      // deviation = (max - min) * 10000 / min
      let deviation = ( max_price - min_price ) * 10_000 / min_price
      deviation <= threshold_bps
    }
  }
}

/// Check all oracle sources are recent (within freshness window)
fn oracle_sources_fresh(
  sources: List<OracleSource>,
  current_time: Int,
  freshness_ms: Int,
) -> Bool {
  list.all(sources, fn(s) { current_time - s.timestamp <= freshness_ms })
}

/// Validate oracle prices have consensus and are fresh
fn oracle_valid(prices: OraclePrices, current_time: Int) -> Bool {
  let num_sources = list.length(prices.sources)
  and {
    num_sources >= 2,
    oracle_sources_agree(prices.sources, oracle_consensus_threshold_bps),
    oracle_sources_fresh(prices.sources, current_time, oracle_freshness_ms),
  }
}

/// Check allocations are within safety bounds and sum to 100%
fn allocations_valid(alloc: Allocations, datum: TreasuryDatum) -> Bool {
  and {
    alloc.ada_bps >= datum.min_ada_bps,
    alloc.ada_bps <= datum.max_ada_bps,
    alloc.djed_bps >= min_djed_bps,
    alloc.lp_bps >= min_lp_bps,
    alloc.ada_bps + alloc.djed_bps + alloc.lp_bps == 10_000,
  }
}

/// Check all trades have acceptable slippage
fn trades_slippage_ok(trades: List<Trade>) -> Bool {
  list.all(trades, fn(t) { t.max_slippage_bps <= max_allowed_slippage_bps })
}

/// Validate rebalancing trigger reason against current state
fn rebalance_reason_valid(
  datum: TreasuryDatum,
  reason: RebalanceReason,
  oracle_prices: OraclePrices,
) -> Bool {
  when reason is {
    AllocationDrift { ada_drift_bps } ->
      ada_drift_bps > datum.rebalance_threshold_bps
    PriceBelowMA { .. } -> {
      let ma = calculate_ma(datum.ada_price_history)
      if ma == 0 {
        False
      } else {
        oracle_prices.ada_price_usd * ma_denominator < ma * ma_buy_numerator
      }
    }
    PriceAboveMA { .. } -> {
      let ma = calculate_ma(datum.ada_price_history)
      if ma == 0 {
        False
      } else {
        oracle_prices.ada_price_usd * ma_denominator > ma * ma_sell_numerator
      }
    }
    ManualRebalance -> True
  }
}

/// Parameters are within reasonable bounds
fn parameters_reasonable(
  new_ada: Int,
  new_djed: Int,
  new_lp: Int,
  new_threshold: Int,
) -> Bool {
  and {
    new_ada + new_djed + new_lp == 10_000,
    new_ada >= 3_000,
    new_ada <= 7_000,
    new_djed >= min_djed_bps,
    new_lp >= min_lp_bps,
    new_threshold >= 500,
    new_threshold <= 2_500,
  }
}

/// Find the single continuing output at the script address.
/// Fails if there is not exactly one.
fn get_continuing_output(
  transaction: Transaction,
  script_hash: ByteArray,
) -> transaction.Output {
  let continuing = find_script_outputs(transaction.outputs, script_hash)
  expect [output] = continuing
  output
}

// ---------------------------------------------------------------------------
// Main Validator
// ---------------------------------------------------------------------------

validator chaos_vault {
  spend(
    datum_opt: Option<TreasuryDatum>,
    redeemer: TreasuryRedeemer,
    own_ref: OutputReference,
    transaction: Transaction,
  ) -> Bool {
    expect Some(datum) = datum_opt

    // Resolve own input to get the script hash
    let own_input = resolve_input(transaction.inputs, own_ref)
    expect Script(own_script_hash) = own_input.address.payment_credential

    let current_time = tx_validity_start(transaction)

    when redeemer is {
      // ===================================================================
      // DEPOSIT: User sends ADA to treasury, receives CHAOS tokens
      // ===================================================================
      Deposit { user_pkh, ada_lovelace, chaos_to_mint } -> {
        let cont_output = get_continuing_output(transaction, own_script_hash)
        let cont_lovelace = assets.lovelace_of(cont_output.value)
        let old_lovelace = assets.lovelace_of(own_input.value)

        // Verify the continuing output datum is updated correctly
        expect InlineDatum(cont_datum_data) = cont_output.datum
        expect cont_datum: TreasuryDatum = cont_datum_data

        and {
          // Circuit breaker must not be active
          !datum.circuit_breaker_active,
          // Minimum deposit enforced
          ada_lovelace >= min_deposit_lovelace,
          // Minimum CHAOS mint to prevent dust
          chaos_to_mint >= min_chaos_mint,
          // Transaction must be signed by depositor
          signed_by(transaction, user_pkh),
          // Continuing output has at least old + deposited ADA
          cont_lovelace >= old_lovelace + ada_lovelace,
          // Datum ada_lovelace field updated correctly
          cont_datum.ada_lovelace >= datum.ada_lovelace + ada_lovelace,
        }
      }

      // ===================================================================
      // WITHDRAW: User burns CHAOS tokens, receives proportional assets
      // ===================================================================
      Withdraw { user_pkh, chaos_to_burn, ada_to_return, djed_to_return } -> {
        let cont_output = get_continuing_output(transaction, own_script_hash)
        let cont_lovelace = assets.lovelace_of(cont_output.value)
        let old_lovelace = assets.lovelace_of(own_input.value)

        // Verify the continuing output datum reflects the withdrawal
        expect InlineDatum(cont_datum_data) = cont_output.datum
        expect cont_datum: TreasuryDatum = cont_datum_data

        and {
          // Circuit breaker must not be active
          !datum.circuit_breaker_active,
          // Must burn positive amount
          chaos_to_burn > 0,
          // Return amounts must be non-negative
          ada_to_return >= 0,
          djed_to_return >= 0,
          // At least one asset returned
          ada_to_return > 0 || djed_to_return > 0,
          // Transaction must be signed by withdrawer
          signed_by(transaction, user_pkh),
          // Continuing output retains funds minus withdrawn ADA
          cont_lovelace >= old_lovelace - ada_to_return,
          // Datum reflects reduced holdings
          cont_datum.ada_lovelace == datum.ada_lovelace - ada_to_return,
          cont_datum.djed_amount == datum.djed_amount - djed_to_return,
        }
      }

      // ===================================================================
      // REBALANCE: Operator triggers portfolio rebalancing
      // ===================================================================
      Rebalance { reason, trades, new_allocations, oracle_prices } -> {
        let cont_output = get_continuing_output(transaction, own_script_hash)
        let cont_lovelace = assets.lovelace_of(cont_output.value)
        let old_lovelace = assets.lovelace_of(own_input.value)

        // Verify the continuing output datum reflects new allocations
        expect InlineDatum(cont_datum_data) = cont_output.datum
        expect cont_datum: TreasuryDatum = cont_datum_data

        // Total value must be conserved within slippage bounds (2%)
        // We check ADA value is within 98% of original
        let min_retained = old_lovelace * 9_800 / 10_000

        and {
          // Circuit breaker must not be active
          !datum.circuit_breaker_active,
          // Must be signed by an authorized operator
          operator_signed(transaction, datum.authorized_operators),
          // Rebalancing reason must be valid (trigger met)
          rebalance_reason_valid(datum, reason, oracle_prices),
          // Oracle consensus: >=2 sources within 5%, all fresh
          oracle_valid(oracle_prices, current_time),
          // New allocations within safety bounds
          allocations_valid(new_allocations, datum),
          // All trades have acceptable slippage (<= 2%)
          trades_slippage_ok(trades),
          // At least one trade
          list.length(trades) > 0,
          // Minimum time since last rebalance
          current_time - datum.last_rebalance_time >= min_rebalance_interval,
          // Total value conserved within slippage bounds
          cont_lovelace >= min_retained,
          // Datum reflects new allocation targets
          cont_datum.target_ada_bps == new_allocations.ada_bps,
          cont_datum.target_djed_bps == new_allocations.djed_bps,
          cont_datum.target_lp_bps == new_allocations.lp_bps,
          // Rebalance count incremented
          cont_datum.rebalance_count == datum.rebalance_count + 1,
          // Last rebalance time updated
          cont_datum.last_rebalance_time == current_time,
        }
      }

      // ===================================================================
      // UPDATE PARAMETERS: Governance changes strategy params
      // ===================================================================
      UpdateParameters {
        new_target_ada_bps,
        new_target_djed_bps,
        new_target_lp_bps,
        new_threshold_bps,
      } ->
        and {
          // Must be signed by governance key
          signed_by(transaction, datum.governance_pkh),
          // New parameters must be reasonable
          parameters_reasonable(
            new_target_ada_bps,
            new_target_djed_bps,
            new_target_lp_bps,
            new_threshold_bps,
          ),
          // Time-lock: sufficient time since last rebalance
          current_time - datum.last_rebalance_time >= governance_timelock_ms,
        }

      // ===================================================================
      // ADD OPERATOR: Governance adds an authorized operator
      // ===================================================================
      AddOperator { operator } ->
        and {
          signed_by(transaction, datum.governance_pkh),
          list.length(datum.authorized_operators) < max_operators,
          !has_pkh(datum.authorized_operators, operator),
        }

      // ===================================================================
      // REMOVE OPERATOR: Governance removes an authorized operator
      // ===================================================================
      RemoveOperator { operator } ->
        and {
          signed_by(transaction, datum.governance_pkh),
          has_pkh(datum.authorized_operators, operator),
          list.length(datum.authorized_operators) > 1,
        }

      // ===================================================================
      // TRIGGER CIRCUIT BREAKER: Emergency pause
      // ===================================================================
      TriggerCircuitBreaker ->
        and {
          signed_by(transaction, datum.governance_pkh),
          !datum.circuit_breaker_active,
        }

      // ===================================================================
      // RESET CIRCUIT BREAKER: Resume operations
      // ===================================================================
      ResetCircuitBreaker ->
        and {
          signed_by(transaction, datum.governance_pkh),
          datum.circuit_breaker_active,
          current_time - datum.last_rebalance_time >= circuit_breaker_cooldown_ms,
        }
    }
  }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

test calculate_ma_empty() {
  calculate_ma([]) == 0
}

test calculate_ma_single() {
  calculate_ma([PricePoint { timestamp: 1000, price_usd: 650_000 }]) == 650_000
}

test calculate_ma_multiple() {
  let history =
    [
      PricePoint { timestamp: 1000, price_usd: 600_000 },
      PricePoint { timestamp: 2000, price_usd: 700_000 },
      PricePoint { timestamp: 3000, price_usd: 650_000 },
    ]
  calculate_ma(history) == 650_000
}

test oracle_sources_agree_empty() {
  !oracle_sources_agree([], 500)
}

test oracle_sources_agree_single() {
  !oracle_sources_agree(
    [OracleSource { name: "a", price_usd: 650_000, timestamp: 1000 }],
    500,
  )
}

test oracle_sources_agree_within_threshold() {
  let sources =
    [
      OracleSource { name: "a", price_usd: 650_000, timestamp: 1000 },
      OracleSource { name: "b", price_usd: 652_000, timestamp: 1000 },
    ]
  oracle_sources_agree(sources, 500)
}

test oracle_sources_agree_outside_threshold() {
  let sources =
    [
      OracleSource { name: "a", price_usd: 600_000, timestamp: 1000 },
      OracleSource { name: "b", price_usd: 700_000, timestamp: 1000 },
    ]
  !oracle_sources_agree(sources, 500)
}

test oracle_sources_fresh_all_recent() {
  let sources =
    [
      OracleSource { name: "a", price_usd: 650_000, timestamp: 9_000_000 },
      OracleSource { name: "b", price_usd: 652_000, timestamp: 9_500_000 },
    ]
  oracle_sources_fresh(sources, 10_000_000, 3_600_000)
}

test oracle_sources_fresh_stale() {
  let sources =
    [
      OracleSource { name: "a", price_usd: 650_000, timestamp: 1_000_000 },
      OracleSource { name: "b", price_usd: 652_000, timestamp: 9_500_000 },
    ]
  !oracle_sources_fresh(sources, 10_000_000, 3_600_000)
}

test allocations_valid_correct() {
  let alloc = Allocations { ada_bps: 5_000, djed_bps: 3_000, lp_bps: 2_000 }
  let datum =
    TreasuryDatum {
      ada_lovelace: 0,
      djed_amount: 0,
      lp_positions: [],
      target_ada_bps: 5_000,
      target_djed_bps: 3_000,
      target_lp_bps: 2_000,
      rebalance_threshold_bps: 500,
      ada_price_history: [],
      ma_window: 7,
      authorized_operators: [],
      governance_pkh: #"aa",
      min_ada_bps: 3_000,
      max_ada_bps: 7_000,
      circuit_breaker_active: False,
      last_rebalance_time: 0,
      inception_time: 0,
      total_deposits: 0,
      total_withdrawals: 0,
      rebalance_count: 0,
    }
  allocations_valid(alloc, datum)
}

test allocations_valid_sum_not_100() {
  let alloc = Allocations { ada_bps: 5_000, djed_bps: 3_000, lp_bps: 1_000 }
  let datum =
    TreasuryDatum {
      ada_lovelace: 0,
      djed_amount: 0,
      lp_positions: [],
      target_ada_bps: 5_000,
      target_djed_bps: 3_000,
      target_lp_bps: 2_000,
      rebalance_threshold_bps: 500,
      ada_price_history: [],
      ma_window: 7,
      authorized_operators: [],
      governance_pkh: #"aa",
      min_ada_bps: 3_000,
      max_ada_bps: 7_000,
      circuit_breaker_active: False,
      last_rebalance_time: 0,
      inception_time: 0,
      total_deposits: 0,
      total_withdrawals: 0,
      rebalance_count: 0,
    }
  !allocations_valid(alloc, datum)
}

test parameters_reasonable_valid() {
  parameters_reasonable(5_000, 3_000, 2_000, 1_000)
}

test parameters_reasonable_sum_wrong() {
  !parameters_reasonable(5_000, 3_000, 3_000, 1_000)
}

test parameters_reasonable_ada_too_low() {
  !parameters_reasonable(2_000, 6_000, 2_000, 1_000)
}

test parameters_reasonable_threshold_too_high() {
  !parameters_reasonable(5_000, 3_000, 2_000, 3_000)
}

test has_pkh_found() {
  has_pkh([#"aa", #"bb", #"cc"], #"bb")
}

test has_pkh_not_found() {
  !has_pkh([#"aa", #"bb", #"cc"], #"dd")
}

test trades_slippage_ok_valid() {
  let trades =
    [
      Trade {
        action: Buy,
        asset_in_policy: #"",
        asset_in_name: #"",
        amount_in: 1000,
        asset_out_policy: #"",
        asset_out_name: #"",
        amount_out: 1000,
        dex: Minswap,
        max_slippage_bps: 100,
      },
    ]
  trades_slippage_ok(trades)
}

test trades_slippage_ok_too_high() {
  let trades =
    [
      Trade {
        action: Buy,
        asset_in_policy: #"",
        asset_in_name: #"",
        amount_in: 1000,
        asset_out_policy: #"",
        asset_out_name: #"",
        amount_out: 1000,
        dex: Minswap,
        max_slippage_bps: 300,
      },
    ]
  !trades_slippage_ok(trades)
}
