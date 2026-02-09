# CHAOS Token Smart Contract Specification

**Language**: Aiken v1.0+
**Network**: Cardano (Preview Testnet → Mainnet)
**Audit Status**: 🚧 Pending (Phase 1)
**Version**: 1.0.0

---

## Overview

CHAOS uses two primary smart contracts written in Aiken:
1. **Treasury Vault** (`chaos_vault.ak`) - Manages ADA, DJED, and LP positions
2. **CHAOS Token** (`chaos_token.ak`) - Minting policy for governance token

Both contracts prioritize **security, formal verification, and gas efficiency**.

---

## Contract 1: Treasury Vault (`chaos_vault.ak`)

### Purpose

The Treasury Vault is the core smart contract that:
- Holds all protocol assets (ADA, DJED, LP tokens)
- Validates rebalancing transactions
- Enforces strategy parameters (50/30/20 allocations)
- Authorizes deposits and withdrawals
- Implements safety bounds and circuit breakers

### Datum Structure

```rust
/// Treasury state stored in the UTXO
type TreasuryDatum {
  // Asset holdings
  ada_amount: Int,           // ADA in lovelace (1 ADA = 1,000,000 lovelace)
  djed_amount: Int,          // DJED in smallest unit
  lp_positions: List<LPPosition>,

  // Strategy parameters
  target_ada_allocation: Int,     // Basis points (5000 = 50%)
  target_djed_allocation: Int,    // Basis points (3000 = 30%)
  target_lp_allocation: Int,      // Basis points (2000 = 20%)
  rebalance_threshold: Int,       // Basis points (1000 = 10%)

  // Moving average data (for validation)
  ada_price_history: List<PricePoint>,  // Last 30 days
  moving_average_window: Int,           // Default: 30

  // Authorization
  authorized_operators: List<PubKeyHash>,
  governance_address: Address,

  // Safety mechanisms
  min_ada_allocation: Int,        // Minimum 35% (3500 basis points)
  max_ada_allocation: Int,        // Maximum 65% (6500 basis points)
  circuit_breaker_triggered: Bool,
  last_rebalance_time: POSIXTime,

  // Metadata
  inception_time: POSIXTime,
  total_deposits: Int,
  total_withdrawals: Int,
  rebalance_count: Int
}

/// LP position details
type LPPosition {
  dex: DEX,                  // Minswap | SundaeSwap | WingRiders
  pair: (AssetClass, AssetClass),
  lp_tokens: Int,
  value_usd: Int             // Cached value (updated on rebalance)
}

/// Historical price point
type PricePoint {
  timestamp: POSIXTime,
  price_usd: Int             // Price in micro-USD (1 USD = 1,000,000)
}

/// DEX identifier
type DEX {
  Minswap
  SundaeSwap
  WingRiders
}
```

### Redeemer Structure

```rust
/// Actions that can be performed on the treasury
type TreasuryRedeemer {
  // Core operations
  Deposit {
    user_address: Address,
    ada_amount: Int,
    chaos_to_mint: Int
  }

  Withdraw {
    user_address: Address,
    chaos_to_burn: Int,
    ada_to_return: Int,
    djed_to_return: Int
  }

  Rebalance {
    reason: RebalanceReason,
    trades: List<Trade>,
    new_allocations: Allocations,
    oracle_prices: OraclePrices
  }

  // Governance operations
  UpdateParameters {
    new_target_ada: Option<Int>,
    new_target_djed: Option<Int>,
    new_target_lp: Option<Int>,
    new_threshold: Option<Int>,
    governance_signature: Signature
  }

  AddOperator {
    operator: PubKeyHash,
    governance_signature: Signature
  }

  RemoveOperator {
    operator: PubKeyHash,
    governance_signature: Signature
  }

  // Emergency operations
  TriggerCircuitBreaker {
    reason: String,
    governance_signature: Signature
  }

  ResetCircuitBreaker {
    governance_signature: Signature
  }
}

/// Reason for rebalancing
type RebalanceReason {
  AllocationDrift { ada_drift_bps: Int }
  AdaBelowMA { discount_bps: Int }
  AdaAboveMA { premium_bps: Int }
  ManualRebalance { justification: String }
}

/// Trade to execute during rebalancing
type Trade {
  action: TradeAction,
  asset_in: AssetClass,
  amount_in: Int,
  asset_out: AssetClass,
  amount_out: Int,
  dex: DEX,
  max_slippage_bps: Int      // Maximum allowed slippage (200 = 2%)
}

type TradeAction {
  Buy
  Sell
}

/// Target allocations after rebalancing
type Allocations {
  ada_bps: Int,
  djed_bps: Int,
  lp_bps: Int
}

/// Oracle price data for validation
type OraclePrices {
  ada_price: Int,
  djed_price: Int,
  sources: List<OracleSource>,
  timestamp: POSIXTime
}

type OracleSource {
  name: String,
  price: Int,
  timestamp: POSIXTime
}
```

### Validation Logic

#### 1. Deposit Validation

```rust
validator deposit_validation(
  datum: TreasuryDatum,
  redeemer: TreasuryRedeemer,
  ctx: ScriptContext
) -> Bool {
  when redeemer is {
    Deposit { user_address, ada_amount, chaos_to_mint } -> {
      // 1. Verify ADA is sent to treasury
      let ada_received = value_sent_to_treasury(ctx, ada_amount)

      // 2. Calculate correct CHAOS amount
      let total_value = calculate_total_value(datum)
      let expected_chaos = (ada_amount * total_chaos_supply) / total_value

      // 3. Verify correct amount being minted
      and {
        ada_received,
        chaos_to_mint == expected_chaos,
        chaos_to_mint >= minimum_chaos_mint,  // Prevent dust
        !datum.circuit_breaker_triggered
      }
    }
    _ -> False
  }
}
```

#### 2. Withdrawal Validation

```rust
validator withdrawal_validation(
  datum: TreasuryDatum,
  redeemer: TreasuryRedeemer,
  ctx: ScriptContext
) -> Bool {
  when redeemer is {
    Withdraw { user_address, chaos_to_burn, ada_to_return, djed_to_return } -> {
      // 1. Verify CHAOS tokens are burned
      let chaos_burned = tokens_burned(ctx, chaos_to_burn)

      // 2. Calculate proportional withdrawal
      let user_share = chaos_to_burn / total_chaos_supply
      let expected_ada = datum.ada_amount * user_share
      let expected_djed = datum.djed_amount * user_share

      // 3. Verify correct amounts being withdrawn
      and {
        chaos_burned,
        ada_to_return == expected_ada,
        djed_to_return == expected_djed,
        assets_sent_to_user(ctx, user_address, ada_to_return, djed_to_return),
        !datum.circuit_breaker_triggered
      }
    }
    _ -> False
  }
}
```

#### 3. Rebalance Validation (Critical)

```rust
validator rebalance_validation(
  datum: TreasuryDatum,
  redeemer: TreasuryRedeemer,
  ctx: ScriptContext
) -> Bool {
  when redeemer is {
    Rebalance { reason, trades, new_allocations, oracle_prices } -> {
      and {
        // 1. Verify operator is authorized
        operator_authorized(ctx, datum.authorized_operators),

        // 2. Verify rebalancing is needed
        rebalance_trigger_valid(datum, reason, oracle_prices),

        // 3. Verify oracle consensus (≥2 sources within 5%)
        oracle_consensus_valid(oracle_prices),

        // 4. Verify new allocations are within bounds
        allocations_within_bounds(new_allocations, datum),

        // 5. Verify trades are necessary and correct
        trades_valid(datum, trades, new_allocations),

        // 6. Verify slippage is acceptable
        all_trades_below_max_slippage(trades),

        // 7. Verify time-delay for large rebalances
        time_delay_respected(datum, trades),

        // 8. Circuit breaker not triggered
        !datum.circuit_breaker_triggered
      }
    }
    _ -> False
  }
}

/// Check if rebalancing trigger is valid
fn rebalance_trigger_valid(
  datum: TreasuryDatum,
  reason: RebalanceReason,
  prices: OraclePrices
) -> Bool {
  when reason is {
    AllocationDrift { ada_drift_bps } -> {
      let current_allocation = calculate_ada_allocation(datum, prices)
      let drift = abs(current_allocation - datum.target_ada_allocation)
      drift > datum.rebalance_threshold
    }

    AdaBelowMA { discount_bps } -> {
      let ma = calculate_moving_average(datum.ada_price_history)
      let current_price = prices.ada_price
      current_price < (ma * 9000) / 10000  // < 90% of MA
    }

    AdaAboveMA { premium_bps } -> {
      let ma = calculate_moving_average(datum.ada_price_history)
      let current_price = prices.ada_price
      current_price > (ma * 11000) / 10000  // > 110% of MA
    }

    ManualRebalance { justification } -> {
      // Requires governance approval (checked separately)
      True
    }
  }
}

/// Verify oracle prices have consensus
fn oracle_consensus_valid(prices: OraclePrices) -> Bool {
  let num_sources = length(prices.sources)
  and {
    num_sources >= 2,                          // At least 2 sources
    all_within_threshold(prices.sources, 500), // Within 5% of each other
    all_recent(prices.sources, 3600)          // Updated within 1 hour
  }
}

/// Verify allocations are within safety bounds
fn allocations_within_bounds(
  alloc: Allocations,
  datum: TreasuryDatum
) -> Bool {
  and {
    alloc.ada_bps >= datum.min_ada_allocation,     // ≥ 35%
    alloc.ada_bps <= datum.max_ada_allocation,     // ≤ 65%
    alloc.ada_bps + alloc.djed_bps + alloc.lp_bps == 10000,  // Sum to 100%
    alloc.djed_bps >= 2000,                        // ≥ 20% (stability buffer)
    alloc.lp_bps >= 1000                           // ≥ 10% (minimum yield)
  }
}
```

#### 4. Governance Validation

```rust
validator governance_validation(
  datum: TreasuryDatum,
  redeemer: TreasuryRedeemer,
  ctx: ScriptContext
) -> Bool {
  when redeemer is {
    UpdateParameters { new_target_ada, new_target_djed, new_target_lp, new_threshold, governance_signature } -> {
      and {
        // Verify governance signature
        verify_governance_signature(governance_signature, datum.governance_address),

        // Verify new parameters are reasonable
        parameters_reasonable(new_target_ada, new_target_djed, new_target_lp, new_threshold),

        // Time-lock: 7 days since proposal
        time_lock_expired(ctx, 604800)
      }
    }

    AddOperator { operator, governance_signature } -> {
      and {
        verify_governance_signature(governance_signature, datum.governance_address),
        length(datum.authorized_operators) < 5,  // Max 5 operators
        !list_contains(datum.authorized_operators, operator)
      }
    }

    RemoveOperator { operator, governance_signature } -> {
      and {
        verify_governance_signature(governance_signature, datum.governance_address),
        list_contains(datum.authorized_operators, operator),
        length(datum.authorized_operators) > 1   // Always keep at least 1
      }
    }

    _ -> False
  }
}
```

#### 5. Circuit Breaker Validation

```rust
validator circuit_breaker_validation(
  datum: TreasuryDatum,
  redeemer: TreasuryRedeemer,
  ctx: ScriptContext
) -> Bool {
  when redeemer is {
    TriggerCircuitBreaker { reason, governance_signature } -> {
      and {
        verify_governance_signature(governance_signature, datum.governance_address),
        !datum.circuit_breaker_triggered,
        reason_is_emergency(reason)  // Verify it's a valid emergency
      }
    }

    ResetCircuitBreaker { governance_signature } -> {
      and {
        verify_governance_signature(governance_signature, datum.governance_address),
        datum.circuit_breaker_triggered,
        sufficient_time_passed(datum.last_rebalance_time, 86400)  // 24 hours
      }
    }

    _ -> False
  }
}
```

### Gas Optimization

**Target**: < 10,000 execution units per transaction

**Optimizations**:
1. Use Int instead of BigInt where possible (lovelace amounts fit in Int)
2. Limit price history to last 30 data points (not full history)
3. Batch oracle checks (single validation for all sources)
4. Use builtins for common operations (`add_integer`, `multiply_integer`)
5. Minimize list operations (use `length`, avoid `fold` where possible)

**Estimated Gas Costs**:
- Deposit: ~3,000 execution units
- Withdrawal: ~3,500 execution units
- Rebalancing: ~8,000 execution units (most complex)
- Governance update: ~2,500 execution units

---

## Contract 2: CHAOS Token Minting Policy (`chaos_token.ak`)

### Purpose

The CHAOS token minting policy controls:
- Initial token distribution (ISPO, LBP, team allocations)
- Algorithmic minting on deposits
- Burning on withdrawals
- Maximum supply enforcement (100M tokens)

### Policy Structure

```rust
/// CHAOS token minting policy
type CHAOSPolicy {
  /// Initial distribution (one-time minting)
  InitialMint {
    ispo_allocation: Int,        // 60M tokens
    lbp_allocation: Int,          // 30M tokens
    team_allocation: Int,         // 5M tokens
    treasury_allocation: Int,     // 3M tokens
    liquidity_allocation: Int,    // 2M tokens
    recipients: List<(Address, Int)>
  }

  /// Algorithmic minting (proportional to deposit)
  DepositMint {
    user_address: Address,
    ada_deposited: Int,
    total_tvl: Int,
    total_supply: Int
  }

  /// Burning (on withdrawal)
  WithdrawBurn {
    user_address: Address,
    chaos_amount: Int
  }
}
```

### Minting Validation

```rust
validator chaos_minting_validation(
  redeemer: CHAOSPolicy,
  ctx: ScriptContext
) -> Bool {
  when redeemer is {
    InitialMint { ispo_allocation, lbp_allocation, team_allocation, treasury_allocation, liquidity_allocation, recipients } -> {
      and {
        // 1. Verify total is 100M
        ispo_allocation + lbp_allocation + team_allocation + treasury_allocation + liquidity_allocation == 100_000_000,

        // 2. Verify allocations match plan
        ispo_allocation == 60_000_000,
        lbp_allocation == 30_000_000,
        team_allocation == 5_000_000,
        treasury_allocation == 3_000_000,
        liquidity_allocation == 2_000_000,

        // 3. Verify this is first mint (no existing supply)
        current_supply(ctx) == 0,

        // 4. Verify tokens sent to correct recipients
        all_recipients_valid(recipients),

        // 5. Verify governance approval
        governance_approved(ctx)
      }
    }

    DepositMint { user_address, ada_deposited, total_tvl, total_supply } -> {
      // Calculate proportional mint: shares = deposit × supply / TVL
      let chaos_to_mint = (ada_deposited * total_supply) / total_tvl

      and {
        // 1. Verify calculation is correct
        mint_amount_correct(ctx, chaos_to_mint),

        // 2. Verify tokens sent to user
        tokens_sent_to_user(ctx, user_address, chaos_to_mint),

        // 3. Verify treasury receives ADA
        ada_sent_to_treasury(ctx, ada_deposited),

        // 4. Verify max supply not exceeded
        total_supply + chaos_to_mint <= 100_000_000,

        // 5. Minimum mint to prevent dust
        chaos_to_mint >= 100
      }
    }

    WithdrawBurn { user_address, chaos_amount } -> {
      and {
        // 1. Verify tokens are burned
        tokens_burned(ctx, chaos_amount),

        // 2. Verify user owns the tokens
        user_owns_tokens(ctx, user_address, chaos_amount),

        // 3. Verify treasury sends proportional assets
        treasury_withdrawal_valid(ctx, chaos_amount)
      }
    }
  }
}
```

### Token Metadata

```rust
/// On-chain metadata for CHAOS token
type CHAOSMetadata {
  name: "CHAOS Token",
  ticker: "CHAOS",
  description: "Governance token for CHAOS volatility harvesting fund",
  decimals: 6,
  logo: "ipfs://...",  // IPFS hash for logo
  website: "https://chaostoken.io",
  max_supply: 100_000_000
}
```

---

## Security Considerations

### 1. Double-Spending Protection

**Risk**: User withdraws while deposit is being processed

**Mitigation**:
- Use UTXO model's inherent protection (can't spend same UTXO twice)
- Implement sequential transaction processing
- Add nonce to datum to detect replays

### 2. Oracle Manipulation

**Risk**: Attacker manipulates price feed to trigger false rebalancing

**Mitigation**:
- Require ≥2 independent oracles
- Verify prices are within 5% of each other
- 1-hour time delay between signal and execution
- Reject if any source shows >20% price change in 1 hour

### 3. Front-Running

**Risk**: Attacker sees rebalancing transaction and front-runs it

**Mitigation**:
- Use time-locked transactions (can't be executed until specific slot)
- Implement slippage protection (max 2%)
- Use Minswap's anti-MEV features

### 4. Governance Attacks

**Risk**: Malicious governance proposal changes parameters

**Mitigation**:
- 7-day time-lock on all parameter changes
- Require >50% CHAOS holder approval
- Circuit breaker can override malicious changes
- Parameter bounds hard-coded (can't set 0% ADA allocation)

### 5. Reentrancy

**Risk**: Not applicable in EUTXO model (no state mutation)

**Status**: ✅ Safe by design (Cardano's EUTXO prevents reentrancy)

### 6. Integer Overflow/Underflow

**Risk**: Large numbers cause overflow

**Mitigation**:
- Use checked arithmetic in Aiken (`add_integer`, `multiply_integer`)
- Validate all inputs are positive
- Test with maximum values (18.4 quintillion lovelace = entire ADA supply)

### 7. Dust Attacks

**Risk**: Attacker creates many tiny UTXOs to bloat the ledger

**Mitigation**:
- Minimum deposit: 100 ADA
- Minimum withdrawal: 10 CHAOS tokens
- UTXO consolidation mechanism

---

## Testing Strategy

### Unit Tests

```rust
test deposit_valid() {
  let datum = mock_treasury_datum()
  let redeemer = Deposit {
    user_address: mock_address(),
    ada_amount: 1000_000_000,  // 1000 ADA
    chaos_to_mint: 1000_000_000
  }
  let ctx = mock_script_context()

  assert deposit_validation(datum, redeemer, ctx) == True
}

test deposit_invalid_amount() {
  let datum = mock_treasury_datum()
  let redeemer = Deposit {
    user_address: mock_address(),
    ada_amount: 1000_000_000,
    chaos_to_mint: 999_000_000  // Wrong amount!
  }
  let ctx = mock_script_context()

  assert deposit_validation(datum, redeemer, ctx) == False
}

// Test all edge cases:
// - Zero amounts
// - Maximum amounts (entire ADA supply)
// - Circuit breaker active
// - Oracle disagreement
// - Invalid allocations (>65% ADA)
// - Unauthorized operator
```

### Integration Tests (Testnet)

1. **Deposit Flow**: Deposit ADA → Mint CHAOS → Verify balance
2. **Withdrawal Flow**: Burn CHAOS → Withdraw proportional assets → Verify balance
3. **Rebalancing Flow**: Trigger condition → Execute rebalance → Verify allocations
4. **Governance Flow**: Submit proposal → Vote → Execute after time-lock
5. **Circuit Breaker**: Trigger emergency → Verify operations blocked → Reset

### Property-Based Tests

```rust
property test_allocations_always_sum_to_100_percent() {
  forall datum in arbitrary_treasury_datum() {
    let total = datum.target_ada_allocation +
                datum.target_djed_allocation +
                datum.target_lp_allocation
    assert total == 10000  // Always 100.00%
  }
}

property test_withdrawal_proportional() {
  forall (datum, chaos_amount) in arbitrary_withdrawal() {
    let user_share = chaos_amount / total_chaos_supply
    let expected_ada = datum.ada_amount * user_share

    // User always gets proportional share (within rounding error)
    assert abs(actual_ada - expected_ada) < 1000  // < 0.001 ADA
  }
}
```

---

## Deployment Checklist

### Pre-Deployment

- [ ] All unit tests passing (>95% coverage)
- [ ] Integration tests on testnet successful
- [ ] Property-based tests show no violations
- [ ] External audit completed (zero critical/high issues)
- [ ] Gas costs measured and optimized
- [ ] Emergency procedures documented

### Testnet Deployment

- [ ] Deploy to Cardano Preview testnet
- [ ] Initialize treasury with test funds
- [ ] Execute 10+ deposit/withdrawal transactions
- [ ] Execute 3+ rebalancing transactions
- [ ] Test governance proposal flow
- [ ] Test circuit breaker activation/reset
- [ ] 100+ community testers validate functionality

### Mainnet Deployment

- [ ] Final audit review
- [ ] Deploy treasury vault contract
- [ ] Deploy CHAOS minting policy
- [ ] Execute initial mint (100M tokens)
- [ ] Distribute ISPO allocation (60M)
- [ ] Set TVL cap ($10K initially)
- [ ] Monitor for 72 hours before scaling

---

## Upgrade Path

**Aiken contracts are immutable by default**, but we can upgrade via:

1. **New Contract Deployment**: Deploy v2 contract, migrate funds via governance
2. **Proxy Pattern**: Use a reference script that points to the latest version
3. **Governance Parameters**: Most changes (allocations, thresholds) are parameters, not code

**Planned Upgrades** (Post-Phase 1):
- Multi-asset support (add SOL, BTC, ETH)
- Advanced strategies (ML-enhanced signals)
- Flash loan protection
- Batch operations

---

## Gas Budget & Costs

| Operation | Execution Units | Memory Units | Estimated Fee (ADA) |
|-----------|----------------|--------------|---------------------|
| Deposit | 3,000 | 8,000 | 0.3 |
| Withdrawal | 3,500 | 9,000 | 0.35 |
| Rebalancing | 8,000 | 15,000 | 0.8 |
| Governance Update | 2,500 | 7,000 | 0.25 |

**Total Annual Cost** (15 rebalances/year): ~12 ADA (~$8 at $0.65/ADA)

**Optimization Goal**: Reduce rebalancing cost to <0.5 ADA

---

## Appendix: Helper Functions

### Calculate Total Value

```rust
fn calculate_total_value(datum: TreasuryDatum, ada_price: Int, djed_price: Int) -> Int {
  let ada_value = (datum.ada_amount * ada_price) / 1_000_000
  let djed_value = (datum.djed_amount * djed_price) / 1_000_000
  let lp_value = sum(map(lp -> lp.value_usd, datum.lp_positions))

  ada_value + djed_value + lp_value
}
```

### Calculate Moving Average

```rust
fn calculate_moving_average(price_history: List<PricePoint>) -> Int {
  let sum = fold(price_history, 0, fn(acc, point) { acc + point.price_usd })
  sum / length(price_history)
}
```

### Verify Oracle Consensus

```rust
fn all_within_threshold(sources: List<OracleSource>, threshold_bps: Int) -> Bool {
  let prices = map(sources, fn(s) { s.price })
  let min_price = minimum(prices)
  let max_price = maximum(prices)
  let deviation = ((max_price - min_price) * 10000) / min_price

  deviation <= threshold_bps
}
```

---

**Last Updated**: February 7, 2026
**Status**: ✅ Specification Complete, 🚧 Implementation Starting (Week 2)
**Target LOC**: 800-1000 (both contracts combined)
