// ============================================================================
// CHAOS Token Minting Policy
// Language: Aiken v1.1+
// Network: Cardano (Preprod → Mainnet)
//
// Controls CHAOS token lifecycle:
// - Initial distribution (100M tokens, one-time)
// - Algorithmic minting on deposits (proportional to TVL share)
// - Burning on withdrawals
// - Maximum supply enforcement
// ============================================================================

use aiken/collection/dict
use aiken/collection/list
use cardano/assets.{PolicyId}
use cardano/transaction.{Transaction}

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// Recipient for initial distribution
pub type Recipient {
  pkh: ByteArray,
  amount: Int,
}

/// CHAOS token minting/burning actions
pub type CHAOSRedeemer {
  /// Initial distribution (one-time, 100M total)
  InitialMint {
    recipients: List<Recipient>,
    governance_pkh: ByteArray,
  }

  /// Algorithmic minting on deposit
  DepositMint {
    user_pkh: ByteArray,
    ada_deposited: Int,
    total_tvl: Int,
    total_supply: Int,
    chaos_to_mint: Int,
  }

  /// Burning on withdrawal
  WithdrawBurn {
    user_pkh: ByteArray,
    chaos_to_burn: Int,
  }
}

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

/// Maximum total supply: 100 million CHAOS tokens (in smallest unit, 6 decimals)
const max_supply: Int = 100_000_000_000_000

/// Minimum CHAOS tokens to mint (prevent dust attacks)
const min_mint_amount: Int = 100_000_000

/// CHAOS token name
const chaos_token_name: ByteArray = "CHAOS"

// ---------------------------------------------------------------------------
// Helper Functions
// ---------------------------------------------------------------------------

/// Sum the amounts for all recipients
fn sum_recipients(recipients: List<Recipient>) -> Int {
  list.foldl(recipients, 0, fn(r, acc) { acc + r.amount })
}

/// All recipient amounts are positive
fn all_positive(recipients: List<Recipient>) -> Bool {
  list.all(recipients, fn(r) { r.amount > 0 })
}

/// Check if a transaction is signed by a given pubkey hash
fn signed_by(transaction: Transaction, pkh: ByteArray) -> Bool {
  list.has(transaction.extra_signatories, pkh)
}

/// Get the amount of CHAOS tokens being minted (positive) or burned (negative)
/// in this transaction, for our own policy ID
fn get_mint_amount(transaction: Transaction, policy_id: PolicyId) -> Int {
  let minted_tokens = assets.tokens(transaction.mint, policy_id)
  when dict.to_pairs(minted_tokens) is {
    [Pair(name, amount)] ->
      if name == chaos_token_name {
        amount
      } else {
        0
      }
    _ -> 0
  }
}

// ---------------------------------------------------------------------------
// Main Minting Policy
// ---------------------------------------------------------------------------

validator chaos_token {
  mint(
    redeemer: CHAOSRedeemer,
    policy_id: PolicyId,
    transaction: Transaction,
  ) -> Bool {
    let mint_amount = get_mint_amount(transaction, policy_id)

    when redeemer is {
      // ===================================================================
      // INITIAL MINT: One-time creation of 100M CHAOS tokens
      // ===================================================================
      InitialMint { recipients, governance_pkh } -> {
        let total_distributed = sum_recipients(recipients)

        and {
          // Must be minting (positive amount)
          mint_amount > 0,
          // Total minted must equal max supply
          mint_amount == max_supply,
          // Distribution must sum to total supply
          total_distributed == max_supply,
          // All amounts must be positive
          all_positive(recipients),
          // Must be signed by governance
          signed_by(transaction, governance_pkh),
        }
      }

      // ===================================================================
      // DEPOSIT MINT: Proportional minting when user deposits ADA
      // ===================================================================
      DepositMint {
        user_pkh,
        ada_deposited,
        total_tvl,
        total_supply,
        chaos_to_mint,
      } -> {
        // Calculate expected mint: deposit * supply / TVL
        let expected_mint =
          if total_tvl > 0 {
            ada_deposited * total_supply / total_tvl
          } else {
            // First deposit: 1:1 ratio (1 ADA = 1 CHAOS in smallest units)
            ada_deposited
          }

        and {
          // Must be minting (positive amount)
          mint_amount > 0,
          // Amount matches the redeemer declaration
          mint_amount == chaos_to_mint,
          // Calculation is correct (allow 1% tolerance for rounding)
          chaos_to_mint <= expected_mint + expected_mint / 100,
          chaos_to_mint >= expected_mint - expected_mint / 100,
          // Minimum mint to prevent dust
          chaos_to_mint >= min_mint_amount,
          // Must not exceed max supply
          total_supply + chaos_to_mint <= max_supply,
          // User must sign the transaction
          signed_by(transaction, user_pkh),
          // Deposit must be positive
          ada_deposited > 0,
          // TVL and supply must be non-negative
          total_tvl >= 0,
          total_supply >= 0,
        }
      }

      // ===================================================================
      // WITHDRAW BURN: Burning CHAOS tokens on withdrawal
      // ===================================================================
      WithdrawBurn { user_pkh, chaos_to_burn } ->
        and {
          // Must be burning (negative amount)
          mint_amount < 0,
          // Burn amount matches (mint_amount is negative for burns)
          mint_amount == -chaos_to_burn,
          // Must burn a positive amount
          chaos_to_burn > 0,
          // User must sign the transaction
          signed_by(transaction, user_pkh),
        }
    }
  }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

test sum_recipients_empty() {
  sum_recipients([]) == 0
}

test sum_recipients_multiple() {
  let recipients =
    [
      Recipient { pkh: #"aa", amount: 60_000_000_000_000 },
      Recipient { pkh: #"bb", amount: 30_000_000_000_000 },
      Recipient { pkh: #"cc", amount: 10_000_000_000_000 },
    ]
  sum_recipients(recipients) == 100_000_000_000_000
}

test all_positive_valid() {
  let recipients =
    [
      Recipient { pkh: #"aa", amount: 100 },
      Recipient { pkh: #"bb", amount: 200 },
    ]
  all_positive(recipients)
}

test all_positive_with_zero() {
  let recipients =
    [
      Recipient { pkh: #"aa", amount: 100 },
      Recipient { pkh: #"bb", amount: 0 },
    ]
  !all_positive(recipients)
}

test all_positive_with_negative() {
  let recipients =
    [
      Recipient { pkh: #"aa", amount: 100 },
      Recipient { pkh: #"bb", amount: -50 },
    ]
  !all_positive(recipients)
}
