/-
  Game-theoretic formalization of Cardano staking

  This file defines the staking game, strategies, utilities, and
  the concept of Nash equilibrium in this context.
-/

import CardanoNash.Basic
import CardanoNash.Rewards
import Mathlib.Data.Finset.Basic

namespace CardanoNash

/-- Player types in the staking game -/
inductive Player
  | Delegator (id : ℕ)
  | PoolOperator (id : ℕ)

/-- Strategy for a delegator: choose which pool to delegate to -/
structure DelegatorStrategy (n_pools : ℕ) where
  choice : Fin n_pools  -- Which pool to delegate to

/-- Strategy for a pool operator: set margin and cost -/
structure PoolOperatorStrategy where
  margin : ℝ
  cost : ℝ
  margin_valid : 0 ≤ margin ∧ margin ≤ 1
  cost_nonneg : 0 ≤ cost

/-- Combined strategy profile for all players -/
structure StrategyProfile (n_pools : ℕ) (n_delegators : ℕ) where
  delegator_strategies : Fin n_delegators → DelegatorStrategy n_pools
  operator_strategies : Fin n_pools → PoolOperatorStrategy

noncomputable section

/-- Utility for a delegator: expected rewards from their delegation -/
def delegatorUtility
    (params : PoolParams)
    (delegator_stake : Stake)
    (pool : StakePool)
    (epoch_rewards : ℝ) : ℝ :=
  delegatorReward delegator_stake.val pool (poolRewards params pool epoch_rewards)

/-- Utility for a pool operator: their share of pool rewards -/
def operatorUtility
    (params : PoolParams)
    (pool : StakePool)
    (epoch_rewards : ℝ) : ℝ :=
  let total := poolRewards params pool epoch_rewards
  operatorRewards pool total

/--
  Best response for a delegator: which pool maximizes their utility?

  This is a key part of Nash equilibrium - each player is playing their best response.
-/
def bestResponseDelegator
    (params : PoolParams)
    (_delegator_stake : Stake)
    (pools : List StakePool)
    (epoch_rewards : ℝ) : Option StakePool :=
  -- Find pool with highest desirability (simplified)
  pools.foldl (fun best pool =>
    match best with
    | none => some pool
    | some b =>
      if poolDesirability params pool epoch_rewards >
         poolDesirability params b epoch_rewards
      then some pool else some b
  ) none

/--
  Check if a delegator is playing a best response given current pool configuration
-/
def isDelegatorBestResponse
    (params : PoolParams)
    (delegator_stake : Stake)
    (chosen_pool : StakePool)
    (all_pools : List StakePool)
    (epoch_rewards : ℝ) : Prop :=
  ∀ (other_pool : StakePool), other_pool ∈ all_pools →
    delegatorUtility params delegator_stake chosen_pool epoch_rewards ≥
    delegatorUtility params delegator_stake other_pool epoch_rewards

/-
  Pool splitting: Can an operator improve utility by running multiple pools?

  This is CRITICAL for Nash equilibrium. If splitting is profitable,
  the equilibrium breaks down!
-/
def splittingProfitable
    (params : PoolParams)
    (single_pool : StakePool)
    (split_pools : List StakePool)
    (epoch_rewards : ℝ) : Prop :=
  let single_utility := operatorUtility params single_pool epoch_rewards
  let split_utility := (split_pools.map (operatorUtility params · epoch_rewards)).sum
  split_utility > single_utility

/--
  Nash equilibrium condition: no player can improve by unilaterally deviating

  ISSUE: This is just the definition. We need to PROVE it exists!
-/
def isNashEquilibrium
    {n_pools n_delegators : ℕ}
    (params : PoolParams)
    (state : SystemState n_pools n_delegators)
    (epoch_rewards : ℝ) : Prop :=
  -- No delegator wants to switch pools (simplified: check all pools are best responses)
  (∀ (i : Fin n_pools),
    isDelegatorBestResponse
      params
      (state.pools i).pledge  -- Use pool's pledge as proxy for delegator stake
      (state.pools i)
      (List.ofFn state.pools)
      epoch_rewards)
  ∧
  -- No operator wants to change their parameters (margin, cost)
  (∀ (i : Fin n_pools),
    let pool := state.pools i
    ∀ (alt_margin : ℝ) (alt_cost : ℝ),
      (h_m1 : 0 ≤ alt_margin) → (h_m2 : alt_margin ≤ 1) → (h_c : 0 ≤ alt_cost) →
      let alt_pool : StakePool := {
        id := pool.id
        pledge := pool.pledge
        stake := pool.stake
        margin := alt_margin
        cost := alt_cost
        margin_valid := ⟨h_m1, h_m2⟩
        cost_nonneg := h_c
      }
      operatorUtility params pool epoch_rewards ≥
      operatorUtility params alt_pool epoch_rewards)
  ∧
  -- No operator profits from pool splitting (when a0 is high enough)
  (∀ (i : Fin n_pools),
    ∀ (split_pools : List StakePool),
      ¬splittingProfitable params (state.pools i) split_pools epoch_rewards)

end

end CardanoNash
