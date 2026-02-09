/-
  Basic definitions for Cardano stake pool game theory analysis

  This file defines the fundamental types and structures needed to model
  Cardano's proof-of-stake system.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic

namespace CardanoNash

/-- Stake amount in ADA (simplified as ℝ≥0) -/
abbrev Stake := { x : ℝ // 0 ≤ x }

/-- Pool identifier -/
abbrev PoolId := ℕ

/-- Address/stakeholder identifier -/
abbrev Address := ℕ

/-- Pledge influence parameter (a₀ in the papers), typically 0.3 for Cardano -/
structure PledgeInfluence where
  value : ℝ
  nonneg : 0 ≤ value
  bounded : value ≤ 1

/-- Target number of pools (k parameter) -/
structure TargetPools where
  value : ℕ
  positive : 0 < value

/-- Saturation point for a pool -/
structure Saturation where
  value : ℝ
  positive : 0 < value

/-- Pool parameters -/
structure PoolParams where
  pledge_influence : PledgeInfluence
  target_pools : TargetPools
  saturation : Saturation
  total_stake : Stake

/-- A stake pool with its properties -/
structure StakePool where
  id : ℕ
  pledge : Stake  -- Operator's pledge
  stake : Stake   -- Total delegated stake (including pledge)
  margin : ℝ      -- Pool margin/fee (0 to 1)
  cost : ℝ        -- Fixed cost per epoch
  margin_valid : 0 ≤ margin ∧ margin ≤ 1
  cost_nonneg : 0 ≤ cost

/-- Helper to check if pool is valid -/
def StakePool.isValid (pool : StakePool) : Prop :=
  pool.pledge.val ≤ pool.stake.val

/-- Delegation decision: which pool a delegator chooses -/
structure Delegation where
  delegator : Address
  pool : ℕ  -- Pool ID
  amount : Stake

/-- System state: configuration of all pools and delegations -/
structure SystemState (n_pools : ℕ) (n_delegators : ℕ) where
  pools : Fin n_pools → StakePool
  delegations : List Delegation

end CardanoNash
