/-
  Cardano reward mechanism formalization

  This formalizes the reward calculation as specified in the
  "Reward Sharing Schemes for Stake Pools" paper by Brünjes et al.

  Key formula: R(σ, s, c, m, z) where
    σ = pool's stake
    s = pool's pledge
    c = pool's fixed cost
    m = pool's margin
    z = saturation point
-/

import CardanoNash.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace CardanoNash

open Real

noncomputable section

/--
  Apparent performance of a pool (simplified to 1.0 for honest pools)
  In reality this depends on block production performance
-/
def performance : ℝ := 1.0

/--
  Pool's relative stake (σ/total_stake)
  This determines the expected number of blocks the pool will produce
-/
def relativeStake (pool : StakePool) (total : ℝ) (_h : 0 < total) : ℝ :=
  pool.stake.val / total

/--
  Capped stake: min(σ, z) where z is the saturation point
  Prevents pools from growing too large
-/
def cappedStake (pool_stake : ℝ) (saturation : ℝ) : ℝ :=
  min pool_stake saturation

/--
  Pledge benefit function: s / (1 + a₀) where
    s = pledge
    a₀ = pledge influence parameter

  This is simplified; the actual formula is more complex
-/
def pledgeBenefit (pledge : ℝ) (a0 : ℝ) : ℝ :=
  pledge / (1 + a0)

/--
  Pool's total rewards in an epoch (simplified model)

  R(σ, s, c, m, z) = (R₀ × min(σ, z) / z) × (1 + a₀ × s / z)

  Where:
    R₀ = total rewards available in the epoch
    σ = pool's stake
    s = pool's pledge
    z = saturation point
    a₀ = pledge influence parameter

  This is a simplified version. The actual Cardano formula is:
  R(σ, s, c, m) = (R × min(σ, z) / z) × (1 + a₀) × (s + σ × a₀) / (z × (1 + a₀))
-/
def poolRewards (params : PoolParams) (pool : StakePool) (epoch_rewards : ℝ) : ℝ :=
  let σ := pool.stake.val
  let s := pool.pledge.val
  let z := params.saturation.value
  let a0 := params.pledge_influence.value
  let stake_factor := min σ z / z
  let pledge_factor := (1 + a0) * (s + σ * a0) / (z * (1 + a0))
  epoch_rewards * stake_factor * pledge_factor

/--
  Pool operator rewards (what the operator keeps)
  Operator gets: fixed_cost + margin × (total_rewards - fixed_cost)
-/
def operatorRewards (pool : StakePool) (total_rewards : ℝ) : ℝ :=
  let after_cost := max 0 (total_rewards - pool.cost)
  pool.cost + pool.margin * after_cost

/--
  Rewards available for delegators (distributed proportionally)
-/
def delegatorRewards (pool : StakePool) (total_rewards : ℝ) : ℝ :=
  let after_cost := max 0 (total_rewards - pool.cost)
  (1 - pool.margin) * after_cost

/--
  Individual delegator's reward based on their stake in the pool
-/
def delegatorReward (delegation_amount : ℝ) (pool : StakePool) (total_rewards : ℝ) : ℝ :=
  if pool.stake.val > 0 then
    (delegation_amount / pool.stake.val) * delegatorRewards pool total_rewards
  else
    0

/--
  Non-myopic pool ranking: expected long-term return per unit of stake

  This is what rational delegators use to choose pools in equilibrium.
  Simplified version that assumes the pool will reach saturation.
-/
def nonMyopicPoolRank (params : PoolParams) (pool : StakePool) (epoch_rewards : ℝ) : ℝ :=
  let total_rewards := poolRewards params pool epoch_rewards
  let delegator_share := delegatorRewards pool total_rewards
  -- Expected return per unit of stake
  if pool.stake.val > 0 then
    delegator_share / pool.stake.val
  else
    0

/--
  CRITICAL ASSUMPTION: The desirability function

  This is what delegators use to rank pools. The Nash equilibrium proof
  assumes this ranking leads to convergence to k pools.

  STRUCTURAL ISSUE: This may not always hold!
-/
def poolDesirability (params : PoolParams) (pool : StakePool) (epoch_rewards : ℝ) : ℝ :=
  nonMyopicPoolRank params pool epoch_rewards

end

end CardanoNash
