/-
  CHAOS Protocol — Core Types
  Formal verification of the CHAOS antifragile volatility harvesting strategy.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace CHAOS

/-- Portfolio allocation parameters -/
structure Params where
  α : ℝ  -- Volatile asset allocation target
  β : ℝ  -- Stablecoin allocation target
  γ : ℝ  -- LP allocation target
  δ : ℝ  -- Rebalancing threshold
  c : ℝ  -- Transaction cost per unit traded
  h_α_pos : 0 < α
  h_α_lt  : α < 1
  h_β_pos : 0 < β
  h_γ_pos : 0 < γ
  h_sum   : α + β + γ = 1
  h_δ_pos : 0 < δ
  h_c_pos : 0 < c

/-- Treasury state -/
structure Treasury where
  asset_tokens : ℝ    -- Number of volatile asset tokens
  stable_value : ℝ    -- Stablecoin value in USD
  lp_value     : ℝ    -- LP position value in USD
  h_asset_nn   : 0 ≤ asset_tokens
  h_stable_nn  : 0 ≤ stable_value
  h_lp_nn      : 0 ≤ lp_value

/-- Portfolio value given asset price -/
def Treasury.value (t : Treasury) (p : ℝ) : ℝ :=
  t.asset_tokens * p + t.stable_value + t.lp_value

/-- Asset allocation fraction -/
noncomputable def Treasury.asset_alloc (t : Treasury) (p : ℝ) (_h : 0 < t.value p) : ℝ :=
  (t.asset_tokens * p) / t.value p

end CHAOS
