/-
  CHAOS Protocol — LP Fee Floor (Theorem 3)

  Proves that when LP yield exceeds impermanent loss,
  the LP position contributes a positive return floor.
-/
import CHAOS.Basic

namespace CHAOS

/-- Theorem 3: LP fee return floor.

When LP yield exceeds impermanent loss, LP positions
contribute a positive return to the portfolio. -/
theorem lp_fee_floor
    (params : Params)
    (r_lp : ℝ)
    (il_max : ℝ)
    (_h_yield_pos : 0 < r_lp)
    (_h_il_nn : 0 ≤ il_max)
    (h_yield_gt_il : il_max < r_lp) :
    let floor := params.γ * (r_lp - il_max)
    floor > 0 := by
  simp only
  apply mul_pos params.h_γ_pos
  linarith

/-- Numerical instance: γ=0.20, r_LP=0.20, IL_max=0.05 gives floor = 3% -/
example : (0.20 : ℝ) * (0.20 - 0.05) = 0.03 := by norm_num

/-- The floor is monotone increasing in γ -/
theorem floor_mono_gamma
    (γ₁ γ₂ r_lp il_max : ℝ)
    (_h1 : 0 < γ₁) (h2 : γ₁ ≤ γ₂)
    (h_net : 0 < r_lp - il_max) :
    γ₁ * (r_lp - il_max) ≤ γ₂ * (r_lp - il_max) := by
  apply mul_le_mul_of_nonneg_right h2 (le_of_lt h_net)

end CHAOS
