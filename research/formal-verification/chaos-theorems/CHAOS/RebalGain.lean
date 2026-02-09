/-
  CHAOS Protocol — Rebalancing Gain (Lemma 1 / Theorem 1)

  Proves that the rebalancing premium ½α(1-α)σ² is strictly positive,
  and is maximized at α = 0.5.
-/
import CHAOS.Basic

namespace CHAOS

/-- Lemma 1: Rebalancing premium per period.

For a portfolio with fraction α in a risky asset with
log-return variance σ², the rebalancing premium over
buy-and-hold is ½α(1-α)σ². -/
theorem rebalancing_premium
    (params : Params)
    (σ : ℝ)
    (h_σ : 0 < σ) :
    let premium := (1/2) * params.α * (1 - params.α) * σ^2
    premium > 0 := by
  simp only
  apply mul_pos
  · apply mul_pos
    · apply mul_pos
      · norm_num
      · exact params.h_α_pos
    · linarith [params.h_α_lt]
  · exact sq_pos_of_pos h_σ

/-- The rebalancing premium α(1-α) is maximized at α = 0.5 -/
theorem premium_maximized_at_half
    (_σ : ℝ) (_ : 0 < _σ)
    (α : ℝ) (_ : 0 < α) (_ : α < 1) :
    α * (1 - α) ≤ (1/2 : ℝ) * (1 - 1/2) := by
  -- α(1-α) ≤ 1/4 by AM-GM, with equality at α = 1/2
  nlinarith [sq_nonneg (α - 1/2)]

end CHAOS
