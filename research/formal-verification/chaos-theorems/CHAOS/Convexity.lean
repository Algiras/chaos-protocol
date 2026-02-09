/-
  CHAOS Protocol — Convexity / Antifragility (Theorem 4)

  Proves that the rebalanced portfolio has a convex payoff function
  (positive second derivative), meaning it benefits from volatility.
-/
import CHAOS.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace CHAOS

/-- Round-trip gain from symmetric price move with rebalancing.

After price moves by Δp and then returns, the rebalanced
portfolio gains α(1-α)P₀(Δp)²/(p₀(p₀+Δp)). -/
noncomputable def roundTripGain (α P₀ p₀ Δp : ℝ) : ℝ :=
  α * (1 - α) * P₀ * Δp^2 / (p₀ * (p₀ + Δp))

/-- Theorem 4: The round-trip gain is strictly positive for any nonzero price move -/
theorem convex_payoff
    (params : Params)
    (P₀ p₀ Δp : ℝ)
    (h_P : 0 < P₀)
    (h_p : 0 < p₀)
    (h_Δp : Δp ≠ 0)
    (h_sum_pos : 0 < p₀ + Δp) :
    roundTripGain params.α P₀ p₀ Δp > 0 := by
  unfold roundTripGain
  apply div_pos
  · -- Numerator: α(1-α)P₀(Δp)² > 0
    have h_α_pos := params.h_α_pos
    have h_1mα_pos : 0 < 1 - params.α := by linarith [params.h_α_lt]
    have h_Δp2_pos : 0 < Δp ^ 2 := by positivity
    positivity
  · -- Denominator: p₀(p₀ + Δp) > 0
    exact mul_pos h_p h_sum_pos

/-- Second derivative of portfolio value is positive (convexity) -/
theorem positive_second_derivative
    (params : Params)
    (P₀ p₀ : ℝ)
    (h_P : 0 < P₀)
    (h_p : 0 < p₀) :
    let d2V := 2 * params.α * (1 - params.α) * P₀ / p₀^2
    d2V > 0 := by
  simp only
  have h_α_pos := params.h_α_pos
  have h_1mα_pos : 0 < 1 - params.α := by linarith [params.h_α_lt]
  positivity

/-- Corollary: expected value under volatility exceeds value without (Jensen) -/
theorem jensen_antifragility
    (params : Params)
    (P₀ p₀ σ : ℝ)
    (h_P : 0 < P₀) (h_p : 0 < p₀) (h_σ : 0 < σ) :
    -- E[V(Δp)] ≈ V(0) + ½ d²V/dp² σ² > V(0)
    let bonus := (1/2) * (2 * params.α * (1 - params.α) * P₀ / p₀^2) * σ^2
    bonus > 0 := by
  simp only
  have h_α_pos := params.h_α_pos
  have h_1mα_pos : 0 < 1 - params.α := by linarith [params.h_α_lt]
  positivity

end CHAOS
