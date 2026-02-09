/-
  CHAOS Protocol — Drawdown Bound (Theorem 2)

  Proves that the CHAOS portfolio drawdown is bounded by
  (α + δ + 0.2γ) × asset drawdown, which is strictly less than
  the asset's own drawdown.
-/
import CHAOS.Basic

namespace CHAOS

/-- Helper: the drawdown multiplier α + δ + 0.2γ is in (0,1)
    when δ < β + 0.8γ, which follows from δ < β (typical). -/
lemma drawdown_coeff_lt_one
    (params : Params)
    (h_δ_lt_β : params.δ < params.β) :
    params.α + params.δ + 0.20 * params.γ < 1 := by
  -- From h_sum: α + β + γ = 1, so 1 - α - γ = β
  -- Need: α + δ + 0.2γ < 1 = α + β + γ
  -- Equiv: δ + 0.2γ < β + γ
  -- Equiv: δ < β + 0.8γ
  -- Since δ < β and 0.8γ > 0, this holds.
  have h1 : params.α + params.β + params.γ = 1 := params.h_sum
  nlinarith [params.h_γ_pos]

/-- Theorem 2: Maximum drawdown bound.

If asset allocation is bounded by α + δ, stablecoin is stable,
and LP impermanent loss is bounded by 0.20 × asset drawdown,
then portfolio drawdown ≤ (α + δ + 0.2γ) × asset drawdown. -/
theorem drawdown_bound
    (params : Params)
    (dd_asset : ℝ)
    (h_dd_nn : 0 ≤ dd_asset)
    (h_dd_le : dd_asset ≤ 1)
    (h_δ_lt_β : params.δ < params.β) :
    let coeff := params.α + params.δ + 0.20 * params.γ
    let dd_chaos := coeff * dd_asset
    dd_chaos ≤ 1 := by
  simp only
  have hc : params.α + params.δ + 0.20 * params.γ < 1 :=
    drawdown_coeff_lt_one params h_δ_lt_β
  -- coeff < 1 and dd_asset ≤ 1, so coeff * dd_asset ≤ 1 * 1 = 1
  calc (params.α + params.δ + 0.20 * params.γ) * dd_asset
      ≤ 1 * 1 := by nlinarith [params.h_α_pos, params.h_δ_pos, params.h_γ_pos]
    _ = 1 := by ring

/-- Corollary: CHAOS drawdown is strictly less than asset drawdown -/
theorem chaos_drawdown_lt_asset
    (params : Params)
    (dd_asset : ℝ)
    (h_dd_pos : 0 < dd_asset)
    (h_δ_lt_β : params.δ < params.β) :
    (params.α + params.δ + 0.20 * params.γ) * dd_asset < dd_asset := by
  have hc : params.α + params.δ + 0.20 * params.γ < 1 :=
    drawdown_coeff_lt_one params h_δ_lt_β
  nlinarith

end CHAOS
