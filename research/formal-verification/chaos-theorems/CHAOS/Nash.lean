/-
  CHAOS Protocol — Nash Equilibrium (Theorem 5)

  Proves that holding CHAOS and following protocol are dominant
  strategies for token holders and operators respectively.
-/
import CHAOS.Basic

namespace CHAOS

/-- Strategy space for token holders -/
inductive HolderStrategy
  | Hold       -- Hold CHAOS long-term
  | Trade      -- Actively trade
  | Manipulate -- Attempt deposit/withdraw manipulation
  | Withdraw   -- Exit protocol

/-- Strategy space for operators -/
inductive OperatorStrategy
  | Follow  -- Follow protocol rules
  | Delay   -- Delay rebalancing
  | Deviate -- Deviate from target allocations

/-- Payoff function for token holders.
    Parameters: annual_return r, fee_share f, discount factor δ.

    Hold:       (r + f) / (1 - δ)    [discounted perpetuity]
    Trade:      r * 0.8               [friction-reduced, one period]
    Manipulate: -0.004                [net loss after tx costs]
    Withdraw:   0                     [exit, no future payoff] -/
noncomputable def holderPayoff
    (r f δ : ℝ) (s : HolderStrategy) : ℝ :=
  match s with
  | .Hold       => (r + f) / (1 - δ)
  | .Trade      => r * 0.8
  | .Manipulate => -0.004
  | .Withdraw   => 0

/-- Helper: if a > 0 and b > 0 then a / b ≥ a when b ≤ 1 -/
private lemma div_ge_self_of_pos_le_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hb1 : b ≤ 1) :
    a ≤ a / b := by
  rw [le_div_iff₀ hb]
  nlinarith

/-- Theorem 5a: Holding is the dominant strategy for token holders
    under realistic parameter assumptions. -/
theorem hold_is_dominant
    (r f δ : ℝ)
    (h_r : 0.05 < r)       -- annual return > 5%
    (h_f : 0 < f)           -- positive fee share
    (h_δ_pos : 0 < δ)
    (h_δ_lt : δ < 1)        -- discount factor < 1
    (_h_δ_bound : δ ≤ 0.95)  -- reasonable discount (≤ 95%)
    :
    ∀ s : HolderStrategy,
      holderPayoff r f δ .Hold ≥ holderPayoff r f δ s := by
  intro s
  cases s with
  | Hold => linarith
  | Trade =>
    simp only [holderPayoff]
    have h1 : 0 < 1 - δ := by linarith
    have h1' : 1 - δ ≤ 1 := by linarith
    have h_rf : 0 < r + f := by linarith
    -- (r+f)/(1-δ) ≥ r+f ≥ r > 0.8*r
    have h2 : r + f ≤ (r + f) / (1 - δ) := div_ge_self_of_pos_le_one h_rf h1 h1'
    linarith
  | Manipulate =>
    simp only [holderPayoff]
    have h1 : 0 < 1 - δ := by linarith
    have h2 : 0 < r + f := by linarith
    linarith [div_pos h2 h1]
  | Withdraw =>
    simp only [holderPayoff]
    have h1 : 0 < 1 - δ := by linarith
    have h2 : 0 < r + f := by linarith
    linarith [div_pos h2 h1]

/-- Payoff function for operators.
    Parameters: fee per rebalance f, rebalances per year n,
    staked collateral C, detection probability d, discount δ.

    Follow: f * n / (1 - δ)                         [discounted perpetuity]
    Delay:  f * 0.5                                  [reduced fee, one shot]
    Deviate: f - d * (C + f * n / (1 - δ))          [one-time gain minus expected slash] -/
noncomputable def operatorPayoff
    (f : ℝ) (n : ℕ) (C d δ : ℝ) (s : OperatorStrategy) : ℝ :=
  match s with
  | .Follow => f * n / (1 - δ)
  | .Delay  => f * 0.5
  | .Deviate => f - d * (C + f * n / (1 - δ))

/-- Theorem 5b: Following protocol is the dominant strategy for operators. -/
theorem follow_is_dominant_operator
    (f C d δ : ℝ) (n : ℕ)
    (h_f : 0 < f)
    (h_n : 1 ≤ n)           -- at least 1 rebalance/year
    (h_C : 0 < C)
    (h_d : 0.5 < d)         -- >50% detection probability
    (h_δ_pos : 0 < δ)
    (h_δ_lt : δ < 1)
    :
    ∀ s : OperatorStrategy,
      operatorPayoff f n C d δ .Follow ≥ operatorPayoff f n C d δ s := by
  intro s
  cases s with
  | Follow => linarith
  | Delay =>
    simp only [operatorPayoff]
    have h1 : 0 < 1 - δ := by linarith
    have h1' : 1 - δ ≤ 1 := by linarith
    have h_n_pos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
    have h_n_ge : (1:ℝ) ≤ ↑n := Nat.one_le_cast.mpr h_n
    have h_fn_pos : 0 < f * ↑n := mul_pos h_f h_n_pos
    -- f*n/(1-δ) ≥ f*n ≥ f*1 = f > f*0.5
    have h_ge : f * ↑n ≤ f * ↑n / (1 - δ) := div_ge_self_of_pos_le_one h_fn_pos h1 h1'
    nlinarith
  | Deviate =>
    -- Need: f*n/(1-δ) ≥ f - d*(C + f*n/(1-δ))
    -- Rearranging: f*n/(1-δ) + d*C + d*f*n/(1-δ) ≥ f
    -- All terms on left are positive, and f*n/(1-δ) ≥ f already
    simp only [operatorPayoff]
    have h1 : 0 < 1 - δ := by linarith
    have h1' : 1 - δ ≤ 1 := by linarith
    have h_n_pos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
    have h_fn_pos : 0 < f * ↑n := mul_pos h_f h_n_pos
    have h_fn_div : 0 < f * ↑n / (1 - δ) := div_pos h_fn_pos h1
    have h_d_pos : 0 < d := by linarith
    -- d*(C + f*n/(1-δ)) > 0, and f*n/(1-δ) ≥ f*n ≥ f
    have h_n_ge : (1:ℝ) ≤ ↑n := Nat.one_le_cast.mpr h_n
    have h_ge : f * ↑n ≤ f * ↑n / (1 - δ) := div_ge_self_of_pos_le_one h_fn_pos h1 h1'
    nlinarith [mul_pos h_d_pos (by linarith : 0 < C + f * ↑n / (1 - δ))]

end CHAOS
