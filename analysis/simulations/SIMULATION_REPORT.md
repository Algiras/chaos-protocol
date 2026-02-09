# Cardano Staking Game Theory — Simulation Report

**Purpose**: Provide empirical evidence for the open research questions (`sorry` statements) in `cardano-nash-verification/` that cannot be resolved purely by the Lean 4 theorem prover.

---

## Mapping: Lean sorry → Simulation → Finding

### 1. Pool Splitting Profitability (`no_profitable_splitting`)

**Lean file**: `CardanoNash/Nash.lean:72`
**Status**: ⚠️ OPEN — the KEY unproven theorem

**Simulation**: Sweep a₀ from 0.01 to 0.5. For each value, check whether splitting a saturated pool into 2, 3, or 5 equal sub-pools yields higher operator rewards.

**Finding**: Splitting is **never profitable** in our simulation across all a₀ values tested (0.01–0.5) and pledge levels (1%–50% of saturation). The splitting advantage is consistently negative (-50% to -5%), meaning the single pool always dominates.

**Interpretation**: This is **stronger** than the Edinburgh claim (that a₀ ≥ 0.1 prevents splitting). Under the Brünjes et al. reward formula, the s/z pledge factor creates a superlinear penalty when pledge is diluted across sub-pools. This suggests `no_profitable_splitting` may hold for **all** a₀ > 0, not just a₀ ≥ 0.1.

**Implication for Lean proof**: The theorem is likely provable. The key insight is that `min(s,z)/z` appears multiplicatively — splitting pledge sublinearly reduces each pool's reward.

---

### 2. Reward Function Concavity (`reward_function_concave_in_stake`)

**Lean file**: `CardanoNash/Verification.lean:75`
**Status**: ⚠️ OPEN

**Simulation**: Plot pool rewards vs. stake from 0 to 2× saturation.

**Finding**: The reward function is **piecewise linear** — increasing linearly below saturation, then flat above. The marginal reward shows a sharp discontinuity at the saturation point (drops to near-zero). Technically, this is not "concave" in the smooth sense but shows **decreasing marginal returns** at the saturation boundary.

**Interpretation**: The `min(σ,z)` function makes the reward piecewise-linear rather than smoothly concave. The Lean theorem as stated (strict inequality on marginal reward) holds **at the saturation boundary** but needs careful handling of the linear region below saturation where marginal reward is constant.

**Implication for Lean proof**: The theorem should be reformulated. Below saturation, marginal reward is constant (not decreasing). At and above saturation, marginal reward drops to zero. The economically important property (can't gain by growing past saturation) holds.

---

### 3. Nash Equilibrium Existence (`nash_equilibrium_exists`)

**Lean file**: `CardanoNash/Nash.lean:117`
**Status**: ⚠️ OPEN

**Simulation**: Agent-based model with 50 pools and 1000 delegators. Each epoch, delegators switch to the pool with highest return per ADA.

**Finding**: The system converges to equilibrium within ~25 epochs (from ~800+ switches/epoch to 0). This is fast convergence. All 50 pools remain active, suggesting the equilibrium distributes stake across all available pools.

**Interpretation**: Empirically, best-response dynamics converge. This is consistent with equilibrium existence but does not prove it — convergence of a specific algorithm doesn't guarantee a mathematical fixed point exists.

**Implication for Lean proof**: Simulation supports the theorem. A potential proof strategy: show the potential function (sum of delegator utilities) is bounded and increases with each best-response move → must converge.

---

### 4. Equilibrium Uniqueness (`equilibrium_uniqueness`)

**Lean file**: `CardanoNash/Verification.lean:144`
**Status**: ⚠️ OPEN

**Simulation**: Run 10 trials from different random initial conditions. Compare final stake distributions.

**Finding**: Mean L2 distance between final states ≈ 0.028, max ≈ 0.048. The equilibrium is **approximately unique** (all trials converge to similar distributions) but not exactly so — there is small variation due to pool ordering and tie-breaking.

**Interpretation**: The equilibrium appears to be unique up to permutation of pools with similar parameters. The small variation comes from symmetry-breaking when pools have nearly identical returns.

**Implication for Lean proof**: Uniqueness likely holds modulo pool ordering. The 0.01 tolerance in the theorem may be too tight — 0.05 would match simulation evidence.

---

### 5. MEV Preserves Equilibrium (`mev_preserves_equilibrium`)

**Lean file**: `CardanoNash/Verification.lean:187`
**Status**: ❌ LIKELY FALSE

**Simulation**: Give top 20% of pools MEV revenue that allows them to lower margins. Test with MEV advantages of 0%, 5%, 10%, 20%, 50%.

**Finding**: At 20% MEV advantage, MEV-capable pools attract **31%** of total stake (vs. their "fair share" of 20%). HHI increases from 53.6 to 54.4. At 50% MEV, this rises further.

**Interpretation**: MEV **does break equilibrium**. Pools with MEV infrastructure can offer better returns, attracting disproportionate stake. This creates centralization pressure toward MEV-capable operators.

**Implication for Lean proof**: The `sorry` is correctly marked as ❌ LIKELY FALSE. The simulation provides a constructive counterexample: asymmetric MEV revenue breaks the symmetric equilibrium assumption.

---

### 6. Zero-Pledge Pool Viability (`zero_pledge_issue`)

**Lean file**: `CardanoNash/Nash.lean:147`
**Status**: ⚠️ OPEN

**Simulation**: Compute delegator return per ADA for pools with pledge from 0% to 100% of saturation.

**Finding**: Zero-pledge pools return **0.182 ADA per ADA staked** per epoch — this is **non-zero and viable**. However, it's lower than pools with 50%+ pledge (0.20+). The difference is modest (≈10%) suggesting the pledge incentive may be too weak to prevent low-pledge pools.

**Interpretation**: The simplified reward formula gives non-zero rewards for zero-pledge pools. The actual Cardano implementation may round differently, but economically, zero-pledge pools are viable — just slightly less attractive.

**Implication for Lean proof**: The disjunction `poolRewards params pool epoch_rewards = 0 ∨ ∃ issue` should resolve to the right disjunct (∃ issue): zero-pledge pools get rewards but create a potential Sybil vector.

---

### 7. Bounded Rationality (`bounded_rationality_equilibrium_existence`)

**Lean file**: `CardanoNash/Verification.lean` (near end)
**Status**: ⚠️ OPEN

**Simulation**: Same agent-based model but with Gaussian noise (σ=10% of mean return) added to perceived pool returns.

**Finding**: With noise, the system still converges but slower. All 50 pools remain active. Switches per epoch stabilize near a low but non-zero level (noisy delegators occasionally switch suboptimally). An **approximate equilibrium** emerges.

**Interpretation**: Bounded rationality doesn't destroy equilibrium — it makes it "fuzzy." The system oscillates in a small neighborhood of the rational equilibrium, consistent with the ε-Nash equilibrium concept.

**Implication for Lean proof**: The bounded rationality theorem is essentially trivially true (existential with True conclusion), but the simulation shows the *economically meaningful* version holds too.

---

### 8. Centralization Trade-off (`nash_equilibrium_centralization_tradeoff`)

**Lean file**: `CardanoNash/Nash.lean:164`
**Status**: ⚠️ OPEN

**Simulation**: Track how much stake the top pools control in equilibrium.

**Finding**: In the rational agent simulation, all pools remain active and stake is distributed across all 50 pools. The top-k pools (by the Lean definition) control >95% of stake trivially because all pools are in the "top k" when k=500 and we only simulate 50.

**Interpretation**: With realistic pool counts (50 vs. k=500), centralization is modest. But the CIP-24 concern remains: the equilibrium *structure* favors pools with higher pledge, creating a plutocratic tendency.

---

---

## Additional Analyses

### Deep Phase Transition (see `deep_phase_transition.py`)

Exhaustive search across all adversarial splitting strategies:
- **Equal split** (pledge shared equally, 2/3/5/10 way)
- **Sybil split** (all pledge in one pool, zero-pledge the rest)
- **Optimal split** (numerically optimized pledge distribution via Nelder-Mead)
- **Pledge sensitivity** (tested 0.1%–50% of saturation)

**Finding**: Splitting is **never profitable** regardless of a₀, number of splits, strategy, or pledge level. The advantage ranges from -50% to -90%. This is because the reward formula R(σ,s) = R/(1+a₀) × min(σ,z)/z × (a₀×s/z + min(σ,z)/z) penalizes pledge dilution superlinearly.

**Implication**: The "phase transition at a₀=0.1" may not exist. `no_profitable_splitting` may be provable for all a₀ > 0.

### Dynamic Equilibrium (see `equilibrium_dynamics.py`)

Three dynamic analyses:

1. **Perturbation recovery**: After randomly reassigning 30% of delegators, the system recovers to equilibrium in **1 epoch**. The system is extremely stable.

2. **Margin competition**: When operators dynamically adjust margins (lower when losing stake, raise when gaining), margins converge to ~4.8% — no destructive race to the bottom. The cost floor (340 ADA) acts as a natural lower bound.

3. **Network growth**: As the network grows 3× (new pools and delegators join), the Nakamoto coefficient improves from 10 to 18, and the Gini stays moderate (~0.35). This suggests the equilibrium is robust to growth.

---

## Proof Strategy Recommendations

| sorry | Approach | Difficulty |
|-------|----------|------------|
| `no_profitable_splitting` | Algebraic: show R(σ,s) is concave in splitting | Medium |
| `reward_function_concave` | Reformulate: piecewise-linear with min | Easy |
| `nash_equilibrium_exists` | Potential function argument | Hard |
| `equilibrium_uniqueness` | Modulo pool ordering; may need weaker statement | Medium |
| `mev_preserves_equilibrium` | **Disprove**: construct counterexample from simulation data | Easy |
| `zero_pledge_issue` | Compute: show R(σ,0) > 0 for σ > 0 | Easy |
| `centralization_tradeoff` | Sum-of-stakes argument: ∑σᵢ = total_stake | Easy |
| `phase_transition` | May not exist: simulation shows splitting always unprofitable | Revisit |

---

## How to Run

```bash
# Quick mode (~3s)
python simulations/cardano_staking_sim.py --quick

# Full mode (~4s)
python simulations/cardano_staking_sim.py

# Custom output directory
python simulations/cardano_staking_sim.py --output simulations/my_results
```

Output: `simulations/results/staking_simulation_results.png` (9-panel chart) and `simulation_results.json` (raw data).

```bash
# Deep phase transition analysis
python simulations/deep_phase_transition.py

# Dynamic equilibrium analysis
python simulations/equilibrium_dynamics.py
```

Output:
- `simulations/results/staking_simulation_results.png` — Main 9-panel results
- `simulations/results/deep_phase_transition.png` — Phase transition deep dive
- `simulations/results/equilibrium_dynamics.png` — Dynamic stability analysis
- `simulations/results/simulation_results.json` — Raw numerical data
