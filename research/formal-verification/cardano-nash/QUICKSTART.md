# Quick Start Guide

## Installation

### 1. Install Lean 4

```bash
# Install elan (Lean version manager)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Follow the prompts, then restart your terminal

# Verify installation
elan --version
```

### 2. Setup the Project

```bash
cd cardano-nash-verification

# Download mathlib (this may take a while)
lake exe cache get

# Build the project
lake build
```

### 3. Open in VS Code (Recommended)

```bash
# Install Lean 4 VS Code extension
code --install-extension leanprover.lean4

# Open the project
code .
```

## Working with the Formalization

### File Structure

- `CardanoNash/Basic.lean` - Start here: basic types and definitions
- `CardanoNash/Rewards.lean` - Reward calculation (this is the core!)
- `CardanoNash/Game.lean` - Game theory model
- `CardanoNash/Nash.lean` - Main theorems to prove
- `CardanoNash/Verification.lean` - Test cases and edge cases

### Key Theorems to Work On

#### 1. **Most Important**: Pool Splitting Prevention

```lean
-- File: CardanoNash/Nash.lean, line ~67
theorem no_profitable_splitting
    (params : PoolParams)
    (h_a0 : pledge_prevents_splitting params.pledge_influence.value)
    (pool : StakePool)
    (h_valid : pool.isValid)
    (epoch_rewards : ℝ)
    (h_positive : 0 < epoch_rewards) :
    ∀ (n_splits : ℕ) (h_n : 0 < n_splits),
      ∀ (split_pools : List StakePool),
        split_pools.length = n_splits →
        (split_pools.map (·.stake.val)).sum = pool.stake.val →
        (split_pools.map (·.pledge.val)).sum = pool.pledge.val →
        ¬splittingProfitable params pool split_pools epoch_rewards :=
by
  sorry  -- TODO: Prove this!
```

**How to approach**:
1. Expand the definitions of `splittingProfitable`, `operatorUtility`, `poolRewards`
2. Show that the reward function is concave in pledge
3. Use Jensen's inequality: f(x) > f(x₁) + f(x₂) when f is strictly concave

#### 2. Main Nash Equilibrium Existence

```lean
-- File: CardanoNash/Nash.lean, line ~103
theorem nash_equilibrium_exists
    (params : PoolParams)
    (h_a0 : pledge_prevents_splitting params.pledge_influence.value)
    (n_pools : ℕ)
    (n_delegators : ℕ)
    (epoch_rewards : ℝ)
    (h_positive : 0 < epoch_rewards) :
    ∃ (equilibrium : SystemState n_pools n_delegators),
      isNashEquilibrium params equilibrium epoch_rewards :=
by
  sorry  -- This depends on #1
```

**Dependencies**:
- Needs `no_profitable_splitting` to be proven first
- Uses Brouwer's fixed point theorem (available in mathlib)
- Requires showing the best response function is continuous

#### 3. Finding the Phase Transition

```lean
-- File: CardanoNash/Nash.lean, line ~120
theorem splitting_below_threshold
    (params : PoolParams)
    (h_a0 : params.pledge_influence.value < 0.1)
    (pool : StakePool)
    (epoch_rewards : ℝ) :
    ∃ (split_pools : List StakePool),
      splittingProfitable params pool split_pools epoch_rewards :=
by
  sorry  -- Construct a counterexample!
```

**Strategy**:
1. Use `a0 = 0.09` (just below threshold)
2. Construct a specific pool with high stake, medium pledge
3. Show splitting into 2 pools increases total rewards
4. This should be *calculable* with concrete numbers

## Lean 4 Crash Course

### Basic Proof Tactics

```lean
theorem example (h : P) : P := by
  exact h                    -- Use hypothesis directly

theorem example2 (h : P → Q) (hp : P) : Q := by
  apply h                    -- Apply function
  exact hp                   -- Prove subgoal

theorem example3 (h1 : P) (h2 : Q) : P ∧ Q := by
  constructor               -- Split conjunction
  · exact h1                -- First subgoal
  · exact h2                -- Second subgoal

theorem example4 : P ∨ Q := by
  left                      -- Choose left side of disjunction
  sorry                     -- Or: right

theorem example5 : ∃ x, P x := by
  use 5                     -- Provide witness
  sorry                     -- Prove P 5
```

### Working with Real Numbers

```lean
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

-- Prove inequality
theorem reward_positive (r : ℝ) (h : r > 0) : r + 1 > 1 := by
  linarith  -- Linear arithmetic tactic

-- Use calculus
theorem derivative_example (f : ℝ → ℝ) :
  deriv f x = 0 → IsLocalMin f x := by
  sorry
```

### Debugging Tips

1. **See goal state**: Place cursor after `by`, VS Code shows current goal
2. **Check types**: Hover over any term to see its type
3. **Try auto-tactics first**:
   ```lean
   by simp          -- Simplification
   by ring          -- Ring arithmetic
   by linarith      -- Linear arithmetic
   by omega         -- Integer linear arithmetic
   ```
4. **Split complex proofs**: Use `have` to state intermediate results
   ```lean
   theorem big_proof : Complicated := by
     have step1 : Simple := by sorry
     have step2 : AlsoSimple := by sorry
     sorry  -- Combine step1 and step2
   ```

## Computational Verification

Lean 4 can **compute** with your definitions!

```lean
-- Define concrete parameters
def cardano_params : PoolParams := {
  pledge_influence := { value := 0.3, nonneg := by norm_num, bounded := by norm_num }
  target_pools := { value := 500, positive := by norm_num }
  saturation := { value := 68000000, positive := by norm_num }
  total_stake := ⟨34000000000, by norm_num⟩
}

-- Create a test pool
def test_pool : StakePool := {
  id := 1
  pledge := ⟨1000000, by norm_num⟩
  stake := ⟨60000000, by norm_num⟩
  margin := 0.02
  cost := 340
  margin_valid := by norm_num
  cost_nonneg := by norm_num
}

-- Compute rewards
#eval poolRewards cardano_params test_pool 1000000
```

## Research Workflow

### Finding Structural Issues

1. **Start with simple cases**:
   ```lean
   -- What if there's only 1 pool?
   example : isNashEquilibrium params (onePoolState) epoch_rewards := by sorry

   -- What if all pools have zero pledge?
   example : ∀ i, (state.pools i).pledge.val = 0 → False := by sorry
   ```

2. **Test edge cases**:
   - Very small a₀ (like 0.01)
   - Very large k (like 10000)
   - Extreme pledge values
   - Saturation edge cases

3. **Look for contradictions**:
   ```lean
   -- Try to prove something false
   theorem impossible : False := by
     have h1 : equilibrium_exists := sorry
     have h2 : equilibrium_is_centralized := sorry
     have h3 : centralized → ¬secure := sorry
     -- If we can derive False, we found an inconsistency!
     sorry
   ```

### Contributing Your Findings

When you prove or disprove a theorem:

1. Remove the `sorry`
2. Add a comment explaining the key insight
3. Add test cases showing it works
4. Document any surprising results in `ANALYSIS.md`

## Resources

- [Lean 4 Manual](https://lean-lang.org/lean4/doc/)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
- [Mathlib Docs](https://leanprover-community.github.io/mathlib4_docs/)
- [Zulip Chat](https://leanprover.zulipchat.com/) - Ask questions here!

## Common Issues

### Build fails with "unknown package"
```bash
lake update
lake build
```

### VS Code doesn't show proof state
- Restart Lean server: Cmd/Ctrl + Shift + P → "Lean 4: Restart Server"

### "Tactic 'sorry' is deprecated"
Change `sorry` to `admit` (they do the same thing but `admit` is preferred)

## Next Steps

1. **Read `ANALYSIS.md`** to understand the structural issues
2. **Try proving `reward_function_monotone_in_pledge`** in `Verification.lean` (easier warm-up)
3. **Work on `no_profitable_splitting`** (the main challenge)
4. **Join the discussion** on Lean Zulip or Cardano forums

Good luck! 🚀
