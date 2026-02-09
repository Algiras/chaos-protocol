# Cardano Nash Equilibrium Formal Verification

A Lean 4 formalization investigating whether Nash equilibrium truly exists in Cardano's proof-of-stake reward mechanism.

## 🎯 Project Goal

Formally verify (or find counterexamples to) the claim that Cardano's staking game has a **non-myopic Nash equilibrium** that converges to k equally-saturated stake pools.

Based on the paper: ["Reward Sharing Schemes for Stake Pools"](https://arxiv.org/abs/1807.11218) by Brünjes, Kiayias, Koutsoupias, and Stouka (2018).

## 🔍 What We're Investigating

### The Claim
Cardano's reward mechanism creates a Nash equilibrium where:
1. No delegator wants to switch pools
2. No operator wants to change their parameters
3. No operator profits from splitting their pool
4. The system converges to `k` pools (k ≈ 500 for Cardano)

### The Structural Issues We Found

Through literature review, we identified several **potential problems**:

1. **Centralization vs. Nash Equilibrium** ([CIP-24](https://cips.cardano.org/cip/CIP-24))
   - The Nash equilibrium goal (k fully saturated pools) conflicts with decentralization
   - "The stated goal of having k fully saturated pools and all other pools having no stake other than owner pledge goes against the Cardano goal of decentralization"

2. **Phase Transition Assumptions**
   - Research claims a₀ = 0.1 is a "phase transition" point where splitting becomes unprofitable
   - **This needs rigorous mathematical proof!**
   - What happens at a₀ = 0.09? 0.095? Is there a continuous or discontinuous transition?

3. **Non-Myopic Behavior Assumption**
   - The proof assumes all delegators are rational and non-myopic (long-term optimizers)
   - Real-world evidence suggests delegators choose pools based on brand, marketing, and social factors
   - Does bounded rationality break the equilibrium?

4. **MEV and Strategic Behavior**
   - The current model ignores Maximal Extractable Value (MEV)
   - Pool operators might have additional profit incentives not captured in the reward function

5. **Uniqueness of Equilibrium**
   - Multiple equilibria could exist, leading to coordination problems
   - Is the equilibrium unique or do multiple stable configurations exist?

## 📁 Project Structure

```
CardanoNash/
├── Basic.lean          # Core types: Stake, Pool, Parameters
├── Rewards.lean        # Reward calculation formalization
├── Game.lean           # Game theory: strategies, utilities, best responses
├── Nash.lean           # Nash equilibrium theorems and conjectures
└── Verification.lean   # Main verification goals and test cases
```

## 🚀 Setup

### Prerequisites

1. Install Lean 4:
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

2. Install mathlib:
```bash
lake exe cache get
```

3. Build the project:
```bash
lake build
```

## 🔬 Key Theorems to Prove (or Disprove!)

### 1. Pool Splitting Prevention

```lean
theorem no_profitable_splitting
    (params : PoolParams)
    (h_a0 : params.pledge_influence.value ≥ 0.1)
    (pool : StakePool)
    (epoch_rewards : ℝ) :
    ∀ (split_pools : List StakePool),
      ¬splittingProfitable params pool split_pools epoch_rewards
```

**Status**: ❌ Unproven - **This is the critical theorem!**

### 2. Nash Equilibrium Existence

```lean
theorem nash_equilibrium_exists
    (params : PoolParams)
    (h_a0 : pledge_prevents_splitting params.pledge_influence.value)
    (n_pools n_delegators : ℕ)
    (epoch_rewards : ℝ) :
    ∃ (equilibrium : SystemState n_pools n_delegators),
      isNashEquilibrium params equilibrium epoch_rewards
```

**Status**: ❌ Unproven - Depends on #1 and other assumptions

### 3. Phase Transition at a₀ = 0.1

```lean
theorem phase_transition_at_point_one
    (params : PoolParams) :
    params.pledge_influence.value < 0.1 →
    ∃ (pool : StakePool) (split : List StakePool),
      splittingProfitable params pool split epoch_rewards
```

**Status**: ❌ Unproven - Need to construct explicit counterexample

### 4. Centralization Trade-off

```lean
theorem nash_equilibrium_centralization_tradeoff
    (params : PoolParams)
    (equilibrium : SystemState params.target_pools.value n_delegators)
    (h_nash : isNashEquilibrium params equilibrium epoch_rewards) :
    -- Top k pools control >95% of stake
    (∃ threshold, threshold > 0.95 * params.total_stake.val ∧ ...)
```

**Status**: ⚠️ May be provable - Shows the **problem** with Nash equilibrium

## 🧪 Testing Strategy

### 1. Constructive Proofs
Try to prove the theorems from first principles using:
- Calculus (derivatives of reward function)
- Real analysis (continuity, limits)
- Game theory (best response dynamics)

### 2. Counterexample Search
If proofs fail, construct explicit counterexamples:
- Edge case parameter values
- Specific pool configurations that break assumptions
- Attack scenarios (Sybil, collusion, MEV)

### 3. Numerical Verification
Use Lean's computational capabilities to:
- Simulate best response dynamics
- Check convergence for specific parameters
- Verify phase transition numerically

## 📊 Current Status

| Component | Status | Notes |
|-----------|--------|-------|
| Basic types | ✅ Complete | Core definitions done |
| Reward function | ✅ Complete | Formalized from paper |
| Game theory model | ✅ Complete | Strategies, utilities defined |
| Nash equilibrium definition | ✅ Complete | Properly formalized |
| **Main theorems** | ❌ **Unproven** | **This is the work!** |
| Phase transition proof | ❌ Unproven | Critical gap |
| Splitting prevention | ❌ Unproven | Critical gap |
| Equilibrium existence | ❌ Unproven | Main goal |
| Uniqueness | ❌ Unproven | Open question |

## 🎓 Academic Context

### Key Papers

1. **[Reward Sharing Schemes for Stake Pools](https://arxiv.org/abs/1807.11218)** (2018)
   - Original paper claiming Nash equilibrium existence
   - **Main reference for this verification**

2. **[Ouroboros: A Provably Secure Proof-of-Stake Blockchain Protocol](https://eprint.iacr.org/2016/889.pdf)** (2017)
   - Introduces "approximate Nash equilibrium" for consensus
   - Block production game

3. **[Pool Splitting Behaviour and Equilibrium Properties](https://blogs.ed.ac.uk/blockchain/2022/04/19/pool-splitting-behaviour-and-equilibrium-properties-in-cardano-rewards-scheme/)** (2022)
   - Agent-based modeling study
   - **Found the a₀ = 0.1 phase transition**

4. **[CIP-24: Non-Centralizing Rankings](https://cips.cardano.org/cip/CIP-24)**
   - Identifies centralization problem with k-pool equilibrium
   - **Questions the desirability of the equilibrium**

### Existing Formalizations

- **Cardano Ledger in Agda**: [formal-ledger-specifications](https://github.com/IntersectMBO/formal-ledger-specifications)
  - Formalizes ledger rules, not game theory
  - Reward calculation is specified but economic properties not proven

- **Nash Equilibrium in Coq/Isabelle**: [arXiv:1709.02096](https://arxiv.org/abs/1709.02096)
  - General Nash equilibrium existence theorem
  - Can we apply it to Cardano's specific game?

## 🤝 Contributing

This is a research project. Key areas where help is needed:

1. **Proving the splitting prevention theorem** (hardest part!)
2. Formalizing the phase transition
3. Constructing counterexamples for edge cases
4. Connecting to existing game theory libraries in mathlib
5. Numerical verification and simulations

## 📝 License

This project is part of academic research into blockchain game theory.

## 🔗 References

- [Cardano Official](https://cardano.org/)
- [IOHK Research](https://iohk.io/en/research/)
- [Lean 4 Documentation](https://lean-lang.org/)
- [Mathlib Game Theory](https://leanprover-community.github.io/mathlib4_docs/)

---

**Note**: This formalization is a work in progress and represents an attempt to rigorously verify claims made in academic papers. Finding where proofs fail is as valuable as completing them!
