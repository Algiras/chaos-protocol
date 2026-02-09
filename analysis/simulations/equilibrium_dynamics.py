"""
Dynamic Equilibrium Analysis

Explores stability and time-to-equilibrium questions:
1. Perturbation recovery — how fast does the system recover from shocks?
2. Dynamic margin competition — what if operators adapt margins over time?
3. Network growth — what happens as total stake and pool count grows?
4. Nakamoto coefficient over time — centralization dynamics

Maps to multiple Lean sorry's:
  - nash_equilibrium_exists (convergence → existence)
  - nash_equilibrium_centralization_tradeoff (Nakamoto coefficient)
  - bounded_rationality_equilibrium_existence (approximate dynamics)
"""

import numpy as np
import matplotlib.pyplot as plt
from cardano_staking_sim import (PoolParams, StakePool, pool_rewards,
                                  operator_rewards, delegator_reward_per_ada)
import os


def simulate_perturbation_recovery(params: PoolParams, n_pools: int = 50,
                                    n_delegators: int = 1000,
                                    n_epochs: int = 300,
                                    shock_epoch: int = 100,
                                    shock_fraction: float = 0.3) -> dict:
    """
    1. Let the system reach equilibrium.
    2. At shock_epoch, randomly reassign shock_fraction of delegators.
    3. Measure recovery time.
    """
    rng = np.random.default_rng(42)
    pledges = rng.uniform(0.001 * params.z, 0.3 * params.z, n_pools)
    margins = rng.uniform(0.01, 0.05, n_pools)
    delegator_stakes = rng.exponential(50_000, n_delegators)
    delegator_pools = rng.integers(0, n_pools, n_delegators)

    history = {"epoch": [], "switches": [], "gini": [], "herfindahl": []}

    for epoch in range(n_epochs):
        # Apply shock
        if epoch == shock_epoch:
            n_shock = int(shock_fraction * n_delegators)
            shocked = rng.choice(n_delegators, n_shock, replace=False)
            delegator_pools[shocked] = rng.integers(0, n_pools, n_shock)

        pool_stakes = np.zeros(n_pools)
        for d in range(n_delegators):
            pool_stakes[delegator_pools[d]] += delegator_stakes[d]
        total_stakes = pool_stakes + pledges

        returns_per_ada = np.zeros(n_pools)
        for p in range(n_pools):
            pool = StakePool(id=p, pledge=pledges[p], stake=total_stakes[p],
                             margin=margins[p])
            returns_per_ada[p] = delegator_reward_per_ada(pool, pool_rewards(params, pool))

        switches = 0
        for d in range(n_delegators):
            best = np.argmax(returns_per_ada)
            if best != delegator_pools[d]:
                delegator_pools[d] = best
                switches += 1

        s = total_stakes / total_stakes.sum()
        gini = np.sum(np.abs(np.subtract.outer(s, s))) / (2 * n_pools * np.sum(s))
        hhi = np.sum(s ** 2)

        history["epoch"].append(epoch)
        history["switches"].append(switches)
        history["gini"].append(float(gini))
        history["herfindahl"].append(float(hhi))

    # Find recovery time: first epoch after shock where switches = 0
    recovery_time = None
    for i, e in enumerate(history["epoch"]):
        if e > shock_epoch and history["switches"][i] == 0:
            recovery_time = e - shock_epoch
            break

    history["shock_epoch"] = shock_epoch
    history["recovery_time"] = recovery_time
    return history


def simulate_margin_competition(params: PoolParams, n_pools: int = 30,
                                 n_delegators: int = 500,
                                 n_epochs: int = 200) -> dict:
    """
    Operators dynamically adjust margins: if a pool is losing delegators,
    it lowers margin. If winning, it raises margin (profit-taking).
    """
    rng = np.random.default_rng(42)
    pledges = rng.uniform(0.01 * params.z, 0.2 * params.z, n_pools)
    margins = np.full(n_pools, 0.05)  # Start everyone at 5%
    delegator_stakes = rng.exponential(50_000, n_delegators)
    delegator_pools = rng.integers(0, n_pools, n_delegators)

    history = {"epoch": [], "mean_margin": [], "std_margin": [],
               "min_margin": [], "n_active": []}
    prev_pool_stakes = np.zeros(n_pools)

    for epoch in range(n_epochs):
        pool_stakes = np.zeros(n_pools)
        for d in range(n_delegators):
            pool_stakes[delegator_pools[d]] += delegator_stakes[d]
        total_stakes = pool_stakes + pledges

        # Operators adjust margins
        if epoch > 0:
            for p in range(n_pools):
                delta_stake = pool_stakes[p] - prev_pool_stakes[p]
                if delta_stake < -1000:  # losing stake
                    margins[p] = max(0.005, margins[p] - 0.002)
                elif delta_stake > 1000:  # gaining stake
                    margins[p] = min(0.10, margins[p] + 0.001)
        prev_pool_stakes = pool_stakes.copy()

        returns_per_ada = np.zeros(n_pools)
        for p in range(n_pools):
            pool = StakePool(id=p, pledge=pledges[p], stake=total_stakes[p],
                             margin=margins[p])
            returns_per_ada[p] = delegator_reward_per_ada(pool, pool_rewards(params, pool))

        for d in range(n_delegators):
            delegator_pools[d] = np.argmax(returns_per_ada)

        n_active = np.sum(pool_stakes > params.z * 0.01)
        history["epoch"].append(epoch)
        history["mean_margin"].append(float(np.mean(margins)))
        history["std_margin"].append(float(np.std(margins)))
        history["min_margin"].append(float(np.min(margins)))
        history["n_active"].append(int(n_active))

    return history


def simulate_network_growth(base_params: PoolParams,
                             growth_epochs: int = 100,
                             final_multiplier: float = 3.0) -> dict:
    """
    Simulate network growing from current size to 3× over time.
    New pools and delegators join. Track Nakamoto coefficient.
    """
    rng = np.random.default_rng(42)
    history = {"epoch": [], "total_stake": [], "n_pools": [],
               "nakamoto_coeff": [], "gini": []}

    # Start with 30 pools
    n_pools_start = 30
    pledges = list(rng.uniform(0.001 * base_params.z, 0.3 * base_params.z, n_pools_start))
    margins = list(rng.uniform(0.01, 0.05, n_pools_start))

    n_delegators = 500
    delegator_stakes = list(rng.exponential(50_000, n_delegators))
    delegator_pools = list(rng.integers(0, n_pools_start, n_delegators))

    for epoch in range(growth_epochs):
        growth_factor = 1 + (final_multiplier - 1) * epoch / growth_epochs
        current_total = base_params.total_stake * growth_factor
        params = PoolParams(
            a0=base_params.a0, k=base_params.k,
            total_stake=current_total, R=base_params.R * growth_factor
        )

        # Add new pools and delegators proportionally
        if epoch % 10 == 0 and epoch > 0:
            n_new_pools = max(1, int(2 * growth_factor))
            for _ in range(n_new_pools):
                pledges.append(rng.uniform(0.001 * params.z, 0.2 * params.z))
                margins.append(rng.uniform(0.01, 0.04))
            n_new_del = max(5, int(20 * growth_factor))
            for _ in range(n_new_del):
                delegator_stakes.append(rng.exponential(60_000))
                delegator_pools.append(rng.integers(0, len(pledges)))

        n_pools = len(pledges)
        pool_stakes = np.zeros(n_pools)
        for d in range(len(delegator_pools)):
            if delegator_pools[d] < n_pools:
                pool_stakes[delegator_pools[d]] += delegator_stakes[d]

        total_stakes = pool_stakes + np.array(pledges)

        returns_per_ada = np.zeros(n_pools)
        for p in range(n_pools):
            pool = StakePool(id=p, pledge=pledges[p], stake=total_stakes[p],
                             margin=margins[p])
            returns_per_ada[p] = delegator_reward_per_ada(pool, pool_rewards(params, pool))

        for d in range(len(delegator_pools)):
            delegator_pools[d] = int(np.argmax(returns_per_ada))

        # Nakamoto coefficient: min pools controlling >50% of stake
        s = np.sort(total_stakes)[::-1]
        cumsum = np.cumsum(s) / s.sum()
        nakamoto = int(np.searchsorted(cumsum, 0.5) + 1)

        s_norm = total_stakes / total_stakes.sum()
        gini = np.sum(np.abs(np.subtract.outer(s_norm, s_norm))) / (
            2 * n_pools * np.sum(s_norm))

        history["epoch"].append(epoch)
        history["total_stake"].append(float(current_total))
        history["n_pools"].append(n_pools)
        history["nakamoto_coeff"].append(nakamoto)
        history["gini"].append(float(gini))

    return history


def plot_dynamics(perturbation, margin_comp, growth, output_dir: str):
    os.makedirs(output_dir, exist_ok=True)
    fig, axes = plt.subplots(2, 3, figsize=(18, 10))
    fig.suptitle("Dynamic Equilibrium Analysis\n"
                 "Stability, competition, and growth dynamics",
                 fontsize=14, fontweight="bold")

    # --- 1. Perturbation Recovery ---
    ax = axes[0, 0]
    ax.plot(perturbation["epoch"], perturbation["switches"],
            color="#2563eb", linewidth=1.5)
    ax.axvline(perturbation["shock_epoch"], color="red", linewidth=2,
               linestyle="--", label=f"Shock (30% reassigned)")
    if perturbation["recovery_time"]:
        ax.annotate(f"Recovery: {perturbation['recovery_time']} epochs",
                    xy=(perturbation["shock_epoch"] + perturbation["recovery_time"], 0),
                    fontsize=9, color="green", fontweight="bold")
    ax.set_xlabel("Epoch")
    ax.set_ylabel("Delegator switches")
    ax.set_title("Perturbation Recovery")
    ax.legend()
    ax.grid(alpha=0.3)

    # --- 2. HHI Around Shock ---
    ax = axes[0, 1]
    ax.plot(perturbation["epoch"], [h * 10000 for h in perturbation["herfindahl"]],
            color="#10b981", linewidth=1.5)
    ax.axvline(perturbation["shock_epoch"], color="red", linewidth=2, linestyle="--")
    ax.set_xlabel("Epoch")
    ax.set_ylabel("HHI × 10000")
    ax.set_title("Concentration Around Shock")
    ax.grid(alpha=0.3)

    # --- 3. Margin Competition ---
    ax = axes[0, 2]
    ax.plot(margin_comp["epoch"], [m * 100 for m in margin_comp["mean_margin"]],
            color="#2563eb", linewidth=2, label="Mean margin")
    ax.fill_between(
        margin_comp["epoch"],
        [(m - s) * 100 for m, s in zip(margin_comp["mean_margin"], margin_comp["std_margin"])],
        [(m + s) * 100 for m, s in zip(margin_comp["mean_margin"], margin_comp["std_margin"])],
        alpha=0.2, color="#2563eb"
    )
    ax.plot(margin_comp["epoch"], [m * 100 for m in margin_comp["min_margin"]],
            color="#dc2626", linewidth=1, linestyle="--", label="Min margin")
    ax.set_xlabel("Epoch")
    ax.set_ylabel("Margin (%)")
    ax.set_title("Margin Competition (race to bottom?)")
    ax.legend()
    ax.grid(alpha=0.3)

    # --- 4. Network Growth: Pool Count ---
    ax = axes[1, 0]
    ax.plot(growth["epoch"], growth["n_pools"], color="#8b5cf6", linewidth=2)
    ax.set_xlabel("Epoch")
    ax.set_ylabel("Number of pools")
    ax.set_title("Pool Growth Over Time")
    ax.grid(alpha=0.3)

    # --- 5. Nakamoto Coefficient ---
    ax = axes[1, 1]
    ax.plot(growth["epoch"], growth["nakamoto_coeff"], color="#dc2626", linewidth=2)
    ax.set_xlabel("Epoch")
    ax.set_ylabel("Nakamoto coefficient")
    ax.set_title("Nakamoto Coefficient\n(min pools for >50% control)")
    ax.grid(alpha=0.3)

    # --- 6. Gini During Growth ---
    ax = axes[1, 2]
    ax.plot(growth["epoch"], growth["gini"], color="#f59e0b", linewidth=2)
    ax.set_xlabel("Epoch")
    ax.set_ylabel("Gini coefficient")
    ax.set_title("Stake Inequality During Growth")
    ax.grid(alpha=0.3)

    plt.tight_layout(rect=[0, 0, 1, 0.93])
    plt.savefig(os.path.join(output_dir, "equilibrium_dynamics.png"),
                dpi=200, bbox_inches="tight")
    plt.close()
    print(f"Saved: {output_dir}/equilibrium_dynamics.png")


def main():
    params = PoolParams()
    print("=" * 60)
    print("Dynamic Equilibrium Analysis")
    print("=" * 60)

    print("\n[1/3] Perturbation recovery...")
    perturbation = simulate_perturbation_recovery(params)
    print(f"  Recovery time: {perturbation['recovery_time']} epochs after 30% shock")

    print("[2/3] Margin competition...")
    margin_comp = simulate_margin_competition(params)
    print(f"  Final mean margin: {margin_comp['mean_margin'][-1]*100:.2f}%")
    print(f"  Final min margin: {margin_comp['min_margin'][-1]*100:.2f}%")

    print("[3/3] Network growth dynamics...")
    growth = simulate_network_growth(params)
    print(f"  Final Nakamoto coefficient: {growth['nakamoto_coeff'][-1]}")
    print(f"  Final Gini: {growth['gini'][-1]:.4f}")

    print("\nGenerating plots...")
    plot_dynamics(perturbation, margin_comp, growth, "simulations/results")

    print("\n" + "=" * 60)
    print("KEY FINDINGS:")
    print("=" * 60)
    rec = perturbation['recovery_time']
    print(f"  Perturbation recovery: {'Fast (' + str(rec) + ' epochs)' if rec else 'Slow (>200 epochs)'}")
    print(f"  Margin race-to-bottom: Min margin → {margin_comp['min_margin'][-1]*100:.2f}%")
    print(f"  Nakamoto coefficient:  {growth['nakamoto_coeff'][-1]} pools for 50% control")
    print(f"  Centralization:        Gini = {growth['gini'][-1]:.4f}")
    print("=" * 60)


if __name__ == "__main__":
    main()
