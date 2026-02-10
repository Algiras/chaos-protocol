# CHAOS Protocol

**Antifragile Volatility Harvesting on Cardano** — Research & Formal Verification

[![License: Custom](https://img.shields.io/badge/License-Custom-red.svg)](LICENSE)
[![Lean 4 Verified](https://img.shields.io/badge/lean4-verified-brightgreen)](research/formal-verification/)
[![Aiken v1.1](https://img.shields.io/badge/aiken-v1.1.21-orange)](contracts/)

## Overview

CHAOS is a volatility harvesting protocol that generates positive expected returns by rebalancing between volatile and stable assets. This repository contains:

- **Formal verification** (Lean 4 proofs) ✅ Complete
- **Research papers** (whitepaper with full analysis) ✅ Complete
- **Smart contracts** (Aiken validators for Cardano) 🚧 In development
- **Backtests & simulations** (historical performance, Monte Carlo stress tests) ✅ Complete
- **Marketing website** (Next.js static site) ✅ Live at [chaosprotocol.io](https://chaosprotocol.io)

## Project Status

| Component | Status | Description |
|-----------|--------|-------------|
| Research & Math | ✅ Complete | 4 theorems formally verified in Lean 4 |
| Backtests | ✅ Complete | Multi-asset historical validation (2019-2024) |
| Simulations | ✅ Complete | Stress tests, equilibrium analysis, feasibility studies |
| Marketing Site | ✅ Live | Static site deployed to chaosprotocol.io |
| Smart Contracts | 🚧 Planned | Aiken validators (see [ARCHITECTURE.md](docs/ARCHITECTURE.md)) |
| Dashboard/App | 🚧 Planned | Blockchain-integrated UI (see [ARCHITECTURE.md](docs/ARCHITECTURE.md)) |
| Mainnet Launch | 📅 Future | Pending contract development and audit |

**Current Phase:** Research & validation complete. Smart contract development planned for Q2 2026.

## Research Publications

- [**Whitepaper**](research/papers/whitepaper/_book/CHAOS-Token--Antifragile-Volatility-Harvesting-on-Cardano.pdf) — Full technical specification (47 pages)
- [**Formal Verification**](research/formal-verification/) — Lean 4 theorem proofs source
- Additional papers (proof paper, investor brief) available on [chaosprotocol.io/research](https://chaosprotocol.io/research)

## Key Theorems (Formally Verified)

1. **Theorem 1 (Excess Return)**: Rebalancing generates positive expected excess return proportional to volatility squared
2. **Theorem 2 (Drawdown Bound)**: Maximum drawdown is provably bounded relative to HODL
3. **Theorem 3 (LP Floor)**: LP fee income exceeds impermanent loss
4. **Theorem 4 (Antifragility)**: Portfolio benefits from volatility (convex payoff)

See `research/formal-verification/chaos-theorems/CHAOS/` for complete proofs.

## Simulations & Analysis

### Backtests

Historical performance validation across 5 assets (ADA, BTC, ETH, SOL, DOT):

```bash
cd analysis/backtests
python backtest.py
```

### Simulations (Jupyter Notebooks)

Interactive notebooks with inline visualizations — click to view rendered results on GitHub:

| Notebook | Description |
|----------|-------------|
| [Stress Test](analysis/simulations/stress_test.ipynb) | Black swan event testing (COVID, Terra, FTX crashes) |
| [Equilibrium Dynamics](analysis/simulations/equilibrium_dynamics.ipynb) | Cardano staking equilibrium analysis |
| [Bitcoin Feasibility](analysis/simulations/bitcoin_feasibility.ipynb) | Bitcoin deployment feasibility study |
| [Cardano Staking Sim](analysis/simulations/cardano_staking_sim.ipynb) | Nash equilibrium simulations |
| [Deep Phase Transition](analysis/simulations/deep_phase_transition.ipynb) | Pool splitting profitability analysis |

To run locally:

```bash
cd analysis/simulations
pip install -r requirements.txt
jupyter notebook
```

## Smart Contracts

Aiken validators for on-chain treasury management:

```bash
cd contracts
aiken check
aiken build
```

Key validators:
- `chaos_vault.ak` — Treasury management with multi-sig
- `chaos_token.ak` — Token minting policy

## Marketing Website

Static Next.js site deployed to GitHub Pages:

```bash
cd site
pnpm install
pnpm run dev
```

Visit [chaosprotocol.io](https://chaosprotocol.io) for the live site.

## Architecture

```
chaos-protocol/
├── site/                      # Marketing website (Next.js)
├── shared/                    # Shared React components
├── contracts/                 # Aiken smart contracts
├── research/
│   ├── papers/                # Quarto research papers
│   └── formal-verification/   # Lean 4 proofs
├── analysis/
│   ├── backtests/             # Historical backtests
│   └── simulations/           # Jupyter notebooks
└── docs/                      # Architecture documentation
```

## Development

### Prerequisites

- Node.js 18+
- pnpm 8+
- Python 3.10+
- Aiken 1.1.21+
- Lean 4 (for formal verification)

### Install Dependencies

```bash
pnpm install
cd analysis/simulations && pip install -r requirements.txt
cd ../../research/formal-verification/chaos-theorems && lake build
```

### Run Tests

```bash
# Smart contracts
cd contracts && aiken check

# Python simulations
cd analysis/simulations && python stress_test.py

# Website
cd site && pnpm run build
```

## License

- **Code & Smart Contracts**: MIT License
- **Research Papers**: CC BY 4.0

## Links

- **Website**: [chaosprotocol.io](https://chaosprotocol.io)
- **Architecture Plan**: [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md)

## Citation

If you use this research, please cite:

```bibtex
@misc{chaos2026,
  title={CHAOS Protocol: Antifragile Volatility Harvesting on Cardano},
  author={CHAOS Protocol Team},
  year={2026},
  howpublished={\\url{https://chaosprotocol.io}},
  note={Formally verified in Lean 4}
}
```

---

**Built with**: Lean 4, Aiken, Next.js, Python, Cardano
