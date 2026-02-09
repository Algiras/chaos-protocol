# CHAOS Architecture Plan: Blockchain Integration

**Status**: Plan — not yet implemented  
**Date**: February 2026

---

## Philosophy

> The server is an optimized cache for reducing API costs. All decisions, data, and state live on-chain. The UI is minimal.

This means:
1. **Cardano blockchain** is the source of truth for treasury state, proposals, votes, balances
2. **Next.js API routes** are a read cache — they poll Blockfrost/Koios, aggregate, and serve pre-computed responses
3. **Wallet (Mesh SDK)** handles all write operations — signing transactions directly from the browser
4. **No backend database** — the cache layer is stateless (in-memory or simple file cache, rebuilt from chain)

---

## Current State

| Component | Status |
|-----------|--------|
| Smart contracts (`chaos_vault.ak`, `chaos_token.ak`) | Specified, not implemented (only hello_world template exists) |
| API routes (`pages/api/`) | Specified, not implemented |
| Governance UI | Complete with mock data |
| Dashboard UI | Complete with mock data |
| Wallet integration | MeshProvider + CardanoWallet button only |
| Currency persistence | Done (localStorage keyed by wallet address) |
| Blockfrost API key | Preprod key exists in root `.env` |

---

## Architecture Overview

```
┌─────────────────────────────────────────────────────┐
│                    Browser (Next.js)                 │
│                                                     │
│  ┌───────────┐  ┌──────────┐  ┌──────────────────┐ │
│  │ Governance │  │Dashboard │  │ Time Machine     │ │
│  │ Page       │  │Page      │  │ Page (no chain)  │ │
│  └─────┬──┬──┘  └────┬──┬──┘  └──────────────────┘ │
│        │  │          │  │                            │
│        │  │   READS  │  │  WRITES                   │
│        │  │          │  │                            │
│  ┌─────▼──┼──────────▼──┼───┐                       │
│  │  React Query / SWR    │   │  useTreasury()       │
│  │  (client-side cache)  │   │  useProposals()      │
│  │                       │   │  useUserBalance()    │
│  └───────┬───────────────┘   │  useVote()           │
│          │                   └───┬──────────────────│
│          │                       │                   │
│  ┌───────▼───────┐  ┌───────────▼──────────┐       │
│  │ Next.js API   │  │ Mesh SDK             │       │
│  │ Routes (cache)│  │ (tx building + sign) │       │
│  └───────┬───────┘  └───────────┬──────────┘       │
└──────────┼──────────────────────┼───────────────────┘
           │ READ                 │ SUBMIT TX
           │                     │
    ┌──────▼──────┐       ┌──────▼──────┐
    │ Blockfrost  │       │ Cardano     │
    │ API (read)  │       │ Node        │
    └──────┬──────┘       │ (via wallet)│
           │              └─────────────┘
    ┌──────▼──────┐
    │  Cardano    │
    │  Blockchain │
    └─────────────┘
```

---

## Phase 1: Cache Layer + Read Hooks

### 1a. Blockfrost Service (`lib/blockfrost.ts`)

Thin wrapper around the Blockfrost API for Cardano queries.

```typescript
// lib/blockfrost.ts
import { BlockfrostProvider } from '@meshsdk/core';

const BLOCKFROST_KEY = process.env.BLOCKFROST_API_KEY;
const NETWORK = process.env.NEXT_PUBLIC_CARDANO_NETWORK || 'preprod';

export const blockfrost = new BlockfrostProvider(BLOCKFROST_KEY);

// Direct Blockfrost REST calls for things Mesh doesn't wrap
export async function fetchScriptUtxos(scriptHash: string) { ... }
export async function fetchAssetHolders(policyId: string) { ... }
export async function fetchTransactions(address: string) { ... }
```

### 1b. API Routes (Cache Layer)

Each route reads from Blockfrost, parses on-chain datum, and returns JSON. These follow the existing `API-SPECIFICATION.md` shapes.

| Route | Source | Cache TTL | Purpose |
|-------|--------|-----------|---------|
| `GET /api/treasury/state` | Treasury vault UTXO datum | 60s | TVL, allocations, drift |
| `GET /api/treasury/history` | Indexed rebalance txs | 5min | Historical chart data |
| `GET /api/proposals` | Governance script UTXOs | 30s | All proposals + vote tallies |
| `GET /api/proposals/[id]` | Single UTXO | 30s | Proposal detail |
| `GET /api/user/[address]/balance` | Token balance query | 30s | CHAOS balance, portfolio value |
| `GET /api/prices/current` | DEX pool data + oracle | 30s | ADA/DJED prices |
| `GET /api/stats/overview` | Aggregated | 5min | Protocol-level stats |

**Cache strategy**: Simple in-memory `Map<string, { data, expiry }>`. No Redis/DB needed initially. Next.js API routes are long-lived in dev and serverless in prod — for serverless, set `Cache-Control` headers and rely on CDN edge cache (Vercel).

```
pages/api/
  treasury/
    state.ts          → reads vault UTXO, parses TreasuryDatum
    history.ts        → reads indexed rebalance txs
  proposals/
    index.ts          → reads all governance UTXOs
    [id].ts           → single proposal detail
    vote.ts           → (POST) validates + returns unsigned tx for client to sign
  user/
    [address]/
      balance.ts      → CHAOS token balance + portfolio value
  prices/
    current.ts        → DEX pool prices
  stats/
    overview.ts       → aggregated protocol stats
```

### 1c. Client Hooks (`hooks/useChain.ts`)

React hooks that call the cache API, with SWR or React Query for client-side caching + revalidation.

```typescript
// hooks/useChain.ts
export function useTreasuryState()    // → { data, isLoading, error }
export function useProposals(filters) // → { proposals, isLoading }
export function useProposal(id)       // → { proposal, isLoading }
export function useUserBalance(addr)  // → { balance, portfolio, pnl }
export function usePrices()           // → { ada, djed }
export function useProtocolStats()    // → { tvl, users, volume }
```

---

## Phase 2: Write Operations via Wallet

All writes go directly from browser → wallet → chain. The server is never in the write path.

### 2a. Transaction Builders (`lib/transactions/`)

Use Mesh SDK's `MeshTxBuilder` to construct transactions. The user's wallet signs them.

```
lib/transactions/
  deposit.ts      → build deposit tx (send ADA to vault, mint CHAOS)
  withdraw.ts     → build withdraw tx (burn CHAOS, receive ADA+DJED)
  vote.ts         → build vote tx (attach vote datum to governance UTXO)
  propose.ts      → build proposal tx (create governance UTXO with proposal datum)
```

#### Vote Transaction Flow

```
1. User clicks "Vote For" on proposal prop-001
2. UI calls buildVoteTx({ proposalId, choice: 'for', votingPower })
3. MeshTxBuilder constructs tx:
   - Input: governance script UTXO for prop-001
   - Output: same UTXO with updated vote tallies in datum
   - Signer: user's wallet address
4. wallet.signTx(unsignedTx) → user approves in wallet popup
5. wallet.submitTx(signedTx) → submitted to Cardano node
6. UI polls /api/proposals/prop-001 until vote appears (or listens for tx confirmation)
```

#### Deposit Transaction Flow

```
1. User enters deposit amount (e.g., 10,000 ADA)
2. UI calls buildDepositTx({ amount: 10_000_000_000, userAddress })
3. MeshTxBuilder constructs tx:
   - Input: treasury vault UTXO
   - Output: vault UTXO with updated ada_amount in datum
   - Mint: CHAOS tokens (proportional to deposit / TVL)
   - Signer: user's wallet
4. wallet.signTx() → wallet.submitTx()
5. Dashboard refreshes balance via useUserBalance()
```

### 2b. Wallet Hook Extensions (`hooks/useWalletActions.ts`)

```typescript
export function useWalletActions() {
  const { wallet, connected } = useWallet();
  
  return {
    deposit: async (amount: number) => { ... },
    withdraw: async (chaosAmount: number) => { ... },
    vote: async (proposalId: string, choice: VoteChoice) => { ... },
    propose: async (proposal: ProposalDraft) => { ... },
  };
}
```

---

## Phase 3: Dashboard Rework

### User View (default when wallet connected)

Shows data from `useUserBalance(walletAddress)`:
- CHAOS token balance + USD/EUR value
- Portfolio allocation pie chart (user's proportional share of vault)
- P&L since first deposit
- Transaction history (deposits, withdrawals, rewards)
- Action buttons: Deposit, Withdraw, Claim Rewards (all trigger wallet tx)

### Admin View (toggle, gated by wallet address)

Admin addresses are stored in the `TreasuryDatum.authorized_operators` list on-chain. The check:

```typescript
const { data: treasury } = useTreasuryState();
const isAdmin = treasury?.authorizedOperators.includes(walletAddress);
```

Admin view adds:
- Full treasury overview (total TVL, all positions, all allocations)
- Rebalance controls (trigger manual rebalance via wallet tx)
- Operator management
- Circuit breaker controls
- All user activity (aggregate stats)
- Governance proposal creation

The toggle only appears if `isAdmin === true`. No admin routes or server-side gating needed — the UI simply checks the on-chain datum.

---

## Phase 4: Governance Rework

### On-Chain Governance Model

Each proposal is a UTXO at the governance script address with a datum:

```typescript
// On-chain (Aiken)
type ProposalDatum {
  id: ByteArray,
  title: ByteArray,
  category: ProposalCategory,
  status: ProposalStatus,
  proposer: PubKeyHash,
  created_at: POSIXTime,
  voting_ends_at: POSIXTime,
  votes_for: Int,
  votes_against: Int,
  votes_abstain: Int,
  quorum_bps: Int,
  threshold_bps: Int,
  // Compact: no description on-chain (too expensive)
  // Description stored as tx metadata or off-chain (IPFS hash in metadata)
  metadata_hash: ByteArray,
}

type VoteRedeemer {
  Vote {
    choice: VoteChoice,      // For | Against | Abstain
    voting_power: Int,
  }
}
```

**Key design decision**: Proposal descriptions and details are too large for on-chain datum. Store them as:
- **Option A**: Cardano transaction metadata (up to 16KB per tx, free)
- **Option B**: IPFS with CID stored on-chain (more flexible)
- **Recommended**: Transaction metadata for Phase 1 (simpler, no IPFS dependency). The cache API route parses the creating tx's metadata to extract the description.

### Governance Page Data Flow

```
READ:
  /api/proposals → parses all governance UTXOs → returns Proposal[]
  Cache layer decodes each ProposalDatum + fetches tx metadata for descriptions

WRITE:
  Vote: browser builds VoteRedeemer tx → wallet signs → submit
  Propose: browser builds new governance UTXO tx + metadata → wallet signs → submit
```

### Voting Power

Voting power = CHAOS token balance at snapshot time. The cache layer queries:
- `fetchAssetHolders(CHAOS_POLICY_ID)` for total supply
- `useUserBalance(address)` for individual balance

No staking or delegation in Phase 1.

---

## Implementation Order

### Sprint 1: Foundation (est. 2-3 days)
1. Write `chaos_vault.ak` and `chaos_token.ak` in Aiken (from existing spec)
2. Deploy to Cardano Preprod testnet
3. Create `lib/blockfrost.ts` service
4. Create `.env.local` with `BLOCKFROST_API_KEY` and contract addresses

### Sprint 2: Cache API (est. 2 days)
1. `pages/api/treasury/state.ts` — read vault UTXO, parse datum
2. `pages/api/proposals/index.ts` — read governance UTXOs
3. `pages/api/user/[address]/balance.ts` — CHAOS token balance
4. `pages/api/prices/current.ts` — DEX pool prices
5. Simple in-memory cache wrapper

### Sprint 3: Client Hooks + Dashboard (est. 2 days)
1. Install `swr` (lightweight, fits Next.js well)
2. Create `hooks/useChain.ts` with all read hooks
3. Rewire `dashboard.tsx` to use real data (replace mock data)
4. Add admin toggle (check `authorized_operators` from treasury datum)
5. Admin panel: treasury overview, rebalance trigger

### Sprint 4: Wallet Transactions (est. 2-3 days)
1. `lib/transactions/deposit.ts` — build deposit tx
2. `lib/transactions/withdraw.ts` — build withdraw tx
3. `lib/transactions/vote.ts` — build vote tx
4. `hooks/useWalletActions.ts` — React hook wrapping tx builders
5. Wire deposit/withdraw buttons on dashboard
6. Wire vote buttons on governance page

### Sprint 5: Governance Live (est. 1-2 days)
1. `lib/transactions/propose.ts` — build proposal creation tx
2. Rewire `governance.tsx` to use `useProposals()` hook
3. Remove `GovernanceContext.tsx` (replaced by hooks + on-chain data)
4. Proposal creation form (admin only)
5. Vote confirmation flow with tx hash display

### Sprint 6: Polish (est. 1 day)
1. Loading states (skeleton cards while chain data loads)
2. Error handling (Blockfrost down, tx rejected, insufficient funds)
3. Tx confirmation toasts
4. Optimistic updates (show vote immediately, revert if tx fails)
5. Remove all remaining mock data

---

## Files to Create

```
lib/
  blockfrost.ts                   # Blockfrost API wrapper
  transactions/
    deposit.ts                    # Deposit tx builder
    withdraw.ts                   # Withdraw tx builder
    vote.ts                       # Vote tx builder
    propose.ts                    # Proposal creation tx builder
  contracts/
    addresses.ts                  # Script addresses, policy IDs (from env)
    datum.ts                      # Datum encode/decode helpers (CBOR ↔ TS)
    
hooks/
  useChain.ts                     # SWR hooks for cache API
  useWalletActions.ts             # Wallet write operations

pages/api/
  treasury/
    state.ts
    history.ts
  proposals/
    index.ts
    [id].ts
  user/
    [address]/
      balance.ts
  prices/
    current.ts
  stats/
    overview.ts
```

## Files to Modify

```
pages/dashboard.tsx               # Replace mock data with hooks, add admin toggle
pages/governance.tsx              # Replace GovernanceContext with hooks + wallet actions
contexts/GovernanceContext.tsx     # DELETE (replaced by on-chain data)
lib/governance/types.ts           # Keep types, remove MOCK_PROPOSALS
```

## Files Unchanged

```
pages/index.tsx                   # Landing page (static marketing)
pages/investors.tsx               # Investor page (static marketing)
pages/time-machine.tsx            # Uses local simulation data (no chain)
contexts/CurrencyContext.tsx      # Already done (wallet-aware localStorage)
components/layout/*               # Shared layout (no changes needed)
```

---

## Environment Variables

```env
# .env.local
BLOCKFROST_API_KEY=your_api_key_here  # Get from https://blockfrost.io
NEXT_PUBLIC_CARDANO_NETWORK=preprod
NEXT_PUBLIC_TREASURY_SCRIPT_HASH=<deployed vault script hash>
NEXT_PUBLIC_CHAOS_POLICY_ID=<deployed token policy ID>
NEXT_PUBLIC_GOVERNANCE_SCRIPT_HASH=<deployed governance script hash>
NEXT_PUBLIC_ADMIN_ADDRESSES=addr_test1...,addr_test1...
```

Note: `NEXT_PUBLIC_ADMIN_ADDRESSES` is a **fallback only** for Phase 1 before the treasury contract is deployed. Once live, admin status is determined by `authorized_operators` in the on-chain `TreasuryDatum`.

---

## Dependencies to Add

```bash
npm install swr        # Client-side data fetching + cache (13KB)
# @meshsdk/core already installed — provides MeshTxBuilder, Blockfrost, CBOR
# No other new deps needed
```

---

## Key Decisions

1. **SWR over React Query** — lighter (13KB vs 40KB), built-in Next.js integration, sufficient for our read-heavy pattern
2. **No database** — cache is in-memory on server, CDN edge cache in production
3. **No IPFS initially** — proposal descriptions go in Cardano tx metadata (up to 16KB, plenty for governance text)
4. **Admin check is client-side** — the on-chain datum is the authority; the UI just reads it. No server-side admin routes.
5. **Optimistic updates for votes** — show the vote immediately in UI, revert if tx fails
6. **Preprod first** — all development against Cardano Preprod testnet using existing Blockfrost key
