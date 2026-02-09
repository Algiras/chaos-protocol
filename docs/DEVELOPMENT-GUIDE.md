# CHAOS Token Development Guide

**Welcome to the CHAOS development team!** This guide will get you from zero to productive in under 30 minutes.

---

## 🚀 Quick Start (5 minutes)

### Prerequisites

```bash
# Check you have these installed:
node --version     # v20+
npm --version      # v9+
git --version      # v2.40+

# Install Aiken (for smart contracts)
cargo install aiken

# Install Quarto (for whitepaper)
# Download from: https://quarto.org/docs/get-started/
```

### Clone and Setup

```bash
# Clone the repository
git clone https://github.com/chaostoken/equalibrium.git
cd equalibrium/chaos-production

# Install dependencies
npm install

# Set up environment variables
cp .env.example .env
# Edit .env and add your Blockfrost API key (optional for local dev)

# Start development server
npm run dev
```

Open [http://localhost:3000](http://localhost:3000) and you should see the CHAOS dashboard!

---

## 📁 Project Structure

```
chaos-production/
│
├── aiken/                    # Smart contracts (Aiken)
│   ├── lib/
│   │   ├── chaos_vault.ak    # Treasury management
│   │   └── chaos_token.ak    # Token minting policy
│   ├── validators/
│   └── tests/
│
├── src/                      # Frontend (Next.js + Mesh.js)
│   ├── app/
│   │   ├── page.tsx          # Main dashboard
│   │   ├── governance/       # Governance UI
│   │   └── api/              # API routes
│   ├── components/
│   │   ├── WalletConnect.tsx
│   │   ├── DepositForm.tsx
│   │   └── PerformanceChart.tsx
│   └── lib/
│       ├── mesh-tx-builder.ts    # Transaction helpers
│       └── utils.ts
│
├── services/                 # Backend services (Node.js)
│   ├── rebalancing-engine.ts # Strategy execution
│   ├── price-oracle.ts       # Multi-source oracle
│   ├── api/                  # Express.js REST API
│   └── db/                   # Prisma ORM
│
├── tests/                    # Tests
│   ├── unit/
│   ├── integration/
│   └── e2e/
│
├── docs/                     # Documentation
│   ├── API-SPECIFICATION.md
│   ├── SMART-CONTRACT-SPECIFICATION.md
│   └── ARCHITECTURE.md
│
└── scripts/                  # Deployment scripts
    ├── deploy-testnet.sh
    ├── deploy-mainnet.sh
    └── initialize-treasury.ts
```

---

## 🛠️ Development Workflow

### 1. Frontend Development

**Tech Stack**: Next.js 14 (App Router) + Mesh.js + TailwindCSS

```bash
# Start dev server with hot reload
npm run dev

# Run type checking
npm run type-check

# Run linter
npm run lint

# Format code
npm run format
```

**Creating a New Component**:

```typescript
// src/components/MyComponent.tsx
'use client';

import { useWallet } from '@meshsdk/react';

export function MyComponent() {
  const { wallet, connected } = useWallet();

  return (
    <div className="p-4">
      {connected ? (
        <p>Wallet connected!</p>
      ) : (
        <p>Please connect wallet</p>
      )}
    </div>
  );
}
```

**Adding a New Page**:

```typescript
// src/app/my-page/page.tsx
export default function MyPage() {
  return <h1>My New Page</h1>;
}

// Automatically available at /my-page
```

### 2. Smart Contract Development

**Tech Stack**: Aiken v1.0+

```bash
# Check Aiken installation
aiken --version

# Build contracts
cd aiken
aiken build

# Run tests
aiken check

# Generate blueprint (Plutus script)
aiken blueprint convert
```

**Writing a Validator**:

```rust
// aiken/lib/my_validator.ak
use aiken/list
use aiken/transaction.{ScriptContext}

type MyDatum {
  owner: ByteArray,
  amount: Int
}

type MyRedeemer {
  Withdraw
  Update { new_amount: Int }
}

validator {
  fn my_validator(datum: MyDatum, redeemer: MyRedeemer, ctx: ScriptContext) -> Bool {
    when redeemer is {
      Withdraw ->
        // Verify owner signature
        list.has(ctx.transaction.extra_signatories, datum.owner)

      Update { new_amount } ->
        new_amount > datum.amount
    }
  }
}
```

**Running Contract Tests**:

```rust
// aiken/lib/my_validator_test.ak
use aiken/my_validator.{MyDatum, MyRedeemer, my_validator}

test withdraw_valid() {
  let datum = MyDatum { owner: #"abc123", amount: 1000 }
  let redeemer = Withdraw
  let ctx = mock_context(signed_by: #"abc123")

  my_validator(datum, redeemer, ctx) == True
}

test withdraw_invalid_signer() {
  let datum = MyDatum { owner: #"abc123", amount: 1000 }
  let redeemer = Withdraw
  let ctx = mock_context(signed_by: #"xyz789")  // Wrong signer!

  my_validator(datum, redeemer, ctx) == False
}
```

### 3. Backend Service Development

**Tech Stack**: Node.js 20 + TypeScript + Express.js + Prisma

```bash
# Start backend service
npm run backend:dev

# Run database migrations
npx prisma migrate dev

# Generate Prisma client
npx prisma generate

# Open Prisma Studio (database GUI)
npx prisma studio
```

**Creating a New Service**:

```typescript
// services/my-service.ts
import { PrismaClient } from '@prisma/client';

const prisma = new PrismaClient();

export class MyService {
  async getData(): Promise<MyData[]> {
    return prisma.myTable.findMany();
  }

  async createData(data: CreateMyData): Promise<MyData> {
    return prisma.myTable.create({ data });
  }
}
```

**Adding an API Endpoint**:

```typescript
// src/app/api/my-endpoint/route.ts
import { NextResponse } from 'next/server';

export async function GET(request: Request) {
  try {
    const data = await fetchMyData();
    return NextResponse.json({ success: true, data });
  } catch (error) {
    return NextResponse.json(
      { success: false, error: error.message },
      { status: 500 }
    );
  }
}
```

### 4. Testing

**Unit Tests** (Jest):

```bash
npm run test
npm run test:watch     # Watch mode
npm run test:coverage  # With coverage report
```

```typescript
// tests/unit/my-function.test.ts
import { myFunction } from '@/lib/utils';

describe('myFunction', () => {
  it('should return correct value', () => {
    expect(myFunction(5)).toBe(10);
  });

  it('should handle edge cases', () => {
    expect(myFunction(0)).toBe(0);
    expect(myFunction(-5)).toThrow();
  });
});
```

**Integration Tests** (Local Emulator):

```bash
npm run test:integration
```

**E2E Tests** (Playwright):

```bash
npm run test:e2e
npm run test:e2e:ui  # Interactive mode
```

```typescript
// tests/e2e/deposit.spec.ts
import { test, expect } from '@playwright/test';

test('user can deposit ADA', async ({ page }) => {
  await page.goto('http://localhost:3000');

  // Connect wallet
  await page.click('text=Connect Wallet');
  await page.click('text=Nami');

  // Enter deposit amount
  await page.fill('[placeholder="Amount"]', '100');
  await page.click('text=Deposit');

  // Verify success
  await expect(page.locator('text=Deposit successful')).toBeVisible();
});
```

---

## 🎨 Code Style Guidelines

### TypeScript/JavaScript

```typescript
// ✅ Good
export async function getTreasuryState(): Promise<TreasuryState> {
  const data = await prisma.treasury.findFirst();
  if (!data) throw new Error('Treasury not found');
  return mapToTreasuryState(data);
}

// ❌ Bad
export async function getTreasuryState() {  // No return type
  let data = await prisma.treasury.findFirst()  // No semicolon
  if (!data) return null  // Inconsistent error handling
  return data  // No mapping
}
```

**Rules**:
- Always use TypeScript (no `any` types)
- Prefer `async/await` over promises
- Use meaningful variable names
- Add JSDoc comments for public APIs
- Prefer functional style (map, filter, reduce)

### Aiken

```rust
// ✅ Good
fn calculate_total_value(ada: Int, djed: Int, lp: Int) -> Int {
  ada + djed + lp
}

// ❌ Bad
fn calc(a, b, c) {  // Unclear parameter names
  a + b + c
}
```

**Rules**:
- Use snake_case for functions and variables
- Use PascalCase for types
- Prefer explicit types
- Add doc comments (`///`) for validators
- Keep functions under 50 lines

---

## 🔧 Common Tasks

### Add a New Dependency

```bash
npm install package-name
npm install -D @types/package-name  # Type definitions
```

### Update Database Schema

```bash
# 1. Edit prisma/schema.prisma
# 2. Create migration
npx prisma migrate dev --name add_my_table

# 3. Generate client
npx prisma generate
```

### Deploy to Testnet

```bash
# 1. Build smart contracts
cd aiken && aiken build

# 2. Run deployment script
npm run deploy:testnet

# 3. Verify deployment
npm run verify:testnet
```

### Run Backtest Locally

```bash
cd ../chaos-backtest
python backtest.py

# View results
open chaos_backtest_results.png
```

### Generate Whitepaper PDF

```bash
cd ../whitepaper
quarto render

# Output: whitepaper/_book/whitepaper.pdf
open _book/whitepaper.pdf
```

---

## 🐛 Debugging

### Frontend Debugging

```typescript
// Use Next.js built-in debugging
console.log('Debug:', value);

// React DevTools
// Install browser extension

// Network requests
// Use browser DevTools Network tab

// Mesh.js transactions
import { Transaction } from '@meshsdk/core';

const tx = await buildMyTransaction();
console.log('Transaction:', tx.toJSON());
```

### Smart Contract Debugging

```rust
// Aiken doesn't have print debugging
// Use test-driven development instead

test debug_my_validator() {
  let datum = MyDatum { ... }
  let redeemer = MyRedeemer { ... }
  let ctx = mock_context()

  // Add assertions to understand behavior
  let result = my_validator(datum, redeemer, ctx)
  trace @"Result": result  // Aiken trace

  result == True
}
```

### Backend Debugging

```typescript
// VS Code launch.json
{
  "type": "node",
  "request": "launch",
  "name": "Debug Backend",
  "program": "${workspaceFolder}/services/index.ts",
  "preLaunchTask": "tsc: build",
  "outFiles": ["${workspaceFolder}/dist/**/*.js"]
}

// Or use Node inspector
node --inspect services/index.ts
```

---

## 📦 Build and Deploy

### Build for Production

```bash
# Frontend
npm run build
npm run start  # Test production build

# Smart Contracts
cd aiken
aiken build --optimize

# Backend
npm run backend:build
```

### Deploy to Preview Testnet

```bash
# 1. Set environment
export NETWORK=preview
export BLOCKFROST_API_KEY=your_key

# 2. Deploy contracts
npm run deploy:testnet

# 3. Initialize treasury
npm run init:treasury -- --network preview

# 4. Deploy frontend
vercel deploy --prebuilt
```

### Deploy to Mainnet

```bash
# ⚠️ Only after full audit and testing!

# 1. Set environment
export NETWORK=mainnet
export BLOCKFROST_API_KEY=your_mainnet_key

# 2. Deploy contracts (with multi-sig)
npm run deploy:mainnet

# 3. Initialize treasury (with TVL cap)
npm run init:treasury -- --network mainnet --tvl-cap 10000

# 4. Deploy frontend
vercel deploy --prod
```

---

## 🧪 Testing Checklist

Before submitting a PR, ensure:

- [ ] All tests pass: `npm run test`
- [ ] Type checking passes: `npm run type-check`
- [ ] Linting passes: `npm run lint`
- [ ] Code is formatted: `npm run format`
- [ ] Aiken contracts build: `cd aiken && aiken check`
- [ ] No console.log statements in production code
- [ ] Added tests for new features
- [ ] Updated documentation
- [ ] Tested manually on testnet (for smart contract changes)

---

## 🤝 Contributing

### Branch Naming

- `feature/add-wallet-connection` - New features
- `fix/rebalancing-bug` - Bug fixes
- `docs/api-specification` - Documentation
- `refactor/clean-up-types` - Code improvements

### Commit Messages

```
feat: add wallet connection component
fix: resolve rebalancing calculation error
docs: update API specification
test: add unit tests for price oracle
refactor: simplify transaction builder
```

### Pull Request Process

1. Create a feature branch from `main`
2. Make changes and commit
3. Push to your fork
4. Open PR with description:
   - What changed
   - Why it changed
   - How to test
5. Address review feedback
6. Squash and merge

---

## 📚 Resources

### Official Documentation

- **Mesh.js**: https://meshjs.dev/
- **Aiken**: https://aiken-lang.org/
- **Next.js**: https://nextjs.org/docs
- **Prisma**: https://www.prisma.io/docs
- **Cardano**: https://docs.cardano.org/

### Internal Documentation

- [API Specification](./API-SPECIFICATION.md)
- [Smart Contract Specification](./SMART-CONTRACT-SPECIFICATION.md)
- [Architecture Overview](./ARCHITECTURE.md)
- [Whitepaper](../whitepaper/)

### Community

- **Discord**: [discord.gg/chaostoken](https://discord.gg/chaostoken)
- **GitHub Issues**: [github.com/chaostoken/equalibrium/issues](https://github.com/chaostoken/equalibrium/issues)
- **Weekly Calls**: Fridays 3pm UTC

---

## 🆘 Getting Help

### Common Issues

**Issue**: `npm install` fails

**Solution**: Delete `node_modules` and `package-lock.json`, then retry

---

**Issue**: Aiken build fails with "unknown validator"

**Solution**: Check validator signature matches in `aiken.toml`

---

**Issue**: Mesh.js wallet not connecting

**Solution**: Ensure wallet extension is installed and enabled. Try in incognito mode.

---

**Issue**: Prisma migrations fail

**Solution**: Reset database: `npx prisma migrate reset`

---

### Ask for Help

1. **Check documentation** (above resources)
2. **Search GitHub issues** for similar problems
3. **Ask in Discord** #dev-help channel
4. **Create GitHub issue** if it's a bug

---

## 📊 Performance Targets

| Metric | Target | Measured |
|--------|--------|----------|
| **Frontend** |
| Lighthouse Score | >90 | TBD |
| First Contentful Paint | <1.5s | TBD |
| Time to Interactive | <3s | TBD |
| **Backend** |
| API Response Time (p95) | <200ms | TBD |
| Database Query Time | <50ms | TBD |
| **Smart Contracts** |
| Execution Units | <10,000 | TBD |
| Transaction Fee | <0.5 ADA | TBD |

---

## 🎯 Development Roadmap

### Phase 1 (Current) - Weeks 1-13

- [x] Project setup
- [x] Whitepaper foundation
- [ ] Smart contracts (Weeks 2-6)
- [ ] Frontend MVP (Weeks 4-8)
- [ ] Backend services (Weeks 5-7)
- [ ] Testnet deployment (Week 8)
- [ ] Security audit (Weeks 9-11)
- [ ] Mainnet launch (Week 12-13)

### Phase 2 - Months 4-6

- [ ] Automated rebalancing
- [ ] Governance implementation
- [ ] ISPO launch
- [ ] Multiple DEX support

### Phase 3 - Months 7-12

- [ ] LBP token launch
- [ ] ML-enhanced strategies
- [ ] Mobile apps
- [ ] Enterprise features

---

## 📝 Notes

- **Always test on testnet first** before mainnet changes
- **Never commit private keys** or sensitive data
- **Use environment variables** for configuration
- **Write tests** for critical logic
- **Document your code** (especially smart contracts)
- **Keep PRs small** (< 500 lines of code)
- **Ask questions** - there are no stupid questions!

---

**Happy coding! Let's build something amazing together.** 🚀

---

**Last Updated**: February 7, 2026
**Maintainer**: CHAOS Development Team
**Questions**: [dev@chaostoken.io](mailto:dev@chaostoken.io)
