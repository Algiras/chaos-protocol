# CHAOS Token API Specification

**Version**: 1.0.0 (Phase 1 MVP)
**Base URL**: `https://api.chaostoken.io` (Production) | `http://localhost:3001` (Development)
**Protocol**: REST (JSON)
**Authentication**: Public read-only (Phase 1), API keys for write operations (Phase 2+)

---

## Overview

The CHAOS API provides programmatic access to:
- Treasury state and holdings
- Portfolio performance metrics
- Historical price data
- Rebalancing event history
- User portfolio information

All endpoints return JSON responses. Timestamps are in ISO 8601 format (UTC).

---

## Base Response Format

### Success Response
```json
{
  "success": true,
  "data": { /* endpoint-specific data */ },
  "timestamp": "2026-02-07T21:00:00.000Z"
}
```

### Error Response
```json
{
  "success": false,
  "error": {
    "code": "ERROR_CODE",
    "message": "Human-readable error message",
    "details": { /* optional additional context */ }
  },
  "timestamp": "2026-02-07T21:00:00.000Z"
}
```

### Common Error Codes
- `INVALID_REQUEST` (400) - Malformed request
- `NOT_FOUND` (404) - Resource not found
- `RATE_LIMIT_EXCEEDED` (429) - Too many requests
- `INTERNAL_ERROR` (500) - Server error
- `SERVICE_UNAVAILABLE` (503) - Temporary outage

---

## Endpoints

### 1. Treasury Endpoints

#### GET `/api/treasury/state`

Get current treasury state and allocations.

**Response**:
```json
{
  "success": true,
  "data": {
    "timestamp": "2026-02-07T21:00:00.000Z",
    "totalValueUsd": 12500000.00,
    "totalValueAda": 19230769.23,
    "holdings": {
      "ada": {
        "amount": 9615384.615,
        "valueUsd": 6250000.00,
        "percentage": 50.00,
        "priceUsd": 0.65
      },
      "djed": {
        "amount": 3750000.00,
        "valueUsd": 3750000.00,
        "percentage": 30.00,
        "priceUsd": 1.00
      },
      "lpPositions": {
        "valueUsd": 2500000.00,
        "percentage": 20.00,
        "positions": [
          {
            "dex": "Minswap",
            "pair": "ADA/DJED",
            "valueUsd": 1500000.00,
            "lpTokens": 1224744.87
          },
          {
            "dex": "SundaeSwap",
            "pair": "ADA/DJED",
            "valueUsd": 1000000.00,
            "lpTokens": 1000000.00
          }
        ]
      }
    },
    "targetAllocations": {
      "ada": 50.00,
      "djed": 30.00,
      "lpPositions": 20.00
    },
    "allocationDrift": {
      "ada": 0.00,
      "djed": 0.00,
      "lpPositions": 0.00
    },
    "nextRebalanceCheck": "2026-02-07T21:05:00.000Z",
    "lastRebalance": {
      "timestamp": "2026-02-05T14:30:00.000Z",
      "reason": "ADA below MA",
      "txHash": "abc123..."
    }
  },
  "timestamp": "2026-02-07T21:00:00.000Z"
}
```

**Rate Limit**: 100 requests/minute

---

#### GET `/api/treasury/history`

Get historical treasury values and allocations.

**Query Parameters**:
- `period` (optional): `1d`, `7d`, `30d`, `90d`, `1y`, `all` (default: `30d`)
- `interval` (optional): `1h`, `4h`, `1d` (default: `1d`)

**Response**:
```json
{
  "success": true,
  "data": {
    "period": "30d",
    "interval": "1d",
    "dataPoints": 30,
    "history": [
      {
        "timestamp": "2026-01-08T00:00:00.000Z",
        "totalValueUsd": 12000000.00,
        "adaPrice": 0.62,
        "allocations": {
          "ada": 50.5,
          "djed": 29.8,
          "lpPositions": 19.7
        }
      },
      // ... 29 more data points
    ]
  },
  "timestamp": "2026-02-07T21:00:00.000Z"
}
```

**Rate Limit**: 50 requests/minute

---

### 2. Performance Endpoints

#### GET `/api/performance/metrics`

Get comprehensive performance metrics.

**Query Parameters**:
- `period` (optional): `7d`, `30d`, `90d`, `1y`, `all` (default: `all`)

**Response**:
```json
{
  "success": true,
  "data": {
    "period": "all",
    "inceptionDate": "2026-01-01T00:00:00.000Z",
    "metrics": {
      "totalReturn": {
        "chaos": 8.5,
        "hodl": -15.2,
        "outperformance": 23.7
      },
      "cagr": {
        "chaos": 4.2,
        "hodl": -8.1
      },
      "volatility": {
        "chaos": 36.5,
        "hodl": 68.2
      },
      "sharpeRatio": {
        "chaos": 1.87,
        "hodl": 0.42
      },
      "maxDrawdown": {
        "chaos": -40.2,
        "hodl": -66.4,
        "chaosDate": "2022-06-18T00:00:00.000Z",
        "hodlDate": "2022-11-21T00:00:00.000Z"
      },
      "winRate": 67.5,
      "profitFactor": 2.8
    },
    "components": {
      "adaPriceAppreciation": 2.5,
      "rebalancingAlpha": 7.2,
      "lpFees": 4.0,
      "djedHoldings": 0.3
    }
  },
  "timestamp": "2026-02-07T21:00:00.000Z"
}
```

**Rate Limit**: 50 requests/minute

---

#### GET `/api/performance/chart`

Get chart data for performance visualization.

**Query Parameters**:
- `period` (optional): `7d`, `30d`, `90d`, `1y`, `all` (default: `1y`)
- `benchmark` (optional): `hodl`, `60-40`, `djed` (default: `hodl`)

**Response**:
```json
{
  "success": true,
  "data": {
    "period": "1y",
    "benchmark": "hodl",
    "dataPoints": 365,
    "series": [
      {
        "name": "CHAOS",
        "data": [
          { "date": "2025-02-07", "value": 100000 },
          { "date": "2025-02-08", "value": 100250 },
          // ... 363 more points
        ]
      },
      {
        "name": "HODL",
        "data": [
          { "date": "2025-02-07", "value": 100000 },
          { "date": "2025-02-08", "value": 99800 },
          // ... 363 more points
        ]
      }
    ]
  },
  "timestamp": "2026-02-07T21:00:00.000Z"
}
```

**Rate Limit**: 50 requests/minute

---

### 3. Price Endpoints

#### GET `/api/prices/current`

Get current prices from the oracle.

**Response**:
```json
{
  "success": true,
  "data": {
    "ada": {
      "priceUsd": 0.6523,
      "sources": [
        { "name": "CoinGecko", "price": 0.6521, "timestamp": "2026-02-07T21:00:15.000Z" },
        { "name": "Charli3", "price": 0.6524, "timestamp": "2026-02-07T21:00:18.000Z" },
        { "name": "Orcfax", "price": 0.6522, "timestamp": "2026-02-07T21:00:12.000Z" },
        { "name": "Minswap TWAP", "price": 0.6525, "timestamp": "2026-02-07T21:00:20.000Z" }
      ],
      "consensus": true,
      "deviation": 0.06,
      "movingAverage30d": 0.5842,
      "movingAverage7d": 0.6401
    },
    "djed": {
      "priceUsd": 1.0012,
      "pegDeviation": 0.12
    }
  },
  "timestamp": "2026-02-07T21:00:00.000Z"
}
```

**Rate Limit**: 100 requests/minute

---

#### GET `/api/prices/history`

Get historical price data.

**Query Parameters**:
- `asset` (required): `ada` or `djed`
- `period` (optional): `7d`, `30d`, `90d`, `1y`, `all` (default: `30d`)
- `interval` (optional): `5m`, `1h`, `4h`, `1d` (default: `1d`)

**Response**:
```json
{
  "success": true,
  "data": {
    "asset": "ada",
    "period": "30d",
    "interval": "1d",
    "dataPoints": 30,
    "prices": [
      {
        "timestamp": "2026-01-08T00:00:00.000Z",
        "open": 0.62,
        "high": 0.64,
        "low": 0.61,
        "close": 0.63,
        "volume": 45000000,
        "movingAverage": 0.58
      },
      // ... 29 more data points
    ]
  },
  "timestamp": "2026-02-07T21:00:00.000Z"
}
```

**Rate Limit**: 50 requests/minute

---

### 4. Rebalancing Endpoints

#### GET `/api/rebalancing/events`

Get rebalancing event history.

**Query Parameters**:
- `limit` (optional): Number of events to return (default: 20, max: 100)
- `offset` (optional): Pagination offset (default: 0)

**Response**:
```json
{
  "success": true,
  "data": {
    "total": 45,
    "limit": 20,
    "offset": 0,
    "events": [
      {
        "id": "rebal_123",
        "timestamp": "2026-02-05T14:30:00.000Z",
        "reason": "ADA below MA",
        "trigger": {
          "type": "price_signal",
          "condition": "ada_price < 0.90 * ma",
          "adaPrice": 0.52,
          "movingAverage": 0.58
        },
        "preRebalance": {
          "ada": { "amount": 9000000, "percentage": 45.5 },
          "djed": { "amount": 4000000, "percentage": 32.0 },
          "lpPositions": { "value": 2800000, "percentage": 22.5 }
        },
        "postRebalance": {
          "ada": { "amount": 9800000, "percentage": 50.0 },
          "djed": { "amount": 3600000, "percentage": 30.0 },
          "lpPositions": { "value": 2400000, "percentage": 20.0 }
        },
        "trades": [
          {
            "action": "buy",
            "asset": "ada",
            "amount": 800000,
            "priceUsd": 0.52,
            "valueUsd": 416000,
            "dex": "Minswap",
            "slippage": 0.08
          },
          {
            "action": "sell",
            "asset": "lp_tokens",
            "amount": 408163.27,
            "valueUsd": 400000,
            "dex": "Minswap"
          }
        ],
        "cost": {
          "fees": 1200,
          "slippage": 332,
          "total": 1532
        },
        "profit": 12500,
        "txHash": "abc123def456...",
        "blockHeight": 8234567
      },
      // ... 19 more events
    ]
  },
  "timestamp": "2026-02-07T21:00:00.000Z"
}
```

**Rate Limit**: 50 requests/minute

---

#### GET `/api/rebalancing/next-check`

Get information about the next rebalancing check.

**Response**:
```json
{
  "success": true,
  "data": {
    "nextCheck": "2026-02-07T21:05:00.000Z",
    "checkInterval": 300,
    "currentConditions": {
      "allocationDrift": {
        "ada": 0.2,
        "threshold": 10.0,
        "triggered": false
      },
      "priceSignal": {
        "adaPrice": 0.6523,
        "movingAverage": 0.5842,
        "ratio": 1.116,
        "buyThreshold": 0.90,
        "sellThreshold": 1.10,
        "triggered": true,
        "signal": "sell"
      }
    },
    "willRebalance": true,
    "estimatedCost": 1200
  },
  "timestamp": "2026-02-07T21:00:00.000Z"
}
```

**Rate Limit**: 100 requests/minute

---

### 5. User Portfolio Endpoints

#### GET `/api/user/:address/balance`

Get CHAOS token balance and portfolio value for a user.

**Path Parameters**:
- `address` (required): Cardano wallet address (stake or payment)

**Response**:
```json
{
  "success": true,
  "data": {
    "address": "addr1q9y...",
    "chaosBalance": 125000.00,
    "chaosPercentage": 0.125,
    "portfolioValue": {
      "usd": 156250.00,
      "ada": 239583.33
    },
    "deposits": [
      {
        "timestamp": "2026-01-15T10:30:00.000Z",
        "adaDeposited": 100000.00,
        "chaosReceived": 100000.00,
        "sharePrice": 1.00,
        "txHash": "xyz789..."
      },
      {
        "timestamp": "2026-01-22T14:00:00.000Z",
        "adaDeposited": 50000.00,
        "chaosReceived": 25000.00,
        "sharePrice": 2.00,
        "txHash": "abc123..."
      }
    ],
    "totalDeposited": {
      "ada": 150000.00,
      "usd": 97500.00
    },
    "profitLoss": {
      "usd": 58750.00,
      "percentage": 60.25
    },
    "since": "2026-01-15T10:30:00.000Z"
  },
  "timestamp": "2026-02-07T21:00:00.000Z"
}
```

**Rate Limit**: 100 requests/minute per address

---

### 6. Statistics Endpoints

#### GET `/api/stats/overview`

Get high-level protocol statistics.

**Response**:
```json
{
  "success": true,
  "data": {
    "tvl": {
      "usd": 12500000.00,
      "ada": 19230769.23
    },
    "users": {
      "total": 1247,
      "activeLastWeek": 892,
      "activeLastMonth": 1103
    },
    "chaosToken": {
      "totalSupply": 100000000.00,
      "circulating": 5000000.00,
      "price": 1.25,
      "marketCap": 6250000.00
    },
    "volume": {
      "last24h": 125000.00,
      "last7d": 980000.00,
      "last30d": 4500000.00
    },
    "rebalancing": {
      "totalEvents": 45,
      "last24h": 0,
      "last7d": 2,
      "avgCost": 1200,
      "winRate": 67.5
    }
  },
  "timestamp": "2026-02-07T21:00:00.000Z"
}
```

**Rate Limit**: 100 requests/minute

---

## Rate Limiting

All endpoints are rate-limited to prevent abuse:

**Default Limits**:
- Read endpoints: 100 requests/minute
- Heavy queries: 50 requests/minute
- Per-user queries: 100 requests/minute per address

**Headers**:
```
X-RateLimit-Limit: 100
X-RateLimit-Remaining: 95
X-RateLimit-Reset: 1675800000
```

**Rate Limit Exceeded Response**:
```json
{
  "success": false,
  "error": {
    "code": "RATE_LIMIT_EXCEEDED",
    "message": "Too many requests. Please try again in 42 seconds.",
    "retryAfter": 42
  },
  "timestamp": "2026-02-07T21:00:00.000Z"
}
```

---

## WebSocket API (Phase 2+)

Real-time updates via WebSocket (Coming in Phase 2):

**Connection**: `wss://api.chaostoken.io/ws`

**Channels**:
- `treasury.state` - Treasury updates every 5 minutes
- `prices.ada` - ADA price updates real-time
- `rebalancing.events` - New rebalancing events
- `user.{address}` - User-specific updates

**Example**:
```javascript
const ws = new WebSocket('wss://api.chaostoken.io/ws');
ws.send(JSON.stringify({ action: 'subscribe', channel: 'treasury.state' }));
```

---

## Error Handling

### Error Codes

| Code | HTTP Status | Description |
|------|------------|-------------|
| `INVALID_REQUEST` | 400 | Malformed request or invalid parameters |
| `UNAUTHORIZED` | 401 | Missing or invalid API key |
| `FORBIDDEN` | 403 | Insufficient permissions |
| `NOT_FOUND` | 404 | Resource not found |
| `RATE_LIMIT_EXCEEDED` | 429 | Too many requests |
| `INTERNAL_ERROR` | 500 | Server error |
| `SERVICE_UNAVAILABLE` | 503 | Temporary outage or maintenance |

### Example Error Handling (JavaScript)

```javascript
async function getTreasuryState() {
  try {
    const response = await fetch('https://api.chaostoken.io/api/treasury/state');
    const data = await response.json();

    if (!data.success) {
      console.error('Error:', data.error.message);
      return null;
    }

    return data.data;
  } catch (error) {
    console.error('Network error:', error);
    return null;
  }
}
```

---

## SDKs and Client Libraries

### Official SDKs (Phase 2+)

- **JavaScript/TypeScript**: `@chaostoken/sdk`
- **Python**: `chaostoken-sdk`
- **Rust**: `chaostoken` crate

### Example Usage (TypeScript)

```typescript
import { CHAOSClient } from '@chaostoken/sdk';

const client = new CHAOSClient({
  baseUrl: 'https://api.chaostoken.io',
  apiKey: 'optional-for-phase1'
});

// Get treasury state
const state = await client.treasury.getState();
console.log('TVL:', state.totalValueUsd);

// Get performance metrics
const metrics = await client.performance.getMetrics({ period: '1y' });
console.log('Sharpe Ratio:', metrics.sharpeRatio.chaos);

// Get user balance
const balance = await client.user.getBalance('addr1q9y...');
console.log('CHAOS Balance:', balance.chaosBalance);
```

---

## Changelog

### v1.0.0 (Phase 1 MVP) - February 2026
- Initial API release
- Treasury state and history endpoints
- Performance metrics and charts
- Price oracle endpoints
- Rebalancing event history
- User portfolio queries
- Protocol statistics

### Future (Phase 2+)
- WebSocket real-time updates
- Write operations (deposits, withdrawals)
- Governance endpoints (proposals, voting)
- API key authentication
- Advanced analytics endpoints
- Batch queries

---

## Support

**API Issues**: [api@chaostoken.io](mailto:api@chaostoken.io)
**Documentation**: [https://docs.chaostoken.io/api](https://docs.chaostoken.io/api)
**Status Page**: [https://status.chaostoken.io](https://status.chaostoken.io)

---

**Last Updated**: February 7, 2026
**Version**: 1.0.0
**Status**: ✅ Specification Complete, 🚧 Implementation Pending
