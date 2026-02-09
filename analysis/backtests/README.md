# CHAOS Token Backtest

Testing the antifragile volatility harvesting hypothesis with real Cardano data.

## 🎯 Hypothesis

**CHAOS token will outperform simple HODL by:**
1. Buying ADA when it drops (cheap)
2. Selling ADA when it pumps (expensive)
3. Earning LP fees from volatility
4. Rebalancing to capture mean reversion

## 🚀 Quick Start

### 1. Install Dependencies

```bash
pip install -r requirements.txt
```

### 2. (Optional) Get API Keys

For real-time data:
```bash
cp .env.example .env
# Edit .env and add your Blockfrost API key from https://blockfrost.io
```

**Note**: The backtest works without API keys using CoinGecko's free tier.

### 3. Run Backtest

```bash
python backtest.py
```

This will:
- ✅ Fetch 1 year of ADA price history
- ✅ Simulate CHAOS rebalancing strategy
- ✅ Compare against simple HODL
- ✅ Generate performance report
- ✅ Create visualization (chaos_backtest_results.png)

## 📊 What Gets Tested

### Strategy Parameters

```python
initial_capital = $100,000
target_ada_allocation = 50%
target_djed_allocation = 30%
target_lp_allocation = 20%

# Rebalancing triggers:
- If allocation drifts >10% from target
- If ADA price < 90% of 30-day MA (buy opportunity)
- If ADA price > 110% of 30-day MA (sell opportunity)
```

### Performance Metrics

- **Total Return**: Absolute profit/loss
- **CAGR**: Compound Annual Growth Rate
- **Volatility**: Risk (standard deviation of returns)
- **Max Drawdown**: Worst peak-to-trough decline
- **Sharpe Ratio**: Risk-adjusted returns
- **Outperformance**: CHAOS vs HODL difference

## 📈 Expected Results

Based on theoretical analysis, we expect:

### Bull Market (ADA +100%)
```
HODL: +100%
CHAOS: +50-60% (underperforms but still profitable)
Reason: Sold too early, but captured profit
```

### Bear Market (ADA -50%)
```
HODL: -50%
CHAOS: -15 to -25% (outperforms)
Reason: Rebalanced to DJED, bought discount
```

### Volatile Sideways (±20% daily)
```
HODL: ~0%
CHAOS: +15-30% (significantly outperforms)
Reason: Constantly buy low, sell high + LP fees
```

### Average All Conditions
```
Expected CHAOS CAGR: 15-30%
Expected Sharpe Ratio: 1.5-2.5 (good)
Expected Outperformance: +10-20%
```

## 🔬 Testing Different Scenarios

### Modify Parameters

Edit `backtest.py`:

```python
# Test more conservative allocation
strategy = CHAOSStrategy(
    target_ada_allocation=0.30,  # 30% ADA instead of 50%
    target_djed_allocation=0.50,  # 50% DJED (more stable)
    buy_threshold=0.85,  # More aggressive buying
)

# Test different time periods
data = fetcher.get_all_data(days=730)  # 2 years instead of 1
```

### Test Specific Market Conditions

```python
# Test only bear market (e.g., June 2022 - Jan 2023)
data_ada = data['ada']['2022-06-01':'2023-01-01']

# Test only bull market (e.g., Oct 2023 - Mar 2024)
data_ada = data['ada']['2023-10-01':'2024-03-01']
```

## 📁 Output Files

After running backtest:

```
chaos_backtest_results.png    # Visual dashboard
chaos_backtest_data.csv        # Raw daily data
```

## 🎓 Understanding the Results

### ✅ Hypothesis CONFIRMED if:
- Outperformance > 10%
- Sharpe Ratio > 1.5
- Lower max drawdown than HODL
- **Conclusion**: CHAOS is antifragile!

### ⚠️ Hypothesis INCONCLUSIVE if:
- Outperformance 0-10%
- Sharpe Ratio 1.0-1.5
- Similar drawdown to HODL
- **Conclusion**: Needs parameter optimization

### ❌ Hypothesis REJECTED if:
- Outperformance < 0% (underperforms)
- Sharpe Ratio < 1.0
- Higher drawdown than HODL
- **Conclusion**: Back to drawing board

## 🔄 Next Steps Based on Results

### If Hypothesis Confirmed ✅
1. ✅ Test with more data (2-3 years)
2. ✅ Optimize parameters (grid search)
3. ✅ Add more sophisticated strategies
4. ✅ Build real smart contract
5. ✅ Deploy small pilot ($10k)

### If Hypothesis Rejected ❌
1. 🔍 Analyze why it failed
2. 🔍 Test alternative strategies:
   - Different rebalancing thresholds
   - Different MA windows
   - Include options hedging
   - Multi-asset treasury
3. 🔍 Consider it might not be antifragile (honest assessment)

## 🛠️ Advanced Usage

### Monte Carlo Simulation

Test across 1000 random scenarios:

```python
# Add to backtest.py
for i in range(1000):
    # Randomize parameters
    strategy = CHAOSStrategy(
        buy_threshold=np.random.uniform(0.85, 0.95),
        sell_threshold=np.random.uniform(1.05, 1.15),
        # ...
    )
    results = strategy.backtest(...)
    # Collect statistics
```

### Live Trading Simulation

Test with real-time data:

```python
# Add to data_fetcher.py
def fetch_live_prices(self):
    # Fetch current prices every minute
    # Simulate rebalancing decisions
    # Track paper trading performance
```

## 📚 References

- [Antifragile by Nassim Taleb](https://www.amazon.com/Antifragile-Things-Gain-Disorder-ebook/dp/B0083DJWGO)
- [Volatility Harvesting](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=2785678)
- [Mean Reversion Trading](https://www.investopedia.com/terms/m/meanreversion.asp)

## ⚠️ Disclaimer

**This is a theoretical backtest, not financial advice.**

- Past performance ≠ future results
- Backtests can overfit
- Real trading has slippage, fees, and execution risk
- Smart contract risk is real
- Only invest what you can afford to lose

---

**Let's test if CHAOS truly is antifragile!** 🌀
