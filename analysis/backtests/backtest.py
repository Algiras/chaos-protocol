"""
CHAOS Token Backtest - Main Execution

Runs complete backtest and generates analysis.

Usage:
    python backtest.py                          # default: ADA, 365 days
    python backtest.py --coin bitcoin --days 730
    python backtest.py --coin ethereum
"""

import argparse
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import seaborn as sns
from data_fetcher import CryptoDataFetcher, COIN_REGISTRY
from chaos_strategy import CHAOSStrategy
from typing import Dict
import warnings
warnings.filterwarnings('ignore')

sns.set_style("darkgrid")
plt.rcParams['figure.figsize'] = (15, 10)


def calculate_performance_metrics(results: pd.DataFrame) -> Dict:
    """Calculate comprehensive performance metrics."""

    chaos_returns = results['returns'].dropna()
    chaos_final = results['portfolio_value'].iloc[-1]
    chaos_initial = results['portfolio_value'].iloc[0]

    hodl_final = results['hodl_value'].iloc[-1]
    hodl_initial = results['hodl_value'].iloc[0]

    days = len(results)
    years = max(days / 365, 0.01)

    metrics = {
        'chaos_total_return': (chaos_final / chaos_initial - 1) * 100,
        'hodl_total_return': (hodl_final / hodl_initial - 1) * 100,
        'chaos_cagr': ((chaos_final / chaos_initial) ** (1/years) - 1) * 100,
        'hodl_cagr': ((hodl_final / hodl_initial) ** (1/years) - 1) * 100,

        'chaos_volatility': chaos_returns.std() * np.sqrt(365) * 100,
        'chaos_max_drawdown': (
            (results['portfolio_value'] / results['portfolio_value'].cummax() - 1).min() * 100
        ),
        'hodl_max_drawdown': (
            (results['hodl_value'] / results['hodl_value'].cummax() - 1).min() * 100
        ),

        'chaos_sharpe': (
            (chaos_returns.mean() * 365) / (chaos_returns.std() * np.sqrt(365))
            if chaos_returns.std() > 0 else 0
        ),

        'outperformance': (
            ((chaos_final / chaos_initial) / (hodl_final / hodl_initial) - 1) * 100
        ),

        'num_rebalances': results['rebalanced'].sum(),
        'rebalance_frequency': days / results['rebalanced'].sum() if results['rebalanced'].sum() > 0 else 0,
    }

    return metrics


def plot_results(
    results: pd.DataFrame,
    metrics: Dict,
    asset_name: str = 'ADA',
    save_path: str = 'chaos_backtest_results.png',
):
    """Generate comprehensive visualization of results."""

    fig, axes = plt.subplots(3, 2, figsize=(16, 12))
    fig.suptitle(f'CHAOS Backtest Results — {asset_name}', fontsize=16, fontweight='bold')

    # 1. Portfolio Value
    ax1 = axes[0, 0]
    ax1.plot(results.index, results['portfolio_value'], label='CHAOS Strategy', linewidth=2, color='#00d4aa')
    ax1.plot(results.index, results['hodl_value'], label=f'HODL {asset_name}', linewidth=2, color='#0033ad', alpha=0.7)
    ax1.set_title('Portfolio Value Over Time', fontweight='bold')
    ax1.set_ylabel('Value (USD)')
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    # 2. Cumulative Returns
    ax2 = axes[0, 1]
    ax2.plot(results.index, results['cumulative_return'], label='CHAOS', linewidth=2, color='#00d4aa')
    ax2.plot(results.index, results['hodl_return'], label='HODL', linewidth=2, color='#0033ad', alpha=0.7)
    ax2.axhline(y=0, color='black', linestyle='--', alpha=0.3)
    ax2.set_title('Cumulative Returns (%)', fontweight='bold')
    ax2.set_ylabel('Return (%)')
    ax2.legend()
    ax2.grid(True, alpha=0.3)

    # 3. Price and Rebalance Points
    ax3 = axes[1, 0]
    ax3.plot(results.index, results['asset_price'], label=f'{asset_name} Price', color='#0033ad', alpha=0.6)
    rebalance_points = results[results['rebalanced']]
    ax3.scatter(rebalance_points.index, rebalance_points['asset_price'],
                color='red', s=50, alpha=0.6, label='Rebalances', zorder=5)
    ax3.set_title(f'{asset_name} Price & Rebalance Points', fontweight='bold')
    ax3.set_ylabel('Price (USD)')
    ax3.legend()
    ax3.grid(True, alpha=0.3)

    # 4. Asset Allocation
    ax4 = axes[1, 1]
    ax4.fill_between(results.index, 0, results['asset_allocation'] * 100,
                      label=f'{asset_name} %', alpha=0.7, color='#0033ad')
    ax4.axhline(y=50, color='red', linestyle='--', alpha=0.5, label='Target (50%)')
    ax4.set_title(f'{asset_name} Allocation Over Time', fontweight='bold')
    ax4.set_ylabel('Allocation (%)')
    ax4.set_ylim(0, 100)
    ax4.legend()
    ax4.grid(True, alpha=0.3)

    # 5. Rolling Sharpe
    ax5 = axes[2, 0]
    rolling_sharpe = (
        results['returns'].rolling(window=90).mean() * 365 /
        (results['returns'].rolling(window=90).std() * np.sqrt(365))
    )
    ax5.plot(results.index, rolling_sharpe, color='#00d4aa', linewidth=2)
    ax5.axhline(y=1.0, color='orange', linestyle='--', alpha=0.5, label='Sharpe = 1.0')
    ax5.axhline(y=2.0, color='green', linestyle='--', alpha=0.5, label='Sharpe = 2.0')
    ax5.set_title('Rolling 90-Day Sharpe Ratio', fontweight='bold')
    ax5.set_ylabel('Sharpe Ratio')
    ax5.legend()
    ax5.grid(True, alpha=0.3)

    # 6. Metrics Summary
    ax6 = axes[2, 1]
    ax6.axis('off')

    metrics_text = f"""
    PERFORMANCE SUMMARY — {asset_name}
    {'='*40}

    CHAOS Strategy:
      Total Return:     {metrics['chaos_total_return']:>8.2f}%
      CAGR:            {metrics['chaos_cagr']:>8.2f}%
      Volatility:      {metrics['chaos_volatility']:>8.2f}%
      Max Drawdown:    {metrics['chaos_max_drawdown']:>8.2f}%
      Sharpe Ratio:    {metrics['chaos_sharpe']:>8.2f}

    HODL Strategy:
      Total Return:     {metrics['hodl_total_return']:>8.2f}%
      CAGR:            {metrics['hodl_cagr']:>8.2f}%
      Max Drawdown:    {metrics['hodl_max_drawdown']:>8.2f}%

    Outperformance:    {metrics['outperformance']:>8.2f}%

    Trading Activity:
      Rebalances:      {metrics['num_rebalances']:>8.0f}
      Avg Days/Trade:  {metrics['rebalance_frequency']:>8.1f}
    """

    ax6.text(0.1, 0.9, metrics_text, transform=ax6.transAxes,
             fontsize=10, verticalalignment='top', fontfamily='monospace',
             bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.3))

    plt.tight_layout()
    plt.savefig(save_path, dpi=300, bbox_inches='tight')
    print(f"\n  Results saved to: {save_path}")

    return fig


def print_metrics(metrics: Dict, asset_name: str = 'ADA'):
    """Print performance metrics in formatted table."""

    print("\n" + "="*70)
    print(f"CHAOS TOKEN BACKTEST RESULTS — {asset_name}")
    print("="*70)

    print("\n  RETURNS:")
    print(f"   CHAOS Total Return:     {metrics['chaos_total_return']:>10.2f}%")
    print(f"   HODL Total Return:      {metrics['hodl_total_return']:>10.2f}%")
    print(f"   Outperformance:         {metrics['outperformance']:>10.2f}%")
    print(f"\n   CHAOS CAGR:             {metrics['chaos_cagr']:>10.2f}%")
    print(f"   HODL CAGR:              {metrics['hodl_cagr']:>10.2f}%")

    print("\n  RISK METRICS:")
    print(f"   CHAOS Volatility:       {metrics['chaos_volatility']:>10.2f}%")
    print(f"   CHAOS Max Drawdown:     {metrics['chaos_max_drawdown']:>10.2f}%")
    print(f"   HODL Max Drawdown:      {metrics['hodl_max_drawdown']:>10.2f}%")

    print("\n  RISK-ADJUSTED:")
    print(f"   CHAOS Sharpe Ratio:     {metrics['chaos_sharpe']:>10.2f}")

    print("\n  TRADING ACTIVITY:")
    print(f"   Total Rebalances:       {metrics['num_rebalances']:>10.0f}")
    print(f"   Avg Days per Trade:     {metrics['rebalance_frequency']:>10.1f}")

    print("\n" + "="*70)

    print("\n  VERDICT:")
    if metrics['outperformance'] > 10:
        print("   CHAOS strategy SIGNIFICANTLY outperforms HODL")
    elif metrics['outperformance'] > 0:
        print("   CHAOS strategy outperforms HODL")
    else:
        print("   CHAOS strategy underperforms HODL in this period")

    if metrics['chaos_sharpe'] > 2.0:
        print("   Excellent risk-adjusted returns (Sharpe > 2.0)")
    elif metrics['chaos_sharpe'] > 1.0:
        print("   Good risk-adjusted returns (Sharpe > 1.0)")
    else:
        print("   Modest risk-adjusted returns (Sharpe < 1.0)")

    print("="*70 + "\n")


def main():
    parser = argparse.ArgumentParser(description='CHAOS Single-Asset Backtest')
    parser.add_argument('--coin', default='cardano', help='CoinGecko coin ID (default: cardano)')
    parser.add_argument('--days', type=int, default=365, help='Days of history (default: 365)')
    parser.add_argument('--capital', type=float, default=100_000, help='Initial capital')
    args = parser.parse_args()

    coin_id = args.coin
    info = COIN_REGISTRY.get(coin_id, (coin_id.upper(), coin_id.title(), 0.10))
    ticker, name, lp_apy = info

    print(f"\n  CHAOS TOKEN BACKTEST — {name} ({ticker})\n")

    # 1. Fetch data
    fetcher = CryptoDataFetcher()
    data = fetcher.get_all_data(coin_id=coin_id, days=args.days)

    # 2. Initialize strategy
    strategy = CHAOSStrategy(
        asset_name=ticker,
        initial_capital=args.capital,
        target_asset_allocation=0.50,
        target_stable_allocation=0.30,
        target_lp_allocation=0.20,
        rebalance_threshold=0.10,
        ma_window=30,
        buy_threshold=0.90,
        sell_threshold=1.10,
        tx_cost=0.004,
        lp_apy_default=lp_apy,
    )

    # 3. Run backtest
    results = strategy.backtest(
        price_data=data['price'],
        lp_data=data['lp'],
        stable_data=data['stable'],
    )

    # 4. Calculate metrics
    metrics = calculate_performance_metrics(results)

    # 5. Print results
    print_metrics(metrics, asset_name=ticker)

    # 6. Generate plots
    plot_results(results, metrics, asset_name=ticker)

    # 7. Save results
    results.to_csv('chaos_backtest_data.csv')
    print(f"  Detailed results saved to: chaos_backtest_data.csv")
    print(f"\n  Backtest complete!")

    return results, metrics


if __name__ == "__main__":
    results, metrics = main()
