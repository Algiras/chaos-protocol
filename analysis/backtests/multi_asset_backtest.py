"""
CHAOS Multi-Asset Backtest

Run the CHAOS volatility-harvesting strategy across multiple cryptocurrencies
and compare results. Proves the strategy is asset-agnostic.

Usage:
    python multi_asset_backtest.py                         # default 5 coins, 365 days
    python multi_asset_backtest.py --coins cardano bitcoin ethereum solana polkadot
    python multi_asset_backtest.py --days 730 --coins cardano bitcoin
"""

import argparse
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
from typing import Dict, List
from data_fetcher import CryptoDataFetcher, COIN_REGISTRY
from chaos_strategy import CHAOSStrategy
import warnings
warnings.filterwarnings('ignore')


# ---------------------------------------------------------------------------
#  Metrics
# ---------------------------------------------------------------------------

def compute_metrics(results: pd.DataFrame, asset_name: str) -> Dict:
    """Compute standard performance metrics from a backtest results DataFrame."""
    rets = results['returns'].dropna()
    chaos_final = results['portfolio_value'].iloc[-1]
    chaos_init = results['portfolio_value'].iloc[0]
    hodl_final = results['hodl_value'].iloc[-1]
    hodl_init = results['hodl_value'].iloc[0]

    days = len(results)
    years = max(days / 365, 0.01)

    vol = rets.std() * np.sqrt(365) if len(rets) > 1 else 0
    sharpe = (rets.mean() * 365) / (vol / 100) if vol > 0 else 0

    chaos_dd = (results['portfolio_value'] / results['portfolio_value'].cummax() - 1).min() * 100
    hodl_dd = (results['hodl_value'] / results['hodl_value'].cummax() - 1).min() * 100

    return {
        'asset': asset_name,
        'chaos_return': (chaos_final / chaos_init - 1) * 100,
        'hodl_return': (hodl_final / hodl_init - 1) * 100,
        'outperformance': ((chaos_final / chaos_init) / (hodl_final / hodl_init) - 1) * 100,
        'chaos_cagr': ((chaos_final / chaos_init) ** (1 / years) - 1) * 100,
        'hodl_cagr': ((hodl_final / hodl_init) ** (1 / years) - 1) * 100,
        'chaos_vol': vol * 100 if vol < 1 else vol,
        'chaos_sharpe': sharpe,
        'chaos_max_dd': chaos_dd,
        'hodl_max_dd': hodl_dd,
        'dd_reduction': hodl_dd - chaos_dd,  # positive = CHAOS protects more
        'n_rebalances': int(results['rebalanced'].sum()),
        'days': days,
    }


# ---------------------------------------------------------------------------
#  Plotting
# ---------------------------------------------------------------------------

def plot_multi_asset(
    all_results: Dict[str, pd.DataFrame],
    all_metrics: List[Dict],
    save_path: str = 'multi_asset_backtest.png',
):
    """Generate a comprehensive multi-asset comparison chart."""

    n = len(all_results)
    fig = plt.figure(figsize=(18, 5 * ((n + 1) // 2 + 2)))
    gs = fig.add_gridspec(
        nrows=(n + 1) // 2 + 2, ncols=2,
        hspace=0.40, wspace=0.28,
    )

    colors_chaos = '#2563eb'
    colors_hodl = '#dc2626'

    # --- Per-asset panels: cumulative return ---
    for i, (coin_id, df) in enumerate(all_results.items()):
        row, col = divmod(i, 2)
        ax = fig.add_subplot(gs[row, col])

        ax.plot(df.index, df['cumulative_return'], linewidth=2, color=colors_chaos, label='CHAOS')
        ax.plot(df.index, df['hodl_return'], linewidth=2, color=colors_hodl, linestyle='--', label='HODL')
        ax.axhline(0, color='gray', linewidth=0.8)
        ax.fill_between(
            df.index,
            df['cumulative_return'],
            df['hodl_return'],
            where=(df['cumulative_return'] > df['hodl_return']),
            interpolate=True, alpha=0.15, color='green',
        )
        ax.fill_between(
            df.index,
            df['cumulative_return'],
            df['hodl_return'],
            where=(df['cumulative_return'] < df['hodl_return']),
            interpolate=True, alpha=0.15, color='red',
        )
        info = COIN_REGISTRY.get(coin_id, (coin_id.upper(), coin_id.title(), 0))
        ax.set_title(f'{info[1]} ({info[0]})', fontsize=12, fontweight='bold')
        ax.set_ylabel('Cumulative Return (%)')
        ax.legend(fontsize=9)
        ax.grid(True, alpha=0.2)

    # --- Summary bar chart: outperformance ---
    summary_row = (n + 1) // 2
    ax_bar = fig.add_subplot(gs[summary_row, 0])

    names = [m['asset'] for m in all_metrics]
    outperf = [m['outperformance'] for m in all_metrics]
    bar_colors = ['#10b981' if o >= 0 else '#dc2626' for o in outperf]

    bars = ax_bar.barh(names, outperf, color=bar_colors, edgecolor='black', linewidth=0.8)
    ax_bar.axvline(0, color='black', linewidth=0.8)
    ax_bar.set_xlabel('CHAOS Outperformance vs HODL (%)')
    ax_bar.set_title('Strategy Outperformance by Asset', fontsize=12, fontweight='bold')
    ax_bar.grid(axis='x', alpha=0.2)

    for bar, val in zip(bars, outperf):
        ax_bar.text(
            bar.get_width() + (1 if val >= 0 else -1),
            bar.get_y() + bar.get_height() / 2,
            f'{val:+.1f}%', va='center', fontsize=10, fontweight='bold',
        )

    # --- Summary bar chart: Sharpe ratio ---
    ax_sharpe = fig.add_subplot(gs[summary_row, 1])

    sharpes = [m['chaos_sharpe'] for m in all_metrics]
    s_colors = ['#2563eb' if s >= 1.0 else '#f59e0b' if s >= 0 else '#dc2626' for s in sharpes]

    bars_s = ax_sharpe.barh(names, sharpes, color=s_colors, edgecolor='black', linewidth=0.8)
    ax_sharpe.axvline(1.0, color='gray', linestyle='--', alpha=0.5)
    ax_sharpe.axvline(2.0, color='#10b981', linestyle='--', alpha=0.5)
    ax_sharpe.set_xlabel('Sharpe Ratio')
    ax_sharpe.set_title('Risk-Adjusted Returns (Sharpe)', fontsize=12, fontweight='bold')
    ax_sharpe.grid(axis='x', alpha=0.2)

    # --- Drawdown comparison ---
    ax_dd = fig.add_subplot(gs[summary_row + 1, 0])
    x = np.arange(len(names))
    w = 0.35

    chaos_dd = [m['chaos_max_dd'] for m in all_metrics]
    hodl_dd_vals = [m['hodl_max_dd'] for m in all_metrics]

    ax_dd.barh(x - w / 2, chaos_dd, w, label='CHAOS Max DD', color='#2563eb', edgecolor='black', linewidth=0.8)
    ax_dd.barh(x + w / 2, hodl_dd_vals, w, label='HODL Max DD', color='#dc2626', edgecolor='black', linewidth=0.8)
    ax_dd.set_yticks(x)
    ax_dd.set_yticklabels(names)
    ax_dd.set_xlabel('Maximum Drawdown (%)')
    ax_dd.set_title('Drawdown Protection: CHAOS vs HODL', fontsize=12, fontweight='bold')
    ax_dd.legend(fontsize=9)
    ax_dd.grid(axis='x', alpha=0.2)

    # --- Volatility scatter ---
    ax_vol = fig.add_subplot(gs[summary_row + 1, 1])

    vols = [m['chaos_vol'] for m in all_metrics]
    rets_chaos = [m['chaos_return'] for m in all_metrics]
    rets_hodl = [m['hodl_return'] for m in all_metrics]

    ax_vol.scatter(vols, rets_chaos, s=120, c='#2563eb', edgecolors='black', linewidths=1, zorder=5, label='CHAOS')
    for i, name in enumerate(names):
        ax_vol.annotate(name, (vols[i], rets_chaos[i]), textcoords='offset points', xytext=(8, 4), fontsize=9)

    ax_vol.set_xlabel('Annualized Volatility (%)')
    ax_vol.set_ylabel('Total Return (%)')
    ax_vol.set_title('Risk-Return Scatter', fontsize=12, fontweight='bold')
    ax_vol.legend(fontsize=9)
    ax_vol.grid(True, alpha=0.2)

    fig.suptitle(
        'CHAOS Volatility Harvesting — Multi-Asset Comparison',
        fontsize=16, fontweight='bold', y=1.0,
    )

    plt.savefig(save_path, dpi=200, bbox_inches='tight')
    print(f"\n  Chart saved: {save_path}")
    return fig


def print_summary_table(metrics_list: List[Dict]):
    """Print a formatted summary table."""
    print("\n" + "=" * 100)
    print("MULTI-ASSET BACKTEST SUMMARY")
    print("=" * 100)

    header = (
        f"{'Asset':<10} {'CHAOS':>8} {'HODL':>8} {'Outperf':>8} "
        f"{'Sharpe':>7} {'CHAOS DD':>9} {'HODL DD':>8} {'Rebals':>7} {'Days':>5}"
    )
    print(header)
    print("-" * 100)

    for m in metrics_list:
        row = (
            f"{m['asset']:<10} "
            f"{m['chaos_return']:>+7.1f}% "
            f"{m['hodl_return']:>+7.1f}% "
            f"{m['outperformance']:>+7.1f}% "
            f"{m['chaos_sharpe']:>7.2f} "
            f"{m['chaos_max_dd']:>+8.1f}% "
            f"{m['hodl_max_dd']:>+7.1f}% "
            f"{m['n_rebalances']:>7} "
            f"{m['days']:>5}"
        )
        print(row)

    print("-" * 100)

    # Aggregate
    avg_outperf = np.mean([m['outperformance'] for m in metrics_list])
    avg_sharpe = np.mean([m['chaos_sharpe'] for m in metrics_list])
    win_rate = sum(1 for m in metrics_list if m['outperformance'] > 0) / len(metrics_list)
    avg_dd_reduction = np.mean([m['dd_reduction'] for m in metrics_list])

    print(f"\n  Average outperformance:  {avg_outperf:+.1f}%")
    print(f"  Average Sharpe ratio:    {avg_sharpe:.2f}")
    print(f"  Win rate (vs HODL):      {win_rate:.0%} ({sum(1 for m in metrics_list if m['outperformance'] > 0)}/{len(metrics_list)})")
    print(f"  Avg DD reduction:        {avg_dd_reduction:+.1f} pp")

    if avg_outperf > 0:
        print("\n  VERDICT: CHAOS strategy outperforms HODL on average across assets.")
        print("  The volatility harvesting effect is ASSET-AGNOSTIC.")
    else:
        print("\n  VERDICT: Mixed results — strategy may need parameter tuning per asset.")

    print("=" * 100 + "\n")


# ---------------------------------------------------------------------------
#  Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description='CHAOS Multi-Asset Backtest')
    parser.add_argument(
        '--coins', nargs='+',
        default=['cardano', 'bitcoin', 'ethereum', 'solana', 'polkadot'],
        help='CoinGecko coin IDs to backtest',
    )
    parser.add_argument('--days', type=int, default=365, help='Days of history')
    parser.add_argument('--capital', type=float, default=100_000, help='Initial capital ($)')
    parser.add_argument('--output', default='multi_asset_backtest.png', help='Output chart path')
    parser.add_argument('--csv', default='multi_asset_results.csv', help='Output CSV path')
    args = parser.parse_args()

    print("\n" + "=" * 60)
    print("  CHAOS MULTI-ASSET BACKTEST")
    print(f"  Assets: {', '.join(args.coins)}")
    print(f"  Period: {args.days} days | Capital: ${args.capital:,.0f}")
    print("=" * 60 + "\n")

    fetcher = CryptoDataFetcher()
    all_results: Dict[str, pd.DataFrame] = {}
    all_metrics: List[Dict] = []

    for coin_id in args.coins:
        info = COIN_REGISTRY.get(coin_id, (coin_id.upper(), coin_id.title(), 0.10))
        ticker, name, lp_apy = info

        print(f"\n{'─'*50}")
        print(f"  {name} ({ticker})")
        print(f"{'─'*50}")

        data = fetcher.get_all_data(coin_id=coin_id, days=args.days)

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

        results = strategy.backtest(
            price_data=data['price'],
            lp_data=data['lp'],
            stable_data=data['stable'],
            quiet=False,
        )

        metrics = compute_metrics(results, ticker)
        all_results[coin_id] = results
        all_metrics.append(metrics)

    # Summary
    print_summary_table(all_metrics)

    # Chart
    plot_multi_asset(all_results, all_metrics, save_path=args.output)

    # Save CSV
    summary_df = pd.DataFrame(all_metrics)
    summary_df.to_csv(args.csv, index=False)
    print(f"  Summary CSV saved: {args.csv}")

    return all_results, all_metrics


if __name__ == '__main__':
    main()
