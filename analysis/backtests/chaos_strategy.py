"""
CHAOS Token Strategy Implementation

Implements the antifragile volatility harvesting strategy.
Asset-agnostic: works with any volatile asset paired against a stablecoin.
"""

import pandas as pd
import numpy as np
from typing import Dict, Tuple, Optional
from dataclasses import dataclass


@dataclass
class TreasuryState:
    """Current state of the CHAOS treasury."""
    asset_amount: float
    stable_amount: float
    lp_positions: float
    timestamp: pd.Timestamp

    def total_value_usd(self, asset_price: float, stable_price: float = 1.0) -> float:
        """Calculate total treasury value in USD."""
        return (
            self.asset_amount * asset_price +
            self.stable_amount * stable_price +
            self.lp_positions  # LP positions already in USD
        )

    def asset_percentage(self, asset_price: float) -> float:
        """Calculate volatile asset as percentage of treasury."""
        total = self.total_value_usd(asset_price)
        return (self.asset_amount * asset_price) / total if total > 0 else 0


class CHAOSStrategy:
    """
    Volatility Harvesting Antifragile Strategy.

    Core principles:
    1. Buy the volatile asset when it drops below its mean (cheap)
    2. Sell the volatile asset when it rises above its mean (expensive)
    3. Maintain LP positions to earn fees
    4. Rebalance to target allocations

    Works with any volatile asset (ADA, BTC, ETH, SOL, etc.)
    """

    def __init__(
        self,
        asset_name: str = "ADA",
        initial_capital: float = 100000,
        target_asset_allocation: float = 0.50,
        target_stable_allocation: float = 0.30,
        target_lp_allocation: float = 0.20,
        rebalance_threshold: float = 0.10,
        ma_window: int = 30,
        buy_threshold: float = 0.90,
        sell_threshold: float = 1.10,
        tx_cost: float = 0.004,
        lp_apy_default: float = 0.20,
    ):
        self.asset_name = asset_name
        self.initial_capital = initial_capital
        self.target_asset = target_asset_allocation
        self.target_stable = target_stable_allocation
        self.target_lp = target_lp_allocation
        self.rebalance_threshold = rebalance_threshold
        self.ma_window = ma_window
        self.buy_threshold = buy_threshold
        self.sell_threshold = sell_threshold
        self.tx_cost = tx_cost
        self.lp_apy_default = lp_apy_default

        # Performance tracking
        self.trades = []
        self.portfolio_values = []

    def initialize_treasury(self, asset_price: float) -> TreasuryState:
        """Initialize treasury with target allocations."""
        asset_amount = (self.initial_capital * self.target_asset) / asset_price
        stable_amount = self.initial_capital * self.target_stable
        lp_positions = self.initial_capital * self.target_lp

        return TreasuryState(
            asset_amount=asset_amount,
            stable_amount=stable_amount,
            lp_positions=lp_positions,
            timestamp=pd.Timestamp.now()
        )

    def should_rebalance(
        self,
        state: TreasuryState,
        asset_price: float,
        asset_ma: float
    ) -> Tuple[bool, str]:
        """
        Determine if rebalancing is needed.

        Returns:
            (should_rebalance, reason)
        """
        current_pct = state.asset_percentage(asset_price)
        deviation = abs(current_pct - self.target_asset)

        if deviation > self.rebalance_threshold:
            return True, f"Allocation deviation: {deviation:.1%}"

        if asset_price < asset_ma * self.buy_threshold:
            discount = (asset_ma - asset_price) / asset_ma
            return True, f"{self.asset_name} cheap: {discount:.1%} below MA"

        if asset_price > asset_ma * self.sell_threshold:
            premium = (asset_price - asset_ma) / asset_ma
            return True, f"{self.asset_name} expensive: {premium:.1%} above MA"

        return False, "No rebalance needed"

    def execute_rebalance(
        self,
        state: TreasuryState,
        asset_price: float,
        stable_price: float,
        reason: str
    ) -> TreasuryState:
        """Execute rebalancing to target allocations with transaction costs."""
        total_value = state.total_value_usd(asset_price, stable_price)

        target_asset_value = total_value * self.target_asset
        target_stable_value = total_value * self.target_stable
        target_lp_value = total_value * self.target_lp

        current_asset_value = state.asset_amount * asset_price

        # Apply transaction cost on traded volume
        trade_volume = abs(target_asset_value - current_asset_value)
        cost = trade_volume * self.tx_cost
        total_value -= cost

        # Recalculate targets after cost
        target_asset_value = total_value * self.target_asset
        target_stable_value = total_value * self.target_stable
        target_lp_value = total_value * self.target_lp

        new_asset_amount = target_asset_value / asset_price
        new_stable_amount = target_stable_value / stable_price
        new_lp_positions = target_lp_value

        self.trades.append({
            'timestamp': state.timestamp,
            'reason': reason,
            'asset_traded': new_asset_amount - state.asset_amount,
            'asset_price': asset_price,
            'portfolio_value': total_value,
            'tx_cost': cost,
        })

        return TreasuryState(
            asset_amount=new_asset_amount,
            stable_amount=new_stable_amount,
            lp_positions=new_lp_positions,
            timestamp=state.timestamp
        )

    def accrue_lp_fees(
        self,
        state: TreasuryState,
        daily_lp_apy: float
    ) -> TreasuryState:
        """Add LP fee earnings to LP positions."""
        daily_rate = daily_lp_apy / 365
        fee_earnings = state.lp_positions * daily_rate

        return TreasuryState(
            asset_amount=state.asset_amount,
            stable_amount=state.stable_amount,
            lp_positions=state.lp_positions + fee_earnings,
            timestamp=state.timestamp
        )

    def backtest(
        self,
        price_data: pd.DataFrame,
        lp_data: Optional[pd.DataFrame] = None,
        stable_data: Optional[pd.DataFrame] = None,
        quiet: bool = False,
    ) -> pd.DataFrame:
        """
        Run backtest of CHAOS strategy on any asset.

        Args:
            price_data: DataFrame with 'price' column and DatetimeIndex
            lp_data: Optional DataFrame with 'lp_fee_apy' column
            stable_data: Optional DataFrame with 'stable_price' column
            quiet: Suppress verbose output

        Returns:
            DataFrame with daily portfolio values and performance metrics
        """
        if not quiet:
            print("=" * 60)
            print(f"RUNNING CHAOS STRATEGY BACKTEST — {self.asset_name}")
            print("=" * 60)

        data = price_data[['price']].copy()

        # Join optional data
        if lp_data is not None and 'lp_fee_apy' in lp_data.columns:
            data = data.join(lp_data[['lp_fee_apy']], how='left')
        if stable_data is not None and 'stable_price' in stable_data.columns:
            data = data.join(stable_data[['stable_price']], how='left')

        data = data.ffill().bfill()
        data['lp_fee_apy'] = data.get('lp_fee_apy', pd.Series(self.lp_apy_default, index=data.index))
        data['stable_price'] = data.get('stable_price', pd.Series(1.0, index=data.index))
        data.fillna({'lp_fee_apy': self.lp_apy_default, 'stable_price': 1.0}, inplace=True)

        data['asset_ma'] = data['price'].rolling(window=self.ma_window).mean()

        initial_price = data.iloc[self.ma_window]['price']
        state = self.initialize_treasury(initial_price)

        # Reset tracking
        self.trades = []
        self.portfolio_values = []

        for idx in range(self.ma_window, len(data)):
            row = data.iloc[idx]
            state.timestamp = row.name

            asset_price = row['price']
            asset_ma = row['asset_ma']
            stable_price = row['stable_price']
            lp_apy = row['lp_fee_apy']

            state = self.accrue_lp_fees(state, lp_apy)

            should_rebal, reason = self.should_rebalance(state, asset_price, asset_ma)

            if should_rebal:
                state = self.execute_rebalance(state, asset_price, stable_price, reason)

            portfolio_value = state.total_value_usd(asset_price, stable_price)

            self.portfolio_values.append({
                'timestamp': state.timestamp,
                'portfolio_value': portfolio_value,
                'asset_price': asset_price,
                'asset_amount': state.asset_amount,
                'stable_amount': state.stable_amount,
                'lp_positions': state.lp_positions,
                'asset_allocation': state.asset_percentage(asset_price),
                'rebalanced': should_rebal,
            })

        results_df = pd.DataFrame(self.portfolio_values)
        results_df.set_index('timestamp', inplace=True)

        results_df['returns'] = results_df['portfolio_value'].pct_change()
        results_df['cumulative_return'] = (
            (results_df['portfolio_value'] / self.initial_capital - 1) * 100
        )
        results_df['hodl_value'] = (
            self.initial_capital * results_df['asset_price'] / initial_price
        )
        results_df['hodl_return'] = (
            (results_df['hodl_value'] / self.initial_capital - 1) * 100
        )

        if not quiet:
            print(f"\n  Backtest complete: {len(results_df)} days simulated")
            print(f"  Rebalances executed: {len(self.trades)}")

        return results_df


# Backwards-compatible aliases
TreasuryState.ada_amount = property(lambda self: self.asset_amount)
TreasuryState.djed_amount = property(lambda self: self.stable_amount)
TreasuryState.ada_percentage = TreasuryState.asset_percentage


if __name__ == "__main__":
    print("CHAOS Strategy module loaded. Run backtest.py to execute full simulation.")
