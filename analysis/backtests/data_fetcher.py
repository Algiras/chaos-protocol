"""
CHAOS Token Backtesting - Data Fetcher

Fetches historical price data from CoinGecko for any supported cryptocurrency.
"""

import os
import requests
import pandas as pd
import numpy as np
from datetime import datetime, timedelta
from typing import Dict, Optional
from dotenv import load_dotenv
import time

load_dotenv()

# Well-known CoinGecko IDs for popular assets
COIN_REGISTRY = {
    # ID            : (ticker, display name, typical LP APY estimate)
    'cardano':       ('ADA',  'Cardano',           0.20),
    'bitcoin':       ('BTC',  'Bitcoin',            0.05),
    'ethereum':      ('ETH',  'Ethereum',           0.08),
    'solana':        ('SOL',  'Solana',             0.12),
    'polkadot':      ('DOT',  'Polkadot',           0.15),
    'avalanche-2':   ('AVAX', 'Avalanche',          0.10),
    'chainlink':     ('LINK', 'Chainlink',          0.06),
    'dogecoin':      ('DOGE', 'Dogecoin',           0.04),
    'ripple':        ('XRP',  'XRP',                0.06),
    'matic-network': ('MATIC','Polygon',            0.10),
    'cosmos':        ('ATOM', 'Cosmos',             0.10),
    'near':          ('NEAR', 'NEAR Protocol',      0.12),
    'sui':           ('SUI',  'Sui',                0.15),
    'aptos':         ('APT',  'Aptos',              0.12),
}


class CryptoDataFetcher:
    """Fetch historical crypto data from CoinGecko (works for any supported coin)."""

    COINGECKO_API = 'https://api.coingecko.com/api/v3'

    def __init__(self, coingecko_api_key: Optional[str] = None):
        self.api_key = coingecko_api_key or os.getenv('COINGECKO_API_KEY')

    def _get_headers(self) -> dict:
        if self.api_key:
            return {'x-cg-demo-api-key': self.api_key}
        return {}

    def fetch_price_history(
        self,
        coin_id: str = 'cardano',
        days: int = 365,
        vs_currency: str = 'usd',
    ) -> pd.DataFrame:
        """
        Fetch price history from CoinGecko for any coin.

        Args:
            coin_id: CoinGecko coin ID (e.g. 'cardano', 'bitcoin', 'ethereum')
            days: Number of days of history
            vs_currency: Quote currency

        Returns:
            DataFrame with columns: price, market_cap, volume, returns, volatility_30d
        """
        info = COIN_REGISTRY.get(coin_id, (coin_id.upper(), coin_id.title(), 0.10))
        ticker = info[0]
        print(f"Fetching {days} days of {ticker} price history...")

        url = f"{self.COINGECKO_API}/coins/{coin_id}/market_chart"
        params = {
            'vs_currency': vs_currency,
            'days': days,
            'interval': 'daily',
        }

        try:
            time.sleep(1.5)  # rate-limit courtesy
            response = requests.get(url, params=params, headers=self._get_headers(), timeout=30)
            response.raise_for_status()
            data = response.json()

            df = pd.DataFrame({
                'timestamp': [x[0] for x in data['prices']],
                'price':      [x[1] for x in data['prices']],
                'market_cap': [x[1] for x in data['market_caps']],
                'volume':     [x[1] for x in data['total_volumes']],
            })
            df['timestamp'] = pd.to_datetime(df['timestamp'], unit='ms')
            df.set_index('timestamp', inplace=True)

            df['returns'] = df['price'].pct_change()
            df['volatility_30d'] = df['returns'].rolling(window=30).std() * np.sqrt(365)

            print(f"  Fetched {len(df)} data points for {ticker}")
            print(f"  Price range: ${df['price'].min():.4f} - ${df['price'].max():.4f}")
            print(f"  Avg 30d vol: {df['volatility_30d'].mean():.1%}")
            return df

        except Exception as e:
            print(f"  CoinGecko error for {coin_id}: {e}")
            print(f"  Falling back to simulated data for {ticker}")
            return self._simulate_price_history(coin_id, days)

    def simulate_lp_fees(self, coin_id: str = 'cardano', days: int = 365) -> pd.DataFrame:
        """Simulate LP fee APY data."""
        info = COIN_REGISTRY.get(coin_id, (coin_id.upper(), coin_id.title(), 0.10))
        base_apy = info[2]

        dates = pd.date_range(end=datetime.now(), periods=days, freq='D')
        np.random.seed(abs(hash(coin_id)) % (2**31))
        volatility_factor = 1 + 0.5 * np.random.randn(len(dates))

        return pd.DataFrame({
            'lp_fee_apy': base_apy * np.abs(volatility_factor),
        }, index=pd.DatetimeIndex(dates, name='timestamp'))

    def simulate_stable_price(self, days: int = 365) -> pd.DataFrame:
        """Simulate stablecoin price (tight peg around $1)."""
        dates = pd.date_range(end=datetime.now(), periods=days, freq='D')
        np.random.seed(42)
        prices = 1.0 + 0.005 * np.random.randn(len(dates))

        return pd.DataFrame({
            'stable_price': prices,
        }, index=pd.DatetimeIndex(dates, name='timestamp'))

    def _simulate_price_history(self, coin_id: str, days: int = 365) -> pd.DataFrame:
        """Simulate realistic price history when API is unavailable."""
        dates = pd.date_range(end=datetime.now(), periods=days, freq='D')
        np.random.seed(abs(hash(coin_id)) % (2**31))

        # Different starting prices per coin
        start_prices = {
            'cardano': 0.65, 'bitcoin': 42000, 'ethereum': 2200,
            'solana': 100, 'polkadot': 7, 'avalanche-2': 35,
            'dogecoin': 0.08, 'ripple': 0.55, 'chainlink': 14,
        }
        start = start_prices.get(coin_id, 10.0)

        # Bear → recovery shape
        trend = np.concatenate([
            np.linspace(1.0, 0.35, days // 2),
            np.linspace(0.35, 0.70, days - days // 2),
        ])
        daily_returns = np.random.normal(0, 0.025, days)
        price_mult = np.exp(np.cumsum(daily_returns))
        prices = start * trend * price_mult / price_mult[0]

        volume = 500e6 + 300e6 * np.abs(np.random.randn(days))

        df = pd.DataFrame({
            'price': prices,
            'market_cap': prices * 1e9,
            'volume': volume,
        }, index=pd.DatetimeIndex(dates, name='timestamp'))

        df['returns'] = df['price'].pct_change()
        df['volatility_30d'] = df['returns'].rolling(window=30).std() * np.sqrt(365)

        info = COIN_REGISTRY.get(coin_id, (coin_id.upper(),))
        print(f"  Simulated {len(df)} days for {info[0]}")
        print(f"  Price range: ${df['price'].min():.4f} - ${df['price'].max():.4f}")
        return df

    def get_all_data(
        self,
        coin_id: str = 'cardano',
        days: int = 365,
    ) -> Dict[str, pd.DataFrame]:
        """
        Fetch all data needed for backtesting a given coin.

        Returns dict with keys: 'price', 'lp', 'stable'
        """
        return {
            'price':  self.fetch_price_history(coin_id=coin_id, days=days),
            'lp':     self.simulate_lp_fees(coin_id=coin_id, days=days),
            'stable': self.simulate_stable_price(days=days),
        }


# Backwards-compatible alias
CardanoDataFetcher = CryptoDataFetcher


if __name__ == "__main__":
    fetcher = CryptoDataFetcher()
    for coin in ['cardano', 'bitcoin', 'ethereum']:
        data = fetcher.get_all_data(coin_id=coin, days=365)
        print(f"\n{coin}: {len(data['price'])} price points\n")
