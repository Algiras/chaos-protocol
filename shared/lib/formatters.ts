/**
 * Shared formatting utilities for the CHAOS app.
 */

type CurrencyCode = 'USD' | 'EUR' | 'GBP' | 'ADA';

/** Format a number as currency (no decimals). Defaults to USD. */
export function formatCurrency(
  value: number,
  currency: CurrencyCode = 'USD',
): string {
  return new Intl.NumberFormat('en-US', {
    style: 'currency',
    currency,
    minimumFractionDigits: 0,
    maximumFractionDigits: 0,
  }).format(value);
}

/** Format a number as a percentage with sign prefix */
export function formatPercent(value: number): string {
  const sign = value >= 0 ? '+' : '';
  return `${sign}${value.toFixed(2)}%`;
}

/** Format a number with comma separators */
export function formatNumber(num: number): string {
  return new Intl.NumberFormat('en-US').format(num);
}

/** Format an ISO date string to "Jan 15, 2025" style */
export function formatDate(dateStr: string): string {
  const date = new Date(dateStr);
  return date.toLocaleDateString('en-US', {
    month: 'short',
    day: 'numeric',
    year: 'numeric',
  });
}
