import { Card, CardContent } from './card';
import { formatPercent } from '../../lib/formatters';
import { type LucideIcon } from 'lucide-react';

const COLOR_MAP = {
  blue: { bg: 'bg-blue-50', border: 'border-blue-100', icon: 'text-blue-500' },
  gray: { bg: 'bg-gray-50', border: 'border-gray-100', icon: 'text-gray-400' },
  emerald: { bg: 'bg-emerald-50', border: 'border-emerald-100', icon: 'text-emerald-500' },
  rose: { bg: 'bg-rose-50', border: 'border-rose-100', icon: 'text-rose-500' },
  amber: { bg: 'bg-amber-50', border: 'border-amber-100', icon: 'text-amber-500' },
  purple: { bg: 'bg-purple-50', border: 'border-purple-100', icon: 'text-purple-500' },
} as const;

export type StatCardColor = keyof typeof COLOR_MAP;

interface StatCardProps {
  label: string;
  value: string;
  change?: number;
  subtext?: string;
  icon: LucideIcon;
  color: StatCardColor;
}

export function StatCard({
  label,
  value,
  change,
  subtext,
  icon: Icon,
  color,
}: StatCardProps) {
  const colors = COLOR_MAP[color];

  return (
    <Card className={`${colors.bg} ${colors.border} border-2`}>
      <CardContent className="p-3 md:p-4">
        <div className="flex items-start justify-between mb-2">
          <span className="text-xs md:text-sm text-gray-500">{label}</span>
          <Icon className={`w-4 h-4 ${colors.icon}`} />
        </div>
        <div className="text-lg md:text-2xl font-black text-gray-900">{value}</div>
        {change !== undefined && (
          <div
            className={`text-xs md:text-sm font-semibold ${
              change >= 0 ? 'text-emerald-600' : 'text-rose-600'
            }`}
          >
            {formatPercent(change)}
          </div>
        )}
        {subtext && (
          <div className="text-xs text-gray-500 mt-1">{subtext}</div>
        )}
      </CardContent>
    </Card>
  );
}
