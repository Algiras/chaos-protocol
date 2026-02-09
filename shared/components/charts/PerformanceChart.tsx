import { motion } from 'framer-motion';

interface PerformanceChartProps {
  data: {
    date: string;
    chaos: number;
    hodl: number;
  }[];
  currentIndex: number;
  totalDataPoints: number;
  currentValue?: number;
  height?: number;
  showHodl?: boolean;
  maxValue?: number;
  minValue?: number;
}

export function PerformanceChart({
  data,
  currentIndex,
  totalDataPoints,
  currentValue,
  height = 300,
  showHodl = true,
  maxValue = 50000,
  minValue = 5000,
}: PerformanceChartProps) {
  const padding = { top: 20, right: 20, bottom: 40, left: 60 };
  const chartWidth = 1000;
  const chartHeight = 300;
  
  // Calculate scales
  const valueRange = maxValue - minValue;
  
  const getX = (index: number) => {
    return padding.left + (index / (totalDataPoints - 1)) * (chartWidth - padding.left - padding.right);
  };
  
  const getY = (value: number) => {
    return padding.top + (1 - (value - minValue) / valueRange) * (chartHeight - padding.top - padding.bottom);
  };

  // Generate Y-axis labels
  const yLabels = [minValue, minValue + valueRange * 0.25, minValue + valueRange * 0.5, minValue + valueRange * 0.75, maxValue];
  
  // Generate X-axis labels (years)
  const years = ['2018', '2019', '2020', '2021', '2022', '2023', '2024', '2025'];

  return (
    <div className="w-full" style={{ height }}>
      <svg 
        viewBox={`0 0 ${chartWidth} ${chartHeight}`} 
        className="w-full h-full"
        preserveAspectRatio="xMidYMid meet"
      >
        {/* Grid lines */}
        {yLabels.map((value, i) => {
          const y = getY(value);
          return (
            <g key={i}>
              <line
                x1={padding.left}
                y1={y}
                x2={chartWidth - padding.right}
                y2={y}
                stroke="#e5e7eb"
                strokeWidth="1"
                strokeDasharray={i === 0 || i === yLabels.length - 1 ? '0' : '4,4'}
              />
            </g>
          );
        })}

        {/* CHAOS Strategy Line */}
        {data.length > 1 && (
          <motion.path
            d={`M ${data.map((d, i) => {
              const x = getX(i);
              const y = getY(d.chaos);
              return `${i === 0 ? '' : 'L '}${x} ${y}`;
            }).join(' ')}`}
            fill="none"
            stroke="url(#chaosGradient)"
            strokeWidth="3"
            strokeLinecap="round"
            strokeLinejoin="round"
            initial={{ pathLength: 0 }}
            animate={{ pathLength: data.length / totalDataPoints }}
            transition={{ duration: 0.3, ease: 'linear' }}
          />
        )}

        {/* HODL Line */}
        {showHodl && data.length > 1 && (
          <motion.path
            d={`M ${data.map((d, i) => {
              const x = getX(i);
              const y = getY(d.hodl);
              return `${i === 0 ? '' : 'L '}${x} ${y}`;
            }).join(' ')}`}
            fill="none"
            stroke="#9ca3af"
            strokeWidth="2"
            strokeDasharray="6,4"
            strokeLinecap="round"
            strokeLinejoin="round"
            initial={{ pathLength: 0 }}
            animate={{ pathLength: data.length / totalDataPoints }}
            transition={{ duration: 0.3, ease: 'linear' }}
          />
        )}

        {/* Current Position Indicator */}
        {currentValue && currentIndex < data.length && (
          <motion.g
            initial={{ opacity: 0 }}
            animate={{ opacity: 1 }}
            transition={{ duration: 0.2 }}
          >
            <circle
              cx={getX(currentIndex)}
              cy={getY(currentValue)}
              r="8"
              fill="#3b82f6"
              stroke="white"
              strokeWidth="3"
              className="drop-shadow-lg"
            />
            {/* Value label */}
            <g transform={`translate(${getX(currentIndex) + 15}, ${getY(currentValue) - 10})`}>
              <rect
                x="-5"
                y="-20"
                width="80"
                height="24"
                rx="4"
                fill="#1f2937"
              />
              <text
                x="35"
                y="-4"
                textAnchor="middle"
                fill="white"
                fontSize="12"
                fontWeight="600"
              >
                ${(currentValue / 1000).toFixed(1)}K
              </text>
            </g>
          </motion.g>
        )}

        {/* Y-axis labels */}
        {yLabels.map((value, i) => (
          <text
            key={`ylabel-${i}`}
            x={padding.left - 10}
            y={getY(value) + 4}
            textAnchor="end"
            fill="#6b7280"
            fontSize="11"
            fontWeight="500"
          >
            ${value >= 1000 ? `${(value / 1000).toFixed(0)}K` : value}
          </text>
        ))}

        {/* X-axis labels */}
        {years.map((year, i) => {
          const x = padding.left + (i / (years.length - 1)) * (chartWidth - padding.left - padding.right);
          return (
            <text
              key={`xlabel-${year}`}
              x={x}
              y={chartHeight - 10}
              textAnchor="middle"
              fill="#6b7280"
              fontSize="11"
              fontWeight="500"
            >
              {year}
            </text>
          );
        })}

        {/* Gradient definition */}
        <defs>
          <linearGradient id="chaosGradient" x1="0%" y1="0%" x2="100%" y2="0%">
            <stop offset="0%" stopColor="#3b82f6" />
            <stop offset="50%" stopColor="#8b5cf6" />
            <stop offset="100%" stopColor="#9333ea" />
          </linearGradient>
          
          {/* Area fill gradient */}
          <linearGradient id="areaGradient" x1="0%" y1="0%" x2="0%" y2="100%">
            <stop offset="0%" stopColor="#3b82f6" stopOpacity="0.2" />
            <stop offset="100%" stopColor="#3b82f6" stopOpacity="0" />
          </linearGradient>
        </defs>

        {/* Area fill under CHAOS line */}
        {data.length > 1 && (
          <motion.path
            d={`M ${getX(0)} ${getY(minValue)} L ${data.map((d, i) => `${getX(i)} ${getY(d.chaos)}`).join(' L ')} L ${getX(data.length - 1)} ${getY(minValue)} Z`}
            fill="url(#areaGradient)"
            initial={{ opacity: 0 }}
            animate={{ opacity: 1 }}
            transition={{ duration: 0.5 }}
          />
        )}
      </svg>
    </div>
  );
}


