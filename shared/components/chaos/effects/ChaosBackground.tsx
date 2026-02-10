'use client';

import React, { useMemo } from 'react';
import { motion } from 'framer-motion';

interface ChaosBackgroundProps {
  /** Intensity of the chaos effect (0-1) */
  intensity?: number;
  /** Color palette */
  colors?: string[];
  /** Number of chaos elements */
  elementCount?: number;
  className?: string;
}

/**
 * ChaosBackground Component
 *
 * Creates an animated background with chaos-inspired moving shapes
 */
export const ChaosBackground: React.FC<ChaosBackgroundProps> = ({
  intensity = 0.5,
  colors = ['#2B5278', '#6366F1', '#5B8AB8', '#14B8A6', '#8B5CF6'],
  elementCount = 15,
  className = '',
}) => {
  const elements = useMemo(() => {
    return Array.from({ length: elementCount }, (_, i) => ({
      id: i,
      x: Math.random() * 100,
      y: Math.random() * 100,
      size: 50 + Math.random() * 200,
      duration: 15 + Math.random() * 20,
      delay: Math.random() * 5,
      color: colors[Math.floor(Math.random() * colors.length)],
      blur: 60 + Math.random() * 80,
    }));
  }, [elementCount, colors]);

  return (
    <div className={`absolute inset-0 overflow-hidden ${className}`}>
      {elements.map((element) => (
        <motion.div
          key={element.id}
          className="absolute rounded-full"
          style={{
            width: element.size,
            height: element.size,
            background: `radial-gradient(circle, ${element.color}40 0%, transparent 70%)`,
            filter: `blur(${element.blur}px)`,
            left: `${element.x}%`,
            top: `${element.y}%`,
          }}
          animate={{
            x: [
              0,
              Math.random() * 100 - 50,
              Math.random() * -100 + 50,
              0,
            ],
            y: [
              0,
              Math.random() * 100 - 50,
              Math.random() * -100 + 50,
              0,
            ],
            scale: [1, 1.2, 0.8, 1],
            opacity: [0.3 * intensity, 0.6 * intensity, 0.3 * intensity],
          }}
          transition={{
            duration: element.duration,
            delay: element.delay,
            repeat: Infinity,
            ease: 'easeInOut',
          }}
        />
      ))}
    </div>
  );
};

export default ChaosBackground;
