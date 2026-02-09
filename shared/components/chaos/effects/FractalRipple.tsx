'use client';

import React, { useEffect, useState } from 'react';

interface FractalRippleProps {
  /** X position of ripple origin (relative to container) */
  x: number;
  /** Y position of ripple origin (relative to container) */
  y: number;
  /** Color of the ripple */
  color?: string;
  /** Duration of the animation in milliseconds */
  duration?: number;
  /** Number of concentric ripples */
  ripples?: number;
  /** Callback when animation completes */
  onComplete?: () => void;
}

/**
 * FractalRipple Component
 *
 * Creates a fractal-inspired ripple effect that emanates from a cursor position.
 * Uses multiple concentric circles with varying delays and scales to create
 * a self-similar, organic ripple pattern inspired by fractals.
 */
export const FractalRipple: React.FC<FractalRippleProps> = ({
  x,
  y,
  color = 'rgba(123, 44, 191, 0.4)', // chaos purple
  duration = 600,
  ripples = 3,
  onComplete,
}) => {
  const [isAnimating, setIsAnimating] = useState(true);

  useEffect(() => {
    const timer = setTimeout(() => {
      setIsAnimating(false);
      onComplete?.();
    }, duration);

    return () => clearTimeout(timer);
  }, [duration, onComplete]);

  if (!isAnimating) return null;

  return (
    <div className="absolute inset-0 pointer-events-none overflow-hidden">
      {Array.from({ length: ripples }).map((_, index) => {
        const delay = index * (duration / (ripples * 2));
        const scale = 1 + index * 0.5;

        return (
          <div
            key={index}
            className="absolute rounded-full border-2 animate-fractal-ripple"
            style={{
              left: x,
              top: y,
              borderColor: color,
              transform: 'translate(-50%, -50%)',
              animation: `fractal-ripple ${duration}ms cubic-bezier(0.4, 0, 0.2, 1) ${delay}ms forwards`,
              width: '20px',
              height: '20px',
            }}
          />
        );
      })}

      {/* Add fractal-inspired particles */}
      {Array.from({ length: 8 }).map((_, index) => {
        const angle = (index * Math.PI * 2) / 8;
        const distance = 30;
        const particleX = x + Math.cos(angle) * distance;
        const particleY = y + Math.sin(angle) * distance;
        const delay = duration / 3;

        return (
          <div
            key={`particle-${index}`}
            className="absolute rounded-full"
            style={{
              left: particleX,
              top: particleY,
              width: '4px',
              height: '4px',
              backgroundColor: color,
              transform: 'translate(-50%, -50%)',
              animation: `fractal-particle ${duration}ms cubic-bezier(0.4, 0, 0.2, 1) ${delay}ms forwards`,
            }}
          />
        );
      })}

      <style jsx>{`
        @keyframes fractal-ripple {
          0% {
            transform: translate(-50%, -50%) scale(0);
            opacity: 1;
          }
          100% {
            transform: translate(-50%, -50%) scale(4);
            opacity: 0;
          }
        }

        @keyframes fractal-particle {
          0% {
            transform: translate(-50%, -50%) scale(1);
            opacity: 1;
          }
          50% {
            transform: translate(-50%, -50%) scale(1.5);
            opacity: 0.8;
          }
          100% {
            transform: translate(-50%, -50%) scale(0);
            opacity: 0;
          }
        }

        @media (prefers-reduced-motion: reduce) {
          .animate-fractal-ripple {
            animation: none !important;
          }
        }
      `}</style>
    </div>
  );
};

/**
 * Hook for managing fractal ripple effects
 *
 * Usage:
 * const { ripples, addRipple } = useFractalRipple();
 *
 * return (
 *   <div onClick={(e) => addRipple(e.clientX, e.clientY)}>
 *     {ripples}
 *   </div>
 * );
 */
export const useFractalRipple = () => {
  const [ripples, setRipples] = useState<Array<{ id: number; x: number; y: number }>>([]);

  const addRipple = (x: number, y: number) => {
    const id = Date.now();
    setRipples((prev) => [...prev, { id, x, y }]);
  };

  const removeRipple = (id: number) => {
    setRipples((prev) => prev.filter((ripple) => ripple.id !== id));
  };

  const rippleElements = ripples.map((ripple) => (
    <FractalRipple
      key={ripple.id}
      x={ripple.x}
      y={ripple.y}
      onComplete={() => removeRipple(ripple.id)}
    />
  ));

  return { ripples: rippleElements, addRipple };
};

export default FractalRipple;
