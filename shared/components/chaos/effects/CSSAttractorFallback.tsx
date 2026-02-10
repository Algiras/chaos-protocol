'use client';

import React from 'react';
import { motion } from 'framer-motion';

interface CSSAttractorFallbackProps {
  className?: string;
  opacity?: number;
}

/**
 * CSS-based fallback for Lorenz attractor when WebGL fails
 * Creates a visually similar effect using CSS animations
 */
export const CSSAttractorFallback: React.FC<CSSAttractorFallbackProps> = ({
  className = '',
  opacity = 0.6,
}) => {
  // Generate particle positions in a butterfly/lorenz-like pattern
  const particles = Array.from({ length: 150 }, (_, i) => {
    const angle = (i / 150) * Math.PI * 4;
    const radius = 20 + (i % 30);
    const side = i % 2 === 0 ? 1 : -1;

    return {
      id: i,
      x: 50 + Math.cos(angle) * radius * side,
      y: 50 + Math.sin(angle) * radius * 0.6,
      delay: i * 0.03,
      duration: 15 + (i % 8),
      size: 8 + (i % 8), // Much larger particles: 8-16px
    };
  });

  return (
    <div
      className={`absolute inset-0 overflow-hidden ${className}`}
      style={{ opacity }}
    >
      {/* Gradient background - more visible */}
      <div className="absolute inset-0 bg-gradient-to-br from-blue-900/30 via-purple-900/30 to-blue-900/30" />

      {/* Animated particles */}
      {particles.map((particle) => (
        <motion.div
          key={particle.id}
          className="absolute rounded-full"
          style={{
            left: `${particle.x}%`,
            top: `${particle.y}%`,
            width: particle.size,
            height: particle.size,
            background: `radial-gradient(circle, rgba(99, 102, 241, 0.9), rgba(59, 130, 246, 0.6) 50%, transparent)`,
            boxShadow: `0 0 ${particle.size * 4}px rgba(99, 102, 241, 0.8), 0 0 ${particle.size * 8}px rgba(59, 130, 246, 0.4)`,
          }}
          animate={{
            x: [0, Math.random() * 80 - 40, Math.random() * -80 + 40, 0],
            y: [0, Math.random() * 80 - 40, Math.random() * -80 + 40, 0],
            opacity: [0.5, 1, 0.5],
            scale: [1, 1.5, 0.8, 1],
          }}
          transition={{
            duration: particle.duration,
            delay: particle.delay,
            repeat: Infinity,
            ease: 'easeInOut',
          }}
        />
      ))}

      {/* Large flowing shapes for depth */}
      {[0, 1, 2].map((i) => (
        <motion.div
          key={`shape-${i}`}
          className="absolute rounded-full"
          style={{
            width: 300 + i * 100,
            height: 300 + i * 100,
            left: `${25 + i * 25}%`,
            top: `${20 + i * 15}%`,
            background: `radial-gradient(circle, rgba(59, 130, 246, 0.15), transparent 70%)`,
            filter: 'blur(60px)',
          }}
          animate={{
            x: [0, 50, -50, 0],
            y: [0, -30, 30, 0],
            scale: [1, 1.1, 0.9, 1],
          }}
          transition={{
            duration: 15 + i * 5,
            repeat: Infinity,
            ease: 'easeInOut',
          }}
        />
      ))}
    </div>
  );
};

export default CSSAttractorFallback;
