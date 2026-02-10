'use client';

import React, { useEffect, useState } from 'react';
import { motion, AnimatePresence } from 'framer-motion';

interface Particle {
  id: number;
  angle: number;
  velocity: number;
  size: number;
  color: string;
}

interface ParticleBurstProps {
  /** X position of burst origin */
  x: number;
  /** Y position of burst origin */
  y: number;
  /** Number of particles */
  particleCount?: number;
  /** Particle colors */
  colors?: string[];
  /** Duration of animation */
  duration?: number;
  /** Callback when animation completes */
  onComplete?: () => void;
}

/**
 * ParticleBurst Component
 *
 * Creates an explosive particle burst effect for interactive elements
 */
export const ParticleBurst: React.FC<ParticleBurstProps> = ({
  x,
  y,
  particleCount = 20,
  colors = ['#2B5278', '#6366F1', '#5B8AB8', '#14B8A6'],
  duration = 800,
  onComplete,
}) => {
  const [particles, setParticles] = useState<Particle[]>([]);

  useEffect(() => {
    // Generate particles with random properties
    const newParticles: Particle[] = Array.from({ length: particleCount }, (_, i) => ({
      id: i,
      angle: (Math.PI * 2 * i) / particleCount + Math.random() * 0.5,
      velocity: 100 + Math.random() * 150,
      size: 4 + Math.random() * 6,
      color: colors[Math.floor(Math.random() * colors.length)],
    }));

    setParticles(newParticles);

    // Cleanup after animation
    const timer = setTimeout(() => {
      setParticles([]);
      onComplete?.();
    }, duration);

    return () => clearTimeout(timer);
  }, [x, y, particleCount, colors, duration, onComplete]);

  return (
    <div className="absolute inset-0 pointer-events-none">
      <AnimatePresence>
        {particles.map((particle) => {
          const endX = x + Math.cos(particle.angle) * particle.velocity;
          const endY = y + Math.sin(particle.angle) * particle.velocity;

          return (
            <motion.div
              key={particle.id}
              className="absolute rounded-full"
              style={{
                width: particle.size,
                height: particle.size,
                backgroundColor: particle.color,
                left: x,
                top: y,
                boxShadow: `0 0 ${particle.size * 2}px ${particle.color}`,
              }}
              initial={{
                x: 0,
                y: 0,
                opacity: 1,
                scale: 1,
              }}
              animate={{
                x: endX - x,
                y: endY - y,
                opacity: 0,
                scale: 0,
              }}
              exit={{
                opacity: 0,
              }}
              transition={{
                duration: duration / 1000,
                ease: [0.25, 0.46, 0.45, 0.94],
              }}
            />
          );
        })}
      </AnimatePresence>
    </div>
  );
};

export default ParticleBurst;
