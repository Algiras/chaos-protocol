import { motion } from 'framer-motion';
import { ReactNode } from 'react';

interface GlowOnHoverProps {
  children: ReactNode;
  glowColor?: string;
  intensity?: 'low' | 'medium' | 'high';
  className?: string;
}

/**
 * GlowOnHover Component
 *
 * Adds a glow effect on hover with smooth transitions
 */
export function GlowOnHover({
  children,
  glowColor = 'rgba(99, 102, 241, 0.4)',
  intensity = 'medium',
  className = '',
}: GlowOnHoverProps) {
  const glowIntensity = {
    low: '0 0 20px',
    medium: '0 0 30px',
    high: '0 0 40px',
  };

  return (
    <motion.div
      className={`${className} overflow-hidden rounded-3xl`}
      whileHover={{
        boxShadow: `${glowIntensity[intensity]} ${glowColor}`,
        scale: 1.02,
      }}
      transition={{
        duration: 0.3,
        ease: 'easeInOut',
      }}
    >
      {children}
    </motion.div>
  );
}
