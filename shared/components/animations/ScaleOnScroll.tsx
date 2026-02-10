import { motion, useScroll, useTransform } from 'framer-motion';
import { ReactNode, useRef } from 'react';

interface ScaleOnScrollProps {
  children: ReactNode;
  scaleFrom?: number;
  scaleTo?: number;
  className?: string;
}

/**
 * ScaleOnScroll Component
 *
 * Scales content as user scrolls into view
 */
export function ScaleOnScroll({
  children,
  scaleFrom = 0.8,
  scaleTo = 1,
  className = '',
}: ScaleOnScrollProps) {
  const ref = useRef<HTMLDivElement>(null);
  const { scrollYProgress } = useScroll({
    target: ref,
    offset: ['start end', 'center center'],
  });

  const scale = useTransform(scrollYProgress, [0, 1], [scaleFrom, scaleTo]);
  const opacity = useTransform(scrollYProgress, [0, 0.5, 1], [0, 0.8, 1]);

  return (
    <div ref={ref} className={className}>
      <motion.div style={{ scale, opacity }}>{children}</motion.div>
    </div>
  );
}
