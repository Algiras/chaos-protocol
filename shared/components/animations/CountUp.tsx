import { useEffect, useState } from 'react';
import { motion, useSpring, useTransform } from 'framer-motion';

interface CountUpProps {
  end: number;
  duration?: number;
  prefix?: string;
  suffix?: string;
  decimals?: number;
  className?: string;
  delay?: number;
  separator?: string;
}

export function CountUp({
  end,
  duration = 2,
  prefix = '',
  suffix = '',
  decimals = 0,
  className = '',
  delay = 0,
  separator = '',
}: CountUpProps) {
  const [isInView, setIsInView] = useState(false);
  const spring = useSpring(0, {
    duration: duration * 1000,
    bounce: 0,
  });
  const display = useTransform(spring, (current) => {
    const num = current.toFixed(decimals);
    if (separator) {
      return Number(num).toLocaleString('en-US');
    }
    return num;
  });

  useEffect(() => {
    if (isInView) {
      const timer = setTimeout(() => {
        spring.set(end);
      }, delay * 1000);
      return () => clearTimeout(timer);
    }
  }, [isInView, spring, end, delay]);

  return (
    <motion.span
      className={className}
      onViewportEnter={() => setIsInView(true)}
      viewport={{ once: true, amount: 0.5 }}
    >
      {prefix}
      <motion.span>{display}</motion.span>
      {suffix}
    </motion.span>
  );
}
