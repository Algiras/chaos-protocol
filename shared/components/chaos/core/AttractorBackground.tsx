'use client';

import React, { Suspense, useState, useEffect, lazy } from 'react';
import { Canvas } from '@react-three/fiber';

// Lazy load attractor components for code splitting
const LorenzAttractor = lazy(() =>
  import('../attractors/Lorenz').then(module => ({ default: module.default }))
);

const FloatingParticles = lazy(() =>
  import('../effects/FloatingParticles').then(module => ({ default: module.default }))
);

interface AttractorBackgroundProps {
  /** Type of attractor to display */
  type?: 'lorenz' | 'rossler' | 'henon' | 'duffing';
  /** Volatility parameter (0-1) affects chaos level */
  volatility?: number;
  /** Market sentiment affects colors and behavior */
  sentiment?: 'bullish' | 'bearish' | 'neutral';
  /** Enable mouse interaction */
  interactive?: boolean;
  /** Performance mode: affects particle count and quality */
  performance?: 'high' | 'medium' | 'low' | 'auto';
  /** Additional className for the container */
  className?: string;
  /** z-index for layering */
  zIndex?: number;
  /** Opacity of the attractor */
  opacity?: number;
}

/**
 * Detect device GPU capabilities
 */
const detectGPUCapability = (): 'high' | 'medium' | 'low' => {
  if (typeof window === 'undefined') return 'medium';

  // Check for mobile devices
  const isMobile = /iPhone|iPad|iPod|Android/i.test(navigator.userAgent);
  if (isMobile) return 'low';

  // Check screen size
  const width = window.innerWidth;
  if (width < 768) return 'low';
  if (width < 1024) return 'medium';

  // Check for WebGL support
  try {
    const canvas = document.createElement('canvas');
    const gl = canvas.getContext('webgl') || canvas.getContext('experimental-webgl');
    if (!gl) return 'low';

    // Check for high-performance GPU
    const debugInfo = (gl as any).getExtension('WEBGL_debug_renderer_info');
    if (debugInfo) {
      const renderer = (gl as any).getParameter(debugInfo.UNMASKED_RENDERER_WEBGL);
      // High-end GPUs
      if (/nvidia|amd|apple m[1-9]/i.test(renderer)) return 'high';
    }

    return 'medium';
  } catch {
    return 'low';
  }
};

/**
 * Check if user prefers reduced motion
 */
const prefersReducedMotion = (): boolean => {
  if (typeof window === 'undefined') return false;
  return window.matchMedia('(prefers-reduced-motion: reduce)').matches;
};

/**
 * Get color scheme based on sentiment - refined monochromatic
 */
const getSentimentColors = (sentiment: 'bullish' | 'bearish' | 'neutral'): [string, string, string] => {
  switch (sentiment) {
    case 'bullish':
      return ['#14B8A6', '#06B6D4', '#5B8AB8']; // teal -> cyan -> light blue (subtle optimism)
    case 'bearish':
      return ['#3D6B92', '#2B5278', '#1E3A5F']; // dark blues (conservative)
    case 'neutral':
    default:
      return ['#2B5278', '#6366F1', '#5B8AB8']; // steel blue -> indigo -> light blue (balanced)
  }
};

/**
 * CSS gradient fallback for low-performance devices
 */
const GradientFallback: React.FC<{
  sentiment: 'bullish' | 'bearish' | 'neutral';
  opacity: number;
  className?: string;
}> = ({ sentiment, opacity, className = '' }) => {
  const gradients = {
    bullish: 'from-chaos-accent-teal/20 via-chaos-accent-cyan/15 to-chaos-primary-400/10',
    bearish: 'from-chaos-primary-700/20 via-chaos-primary-600/15 to-chaos-primary-500/10',
    neutral: 'from-chaos-primary-600/15 via-chaos-accent-purple/10 to-chaos-primary-400/10',
  };

  return (
    <div
      className={`absolute inset-0 bg-gradient-to-br ${gradients[sentiment]} ${className}`}
      style={{ opacity }}
      aria-hidden="true"
    />
  );
};

/**
 * AttractorBackground Component
 *
 * Displays an animated 3D strange attractor as a background element.
 * Automatically detects device capabilities and provides appropriate fallbacks.
 *
 * Features:
 * - GPU capability detection
 * - Responsive complexity (mobile/tablet/desktop)
 * - Respects prefers-reduced-motion
 * - Lazy loading and code splitting
 * - CSS gradient fallback for low-power devices
 */
export const AttractorBackground: React.FC<AttractorBackgroundProps> = ({
  type = 'lorenz',
  volatility = 0.5,
  sentiment = 'neutral',
  interactive = true,
  performance = 'auto',
  className = '',
  zIndex = -1,
  opacity = 0.6,
}) => {
  const [capability, setCapability] = useState<'high' | 'medium' | 'low'>('medium');
  const [reducedMotion, setReducedMotion] = useState(false);
  const [isClient, setIsClient] = useState(false);

  useEffect(() => {
    setIsClient(true);
    setReducedMotion(prefersReducedMotion());

    // Detect GPU capability
    const detectedCapability = performance === 'auto' ? detectGPUCapability() : performance;
    setCapability(detectedCapability);

    // Listen for visibility change to pause animations
    const handleVisibilityChange = () => {
      // This will be handled by React Three Fiber's frameloop
    };

    document.addEventListener('visibilitychange', handleVisibilityChange);
    return () => document.removeEventListener('visibilitychange', handleVisibilityChange);
  }, [performance]);

  // Use CSS fallback for low performance or reduced motion
  if (!isClient || capability === 'low' || reducedMotion) {
    return (
      <GradientFallback
        sentiment={sentiment}
        opacity={opacity}
        className={className}
      />
    );
  }

  // Get attractor parameters based on capability
  // Note: 'low' capability is handled by early return above
  const getAttractorParams = () => {
    const colors = getSentimentColors(sentiment);

    switch (capability) {
      case 'high':
        return {
          points: 3000,
          colors,
          speed: 1,
          interactive: interactive,
        };
      case 'medium':
      default:
        return {
          points: 2000,
          colors,
          speed: 0.8,
          interactive: interactive,
        };
    }
  };

  const params = getAttractorParams();

  return (
    <div
      className={`absolute inset-0 ${className}`}
      style={{ zIndex, opacity }}
      aria-hidden="true"
    >
      <Canvas
        camera={{ position: [0, 2, 5], fov: 75 }}
        gl={{
          antialias: false,
          alpha: true,
          powerPreference: 'default',
          preserveDrawingBuffer: true,
          failIfMajorPerformanceCaveat: false,
        }}
        dpr={1}
        frameloop="always"
        style={{ width: '100%', height: '100%' }}
        onCreated={(state) => {
          state.gl.setClearColor(0x000000, 0);
          // Handle context loss
          const canvas = state.gl.domElement;
          canvas.addEventListener('webglcontextlost', (e) => {
            e.preventDefault();
            console.log('WebGL context lost, attempting to restore...');
          });
          canvas.addEventListener('webglcontextrestored', () => {
            console.log('WebGL context restored');
          });
        }}
      >
        <Suspense fallback={null}>
          {type === 'lorenz' && (
            <LorenzAttractor
              {...params}
              volatility={volatility}
            />
          )}
          {/* Future: Add Rössler, Hénon, Duffing attractors here */}

          {/* Add floating particles for ambient effect - reduced for performance */}
          <FloatingParticles
            count={50}
            size={0.05}
            colors={params.colors}
            speed={0.3}
            spread={20}
          />
        </Suspense>

        {/* Enhanced lighting for better visibility and glow */}
        <ambientLight intensity={0.6} />
        <pointLight position={[10, 10, 10]} intensity={1.2} color="#5B8AB8" />
        <pointLight position={[-10, -10, -10]} intensity={0.6} color="#6366F1" />
      </Canvas>
    </div>
  );
};

export default AttractorBackground;
