'use client';

import React, { useRef, useMemo } from 'react';
import { useFrame } from '@react-three/fiber';
import * as THREE from 'three';

interface FloatingParticlesProps {
  /** Number of particles */
  count?: number;
  /** Particle size */
  size?: number;
  /** Particle colors */
  colors?: string[];
  /** Movement speed */
  speed?: number;
  /** Spread area */
  spread?: number;
}

/**
 * FloatingParticles Component
 *
 * Creates a field of floating, drifting particles for ambient background effect
 */
export const FloatingParticles: React.FC<FloatingParticlesProps> = ({
  count = 200,
  size = 0.05,
  colors = ['#2B5278', '#6366F1', '#5B8AB8', '#14B8A6'],
  speed = 0.5,
  spread = 15,
}) => {
  const pointsRef = useRef<THREE.Points>(null);

  // Generate random positions and velocities
  const [positions, velocities, particleColors] = useMemo(() => {
    const positions = new Float32Array(count * 3);
    const velocities = new Float32Array(count * 3);
    const particleColors = new Float32Array(count * 3);

    const colorObjs = colors.map(c => new THREE.Color(c));

    for (let i = 0; i < count; i++) {
      const i3 = i * 3;

      // Random position within spread
      positions[i3] = (Math.random() - 0.5) * spread;
      positions[i3 + 1] = (Math.random() - 0.5) * spread;
      positions[i3 + 2] = (Math.random() - 0.5) * spread;

      // Random velocity (slow drift)
      velocities[i3] = (Math.random() - 0.5) * 0.02;
      velocities[i3 + 1] = (Math.random() - 0.5) * 0.02;
      velocities[i3 + 2] = (Math.random() - 0.5) * 0.02;

      // Random color from palette
      const color = colorObjs[Math.floor(Math.random() * colorObjs.length)];
      particleColors[i3] = color.r;
      particleColors[i3 + 1] = color.g;
      particleColors[i3 + 2] = color.b;
    }

    return [positions, velocities, particleColors];
  }, [count, spread, colors]);

  // Animate particles
  useFrame((state) => {
    if (!pointsRef.current) return;

    const positions = pointsRef.current.geometry.attributes.position.array as Float32Array;

    for (let i = 0; i < count; i++) {
      const i3 = i * 3;

      // Apply velocity
      positions[i3] += velocities[i3] * speed;
      positions[i3 + 1] += velocities[i3 + 1] * speed;
      positions[i3 + 2] += velocities[i3 + 2] * speed;

      // Wrap around bounds
      const halfSpread = spread / 2;
      if (Math.abs(positions[i3]) > halfSpread) {
        positions[i3] = -positions[i3];
      }
      if (Math.abs(positions[i3 + 1]) > halfSpread) {
        positions[i3 + 1] = -positions[i3 + 1];
      }
      if (Math.abs(positions[i3 + 2]) > halfSpread) {
        positions[i3 + 2] = -positions[i3 + 2];
      }

      // Add subtle wave motion
      const time = state.clock.elapsedTime;
      positions[i3 + 1] += Math.sin(time + i) * 0.001;
    }

    pointsRef.current.geometry.attributes.position.needsUpdate = true;
  });

  return (
    <points ref={pointsRef}>
      <bufferGeometry>
        <bufferAttribute
          attach="attributes-position"
          count={count}
          array={positions}
          itemSize={3}
        />
        <bufferAttribute
          attach="attributes-color"
          count={count}
          array={particleColors}
          itemSize={3}
        />
      </bufferGeometry>
      <pointsMaterial
        size={size}
        vertexColors
        transparent
        opacity={0.6}
        sizeAttenuation
        blending={THREE.AdditiveBlending}
      />
    </points>
  );
};

export default FloatingParticles;
