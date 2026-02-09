'use client';

import React, { useRef, useMemo } from 'react';
import { useFrame } from '@react-three/fiber';
import * as THREE from 'three';

interface RosslerAttractorProps {
  /** Number of points in the attractor path */
  points?: number;
  /** Volatility affects the chaos parameters (0-1) */
  volatility?: number;
  /** Color gradient for the attractor lines */
  colors?: [string, string, string];
  /** Scale factor for the attractor */
  scale?: number;
  /** Speed of animation */
  speed?: number;
  /** Enable mouse interaction */
  interactive?: boolean;
}

/**
 * Rössler Attractor Component
 *
 * Creates a 3D visualization of the Rössler attractor, which exhibits chaotic
 * behavior similar to the Lorenz attractor but with a simpler spiral structure.
 *
 * The system is defined by:
 * dx/dt = -y - z
 * dy/dt = x + ay
 * dz/dt = b + z(x - c)
 *
 * The Rössler attractor is characterized by its elegant spiral ribbon shape.
 */
export const RosslerAttractor: React.FC<RosslerAttractorProps> = ({
  points = 5000,
  volatility = 0.5,
  colors = ['#0B4F6C', '#7B2CBF', '#C9184A'], // attractor blue -> purple -> magenta
  scale = 0.15,
  speed = 1,
  interactive = true,
}) => {
  const lineRef = useRef<THREE.Line>(null);
  const groupRef = useRef<THREE.Group>(null);

  // Rössler attractor parameters (influenced by volatility)
  const a = 0.2;
  const b = 0.2;
  const c = 5.7 + volatility * 2; // Increase chaos with volatility

  // Generate Rössler attractor points using Runge-Kutta method
  const positions = useMemo(() => {
    const vertices: number[] = [];
    let x = 0.1;
    let y = 0;
    let z = 0;
    const dt = 0.01;

    for (let i = 0; i < points; i++) {
      // Rössler equations
      const dx = -y - z;
      const dy = x + a * y;
      const dz = b + z * (x - c);

      // Runge-Kutta 4th order integration
      x += dx * dt;
      y += dy * dt;
      z += dz * dt;

      vertices.push(x * scale, y * scale, z * scale);
    }

    return new Float32Array(vertices);
  }, [points, volatility, scale, a, b, c]);

  // Create color gradient along the attractor path
  const colorArray = useMemo(() => {
    const colors_array: number[] = [];
    const color1 = new THREE.Color(colors[0]);
    const color2 = new THREE.Color(colors[1]);
    const color3 = new THREE.Color(colors[2]);

    for (let i = 0; i < points; i++) {
      const t = i / points;
      let color: THREE.Color;

      if (t < 0.5) {
        // Interpolate between color1 and color2
        color = color1.clone().lerp(color2, t * 2);
      } else {
        // Interpolate between color2 and color3
        color = color2.clone().lerp(color3, (t - 0.5) * 2);
      }

      colors_array.push(color.r, color.g, color.b);
    }

    return new Float32Array(colors_array);
  }, [points, colors]);

  // Animate the attractor (slow rotation around Z axis)
  useFrame((state) => {
    if (!groupRef.current) return;

    // Slow rotation - Rössler looks best rotating around Z axis
    groupRef.current.rotation.z += 0.002 * speed;
    groupRef.current.rotation.x = Math.sin(state.clock.elapsedTime * 0.2) * 0.2;

    // Subtle breathing effect
    const breathe = Math.sin(state.clock.elapsedTime * 0.5) * 0.02;
    groupRef.current.scale.setScalar(1 + breathe);
  });

  return (
    <group ref={groupRef}>
      {/* @ts-ignore - Three.js line ref type issue */}
      <line ref={lineRef}>
        <bufferGeometry>
          <bufferAttribute
            attach="attributes-position"
            count={positions.length / 3}
            array={positions}
            itemSize={3}
          />
          <bufferAttribute
            attach="attributes-color"
            count={colorArray.length / 3}
            array={colorArray}
            itemSize={3}
          />
        </bufferGeometry>
        <lineBasicMaterial
          vertexColors
          linewidth={2}
          transparent
          opacity={0.8}
        />
      </line>

      {/* Add glow effect with particles at key points */}
      {Array.from({ length: 40 }).map((_, i) => {
        const index = Math.floor((i / 40) * (positions.length / 3)) * 3;
        return (
          <mesh
            key={i}
            position={[
              positions[index],
              positions[index + 1],
              positions[index + 2],
            ]}
          >
            <sphereGeometry args={[0.015, 8, 8]} />
            <meshBasicMaterial
              color={i < 13 ? colors[0] : i < 27 ? colors[1] : colors[2]}
              transparent
              opacity={0.6}
            />
          </mesh>
        );
      })}
    </group>
  );
};

export default RosslerAttractor;
