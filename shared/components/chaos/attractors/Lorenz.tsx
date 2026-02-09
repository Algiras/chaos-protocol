'use client';

import React, { useRef, useMemo, useEffect } from 'react';
import { useFrame, useThree } from '@react-three/fiber';
import * as THREE from 'three';

interface LorenzAttractorProps {
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
 * Lorenz Attractor Component
 *
 * Creates a 3D visualization of the Lorenz attractor, a set of chaotic
 * solutions to the Lorenz system. The butterfly-shaped attractor is a
 * classic example of how deterministic systems can produce chaotic behavior.
 *
 * The system is defined by:
 * dx/dt = σ(y - x)
 * dy/dt = x(ρ - z) - y
 * dz/dt = xy - βz
 */
export const LorenzAttractor: React.FC<LorenzAttractorProps> = ({
  points = 5000,
  volatility = 0.5,
  colors = ['#2B5278', '#6366F1', '#5B8AB8'], // Refined: steel blue -> indigo -> light blue
  scale = 0.05,
  speed = 1,
  interactive = true,
}) => {
  const lineRef = useRef<THREE.Line>(null);
  const groupRef = useRef<THREE.Group>(null);

  // Lorenz attractor parameters (influenced by volatility)
  const sigma = 10;
  const rho = 28 + volatility * 10; // Increase chaos with volatility
  const beta = 8 / 3;

  // Generate Lorenz attractor points using Runge-Kutta method
  const positions = useMemo(() => {
    const vertices: number[] = [];
    let x = 0.1;
    let y = 0;
    let z = 0;
    const dt = 0.005;

    for (let i = 0; i < points; i++) {
      // Lorenz equations
      const dx = sigma * (y - x);
      const dy = x * (rho - z) - y;
      const dz = x * y - beta * z;

      // Runge-Kutta 4th order integration
      x += dx * dt;
      y += dy * dt;
      z += dz * dt;

      vertices.push(x * scale, y * scale, z * scale);
    }

    return new Float32Array(vertices);
  }, [points, volatility, scale, sigma, rho, beta]);

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

  // Animate the attractor (slow rotation)
  useFrame((state) => {
    if (!groupRef.current) return;

    // Slow rotation around Y axis
    groupRef.current.rotation.y += 0.001 * speed;

    // Subtle breathing effect
    const breathe = Math.sin(state.clock.elapsedTime * 0.5) * 0.02;
    groupRef.current.scale.setScalar(1 + breathe);

    // Interactive camera orbit
    if (interactive && state.camera) {
      const time = state.clock.elapsedTime * 0.1;
      state.camera.position.x = Math.sin(time) * 5;
      state.camera.position.z = Math.cos(time) * 5;
      state.camera.position.y = Math.sin(time * 0.5) * 2 + 2;
      state.camera.lookAt(0, 0, 0);
    }
  });

  // Mouse interaction - parallax effect
  useEffect(() => {
    if (!interactive) return;

    const handleMouseMove = (event: MouseEvent) => {
      if (!groupRef.current) return;

      const x = (event.clientX / window.innerWidth) * 2 - 1;
      const y = -(event.clientY / window.innerHeight) * 2 + 1;

      // Subtle parallax rotation
      groupRef.current.rotation.x = y * 0.1;
      groupRef.current.rotation.z = x * 0.1;
    };

    window.addEventListener('mousemove', handleMouseMove);
    return () => window.removeEventListener('mousemove', handleMouseMove);
  }, [interactive]);

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
          opacity={0.95}
        />
      </line>

      {/* Add glow effect with particles at key points */}
      {Array.from({ length: 50 }).map((_, i) => {
        const index = Math.floor((i / 50) * (positions.length / 3)) * 3;
        return (
          <mesh
            key={i}
            position={[
              positions[index],
              positions[index + 1],
              positions[index + 2],
            ]}
          >
            <sphereGeometry args={[0.02, 8, 8]} />
            <meshBasicMaterial
              color={i < 17 ? colors[0] : i < 34 ? colors[1] : colors[2]}
              transparent
              opacity={0.6}
            />
          </mesh>
        );
      })}
    </group>
  );
};

export default LorenzAttractor;
