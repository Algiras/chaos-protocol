'use client';

import React from 'react';
import { Canvas } from '@react-three/fiber';

/**
 * Simple test component to verify React Three Fiber works
 */
export const SimpleCanvas: React.FC = () => {
  return (
    <div style={{ width: '100%', height: '400px', background: '#1a1a1a' }}>
      <Canvas>
        <mesh>
          <boxGeometry args={[1, 1, 1]} />
          <meshStandardMaterial color="orange" />
        </mesh>
        <ambientLight intensity={0.5} />
        <pointLight position={[10, 10, 10]} />
      </Canvas>
    </div>
  );
};

export default SimpleCanvas;
