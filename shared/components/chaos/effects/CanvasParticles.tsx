'use client';

import React, { useEffect, useRef } from 'react';

interface CanvasParticlesProps {
  className?: string;
  opacity?: number;
  particleCount?: number;
  connectionDistance?: number;
  mouseRadius?: number;
}

interface Particle {
  x: number;
  y: number;
  vx: number;
  vy: number;
  size: number;
  hue: number;
  life: number;
  depth: number; // 0-1, for parallax layering
}

/**
 * Canvas-based particle system using requestAnimationFrame
 * GPU-accelerated and smooth like a game
 */
export const CanvasParticles: React.FC<CanvasParticlesProps> = ({
  className = '',
  opacity = 0.8,
  particleCount = 150,
  connectionDistance = 120,
  mouseRadius = 200,
}) => {
  const canvasRef = useRef<HTMLCanvasElement>(null);
  const particlesRef = useRef<Particle[]>([]);
  const animationRef = useRef<number>();
  const mouseRef = useRef({ x: 0.5, y: 0.5 }); // Normalized mouse position
  const mousePxRef = useRef({ x: -1000, y: -1000 }); // Pixel mouse position for attraction
  const prevMousePxRef = useRef({ x: -1000, y: -1000 }); // Previous mouse position for velocity
  const mouseVelocityRef = useRef({ vx: 0, vy: 0 }); // Mouse velocity for force wave
  const mouseCurlRef = useRef(0); // Curl/vorticity from circular mouse motion
  const scrollRef = useRef(0);
  const scrollVelocityRef = useRef(0);

  useEffect(() => {
    const canvas = canvasRef.current;
    if (!canvas) return;

    const ctx = canvas.getContext('2d', { alpha: true });
    if (!ctx) return;

    // Check reduced motion preference
    const prefersReducedMotion = window.matchMedia('(prefers-reduced-motion: reduce)').matches;

    // Set canvas size with HiDPI fix
    const setSize = () => {
      const dpr = window.devicePixelRatio;
      canvas.width = canvas.offsetWidth * dpr;
      canvas.height = canvas.offsetHeight * dpr;
      // Reset transform before scaling to prevent compounding
      ctx.setTransform(1, 0, 0, 1, 0, 0);
      ctx.scale(dpr, dpr);
    };
    setSize();
    window.addEventListener('resize', setSize);

    // Track mouse for parallax and attraction + calculate velocity and curl
    const handleMouseMove = (e: MouseEvent) => {
      const newX = e.clientX;
      const newY = e.clientY;
      const prevX = prevMousePxRef.current.x;
      const prevY = prevMousePxRef.current.y;

      // Calculate mouse velocity for force wave effect
      const vx = (newX - prevX) * 0.1;
      const vy = (newY - prevY) * 0.1;
      mouseVelocityRef.current = { vx, vy };

      // Calculate curl (vorticity) from circular motion
      // Cross product of position vector and velocity vector
      const dx = newX - window.innerWidth / 2;
      const dy = newY - window.innerHeight / 2;
      const curl = (dx * vy - dy * vx) / 10000;
      mouseCurlRef.current = curl;

      prevMousePxRef.current = { x: newX, y: newY };

      mouseRef.current = {
        x: newX / window.innerWidth,
        y: newY / window.innerHeight,
      };
      mousePxRef.current = { x: newX, y: newY };
    };

    // Track scroll for parallax + velocity
    const handleScroll = () => {
      const newScroll = window.scrollY;
      scrollVelocityRef.current = newScroll - scrollRef.current;
      scrollRef.current = newScroll;
    };

    // Click/touch shockwave: repel particles from click point
    const clickRadius = 300;
    const handleClick = (e: MouseEvent) => {
      if (prefersReducedMotion) return;
      const cx = e.clientX;
      const cy = e.clientY;
      const w = canvas.offsetWidth;
      const h = canvas.offsetHeight;
      const mouseOX = (mouseRef.current.x - 0.5) * 0.05;
      const mouseOY = (mouseRef.current.y - 0.5) * 0.05;
      const scrOff = (scrollRef.current / window.innerHeight) * 0.1;

      particlesRef.current.forEach((p) => {
        const px = (p.x + mouseOX * p.depth) * w;
        const py = (p.y + (mouseOY - scrOff) * p.depth) * h;
        const dx = px - cx;
        const dy = py - cy;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist < clickRadius && dist > 1) {
          const strength = 0.002 * (1 - dist / clickRadius);
          p.vx += (dx / dist) * strength;
          p.vy += (dy / dist) * strength;
        }
      });
    };

    window.addEventListener('mousemove', handleMouseMove);
    window.addEventListener('click', handleClick);
    window.addEventListener('scroll', handleScroll, { passive: true });

    // Initialize particles with two distinct depth layers for parallax
    const initParticles = () => {
      particlesRef.current = [];
      for (let i = 0; i < particleCount; i++) {
        // Two layers: 60% background layer (depth 0.15), 40% foreground layer (depth 1.0)
        const depth = i < particleCount * 0.6 ? 0.15 : 1.0;
        particlesRef.current.push({
          x: Math.random(),
          y: Math.random(),
          vx: (Math.random() - 0.5) * 0.0003,
          vy: (Math.random() - 0.5) * 0.0003,
          size: depth > 0.5 ? 5 + Math.random() * 3 : 1.5 + Math.random() * 1.5, // Front: 5-8px, Back: 1.5-3px
          hue: 200 + Math.random() * 80, // Blue through purple range
          life: Math.random(),
          depth,
        });
      }
    };
    initParticles();

    // Animation loop using requestAnimationFrame
    const animate = () => {
      const w = canvas.offsetWidth;
      const h = canvas.offsetHeight;

      // Clear canvas completely for crisp particles
      ctx.clearRect(0, 0, w, h);

      // Calculate parallax offsets (strong mouse parallax, gentle scroll)
      const mouseOffsetX = (mouseRef.current.x - 0.5) * 0.25;
      const mouseOffsetY = (mouseRef.current.y - 0.5) * 0.25;
      const scrollOffset = (scrollRef.current / window.innerHeight) * 0.08;

      // Decay scroll velocity, mouse velocity, and curl each frame
      scrollVelocityRef.current *= 0.9;
      mouseVelocityRef.current.vx *= 0.92;
      mouseVelocityRef.current.vy *= 0.92;
      mouseCurlRef.current *= 0.95; // Whirlwind momentum persists briefly

      const mx = mousePxRef.current.x;
      const my = mousePxRef.current.y;

      // Store screen positions for connection lines
      const screenPositions: { px: number; py: number; hue: number; alpha: number }[] = [];

      // Update and draw particles
      particlesRef.current.forEach((p) => {
        if (!prefersReducedMotion) {
          // Update position
          p.x += p.vx;
          p.y += p.vy;

          // Chaos theory: Strange attractor behavior (Lorenz-inspired drift)
          // Particles orbit around multiple attractor points creating chaotic paths
          const dx = p.x - 0.5;
          const dy = p.y - 0.5;
          const r = Math.sqrt(dx * dx + dy * dy);

          // Multi-attractor system creates chaotic, unpredictable motion
          const attractor1 = { x: 0.3, y: 0.4 };
          const attractor2 = { x: 0.7, y: 0.6 };

          const d1x = p.x - attractor1.x;
          const d1y = p.y - attractor1.y;
          const d2x = p.x - attractor2.x;
          const d2y = p.y - attractor2.y;

          // Chaotic switching between attractors based on position
          const useAttractor1 = Math.sin(p.x * 10 + p.y * 7) > 0;

          if (useAttractor1) {
            p.vx += -d1x * 0.000008 + d1y * 0.000005; // Orbit + drift
            p.vy += -d1y * 0.000008 - d1x * 0.000005;
          } else {
            p.vx += -d2x * 0.000008 - d2y * 0.000005;
            p.vy += -d2y * 0.000008 + d2x * 0.000005;
          }

          // Mouse force wave: push particles away from fast mouse movement
          const parallaxX = mouseOffsetX * p.depth;
          const parallaxY = (mouseOffsetY - scrollOffset) * p.depth;
          const screenX = (p.x + parallaxX) * w;
          const screenY = (p.y + parallaxY) * h;
          const dmx = mx - screenX;
          const dmy = my - screenY;
          const mouseDist = Math.sqrt(dmx * dmx + dmy * dmy);

          // Force wave: particles get pushed by mouse velocity (stronger effect)
          const mouseSpeed = Math.sqrt(
            mouseVelocityRef.current.vx * mouseVelocityRef.current.vx +
            mouseVelocityRef.current.vy * mouseVelocityRef.current.vy
          );

          if (mouseDist < mouseRadius && mouseDist > 1) {
            // Butterfly effect: small mouse movements amplified exponentially
            const distanceFactor = 1 - mouseDist / mouseRadius;
            const butterflyAmplification = Math.pow(distanceFactor, 0.5); // Square root for stronger effect

            if (mouseSpeed > 0.1) {
              // Push particles away from cursor path (exponentially stronger for nearby particles)
              const waveForce = 0.00025 * mouseSpeed * butterflyAmplification * p.depth;
              p.vx -= (dmx / mouseDist) * waveForce;
              p.vy -= (dmy / mouseDist) * waveForce;
            } else {
              // Gentle attraction when mouse is slow/still
              const attractForce = 0.00003 * distanceFactor;
              p.vx += (dmx / mouseDist) * attractForce;
              p.vy += (dmy / mouseDist) * attractForce;
            }

            // Whirlwind effect from circular mouse motion (chaos vortex)
            const curl = mouseCurlRef.current;
            if (Math.abs(curl) > 0.01) {
              const curlStrength = Math.min(Math.abs(curl), 1.0) * 0.0004 * butterflyAmplification;
              // Perpendicular force creates rotation
              p.vx += -dmy / mouseDist * curlStrength * Math.sign(curl) * p.depth;
              p.vy += dmx / mouseDist * curlStrength * Math.sign(curl) * p.depth;
            }
          }

          // Gentle scroll influence (subtle, doesn't disrupt flow)
          const scrollV = scrollVelocityRef.current;
          if (Math.abs(scrollV) > 2) {
            p.vy += scrollV * 0.0000005 * p.depth;
          }

          // Velocity damping to prevent runaway
          p.vx *= 0.999;
          p.vy *= 0.999;
        }

        // Wrap around edges
        if (p.x < -0.1) p.x = 1.1;
        if (p.x > 1.1) p.x = -0.1;
        if (p.y < -0.1) p.y = 1.1;
        if (p.y > 1.1) p.y = -0.1;

        // Animate life for pulsing effect
        p.life = (p.life + 0.008) % 1;
        const pulse = 0.5 + Math.sin(p.life * Math.PI * 2) * 0.5;

        // Apply parallax based on depth (deeper = more movement)
        const parallaxX = mouseOffsetX * p.depth;
        const parallaxY = (mouseOffsetY - scrollOffset) * p.depth;

        // Calculate screen position with parallax
        const px = (p.x + parallaxX) * w;
        const py = (p.y + parallaxY) * h;
        // Foreground particles brighter for depth perception
        let alpha = pulse * (p.depth > 0.5 ? 0.9 : 0.5);

        // Mouse proximity glow boost
        const dmx2 = mx - px;
        const dmy2 = my - py;
        const mouseDistToParticle = Math.sqrt(dmx2 * dmx2 + dmy2 * dmy2);
        if (mouseDistToParticle < mouseRadius) {
          const boost = 0.3 * (1 - mouseDistToParticle / mouseRadius);
          alpha = Math.min(1, alpha + boost);
        }

        screenPositions.push({ px, py, hue: p.hue, alpha });

        // Very large outer glow
        const gradient = ctx.createRadialGradient(px, py, 0, px, py, p.size * 6);
        gradient.addColorStop(0, `hsla(${p.hue}, 100%, 75%, ${alpha})`);
        gradient.addColorStop(0.3, `hsla(${p.hue}, 95%, 65%, ${alpha * 0.7})`);
        gradient.addColorStop(0.6, `hsla(${p.hue}, 90%, 55%, ${alpha * 0.4})`);
        gradient.addColorStop(1, `hsla(${p.hue}, 85%, 45%, 0)`);

        ctx.fillStyle = gradient;
        ctx.beginPath();
        ctx.arc(px, py, p.size * 6, 0, Math.PI * 2);
        ctx.fill();

        // Bright inner core
        ctx.fillStyle = `hsla(${p.hue}, 100%, 80%, ${alpha})`;
        ctx.shadowColor = `hsla(${p.hue}, 100%, 70%, ${alpha * 0.8})`;
        ctx.shadowBlur = p.size * 3;
        ctx.beginPath();
        ctx.arc(px, py, p.size * 2, 0, Math.PI * 2);
        ctx.fill();
        ctx.shadowBlur = 0;
      });

      // Draw connection lines between nearby particles (constellation effect)
      if (!prefersReducedMotion) {
        ctx.lineWidth = 0.5;
        for (let i = 0; i < screenPositions.length; i++) {
          for (let j = i + 1; j < screenPositions.length; j++) {
            const a = screenPositions[i];
            const b = screenPositions[j];
            const dx = a.px - b.px;
            const dy = a.py - b.py;
            const dist = Math.sqrt(dx * dx + dy * dy);

            if (dist < connectionDistance) {
              const lineAlpha = (1 - dist / connectionDistance) * 0.15 * Math.min(a.alpha, b.alpha);
              const avgHue = (a.hue + b.hue) / 2;
              ctx.strokeStyle = `hsla(${avgHue}, 80%, 65%, ${lineAlpha})`;
              ctx.beginPath();
              ctx.moveTo(a.px, a.py);
              ctx.lineTo(b.px, b.py);
              ctx.stroke();
            }
          }
        }
      }

      animationRef.current = requestAnimationFrame(animate);
    };

    animate();

    return () => {
      if (animationRef.current) {
        cancelAnimationFrame(animationRef.current);
      }
      window.removeEventListener('resize', setSize);
      window.removeEventListener('mousemove', handleMouseMove);
      window.removeEventListener('click', handleClick);
      window.removeEventListener('scroll', handleScroll);
    };
  }, [particleCount, connectionDistance, mouseRadius]);

  return (
    <canvas
      ref={canvasRef}
      className={`fixed inset-0 w-screen h-screen ${className}`}
      style={{
        opacity,
        zIndex: 0,
        pointerEvents: 'none',
      }}
    />
  );
};

export default CanvasParticles;
