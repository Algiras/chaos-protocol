import "../styles/globals.css";
import type { AppProps } from "next/app";
import { AnimatePresence } from "framer-motion";
import { useRouter } from "next/router";
import { Layout } from "@/components/layout";
import { MarketingHeader } from "@/components/layout/MarketingHeader";
import React from "react";
import dynamic from "next/dynamic";

const CanvasParticles = dynamic(
  () => import("@chaos/shared/components/chaos/effects/CanvasParticles"),
  { ssr: false }
);

export default function App({ Component, pageProps }: AppProps) {
  const router = useRouter();

  // Detect performance tier - reduce particles on lower-end devices
  const [particleCount, setParticleCount] = React.useState(50); // Default to 50

  React.useEffect(() => {
    // Check if device can handle more particles
    const isHighPerformance =
      navigator.hardwareConcurrency && navigator.hardwareConcurrency >= 8 &&
      !navigator.userAgent.includes('Windows NT 6'); // Avoid older Windows

    // Reduce to 30 particles on lower-end devices, 50 for mid-tier, 80 for high-end
    setParticleCount(isHighPerformance ? 80 : 30);
  }, []);

  return (
    <>
      <CanvasParticles opacity={0.4} particleCount={particleCount} />
      <MarketingHeader />
      <Layout>
        <AnimatePresence mode="wait">
          <Component key={router.pathname} {...pageProps} />
        </AnimatePresence>
      </Layout>
    </>
  );
}
