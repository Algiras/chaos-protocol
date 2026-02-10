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

  return (
    <>
      <CanvasParticles opacity={0.5} particleCount={150} />
      <MarketingHeader />
      <Layout>
        <AnimatePresence mode="wait">
          <Component key={router.pathname} {...pageProps} />
        </AnimatePresence>
      </Layout>
    </>
  );
}
