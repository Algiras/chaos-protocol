import "../styles/globals.css";
import type { AppProps } from "next/app";
import { AnimatePresence } from "framer-motion";
import { useRouter } from "next/router";
import { Layout } from "@/components/layout";
import { isApp } from "@/lib/build-target";
import React from "react";
import dynamic from "next/dynamic";

// Conditionally import providers based on build target
// Use dynamic import to avoid SSR issues
let MeshProvider: any;
let CurrencyProvider: any;

// Create pass-through provider component
const PassThroughProvider = ({ children }: { children: React.ReactNode }) => <>{children}</>;
PassThroughProvider.displayName = 'PassThroughProvider';

if (isApp) {
  // Dynamic require only on client side
  if (typeof window !== 'undefined') {
    MeshProvider = require("@meshsdk/react").MeshProvider;
    CurrencyProvider = require("@/contexts/CurrencyContext").CurrencyProvider;
  } else {
    // SSR fallback - just pass through children
    MeshProvider = PassThroughProvider;
    CurrencyProvider = PassThroughProvider;
  }
} else {
  // Marketing mode - no-op providers
  MeshProvider = PassThroughProvider;
  CurrencyProvider = PassThroughProvider;
}

export default function App({ Component, pageProps }: AppProps) {
  const router = useRouter();

  return (
    <MeshProvider>
      <CurrencyProvider>
        <AnimatePresence mode="wait">
          <Layout key={router.pathname}>
            <Component {...pageProps} />
          </Layout>
        </AnimatePresence>
      </CurrencyProvider>
    </MeshProvider>
  );
}
