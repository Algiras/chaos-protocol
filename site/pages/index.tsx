import Head from "next/head";
import Link from "next/link";
import { motion } from "framer-motion";
import { Button } from "@/components/ui/button";
import { FadeIn, StaggerContainer, StaggerItem } from "@/components/animations";
import { TrendingUp, Shield, Wallet, ArrowRight, LineChart, Sparkles, FileText, Zap, Lock, BarChart3, Users } from "lucide-react";
import dynamic from "next/dynamic";

// Lazy load AttractorBackground for better performance
const AttractorBackground = dynamic(
  () => import("@/components/chaos/core/AttractorBackground"),
  { ssr: false }
);

export default function Home() {
  return (
    <div className="bg-gray-900 min-h-screen">
      <Head>
        <title>CHAOS | Antifragile Treasury Protocol</title>
        <meta name="description" content="CHAOS is a formally verified treasury management protocol that profits from crypto volatility." />
        <meta property="og:title" content="CHAOS | Antifragile Treasury Protocol" />
        <meta property="og:description" content="A formally verified treasury protocol that turns volatility into profit. Mathematically proven with zero unproven assumptions." />
        <meta property="og:image" content="https://chaosprotocol.io/og-image.png" />
        <meta property="og:url" content="https://chaosprotocol.io" />
        <meta property="og:type" content="website" />
        <meta name="twitter:card" content="summary_large_image" />
        <meta name="twitter:title" content="CHAOS | Antifragile Treasury Protocol" />
        <meta name="twitter:description" content="A formally verified treasury protocol that turns volatility into profit. Mathematically proven with zero unproven assumptions." />
        <meta name="twitter:image" content="https://chaosprotocol.io/og-image.png" />
      </Head>

      {/* Hero Section */}
      <section className="relative pt-32 pb-20 overflow-hidden">
        {/* Lorenz Attractor Background - Subtle, elegant motion */}
        <AttractorBackground
          type="lorenz"
          volatility={0.4}
          sentiment="neutral"
          interactive={true}
          performance="auto"
          opacity={0.8}
          className="absolute inset-0"
        />

        {/* Additional Background Effects for depth */}
        <motion.div
          initial={{ opacity: 0 }}
          animate={{ opacity: 0.2 }}
          transition={{ duration: 2 }}
          className="absolute inset-0 bg-gradient-to-b from-transparent via-gray-900/50 to-gray-900"
        />
        
        <div className="relative max-w-7xl mx-auto px-6">
          <FadeIn>
            <span className="inline-block px-4 py-2 rounded-full bg-blue-600/20 text-blue-400 text-sm font-bold mb-8 border border-blue-600/30">
              Built on Cardano
            </span>
          </FadeIn>

          <FadeIn delay={0.1}>
            <h1 className="text-5xl md:text-7xl lg:text-8xl font-black text-white mb-8 leading-tight tracking-tight">
              Make Money From<br />
              <span className="text-transparent bg-clip-text bg-gradient-to-r from-blue-400 via-purple-400 to-emerald-400">
                Market Chaos
              </span>
            </h1>
          </FadeIn>

          <FadeIn delay={0.2}>
            <p className="text-xl text-gray-400 max-w-2xl mb-12 leading-relaxed">
              A formally verified treasury protocol that turns volatility into profit. 
              Mathematically proven with zero unproven assumptions.
            </p>
          </FadeIn>

          <FadeIn delay={0.3}>
            <div className="flex flex-col sm:flex-row gap-4">
              <Link href="/coming-soon">
                <Button size="lg" variant="chaos" className="text-lg px-8 py-6">
                  <Sparkles className="mr-3 h-6 w-6" />
                  Launch App
                  <ArrowRight className="ml-2 h-5 w-5" />
                </Button>
              </Link>
              <Link href="/research">
                <Button size="lg" variant="outline" className="text-lg px-8 py-6 border-gray-700 text-white hover:bg-gray-800">
                  <FileText className="mr-3 h-6 w-6" />
                  Research & Publications
                </Button>
              </Link>
            </div>
          </FadeIn>
        </div>
      </section>

      {/* Stats Section */}
      <section className="py-20 border-y border-gray-800 relative">
        <div className="max-w-7xl mx-auto px-6 relative">
          <StaggerContainer staggerDelay={0.1} className="grid grid-cols-2 md:grid-cols-4 gap-8">
            <StaggerItem>
              <motion.div
                className="text-center"
                initial={{ scale: 0 }}
                whileInView={{ scale: 1 }}
                viewport={{ once: true }}
                transition={{ type: "spring", stiffness: 100, damping: 10 }}
              >
                <div className="text-4xl md:text-5xl font-black text-transparent bg-clip-text bg-gradient-to-r from-chaos-accent-cyan to-chaos-primary-300 mb-2 animate-spring-in">
                  +39%
                </div>
                <div className="text-sm text-gray-500 font-medium uppercase tracking-wider">Bear Market Outperformance</div>
              </motion.div>
            </StaggerItem>
            <StaggerItem>
              <motion.div
                className="text-center"
                initial={{ scale: 0 }}
                whileInView={{ scale: 1 }}
                viewport={{ once: true }}
                transition={{ type: "spring", stiffness: 100, damping: 10, delay: 0.1 }}
              >
                <div className="text-4xl md:text-5xl font-black text-transparent bg-clip-text bg-gradient-to-r from-chaos-primary-400 to-chaos-accent-purple mb-2 animate-spring-in">
                  1.87
                </div>
                <div className="text-sm text-gray-500 font-medium uppercase tracking-wider">Sharpe Ratio</div>
              </motion.div>
            </StaggerItem>
            <StaggerItem>
              <motion.div
                className="text-center"
                initial={{ scale: 0 }}
                whileInView={{ scale: 1 }}
                viewport={{ once: true }}
                transition={{ type: "spring", stiffness: 100, damping: 10, delay: 0.2 }}
              >
                <div className="text-4xl md:text-5xl font-black text-transparent bg-clip-text bg-gradient-to-r from-chaos-accent-purple to-chaos-primary-300 mb-2 animate-spring-in">
                  5/5
                </div>
                <div className="text-sm text-gray-500 font-medium uppercase tracking-wider">Assets Tested</div>
              </motion.div>
            </StaggerItem>
            <StaggerItem>
              <motion.div
                className="text-center"
                initial={{ scale: 0 }}
                whileInView={{ scale: 1 }}
                viewport={{ once: true }}
                transition={{ type: "spring", stiffness: 100, damping: 10, delay: 0.3 }}
              >
                <div className="text-4xl md:text-5xl font-black text-transparent bg-clip-text bg-gradient-to-r from-chaos-primary-300 to-chaos-accent-cyan mb-2 animate-spring-in">
                  4
                </div>
                <div className="text-sm text-gray-500 font-medium uppercase tracking-wider">Theorems Proved</div>
              </motion.div>
            </StaggerItem>
          </StaggerContainer>
        </div>
      </section>

      {/* Features Section */}
      <section className="py-32">
        <div className="max-w-7xl mx-auto px-6">
          <FadeIn className="text-center mb-20">
            <h2 className="text-4xl md:text-5xl font-black text-white mb-6">Protocol Features</h2>
            <p className="text-gray-400 text-xl max-w-2xl mx-auto">
              A simple three-bucket approach that turns volatility into profit.
            </p>
          </FadeIn>

          <div className="space-y-12">
            <FadeIn>
              <div className="flex flex-col md:flex-row gap-8 items-start">
                <div className="flex-shrink-0 w-16 h-16 bg-gradient-to-br from-blue-600 to-purple-600 rounded-2xl flex items-center justify-center">
                  <span className="text-3xl font-black text-white">01</span>
                </div>
                <div className="flex-1">
                  <h3 className="text-2xl font-bold text-white mb-4">Diversify and Democratize with Ease</h3>
                  <p className="text-gray-400 text-lg leading-relaxed mb-4">
                    Split your portfolio into three buckets: 50% volatile asset, 30% stablecoin, 20% LP positions. 
                    Diversified from day one, reducing risk while maximizing returns.
                  </p>
                  <div className="flex items-center gap-2 text-blue-400 font-semibold">
                    <Wallet className="w-5 h-5" />
                    <span>Balanced Allocation</span>
                  </div>
                </div>
              </div>
            </FadeIn>

            <FadeIn delay={0.1}>
              <div className="flex flex-col md:flex-row gap-8 items-start">
                <div className="flex-shrink-0 w-16 h-16 bg-gradient-to-br from-purple-600 to-emerald-600 rounded-2xl flex items-center justify-center">
                  <span className="text-3xl font-black text-white">02</span>
                </div>
                <div className="flex-1">
                  <h3 className="text-2xl font-bold text-white mb-4">Auto-Rebalance on Market Swings</h3>
                  <p className="text-gray-400 text-lg leading-relaxed mb-4">
                    When prices swing, the protocol sells high and buys low automatically. 
                    Every price movement becomes an opportunity to profit. No emotional trading required.
                  </p>
                  <div className="flex items-center gap-2 text-purple-400 font-semibold">
                    <Zap className="w-5 h-5" />
                    <span>Real-Time Execution</span>
                  </div>
                </div>
              </div>
            </FadeIn>

            <FadeIn delay={0.2}>
              <div className="flex flex-col md:flex-row gap-8 items-start">
                <div className="flex-shrink-0 w-16 h-16 bg-gradient-to-br from-emerald-600 to-blue-600 rounded-2xl flex items-center justify-center">
                  <span className="text-3xl font-black text-white">03</span>
                </div>
                <div className="flex-1">
                  <h3 className="text-2xl font-bold text-white mb-4">Mathematically Proven</h3>
                  <p className="text-gray-400 text-lg leading-relaxed mb-4">
                    4 theorems formally verified in Lean 4. Zero unproven assumptions.
                    The strategy&apos;s performance is backed by rigorous mathematical proof.
                  </p>
                  <div className="flex items-center gap-2 text-emerald-400 font-semibold">
                    <Shield className="w-5 h-5" />
                    <span>Formal Verification</span>
                  </div>
                </div>
              </div>
            </FadeIn>

            <FadeIn delay={0.3}>
              <div className="flex flex-col md:flex-row gap-8 items-start">
                <div className="flex-shrink-0 w-16 h-16 bg-gradient-to-br from-amber-600 to-orange-600 rounded-2xl flex items-center justify-center">
                  <span className="text-3xl font-black text-white">04</span>
                </div>
                <div className="flex-1">
                  <h3 className="text-2xl font-bold text-white mb-4">LP Fee Floor Protection</h3>
                  <p className="text-gray-400 text-lg leading-relaxed mb-4">
                    Earn consistent ~20% APY from liquidity provision positions. 
                    Creates a performance floor that protects against bear markets.
                  </p>
                  <div className="flex items-center gap-2 text-amber-400 font-semibold">
                    <TrendingUp className="w-5 h-5" />
                    <span>Yield Generation</span>
                  </div>
                </div>
              </div>
            </FadeIn>

            <FadeIn delay={0.4}>
              <div className="flex flex-col md:flex-row gap-8 items-start">
                <div className="flex-shrink-0 w-16 h-16 bg-gradient-to-br from-rose-600 to-pink-600 rounded-2xl flex items-center justify-center">
                  <span className="text-3xl font-black text-white">05</span>
                </div>
                <div className="flex-1">
                  <h3 className="text-2xl font-bold text-white mb-4">Bounded Maximum Drawdown</h3>
                  <p className="text-gray-400 text-lg leading-relaxed mb-4">
                    Maximum drawdown is bounded by stablecoin allocation and rebalancing thresholds. 
                    Even in the worst market conditions, losses are capped.
                  </p>
                  <div className="flex items-center gap-2 text-rose-400 font-semibold">
                    <Lock className="w-5 h-5" />
                    <span>Risk Protection</span>
                  </div>
                </div>
              </div>
            </FadeIn>
          </div>
        </div>
      </section>

      {/* CTA Section */}
      <section className="py-32 bg-gradient-to-b from-gray-800 to-gray-900">
        <div className="max-w-4xl mx-auto px-6 text-center">
          <FadeIn>
            <motion.div
              initial={{ scale: 0.9 }}
              animate={{ scale: 1 }}
              className="inline-block mb-8"
            >
              <div className="w-24 h-24 bg-gradient-to-br from-blue-600 to-purple-600 rounded-3xl flex items-center justify-center mx-auto shadow-2xl shadow-blue-600/30">
                <Sparkles className="w-12 h-12 text-white" />
              </div>
            </motion.div>
            <h2 className="text-4xl md:text-5xl font-black text-white mb-6">
              Ready to Tame Chaos?
            </h2>
          </FadeIn>
          <FadeIn delay={0.1}>
            <p className="text-gray-400 text-xl mb-12 leading-relaxed">
              Join the community. Read the code. Run the backtest yourself. 
              See the strategy in action through market history.
            </p>
          </FadeIn>
          <FadeIn delay={0.2}>
            <div className="flex flex-col sm:flex-row gap-4 justify-center">
              <Link href="/coming-soon">
                <Button size="lg" variant="chaos" className="text-lg px-10 py-6">
                  <Sparkles className="mr-3 h-6 w-6" />
                  Launch App
                  <ArrowRight className="ml-2 h-5 w-5" />
                </Button>
              </Link>
              <Link href="/research">
                <Button size="lg" variant="outline" className="text-lg px-10 py-6 border-gray-700 text-white hover:bg-gray-800">
                  <FileText className="mr-3 h-6 w-6" />
                  Read Papers
                </Button>
              </Link>
            </div>
          </FadeIn>
        </div>
      </section>

    </div>
  );
}
