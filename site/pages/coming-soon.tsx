import Head from 'next/head';
import Link from 'next/link';
import { motion } from 'framer-motion';
import { Button } from '@/components/ui/button';
import { ArrowLeft, Rocket, FileText, Github, Clock } from 'lucide-react';
import dynamic from 'next/dynamic';

// Lazy load AttractorBackground for better performance
const AttractorBackground = dynamic(
  () => import("@/components/chaos/core/AttractorBackground"),
  { ssr: false }
);

export default function ComingSoon() {
  return (
    <>
      <Head>
        <title>Coming Soon | CHAOS Protocol</title>
        <meta name="description" content="The CHAOS Protocol app is coming soon. Stay tuned." />
        <meta property="og:title" content="Coming Soon | CHAOS Protocol" />
        <meta property="og:description" content="The CHAOS Protocol app is coming soon. Stay tuned." />
        <meta property="og:image" content="https://chaosprotocol.io/og-image.png" />
        <meta property="og:url" content="https://chaosprotocol.io/coming-soon" />
        <meta property="og:type" content="website" />
        <meta name="twitter:card" content="summary_large_image" />
        <meta name="twitter:title" content="Coming Soon | CHAOS Protocol" />
        <meta name="twitter:description" content="The CHAOS Protocol app is coming soon. Stay tuned." />
        <meta name="twitter:image" content="https://chaosprotocol.io/og-image.png" />
      </Head>

      <section className="relative min-h-[80vh] flex items-center justify-center bg-gray-900 overflow-hidden">
        {/* Lorenz Attractor Background */}
        <AttractorBackground
          type="lorenz"
          volatility={0.6}
          sentiment="neutral"
          interactive={true}
          performance="auto"
          opacity={0.5}
          className="absolute inset-0"
        />

        <motion.div
          initial={{ opacity: 0 }}
          animate={{ opacity: 0.2 }}
          transition={{ duration: 2 }}
          className="absolute inset-0 bg-gradient-to-b from-transparent via-gray-900/70 to-gray-900"
        />

        <div className="relative z-10 max-w-3xl mx-auto px-6 text-center">
          <motion.div
            initial={{ scale: 0.5, opacity: 0 }}
            animate={{ scale: 1, opacity: 1 }}
            transition={{
              type: 'spring',
              stiffness: 100,
              damping: 15,
              delay: 0.2
            }}
            className="inline-block mb-8"
          >
            <div className="w-32 h-32 bg-gradient-to-br from-blue-600 via-purple-600 to-emerald-600 rounded-3xl flex items-center justify-center mx-auto shadow-2xl shadow-purple-600/40 animate-pulse">
              <Rocket className="w-16 h-16 text-white" />
            </div>
          </motion.div>

          <motion.div
            initial={{ opacity: 0, y: 30 }}
            animate={{ opacity: 1, y: 0 }}
            transition={{ delay: 0.4, duration: 0.8 }}
          >
            <h1 className="text-5xl md:text-7xl font-black text-white mb-6 leading-tight">
              Coming Soon
            </h1>
            <p className="text-2xl text-transparent bg-clip-text bg-gradient-to-r from-blue-400 via-purple-400 to-emerald-400 mb-4 font-bold">
              Building the Future of DeFi
            </p>
            <p className="text-xl text-gray-400 mb-12 leading-relaxed max-w-2xl mx-auto">
              The CHAOS Protocol app is under development. Explore our formally verified research and mathematical proofs while we build.
            </p>
          </motion.div>

          {/* Progress Indicators */}
          <motion.div
            initial={{ opacity: 0, scale: 0.9 }}
            animate={{ opacity: 1, scale: 1 }}
            transition={{ delay: 0.6, duration: 0.6 }}
            className="mb-12"
          >
            <div className="grid grid-cols-3 gap-4 max-w-xl mx-auto mb-8">
              <div className="bg-gray-800/50 backdrop-blur border border-gray-700 rounded-xl p-4">
                <div className="text-3xl font-black text-emerald-400 mb-1">✓</div>
                <div className="text-sm text-gray-400">Research</div>
              </div>
              <div className="bg-gray-800/50 backdrop-blur border border-gray-700 rounded-xl p-4">
                <div className="text-3xl font-black text-emerald-400 mb-1">✓</div>
                <div className="text-sm text-gray-400">Proofs</div>
              </div>
              <div className="bg-gray-800/50 backdrop-blur border border-purple-600 rounded-xl p-4 ring-2 ring-purple-600/30">
                <Clock className="w-8 h-8 text-purple-400 mx-auto mb-1 animate-pulse" />
                <div className="text-sm text-purple-400 font-semibold">Contracts</div>
              </div>
            </div>
          </motion.div>

          <motion.div
            initial={{ opacity: 0, y: 20 }}
            animate={{ opacity: 1, y: 0 }}
            transition={{ delay: 0.8 }}
            className="flex flex-col sm:flex-row gap-4 justify-center"
          >
            <Link href="/">
              <Button size="lg" variant="outline" className="text-lg px-8 py-6 border-gray-700 text-white hover:bg-gray-800">
                <ArrowLeft className="mr-2 h-5 w-5" />
                Back to Home
              </Button>
            </Link>
            <Link href="/research">
              <Button size="lg" variant="chaos" className="text-lg px-8 py-6">
                <FileText className="mr-2 h-5 w-5" />
                Read Research
              </Button>
            </Link>
            <Link href="https://github.com/Algiras/chaos-protocol">
              <Button size="lg" variant="outline" className="text-lg px-8 py-6 border-gray-700 text-white hover:bg-gray-800">
                <Github className="mr-2 h-5 w-5" />
                View Code
              </Button>
            </Link>
          </motion.div>
        </div>
      </section>
    </>
  );
}
