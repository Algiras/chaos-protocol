import Head from 'next/head';
import Link from 'next/link';
import { motion } from 'framer-motion';
import { Button } from '@/components/ui/button';
import { ArrowLeft, Rocket, FileText } from 'lucide-react';

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

      <section className="min-h-[80vh] flex items-center justify-center bg-gray-900">
        <div className="max-w-2xl mx-auto px-6 text-center">
          <motion.div
            initial={{ scale: 0.8, opacity: 0 }}
            animate={{ scale: 1, opacity: 1 }}
            transition={{ type: 'spring', stiffness: 100, damping: 15 }}
            className="inline-block mb-8"
          >
            <div className="w-24 h-24 bg-gradient-to-br from-blue-600 to-purple-600 rounded-3xl flex items-center justify-center mx-auto shadow-2xl shadow-blue-600/30">
              <Rocket className="w-12 h-12 text-white" />
            </div>
          </motion.div>

          <motion.div
            initial={{ opacity: 0, y: 20 }}
            animate={{ opacity: 1, y: 0 }}
            transition={{ delay: 0.2 }}
          >
            <h1 className="text-5xl md:text-6xl font-black text-white mb-6">
              Coming Soon
            </h1>
            <p className="text-xl text-gray-400 mb-12 leading-relaxed">
              The CHAOS Protocol app is under development. In the meantime, explore our research and formally verified proofs.
            </p>
          </motion.div>

          <motion.div
            initial={{ opacity: 0, y: 20 }}
            animate={{ opacity: 1, y: 0 }}
            transition={{ delay: 0.4 }}
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
          </motion.div>
        </div>
      </section>
    </>
  );
}
