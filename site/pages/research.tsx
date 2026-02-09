import Head from 'next/head';
import { motion } from 'framer-motion';
import { FadeIn, StaggerContainer, StaggerItem } from '@/components/animations';
import { Button } from '@/components/ui/button';
import { Card, CardContent, CardHeader, CardTitle, CardDescription } from '@/components/ui/card';
import { ArrowRight, FileText, Github, CheckCircle2, Download, ExternalLink, BookOpen, Shield } from 'lucide-react';
import dynamic from 'next/dynamic';
import type { GetStaticProps } from 'next';

// Lazy load AttractorBackground for better performance
const AttractorBackground = dynamic(
  () => import("@/components/chaos/core/AttractorBackground"),
  { ssr: false }
);

const theorems = [
  {
    num: 1,
    name: 'Positive Expected Value',
    statement: 'Rebalancing premium exceeds transaction costs when volatility σ > 25.5%',
    icon: CheckCircle2
  },
  {
    num: 2,
    name: 'Bounded Maximum Drawdown',
    statement: 'Maximum drawdown ≤ 64% of underlying asset drawdown',
    icon: CheckCircle2
  },
  {
    num: 3,
    name: 'LP Fee Floor Protection',
    statement: 'Minimum 3% annual return from liquidity provision fees alone',
    icon: CheckCircle2
  },
  {
    num: 4,
    name: 'Convex Payoff Structure',
    statement: 'Strategy gains from both upward and downward price movements',
    icon: CheckCircle2
  },
];

const publications = [
  {
    title: 'CHAOS Whitepaper',
    description: 'Comprehensive analysis of the CHAOS protocol including mathematical framework, game theory, formal verification, backtest results, and risk analysis.',
    pages: 47,
    file: '/whitepaper/chaos-whitepaper.pdf',
    icon: FileText,
    highlight: true
  },
  {
    title: 'Formal Verification Proof Paper',
    description: 'Complete Lean 4 formal proofs of the four core theorems. Zero unproven assumptions. Mathematical certainty.',
    pages: 23,
    file: '/whitepaper/proof-paper.pdf',
    icon: Shield,
    highlight: true
  },
  {
    title: 'Investor Brief & Litepaper',
    description: 'Executive summary for investors. Key metrics, performance data, and market opportunity.',
    pages: 8,
    file: '/whitepaper/investor-brief.pdf',
    icon: BookOpen,
    highlight: false
  },
];

export default function Research() {
  return (
    <>
      <Head>
        <title>Research & Publications | CHAOS Protocol</title>
        <meta name="description" content="Formally verified theorems and research publications for the CHAOS antifragile treasury protocol." />
      </Head>

      {/* Hero Section */}
      <section className="relative min-h-[60vh] flex items-center justify-center overflow-hidden bg-gradient-to-br from-gray-900 via-gray-800 to-gray-900">
        {/* Lorenz Attractor Background */}
        <AttractorBackground
          type="lorenz"
          volatility={0.3}
          sentiment="neutral"
          interactive={true}
          performance="auto"
          opacity={0.4}
          className="absolute inset-0"
        />

        <motion.div
          initial={{ opacity: 0 }}
          animate={{ opacity: 0.3 }}
          transition={{ duration: 2 }}
          className="absolute inset-0 bg-gradient-to-b from-transparent via-gray-900/50 to-gray-900"
        />

        <div className="relative z-10 max-w-6xl mx-auto px-6 text-center">
          <FadeIn>
            <span className="inline-block px-4 py-2 rounded-full bg-blue-600/20 text-blue-400 text-sm font-bold mb-8 border border-blue-600/30">
              Mathematically Proven
            </span>
          </FadeIn>

          <FadeIn delay={0.1}>
            <h1 className="text-5xl md:text-7xl font-black text-white mb-6 leading-tight">
              Research &<br />
              <span className="text-transparent bg-clip-text bg-gradient-to-r from-blue-400 via-purple-400 to-emerald-400">
                Publications
              </span>
            </h1>
          </FadeIn>

          <FadeIn delay={0.2}>
            <p className="text-xl text-gray-300 max-w-2xl mx-auto mb-12 leading-relaxed">
              Formally verified in Lean 4. Four theorems with zero unproven assumptions.
              The mathematics behind antifragile volatility harvesting.
            </p>
          </FadeIn>
        </div>
      </section>

      {/* Formally Verified Theorems */}
      <section className="py-32 bg-gray-900">
        <div className="max-w-6xl mx-auto px-6">
          <FadeIn className="text-center mb-16">
            <h2 className="text-4xl md:text-5xl font-black text-white mb-6">Formally Verified Theorems</h2>
            <p className="text-gray-400 text-xl max-w-2xl mx-auto">
              Proven in Lean 4, the gold standard for mathematical verification.
              Each theorem provides mathematical certainty about the protocol&apos;s behavior.
            </p>
          </FadeIn>

          <StaggerContainer staggerDelay={0.1} className="space-y-6">
            {theorems.map((theorem, idx) => (
              <StaggerItem key={idx}>
                <Card className="bg-gray-800 border-gray-700 hover:border-blue-600/50 transition-all duration-300">
                  <CardContent className="p-8">
                    <div className="flex items-start gap-6">
                      <div className="flex-shrink-0">
                        <div className="w-16 h-16 bg-gradient-to-br from-blue-600 to-purple-600 rounded-2xl flex items-center justify-center">
                          <span className="text-2xl font-black text-white">{theorem.num}</span>
                        </div>
                      </div>
                      <div className="flex-1">
                        <div className="flex items-center gap-3 mb-3">
                          <CheckCircle2 className="w-6 h-6 text-emerald-400" />
                          <h3 className="text-2xl font-bold text-white">{theorem.name}</h3>
                        </div>
                        <p className="text-gray-300 text-lg leading-relaxed">{theorem.statement}</p>
                      </div>
                    </div>
                  </CardContent>
                </Card>
              </StaggerItem>
            ))}
          </StaggerContainer>

          <FadeIn delay={0.5} className="text-center mt-12">
            <div className="inline-flex items-center gap-2 px-6 py-3 rounded-full bg-emerald-600/10 text-emerald-400 border border-emerald-600/30">
              <Shield className="w-5 h-5" />
              <span className="font-semibold">Zero unproven assumptions. Mathematical certainty.</span>
            </div>
          </FadeIn>
        </div>
      </section>

      {/* Publications */}
      <section className="py-32 bg-gradient-to-b from-gray-900 to-gray-800">
        <div className="max-w-6xl mx-auto px-6">
          <FadeIn className="text-center mb-16">
            <h2 className="text-4xl md:text-5xl font-black text-white mb-6">Publications</h2>
            <p className="text-gray-400 text-xl max-w-2xl mx-auto">
              Deep dive into the mathematics, verification, and implementation of CHAOS.
            </p>
          </FadeIn>

          <StaggerContainer staggerDelay={0.15} className="grid md:grid-cols-2 lg:grid-cols-3 gap-8">
            {publications.map((pub, idx) => {
              const Icon = pub.icon;
              return (
                <StaggerItem key={idx}>
                  <Card className={`h-full bg-gray-800 border-gray-700 hover:border-purple-600/50 transition-all duration-300 ${pub.highlight ? 'ring-2 ring-purple-600/30' : ''}`}>
                    <CardHeader>
                      <div className="w-14 h-14 bg-gradient-to-br from-purple-600 to-blue-600 rounded-xl flex items-center justify-center mb-4">
                        <Icon className="w-7 h-7 text-white" />
                      </div>
                      <CardTitle className="text-white text-2xl">{pub.title}</CardTitle>
                      <CardDescription className="text-gray-400 text-base">
                        {pub.description}
                      </CardDescription>
                    </CardHeader>
                    <CardContent>
                      <div className="flex items-center justify-between mb-6">
                        <span className="text-gray-500 text-sm font-medium">{pub.pages} pages</span>
                        {pub.highlight && (
                          <span className="px-3 py-1 rounded-full bg-purple-600/20 text-purple-400 text-xs font-semibold border border-purple-600/30">
                            Featured
                          </span>
                        )}
                      </div>
                      <a href={pub.file} download>
                        <Button variant="outline" className="w-full border-gray-700 text-white hover:bg-gray-700 hover:text-blue-400">
                          <Download className="mr-2 h-4 w-4" />
                          Download PDF
                        </Button>
                      </a>
                    </CardContent>
                  </Card>
                </StaggerItem>
              );
            })}
          </StaggerContainer>

          {/* GitHub Repository Card */}
          <FadeIn delay={0.6} className="mt-12">
            <Card className="bg-gray-800 border-gray-700 hover:border-blue-600/50 transition-all duration-300">
              <CardContent className="p-8">
                <div className="flex flex-col md:flex-row items-center justify-between gap-6">
                  <div className="flex items-center gap-6">
                    <div className="w-16 h-16 bg-gradient-to-br from-gray-700 to-gray-900 rounded-2xl flex items-center justify-center">
                      <Github className="w-8 h-8 text-white" />
                    </div>
                    <div>
                      <h3 className="text-2xl font-bold text-white mb-2">GitHub Repository</h3>
                      <p className="text-gray-400 text-lg">
                        Full source code, Lean 4 proofs, and implementation details
                      </p>
                    </div>
                  </div>
                  <a href="https://github.com/Algiras/chaos" target="_blank" rel="noopener noreferrer">
                    <Button variant="outline" size="lg" className="border-gray-700 text-white hover:bg-gray-700 hover:text-blue-400">
                      <ExternalLink className="mr-2 h-5 w-5" />
                      View on GitHub
                    </Button>
                  </a>
                </div>
              </CardContent>
            </Card>
          </FadeIn>
        </div>
      </section>

      {/* CTA Section */}
      <section className="py-32 bg-gray-900">
        <div className="max-w-4xl mx-auto px-6 text-center">
          <FadeIn>
            <motion.div
              initial={{ scale: 0.9 }}
              animate={{ scale: 1 }}
              className="inline-block mb-8"
            >
              <div className="w-24 h-24 bg-gradient-to-br from-blue-600 to-purple-600 rounded-3xl flex items-center justify-center mx-auto shadow-2xl shadow-blue-600/30">
                <Shield className="w-12 h-12 text-white" />
              </div>
            </motion.div>
            <h2 className="text-4xl md:text-5xl font-black text-white mb-6">
              Ready to See It in Action?
            </h2>
          </FadeIn>
          <FadeIn delay={0.1}>
            <p className="text-gray-400 text-xl mb-12 leading-relaxed">
              Explore the protocol with real-time portfolio management and governance features.
            </p>
          </FadeIn>
          <FadeIn delay={0.2}>
            <a href={process.env.NEXT_PUBLIC_SITE_URL === 'https://chaosprotocol.io' ? 'https://app.chaosprotocol.io' : '/dashboard'}>
              <Button size="lg" variant="chaos" className="text-lg px-10 py-6">
                Launch App
                <ArrowRight className="ml-2 h-5 w-5" />
              </Button>
            </a>
          </FadeIn>
        </div>
      </section>
    </>
  );
}
