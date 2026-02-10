import Head from 'next/head';
import Link from 'next/link';
import { motion } from 'framer-motion';
import { FadeIn, StaggerContainer, StaggerItem } from '@/components/animations';
import { Button } from '@/components/ui/button';
import { Card, CardContent, CardHeader, CardTitle, CardDescription } from '@/components/ui/card';
import { ArrowRight, Wallet, TrendingUp, Shield, Zap, DollarSign, BarChart3, Lock } from 'lucide-react';
const steps = [
  {
    num: 1,
    title: 'Diversify Your Portfolio',
    description: 'Split your capital into three buckets: 50% volatile asset (BTC, ADA, ETH), 30% stablecoin (USDC/DJED), and 20% liquidity provision positions. This balanced allocation reduces risk from day one.',
    details: [
      '50% in volatile crypto asset',
      '30% in stablecoin reserve',
      '20% in LP positions for fees'
    ],
    icon: Wallet,
    gradient: 'from-blue-600 to-purple-600'
  },
  {
    num: 2,
    title: 'Rebalance on Price Swings',
    description: 'When the volatile asset moves ±10% from target allocation, the protocol automatically rebalances by selling high or buying low. This captures the rebalancing premium from market volatility.',
    details: [
      'Price rises → Sell high automatically',
      'Price falls → Buy low automatically',
      'Capture profit on every swing'
    ],
    icon: Zap,
    gradient: 'from-purple-600 to-emerald-600'
  },
  {
    num: 3,
    title: 'Earn Continuous LP Fees',
    description: 'The 20% LP allocation generates consistent ~20% APY from trading fees. This creates a performance floor that protects against bear markets while the rebalancing strategy profits from volatility.',
    details: [
      '~20% APY from LP trading fees',
      'Creates a performance floor',
      'Works in all market conditions'
    ],
    icon: DollarSign,
    gradient: 'from-emerald-600 to-blue-600'
  },
];

const gradientMap: Record<string, string> = {
  blue: 'from-blue-600 to-blue-400',
  purple: 'from-purple-600 to-purple-400',
  emerald: 'from-emerald-600 to-emerald-400',
};

const benefits = [
  {
    title: 'Bounded Drawdown',
    description: 'Maximum drawdown is mathematically proven to be ≤64% of the underlying asset drawdown. The stablecoin buffer and rebalancing mechanism limit losses.',
    icon: Shield,
    color: 'blue'
  },
  {
    title: 'Convex Payoff',
    description: 'The strategy gains from both upward and downward price movements. Volatility becomes your ally, not your enemy. More chaos = more profit opportunity.',
    icon: TrendingUp,
    color: 'purple'
  },
  {
    title: 'Positive Expected Value',
    description: 'Formally proven to have positive expected value when asset volatility exceeds 25.5%. Transaction costs are more than offset by rebalancing gains.',
    icon: BarChart3,
    color: 'emerald'
  },
];

export default function HowItWorks() {
  return (
    <>
      <Head>
        <title>How It Works | CHAOS Protocol</title>
        <meta name="description" content="Learn how CHAOS turns market volatility into profit through diversification, automatic rebalancing, and LP fee generation." />
        <meta property="og:title" content="How It Works | CHAOS Protocol" />
        <meta property="og:description" content="Learn how CHAOS turns market volatility into profit through diversification, automatic rebalancing, and LP fee generation." />
        <meta property="og:image" content="https://chaosprotocol.io/og-image.png" />
        <meta property="og:url" content="https://chaosprotocol.io/how-it-works" />
        <meta property="og:type" content="article" />
        <meta name="twitter:card" content="summary_large_image" />
        <meta name="twitter:title" content="How It Works | CHAOS Protocol" />
        <meta name="twitter:description" content="Learn how CHAOS turns market volatility into profit through diversification, automatic rebalancing, and LP fee generation." />
        <meta name="twitter:image" content="https://chaosprotocol.io/og-image.png" />
      </Head>

      {/* Hero Section */}
      <section className="relative min-h-[60vh] flex items-center justify-center overflow-hidden">
        <div className="relative z-10 max-w-6xl mx-auto px-6 text-center">
          <FadeIn>
            <span className="inline-block px-4 py-2 rounded-full bg-purple-600/20 text-purple-400 text-sm font-bold mb-8 border border-purple-600/30">
              Simple Yet Powerful
            </span>
          </FadeIn>

          <FadeIn delay={0.1}>
            <h1 className="text-5xl md:text-7xl font-black text-white mb-6 leading-tight">
              How
              <span className="text-transparent bg-clip-text bg-gradient-to-r from-blue-400 via-purple-400 to-emerald-400">
                {' '}CHAOS{' '}
              </span>
              Works
            </h1>
          </FadeIn>

          <FadeIn delay={0.2}>
            <p className="text-xl text-gray-300 max-w-2xl mx-auto mb-12 leading-relaxed">
              Three simple steps to turn market volatility into consistent profit.
              No complex strategies. No emotional trading. Just math.
            </p>
          </FadeIn>
        </div>
      </section>

      {/* How It Works Steps */}
      <section className="py-32">
        <div className="max-w-6xl mx-auto px-6">
          <FadeIn className="text-center mb-20">
            <h2 className="text-4xl md:text-5xl font-black text-white mb-6">The Strategy in 3 Steps</h2>
            <p className="text-gray-300 text-xl max-w-2xl mx-auto">
              A formally verified approach to profiting from market chaos.
            </p>
          </FadeIn>

          <div className="space-y-16">
            {steps.map((step, idx) => {
              const Icon = step.icon;
              return (
                <FadeIn key={idx} delay={idx * 0.2}>
                  <motion.div
                    initial={{ opacity: 0, x: idx % 2 === 0 ? -50 : 50 }}
                    whileInView={{ opacity: 1, x: 0 }}
                    viewport={{ once: true }}
                    transition={{ duration: 0.6 }}
                  >
                    <Card className="bg-gray-800 border-gray-700 hover:border-purple-600/50 transition-all duration-300">
                      <CardContent className="p-8 md:p-12">
                        <div className="flex flex-col md:flex-row gap-8 items-start">
                          <div className="flex-shrink-0">
                            <div className={`w-20 h-20 bg-gradient-to-br ${step.gradient} rounded-2xl flex items-center justify-center shadow-2xl`}>
                              <Icon className="w-10 h-10 text-white" />
                            </div>
                          </div>
                          <div className="flex-1">
                            <div className="flex items-center gap-4 mb-4">
                              <span className="text-5xl font-black text-gray-700">{step.num}</span>
                              <h3 className="text-3xl font-bold text-white">{step.title}</h3>
                            </div>
                            <p className="text-gray-300 text-lg leading-relaxed mb-6">
                              {step.description}
                            </p>
                            <ul className="space-y-3">
                              {step.details.map((detail, detailIdx) => (
                                <li key={detailIdx} className="flex items-center gap-3 text-gray-400">
                                  <div className="w-2 h-2 rounded-full bg-gradient-to-r from-blue-400 to-purple-400" />
                                  <span>{detail}</span>
                                </li>
                              ))}
                            </ul>
                          </div>
                        </div>
                      </CardContent>
                    </Card>
                  </motion.div>
                </FadeIn>
              );
            })}
          </div>
        </div>
      </section>

      {/* Key Benefits */}
      <section className="py-32">
        <div className="max-w-6xl mx-auto px-6">
          <FadeIn className="text-center mb-16">
            <h2 className="text-4xl md:text-5xl font-black text-white mb-6">Key Benefits</h2>
            <p className="text-gray-300 text-xl max-w-2xl mx-auto">
              Mathematically proven advantages over traditional HODL strategies.
            </p>
          </FadeIn>

          <StaggerContainer staggerDelay={0.15} className="grid md:grid-cols-3 gap-8">
            {benefits.map((benefit, idx) => {
              const Icon = benefit.icon;
              return (
                <StaggerItem key={idx}>
                  <Card className="h-full bg-gray-800 border-gray-700 hover:border-purple-600/50 transition-all duration-300">
                    <CardHeader>
                      <div className={`w-14 h-14 bg-gradient-to-br ${gradientMap[benefit.color]} rounded-xl flex items-center justify-center mb-4`}>
                        <Icon className="w-7 h-7 text-white" />
                      </div>
                      <CardTitle className="text-white text-2xl">{benefit.title}</CardTitle>
                    </CardHeader>
                    <CardContent>
                      <p className="text-gray-400 text-base leading-relaxed">
                        {benefit.description}
                      </p>
                    </CardContent>
                  </Card>
                </StaggerItem>
              );
            })}
          </StaggerContainer>

          {/* Mathematical Guarantee */}
          <FadeIn delay={0.5} className="text-center mt-16">
            <Card className="bg-gradient-to-br from-purple-900/30 to-blue-900/30 border-purple-600/30 shadow-2xl shadow-purple-600/10">
              <CardContent className="p-12">
                <div className="flex items-center justify-center gap-3 mb-6">
                  <Lock className="w-8 h-8 text-purple-400" />
                  <h3 className="text-3xl font-black text-white">Mathematical Guarantee</h3>
                </div>
                <p className="text-gray-300 text-xl leading-relaxed max-w-3xl mx-auto">
                  Every claim is backed by formal proofs in Lean 4. No assumptions. No handwaving.
                  Just pure mathematics verifying that the strategy works as promised.
                </p>
              </CardContent>
            </Card>
          </FadeIn>
        </div>
      </section>

      {/* CTA Section */}
      <section className="py-32">
        <div className="max-w-4xl mx-auto px-6 text-center">
          <FadeIn>
            <motion.div
              initial={{ scale: 0.9 }}
              animate={{ scale: 1 }}
              className="inline-block mb-8"
            >
              <div className="w-24 h-24 bg-gradient-to-br from-blue-600 to-purple-600 rounded-3xl flex items-center justify-center mx-auto shadow-2xl shadow-blue-600/30">
                <Zap className="w-12 h-12 text-white" />
              </div>
            </motion.div>
            <h2 className="text-4xl md:text-5xl font-black text-white mb-6">
              Ready to Start Harvesting Volatility?
            </h2>
          </FadeIn>
          <FadeIn delay={0.1}>
            <p className="text-gray-300 text-xl mb-12 leading-relaxed">
              Connect your wallet and see the protocol in action.
            </p>
          </FadeIn>
          <FadeIn delay={0.2}>
            <div className="flex flex-col sm:flex-row gap-4 justify-center">
              <Link href="/coming-soon">
                <Button size="lg" variant="chaos" className="text-lg px-10 py-6">
                  Launch App
                  <ArrowRight className="ml-2 h-5 w-5" />
                </Button>
              </Link>
              <Link href="/research">
                <Button size="lg" variant="outline" className="text-lg px-10 py-6 border-gray-700 text-white hover:bg-gray-800">
                  Read the Research
                </Button>
              </Link>
            </div>
          </FadeIn>
        </div>
      </section>
    </>
  );
}
