import Head from 'next/head';
import { motion } from 'framer-motion';
import { FadeIn, CountUp, StaggerContainer, StaggerItem } from '@/components/animations';
import { Button } from '@/components/ui/button';
import { Card, CardContent, CardHeader, CardTitle, CardDescription } from '@/components/ui/card';
import Link from 'next/link';
import { ArrowRight, TrendingUp, Shield, Zap, Wallet, Vote, Users } from 'lucide-react';

const performanceData = [
  { asset: 'ADA (Cardano)', chaos: -31.8, hodl: -61.9, edge: 79.1, chaosDD: -46.7, hodlDD: -74.5 },
  { asset: 'BTC (Bitcoin)', chaos: -4.9, hodl: -14.2, edge: 10.9, chaosDD: -27.9, hodlDD: -49.6 },
  { asset: 'ETH (Ethereum)', chaos: 9.5, hodl: 3.4, edge: 6.0, chaosDD: -36.7, hodlDD: -62.3 },
  { asset: 'SOL (Solana)', chaos: -9.5, hodl: -30.4, edge: 30.0, chaosDD: -41.5, hodlDD: -68.3 },
  { asset: 'DOT (Polkadot)', chaos: -34.6, hodl: -65.7, edge: 90.9, chaosDD: -46.5, hodlDD: -76.4 },
];

const theorems = [
  { num: 1, name: 'Positive expected value', result: 'Rebalancing premium > costs when \u03c3 > 25.5%', icon: TrendingUp },
  { num: 2, name: 'Bounded drawdown', result: 'CHAOS DD \u2264 64% of asset DD', icon: Shield },
  { num: 3, name: 'LP fee floor', result: '\u2265 3% annual return from fees alone', icon: Wallet },
  { num: 4, name: 'Convex payoff', result: 'Strategy gains from volatility', icon: Zap },
];

export default function Investors() {
  return (
    <>
      <Head>
        <title>Invest in CHAOS | Antifragile Treasury Protocol</title>
        <meta name="description" content="CHAOS is a formally verified treasury management protocol that profits from crypto volatility. Backtested +39% outperformance." />
      </Head>

      {/* Hero Section */}
      <section className="relative min-h-[85vh] flex items-center justify-center overflow-hidden bg-gradient-to-br from-blue-50 via-white to-emerald-50">
        <motion.div
          initial={{ opacity: 0 }}
          animate={{ opacity: 0.1 }}
          transition={{ duration: 1.5 }}
          className="absolute inset-0 bg-[radial-gradient(ellipse_at_top_right,_var(--tw-gradient-stops))] from-blue-200 via-transparent to-transparent"
        />
        
        <div className="relative z-10 max-w-6xl mx-auto px-6 text-center">
          <motion.div
            initial={{ opacity: 0, y: 30 }}
            animate={{ opacity: 1, y: 0 }}
            transition={{ duration: 0.8, delay: 0.2 }}
          >
            <span className="inline-block px-4 py-2 rounded-full bg-blue-100 text-blue-700 text-sm font-semibold mb-6">
              Pre-Seed Investment Opportunity
            </span>
          </motion.div>

          <motion.h1
            initial={{ opacity: 0, y: 30 }}
            animate={{ opacity: 1, y: 0 }}
            transition={{ duration: 0.8, delay: 0.4 }}
            className="text-5xl md:text-7xl font-black text-gray-900 mb-6 leading-tight"
          >
            Make Money From<br />
            <span className="text-transparent bg-clip-text bg-gradient-to-r from-blue-600 to-emerald-500">
              Market Chaos
            </span>
          </motion.h1>

          <motion.p
            initial={{ opacity: 0, y: 30 }}
            animate={{ opacity: 1, y: 0 }}
            transition={{ duration: 0.8, delay: 0.6 }}
            className="text-xl text-gray-600 max-w-2xl mx-auto mb-12"
          >
            CHAOS is a formally verified treasury protocol that turns volatility into profit. 
            Mathematically proven. Zero unproven assumptions.
          </motion.p>

          {/* Metrics */}
          <StaggerContainer staggerDelay={0.15} className="grid grid-cols-2 md:grid-cols-4 gap-6 max-w-4xl mx-auto mb-12">
            <StaggerItem>
              <Card className="border-blue-100 shadow-lg shadow-blue-100/50">
                <CardContent className="pt-6">
                  <div className="text-4xl font-black text-blue-600 mb-2">
                    +<CountUp end={39} suffix="%" duration={2} delay={0.8} />
                  </div>
                  <div className="text-sm text-gray-500 font-medium">Outperformance vs HODL</div>
                </CardContent>
              </Card>
            </StaggerItem>
            <StaggerItem>
              <Card className="border-emerald-100 shadow-lg shadow-emerald-100/50">
                <CardContent className="pt-6">
                  <div className="text-4xl font-black text-emerald-600 mb-2">
                    <CountUp end={1.87} decimals={2} duration={2} delay={0.9} />
                  </div>
                  <div className="text-sm text-gray-500 font-medium">Sharpe Ratio</div>
                </CardContent>
              </Card>
            </StaggerItem>
            <StaggerItem>
              <Card className="border-purple-100 shadow-lg shadow-purple-100/50">
                <CardContent className="pt-6">
                  <div className="text-4xl font-black text-purple-600 mb-2">
                    <CountUp end={40} suffix="%" duration={2} delay={1.0} />
                  </div>
                  <div className="text-sm text-gray-500 font-medium">Less Drawdown</div>
                </CardContent>
              </Card>
            </StaggerItem>
            <StaggerItem>
              <Card className="border-amber-100 shadow-lg shadow-amber-100/50">
                <CardContent className="pt-6">
                  <div className="text-4xl font-black text-amber-600 mb-2">
                    <CountUp end={5} suffix="/5" duration={2} delay={1.1} />
                  </div>
                  <div className="text-sm text-gray-500 font-medium">Win Rate</div>
                </CardContent>
              </Card>
            </StaggerItem>
          </StaggerContainer>

          <motion.div
            initial={{ opacity: 0, y: 30 }}
            animate={{ opacity: 1, y: 0 }}
            transition={{ duration: 0.8, delay: 1.3 }}
            className="flex flex-col sm:flex-row gap-4 justify-center"
          >
            <Link href="#contact">
              <Button size="lg" className="bg-gradient-to-r from-blue-600 to-purple-600 hover:opacity-90 text-lg px-8 shadow-lg shadow-blue-600/25">
                Get Investment Deck
                <ArrowRight className="ml-2 h-5 w-5" />
              </Button>
            </Link>
            <Link href="/dashboard">
              <Button size="lg" variant="outline" className="text-lg px-8">
                Launch App
              </Button>
            </Link>
          </motion.div>
        </div>

        <motion.div
          initial={{ opacity: 0 }}
          animate={{ opacity: 1 }}
          transition={{ duration: 1, delay: 1.5 }}
          className="absolute bottom-8 left-1/2 transform -translate-x-1/2"
        >
          <motion.div
            animate={{ y: [0, 10, 0] }}
            transition={{ duration: 2, repeat: Infinity, ease: "easeInOut" }}
            className="w-6 h-10 border-2 border-gray-300 rounded-full flex justify-center pt-2"
          >
            <motion.div
              animate={{ opacity: [1, 0, 1], y: [0, 8, 0] }}
              transition={{ duration: 2, repeat: Infinity, ease: "easeInOut" }}
              className="w-1 h-2 bg-gray-400 rounded-full"
            />
          </motion.div>
        </motion.div>
      </section>

      {/* Performance Section */}
      <section className="py-24 bg-gray-900">
        <div className="max-w-6xl mx-auto px-6">
          <FadeIn className="text-center mb-16">
            <h2 className="text-4xl font-black text-white mb-4">Real Results, Real Data</h2>
            <p className="text-gray-400 text-lg max-w-2xl mx-auto">
              Multi-asset backtest using live CoinGecko price data. CHAOS beats HODL on every single asset.
            </p>
          </FadeIn>

          <FadeIn delay={0.2}>
            <Card className="bg-gray-800 border-gray-700 overflow-hidden">
              <CardContent className="p-0">
                <div className="overflow-x-auto">
                  <table className="w-full">
                    <thead>
                      <tr className="border-b border-gray-700">
                        <th className="text-left py-4 px-4 text-gray-400 font-medium">Asset</th>
                        <th className="text-right py-4 px-4 text-gray-400 font-medium">CHAOS Return</th>
                        <th className="text-right py-4 px-4 text-gray-400 font-medium">HODL Return</th>
                        <th className="text-right py-4 px-4 text-gray-400 font-medium">Edge</th>
                        <th className="text-right py-4 px-4 text-gray-400 font-medium hidden md:table-cell">CHAOS Max DD</th>
                        <th className="text-right py-4 px-4 text-gray-400 font-medium hidden md:table-cell">HODL Max DD</th>
                      </tr>
                    </thead>
                    <tbody>
                      {performanceData.map((row, index) => (
                        <motion.tr
                          key={row.asset}
                          initial={{ opacity: 0, x: -30 }}
                          whileInView={{ opacity: 1, x: 0 }}
                          viewport={{ once: true }}
                          transition={{ duration: 0.5, delay: index * 0.1 }}
                          className="border-b border-gray-700/50 hover:bg-gray-700/30 transition-colors"
                        >
                          <td className="py-4 px-4 text-white font-semibold">{row.asset}</td>
                          <td className={`py-4 px-4 text-right font-bold ${row.chaos >= 0 ? 'text-emerald-400' : 'text-rose-400'}`}>
                            {row.chaos >= 0 ? '+' : ''}{row.chaos}%
                          </td>
                          <td className={`py-4 px-4 text-right font-bold ${row.hodl >= 0 ? 'text-emerald-400' : 'text-rose-400'}`}>
                            {row.hodl >= 0 ? '+' : ''}{row.hodl}%
                          </td>
                          <td className="py-4 px-4 text-right font-bold text-emerald-400">
                            +{row.edge}%
                          </td>
                          <td className="py-4 px-4 text-right text-gray-400 hidden md:table-cell">{row.chaosDD}%</td>
                          <td className="py-4 px-4 text-right text-gray-400 hidden md:table-cell">{row.hodlDD}%</td>
                        </motion.tr>
                      ))}
                    </tbody>
                  </table>
                </div>
              </CardContent>
            </Card>
          </FadeIn>
        </div>
      </section>

      {/* Mathematical Foundation */}
      <section className="py-24 bg-white">
        <div className="max-w-6xl mx-auto px-6">
          <FadeIn className="text-center mb-16">
            <h2 className="text-4xl font-black text-gray-900 mb-4">Mathematical Foundation</h2>
            <p className="text-gray-600 text-lg max-w-2xl mx-auto">
              Four theorems formally verified in Lean 4. Zero unproven assumptions.
            </p>
          </FadeIn>

          <StaggerContainer staggerDelay={0.15} className="grid md:grid-cols-2 gap-6">
            {theorems.map((theorem) => (
              <StaggerItem key={theorem.num}>
                <motion.div
                  whileHover={{ y: -4 }}
                  transition={{ duration: 0.2 }}
                >
                  <Card className="bg-gradient-to-br from-gray-50 to-white border-gray-100 shadow-lg h-full">
                    <CardContent className="p-8">
                      <div className="flex items-center gap-4 mb-4">
                        <div className="w-12 h-12 bg-blue-100 rounded-xl flex items-center justify-center">
                          <theorem.icon className="w-6 h-6 text-blue-600" />
                        </div>
                        <span className="px-3 py-1 bg-emerald-100 text-emerald-700 text-xs font-bold rounded-full">
                          Proved
                        </span>
                      </div>
                      <h3 className="text-xl font-bold text-gray-900 mb-2">{theorem.name}</h3>
                      <p className="text-gray-600">{theorem.result}</p>
                    </CardContent>
                  </Card>
                </motion.div>
              </StaggerItem>
            ))}
          </StaggerContainer>
        </div>
      </section>

      {/* Tokenomics */}
      <section className="py-24 bg-gradient-to-br from-blue-600 to-purple-700">
        <div className="max-w-6xl mx-auto px-6">
          <FadeIn className="text-center mb-16">
            <h2 className="text-4xl font-black text-white mb-4">Tokenomics</h2>
            <p className="text-blue-100 text-lg max-w-2xl mx-auto">
              100M fixed supply. 90% community-owned. No inflation.
            </p>
          </FadeIn>

          <FadeIn delay={0.2}>
            <Card className="bg-white/10 backdrop-blur-sm border-white/20">
              <CardContent className="p-8 md:p-12">
                {/* Token Distribution Bar */}
                <div className="mb-12">
                  <div className="h-12 md:h-16 rounded-xl overflow-hidden flex mb-4">
                    <motion.div
                      initial={{ width: 0 }}
                      whileInView={{ width: '60%' }}
                      viewport={{ once: true }}
                      transition={{ duration: 1.2, ease: 'easeOut' }}
                      className="bg-blue-400 flex items-center justify-center text-white font-bold text-sm md:text-base"
                    >
                      60% ISPO
                    </motion.div>
                    <motion.div
                      initial={{ width: 0 }}
                      whileInView={{ width: '30%' }}
                      viewport={{ once: true }}
                      transition={{ duration: 1.2, ease: 'easeOut', delay: 0.2 }}
                      className="bg-emerald-400 flex items-center justify-center text-white font-bold text-sm md:text-base"
                    >
                      30% LBP
                    </motion.div>
                    <motion.div
                      initial={{ width: 0 }}
                      whileInView={{ width: '5%' }}
                      viewport={{ once: true }}
                      transition={{ duration: 1.2, ease: 'easeOut', delay: 0.4 }}
                      className="bg-amber-400 flex items-center justify-center text-white font-bold text-xs md:text-sm"
                    >
                      5%
                    </motion.div>
                    <motion.div
                      initial={{ width: 0 }}
                      whileInView={{ width: '3%' }}
                      viewport={{ once: true }}
                      transition={{ duration: 1.2, ease: 'easeOut', delay: 0.6 }}
                      className="bg-gray-400 flex items-center justify-center text-white font-bold text-xs"
                    >
                      3%
                    </motion.div>
                    <motion.div
                      initial={{ width: 0 }}
                      whileInView={{ width: '2%' }}
                      viewport={{ once: true }}
                      transition={{ duration: 1.2, ease: 'easeOut', delay: 0.8 }}
                      className="bg-gray-300 flex items-center justify-center text-gray-700 font-bold text-xs"
                    >
                      2%
                    </motion.div>
                  </div>
                  <div className="flex flex-wrap gap-4 justify-center text-sm">
                    <div className="flex items-center gap-2">
                      <div className="w-3 h-3 bg-blue-400 rounded"></div>
                      <span className="text-white">60% Community ISPO</span>
                    </div>
                    <div className="flex items-center gap-2">
                      <div className="w-3 h-3 bg-emerald-400 rounded"></div>
                      <span className="text-white">30% Fair Launch (LBP)</span>
                    </div>
                    <div className="flex items-center gap-2">
                      <div className="w-3 h-3 bg-amber-400 rounded"></div>
                      <span className="text-white">5% Team</span>
                    </div>
                    <div className="flex items-center gap-2">
                      <div className="w-3 h-3 bg-gray-400 rounded"></div>
                      <span className="text-white">3% Treasury</span>
                    </div>
                    <div className="flex items-center gap-2">
                      <div className="w-3 h-3 bg-gray-300 rounded"></div>
                      <span className="text-white">2% Liquidity</span>
                    </div>
                  </div>
                </div>

                {/* Revenue Model */}
                <div className="grid md:grid-cols-3 gap-6">
                  <div className="bg-white/10 backdrop-blur rounded-2xl p-6 text-center">
                    <div className="text-4xl font-black text-white mb-2">2%</div>
                    <div className="text-blue-100">Annual Management Fee</div>
                  </div>
                  <div className="bg-white/10 backdrop-blur rounded-2xl p-6 text-center">
                    <div className="text-4xl font-black text-white mb-2">20%</div>
                    <div className="text-blue-100">Performance Fee</div>
                  </div>
                  <div className="bg-white/10 backdrop-blur rounded-2xl p-6 text-center">
                    <div className="text-4xl font-black text-emerald-300 mb-2">70%</div>
                    <div className="text-blue-100">To CHAOS Stakers</div>
                  </div>
                </div>
              </CardContent>
            </Card>
          </FadeIn>
        </div>
      </section>

      {/* Governance */}
      <section className="py-24 bg-gradient-to-br from-emerald-50 to-white">
        <div className="max-w-6xl mx-auto px-6">
          <FadeIn className="text-center mb-16">
            <h2 className="text-4xl font-black text-gray-900 mb-4">Decentralized Governance</h2>
            <p className="text-gray-600 text-lg max-w-2xl mx-auto">
              CHAOS token holders govern the protocol. Vote on strategy parameters, treasury allocation, and system upgrades.
            </p>
          </FadeIn>

          <StaggerContainer staggerDelay={0.15} className="grid md:grid-cols-3 gap-8">
            <StaggerItem>
              <motion.div whileHover={{ y: -4 }}>
                <Card className="bg-white border-emerald-100 shadow-lg h-full">
                  <CardContent className="p-8">
                    <div className="w-14 h-14 bg-emerald-100 rounded-xl flex items-center justify-center mb-6">
                      <Vote className="w-7 h-7 text-emerald-600" />
                    </div>
                    <h3 className="text-xl font-bold text-gray-900 mb-3">Voting Power</h3>
                    <p className="text-gray-600 mb-4">
                      1 CHAOS = 1 Vote. Stake your tokens to increase voting power by 50%.
                    </p>
                    <div className="text-3xl font-black text-emerald-600">85K+</div>
                    <div className="text-sm text-gray-500">Active voters</div>
                  </CardContent>
                </Card>
              </motion.div>
            </StaggerItem>

            <StaggerItem>
              <motion.div whileHover={{ y: -4 }}>
                <Card className="bg-white border-blue-100 shadow-lg h-full">
                  <CardContent className="p-8">
                    <div className="w-14 h-14 bg-blue-100 rounded-xl flex items-center justify-center mb-6">
                      <Shield className="w-7 h-7 text-blue-600" />
                    </div>
                    <h3 className="text-xl font-bold text-gray-900 mb-3">Parameter Control</h3>
                    <p className="text-gray-600 mb-4">
                      Vote on rebalancing thresholds, allocation targets, and fee structures.
                    </p>
                    <div className="text-3xl font-black text-blue-600">24</div>
                    <div className="text-sm text-gray-500">Proposals executed</div>
                  </CardContent>
                </Card>
              </motion.div>
            </StaggerItem>

            <StaggerItem>
              <motion.div whileHover={{ y: -4 }}>
                <Card className="bg-white border-purple-100 shadow-lg h-full">
                  <CardContent className="p-8">
                    <div className="w-14 h-14 bg-purple-100 rounded-xl flex items-center justify-center mb-6">
                      <Users className="w-7 h-7 text-purple-600" />
                    </div>
                    <h3 className="text-xl font-bold text-gray-900 mb-3">Treasury Governance</h3>
                    <p className="text-gray-600 mb-4">
                      Community controls $2.8M treasury. Vote on investments and allocations.
                    </p>
                    <div className="text-3xl font-black text-purple-600">$2.8M</div>
                    <div className="text-sm text-gray-500">Under governance</div>
                  </CardContent>
                </Card>
              </motion.div>
            </StaggerItem>
          </StaggerContainer>

          <FadeIn delay={0.4} className="mt-12 text-center">
            <Link href="/governance">
              <Button size="lg" className="bg-gradient-to-r from-blue-600 to-purple-600 hover:opacity-90 text-lg px-8 shadow-lg shadow-blue-600/25">
                <Vote className="mr-2 h-5 w-5" />
                View Governance Portal
                <ArrowRight className="ml-2 h-5 w-5" />
              </Button>
            </Link>
          </FadeIn>
        </div>
      </section>

      {/* Risk Assessment */}
      <section className="py-24 bg-gray-50">
        <div className="max-w-6xl mx-auto px-6">
          <FadeIn className="text-center mb-16">
            <h2 className="text-4xl font-black text-gray-900 mb-4">Risk Assessment</h2>
            <p className="text-gray-600 text-lg max-w-2xl mx-auto">
              Full transparency on risks and mitigations.
            </p>
          </FadeIn>

          <div className="grid md:grid-cols-2 gap-12">
            {/* Risk Waterfall */}
            <FadeIn delay={0.2}>
              <Card>
                <CardHeader>
                  <CardTitle>Expected Return Breakdown</CardTitle>
                </CardHeader>
                <CardContent>
                  <div className="space-y-4">
                    <div>
                      <div className="flex justify-between mb-2">
                        <span className="text-gray-600">Rebalancing Alpha</span>
                        <span className="font-bold text-emerald-600">+7.7%</span>
                      </div>
                      <motion.div
                        initial={{ width: 0 }}
                        whileInView={{ width: '77%' }}
                        viewport={{ once: true }}
                        transition={{ duration: 0.8, delay: 0.3 }}
                        className="h-4 bg-emerald-500 rounded-full"
                      />
                    </div>
                    <div>
                      <div className="flex justify-between mb-2">
                        <span className="text-gray-600">LP Fee Income</span>
                        <span className="font-bold text-emerald-600">+4.0%</span>
                      </div>
                      <motion.div
                        initial={{ width: 0 }}
                        whileInView={{ width: '40%' }}
                        viewport={{ once: true }}
                        transition={{ duration: 0.8, delay: 0.5 }}
                        className="h-4 bg-emerald-400 rounded-full"
                      />
                    </div>
                    <div>
                      <div className="flex justify-between mb-2">
                        <span className="text-gray-600">Risk-Adj. Cost</span>
                        <span className="font-bold text-rose-500">-10.0%</span>
                      </div>
                      <motion.div
                        initial={{ width: 0 }}
                        whileInView={{ width: '100%' }}
                        viewport={{ once: true }}
                        transition={{ duration: 0.8, delay: 0.7 }}
                        className="h-4 bg-rose-500 rounded-full"
                      />
                    </div>
                    <div className="pt-4 border-t-2 border-gray-200">
                      <div className="flex justify-between mb-2">
                        <span className="font-bold text-gray-900">NET EXPECTED</span>
                        <span className="font-bold text-blue-600">+1.7%</span>
                      </div>
                      <motion.div
                        initial={{ width: 0 }}
                        whileInView={{ width: '17%' }}
                        viewport={{ once: true }}
                        transition={{ duration: 0.8, delay: 0.9 }}
                        className="h-6 bg-blue-600 rounded-full"
                      />
                    </div>
                  </div>
                </CardContent>
              </Card>
            </FadeIn>

            {/* Risk List */}
            <FadeIn delay={0.4}>
              <div className="space-y-4">
                <h3 className="text-xl font-bold text-gray-900 mb-6">Top Risks & Mitigations</h3>
                {[
                  { risk: 'Regulatory action', weight: '40%', mitigation: 'Offshore entity, progressive decentralization' },
                  { risk: 'Bull underperformance', weight: '35%', mitigation: 'By design; disclosed upfront' },
                  { risk: 'Smart contract bugs', weight: '15%', mitigation: 'Multiple audits, formal verification, TVL caps' },
                  { risk: 'Oracle failure', weight: '10%', mitigation: '4-source consensus, circuit breakers' },
                ].map((item, index) => (
                  <motion.div
                    key={item.risk}
                    initial={{ opacity: 0, x: 30 }}
                    whileInView={{ opacity: 1, x: 0 }}
                    viewport={{ once: true }}
                    transition={{ duration: 0.5, delay: 0.5 + index * 0.1 }}
                  >
                    <Card>
                      <CardContent className="p-4">
                        <div className="flex justify-between items-start mb-2">
                          <span className="font-semibold text-gray-900">{item.risk}</span>
                          <span className="text-sm text-gray-500">{item.weight}</span>
                        </div>
                        <p className="text-sm text-gray-600">{item.mitigation}</p>
                      </CardContent>
                    </Card>
                  </motion.div>
                ))}
              </div>
            </FadeIn>
          </div>
        </div>
      </section>

      {/* Roadmap */}
      <section className="py-24 bg-white">
        <div className="max-w-6xl mx-auto px-6">
          <FadeIn className="text-center mb-16">
            <h2 className="text-4xl font-black text-gray-900 mb-4">Roadmap & Budget</h2>
            <p className="text-gray-600 text-lg max-w-2xl mx-auto">
              12-month journey from testnet to scale.
            </p>
          </FadeIn>

          <FadeIn delay={0.2}>
            <div className="relative">
              {/* Timeline Bar */}
              <div className="hidden md:block h-4 bg-gray-100 rounded-full overflow-hidden mb-12">
                <motion.div
                  initial={{ width: 0 }}
                  whileInView={{ width: '100%' }}
                  viewport={{ once: true }}
                  transition={{ duration: 2, ease: 'easeOut' }}
                  className="h-full bg-gradient-to-r from-blue-500 via-emerald-500 to-amber-500"
                />
              </div>

              {/* Timeline Items */}
              <div className="grid md:grid-cols-3 gap-8">
                {[
                  { phase: 'Phase 1', title: 'MVP', months: 'Months 1-3', budget: '$330K', items: ['Testnet deployment', 'Security audit', '100+ beta testers'], bgColor: 'bg-blue-100', textColor: 'text-blue-700', priceColor: 'text-blue-600' },
                  { phase: 'Phase 2', title: 'Launch', months: 'Months 4-6', budget: '$490K', items: ['Mainnet launch', 'ISPO begins', '$5-10M TVL target'], bgColor: 'bg-emerald-100', textColor: 'text-emerald-700', priceColor: 'text-emerald-600' },
                  { phase: 'Phase 3', title: 'Scale', months: 'Months 7-12', budget: '$1.1M', items: ['LBP token launch', 'ML signal layer', 'Mobile app, full DAO'], bgColor: 'bg-amber-100', textColor: 'text-amber-700', priceColor: 'text-amber-600' },
                ].map((phase, index) => (
                  <motion.div
                    key={phase.phase}
                    initial={{ opacity: 0, y: 30 }}
                    whileInView={{ opacity: 1, y: 0 }}
                    viewport={{ once: true }}
                    transition={{ duration: 0.5, delay: 0.3 + index * 0.2 }}
                    className="text-center"
                  >
                    <div className={`inline-block px-4 py-2 rounded-full ${phase.bgColor} ${phase.textColor} font-bold text-sm mb-4`}>
                      {phase.phase}
                    </div>
                    <h3 className="text-2xl font-bold text-gray-900 mb-2">{phase.title}</h3>
                    <p className="text-gray-500 mb-2">{phase.months}</p>
                    <p className={`text-3xl font-black ${phase.priceColor} mb-4`}>{phase.budget}</p>
                    <ul className="space-y-2 text-gray-600">
                      {phase.items.map((item) => (
                        <li key={item}>{item}</li>
                      ))}
                    </ul>
                  </motion.div>
                ))}
              </div>
            </div>
          </FadeIn>
        </div>
      </section>

      {/* Contact Section */}
      <section id="contact" className="py-24 bg-gray-900">
        <div className="max-w-4xl mx-auto px-6">
          <FadeIn className="text-center mb-12">
            <h2 className="text-4xl font-black text-white mb-4">Get In Touch</h2>
            <p className="text-gray-400 text-lg">
              Interested in participating? Let&apos;s talk.
            </p>
          </FadeIn>

          <FadeIn delay={0.2}>
            <Card>
              <CardContent className="p-8 md:p-12">
                <div className="grid md:grid-cols-2 gap-8 mb-8">
                  <div>
                    <h3 className="text-xl font-bold text-gray-900 mb-4">Links</h3>
                    <div className="space-y-3">
                      <p className="text-gray-600">
                        <span className="font-semibold">Web:</span>{' '}
                        <a href="https://chaosprotocol.io" className="text-blue-600 hover:underline">chaosprotocol.io</a>
                      </p>
                      <p className="text-gray-600">
                        <span className="font-semibold">GitHub:</span>{' '}
                        <a href="https://github.com/Algiras/chaos-protocol" className="text-blue-600 hover:underline">github.com/Algiras/chaos-protocol</a>
                      </p>
                    </div>
                  </div>
                  <div>
                    <h3 className="text-xl font-bold text-gray-900 mb-4">Resources</h3>
                    <div className="space-y-3">
                      <Card className="hover:bg-gray-50 cursor-pointer transition-colors">
                        <CardContent className="p-4">
                          <div className="font-semibold text-gray-900">Investor Brief</div>
                          <div className="text-sm text-gray-500">7-page overview</div>
                        </CardContent>
                      </Card>
                      <Card className="hover:bg-gray-50 cursor-pointer transition-colors">
                        <CardContent className="p-4">
                          <div className="font-semibold text-gray-900">Full Whitepaper</div>
                          <div className="text-sm text-gray-500">80+ pages with proofs</div>
                        </CardContent>
                      </Card>
                    </div>
                  </div>
                </div>

                <div className="text-center pt-8 border-t border-gray-200">
                  <Link href="/coming-soon">
                    <Button size="lg" className="bg-gradient-to-r from-blue-600 to-purple-600 hover:opacity-90 text-lg px-8 shadow-lg shadow-blue-600/25">
                      Launch App
                      <ArrowRight className="ml-2 h-5 w-5" />
                    </Button>
                  </Link>
                </div>
              </CardContent>
            </Card>
          </FadeIn>
        </div>
      </section>
    </>
  );
}
