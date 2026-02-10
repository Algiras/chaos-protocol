/* eslint-disable react/no-unescaped-entities */
import Head from 'next/head';
import { FadeIn } from '@/components/animations';
import { AlertTriangle } from 'lucide-react';

export default function RiskDisclosure() {
  return (
    <>
      <Head>
        <title>Risk Disclosure | CHAOS Protocol</title>
        <meta name="description" content="Risk Disclosure for CHAOS Protocol - Understand the risks before participating" />
      </Head>

      <div className="min-h-screen py-24">
        <div className="max-w-4xl mx-auto px-6">
          <FadeIn>
            <div className="flex items-center gap-4 mb-4">
              <AlertTriangle className="w-12 h-12 text-amber-500" />
              <h1 className="text-4xl md:text-5xl font-black text-white">Risk Disclosure</h1>
            </div>
            <p className="text-gray-400 mb-8">Last Updated: February 10, 2026</p>
            <div className="bg-amber-500/10 border border-amber-500/30 rounded-lg p-6 mb-12">
              <p className="text-amber-200 font-semibold">
                ⚠️ IMPORTANT: Please read this Risk Disclosure carefully before using CHAOS Protocol. Participation involves significant financial risks that may result in complete loss of funds.
              </p>
            </div>
          </FadeIn>

          <FadeIn delay={0.1}>
            <div className="prose prose-invert prose-lg max-w-none">
              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">1. General Investment Risks</h2>
                <h3 className="text-xl font-semibold text-white mb-3">1.1 Loss of Principal</h3>
                <p className="text-gray-300 mb-4">
                  You may lose some or all of your invested capital. Cryptocurrency markets are highly volatile, and the Protocol&apos;s strategies do not guarantee protection against losses.
                </p>

                <h3 className="text-xl font-semibold text-white mb-3">1.2 No Guaranteed Returns</h3>
                <p className="text-gray-300 mb-4">
                  Historical performance, backtests, and projections do not guarantee future results. Market conditions change, and past success does not predict future outcomes.
                </p>

                <h3 className="text-xl font-semibold text-white mb-3">1.3 Market Volatility</h3>
                <p className="text-gray-300 mb-4">
                  Cryptocurrency prices can fluctuate dramatically in short periods. While the Protocol aims to profit from volatility, extreme market movements may result in significant losses.
                </p>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">2. Protocol-Specific Risks</h2>
                <h3 className="text-xl font-semibold text-white mb-3">2.1 Smart Contract Risk</h3>
                <p className="text-gray-300 mb-4">
                  Despite formal verification and audits, smart contracts may contain undiscovered vulnerabilities that could be exploited, resulting in loss of funds.
                </p>

                <h3 className="text-xl font-semibold text-white mb-3">2.2 Oracle Risk</h3>
                <p className="text-gray-300 mb-4">
                  The Protocol relies on price oracles. Oracle failures, manipulation, or incorrect data could trigger unintended rebalancing or losses.
                </p>

                <h3 className="text-xl font-semibold text-white mb-3">2.3 Rebalancing Strategy Risk</h3>
                <p className="text-gray-300 mb-4">
                  The automated rebalancing strategy may underperform in certain market conditions, particularly during strong bull markets or trending markets.
                </p>

                <h3 className="text-xl font-semibold text-white mb-3">2.4 Liquidity Risk</h3>
                <p className="text-gray-300 mb-4">
                  During periods of high volatility or low market liquidity, you may not be able to exit positions at desired prices. Withdrawals may be delayed or subject to slippage.
                </p>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">3. Blockchain and Technical Risks</h2>
                <h3 className="text-xl font-semibold text-white mb-3">3.1 Network Congestion</h3>
                <p className="text-gray-300 mb-4">
                  Cardano network congestion may delay transactions, causing missed rebalancing opportunities or inability to exit positions promptly.
                </p>

                <h3 className="text-xl font-semibold text-white mb-3">3.2 Private Key Security</h3>
                <p className="text-gray-300 mb-4">
                  You are solely responsible for securing your private keys. Loss of private keys results in permanent, irreversible loss of funds. We cannot recover lost keys.
                </p>

                <h3 className="text-xl font-semibold text-white mb-3">3.3 Protocol Upgrades</h3>
                <p className="text-gray-300 mb-4">
                  Protocol upgrades or changes to underlying blockchain infrastructure may introduce new risks or temporarily disrupt services.
                </p>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">4. Regulatory and Legal Risks</h2>
                <h3 className="text-xl font-semibold text-white mb-3">4.1 Regulatory Uncertainty</h3>
                <p className="text-gray-300 mb-4">
                  Cryptocurrency regulations are evolving globally. Future regulations may restrict or prohibit your ability to use the Protocol, potentially affecting asset values or accessibility.
                </p>

                <h3 className="text-xl font-semibold text-white mb-3">4.2 Tax Implications</h3>
                <p className="text-gray-300 mb-4">
                  Cryptocurrency transactions may have tax consequences in your jurisdiction. You are responsible for understanding and complying with all applicable tax laws.
                </p>

                <h3 className="text-xl font-semibold text-white mb-3">4.3 Jurisdictional Restrictions</h3>
                <p className="text-gray-300 mb-4">
                  The Protocol may not be available in all jurisdictions. Use may be prohibited or restricted based on your location.
                </p>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">5. Governance and Operational Risks</h2>
                <h3 className="text-xl font-semibold text-white mb-3">5.1 Governance Decisions</h3>
                <p className="text-gray-300 mb-4">
                  Token holders make governance decisions. You may disagree with decisions that affect protocol parameters, fees, or strategy.
                </p>

                <h3 className="text-xl font-semibold text-white mb-3">5.2 Team and Development Risk</h3>
                <p className="text-gray-300 mb-4">
                  While aiming for progressive decentralization, early-stage risks include dependence on core team members and development decisions.
                </p>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">6. Token-Specific Risks</h2>
                <h3 className="text-xl font-semibold text-white mb-3">6.1 Token Price Volatility</h3>
                <p className="text-gray-300 mb-4">
                  CHAOS token price may fluctuate significantly and may not correlate with protocol performance or underlying asset values.
                </p>

                <h3 className="text-xl font-semibold text-white mb-3">6.2 Liquidity Risk</h3>
                <p className="text-gray-300 mb-4">
                  CHAOS tokens may have limited liquidity, especially during launch phases. You may not be able to sell tokens at desired prices or timing.
                </p>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">7. Third-Party Risks</h2>
                <h3 className="text-xl font-semibold text-white mb-3">7.1 DEX and LP Risks</h3>
                <p className="text-gray-300 mb-4">
                  The Protocol interacts with third-party DEXs and liquidity pools. These platforms have their own risks, including smart contract vulnerabilities and impermanent loss.
                </p>

                <h3 className="text-xl font-semibold text-white mb-3">7.2 Wallet Provider Risks</h3>
                <p className="text-gray-300 mb-4">
                  Third-party wallet providers may experience outages, security breaches, or discontinuation of services.
                </p>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">8. Risk Management Recommendations</h2>
                <p className="text-gray-300 mb-4">
                  To mitigate risks, we recommend:
                </p>
                <ul className="list-disc list-inside text-gray-300 mb-4 space-y-2">
                  <li><strong className="text-white">Only invest what you can afford to lose</strong> - Never invest money needed for living expenses</li>
                  <li><strong className="text-white">Diversify your portfolio</strong> - Don&apos;t allocate all assets to a single protocol or strategy</li>
                  <li><strong className="text-white">Start small</strong> - Test with smaller amounts before committing significant capital</li>
                  <li><strong className="text-white">Secure your keys</strong> - Use hardware wallets and backup recovery phrases securely</li>
                  <li><strong className="text-white">Do your own research</strong> - Understand how the Protocol works before participating</li>
                  <li><strong className="text-white">Monitor regularly</strong> - Keep track of your positions and protocol updates</li>
                  <li><strong className="text-white">Consult professionals</strong> - Seek advice from qualified financial, legal, and tax advisors</li>
                </ul>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">9. Acknowledgment</h2>
                <p className="text-gray-300 mb-4">
                  By using CHAOS Protocol, you acknowledge that:
                </p>
                <ul className="list-disc list-inside text-gray-300 mb-4 space-y-2">
                  <li>You have read and understood this Risk Disclosure</li>
                  <li>You accept all risks associated with using the Protocol</li>
                  <li>You are solely responsible for your investment decisions</li>
                  <li>No guarantees or promises have been made regarding returns or outcomes</li>
                  <li>You may lose all of your invested capital</li>
                </ul>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">10. Contact</h2>
                <p className="text-gray-300 mb-4">
                  For questions about risks or the Protocol, please contact us through our GitHub repository:
                </p>
                <p className="text-gray-300">
                  <a href="https://github.com/Algiras/chaos-protocol" className="text-blue-400 hover:underline" target="_blank" rel="noopener noreferrer">
                    github.com/Algiras/chaos-protocol
                  </a>
                </p>
              </section>

              <div className="bg-rose-500/10 border border-rose-500/30 rounded-lg p-6">
                <p className="text-rose-200 font-semibold">
                  ⚠️ FINAL WARNING: Cryptocurrency and DeFi protocols involve substantial risk of loss. Never invest more than you can afford to lose. This disclosure does not cover all possible risks. Additional risks may exist that are not currently known or anticipated.
                </p>
              </div>
            </div>
          </FadeIn>
        </div>
      </div>
    </>
  );
}
