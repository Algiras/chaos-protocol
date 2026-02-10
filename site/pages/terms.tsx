/* eslint-disable react/no-unescaped-entities */
import Head from 'next/head';
import { FadeIn } from '@/components/animations';

export default function Terms() {
  return (
    <>
      <Head>
        <title>Terms of Service | CHAOS Protocol</title>
        <meta name="description" content="Terms of Service for CHAOS Protocol - Antifragile Treasury Management on Cardano" />
      </Head>

      <div className="min-h-screen py-24">
        <div className="max-w-4xl mx-auto px-6">
          <FadeIn>
            <h1 className="text-4xl md:text-5xl font-black text-white mb-4">Terms of Service</h1>
            <p className="text-gray-400 mb-12">Last Updated: February 10, 2026</p>
          </FadeIn>

          <FadeIn delay={0.1}>
            <div className="prose prose-invert prose-lg max-w-none">
              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">1. Acceptance of Terms</h2>
                <p className="text-gray-300 mb-4">
                  By accessing or using CHAOS Protocol (&quot;the Protocol&quot;), you agree to be bound by these Terms of Service (&quot;Terms&quot;). If you do not agree to these Terms, do not use the Protocol.
                </p>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">2. Description of Service</h2>
                <p className="text-gray-300 mb-4">
                  CHAOS Protocol is a decentralized treasury management protocol built on the Cardano blockchain. The Protocol uses algorithmic rebalancing strategies to manage portfolio allocations.
                </p>
                <p className="text-gray-300 mb-4">
                  <strong className="text-white">The Protocol is provided &quot;as is&quot; without warranties of any kind.</strong> We do not guarantee profits, returns, or specific outcomes.
                </p>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">3. Eligibility</h2>
                <p className="text-gray-300 mb-4">
                  You must be at least 18 years old to use the Protocol. By using the Protocol, you represent and warrant that:
                </p>
                <ul className="list-disc list-inside text-gray-300 mb-4 space-y-2">
                  <li>You are of legal age in your jurisdiction</li>
                  <li>You have the legal capacity to enter into these Terms</li>
                  <li>Your use complies with all applicable laws and regulations</li>
                  <li>You are not located in a jurisdiction where use of the Protocol is prohibited</li>
                </ul>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">4. Wallet and Private Keys</h2>
                <p className="text-gray-300 mb-4">
                  You are solely responsible for:
                </p>
                <ul className="list-disc list-inside text-gray-300 mb-4 space-y-2">
                  <li>Maintaining the security of your wallet and private keys</li>
                  <li>All transactions initiated from your wallet</li>
                  <li>Backing up your wallet and recovery phrases</li>
                </ul>
                <p className="text-gray-300 mb-4">
                  <strong className="text-white">We cannot recover lost private keys or reverse transactions.</strong> Loss of private keys may result in permanent loss of funds.
                </p>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">5. Financial Risks</h2>
                <p className="text-gray-300 mb-4">
                  Use of the Protocol involves significant financial risks, including but not limited to:
                </p>
                <ul className="list-disc list-inside text-gray-300 mb-4 space-y-2">
                  <li>Loss of principal investment</li>
                  <li>Market volatility and price fluctuations</li>
                  <li>Smart contract vulnerabilities</li>
                  <li>Liquidity risks</li>
                  <li>Regulatory changes</li>
                </ul>
                <p className="text-gray-300 mb-4">
                  <strong className="text-white">Only invest what you can afford to lose.</strong> Past performance does not guarantee future results.
                </p>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">6. No Financial Advice</h2>
                <p className="text-gray-300 mb-4">
                  Nothing in the Protocol, website, or documentation constitutes financial, investment, legal, or tax advice. You should consult with qualified professionals before making any financial decisions.
                </p>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">7. Fees and Gas Costs</h2>
                <p className="text-gray-300 mb-4">
                  Use of the Protocol may incur:
                </p>
                <ul className="list-disc list-inside text-gray-300 mb-4 space-y-2">
                  <li>Protocol fees as specified in the documentation</li>
                  <li>Blockchain transaction fees (gas costs)</li>
                  <li>Liquidity provider fees</li>
                </ul>
                <p className="text-gray-300 mb-4">
                  You are responsible for all applicable fees. Fees are subject to change.
                </p>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">8. Prohibited Uses</h2>
                <p className="text-gray-300 mb-4">
                  You agree not to:
                </p>
                <ul className="list-disc list-inside text-gray-300 mb-4 space-y-2">
                  <li>Use the Protocol for any illegal purpose</li>
                  <li>Engage in market manipulation or wash trading</li>
                  <li>Attempt to exploit vulnerabilities or attack the Protocol</li>
                  <li>Use the Protocol to launder money or finance terrorism</li>
                  <li>Violate any applicable laws or regulations</li>
                </ul>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">9. Intellectual Property</h2>
                <p className="text-gray-300 mb-4">
                  The Protocol&apos;s open-source code is licensed under applicable open-source licenses. Trademarks, branding, and non-code content remain our property.
                </p>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">10. Limitation of Liability</h2>
                <p className="text-gray-300 mb-4">
                  To the maximum extent permitted by law:
                </p>
                <ul className="list-disc list-inside text-gray-300 mb-4 space-y-2">
                  <li>We are not liable for any losses, damages, or claims arising from your use of the Protocol</li>
                  <li>We do not guarantee the Protocol will be error-free or uninterrupted</li>
                  <li>Our total liability shall not exceed the fees you paid in the 12 months prior to the claim</li>
                </ul>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">11. Indemnification</h2>
                <p className="text-gray-300 mb-4">
                  You agree to indemnify and hold harmless CHAOS Protocol, its contributors, and affiliates from any claims, damages, or expenses arising from your use of the Protocol or violation of these Terms.
                </p>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">12. Dispute Resolution</h2>
                <p className="text-gray-300 mb-4">
                  Any disputes shall be resolved through binding arbitration in accordance with international arbitration rules. You waive the right to participate in class action lawsuits.
                </p>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">13. Modifications</h2>
                <p className="text-gray-300 mb-4">
                  We reserve the right to modify these Terms at any time. Changes will be posted with an updated date. Continued use constitutes acceptance of modified Terms.
                </p>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">14. Severability</h2>
                <p className="text-gray-300 mb-4">
                  If any provision of these Terms is found to be unenforceable, the remaining provisions shall remain in full force and effect.
                </p>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">15. Contact</h2>
                <p className="text-gray-300 mb-4">
                  For questions about these Terms, please contact us through our GitHub repository:
                </p>
                <p className="text-gray-300">
                  <a href="https://github.com/Algiras/chaos-protocol" className="text-blue-400 hover:underline" target="_blank" rel="noopener noreferrer">
                    github.com/Algiras/chaos-protocol
                  </a>
                </p>
              </section>
            </div>
          </FadeIn>
        </div>
      </div>
    </>
  );
}
