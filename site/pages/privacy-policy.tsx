/* eslint-disable react/no-unescaped-entities */
import Head from 'next/head';
import { FadeIn } from '@/components/animations';

export default function PrivacyPolicy() {
  return (
    <>
      <Head>
        <title>Privacy Policy | CHAOS Protocol</title>
        <meta name="description" content="Privacy Policy for CHAOS Protocol - Antifragile Treasury Management on Cardano" />
      </Head>

      <div className="min-h-screen py-24">
        <div className="max-w-4xl mx-auto px-6">
          <FadeIn>
            <h1 className="text-4xl md:text-5xl font-black text-white mb-4">Privacy Policy</h1>
            <p className="text-gray-400 mb-12">Last Updated: February 10, 2026</p>
          </FadeIn>

          <FadeIn delay={0.1}>
            <div className="prose prose-invert prose-lg max-w-none">
              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">1. Introduction</h2>
                <p className="text-gray-300 mb-4">
                  CHAOS Protocol (&quot;we,&quot; &quot;us,&quot; or &quot;our&quot;) is committed to protecting your privacy. This Privacy Policy explains how we collect, use, disclose, and safeguard your information when you interact with our decentralized protocol and website.
                </p>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">2. Information We Collect</h2>
                <h3 className="text-xl font-semibold text-white mb-3">2.1 Blockchain Data</h3>
                <p className="text-gray-300 mb-4">
                  As a blockchain-based protocol, all transactions are recorded on the Cardano blockchain. This includes:
                </p>
                <ul className="list-disc list-inside text-gray-300 mb-4 space-y-2">
                  <li>Wallet addresses</li>
                  <li>Transaction amounts and timestamps</li>
                  <li>Smart contract interactions</li>
                </ul>
                <p className="text-gray-300 mb-4">
                  This information is publicly available and immutable by nature of blockchain technology.
                </p>

                <h3 className="text-xl font-semibold text-white mb-3">2.2 Website Usage Data</h3>
                <p className="text-gray-300 mb-4">
                  When you visit our website, we may collect:
                </p>
                <ul className="list-disc list-inside text-gray-300 mb-4 space-y-2">
                  <li>IP address and browser information</li>
                  <li>Pages visited and time spent</li>
                  <li>Referral sources</li>
                </ul>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">3. How We Use Information</h2>
                <p className="text-gray-300 mb-4">
                  We use collected information to:
                </p>
                <ul className="list-disc list-inside text-gray-300 mb-4 space-y-2">
                  <li>Provide and improve our protocol services</li>
                  <li>Analyze protocol performance and usage patterns</li>
                  <li>Detect and prevent fraud or security issues</li>
                  <li>Communicate important protocol updates</li>
                </ul>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">4. Data Sharing and Disclosure</h2>
                <p className="text-gray-300 mb-4">
                  We do not sell your personal information. We may share information:
                </p>
                <ul className="list-disc list-inside text-gray-300 mb-4 space-y-2">
                  <li>With service providers who assist in operating our website</li>
                  <li>When required by law or legal process</li>
                  <li>To protect our rights, privacy, safety, or property</li>
                </ul>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">5. Cookies and Tracking</h2>
                <p className="text-gray-300 mb-4">
                  We may use cookies and similar tracking technologies to improve your experience. You can control cookie preferences through your browser settings.
                </p>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">6. Data Security</h2>
                <p className="text-gray-300 mb-4">
                  We implement reasonable security measures to protect your information. However, no method of transmission over the internet is 100% secure. Use of blockchain wallets and custody of private keys remains your responsibility.
                </p>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">7. International Users</h2>
                <p className="text-gray-300 mb-4">
                  CHAOS Protocol operates globally. By using our services, you consent to the transfer of information to jurisdictions that may have different data protection laws than your country of residence.
                </p>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">8. Children&apos;s Privacy</h2>
                <p className="text-gray-300 mb-4">
                  Our services are not intended for individuals under 18 years of age. We do not knowingly collect personal information from children.
                </p>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">9. Changes to This Policy</h2>
                <p className="text-gray-300 mb-4">
                  We may update this Privacy Policy from time to time. Changes will be posted on this page with an updated revision date. Continued use of our services constitutes acceptance of the updated policy.
                </p>
              </section>

              <section className="mb-12">
                <h2 className="text-2xl font-bold text-white mb-4">10. Contact Us</h2>
                <p className="text-gray-300 mb-4">
                  For questions about this Privacy Policy, please contact us through our GitHub repository:
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
