import Link from 'next/link';

export function Footer() {
  return (
    <footer className="bg-gray-950 py-12">
      <div className="max-w-6xl mx-auto px-6">
        <div className="grid md:grid-cols-3 gap-8 mb-8">
          <div>
            <h3 className="text-xl font-black text-white mb-4">CHAOS</h3>
            <p className="text-gray-400 text-sm">
              Antifragile treasury management protocol on Cardano.
            </p>
          </div>
          <div>
            <h4 className="font-semibold text-white mb-4">Learn</h4>
            <ul className="space-y-2 text-sm">
              <li>
                <Link href="/research" className="text-gray-400 hover:text-blue-400 transition-colors">
                  Research &amp; Publications
                </Link>
              </li>
              <li>
                <Link href="/how-it-works" className="text-gray-400 hover:text-blue-400 transition-colors">
                  How It Works
                </Link>
              </li>
              <li>
                <Link href="/investors" className="text-gray-400 hover:text-blue-400 transition-colors">
                  For Investors
                </Link>
              </li>
            </ul>
          </div>
          <div>
            <h4 className="font-semibold text-white mb-4">Resources</h4>
            <ul className="space-y-2 text-sm">
              <li>
                <a href="https://github.com/Algiras/chaos-protocol" className="text-gray-400 hover:text-blue-400 transition-colors">
                  GitHub
                </a>
              </li>
              <li>
                <a href="/whitepaper/chaos-whitepaper.pdf" className="text-gray-400 hover:text-blue-400 transition-colors">
                  Whitepaper
                </a>
              </li>
            </ul>
          </div>
        </div>
        <div className="border-t border-gray-800 pt-8 text-center">
          <p className="text-gray-500 text-sm">
            &copy; 2026 CHAOS Protocol. All rights reserved.
          </p>
        </div>
      </div>
    </footer>
  );
}
