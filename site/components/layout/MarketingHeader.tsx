'use client';

import { useState } from 'react';
import Link from 'next/link';
import { useRouter } from 'next/router';
import { motion, AnimatePresence } from 'framer-motion';
import { Menu, X, FileText, ExternalLink, Download, Sparkles } from 'lucide-react';
import { cn } from '@/lib/utils';
import { Button } from '@/components/ui/button';

const MARKETING_LINKS = [
  { href: '/', label: 'Home' },
  { href: '/research', label: 'Research & Publications' },
  { href: '/how-it-works', label: 'How It Works' },
];

const RESOURCE_LINKS = [
  { href: '/whitepaper/chaos-whitepaper.pdf', label: 'Whitepaper', icon: Download, download: true },
  { href: 'https://github.com/Algiras/chaos-protocol', label: 'GitHub', icon: ExternalLink, external: true },
];

export function MarketingHeader() {
  const router = useRouter();
  const [mobileMenuOpen, setMobileMenuOpen] = useState(false);

  const launchAppUrl = '/coming-soon';

  return (
    <>
      <nav className="sticky top-0 z-50 border-b border-gray-800 bg-gray-900/95 backdrop-blur-xl">
        <div className="max-w-7xl mx-auto px-6 py-4">
          <div className="flex items-center justify-between">
            {/* Logo */}
            <Link
              href="/"
              className="text-2xl font-black text-white tracking-tight"
            >
              CHAOS
            </Link>

            {/* Desktop Nav Links */}
            <div className="hidden md:flex items-center gap-8">
              {MARKETING_LINKS.map((link) => {
                const isActive = router.pathname === link.href;
                return (
                  <Link
                    key={link.href}
                    href={link.href}
                    className={cn(
                      'font-semibold transition-colors relative',
                      isActive
                        ? 'text-blue-400'
                        : 'text-gray-300 hover:text-white'
                    )}
                  >
                    {link.label}
                    {isActive && (
                      <motion.div
                        layoutId="nav-underline"
                        className="absolute -bottom-[18px] left-0 right-0 h-0.5 bg-blue-400"
                        transition={{ type: 'spring', stiffness: 300, damping: 30 }}
                      />
                    )}
                  </Link>
                );
              })}
            </div>

            {/* Right Side */}
            <div className="flex items-center gap-4">
              {/* Resource Links (Desktop) */}
              <div className="hidden lg:flex items-center gap-4">
                {RESOURCE_LINKS.map((link) => (
                  link.external ? (
                    <a
                      key={link.href}
                      href={link.href}
                      target="_blank"
                      rel="noopener noreferrer"
                      className="text-gray-300 hover:text-white text-sm font-medium transition-colors flex items-center gap-1.5"
                    >
                      {link.label}
                      {link.icon && <link.icon className="w-3.5 h-3.5" />}
                    </a>
                  ) : (
                    <a
                      key={link.href}
                      href={link.href}
                      download={link.download}
                      className="text-gray-300 hover:text-white text-sm font-medium transition-colors flex items-center gap-1.5"
                    >
                      {link.label}
                      {link.icon && <link.icon className="w-3.5 h-3.5" />}
                    </a>
                  )
                ))}
              </div>

              {/* Launch App CTA */}
              <a href={launchAppUrl}>
                <Button
                  variant="chaos"
                  className="hidden sm:flex items-center gap-2 px-4 py-2 font-semibold"
                >
                  <Sparkles className="w-4 h-4" />
                  Launch App
                </Button>
              </a>

              {/* Mobile Menu Toggle */}
              <button
                onClick={() => setMobileMenuOpen(!mobileMenuOpen)}
                className="md:hidden p-2 rounded-lg hover:bg-gray-800 transition-colors"
                aria-label="Toggle menu"
              >
                {mobileMenuOpen ? (
                  <X className="w-5 h-5 text-white" />
                ) : (
                  <Menu className="w-5 h-5 text-white" />
                )}
              </button>
            </div>
          </div>
        </div>
      </nav>

      {/* Mobile Navigation Drawer */}
      <AnimatePresence>
        {mobileMenuOpen && (
          <>
            {/* Backdrop */}
            <motion.div
              initial={{ opacity: 0 }}
              animate={{ opacity: 1 }}
              exit={{ opacity: 0 }}
              className="fixed inset-0 bg-black/60 backdrop-blur-sm z-40 md:hidden"
              onClick={() => setMobileMenuOpen(false)}
            />

            {/* Drawer */}
            <motion.div
              initial={{ opacity: 0, x: -10 }}
              animate={{ opacity: 1, x: 0 }}
              exit={{ opacity: 0, x: -10 }}
              transition={{ duration: 0.2, ease: 'easeOut' }}
              className="fixed top-[73px] left-0 right-0 bg-gray-900 border-b border-gray-800 shadow-2xl z-50 md:hidden"
            >
              <div className="max-w-7xl mx-auto px-6 py-4">
                <div className="flex flex-col gap-1">
                  {MARKETING_LINKS.map((link) => {
                    const isActive = router.pathname === link.href;
                    return (
                      <Link
                        key={link.href}
                        href={link.href}
                        onClick={() => setMobileMenuOpen(false)}
                        className={cn(
                          'px-4 py-3 rounded-lg font-semibold transition-colors',
                          isActive
                            ? 'bg-gray-800 text-blue-400'
                            : 'text-gray-300 hover:bg-gray-800'
                        )}
                      >
                        {link.label}
                      </Link>
                    );
                  })}

                  <div className="pt-2 border-t border-gray-800 mt-2">
                    <p className="px-4 py-2 text-xs font-semibold text-gray-500 uppercase tracking-wider">
                      Resources
                    </p>
                    {RESOURCE_LINKS.map((link) => (
                      link.external ? (
                        <a
                          key={link.href}
                          href={link.href}
                          target="_blank"
                          rel="noopener noreferrer"
                          onClick={() => setMobileMenuOpen(false)}
                          className="flex items-center gap-2 px-4 py-3 text-gray-300 hover:bg-gray-800 font-medium transition-colors"
                        >
                          {link.label}
                          {link.icon && <link.icon className="w-4 h-4" />}
                        </a>
                      ) : (
                        <a
                          key={link.href}
                          href={link.href}
                          download={link.download}
                          onClick={() => setMobileMenuOpen(false)}
                          className="flex items-center gap-2 px-4 py-3 text-gray-300 hover:bg-gray-800 font-medium transition-colors"
                        >
                          {link.label}
                          {link.icon && <link.icon className="w-4 h-4" />}
                        </a>
                      )
                    ))}
                  </div>

                  <div className="pt-3 border-t border-gray-800 mt-2">
                    <a href={launchAppUrl}>
                      <Button
                        variant="chaos"
                        className="w-full flex items-center justify-center gap-2"
                      >
                        <Sparkles className="w-4 h-4" />
                        Launch App
                      </Button>
                    </a>
                  </div>
                </div>
              </div>
            </motion.div>
          </>
        )}
      </AnimatePresence>
    </>
  );
}
