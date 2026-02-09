import { ReactNode } from 'react';
import dynamic from 'next/dynamic';
import { MarketingHeader } from './MarketingHeader';
import { Footer } from './Footer';
import { PageTransition } from '@/components/animations';
import { isMarketing } from '@/lib/build-target';

// Dynamically import AppHeader to avoid SSR issues with wallet hooks
const AppHeaderDynamic = dynamic(() => import('./AppHeader').then(mod => mod.AppHeader), {
  ssr: false,
  loading: () => <div className="h-[73px]" /> // Placeholder with same height
});

interface LayoutProps {
  children: ReactNode;
  /** Hide footer on specific pages if needed */
  hideFooter?: boolean;
}

export function Layout({ children, hideFooter = false }: LayoutProps) {
  // Select the appropriate header based on build target
  const Header = isMarketing ? MarketingHeader : AppHeaderDynamic;

  return (
    <div className="min-h-screen flex flex-col">
      <Header />
      <PageTransition>
        <main className="flex-1">
          {children}
        </main>
      </PageTransition>
      {!hideFooter && <Footer />}
    </div>
  );
}
