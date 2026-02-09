export type BuildTarget = 'marketing' | 'app';

export const BUILD_TARGET = (process.env.NEXT_PUBLIC_BUILD_TARGET as BuildTarget) || 'app';
export const isMarketing = BUILD_TARGET === 'marketing';
export const isApp = BUILD_TARGET === 'app';

export function walletEnabled(): boolean {
  return isApp;
}

export function apiEnabled(): boolean {
  return isApp;
}

export function getNavLinks() {
  if (isMarketing) {
    return [
      { href: '/', label: 'Home' },
      { href: '/research', label: 'Research & Publications' },
      { href: '/how-it-works', label: 'How It Works' },
    ];
  } else {
    return [
      { href: '/dashboard', label: 'Dashboard' },
      { href: '/governance', label: 'Governance' },
    ];
  }
}
