/** @type {import('next').NextConfig} */
module.exports = {
  reactStrictMode: true,
  trailingSlash: true, // GitHub Pages compatibility
  images: { unoptimized: true }, // Required for static export
  transpilePackages: ['@chaos/shared'],
  // Exclude app-only pages from marketing build
  exportPathMap: async function (
    defaultPathMap,
    { dev, dir, outDir, distDir, buildId }
  ) {
    const pathMap = {};
    // Only include marketing pages
    for (const path in defaultPathMap) {
      if (!path.startsWith('/dashboard') && !path.startsWith('/governance') && !path.startsWith('/api')) {
        pathMap[path] = defaultPathMap[path];
      }
    }
    return pathMap;
  },
};
