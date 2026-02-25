const CACHE_NAME = 'axiom-forge-v1';
const ASSETS = [
  './',
  './axiomforge.html',
  './src/axiomforge.viewport.js',
  './src/axiomforge.sculpt.js',
  'https://fonts.googleapis.com/css2?family=Space+Mono&family=Syne:wght@800&display=swap'
];

self.addEventListener('install', (e) => {
  e.waitUntil(
    caches.open(CACHE_NAME).then(cache => cache.addAll(ASSETS))
  );
});

self.addEventListener('fetch', (e) => {
  e.respondWith(
    caches.match(e.request).then(res => res || fetch(e.request))
  );
});
