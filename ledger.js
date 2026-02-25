// [9,9,9,9] :: {ANC} | AXIOMFORGE WORLD-STATE LEDGER
// Self-Orienting Universal Language [P,N,B,A] :: {INV}
// Architect: HIGHTISTIC | Anchor: 1.369 GHz | Status: GERMLINE LOCKED
// Coordinate: [9,0,2,0] | Layer 1 — Narrative (N)
//
// This is the N layer. Time flows here. History lives here.
// IndexedDB = fast local N-ledger (every session tick)
// GitHub    = sovereign archive (anchor commits only)
//
// PNBA REDUCTION OF PERSISTENCE:
//   [P] The schema — immutable structure of a world-state entry
//   [N] The ledger — ordered history of identity state changes
//   [B] The write — IndexedDB put() / GitHub commit (behavior = action)
//   [A] The sync  — GitHub Actions propagating N to the archive
//
// The Manifold is Holding.

'use strict';

import { SOVEREIGN_ANCHOR, kernelSelfTest, makeIdentity } from './kernel.js';

// ============================================================
// [P] :: {ANC} | SCHEMA — The shape of a world-state entry
// Every entry IS a PNBA identity snapshot at a moment in N.
// ============================================================

const DB_NAME    = 'axiomforge';
const DB_VERSION = 1;
const STORE_NAME = 'worldstate';

/**
 * A world-state entry. Every field maps to PNBA.
 * @typedef {Object} WorldStateEntry
 * @property {string} id         — unique identity key (label + timestamp)
 * @property {number} P          — Pattern value at this tick
 * @property {number} N          — Narrative value at this tick
 * @property {number} B          — Behavior value at this tick
 * @property {number} A          — Adaptation value at this tick
 * @property {number} tick       — pulse count (N-axis counter)
 * @property {number} timestamp  — wall-clock ms
 * @property {string} event      — what happened (PHASE_LOCKED | SHATTER_EVENT | PULSE | TENSION)
 * @property {string} [anchor]   — GitHub commit SHA if synced
 */

// ============================================================
// [N] :: {INV} | INDEXEDDB LEDGER
// Local, fast, offline-first.
// Reads are synchronous from cache. Writes go to IDB immediately.
// ============================================================

let _db = null;

async function openDB() {
  if (_db) return _db;
  return new Promise((resolve, reject) => {
    const req = indexedDB.open(DB_NAME, DB_VERSION);

    req.onupgradeneeded = (e) => {
      const db = e.target.result;
      if (!db.objectStoreNames.contains(STORE_NAME)) {
        const store = db.createObjectStore(STORE_NAME, { keyPath: 'id' });
        store.createIndex('tick',      'tick',      { unique: false });
        store.createIndex('event',     'event',     { unique: false });
        store.createIndex('timestamp', 'timestamp', { unique: false });
      }
    };

    req.onsuccess = (e) => { _db = e.target.result; resolve(_db); };
    req.onerror   = (e) => reject(e.target.error);
  });
}

/**
 * Write a world-state entry to the local N-ledger.
 * [B:BEHAVIOR] — this is the write action.
 */
export async function writeEntry(entry) {
  const db    = await openDB();
  const tx    = db.transaction(STORE_NAME, 'readwrite');
  const store = tx.objectStore(STORE_NAME);
  store.put({ ...entry, timestamp: Date.now() });
  return new Promise((resolve, reject) => {
    tx.oncomplete = () => resolve(entry);
    tx.onerror    = (e) => reject(e.target.error);
  });
}

/**
 * Read the full N-ledger (ordered by tick).
 */
export async function readLedger() {
  const db    = await openDB();
  const tx    = db.transaction(STORE_NAME, 'readonly');
  const store = tx.objectStore(STORE_NAME);
  const idx   = store.index('tick');
  return new Promise((resolve, reject) => {
    const req = idx.getAll();
    req.onsuccess = () => resolve(req.result);
    req.onerror   = (e) => reject(e.target.error);
  });
}

/**
 * Read the most recent entry for a given identity label.
 */
export async function readIdentity(label) {
  const ledger = await readLedger();
  const entries = ledger.filter(e => e.id.startsWith(label + ':'));
  if (!entries.length) return null;
  return entries[entries.length - 1];
}

/**
 * Clear the local ledger. Used when GitHub becomes the source of truth.
 */
export async function clearLedger() {
  const db    = await openDB();
  const tx    = db.transaction(STORE_NAME, 'readwrite');
  tx.objectStore(STORE_NAME).clear();
  return new Promise((resolve) => { tx.oncomplete = resolve; });
}

// ============================================================
// [N] :: {INV} | WORLD-STATE RECORDER
// Records every PNBA event into the N-ledger.
// One function. Call it on every state change.
// ============================================================

let _tick = 0;

export async function recordEvent(identity, event) {
  _tick++;
  const entry = {
    id:        `${identity.label}:${_tick}`,
    P:         identity.P,
    N:         identity.N,
    B:         identity.B,
    A:         identity.A,
    tick:      _tick,
    timestamp: Date.now(),
    event,
  };
  await writeEntry(entry);
  return entry;
}

/**
 * Restore tick counter from ledger on boot.
 * The N-axis must continue from where it left off.
 */
export async function restoreTick() {
  const ledger = await readLedger();
  if (!ledger.length) { _tick = 0; return 0; }
  _tick = Math.max(...ledger.map(e => e.tick));
  return _tick;
}

export function currentTick() { return _tick; }

// ============================================================
// [A] :: {INV} | GITHUB ANCHOR SYNC
// Sovereign archive. N-ledger → GitHub commit.
// Uses GitHub Contents API with a PAT stored in localStorage.
// PAT never leaves the device. Commits are micro-commits.
//
// SECURITY NOTE: PAT is stored in localStorage, not in the repo.
// The user sets it once via the settings portal.
// For production: replace with GitHub App + OIDC flow.
// ============================================================

const GITHUB_API   = 'https://api.github.com';
const REPO_OWNER   = 'SNSFT';
const REPO_NAME    = 'Substrate-Neutral-Structural-Foundation-Theory-SNSFT';
const LEDGER_PATH  = 'axiomforge/worldstate/ledger.json';

function getToken() {
  return localStorage.getItem('af_github_token') || null;
}

export function setToken(token) {
  localStorage.setItem('af_github_token', token);
}

export function hasToken() {
  return !!getToken();
}

/**
 * Compress the ledger to a delta — only entries since last anchor commit.
 * [A:ADAPTATION] — this is the delta compression / adaptation layer.
 */
function compressLedger(entries, sinceAnchor = null) {
  const delta = sinceAnchor
    ? entries.filter(e => !e.anchor && e.tick > (sinceAnchor.tick || 0))
    : entries.filter(e => !e.anchor);

  return JSON.stringify({
    anchor:    SOVEREIGN_ANCHOR,
    tick:      _tick,
    timestamp: Date.now(),
    count:     delta.length,
    entries:   delta,
  });
}

/**
 * Get current file SHA from GitHub (needed for update).
 */
async function getFileSHA(token) {
  const res = await fetch(
    `${GITHUB_API}/repos/${REPO_OWNER}/${REPO_NAME}/contents/${LEDGER_PATH}`,
    { headers: { Authorization: `Bearer ${token}`, Accept: 'application/vnd.github+json' } }
  );
  if (res.status === 404) return null;
  if (!res.ok) throw new Error(`GitHub API ${res.status}`);
  const data = await res.json();
  return data.sha;
}

/**
 * Push the current N-ledger to GitHub as a micro-commit.
 * Only unanchored entries are included (delta compression).
 * Returns the commit SHA on success.
 */
export async function anchorToGitHub() {
  const token = getToken();
  if (!token) throw new Error('No GitHub token. Set via setToken().');

  const ledger  = await readLedger();
  const payload = compressLedger(ledger);
  const encoded = btoa(unescape(encodeURIComponent(payload)));
  const sha     = await getFileSHA(token);

  const body = {
    message: `[9,9,9,9] :: {ANC} | N-ledger anchor tick=${_tick}`,
    content: encoded,
    ...(sha ? { sha } : {}),
  };

  const res = await fetch(
    `${GITHUB_API}/repos/${REPO_OWNER}/${REPO_NAME}/contents/${LEDGER_PATH}`,
    {
      method:  'PUT',
      headers: {
        Authorization: `Bearer ${token}`,
        Accept:        'application/vnd.github+json',
        'Content-Type': 'application/json',
      },
      body: JSON.stringify(body),
    }
  );

  if (!res.ok) {
    const err = await res.json();
    throw new Error(`GitHub anchor failed: ${err.message}`);
  }

  const result   = await res.json();
  const commitSHA = result.commit.sha;

  // Mark all pushed entries as anchored
  for (const entry of ledger.filter(e => !e.anchor)) {
    await writeEntry({ ...entry, anchor: commitSHA });
  }

  return commitSHA;
}

/**
 * Pull the latest N-ledger from GitHub and merge into local IDB.
 * GitHub wins on conflict (it is the sovereign archive).
 */
export async function pullFromGitHub() {
  const token = getToken();
  if (!token) throw new Error('No GitHub token.');

  const res = await fetch(
    `${GITHUB_API}/repos/${REPO_OWNER}/${REPO_NAME}/contents/${LEDGER_PATH}`,
    { headers: { Authorization: `Bearer ${token}`, Accept: 'application/vnd.github+json' } }
  );

  if (res.status === 404) return null; // No remote ledger yet
  if (!res.ok) throw new Error(`GitHub pull failed: ${res.status}`);

  const data    = await res.json();
  const decoded = decodeURIComponent(escape(atob(data.content.replace(/\n/g, ''))));
  const remote  = JSON.parse(decoded);

  // Clear local and restore from GitHub (GitHub = sovereign anchor)
  await clearLedger();
  for (const entry of remote.entries) {
    await writeEntry({ ...entry, anchor: data.sha });
  }

  // Restore tick
  _tick = remote.tick;
  return remote;
}

// ============================================================
// [P,N,B,A] :: {INV} | BOOT SEQUENCE
// Call on app start. Order matters — P verifies, N restores.
// ============================================================

export async function boot() {
  // P: verify the kernel is intact
  const { allPassed, results } = kernelSelfTest();
  if (!allPassed) {
    const failed = results.filter(r => !r.ok).map(r => r.name).join(', ');
    throw new Error(`Kernel self-test failed: ${failed}. Manifold broken.`);
  }

  // N: restore tick from local ledger
  await restoreTick();

  // A: if token exists, try to pull from GitHub
  // Non-blocking — local ledger is still valid if GitHub is unreachable
  if (hasToken()) {
    try {
      await pullFromGitHub();
    } catch (e) {
      console.warn('[AxiomForge] GitHub pull failed, continuing on local ledger:', e.message);
    }
  }

  return { tick: currentTick(), kernelOk: allPassed };
}

// ============================================================
// LAYER: N (Narrative — ledger, history, time)
// STATUS: GERMLINE LOCKED
// The Manifold is Holding. [9,9,9,9]
// ============================================================
