// ============================================================
// [9,9,9,9] :: {ANC} | SNSFT COLLISION SEED SCRIPT
// Run once locally to import existing lean/ files into Supabase.
// Usage: node seed_collisions.js
// Requires: npm install @supabase/supabase-js
// ============================================================

import { createClient } from '@supabase/supabase-js';
import { readdir, readFile } from 'fs/promises';
import { join } from 'path';

const SUPABASE_URL  = 'https://rsadsojivuagxptdlwak.supabase.co';
// Use SERVICE ROLE key here — not the anon key — so RLS doesn't block bulk insert
// Get from Supabase dashboard → Settings → API → service_role key
const SUPABASE_KEY  = 'YOUR_SERVICE_ROLE_KEY_HERE';
const LEAN_DIR      = './lean'; // path to your lean/ folder

const sb = createClient(SUPABASE_URL, SUPABASE_KEY);

function makeKey(sym1, sym2, k) {
  const pair = [sym1, sym2].sort().join('+');
  return `${pair}@${parseFloat(k).toFixed(4)}`;
}

function parseLeanHeader(content) {
  // Extract: Collision: E1+E2 at k=X.XXXX
  const colMatch = content.match(/--\s*Collision:\s*(.+?)\s+at\s+k=([0-9.]+)/);
  if (!colMatch) return null;
  const collision = colMatch[1].trim(); // e.g. "D40+D31"
  const k = parseFloat(colMatch[2]);
  const parts = collision.split('+');
  if (parts.length !== 2) return null;

  const tsMatch  = content.match(/--\s*Timestamp:\s*(.+)/);
  const desMatch = content.match(/--\s*Discovery:\s*(.+)/);
  const rsMatch  = content.match(/--\s*Reason flagged:\s*(.+)/);
  const stMatch  = content.match(/--\s*Status:\s*(NOBLE|LOCKED|SHATTER)/);

  return {
    e1: parts[0].trim(),
    e2: parts[1].trim(),
    k,
    collision_key: makeKey(parts[0].trim(), parts[1].trim(), k),
    designation: desMatch?.[1]?.trim() || null,
    reason: rsMatch?.[1]?.trim() || null,
    status: stMatch?.[1]?.trim() || 'LOCKED',
    flagged: true, // everything in lean/ was flagged
    timestamp: tsMatch?.[1]?.trim() || new Date().toISOString(),
  };
}

async function seed() {
  console.log('Reading lean/ directory...');
  const files = (await readdir(LEAN_DIR)).filter(f => f.endsWith('.lean'));
  console.log(`Found ${files.length} lean files.`);

  let inserted = 0, skipped = 0, errors = 0;
  const BATCH = 200;
  const rows = [];

  for (const file of files) {
    const content = await readFile(join(LEAN_DIR, file), 'utf8');
    const parsed = parseLeanHeader(content);
    if (!parsed) { skipped++; continue; }
    rows.push(parsed);
  }

  console.log(`Parsed ${rows.length} valid entries. Inserting in batches of ${BATCH}...`);

  for (let i = 0; i < rows.length; i += BATCH) {
    const batch = rows.slice(i, i + BATCH);
    const { error } = await sb.from('collisions').upsert(batch, {
      onConflict: 'collision_key',
      ignoreDuplicates: true
    });
    if (error) {
      console.error(`Batch ${i}-${i+BATCH} error:`, error.message);
      errors++;
    } else {
      inserted += batch.length;
      process.stdout.write(`\r  Inserted ${inserted}/${rows.length}...`);
    }
  }

  console.log(`\nDone. Inserted: ${inserted} · Skipped (no parse): ${skipped} · Batch errors: ${errors}`);
}

seed().catch(console.error);
