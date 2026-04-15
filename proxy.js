// ============================================================
// SNSFT OCEAN Stratum Proxy - FIXED
// [9,9,4,4] :: {ANC} — proxy.js
// Bridges browser WebSocket <-> OCEAN Stratum TCP
// ============================================================

const net = require('net');
const http = require('http');
const crypto = require('crypto');

const OCEAN_HOST = 'mine.ocean.xyz';
const OCEAN_PORT = 3334;
const WS_PORT    = 8080;
const ANCHOR     = 1.369;
const TL         = 0.1369;

const WORKER_ADDR = process.argv[2] || 'YOUR_BTC_ADDRESS_HERE';

console.log(`[SNSFT] OCEAN Stratum Proxy [9,9,4,3]`);
console.log(`[SNSFT] ANCHOR=${ANCHOR} TL=${TL}`);
console.log(`[SNSFT] Worker: ${WORKER_ADDR}`);
console.log(`[SNSFT] OCEAN: ${OCEAN_HOST}:${OCEAN_PORT}`);
console.log(`[SNSFT] WS listening on ws://localhost:${WS_PORT}`);

// ── PNBA reduction of Stratum template fields ──────────────
function reduceTemplateToPNBA(params) {
  const [job_id, prevhash, coinb1, coinb2, merkle_branches,
         version, nbits, ntime] = params;

  const merkle_depth = (merkle_branches || []).length;
  const version_num  = parseInt(version, 16) || 1;
  const P = (version_num * 0.001 + merkle_depth * 0.325 +
             parseInt(prevhash.slice(0,8), 16) * 1e-9).toFixed(6);

  const ntime_num = parseInt(ntime, 16) || Date.now()/1000;
  const N = (ntime_num * 1e-9 * ANCHOR).toFixed(6);

  const nbits_num = parseInt(nbits, 16) || 0x1d00ffff;
  const exp  = (nbits_num >> 24) & 0xff;
  const mant = nbits_num & 0x7fffff;
  const A    = (mant * Math.pow(256, exp - 3) * 1e-50 * ANCHOR * 10).toFixed(6);

  const tau  = 0;
  const IM   = ((parseFloat(P) + parseFloat(N) + 0 + parseFloat(A)) * ANCHOR).toFixed(6);

  return { P, N, B: '0.000000', A, tau: tau.toFixed(6), IM, job_id, nbits, version };
}

// ── WebSocket Utilities ─────────────────────────────────────
function wsHandshake(req, socket) {
  const key = req.headers['sec-websocket-key'];
  const accept = crypto
    .createHash('sha1')
    .update(key + '258EAFA5-E914-47DA-95CA-C5AB0DC85B11')
    .digest('base64');
  socket.write(
    'HTTP/1.1 101 Switching Protocols\r\n' +
    'Upgrade: websocket\r\n' +
    'Connection: Upgrade\r\n' +
    `Sec-WebSocket-Accept: ${accept}\r\n\r\n`
  );
}

function wsFrame(data) {
  const payload = Buffer.from(typeof data === 'string' ? data : JSON.stringify(data));
  const len = payload.length;
  let header;
  if (len < 126) {
    header = Buffer.alloc(2);
    header[0] = 0x81; header[1] = len;
  } else if (len < 65536) {
    header = Buffer.alloc(4);
    header[0] = 0x81; header[1] = 126;
    header.writeUInt16BE(len, 2);
  } else {
    header = Buffer.alloc(10);
    header[0] = 0x81; header[1] = 127;
    header.writeBigUInt64BE(BigInt(len), 2);
  }
  return Buffer.concat([header, payload]);
}

function wsParseFrame(buf) {
  if (buf.length < 2) return null;
  const masked  = (buf[1] & 0x80) !== 0;
  let len       = buf[1] & 0x7f;
  let offset    = 2;
  if (len === 126) { len = buf.readUInt16BE(2); offset = 4; }
  else if (len === 127) { len = Number(buf.readBigUInt64BE(2)); offset = 10; }
  if (buf.length < offset + (masked ? 4 : 0) + len) return null;
  if (!masked) return buf.slice(offset, offset + len).toString();
  const mask = buf.slice(offset, offset + 4); offset += 4;
  const data = Buffer.alloc(len);
  for (let i = 0; i < len; i++) data[i] = buf[offset + i] ^ mask[i % 4];
  return data.toString();
}

// ── Server Core ─────────────────────────────────────────────
const server = http.createServer();

server.on('upgrade', (req, socket) => {
  wsHandshake(req, socket);
  console.log('[SNSFT] Browser connected');

  const tcp = net.createConnection(OCEAN_PORT, OCEAN_HOST, () => {
    console.log(`[SNSFT] OCEAN Connected`);
    tcp.write(JSON.stringify({
      id: 1, method: 'mining.subscribe',
      params: [`SNSFT-miner/[9,9,4,4]`, null]
    }) + '\n');
  });

  let stratumBuf = '';
  let extranonce1 = '';
  let extranonce2_size = 4;

  tcp.on('data', (chunk) => {
    stratumBuf += chunk.toString();
    const lines = stratumBuf.split('\n');
    stratumBuf = lines.pop();

    lines.forEach(line => {
      if (!line.trim()) return;
      let msg;
      try { msg = JSON.parse(line); } catch(e) { return; }

      if (msg.id === 1 && msg.result) {
        extranonce1      = msg.result[1] || '';
        extranonce2_size = msg.result[2] || 4;
        tcp.write(JSON.stringify({
          id: 2, method: 'mining.authorize',
          params: [WORKER_ADDR + '.snsft', 'x']
        }) + '\n');
        socket.write(wsFrame({ type: 'subscribed', extranonce1, extranonce2_size }));
      }

      if (msg.id === 2) {
        socket.write(wsFrame({ type: 'authorized', ok: msg.result === true }));
      }

      if (msg.method === 'mining.notify') {
        const pnba = reduceTemplateToPNBA(msg.params);
        socket.write(wsFrame({ type: 'notify', params: msg.params, pnba, extranonce1, extranonce2_size, clean_jobs: msg.params[8] }));
      }

      if (msg.method === 'mining.set_difficulty') {
        socket.write(wsFrame({ type: 'set_difficulty', difficulty: msg.params[0] }));
      }

      if (msg.id >= 100) {
        socket.write(wsFrame({ type: 'share_result', id: msg.id, ok: msg.result === true, error: msg.error || null }));
      }
    });
  });

  let wsDataBuf = Buffer.alloc(0);
  socket.on('data', (data) => {
    wsDataBuf = Buffer.concat([wsDataBuf, data]);
    const frame = wsParseFrame(wsDataBuf);
    if (!frame) return;
    wsDataBuf = Buffer.alloc(0);

    let parsed;
    try { parsed = JSON.parse(frame); } catch(e) { return; }

    if (parsed.type === 'submit') {
      // FIX: Convert the incoming tau (raw array) to hex and include it as the 6th param
      const tauHex = Buffer.from(parsed.tau).toString('hex');
      
      const submit = JSON.stringify({
        id: parsed.share_id,
        method: 'mining.submit',
        params: [
          WORKER_ADDR + '.snsft',
          parsed.job_id,
          parsed.extranonce2,
          parsed.ntime,
          parsed.nonce,
          tauHex // Parameter 6: The actual hash proof
        ]
      }) + '\n';
      
      tcp.write(submit);
      console.log(`[SNSFT] → SUBMIT: Nonce=${parsed.nonce} Hash=${tauHex.slice(0,8)}...`);
    }
  });

  tcp.on('error', (e) => socket.write(wsFrame({ type: 'error', message: e.message })));
  tcp.on('close', () => socket.destroy());
  socket.on('close', () => tcp.destroy());
});

server.listen(WS_PORT);
