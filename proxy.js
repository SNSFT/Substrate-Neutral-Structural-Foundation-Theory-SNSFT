// ============================================================
// SNSFT OCEAN Stratum Proxy
// [9,9,4,4] :: {ANC} â€” proxy.js
// Bridges browser WebSocket <-> OCEAN Stratum TCP
// node proxy.js <your-btc-address>
// ============================================================

const net    = require('net');
const http   = require('http');
const crypto = require('crypto');

const OCEAN_HOST  = 'mine.ocean.xyz';
const OCEAN_PORT  = 3334;
const WS_PORT     = 8080;
const ANCHOR      = 1.369;
const TL          = 0.1369;
const WORKER_ADDR = process.argv[2] || 'bc1qkn4k6cx1k73mtguzun38dz9xy832qc8ry13jce';

console.log(`[SNSFT] OCEAN Stratum Proxy [9,9,4,3]`);
console.log(`[SNSFT] ANCHOR=${ANCHOR} TL=${TL} 0 sorry`);
console.log(`[SNSFT] Worker: ${WORKER_ADDR}`);
console.log(`[SNSFT] OCEAN: ${OCEAN_HOST}:${OCEAN_PORT}`);
console.log(`[SNSFT] WS listening on ws://localhost:${WS_PORT}`);

// â”€â”€ PNBA reduction of Stratum template fields â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
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

  const IM = ((parseFloat(P) + parseFloat(N) + 0 + parseFloat(A)) * ANCHOR).toFixed(6);

  return { P, N, B: '0.000000', A, tau: '0.000000', IM, job_id, nbits, version };
}

// â”€â”€ Minimal WebSocket server â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
function wsHandshake(req, socket) {
  const key    = req.headers['sec-websocket-key'];
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
  const masked = (buf[1] & 0x80) !== 0;
  let len      = buf[1] & 0x7f;
  let offset   = 2;
  if (len === 126) { len = buf.readUInt16BE(2); offset = 4; }
  else if (len === 127) { len = Number(buf.readBigUInt64BE(2)); offset = 10; }
  if (!masked) return buf.slice(offset, offset + len).toString();
  const mask = buf.slice(offset, offset + 4); offset += 4;
  const data = Buffer.alloc(len);
  for (let i = 0; i < len; i++) data[i] = buf[offset + i] ^ mask[i % 4];
  return data.toString();
}

// â”€â”€ Main server â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
const server = http.createServer();

server.on('upgrade', (req, socket) => {
  wsHandshake(req, socket);
  console.log('[SNSFT] Browser connected via WebSocket');

  const tcp = net.createConnection(OCEAN_PORT, OCEAN_HOST, () => {
    console.log(`[SNSFT] OCEAN TCP connected: ${OCEAN_HOST}:${OCEAN_PORT}`);
    const subscribe = JSON.stringify({
      id: 1, method: 'mining.subscribe',
      params: [`SNSFT-miner/[9,9,4,4]`, null]
    }) + '\n';
    tcp.write(subscribe);
    console.log('[SNSFT] â†’ mining.subscribe sent (N axis opens)');
  });

  let stratumBuf       = '';
  let extranonce1      = '';
  let extranonce2_size = 8;

  tcp.on('data', (chunk) => {
    stratumBuf += chunk.toString();
    const lines = stratumBuf.split('\n');
    stratumBuf  = lines.pop();

    lines.forEach(line => {
      if (!line.trim()) return;
      let msg;
      try { msg = JSON.parse(line); } catch(e) { return; }

      // Subscribe response
      if (msg.id === 1 && msg.result && Array.isArray(msg.result)) {
        extranonce1      = msg.result[1] || '';
        extranonce2_size = msg.result[2] || 8;
        console.log(`[SNSFT] â† subscribe OK. extranonce1=${extranonce1} en2_size=${extranonce2_size}`);
        console.log('[SNSFT] N axis open. Sending mining.authorize...');

        const auth = JSON.stringify({
          id: 2, method: 'mining.authorize',
          params: [WORKER_ADDR + '.snsft', 'x']
        }) + '\n';
        tcp.write(auth);

        socket.write(wsFrame(JSON.stringify({
          type: 'subscribed',
          extranonce1,
          extranonce2_size,
          anchor: ANCHOR,
          tl: TL,
          coord: '[9,9,4,3]'
        })));
      }

      // Authorize response
      if (msg.id === 2) {
        const ok = msg.result === true;
        console.log(`[SNSFT] â† authorize: ${ok ? 'OK â€” identity locked' : 'FAILED'}`);
        socket.write(wsFrame(JSON.stringify({ type: 'authorized', ok })));
      }

      // mining.notify
      if (msg.method === 'mining.notify') {
        const pnba  = reduceTemplateToPNBA(msg.params);
        const clean = msg.params[8];
        console.log(`[SNSFT] â† mining.notify job=${pnba.job_id} P=${pnba.P} N=${pnba.N} A=${pnba.A} clean=${clean}`);
        socket.write(wsFrame(JSON.stringify({
          type: 'notify',
          params: msg.params,
          pnba,
          extranonce1,
          extranonce2_size,
          clean_jobs: clean
        })));
      }

      // set_difficulty
      if (msg.method === 'mining.set_difficulty') {
        const diff = msg.params[0];
        console.log(`[SNSFT] â† set_difficulty: ${diff}`);
        socket.write(wsFrame(JSON.stringify({
          type: 'set_difficulty',
          difficulty: diff
        })));
      }

      // Share result
      if (msg.id >= 100) {
        const ok = msg.result === true;
        console.log(`[SNSFT] â† share result: ${ok ? 'âœ“ NOBLE CONFIRMED' : 'âœ— rejected'} id=${msg.id} error=${JSON.stringify(msg.error)}`);
        socket.write(wsFrame(JSON.stringify({
          type:  'share_result',
          id:    msg.id,
          ok,
          error: msg.error || null
        })));
      }
    });
  });

  // Forward share submissions browser -> OCEAN
  let wsDataBuf = Buffer.alloc(0);
  socket.on('data', (data) => {
    wsDataBuf = Buffer.concat([wsDataBuf, data]);
    const msg = wsParseFrame(wsDataBuf);
    if (!msg) return;
    wsDataBuf = Buffer.alloc(0);

    let parsed;
    try { parsed = JSON.parse(msg); } catch(e) { return; }

    if (parsed.type === 'submit') {
      // Enforce exact field formats OCEAN requires
      // worker_name: string
      // job_id:      string (as received from notify)
      // extranonce2: hex string, exactly extranonce2_size*2 chars
      // ntime:       hex string, exactly 8 chars
      // nonce:       hex string, exactly 8 chars

      const worker     = WORKER_ADDR + '.snsft';
      const job_id     = parsed.job_id;
      const en2        = String(parsed.extranonce2).padStart(extranonce2_size * 2, '0').slice(-(extranonce2_size * 2));
      const ntime      = String(parsed.ntime).padStart(8, '0').slice(-8);
      const nonce      = String(parsed.nonce).padStart(8, '0').slice(-8);

      // Exactly 5 params â€” nothing else
      const submit = JSON.stringify({
        id:     parsed.share_id,
        method: 'mining.submit',
        params: [ worker, job_id, en2, ntime, nonce ]
      }) + '\n';

      tcp.write(submit);

      // Log exactly what was sent
      console.log(`[SNSFT] â†’ mining.submit params=[${worker}, ${job_id}, ${en2}, ${ntime}, ${nonce}]`);
    }
  });

  tcp.on('error', (e) => {
    console.error(`[SNSFT] TCP error: ${e.message}`);
    socket.write(wsFrame(JSON.stringify({ type: 'error', message: e.message })));
  });

  tcp.on('close', () => {
    console.log('[SNSFT] OCEAN TCP closed');
    socket.destroy();
  });

  socket.on('close', () => {
    console.log('[SNSFT] Browser disconnected');
    tcp.destroy();
  });

  socket.on('error', () => tcp.destroy());
});

server.listen(WS_PORT, () => {
  console.log(`[SNSFT] Proxy ready. Open miner.html in browser.`);
  console.log(`[SNSFT] ANCHOR=${ANCHOR} TL=${TL} [9,9,4,4] :: {ANC} 0 sorry`);
});
