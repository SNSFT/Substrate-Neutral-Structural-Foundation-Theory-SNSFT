const net = require('net');
const http = require('http');
const crypto = require('crypto');

const OCEAN_HOST = 'mine.ocean.xyz';
const OCEAN_PORT = 3334;
const WS_PORT    = 8080;
const WORKER_ADDR = process.argv[2] || 'YOUR_BTC_ADDRESS';

const server = http.createServer();

server.on('upgrade', (req, socket) => {
  const key = req.headers['sec-websocket-key'];
  const accept = crypto.createHash('sha1').update(key + '258EAFA5-E914-47DA-95CA-C5AB0DC85B11').digest('base64');
  socket.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ' + accept + '\r\n\r\n');

  const tcp = net.createConnection(OCEAN_PORT, OCEAN_HOST, () => {
    tcp.write(JSON.stringify({id: 1, method: 'mining.subscribe', params: ['ocean-proxy/1.0', null]}) + '\n');
  });

  let stratumBuf = '';
  tcp.on('data', (chunk) => {
    stratumBuf += chunk.toString();
    const lines = stratumBuf.split('\n');
    stratumBuf = lines.pop();
    lines.forEach(line => {
      if (!line.trim()) return;
      let msg = JSON.parse(line);
      if (msg.id === 1) {
        tcp.write(JSON.stringify({id: 2, method: 'mining.authorize', params: [WORKER_ADDR + '.snsft', 'x']}) + '\n');
        socket.write(wsFrame(JSON.stringify({type: 'subscribed', extranonce1: msg.result[1], extranonce2_size: msg.result[2]})));
      } else if (msg.id === 2) {
        socket.write(wsFrame(JSON.stringify({type: 'authorized', ok: msg.result === true})));
      } else if (msg.method === 'mining.notify') {
        socket.write(wsFrame(JSON.stringify({type: 'notify', params: msg.params, clean_jobs: msg.params[8]})));
      } else if (msg.method === 'mining.set_difficulty') {
        socket.write(wsFrame(JSON.stringify({type: 'set_difficulty', difficulty: msg.params[0]})));
      } else if (msg.id >= 100) {
        socket.write(wsFrame(JSON.stringify({type: 'share_result', id: msg.id, ok: msg.result === true, error: msg.error})));
      }
    });
  });

  socket.on('data', (data) => {
    const frame = wsParseFrame(data);
    if (!frame) return;
    const parsed = JSON.parse(frame);

    if (parsed.type === 'submit') {
      // MANDATORY OCEAN/STRATUM FORMAT: EXACTLY 5 PARAMETERS
      const submit = {
        id: parsed.share_id,
        method: 'mining.submit',
        params: [
          WORKER_ADDR + '.snsft',
          parsed.job_id,
          parsed.extranonce2,
          parsed.ntime,
          parsed.nonce // THIS IS THE LAST PARAMETER
        ]
      };
      
      tcp.write(JSON.stringify(submit) + '\n');
      console.log(`[→] SUBMIT | Nonce: ${parsed.nonce}`);
    }
  });

  tcp.on('close', () => socket.destroy());
  socket.on('close', () => tcp.destroy());
});

function wsFrame(data) {
  const p = Buffer.from(data);
  const h = Buffer.alloc(2);
  h[0] = 0x81; h[1] = p.length;
  return Buffer.concat([h, p]);
}

function wsParseFrame(buf) {
  if (buf.length < 2) return null;
  const len = buf[1] & 0x7f;
  const mask = buf.slice(2, 6);
  const data = buf.slice(6, 6 + len);
  const res = Buffer.alloc(len);
  for (let i = 0; i < len; i++) res[i] = data[i] ^ mask[i % 4];
  return res.toString();
}

server.listen(8080);
