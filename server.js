const express = require('express');
const http = require('http');
const path = require('path');
const { Server } = require('socket.io');

const app = express();
const server = http.createServer(app);
const io = new Server(server);
app.use(express.static(path.join(__dirname, 'public')));

// ---------- constants ----------
const W = 2400, H = 2400;
const TICK = 30;
const DT = 1 / TICK;
const FUSE_COUNT = 6;
const RESTART_AFTER = 8; // seconds on win/lose screen
// appearance: hair style, hair color, skin tone, shirt style, shirt color, pants, shoes, flashlight
const LOOK_LIMITS = [9, 9, 5, 5, 12, 10, 8, 8];
function cleanLook(l) {
  if (!Array.isArray(l) || l.length !== LOOK_LIMITS.length) return LOOK_LIMITS.map(() => 0);
  return l.map((v, i) => (Number.isInteger(v) && v >= 0 && v < LOOK_LIMITS[i] ? v : 0));
}

const WALK = 125, SPRINT = 190;
const PLAYER_R = 11;
const STAMINA_DRAIN = 32, STAMINA_REGEN = 16;
const PING_COOLDOWN = 4;
const PING_NOISE = 750, SPRINT_NOISE = 380, FUSE_NOISE = 520;

const M_WANDER = 70, M_INVESTIGATE = 112, M_CHASE = 168;
const M_SIGHT = 200, M_LOSE = 450, M_RADIUS = 18, M_CATCH = 26;

const rnd = (a, b) => a + Math.random() * (b - a);
const dist = (ax, ay, bx, by) => Math.hypot(ax - bx, ay - by);
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));

function pushOut(o, rad, pillars) {
  for (const p of pillars) {
    const dx = o.x - p.x, dy = o.y - p.y;
    const d = Math.hypot(dx, dy);
    const min = p.r + rad;
    if (d < min && d > 0.001) {
      o.x = p.x + (dx / d) * min;
      o.y = p.y + (dy / d) * min;
    }
  }
}

// ---------- game room ----------
class Game {
  constructor(code) {
    this.code = code;
    this.players = new Map();
    this.phase = 'playing';
    this.phaseT = 0;
    this.genMap();
    this.timer = setInterval(() => this.tick(), 1000 / TICK);
  }

  genMap() {
    const cx = W / 2, cy = H / 2;
    const corners = [[260, 260], [W - 260, 260], [260, H - 260], [W - 260, H - 260]];
    const ec = corners[Math.floor(Math.random() * 4)];
    this.exit = { x: ec[0], y: ec[1] };

    this.pillars = [];
    let tries = 0;
    while (this.pillars.length < 55 && tries++ < 3000) {
      const r = rnd(28, 70), x = rnd(80, W - 80), y = rnd(80, H - 80);
      if (dist(x, y, cx, cy) < 220 + r) continue;
      if (dist(x, y, this.exit.x, this.exit.y) < 160 + r) continue;
      this.pillars.push({ x, y, r });
    }

    this.fuses = [];
    tries = 0;
    let minGap = 450;
    while (this.fuses.length < FUSE_COUNT && tries++ < 6000) {
      if (tries % 1500 === 0) minGap -= 80; // loosen if the map is crowded
      const x = rnd(150, W - 150), y = rnd(150, H - 150);
      if (dist(x, y, cx, cy) < 600) continue;
      if (dist(x, y, this.exit.x, this.exit.y) < 400) continue;
      if (this.pillars.some(p => dist(x, y, p.x, p.y) < p.r + 30)) continue;
      if (this.fuses.some(f => dist(x, y, f.x, f.y) < minGap)) continue;
      this.fuses.push({ x, y, c: false });
    }

    let mx, my;
    do { mx = rnd(200, W - 200); my = rnd(200, H - 200); } while (dist(mx, my, cx, cy) < 900);
    this.monster = { x: mx, y: my, s: 'wander', tx: mx, ty: my, chase: null, lost: 0, stuck: 0, side: 1 };
    this.noises = [];
  }

  mapPayload() {
    return {
      W, H,
      pillars: this.pillars,
      exit: this.exit,
      fuses: this.fuses.map(f => ({ x: f.x, y: f.y })),
    };
  }

  resetRound() {
    this.phase = 'playing';
    this.phaseT = 0;
    this.genMap();
    for (const p of this.players.values()) this.respawn(p);
    io.to(this.code).emit('map', this.mapPayload());
  }

  respawn(p) {
    p.x = W / 2 + rnd(-50, 50);
    p.y = H / 2 + rnd(-50, 50);
    p.alive = true;
    p.escaped = false;
    p.stamina = 100;
    p.pingCd = 0;
    p.noiseT = 0;
  }

  addPlayer(id, name, look) {
    const p = {
      id, name, look, in: { x: 0, y: 0, sp: false, f: 0 },
      x: 0, y: 0, alive: true, escaped: false, stamina: 100, pingCd: 0, noiseT: 0,
    };
    this.respawn(p);
    this.players.set(id, p);
    return p;
  }

  addNoise(x, y, r) { this.noises.push({ x, y, r }); }

  ping(id) {
    const p = this.players.get(id);
    if (!p || !p.alive || p.escaped || this.phase !== 'playing' || p.pingCd > 0) return;
    p.pingCd = PING_COOLDOWN;
    this.addNoise(p.x, p.y, PING_NOISE);
    io.to(this.code).emit('ev', { t: 'ping', id, x: p.x, y: p.y });
  }

  tick() {
    const dt = DT;
    this.phaseT += dt;

    if (this.phase !== 'playing') {
      if (this.phaseT > RESTART_AFTER && this.players.size > 0) this.resetRound();
      this.broadcast();
      return;
    }

    const got = this.fuses.filter(f => f.c).length;
    const need = this.fuses.length;

    // players
    for (const p of this.players.values()) {
      if (!p.alive || p.escaped) continue;
      p.pingCd = Math.max(0, p.pingCd - dt);

      let { x: ix, y: iy, sp } = p.in;
      const len = Math.hypot(ix, iy);
      const moving = len > 0.01;
      if (moving) { ix /= len; iy /= len; }

      const sprinting = sp && moving && p.stamina > 0;
      const speed = sprinting ? SPRINT : WALK;
      if (moving) {
        p.x = clamp(p.x + ix * speed * dt, 12, W - 12);
        p.y = clamp(p.y + iy * speed * dt, 12, H - 12);
        pushOut(p, PLAYER_R, this.pillars);
      }

      if (sprinting) {
        p.stamina = Math.max(0, p.stamina - STAMINA_DRAIN * dt);
        p.noiseT -= dt;
        if (p.noiseT <= 0) { this.addNoise(p.x, p.y, SPRINT_NOISE); p.noiseT = 0.45; }
      } else {
        p.stamina = Math.min(100, p.stamina + STAMINA_REGEN * dt);
      }

      // collect fuses
      for (let i = 0; i < this.fuses.length; i++) {
        const f = this.fuses[i];
        if (!f.c && dist(p.x, p.y, f.x, f.y) < 28) {
          f.c = true;
          this.addNoise(f.x, f.y, FUSE_NOISE);
          io.to(this.code).emit('ev', { t: 'fuse', id: p.id, i, x: f.x, y: f.y });
        }
      }

      // escape
      const open = this.fuses.every(f => f.c);
      if (open && dist(p.x, p.y, this.exit.x, this.exit.y) < 44) {
        p.escaped = true;
        io.to(this.code).emit('ev', { t: 'escape', id: p.id });
      }
    }

    this.updateMonster(dt);

    // win / lose
    if (this.players.size > 0) {
      const remaining = [...this.players.values()].filter(p => p.alive && !p.escaped).length;
      if (remaining === 0) {
        const escaped = [...this.players.values()].some(p => p.escaped);
        this.phase = escaped ? 'won' : 'lost';
        this.phaseT = 0;
      }
    }

    this.broadcast();
  }

  updateMonster(dt) {
    const m = this.monster;
    const alive = [...this.players.values()].filter(p => p.alive && !p.escaped);

    // hear noises
    if (m.s !== 'chase') {
      let best = null, bestD = Infinity;
      for (const n of this.noises) {
        const d = dist(m.x, m.y, n.x, n.y);
        if (d < n.r && d < bestD) { best = n; bestD = d; }
      }
      if (best) {
        m.s = 'investigate';
        m.tx = best.x + rnd(-40, 40);
        m.ty = best.y + rnd(-40, 40);
      }
    }
    this.noises = [];

    // sight
    if (m.s !== 'chase') {
      let near = null, nd = Infinity;
      for (const p of alive) {
        const d = dist(m.x, m.y, p.x, p.y);
        if (d < M_SIGHT && d < nd) { near = p; nd = d; }
      }
      if (near) { m.s = 'chase'; m.chase = near.id; m.lost = 0; }
    }

    // chase upkeep
    if (m.s === 'chase') {
      const t = this.players.get(m.chase);
      if (!t || !t.alive || t.escaped) {
        m.s = 'wander'; m.chase = null; this.pickWander(m, alive);
      } else {
        m.tx = t.x; m.ty = t.y;
        if (dist(m.x, m.y, t.x, t.y) > M_LOSE) {
          m.lost += dt;
          if (m.lost > 3) { m.s = 'investigate'; m.chase = null; m.lost = 0; }
        } else m.lost = 0;
      }
    }

    // move
    const speed = m.s === 'chase' ? M_CHASE : m.s === 'investigate' ? M_INVESTIGATE : M_WANDER;
    let dx = m.tx - m.x, dy = m.ty - m.y;
    const d = Math.hypot(dx, dy);
    if (d < 20) {
      if (m.s !== 'chase') { m.s = 'wander'; this.pickWander(m, alive); }
    } else {
      dx /= d; dy /= d;
      if (m.stuck > 0.25) { // slide around pillars
        const ang = 1.2 * m.side;
        const c = Math.cos(ang), s = Math.sin(ang);
        const rx = dx * c - dy * s, ry = dx * s + dy * c;
        dx = rx; dy = ry;
      }
      const step = speed * dt;
      const ox = m.x, oy = m.y;
      m.x = clamp(m.x + dx * step, 20, W - 20);
      m.y = clamp(m.y + dy * step, 20, H - 20);
      pushOut(m, M_RADIUS, this.pillars);
      const moved = dist(ox, oy, m.x, m.y);
      if (moved < step * 0.4) {
        m.stuck += dt;
        if (m.stuck > 1.2) { m.side = -m.side; m.stuck = 0.3; }
      } else m.stuck = Math.max(0, m.stuck - dt * 2);
    }

    // catch
    for (const p of alive) {
      if (dist(m.x, m.y, p.x, p.y) < M_CATCH) {
        p.alive = false;
        io.to(this.code).emit('ev', { t: 'death', id: p.id, x: p.x, y: p.y });
        if (m.chase === p.id) { m.s = 'wander'; m.chase = null; this.pickWander(m, alive.filter(a => a !== p)); }
      }
    }
  }

  pickWander(m, alive) {
    if (alive.length && Math.random() < 0.4) {
      const p = alive[Math.floor(Math.random() * alive.length)];
      m.tx = clamp(p.x + rnd(-350, 350), 40, W - 40);
      m.ty = clamp(p.y + rnd(-350, 350), 40, H - 40);
    } else {
      m.tx = rnd(100, W - 100);
      m.ty = rnd(100, H - 100);
    }
  }

  broadcast() {
    const got = this.fuses.filter(f => f.c).length;
    io.to(this.code).emit('s', {
      ph: this.phase,
      rt: Math.max(0, RESTART_AFTER - this.phaseT),
      fc: this.fuses.map(f => (f.c ? 1 : 0)),
      got,
      need: this.fuses.length,
      open: got >= this.fuses.length,
      m: { x: Math.round(this.monster.x), y: Math.round(this.monster.y), s: this.monster.s },
      p: [...this.players.values()].map(p => ({
        id: p.id, n: p.name, x: Math.round(p.x * 10) / 10, y: Math.round(p.y * 10) / 10,
        a: p.alive, e: p.escaped, s: Math.round(p.stamina), pc: Math.round(p.pingCd * 10) / 10,
        l: p.look,
      })),
    });
  }

  destroy() { clearInterval(this.timer); }
}

// ---------- sockets ----------
const games = new Map();

function newCode() {
  const abc = 'abcdefghjkmnpqrstuvwxyz23456789';
  let c;
  do {
    c = '';
    for (let i = 0; i < 4; i++) c += abc[Math.floor(Math.random() * abc.length)];
  } while (games.has(c));
  return c;
}

io.on('connection', (socket) => {
  let game = null;

  socket.on('join', (data) => {
    if (game) return;
    data = data || {};
    const name = String(data.name || 'Survivor').replace(/[^\w \-]/g, '').slice(0, 12) || 'Survivor';
    const look = cleanLook(data.look);

    let room;
    if (data.mode === 'create') {
      room = newCode();
    } else {
      room = String(data.room || '').toLowerCase().replace(/[^a-z0-9]/g, '').slice(0, 12);
      if (!games.has(room)) { socket.emit('err', { m: 'No game found with that code.' }); return; }
    }

    let g = games.get(room);
    if (!g) { g = new Game(room); games.set(room, g); }
    if (g.players.size >= 8) { socket.emit('err', { m: 'That game is full (8 players max).' }); return; }

    game = g;
    socket.join(room);
    game.addPlayer(socket.id, name, look);
    socket.emit('you', { id: socket.id, room });
    socket.emit('map', game.mapPayload());
  });

  socket.on('i', (inp) => {
    if (!game) return;
    const p = game.players.get(socket.id);
    if (!p || !inp) return;
    p.in.x = clamp(Number(inp.x) || 0, -1, 1);
    p.in.y = clamp(Number(inp.y) || 0, -1, 1);
    p.in.sp = !!inp.sp;
    const f = Number(inp.f);
    p.in.f = Number.isFinite(f) ? clamp(f, -7, 7) : 0;
  });

  socket.on('ping', () => { if (game) game.ping(socket.id); });

  socket.on('disconnect', () => {
    if (!game) return;
    game.players.delete(socket.id);
    if (game.players.size === 0) {
      game.destroy();
      games.delete(game.code);
    }
  });
});

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => console.log(`BLACKOUT running on http://localhost:${PORT}`));
