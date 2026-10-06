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
const RESULT_TIME = Number(process.env.BLACKOUT_RESULT_TIME) || 8; // seconds on the win/lose screen
const MAX_PLAYERS = 8;

// appearance: hair style, hair color, skin tone, shirt style, shirt color, pants, shoes
const LOOK_LIMITS = [9, 9, 5, 5, 12, 10, 21];
function cleanLook(l) {
  if (!Array.isArray(l) || l.length !== LOOK_LIMITS.length) return LOOK_LIMITS.map(() => 0);
  return l.map((v, i) => (Number.isInteger(v) && v >= 0 && v < LOOK_LIMITS[i] ? v : 0));
}

const WALK = 125, SPRINT = 190;
const PLAYER_R = 11;
const STAMINA_DRAIN = 32, STAMINA_REGEN = 16;
const PING_COOLDOWN = 4;
const PING_NOISE = 750, SPRINT_NOISE = 380, FUSE_NOISE = 520;

// bot monster
const M_WANDER = 70, M_INVESTIGATE = 112, M_CHASE = 168;
const M_SIGHT = 200, M_LOSE = 450, M_RADIUS = 18, M_CATCH = 26;
const DIFF = {
  easy:   { spd: 0.85, hear: 0.8, sight: 170 },
  normal: { spd: 1,    hear: 1,   sight: 200 },
  hard:   { spd: 1.12, hear: 1.2, sight: 235 },
};
// human-controlled monster
const M_PLAYER = 150;
const TP_TIME = 45, TP_MAX = 3;   // human monster: +1 teleport every 45s

const rnd = (a, b) => a + Math.random() * (b - a);
const dist = (ax, ay, bx, by) => Math.hypot(ax - bx, ay - by);
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));

// ---------- tile map helpers ----------
const T = 40, N = 60;                 // tile size, tiles per side (N*T = W)
const SOLID = '#DSPT';
function solidT(grid, tx, ty) {
  if (tx < 0 || ty < 0 || tx >= N || ty >= N) return true;
  return SOLID.includes(grid[ty][tx]);
}
function blockedAt(grid, x, y, r) {
  const x0 = Math.floor((x - r) / T), x1 = Math.floor((x + r) / T);
  const y0 = Math.floor((y - r) / T), y1 = Math.floor((y + r) / T);
  return solidT(grid, x0, y0) || solidT(grid, x1, y0) || solidT(grid, x0, y1) || solidT(grid, x1, y1);
}
function pushOut(o, rad, grid) {
  for (let pass = 0; pass < 2; pass++) {
    const x0 = Math.floor((o.x - rad) / T), x1 = Math.floor((o.x + rad) / T);
    const y0 = Math.floor((o.y - rad) / T), y1 = Math.floor((o.y + rad) / T);
    for (let ty = y0; ty <= y1; ty++) {
      for (let tx = x0; tx <= x1; tx++) {
        if (!solidT(grid, tx, ty)) continue;
        const rx = tx * T, ry = ty * T;
        const nx = clamp(o.x, rx, rx + T), ny = clamp(o.y, ry, ry + T);
        const dx = o.x - nx, dy = o.y - ny, d = Math.hypot(dx, dy);
        if (d < rad) {
          if (d > 0.0001) { o.x = nx + dx / d * rad; o.y = ny + dy / d * rad; }
          else {
            const l = o.x - rx, r = rx + T - o.x, t = o.y - ry, b = ry + T - o.y, m = Math.min(l, r, t, b);
            if (m === l) o.x = rx - rad; else if (m === r) o.x = rx + T + rad; else if (m === t) o.y = ry - rad; else o.y = ry + T + rad;
          }
        }
      }
    }
  }
}

function buildGrid() {
  const g = Array.from({ length: N }, () => Array(N).fill('#'));
  const carve = (x0, y0, x1, y1, ch) => { for (let y = y0; y <= y1; y++) for (let x = x0; x <= x1; x++) g[y][x] = ch; };
  for (const [a, b] of [[2, 5], [28, 31], [54, 57]]) { carve(2, a, 57, b, '.'); carve(a, 2, b, 57, '.'); }
  const rs = [[7, 16], [18, 26], [33, 42], [44, 52]];
  const rooms = [];
  for (const ry of rs) for (const rx of rs) { carve(rx[0], ry[0], rx[1], ry[1], ','); rooms.push({ x0: rx[0], x1: rx[1], y0: ry[0], y1: ry[1] }); }
  const kinds = ['class', 'class', 'library', 'storage', 'cafe'];
  for (const r of rooms) {
    const cx = (r.x0 + r.x1) >> 1, cy = (r.y0 + r.y1) >> 1;
    // doors (some room-to-room doors are left out for variety)
    const door = (x0, y0, x1, y1, bx, by) => {
      const inter = g[by] && g[by][bx] === ',';
      if (inter && Math.random() < 0.3) return;
      carve(x0, y0, x1, y1, ',');
    };
    door(r.x0 - 1, cy - 1, r.x0 - 1, cy + 1, r.x0 - 2, cy);
    door(r.x1 + 1, cy - 1, r.x1 + 1, cy + 1, r.x1 + 2, cy);
    door(cx - 1, r.y0 - 1, cx + 1, r.y0 - 1, cx, r.y0 - 2);
    door(cx - 1, r.y1 + 1, cx + 1, r.y1 + 1, cx, r.y1 + 2);
    // furniture, keeping a clear cross through the room
    const kind = kinds[Math.floor(Math.random() * kinds.length)];
    for (let y = r.y0; y <= r.y1; y++) for (let x = r.x0; x <= r.x1; x++) {
      if (Math.abs(x - cx) <= 1 || Math.abs(y - cy) <= 1) continue;
      const lx = x - r.x0, ly = y - r.y0;
      if (kind === 'class' && lx % 3 === 1 && ly % 3 === 1) g[y][x] = 'D';
      else if (kind === 'library' && (y === r.y0 || y === r.y1 || (ly % 4 === 2 && lx > 0 && lx < r.x1 - r.x0))) g[y][x] = 'S';
      else if (kind === 'storage' && Math.random() < 0.16) g[y][x] = 'P';
      else if (kind === 'cafe' && lx % 4 === 1 && ly % 4 === 1) g[y][x] = 'T';
    }
  }
  // a few crates in the hallways
  for (let i = 0; i < 14; i++) {
    const x = 6 + Math.floor(Math.random() * 48), y = 6 + Math.floor(Math.random() * 48);
    if (g[y][x] === '.' && !(x >= 28 && x <= 31 && y >= 28 && y <= 31) && !(x >= 28 && x <= 31) && !(y >= 28 && y <= 31)) g[y][x] = 'P';
  }
  return g;
}

// ---------- game room ----------
class Game {
  constructor(code, hostId) {
    this.code = code;
    this.players = new Map();
    this.hostId = hostId;
    this.phase = 'lobby'; // lobby -> playing -> won | lost -> lobby
    this.phaseT = 0;
    this.tickN = 0;
    this.mode = 'bot';    // who plays the monster: 'random' | 'pick' | 'bot'
    this.pickId = null;
    this.diff = 'normal';
    this.monsterId = null; // set while a human is playing the monster
    this.noises = [];
    this.genMap();
    this.timer = setInterval(() => this.tick(), 1000 / TICK);
  }

  genMap() {
    this.grid = buildGrid();
    const grid = this.grid;
    const sx = 30 * T, sy = 30 * T;                  // spawn: middle of the building
    // flood fill from the spawn so everything we place is reachable
    const seen = new Uint8Array(N * N), q = [[29, 29]];
    seen[29 * N + 29] = 1;
    while (q.length) {
      const [x, y] = q.pop();
      for (const [dx, dy] of [[1, 0], [-1, 0], [0, 1], [0, -1]]) {
        const nx = x + dx, ny = y + dy;
        if (solidT(grid, nx, ny) || seen[ny * N + nx]) continue;
        seen[ny * N + nx] = 1; q.push([nx, ny]);
      }
    }
    this.floors = [];
    for (let y = 0; y < N; y++) for (let x = 0; x < N; x++) if (seen[y * N + x]) this.floors.push({ x: x * T + T / 2, y: y * T + T / 2, c: grid[y][x] });
    const corners = [[3, 3], [56, 3], [3, 56], [56, 56]];
    const ec = corners[Math.floor(Math.random() * 4)];
    this.exit = { x: ec[0] * T + T / 2, y: ec[1] * T + T / 2 };
    this.spawn = { x: sx, y: sy };

    this.fuses = [];
    const roomFloors = this.floors.filter(f => f.c === ',');
    let tries = 0, minGap = 600;
    while (this.fuses.length < FUSE_COUNT && tries++ < 6000) {
      if (tries % 1000 === 0) minGap -= 100;
      const f = roomFloors[Math.floor(Math.random() * roomFloors.length)];
      if (dist(f.x, f.y, sx, sy) < 500) continue;
      if (dist(f.x, f.y, this.exit.x, this.exit.y) < 500) continue;
      if (this.fuses.some(o => dist(f.x, f.y, o.x, o.y) < minGap)) continue;
      this.fuses.push({ x: f.x, y: f.y, c: false });
    }
    let mf;
    do { mf = this.floors[Math.floor(Math.random() * this.floors.length)]; } while (dist(mf.x, mf.y, sx, sy) < 900);
    this.monster = { x: mf.x, y: mf.y, s: 'wander', tx: mf.x, ty: mf.y, chase: null, lost: 0 };
    this.field = null;
    this.noises = [];
  }

  mapPayload() {
    return {
      W, H, T, N,
      grid: this.grid.map(r => r.join('')),
      exit: this.exit,
      fuses: this.fuses.map(f => ({ x: f.x, y: f.y })),
    };
  }

  // ----- bot navigation -----
  los(x0, y0, x1, y1, r) {
    const d = dist(x0, y0, x1, y1), n = Math.ceil(d / 12);
    for (let i = 1; i < n; i++) {
      const t = i / n;
      if (blockedAt(this.grid, x0 + (x1 - x0) * t, y0 + (y1 - y0) * t, r)) return false;
    }
    return true;
  }
  fieldFor(tx, ty) {
    const key = ty * N + tx;
    if (this.field && this.field.key === key) return this.field.df;
    const df = new Int16Array(N * N).fill(-1);
    const q = [key]; df[key] = 0;
    for (let h = 0; h < q.length; h++) {
      const c = q[h], x = c % N, y = (c / N) | 0;
      for (const [dx, dy] of [[1, 0], [-1, 0], [0, 1], [0, -1]]) {
        const nx = x + dx, ny = y + dy;
        if (solidT(this.grid, nx, ny) || df[ny * N + nx] >= 0) continue;
        df[ny * N + nx] = df[c] + 1; q.push(ny * N + nx);
      }
    }
    this.field = { key, df };
    return df;
  }
  // unit direction the bot should walk to reach (tx,ty)
  navDir(m, tx, ty) {
    if (this.los(m.x, m.y, tx, ty, M_RADIUS - 2)) {
      const d = dist(m.x, m.y, tx, ty) || 1;
      return [(tx - m.x) / d, (ty - m.y) / d];
    }
    const gx = clamp(Math.floor(tx / T), 0, N - 1), gy = clamp(Math.floor(ty / T), 0, N - 1);
    const df = this.fieldFor(gx, gy);
    const mx = Math.floor(m.x / T), my = Math.floor(m.y / T);
    let best = df[my * N + mx], bx = mx, by = my;
    if (best < 0) return null;
    for (const [dx, dy] of [[1, 0], [-1, 0], [0, 1], [0, -1]]) {
      const nx = mx + dx, ny = my + dy;
      if (nx < 0 || ny < 0 || nx >= N || ny >= N) continue;
      const v = df[ny * N + nx];
      if (v >= 0 && v < best) { best = v; bx = nx; by = ny; }
    }
    if (bx === mx && by === my) return null;
    const wx = bx * T + T / 2, wy = by * T + T / 2, d = dist(m.x, m.y, wx, wy) || 1;
    return [(wx - m.x) / d, (wy - m.y) / d];
  }
  nearestFloor(x, y) {
    if (!blockedAt(this.grid, x, y, M_RADIUS)) return { x, y };
    const tx = Math.floor(x / T), ty = Math.floor(y / T);
    for (let r = 1; r <= 5; r++) {
      for (let dy = -r; dy <= r; dy++) for (let dx = -r; dx <= r; dx++) {
        if (Math.max(Math.abs(dx), Math.abs(dy)) !== r) continue;
        if (!solidT(this.grid, tx + dx, ty + dy)) return { x: (tx + dx) * T + T / 2, y: (ty + dy) * T + T / 2 };
      }
    }
    return null;
  }

  // ----- lobby -----
  setLobby(id, d) {
    if (id !== this.hostId || this.phase !== 'lobby' || !d) return;
    if (['random', 'pick', 'bot'].includes(d.mode)) this.mode = d.mode;
    if (this.mode === 'pick' && typeof d.pickId === 'string' && this.players.has(d.pickId)) this.pickId = d.pickId;
    if (['easy', 'normal', 'hard'].includes(d.diff)) this.diff = d.diff;
  }

  start(id) {
    if (id !== this.hostId || this.phase !== 'lobby') return;
    this.startRound();
  }

  startRound() {
    this.genMap();
    const ids = [...this.players.keys()];
    let mid = null;
    if (ids.length >= 2) {
      if (this.mode === 'random') mid = ids[Math.floor(Math.random() * ids.length)];
      else if (this.mode === 'pick' && this.pickId && this.players.has(this.pickId)) mid = this.pickId;
    }
    this.monsterId = mid;
    for (const p of this.players.values()) {
      this.respawn(p);
      p.spec = false;
      p.monster = p.id === mid;
      if (p.monster) { p.alive = false; p.tp = 1; p.tpT = 0; } // the monster player is not a survivor
    }
    this.phase = 'playing';
    this.phaseT = 0;
    io.to(this.code).emit('map', this.mapPayload());
  }

  returnToLobby() {
    this.phase = 'lobby';
    this.phaseT = 0;
    this.monsterId = null;
    for (const p of this.players.values()) {
      this.respawn(p);
      p.monster = false;
      p.spec = false;
    }
  }

  // ----- players -----
  respawn(p) {
    p.x = 30 * T + rnd(-50, 50);
    p.y = 30 * T + rnd(-50, 50);
    p.in = { x: 0, y: 0, sp: false };
    p.inT = Date.now();
    p.tp = 0; p.tpT = 0;
    p.alive = true;
    p.escaped = false;
    p.stamina = 100;
    p.pingCd = 0;
    p.noiseT = 0;
  }

  addPlayer(id, name, look) {
    const p = {
      id, name, look, in: { x: 0, y: 0, sp: false },
      x: 0, y: 0, alive: true, escaped: false, stamina: 100, pingCd: 0, noiseT: 0,
      monster: false, spec: false, inT: Date.now(), tp: 0, tpT: 0,
    };
    this.respawn(p);
    if (this.phase !== 'lobby') { p.spec = true; p.alive = false; } // joins next round
    this.players.set(id, p);
    return p;
  }

  removePlayer(id) {
    this.players.delete(id);
    if (this.hostId === id) this.hostId = this.players.keys().next().value || null;
    if (this.pickId === id) this.pickId = null;
    if (this.monsterId === id) this.monsterId = null; // the bot takes over
  }

  survivors() {
    return [...this.players.values()].filter(p => !p.monster && !p.spec && p.alive && !p.escaped);
  }

  addNoise(x, y, r) {
    this.noises.push({ x, y, r });
    if (this.monsterId) io.to(this.monsterId).emit('ev', { t: 'noise', x, y, r });
  }

  ping(id) {
    const p = this.players.get(id);
    if (!p || p.monster || p.spec || !p.alive || p.escaped || this.phase !== 'playing' || p.pingCd > 0) return;
    p.pingCd = PING_COOLDOWN;
    this.addNoise(p.x, p.y, PING_NOISE);
    io.to(this.code).emit('ev', { t: 'ping', id, x: p.x, y: p.y });
  }

  // ----- main loop -----
  tick() {
    const dt = DT;
    this.tickN++;
    this.phaseT += dt;

    if (this.phase === 'lobby') {
      if (this.tickN % 6 === 0) this.broadcast();
      return;
    }
    if (this.phase === 'won' || this.phase === 'lost') {
      if (this.phaseT > RESULT_TIME) this.returnToLobby();
      this.broadcast();
      return;
    }

    // stop anyone whose client went quiet (tabbed out, lagging)
    const nowMs = Date.now();
    for (const p of this.players.values()) if (nowMs - p.inT > 350) p.in = { x: 0, y: 0, sp: false };

    // survivors
    for (const p of this.players.values()) {
      if (p.monster || p.spec || !p.alive || p.escaped) continue;
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
        pushOut(p, PLAYER_R, this.grid);
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

    // monster: a human if one was chosen and is still here, otherwise the bot
    if (this.monsterId && this.players.has(this.monsterId)) this.updateHumanMonster(dt);
    else this.updateMonster(dt);

    // win / lose
    if (this.players.size > 0 && this.survivors().length === 0) {
      const escaped = [...this.players.values()].some(p => !p.monster && !p.spec && p.escaped);
      this.phase = escaped ? 'won' : 'lost';
      this.phaseT = 0;
    }

    this.broadcast();
  }

  // a person is the monster (no sprint, but it can teleport)
  updateHumanMonster(dt) {
    const m = this.monster;
    const p = this.players.get(this.monsterId);
    this.noises = [];

    let { x: ix, y: iy } = p.in;
    const len = Math.hypot(ix, iy);
    if (len > 0.01) {
      ix /= len; iy /= len;
      m.x = clamp(m.x + ix * M_PLAYER * dt, 20, W - 20);
      m.y = clamp(m.y + iy * M_PLAYER * dt, 20, H - 20);
      pushOut(m, M_RADIUS, this.grid);
    }
    m.s = 'wander';
    p.x = m.x; p.y = m.y;

    p.tpT = Math.min(TP_TIME, p.tpT + dt);
    if (p.tpT >= TP_TIME && p.tp < TP_MAX) { p.tp++; p.tpT = 0; }

    for (const s of this.survivors()) {
      if (dist(m.x, m.y, s.x, s.y) < M_CATCH) {
        s.alive = false;
        io.to(this.code).emit('ev', { t: 'death', id: s.id, x: s.x, y: s.y });
      }
    }
  }

  teleport(id, x, y) {
    if (this.phase !== 'playing' || id !== this.monsterId) return;
    const p = this.players.get(id);
    x = Number(x); y = Number(y);
    if (!p || p.tp < 1 || !isFinite(x) || !isFinite(y)) return;
    const s = this.nearestFloor(clamp(x, 40, W - 40), clamp(y, 40, H - 40));
    if (!s) return;
    const m = this.monster, fx = m.x, fy = m.y;
    m.x = s.x; m.y = s.y; p.x = m.x; p.y = m.y; p.tp--;
    io.to(this.code).emit('ev', { t: 'tp', x: m.x, y: m.y, fx, fy });
  }

  // the bot is the monster
  updateMonster(dt) {
    const m = this.monster;
    const D = DIFF[this.diff] || DIFF.normal;
    const alive = this.survivors();

    // hear noises
    if (m.s !== 'chase') {
      let best = null, bestD = Infinity;
      for (const n of this.noises) {
        const d = dist(m.x, m.y, n.x, n.y);
        if (d < n.r * D.hear && d < bestD) { best = n; bestD = d; }
      }
      if (best) { m.s = 'investigate'; m.tx = best.x; m.ty = best.y; }
    }
    this.noises = [];

    // sight (walls block it)
    if (m.s !== 'chase') {
      let near = null, nd = Infinity;
      for (const p of alive) {
        const d = dist(m.x, m.y, p.x, p.y);
        if (d < D.sight && d < nd && this.los(m.x, m.y, p.x, p.y, 2)) { near = p; nd = d; }
      }
      if (near) { m.s = 'chase'; m.chase = near.id; m.lost = 0; }
    }

    // chase upkeep
    if (m.s === 'chase') {
      const t = this.players.get(m.chase);
      if (!t || !t.alive || t.escaped || t.monster || t.spec) {
        m.s = 'wander'; m.chase = null; this.pickWander(m, alive);
      } else {
        m.tx = t.x; m.ty = t.y;
        const far = dist(m.x, m.y, t.x, t.y) > M_LOSE || !this.los(m.x, m.y, t.x, t.y, 2);
        if (far) {
          m.lost += dt;
          if (m.lost > 4) { m.s = 'investigate'; m.chase = null; m.lost = 0; }
        } else m.lost = 0;
      }
    }

    // move
    const base = m.s === 'chase' ? M_CHASE : m.s === 'investigate' ? M_INVESTIGATE : M_WANDER;
    const speed = base * D.spd;
    const d = dist(m.x, m.y, m.tx, m.ty);
    if (d < 24) {
      if (m.s !== 'chase') { m.s = 'wander'; this.pickWander(m, alive); }
    } else {
      const dir = this.navDir(m, m.tx, m.ty);
      if (!dir) { if (m.s !== 'chase') { m.s = 'wander'; this.pickWander(m, alive); } }
      else {
        m.x = clamp(m.x + dir[0] * speed * dt, 20, W - 20);
        m.y = clamp(m.y + dir[1] * speed * dt, 20, H - 20);
        pushOut(m, M_RADIUS, this.grid);
      }
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
    let f = null;
    if (alive.length && Math.random() < 0.4) {
      const p = alive[Math.floor(Math.random() * alive.length)];
      for (let i = 0; i < 40 && !f; i++) {
        const c = this.floors[Math.floor(Math.random() * this.floors.length)];
        if (dist(c.x, c.y, p.x, p.y) < 450) f = c;
      }
    }
    if (!f) f = this.floors[Math.floor(Math.random() * this.floors.length)];
    m.tx = f.x; m.ty = f.y;
  }

  broadcast() {
    const got = this.fuses.filter(f => f.c).length;
    const mp = this.monsterId ? this.players.get(this.monsterId) : null;
    io.to(this.code).emit('s', {
      ph: this.phase,
      rt: Math.max(0, RESULT_TIME - this.phaseT),
      lb: { host: this.hostId, mode: this.mode, pick: this.pickId, diff: this.diff },
      fc: this.fuses.map(f => (f.c ? 1 : 0)),
      got,
      need: this.fuses.length,
      open: got >= this.fuses.length,
      m: { x: Math.round(this.monster.x), y: Math.round(this.monster.y), s: this.monster.s, tp: mp ? mp.tp : 0, tpp: mp ? Math.round(mp.tpT / TP_TIME * 100) / 100 : 0 },
      p: [...this.players.values()].map(p => ({
        id: p.id, n: p.name, x: Math.round(p.x * 10) / 10, y: Math.round(p.y * 10) / 10,
        a: p.alive, e: p.escaped, s: Math.round(p.stamina), pc: Math.round(p.pingCd * 10) / 10,
        l: p.look, mo: p.monster ? 1 : 0, sp: p.spec ? 1 : 0,
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
    if (!g) { g = new Game(room, socket.id); games.set(room, g); }
    if (g.players.size >= MAX_PLAYERS) { socket.emit('err', { m: 'That game is full (8 players max).' }); return; }

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
    p.inT = Date.now();
  });

  socket.on('tp', (d) => { if (game && d) game.teleport(socket.id, d.x, d.y); });
  socket.on('ping', () => { if (game) game.ping(socket.id); });
  socket.on('lobby', (d) => { if (game) game.setLobby(socket.id, d); });
  socket.on('start', () => { if (game) game.start(socket.id); });

  socket.on('disconnect', () => {
    if (!game) return;
    game.removePlayer(socket.id);
    if (game.players.size === 0) {
      game.destroy();
      games.delete(game.code);
    }
  });
});

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => console.log(`BLACKOUT running on http://localhost:${PORT}`));
