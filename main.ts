// Sokoban solver: push-optimal, room by room.
//
// The levels this competition draws decompose into independent rooms: a
// one-square hallway with one to four rooms off it, each holding 3 or 4
// boxes, and a box pushed out of its room can never reach a goal again, so
// the level's push-optimal count is the sum of its rooms' optima. This
// program therefore solves each room on its own with an A* over pushes and
// concatenates the rooms' move strings, walking the player between rooms.
//
// A state is the boxes' squares plus the player's reachable region (named
// by its lowest square): the exact square the player stands on inside the
// region never matters, so states that differ only by it are one state.
// The estimate is the cheapest assignment of boxes to goals by push
// distance (the fewest pushes that move one box alone onto a goal, pulled
// back from the goals over open floor), which never overestimates the
// pushes still needed, so the first solved state A* pops is push-optimal.
// Two deadlocks are pruned, both provably safe: a box on a dead square
// (no push, other boxes aside, can ever bring it to a goal) and a box in a
// frozen 2 x 2 block of walls and boxes with a box off its goal.
//
// Everything is budgeted by work, never by the clock: fixed expansion caps
// per search and one global cap for the whole run, fixed direction order
// (u, d, l, r) and fixed heap tie-breaking, so two runs on one set write
// the same bytes. No randomness, no wall clock, no environment read as a
// source of variation. Node 22 runs this file as it is (erasable syntax
// only): node /bot/main.ts, reading /input/<id>/level.txt and writing
// /output/<id>/solution.txt; MAKEFUN_INPUT_DIR / MAKEFUN_OUTPUT_DIR stand
// in for /input and /output outside a container, as the kit's starter does.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

/** The four directions: [dx, dy, step letter, push letter]. */
const DIRS: [number, number, string, string][] = [
  [0, -1, 'u', 'U'],
  [0, 1, 'd', 'D'],
  [-1, 0, 'l', 'L'],
  [1, 0, 'r', 'R'],
];

// Work budgets, in state expansions: never the clock, so a run's answers
// cannot change between its two executions.
const ROOM_EXPANSIONS = 1_000_000;
const WHOLE_EXPANSIONS = 1_000_000;
const MOVE_EXPANSIONS = 200_000;
const GLOBAL_EXPANSIONS = 6_000_000;

interface Level {
  w: number;
  h: number;
  wall: Uint8Array;
  goals: number[];
  boxes: number[];
  player: number;
}

/** A level in XSB text (# wall, space floor, . goal, $ box, * box on a goal, @ player, + player on a goal). */
function parseLevel(text: string): Level {
  const rows = text.split('\n').filter((r) => r.length > 0);
  const h = rows.length;
  const w = Math.max(...rows.map((r) => r.length));
  const wall = new Uint8Array(w * h).fill(1);
  const goals: number[] = [];
  const boxes: number[] = [];
  let player = -1;
  rows.forEach((row, y) => {
    for (let x = 0; x < row.length; x++) {
      const ch = row[x];
      const i = y * w + x;
      if (ch === '#') continue;
      wall[i] = 0;
      if (ch === '.' || ch === '*' || ch === '+') goals.push(i);
      if (ch === '$' || ch === '*') boxes.push(i);
      if (ch === '@' || ch === '+') player = i;
    }
  });
  // A square on the outermost frame is a wall whatever it shows.
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      if (x === 0 || y === 0 || x === w - 1 || y === h - 1) wall[y * w + x] = 1;
    }
  }
  return { w, h, wall, goals, boxes: boxes.sort((a, b) => a - b), player };
}

/**
 * For one goal, the fewest pushes that move a box alone onto it, per
 * square (-1 where no push path exists): pulled back from the goal, a box
 * at y pushed in direction d lands on x when the player can stand at y - d.
 */
function pushDist(level: Level, goal: number): Int32Array {
  const { w, wall } = level;
  const size = wall.length;
  const dist = new Int32Array(size).fill(-1);
  dist[goal] = 0;
  const queue = [goal];
  for (let qi = 0; qi < queue.length; qi++) {
    const x = queue[qi];
    const nd = dist[x] + 1;
    for (const [dx, dy] of DIRS) {
      const d = dy * w + dx;
      const y = x - d;
      if (y < 0 || y >= size || wall[y] || dist[y] !== -1) continue;
      const behind = y - d;
      if (behind < 0 || behind >= size || wall[behind]) continue;
      dist[y] = nd;
      queue.push(y);
    }
  }
  return dist;
}

/** Whether the box just pushed to `t` sits in a frozen 2 x 2 block of walls and boxes with a box off its goal. */
function frozenBlock(level: Level, occupied: Uint8Array, goalSet: Uint8Array, t: number): boolean {
  const { w, wall } = level;
  for (const a of [t, t - 1, t - w, t - w - 1]) {
    const b = a + 1;
    const c = a + w;
    const d = c + 1;
    if (a < 0 || d >= wall.length) continue;
    if (!(wall[a] || occupied[a]) || !(wall[b] || occupied[b]) || !(wall[c] || occupied[c]) || !(wall[d] || occupied[d])) continue;
    if ((occupied[a] && !goalSet[a]) || (occupied[b] && !goalSet[b]) || (occupied[c] && !goalSet[c]) || (occupied[d] && !goalSet[d])) return true;
  }
  return false;
}

/** Reachable-region flood fills, two independent stamp sets: one for the state being expanded, one for successor keys. */
function makeRegion(level: Level) {
  const { w, wall } = level;
  const size = wall.length;
  const seenA = new Int32Array(size);
  const seenB = new Int32Array(size);
  const stack = new Int32Array(size);
  let stampA = 0;
  let stampB = 0;
  const fill = (seen: Int32Array, stamp: number, occupied: Uint8Array, from: number): number => {
    let low = from;
    let n = 0;
    stack[n++] = from;
    seen[from] = stamp;
    while (n > 0) {
      const p = stack[--n];
      if (p < low) low = p;
      const q0 = p - w;
      const q1 = p + w;
      const q2 = p - 1;
      const q3 = p + 1;
      if (!wall[q0] && !occupied[q0] && seen[q0] !== stamp) { seen[q0] = stamp; stack[n++] = q0; }
      if (!wall[q1] && !occupied[q1] && seen[q1] !== stamp) { seen[q1] = stamp; stack[n++] = q1; }
      if (!wall[q2] && !occupied[q2] && seen[q2] !== stamp) { seen[q2] = stamp; stack[n++] = q2; }
      if (!wall[q3] && !occupied[q3] && seen[q3] !== stamp) { seen[q3] = stamp; stack[n++] = q3; }
    }
    return low;
  };
  return {
    /** The lowest square the player reaches from `from`; seenA marks the region. */
    fillA(occupied: Uint8Array, from: number): number {
      stampA++;
      return fill(seenA, stampA, occupied, from);
    },
    inA(q: number): boolean {
      return seenA[q] === stampA;
    },
    /** The lowest square the player reaches from `from`, on the second stamp set. */
    fillB(occupied: Uint8Array, from: number): number {
      stampB++;
      return fill(seenB, stampB, occupied, from);
    },
  };
}

/** A state's key: its region's lowest square and the boxes' squares. Exact while size ** (boxes + 1) stays under 2 ** 53. */
function keyOf(boxes: number[], low: number, size: number): number | string {
  if (boxes.length <= 5) {
    let k = low;
    for (const b of boxes) k = k * size + b;
    return k;
  }
  return low + '|' + boxes.join(',');
}

/**
 * The cheapest assignment of boxes to goals by push distance (branch and
 * bound; at most 6 boxes take the exact match, more take the sum of
 * per-box minima, also admissible). Infinity when no box can reach a
 * distinct goal each: no solution from this state.
 */
function heuristic(boxes: number[], dists: Int32Array[]): number {
  const n = boxes.length;
  if (n === 0) return 0;
  if (n > 6) {
    let s = 0;
    for (const b of boxes) {
      let m = Infinity;
      for (const d of dists) {
        const v = d[b];
        if (v >= 0 && v < m) m = v;
      }
      if (m === Infinity) return Infinity;
      s += m;
    }
    return s;
  }
  const used = new Array<boolean>(n).fill(false);
  let best = Infinity;
  const rec = (i: number, acc: number): void => {
    if (acc >= best) return;
    if (i === n) {
      best = acc;
      return;
    }
    for (let g = 0; g < n; g++) {
      if (used[g]) continue;
      const v = dists[g]![boxes[i]!];
      if (v < 0) continue;
      used[g] = true;
      rec(i + 1, acc + v);
      used[g] = false;
    }
  };
  rec(0, 0);
  return best;
}

/** A binary heap on [f, h, sequence, state]: lower f first, then lower h, then earlier pushed. */
function heapPush(heap: [number, number, number, number][], e: [number, number, number, number]): void {
  let i = heap.length;
  heap.push(e);
  while (i > 0) {
    const p = (i - 1) >> 1;
    const a = heap[i]!;
    const b = heap[p]!;
    if (a[0] > b[0] || (a[0] === b[0] && (a[1] > b[1] || (a[1] === b[1] && a[2] > b[2])))) break;
    heap[i] = b;
    heap[p] = a;
    i = p;
  }
}

function heapPop(heap: [number, number, number, number][]): [number, number, number, number] {
  const top = heap[0]!;
  const last = heap.pop()!;
  if (heap.length > 0) {
    heap[0] = last;
    for (let i = 0; ; ) {
      let c = 2 * i + 1;
      if (c >= heap.length) break;
      if (c + 1 < heap.length) {
        const a = heap[c + 1]!;
        const b = heap[c]!;
        if (a[0] < b[0] || (a[0] === b[0] && (a[1] < b[1] || (a[1] === b[1] && a[2] < b[2])))) c++;
      }
      const a = heap[c]!;
      const b = heap[i]!;
      if (a[0] > b[0] || (a[0] === b[0] && (a[1] > b[1] || (a[1] === b[1] && a[2] > b[2])))) break;
      heap[i] = a;
      heap[c] = b;
      i = c;
    }
  }
  return top;
}

/** The shortest walk from `from` to `to` around walls and boxes, in lower LURD letters (first direction first on ties). */
function walkTo(level: Level, occupied: Uint8Array, from: number, to: number): string {
  const { w, wall } = level;
  if (from === to) return '';
  const prev = new Int32Array(wall.length).fill(-1);
  const how = new Array<string>(wall.length);
  const queue = [from];
  prev[from] = from;
  for (let qi = 0; qi < queue.length; qi++) {
    const p = queue[qi];
    if (p === to) break;
    for (const [dx, dy, letter] of DIRS) {
      const q = p + dy * w + dx;
      if (q < 0 || q >= wall.length || wall[q] || occupied[q] || prev[q] !== -1) continue;
      prev[q] = p;
      how[q] = letter;
      queue.push(q);
    }
  }
  if (prev[to] === -1) throw new Error('walkTo: the push square is out of reach');
  let s = '';
  for (let p = to; p !== from; p = prev[p]) s = how[p] + s;
  return s;
}

/** The square the player stands on after `moves` (LURD, case aside) from `from` on a board `w` wide. */
function endOf(w: number, from: number, moves: string): number {
  let p = from;
  for (const ch of moves.toLowerCase()) p += ch === 'u' ? -w : ch === 'd' ? w : ch === 'l' ? -1 : 1;
  return p;
}

/**
 * The push-optimal solution of `level` by A* over pushes, or null when the
 * search gives up (or the level has no solution). Moves: lower letters are
 * steps, upper ones pushes.
 */
function solvePushAStar(level: Level, cap: number, work: { left: number }): { pushes: number; moves: string } | null {
  const { w, wall, goals } = level;
  const size = wall.length;
  const goalSet = new Uint8Array(size);
  for (const g of goals) goalSet[g] = 1;
  const dists = goals.map((g) => pushDist(level, g));
  const live = new Uint8Array(size);
  for (let i = 0; i < size; i++) {
    for (const d of dists) {
      if (d[i] >= 0) {
        live[i] = 1;
        break;
      }
    }
  }
  if (level.boxes.some((b) => !live[b])) return null;
  const boxes0 = level.boxes.slice().sort((a, b) => a - b);
  if (boxes0.every((b) => goalSet[b])) return { pushes: 0, moves: '' };

  const region = makeRegion(level);
  const occupied = new Uint8Array(size);
  for (const b of boxes0) occupied[b] = 1;
  const low0 = region.fillB(occupied, level.player);
  for (const b of boxes0) occupied[b] = 0;

  const boxesArr: number[][] = [boxes0];
  const playerArr: number[] = [level.player];
  const lowArr: number[] = [low0];
  const gArr: number[] = [0];
  const parentArr: number[] = [-1];
  const pushFromArr: number[] = [-1];
  const pushToArr: number[] = [-1];
  const pushDirArr: number[] = [-1];

  const closed = new Map<number | string, number>();
  closed.set(keyOf(boxes0, low0, size), 0);
  const heap: [number, number, number, number][] = [];
  let seq = 0;
  const h0 = heuristic(boxes0, dists);
  if (h0 === Infinity) return null;
  heapPush(heap, [h0, h0, seq++, 0]);

  const occ = new Uint8Array(size);
  let expansions = 0;
  while (heap.length > 0) {
    const [, , , s] = heapPop(heap);
    const bs = boxesArr[s]!;
    if (closed.get(keyOf(bs, lowArr[s]!, size))! < gArr[s]!) continue;
    if (bs.every((b) => goalSet[b])) {
      // Rebuild the moves: walk to each push's square, then push.
      const path: number[] = [];
      for (let t = s; t > 0; t = parentArr[t]!) path.push(t);
      path.reverse();
      let moves = '';
      let player = level.player;
      let boxes = boxes0.slice();
      for (const t of path) {
        const from = pushFromArr[t]!;
        const to = pushToArr[t]!;
        const di = pushDirArr[t]!;
        const d = DIRS[di]![1] * w + DIRS[di]![0];
        for (const b of boxes) occ[b] = 1;
        moves += walkTo(level, occ, player, from - d);
        for (const b of boxes) occ[b] = 0;
        moves += DIRS[di]![3];
        player = from;
        boxes[boxes.indexOf(from)] = to;
        boxes.sort((a, b) => a - b);
      }
      return { pushes: gArr[s]!, moves };
    }
    if (expansions >= cap || work.left <= 0) return null;
    expansions++;
    work.left--;
    for (const b of bs) occ[b] = 1;
    region.fillA(occ, playerArr[s]!);
    for (let bi = 0; bi < bs.length; bi++) {
      const b = bs[bi]!;
      for (let di = 0; di < 4; di++) {
        const [dx, dy] = DIRS[di]!;
        const d = dy * w + dx;
        const behind = b - d;
        const t = b + d;
        if (behind < 0 || behind >= size || !region.inA(behind)) continue;
        if (t < 0 || t >= size || wall[t] || occ[t] || !live[t]) continue;
        occ[b] = 0;
        occ[t] = 1;
        const frozen = frozenBlock(level, occ, goalSet, t);
        let nkey: number | string = -1;
        let nlow = -1;
        let nb: number[] | null = null;
        if (!frozen) {
          nb = bs.slice();
          nb[bi] = t;
          nb.sort((a, b2) => a - b2);
          nlow = region.fillB(occ, b);
          nkey = keyOf(nb, nlow, size);
        }
        occ[t] = 0;
        occ[b] = 1;
        if (frozen || nb === null) continue;
        const ng = gArr[s]! + 1;
        const prev = closed.get(nkey);
        if (prev !== undefined && prev <= ng) continue;
        const nh = heuristic(nb, dists);
        if (nh === Infinity) continue;
        closed.set(nkey, ng);
        const idx = boxesArr.length;
        boxesArr.push(nb);
        playerArr.push(b);
        lowArr.push(nlow);
        gArr.push(ng);
        parentArr.push(s);
        pushFromArr.push(b);
        pushToArr.push(t);
        pushDirArr.push(di);
        heapPush(heap, [ng + nh, nh, seq++, idx]);
      }
    }
    for (const b of bs) occ[b] = 0;
  }
  return null;
}

/**
 * The level's rooms: cut the dead squares of the player's row (the
 * hallway: a box there reaches no goal) out of the floor, and each part
 * left that holds a box is a room, its squares, boxes and goals. Null when
 * some part holds more or fewer boxes than goals, or a box starts in the
 * hallway: then the level is no set of rooms.
 */
function roomsOf(level: Level): { squares: number[]; boxes: number[]; goals: number[]; done: boolean }[] | null {
  const { w, wall, goals, boxes, player } = level;
  const dists = goals.map((g) => pushDist(level, g));
  const live = new Uint8Array(wall.length);
  for (let i = 0; i < wall.length; i++) {
    for (const d of dists) {
      if (d[i] >= 0) {
        live[i] = 1;
        break;
      }
    }
  }
  const row = Math.floor(player / w);
  const cut = new Uint8Array(wall.length);
  for (let i = row * w; i < (row + 1) * w; i++) if (!wall[i] && !live[i]) cut[i] = 1;
  if (boxes.some((b) => cut[b])) return null;
  const part = new Int32Array(wall.length).fill(-1);
  const rooms: { squares: number[]; boxes: number[]; goals: number[]; done: boolean }[] = [];
  for (let s = 0; s < wall.length; s++) {
    if (wall[s] || cut[s] || part[s] >= 0) continue;
    const squares = [s];
    part[s] = rooms.length;
    for (let i = 0; i < squares.length; i++) {
      for (const [dx, dy] of DIRS) {
        const q = squares[i]! + dy * w + dx;
        if (q < 0 || q >= wall.length || wall[q] || cut[q] || part[q] >= 0) continue;
        part[q] = rooms.length;
        squares.push(q);
      }
    }
    rooms.push({ squares, boxes: [], goals: [], done: false });
  }
  for (const b of boxes) rooms[part[b]!]!.boxes.push(b);
  for (const g of goals) if (part[g]! >= 0) rooms[part[g]!]!.goals.push(g);
  if (goals.some((g) => part[g]! < 0) || rooms.some((r) => r.boxes.length !== r.goals.length)) return null;
  return rooms.filter((r) => r.boxes.length > 0);
}

/** The level solved room by room, the other rooms' boxes standing as walls; null when a room's search gives up. */
function solveByRooms(level: Level, work: { left: number }): { pushes: number; moves: string } | null {
  const rooms = roomsOf(level);
  if (rooms === null) return null;
  let player = level.player;
  let pushes = 0;
  let moves = '';
  for (const room of rooms) {
    const wall = level.wall.slice();
    for (const other of rooms) {
      if (other === room) continue;
      // A room already solved has its boxes standing on its goals; a room
      // still to come has them where the level put them.
      for (const b of other.done ? other.goals : other.boxes) wall[b] = 1;
    }
    const sub: Level = {
      w: level.w,
      h: level.h,
      wall,
      goals: room.goals.slice().sort((a, b) => a - b),
      boxes: room.boxes.slice().sort((a, b) => a - b),
      player,
    };
    const solved = solvePushAStar(sub, ROOM_EXPANSIONS, work);
    if (solved === null) return null;
    pushes += solved.pushes;
    moves += solved.moves;
    player = endOf(level.w, player, solved.moves);
    room.done = true;
  }
  return { pushes, moves };
}

/** Fallback: a plain A* over moves (fewest steps), like the house baseline, so a level still gets a valid answer. */
function solveMoveAStar(level: Level, cap: number, work: { left: number }): string | null {
  const { w, wall, goals } = level;
  const size = wall.length;
  const goalSet = new Uint8Array(size);
  for (const g of goals) goalSet[g] = 1;
  const manhattan = (b: number): number => {
    let m = Infinity;
    for (const g of goals) {
      const v = Math.abs((g % w) - (b % w)) + Math.abs(Math.floor(g / w) - Math.floor(b / w));
      if (v < m) m = v;
    }
    return m;
  };
  const est = (bs: number[]): number => bs.reduce((a, b) => a + manhattan(b), 0);
  const keyOfMove = (p: number, bs: number[]): string => p + '|' + bs.join(',');
  const boxes0 = level.boxes.slice().sort((a, b) => a - b);
  if (boxes0.every((b) => goalSet[b])) return '';
  const sp: number[] = [level.player];
  const sb: number[][] = [boxes0];
  const sg: number[] = [0];
  const parent: number[] = [-1];
  const step: string[] = [''];
  const best = new Map<string, number>([[keyOfMove(level.player, boxes0), 0]]);
  const heap: [number, number, number, number][] = [];
  let seq = 0;
  heapPush(heap, [est(boxes0), est(boxes0), seq++, 0]);
  let expansions = 0;
  while (heap.length > 0) {
    const [, , , s] = heapPop(heap);
    const bs = sb[s]!;
    if (best.get(keyOfMove(sp[s]!, bs))! < sg[s]!) continue;
    if (bs.every((b) => goalSet[b])) {
      let moves = '';
      for (let t = s; t > 0; t = parent[t]!) moves = step[t]! + moves;
      return moves;
    }
    if (expansions >= cap || work.left <= 0) return null;
    expansions++;
    work.left--;
    const p = sp[s]!;
    for (const [dx, dy, letter] of DIRS) {
      const d = dy * w + dx;
      const q = p + d;
      if (q < 0 || q >= size || wall[q]) continue;
      let nb = bs;
      let move = letter;
      const at = bs.indexOf(q);
      if (at >= 0) {
        if (q + d < 0 || q + d >= size || wall[q + d] || bs.includes(q + d)) continue;
        nb = bs.slice();
        nb[at] = q + d;
        nb.sort((a, b) => a - b);
        move = letter.toUpperCase();
      }
      const k = keyOfMove(q, nb);
      const seen = best.get(k);
      if (seen !== undefined && sg[seen]! <= sg[s]! + 1) continue;
      const t = sp.length;
      sp.push(q);
      sb.push(nb);
      sg.push(sg[s]! + 1);
      parent.push(s);
      step.push(move);
      best.set(k, t);
      const e = est(nb);
      heapPush(heap, [sg[s]! + 1 + e, e, seq++, t]);
    }
  }
  return null;
}

/** One level's moves: rooms first, then the whole level, then the move-based fallback; '' when nothing solves it. */
function solveLevel(text: string, work: { left: number }): string {
  const level = parseLevel(text);
  const goalSet = new Set(level.goals);
  if (level.boxes.length === 0 || level.boxes.every((b) => goalSet.has(b))) return '';
  const byRooms = solveByRooms(level, work);
  if (byRooms !== null) return byRooms.moves;
  const whole = solvePushAStar(level, WHOLE_EXPANSIONS, work);
  if (whole !== null) return whole.moves;
  return solveMoveAStar(level, MOVE_EXPANSIONS, work) ?? '';
}

const work = { left: GLOBAL_EXPANSIONS };
for (const id of readdirSync(I).sort()) {
  const moves = solveLevel(readFileSync(join(I, id, 'level.txt'), 'utf8'), work);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`);
}
