// tiny-stack-vm: an exact interpreter of make.fun's tiny stack ISA v1 (the kit's
// generator/subject/ISA.md). One run answers every instance: for /input/<id>/
// {program.bin,input.bin} it writes /output/<id>/stdout.bin (the bytes the
// program wrote) and /output/<id>/exit.txt (its exit code, decimal).
// One INFO word per opcode byte packs the immediate size, pops and pushes, so
// each step checks the tables once; execution dispatches on the raw opcode.
// Step order is ISA.md's "One step": traps keep the bytes already written and
// the trapping instruction writes none of its own. No clock, no randomness,
// nothing read but the input files.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// info = imm | pops<<8 | pushes<<16; a negative word = not an opcode (trap 5).
const INFO = new Int32Array(256).fill(-1);
for (const [b, i, p, s] of [
  [0x00, 0, 0, 0], [0x01, 1, 0, 1], [0x02, 4, 0, 1], [0x03, 0, 1, 0], [0x04, 0, 1, 2],
  [0x05, 0, 2, 2], [0x06, 0, 2, 3], [0x07, 0, 3, 3],
  [0x10, 0, 2, 1], [0x11, 0, 2, 1], [0x12, 0, 2, 1], [0x13, 0, 2, 1], [0x14, 0, 2, 1],
  [0x15, 0, 2, 1], [0x16, 0, 2, 1], [0x17, 0, 1, 1], [0x18, 0, 2, 1], [0x19, 0, 2, 1],
  [0x1a, 0, 2, 1], [0x1b, 0, 1, 1], [0x1c, 0, 2, 1], [0x1d, 0, 2, 1], [0x1e, 0, 2, 1],
  [0x20, 0, 2, 1], [0x21, 0, 2, 1], [0x22, 0, 2, 1],
  [0x30, 2, 0, 0], [0x31, 2, 1, 0], [0x32, 2, 1, 0], [0x33, 2, 0, 0], [0x34, 0, 0, 0],
  [0x40, 0, 1, 1], [0x41, 0, 2, 0],
  [0x50, 0, 1, 0], [0x51, 0, 1, 0], [0x52, 0, 0, 1], [0x53, 0, 1, 0],
]) INFO[b] = i | p << 8 | s << 16;

// PRINT's digit scratch: an int32 is at most "-2147483648", 11 bytes.
const DIG = new Uint8Array(12);

// Runs one program to its end: what it wrote and its exit code (a trap's code).
function run(p: Uint8Array, inp: Uint8Array): { out: Uint8Array; exit: number } {
  const n = p.length;
  const D = new Int32Array(256); // data stack
  let sp = 0;
  const C = new Int32Array(64); // return addresses
  let csp = 0;
  const M = new Int32Array(256); // memory words
  const out = new Uint8Array(65536);
  let olen = 0;
  let ip = 0;
  let pc = 0;
  let steps = 0;
  const stop = (exit: number) => ({ out: out.subarray(0, olen), exit });
  for (;;) {
    if (steps === 1000000) return stop(10);
    if (pc < 0 || pc >= n) return stop(9);
    const info = INFO[p[pc]];
    if (info < 0) return stop(5);
    const imm = info & 255;
    if (pc + imm >= n) return stop(9); // immediate cut off by the end
    steps++;
    const next = pc + 1 + imm;
    const pops = info >> 8 & 255;
    if (sp < pops) return stop(2);
    if (sp - pops + (info >> 16 & 255) > 256) return stop(3);
    const op = p[pc];
    pc = next;
    switch (op) {
      case 0x00: return stop(0);
      case 0x01: D[sp++] = p[next - 1] << 24 >> 24; break;
      case 0x02:
        D[sp++] = p[next - 4] | p[next - 3] << 8 | p[next - 2] << 16 | p[next - 1] << 24;
        break;
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp - 1]; sp++; break;
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 0x06: D[sp] = D[sp - 2]; sp++; break;
      case 0x07: {
        const t = D[sp - 3];
        D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = t;
        break;
      }
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break;
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r: number;
        switch (op) {
          case 0x10: r = a + b | 0; break;
          case 0x11: r = a - b | 0; break;
          case 0x12: r = Math.imul(a, b); break;
          case 0x13:
            if (b === 0) return stop(4);
            r = a === -2147483648 && b === -1 ? a : a / b | 0;
            break;
          case 0x14:
            if (b === 0) return stop(4);
            r = b === -1 ? 0 : a % b | 0;
            break;
          case 0x15: if (b === 0) return stop(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break;
          case 0x16: if (b === 0) return stop(4); r = (a >>> 0) % (b >>> 0) | 0; break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break;
          case 0x1d: r = a >> (b & 31); break;
          case 0x1e: r = (a >>> (b & 31)) | 0; break;
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          default: r = a >>> 0 < b >>> 0 ? 1 : 0; break;
        }
        sp -= 2; D[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((p[next - 2] | p[next - 1] << 8) << 16) >> 16;
        let take = op === 0x30;
        if (!take) { const v = D[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = next + rel;
        break;
      }
      case 0x33:
        if (csp === 64) return stop(7);
        C[csp++] = next;
        pc = p[next - 2] | p[next - 1] << 8;
        break;
      case 0x34:
        if (csp === 0) return stop(8);
        pc = C[--csp];
        break;
      case 0x40: {
        const a = D[sp - 1];
        if (a < 0 || a > 255) return stop(6);
        D[sp - 1] = M[a];
        break;
      }
      case 0x41: {
        const a = D[sp - 1];
        if (a < 0 || a > 255) return stop(6);
        M[a] = D[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: {
        const v = D[sp - 1];
        const neg = v < 0;
        let u = neg ? -v : v;
        let m = 0;
        do { DIG[m++] = 48 + u % 10; u = (u - u % 10) / 10; } while (u > 0);
        const len = m + (neg ? 1 : 0);
        if (olen + len > 65536) return stop(11);
        sp--;
        if (neg) out[olen++] = 45;
        while (m > 0) out[olen++] = DIG[--m];
        break;
      }
      case 0x51:
        if (olen + 1 > 65536) return stop(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 0x52: D[sp++] = ip < inp.length ? inp[ip++] : -1; break;
      case 0x53: return stop(D[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(
    new Uint8Array(readFileSync(join(I, id, 'program.bin'))),
    new Uint8Array(readFileSync(join(I, id, 'input.bin'))),
  );
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), r.exit + '\n');
}
