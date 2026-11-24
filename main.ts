// A complete interpreter for make.fun's tiny stack ISA: 32-bit wrapping integers, a 256-value data stack, a
// 64-deep call stack, 256 words of memory, input/output, all ten traps with their own exit codes, and the step
// and output limits, matching the reference VM's behaviour on every edge case (wrapping multiply, signed and
// unsigned division, shift counts, sign extension, traps keeping the output written before them).
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// One digit per opcode byte 0x00..0x53: immediate bytes, values popped, values pushed.
const IM = '014' + '0'.repeat(45) + '2222' + '0'.repeat(32);
const PO = '00011223' + '00000000' + '22222221' + '22212220' + '222' + '0'.repeat(13) + '0110' + '0' + '0'.repeat(11) + '12' + '0'.repeat(14) + '1101';
const PU = '01102233' + '00000000' + '11111111' + '11111110' + '111' + '0'.repeat(29) + '10' + '0'.repeat(14) + '0010';

function run(p: Uint8Array, inp: Uint8Array): { out: Uint8Array; code: number } {
  const n = p.length;
  const D = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0;
  let csp = 0;
  let olen = 0;
  let ip = 0;
  let pc = 0;
  let steps = 0;
  const end = (code: number): { out: Uint8Array; code: number } => ({ out: out.slice(0, olen), code });
  for (;;) {
    if (steps === 1e6) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = p[pc];
    const ok = op < 8 || (op > 15 && op < 35 && op !== 31) || (op > 47 && op < 53) || op === 64 || op === 65 || (op > 79 && op < 84);
    if (!ok) return end(5);
    const imm = IM.charCodeAt(op) - 48;
    if (pc + imm >= n) return end(9);
    steps++;
    const po = PO.charCodeAt(op) - 48;
    if (sp < po) return end(2);
    if (sp - po + (PU.charCodeAt(op) - 48) > 256) return end(3);
    const nx = pc + 1 + imm;
    pc = nx;
    if (op > 15 && op < 35 && op !== 23 && op !== 27) {
      const b = D[sp - 1];
      const a = D[sp - 2];
      let r: number;
      if (op === 16) r = (a + b) | 0;
      else if (op === 17) r = (a - b) | 0;
      else if (op === 18) r = Math.imul(a, b);
      else if (op === 19) {
        if (b === 0) return end(4);
        r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
      } else if (op === 20) {
        if (b === 0) return end(4);
        r = b === -1 ? 0 : a % b | 0;
      } else if (op === 21) {
        if (b === 0) return end(4);
        r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
      } else if (op === 22) {
        if (b === 0) return end(4);
        r = (a >>> 0) % (b >>> 0) | 0;
      } else if (op === 24) r = a & b;
      else if (op === 25) r = a | b;
      else if (op === 26) r = a ^ b;
      else if (op === 28) r = a << (b & 31);
      else if (op === 29) r = a >> (b & 31);
      else if (op === 30) r = (a >>> (b & 31)) | 0;
      else if (op === 32) r = a === b ? 1 : 0;
      else if (op === 33) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
      D[sp - 2] = r;
      sp--;
      continue;
    }
    switch (op) {
      case 0:
        return end(0);
      case 1:
        D[sp++] = (p[nx - 1] << 24) >> 24;
        break;
      case 2:
        D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24);
        break;
      case 3:
        sp--;
        break;
      case 4:
        D[sp] = D[sp - 1];
        sp++;
        break;
      case 5: {
        const t = D[sp - 1];
        D[sp - 1] = D[sp - 2];
        D[sp - 2] = t;
        break;
      }
      case 6:
        D[sp] = D[sp - 2];
        sp++;
        break;
      case 7: {
        const a = D[sp - 3];
        D[sp - 3] = D[sp - 2];
        D[sp - 2] = D[sp - 1];
        D[sp - 1] = a;
        break;
      }
      case 23:
        D[sp - 1] = -D[sp - 1] | 0;
        break;
      case 27:
        D[sp - 1] = ~D[sp - 1];
        break;
      case 48:
      case 49:
      case 50: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        if (op === 48) pc = nx + rel;
        else {
          const v = D[--sp];
          if ((op === 49) === (v === 0)) pc = nx + rel;
        }
        break;
      }
      case 51:
        if (csp === 64) return end(7);
        C[csp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 52:
        if (csp === 0) return end(8);
        pc = C[--csp];
        break;
      case 64: {
        const a = D[sp - 1];
        if (a < 0 || a > 255) return end(6);
        D[sp - 1] = M[a];
        break;
      }
      case 65: {
        const a = D[sp - 1];
        if (a < 0 || a > 255) return end(6);
        M[a] = D[sp - 2];
        sp -= 2;
        break;
      }
      case 80: {
        const s = String(D[sp - 1]);
        if (olen + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 81:
        if (olen === 65536) return end(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 82:
        D[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 83:
        return end(D[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
