// A tiny stack VM for make.fun's tiny stack ISA (version 1), written from the ISA spec in the kit
// (generator/subject/ISA.md). One run answers every instance of a set: it runs each <id>/program.bin
// on <id>/input.bin and writes <id>/stdout.bin and <id>/exit.txt (a halt's 0, an EXIT's low byte, or
// a trap's code). A step's checks run in the ISA's order: step limit, pc in bounds, known opcode,
// immediate fits, stack needs, own traps, effect.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

function run(P, inp) {
  const n = P.length;
  const S = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  const il = inp.length;
  let sp = 0;
  let cs = 0;
  let ol = 0;
  let pc = 0;
  let ip = 0;
  let steps = 0;
  const fin = (code) => [out.subarray(0, ol), code];
  for (;;) {
    if (steps === 1000000) return fin(10);
    if (pc < 0 || pc >= n) return fin(9);
    const op = P[pc];
    const im = op === 1 ? 1 : op === 2 ? 4 : op >= 48 && op <= 51 ? 2 : 0;
    if (im !== 0 && pc + im >= n) return fin(9);
    steps++;
    const next = pc + 1 + im;
    pc = next;
    switch (op) {
      case 0: // HALT
        return fin(0);
      case 1: // PUSH8, sign-extended
        if (sp === 256) return fin(3);
        S[sp++] = (P[next - 1] << 24) >> 24;
        break;
      case 2: // PUSH32, little-endian
        if (sp === 256) return fin(3);
        S[sp++] = P[next - 4] | (P[next - 3] << 8) | (P[next - 2] << 16) | (P[next - 1] << 24);
        break;
      case 3:
        if (sp === 0) return fin(2);
        sp--;
        break;
      case 4:
        if (sp === 0) return fin(2);
        if (sp === 256) return fin(3);
        S[sp] = S[sp - 1];
        sp++;
        break;
      case 5: {
        if (sp < 2) return fin(2);
        const t = S[sp - 1];
        S[sp - 1] = S[sp - 2];
        S[sp - 2] = t;
        break;
      }
      case 6:
        if (sp < 2) return fin(2);
        if (sp === 256) return fin(3);
        S[sp] = S[sp - 2];
        sp++;
        break;
      case 7: { // ROT: ( a b c -- b c a )
        if (sp < 3) return fin(2);
        const a = S[sp - 3];
        S[sp - 3] = S[sp - 2];
        S[sp - 2] = S[sp - 1];
        S[sp - 1] = a;
        break;
      }
      case 23:
        if (sp === 0) return fin(2);
        S[sp - 1] = -S[sp - 1];
        break;
      case 27:
        if (sp === 0) return fin(2);
        S[sp - 1] = ~S[sp - 1];
        break;
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30:
      case 32: case 33: case 34: { // binary ops
        if (sp < 2) return fin(2);
        const b = S[sp - 1];
        const a = S[sp - 2];
        let r;
        if (op === 16) r = a + b;
        else if (op === 17) r = a - b;
        else if (op === 18) r = Math.imul(a, b);
        else if (op === 19) { // DIV, truncating
          if (b === 0) return fin(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 20) { // MOD, sign of a
          if (b === 0) return fin(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 21) { // DIVU, unsigned
          if (b === 0) return fin(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 22) { // MODU
          if (b === 0) return fin(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 24) r = a & b;
        else if (op === 25) r = a | b;
        else if (op === 26) r = a ^ b;
        else if (op === 28) r = a << (b & 31);
        else if (op === 29) r = a >> (b & 31);
        else if (op === 30) r = (a >>> (b & 31)) | 0;
        else if (op === 32) r = a === b ? 1 : 0;
        else if (op === 33) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
        S[sp - 2] = r;
        sp--;
        break;
      }
      case 48: case 49: case 50: { // JMP, JZ, JNZ: signed offset from the next instruction
        const rel = ((P[next - 2] | (P[next - 1] << 8)) << 16) >> 16;
        let take = op === 48;
        if (op !== 48) {
          if (sp === 0) return fin(2);
          const v = S[--sp];
          take = op === 49 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 51: // CALL: unsigned absolute target
        if (cs === 64) return fin(7);
        C[cs++] = next;
        pc = P[next - 2] | (P[next - 1] << 8);
        break;
      case 52:
        if (cs === 0) return fin(8);
        pc = C[--cs];
        break;
      case 64: {
        if (sp === 0) return fin(2);
        const addr = S[sp - 1];
        if (addr < 0 || addr > 255) return fin(6);
        S[sp - 1] = M[addr];
        break;
      }
      case 65: {
        if (sp < 2) return fin(2);
        const addr = S[sp - 1];
        if (addr < 0 || addr > 255) return fin(6);
        M[addr] = S[sp - 2];
        sp -= 2;
        break;
      }
      case 80: {
        if (sp === 0) return fin(2);
        const s = String(S[sp - 1]);
        if (ol + s.length > 65536) return fin(11);
        for (let k = 0; k < s.length; k++) out[ol++] = s.charCodeAt(k);
        sp--;
        break;
      }
      case 81:
        if (sp === 0) return fin(2);
        if (ol === 65536) return fin(11);
        out[ol++] = S[--sp] & 255;
        break;
      case 82: // IN: next input byte, -1 past the end
        if (sp === 256) return fin(3);
        S[sp++] = ip < il ? inp[ip++] : -1;
        break;
      case 83:
        if (sp === 0) return fin(2);
        return fin(S[sp - 1] & 255);
      default:
        return fin(5);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const ans = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), ans[0]);
  writeFileSync(join(O, id, 'exit.txt'), ans[1] + '\n');
}
