// A tiny stack virtual machine, written for make.fun's tiny-stack-vm-01 bounty.
// One run answers a whole set: for each folder in the input directory it reads
// program.bin and input.bin, executes the program under the ISA's exact rules
// (wrapping 32-bit arithmetic, bounded stacks and memory, numbered traps), and
// writes the program's output bytes plus its exit code to the output directory.
// The interpreter keeps its stacks in fixed typed arrays with explicit depth
// counters, so every bound in the spec is checked before each instruction runs.
import * as fs from 'node:fs';
import * as path from 'node:path';

type Outcome = { bytes: number[]; code: number };

function execute(prog: Uint8Array, input: Uint8Array): Outcome {
  const data = new Int32Array(256);
  const rets = new Int32Array(64);
  const mem = new Int32Array(256);
  const bytes: number[] = [];
  let sp = 0;
  let rsp = 0;
  let pc = 0;
  let readAt = 0;
  let steps = 0;
  const progLen = prog.length;
  const fail = (code: number): Outcome => ({ bytes, code });

  for (;;) {
    if (steps >= 1000000) return fail(10);
    if (pc < 0 || pc >= progLen) return fail(9);
    const op = prog[pc];
    const isBin = op >= 0x10 && op <= 0x22 && op !== 0x17 && op !== 0x1b && op !== 0x1f;
    const known =
      op <= 0x07 || isBin || op === 0x17 || op === 0x1b ||
      (op >= 0x30 && op <= 0x34) || op === 0x40 || op === 0x41 ||
      (op >= 0x50 && op <= 0x53);
    if (!known) return fail(5);
    let imm = 0;
    if (op === 0x01) imm = 1;
    else if (op === 0x02) imm = 4;
    else if (op >= 0x30 && op <= 0x33) imm = 2;
    if (pc + 1 + imm > progLen) return fail(9);

    // Stack bookkeeping first: how many values this opcode pops, and the net
    // change in depth once it has run. Underflow and overflow trap before it.
    let pops = 0;
    let delta = 0;
    if (op === 0x01 || op === 0x02 || op === 0x52) delta = 1;
    else if (op === 0x03 || op === 0x31 || op === 0x32 || op === 0x50 || op === 0x51 || op === 0x53) { pops = 1; delta = -1; }
    else if (op === 0x04) { pops = 1; delta = 1; }
    else if (op === 0x05) pops = 2;
    else if (op === 0x06) { pops = 2; delta = 1; }
    else if (op === 0x07) pops = 3;
    else if (isBin) { pops = 2; delta = -1; }
    else if (op === 0x17 || op === 0x1b || op === 0x40) pops = 1;
    else if (op === 0x41) { pops = 2; delta = -2; }
    if (sp < pops) return fail(2);
    if (sp + delta > 256) return fail(3);
    steps++;

    const imm16 = imm === 2 ? ((prog[pc + 1] | (prog[pc + 2] << 8)) << 16) >> 16 : 0;
    let next = pc + 1 + imm;

    if (op === 0x00) return { bytes, code: 0 };
    if (op === 0x01) data[sp++] = (prog[pc + 1] << 24) >> 24;
    else if (op === 0x02) data[sp++] = prog[pc + 1] | (prog[pc + 2] << 8) | (prog[pc + 3] << 16) | (prog[pc + 4] << 24);
    else if (op === 0x03) sp--;
    else if (op === 0x04) { data[sp] = data[sp - 1]; sp++; }
    else if (op === 0x05) { const t = data[sp - 1]; data[sp - 1] = data[sp - 2]; data[sp - 2] = t; }
    else if (op === 0x06) { data[sp] = data[sp - 2]; sp++; }
    else if (op === 0x07) { const a = data[sp - 3]; data[sp - 3] = data[sp - 2]; data[sp - 2] = data[sp - 1]; data[sp - 1] = a; }
    else if (isBin) {
      const b = data[--sp];
      const a = data[sp - 1];
      let r: number;
      if (op === 0x10) r = a + b;
      else if (op === 0x11) r = a - b;
      else if (op === 0x12) r = Math.imul(a, b);
      else if (op === 0x13) { if (b === 0) return fail(4); r = Math.trunc(a / b); }
      else if (op === 0x14) { if (b === 0) return fail(4); r = a % b; }
      else if (op === 0x15) { if (b === 0) return fail(4); r = Math.trunc((a >>> 0) / (b >>> 0)); }
      else if (op === 0x16) { if (b === 0) return fail(4); r = (a >>> 0) % (b >>> 0); }
      else if (op === 0x18) r = a & b;
      else if (op === 0x19) r = a | b;
      else if (op === 0x1a) r = a ^ b;
      else if (op === 0x1c) r = a << (b & 31);
      else if (op === 0x1d) r = a >> (b & 31);
      else if (op === 0x1e) r = a >>> (b & 31);
      else if (op === 0x20) r = a === b ? 1 : 0;
      else if (op === 0x21) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
      data[sp - 1] = r;
    }
    else if (op === 0x17) data[sp - 1] = -data[sp - 1];
    else if (op === 0x1b) data[sp - 1] = ~data[sp - 1];
    else if (op === 0x30) next = pc + 3 + imm16;
    else if (op === 0x31) { if (data[--sp] === 0) next = pc + 3 + imm16; }
    else if (op === 0x32) { if (data[--sp] !== 0) next = pc + 3 + imm16; }
    else if (op === 0x33) {
      if (rsp >= 64) return fail(7);
      rets[rsp++] = pc + 3;
      next = prog[pc + 1] | (prog[pc + 2] << 8);
    }
    else if (op === 0x34) {
      if (rsp === 0) return fail(8);
      next = rets[--rsp];
    }
    else if (op === 0x40) {
      const addr = data[sp - 1];
      if (addr < 0 || addr > 255) return fail(6);
      data[sp - 1] = mem[addr];
    }
    else if (op === 0x41) {
      const addr = data[--sp];
      const value = data[--sp];
      if (addr < 0 || addr > 255) return fail(6);
      mem[addr] = value;
    }
    else if (op === 0x50) {
      const text = String(data[--sp]);
      if (bytes.length + text.length > 65536) return fail(11);
      for (let i = 0; i < text.length; i++) bytes.push(text.charCodeAt(i));
    }
    else if (op === 0x51) {
      if (bytes.length + 1 > 65536) return fail(11);
      bytes.push(data[--sp] & 255);
    }
    else if (op === 0x52) data[sp++] = readAt < input.length ? input[readAt++] : -1;
    else if (op === 0x53) return { bytes, code: data[--sp] & 255 };
    pc = next;
  }
}

const inDir = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const outDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const ids = fs.readdirSync(inDir).sort();
for (const id of ids) {
  const prog = fs.readFileSync(path.join(inDir, id, 'program.bin'));
  const input = fs.readFileSync(path.join(inDir, id, 'input.bin'));
  const outcome = execute(new Uint8Array(prog), new Uint8Array(input));
  const target = path.join(outDir, id);
  fs.mkdirSync(target, { recursive: true });
  fs.writeFileSync(path.join(target, 'stdout.bin'), Uint8Array.from(outcome.bytes));
  fs.writeFileSync(path.join(target, 'exit.txt'), outcome.code + '\n');
}
