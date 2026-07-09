#!/usr/bin/env node

import { EGPTNumber } from '../EGPTNumber.js';
import { EGPTMath } from '../EGPTMath.js';
import { ComplexEGPTNumber, TwiddleTable } from '../EGPTComplex.js';

console.log('Testing conditionalEntropyVector for n-gon level mismatch\n');

// Case: We have ω₈¹ (8-gon native, phase 1/8) 
//       at a recursion level using 4-gon twiddles

const table8 = new TwiddleTable(8);
const table4 = new TwiddleTable(4);

const omega8_1 = table8.getTwiddle(1); // phase 1/8
const omega4_0 = table4.getTwiddle(0); // phase 0

console.log('Signal value: ω₈¹ (8-gon native)');
console.log('  Phase:', omega8_1.getPhase().toString());
console.log('  Real:', omega8_1.real.toString());
console.log('  Imag:', omega8_1.imag.toString());

console.log('\nTwiddle: ω₄⁰ (4-gon)');
console.log('  Phase:', omega4_0.getPhase().toString());

// What should k_en and p_en be?
// Based on your hint: "where a wave with period N at twiddle omega"

// Try: k_en = signal's phase, p_en = twiddle's phase?
const k_en = omega8_1.getPhase(); // 1/8
const p_en = omega4_0.getPhase(); // 0

console.log('\nTrying conditionalEntropyVector(signal_phase, twiddle_phase):');
console.log(`  k_en = ${k_en.toString()}`);
console.log(`  p_en = ${p_en.toString()}`);

// This won't work because p_en=0 is invalid...

// Maybe we need magnitude? Or the actual values?
console.log('\nLet me try with the actual EGPTNumber values (not phases):');

// For ω₈¹ = (1/2) + i(1/2), maybe we use the real part as k_en?
const k_en2 = omega8_1.real;
const p_en2 = EGPTNumber.fromBigInt(4n); // The 4-gon level?

console.log(`  k_en = ${k_en2.toString()} (real part of ω₈¹)`);
console.log(`  p_en = ${p_en2.toString()} (4-gon level)`);

try {
    const result = EGPTMath.conditionalEntropyVector(k_en2, p_en2);
    console.log(`  Result: ${result.toString()}`);
} catch (e) {
    console.log(`  Error: ${e.message}`);
}

// Let me try another interpretation:
console.log('\nMaybe k_en is the index and p_en is N?');
const k_en3 = EGPTNumber.fromBigInt(1n); // index 1 in 8-gon
const p_en3 = EGPTNumber.fromBigInt(8n); // 8-gon size

const result3 = EGPTMath.conditionalEntropyVector(k_en3, p_en3);
console.log(`  conditionalEntropyVector(1, 8) = ${result3.toString()}`);

console.log('\nI need clarification on what k_en and p_en should be in FFT context!');
