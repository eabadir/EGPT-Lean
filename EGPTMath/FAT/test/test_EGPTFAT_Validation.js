#!/usr/bin/env node

/**
 * EGPTFAT Validation Suite - 100% Unit-Circle Focus
 * 
 * Mirrors Foundation/proofs/eqft-validation/ but tests production EGPTFAT.js
 * Uses ONLY unit-circle signals (twiddle values) for exact arithmetic validation
 * 
 * This is the CORRECT way to test phase-based EQFT: with unit-circle signals only.
 */

import { EGPTNumber } from '../../EGPTNumber.js';
import { ComplexEGPTNumber, TwiddleTable } from '../../EGPTComplex.js';
import { EGPTMath } from '../../EGPTMath.js';
import { fat, ifat, qft, iqft } from '../EGPTFAT.js';

console.log('╔════════════════════════════════════════════════════════════════════════════════╗');
console.log('║  EGPTFAT VALIDATION SUITE - Unit-Circle Signals Only                           ║');
console.log('║  Tests production EGPTFAT.js with validated Foundation proof patterns          ║');
console.log('╚════════════════════════════════════════════════════════════════════════════════╝');
console.log('');

// Test tracking
let totalTests = 0;
let passedTests = 0;

function test(name, fn) {
    totalTests++;
    try {
        const result = fn();
        if (result === true) {
            console.log(`✅ ${name}`);
            passedTests++;
            return true;
        } else {
            console.log(`❌ ${name}: Test returned false`);
            return false;
        }
    } catch (error) {
        console.log(`❌ ${name}: ${error.message}`);
        if (error.stack) {
            console.log(`   Stack: ${error.stack.split('\n').slice(0, 3).join('\n   ')}`);
        }
        return false;
    }
}

// =============================================================================
// Test 1: Phase Ring Laws (via TwiddleTable multiply operations)
// =============================================================================

console.log('═'.repeat(80));
console.log('Test 1: Phase Ring Laws - Twiddle Multiply Operations');
console.log('─'.repeat(80));
console.log('');

for (const N of [8, 16, 32]) {
    test(`Phase multiply commutativity N=${N}`, () => {
        const table = new TwiddleTable(N); // Use same topology as EGPTFAT.js
        const w1 = table.getTwiddle(1);
        const w2 = table.getTwiddle(2);
        
        const ab = w1.multiply(w2);
        const ba = w2.multiply(w1);
        
        return ab.equals(ba);
    });
    
    test(`Phase multiply associativity N=${N}`, () => {
        const table = new TwiddleTable(N); // Use same topology as EGPTFAT.js
        const w1 = table.getTwiddle(1);
        const w2 = table.getTwiddle(2);
        const w3 = table.getTwiddle(3);
        
        const ab_c = w1.multiply(w2).multiply(w3);
        const a_bc = w1.multiply(w2.multiply(w3));
        
        return ab_c.equals(a_bc);
    });
    
    test(`Phase multiply identity N=${N} (ω^0 = 1)`, () => {
        const table = new TwiddleTable(N); // Use same topology as EGPTFAT.js
        const w0 = table.getTwiddle(0); // Identity element
        const wk = table.getTwiddle(5);
        
        const prod = wk.multiply(w0);
        
        return prod.equals(wk);
    });
}

// =============================================================================
// Test 2: Round-Trip with Unit-Circle Signals (Impulse)
// =============================================================================

console.log('\n' + '═'.repeat(80));
console.log('Test 2: Round-Trip - Impulse Signal (Unit-Circle)');
console.log('─'.repeat(80));
console.log('');

for (const N of [4, 8, 16, 32, 64]) {
    test(`Impulse round-trip N=${N}`, () => {
        const table = new TwiddleTable(N); // Use same topology as EGPTFAT.js
        const ZERO = EGPTNumber.fromBigInt(0n);
        const signal = [];
        
        for (let i = 0; i < N; i++) {
            if (i === 0) {
                signal.push(table.getTwiddle(0)); // ω^0 = (1, 0)
            } else {
                signal.push(new ComplexEGPTNumber(ZERO, ZERO));
            }
        }
        
        const spectrum = fat(signal);
        const reconstructed = ifat(spectrum);
        
        for (let i = 0; i < N; i++) {
            if (!signal[i].equals(reconstructed[i])) {
                console.error(`   [DEBUG] Index ${i} mismatch:`);
                console.error(`     Expected: ${signal[i].toString()}`);
                console.error(`     Got:      ${reconstructed[i].toString()}`);
                throw new Error(`Impulse round-trip failed at index ${i}`);
            }
        }
        return true;
    });
}

// =============================================================================
// Test 3: Round-Trip - DC Signal (All Ones, Unit-Circle)
// =============================================================================

console.log('\n' + '═'.repeat(80));
console.log('Test 3: Round-Trip - DC Signal (All Ones)');
console.log('─'.repeat(80));
console.log('');

for (const N of [4, 8, 16, 32, 64]) {
    test(`DC signal round-trip N=${N}`, () => {
        const table = new TwiddleTable(N); // Use same topology as EGPTFAT.js
        const ONE = table.getTwiddle(0); // ω^0 = (1, 0)
        const signal = Array.from({ length: N }, () => ONE);
        
        const spectrum = fat(signal);
        const reconstructed = ifat(spectrum);
        
        for (let i = 0; i < N; i++) {
            if (!signal[i].equals(reconstructed[i])) {
                console.error(`   [DEBUG] Index ${i} mismatch:`);
                console.error(`     Expected: ${signal[i].toString()}`);
                console.error(`     Got:      ${reconstructed[i].toString()}`);
                throw new Error(`DC round-trip failed at index ${i}`);
            }
        }
        return true;
    });
}

// =============================================================================
// Test 4: Round-Trip - Mixed Twiddle Signal
// =============================================================================

console.log('\n' + '═'.repeat(80));
console.log('Test 4: Round-Trip - Mixed Twiddle Signal (Unit-Circle)');
console.log('─'.repeat(80));
console.log('NOTE: This test uses signals composed of multiple twiddle values');
console.log('');

for (const N of [4, 8, 16, 32]) {
    test(`Mixed twiddle round-trip N=${N} (alternating ω^0 and ω^1)`, () => {
        const table = new TwiddleTable(N); // Use same topology as EGPTFAT.js
        const signal = [];
        
        for (let i = 0; i < N; i++) {
            // Alternate between ω^0 and ω^1
            signal.push(table.getTwiddle(i % 2));
        }
        
        const spectrum = fat(signal);
        const reconstructed = ifat(spectrum);
        
        for (let i = 0; i < N; i++) {
            if (!signal[i].equals(reconstructed[i])) {
                console.error(`   [DEBUG N=${N}] Index ${i} mismatch:`);
                console.error(`     Expected: ${signal[i].toString()}`);
                console.error(`     Got:      ${reconstructed[i].toString()}`);
                throw new Error(`Mixed twiddle round-trip failed at index ${i}`);
            }
        }
        return true;
    });
    
    test(`Mixed twiddle round-trip N=${N} (sequential twiddles)`, () => {
        const table = new TwiddleTable(N); // Use same topology as EGPTFAT.js
        const signal = [];
        
        // Use sequential twiddles: [ω^0, ω^1, ω^2, ...]
        for (let i = 0; i < N; i++) {
            signal.push(table.getTwiddle(i));
        }
        
        const spectrum = fat(signal);
        const reconstructed = ifat(spectrum);
        
        for (let i = 0; i < N; i++) {
            if (!signal[i].equals(reconstructed[i])) {
                console.error(`   [DEBUG N=${N}] Index ${i} mismatch:`);
                console.error(`     Expected: ${signal[i].toString()}`);
                console.error(`     Got:      ${reconstructed[i].toString()}`);
                throw new Error(`Sequential twiddle round-trip failed at index ${i}`);
            }
        }
        return true;
    });
}

// =============================================================================
// Test 5: QFT Interface Tests
// =============================================================================

console.log('\n' + '═'.repeat(80));
console.log('Test 5: QFT/IQFT Interface (Phase-Space Operations)');
console.log('─'.repeat(80));
console.log('');

for (const N of [4, 8, 16]) {
    test(`QFT/IQFT round-trip N=${N}`, () => {
        const table = new TwiddleTable(N); // Use same topology as EGPTFAT.js
        const signal = [];
        
        for (let i = 0; i < N; i++) {
            signal.push(table.getTwiddle(i % 4));
        }
        
        const spectrum = qft(signal);
        const reconstructed = iqft(spectrum);
        
        for (let i = 0; i < N; i++) {
            if (!signal[i].equals(reconstructed[i])) {
                throw new Error(`QFT round-trip failed at index ${i}`);
            }
        }
        return true;
    });
}

// =============================================================================
// Test Summary
// =============================================================================

console.log('\n' + '═'.repeat(80));
console.log('VALIDATION SUMMARY');
console.log('═'.repeat(80));
console.log(`Total tests: ${totalTests}`);
console.log(`Passed: ${passedTests}`);
console.log(`Failed: ${totalTests - passedTests}`);
console.log('═'.repeat(80));

if (passedTests === totalTests) {
    console.log('\n✅ ALL VALIDATION TESTS PASSED - EGPTFAT.js is correctly implementing phase-based EQFT\n');
    process.exit(0);
} else {
    console.log(`\n❌ ${totalTests - passedTests} VALIDATION TEST(S) FAILED\n`);
    process.exit(1);
}

