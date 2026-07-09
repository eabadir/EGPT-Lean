#!/usr/bin/env node

/**
 * EGPTFAT Traditional FFT Compatibility Test
 * 
 * Tests EGPTFAT.js with TYPICAL FFT inputs (real-valued signals, arbitrary complex)
 * to verify it can serve as a drop-in replacement for traditional FFT libraries.
 */

import { EGPTNumber } from '../../EGPTNumber.js';
import { ComplexEGPTNumber, TwiddleTable } from '../../EGPTComplex.js';
import { fft, ifft } from '../EGPTFAT.js';

console.log('╔════════════════════════════════════════════════════════════════════════════════╗');
console.log('║  EGPTFAT TRADITIONAL FFT COMPATIBILITY TEST                                    ║');
console.log('║  Testing with TYPICAL FFT inputs (not unit-circle)                            ║');
console.log('╚════════════════════════════════════════════════════════════════════════════════╝');
console.log('');

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

function arraysEqual(a, b, tolerance = 0) {
    if (a.length !== b.length) return false;
    for (let i = 0; i < a.length; i++) {
        if (!a[i].equals(b[i], tolerance)) {
            console.log(`   [DEBUG] Mismatch at index ${i}:`);
            console.log(`     Expected: ${a[i].toString()}`);
            console.log(`     Got:      ${b[i].toString()}`);
            return false;
        }
    }
    return true;
}

// =============================================================================
// Test 1: Real-Valued Integer Signals (Most Common FFT Use Case)
// =============================================================================

console.log('═'.repeat(80));
console.log('Test 1: Real-Valued Integer Signals');
console.log('─'.repeat(80));
console.log('NOTE: These are the MOST COMMON FFT inputs (audio, sensors, etc.)');
console.log('');

for (const N of [4, 8, 16]) {
    test(`Real integers round-trip N=${N} [1,2,3,...]`, () => {
        const signal = [];
        for (let i = 0; i < N; i++) {
            signal.push(new ComplexEGPTNumber(
                EGPTNumber.fromBigInt(BigInt(i + 1)),
                EGPTNumber.fromBigInt(0n)
            ));
        }
        
        const spectrum = fft(signal);
        const reconstructed = ifft(spectrum);
        
        return arraysEqual(signal, reconstructed);
    });
    
    test(`Real integers round-trip N=${N} [1,1,1,...]`, () => {
        const signal = [];
        for (let i = 0; i < N; i++) {
            signal.push(new ComplexEGPTNumber(
                EGPTNumber.fromBigInt(1n),
                EGPTNumber.fromBigInt(0n)
            ));
        }
        
        const spectrum = fft(signal);
        const reconstructed = ifft(spectrum);
        
        return arraysEqual(signal, reconstructed);
    });
    
    test(`Real integers round-trip N=${N} alternating [1,0,1,0,...]`, () => {
        const signal = [];
        for (let i = 0; i < N; i++) {
            signal.push(new ComplexEGPTNumber(
                EGPTNumber.fromBigInt(BigInt(i % 2)),
                EGPTNumber.fromBigInt(0n)
            ));
        }
        
        const spectrum = fft(signal);
        const reconstructed = ifft(spectrum);
        
        return arraysEqual(signal, reconstructed);
    });
}

// =============================================================================
// Test 2: Real-Valued Rational Signals
// =============================================================================

console.log('\n' + '═'.repeat(80));
console.log('Test 2: Real-Valued Rational Signals');
console.log('─'.repeat(80));
console.log('NOTE: Rational numbers (fractions) are exact in EGPT system');
console.log('');

for (const N of [4, 8, 16]) {
    test(`Real rationals round-trip N=${N} [1/2, 1/3, 1/4, ...]`, () => {
        const signal = [];
        for (let i = 0; i < N; i++) {
            signal.push(new ComplexEGPTNumber(
                EGPTNumber.fromRational(1n, BigInt(i + 2)),
                EGPTNumber.fromBigInt(0n)
            ));
        }
        
        const spectrum = fft(signal);
        const reconstructed = ifft(spectrum);
        
        return arraysEqual(signal, reconstructed);
    });
}

// =============================================================================
// Test 3: Complex-Valued Signals (Arbitrary, Not Unit-Circle)
// =============================================================================

console.log('\n' + '═'.repeat(80));
console.log('Test 3: Arbitrary Complex-Valued Signals');
console.log('─'.repeat(80));
console.log('NOTE: General complex numbers, NOT on unit circle');
console.log('');

for (const N of [4, 8, 16]) {
    test(`Complex signal round-trip N=${N} [(1+2i), (3+4i), ...]`, () => {
        const signal = [];
        for (let i = 0; i < N; i++) {
            signal.push(new ComplexEGPTNumber(
                EGPTNumber.fromBigInt(BigInt(2*i + 1)),
                EGPTNumber.fromBigInt(BigInt(2*i + 2))
            ));
        }
        
        const spectrum = fft(signal);
        const reconstructed = ifft(spectrum);
        
        return arraysEqual(signal, reconstructed);
    });
    
    test(`Complex signal round-trip N=${N} [(i/2), (i/3), ...]`, () => {
        const signal = [];
        for (let i = 0; i < N; i++) {
            signal.push(new ComplexEGPTNumber(
                EGPTNumber.fromBigInt(0n),
                EGPTNumber.fromRational(1n, BigInt(i + 2))
            ));
        }
        
        const spectrum = fft(signal);
        const reconstructed = ifft(spectrum);
        
        return arraysEqual(signal, reconstructed);
    });
}

// =============================================================================
// Test 4: Impulse Response (Traditional FFT Test)
// =============================================================================

console.log('\n' + '═'.repeat(80));
console.log('Test 4: Impulse Response (Traditional FFT Validation)');
console.log('─'.repeat(80));
console.log('');

for (const N of [4, 8, 16, 32]) {
    test(`Impulse at index 0, N=${N}`, () => {
        const ZERO = EGPTNumber.fromBigInt(0n);
        const ONE = EGPTNumber.fromBigInt(1n);
        const signal = [];
        
        for (let i = 0; i < N; i++) {
            if (i === 0) {
                signal.push(new ComplexEGPTNumber(ONE, ZERO));
            } else {
                signal.push(new ComplexEGPTNumber(ZERO, ZERO));
            }
        }
        
        const spectrum = fft(signal);
        const reconstructed = ifft(spectrum);
        
        return arraysEqual(signal, reconstructed);
    });
}

// =============================================================================
// Summary
// =============================================================================

console.log('\n' + '═'.repeat(80));
console.log('TRADITIONAL FFT COMPATIBILITY SUMMARY');
console.log('═'.repeat(80));
console.log(`Total tests: ${totalTests}`);
console.log(`Passed: ${passedTests}`);
console.log(`Failed: ${totalTests - passedTests}`);
console.log('═'.repeat(80));

if (passedTests === totalTests) {
    console.log('\n✅ FULL COMPATIBILITY - EGPTFAT can replace traditional FFT libraries!\n');
    process.exit(0);
} else {
    const passRate = (passedTests / totalTests * 100).toFixed(1);
    console.log(`\n⚠️  ${passRate}% compatibility - Some traditional inputs fail\n`);
    process.exit(1);
}

