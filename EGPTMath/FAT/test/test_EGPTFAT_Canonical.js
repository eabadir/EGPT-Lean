#!/usr/bin/env node

/**
 * Canonical FAT Test Suite
 * 
 * Dedicated test suite for canonical FAT implementation (EGPTFAT.js)
 * Tests round-trip identity, spectrum correctness, and edge cases.
 * 
 * Focus: Debug and fix round-trip bugs in canonical implementation
 */

import { EGPTNumber } from '../../EGPTNumber.js';
import { ComplexEGPTNumber, TwiddleTable } from '../../EGPTComplex.js';
import { EGPTMath } from '../../EGPTMath.js';
import { fat, ifat } from '../EGPTFAT.js';

console.log('╔════════════════════════════════════════════════════════════════════════════════╗');
console.log('║  CANONICAL FAT: COMPREHENSIVE TEST SUITE                                       ║');
console.log('║  Testing EGPTFAT.js canonical implementation                                   ║');
console.log('╚════════════════════════════════════════════════════════════════════════════════╝');
console.log('');

let testsPassed = 0;
let testsTotal = 0;
let testsFailed = [];

/**
 * Test function
 */
function test(name, testFn) {
    testsTotal++;
    try {
        const result = testFn();
        if (result) {
            console.log(`✅ ${name}`);
            testsPassed++;
            return true;
        } else {
            console.log(`❌ ${name}`);
            testsFailed.push(name);
            return false;
        }
    } catch (error) {
        console.log(`❌ ${name}: ${error.message}`);
        console.log(`   Stack: ${error.stack?.split('\n').slice(0, 3).join('\n')}`);
        testsFailed.push(`${name}: ${error.message}`);
        return false;
    }
}

/**
 * Compare two ComplexEGPTNumber arrays for exact equality
 */
function arraysEqual(a, b) {
    if (a.length !== b.length) return false;
    for (let i = 0; i < a.length; i++) {
        if (!a[i].equals(b[i])) {
            return false;
        }
    }
    return true;
}

/**
 * Create deterministic signal with pattern (i % 5) + 1
 * This is the failing test case pattern
 */
function createDeterministicSignal(N) {
    const signal = [];
    for (let i = 0; i < N; i++) {
        const val = BigInt((i % 5) + 1);
        signal.push(new ComplexEGPTNumber(
            EGPTNumber.fromBigInt(val),
            EGPTNumber.fromBigInt(0n)
        ));
    }
    return signal;
}

/**
 * Create signal with pattern i + 1 (simple increment)
 */
function createIncrementSignal(N) {
    const signal = [];
    for (let i = 0; i < N; i++) {
        signal.push(new ComplexEGPTNumber(
            EGPTNumber.fromBigInt(BigInt(i + 1)),
            EGPTNumber.fromBigInt(0n)
        ));
    }
    return signal;
}

/**
 * Create signal with pattern (i * 2) % N (wrapping pattern)
 */
function createWrappingSignal(N) {
    const signal = [];
    for (let i = 0; i < N; i++) {
        const val = BigInt((i * 2) % N);
        signal.push(new ComplexEGPTNumber(
            EGPTNumber.fromBigInt(val),
            EGPTNumber.fromBigInt(0n)
        ));
    }
    return signal;
}

/**
 * Create impulse-like signal (non-zero at index 0 only, but different value)
 */
function createImpulseLikeSignal(N) {
    const signal = [];
    for (let i = 0; i < N; i++) {
        const val = i === 0 ? BigInt(N) : 0n;
        signal.push(new ComplexEGPTNumber(
            EGPTNumber.fromBigInt(val),
            EGPTNumber.fromBigInt(0n)
        ));
    }
    return signal;
}

/**
 * Create impulse signal (non-zero at specified index)
 */
function createImpulseSignal(N, index = 0) {
    const signal = [];
    for (let i = 0; i < N; i++) {
        const val = i === index ? 1n : 0n;
        signal.push(new ComplexEGPTNumber(
            EGPTNumber.fromBigInt(val),
            EGPTNumber.fromBigInt(0n)
        ));
    }
    return signal;
}

/**
 * Create DC signal (all ones)
 */
function createDCSignal(N) {
    const signal = [];
    for (let i = 0; i < N; i++) {
        signal.push(new ComplexEGPTNumber(
            EGPTNumber.fromBigInt(1n),
            EGPTNumber.fromBigInt(0n)
        ));
    }
    return signal;
}

/**
 * Create alternating signal [1, -1, 1, -1, ...]
 */
function createAlternatingSignal(N) {
    const signal = [];
    for (let i = 0; i < N; i++) {
        const val = i % 2 === 0 ? 1n : -1n;
        signal.push(new ComplexEGPTNumber(
            EGPTNumber.fromBigInt(val),
            EGPTNumber.fromBigInt(0n)
        ));
    }
    return signal;
}

/**
 * Create zero signal (all zeros)
 */
function createZeroSignal(N) {
    const signal = [];
    for (let i = 0; i < N; i++) {
        signal.push(new ComplexEGPTNumber(
            EGPTNumber.fromBigInt(0n),
            EGPTNumber.fromBigInt(0n)
        ));
    }
    return signal;
}

/**
 * Create unit-circle signal (twiddle values from N-gon)
 * This is the CORRECT test for phase-based EQFT
 * @param {number} N - Signal length (power of 2)
 * @param {Array<number>} indices - Optional array of twiddle indices to use (cycles if shorter than N)
 * @returns {Array<ComplexEGPTNumber>} Signal with twiddle values
 */
function createUnitCircleSignal(N, indices = null) {
    const table = new TwiddleTable(N, 'circular');
    const signal = [];
    for (let i = 0; i < N; i++) {
        const idx = indices ? indices[i % indices.length] : i;
        signal.push(table.getTwiddle(idx));
    }
    return signal;
}

/**
 * Create mixed unit-circle signal (multiple twiddles added together)
 * All components are from the unit circle, so result should be exact
 * @param {number} N - Signal length (power of 2)
 * @returns {Array<ComplexEGPTNumber>} Signal with mixed twiddle values
 */
function createMixedTwiddleSignal(N) {
    const table = new TwiddleTable(N, 'circular');
    const signal = [];
    for (let i = 0; i < N; i++) {
        // Mix twiddles: ω^i + ω^(2i) (both unit circle)
        const t1 = table.getTwiddle(i);
        const t2 = table.getTwiddle((2 * i) % N);
        signal.push(t1.add(t2));
    }
    return signal;
}

// =============================================================================
// Test Group 1: Failing Test Case - Deterministic Round-Trip
// =============================================================================

console.log('═'.repeat(80));
console.log('Test Group 1: Failing Test Case - Deterministic Round-Trip');
console.log('─'.repeat(80));

const failingSizes = [8, 16, 32];
for (const N of failingSizes) {
    test(`Failing case: Round-trip N=${N} (pattern (i % 5) + 1)`, () => {
        const signal = createDeterministicSignal(N);
        const spectrum = fat(signal);
        const reconstructed = ifat(spectrum, true);
        return arraysEqual(signal, reconstructed);
    });
}

// =============================================================================
// Test Group 2: Deterministic Round-Trip Tests (Various Patterns)
// =============================================================================

console.log('\n═'.repeat(80));
console.log('Test Group 2: Deterministic Round-Trip Tests');
console.log('─'.repeat(80));

const deterministicSizes = [4, 8, 16];
for (const N of deterministicSizes) {
    test(`Round-trip N=${N} (pattern: increment i+1)`, () => {
        const signal = createIncrementSignal(N);
        const spectrum = fat(signal);
        const reconstructed = ifat(spectrum, true);
        return arraysEqual(signal, reconstructed);
    });
    
    test(`Round-trip N=${N} (pattern: wrapping (i*2)%N)`, () => {
        const signal = createWrappingSignal(N);
        const spectrum = fat(signal);
        const reconstructed = ifat(spectrum, true);
        return arraysEqual(signal, reconstructed);
    });
    
    test(`Round-trip N=${N} (pattern: impulse-like at 0)`, () => {
        const signal = createImpulseLikeSignal(N);
        const spectrum = fat(signal);
        const reconstructed = ifat(spectrum, true);
        return arraysEqual(signal, reconstructed);
    });
}

// =============================================================================
// Test Group 3: Spectrum Verification Tests
// =============================================================================

console.log('\n═'.repeat(80));
console.log('Test Group 3: Spectrum Verification');
console.log('─'.repeat(80));

for (const N of [4, 8, 16]) {
    test(`Spectrum conjugate symmetry N=${N}`, () => {
        const signal = createDeterministicSignal(N);
        const spectrum = fat(signal);
        
        // For real input, spectrum should be conjugate symmetric
        // X[k] = X*[N-k] for k = 1..N/2-1
        for (let k = 1; k < N / 2; k++) {
            const Xk = spectrum[k];
            const XNk = spectrum[N - k];
            
            // Real parts should be equal
            if (!Xk.real.equals(XNk.real)) {
                return false;
            }
            
            // Imaginary parts should be negatives
            const negXNk_imag = XNk.imag.clone().scalarMultiply(-1n);
            if (!Xk.imag.equals(negXNk_imag)) {
                return false;
            }
        }
        return true;
    });
}

// =============================================================================
// Test Group 4: Edge Case Round-Trips
// =============================================================================

console.log('\n═'.repeat(80));
console.log('Test Group 4: Edge Case Round-Trips');
console.log('─'.repeat(80));

for (const N of [4, 8, 16]) {
    test(`Round-trip N=${N} (zero signal)`, () => {
        const signal = createZeroSignal(N);
        const spectrum = fat(signal);
        const reconstructed = ifat(spectrum, true);
        return arraysEqual(signal, reconstructed);
    });
    
    test(`Round-trip N=${N} (DC signal - all ones)`, () => {
        const signal = createDCSignal(N);
        const spectrum = fat(signal);
        const reconstructed = ifat(spectrum, true);
        return arraysEqual(signal, reconstructed);
    });
    
    test(`Round-trip N=${N} (alternating [1,-1,1,-1,...])`, () => {
        const signal = createAlternatingSignal(N);
        const spectrum = fat(signal);
        const reconstructed = ifat(spectrum, true);
        return arraysEqual(signal, reconstructed);
    });
    
    // Single non-zero at different indices
    for (let idx = 0; idx < Math.min(N, 4); idx++) {
        test(`Round-trip N=${N} (impulse at index ${idx})`, () => {
            const signal = createImpulseSignal(N, idx);
            const spectrum = fat(signal);
            const reconstructed = ifat(spectrum, true);
            return arraysEqual(signal, reconstructed);
        });
    }
}

// =============================================================================
// Test Group 5: Unnormalized Round-Trip
// =============================================================================

console.log('\n═'.repeat(80));
console.log('Test Group 5: Unnormalized Round-Trip');
console.log('─'.repeat(80));

for (const N of [4, 8, 16]) {
    test(`Unnormalized round-trip N=${N} (should equal N * original)`, () => {
        const signal = createDeterministicSignal(N);
        const spectrum = fat(signal);
        const reconstructed_unnorm = ifat(spectrum, false);
        
        // Unnormalized result should be N * original
        const N_big = EGPTNumber.fromBigInt(BigInt(N));
        for (let i = 0; i < N; i++) {
            const expected_real = EGPTMath.multiply(signal[i].real, N_big);
            const expected_imag = EGPTMath.multiply(signal[i].imag, N_big);
            const expected = new ComplexEGPTNumber(expected_real, expected_imag);
            if (!reconstructed_unnorm[i].equals(expected)) {
                return false;
            }
        }
        return true;
    });
}

// =============================================================================
// Test Group 6: Recursive Structure Tests (for debugging)
// =============================================================================

console.log('\n═'.repeat(80));
console.log('Test Group 6: Recursive Structure Tests');
console.log('─'.repeat(80));

// Test small sizes to isolate recursive levels
test(`Round-trip N=2 (base recursive size)`, () => {
    const signal = createDeterministicSignal(2);
    const spectrum = fat(signal);
    const reconstructed = ifat(spectrum, true);
    return arraysEqual(signal, reconstructed);
});

test(`Round-trip N=4 (first recursive level)`, () => {
    const signal = createDeterministicSignal(4);
    const spectrum = fat(signal);
    const reconstructed = ifat(spectrum, true);
    return arraysEqual(signal, reconstructed);
});

// Test with specific patterns that exercise even/odd branches
test(`Round-trip N=8 (even indices only)`, () => {
    const signal = [];
    for (let i = 0; i < 8; i++) {
        const val = i % 2 === 0 ? BigInt(i + 1) : 0n;
        signal.push(new ComplexEGPTNumber(
            EGPTNumber.fromBigInt(val),
            EGPTNumber.fromBigInt(0n)
        ));
    }
    const spectrum = fat(signal);
    const reconstructed = ifat(spectrum, true);
    return arraysEqual(signal, reconstructed);
});

test(`Round-trip N=8 (odd indices only)`, () => {
    const signal = [];
    for (let i = 0; i < 8; i++) {
        const val = i % 2 === 1 ? BigInt(i + 1) : 0n;
        signal.push(new ComplexEGPTNumber(
            EGPTNumber.fromBigInt(val),
            EGPTNumber.fromBigInt(0n)
        ));
    }
    const spectrum = fat(signal);
    const reconstructed = ifat(spectrum, true);
    return arraysEqual(signal, reconstructed);
});

// =============================================================================
// Test Group 7: Unit-Circle Signals (Phase-Based EQFT)
// =============================================================================

console.log('\n' + '═'.repeat(80));
console.log('Test Group 7: Unit-Circle Signals (Phase-Based EQFT)');
console.log('─'.repeat(80));
console.log('NOTE: These tests use ONLY unit-circle values (twiddles from N-gon)');
console.log('      These are the CORRECT signals for exact phase-based EQFT arithmetic');
console.log('');

for (const N of [4, 8, 16, 32]) {
    test(`Unit-circle round-trip N=${N} (twiddle signal)`, () => {
        const signal = createUnitCircleSignal(N);
        const spectrum = fat(signal);
        const reconstructed = ifat(spectrum);
        return arraysEqual(signal, reconstructed);
    });
    
    test(`Unit-circle round-trip N=${N} (mixed twiddles)`, () => {
        const signal = createMixedTwiddleSignal(N);
        const spectrum = fat(signal);
        const reconstructed = ifat(spectrum);
        return arraysEqual(signal, reconstructed);
    });

    test(`Unit-circle round-trip N=${N} (DC signal - all ones)`, () => {
        const signal = createUnitCircleSignal(N, [0]); // All ω^0 = (1, 0)
        const spectrum = fat(signal);
        const reconstructed = ifat(spectrum);
        return arraysEqual(signal, reconstructed);
    });
    
    test(`Unit-circle round-trip N=${N} (impulse - single twiddle)`, () => {
        const table = new TwiddleTable(N, 'circular');
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
        return arraysEqual(signal, reconstructed);
    });
}

// =============================================================================
// Test Summary
// =============================================================================

console.log('\n' + '═'.repeat(80));
console.log('TEST SUMMARY');
console.log('═'.repeat(80));
console.log(`Total tests: ${testsTotal}`);
console.log(`Passed: ${testsPassed}`);
console.log(`Failed: ${testsFailed.length}`);

if (testsFailed.length > 0) {
    console.log('\nFailed tests:');
    testsFailed.forEach(name => console.log(`  ❌ ${name}`));
}

console.log(`\nSuccess rate: ${((testsPassed / testsTotal) * 100).toFixed(1)}%`);

// Exit with appropriate code
if (testsFailed.length === 0) {
    console.log('\n✅ All tests passed!');
    process.exit(0);
} else {
    console.log('\n❌ Some tests failed');
    process.exit(1);
}

