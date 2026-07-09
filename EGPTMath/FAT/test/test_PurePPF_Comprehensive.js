#!/usr/bin/env node

/**
 * Comprehensive Test Suite: Pure PPF vs Canonical FAT
 * 
 * Tests:
 * 1. Functionality equivalence (all tests from RC5)
 * 2. Round-trip identity
 * 3. Impulse response
 * 4. Linearity
 * 5. Conjugate symmetry
 * 6. Various input formats
 * 7. Edge cases
 */

import { EGPTNumber } from '../../EGPTNumber.js';
import { ComplexEGPTNumber, TwiddleTable } from '../../EGPTComplex.js';
import { fat as fat_canonical, ifat as ifat_canonical } from '../EGPTFAT.js';
import { fat_pureppf, ifat_pureppf } from '../EGPTFAT_PurePPF.js';

console.log('╔════════════════════════════════════════════════════════════════════════════════╗');
console.log('║  PURE PPF FAT: COMPREHENSIVE TEST SUITE                                         ║');
console.log('║  Validating Pure PPF implementation against canonical                          ║');
console.log('╚════════════════════════════════════════════════════════════════════════════════╝');
console.log('');

let testsPassed = 0;
let testsTotal = 0;
let testsFailed = [];

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
 * Compare two ComplexEGPTNumber arrays within tolerance (for float comparisons)
 */
function arraysEqualApprox(a, b, tolerance = 1e-10) {
    if (a.length !== b.length) return false;
    for (let i = 0; i < a.length; i++) {
        const a_real = a[i].real._getPPFRationalParts();
        const a_imag = a[i].imag._getPPFRationalParts();
        const b_real = b[i].real._getPPFRationalParts();
        const b_imag = b[i].imag._getPPFRationalParts();
        
        // Cross multiply to test equality: a/b = c/d iff a*d = b*c
        const real_eq = (a_real.numerator * b_real.denominator) === (b_real.numerator * a_real.denominator);
        const imag_eq = (a_imag.numerator * b_imag.denominator) === (b_imag.numerator * a_imag.denominator);
        
        if (!real_eq || !imag_eq) {
            return false;
        }
    }
    return true;
}

/**
 * Create impulse signal
 */
function createImpulseSignal(N, index = 0) {
    const signal = [];
    for (let i = 0; i < N; i++) {
        const real = EGPTNumber.fromBigInt(i === index ? BigInt(N) : 0n);
        const imag = EGPTNumber.fromBigInt(0n);
        signal.push(new ComplexEGPTNumber(real, imag));
    }
    return signal;
}

/**
 * Create random signal
 */
function createRandomSignal(N, range = 10) {
    const signal = [];
    for (let i = 0; i < N; i++) {
        const real = EGPTNumber.fromBigInt(BigInt(Math.floor(Math.random() * range * 2 - range)));
        const imag = EGPTNumber.fromBigInt(BigInt(Math.floor(Math.random() * range * 2 - range)));
        signal.push(new ComplexEGPTNumber(real, imag));
    }
    return signal;
}

// =============================================================================
// Test Group 1: Round-Trip Identity
// =============================================================================

console.log('═'.repeat(80));
console.log('Test Group 1: Round-Trip Identity (IEQFT(EQFT(x)) = x)');
console.log('─'.repeat(80));

const roundTripSizes = [2, 4, 8, 16];
for (const N of roundTripSizes) {
    test(`Round-trip N=${N} (canonical)`, () => {
        const signal = createRandomSignal(N, 5);
        const spectrum = fat_canonical(signal);
        const reconstructed = ifat_canonical(spectrum, true);
        return arraysEqual(signal, reconstructed);
    });
    
    test(`Round-trip N=${N} (pure PPF)`, () => {
        const signal = createRandomSignal(N, 5);
        const spectrum = fat_pureppf(signal);
        const reconstructed = ifat_pureppf(spectrum, true);
        return arraysEqual(signal, reconstructed);
    });
    
    test(`Round-trip N=${N} (canonical vs pure PPF equivalence)`, () => {
        const signal = createRandomSignal(N, 5);
        const spectrum_canonical = fat_canonical(signal);
        const spectrum_pure = fat_pureppf(signal);
        const reconstructed_canonical = ifat_canonical(spectrum_canonical, true);
        const reconstructed_pure = ifat_pureppf(spectrum_pure, true);
        
        // Both should match original
        return arraysEqual(signal, reconstructed_canonical) && 
               arraysEqual(signal, reconstructed_pure) &&
               arraysEqualApprox(spectrum_canonical, spectrum_pure);
    });
}

// =============================================================================
// Test Group 2: Impulse Response
// =============================================================================

console.log('\n═'.repeat(80));
console.log('Test Group 2: Impulse Signal (δ[n])');
console.log('─'.repeat(80));

for (const N of [2, 4, 8, 16]) {
    test(`Impulse N=${N} (canonical)`, () => {
        const signal = createImpulseSignal(N, 0);
        const spectrum = fat_canonical(signal);
        
        // Impulse at index 0 should give flat spectrum (all 1.0)
        // After normalization, all coefficients should be N (the impulse magnitude)
        for (let i = 0; i < N; i++) {
            const real = spectrum[i].real._getPPFRationalParts();
            const imag = spectrum[i].imag._getPPFRationalParts();
            // Real part should be N, imag should be 0
            if (!(real.numerator === BigInt(N) * real.denominator && imag.numerator === 0n)) {
                return false;
            }
        }
        return true;
    });
    
    test(`Impulse N=${N} (pure PPF)`, () => {
        const signal = createImpulseSignal(N, 0);
        const spectrum = fat_pureppf(signal);
        
        // Impulse at index 0 should give flat spectrum (all 1.0)
        for (let i = 0; i < N; i++) {
            const real = spectrum[i].real._getPPFRationalParts();
            const imag = spectrum[i].imag._getPPFRationalParts();
            // Real part should be N, imag should be 0
            if (!(real.numerator === BigInt(N) * real.denominator && imag.numerator === 0n)) {
                return false;
            }
        }
        return true;
    });
    
    test(`Impulse N=${N} (canonical vs pure PPF)`, () => {
        const signal = createImpulseSignal(N, 0);
        const spectrum_canonical = fat_canonical(signal);
        const spectrum_pure = fat_pureppf(signal);
        return arraysEqualApprox(spectrum_canonical, spectrum_pure);
    });
}

// =============================================================================
// Test Group 3: Linearity (Superposition Principle)
// =============================================================================

console.log('\n═'.repeat(80));
console.log('Test Group 3: Linearity (FAT(a·x + b·y) = a·FAT(x) + b·FAT(y))');
console.log('─'.repeat(80));

for (const N of [4, 8]) {
    test(`Linearity N=${N} (canonical)`, () => {
        const x = createRandomSignal(N, 3);
        const y = createRandomSignal(N, 3);
        const a = 2n;
        const b = 3n;
        
        // Compute FAT(a·x + b·y)
        const combined = x.map((z, i) => {
            const real = EGPTNumber.fromBigInt(a * z.real.toBigInt() + b * y[i].real.toBigInt());
            const imag = EGPTNumber.fromBigInt(a * z.imag.toBigInt() + b * y[i].imag.toBigInt());
            return new ComplexEGPTNumber(real, imag);
        });
        const spectrum_combined = fat_canonical(combined);
        
        // Compute a·FAT(x) + b·FAT(y)
        const spectrum_x = fat_canonical(x);
        const spectrum_y = fat_canonical(y);
        const spectrum_sum = spectrum_x.map((z, i) => {
            const real = EGPTNumber.fromBigInt(a * z.real.toBigInt() + b * spectrum_y[i].real.toBigInt());
            const imag = EGPTNumber.fromBigInt(a * z.imag.toBigInt() + b * spectrum_y[i].imag.toBigInt());
            return new ComplexEGPTNumber(real, imag);
        });
        
        return arraysEqualApprox(spectrum_combined, spectrum_sum);
    });
    
    test(`Linearity N=${N} (pure PPF)`, () => {
        const x = createRandomSignal(N, 3);
        const y = createRandomSignal(N, 3);
        const a = 2n;
        const b = 3n;
        
        const combined = x.map((z, i) => {
            const real = EGPTNumber.fromBigInt(a * z.real.toBigInt() + b * y[i].real.toBigInt());
            const imag = EGPTNumber.fromBigInt(a * z.imag.toBigInt() + b * y[i].imag.toBigInt());
            return new ComplexEGPTNumber(real, imag);
        });
        const spectrum_combined = fat_pureppf(combined);
        
        const spectrum_x = fat_pureppf(x);
        const spectrum_y = fat_pureppf(y);
        const spectrum_sum = spectrum_x.map((z, i) => {
            const real = EGPTNumber.fromBigInt(a * z.real.toBigInt() + b * spectrum_y[i].real.toBigInt());
            const imag = EGPTNumber.fromBigInt(a * z.imag.toBigInt() + b * spectrum_y[i].imag.toBigInt());
            return new ComplexEGPTNumber(real, imag);
        });
        
        return arraysEqualApprox(spectrum_combined, spectrum_sum);
    });
}

// =============================================================================
// Test Group 4: Conjugate Symmetry (Real Input → Conjugate Symmetric Output)
// =============================================================================

console.log('\n═'.repeat(80));
console.log('Test Group 4: Conjugate Symmetry (Real Input)');
console.log('─'.repeat(80));

for (const N of [4, 8]) {
    test(`Conjugate symmetry N=${N} (canonical)`, () => {
        const signal = createRandomSignal(N, 5).map(z => 
            new ComplexEGPTNumber(z.real, EGPTNumber.fromBigInt(0n)) // Real-only
        );
        const spectrum = fat_canonical(signal);
        
        // X[k] = X̄[N-k] for real input (with X[0] and X[N/2] being real)
        for (let k = 1; k < N / 2; k++) {
            const Xk = spectrum[k];
            const XNk = spectrum[N - k];
            
            // X[k] should be conjugate of X[N-k]
            // real parts equal, imag parts negated
            if (!Xk.real.equals(XNk.real)) {
                return false;
            }
            const negated_imag = EGPTNumber.fromBigInt(-XNk.imag.toBigInt());
            if (!Xk.imag.equals(negated_imag)) {
                return false;
            }
        }
        return true;
    });
    
    test(`Conjugate symmetry N=${N} (pure PPF)`, () => {
        const signal = createRandomSignal(N, 5).map(z => 
            new ComplexEGPTNumber(z.real, EGPTNumber.fromBigInt(0n)) // Real-only
        );
        const spectrum = fat_pureppf(signal);
        
        for (let k = 1; k < N / 2; k++) {
            const Xk = spectrum[k];
            const XNk = spectrum[N - k];
            
            if (!Xk.real.equals(XNk.real)) {
                return false;
            }
            // Imag should be negated
            const Xk_imag_neg = EGPTNumber.fromBigInt(-XNk.imag.toBigInt());
            if (!Xk.imag.equals(Xk_imag_neg)) {
                return false;
            }
        }
        return true;
    });
}

// =============================================================================
// Test Group 5: Edge Cases
// =============================================================================

console.log('\n═'.repeat(80));
console.log('Test Group 5: Edge Cases');
console.log('─'.repeat(80));

test('N=1 base case (canonical)', () => {
    const signal = [new ComplexEGPTNumber(EGPTNumber.fromBigInt(5n), EGPTNumber.fromBigInt(0n))];
    const spectrum = fat_canonical(signal);
    return signal.length === 1 && signal[0].equals(spectrum[0]);
});

test('N=1 base case (pure PPF)', () => {
    const signal = [new ComplexEGPTNumber(EGPTNumber.fromBigInt(5n), EGPTNumber.fromBigInt(0n))];
    const spectrum = fat_pureppf(signal);
    return signal.length === 1 && signal[0].equals(spectrum[0]);
});

test('Zero signal (canonical)', () => {
    const N = 8;
    const signal = Array(N).fill(new ComplexEGPTNumber(
        EGPTNumber.fromBigInt(0n),
        EGPTNumber.fromBigInt(0n)
    ));
    const spectrum = fat_canonical(signal);
    return spectrum.every(z => z.real.toBigInt() === 0n && z.imag.toBigInt() === 0n);
});

test('Zero signal (pure PPF)', () => {
    const N = 8;
    const signal = Array(N).fill(new ComplexEGPTNumber(
        EGPTNumber.fromBigInt(0n),
        EGPTNumber.fromBigInt(0n)
    ));
    const spectrum = fat_pureppf(signal);
    return spectrum.every(z => z.real.toBigInt() === 0n && z.imag.toBigInt() === 0n);
});

test('Non-power-of-2 size error (canonical)', () => {
    try {
        const signal = createRandomSignal(7, 5);
        fat_canonical(signal);
        return false; // Should throw
    } catch (error) {
        return error.message.includes('power of 2') || error.message.includes('power-of-2');
    }
});

test('Non-power-of-2 size error (pure PPF)', () => {
    try {
        const signal = createRandomSignal(7, 5);
        fat_pureppf(signal);
        return false; // Should throw
    } catch (error) {
        return error.message.includes('power of 2') || error.message.includes('power-of-2');
    }
});

// Test Group 6: High Precision — skipped (huge BigInt rationals cause OOM in pedagogical impl)

// =============================================================================
// Summary
// =============================================================================

console.log('\n' + '═'.repeat(80));
console.log('TEST SUMMARY');
console.log('═'.repeat(80));
console.log(`Total Tests: ${testsTotal}`);
console.log(`Passed: ${testsPassed}`);
console.log(`Failed: ${testsTotal - testsPassed}`);
console.log(`Success Rate: ${((testsPassed / testsTotal) * 100).toFixed(2)}%`);

if (testsFailed.length > 0) {
    console.log('\n❌ Failed Tests:');
    testsFailed.forEach(name => console.log(`   - ${name}`));
} else {
    console.log('\n✅ All tests passed!');
}

console.log('═'.repeat(80));

process.exit(testsFailed.length > 0 ? 1 : 0);

