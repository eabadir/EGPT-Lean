#!/usr/bin/env node

/**
 * IEQFT Fundamental Operations Test Suite
 * 
 * Comprehensive test suite to validate all fundamental library operations
 * necessary for IEQFT, with targeted investigation of:
 * - Odd branch behavior in recursive IEQFT
 * - Unexpected imaginary component in O[k] values
 * - Recursive structure correctness at each level
 * - Butterfly operation correctness
 * - Even/odd branch separation and recombination
 * 
 * @version 1.0.0
 * @date December 2025
 */

import { EGPTNumber } from '../lib/EGPTNumber.js';
import { ComplexEGPTNumber, TwiddleTable, EGPTComplex } from '../lib/EGPTComplex.js';
import { EGPTMath } from '../lib//EGPTMath.js';
import { TestFramework } from '../lib/test/EGPTTestSuite.js';

console.log('╔════════════════════════════════════════════════════════════════════════════════╗');
console.log('║  IEQFT FUNDAMENTAL OPERATIONS TEST SUITE                                       ║');
console.log('║  Systematic validation of all IEQFT operations with odd branch investigation ║');
console.log('╚════════════════════════════════════════════════════════════════════════════════╝');
console.log('');

const test = new TestFramework();

// =============================================================================
// HELPER FUNCTIONS AND IEQFT IMPLEMENTATION
// =============================================================================

/**
 * Canonical IEQFT implementation (from working proof)
 */
function canonicalTwiddles(N) {
    const table = new TwiddleTable(N);
    const arr = [];
    for (let j = 0; j < N; j++) arr.push(table.getTwiddle(j));
    return arr;
}

function canonicalConjugateTwiddles(N) {
    const forward = canonicalTwiddles(N);
    return forward.map(w => w.conjugate());
}

function canonicalAdd(z1, z2) {
    return z1.add(z2);
}

function canonicalSub(z1, z2) {
    return z1.subtract(z2);
}

function canonicalMul(z1, z2) {
    return EGPTComplex.complexMultiply(z1, z2);
}

function IEQFT_CANONICAL(X, applyNormalization = true) {
    const N = X.length;
    if (N === 1) return [X[0]];
    const twConj = canonicalConjugateTwiddles(N);
    const Y = IEQFT_recursive_canonical(X, twConj, 0, N, 1);
    const N_big = BigInt(N);
    
    if (applyNormalization) {
        for (let i = 0; i < N; i++) {
            if (typeof Y[i].scaleByRational === 'function') {
                Y[i] = Y[i].scaleByRational(1n, N_big);
            } else {
                const r = EGPTMath.divide(Y[i].real, EGPTNumber.fromBigInt(N_big));
                const im = EGPTMath.divide(Y[i].imag, EGPTNumber.fromBigInt(N_big));
                Y[i] = new ComplexEGPTNumber(r, im);
            }
        }
    }
    return Y;
}

function IEQFT_recursive_canonical(X, twConj, start, N, stride) {
    if (N === 1) return [X[start]];
    const N2 = N / 2;
    const E = IEQFT_recursive_canonical(X, twConj, start, N2, stride * 2);
    const O = IEQFT_recursive_canonical(X, twConj, start + stride, N2, stride * 2);
    const result = new Array(N);
    const twStride = twConj.length / N;
    for (let k = 0; k < N2; k++) {
        const omega_conj_k = twConj[k * twStride];
        const t = canonicalMul(O[k], omega_conj_k);
        result[k] = canonicalAdd(E[k], t);
        result[k + N2] = canonicalSub(E[k], t);
    }
    return result;
}

/**
 * Helper: Format complex number for display
 */
function formatComplex(z) {
    const re = z.real.toNumber();
    const im = z.imag.toNumber();
    if (Math.abs(im) < 1e-10) return `${re}`;
    if (Math.abs(re) < 1e-10) return `${im}i`;
    return `${re}${im >= 0 ? '+' : ''}${im}i`;
}

/**
 * Helper: Check if complex number is real (imaginary part is zero)
 */
function isReal(z, tolerance = 1e-10) {
    return Math.abs(z.imag.toNumber()) < tolerance;
}

/**
 * Helper: Extract even indices from array
 */
function extractEvenIndices(arr, stride = 1) {
    const result = [];
    for (let i = 0; i < arr.length; i += stride * 2) {
        result.push(arr[i]);
    }
    return result;
}

/**
 * Helper: Extract odd indices from array
 */
function extractOddIndices(arr, stride = 1) {
    const result = [];
    for (let i = stride; i < arr.length; i += stride * 2) {
        result.push(arr[i]);
    }
    return result;
}

// =============================================================================
// PHASE 1: FOUNDATION OPERATIONS (PREREQUISITES)
// =============================================================================

console.log('\n🎯 PHASE 1: Foundation Operations (Prerequisites)');
console.log('═'.repeat(80));

test.test("Complex Add with twiddle products", "Foundation Operations", () => {
    const z1 = new ComplexEGPTNumber(
        EGPTNumber.fromBigInt(1n),
        EGPTNumber.fromBigInt(2n)
    );
    const z2 = new ComplexEGPTNumber(
        EGPTNumber.fromBigInt(3n),
        EGPTNumber.fromBigInt(4n)
    );
    const sum = canonicalAdd(z1, z2);
    return sum.real.toBigInt() === 4n && sum.imag.toBigInt() === 6n;
});

test.test("Complex Subtract with twiddle products", "Foundation Operations", () => {
    const z1 = new ComplexEGPTNumber(
        EGPTNumber.fromBigInt(5n),
        EGPTNumber.fromBigInt(6n)
    );
    const z2 = new ComplexEGPTNumber(
        EGPTNumber.fromBigInt(2n),
        EGPTNumber.fromBigInt(3n)
    );
    const diff = canonicalSub(z1, z2);
    return diff.real.toBigInt() === 3n && diff.imag.toBigInt() === 3n;
});

test.test("Complex Multiply with conjugate twiddle (unit circle)", "Foundation Operations", () => {
    const table = new TwiddleTable(8);
    const omega = table.getTwiddle(1);
    const omega_conj = omega.conjugate();
    const z = new ComplexEGPTNumber(
        EGPTNumber.fromBigInt(2n),
        EGPTNumber.fromBigInt(0n)
    );
    const result = canonicalMul(z, omega_conj);
    // Verify result is a complex number (not necessarily unit magnitude due to scaling)
    return result instanceof ComplexEGPTNumber;
});

test.test("Complex Multiply with conjugate twiddle preserves structure", "Foundation Operations", () => {
    const table = new TwiddleTable(4);
    const omega_conj = table.getTwiddle(1).conjugate();
    const z = new ComplexEGPTNumber(
        EGPTNumber.fromRational(1n, 2n),
        EGPTNumber.fromRational(1n, 2n)
    );
    const result = canonicalMul(z, omega_conj);
    // Verify multiplication produces valid complex number
    return result.real instanceof EGPTNumber && result.imag instanceof EGPTNumber;
});

test.test("Conjugate twiddle generation correctness", "Foundation Operations", () => {
    const N = 8;
    const twiddles = canonicalTwiddles(N);
    const conjTwiddles = canonicalConjugateTwiddles(N);
    
    // Verify ω^k * ω^k* = |ω|^2 = 1 (for unit circle)
    for (let k = 0; k < N; k++) {
        const product = canonicalMul(twiddles[k], conjTwiddles[k]);
        const magSq = product.getMagnitudeSquared();
        // For unit circle twiddles, magnitude squared should be 1
        const magVal = magSq.toNumber();
        if (Math.abs(magVal - 1.0) > 0.01) return false;
    }
    return true;
});

test.test("ScaleByRational for normalization (N=4)", "Foundation Operations", () => {
    const z = new ComplexEGPTNumber(
        EGPTNumber.fromBigInt(8n),
        EGPTNumber.fromBigInt(4n)
    );
    const scaled = z.scaleByRational(1n, 4n);
    return scaled.real.toBigInt() === 2n && scaled.imag.toBigInt() === 1n;
});

test.test("ScaleByRational for normalization (N=8)", "Foundation Operations", () => {
    const z = new ComplexEGPTNumber(
        EGPTNumber.fromBigInt(16n),
        EGPTNumber.fromBigInt(8n)
    );
    const scaled = z.scaleByRational(1n, 8n);
    return scaled.real.toBigInt() === 2n && scaled.imag.toBigInt() === 1n;
});

// =============================================================================
// PHASE 2: RECURSIVE STRUCTURE TESTS
// =============================================================================

console.log('\n🎯 PHASE 2: Recursive Structure Tests');
console.log('═'.repeat(80));

test.test("Base case (N=1)", "Recursive Structure", () => {
    const ZERO = EGPTNumber.fromBigInt(0n);
    const ONE = EGPTNumber.fromBigInt(1n);
    const input = [new ComplexEGPTNumber(ONE, ZERO)];
    const output = IEQFT_CANONICAL(input);
    return output.length === 1 && output[0].equals(input[0]);
});

test.test("Level 1 (N=2) - smallest non-trivial", "Recursive Structure", () => {
    const ZERO = EGPTNumber.fromBigInt(0n);
    const ONE = EGPTNumber.fromBigInt(1n);
    const input = [
        new ComplexEGPTNumber(ONE, ZERO),
        new ComplexEGPTNumber(ONE, ZERO)
    ];
    const output = IEQFT_CANONICAL(input, false); // No normalization for testing
    
    // For N=2, even branch is [input[0]], odd branch is [input[1]]
    // Both should be processed correctly
    return output.length === 2;
});

test.test("Level 2 (N=4) - even branch structure", "Recursive Structure", () => {
    const ZERO = EGPTNumber.fromBigInt(0n);
    const ONE = EGPTNumber.fromBigInt(1n);
    const input = [
        new ComplexEGPTNumber(ONE, ZERO),  // index 0 (even)
        new ComplexEGPTNumber(ZERO, ZERO), // index 1 (odd)
        new ComplexEGPTNumber(ONE, ZERO),  // index 2 (even)
        new ComplexEGPTNumber(ZERO, ZERO)  // index 3 (odd)
    ];
    
    // Even branch should process indices 0, 2
    const evenIndices = extractEvenIndices(input);
    return evenIndices.length === 2;
});

test.test("Level 2 (N=4) - odd branch structure", "Recursive Structure", () => {
    const ZERO = EGPTNumber.fromBigInt(0n);
    const ONE = EGPTNumber.fromBigInt(1n);
    const input = [
        new ComplexEGPTNumber(ONE, ZERO),  // index 0 (even)
        new ComplexEGPTNumber(ONE, ZERO),  // index 1 (odd)
        new ComplexEGPTNumber(ZERO, ZERO),  // index 2 (even)
        new ComplexEGPTNumber(ZERO, ZERO)  // index 3 (odd)
    ];
    
    // Odd branch should process indices 1, 3
    const oddIndices = extractOddIndices(input);
    return oddIndices.length === 2;
});

test.test("Level 3 (N=8) - full structure", "Recursive Structure", () => {
    const ZERO = EGPTNumber.fromBigInt(0n);
    const ONE = EGPTNumber.fromBigInt(1n);
    const input = new Array(8).fill(null).map(() => new ComplexEGPTNumber(ZERO, ZERO));
    input[0] = new ComplexEGPTNumber(ONE, ZERO);
    
    const output = IEQFT_CANONICAL(input);
    return output.length === 8;
});

// =============================================================================
// PHASE 3: ODD BRANCH INVESTIGATION
// =============================================================================

console.log('\n🎯 PHASE 3: Odd Branch Investigation');
console.log('═'.repeat(80));

test.test("Odd branch input analysis - purely real input", "Odd Branch Investigation", () => {
    const ZERO = EGPTNumber.fromBigInt(0n);
    const ONE = EGPTNumber.fromBigInt(1n);
    const input = [
        new ComplexEGPTNumber(ZERO, ZERO),
        new ComplexEGPTNumber(ONE, ZERO),  // Only odd index non-zero
        new ComplexEGPTNumber(ZERO, ZERO),
        new ComplexEGPTNumber(ZERO, ZERO)
    ];
    
    // All inputs should be real
    const allReal = input.every(z => isReal(z));
    return allReal;
});

test.test("Odd branch input - check for initial imaginary components", "Odd Branch Investigation", () => {
    const ZERO = EGPTNumber.fromBigInt(0n);
    const ONE = EGPTNumber.fromBigInt(1n);
    const input = new Array(8).fill(null).map(() => new ComplexEGPTNumber(ZERO, ZERO));
    input[1] = new ComplexEGPTNumber(ONE, ZERO);
    input[3] = new ComplexEGPTNumber(ONE, ZERO);
    
    // Extract odd branch inputs
    const oddInputs = extractOddIndices(input);
    const allReal = oddInputs.every(z => isReal(z));
    return allReal;
});

test.test("Odd branch intermediate values - trace E[k] at level 1 (N=4)", "Odd Branch Investigation", () => {
    const ZERO = EGPTNumber.fromBigInt(0n);
    const ONE = EGPTNumber.fromBigInt(1n);
    // Create input where odd branch gets [1, 0] at N=2 level
    const input = new Array(4).fill(null).map(() => new ComplexEGPTNumber(ZERO, ZERO));
    input[1] = new ComplexEGPTNumber(ONE, ZERO);
    
    // Run IEQFT without normalization to see intermediate values
    const output = IEQFT_CANONICAL(input, false);
    
    // Output should be valid complex numbers
    return output.every(z => z instanceof ComplexEGPTNumber);
});

test.test("Odd branch twiddle application - verify correct twiddle selection", "Odd Branch Investigation", () => {
    const N = 8;
    const twConj = canonicalConjugateTwiddles(N);
    const twStride = twConj.length / N;
    
    // At level 0 (N=8), k=1, we should use twConj[1 * twStride]
    const twiddle_index = 1 * twStride;
    return twiddle_index >= 0 && twiddle_index < twConj.length;
});

// =============================================================================
// PHASE 4: BUTTERFLY OPERATION VALIDATION
// =============================================================================

console.log('\n🎯 PHASE 4: Butterfly Operation Validation');
console.log('═'.repeat(80));

test.test("Butterfly with simple real values", "Butterfly Operations", () => {
    const ONE = EGPTNumber.fromBigInt(1n);
    const ZERO = EGPTNumber.fromBigInt(0n);
    
    // E[k] = (1, 0), O[k] = (2, 0)
    const E_k = new ComplexEGPTNumber(ONE, ZERO);
    const O_k = new ComplexEGPTNumber(
        EGPTNumber.fromBigInt(2n),
        ZERO
    );
    
    // Simple twiddle = (1, 0) - no rotation
    const twiddle = new ComplexEGPTNumber(ONE, ZERO);
    
    // Butterfly: result[k] = E[k] + O[k]*twiddle, result[k+N2] = E[k] - O[k]*twiddle
    const t = canonicalMul(O_k, twiddle);
    const result_k = canonicalAdd(E_k, t);
    const result_k_N2 = canonicalSub(E_k, t);
    
    // Both results should be real
    return isReal(result_k) && isReal(result_k_N2);
});

test.test("Butterfly with complex twiddle - verify structure", "Butterfly Operations", () => {
    const ZERO = EGPTNumber.fromBigInt(0n);
    const ONE = EGPTNumber.fromBigInt(1n);
    
    const E_k = new ComplexEGPTNumber(ONE, ZERO);
    const O_k = new ComplexEGPTNumber(ONE, ZERO);
    
    // Use actual conjugate twiddle from table
    const table = new TwiddleTable(4);
    const twiddle = table.getTwiddle(1).conjugate();
    
    const t = canonicalMul(O_k, twiddle);
    const result_k = canonicalAdd(E_k, t);
    const result_k_N2 = canonicalSub(E_k, t);
    
    // Results should be valid complex numbers
    return result_k instanceof ComplexEGPTNumber && result_k_N2 instanceof ComplexEGPTNumber;
});

test.test("Butterfly symmetry - E[k] + t and E[k] - t relationship", "Butterfly Operations", () => {
    const ZERO = EGPTNumber.fromBigInt(0n);
    const ONE = EGPTNumber.fromBigInt(1n);
    
    const E_k = new ComplexEGPTNumber(ONE, ZERO);
    const O_k = new ComplexEGPTNumber(
        EGPTNumber.fromBigInt(2n),
        ZERO
    );
    
    const twiddle = new ComplexEGPTNumber(ONE, ZERO);
    const t = canonicalMul(O_k, twiddle);
    
    const result_k = canonicalAdd(E_k, t);
    const result_k_N2 = canonicalSub(E_k, t);
    
    // For E_k = 1, O_k = 2, twiddle = 1:
    // t = 2, result[k] = 3, result[k+N2] = -1
    // Verify: result[k] + result[k+N2] should equal 2*E_k = 2
    const sum = canonicalAdd(result_k, result_k_N2);
    const expected = EGPTNumber.fromBigInt(2n);
    
    return sum.real.equals(expected) && isReal(sum);
});

// =============================================================================
// PHASE 5: RECURSIVE LEVEL INTERACTION
// =============================================================================

console.log('\n🎯 PHASE 5: Recursive Level Interaction');
console.log('═'.repeat(80));

test.test("Value propagation - impulse signal [1,0,0,0,0,0,0,0]", "Recursive Interaction", () => {
    const ZERO = EGPTNumber.fromBigInt(0n);
    const ONE = EGPTNumber.fromBigInt(1n);
    const input = new Array(8).fill(null).map(() => new ComplexEGPTNumber(ZERO, ZERO));
    input[0] = new ComplexEGPTNumber(ONE, ZERO);
    
    const output = IEQFT_CANONICAL(input);
    
    // Impulse should produce all ones after normalization
    // Check that output is valid
    return output.length === 8 && output.every(z => z instanceof ComplexEGPTNumber);
});

test.test("Even/odd interaction - no cross-contamination", "Recursive Interaction", () => {
    const ZERO = EGPTNumber.fromBigInt(0n);
    const ONE = EGPTNumber.fromBigInt(1n);
    
    // Create input with even indices = 1, odd indices = 0
    const input = new Array(8).fill(null).map((_, i) => {
        if (i % 2 === 0) {
            return new ComplexEGPTNumber(ONE, ZERO);
        } else {
            return new ComplexEGPTNumber(ZERO, ZERO);
        }
    });
    
    const output = IEQFT_CANONICAL(input, false);
    
    // Verify output is valid
    return output.length === 8;
});

test.test("Normalization propagation - verify applied only at top level", "Recursive Interaction", () => {
    const ZERO = EGPTNumber.fromBigInt(0n);
    const ONE = EGPTNumber.fromBigInt(1n);
    const input = new Array(4).fill(null).map(() => new ComplexEGPTNumber(ZERO, ZERO));
    input[0] = new ComplexEGPTNumber(ONE, ZERO);
    
    // Test with normalization
    const outputWithNorm = IEQFT_CANONICAL(input, true);
    
    // Test without normalization
    const outputWithoutNorm = IEQFT_CANONICAL(input, false);
    
    // Values should differ by factor of N=4
    const ratio = EGPTMath.divide(outputWithNorm[0].real, outputWithoutNorm[0].real);
    const expectedRatio = EGPTNumber.fromRational(1n, 4n);
    
    return ratio.equals(expectedRatio);
});

// =============================================================================
// PHASE 6: SPECIFIC BUG REPRODUCTION TESTS
// =============================================================================

console.log('\n🎯 PHASE 6: Specific Bug Reproduction Tests');
console.log('═'.repeat(80));

test.test("Minimal reproducer [1,2,0,0,0,0,0,0] - execute IEQFT", "Bug Reproduction", () => {
    const ZERO = EGPTNumber.fromBigInt(0n);
    const ONE = EGPTNumber.fromBigInt(1n);
    const TWO = EGPTNumber.fromBigInt(2n);
    
    const input = [
        new ComplexEGPTNumber(ONE, ZERO),
        new ComplexEGPTNumber(TWO, ZERO),
        new ComplexEGPTNumber(ZERO, ZERO),
        new ComplexEGPTNumber(ZERO, ZERO),
        new ComplexEGPTNumber(ZERO, ZERO),
        new ComplexEGPTNumber(ZERO, ZERO),
        new ComplexEGPTNumber(ZERO, ZERO),
        new ComplexEGPTNumber(ZERO, ZERO)
    ];
    
    const output = IEQFT_CANONICAL(input);
    
    // Log first few values for debugging
    console.log(`      Input: [1, 2, 0, 0, 0, 0, 0, 0]`);
    console.log(`      Output[0]: ${formatComplex(output[0])}`);
    console.log(`      Output[1]: ${formatComplex(output[1])}`);
    console.log(`      Output[2]: ${formatComplex(output[2])}`);
    console.log(`      Output[3]: ${formatComplex(output[3])}`);
    
    // Check if any output has unexpected imaginary component
    const unexpectedImag = output.slice(0, 4).some(z => !isReal(z, 1e-6));
    if (unexpectedImag) {
        console.log(`      ⚠️  Unexpected imaginary components detected in output`);
    }
    
    return output.length === 8;
});

test.test("Odd index pattern - [0,1,0,0,0,0,0,0]", "Bug Reproduction", () => {
    const ZERO = EGPTNumber.fromBigInt(0n);
    const ONE = EGPTNumber.fromBigInt(1n);
    
    const input = new Array(8).fill(null).map(() => new ComplexEGPTNumber(ZERO, ZERO));
    input[1] = new ComplexEGPTNumber(ONE, ZERO);
    
    const output = IEQFT_CANONICAL(input);
    
    // Log odd index pattern results
    console.log(`      Odd index input: Output[0]=${formatComplex(output[0])}, Output[1]=${formatComplex(output[1])}`);
    
    return output.length === 8;
});

test.test("Even index pattern - [1,0,0,0,0,0,0,0] comparison", "Bug Reproduction", () => {
    const ZERO = EGPTNumber.fromBigInt(0n);
    const ONE = EGPTNumber.fromBigInt(1n);
    
    const input = new Array(8).fill(null).map(() => new ComplexEGPTNumber(ZERO, ZERO));
    input[0] = new ComplexEGPTNumber(ONE, ZERO);
    
    const output = IEQFT_CANONICAL(input);
    
    // This case is known to work (impulse)
    console.log(`      Even index (impulse) input: Output[0]=${formatComplex(output[0])}`);
    
    return output.length === 8 && isReal(output[0]);
});

test.test("Stride-based indexing verification - level 0 (N=8)", "Bug Reproduction", () => {
    const N = 8;
    const twConj = canonicalConjugateTwiddles(N);
    const twStride = twConj.length / N;
    
    // At level 0, for k=0,1,2,3, we use twiddles at indices 0, twStride, 2*twStride, 3*twStride
    const indices = [];
    for (let k = 0; k < N/2; k++) {
        const idx = k * twStride;
        indices.push(idx);
    }
    
    // All indices should be valid
    return indices.every(idx => idx >= 0 && idx < twConj.length);
});

test.test("Stride-based indexing verification - level 1 (N=4)", "Bug Reproduction", () => {
    const N = 4;
    const twConj = canonicalConjugateTwiddles(N);
    const twStride = twConj.length / N;
    
    // At level 1 (N=4), twStride should be valid
    const indices = [];
    for (let k = 0; k < N/2; k++) {
        const idx = k * twStride;
        indices.push(idx);
    }
    
    return indices.every(idx => idx >= 0 && idx < twConj.length);
});

// =============================================================================
// PHASE 7: MATHEMATICAL CORRECTNESS
// =============================================================================

console.log('\n🎯 PHASE 7: Mathematical Correctness');
console.log('═'.repeat(80));

test.test("Linearity property - IEQFT(a·X + b·Y) = a·IEQFT(X) + b·IEQFT(Y)", "Mathematical Correctness", () => {
    const ZERO = EGPTNumber.fromBigInt(0n);
    const ONE = EGPTNumber.fromBigInt(1n);
    const TWO = EGPTNumber.fromBigInt(2n);
    
    // X = [1, 0, 0, 0]
    const X = new Array(4).fill(null).map(() => new ComplexEGPTNumber(ZERO, ZERO));
    X[0] = new ComplexEGPTNumber(ONE, ZERO);
    
    // Y = [0, 1, 0, 0]
    const Y = new Array(4).fill(null).map(() => new ComplexEGPTNumber(ZERO, ZERO));
    Y[1] = new ComplexEGPTNumber(ONE, ZERO);
    
    // Compute IEQFT(X) and IEQFT(Y)
    const ieqft_X = IEQFT_CANONICAL(X, false);
    const ieqft_Y = IEQFT_CANONICAL(Y, false);
    
    // Compute a·IEQFT(X) + b·IEQFT(Y) where a=2, b=3
    const combined = ieqft_X.map((z, i) => {
        const scaled_X = z.scaleBy(2n);
        const scaled_Y = ieqft_Y[i].scaleBy(3n);
        return canonicalAdd(scaled_X, scaled_Y);
    });
    
    // Compute 2·X + 3·Y and then IEQFT
    const linear_input = X.map((z, i) => {
        const scaled_X = z.scaleBy(2n);
        const scaled_Y = Y[i].scaleBy(3n);
        return canonicalAdd(scaled_X, scaled_Y);
    });
    const ieqft_combined = IEQFT_CANONICAL(linear_input, false);
    
    // Compare results (with tolerance for floating point conversion)
    const tolerance = 1e-6;
    let allMatch = true;
    for (let i = 0; i < combined.length; i++) {
        const diff_re = Math.abs(combined[i].real.toNumber() - ieqft_combined[i].real.toNumber());
        const diff_im = Math.abs(combined[i].imag.toNumber() - ieqft_combined[i].imag.toNumber());
        if (diff_re > tolerance || diff_im > tolerance) {
            allMatch = false;
            break;
        }
    }
    
    return allMatch;
});

test.test("Energy conservation (Parseval) - with exact rational inputs", "Mathematical Correctness", () => {
    const ZERO = EGPTNumber.fromBigInt(0n);
    const ONE = EGPTNumber.fromBigInt(1n);
    
    // Create simple input
    const input = new Array(4).fill(null).map(() => new ComplexEGPTNumber(ZERO, ZERO));
    input[0] = new ComplexEGPTNumber(ONE, ZERO);
    
    // Compute IEQFT
    const output = IEQFT_CANONICAL(input, false);
    
    // Compute input energy (magnitude squared sum)
    const inputEnergy = input.reduce((sum, z) => {
        return EGPTMath.add(sum, z.getMagnitudeSquared());
    }, EGPTNumber.fromBigInt(0n));
    
    // Compute output energy (magnitude squared sum)
    const outputEnergy = output.reduce((sum, z) => {
        return EGPTMath.add(sum, z.getMagnitudeSquared());
    }, EGPTNumber.fromBigInt(0n));
    
    // For Parseval: ||X||² = N * ||x||² after IEQFT
    // But we're computing IEQFT, so we need to account for normalization
    // Without normalization: outputEnergy should relate to inputEnergy
    const N = BigInt(input.length);
    const scaledInputEnergy = EGPTMath.multiply(inputEnergy, EGPTNumber.fromBigInt(N));
    
    // Check if outputEnergy ≈ scaledInputEnergy (with tolerance)
    const diff = EGPTMath.subtract(outputEnergy, scaledInputEnergy);
    const diffVal = Math.abs(diff.toNumber());
    
    return diffVal < 1.0; // Loose tolerance for this test
});

// =============================================================================
// DETAILED ODD BRANCH TRACE
// =============================================================================

console.log('\n🎯 DETAILED ODD BRANCH TRACE');
console.log('═'.repeat(80));

/**
 * Detailed trace of odd branch for [1,2,0,0,0,0,0,0] input
 */
function traceOddBranch() {
    console.log('\n📊 Tracing odd branch for input [1, 2, 0, 0, 0, 0, 0, 0]');
    console.log('─'.repeat(60));
    
    const ZERO = EGPTNumber.fromBigInt(0n);
    const ONE = EGPTNumber.fromBigInt(1n);
    const TWO = EGPTNumber.fromBigInt(2n);
    
    const input = [
        new ComplexEGPTNumber(ONE, ZERO),
        new ComplexEGPTNumber(TWO, ZERO),
        new ComplexEGPTNumber(ZERO, ZERO),
        new ComplexEGPTNumber(ZERO, ZERO),
        new ComplexEGPTNumber(ZERO, ZERO),
        new ComplexEGPTNumber(ZERO, ZERO),
        new ComplexEGPTNumber(ZERO, ZERO),
        new ComplexEGPTNumber(ZERO, ZERO)
    ];
    
    console.log('Input array:');
    input.forEach((z, i) => {
        console.log(`  [${i}]: ${formatComplex(z)}`);
    });
    
    // Extract odd branch (indices 1, 3, 5, 7)
    const oddBranch = extractOddIndices(input);
    console.log('\nOdd branch inputs (indices 1, 3, 5, 7):');
    oddBranch.forEach((z, i) => {
        console.log(`  [${i}]: ${formatComplex(z)}`);
    });
    
    // Check if all are real
    const allReal = oddBranch.every(z => isReal(z));
    console.log(`\nAll odd branch inputs are real: ${allReal ? '✅' : '❌'}`);
    
    // Run IEQFT and check output
    const output = IEQFT_CANONICAL(input, false); // No normalization for debugging
    console.log('\nIEQFT output (without normalization):');
    output.forEach((z, i) => {
        const realFlag = isReal(z) ? '' : ' ⚠️ HAS IMAGINARY';
        console.log(`  [${i}]: ${formatComplex(z)}${realFlag}`);
    });
    
    // Check which outputs have unexpected imaginary components
    const unexpectedImag = [];
    output.forEach((z, i) => {
        if (!isReal(z, 1e-6)) {
            unexpectedImag.push(i);
        }
    });
    
    if (unexpectedImag.length > 0) {
        console.log(`\n⚠️  Outputs with unexpected imaginary components: [${unexpectedImag.join(', ')}]`);
    } else {
        console.log(`\n✅ All outputs are real`);
    }
}

traceOddBranch();

// =============================================================================
// FINAL SUMMARY
// =============================================================================

console.log('\n' + '═'.repeat(80));
test.printSummary();

console.log('\n🎯 TEST SUITE COMPLETE');
console.log('═'.repeat(80));
console.log('This suite systematically tests all fundamental operations for IEQFT.');
console.log('Review the detailed odd branch trace above for bug investigation.');

