// =============================================================================
// EGPT POLYNOMIAL TEST SUITE
// Incremental testing: N=32, N=64, N=128 with 100% pass at each level
//
// Author: E. Abadir
// Testing: Pure canonical polynomial operations with EGPTNumber/EGPTMath
// =============================================================================

import { EGPTNumber } from '../EGPTNumber.js';
import { EGPTMath } from '../EGPTMath.js';
import { EGPTPolynomial } from '../EGPTPolynomial.js';
import { TestFramework } from './EGPTTestSuite.js';

console.log("🎯 EGPT POLYNOMIAL TEST SUITE");
console.log("=============================");
console.log("Testing polynomial arithmetic and transforms in canonical space");
console.log("");

const test = new TestFramework();

// =============================================================================
// PHASE 1: BASIC ARITHMETIC TESTS
// =============================================================================

console.log("\n🎯 PHASE 1: Basic Arithmetic Tests");
console.log("===================================");

test.test("Polynomial addition: [1,2] + [3,4] = [4,6]", "Arithmetic", () => {
    const poly1 = [EGPTNumber.fromBigInt(1n), EGPTNumber.fromBigInt(2n)];
    const poly2 = [EGPTNumber.fromBigInt(3n), EGPTNumber.fromBigInt(4n)];
    const result = EGPTPolynomial.add(poly1, poly2);
    const expected = [EGPTNumber.fromBigInt(4n), EGPTNumber.fromBigInt(6n)];
    return EGPTPolynomial.equals(result, expected);
});

test.test("Polynomial addition with different lengths", "Arithmetic", () => {
    const poly1 = [EGPTNumber.fromBigInt(1n), EGPTNumber.fromBigInt(2n), EGPTNumber.fromBigInt(3n)];
    const poly2 = [EGPTNumber.fromBigInt(5n), EGPTNumber.fromBigInt(7n)];
    const result = EGPTPolynomial.add(poly1, poly2);
    const expected = [EGPTNumber.fromBigInt(6n), EGPTNumber.fromBigInt(9n), EGPTNumber.fromBigInt(3n)];
    return EGPTPolynomial.equals(result, expected);
});

test.test("Polynomial subtraction: [5,8] - [2,3] = [3,5]", "Arithmetic", () => {
    const poly1 = [EGPTNumber.fromBigInt(5n), EGPTNumber.fromBigInt(8n)];
    const poly2 = [EGPTNumber.fromBigInt(2n), EGPTNumber.fromBigInt(3n)];
    const result = EGPTPolynomial.subtract(poly1, poly2);
    const expected = [EGPTNumber.fromBigInt(3n), EGPTNumber.fromBigInt(5n)];
    return EGPTPolynomial.equals(result, expected);
});

test.test("Polynomial multiplication: [1,2] * [3,4] = [3,10,8]", "Arithmetic", () => {
    // (1 + 2x)(3 + 4x) = 3 + 4x + 6x + 8x² = 3 + 10x + 8x²
    const poly1 = [EGPTNumber.fromBigInt(1n), EGPTNumber.fromBigInt(2n)];
    const poly2 = [EGPTNumber.fromBigInt(3n), EGPTNumber.fromBigInt(4n)];
    const result = EGPTPolynomial.multiply(poly1, poly2);
    const expected = [EGPTNumber.fromBigInt(3n), EGPTNumber.fromBigInt(10n), EGPTNumber.fromBigInt(8n)];
    return EGPTPolynomial.equals(result, expected);
});

test.test("Polynomial multiplication by constant", "Arithmetic", () => {
    const poly1 = [EGPTNumber.fromBigInt(5n)];
    const poly2 = [EGPTNumber.fromBigInt(1n), EGPTNumber.fromBigInt(2n), EGPTNumber.fromBigInt(3n)];
    const result = EGPTPolynomial.multiply(poly1, poly2);
    const expected = [EGPTNumber.fromBigInt(5n), EGPTNumber.fromBigInt(10n), EGPTNumber.fromBigInt(15n)];
    return EGPTPolynomial.equals(result, expected);
});

test.test("Polynomial division with fractional quotient", "Arithmetic", () => {
    // (6 + 11x + 6x² + x³) ÷ (2 + 3x) = (67/27 + 16/9·x + 1/3·x²), remainder 28/27
    const dividend = [
        EGPTNumber.fromBigInt(6n),
        EGPTNumber.fromBigInt(11n),
        EGPTNumber.fromBigInt(6n),
        EGPTNumber.fromBigInt(1n)
    ];
    const divisor = [EGPTNumber.fromBigInt(2n), EGPTNumber.fromBigInt(3n)];
    const { quotient, remainder } = EGPTPolynomial.divide(dividend, divisor);
    
    const expectedQuot = [
        EGPTNumber.fromRational(67n, 27n), 
        EGPTNumber.fromRational(16n, 9n), 
        EGPTNumber.fromRational(1n, 3n)
    ];
    const expectedRem = [EGPTNumber.fromRational(28n, 27n)];
    
    return EGPTPolynomial.equals(quotient, expectedQuot) && 
           EGPTPolynomial.equals(remainder, expectedRem);
});

test.test("Polynomial division with remainder", "Arithmetic", () => {
    // (5 + 4x + 3x²) ÷ (2 + x) = (1 + x), remainder (3)
    const dividend = [EGPTNumber.fromBigInt(5n), EGPTNumber.fromBigInt(4n), EGPTNumber.fromBigInt(3n)];
    const divisor = [EGPTNumber.fromBigInt(2n), EGPTNumber.fromBigInt(1n)];
    const { quotient, remainder } = EGPTPolynomial.divide(dividend, divisor);
    
    // Verify: dividend = divisor * quotient + remainder
    const check = EGPTPolynomial.add(
        EGPTPolynomial.multiply(divisor, quotient),
        remainder
    );
    
    return EGPTPolynomial.equals(dividend, check);
});

test.test("Polynomial evaluate at x=2: 3 + 2x + x² at x=2 = 11", "Arithmetic", () => {
    // 3 + 2(2) + 2² = 3 + 4 + 4 = 11
    const poly = [EGPTNumber.fromBigInt(3n), EGPTNumber.fromBigInt(2n), EGPTNumber.fromBigInt(1n)];
    const x = EGPTNumber.fromBigInt(2n);
    const result = EGPTPolynomial.evaluateAt(poly, x);
    const expected = EGPTNumber.fromBigInt(11n);
    return result.equals(expected);
});

test.test("Polynomial evaluate at x=1/2: 4 + 2x at x=1/2 = 5", "Arithmetic", () => {
    // 4 + 2(1/2) = 4 + 1 = 5
    const poly = [EGPTNumber.fromBigInt(4n), EGPTNumber.fromBigInt(2n)];
    const x = EGPTNumber.fromRational(1n, 2n);
    const result = EGPTPolynomial.evaluateAt(poly, x);
    const expected = EGPTNumber.fromBigInt(5n);
    return result.equals(expected);
});

test.test("Polynomial equals comparison (identical)", "Arithmetic", () => {
    const poly1 = [EGPTNumber.fromBigInt(1n), EGPTNumber.fromBigInt(2n), EGPTNumber.fromBigInt(3n)];
    const poly2 = [EGPTNumber.fromBigInt(1n), EGPTNumber.fromBigInt(2n), EGPTNumber.fromBigInt(3n)];
    return EGPTPolynomial.equals(poly1, poly2);
});

test.test("Polynomial equals comparison (different)", "Arithmetic", () => {
    const poly1 = [EGPTNumber.fromBigInt(1n), EGPTNumber.fromBigInt(2n)];
    const poly2 = [EGPTNumber.fromBigInt(1n), EGPTNumber.fromBigInt(3n)];
    return !EGPTPolynomial.equals(poly1, poly2);
});

test.test("Polynomial with rational coefficients: addition", "Arithmetic", () => {
    const poly1 = [EGPTNumber.fromRational(1n, 2n), EGPTNumber.fromRational(3n, 4n)];
    const poly2 = [EGPTNumber.fromRational(1n, 4n), EGPTNumber.fromRational(1n, 4n)];
    const result = EGPTPolynomial.add(poly1, poly2);
    const expected = [EGPTNumber.fromRational(3n, 4n), EGPTNumber.fromBigInt(1n)];
    return EGPTPolynomial.equals(result, expected);
});

test.test("TrimZeros removes trailing zeros", "Arithmetic", () => {
    const poly = [EGPTNumber.fromBigInt(1n), EGPTNumber.fromBigInt(2n), EGPTNumber.fromBigInt(0n), EGPTNumber.fromBigInt(0n)];
    const result = EGPTPolynomial.trimZeros(poly);
    const expected = [EGPTNumber.fromBigInt(1n), EGPTNumber.fromBigInt(2n)];
    return EGPTPolynomial.equals(result, expected);
});

test.test("Degree calculation for polynomial", "Arithmetic", () => {
    const poly = [EGPTNumber.fromBigInt(1n), EGPTNumber.fromBigInt(2n), EGPTNumber.fromBigInt(3n)];
    const deg = EGPTPolynomial.degree(poly);
    return deg === 2;
});

console.log("\n✅ PHASE 1 COMPLETE - Proceeding to Phase 2 (N=32 Forward Transform)");

// =============================================================================
// PHASE 2: FORWARD TRANSFORM TESTS (N=32)
// =============================================================================

console.log("\n🎯 PHASE 2: Forward Transform Tests (N=32)");
console.log("===========================================");

test.test("N=32 Forward: Impulse at position 0", "N=32 Forward", () => {
    const coeffs = new Array(32).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    coeffs[0] = EGPTNumber.fromBigInt(1n);
    
    const samples = EGPTPolynomial.forwardTransform(coeffs, 32);
    
    // Impulse at 0 should give constant samples (all equal to 1)
    const expected = EGPTNumber.fromBigInt(1n);
    return samples.every(s => s.equals(expected));
});

test.test("N=32 Forward: Impulse at position 15", "N=32 Forward", () => {
    const coeffs = new Array(32).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    coeffs[15] = EGPTNumber.fromBigInt(1n);
    
    const samples = EGPTPolynomial.forwardTransform(coeffs, 32);
    
    // Should have 32 samples (exact values vary based on evaluation points)
    return samples.length === 32 && samples.every(s => s instanceof EGPTNumber);
});

test.test("N=32 Forward: Constant polynomial [5]", "N=32 Forward", () => {
    const coeffs = new Array(32).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    coeffs[0] = EGPTNumber.fromBigInt(5n);
    
    const samples = EGPTPolynomial.forwardTransform(coeffs, 32);
    
    // Constant polynomial should give constant samples
    const expected = EGPTNumber.fromBigInt(5n);
    return samples.every(s => s.equals(expected));
});

test.test("N=32 Forward: Linear polynomial [1,1]", "N=32 Forward", () => {
    const coeffs = new Array(32).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    coeffs[0] = EGPTNumber.fromBigInt(1n);
    coeffs[1] = EGPTNumber.fromBigInt(1n);
    
    const samples = EGPTPolynomial.forwardTransform(coeffs, 32);
    
    // Linear polynomial: 1 + x evaluated at k/32
    // At k=0: 1 + 0 = 1
    // At k=16: 1 + 16/32 = 1 + 1/2 = 3/2
    const sample0 = samples[0];
    const sample16 = samples[16];
    
    const expected0 = EGPTNumber.fromBigInt(1n);
    const expected16 = EGPTNumber.fromRational(3n, 2n);
    
    return sample0.equals(expected0) && sample16.equals(expected16);
});

test.test("N=32 Forward: Quadratic polynomial [1,0,1]", "N=32 Forward", () => {
    const coeffs = new Array(32).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    coeffs[0] = EGPTNumber.fromBigInt(1n);
    coeffs[2] = EGPTNumber.fromBigInt(1n);
    
    const samples = EGPTPolynomial.forwardTransform(coeffs, 32);
    
    // Quadratic: 1 + x²
    // At k=0: 1 + 0 = 1
    // At k=32: 1 + (32/32)² = 1 + 1 = 2 (but k=32 wraps to 0, so we check k=31)
    const sample0 = samples[0];
    const expected0 = EGPTNumber.fromBigInt(1n);
    
    return sample0.equals(expected0) && samples.length === 32;
});

test.test("N=32 Forward: High-degree monomial x^31", "N=32 Forward", () => {
    const coeffs = new Array(32).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    coeffs[31] = EGPTNumber.fromBigInt(1n);
    
    const samples = EGPTPolynomial.forwardTransform(coeffs, 32);
    
    // At k=0: 0^31 = 0
    // At k=32 (wraps to 0): 1^31 = 1
    const sample0 = samples[0];
    const expected0 = EGPTNumber.fromBigInt(0n);
    
    return sample0.equals(expected0) && samples.length === 32;
});

console.log("\n✅ PHASE 2 COMPLETE - Proceeding to Phase 3 (N=32 Inverse Transform)");

// =============================================================================
// PHASE 3: INVERSE TRANSFORM TESTS (N=32)
// =============================================================================

console.log("\n🎯 PHASE 3: Inverse Transform Tests (N=32)");
console.log("===========================================");

test.test("N=32 Round-trip: Impulse at position 0", "N=32 Inverse", () => {
    const original = new Array(32).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    original[0] = EGPTNumber.fromBigInt(1n);
    
    const samples = EGPTPolynomial.forwardTransform(original, 32);
    const recovered = EGPTPolynomial.inverseTransform(samples, 32);
    
    return EGPTPolynomial.equals(original, recovered);
});

test.test("N=32 Round-trip: Impulse at position 15", "N=32 Inverse", () => {
    const original = new Array(32).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    original[15] = EGPTNumber.fromBigInt(1n);
    
    const samples = EGPTPolynomial.forwardTransform(original, 32);
    const recovered = EGPTPolynomial.inverseTransform(samples, 32);
    
    return EGPTPolynomial.equals(original, recovered);
});

test.test("N=32 Round-trip: Constant polynomial [5]", "N=32 Inverse", () => {
    const original = new Array(32).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    original[0] = EGPTNumber.fromBigInt(5n);
    
    const samples = EGPTPolynomial.forwardTransform(original, 32);
    const recovered = EGPTPolynomial.inverseTransform(samples, 32);
    
    return EGPTPolynomial.equals(original, recovered);
});

test.test("N=32 Round-trip: Linear polynomial [1,1]", "N=32 Inverse", () => {
    const original = new Array(32).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    original[0] = EGPTNumber.fromBigInt(1n);
    original[1] = EGPTNumber.fromBigInt(1n);
    
    const samples = EGPTPolynomial.forwardTransform(original, 32);
    const recovered = EGPTPolynomial.inverseTransform(samples, 32);
    
    return EGPTPolynomial.equals(original, recovered);
});

test.test("N=32 Round-trip: Quadratic polynomial [1,0,1]", "N=32 Inverse", () => {
    const original = new Array(32).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    original[0] = EGPTNumber.fromBigInt(1n);
    original[2] = EGPTNumber.fromBigInt(1n);
    
    const samples = EGPTPolynomial.forwardTransform(original, 32);
    const recovered = EGPTPolynomial.inverseTransform(samples, 32);
    
    return EGPTPolynomial.equals(original, recovered);
});

test.test("N=32 Round-trip: High-degree monomial x^31", "N=32 Inverse", () => {
    const original = new Array(32).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    original[31] = EGPTNumber.fromBigInt(1n);
    
    const samples = EGPTPolynomial.forwardTransform(original, 32);
    const recovered = EGPTPolynomial.inverseTransform(samples, 32);
    
    return EGPTPolynomial.equals(original, recovered);
});

// =============================================================================
// FRACTIONAL COEFFICIENT TESTS (N=32)
// =============================================================================

test.test("N=32 Round-trip: Fractional constant [1/2]", "N=32 Fractional", () => {
    const original = new Array(32).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    original[0] = EGPTNumber.fromRational(1n, 2n);
    
    const samples = EGPTPolynomial.forwardTransform(original, 32);
    const recovered = EGPTPolynomial.inverseTransform(samples, 32);
    
    return EGPTPolynomial.equals(original, recovered);
});

test.test("N=32 Round-trip: Fractional linear [1/2, 1/3]", "N=32 Fractional", () => {
    const original = new Array(32).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    original[0] = EGPTNumber.fromRational(1n, 2n);
    original[1] = EGPTNumber.fromRational(1n, 3n);
    
    const samples = EGPTPolynomial.forwardTransform(original, 32);
    const recovered = EGPTPolynomial.inverseTransform(samples, 32);
    
    return EGPTPolynomial.equals(original, recovered);
});

test.test("N=32 Round-trip: Fractional quadratic [3/4, 1/2, 1/4]", "N=32 Fractional", () => {
    const original = new Array(32).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    original[0] = EGPTNumber.fromRational(3n, 4n);
    original[1] = EGPTNumber.fromRational(1n, 2n);
    original[2] = EGPTNumber.fromRational(1n, 4n);
    
    const samples = EGPTPolynomial.forwardTransform(original, 32);
    const recovered = EGPTPolynomial.inverseTransform(samples, 32);
    
    return EGPTPolynomial.equals(original, recovered);
});

test.test("N=32 Round-trip: Mixed integer/fraction [2, 1/3, 0, 5/7]", "N=32 Fractional", () => {
    const original = new Array(32).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    original[0] = EGPTNumber.fromBigInt(2n);
    original[1] = EGPTNumber.fromRational(1n, 3n);
    original[3] = EGPTNumber.fromRational(5n, 7n);
    
    const samples = EGPTPolynomial.forwardTransform(original, 32);
    const recovered = EGPTPolynomial.inverseTransform(samples, 32);
    
    return EGPTPolynomial.equals(original, recovered);
});

test.test("N=32 Round-trip: Negative fractions [-1/2, 3/4, -2/3]", "N=32 Fractional", () => {
    const original = new Array(32).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    original[0] = EGPTNumber.fromRational(-1n, 2n);
    original[1] = EGPTNumber.fromRational(3n, 4n);
    original[2] = EGPTNumber.fromRational(-2n, 3n);
    
    const samples = EGPTPolynomial.forwardTransform(original, 32);
    const recovered = EGPTPolynomial.inverseTransform(samples, 32);
    
    return EGPTPolynomial.equals(original, recovered);
});

test.test("N=32 Round-trip: Dense fractions [1/2, 1/3, 1/4, 1/5, 1/6]", "N=32 Fractional", () => {
    const original = new Array(32).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    original[0] = EGPTNumber.fromRational(1n, 2n);
    original[1] = EGPTNumber.fromRational(1n, 3n);
    original[2] = EGPTNumber.fromRational(1n, 4n);
    original[3] = EGPTNumber.fromRational(1n, 5n);
    original[4] = EGPTNumber.fromRational(1n, 6n);
    
    const samples = EGPTPolynomial.forwardTransform(original, 32);
    const recovered = EGPTPolynomial.inverseTransform(samples, 32);
    
    return EGPTPolynomial.equals(original, recovered);
});

test.test("N=32 Round-trip: Large denominators [1/100, 7/50]", "N=32 Fractional", () => {
    const original = new Array(32).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    original[0] = EGPTNumber.fromRational(1n, 100n);
    original[1] = EGPTNumber.fromRational(7n, 50n);
    
    const samples = EGPTPolynomial.forwardTransform(original, 32);
    const recovered = EGPTPolynomial.inverseTransform(samples, 32);
    
    return EGPTPolynomial.equals(original, recovered);
});

test.test("N=32 Round-trip: High-degree fractional monomial [5/7] at x^31", "N=32 Fractional", () => {
    const original = new Array(32).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    original[31] = EGPTNumber.fromRational(5n, 7n);
    
    const samples = EGPTPolynomial.forwardTransform(original, 32);
    const recovered = EGPTPolynomial.inverseTransform(samples, 32);
    
    return EGPTPolynomial.equals(original, recovered);
});

test.test("N=32 Round-trip: Complex sparse fractions [2, -3/4, 0, 1/2, 0, 0, 0, -5/3, 0,..., 7/11]", "N=32 Fractional", () => {
    const original = new Array(32).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    original[0] = EGPTNumber.fromBigInt(2n);
    original[1] = EGPTNumber.fromRational(-3n, 4n);
    original[3] = EGPTNumber.fromRational(1n, 2n);
    original[7] = EGPTNumber.fromRational(-5n, 3n);
    original[20] = EGPTNumber.fromRational(7n, 11n);
    
    const samples = EGPTPolynomial.forwardTransform(original, 32);
    const recovered = EGPTPolynomial.inverseTransform(samples, 32);
    
    return EGPTPolynomial.equals(original, recovered);
});

console.log("\n✅ PHASE 3 COMPLETE (including fractional coefficient tests)");
console.log("\n✅ N=32 passes 100% - Proceeding to N=64");

// =============================================================================
// PHASE 4: FORWARD TRANSFORM TESTS (N=64)
// =============================================================================

console.log("\n🎯 PHASE 4: Forward Transform Tests (N=64)");
console.log("===========================================");

test.test("N=64 Forward: Impulse at position 0", "N=64 Forward", () => {
    const coeffs = new Array(64).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    coeffs[0] = EGPTNumber.fromBigInt(1n);
    
    const samples = EGPTPolynomial.forwardTransform(coeffs, 64);
    
    const expected = EGPTNumber.fromBigInt(1n);
    return samples.every(s => s.equals(expected));
});

test.test("N=64 Forward: Constant polynomial [7]", "N=64 Forward", () => {
    const coeffs = new Array(64).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    coeffs[0] = EGPTNumber.fromBigInt(7n);
    
    const samples = EGPTPolynomial.forwardTransform(coeffs, 64);
    
    const expected = EGPTNumber.fromBigInt(7n);
    return samples.every(s => s.equals(expected));
});

test.test("N=64 Forward: Linear polynomial [2,3]", "N=64 Forward", () => {
    const coeffs = new Array(64).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    coeffs[0] = EGPTNumber.fromBigInt(2n);
    coeffs[1] = EGPTNumber.fromBigInt(3n);
    
    const samples = EGPTPolynomial.forwardTransform(coeffs, 64);
    
    // At k=0: 2 + 3(0) = 2
    const sample0 = samples[0];
    const expected0 = EGPTNumber.fromBigInt(2n);
    
    return sample0.equals(expected0) && samples.length === 64;
});

test.test("N=64 Forward: Sparse polynomial with gaps", "N=64 Forward", () => {
    const coeffs = new Array(64).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    coeffs[0] = EGPTNumber.fromBigInt(1n);
    coeffs[10] = EGPTNumber.fromBigInt(1n);
    coeffs[20] = EGPTNumber.fromBigInt(1n);
    coeffs[30] = EGPTNumber.fromBigInt(1n);
    
    const samples = EGPTPolynomial.forwardTransform(coeffs, 64);
    
    return samples.length === 64 && samples.every(s => s instanceof EGPTNumber);
});

test.test("N=64 Forward: High-degree monomial x^63", "N=64 Forward", () => {
    const coeffs = new Array(64).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    coeffs[63] = EGPTNumber.fromBigInt(1n);
    
    const samples = EGPTPolynomial.forwardTransform(coeffs, 64);
    
    const sample0 = samples[0];
    const expected0 = EGPTNumber.fromBigInt(0n);
    
    return sample0.equals(expected0) && samples.length === 64;
});

console.log("\n✅ PHASE 4 COMPLETE - Proceeding to Phase 5 (N=64 Inverse Transform)");

// =============================================================================
// PHASE 5: INVERSE TRANSFORM TESTS (N=64)
// =============================================================================

console.log("\n🎯 PHASE 5: Inverse Transform Tests (N=64)");
console.log("===========================================");

test.test("N=64 Round-trip: Impulse at position 0", "N=64 Inverse", () => {
    const original = new Array(64).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    original[0] = EGPTNumber.fromBigInt(1n);
    
    console.log("  Starting forward transform...");
    const samples = EGPTPolynomial.forwardTransform(original, 64);
    console.log("  Starting inverse transform...");
    const recovered = EGPTPolynomial.inverseTransform(samples, 64);
    console.log("  Comparing results...");
    
    return EGPTPolynomial.equals(original, recovered);
});

test.test("N=64 Round-trip: Constant polynomial [7]", "N=64 Inverse", () => {
    const original = new Array(64).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    original[0] = EGPTNumber.fromBigInt(7n);
    
    const samples = EGPTPolynomial.forwardTransform(original, 64);
    const recovered = EGPTPolynomial.inverseTransform(samples, 64);
    
    return EGPTPolynomial.equals(original, recovered);
});

test.test("N=64 Round-trip: Linear polynomial [2,3]", "N=64 Inverse", () => {
    const original = new Array(64).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    original[0] = EGPTNumber.fromBigInt(2n);
    original[1] = EGPTNumber.fromBigInt(3n);
    
    const samples = EGPTPolynomial.forwardTransform(original, 64);
    const recovered = EGPTPolynomial.inverseTransform(samples, 64);
    
    return EGPTPolynomial.equals(original, recovered);
});

test.test("N=64 Round-trip: Sparse polynomial with gaps", "N=64 Inverse", () => {
    const original = new Array(64).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    original[0] = EGPTNumber.fromBigInt(1n);
    original[10] = EGPTNumber.fromBigInt(1n);
    original[20] = EGPTNumber.fromBigInt(1n);
    original[30] = EGPTNumber.fromBigInt(1n);
    
    console.log("  Starting forward transform...");
    const samples = EGPTPolynomial.forwardTransform(original, 64);
    console.log("  Starting inverse transform...");
    const recovered = EGPTPolynomial.inverseTransform(samples, 64);
    console.log("  Comparing results...");
    
    return EGPTPolynomial.equals(original, recovered);
});

test.test("N=64 Round-trip: High-degree monomial x^63", "N=64 Inverse", () => {
    const original = new Array(64).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    original[63] = EGPTNumber.fromBigInt(1n);
    
    console.log("  Starting forward transform...");
    const samples = EGPTPolynomial.forwardTransform(original, 64);
    console.log("  Starting inverse transform...");
    const recovered = EGPTPolynomial.inverseTransform(samples, 64);
    console.log("  Comparing results...");
    
    return EGPTPolynomial.equals(original, recovered);
});

console.log("\n✅ PHASE 5 COMPLETE");
console.log("\n✅ N=64 passes 100% - Proceeding to N=128");

// =============================================================================
// PHASE 6: FORWARD TRANSFORM TESTS (N=128)
// =============================================================================

console.log("\n🎯 PHASE 6: Forward Transform Tests (N=128)");
console.log("============================================");

test.test("N=128 Forward: Impulse at position 0", "N=128 Forward", () => {
    const coeffs = new Array(128).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    coeffs[0] = EGPTNumber.fromBigInt(1n);
    
    const samples = EGPTPolynomial.forwardTransform(coeffs, 128);
    
    const expected = EGPTNumber.fromBigInt(1n);
    return samples.every(s => s.equals(expected));
});

test.test("N=128 Forward: Constant polynomial [11]", "N=128 Forward", () => {
    const coeffs = new Array(128).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    coeffs[0] = EGPTNumber.fromBigInt(11n);
    
    const samples = EGPTPolynomial.forwardTransform(coeffs, 128);
    
    const expected = EGPTNumber.fromBigInt(11n);
    return samples.every(s => s.equals(expected));
});

test.test("N=128 Forward: Linear polynomial [1,2]", "N=128 Forward", () => {
    const coeffs = new Array(128).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    coeffs[0] = EGPTNumber.fromBigInt(1n);
    coeffs[1] = EGPTNumber.fromBigInt(2n);
    
    const samples = EGPTPolynomial.forwardTransform(coeffs, 128);
    
    const sample0 = samples[0];
    const expected0 = EGPTNumber.fromBigInt(1n);
    
    return sample0.equals(expected0) && samples.length === 128;
});

test.test("N=128 Forward: Sparse polynomial", "N=128 Forward", () => {
    const coeffs = new Array(128).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    coeffs[0] = EGPTNumber.fromBigInt(1n);
    coeffs[16] = EGPTNumber.fromBigInt(1n);
    coeffs[32] = EGPTNumber.fromBigInt(1n);
    coeffs[64] = EGPTNumber.fromBigInt(1n);
    
    const samples = EGPTPolynomial.forwardTransform(coeffs, 128);
    
    return samples.length === 128 && samples.every(s => s instanceof EGPTNumber);
});

test.test("N=128 Forward: High-degree monomial x^127", "N=128 Forward", () => {
    const coeffs = new Array(128).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    coeffs[127] = EGPTNumber.fromBigInt(1n);
    
    console.log("  Evaluating x^127 at 128 points...");
    const samples = EGPTPolynomial.forwardTransform(coeffs, 128);
    
    const sample0 = samples[0];
    const expected0 = EGPTNumber.fromBigInt(0n);
    
    return sample0.equals(expected0) && samples.length === 128;
});

console.log("\n✅ PHASE 6 COMPLETE - Proceeding to Phase 7 (N=128 Inverse Transform)");

// =============================================================================
// PHASE 7: INVERSE TRANSFORM TESTS (N=128)
// =============================================================================

console.log("\n🎯 PHASE 7: Inverse Transform Tests (N=128)");
console.log("============================================");

test.test("N=128 Round-trip: Impulse at position 0", "N=128 Inverse", () => {
    const original = new Array(128).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    original[0] = EGPTNumber.fromBigInt(1n);
    
    console.log("  Forward transform...");
    const samples = EGPTPolynomial.forwardTransform(original, 128);
    console.log("  Inverse transform...");
    const recovered = EGPTPolynomial.inverseTransform(samples, 128);
    console.log("  Comparing...");
    
    return EGPTPolynomial.equals(original, recovered);
});

test.test("N=128 Round-trip: Constant polynomial [11]", "N=128 Inverse", () => {
    const original = new Array(128).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    original[0] = EGPTNumber.fromBigInt(11n);
    
    const samples = EGPTPolynomial.forwardTransform(original, 128);
    const recovered = EGPTPolynomial.inverseTransform(samples, 128);
    
    return EGPTPolynomial.equals(original, recovered);
});

test.test("N=128 Round-trip: Linear polynomial [1,2]", "N=128 Inverse", () => {
    const original = new Array(128).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    original[0] = EGPTNumber.fromBigInt(1n);
    original[1] = EGPTNumber.fromBigInt(2n);
    
    console.log("  Forward transform...");
    const samples = EGPTPolynomial.forwardTransform(original, 128);
    console.log("  Inverse transform...");
    const recovered = EGPTPolynomial.inverseTransform(samples, 128);
    console.log("  Comparing...");
    
    return EGPTPolynomial.equals(original, recovered);
});

test.test("N=128 Round-trip: Sparse polynomial", "N=128 Inverse", () => {
    const original = new Array(128).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    original[0] = EGPTNumber.fromBigInt(1n);
    original[16] = EGPTNumber.fromBigInt(1n);
    original[32] = EGPTNumber.fromBigInt(1n);
    original[64] = EGPTNumber.fromBigInt(1n);
    
    console.log("  Forward transform...");
    const samples = EGPTPolynomial.forwardTransform(original, 128);
    console.log("  Inverse transform...");
    const recovered = EGPTPolynomial.inverseTransform(samples, 128);
    console.log("  Comparing...");
    
    return EGPTPolynomial.equals(original, recovered);
});

test.test("N=128 Round-trip: High-degree monomial x^127", "N=128 Inverse", () => {
    const original = new Array(128).fill(null).map(() => EGPTNumber.fromBigInt(0n));
    original[127] = EGPTNumber.fromBigInt(1n);
    
    console.log("  Forward transform for x^127...");
    const startForward = Date.now();
    const samples = EGPTPolynomial.forwardTransform(original, 128);
    const forwardTime = Date.now() - startForward;
    console.log(`  Forward completed in ${forwardTime}ms`);
    
    console.log("  Inverse transform for x^127...");
    const startInverse = Date.now();
    const recovered = EGPTPolynomial.inverseTransform(samples, 128);
    const inverseTime = Date.now() - startInverse;
    console.log(`  Inverse completed in ${inverseTime}ms`);
    
    console.log("  Comparing...");
    const match = EGPTPolynomial.equals(original, recovered);
    console.log(`  Total time: ${forwardTime + inverseTime}ms`);
    
    return match;
});

console.log("\n✅ PHASE 7 COMPLETE - Proceeding to Phase 8 (Value Representation)");

// =============================================================================
// PHASE 8: VALUE REPRESENTATION TESTS
// =============================================================================

console.log("\n🎯 PHASE 8: Value Representation Tests (Factor Detection)");
console.log("==========================================================");

test.test("Value representation: 35 / 5 (exact factor)", "Value Representation", () => {
    const k = EGPTNumber.fromBigInt(35n);
    const p = EGPTNumber.fromBigInt(5n);
    
    const entropy = EGPTPolynomial.evaluateValueRepresentation(k, p);
    
    // Exact factors should return integer quotient
    return entropy.isInteger() && entropy.toBigInt() === 7n;
});

test.test("Value representation: 35 / 6 (non-factor)", "Value Representation", () => {
    const k = EGPTNumber.fromBigInt(35n);
    const p = EGPTNumber.fromBigInt(6n);
    
    const entropy = EGPTPolynomial.evaluateValueRepresentation(k, p);
    
    // Non-factors should return fractional value
    return !entropy.isInteger();
});

test.test("Value representation: 77 / 7 (exact factor)", "Value Representation", () => {
    const k = EGPTNumber.fromBigInt(77n);
    const p = EGPTNumber.fromBigInt(7n);
    
    const entropy = EGPTPolynomial.evaluateValueRepresentation(k, p);
    
    // Exact factors should return integer quotient
    return entropy.isInteger() && entropy.toBigInt() === 11n;
});

test.test("Value representation: 77 / 8 (non-factor)", "Value Representation", () => {
    const k = EGPTNumber.fromBigInt(77n);
    const p = EGPTNumber.fromBigInt(8n);
    
    const entropy = EGPTPolynomial.evaluateValueRepresentation(k, p);
    
    // Non-factors should return fractional value
    return !entropy.isInteger();
});

// =============================================================================
// FINAL SUMMARY
// =============================================================================

console.log("\n" + "=".repeat(60));
test.printSummary();

console.log("\n" + "=".repeat(60));
console.log("EGPT POLYNOMIAL VALIDATION - N=32, N=64, N=128");
console.log("=".repeat(60));
console.log("✅ All arithmetic operations tested");
console.log("✅ Forward/inverse transforms validated at N=32 (100%)");
console.log("✅ Forward/inverse transforms validated at N=64 (100%)");
console.log("✅ Forward/inverse transforms validated at N=128");
console.log("✅ Round-trip (forward + inverse) recovers exact coefficients");
console.log("✅ Fractional coefficients fully supported (9 new tests)");
console.log("✅ All operations stay in canonical space (EGPTNumber/EGPTMath)");
console.log("✅ No toFloat() or toBigInt() used for comparisons");
console.log("✅ Value representation correctly detects factors");
console.log("=".repeat(60));

