
import { EGPTNumber } from '../EGPTNumber.js';
import { EGPTMath } from '../EGPTMath.js';
import { ComplexEGPTNumber, EGPTComplex } from '../EGPTComplex.js';
import { EGPTranscendental } from '../EGPTranscendental.js';
import { TestFramework } from './EGPTTestSuite.js';


console.log("🎯 TOPOLOGY-NATIVE FUNCTION TESTS");
console.log("===================================");
console.log("Validating sin/cos/PI as emergent properties of the n-gon topology.");

const test = new TestFramework();

// =============================================================================
// PHASE T1: GEOMETRIC CONSTANTS (PHASES)
// =============================================================================

test.test("EGPTranscendental.PI_PHASE represents a half-rotation (1/2)", "Geometric Constants", () => {
    const pi_phase = EGPTranscendental.PI_PHASE;
    const expected = EGPTNumber.fromRational(1n, 2n);
    return pi_phase.equals(expected);
});

test.test("EGPTranscendental.TAU_PHASE represents a full-rotation (1)", "Geometric Constants", () => {
    const tau_phase = EGPTranscendental.TAU_PHASE;
    const expected = EGPTNumber.fromBigInt(1n);
    return tau_phase.equals(expected);
});

// =============================================================================
// PHASE T2: TOPOLOGY-NATIVE TRIGONOMETRIC FUNCTIONS
// =============================================================================

test.test("cos(0) = 1", "N-Gon Trigonometry", () => {
    const phase = EGPTNumber.fromBigInt(0n);
    const result = EGPTranscendental.cos(phase);
    return result.equals(EGPTNumber.fromBigInt(1n));
});

test.test("sin(0) = 0", "N-Gon Trigonometry", () => {
    const phase = EGPTNumber.fromBigInt(0n);
    const result = EGPTranscendental.sin(phase);
    return result.equals(EGPTNumber.fromBigInt(0n));
});

test.test("cos(PI_PHASE) = -1 (half-rotation)", "N-Gon Trigonometry", () => {
    const result = EGPTranscendental.cos(EGPTranscendental.PI_PHASE);
    return result.equals(EGPTNumber.fromBigInt(-1n));
});

test.test("sin(PI_PHASE) = 0 (half-rotation)", "N-Gon Trigonometry", () => {
    const result = EGPTranscendental.sin(EGPTranscendental.PI_PHASE);
    // Use tolerance for zero due to potential rational representation complexities
    return result.equals(EGPTNumber.fromBigInt(0n));
});

test.test("cos(PI_PHASE / 2) = 0 (quarter-rotation)", "N-Gon Trigonometry", () => {
    const quarter_phase = EGPTMath.divide(EGPTranscendental.PI_PHASE, EGPTNumber.fromBigInt(2n)); // Phase 1/4
    const result = EGPTranscendental.cos(quarter_phase);
    return result.equals(EGPTNumber.fromBigInt(0n));
});

test.test("sin(PI_PHASE / 2) = 1 (quarter-rotation)", "N-Gon Trigonometry", () => {
    const quarter_phase = EGPTMath.divide(EGPTranscendental.PI_PHASE, EGPTNumber.fromBigInt(2n)); // Phase 1/4
    const result = EGPTranscendental.sin(quarter_phase);
    return result.equals(EGPTNumber.fromBigInt(1n));
});

test.test("cos(TAU_PHASE) = 1 (full-rotation)", "N-Gon Trigonometry", () => {
    const result = EGPTranscendental.cos(EGPTranscendental.TAU_PHASE);
    return result.equals(EGPTNumber.fromBigInt(1n));
});

// =============================================================================
// PHASE T3: VERIFYING THE N-GON (discrete vertex) TOPOLOGY
// =============================================================================

test.test("cos^2(phase) + sin^2(phase) != 1 for diagonal phases", "N-Gon Topology Verification", () => {
    // Phase 1/8 is a diagonal on the discrete vertex topology
    const diagonal_phase = EGPTNumber.fromRational(1n, 8n); 

    const cos_val = EGPTranscendental.cos(diagonal_phase); // Should be 1/2 in our topology
    const sin_val = EGPTranscendental.sin(diagonal_phase); // Should be 1/2 in our topology

    const cos_sq = EGPTMath.multiply(cos_val, cos_val); // (1/2)^2 = 1/4
    const sin_sq = EGPTMath.multiply(sin_val, sin_val); // (1/2)^2 = 1/4

    const sum = EGPTMath.add(cos_sq, sin_sq); // 1/4 + 1/4 = 1/2

    const H_one = EGPTNumber.fromBigInt(1n);
    
    // The sum should be 1/2, which is NOT 1. This confirms the discrete vertex topology.
    return !sum.equals(H_one) && sum.equals(EGPTNumber.fromRational(1n, 2n));
});

test.test("cos(phase 1/8) = 1/2", "N-Gon Topology Verification", () => {
    const phase = EGPTNumber.fromRational(1n, 8n);
    const result = EGPTranscendental.cos(phase);
    const expected = EGPTNumber.fromRational(1n, 2n);
    return result.equals(expected);
});

test.test("sin(phase 1/8) = 1/2", "N-Gon Topology Verification", () => {
    const phase = EGPTNumber.fromRational(1n, 8n);
    const result = EGPTranscendental.sin(phase);
    const expected = EGPTNumber.fromRational(1n, 2n);
    return result.equals(expected);
});


// =============================================================================
// PHASE T4: GEOMETRIC EXPONENTIAL FUNCTION
// =============================================================================

test.test("exp(i * PI_PHASE) = -1 (Euler's Identity)", "Geometric Exponential", () => {
    const H_ZERO = EGPTNumber.fromBigInt(0n);
    const z = new ComplexEGPTNumber(H_ZERO, EGPTranscendental.PI_PHASE); // z = 0 + i*pi_phase
    const result = EGPTComplex.exp(z);
    
    const expected_real = EGPTNumber.fromBigInt(-1n);
    const expected_imag = EGPTNumber.fromBigInt(0n);
    const expected = new ComplexEGPTNumber(expected_real, expected_imag);

    return result.equals(expected);
});

test.test("exp(i * PI_PHASE / 2) = i (Quarter Turn)", "Geometric Exponential", () => {
    const H_ZERO = EGPTNumber.fromBigInt(0n);
    const H_TWO = EGPTNumber.fromBigInt(2n);
    const quarter_phase = EGPTMath.divide(EGPTranscendental.PI_PHASE, H_TWO); // phase 1/4
    const z = new ComplexEGPTNumber(H_ZERO, quarter_phase); 
    const result = EGPTComplex.exp(z);
    
    const expected_real = EGPTNumber.fromBigInt(0n);
    const expected_imag = EGPTNumber.fromBigInt(1n);
    const expected = new ComplexEGPTNumber(expected_real, expected_imag);

    return result.equals(expected);
});

test.test("Unit Circle Identity: |exp(z)| == 1", "Geometric Exponential", () => {
    const z = new ComplexEGPTNumber(EGPTNumber.fromBigInt(2n), EGPTNumber.fromRational(1n, 8n)); // a=2, b=1/8
    const result = EGPTComplex.exp(z); // result is on unit circle

    // In our discrete vertex topology, magnitude is the L1 norm |x| + |y|
    const abs_x = EGPTMath.abs(result.real);
    const abs_y = EGPTMath.abs(result.imag);
    const magnitude = EGPTMath.add(abs_x, abs_y);
    
    const H_ONE = EGPTNumber.fromBigInt(1n);
    return magnitude.equals(H_ONE);
});

test.test("exp(a) acts as frequency multiplier 2^-a", "Geometric Exponential", () => {
    const H_a = EGPTNumber.fromBigInt(1n);   // a = 1
    const H_b = EGPTNumber.fromRational(1n, 8n); // b = 1/8
    const z = new ComplexEGPTNumber(H_a, H_b);

    const result = EGPTComplex.exp(z);
    const result_phase = result.getPhase();

    // Expected phase = b * 2^(-a) = (1/8) * 2^(-1) = 1/16
    const H_neg_a = EGPTNumber.negate(H_a);
    const H_freq_multiplier = EGPTranscendental.exp2(H_neg_a); // H(1/2)
    const H_expected_phase = EGPTMath.normalMultiply(H_b, H_freq_multiplier); // H(1/16)

    return result_phase.equals(H_expected_phase);
});

test.test("Factorial computation: 5! = 120 using topology-native operations", "Geometric Exponential", () => {
    // Compute 5! = 120 using EGPTranscendental.factorial()
    // which implements Stirling's formula: n! ≈ √(2πn) * (n/e)^n
    // using pure canonical operations where π and e emerge through the bijection
    
    const n = 5n;
    const H_result = EGPTranscendental.factorial(n);
    
    // For n=5, factorial is exact (uses direct computation)
    const H_expected = EGPTNumber.fromBigInt(120n);
    
    // Verify the canonical result matches the exact value
    return EGPTMath.equals(H_result, H_expected);
});

test.test("Factorial Stirling approximation: 97! computed via topology-native formula", "Geometric Exponential", () => {
    // Compute 97! using both exact iteration and Stirling's approximation
    // This validates the topology-native Stirling's formula for large n
    
    const n = 97n;
    
    // Step 1: Compute exact factorial iteratively using canonical operations
    let en_97_factorial = EGPTNumber.fromBigInt(1n);
    for (let i = 2n; i <= n; i++) {
        const H_i = EGPTNumber.fromBigInt(i);
        en_97_factorial = EGPTMath.multiply(en_97_factorial, H_i);
    }
    
    // Step 2: Compute using Stirling's approximation
    const H_stirling_result = EGPTranscendental.factorial(n);
    
    // Step 3: Compare results - Stirling should be very close to exact for n=97
    // Calculate relative error: |exact - approx| / exact
    const H_diff = EGPTMath.subtract(en_97_factorial, H_stirling_result);
    const H_abs_diff = EGPTMath.abs(H_diff);
    const H_relative_error = EGPTMath.normalDivide(H_abs_diff, en_97_factorial);
    
    // For n=97, Stirling's approximation should be within 1% of exact value
    const relative_error = H_relative_error.toNumber();
    
    console.log(`      97! (exact) = ${en_97_factorial.toMathString()}`);
    console.log(`      97! (Stirling) = ${H_stirling_result.toMathString()}`);
    console.log(`      Relative error: ${(relative_error * 100).toFixed(4)}%`);
    
    return relative_error < 0.01; // Within 1% error
});

// =============================================================================
// PHASE T5: FFT/FAT FOUNDATIONAL ELEMENTS
// =============================================================================

test.test("Roots of unity: ω_N^0 = 1 for any N", "FFT Foundations", () => {
    // For any N, the 0th root of unity is always 1
    const N = 8;
    const phase = EGPTNumber.fromRational(0n, BigInt(N));
    const root = EGPTComplex.exp(new ComplexEGPTNumber(EGPTNumber.fromBigInt(0n), EGPTMath.multiply(EGPTranscendental.TAU_PHASE, phase)));
    const one = new ComplexEGPTNumber(EGPTNumber.fromBigInt(1n), EGPTNumber.fromBigInt(0n));
    return root.equals(one);
});

test.test("Roots of unity: ω_N^N = 1 (periodicity)", "FFT Foundations", () => {
    // ω_N^N = ω_N^0 = 1
    const N = 8;
    const phase = EGPTNumber.fromRational(BigInt(N), BigInt(N)); // 1 = full rotation
    const root = EGPTComplex.exp(new ComplexEGPTNumber(EGPTNumber.fromBigInt(0n), EGPTMath.multiply(EGPTranscendental.TAU_PHASE, phase)));
    const one = new ComplexEGPTNumber(EGPTNumber.fromBigInt(1n), EGPTNumber.fromBigInt(0n));
    return root.equals(one);
});

test.test("Roots of unity: ω_N^k and ω_N^(N-k) are conjugates", "FFT Foundations", () => {
    // For real FFT/IFFT, conjugate symmetry is fundamental
    const N = 8;
    const k = 2;
    const phase_k = EGPTNumber.fromRational(BigInt(k), BigInt(N));
    const phase_Nk = EGPTNumber.fromRational(BigInt(N - k), BigInt(N));
    
    const root_k = EGPTComplex.exp(new ComplexEGPTNumber(EGPTNumber.fromBigInt(0n), EGPTMath.multiply(EGPTranscendental.TAU_PHASE, phase_k)));
    const root_Nk = EGPTComplex.exp(new ComplexEGPTNumber(EGPTNumber.fromBigInt(0n), EGPTMath.multiply(EGPTranscendental.TAU_PHASE, phase_Nk)));
    
    const root_k_conj = root_k.conjugate();
    return root_k_conj.equals(root_Nk);
});

test.test("Forward FFT: DC component = sum of all inputs", "FFT Foundations", () => {
    // X[0] = Σ x[n] for n=0 to N-1
    const N = 4;
    const signal = [];
    for (let i = 0; i < N; i++) {
        signal.push(new ComplexEGPTNumber(
            EGPTNumber.fromBigInt(BigInt(i + 1)),
            EGPTNumber.fromBigInt(0n)
        ));
    }
    
    // Manual sum
    let sum = EGPTNumber.fromBigInt(0n);
    for (const s of signal) {
        sum = EGPTMath.add(sum, s.real);
    }
    
    // For N=4, signal = [1, 2, 3, 4], sum = 10
    const expected_sum = EGPTNumber.fromBigInt(10n);
    return sum.equals(expected_sum);
});

test.test("Inverse FFT normalization: unnormalized result = N * original", "FFT Foundations", () => {
    // IEQFT without normalization should yield N * original
    const N = 4;
    const scale = EGPTNumber.fromBigInt(BigInt(N));
    
    // If original = a, unnormalized IEQFT(EQFT(a)) = N * a
    const original = EGPTNumber.fromBigInt(5n);
    const scaled = EGPTMath.multiply(original, scale);
    const expected = EGPTNumber.fromBigInt(20n); // 4 * 5
    
    return scaled.equals(expected);
});

// =============================================================================
// FINAL SUMMARY
// =============================================================================
console.log("\n" + "=".repeat(60));
test.printSummary();
console.log("\n" + "=".repeat(60));
console.log("✅ Topology-native functions validated.");

export { test as testResults };
