// =============================================================================
// EGPT FAT: PURE PPF IMPLEMENTATION - MATRIX-BASED NATIVE BIT ENCODING
// Based on EGPT Vector Space Refactor v3.0: Scalar & Vector Paradigm
//
// Author: E. Abadir
// Paradigm: Optimized FAT using pure PPF arithmetic with:
//           - Matrix-based butterfly operations
//           - Native bit encoding (BigInt form during computation)
//           - Bit-shifting optimizations for power-of-2 operations
//           - Phase arithmetic (RC1-inspired) for O(1) twiddle operations
//           - Minimal encode/decode (only at I/O boundaries)
// =============================================================================
import { SimpleLogger } from '../DebugLogger.js';
import { EGPTNumber } from '../EGPTNumber.js';
import { ComplexEGPTNumber, TwiddleTable } from '../EGPTComplex.js';
import { EGPTMath } from '../EGPTMath.js';

SimpleLogger.log("⚡ PURE PPF FAT: Matrix-based native bit encoding");
SimpleLogger.log("📁 File location: EGPT/js/model/EGPTFAT_PurePPF.js");
SimpleLogger.log("🎯 Optimized FAT with phase arithmetic and bit-shifting");

// =============================================================================
// TYPE DEFINITIONS
// =============================================================================

/**
 * Native bit representation: keep values as BigInt during computation
 * Avoids encode/decode overhead
 * @typedef {Object} NativeBitComplex
 * @property {BigInt} real_num - Real numerator
 * @property {BigInt} real_den - Real denominator
 * @property {BigInt} imag_num - Imaginary numerator
 * @property {BigInt} imag_den - Imaginary denominator
 */

/**
 * Phase representation for twiddle factors (RC1-inspired)
 * @typedef {Object} Phase
 * @property {BigInt} k - Phase numerator (0 to N-1)
 * @property {BigInt} N - Phase denominator (FFT size)
 */

/**
 * PPF structure (only used at I/O boundaries)
 * @typedef {Object} PPFStruct
 * @property {BigInt} N - Power level
 * @property {BigInt} offset - Offset from 2^N
 */

/**
 * Complex PPF structure (only used at I/O boundaries)
 * @typedef {Object} PPFComplex
 * @property {PPFStruct} real - Real part PPF
 * @property {PPFStruct} imag - Imaginary part PPF
 */

// =============================================================================
// UTILITY FUNCTIONS
// =============================================================================

/**
 * Check if N is a power of 2
 * @param {number} N - Number to check
 * @returns {boolean} True if N is a power of 2
 */
export function isPowerOfTwo(N) {
    return N > 0 && (N & (N - 1)) === 0;
}

/**
 * Compute log2(N) for power-of-2 N
 * @param {number} N - Power of 2
 * @returns {number} log2(N)
 */
function log2PowerOf2(N) {
    let k = 0;
    let n = N;
    while (n > 1) {
        n >>= 1;
        k++;
    }
    return k;
}

// =============================================================================
// PHASE ARITHMETIC OPERATIONS (RC1-Inspired - O(1))
// =============================================================================

/**
 * Phase addition: (k1/N) + (k2/N) = ((k1 + k2) mod N) / N
 * O(1) operation using modular arithmetic
 * 
 * @param {Phase} phase1 - First phase
 * @param {Phase} phase2 - Second phase
 * @returns {Phase} Sum phase with wrapping
 */
export function phaseAdd(phase1, phase2) {
    if (phase1.N !== phase2.N) {
        throw new Error(`Cannot add phases with different N: ${phase1.N} vs ${phase2.N}`);
    }
    const k_sum = (phase1.k + phase2.k) % phase1.N;
    return { k: k_sum, N: phase1.N };
}

/**
 * Phase subtraction: (k1/N) - (k2/N) = ((k1 - k2) mod N) / N
 * 
 * @param {Phase} phase1 - First phase
 * @param {Phase} phase2 - Second phase
 * @returns {Phase} Difference phase with wrapping
 */
export function phaseSubtract(phase1, phase2) {
    if (phase1.N !== phase2.N) {
        throw new Error(`Cannot subtract phases with different N: ${phase1.N} vs ${phase2.N}`);
    }
    const k_diff = ((phase1.k - phase2.k) % phase1.N + phase1.N) % phase1.N;
    return { k: k_diff, N: phase1.N };
}

/**
 * Phase negation: -k/N = (N-k)/N
 * 
 * @param {Phase} phase - Phase to negate
 * @returns {Phase} Negated phase
 */
export function phaseNegate(phase) {
    if (phase.k === 0n) {
        return { k: 0n, N: phase.N };
    }
    return { k: phase.N - phase.k, N: phase.N };
}

/**
 * Generate twiddle phases for N-point FFT
 * Twiddle factors: ω_N^k = e^(-2πik/N) for k = 0, 1, ..., N-1
 * 
 * @param {number} N - FFT size (power of 2)
 * @param {boolean} inverse - If true, use positive phases (for IFFT)
 * @returns {Array<Phase>} Array of N twiddle phases
 */
export function generateTwiddlePhases(N, inverse = false) {
    if (!isPowerOfTwo(N)) {
        throw new Error(`generateTwiddlePhases: N must be power of 2, got ${N}`);
    }
    const N_big = BigInt(N);
    const phases = [];
    
    for (let k = 0; k < N; k++) {
        const k_big = BigInt(k);
        // Match canonical implementation: canonicalTwiddles uses twiddles[k] directly
        // TwiddleTable stores twiddles as e^(2πij/k) via _phaseToCartesian
        // Canonical uses twiddles[k] for forward FFT, so we use k directly
        // For inverse, canonical uses conjugate twiddles with (N-k) % N
        const phase_k = inverse ? ((N_big - k_big) % N_big) : k_big;
        phases.push({ k: phase_k, N: N_big });
    }
    
    return phases;
}

/**
 * Generate conjugate twiddle phases for IEQFT
 * 
 * @param {number} N - FFT size (power of 2)
 * @returns {Array<Phase>} Array of N conjugate twiddle phases
 */
export function generateConjugateTwiddlePhases(N) {
    if (!isPowerOfTwo(N)) {
        throw new Error(`generateConjugateTwiddlePhases: N must be power of 2, got ${N}`);
    }
    const N_big = BigInt(N);
    const phases = [];
    
    for (let j = 0; j < N; j++) {
        // Conjugate: ω^(-j) = ω^(N-j)
        const conjugateIndex = (N - j) % N;
        phases.push({ k: BigInt(conjugateIndex), N: N_big });
    }
    
    return phases;
}

// =============================================================================
// NATIVE BIT OPERATIONS (Keep in BigInt form - No Encode/Decode)
// =============================================================================

/**
 * Native bit complex addition
 * Computes (a_real/a_den + i*a_imag/a_den) + (b_real/b_den + i*b_imag/b_den)
 * 
 * @param {NativeBitComplex} a - First complex number
 * @param {NativeBitComplex} b - Second complex number
 * @returns {NativeBitComplex} Sum in native bit form
 */
export function nativeBitComplexAdd(a, b) {
    // (a_real/a_den + i*a_imag/a_den) + (b_real/b_den + i*b_imag/b_den)
    // = (a_real*b_den + b_real*a_den) / (a_den*b_den) + i*(a_imag*b_den + b_imag*a_den) / (a_den*b_den)
    
    const real_num = a.real_num * b.real_den + b.real_num * a.real_den;
    const real_den = a.real_den * b.real_den;
    
    const imag_num = a.imag_num * b.imag_den + b.imag_num * a.imag_den;
    const imag_den = a.imag_den * b.imag_den;
    
    return {
        real_num,
        real_den,
        imag_num,
        imag_den
    };
}

/**
 * Native bit complex subtraction
 * 
 * @param {NativeBitComplex} a - First complex number
 * @param {NativeBitComplex} b - Second complex number
 * @returns {NativeBitComplex} Difference in native bit form
 */
export function nativeBitComplexSubtract(a, b) {
    const real_num = a.real_num * b.real_den - b.real_num * a.real_den;
    const real_den = a.real_den * b.real_den;
    
    const imag_num = a.imag_num * b.imag_den - b.imag_num * a.imag_den;
    const imag_den = a.imag_den * b.imag_den;
    
    return {
        real_num,
        real_den,
        imag_num,
        imag_den
    };
}

/**
 * Native bit complex multiplication
 * (a_real + i*a_imag) * (b_real + i*b_imag) = (a_real*b_real - a_imag*b_imag) + i*(a_real*b_imag + a_imag*b_real)
 * 
 * @param {NativeBitComplex} a - First complex number
 * @param {NativeBitComplex} b - Second complex number
 * @returns {NativeBitComplex} Product in native bit form
 */
export function nativeBitComplexMultiply(a, b) {
    // (a_real/a_den + i*a_imag/a_den) * (b_real/b_den + i*b_imag/b_den)
    // = (a_real*b_real - a_imag*b_imag) / (a_den*b_den) + i*(a_real*b_imag + a_imag*b_real) / (a_den*b_den)
    
    const real_num = a.real_num * b.real_num - a.imag_num * b.imag_num;
    const real_den = a.real_den * b.real_den;
    
    const imag_num = a.real_num * b.imag_num + a.imag_num * b.real_num;
    const imag_den = a.imag_den * b.imag_den;
    
    return {
        real_num,
        real_den,
        imag_num,
        imag_den
    };
}

/**
 * Native bit complex scale by power of 2 (bit-shifting optimization)
 * Multiply complex number by 2^shift (or divide if shift < 0)
 * 
 * @param {NativeBitComplex} z - Complex number
 * @param {number} shift - Power of 2 shift (positive = multiply, negative = divide)
 * @returns {NativeBitComplex} Scaled complex number
 */
export function nativeBitComplexScaleByPowerOf2(z, shift) {
    if (shift === 0) {
        return { ...z }; // Return copy
    }
    
    if (shift > 0) {
        // Multiply by 2^shift: left shift numerators
        return {
            real_num: z.real_num << BigInt(shift),
            real_den: z.real_den,
            imag_num: z.imag_num << BigInt(shift),
            imag_den: z.imag_den
        };
    } else {
        // Divide by 2^|shift|: left shift denominators (equivalent to right shift numerators)
        const absShift = -shift;
        return {
            real_num: z.real_num,
            real_den: z.real_den << BigInt(absShift),
            imag_num: z.imag_num,
            imag_den: z.imag_den << BigInt(absShift)
        };
    }
}

/**
 * Native bit complex scale by rational
 * Multiply complex number by (num/den)
 * 
 * @param {NativeBitComplex} z - Complex number
 * @param {BigInt} num - Numerator of scale factor
 * @param {BigInt} den - Denominator of scale factor
 * @returns {NativeBitComplex} Scaled complex number
 */
export function nativeBitComplexScale(z, num, den) {
    return {
        real_num: z.real_num * num,
        real_den: z.real_den * den,
        imag_num: z.imag_num * num,
        imag_den: z.imag_den * den
    };
}

// =============================================================================
// PHASE TO NATIVE BIT CONVERSION (Only when needed)
// =============================================================================

/**
 * Convert phase to native bit complex representation
 * Uses TwiddleTable to get exact Cartesian coordinates
 * 
 * @param {Phase} phase - Phase representation {k, N}
 * @param {BigInt} magnitude - Magnitude (default 1 for unit circle)
 * @returns {NativeBitComplex} Native bit complex representation
 */
export function phaseToNativeBit(phase, magnitude = 1n) {
    // EGPTMath is imported at top level, ensures EGPTMathInstance is set
    const table = new TwiddleTable(Number(phase.N));
    
    // phase.k is already normalized to [0, N) in generateTwiddlePhases
    // For forward FFT, phase.k represents (N-k) mod N which gives e^(-2πik/N)
    // TwiddleTable stores twiddles at index j where phase = j/N (e^(2πij/N))
    // So we need to use phase.k directly as the twiddle index
    const twiddle = table.getTwiddle(Number(phase.k));
    
    // Extract rational coordinates from ComplexEGPTNumber
    const real = twiddle.real;
    const imag = twiddle.imag;
    
    // Get BigInt numerators/denominators using _getPPFRationalParts for exact values
    const realParts = real._getPPFRationalParts();
    const imagParts = imag._getPPFRationalParts();
    
    // Scale by magnitude
    return {
        real_num: realParts.numerator * magnitude,
        real_den: realParts.denominator,
        imag_num: imagParts.numerator * magnitude,
        imag_den: imagParts.denominator
    };
}

// =============================================================================
// TWIDDLE PHASE CACHE
// =============================================================================

/**
 * Global cache for twiddle phases (keyed by N)
 * Avoids regenerating phases for same FFT size
 */
const twiddlePhaseCache = new Map();
const conjugatePhaseCache = new Map();

/**
 * Get or generate twiddle phases for N (cached)
 * 
 * @param {number} N - FFT size (power of 2)
 * @param {boolean} inverse - If true, use positive phases (for IFFT)
 * @returns {Array<Phase>} Array of N twiddle phases
 */
export function getTwiddlePhases(N, inverse = false) {
    const cacheKey = `${N}_${inverse ? 'inv' : 'fwd'}`;
    if (!twiddlePhaseCache.has(cacheKey)) {
        twiddlePhaseCache.set(cacheKey, generateTwiddlePhases(N, inverse));
    }
    return twiddlePhaseCache.get(cacheKey);
}

/**
 * Get or generate conjugate twiddle phases for N (cached)
 * 
 * @param {number} N - FFT size (power of 2)
 * @returns {Array<Phase>} Array of N conjugate twiddle phases
 */
export function getConjugateTwiddlePhases(N) {
    if (!conjugatePhaseCache.has(N)) {
        conjugatePhaseCache.set(N, generateConjugateTwiddlePhases(N));
    }
    return conjugatePhaseCache.get(N);
}

// =============================================================================
// TWIDDLE NATIVE BIT CACHE
// =============================================================================

/**
 * Global cache for twiddles in NativeBitComplex format (keyed by N and inverse flag)
 * Avoids expensive TwiddleTable creation during hot loops
 */
const twiddleNativeBitCache = new Map();
const twiddleTableCache = new Map(); // Cache TwiddleTable instances per N

/**
 * Get TwiddleTable for N (cached)
 * 
 * @param {number} N - FFT size (power of 2)
 * @returns {TwiddleTable} Cached TwiddleTable instance
 */
function getTwiddleTable(N) {
    if (!twiddleTableCache.has(N)) {
        twiddleTableCache.set(N, new TwiddleTable(N));
    }
    return twiddleTableCache.get(N);
}

/**
 * Convert a single phase to NativeBitComplex
 * Uses cached TwiddleTable to avoid recreation
 * 
 * @param {Phase} phase - Phase representation {k, N}
 * @param {BigInt} magnitude - Magnitude (default 1 for unit circle)
 * @returns {NativeBitComplex} Native bit complex representation
 */
function phaseToNativeBitCached(phase, magnitude = 1n) {
    const table = getTwiddleTable(Number(phase.N));
    const twiddle = table.getTwiddle(Number(phase.k));
    
    // Extract rational coordinates from ComplexEGPTNumber
    const real = twiddle.real;
    const imag = twiddle.imag;
    
    // Get BigInt numerators/denominators using _getPPFRationalParts for exact values
    const realParts = real._getPPFRationalParts();
    const imagParts = imag._getPPFRationalParts();
    
    // Scale by magnitude
    return {
        real_num: realParts.numerator * magnitude,
        real_den: realParts.denominator,
        imag_num: imagParts.numerator * magnitude,
        imag_den: imagParts.denominator
    };
}

/**
 * Populate NativeBitComplex twiddles cache for given N and inverse flag
 * 
 * @param {number} N - FFT size (power of 2)
 * @param {boolean} inverse - If true, use conjugate twiddles (for IFFT)
 * @returns {Array<NativeBitComplex>} Array of N twiddles in NativeBitComplex format
 */
function populateTwiddlesNativeBit(N, inverse = false) {
    // Use generateTwiddlePhases with inverse flag for consistency
    // This ensures forward and inverse use the same phase generation logic
    const phases = getTwiddlePhases(N, inverse);
    const twiddlesNative = phases.map(phase => phaseToNativeBitCached(phase));
    return twiddlesNative;
}

/**
 * Get or generate twiddles in NativeBitComplex format (cached)
 * 
 * @param {number} N - FFT size (power of 2)
 * @param {boolean} inverse - If true, use conjugate twiddles (for IFFT)
 * @returns {Array<NativeBitComplex>} Array of N twiddles in NativeBitComplex format
 */
export function getTwiddlesNativeBit(N, inverse = false) {
    const cacheKey = `${N}_${inverse ? 'inv' : 'fwd'}`;
    if (!twiddleNativeBitCache.has(cacheKey)) {
        twiddleNativeBitCache.set(cacheKey, populateTwiddlesNativeBit(N, inverse));
    }
    return twiddleNativeBitCache.get(cacheKey);
}

// =============================================================================
// MATRIX-BASED BUTTERFLY OPERATIONS
// =============================================================================

/**
 * Butterfly operation using matrix form:
 * [X_k    ]   [1   1  ] [E_k      ]
 * [X_{k+N/2}] = [1  -1 ] [ω_k·O_k  ]
 * 
 * Optimized: Uses pre-computed NativeBitComplex twiddles (no conversion overhead)
 * 
 * @param {NativeBitComplex} E - Even component
 * @param {NativeBitComplex} O - Odd component
 * @param {NativeBitComplex} omega_native - Twiddle in NativeBitComplex format (pre-computed)
 * @returns {{upper: NativeBitComplex, lower: NativeBitComplex}} Butterfly outputs
 */
export function butterflyMatrixNative(E, O, omega_native) {
    // Multiply O by twiddle: O_twiddled = ω · O
    const O_twiddled = nativeBitComplexMultiply(omega_native, O);
    
    // Matrix butterfly operation:
    // Upper: E + O_twiddled
    // Lower: E - O_twiddled
    const upper = nativeBitComplexAdd(E, O_twiddled);
    const lower = nativeBitComplexSubtract(E, O_twiddled);
    
    return { upper, lower };
}

// =============================================================================
// PURE PPF EQFT/IEQFT (Using Native Bit Encoding)
// =============================================================================

/**
 * EQFT_PurePPF: Forward transform using native bit encoding
 * 
 * @param {Array<NativeBitComplex>} x - Input signal in native bit form
 * @param {Array<NativeBitComplex>} twiddlesNative - Pre-computed twiddles in NativeBitComplex format
 * @returns {Array<NativeBitComplex>} Frequency domain spectrum in native bit form
 */
export function EQFT_PurePPF(x, twiddlesNative) {
    const N = x.length;
    if (!isPowerOfTwo(N)) {
        throw new Error(`EQFT_PurePPF: N must be power of 2, got ${N}`);
    }
    if (N === 1) {
        return [x[0]];
    }
    
    return EQFT_recursive_native(x, twiddlesNative, 0, N, 1);
}

/**
 * Recursive EQFT with native bit encoding
 * 
 * @private
 * @param {Array<NativeBitComplex>} x - Input signal
 * @param {Array<NativeBitComplex>} twiddlesNative - Pre-computed twiddles in NativeBitComplex format
 * @param {number} start - Start index
 * @param {number} N - Current size
 * @param {number} stride - Stride for indexing
 * @returns {Array<NativeBitComplex>} Transformed result
 */
function EQFT_recursive_native(x, twiddlesNative, start, N, stride) {
    if (N === 1) {
        return [x[start]];
    }
    
    const N2 = N / 2;
    const E = EQFT_recursive_native(x, twiddlesNative, start, N2, stride * 2);
    const O = EQFT_recursive_native(x, twiddlesNative, start + stride, N2, stride * 2);
    
    const result = new Array(N);
    const twiddleStride = Math.floor(twiddlesNative.length / N);
    
    for (let k = 0; k < N2; k++) {
        const twiddleIndex = k * twiddleStride;
        const omega_native = twiddlesNative[twiddleIndex];
        
        const { upper, lower } = butterflyMatrixNative(E[k], O[k], omega_native);
        result[k] = upper;
        result[k + N2] = lower;
    }
    
    return result;
}

/**
 * IEQFT_PurePPF: Inverse transform using native bit encoding
 * 
 * @param {Array<NativeBitComplex>} X - Frequency domain spectrum in native bit form
 * @param {Array<NativeBitComplex>} conjugateTwiddlesNative - Pre-computed conjugate twiddles in NativeBitComplex format
 * @param {boolean} applyNormalization - Whether to apply 1/N normalization (default: true)
 * @returns {Array<NativeBitComplex>} Time domain signal in native bit form
 */
export function IEQFT_PurePPF(X, conjugateTwiddlesNative, applyNormalization = true) {
    const N = X.length;
    if (!isPowerOfTwo(N)) {
        throw new Error(`IEQFT_PurePPF: N must be power of 2, got ${N}`);
    }
    if (N === 1) {
        return [X[0]];
    }
    
    const result = IEQFT_recursive_native(X, conjugateTwiddlesNative, 0, N, 1);
    
    // Apply 1/N normalization using bit-shifting (power of 2)
    if (applyNormalization) {
        const log2N = log2PowerOf2(N);
        for (let i = 0; i < N; i++) {
            result[i] = nativeBitComplexScaleByPowerOf2(result[i], -log2N);
        }
    }
    
    return result;
}

/**
 * Recursive IEQFT with native bit encoding
 * 
 * @private
 * @param {Array<NativeBitComplex>} X - Input spectrum
 * @param {Array<NativeBitComplex>} conjugateTwiddlesNative - Pre-computed conjugate twiddles in NativeBitComplex format
 * @param {number} start - Start index
 * @param {number} N - Current size
 * @param {number} stride - Stride
 * @returns {Array<NativeBitComplex>} Transformed result (unnormalized)
 */
function IEQFT_recursive_native(X, conjugateTwiddlesNative, start, N, stride) {
    if (N === 1) {
        return [X[start]];
    }
    
    const N2 = N / 2;
    const E = IEQFT_recursive_native(X, conjugateTwiddlesNative, start, N2, stride * 2);
    const O = IEQFT_recursive_native(X, conjugateTwiddlesNative, start + stride, N2, stride * 2);
    
    const result = new Array(N);
    const twiddleStride = Math.floor(conjugateTwiddlesNative.length / N);
    
    for (let k = 0; k < N2; k++) {
        const twiddleIndex = k * twiddleStride;
        const omega_conj_native = conjugateTwiddlesNative[twiddleIndex];
        
        const { upper, lower } = butterflyMatrixNative(E[k], O[k], omega_conj_native);
        result[k] = upper;
        result[k + N2] = lower;
    }
    
    return result;
}

// =============================================================================
// I/O CONVERSION (Only at Boundaries)
// =============================================================================

/**
 * Convert ComplexEGPTNumber array to native bit form
 * Only called at input boundary
 * 
 * @param {Array} complexArray - Array of ComplexEGPTNumber
 * @returns {Array<NativeBitComplex>} Native bit array
 */
export function complexEGPTToNativeBit(complexArray) {
    return complexArray.map(z => {
        const real = z.real;
        const imag = z.imag;
        
        // Use _getPPFRationalParts for exact BigInt extraction
        const realParts = real._getPPFRationalParts();
        const imagParts = imag._getPPFRationalParts();
        
        return {
            real_num: realParts.numerator,
            real_den: realParts.denominator,
            imag_num: imagParts.numerator,
            imag_den: imagParts.denominator
        };
    });
}

/**
 * Convert native bit form to ComplexEGPTNumber array
 * Only called at output boundary
 * 
 * @param {Array<NativeBitComplex>} nativeArray - Native bit array
 * @returns {Array} Array of ComplexEGPTNumber
 */
export function nativeBitToComplexEGPT(nativeArray) {
    return nativeArray.map(z => {
        const real = EGPTNumber.fromRational(z.real_num, z.real_den);
        const imag = EGPTNumber.fromRational(z.imag_num, z.imag_den);
        return new ComplexEGPTNumber(real, imag);
    });
}

// =============================================================================
// INTERFACE FUNCTIONS
// =============================================================================

/**
 * FAT_PurePPF: Forward transform interface
 * 
 * @param {Array} input - Input signal (ComplexEGPTNumber array)
 * @returns {Array} Frequency domain spectrum (ComplexEGPTNumber array)
 */
export function fat_pureppf(input) {
    const N = input.length;
    if (!isPowerOfTwo(N)) {
        throw new Error(`FAT_PurePPF requires power-of-2 input length, got ${N}`);
    }
    
    // Convert to native bit (I/O boundary)
    const nativeInput = complexEGPTToNativeBit(input);
    
    // Get twiddles in NativeBitComplex format (cached, pre-computed)
    const twiddlesNative = getTwiddlesNativeBit(N, false);
    
    // Transform using native bit operations
    const nativeOutput = EQFT_PurePPF(nativeInput, twiddlesNative);
    
    // Convert back to ComplexEGPTNumber (I/O boundary)
    return nativeBitToComplexEGPT(nativeOutput);
}

/**
 * IFAT_PurePPF: Inverse transform interface
 * 
 * @param {Array} input - Input spectrum (ComplexEGPTNumber array)
 * @param {boolean} normalize - Apply 1/N normalization (default: true)
 * @returns {Array} Time domain signal (ComplexEGPTNumber array)
 */
export function ifat_pureppf(input, normalize = true) {
    const N = input.length;
    if (!isPowerOfTwo(N)) {
        throw new Error(`IFAT_PurePPF requires power-of-2 input length, got ${N}`);
    }
    
    // Convert to native bit (I/O boundary)
    const nativeInput = complexEGPTToNativeBit(input);
    
    // Get conjugate twiddles in NativeBitComplex format (cached, pre-computed)
    const conjugateTwiddlesNative = getTwiddlesNativeBit(N, true);
    
    // Transform using native bit operations
    const nativeOutput = IEQFT_PurePPF(nativeInput, conjugateTwiddlesNative, normalize);
    
    // Convert back to ComplexEGPTNumber (I/O boundary)
    return nativeBitToComplexEGPT(nativeOutput);
}

