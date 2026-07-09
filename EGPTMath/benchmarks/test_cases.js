// =============================================================================
// FAT BENCHMARK: TEST CASE GENERATORS
// Generates various test signals for benchmarking FAT vs fft.js
//
// Author: E. Abadir
// Purpose: Provide comprehensive test case generators for benchmarking
// =============================================================================

import { EGPTNumber } from '../EGPTNumber.js';
import { ComplexEGPTNumber } from '../EGPTComplex.js';

/**
 * Generate impulse signal (Kronecker delta): x[0] = 1, x[k≠0] = 0
 * 
 * @param {number} N - Signal length (must be power of 2)
 * @param {number} impulseIndex - Index where impulse occurs (default: 0)
 * @returns {Array<ComplexEGPTNumber>} Impulse signal
 */
export function generateImpulseSignal(N, impulseIndex = 0) {
    const signal = [];
    for (let i = 0; i < N; i++) {
        if (i === impulseIndex) {
            signal.push(new ComplexEGPTNumber(
                EGPTNumber.fromBigInt(1n),
                EGPTNumber.fromBigInt(0n)
            ));
        } else {
            signal.push(new ComplexEGPTNumber(
                EGPTNumber.fromBigInt(0n),
                EGPTNumber.fromBigInt(0n)
            ));
        }
    }
    return signal;
}

/**
 * Generate step function: x[0..k] = 1, x[k+1..N-1] = 0
 * 
 * @param {number} N - Signal length
 * @param {number} stepIndex - Index where step occurs (default: N/2)
 * @returns {Array<ComplexEGPTNumber>} Step signal
 */
export function generateStepFunction(N, stepIndex = null) {
    const step = stepIndex !== null ? stepIndex : Math.floor(N / 2);
    const signal = [];
    for (let i = 0; i < N; i++) {
        const value = i <= step ? 1n : 0n;
        signal.push(new ComplexEGPTNumber(
            EGPTNumber.fromBigInt(value),
            EGPTNumber.fromBigInt(0n)
        ));
    }
    return signal;
}

/**
 * Generate sinusoidal signal: x[n] = A * cos(2π * freq * n / N)
 * 
 * @param {number} N - Signal length
 * @param {number} frequency - Frequency (cycles per N samples)
 * @param {number} amplitude - Amplitude (default: 1)
 * @param {number} phase - Phase offset in radians (default: 0)
 * @returns {Array<ComplexEGPTNumber>} Sinusoidal signal
 */
export function generateSinusoid(N, frequency, amplitude = 1, phase = 0) {
    const signal = [];
    for (let i = 0; i < N; i++) {
        const angle = 2 * Math.PI * frequency * i / N + phase;
        const real = amplitude * Math.cos(angle);
        const imag = amplitude * Math.sin(angle);
        signal.push(new ComplexEGPTNumber(
            EGPTNumber.fromRational(
                BigInt(Math.round(real * 1e15)),
                1000000000000000n
            ),
            EGPTNumber.fromRational(
                BigInt(Math.round(imag * 1e15)),
                1000000000000000n
            )
        ));
    }
    return signal;
}

/**
 * Generate random signal with uniform distribution
 * 
 * @param {number} N - Signal length
 * @param {number} min - Minimum value (default: -1)
 * @param {number} max - Maximum value (default: 1)
 * @returns {Array<ComplexEGPTNumber>} Random signal
 */
export function generateRandomSignal(N, min = -1, max = 1) {
    const signal = [];
    const range = max - min;
    for (let i = 0; i < N; i++) {
        const real = min + Math.random() * range;
        const imag = min + Math.random() * range;
        signal.push(new ComplexEGPTNumber(
            EGPTNumber.fromRational(
                BigInt(Math.round(real * 1e15)),
                1000000000000000n
            ),
            EGPTNumber.fromRational(
                BigInt(Math.round(imag * 1e15)),
                1000000000000000n
            )
        ));
    }
    return signal;
}

/**
 * Generate DC signal (all ones): x[n] = 1 for all n
 * 
 * @param {number} N - Signal length
 * @returns {Array<ComplexEGPTNumber>} DC signal
 */
export function generateDCSignal(N) {
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
 * Generate zero signal (all zeros)
 * 
 * @param {number} N - Signal length
 * @returns {Array<ComplexEGPTNumber>} Zero signal
 */
export function generateZeroSignal(N) {
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
 * Generate real-only signal (imaginary part = 0)
 * 
 * @param {number} N - Signal length
 * @param {Function} realFunction - Function f(n) that returns real value for index n
 * @returns {Array<ComplexEGPTNumber>} Real signal
 */
export function generateRealSignal(N, realFunction) {
    const signal = [];
    for (let i = 0; i < N; i++) {
        const real = realFunction(i);
        signal.push(new ComplexEGPTNumber(
            EGPTNumber.fromRational(
                BigInt(Math.round(real * 1e15)),
                1000000000000000n
            ),
            EGPTNumber.fromBigInt(0n)
        ));
    }
    return signal;
}

/**
 * Generate high precision test case with very large BigInt values
 * 
 * @param {number} N - Signal length
 * @param {bigint} magnitude - Magnitude of BigInt values
 * @returns {Array<ComplexEGPTNumber>} High precision signal
 */
export function generateHighPrecisionSignal(N, magnitude = 9999999999999999999999999999999999999999n) {
    const signal = [];
    for (let i = 0; i < N; i++) {
        signal.push(new ComplexEGPTNumber(
            EGPTNumber.fromBigInt(magnitude + BigInt(i)),
            EGPTNumber.fromBigInt(0n)
        ));
    }
    return signal;
}

/**
 * Generate high precision rational fraction signal
 * 
 * @param {number} N - Signal length
 * @param {bigint} numerator - Large numerator
 * @param {bigint} denominator - Large denominator
 * @returns {Array<ComplexEGPTNumber>} High precision rational signal
 */
export function generateHighPrecisionRationalSignal(N, numerator, denominator) {
    const signal = [];
    for (let i = 0; i < N; i++) {
        signal.push(new ComplexEGPTNumber(
            EGPTNumber.fromRational(numerator, denominator),
            EGPTNumber.fromRational(
                BigInt(i) * numerator,
                denominator
            )
        ));
    }
    return signal;
}

/**
 * Convert ComplexEGPTNumber array to Float64Array (fft.js format)
 * 
 * @param {Array<ComplexEGPTNumber>} signal - ComplexEGPTNumber signal
 * @returns {Float64Array} Interleaved format [re0, im0, re1, im1, ...]
 */
export function toFloat64Array(signal) {
    const result = new Float64Array(signal.length * 2);
    for (let i = 0; i < signal.length; i++) {
        result[i * 2] = signal[i].real.toNumber();
        result[i * 2 + 1] = signal[i].imag.toNumber();
    }
    return result;
}

/**
 * Convert Float64Array to ComplexEGPTNumber array
 * 
 * @param {Float64Array} floatArray - Interleaved format
 * @returns {Array<ComplexEGPTNumber>} ComplexEGPTNumber signal
 */
export function fromFloat64Array(floatArray) {
    const N = floatArray.length / 2;
    const signal = [];
    for (let i = 0; i < N; i++) {
        signal.push(new ComplexEGPTNumber(
            EGPTNumber.fromRational(
                BigInt(Math.round(floatArray[i * 2] * 1e15)),
                1000000000000000n
            ),
            EGPTNumber.fromRational(
                BigInt(Math.round(floatArray[i * 2 + 1] * 1e15)),
                1000000000000000n
            )
        ));
    }
    return signal;
}

/**
 * All test case generators
 */
export const testCaseGenerators = {
    impulse: generateImpulseSignal,
    step: generateStepFunction,
    sinusoid: generateSinusoid,
    random: generateRandomSignal,
    dc: generateDCSignal,
    zero: generateZeroSignal,
    real: generateRealSignal,
    highPrecision: generateHighPrecisionSignal,
    highPrecisionRational: generateHighPrecisionRationalSignal
};













