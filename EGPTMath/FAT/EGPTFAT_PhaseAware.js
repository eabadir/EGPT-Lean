// =============================================================================
// EGPT FAT: PHASE-AWARE VERSION - Dynamic Twiddle Generation
//
// KEY INSIGHT: Can't use precomputed twiddle tables - must generate dynamically
// based on the actual phase structure of the signal at each recursion level.
// This handles phase winding correctly.
// =============================================================================

import { EGPTMath } from '../EGPTMath.js';
import { EGPTNumber } from '../EGPTNumber.js';
import { ComplexEGPTNumber, TwiddleTable } from '../EGPTComplex.js';

/**
 * Detect the effective N-gon size from signal phase structure
 * Returns the LCM of all phase denominators in the signal
 */
function detectPhaseStructure(signal) {
    if (signal.length === 0) return 1;
    
    // For unit-circle points, extract their phase denominators
    const denominators = [];
    for (const val of signal) {
        try {
            const phase = val.getPhase();
            const parts = phase._getPPFRationalParts();
            if (parts.denominator > 1n) {
                denominators.push(Number(parts.denominator));
            }
        } catch (e) {
            // If getPhase() fails, value might not be on unit circle
            // Fall back to array length
            return signal.length;
        }
    }
    
    if (denominators.length === 0) return signal.length;
    
    // Calculate LCM of all denominators to get effective N-gon
    const lcm = (a, b) => {
        const gcd = (x, y) => y === 0 ? x : gcd(y, x % y);
        return Math.abs(a * b) / gcd(a, b);
    };
    
    let result = denominators[0];
    for (let i = 1; i < denominators.length; i++) {
        result = lcm(result, denominators[i]);
    }
    
    // Cap at signal length or next power of 2
    return Math.min(result, signal.length);
}

// Recursive EQFT with phase-aware twiddle generation
function _eqft_recursive_phase_aware(signal) {
    const N = signal.length;
    if (N === 1) return [signal[0]];

    const E = _eqft_recursive_phase_aware(signal.filter((_, i) => i % 2 === 0));
    const O = _eqft_recursive_phase_aware(signal.filter((_, i) => i % 2 !== 0));

    // CRITICAL: Detect actual phase structure and generate appropriate twiddles
    const effectiveN = detectPhaseStructure(signal);
    const table = new TwiddleTable(effectiveN);
    
    const result = new Array(N);
    const twiddleStride = effectiveN / N;
    
    for (let k = 0; k < N / 2; k++) {
        const omega = table.getTwiddle(k * twiddleStride);
        const t = O[k].multiply(omega);
        result[k] = E[k].add(t);
        result[k + N / 2] = E[k].subtract(t);
    }
    return result;
}

// Recursive IEQFT with phase-aware twiddle generation
function _ieqft_recursive_phase_aware(spectrum) {
    const N = spectrum.length;
    if (N === 1) return [spectrum[0]];

    const E = _ieqft_recursive_phase_aware(spectrum.filter((_, i) => i % 2 === 0));
    const O = _ieqft_recursive_phase_aware(spectrum.filter((_, i) => i % 2 !== 0));

    // CRITICAL: Detect actual phase structure and generate appropriate twiddles
    const effectiveN = detectPhaseStructure(spectrum);
    const table = new TwiddleTable(effectiveN);
    
    const result = new Array(N);
    const twiddleStride = effectiveN / N;
    
    for (let k = 0; k < N / 2; k++) {
        const omega_conj = table.getTwiddle(-k * twiddleStride);
        const t = O[k].multiply(omega_conj);
        result[k] = E[k].add(t);
        result[k + N / 2] = E[k].subtract(t);
    }
    return result;
}

// Public API
export function fat(signal) {
    return _eqft_recursive_phase_aware(signal);
}

export function ifat(spectrum) {
    const N = spectrum.length;
    const result_unscaled = _ieqft_recursive_phase_aware(spectrum);
    return result_unscaled.map(c => c.scaleByRational(1n, BigInt(N)));
}

export const fft = fat;
export const ifft = ifat;

export function qft(signal) {
    return fat(signal);
}

export function iqft(spectrum) {
    return ifat(spectrum);
}

