// =============================================================================
// EGPT FAT: FIXED VERSION - Each recursion level gets its own N-gon
// =============================================================================

import { EGPTMath } from '../EGPTMath.js';
import { EGPTNumber } from '../EGPTNumber.js';
import { ComplexEGPTNumber, TwiddleTable } from '../EGPTComplex.js';

// Recursive EQFT - FIXED: Create new TwiddleTable for each recursion level
function _eqft_recursive(signal) {
    const N = signal.length;
    if (N === 1) return [signal[0]];
    
    // CRITICAL FIX: Create TwiddleTable matching current N (N-gon for this level)
    const table = new TwiddleTable(N);

    const E = _eqft_recursive(signal.filter((_, i) => i % 2 === 0));  // N/2-gon
    const O = _eqft_recursive(signal.filter((_, i) => i % 2 !== 0));  // N/2-gon

    const result = new Array(N);
    for (let k = 0; k < N / 2; k++) {
        const omega = table.getTwiddle(k);  // Direct index, no stride needed!
        const t = O[k].multiply(omega);
        result[k] = E[k].add(t);
        result[k + N / 2] = E[k].subtract(t);
    }
    return result;
}

// Recursive IEQFT - FIXED: Create new TwiddleTable for each recursion level
function _ieqft_recursive(spectrum) {
    const N = spectrum.length;
    if (N === 1) return [spectrum[0]];
    
    // CRITICAL FIX: Create TwiddleTable matching current N (N-gon for this level)
    const table = new TwiddleTable(N);

    const E = _ieqft_recursive(spectrum.filter((_, i) => i % 2 === 0));  // N/2-gon
    const O = _ieqft_recursive(spectrum.filter((_, i) => i % 2 !== 0));  // N/2-gon

    const result = new Array(N);
    for (let k = 0; k < N / 2; k++) {
        const omega_conj = table.getTwiddle(-k);  // Conjugate, direct index
        const t = O[k].multiply(omega_conj);
        result[k] = E[k].add(t);
        result[k + N / 2] = E[k].subtract(t);
    }
    return result;
}

// Public API
export function fat(signal) {
    return _eqft_recursive(signal);
}

export function ifat(spectrum) {
    const N = spectrum.length;
    const result_unscaled = _ieqft_recursive(spectrum);
    return result_unscaled.map(c => c.scaleByRational(1n, BigInt(N)));
}

// Aliases
export const fft = fat;
export const ifft = ifat;

// QFT interface
export function qft(signal) {
    return fat(signal);
}

export function iqft(spectrum) {
    return ifat(spectrum);
}

