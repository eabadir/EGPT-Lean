// =============================================================================
// EGPT FAT: FAST ABADIR TRANSFORM - FINAL CANONICAL IMPLEMENTATION
//
// Author: E. Abadir
// Copyright (C) 2026 Essam Abadir
// Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
// See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
// Provided WITHOUT ANY WARRANTY. See the DCSL for details.
//
// Paradigm: Exact discrete FFT/IFFT using pure phase-space arithmetic,
// compliant with the EQFT White Paper.
// =============================================================================

import { EGPTMath } from '../EGPTMath.js';
import { EGPTNumber } from '../EGPTNumber.js';
import { ComplexEGPTNumber, TwiddleTable } from '../EGPTComplex.js';

// Recursive EQFT (forward transform)
function _eqft_recursive(signal, table) {
    const N = signal.length;
    if (N === 1) return [signal[0]];

    // Decimate (even-odd split per Cooley-Tukey)
    const E = _eqft_recursive(signal.filter((_, i) => i % 2 === 0), table);
    const O = _eqft_recursive(signal.filter((_, i) => i % 2 !== 0), table);

    // Use parent table with stride to access N-gon vertices
    const result = new Array(N);
    const twiddleStride = table.k / N;
    
    for (let k = 0; k < N / 2; k++) {
        const omega = table.getTwiddle(k * twiddleStride);
        const t = O[k].multiply(omega);
        result[k] = E[k].add(t);
        result[k + N / 2] = E[k].subtract(t);
    }
    
    return result;
}

// Recursive IEQFT (inverse transform)
function _ieqft_recursive(spectrum, table) {
    const N = spectrum.length;
    if (N === 1) return [spectrum[0]];

    // Decimate
    const E = _ieqft_recursive(spectrum.filter((_, i) => i % 2 === 0), table);
    const O = _ieqft_recursive(spectrum.filter((_, i) => i % 2 !== 0), table);

    // Use parent table with stride
    const result = new Array(N);
    const twiddleStride = table.k / N;
    
    for (let k = 0; k < N / 2; k++) {
        const omega_conj = table.getTwiddle(-k * twiddleStride);
        const t = O[k].multiply(omega_conj);
        result[k] = E[k].add(t);
        result[k + N / 2] = E[k].subtract(t);
    }
    
    return result;
}


/**
 * Determine maximum n-gon level needed for signal
 * This ensures the twiddle table can represent all signal values
 */
function getSignalMaxNgonSize(signal) {
    let maxDenom = 1;
    
    for (const val of signal) {
        try {
            // Try to extract phase denominator
            const phase = val.getPhase();
            const parts = phase._getPPFRationalParts();
            const denom = Number(parts.denominator);
            maxDenom = Math.max(maxDenom, denom);
        } catch (e) {
            // If phase extraction fails, value might not be on unit circle
            // Use signal length as safe default
            maxDenom = Math.max(maxDenom, signal.length);
        }
    }
    
    // Return max of signal's max denominator and signal length
    // This ensures we can represent all values AND do the full FFT
    return Math.max(maxDenom, signal.length);
}

// Public API
export function fat(signal) {
    const N = signal.length;
    // Create table large enough for signal's maximum n-gon level
    const tableSize = getSignalMaxNgonSize(signal);
    const table = new TwiddleTable(tableSize);
    return _eqft_recursive(signal, table);
}

export function ifat(spectrum) {
    const N = spectrum.length;
    // For inverse, spectrum values are combinations, so use N as table size
    const table = new TwiddleTable(N);
    const result_unscaled = _ieqft_recursive(spectrum, table);
    // Apply 1/N normalization
    return result_unscaled.map(c => c.scaleByRational(1n, BigInt(N)));
}

// Aliases for standard naming
export const fft = fat;
export const ifft = ifat;

// QFT interface (phase-space, unit-circle focused)
// Same implementation as fat/ifat, but documents unit-circle restriction for exact arithmetic
export function qft(signal) {
    // QFT interface: for best results, use unit-circle signals (twiddle values)
    // obtained from TwiddleTable.getTwiddle() for exact phase arithmetic
    return fat(signal);
}

export function iqft(spectrum) {
    // Inverse QFT: reconstructs signal in phase space
    return ifat(spectrum);
}

