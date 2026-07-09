// =============================================================================
// EGPT FAT: Level-Tracking Version - Preserves Phase Denominators
//
// KEY: Track n-gon level (l) through recursion to ensure correct twiddle count
// at each stage. l determines n-gon size = 2^(l+1) = number of twiddles needed.
// =============================================================================

import { EGPTMath } from '../EGPTMath.js';
import { EGPTNumber } from '../EGPTNumber.js';
import { ComplexEGPTNumber, TwiddleTable } from '../EGPTComplex.js';

/**
 * Encode natural number to PPF
 */
function encodePPF(N) {
    if (N === 0) return { N_level: 0, offset: 0 };
    const bitlength = N.toString(2).length;
    return {
        N_level: bitlength - 1,
        offset: N - (1 << (bitlength - 1))
    };
}

/**
 * Determine maximum n-gon level from signal
 * For ComplexEGPTNumber with integer real part: use PPF encoding of that integer
 * For unit-circle values: extract from phase denominator
 * For complex combinations: use signal length as fallback
 */
function getMaxLevel(signal) {
    let maxLevel = 0;
    
    for (const val of signal) {
        try {
            // First, try to extract as integer (for traditional FFT inputs like [1,2,3,...])
            const parts = val.real._getPPFRationalParts();
            if (parts.denominator === 1n && parts.numerator > 0n) {
                // It's a positive integer - use PPF encoding
                const re = Number(parts.numerator);
                const ppf = encodePPF(re);
                maxLevel = Math.max(maxLevel, ppf.N_level);
                continue;
            }
            
            // Second, try to extract phase (for unit-circle twiddle values)
            const phase = val.getPhase();
            const phase_parts = phase._getPPFRationalParts();
            
            // Phase denominator = 2^(level+1), so level = log2(denom) - 1
            const denom = Number(phase_parts.denominator);
            if (denom > 1) {
                const level = Math.log2(denom) - 1;
                maxLevel = Math.max(maxLevel, level);
            }
        } catch (e) {
            // If both extraction methods fail, this is a complex combination
            // (e.g., spectrum values after forward transform)
            // Use signal length as safe fallback
            const N = signal.length;
            const ppf = encodePPF(N);
            maxLevel = Math.max(maxLevel, ppf.N_level);
        }
    }
    
    // At minimum, need log2(N) level for N samples
    const N = signal.length;
    const minLevel = Math.ceil(Math.log2(N)) - 1;
    
    return Math.max(maxLevel, minLevel);
}

/**
 * Recursive EQFT with explicit level tracking
 * @param {Array<ComplexEGPTNumber>} signal - Input signal
 * @param {number} l - Current n-gon level (determines twiddle count = 2^(l+1))
 */
function _eqft_recursive_with_level(signal, l) {
    const N = signal.length;
    if (N === 1) return [signal[0]];
    
    // Decimate
    const even_signal = signal.filter((_, i) => i % 2 === 0);
    const odd_signal = signal.filter((_, i) => i % 2 !== 0);
    
    // KEY: Compute l for EACH branch from actual signal content
    // The decrement is NOT uniform - it depends on what values are in each branch
    const l_even = getMaxLevel(even_signal);
    const l_odd = getMaxLevel(odd_signal);
    
    // Recurse with branch-specific levels
    const E = _eqft_recursive_with_level(even_signal, l_even);
    const O = _eqft_recursive_with_level(odd_signal, l_odd);
    
    // At this level, use n-gon of size 2^(l+1)
    const ngon_size = 1 << (l + 1);
    const table = new TwiddleTable(ngon_size);
    
    // Combine with butterfly using stride
    const result = new Array(N);
    const twiddleStride = ngon_size / N;
    
    for (let k = 0; k < N / 2; k++) {
        const omega = table.getTwiddle(k * twiddleStride);
        const t = O[k].multiply(omega);
        result[k] = E[k].add(t);
        result[k + N / 2] = E[k].subtract(t);
    }
    
    return result;
}

/**
 * Recursive IEQFT with explicit level tracking
 */
function _ieqft_recursive_with_level(spectrum, l) {
    const N = spectrum.length;
    if (N === 1) return [spectrum[0]];
    
    // Decimate
    const even_spectrum = spectrum.filter((_, i) => i % 2 === 0);
    const odd_spectrum = spectrum.filter((_, i) => i % 2 !== 0);
    
    // KEY: Compute l for EACH branch from actual signal content
    // After forward transform, spectrum values are combinations, so getMaxLevel
    // will fall back to using array length (which is correct for inverse)
    const l_even = getMaxLevel(even_spectrum);
    const l_odd = getMaxLevel(odd_spectrum);
    
    // Recurse with branch-specific levels
    const E = _ieqft_recursive_with_level(even_spectrum, l_even);
    const O = _ieqft_recursive_with_level(odd_spectrum, l_odd);
    
    // At this level, use n-gon of size 2^(l+1)
    const ngon_size = 1 << (l + 1);
    const table = new TwiddleTable(ngon_size);
    
    // Combine with butterfly using stride
    const result = new Array(N);
    const twiddleStride = ngon_size / N;
    
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
    const l_max = getMaxLevel(signal);
    return _eqft_recursive_with_level(signal, l_max);
}

export function ifat(spectrum) {
    const N = spectrum.length;
    const l_max = getMaxLevel(spectrum);
    const result_unscaled = _ieqft_recursive_with_level(spectrum, l_max);
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

