// =============================================================================
// EGPT FAT FORMATTERS - CANONICAL REFERENCE IMPLEMENTATION
// Format conversion utilities for FAT (Fast Abadir Transform)
//
// Author: E. Abadir
// Purpose: Convert between ComplexEGPTNumber and various external formats
//          Provides compatibility with fft.js and other FFT libraries
//          Includes enhanced features: symmetry validation/enforcement,
//          normalization/denormalization helpers
// =============================================================================
import { SimpleLogger } from '../DebugLogger.js';
import { EGPTNumber } from '../EGPTNumber.js';
import { ComplexEGPTNumber, TwiddleTable } from '../EGPTComplex.js';
import { EGPTMath } from '../EGPTMath.js';

SimpleLogger.log("🎓 CANONICAL INFORMATION SPACE: FAT format conversion");
SimpleLogger.log("📁 File location: EGPT/js/model/EGPTFATFormatters.js");
SimpleLogger.log("🎯 EGPTFATFormatters: Format conversion utilities");

// =============================================================================
// BASIC FORMAT CONVERSION
// =============================================================================

/**
 * Convert ComplexEGPTNumber array to fft.js Float64Array format
 * 
 * fft.js uses interleaved format: [re0, im0, re1, im1, ...]
 * 
 * @param {Array<ComplexEGPTNumber>} complexArray - Array of complex numbers
 * @returns {Float64Array} Interleaved real/imaginary pairs
 * 
 * @example
 * ```javascript
 * const spectrum = [z0, z1, z2, ...]; // ComplexEGPTNumber array
 * const floatArray = complexEGPTArrayToFloat64Array(spectrum);
 * // Result: Float64Array([re0, im0, re1, im1, ...])
 * ```
 */
export function complexEGPTArrayToFloat64Array(complexArray) {
    const N = complexArray.length;
    const result = new Float64Array(N * 2);
    for (let i = 0; i < N; i++) {
        result[i * 2] = complexArray[i].real.toNumber();
        result[i * 2 + 1] = complexArray[i].imag.toNumber();
    }
    return result;
}

/**
 * Convert fft.js Float64Array format to ComplexEGPTNumber array
 * 
 * Input: [re0, im0, re1, im1, ...]
 * Uses higher precision scaling for conversion to minimize rounding errors
 * 
 * @param {Float64Array} floatArray - Interleaved real/imaginary pairs
 * @param {bigint} scale - Scaling factor for precision (default: 1e15)
 * @returns {Array<ComplexEGPTNumber>} Array of complex numbers
 * 
 * @example
 * ```javascript
 * const floatArray = new Float64Array([1.0, 2.0, 3.0, 4.0, ...]);
 * const complexArray = float64ArrayToComplexEGPTArray(floatArray);
 * // Result: Array of ComplexEGPTNumber
 * ```
 */
export function float64ArrayToComplexEGPTArray(floatArray, scale = 1000000000000000n) {
    const N = floatArray.length / 2;
    const result = [];
    for (let i = 0; i < N; i++) {
        const real = EGPTNumber.fromRational(
            BigInt(Math.round(floatArray[i * 2] * Number(scale))),
            scale
        );
        const imag = EGPTNumber.fromRational(
            BigInt(Math.round(floatArray[i * 2 + 1] * Number(scale))),
            scale
        );
        result.push(new ComplexEGPTNumber(real, imag));
    }
    return result;
}

/**
 * Convert ComplexEGPTNumber array to simple object array format
 * 
 * Output format: [{real: number, imag: number}, ...]
 * 
 * @param {Array<ComplexEGPTNumber>} complexArray - Array of complex numbers
 * @returns {Array<{real: number, imag: number}>} Array of simple objects
 */
export function complexEGPTArrayToSimpleArray(complexArray) {
    return complexArray.map(z => ({
        real: z.real.toNumber(),
        imag: z.imag.toNumber()
    }));
}

/**
 * Convert simple object array to ComplexEGPTNumber array
 * 
 * Input format: [{real: number, imag: number}, ...]
 * 
 * @param {Array<{real: number, imag: number}>} simpleArray - Array of simple objects
 * @param {bigint} scale - Scaling factor for precision (default: 1e15)
 * @returns {Array<ComplexEGPTNumber>} Array of complex numbers
 */
export function simpleArrayToComplexEGPTArray(simpleArray, scale = 1000000000000000n) {
    return simpleArray.map(({ real, imag }) => {
        const real_egpt = EGPTNumber.fromRational(
            BigInt(Math.round(real * Number(scale))),
            scale
        );
        const imag_egpt = EGPTNumber.fromRational(
            BigInt(Math.round(imag * Number(scale))),
            scale
        );
        return new ComplexEGPTNumber(real_egpt, imag_egpt);
    });
}

// =============================================================================
// FORMAT DETECTION AND AUTO-CONVERSION
// =============================================================================

/**
 * Detect input format and convert to ComplexEGPTNumber array
 * 
 * Supported formats:
 * - Array<ComplexEGPTNumber> - Returns as-is
 * - Float64Array - Interleaved format (fft.js style)
 * - Array<{real: number, imag: number}> - Simple object array
 * - Array<number> - Real-only signal (imaginary part set to 0)
 * 
 * @param {*} input - Input in any supported format
 * @param {bigint} scale - Scaling factor for float conversions (default: 1e15)
 * @returns {Array<ComplexEGPTNumber>} Array of complex numbers
 */
export function detectAndConvertToComplexEGPTArray(input, scale = 1000000000000000n) {
    if (!input || input.length === 0) {
        throw new Error('Input must be a non-empty array');
    }
    
    // Already ComplexEGPTNumber array
    if (input[0] instanceof ComplexEGPTNumber) {
        return [...input]; // Return copy
    }
    
    // Float64Array (interleaved fft.js format)
    if (input instanceof Float64Array) {
        return float64ArrayToComplexEGPTArray(input, scale);
    }
    
    // Array of {real, imag} objects
    if (typeof input[0] === 'object' && 'real' in input[0] && 'imag' in input[0]) {
        return simpleArrayToComplexEGPTArray(input, scale);
    }
    
    // Array of numbers (real-only signal)
    if (typeof input[0] === 'number') {
        return input.map(val => {
            const real = EGPTNumber.fromRational(
                BigInt(Math.round(val * Number(scale))),
                scale
            );
            const imag = EGPTNumber.fromBigInt(0n);
            return new ComplexEGPTNumber(real, imag);
        });
    }
    
    throw new Error(`Unsupported input format. Expected ComplexEGPTNumber[], Float64Array, Array<{real,imag}>, or Array<number>`);
}

/**
 * Detect input format type
 * 
 * @param {*} input - Input to detect
 * @returns {string} Format type: 'complex', 'float64', 'simple', 'real'
 */
export function detectInputFormat(input) {
    if (!input || input.length === 0) {
        throw new Error('Cannot detect format of empty input');
    }
    
    if (input[0] instanceof ComplexEGPTNumber) {
        return 'complex';
    }
    
    if (input instanceof Float64Array) {
        return 'float64';
    }
    
    if (typeof input[0] === 'object' && 'real' in input[0] && 'imag' in input[0]) {
        return 'simple';
    }
    
    if (typeof input[0] === 'number') {
        return 'real';
    }
    
    throw new Error(`Unable to detect input format`);
}

/**
 * Convert ComplexEGPTNumber array to requested output format
 * 
 * @param {Array<ComplexEGPTNumber>} complexArray - Array of complex numbers
 * @param {string} format - Output format: 'complex', 'float64', 'simple', 'real'
 * @returns {*} Output in requested format
 * 
 * @example
 * ```javascript
 * const spectrum = [z0, z1, ...]; // ComplexEGPTNumber array
 * const floatArray = convertComplexEGPTArrayToFormat(spectrum, 'float64');
 * const simpleArray = convertComplexEGPTArrayToFormat(spectrum, 'simple');
 * ```
 */
export function convertComplexEGPTArrayToFormat(complexArray, format = 'complex') {
    switch (format.toLowerCase()) {
        case 'complex':
            return complexArray; // Return as-is
        
        case 'float64':
            return complexEGPTArrayToFloat64Array(complexArray);
        
        case 'simple':
            return complexEGPTArrayToSimpleArray(complexArray);
        
        case 'real':
            // Return only real parts as array of numbers
            return complexArray.map(z => z.real.toNumber());
        
        default:
            throw new Error(`Unsupported output format: ${format}. Expected 'complex', 'float64', 'simple', or 'real'`);
    }
}

// =============================================================================
// ENHANCED FORMAT CONVERSION (SYMMETRY & VALIDATION)
// =============================================================================

/**
 * Check if a ComplexEGPTNumber array represents a real signal
 * 
 * A real signal has all imaginary parts zero (or very small, within tolerance).
 * 
 * @param {Array<ComplexEGPTNumber>} array - Array of complex numbers
 * @param {number} tolerance - Tolerance for zero check (default: 1e-10)
 * @returns {boolean} True if all imaginary parts are effectively zero
 */
export function isRealSignal(array, tolerance = 1e-10) {
    return array.every(z => {
        const im = Math.abs(z.imag.toNumber());
        return im < tolerance;
    });
}

/**
 * Check if a ComplexEGPTNumber array represents a conjugate-symmetric spectrum
 * 
 * For a real signal, the FFT spectrum must be conjugate-symmetric:
 * - X[0] and X[N/2] must be real (or tiny imaginary)
 * - X[k] = conjugate(X[N-k]) for k = 1..N/2-1
 * 
 * @param {Array<ComplexEGPTNumber>} array - Array of complex numbers
 * @param {number} N - FFT size
 * @param {number} tolerance - Tolerance for equality check (default: 1e-10)
 * @returns {boolean} True if spectrum is conjugate-symmetric
 */
export function isConjugateSymmetric(array, N, tolerance = 1e-10) {
    // X[0] and X[N/2] should be real (or tiny imaginary)
    if (Math.abs(array[0].imag.toNumber()) > tolerance) return false;
    if (N % 2 === 0 && Math.abs(array[N/2].imag.toNumber()) > tolerance) return false;
    
    // X[k] should equal conjugate of X[N-k] for k = 1..N/2-1
    for (let k = 1; k < N / 2; k++) {
        const re_k = array[k].real.toNumber();
        const im_k = array[k].imag.toNumber();
        const re_Nk = array[N - k].real.toNumber();
        const im_Nk = array[N - k].imag.toNumber();
        
        // X[k] should equal X*[N-k]
        // So: re_k = re_Nk and im_k = -im_Nk
        const re_err = Math.abs(re_k - re_Nk);
        const im_err = Math.abs(im_k + im_Nk);
        
        if (re_err > tolerance || im_err > tolerance) {
            return false;
        }
    }
    
    return true;
}

/**
 * Enforce conjugate symmetry on a spectrum
 * 
 * Useful for restoring symmetry after format conversion or rounding errors.
 * Modifies the array to ensure:
 * - X[0] and X[N/2] are real
 * - X[k] = conjugate(X[N-k]) for k = 1..N/2-1
 * 
 * @param {Array<ComplexEGPTNumber>} array - Array of complex numbers (spectrum)
 * @param {number} N - FFT size
 * @returns {Array<ComplexEGPTNumber>} Array with enforced conjugate symmetry
 */
export function enforceConjugateSymmetry(array, N) {
    const result = array.map((z, i) => z.clone());
    const N2 = Math.floor(N / 2);
    
    // X[0] must be real
    result[0] = new ComplexEGPTNumber(array[0].real, EGPTNumber.fromBigInt(0n));
    
    // X[N/2] must be real (if N is even)
    if (N % 2 === 0 && N2 < N) {
        result[N2] = new ComplexEGPTNumber(array[N2].real, EGPTNumber.fromBigInt(0n));
    }
    
    // Enforce X[k] = X*[N-k] for k = 1..N/2-1
    for (let k = 1; k < N2; k++) {
        const Nk = N - k;
        
        // For conjugate symmetry: X[k] = X*[N-k]
        // So: re_k = re_Nk and im_k = -im_Nk
        // Average the real parts, and set imaginary parts to be negatives
        const re_k = array[k].real;
        const re_Nk = array[Nk].real;
        const im_k = array[k].imag;
        
        // Average real parts
        const re_avg = EGPTMath.divide(
            EGPTMath.add(re_k, re_Nk),
            EGPTNumber.fromBigInt(2n)
        );
        
        // For imaginary: im_k should equal -im_Nk
        // So: (im_k + (-im_Nk)) / 2 = (im_k - im_Nk) / 2
        const im_diff = EGPTMath.subtract(im_k, array[Nk].imag);
        const im_avg = EGPTMath.divide(im_diff, EGPTNumber.fromBigInt(2n));
        
        result[k] = new ComplexEGPTNumber(re_avg, im_avg);
        result[Nk] = new ComplexEGPTNumber(re_avg, EGPTMath.multiply(im_avg, EGPTNumber.fromBigInt(-1n)));
    }
    
    return result;
}

/**
 * Enhanced Float64Array to ComplexEGPTNumber conversion with symmetry handling
 * 
 * Includes optional symmetry validation and enforcement for real signals.
 * 
 * @param {Float64Array} floatArray - Interleaved real/imaginary pairs
 * @param {Object} options - Conversion options
 * @param {bigint} options.scale - Scaling factor for precision (default: 1e15)
 * @param {boolean} options.enforceSymmetry - Enforce conjugate symmetry for real signals (default: false)
 * @param {number} options.tolerance - Tolerance for symmetry checks (default: 1e-10)
 * @returns {Array<ComplexEGPTNumber>} Array of complex numbers
 */
export function float64ArrayToComplexEGPTArrayEnhanced(floatArray, options = {}) {
    const { 
        scale = 1000000000000000n,
        enforceSymmetry = false,
        tolerance = 1e-10
    } = options;
    
    const N = floatArray.length / 2;
    let result = float64ArrayToComplexEGPTArray(floatArray, scale);
    
    // Check if input appears to be a real signal (all imaginary parts ≈ 0)
    const isReal = isRealSignal(result, tolerance);
    
    // If enforcing symmetry and signal appears real, enforce conjugate symmetry
    if (enforceSymmetry && isReal) {
        result = enforceConjugateSymmetry(result, N);
    }
    
    return result;
}

/**
 * Enhanced ComplexEGPTNumber to Float64Array conversion
 * 
 * @param {Array<ComplexEGPTNumber>} complexArray - Array of complex numbers
 * @returns {Float64Array} Interleaved real/imaginary pairs
 */
export function complexEGPTArrayToFloat64ArrayEnhanced(complexArray) {
    return complexEGPTArrayToFloat64Array(complexArray);
}

/**
 * Enhanced format conversion with symmetry handling
 * 
 * @param {Array<ComplexEGPTNumber>} complexArray - Array of complex numbers
 * @param {string} format - Output format
 * @param {Object} options - Conversion options
 * @returns {*} Output in requested format
 */
export function convertComplexEGPTArrayToFormatEnhanced(complexArray, format, options = {}) {
    return convertComplexEGPTArrayToFormat(complexArray, format);
}

// =============================================================================
// NORMALIZATION HELPERS
// =============================================================================

/**
 * Normalize FFT output (multiply by 1/N)
 * 
 * Standard IFFT normalization convention. This is typically applied
 * to IFFT outputs to get proper scaling relative to the original signal.
 * 
 * @param {Array<ComplexEGPTNumber>} output - Unnormalized output
 * @param {number} N - FFT size
 * @returns {Array<ComplexEGPTNumber>} Normalized output
 */
export function normalizeFFTOutput(output, N) {
    const N_big = BigInt(N);
    return output.map(z => {
        if (typeof z.scaleByRational === 'function') {
            return z.scaleByRational(1n, N_big);
        } else {
            // Fallback scaling
            const r = EGPTMath.divide(z.real, EGPTNumber.fromBigInt(N_big));
            const im = EGPTMath.divide(z.imag, EGPTNumber.fromBigInt(N_big));
            return new ComplexEGPTNumber(r, im);
        }
    });
}

/**
 * Denormalize ComplexEGPTNumber array (multiply by N)
 * 
 * Converts normalized output back to unnormalized state.
 * Useful for fft.js compatibility when fft.js expects unnormalized IFFT output.
 * 
 * @param {Array<ComplexEGPTNumber>} normalizedArray - Normalized array
 * @param {number} N - FFT size
 * @returns {Array<ComplexEGPTNumber>} Denormalized array
 */
export function denormalizeComplexEGPTArray(normalizedArray, N) {
    const N_big = BigInt(N);
    return normalizedArray.map(z => {
        const r = EGPTMath.multiply(z.real, EGPTNumber.fromBigInt(N_big));
        const im = EGPTMath.multiply(z.imag, EGPTNumber.fromBigInt(N_big));
        return new ComplexEGPTNumber(r, im);
    });
}

/**
 * Denormalize output (multiply by N)
 * 
 * Converts normalized output back to unnormalized state.
 * Handles multiple output formats (Float64Array, ComplexEGPTNumber arrays, etc.)
 * 
 * @param {*} normalizedOutput - Normalized output (any supported format)
 * @param {number} N - FFT size
 * @returns {*} Denormalized output (same format as input)
 */
export function denormalizeOutput(normalizedOutput, N) {
    if (normalizedOutput instanceof Float64Array) {
        const result = new Float64Array(normalizedOutput.length);
        for (let i = 0; i < normalizedOutput.length; i++) {
            result[i] = normalizedOutput[i] * N;
        }
        return result;
    } else if (Array.isArray(normalizedOutput)) {
        if (normalizedOutput.length > 0 && normalizedOutput[0] instanceof ComplexEGPTNumber) {
            return denormalizeComplexEGPTArray(normalizedOutput, N);
        }
        return normalizedOutput.map(val => val * N);
    } else {
        throw new Error(`Unsupported output type for denormalizeOutput: ${typeof normalizedOutput}`);
    }
}

