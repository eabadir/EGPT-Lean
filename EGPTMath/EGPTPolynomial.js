// =============================================================================
// EGPT POLYNOMIAL - Pure Canonical Polynomial Operations
// Based on EGPTNumber/EGPTMath canonical space operations
//
// Author: E. Abadir
// Paradigm: All operations stay in canonical space (EGPTNumber/EGPTMath)
//           No conversion to float/decimal for comparisons
//           Polynomial coefficients are EGPTNumber vectors
// =============================================================================

import { EGPTNumber } from './EGPTNumber.js';
import { EGPTMath } from './EGPTMath.js';

/**
 * EGPTPolynomial: Pure canonical polynomial arithmetic and transforms
 * 
 * POLYNOMIAL REPRESENTATION:
 * - Array [a₀, a₁, a₂, ...] represents a₀ + a₁x + a₂x² + ...
 * - All coefficients are EGPTNumber instances
 * - All operations use EGPTMath (stay in canonical space)
 * 
 * ARCHITECTURAL PRINCIPLE:
 * - Once in Shannon space (EGPTNumber), stay there until calculation complete
 * - Use EGPTMath for all operations between EGPTNumbers
 * - Never convert to BigInt/Number/float for comparisons
 * - Use .equals() for canonical comparison
 * 
 * FEATURES:
 * - Basic arithmetic: add, subtract, multiply, divide
 * - Forward transform: Horner evaluation at residue points k/N
 * - Inverse transform: Newton Divided Differences interpolation
 * - Value representation: Conditional entropy for factor detection
 * 
 * @class EGPTPolynomial
 */
export class EGPTPolynomial {
    // Prevent instantiation - all methods are static
    constructor() {
        throw new Error("EGPTPolynomial is a static class and cannot be instantiated.");
    }

    // =============================================================================
    // HELPER METHODS
    // =============================================================================

    /**
     * Remove trailing zero coefficients from polynomial
     * 
     * CANONICAL OPERATION: Uses .equals() for zero comparison
     * 
     * @param {EGPTNumber[]} poly - Polynomial coefficients
     * @returns {EGPTNumber[]} Trimmed polynomial (at least one coefficient)
     */
    static trimZeros(poly) {
        if (!Array.isArray(poly) || poly.length === 0) {
            return [EGPTNumber.fromBigInt(0n)];
        }

        const result = [...poly];
        const zero = EGPTNumber.fromBigInt(0n);
        
        while (result.length > 1 && result[result.length - 1].equals(zero)) {
            result.pop();
        }
        
        return result.length > 0 ? result : [zero];
    }

    /**
     * Get polynomial degree (highest non-zero power)
     * 
     * @param {EGPTNumber[]} poly - Polynomial coefficients
     * @returns {number} Degree (0 for constant polynomial)
     */
    static degree(poly) {
        const trimmed = EGPTPolynomial.trimZeros(poly);
        return trimmed.length - 1;
    }

    /**
     * Check if two polynomials are equal (canonical comparison)
     * 
     * CANONICAL OPERATION: Uses coefficient .equals() method
     * Never uses toFloat() or toBigInt() for comparison
     * 
     * @param {EGPTNumber[]} poly1 - First polynomial
     * @param {EGPTNumber[]} poly2 - Second polynomial
     * @returns {boolean} True if polynomials are equal in canonical space
     */
    static equals(poly1, poly2) {
        const p1 = EGPTPolynomial.trimZeros(poly1);
        const p2 = EGPTPolynomial.trimZeros(poly2);
        
        if (p1.length !== p2.length) return false;
        
        return p1.every((coeff, i) => coeff.equals(p2[i]));
    }

    // =============================================================================
    // CORE ARITHMETIC METHODS
    // =============================================================================

    /**
     * Add two polynomials coefficient-wise
     * 
     * CANONICAL OPERATION: Uses EGPTMath.add() for each coefficient
     * 
     * Complexity: O(max(deg(p1), deg(p2)))
     * 
     * @param {EGPTNumber[]} poly1 - First polynomial
     * @param {EGPTNumber[]} poly2 - Second polynomial
     * @returns {EGPTNumber[]} Sum polynomial
     */
    static add(poly1, poly2) {
        const zero = EGPTNumber.fromBigInt(0n);
        const maxLen = Math.max(poly1.length, poly2.length);
        const result = new Array(maxLen);
        
        for (let i = 0; i < maxLen; i++) {
            const c1 = i < poly1.length ? poly1[i] : zero;
            const c2 = i < poly2.length ? poly2[i] : zero;
            result[i] = EGPTMath.add(c1, c2);
        }
        
        return EGPTPolynomial.trimZeros(result);
    }

    /**
     * Subtract two polynomials coefficient-wise
     * 
     * CANONICAL OPERATION: Uses EGPTMath.subtract() for each coefficient
     * 
     * Complexity: O(max(deg(p1), deg(p2)))
     * 
     * @param {EGPTNumber[]} poly1 - First polynomial (minuend)
     * @param {EGPTNumber[]} poly2 - Second polynomial (subtrahend)
     * @returns {EGPTNumber[]} Difference polynomial
     */
    static subtract(poly1, poly2) {
        const zero = EGPTNumber.fromBigInt(0n);
        const maxLen = Math.max(poly1.length, poly2.length);
        const result = new Array(maxLen);
        
        for (let i = 0; i < maxLen; i++) {
            const c1 = i < poly1.length ? poly1[i] : zero;
            const c2 = i < poly2.length ? poly2[i] : zero;
            result[i] = EGPTMath.subtract(c1, c2);
        }
        
        return EGPTPolynomial.trimZeros(result);
    }

    /**
     * Multiply two polynomials using convolution
     * 
     * CANONICAL OPERATION: Uses EGPTMath.multiply() for coefficient products
     * 
     * Algorithm: (a₀ + a₁x + ...)(b₀ + b₁x + ...) = Σᵢⱼ aᵢbⱼx^(i+j)
     * Complexity: O(deg(p1) × deg(p2))
     * 
     * @param {EGPTNumber[]} poly1 - First polynomial
     * @param {EGPTNumber[]} poly2 - Second polynomial
     * @returns {EGPTNumber[]} Product polynomial
     */
    static multiply(poly1, poly2) {
        if (poly1.length === 0 || poly2.length === 0) {
            return [EGPTNumber.fromBigInt(0n)];
        }
        
        const zero = EGPTNumber.fromBigInt(0n);
        const resultLength = poly1.length + poly2.length - 1;
        const result = new Array(resultLength);
        
        // Initialize result array with zeros
        for (let i = 0; i < resultLength; i++) {
            result[i] = zero.clone();
        }
        
        // Convolution: accumulate products at each power
        for (let i = 0; i < poly1.length; i++) {
            for (let j = 0; j < poly2.length; j++) {
                // result[i + j] += poly1[i] * poly2[j]
                const term = EGPTMath.multiply(poly1[i], poly2[j]);
                result[i + j] = EGPTMath.add(result[i + j], term);
            }
        }
        
        return EGPTPolynomial.trimZeros(result);
    }

    /**
     * Divide two polynomials using long division
     * 
     * CANONICAL OPERATION: Uses EGPTMath.divide() for coefficient division
     * 
     * Returns both quotient and remainder such that:
     * dividend = divisor × quotient + remainder
     * 
     * Complexity: O(deg(dividend) × deg(divisor))
     * 
     * @param {EGPTNumber[]} dividend - Dividend polynomial
     * @param {EGPTNumber[]} divisor - Divisor polynomial
     * @returns {{quotient: EGPTNumber[], remainder: EGPTNumber[]}}
     */
    static divide(dividend, divisor) {
        const zero = EGPTNumber.fromBigInt(0n);
        
        // Make copies to avoid modifying inputs
        let divid = dividend.map(c => c.clone());
        let divis = divisor.map(c => c.clone());
        
        // Trim trailing zeros
        divid = EGPTPolynomial.trimZeros(divid);
        divis = EGPTPolynomial.trimZeros(divis);
        
        // Check for division by zero
        if (divis.length === 1 && divis[0].equals(zero)) {
            throw new Error('Division by zero polynomial');
        }
        
        // If dividend degree < divisor degree, quotient is 0
        if (divid.length < divis.length) {
            return { 
                quotient: [zero.clone()], 
                remainder: divid 
            };
        }
        
        // Calculate quotient degree
        const quotientDegree = divid.length - divis.length;
        const quotient = new Array(quotientDegree + 1);
        for (let i = 0; i <= quotientDegree; i++) {
            quotient[i] = zero.clone();
        }
        
        let remainder = divid.map(c => c.clone());
        const divisorLead = divis[divis.length - 1].clone();
        
        // Long division from high degree to low
        for (let i = quotientDegree; i >= 0; i--) {
            const remainderIdx = i + divis.length - 1;
            
            if (remainderIdx >= remainder.length || remainderIdx < 0) {
                quotient[i] = zero.clone();
                continue;
            }
            
            // Divide leading coefficients (canonical space division)
            const remainderLead = remainder[remainderIdx].clone();
            const quotCoeff = EGPTMath.divide(remainderLead, divisorLead);
            quotient[i] = quotCoeff;
            
            // Subtract divisor × quotCoeff from remainder
            for (let j = 0; j < divis.length; j++) {
                const idx = i + j;
                if (idx < remainder.length) {
                    const term = EGPTMath.multiply(quotCoeff, divis[j]);
                    remainder[idx] = EGPTMath.subtract(remainder[idx], term);
                }
            }
        }
        
        return {
            quotient: EGPTPolynomial.trimZeros(quotient),
            remainder: EGPTPolynomial.trimZeros(remainder)
        };
    }

    /**
     * Evaluate polynomial at a point using Horner's method
     * 
     * CANONICAL OPERATION: Uses EGPTMath.multiply() and EGPTMath.add()
     * 
     * Algorithm: a₀ + x(a₁ + x(a₂ + x(...)))
     * Complexity: O(deg(poly))
     * 
     * STAYS IN CANONICAL SPACE: No conversion to float/decimal
     * 
     * @param {EGPTNumber[]} poly - Polynomial coefficients [a₀, a₁, a₂, ...]
     * @param {EGPTNumber} x - Point to evaluate at (EGPTNumber)
     * @returns {EGPTNumber} Polynomial value at x
     */
    static evaluateAt(poly, x) {
        if (poly.length === 0) {
            return EGPTNumber.fromBigInt(0n);
        }
        
        // Horner's method: start from highest degree
        let result = poly[poly.length - 1].clone();
        
        for (let i = poly.length - 2; i >= 0; i--) {
            // result = result * x + poly[i]
            result = EGPTMath.multiply(result, x);
            result = EGPTMath.add(result, poly[i]);
        }
        
        return result;
    }

    // =============================================================================
    // TRANSFORM METHODS (CONVOLUTION/DECONVOLUTION)
    // =============================================================================

    /**
     * Forward Transform: Evaluate polynomial at N residue points k/N
     * 
     * This is the "convolution" operation - transforms polynomial coefficients
     * into their evaluation at N sample points using Horner's method.
     * 
     * CANONICAL OPERATION: All evaluations stay in EGPTNumber space
     * 
     * Sample points: x_k = k/N for k = 0, 1, ..., N-1
     * Returns: [p(0/N), p(1/N), ..., p((N-1)/N)]
     * 
     * Complexity: O(N × deg(poly))
     * 
     * @param {EGPTNumber[]} coefficients - Polynomial coefficients
     * @param {number} N - Number of sample points (must be positive)
     * @returns {EGPTNumber[]} Array of N evaluated values
     */
    static forwardTransform(coefficients, N) {
        if (N <= 0) {
            throw new Error('N must be positive');
        }
        
        const samples = new Array(N);
        
        for (let k = 0; k < N; k++) {
            // Create sample point x_k = k/N in canonical space
            const x_k = EGPTNumber.fromRational(BigInt(k), BigInt(N));
            
            // Evaluate polynomial at x_k using Horner's method
            samples[k] = EGPTPolynomial.evaluateAt(coefficients, x_k);
        }
        
        return samples;
    }

    /**
     * Inverse Transform: Interpolate polynomial from N samples using Newton DD
     * 
     * This is the "deconvolution" operation - recovers polynomial coefficients
     * from their evaluations at N residue points using Newton Divided Differences.
     * 
     * CANONICAL OPERATION: All operations stay in EGPTNumber space
     * 
     * Algorithm:
     * 1. Build divided difference table
     * 2. Extract Newton coefficients (diagonal)
     * 3. Convert from Newton basis to monomial basis
     * 
     * Complexity: O(N²)
     * 
     * @param {EGPTNumber[]} samples - Array of N evaluated values
     * @param {number} N - Number of sample points
     * @returns {EGPTNumber[]} Polynomial coefficients
     */
    static inverseTransform(samples, N) {
        if (samples.length !== N) {
            throw new Error(`Expected ${N} samples, got ${samples.length}`);
        }
        
        // Create x-values: x_k = k/N for k = 0, 1, ..., N-1
        const xValues = new Array(N);
        for (let k = 0; k < N; k++) {
            xValues[k] = EGPTNumber.fromRational(BigInt(k), BigInt(N));
        }
        
        // Build divided difference table
        const ddTable = EGPTPolynomial._buildDividedDifferenceTable(xValues, samples);
        
        // Extract Newton coefficients (first row = diagonal)
        const newtonCoeffs = new Array(N);
        for (let j = 0; j < N; j++) {
            newtonCoeffs[j] = ddTable[0][j];
        }
        
        // Convert from Newton basis to monomial basis
        const monomialCoeffs = EGPTPolynomial._newtonToMonomial(newtonCoeffs, xValues);
        
        return monomialCoeffs;
    }

    /**
     * Build divided difference table using canonical operations
     * 
     * INTERNAL METHOD: Uses EGPTMath for all operations
     * 
     * Algorithm:
     * - DD[i,0] = f[i]
     * - DD[i,j] = (DD[i+1,j-1] - DD[i,j-1]) / (x[i+j] - x[i])
     * 
     * @param {EGPTNumber[]} xValues - Sample points
     * @param {EGPTNumber[]} fValues - Function values at sample points
     * @returns {EGPTNumber[][]} Divided difference table
     * @private
     */
    static _buildDividedDifferenceTable(xValues, fValues) {
        const N = xValues.length;
        const table = new Array(N);
        
        // Initialize first column with function values
        for (let i = 0; i < N; i++) {
            table[i] = new Array(N - i);
            table[i][0] = fValues[i].clone();
        }
        
        // Build table iteratively
        for (let j = 1; j < N; j++) {
            for (let i = 0; i < N - j; i++) {
                // DD[i,j] = (DD[i+1,j-1] - DD[i,j-1]) / (x[i+j] - x[i])
                const numerator = EGPTMath.subtract(table[i + 1][j - 1], table[i][j - 1]);
                const denominator = EGPTMath.subtract(xValues[i + j], xValues[i]);
                table[i][j] = EGPTMath.divide(numerator, denominator);
            }
        }
        
        return table;
    }

    /**
     * Convert Newton basis coefficients to monomial basis
     * 
     * INTERNAL METHOD: Uses EGPTMath for all operations
     * 
     * Newton basis: c₀ + c₁(x-x₀) + c₂(x-x₀)(x-x₁) + ...
     * Monomial basis: a₀ + a₁x + a₂x² + ...
     * 
     * Algorithm: Expand Newton basis polynomially
     * 
     * @param {EGPTNumber[]} newtonCoeffs - Newton basis coefficients
     * @param {EGPTNumber[]} xValues - Sample points
     * @returns {EGPTNumber[]} Monomial basis coefficients
     * @private
     */
    static _newtonToMonomial(newtonCoeffs, xValues) {
        const N = newtonCoeffs.length;
        const zero = EGPTNumber.fromBigInt(0n);
        const one = EGPTNumber.fromBigInt(1n);
        
        // Initialize result to zero polynomial of length N
        const result = new Array(N);
        for (let i = 0; i < N; i++) {
            result[i] = zero.clone();
        }
        
        // Start with basis = [1]
        let basis = [one.clone()];
        
        // Add each Newton term: c[i] * basis
        // Then update basis = basis * (x - x[i])
        for (let i = 0; i < N; i++) {
            // Add c[i] * basis to result
            for (let k = 0; k < basis.length; k++) {
                const term = EGPTMath.multiply(newtonCoeffs[i], basis[k]);
                result[k] = EGPTMath.add(result[k], term);
            }
            
            // Update basis for next iteration: basis *= (x - x[i])
            // Only do this if we haven't reached the last term
            if (i < N - 1) {
                // Multiply basis by (x - x[i])
                // Create the linear factor [- x[i], 1] representing (x - x[i])
                const negXi = EGPTMath.subtract(zero, xValues[i]);
                const factor = [negXi, one.clone()];
                basis = EGPTPolynomial.multiply(basis, factor);
            }
        }
        
        return EGPTPolynomial.trimZeros(result);
    }

    /**
     * Multiply polynomial by linear factor (x - c)
     * 
     * INTERNAL METHOD: Optimized O(N) operation
     * 
     * Algorithm: (x - c)(a₀ + a₁x + ...) = -c·a₀ + (a₀-c·a₁)x + (a₁-c·a₂)x² + ... + aₙxⁿ⁺¹
     * 
     * @param {EGPTNumber[]} poly - Input polynomial
     * @param {EGPTNumber} c - Constant term (negated, so we compute x + c)
     * @returns {EGPTNumber[]} Result polynomial of degree+1
     * @private
     */
    static _multiplyByLinear(poly, c) {
        const N = poly.length;
        const result = new Array(N + 1);
        
        // result[0] = c * poly[0]
        result[0] = EGPTMath.multiply(c, poly[0]);
        
        // result[i] = poly[i-1] + c * poly[i] for i = 1..N-1
        for (let i = 1; i < N; i++) {
            const term = EGPTMath.multiply(c, poly[i]);
            result[i] = EGPTMath.add(poly[i - 1], term);
        }
        
        // result[N] = poly[N-1]
        result[N] = poly[N - 1].clone();
        
        return result;
    }

    // =============================================================================
    // VALUE REPRESENTATION (FACTOR DETECTION)
    // =============================================================================

    /**
     * Evaluate value representation using conditional entropy
     * 
     * CANONICAL OPERATION: Uses EGPTMath.conditionalEntropyVector()
     * 
     * This method computes the conditional entropy H(k|p), which provides
     * a measure of how "close" p is to being a factor of k.
     * 
     * - Exact factors: Returns integer quotient (high entropy spike)
     * - Non-factors: Returns fractional value (proportional entropy)
     * 
     * Used for factor detection in number-theoretic applications.
     * 
     * @param {EGPTNumber} k - Target number
     * @param {EGPTNumber} p - Potential factor
     * @returns {EGPTNumber} Conditional entropy measure
     */
    static evaluateValueRepresentation(k, p) {
        return EGPTMath.conditionalEntropyVector(k, p);
    }
}

export default EGPTPolynomial;

