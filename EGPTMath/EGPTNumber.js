// =============================================================================
// EGPT NUMBER REFACTORED - PURE VECTOR DATA CONTAINER
// Based on EGPT Vector Space Refactor v3.0: Scalar & Vector Paradigm
//
// Author: E. Abadir
// Copyright (C) 2026 Essam Abadir
// Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
// See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
// Provided WITHOUT ANY WARRANTY. See the DCSL for details.
//
// Paradigm: EGPTNumber as a VECTOR - pure data container for canonical information
//           BigInt as SCALAR - for scaling/translating vectors
//           ALL vector-vector operations moved to EGPTMath static class
// =============================================================================
import { SimpleLogger } from './DebugLogger.js';
SimpleLogger.log("🎓 CANONICAL INFORMATION SPACE: Exact discrete mathematics");
SimpleLogger.log("📁 File location: EGPT/copilot/ - Copilot development workspace");

// =============================================================================
// LEAN COMPLIANCE: GCD Helper for Canonical Reduction
// =============================================================================

/**
 * Greatest Common Divisor for BigInt values using Euclidean algorithm.
 * Required for canonical reduction to co-prime fractions per Lean specification.
 * @param {BigInt} a - First value
 * @param {BigInt} b - Second value
 * @returns {BigInt} - Greatest common divisor
 */
function gcd(a, b) {
    a = a < 0n ? -a : a;
    b = b < 0n ? -b : b;
    while (b) {
        [a, b] = [b, a % b];
    }
    return a;
}

/**
 * Calculates the integer nth root of a BigInt using a binary search algorithm.
 * This is required for scalar reduction to detect perfect powers.
 * @param {BigInt} n - The number to find the root of
 * @param {BigInt} root - The root to find (e.g., 2 for sqrt, 3 for cuberoot)
 * @returns {[BigInt, boolean]} A tuple: [the floor of the root, true if the root is exact]
 */
function nthRoot(n, root) {
    if (n < 0n || root <= 0n) return [0n, false];
    if (n === 0n) return [0n, true];
    if (root === 1n) return [n, true];
    if (n === 1n) return [1n, true];

    let low = 1n;
    let high = n;
    let guess;

    while (low <= high) {
        guess = (low + high) / 2n;
        const p = guess ** root;
        if (p === n) {
            return [guess, true]; // Exact root found
        }
        if (p < n) {
            low = guess + 1n;
        } else {
            high = guess - 1n;
        }
    }
    // `high` is now the integer floor of the root
    return [high, false];
}


// BigInt sqrt extension
BigInt.prototype.sqrt = function () {
    if (this < 0n) throw 'negative number is not supported';
    if (this < 2n) return this;

    function newtonIteration(n, x0) {
        const x1 = ((n / x0) + x0) >> 1n;
        if (x0 === x1 || x0 === (x1 - 1n)) return x0;
        return newtonIteration(n, x1);
    }
    return newtonIteration(this, 1n);
};
/**
 * 🎯 EXTENDED EGPT NUMBER: PURE VECTOR DATA CONTAINER WITH SCALAR MULTIPLIER
 * 
 * ARCHITECTURAL PRINCIPLE: This class IS a vector in the 2D information grid.
 * - Contains ONLY data storage and scalar operations
 * - NO vector-vector arithmetic (moved to EGPTMath)
 * - Mutable scalar operations return 'this' for fluent chaining
 * - Immutable for vector algebra (EGPTMath operates on clones)
 * 
 * EXTENDED VECTOR PARADIGM (per ADDING_Vector_Scaling.md):
 * - EGPTNumber = Scaled Information Vector: scalar * base_vector
 * - scalar = rational multiplier (s_num, s_den) for irrational support
 * - base_vector = (numerator_ppf, denominator_ppf) for rational numbers
 * - H(√k) = { scalar: (1,2), base: H(k) } represents exact irrational roots
 * 
 * MATHEMATICAL FOUNDATION:
 * H(k) = (s_num/s_den) * [log₂(num) - log₂(den)]
 * This enables exact representation of H(√2) = (1/2) * H(2) without approximation
 */
class EGPTNumber {
    /** Rational scalar multiplier numerator @type {BigInt} */
    scalar_numerator;
    /** Rational scalar multiplier denominator @type {BigInt} */
    scalar_denominator;
    /** The PPF for the numerator encoded as log2: { N, offset } @type {{N: BigInt, offset: BigInt}} */
    numerator_encodedAsLog2ppf;
    /** The PPF for the denominator encoded as log2: { N, offset } @type {{N: BigInt, offset: BigInt}} */
    denominator_encodedAsLog2ppf;

    /**
     * Private constructor. Use static factory methods to create instances.
     * @param {{numerator_encodedAsLog2ppf: {N: BigInt, offset: BigInt}, denominator_encodedAsLog2ppf: {N: BigInt, offset: BigInt}}} ppf_pair
     * @param {{numerator: BigInt, denominator: BigInt}} scalar - Optional scalar multiplier (defaults to 1/1)
     * @param {boolean} skip_reduce - Internal flag to prevent infinite recursion during reduction
     */
    constructor(ppf_pair, scalar = null, skip_reduce = false) {
        if (!ppf_pair || !ppf_pair.numerator_encodedAsLog2ppf || !ppf_pair.denominator_encodedAsLog2ppf) {
            throw new Error("EGPTNumber constructor requires a pair of PPF objects.");
        }

        // Initialize scalar multiplier (default is 1/1 = identity)
        if (scalar) {
            this.scalar_numerator = scalar.numerator;
            this.scalar_denominator = scalar.denominator;
        } else {
            this.scalar_numerator = 1n;
            this.scalar_denominator = 1n;
        }

        // Normalize scalar (ensure denominator is positive)
        if (this.scalar_denominator < 0n) {
            this.scalar_numerator = -this.scalar_numerator;
            this.scalar_denominator = -this.scalar_denominator;
        }

        // Reduce scalar to lowest terms
        const scalar_gcd = gcd(this.scalar_numerator < 0n ? -this.scalar_numerator : this.scalar_numerator, this.scalar_denominator);
        this.scalar_numerator = this.scalar_numerator / scalar_gcd;
        this.scalar_denominator = this.scalar_denominator / scalar_gcd;

        this.numerator_encodedAsLog2ppf = ppf_pair.numerator_encodedAsLog2ppf;
        this.denominator_encodedAsLog2ppf = ppf_pair.denominator_encodedAsLog2ppf;

        // LEAN COMPLIANCE: Automatically reduce to canonical form unless explicitly skipped
        if (!skip_reduce) {
            // First, reduce the base rational to its lowest terms
            const reduced = this._reduce();
            this.numerator_encodedAsLog2ppf = reduced.numerator_encodedAsLog2ppf;
            this.denominator_encodedAsLog2ppf = reduced.denominator_encodedAsLog2ppf;

            // Second, attempt to reduce the scalar component for true canonical form
            this._reduceScalar();
        }
    }

    /**
     * LEAN COMPLIANCE: Reduces the rational representation to its lowest terms.
     * This ensures truly canonical representation - every rational has ONE unique form.
     * @returns {{numerator_encodedAsLog2ppf: object, denominator_encodedAsLog2ppf: object}} The reduced PPF pair
     */
    _reduce() {
        const num_val = EGPTNumber._decodePPFLog2ToInteger(this.numerator_encodedAsLog2ppf);
        const den_val = EGPTNumber._decodePPFLog2ToInteger(this.denominator_encodedAsLog2ppf);

        if (den_val === 0n) throw new Error("Denominator cannot be zero in reduction.");
        if (num_val === 0n) {
            // Canonical zero is 0/1
            return {
                numerator_encodedAsLog2ppf: EGPTNumber._integerToPPFEncodedLog2(0n),
                denominator_encodedAsLog2ppf: EGPTNumber._integerToPPFEncodedLog2(1n)
            };
        }

        const common_divisor = gcd(num_val, den_val);

        if (common_divisor === 1n) {
            // Already in lowest terms
            return {
                numerator_encodedAsLog2ppf: this.numerator_encodedAsLog2ppf,
                denominator_encodedAsLog2ppf: this.denominator_encodedAsLog2ppf
            };
        }

        const new_num = num_val / common_divisor;
        const new_den = den_val / common_divisor;

        // Use _encodeRationalToPPF to handle negative numbers without triggering recursion
        return EGPTNumber._encodeRationalToPPF(new_num, new_den);
    }

    /**
     * INTERNAL: Encodes a rational number to PPF format with proper negative handling.
     * This version correctly handles negative numerators via the new PPF encoding convention.
     * @param {BigInt} numerator - The numerator (can be negative)
     * @param {BigInt} denominator - The denominator (should be positive after normalization)
     * @returns {{numerator_encodedAsLog2ppf: object, denominator_encodedAsLog2ppf: object}} - PPF representation
     */
    static _encodeRationalToPPF(numerator, denominator) {
        if (denominator === 0n) throw new Error("Denominator cannot be zero.");

        // --- Start of New Logic ---

        // 1. Normalize signs: The sign is always carried by the numerator.
        if (denominator < 0n) {
            numerator = -numerator;
            denominator = -denominator;
        }

        const isNegative = numerator < 0n;
        const absNumerator = isNegative ? -numerator : numerator;

        // 2. Encode the absolute values into PPF.
        const ppf_abs_num = EGPTNumber._integerToPPFEncodedLog2(absNumerator);
        const ppf_den = EGPTNumber._integerToPPFEncodedLog2(denominator);

        // 3. If the number was negative, apply the transformation to N.
        if (isNegative) {
            // N_neg = -N_abs - 2
            // This moves N into the unused space N < -1.
            ppf_abs_num.N = -ppf_abs_num.N - 2n;
        }

        // 4. Return the PPF pair with the potentially transformed numerator PPF.
        return {
            numerator_encodedAsLog2ppf: ppf_abs_num,
            denominator_encodedAsLog2ppf: ppf_den
        };

        // --- End of New Logic ---
    }

    /**
     * 🎯 SCALAR REDUCTION: Attempts to simplify a scaled vector into a standard rational vector if possible.
     * This is the core of canonical representation for irrational roots.
     * 
     * MATHEMATICAL FOUNDATION:
     * For a scaled vector {scalar:(s_num/s_den), base:(b_num/b_den)}, this represents:
     * (b_num/b_den)^(s_num/s_den)
     * 
     * REDUCTION CONDITIONS:
     * 1. Integer exponents (s_den = 1): Always compute (b_num/b_den)^s_num
     * 2. Fractional exponents: If both b_num and b_den are perfect s_den-th powers
     * 3. ENHANCED: Iterative simplification - find any common factors between root denominator and perfect powers
     * 
     * EXAMPLES:
     * - {scalar:(3/1), base:H(2)} -> {scalar:(1/1), base:H(8)} since 2^3 = 8
     * - {scalar:(1/2), base:H(4/9)} -> {scalar:(1/1), base:H(2/3)} since 4=2², 9=3²
     * - {scalar:(1/6), base:H(27)} -> {scalar:(1/2), base:H(3)} since 27 = 3³, gcd(6,3) = 3
     * - {scalar:(1/2), base:H(2/1)} -> no change since 2 is not a perfect square
     * 
     * This method MODIFIES the current instance to its canonical form.
     */
    _reduceScalar() {
        let s_num = this.scalar_numerator;
        let s_den = this.scalar_denominator;

        // No reduction needed for identity scalar
        if (s_num === 1n && s_den === 1n) {
            return;
        }

        // Decode the base rational components
        let b_num = EGPTNumber._decodePPFLog2ToInteger(this.numerator_encodedAsLog2ppf);
        let b_den = EGPTNumber._decodePPFLog2ToInteger(this.denominator_encodedAsLog2ppf);

        // Handle special case where base is zero
        if (b_num === 0n) {
            // 0^(anything positive) = 0, so no reduction needed
            return;
        }

        // CASE 1: Integer exponents (s_den = 1) - always reduce
        if (s_den === 1n) {
            SimpleLogger.log(`🎯 Canonical Reduction: Integer exponent {${s_num}/1} * H(${b_num}/${b_den})`);

            let new_base_num;
            let new_base_den;

            // Handle negative exponents by inverting the base
            if (s_num >= 0n) {
                new_base_num = b_num ** s_num;
                new_base_den = b_den ** s_num;
            } else {
                const pos_exponent = -s_num;
                new_base_num = b_den ** pos_exponent;
                new_base_den = b_num ** pos_exponent;
            }

            // Encode and update
            const new_ppf_pair = EGPTNumber._encodeRationalToPPF(new_base_num, new_base_den);
            this.numerator_encodedAsLog2ppf = new_ppf_pair.numerator_encodedAsLog2ppf;
            this.denominator_encodedAsLog2ppf = new_ppf_pair.denominator_encodedAsLog2ppf;
            this.scalar_numerator = 1n;
            this.scalar_denominator = 1n;

            SimpleLogger.log(`✅ Reduced integer exponent to: H(${new_base_num}/${new_base_den})`);
            return;
        }

        // CASE 2: Enhanced fractional exponents - iterative simplification
        // ENHANCED REDUCTION LOGIC: Iteratively simplify by finding perfect power factors
        // Example: For (27)^(1/6), we find g=3. new_base = 27^(1/3)=3. new_scalar_den = 6/3=2. Result: 3^(1/2).
        let changed = true;
        while (changed) {
            changed = false;

            // Test divisors of s_den to see if we can extract perfect powers
            for (let g = 2n; g <= s_den; g++) {
                if (s_den % g === 0n) {
                    // Check if both b_num and b_den are perfect g-th powers
                    const abs_b_num = b_num < 0n ? -b_num : b_num;
                    const [root_num, isExactNum] = nthRoot(abs_b_num, g);
                    const [root_den, isExactDen] = nthRoot(b_den, g);

                    if (isExactNum && isExactDen) {
                        SimpleLogger.log(`   Enhanced Reduction: Found ${g}th power factor. ${abs_b_num}^(1/${g}) = ${root_num}, ${b_den}^(1/${g}) = ${root_den}`);

                        // Simplify: (b)^(s_n/s_d) = (b^(1/g))^(g*s_n/s_d) where g divides s_d
                        b_num = b_num < 0n ? -root_num : root_num; // Preserve sign
                        b_den = root_den;
                        s_den = s_den / g;

                        changed = true;
                        break; // Restart the search with simplified values
                    }
                }
            }
        }

        // After enhanced reduction, check if we can now perform final simplification
        const abs_b_num = b_num < 0n ? -b_num : b_num;
        const [final_root_num, isFinalExactNum] = nthRoot(abs_b_num, s_den);
        const [final_root_den, isFinalExactDen] = nthRoot(b_den, s_den);

        if (isFinalExactNum && isFinalExactDen) {
            SimpleLogger.log(`🎯 Final Canonical Reduction: Fractional exponent {${s_num}/${s_den}} * H(${b_num}/${b_den})`);

            // Calculate the new rational base: (root_num^s_num) / (root_den^s_num)
            let new_base_num = final_root_num ** s_num;
            const new_base_den = final_root_den ** s_num;

            // Handle negative base numbers correctly for fractional powers
            if (b_num < 0n) {
                // For negative bases with fractional exponents, only odd numerators are valid
                if (s_num % 2n === 1n) {
                    new_base_num = -new_base_num;
                } else {
                    // Even numerator with negative base - this would be complex, keep as scaled vector
                    return;
                }
            }

            // Encode and update
            const new_ppf_pair = EGPTNumber._encodeRationalToPPF(new_base_num, new_base_den);
            this.numerator_encodedAsLog2ppf = new_ppf_pair.numerator_encodedAsLog2ppf;
            this.denominator_encodedAsLog2ppf = new_ppf_pair.denominator_encodedAsLog2ppf;
            this.scalar_numerator = 1n;
            this.scalar_denominator = 1n;

            SimpleLogger.log(`✅ Reduced fractional exponent to: H(${new_base_num}/${new_base_den})`);
        } else {
            // Update with the partially simplified state from the enhanced reduction
            const new_ppf_pair = EGPTNumber._encodeRationalToPPF(b_num, b_den);
            this.numerator_encodedAsLog2ppf = new_ppf_pair.numerator_encodedAsLog2ppf;
            this.denominator_encodedAsLog2ppf = new_ppf_pair.denominator_encodedAsLog2ppf;

            this.scalar_numerator = s_num; // s_num doesn't change in this reduction
            this.scalar_denominator = s_den;

            // Final reduction of the new scalar itself
            const final_gcd = gcd(this.scalar_numerator, this.scalar_denominator);
            this.scalar_numerator /= final_gcd;
            this.scalar_denominator /= final_gcd;
        }
    }

    // =============================================================================
    // FACTORY METHODS (Static) - VECTOR CREATION FROM CANONICAL SPACE
    // =============================================================================

    /**
     * Creates an EGPTNumber from a standard BigInt, representing n/1.
     * PRIMARY ENCODING: Normal space integer → Canonical information vector
     * @param {BigInt} n - The integer to encode as information vector
     * @returns {EGPTNumber} - Canonical information vector
     */
    static fromBigInt(n) {
        // Handle negative integers by using fromRational which has proper negative handling
        return EGPTNumber.fromRational(n, 1n);
    }

    /**
     * Creates an EGPTNumber from a rational pair of BigInts.
     * RATIONAL ENCODING: Normal space fraction → Canonical information vector
     * @param {BigInt} numerator - Numerator as BigInt scalar
     * @param {BigInt} denominator - Denominator as BigInt scalar  
     * @returns {EGPTNumber} - Canonical information vector
     */
    static fromRational(numerator, denominator) {
        if (denominator === 0n) throw new Error("Denominator cannot be zero.");

        // Use the internal encoding method to handle negatives properly
        const ppf_pair = EGPTNumber._encodeRationalToPPF(numerator, denominator);
        return new EGPTNumber(ppf_pair);
    }

    /**
     * Creates an EGPTNumber from canonical PPF representation.
     * DIRECT CANONICAL ACCESS: PPF → Information vector (preferred method)
     * Supports both legacy format (without scalar) and extended format (with scalar)
     * 
     * @param {{scalar?: {numerator: BigInt, denominator: BigInt}, numerator: {N: BigInt, offset: BigInt}, denominator: {N: BigInt, offset: BigInt}}} ppf_data
     * @returns {EGPTNumber} - Canonical information vector
     */
    static fromPPF(ppf_data) {
        const scalar = ppf_data.scalar || null; // Use provided scalar or default to 1/1

        return new EGPTNumber({
            numerator_encodedAsLog2ppf: ppf_data.numerator,
            denominator_encodedAsLog2ppf: ppf_data.denominator
        }, scalar);
    }

    /**
     * Creates an EGPTNumber from CIS (Canonical Information Space) data.
     * @param {Object} cis_data - CIS representation
     * @returns {EGPTNumber} - Canonical information vector
     */
    static fromCIS(cis_data) {
        const ppf_data = EGPTNumber._cisToPPF(cis_data);
        return EGPTNumber.fromPPF(ppf_data);
    }

    /**
     * 🎯 CREATES SCALED VECTOR: Supports irrational numbers via scalar multiplication
     * 
     * MATHEMATICAL FOUNDATION (per ADDING_Vector_Scaling.md):
     * H(√k) = (1/2) * H(k) represented as { scalar: (1,2), base: H(k) }
     * This enables exact representation of irrational roots without approximation.
     * 
     * EXAMPLES:
     * - H(√2) = fromScaledVector(H(2), 1n, 2n)  // (1/2) * H(2)
     * - H(∛8) = fromScaledVector(H(8), 1n, 3n)  // (1/3) * H(8)  
     * - H(2^(3/2)) = fromScaledVector(H(2), 3n, 2n)  // (3/2) * H(2)
     * 
     * @param {EGPTNumber} base_vector - Base information vector H(k)
     * @param {BigInt} scalar_num - Scalar numerator
     * @param {BigInt} scalar_den - Scalar denominator  
     * @returns {EGPTNumber} - Scaled vector representing scalar * base_vector
     */
    static fromScaledVector(base_vector, scalar_num, scalar_den) {
        if (scalar_den === 0n) throw new Error("Scalar denominator cannot be zero.");

        SimpleLogger.log(`🎯 Creating scaled vector: (${scalar_num}/${scalar_den}) * base_vector`);
        SimpleLogger.log(`   Enables exact irrational representation per ADDING_Vector_Scaling.md`);

        // Clone the base vector's PPF data
        const ppf_pair = {
            numerator_encodedAsLog2ppf: { ...base_vector.numerator_encodedAsLog2ppf },
            denominator_encodedAsLog2ppf: { ...base_vector.denominator_encodedAsLog2ppf }
        };

        // Combine scalars: new_scalar = base_scalar * input_scalar
        const combined_scalar_num = base_vector.scalar_numerator * scalar_num;
        const combined_scalar_den = base_vector.scalar_denominator * scalar_den;

        const scalar = {
            numerator: combined_scalar_num,
            denominator: combined_scalar_den
        };

        return new EGPTNumber(ppf_pair, scalar);
    }

    /**
     * SYNTACTIC SUGAR: Negates an existing EGPTNumber (including scaled vectors).
     * 
     * SPECIAL HANDLING:
     * - For unscaled values (scalar=1/1): Creates proper negative integer/rational
     * - For scaled vectors: Uses scalarMultiply(-1n) (RZF pattern)
     * 
     * This avoids creating negative-scaled vectors which break EGPTMath.multiply.
     * 
     * Example:
     * ```javascript
     * H(5) → H(-5)              // Plain negative integer
     * (1/4)*H(2) → (-1/4)*H(2)  // Negative-scaled vector
     * ```
     * 
     * @param {EGPTNumber} value - Value to negate
     * @returns {EGPTNumber} Negated value
     */
    static negate(value) {
        const scalar_parts = value.getScalarParts();
        
        // Check if this is an unscaled value (scalar = ±1/1)
        // Include both positive and negative unit scalars to normalize them
        const abs_num = scalar_parts.numerator < 0n ? -scalar_parts.numerator : scalar_parts.numerator;
        
        if (abs_num === 1n && scalar_parts.denominator === 1n) {
            // For unit-scaled values (including negative like (-1)*H(1)), create proper integer/rational
            const rational_parts = value._getPPFRationalParts();
            const current_scalar = scalar_parts.numerator / scalar_parts.denominator;
            
            // Apply current scalar and negate
            const final_numerator = -(rational_parts.numerator * scalar_parts.numerator);
            
            return EGPTNumber.fromRational(
                final_numerator,
                rational_parts.denominator
            );
        } else {
            // For truly scaled vectors (like (1/2)*H(2) = √2), use scalar negation
            return value.clone().scalarMultiply(-1n);
        }
    }

    /**
     * SYNTACTIC SUGAR: Safely negates the imaginary component for conjugate.
     * 
     * Helper for creating complex conjugates without expensive operations.
     * 
     * @param {EGPTNumber} value - Value to negate
     * @returns {EGPTNumber} Negated value
     */
    static negateForConjugate(value) {
        return value.clone().scalarMultiply(-1n);
    }

    // =============================================================================
    // INSPECTOR METHODS (Public Instance) - VECTOR STATE EXAMINATION
    // =============================================================================

    /**
     * Gets the rational parts of this information vector including scalar multiplier.
     * CANONICAL EXTRACTION: Scaled Vector → Normal space rational components
     * 
     * MATHEMATICAL CALCULATION:
     * For scaled vector (s_num/s_den) * (base_num/base_den):
     * Result = (s_num * base_num) / (s_den * base_den)
     * 
     * @returns {{numerator: BigInt, denominator: BigInt}} - Normal space rational with scalar applied
     */
    _getPPFRationalParts() {
        const base_numerator = EGPTNumber._decodePPFLog2ToInteger(this.numerator_encodedAsLog2ppf);
        const base_denominator = EGPTNumber._decodePPFLog2ToInteger(this.denominator_encodedAsLog2ppf);

        // Apply scalar multiplication: (s_num/s_den) * (base_num/base_den)
        const result_numerator = this.scalar_numerator * base_numerator;
        const result_denominator = this.scalar_denominator * base_denominator;

        return {
            numerator: result_numerator,
            denominator: result_denominator
        };
    }

    /**
     * Gets the base vector components without scalar multiplier.
     * USEFUL for examining the underlying rational representation.
     * @returns {{numerator: BigInt, denominator: BigInt}} - Base rational without scalar
     */
    getBaseRationalParts() {
        return {
            numerator: EGPTNumber._decodePPFLog2ToInteger(this.numerator_encodedAsLog2ppf),
            denominator: EGPTNumber._decodePPFLog2ToInteger(this.denominator_encodedAsLog2ppf)
        };
    }

    /**
     * Gets the scalar multiplier components.
     * @returns {{numerator: BigInt, denominator: BigInt}} - Scalar multiplier as rational
     */
    getScalarParts() {
        return {
            numerator: this.scalar_numerator,
            denominator: this.scalar_denominator
        };
    }


    /**
     * Tests if this vector represents an integer in normal space.
     * @returns {boolean} - True if denominator divides numerator exactly
     */
    isInteger() {
        const rational = this._getPPFRationalParts();
        if (rational.denominator === 0n) throw new Error("Invalid rational with zero denominator");
        return (rational.numerator % rational.denominator) === 0n;
    }

    /**
     * Tests mathematical equality with another information vector including scalar multipliers.
     * THE ONLY public vector-vector method - fundamental to object identity.
     * 
     * COMPARISON LOGIC:
     * Two scaled vectors are equal if their final rational values are equal:
     * (s1_num/s1_den) * (base1_num/base1_den) == (s2_num/s2_den) * (base2_num/base2_den)
     * 
     * @param {EGPTNumber} other_en - Other information vector to compare
     * @returns {boolean} - True if vectors are mathematically equal
     */
    equals(other_en) {
        const thisRational = this._getPPFRationalParts();
        const otherRational = other_en._getPPFRationalParts();

        // Cross multiply to test equality: a/b = c/d iff a*d = b*c
        return (thisRational.numerator * otherRational.denominator) ===
            (thisRational.denominator * otherRational.numerator);
    }

    /**
     * Returns mathematical string representation of this scaled vector.
     * Shows scalar multiplier when it's not 1, and base vector representation.
     * 
     * EXAMPLES:
     * - Standard rational: "3/4" 
     * - Scaled vector: "(1/2) * H(2)" for H(√2)
     * - Identity scalar: "5" (scalar 1/1 is hidden)
     * 
     * @returns {string} - Mathematical notation showing scalar and base
     */
    toMathString() {
        const rational = this._getPPFRationalParts();
        const isIdentityScalar = (this.scalar_numerator === 1n && this.scalar_denominator === 1n);

        // For identity scalar, just show the final rational value
        if (isIdentityScalar) {
            if (rational.denominator === 1n) {
                return rational.numerator.toString();
            }
            return `${rational.numerator}/${rational.denominator}`;
        }

        // For non-identity scalar, show the scaling operation
        const base_rational = this.getBaseRationalParts();
        const scalar_str = this.scalar_denominator === 1n ?
            this.scalar_numerator.toString() :
            `${this.scalar_numerator}/${this.scalar_denominator}`;

        const base_str = base_rational.denominator === 1n ?
            `H(${base_rational.numerator})` :
            `H(${base_rational.numerator}/${base_rational.denominator})`;

        return `(${scalar_str}) * ${base_str}`;
    }

    /**
     * Gets the rational parts of this information vector with intelligent scalar resolution.
     * CANONICAL EXTRACTION: Attempts to compute exact values when possible, falls back to scaled representation
     * 
     * ENHANCED LOGIC:
     * 1. If scalar is 1/1 (identity), return base rational directly
     * 2. If scalar represents a root that can be computed exactly, compute it
     * 3. If scalar represents a power that can be computed exactly, compute it
     * 4. Otherwise, fall back to arithmetic scalar application (may lose precision)
     * 
     * @returns {{numerator: BigInt, denominator: BigInt}} - Best available rational representation
     */
    getRationalParts() {
        const base_numerator = EGPTNumber._decodePPFLog2ToInteger(this.numerator_encodedAsLog2ppf);
        const base_denominator = EGPTNumber._decodePPFLog2ToInteger(this.denominator_encodedAsLog2ppf);

        // Case 1: Identity scalar - return base directly
        if (this.scalar_numerator === 1n && this.scalar_denominator === 1n) {
            return {
                numerator: base_numerator,
                denominator: base_denominator
            };
        }

        const [final_num, is_exact] =  nthRoot(this._getPPFRationalParts().numerator, this._getPPFRationalParts().denominator);

        if (!is_exact) {
            console.warn("⚠️ PRECISION LOSS: USE EGPTMath operations like .equal(a_en, b_en) instead! Leaving canonical space results unpredictable. getRationalParts() Attempting to compute rational parts with scalar multiplier");
        }

        return {
            numerator: final_num,
            denominator: 1n // Always return denominator as 1 for rational part after nth root (loss of precision)
        };

    }


    /**
     * Enhanced toBigInt with better precision handling
     * Attempts exact computation when possible, warns appropriately when precision is lost
     */
    toBigInt() {
        let rational = this._getPPFRationalParts();
        if (rational.denominator === 0n) throw new Error("Division by zero in toBigInt");

        // Check if the result will be exact
        const remainder = rational.numerator % rational.denominator;

        if (remainder !== 0n) {
            // Check if this is an expected precision loss (e.g., irrational number)
            const scalar_parts = this.getScalarParts();
            if (scalar_parts.numerator !== 1n || scalar_parts.denominator !== 1n) {
                rational = this.getRationalParts(); // Get best available rational parts
                console.warn("⚠️ toBigInt(): Precision loss expected for scaled vector representing irrational value");
                console.warn(`   Scaled vector: (${scalar_parts.numerator}/${scalar_parts.denominator}) * base`);
                console.warn(`   Consider using toNumber() for decimal approximation or keeping in scaled form`);
            } else {
                console.warn("⚠️ toBigInt(): May lose precision if not an integer");
            }
        }

        return rational.numerator / rational.denominator;
    }

    /**
     * Enhanced toNumber with intelligent handling
     * Provides the best decimal approximation available
     */
    toNumber() {
        // Use _getPPFRationalParts() to get exact value (including scalar applied)
        const rational = this._getPPFRationalParts();
        if (rational.denominator === 0n) throw new Error("Division by zero in toNumber");

        // Check if the result will be exact
        const remainder = rational.numerator % rational.denominator;

        if (remainder !== 0n) {
            // Check if this is an expected precision loss (e.g., irrational number)
            const scalar_parts = this.getScalarParts();
            if (scalar_parts.numerator !== 1n || scalar_parts.denominator !== 1n) {
                console.warn("⚠️ toNumber(): Precision loss expected for scaled vector representing irrational value");
                console.warn(`   Scaled vector: (${scalar_parts.numerator}/${scalar_parts.denominator}) * base`);
                console.warn(`   Consider using toBigInt() for integer approximation or keeping in scaled form`);
            } else {
                console.warn("⚠️ toNumber(): May lose precision if not an integer");
            }
        }

        // Convert to Number safely
        if (rational.denominator === 0n) {
            throw new Error("Cannot convert to number: division by zero");
        }

        // For very large numbers, warn about potential precision loss
        const num_bits = rational.numerator.toString(2).length;
        const den_bits = rational.denominator.toString(2).length;

        if (num_bits > 53 || den_bits > 53) {
            console.warn("⚠️ toNumber(): JavaScript Number precision limit may affect result");
        }

        return Number(rational.numerator) / Number(rational.denominator);
    }

   

    /**
     * Exports the canonical PPF representation including scalar multiplier.
     * CANONICAL EXTRACTION: Scaled Vector → Complete PPF format (perfect information preservation)
     * 
     * @returns {{scalar: {numerator: BigInt, denominator: BigInt}, numerator: {N: BigInt, offset: BigInt}, denominator: {N: BigInt, offset: BigInt}}}
     */
    toPPF() {
        return {
            scalar: {
                numerator: this.scalar_numerator,
                denominator: this.scalar_denominator
            },
            numerator: { ...this.numerator_encodedAsLog2ppf },
            denominator: { ...this.denominator_encodedAsLog2ppf }
        };
    }

    /**
     * Exports CIS (Canonical Information Space) representation.
     * @returns {Object} - CIS format for persistence/analysis
     */
    toCIS() {
        return EGPTNumber._ppfToCIS(this.toPPF());
    }

    /**
     * Creates a deep clone of this information vector including scalar multiplier.
     * ESSENTIAL for mutable object model - enables safe scalar operations.
     * @returns {EGPTNumber} - Independent copy of this scaled vector
     */
    clone() {
        const scalar = {
            numerator: this.scalar_numerator,
            denominator: this.scalar_denominator
        };

        return new EGPTNumber({
            numerator_encodedAsLog2ppf: { ...this.numerator_encodedAsLog2ppf },
            denominator_encodedAsLog2ppf: { ...this.denominator_encodedAsLog2ppf }
        }, scalar, true); // Skip reduction since original is already reduced
    }

    // =============================================================================
    // SCALAR OPERATIONS (Public Instance) - MUTABLE CHAINING OPERATIONS
    // =============================================================================

    /**
     * 🎯 SCALAR ADDITION: Vector translation by scalar amount
     * VECTOR ANALOGY: Translate vector H(p) by scalar amount s → H(p + s)
     * 
     * For scaled vectors, this operates on the final rational value:
     * (scalar * base) + s = ((scalar * base_num + s * base_den) / base_den)
     * 
     * MODIFIES this instance and returns this for fluent chaining.
     * @param {BigInt} scalar - Scalar amount to add
     * @returns {this} - This instance for chaining
     */
    scalarAdd(scalar) {
        if (typeof scalar !== 'bigint') {
            throw new Error("scalarAdd requires BigInt scalar");
        }

        const current_rational = this._getPPFRationalParts();

        // Rational addition: current + scalar = current + (scalar * denominator) / denominator
        const new_numerator = current_rational.numerator + (scalar * current_rational.denominator);
        const new_denominator = current_rational.denominator;

        // Replace this vector with the new rational - reset scalar to 1/1
        const encoded = EGPTNumber._encodeRationalToPPF(new_numerator, new_denominator);
        this.numerator_encodedAsLog2ppf = encoded.numerator_encodedAsLog2ppf;
        this.denominator_encodedAsLog2ppf = encoded.denominator_encodedAsLog2ppf;

        // Reset scalar to identity since we've absorbed it into the base
        this.scalar_numerator = 1n;
        this.scalar_denominator = 1n;

        // Auto-reduce to maintain canonical form
        const reduced = this._reduce();
        this.numerator_encodedAsLog2ppf = reduced.numerator_encodedAsLog2ppf;
        this.denominator_encodedAsLog2ppf = reduced.denominator_encodedAsLog2ppf;

        return this;
    }

    /**
     * 🎯 SCALAR SUBTRACTION: Vector translation by negative scalar amount  
     * VECTOR ANALOGY: Translate vector H(p) by -scalar → H(p - s)
     * MODIFIES this instance and returns this for fluent chaining.
     * @param {BigInt} scalar - Scalar amount to subtract
     * @returns {this} - This instance for chaining
     */
    scalarSubtract(scalar) {
        if (typeof scalar !== 'bigint') {
            throw new Error("scalarSubtract requires BigInt scalar");
        }
        return this.scalarAdd(-scalar);
    }

    /**
     * 🎯 SCALAR MULTIPLICATION: Vector scaling by scalar factor
     * VECTOR ANALOGY: Scale vector H(p) by factor s → H(p * s)
     * 
     * For scaled vectors, we can efficiently multiply the scalar component:
     * s * (scalar_num/scalar_den) * base = (s * scalar_num / scalar_den) * base
     * 
     * MODIFIES this instance and returns this for fluent chaining.
     * @param {BigInt} scalar - Scalar factor to multiply by
     * @returns {this} - This instance for chaining
     */
    scalarMultiply(scalar) {
        if (typeof scalar !== 'bigint') {
            throw new Error("scalarMultiply requires BigInt scalar");
        }

        if (scalar === 0n) {
            // Multiply by zero results in zero vector
            const encoded = EGPTNumber._encodeRationalToPPF(0n, 1n);
            this.numerator_encodedAsLog2ppf = encoded.numerator_encodedAsLog2ppf;
            this.denominator_encodedAsLog2ppf = encoded.denominator_encodedAsLog2ppf;
            this.scalar_numerator = 1n;
            this.scalar_denominator = 1n;
            return this;
        }

        // Multiply the scalar component: new_scalar = scalar * old_scalar
        this.scalar_numerator = this.scalar_numerator * scalar;

        // Reduce the scalar to maintain canonical form
        const scalar_gcd = gcd(this.scalar_numerator < 0n ? -this.scalar_numerator : this.scalar_numerator, this.scalar_denominator);
        this.scalar_numerator = this.scalar_numerator / scalar_gcd;
        this.scalar_denominator = this.scalar_denominator / scalar_gcd;

        return this;
    }


    /**
  * 🎯 SCALAR MULTIPLICATION: Vector scaling by scalar factor
  * VECTOR ANALOGY: Scale vector H(p) by factor s → H(p * s)  
  * MODIFIES this instance and returns this for fluent chaining.
  * @param {BigInt} scalar_num - Scalar factor to multiply by
  * @returns {this} - This instance for chaining
  */
    scalarFractionMultiply(scalar_num, scalar_den = 1n) {
        if (typeof scalar_num !== 'bigint') {
            throw new Error("scalarMultiply requires BigInt scalar");
        }

        if (scalar_num === 0n) {
            // Multiply by zero results in zero vector - use _encodeRationalToPPF for safety
            const encoded = EGPTNumber._encodeRationalToPPF(0n, 1n);
            this.numerator_encodedAsLog2ppf = encoded.numerator_encodedAsLog2ppf;
            this.denominator_encodedAsLog2ppf = encoded.denominator_encodedAsLog2ppf;
            return this;
        }

        const current_rational = this._getPPFRationalParts();

        const new_numerator = current_rational.numerator;
        const new_denominator = current_rational.denominator;

        //TODO Need to apply the Formula: product_value = 2^(N_p + N_q) + (offset_p * 2^N_q) + (offset_q * 2^N_p) + (offset_p * offset_q)


        // Use _encodeRationalToPPF to handle negative numbers properly
        const encoded = EGPTNumber._encodeRationalToPPF(new_numerator, new_denominator);
        this.numerator_encodedAsLog2ppf = encoded.numerator_encodedAsLog2ppf;
        this.denominator_encodedAsLog2ppf = encoded.denominator_encodedAsLog2ppf;

        // Auto-reduce to maintain canonical form
        const reduced = this._reduce();
        this.numerator_encodedAsLog2ppf = reduced.numerator_encodedAsLog2ppf;
        this.denominator_encodedAsLog2ppf = reduced.denominator_encodedAsLog2ppf;

        return this;
    }

    /**
     * 🎯 SCALAR DIVISION: Vector scaling by inverse scalar factor
     * VECTOR ANALOGY: Scale vector H(p) by 1/s → H(p / s)
     * 
     * For scaled vectors, we can efficiently divide the scalar component:
     * (scalar_num/scalar_den) * base / s = (scalar_num / (scalar_den * s)) * base
     * 
     * MODIFIES this instance and returns this for fluent chaining.
     * @param {BigInt} scalar - Scalar divisor (must be non-zero)
     * @returns {this} - This instance for chaining
     */
    scalarDivide(scalar) {
        if (typeof scalar !== 'bigint') {
            throw new Error("scalarDivide requires BigInt scalar");
        }

        if (scalar === 0n) {
            throw new Error("Division by zero scalar is undefined");
        }

        // Divide the scalar component: new_scalar = old_scalar / scalar
        this.scalar_denominator = this.scalar_denominator * scalar;

        // Handle negative divisor by flipping sign of numerator
        if (scalar < 0n) {
            this.scalar_numerator = -this.scalar_numerator;
            this.scalar_denominator = -this.scalar_denominator;
        }

        // Reduce the scalar to maintain canonical form
        const scalar_gcd = gcd(this.scalar_numerator < 0n ? -this.scalar_numerator : this.scalar_numerator, this.scalar_denominator);
        this.scalar_numerator = this.scalar_numerator / scalar_gcd;
        this.scalar_denominator = this.scalar_denominator / scalar_gcd;

        return this;
    }

    // =============================================================================
    // INTERNAL HELPERS (Private _ Methods) - PPF ENGINE FOR EGPTMath
    // =============================================================================

    /**
     * INTERNAL: Scale an EGPTNumber by a rational (n_num/n_den).
     * Properly multiplies all components and reduces to canonical form.
     * 
     * Algorithm:
     * 1. Get current value as rational: (s_num/s_den) * (b_num/b_den)
     * 2. Multiply by scale: (n_num/n_den) * (s_num/s_den) * (b_num/b_den)
     * 3. Simplify: (n_num * s_num * b_num) / (n_den * s_den * b_den)
     * 4. Create new EGPTNumber with canonical form
     * 
     * @param {EGPTNumber} value - Value to scale
     * @param {BigInt} scale_num - Numerator of scaling factor
     * @param {BigInt} scale_den - Denominator of scaling factor
     * @returns {EGPTNumber} Scaled value in canonical form
     */
    static _scaleRationalByRational(value, scale_num, scale_den) {
        // Get current components
        const scalar_parts = value.getScalarParts();
        
        // Get base rational WITHOUT scalar multiplication
        const base_num = EGPTNumber._decodePPFLog2ToInteger(value.numerator_encodedAsLog2ppf);
        const base_den = EGPTNumber._decodePPFLog2ToInteger(value.denominator_encodedAsLog2ppf);
        
        // Multiply all components: (scale_num/scale_den) * (scalar_num/scalar_den) * (base_num/base_den)
        const new_num = scale_num * scalar_parts.numerator * base_num;
        const new_den = scale_den * scalar_parts.denominator * base_den;
        
        // Create new EGPTNumber from the resulting rational (constructor will reduce)
        return EGPTNumber.fromRational(new_num, new_den);
    }

    /**
     * INTERNAL: Converts integer to PPF-encoded log₂ representation.
     * Core of the Shannon encoding engine - used by EGPTMath.
     * @param {BigInt} n - Integer to encode
     * @returns {{N: BigInt, offset: BigInt}} - PPF representation
     */
    static _integerToPPFEncodedLog2(n) {
        if (n < 0n) throw new Error("PPF encoding requires non-negative integers");
        if (n === 0n) return { N: -1n, offset: 0n }; // Special case for zero
        if (n === 1n) return { N: 0n, offset: 0n }; // 1 = 2^0 + 0

        // Find N = floor(log₂(n))
        let N = 0n;
        let power_of_2 = 1n;
        while (power_of_2 <= n) {
            if (power_of_2 * 2n > n) break;
            power_of_2 *= 2n;
            N++;
        }

        // Calculate offset = n - 2^N
        const offset = n - power_of_2;
        return { N, offset };
    }

    /**
     * INTERNAL: Decodes PPF log₂ representation back to integer.
     * This version is updated to understand the new convention for negative numbers.
     * @param {{N: BigInt, offset: BigInt}} ppf - PPF representation
     * @returns {BigInt} - Decoded integer (can be negative)
     */
    static _decodePPFLog2ToInteger(ppf) {
        // Case 1: The number is 0.
        if (ppf.N === -1n) {
            // We can add a sanity check: for a canonical zero, offset must be 0.
            if (ppf.offset !== 0n) {
                console.warn(`[EGPTNumber] Non-canonical zero detected: N=-1, offset=${ppf.offset}. Treating as zero.`);
            }
            return 0n;
        }

        // --- Start of New Logic ---

        // Case 2: The number is negative (N < -1).
        if (ppf.N < -1n) {
            // Reverse the transformation: N_abs = -N_neg - 2
            const N_abs = -ppf.N - 2n;

            // Reconstruct the absolute value from the recovered absolute N.
            const abs_value = (1n << N_abs) + ppf.offset;

            // Return the negated result.
            return -abs_value;
        }

        // --- End of New Logic ---

        // Case 3: The number is positive (N >= 0). This logic is unchanged.
        return (1n << ppf.N) + ppf.offset; // 2^N + offset
    }

    /**
     * INTERNAL: Addition in PPF log₂ space - implements Shannon entropy addition.
     * Core operation for EGPTMath vector algebra.
     * @param {{N: BigInt, offset: BigInt}} ppf_a - First PPF
     * @param {{N: BigInt, offset: BigInt}} ppf_b - Second PPF
     * @returns {{N: BigInt, offset: BigInt}} - Sum in PPF space
     */
    static _addInPPFLog2(ppf_a, ppf_b) {
        // Decode to integers, add, re-encode
        const a = EGPTNumber._decodePPFLog2ToInteger(ppf_a);
        const b = EGPTNumber._decodePPFLog2ToInteger(ppf_b);
        const sum = a * b; // Multiplication in normal space = addition in log space

        // Use _encodeRationalToPPF to handle negative results properly
        const encoded = EGPTNumber._encodeRationalToPPF(sum, 1n);
        return encoded.numerator_encodedAsLog2ppf;
    }

    /**
     * INTERNAL: Converts CIS to PPF format.
     * @param {Array} cis - CIS representation
     * @returns {{numerator: object, denominator: object}} - PPF format
     */
    static _cisToPPF(cis) {
        // Implementation depends on CIS format - placeholder for now
        throw new Error("_cisToPPF not yet implemented");
    }

    /**
     * INTERNAL: Converts PPF to CIS format.
     * @param {{numerator: object, denominator: object}} ppf - PPF format  
     * @returns {Array} - CIS representation
     */
    static _ppfToCIS(ppf) {
        // Implementation depends on CIS format - placeholder for now
        throw new Error("_ppfToCIS not yet implemented");
    }

    // =============================================================================
    // STRING REPRESENTATION
    // =============================================================================

    /**
     * Returns string representation for debugging/display.
     * @returns {string} - Mathematical string representation
     */
    toString() {
        return this.toMathString();
    }
}

// ComplexEGPTNumber and TwiddleTable have been moved to EGPTComplex.js

export { EGPTNumber };

SimpleLogger.log("🎯 EGPTNumber Refactored: Pure vector data container with scalar operations");
SimpleLogger.log("📐 Vector paradigm: EGPTNumber = Information Vector, BigInt = Scalar");
SimpleLogger.log("🔗 Fluent chaining: vector.scalarAdd(5n).scalarMultiply(2n).scalarDivide(3n)");
SimpleLogger.log("🌀 TwiddleTable: Phase-based FFT operations for unlimited precision");
