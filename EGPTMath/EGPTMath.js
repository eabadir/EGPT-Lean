// =============================================================================
// EGPT MATH REFACTORED - PURE VECTOR ALGEBRA ENGINE
// Based on EGPT Vector Space Refactor v3.0: Scalar & Vector Paradigm
//
// Author: E. Abadir
// Copyright (C) 2026 Essam Abadir
// Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
// See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
// Provided WITHOUT ANY WARRANTY. See the DCSL for details.
//
// Paradigm: EGPTMath as VECTOR ALGEBRA ENGINE - pure static library
//           Intuitive normal-space naming that abstracts log-space mechanics
//           ALL vector-vector operations centralized here from EGPTNumber
// =============================================================================

import { SimpleLogger } from './DebugLogger.js';
import { EGPTNumber } from './EGPTNumber.js';

SimpleLogger.log("🎓 CANONICAL INFORMATION SPACE: Vector/Scalar paradigm");
SimpleLogger.log("🎯 EGPTMath: Static vector algebra engine");

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
 * 🎯 REFACTORED EGPTMath: PURE VECTOR ALGEBRA ENGINE
 * 
 * ARCHITECTURAL PRINCIPLE: This class operates on EGPTNumber vectors to perform
 * vector algebra with intuitive normal-space naming.
 * 
 * KEY DESIGN PRINCIPLES:
 * - ALL methods are static (cannot be instantiated)
 * - Operates on CLONES to prevent side effects (EGPTNumber instances are mutable)
 * - Returns NEW EGPTNumber instances (functional purity for algebra engine)
 * - Intuitive API: multiply(), divide(), pow() abstract away log-space mechanics
 * - Pedagogical dual naming: addInLogSpace() shows Shannon perspective
 * 
 * VECTOR OPERATIONS MAPPING:
 * Normal Space → Shannon Space → Vector Operation
 * p × q       → H(p) + H(q)   → Vector Addition (tip-to-tail)
 * k ÷ p       → H(k) - H(p)   → Vector Subtraction  
 * base^exp    → exp × H(base) → Repeated Vector Addition
 */
class EGPTMath {
    // Prevent instantiation of this static class
    constructor() {
        throw new Error("EGPTMath is a static class and cannot be instantiated.");
    }

    // Cache for TwiddleTable instances to avoid recreation overhead
    static _twiddleTableCache = new Map();

    // =============================================================================
    // 🎯 PRIMARY VECTOR OPERATIONS - Normal Space API
    // =============================================================================

    /**
     * 🎯 VECTOR MULTIPLICATION: H(p) + H(q) = H(p×q)
     * 
     * VECTOR ANALOGY: Tip-to-tail vector addition in information space
     * MATHEMATICAL TRUTH: Normal space multiplication = Shannon space addition
     * This IS the RET Iron Law implementation: H(p×q) = H(p) + H(q)
     * 
     * @param {EGPTNumber} p_en - First factor vector H(p)
     * @param {EGPTNumber} q_en - Second factor vector H(q)
     * @returns {EGPTNumber} - Product vector H(p×q) = H(p) + H(q)
     */
    static multiply(p_en, q_en) {
        SimpleLogger.log("🎯 Vector Multiplication: H(p) + H(q) = H(p×q) [RET Iron Law]");
        SimpleLogger.log(`   Input H(p): ${p_en.toMathString()}`);
        SimpleLogger.log(`   Input H(q): ${q_en.toMathString()}`);

        // Work on clones to prevent side effects
        const p_clone = p_en.clone();
        const q_clone = q_en.clone();

        const p_scalar = p_clone.getScalarParts();
        const q_scalar = q_clone.getScalarParts();

        // --- NEW LOGIC: Check for common base vector ---
        // Create temporary base-only numbers for comparison (scalar = 1/1)
        const p_base = new EGPTNumber({
            numerator_encodedAsLog2ppf: p_clone.numerator_encodedAsLog2ppf,
            denominator_encodedAsLog2ppf: p_clone.denominator_encodedAsLog2ppf
        }, { numerator: 1n, denominator: 1n }, true);
        const q_base = new EGPTNumber({
            numerator_encodedAsLog2ppf: q_clone.numerator_encodedAsLog2ppf,
            denominator_encodedAsLog2ppf: q_clone.denominator_encodedAsLog2ppf
        }, { numerator: 1n, denominator: 1n }, true);

        if (p_base.equals(q_base)) {
            SimpleLogger.log(`   Common base detected: ${p_base.toMathString()}. Adding scalars.`);

            // Add scalars: (a/b) + (c/d) = (ad+bc)/bd
            const new_s_num = (p_scalar.numerator * q_scalar.denominator) + (q_scalar.numerator * p_scalar.denominator);
            const new_s_den = p_scalar.denominator * q_scalar.denominator;

            // CRITICAL: When scalar sum is 0, this means base^0 = 1
            // Return H(1) directly, not a zero-scaled vector
            if (new_s_num === 0n) {
                SimpleLogger.log(`   Scalars sum to 0: base^0 = 1, returning H(1)`);
                return EGPTNumber.fromBigInt(1n);
            }

            const final_result = EGPTNumber.fromScaledVector(p_base, new_s_num, new_s_den);
            SimpleLogger.log(`   Result H(p×q): ${final_result.toMathString()}`);
            return final_result;
        }

        // Check if scalars are equal
        if (p_scalar.numerator === q_scalar.numerator && p_scalar.denominator === q_scalar.denominator) {
            // If scalars are the same, multiply the bases and re-apply the scalar
            SimpleLogger.log(`   Common scalar detected: ${p_scalar.numerator}/${p_scalar.denominator}. Multiplying base vectors.`);

            const new_num_ppf = EGPTNumber._addInPPFLog2(
                p_clone.numerator_encodedAsLog2ppf,
                q_clone.numerator_encodedAsLog2ppf
            );
            const new_den_ppf = EGPTNumber._addInPPFLog2(
                p_clone.denominator_encodedAsLog2ppf,
                q_clone.denominator_encodedAsLog2ppf
            );

            const base_result = new EGPTNumber({
                numerator_encodedAsLog2ppf: new_num_ppf,
                denominator_encodedAsLog2ppf: new_den_ppf
            });

            const final_result = EGPTNumber.fromScaledVector(base_result, p_scalar.numerator, p_scalar.denominator);
            SimpleLogger.log(`   Result H(p×q): ${final_result.toMathString()}`);
            return final_result;

        } else if (p_scalar.numerator === 1n && p_scalar.denominator === 1n) {
            // p is not scaled, q has scalar s: H(p) * H(q^s) = H(p * q^s) = s * H(p^(1/s) * q)
            // For H(2) * H(√3): H(2 * √3) = H(√(4*3)) = H(√12) = (1/2) * H(12)
            const p_base_rational = p_clone.getBaseRationalParts();
            const q_base_rational = q_clone.getBaseRationalParts();

            // Calculate p^(1/scalar) * q = p^(den/num) * q
            // For H(2) * H(√3): 2^(2/1) * 3 = 4 * 3 = 12
            const p_power_num = q_scalar.denominator;
            const p_power_den = q_scalar.numerator;

            // Compute p^(p_power_num/p_power_den)
            const p_powered_num = p_base_rational.numerator ** p_power_num;
            const p_powered_den = p_base_rational.denominator ** p_power_num;

            const new_base_num = p_powered_num * q_base_rational.numerator;
            const new_base_den = p_powered_den * q_base_rational.denominator;

            const new_base = EGPTNumber.fromRational(new_base_num, new_base_den);
            const final_result = EGPTNumber.fromScaledVector(new_base, q_scalar.numerator, q_scalar.denominator);
            SimpleLogger.log(`   Result H(p×q): ${final_result.toMathString()}`);
            return final_result;

        } else if (q_scalar.numerator === 1n && q_scalar.denominator === 1n) {
            // q is not scaled, p has scalar s: H(p^s) * H(q) = H(p^s * q) = s * H(p * q^(1/s))
            // For H(√2) * H(3): H(√2 * 3) = H(√(2*9)) = H(√18) = (1/2) * H(18)
            const p_base_rational = p_clone.getBaseRationalParts();
            const q_base_rational = q_clone.getBaseRationalParts();

            // Calculate p * q^(1/scalar) = p * q^(den/num)
            // For H(√2) * H(3): 2 * 3^(2/1) = 2 * 9 = 18
            const q_power_num = p_scalar.denominator;
            const q_power_den = p_scalar.numerator;

            // Compute q^(q_power_num/q_power_den)
            const q_powered_num = q_base_rational.numerator ** q_power_num;
            const q_powered_den = q_base_rational.denominator ** q_power_num;

            const new_base_num = p_base_rational.numerator * q_powered_num;
            const new_base_den = p_base_rational.denominator * q_powered_den;

            const new_base = EGPTNumber.fromRational(new_base_num, new_base_den);
            const final_result = EGPTNumber.fromScaledVector(new_base, p_scalar.numerator, p_scalar.denominator);
            SimpleLogger.log(`   Result H(p×q): ${final_result.toMathString()}`);
            return final_result;
        }


        // If scalars are different and neither is 1, the operation is undefined in the current spec.
        // This represents adding H(a^(s1)) + H(b^(s2)) = H((a^s1)*(b^s2)), which doesn't have a simple
        // {scalar, base} representation.
        throw new Error("Vector multiplication with different, non-trivial scalars is not supported in this version.");
    }

    /**
     * 🎯 NORMAL DIVIDE using lossless operations on EGPTNumbers
     * 
     * @param {EGPTNumber} k_en - Dividend vector H(k)
     * @param {EGPTNumber} p_en - Divisor vector H(p)
     * @returns {EGPTNumber} - Quotient vector H(k/p) = H(k) - H(p)
     */
    static divide(k_en, p_en) {
        SimpleLogger.log("🎯 Vector Division: H(k) - H(p) = H(k/p) [Shannon Subtraction]");
        SimpleLogger.log(`   Input H(k): ${k_en.toMathString()}`);
        SimpleLogger.log(`   Input H(p): ${p_en.toMathString()}`);

        // Work on clones to prevent side effects
        const k_clone = k_en.clone();
        const p_clone = p_en.clone();

        const k_scalar = k_clone.getScalarParts();
        const p_scalar = p_clone.getScalarParts();

        // Check if scalars are equal
        if (k_scalar.numerator === p_scalar.numerator && k_scalar.denominator === p_scalar.denominator) {
            // If scalars are the same, divide the bases and re-apply the scalar
            SimpleLogger.log(`   Common scalar detected: ${k_scalar.numerator}/${k_scalar.denominator}. Dividing base vectors.`);

            const new_num_ppf = EGPTNumber._addInPPFLog2(
                k_clone.numerator_encodedAsLog2ppf,
                p_clone.denominator_encodedAsLog2ppf
            );
            const new_den_ppf = EGPTNumber._addInPPFLog2(
                k_clone.denominator_encodedAsLog2ppf,
                p_clone.numerator_encodedAsLog2ppf
            );

            const base_result = new EGPTNumber({
                numerator_encodedAsLog2ppf: new_num_ppf,
                denominator_encodedAsLog2ppf: new_den_ppf
            });

            const final_result = EGPTNumber.fromScaledVector(base_result, k_scalar.numerator, k_scalar.denominator);
            SimpleLogger.log(`   Result H(k/p): ${final_result.toMathString()}`);
            return final_result;
        }

        // If scalars are different, the operation is more complex.
        // H(k^s1) / H(p^s2) -> H((k^s1)/(p^s2))
        throw new Error("Vector division with different scalars is not supported in this version.");
    }

    /**
     * 🎯 NORMAL SPACE DIVISION: Traditional rational division (a / b)
     * This divides the final values of the vectors, not their logarithms.
     * It is the correct operation for statistical ratios like CV or range.
     * @param {EGPTNumber} a_en - The dividend vector.
     * @param {EGPTNumber} b_en - The divisor vector.
     * @returns {EGPTNumber} - A new vector representing the value a / b.
     */
    static normalDivide(a_en, b_en) {
        SimpleLogger.log("➗ Normal Space Division: a / b (for statistical ratios)");
        // Use _getPPFRationalParts() to preserve exact values including scaled vectors
        const a_rational = a_en._getPPFRationalParts();
        const b_rational = b_en._getPPFRationalParts();

        if (b_rational.numerator === 0n) {
            throw new Error("Division by zero in normalDivide.");
        }

        // (a_num/a_den) / (b_num/b_den) = (a_num * b_den) / (a_den * b_num)
        const new_num = a_rational.numerator * b_rational.denominator;
        const new_den = a_rational.denominator * b_rational.numerator;

        return EGPTNumber.fromRational(new_num, new_den);
    }

    /**
     * INTERNAL HELPER: Multiply coordinate values for complex arithmetic
     * 
     * Used for Euclidean complex multiplication: (a+bi)(c+di) = (ac-bd) + i(ad+bc)
     * where ac, bd, ad, bc are coordinate-wise products.
     * 
     * For pure rationals: straightforward rational multiplication
     * For scaled vectors: extracts signs, multiplies absolute values, reapplies sign
     * 
     * CRITICAL: This is NOT "normal space multiplication" - it's multiplication
     * of the coordinate representations within the PPF topology.
     * Negative values are handled as sign × magnitude, not as Shannon exponents.
     * 
     * @param {EGPTNumber} a_en - First coordinate value
     * @param {EGPTNumber} b_en - Second coordinate value  
     * @returns {EGPTNumber} - Product of coordinate values
     * @private
     */
    static _coordinateMultiply(a_en, b_en) {
        const a_scalar = a_en.getScalarParts();
        const b_scalar = b_en.getScalarParts();
        
        // Case 1: Both are pure rationals (no scaled vectors)
        if (a_scalar.numerator === 1n && a_scalar.denominator === 1n &&
            b_scalar.numerator === 1n && b_scalar.denominator === 1n) {
            // Simple rational multiplication
            const a_rational = a_en._getPPFRationalParts();
            const b_rational = b_en._getPPFRationalParts();
            const new_num = a_rational.numerator * b_rational.numerator;
            const new_den = a_rational.denominator * b_rational.denominator;
            return EGPTNumber.fromRational(new_num, new_den);
        }
        
        // For scaled vectors: Extract sign, multiply absolute values, reapply sign
        // This handles: (-a) × b = -(a × b) correctly
        
        const H_ZERO = EGPTNumber.fromBigInt(0n);
        const a_is_negative = EGPTMath.compare(a_en, H_ZERO) < 0;
        const b_is_negative = EGPTMath.compare(b_en, H_ZERO) < 0;
        
        const a_abs = a_is_negative ? EGPTNumber.negate(a_en) : a_en;
        const b_abs = b_is_negative ? EGPTNumber.negate(b_en) : b_en;
        
        // Multiply absolute values using Shannon multiply (works for scaled vectors)
        const product_abs = EGPTMath.multiply(a_abs, b_abs);
        
        // Apply combined sign
        const result_is_negative = a_is_negative !== b_is_negative; // XOR
        return result_is_negative ? EGPTNumber.negate(product_abs) : product_abs;
    }
    
    /**
     * @deprecated Legacy name for _coordinateMultiply
     */
    static normalMultiply(a_en, b_en) {
        return EGPTMath._coordinateMultiply(a_en, b_en);
    }

/**
     * 🎯 SCALAR MODULO: Computes the remainder of a % n using pure BigInt arithmetic.
     * This is the correct, lossless method for modular operations in normal space.
     * It operates on the exact rational values of the EGPTNumber vectors.
     *
     * @param {EGPTNumber} a_en - The dividend vector.
     * @param {EGPTNumber} n_en - The divisor vector.
     * @returns {EGPTNumber} A new vector representing the value a % n.
     */
    static mod (a_en, n_en) {
        SimpleLogger.log("🧮 Scalar Modulo: a % n (using exact BigInt arithmetic)");

        // 1. Get the exact, internal rational parts of both vectors.
        const a_rational = a_en._getPPFRationalParts();
        const n_rational = n_en._getPPFRationalParts();

        if (n_rational.numerator === 0n || n_rational.denominator === 0n) {
            throw new Error("Modulo by zero is undefined.");
        }

        // 2. Bring both rationals to a common denominator to perform the modulo.
        // a/b % c/d = (ad/bd) % (bc/bd)
        const common_denominator = a_rational.denominator * n_rational.denominator;
        const a_scaled_num = a_rational.numerator * n_rational.denominator;
        const n_scaled_num = n_rational.numerator * a_rational.denominator;
        
        if (n_scaled_num === 0n) {
             throw new Error("Modulo by zero is undefined.");
        }

        // 3. Perform the pure BigInt modulo on the scaled numerators.
        const remainder_num = a_scaled_num % n_scaled_num;

        // 4. The result is the remainder over the common denominator.
        // Result = (a_scaled_num % n_scaled_num) / common_denominator
        return EGPTNumber.fromRational(remainder_num, common_denominator);
    }



    /**
     * ⚠️ DEPRECATED/PEDAGOGICAL: Computes a "vector modulo" conceptually.
     * This was the previous, flawed implementation. It is kept for pedagogical
     * comparison but should not be used for precise calculations. Use EGPTMath.mod() instead.
     * Implements the mathematical definition: a mod n = a - n * floor(a/n).
     *
     * @param {EGPTNumber} H_a_en - The dividend vector.
     * @param {EGPTNumber} H_n_en - The divisor vector.
     * @returns {EGPTNumber} A new vector representing the remainder.
     */
    static vectorMod(H_a_en, H_n_en) {
        console.warn("⚠️ Using deprecated EGPTMath.vectorMod. Prefer the exact, scalar-based EGPTMath.mod().");
        // 1. Calculate a/n in normal space.
        const div_en = EGPTMath.normalDivide(H_a_en, H_n_en);
        
        // 2. Get the integer floor of the result. This step is lossy.
        const floor_div_scalar = div_en.toBigInt();
        const floor_div_en = EGPTNumber.fromBigInt(floor_div_scalar);

        // 3. Calculate n * floor(a/n) using normal space multiplication.
        // This requires a new normalMultiply method. Let's add it.
        const term_en = EGPTMath.normalMultiply(H_n_en, floor_div_en);

        // 4. Calculate a - (n * floor(a/n)) using normal space subtraction.
        const remainder_en = EGPTMath.subtract(H_a_en, term_en);

        return remainder_en;
    }
    
    // =============================================================================
    // 🎯 CORE VECTOR COMPARISON AND ARITHMETIC OPERATIONS
    // =============================================================================

    /**
     * 🌀 NORMAL SPACE ADDITION: Traditional rational addition (a + b)
     * @param {EGPTNumber} a_en - First vector value
     * @param {EGPTNumber} b_en - Second vector value
     * @returns {EGPTNumber} - Sum a + b in normal space
     */
    static add(a_en, b_en) {
        const a_rational = a_en._getPPFRationalParts();
        const b_rational = b_en._getPPFRationalParts();

        // Traditional rational addition: a/b + c/d = (ad + bc) / bd
        const sum_numerator = (a_rational.numerator * b_rational.denominator) +
            (b_rational.numerator * a_rational.denominator);
        const sum_denominator = a_rational.denominator * b_rational.denominator;

        return EGPTNumber.fromRational(sum_numerator, sum_denominator);
    }

    /**
     * 🌀 NORMAL SPACE SUBTRACTION: Traditional rational subtraction (a - b)
     * @param {EGPTNumber} a_en - First vector value
     * @param {EGPTNumber} b_en - Second vector value
     * @returns {EGPTNumber} - Difference a - b in normal space
     */
    static subtract(a_en, b_en) {
        const a_rational = a_en._getPPFRationalParts();
        const b_rational = b_en._getPPFRationalParts();

        // Traditional rational subtraction: a/b - c/d = (ad - bc) / bd
        const diff_numerator = (a_rational.numerator * b_rational.denominator) -
            (b_rational.numerator * a_rational.denominator);
        const diff_denominator = a_rational.denominator * b_rational.denominator;

        return EGPTNumber.fromRational(diff_numerator, diff_denominator);
    }

    /**
     * Checks equality between two vectors using exact rational comparison
     * @param {EGPTNumber} a_en - First vector
     * @param {EGPTNumber} b_en - Second vector
     * @returns {boolean} - True if vectors represent same value
     */
    static equals(a_en, b_en) {
        const a_rational = a_en._getPPFRationalParts();
        const b_rational = b_en._getPPFRationalParts();
        
        // Cross multiply to compare: a/b == c/d iff a*d == b*c
        return (a_rational.numerator * b_rational.denominator) ===
               (b_rational.numerator * a_rational.denominator);
    }

    /**
     * Compares two vectors: returns -1 if a < b, 0 if a == b, 1 if a > b
     * @param {EGPTNumber} a_en - First vector
     * @param {EGPTNumber} b_en - Second vector
     * @returns {number} - Comparison result
     */
    static compare(a_en, b_en) {
        const a_rational = a_en._getPPFRationalParts();
        const b_rational = b_en._getPPFRationalParts();
        
        // Cross multiply to compare: a/b vs c/d => compare a*d vs b*c
        const left = a_rational.numerator * b_rational.denominator;
        const right = b_rational.numerator * a_rational.denominator;
        
        if (left < right) return -1;
        if (left > right) return 1;
        return 0;
    }

    /**
     * Returns absolute value of a vector
     * @param {EGPTNumber} a_en - Input vector
     * @returns {EGPTNumber} - Absolute value
     */
    static abs(a_en) {
        const rational = a_en._getPPFRationalParts();
        if (rational.numerator < 0n) {
            return EGPTNumber.fromRational(-rational.numerator, rational.denominator);
        }
        return a_en.clone();
    }

    /**
     * 🎯 SHANNON SPACE SCALING: H(base^(exp_num/exp_den)) = (exp_num/exp_den) * H(base)
     * 
     * Implements exponentiation using Shannon entropy scaling via scaled vectors.
     * base^(a/b) in normal space = (a/b) * H(base) in Shannon space
     * 
     * The scaled vector representation automatically reduces to exact values when possible
     * (e.g., 16^(1/4) reduces to H(2), while 2^(1/2) remains as (1/2)*H(2) representing √2)
     * 
     * @param {EGPTNumber} base_en - Base value H(base)
     * @param {bigint} exp_num - Exponent numerator
     * @param {bigint} [exp_den=1n] - Exponent denominator
     * @returns {EGPTNumber} - Result representing H(base^(exp_num/exp_den))
     */
    static pow(base_en, exp_num, exp_den = 1n) {
        if (exp_den === 0n) {
            throw new Error("Exponent denominator cannot be zero");
        }

        SimpleLogger.log(`🎯 Shannon Space Scaling: H(base^(${exp_num}/${exp_den})) = (${exp_num}/${exp_den}) * H(base)`);
        SimpleLogger.log("   Implemented as scaled vector per ADDING_Vector_Scaling.md");

        // Handle special cases
        if (exp_num === 0n) {
            // base^0 = 1, so H(1) = 0
            return EGPTNumber.fromBigInt(1n);
        }

        if (exp_num === 1n && exp_den === 1n) {
            // base^1 = base, so H(base^1) = H(base)
            return base_en.clone();
        }

        // Create scaled vector: (exp_num/exp_den) * base_en
        // The EGPTNumber constructor will automatically reduce this if possible
        // e.g., (1/4)*H(16) -> H(2), or (1/2)*H(4) -> H(2)
        return EGPTNumber.fromScaledVector(base_en, exp_num, exp_den);
    }

    /**
     * 🎯 SQUARE ROOT: H(√n) = (1/2) * H(n)
     * 
     * Computes square root using Shannon entropy scaling via scaled vectors.
     * √n in normal space = H(n^(1/2)) = (1/2) * H(n) using scaled vector paradigm
     * 
     * @param {EGPTNumber} a_en - Input vector H(n)
     * @returns {EGPTNumber} - Scaled vector representing H(√n)
     */
    static sqrt(a_en) {
        return EGPTMath.pow(a_en, 1n, 2n);
    }

    /**
     * Helper to create EGPTNumber from BigInt (convenience method)
     * @param {bigint} value - BigInt value
     * @returns {EGPTNumber} - New EGPTNumber
     */
    static fromBigInt(value) {
        return EGPTNumber.fromBigInt(value);
    }

    /**
     * 🔧 BIT LENGTH: Returns the bit length in canonical information space
     *
     * For entropy uniformity analysis: divisions = getIntegerBitLength(H_k) - 1 = floor(log₂(k))
     * CRITICAL: Uses canonical EGPTNumber representation, not external string operations.
     *
     * @param {EGPTNumber} egpt_num - EGPTNumber to get bit length for (typically from fromBigInt)
     * @returns {BigInt} - The natural bit length in canonical space
     */
    static getIntegerBitLength(egpt_num) {
        const ppf = egpt_num.numerator_encodedAsLog2ppf;
        if (ppf.N < -1n) {
            // Negative number: N_abs = -N_neg - 2
            const N_abs = -ppf.N - 2n;
            return N_abs + 1n;
        }
        return ppf.N + 1n;
    }

    // =============================================================================
    // 🎯 PEDAGOGICAL ALIASES - Show Shannon perspective
    // =============================================================================

    /**
     * Pedagogical alias for multiply() - shows Shannon space perspective.
     * Normal space multiplication = Shannon space addition.
     * @param {EGPTNumber} p_en - First vector
     * @param {EGPTNumber} q_en - Second vector
     * @returns {EGPTNumber} - Product vector
     */
    static addInLogSpace(p_en, q_en) {
        return EGPTMath.multiply(p_en, q_en);
    }

    /**
     * Pedagogical alias for divide() - shows Shannon space perspective.
     * Normal space division = Shannon space subtraction.
     * @param {EGPTNumber} k_en - Dividend vector
     * @param {EGPTNumber} p_en - Divisor vector
     * @returns {EGPTNumber} - Quotient vector
     */
    static subtractInLogSpace(k_en, p_en) {
        return EGPTMath.divide(k_en, p_en);
    }

    /**
     * Pedagogical alias for add() - shows vector perspective.
     * @param {EGPTNumber} a_en - First vector
     * @param {EGPTNumber} b_en - Second vector
     * @returns {EGPTNumber} - Sum vector
     */
    static addVectors(a_en, b_en) {
        return EGPTMath.add(a_en, b_en);
    }

    // =============================================================================
    // Complex operations and transcendental functions have been moved to:
    // - EGPTComplex.js: ComplexEGPTNumber, TwiddleTable, complex algebra
    // - EGPTranscendental.js: exp, exp2, log2, cos, sin, phase operations
    // =============================================================================

    // =============================================================================
    // 🎯 SCALED VECTOR UTILITIES - Support for Irrational Numbers
    // =============================================================================

    /**
     * 🎯 CHECKS IF SCALED VECTOR REPRESENTS EXACT RATIONAL
     * 
     * Determines if a scaled vector can be exactly represented as a rational number.
     * For irrational roots like H(√2), this will return false.
     * 
     * @param {EGPTNumber} scaled_en - Scaled vector to check
     * @returns {boolean} - True if represents exact rational, false for irrational
     */
    static isExactRational(scaled_en) {
        const scalar_parts = scaled_en.getScalarParts();
        const base_parts = scaled_en.getBaseRationalParts();

        // If scalar is 1/1, it's always exact rational
        if (scalar_parts.numerator === 1n && scalar_parts.denominator === 1n) {
            return true;
        }

        // For fractional scalars, check if the base is a perfect power
        // This is a simplified check - full implementation would need more sophisticated analysis
        return false; // Conservative approach for now
    }

    /**
     * 🎯 CONVERTS SCALED VECTOR TO NORMAL SPACE (when possible)
     * 
     * Attempts to convert a scaled vector back to normal space rational.
     * Only works for exact representations.
     * 
     * @param {EGPTNumber} scaled_en - Scaled vector
     * @returns {EGPTNumber} - Normal space rational (throws if not exact)
     */
    static toNormalSpace(scaled_en) {
        if (!EGPTMath.isExactRational(scaled_en)) {
            throw new Error("Cannot convert irrational scaled vector to exact normal space rational");
        }

        const final_rational = scaled_en._getPPFRationalParts();
        return EGPTNumber.fromRational(final_rational.numerator, final_rational.denominator);
    }

    /**
     * 🎯 DEMONSTRATES IRRATIONAL ROOT REPRESENTATION
     * 
     * Creates example scaled vectors for common irrational roots per ADDING_Vector_Scaling.md
     * 
     * @returns {Object} - Examples of irrational representations
     */
    static demonstrateIrrationalRoots() {
        const examples = {};

        // H(√2) = (1/2) * H(2)
        const H_2 = EGPTNumber.fromBigInt(2n);
        examples.sqrt_2 = EGPTNumber.fromScaledVector(H_2, 1n, 2n);

        // H(∛8) = (1/3) * H(8)  
        const H_8 = EGPTNumber.fromBigInt(8n);
        examples.cuberoot_8 = EGPTNumber.fromScaledVector(H_8, 1n, 3n);

        // H(2^(3/2)) = (3/2) * H(2)
        examples.two_to_three_halves = EGPTNumber.fromScaledVector(H_2, 3n, 2n);

        return examples;
    }

    // =============================================================================
    // 🎯 COMPLEX VECTOR FUNCTIONS - Moved from EGPTNumber
    // =============================================================================

    /**
     * 🎯 VECTOR COURSE CORRECTION: Calculate trajectory deviation for waypoint navigation
     * 
     * PEDAGOGICAL PRINCIPLE: Factors require MAXIMUM course correction from smooth trajectory,
     * creating entropy SPIKES. Non-factors follow smooth trajectory with proportional entropy.
     * 
     * VECTOR NAVIGATION ANALOGY:
     * - Vector k = direct path to star at target coordinates  
     * - Integer waypoints = discrete grid points we can visit
     * - Smooth trajectory = expected path based on k/p ratio
     * - Course correction = deviation needed to hit integer waypoint
     * - Factors = waypoints requiring MAXIMUM course correction → ENTROPY SPIKES
     * 
     * MATHEMATICAL FOUNDATION (CORRECTED):
     * 1. Calculate smooth trajectory ratio: k/p (floating point)
     * 2. Find actual integer landing: floor(k/p) with remainder
     * 3. Exact factors (remainder=0) require MAXIMUM course correction → entropy spike
     * 4. Non-factors require proportional course correction → scaled entropy
     * 
     * @param {EGPTNumber} k_en - Target vector H(k) [star position]
     * @param {EGPTNumber} p_en - Waypoint vector H(p) [integer grid point]
     * @returns {EGPTNumber} - Course correction entropy (SPIKES at factors)
     */
    static conditionalEntropyVector(k_en, p_en) {
        SimpleLogger.log("🎯 Vector Course Correction: Ultra-high precision waypoint navigation");
        SimpleLogger.log(`   Target vector k: ${k_en.toMathString()}`);
        SimpleLogger.log(`   Waypoint p: ${p_en.toMathString()}`);

        // Step 1: Validate inputs using EGPTMath operations
        const H_zero = EGPTMath.fromBigInt(0n);

        if (EGPTMath.compare(p_en, H_zero) <= 0) {
            SimpleLogger.log("   ⚠️ Invalid waypoint - returning fallback entropy");
            return EGPTMath.fromBigInt(50n);
        }

        // Step 2: ULTRA-HIGH PRECISION trajectory analysis using EGPTMath
        // Calculate quotient H(k/p) using Shannon entropy division
        const H_quotient = EGPTMath.divide(k_en, p_en);

        SimpleLogger.log(`   📐 Shannon quotient H(k/p): ${H_quotient.toMathString()}`);

        // Step 3: Check if quotient is an exact integer (indicates exact factor)
        if (H_quotient.isInteger()) {
            SimpleLogger.log("   🎯 EXACT FACTOR: Perfect integer quotient in ultra-high precision!");
            SimpleLogger.log("   🚀 ENTROPY SPIKE: Maximum course correction detected");

            // Exact factors get the ACTUAL Shannon entropy magnitude
            // This preserves the true ultra-high precision relationship
            SimpleLogger.log(`   📊 Factor spike entropy (canonical): ${H_quotient.toMathString()}`);

            // Mark this as an exact factor for normalization awareness
            H_quotient.isExactFactor = true;
            return H_quotient;
        }

        // Step 4: Non-factors get ultra-high precision fractional analysis
        // Use the fractional part of the quotient as the course correction measure

        // Extract rational parts for ultra-high precision analysis
        const quotient_rational = H_quotient._getPPFRationalParts();

        SimpleLogger.log(`   📊 Quotient rational: ${quotient_rational.numerator}/${quotient_rational.denominator}`);

        // For non-integer quotients, the course correction is related to 
        // how "close" we are to the next integer (the remainder effect)
        // Calculate this as the fractional distance using ultra-high precision

        // Create integer part using EGPTMath operations
        const H_integer_part = EGPTMath.fromBigInt(quotient_rational.numerator / quotient_rational.denominator);

        // Calculate fractional part: H_quotient - H_integer_part  
        const H_fractional_part = EGPTMath.subtract(H_quotient, H_integer_part);

        // The course correction entropy is proportional to the fractional deviation
        // Use the fractional part directly as it preserves ultra-high precision differences
        SimpleLogger.log(`   📐 Course correction (fractional): ${H_fractional_part.toMathString()}`);
        SimpleLogger.log(`   📊 Trajectory entropy (ultra-high precision): ${H_fractional_part.toMathString()}`);

        return H_fractional_part;
    }
}

// Export the refactored EGPTMath class
export { EGPTMath };
