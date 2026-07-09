// ===============================================================
// EGPT COMPLEX - COMPLEX NUMBERS AND TWIDDLE OPERATIONS
// Extracted from EGPTNumber.js and EGPTMath.js to eliminate circular dependencies
//
// Author: E. Abadir
// Contains: ComplexEGPTNumber, TwiddleTable, and all complex operations
// =============================================================================

import { SimpleLogger } from './DebugLogger.js';
import { EGPTNumber } from './EGPTNumber.js';
import { EGPTMath } from './EGPTMath.js';
import { EGPTranscendental } from './EGPTranscendental.js';

SimpleLogger.log("🎯 EGPT COMPLEX: Complex numbers and FFT twiddles");

/**
 * 🎯 Represents a complex number a + bi, where 'a' and 'b' are EGPTNumber vectors.
 * This is a pure data container. All arithmetic is handled by EGPTComplex static methods.
 */
class ComplexEGPTNumber {
    /** @type {EGPTNumber} */
    real;
    /** @type {EGPTNumber} */
    imag;

    constructor(realPart, imagPart) {
        if (!(realPart instanceof EGPTNumber) || !(imagPart instanceof EGPTNumber)) {
            throw new Error("ComplexEGPTNumber components must be EGPTNumber instances.");
        }
        this.real = realPart;
        this.imag = imagPart;
    }

    /**
     * Creates a deep clone of this complex number.
     * @returns {ComplexEGPTNumber}
     */
    clone() {
        return new ComplexEGPTNumber(this.real.clone(), this.imag.clone());
    }

    /**
     * Provides a string representation for debugging.
     * @returns {string}
     */
    toString() {
        return `(${this.real.toMathString()}) + i(${this.imag.toMathString()})`;
    }

    /**
     * Checks for mathematical equality with another ComplexEGPTNumber.
     * @param {ComplexEGPTNumber} other
     * @returns {boolean}
     */
    equals(other) {
        return this.real.equals(other.real) && this.imag.equals(other.imag);
    }

    // =============================================================================
    // 🎯 SYNTACTIC SUGAR: Safe operations avoiding reduction issues
    // =============================================================================

    /**
     * Negates this complex number using fast scalar operations (RZF pattern).
     * Returns new negated complex number without triggering expensive reduction.
     * 
     * Pattern: z̄ = -z = (-real, -imag)
     * Implementation: Uses scalarMultiply(-1n) on cloned components
     * 
     * @returns {ComplexEGPTNumber} New negated complex number
     */
    negate() {
        return new ComplexEGPTNumber(
            this.real.clone().scalarMultiply(-1n),
            this.imag.clone().scalarMultiply(-1n)
        );
    }

    /**
     * Returns the complex conjugate (negate imaginary part only).
     * 
     * Pattern: z* = (real, -imag)
     * Used for: IFFT twiddles, complex division, magnitude computation
     * 
     * Uses EGPTNumber.negate() to ensure proper negative representation
     * (avoids negative-scaled vectors that break EGPTMath.multiply).
     * 
     * @returns {ComplexEGPTNumber} Complex conjugate
     */
    conjugate() {
        return new ComplexEGPTNumber(
            this.real.clone(),
            EGPTNumber.negate(this.imag)
        );
    }

    /**
     * Scales this complex number by a real scalar (integer or rational).
     * 
     * Pattern: k * z = (k * real, k * imag)
     * Implementation: Uses scalarMultiply for efficiency
     * 
     * @param {BigInt} scalar - Integer scalar to multiply by
     * @returns {ComplexEGPTNumber} New scaled complex number
     */
    scaleBy(scalar) {
        if (typeof scalar !== 'bigint') {
            throw new Error('scaleBy requires BigInt scalar');
        }
        return new ComplexEGPTNumber(
            this.real.clone().scalarMultiply(scalar),
            this.imag.clone().scalarMultiply(scalar)
        );
    }

    /**
     * Scales this complex number by a rational (a/b).
     * 
     * Pattern: (a/b) * z = (a/b * real, a/b * imag)
     * 
     * @param {BigInt} numerator - Numerator of scalar
     * @param {BigInt} denominator - Denominator of scalar
     * @returns {ComplexEGPTNumber} New scaled complex number
     */
    scaleByRational(numerator, denominator) {
        if (typeof numerator !== 'bigint' || typeof denominator !== 'bigint') {
            throw new Error('scaleByRational requires BigInt numerator and denominator');
        }
        
        // Use helper to scale each component properly
        const scaled_real = EGPTNumber._scaleRationalByRational(this.real, numerator, denominator);
        const scaled_imag = EGPTNumber._scaleRationalByRational(this.imag, numerator, denominator);
        
        return new ComplexEGPTNumber(scaled_real, scaled_imag);
    }

    /**
     * Checks if this is purely real (imaginary part is zero).
     * @returns {boolean}
     */
    isReal() {
        const H_ZERO = EGPTNumber.fromBigInt(0n);
        return this.imag.equals(H_ZERO);
    }

    /**
     * Checks if this is purely imaginary (real part is zero).
     * @returns {boolean}
     */
    isImaginary() {
        const H_ZERO = EGPTNumber.fromBigInt(0n);
        return this.real.equals(H_ZERO);
    }

    /**
     * TOPOLOGY-NATIVE: Calculates the L1 magnitude (|x| + |y|) of this complex number.
     * This is the correct magnitude for our n-gon (square) topology.
     * @returns {EGPTNumber} The L1 magnitude of the complex number.
     */
    getMagnitude() {
        const abs_real = EGPTMath.abs(this.real);
        const abs_imag = EGPTMath.abs(this.imag);
        return EGPTMath.add(abs_real, abs_imag);
    }

    /**
     * TOPOLOGY-NATIVE: Calculates the phase [0, 1) of this complex number.
     * This is the inverse of the _phaseToCartesian mapping. It is essential
     * for performing multiplication topologically via phase addition.
     * @returns {EGPTNumber} The phase of the complex number as a fraction in [0, 1).
     */
    getPhase() {
        const H_ZERO = EGPTNumber.fromBigInt(0n);
        const H_ONE = EGPTNumber.fromBigInt(1n);
        const H_NEG_ONE = EGPTNumber.fromBigInt(-1n);
        const H_quarter = EGPTNumber.fromRational(1n, 4n);
        const H_half = EGPTNumber.fromRational(1n, 2n);
        const H_three_quarter = EGPTNumber.fromRational(3n, 4n);

        const x = this.real;
        const y = this.imag;

        // Handle cardinal points first
        if (y.equals(H_ZERO)) {
            if (x.equals(H_ONE)) return H_ZERO;       // (1, 0) -> phase 0
            if (x.equals(H_NEG_ONE)) return H_half; // (-1, 0) -> phase 1/2
        }
        if (x.equals(H_ZERO)) {
            if (y.equals(H_ONE)) return H_quarter;       // (0, 1) -> phase 1/4
            if (y.equals(H_NEG_ONE)) return H_three_quarter; // (0, -1) -> phase 3/4
        }
        
        // Determine quadrant and reverse the linear interpolation
        const is_x_pos = EGPTMath.compare(x, H_ZERO) > 0;
        const is_y_pos = EGPTMath.compare(y, H_ZERO) > 0;

        if (is_x_pos && is_y_pos) {
            // Quadrant 0: y = progress, x = 1 - progress => progress = y
            // phase = progress * H_quarter
            return EGPTMath.normalMultiply(y, H_quarter);
        } else if (!is_x_pos && is_y_pos) {
            // Quadrant 1: x = -progress, y = 1 - progress => progress = -x
            // phase = H_quarter + (progress * H_quarter)
            const progress = EGPTNumber.negate(x);
            const phase_in_quad = EGPTMath.normalMultiply(progress, H_quarter);
            return EGPTMath.add(H_quarter, phase_in_quad);
        } else if (!is_x_pos && !is_y_pos) {
            // Quadrant 2: y = -progress, x = progress - 1 => progress = -y
            // phase = H_half + (progress * H_quarter)
            const progress = EGPTNumber.negate(y);
            const phase_in_quad = EGPTMath.normalMultiply(progress, H_quarter);
            return EGPTMath.add(H_half, phase_in_quad);
        } else { // is_x_pos && !is_y_pos
            // Quadrant 3: x = progress, y = progress - 1 => progress = x
            // phase = H_three_quarter + (progress * H_quarter)
            const progress = x;
            const phase_in_quad = EGPTMath.normalMultiply(progress, H_quarter);
            return EGPTMath.add(H_three_quarter, phase_in_quad);
        }
    }

    // =============================================================================
    // 🎯 COMPLEX ARITHMETIC: Core operations (immutable - returns new instance)
    // =============================================================================

    /**
     * Adds another complex number to this one (immutable).
     * Returns new ComplexEGPTNumber representing this + other.
     * 
     * Pattern: (a+bi) + (c+di) = (a+c) + (b+d)i
     * 
     * @param {ComplexEGPTNumber} other - Complex number to add
     * @returns {ComplexEGPTNumber} New complex number (this + other)
     */
    add(other) {
        return new ComplexEGPTNumber(
            EGPTMath.add(this.real, other.real),
            EGPTMath.add(this.imag, other.imag)
        );
    }

    /**
     * Subtracts another complex number from this one (immutable).
     * Returns new ComplexEGPTNumber representing this - other.
     * 
     * Pattern: (a+bi) - (c+di) = (a-c) + (b-d)i
     * 
     * @param {ComplexEGPTNumber} other - Complex number to subtract
     * @returns {ComplexEGPTNumber} New complex number (this - other)
     */
    subtract(other) {
        return new ComplexEGPTNumber(
            EGPTMath.subtract(this.real, other.real),
            EGPTMath.subtract(this.imag, other.imag)
        );
    }

    /**
     * Multiplies this complex number by another (immutable).
     * Returns new ComplexEGPTNumber representing this × other.
     * 
     * Pattern: (a+bi)(c+di) = (ac-bd) + (ad+bc)i
     * 
     * @param {ComplexEGPTNumber} other - Complex number to multiply
     * @returns {ComplexEGPTNumber} New complex number (this × other)
     */
    multiply(other) {
        return EGPTComplex.complexMultiply(this, other);
    }

    /**
     * Computes magnitude squared: |z|² = real² + imag²
     * 
     * WARNING: May trigger reduction if components are scaled vectors.
     * Use with caution on twiddles with irrational components.
     * 
     * @returns {EGPTNumber} Magnitude squared
     */
    getMagnitudeSquared() {
        const real_sq = EGPTMath.multiply(this.real, this.real);
        const imag_sq = EGPTMath.multiply(this.imag, this.imag);
        return EGPTMath.add(real_sq, imag_sq);
    }

    // =============================================================================
    // 🎯 MUTABLE OPERATIONS: Modify this instance (for performance)
    // =============================================================================

    /**
     * Adds another complex number to this one IN PLACE (mutable).
     * Modifies this instance and returns it for chaining.
     * 
     * Pattern: this = this + other
     * 
     * @param {ComplexEGPTNumber} other - Complex number to add
     * @returns {ComplexEGPTNumber} This instance (modified)
     */
    addInPlace(other) {
        this.real = EGPTMath.add(this.real, other.real);
        this.imag = EGPTMath.add(this.imag, other.imag);
        return this;
    }

    /**
     * Subtracts another complex number from this one IN PLACE (mutable).
     * Modifies this instance and returns it for chaining.
     * 
     * Pattern: this = this - other
     * 
     * @param {ComplexEGPTNumber} other - Complex number to subtract
     * @returns {ComplexEGPTNumber} This instance (modified)
     */
    subtractInPlace(other) {
        this.real = EGPTMath.subtract(this.real, other.real);
        this.imag = EGPTMath.subtract(this.imag, other.imag);
        return this;
    }

    /**
     * Negates this complex number IN PLACE (mutable).
     * Modifies this instance and returns it for chaining.
     * 
     * Uses fast scalarMultiply(-1n) to avoid reduction.
     * 
     * @returns {ComplexEGPTNumber} This instance (modified)
     */
    negateInPlace() {
        this.real.scalarMultiply(-1n);
        this.imag.scalarMultiply(-1n);
        return this;
    }

    /**
     * Conjugates this complex number IN PLACE (mutable).
     * Modifies this instance and returns it for chaining.
     * 
     * Pattern: this = (real, -imag)
     * 
     * @returns {ComplexEGPTNumber} This instance (modified)
     */
    conjugateInPlace() {
        this.imag.scalarMultiply(-1n);
        return this;
    }
}

// =============================================================================
// TWIDDLE TABLE: PHASE-BASED FFT OPERATIONS
// =============================================================================

/**
 * TWIDDLE TABLE FOR FFT/IFFT OPERATIONS
 * 
 * Generates and stores k twiddle factors with PHASE-BASED operations.
 * 
 * KEY INNOVATION: Twiddle multiplication uses phase arithmetic, not coordinate multiplication!
 *   ω^a × ω^b = ω^(a+b mod k)  [phase addition, not (x,y) multiplication]
 * 
 * This preserves the FFT group structure (ω^k = ω₀) which coordinate multiplication breaks.
 * 
 * @version 1.0.0
 * @date October 2025
 */
class TwiddleTable {
    /**
     * Create a twiddle table for k-point FFT/IFFT.
     * 
     * @param {number} k - Number of twiddles (FFT size, must be positive)
     * @param {string} topology - 'square' (default) or 'circular'
     */
    constructor(k, topology = 'square') {
        if (k <= 0 || !Number.isInteger(k)) {
            throw new Error('TwiddleTable: k must be a positive integer');
        }
        
        this.k = k;
        this.topology = topology;
        this.twiddles = new Map(); // phase_index → ComplexEGPTNumber
        this.phases = new Map();   // phase_index → phase EGPTNumber
        
        // Generate all k twiddles with exact canonical coordinates
        for (let j = 0; j < k; j++) {
            const phase = EGPTNumber.fromRational(BigInt(j), BigInt(k));
            let coords;
            if (this.topology === 'circular') {
                // For FFT compatibility, use circular mapping and NEGATIVE phase for forward transform
                const neg_phase = EGPTNumber.fromRational(BigInt(-j), BigInt(k));
                coords = EGPTranscendental._phaseToCircularCartesian(neg_phase);
            } else {
                coords = EGPTranscendental._phaseToCartesian(phase);
            }
            const twiddle = new ComplexEGPTNumber(coords.x, coords.y);
            
            this.twiddles.set(j, twiddle);
            this.phases.set(j, phase);
        }
    }
    
    /**
     * Get twiddle at phase index j.
     * 
     * Returns ω_k^j = exp(-2πij/k) in canonical PPF coordinates.
     * Handles negative indices via wraparound.
     * 
     * @param {number} j - Phase index (can be negative, will wrap)
     * @returns {ComplexEGPTNumber} Twiddle at phase j/k
     */
    getTwiddle(j) {
        const normalized_j = ((j % this.k) + this.k) % this.k;
        return this.twiddles.get(normalized_j);
    }
    
    /**
     * Get phase EGPTNumber at index j.
     * 
     * @param {number} j - Phase index
     * @returns {EGPTNumber} Phase fraction j/k
     */
    getPhase(j) {
        const normalized_j = ((j % this.k) + this.k) % this.k;
        return this.phases.get(normalized_j);
    }
    
    /**
     * Multiply twiddles via phase addition.
     * 
     * PHASE ARITHMETIC (not coordinate multiplication):
     *   ω^a × ω^b = ω^(a+b mod k)
     * 
     * This preserves FFT group structure by construction.
     * 
     * @param {number} j_a - First phase index
     * @param {number} j_b - Second phase index
     * @returns {Object} {index: number, twiddle: ComplexEGPTNumber}
     */
    multiplyByPhase(j_a, j_b) {
        const j_result = (j_a + j_b) % this.k;
        return {
            index: j_result,
            twiddle: this.getTwiddle(j_result)
        };
    }
    
    /**
     * Raise twiddle to power via phase multiplication.
     * 
     * PHASE ARITHMETIC:
     *   (ω^j)^n = ω^(j×n mod k)
     * 
     * @param {number} j - Phase index
     * @param {number} n - Exponent
     * @returns {Object} {index: number, twiddle: ComplexEGPTNumber}
     */
    powerByPhase(j, n) {
        const j_result = (j * n) % this.k;
        return {
            index: j_result,
            twiddle: this.getTwiddle(j_result)
        };
    }
    
    /**
     * Conjugate twiddle via phase negation.
     * 
     * PHASE ARITHMETIC:
     *   ω^j* = ω^(k-j mod k)
     * 
     * @param {number} j - Phase index
     * @returns {Object} {index: number, twiddle: ComplexEGPTNumber}
     */
    conjugateByPhase(j) {
        const j_result = (this.k - j) % this.k;
        return {
            index: j_result,
            twiddle: this.getTwiddle(j_result)
        };
    }
    
    /**
     * Find phase index from a ComplexEGPTNumber twiddle (inverse lookup).
     * 
     * @param {ComplexEGPTNumber} omega - Twiddle to find
     * @returns {number} Phase index j, or -1 if not found
     */
    getPhaseIndex(omega) {
        for (let j = 0; j < this.k; j++) {
            const twiddle = this.getTwiddle(j);
            if (omega.equals(twiddle)) {
                return j;
            }
        }
        return -1;
    }
}

// =============================================================================
// COMPLEX OPERATIONS - STATIC METHODS
// =============================================================================

/**
 * Static class for complex number operations
 */
class EGPTComplex {
    // Prevent instantiation
    constructor() {
        throw new Error("EGPTComplex is a static class and cannot be instantiated.");
    }

    // Cache for TwiddleTable instances to avoid recreation overhead
    static _twiddleTableCache = new Map();

    /**
     * Geometric exponential function wrapper that returns ComplexEGPTNumber.
     * Delegates to EGPTranscendental.exp() and wraps result in ComplexEGPTNumber.
     * @param {ComplexEGPTNumber} z - Complex exponent
     * @returns {ComplexEGPTNumber} Result as complex number
     */
    static exp(z) {
        const coords = EGPTranscendental.exp(z);
        return new ComplexEGPTNumber(coords.x, coords.y);
    }

    /**
     * Adds two complex numbers: (a+bi) + (c+di) = (a+c) + i(b+d).
     * @param {ComplexEGPTNumber} z1
     * @param {ComplexEGPTNumber} z2
     * @returns {ComplexEGPTNumber}
     */
    static complexAdd(z1, z2) {
        const new_real = EGPTMath.add(z1.real, z2.real);
        const new_imag = EGPTMath.add(z1.imag, z2.imag);
        return new ComplexEGPTNumber(new_real, new_imag);
    }

    /**
     * Checks if a complex number is on the unit circle (L1 norm magnitude = 1).
     * 
     * @param {ComplexEGPTNumber} z - Complex number to check
     * @returns {boolean} True if |z| (L1 norm) equals 1
     * @private
     */
    static _isUnitCircle(z) {
        const magnitude = z.getMagnitude();
        const H_ONE = EGPTNumber.fromBigInt(1n);
        return EGPTMath.equals(magnitude, H_ONE);
    }

    /**
     * Extracts the denominator from a phase fraction.
     * 
     * @param {EGPTNumber} phase - Phase as EGPTNumber fraction
     * @returns {bigint | null} Denominator if phase is exact rational j/k, null otherwise
     * @private
     */
    static _extractPhaseDenominator(phase) {
        try {
            const rational = phase._getPPFRationalParts();
            if (rational.denominator === 0n) return null;
            return rational.denominator;
        } catch (error) {
            return null;
        }
    }

    /**
     * Computes Greatest Common Divisor using Euclidean algorithm.
     * 
     * @param {bigint} a - First number
     * @param {bigint} b - Second number
     * @returns {bigint} GCD of a and b
     * @private
     */
    static _gcd(a, b) {
        a = a < 0n ? -a : a;
        b = b < 0n ? -b : b;
        while (b !== 0n) {
            [a, b] = [b, a % b];
        }
        return a;
    }

    /**
     * Computes Least Common Multiple: LCM(a, b) = (a * b) / GCD(a, b)
     * 
     * @param {bigint} a - First number
     * @param {bigint} b - Second number
     * @returns {bigint} LCM of a and b
     * @private
     */
    static _findLCM(a, b) {
        if (a === 0n || b === 0n) return 0n;
        const gcd = this._gcd(a, b);
        return (a * b) / gcd;
    }

    /**
     * Converts a phase fraction to a twiddle index j for a given k.
     * 
     * @param {EGPTNumber} phase - Phase as EGPTNumber fraction
     * @param {bigint} k - Denominator (TwiddleTable size)
     * @returns {number | null} Twiddle index j if phase = j/k exactly, null otherwise
     * @private
     */
    static _phaseToTwiddleIndex(phase, k) {
        try {
            const rational = phase._getPPFRationalParts();
            if (rational.denominator === 0n) return null;
            
            // Check if phase can be represented as j/k: (rational.numerator * k) must be divisible by rational.denominator
            const numerator_times_k = rational.numerator * k;
            if (numerator_times_k % rational.denominator !== 0n) return null;
            
            const j = Number(numerator_times_k / rational.denominator);
            // Normalize j to [0, k) range
            return ((j % Number(k)) + Number(k)) % Number(k);
        } catch (error) {
            return null;
        }
    }

    /**
     * Gets or creates a TwiddleTable instance for the given k, using cache.
     * 
     * @param {number} k - TwiddleTable size
     * @returns {TwiddleTable} Cached or newly created TwiddleTable
     * @private
     */
    static _getOrCreateTwiddleTable(k) {
        if (!this._twiddleTableCache.has(k)) {
            this._twiddleTableCache.set(k, new TwiddleTable(k));
        }
        return this._twiddleTableCache.get(k);
    }

    /**
     * Helper for coordinate-wise multiplication in complex arithmetic.
     * Handles both pure rationals and scaled vectors correctly.
     * 
     * @param {EGPTNumber} a_en - First coordinate
     * @param {EGPTNumber} b_en - Second coordinate
     * @returns {EGPTNumber} Product a × b
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
     * Multiplies two complex numbers with automatic topology detection.
     * 
     * For unit circle numbers (L1 magnitude = 1), uses phase-based multiplication
     * via TwiddleTable, which preserves the square topology's L1 norm.
     * 
     * For non-unit circle numbers, uses standard Euclidean multiplication:
     * (a+bi)(c+di) = (ac-bd) + i(ad+bc)
     * 
     * @param {ComplexEGPTNumber} z1 - First complex number
     * @param {ComplexEGPTNumber} z2 - Second complex number
     * @returns {ComplexEGPTNumber} Product z1 × z2
     */
    static complexMultiply(z1, z2) {
        // Check if both numbers are on unit circle
        const z1_is_unit = this._isUnitCircle(z1);
        const z2_is_unit = this._isUnitCircle(z2);
        
        if (z1_is_unit && z2_is_unit) {
            // Try phase-based multiplication for unit circle numbers
            try {
                const phase1 = z1.getPhase();
                const phase2 = z2.getPhase();
                
                const denom1 = this._extractPhaseDenominator(phase1);
                const denom2 = this._extractPhaseDenominator(phase2);
                
                if (denom1 !== null && denom2 !== null) {
                    // Find common k using LCM
                    const k_bigint = this._findLCM(denom1, denom2);
                    
                    // Limit k to reasonable size (e.g., 65536) to avoid excessive memory
                    if (k_bigint <= 65536n && k_bigint > 0n) {
                        const k = Number(k_bigint);
                        
                        // Convert phases to twiddle indices
                        const j1 = this._phaseToTwiddleIndex(phase1, k_bigint);
                        const j2 = this._phaseToTwiddleIndex(phase2, k_bigint);
                        
                        if (j1 !== null && j2 !== null) {
                            // Use phase-based multiplication (topologically correct)
                            const table = this._getOrCreateTwiddleTable(k);
                            const result = table.multiplyByPhase(j1, j2);
                            return result.twiddle;
                        }
                    }
                }
            } catch (error) {
                // Fall back to Euclidean if phase operations fail
            }
        }
        
        // Fall back to Euclidean multiplication for non-unit circle numbers
        // or if phase-based multiplication is not possible
        const ac = EGPTComplex._coordinateMultiply(z1.real, z2.real);
        const bd = EGPTComplex._coordinateMultiply(z1.imag, z2.imag);
        const ad = EGPTComplex._coordinateMultiply(z1.real, z2.imag);
        const bc = EGPTComplex._coordinateMultiply(z1.imag, z2.real);
        
        const new_real = EGPTMath.subtract(ac, bd);
        const new_imag = EGPTMath.add(ad, bc);
        return new ComplexEGPTNumber(new_real, new_imag);
    }

  

    /**
     * [HELPER] Calculates the Euclidean magnitude of a complex number.
     * @param {ComplexEGPTNumber} z The complex number.
     * @returns {EGPTNumber} The magnitude `sqrt(real² + imag²)`.
     */
    static complexMagnitude(z) {
        const real_sq = EGPTMath.multiply(z.real, z.real);
        const imag_sq = EGPTMath.multiply(z.imag, z.imag);
        const sum_sq = EGPTMath.add(real_sq, imag_sq);
        return EGPTMath.sqrt(sum_sq);
    }

    /**
     * [HELPER] Normalizes a complex number to a unit vector.
     * @param {ComplexEGPTNumber} z The complex number to normalize.
     * @param {EGPTNumber} [magnitude] Optional pre-calculated magnitude.
     * @returns {ComplexEGPTNumber} The normalized unit vector z/|z|.
     */
    static complexNormalize(z, magnitude = null) {
        const mag = magnitude || EGPTComplex.complexMagnitude(z);
        const H_ZERO = EGPTNumber.fromBigInt(0n);
        if (mag.equals(H_ZERO)) return new ComplexEGPTNumber(H_ZERO, H_ZERO);
        
        // Use normalDivide as this is a division of the final values.
        const new_real = EGPTMath.normalDivide(z.real, mag);
        const new_imag = EGPTMath.normalDivide(z.imag, mag);
        return new ComplexEGPTNumber(new_real, new_imag);
    }

    /**
     * [HELPER] Scales a complex number by a real EGPTNumber magnitude.
     * @param {ComplexEGPTNumber} z The complex number to scale.
     * @param {EGPTNumber} s The scalar magnitude.
     * @returns {ComplexEGPTNumber} The scaled complex number s*z.
     */
    static complexScale(z, s) {
        // Use Shannon multiply as we are scaling the components.
        const new_real = EGPTMath.multiply(z.real, s);
        const new_imag = EGPTMath.multiply(z.imag, s);
        return new ComplexEGPTNumber(new_real, new_imag);
    }

    /**
     * Calculates n^s for a real base n and complex exponent s = a+bi.
     * CORRECTED: Uses _getPPFRationalParts() for exact, canonical exponent values.
     *
     * @param {EGPTNumber} H_n - The real base number.
     * @param {ComplexEGPTNumber} s - The complex exponent.
     * @returns {ComplexEGPTNumber} The result of n^s.
     */
    static complexPower(H_n, s) {
        // --- CORRECTED LOGIC for Magnitude ---
        // 1. Get the rational parts of the real component 'a' of the exponent.
        const exponent_real_parts = s.real._getPPFRationalParts();

        // 2. Calculate the magnitude: M = n^a
        let H_magnitude;
        if (exponent_real_parts.numerator < 0n) {
            const positive_numerator = -exponent_real_parts.numerator;
            const H_positive_power = EGPTMath.pow(H_n, positive_numerator, exponent_real_parts.denominator);
            
            const H_one = EGPTNumber.fromBigInt(1n);
            H_magnitude = EGPTMath.divide(H_one, H_positive_power);
        } else {
            H_magnitude = EGPTMath.pow(H_n, exponent_real_parts.numerator, exponent_real_parts.denominator);
        }

        // 3. Calculate the Phase Index Vector: H_phase = b * log₂(n)
        const H_phase = EGPTMath.multiply(s.imag, H_n);

        // 4. Get the canonical wave vector from the Phase Index Vector.
        const phase_coords = EGPTranscendental._getVectorFromPhase(H_n, H_phase);

        // 5. Scale the phase vector by the magnitude: M * [x, y]
        const H_magnitude_complex = new ComplexEGPTNumber(H_magnitude, EGPTNumber.fromBigInt(0n));
        return EGPTComplex.complexMultiply(H_magnitude_complex, new ComplexEGPTNumber(phase_coords.x, phase_coords.y));
    }

    /**
     * Computes the Riemann Zeta Function ζ(s) for a complex argument s.
     *
     * @param {ComplexEGPTNumber} s - The complex argument.
     * @param {number} maxTerms - The number of terms to sum.
     * @returns {ComplexEGPTNumber} The value of ζ(s).
     */
    static riemannZeta(s, maxTerms = 1000) {
        SimpleLogger.log(`🎯 Computing ζ(s) for s = ${s.toString()} with ${maxTerms} terms.`);

        const H_zero = EGPTNumber.fromBigInt(0n);
        let sum_real = EGPTNumber.fromBigInt(0n);
        let sum_imag = EGPTNumber.fromBigInt(0n);

        // We are calculating n^(-s). Create the negated exponent once.
        const s_neg = new ComplexEGPTNumber(
            s.real.clone().scalarMultiply(-1n),
            s.imag.clone().scalarMultiply(-1n)
        );

        for (let i = 1; i <= maxTerms; i++) {
            const n = BigInt(i);
            const H_n = EGPTNumber.fromBigInt(n);

            const H_term = EGPTComplex.complexPower(H_n, s_neg);

            sum_real = EGPTMath.add(sum_real, H_term.real);
            sum_imag = EGPTMath.add(sum_imag, H_term.imag);
        }
        
        const final_sum = new ComplexEGPTNumber(sum_real, sum_imag);
        SimpleLogger.log(`   Final ζ(s) ≈ ${final_sum.toString()}`);
        return final_sum;
    }

    /**
     * Rotates a ComplexEGPTNumber by a given phase index from a TwiddleTable.
     * 
     * @param {ComplexEGPTNumber} z - The complex number to rotate.
     * @param {number} phaseIndex - The integer phase index (e.g., k in ω^k).
     * @param {TwiddleTable} table - The twiddle table for the current FFT size.
     * @returns {ComplexEGPTNumber} The rotated complex number.
     */
    static rotateByPhase(z, phaseIndex, table) {
        const z_phase_val = z.getPhase();
        const z_phase_index = EGPTComplex._phaseToTwiddleIndex(z_phase_val, BigInt(table.k));

        if (z_phase_index === null) {
            // Fallback to euclidean if phase is not a rational of the table size
            const omega = table.getTwiddle(phaseIndex);
            return z.multiply(omega);
        }

        const new_phase_index = (z_phase_index + phaseIndex);
        const rotated_unit_vector = table.getTwiddle(new_phase_index);

        // Re-apply original magnitude
        const magnitude = z.getMagnitude();
        return rotated_unit_vector.scaleBy(magnitude.toBigInt());
    }

    /**
     * Adds two complex numbers in the L1 (square) topology.
     * 
     * @param {ComplexEGPTNumber} z1
     * @param {ComplexEGPTNumber} z2
     * @returns {ComplexEGPTNumber}
     */
    static addInSquareTopology(z1, z2) {
        const new_real = EGPTMath.add(z1.real, z2.real);
        const new_imag = EGPTMath.add(z1.imag, z2.imag);
        return new ComplexEGPTNumber(new_real, new_imag);
    }
}

// Export the classes
export { ComplexEGPTNumber, TwiddleTable, EGPTComplex };

SimpleLogger.log("🎯 EGPTComplex loaded: Complex numbers and FFT twiddles available");

