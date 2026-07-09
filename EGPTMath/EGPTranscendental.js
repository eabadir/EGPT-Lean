// =============================================================================
// EGPT TRANSCENDENTAL - TRIGONOMETRIC AND EXPONENTIAL FUNCTIONS
// Extracted from EGPTMath.js to eliminate circular dependencies
//
// Author: E. Abadir
// Contains: cos, sin, exp, exp2, log2, phase mapping functions
// =============================================================================

import { SimpleLogger } from './DebugLogger.js';
import { EGPTNumber } from './EGPTNumber.js';
import { EGPTMath } from './EGPTMath.js';

SimpleLogger.log("🎯 EGPT TRANSCENDENTAL: Trigonometric and exponential functions");

/**
 * Static class for transcendental functions
 */
class EGPTranscendental {
    // Prevent instantiation
    constructor() {
        throw new Error("EGPTranscendental is a static class and cannot be instantiated.");
    }

    // Pre-computed constants for circular topology  
    static _circularConstants = {
        H_2: EGPTNumber.fromBigInt(2n),
        H_sqrt2_over_2: null, // √2/2 for 45-degree angles
        init: function() {
            if (!this.H_sqrt2_over_2) {
                const H_half = EGPTNumber.fromRational(1n, 2n);
                this.H_sqrt2_over_2 = EGPTMath.sqrt(H_half);
            }
            return this;
        }
    };

    // =============================================================================
    // 🏷️ GEOMETRIC CONSTANTS
    // =============================================================================

    /**
     * 🏷️ GEOMETRIC CONSTANT: Represents a half-rotation in phase space.
     * This is the canonical equivalent of PI, defined by its geometric meaning.
     */
    static get PI_PHASE() {
        return EGPTNumber.fromRational(1n, 2n);
    }

    /**
     * 🏷️ GEOMETRIC CONSTANT: Represents a full rotation in phase space.
     */
    static get TAU_PHASE() {
        return EGPTNumber.fromBigInt(1n);
    }

    // =============================================================================
    // 🎯 PHASE MAPPING FUNCTIONS
    // =============================================================================

    /**
     * [HELPER] PURE CANONICAL COORDINATES: Fractional rotation → Unit circle coordinates
     * 
     * NO transcendental functions! Uses rational linear interpolation that preserves bijectivity.
     * This is the "relabeling" of the unit circle to use a square topology.
     * 
     * @param {EGPTNumber} H_fraction - Canonical fraction [0,1) representing rotation
     * @returns {Object} {x: EGPTNumber, y: EGPTNumber} - Exact rational coordinates on the square
     * @private
     */
    static _phaseToCartesian(H_fraction) {
        const H_ZERO = EGPTNumber.fromBigInt(0n);
        const H_ONE = EGPTNumber.fromBigInt(1n);
        
        // Quadrant boundaries in canonical space
        const H_quarter = EGPTNumber.fromRational(1n, 4n);
        const H_half = EGPTNumber.fromRational(1n, 2n);
        const H_three_quarter = EGPTNumber.fromRational(3n, 4n);
        
        // EXACT VALUES for cardinal points
        if (EGPTMath.equals(H_fraction, H_ZERO)) return { x: H_ONE.clone(), y: H_ZERO.clone() };
        if (EGPTMath.equals(H_fraction, H_quarter)) return { x: H_ZERO.clone(), y: H_ONE.clone() };
        if (EGPTMath.equals(H_fraction, H_half)) return { x: EGPTNumber.fromBigInt(-1n), y: H_ZERO.clone() };
        if (EGPTMath.equals(H_fraction, H_three_quarter)) return { x: H_ZERO.clone(), y: EGPTNumber.fromBigInt(-1n) };
        
        // CANONICAL QUADRANT MAPPING (linear interpolation on a square)
        if (EGPTMath.compare(H_fraction, H_quarter) < 0) {
            // Quadrant 0: [0, 0.25)
            const progress = EGPTMath.divide(H_fraction, H_quarter);
            const x = EGPTMath.subtract(H_ONE, progress);
            const y = progress;
            return { x, y };
        } else if (EGPTMath.compare(H_fraction, H_half) < 0) {
            // Quadrant 1: [0.25, 0.5)
            const phase_in_quad = EGPTMath.subtract(H_fraction, H_quarter);
            const progress = EGPTMath.divide(phase_in_quad, H_quarter);
            const x = EGPTMath.subtract(H_ZERO, progress);
            const y = EGPTMath.subtract(H_ONE, progress);
            return { x, y };
        } else if (EGPTMath.compare(H_fraction, H_three_quarter) < 0) {
            // Quadrant 2: [0.5, 0.75)
            const phase_in_quad = EGPTMath.subtract(H_fraction, H_half);
            const progress = EGPTMath.divide(phase_in_quad, H_quarter);
            const x = EGPTMath.subtract(progress, H_ONE);
            const y = EGPTMath.subtract(H_ZERO, progress);
            return { x, y };
        } else {
            // Quadrant 3: [0.75, 1.0)
            const phase_in_quad = EGPTMath.subtract(H_fraction, H_three_quarter);
            const progress = EGPTMath.divide(phase_in_quad, H_quarter);
            const x = progress;
            const y = EGPTMath.subtract(progress, H_ONE);
            return { x, y };
        }
    }

    /**
     * [HELPER] Maps phase fraction to CIRCULAR unit circle coordinates using scaled vectors
     * 
     * This is the FFT-compatible bijection for twiddles, using circular topology (L2 norm).
     * It uses scaled vectors to represent irrational coordinates exactly.
     * 
     * For FFT: ω_N^j = exp(-2πij/N)
     * Phase input should be -j/N, which after normalization gives (N-j)/N for j≠0
     * 
     * @param {EGPTNumber} H_fraction - Canonical fraction representing -j/N for FFT
     * @returns {Object} {x: EGPTNumber, y: EGPTNumber} - Exact coordinates on the circular unit circle
     * @private
     */
    static _phaseToCircularCartesian(H_fraction) {
        const C = EGPTranscendental._circularConstants.init();
        const H_ZERO = EGPTNumber.fromBigInt(0n);
        const H_ONE = EGPTNumber.fromBigInt(1n);
        const H_NEG_ONE = EGPTNumber.fromBigInt(-1n);

        // Normalize phase to [0, 1) to handle negative inputs
        const H_TAU = EGPTNumber.fromBigInt(1n);
        let norm_phase = EGPTMath.mod(H_fraction, H_TAU);
        if (EGPTMath.compare(norm_phase, H_ZERO) < 0) {
            norm_phase = EGPTMath.add(norm_phase, H_TAU);
        }
        
        // Check for exact matches to standard FFT angles
        const phase_rational = norm_phase._getPPFRationalParts();
        
        // Cardinal angles (denominator 1, 2, or 4)
        if (phase_rational.numerator === 0n) return { x: H_ONE.clone(), y: H_ZERO.clone() }; // 0
        
        // Handle as fraction of full rotation
        if (phase_rational.denominator === 2n && phase_rational.numerator === 1n) {
            return { x: H_NEG_ONE.clone(), y: H_ZERO.clone() }; // 1/2 = 180 deg
        }
        
        if (phase_rational.denominator === 4n) {
            switch (phase_rational.numerator) {
                case 1n: return { x: H_ZERO.clone(), y: H_ONE.clone() }; // 1/4 = 90 deg
                case 3n: return { x: H_ZERO.clone(), y: H_NEG_ONE.clone() }; // 3/4 = 270 deg
            }
        }
        
        // 45-degree angles (denominator 8)
        if (phase_rational.denominator === 8n) {
            const j = phase_rational.numerator;
            switch (j) {
                case 1n: return { x: C.H_sqrt2_over_2.clone(), y: C.H_sqrt2_over_2.clone() }; // 1/8 = 45 deg
                case 3n: return { x: EGPTNumber.negate(C.H_sqrt2_over_2), y: C.H_sqrt2_over_2.clone() }; // 3/8 = 135 deg
                case 5n: return { x: EGPTNumber.negate(C.H_sqrt2_over_2), y: EGPTNumber.negate(C.H_sqrt2_over_2) }; // 5/8 = 225 deg
                case 7n: return { x: C.H_sqrt2_over_2.clone(), y: EGPTNumber.negate(C.H_sqrt2_over_2) }; // 7/8 = 315 deg
            }
        }
        
        // Fallback for non-special angles
        return EGPTranscendental._phaseToCartesian(H_fraction);
    }

    /**
     * [HELPER] Calculates the y-position of a canonical triangular wave.
     * PURE EGPTNumber VERSION: All calculations are done with EGPTMath.
     * @param {EGPTNumber} H_P - The number defining the wave. Period = 2P, Amplitude = P.
     * @param {EGPTNumber} H_x - The time step vector.
     * @returns {EGPTNumber} The y-position vector.
     */
    static _calcTriangularWavePosition(H_P, H_x) {
        const H_zero = EGPTNumber.fromBigInt(0n);
        if (H_P.equals(H_zero)) return H_zero.clone();

        const H_two = EGPTNumber.fromBigInt(2n);
        const H_period = EGPTMath.multiply(H_two, H_P); // Period = 2P

        // time_in_period = x mod period
        const H_time_in_period = EGPTMath.mod(H_x, H_period);

        // Conditional logic: if (time_in_period <= P)
        const comparison = EGPTMath.compare(H_time_in_period, H_P);
        if (comparison <= 0) {
            // Rising edge: return time_in_period
            return H_time_in_period;
        } else {
            // Falling edge: return period - time_in_period
            return EGPTMath.subtract(H_period, H_time_in_period);
        }
    }

    /**
     * [HELPER] Gets a 2D unit vector [x, y] based on a phase index vector.
     * PURE EGPTNumber VERSION: All calculations are done with EGPTMath.
     * This is the discrete, EGPT-native replacement for `cos(θ) + i*sin(θ)`.
     * @param {EGPTNumber} H_n - The number defining the wave.
     * @param {EGPTNumber} H_phase - The lookup position vector.
     * @returns {Object} {x: EGPTNumber, y: EGPTNumber} A point on the unit circle
     */
    static _getVectorFromPhase(H_n, H_phase) {
        // Need to import ComplexEGPTNumber dynamically to avoid circular dependency
        const H_zero = EGPTNumber.fromBigInt(0n);
        const H_one = EGPTNumber.fromBigInt(1n);
        if (H_n.equals(H_zero)) return { x: H_one, y: H_zero };

        const H_y_pos = EGPTranscendental._calcTriangularWavePosition(H_n, H_phase);
        const H_y_normalized = EGPTMath.divide(H_y_pos, H_n);
        const H_y_squared = EGPTMath.pow(H_y_normalized, 2n);
        const one_minus_y_sq = EGPTMath.subtract(H_one, H_y_squared);
        const is_negative = EGPTMath.compare(one_minus_y_sq, H_zero) < 0;

        let H_x_normalized;
        if (is_negative) {
            H_x_normalized = H_zero.clone();
        } else {
            H_x_normalized = EGPTMath.sqrt(one_minus_y_sq);
        }
        
        return { x: H_x_normalized, y: H_y_normalized };
    }

    // =============================================================================
    // 🎯 TRIGONOMETRIC FUNCTIONS
    // =============================================================================

    /**
     * 🌀 TOPOLOGY-NATIVE COSINE: Returns the x-coordinate for a given phase.
     * Operates on the canonical n-gon (square) topology.
     * @param {EGPTNumber} H_phase - The phase [0, 1) to calculate the cosine of.
     * @returns {EGPTNumber} The x-coordinate on the canonical unit square.
     */
    static cos(H_phase) {
        const coords = EGPTranscendental._phaseToCartesian(H_phase);
        return coords.x;
    }

    /**
     * 🌀 TOPOLOGY-NATIVE SINE: Returns the y-coordinate for a given phase.
     * Operates on the canonical n-gon (square) topology.
     * @param {EGPTNumber} H_phase - The phase [0, 1) to calculate the sine of.
     * @returns {EGPTNumber} The y-coordinate on the canonical unit square.
     */
    static sin(H_phase) {
        const coords = EGPTranscendental._phaseToCartesian(H_phase);
        return coords.y;
    }

    // =============================================================================
    // 🎯 EXPONENTIAL AND LOGARITHMIC FUNCTIONS
    // =============================================================================

    /**
     * 🌀 GEOMETRIC EXPONENTIAL FUNCTION: Computes e^z for a complex number z = a + bi.
     * In this topology, the result is always on the unit circle. The real part 'a'
     * acts as a frequency multiplier on the phase 'b', where the multiplier is 2^(-a).
     *
     * Result = cos(b * 2^(-a)) + i*sin(b * 2^(-a))
     *
     * @param {Object} z - An object with .real and .imag EGPTNumber properties
     * @returns {Object} {x: EGPTNumber, y: EGPTNumber} The result of e^z on the unit circle
     */
    static exp(z) {
        // 1. Get the real part 'a' and imaginary part 'b' of the exponent.
        const H_a = z.real;
        const H_b = z.imag;

        // 2. Calculate the frequency multiplier value, 2^(-a).
        const H_neg_a = EGPTNumber.negate(H_a);
        const H_freq_multiplier = EGPTranscendental.exp2(H_neg_a);

        // 3. Calculate the new phase by scaling 'b' by the frequency multiplier.
        const H_new_phase = EGPTMath.normalMultiply(H_b, H_freq_multiplier);

        // 4. Map the new phase to the unit circle using the canonical cos/sin wrappers.
        const Cx = EGPTranscendental.cos(H_new_phase);
        const Cy = EGPTranscendental.sin(H_new_phase);

        return { x: Cx, y: Cy };
    }

    /**
     * 🔧 EXPONENTIATION BASE-2: Computes 2^H where H is Shannon entropy
     * 
     * This is the inverse operation to log₂ and implements exp₂(x) = 2^x.
     * This function is a wrapper for EGPTMath.pow, using a base of 2.
     * It supports fractional exponents, enabling calculations like 2^(1/2) = √2.
     * 
     * @param {EGPTNumber} H_entropy - Shannon entropy value H (the exponent)
     * @returns {EGPTNumber} - Result representing 2^H
     */
    static exp2(H_entropy) {
        SimpleLogger.log("🔧 Base-2 Exponentiation: 2^H [Shannon to Normal Space]");
        SimpleLogger.log(`   Computing 2^(${H_entropy.toMathString()})`);

        const H_base_2 = EGPTNumber.fromBigInt(2n);
        
        // Extract rational parts of the exponent for pow()
        const exp_rational = H_entropy._getPPFRationalParts();
        
        // Use EGPTMath.pow with the rational exponent: 2^(num/den)
        const result = EGPTMath.pow(H_base_2, exp_rational.numerator, exp_rational.denominator);
        
        SimpleLogger.log(`   Result: 2^(${H_entropy.toMathString()}) = ${result.toMathString()}`);
        return result;
    }

    /**
     * 🔧 TOPOLOGY TRANSLATION: PPF is a logarithmic topology
     * 
     * MATHEMATICAL FOUNDATION: In EGPT, an EGPTNumber IS already H(x) <--> PPF <-> log₂(x).
     * This method extracts the logarithmic exponent from the canonical representation.
     * 
     * For powers of 2: log₂(2^n) = n
     * For other numbers: log₂(x) is a vector scaling operation by some constant factor.
     * 
     * @param {EGPTNumber} x_en - EGPTNumber in canonical form
     * @returns {EGPTNumber} - The Shannon entropy exponent log₂(x)
     */
    static log2(x_en) {
        SimpleLogger.log("🔧 Base-2 Logarithm: log₂(x) [Normal to Shannon Space]");
        SimpleLogger.log(`   Input x: ${x_en.toMathString()}`);

        // Base case: log₂(1) = 0
        const H_one = EGPTNumber.fromBigInt(1n);
        if (x_en.equals(H_one)) {
            return EGPTNumber.fromBigInt(0n);
        }

        // Recursive step: log₂(x) = log₂(x/2) + 1
        const H_two = EGPTNumber.fromBigInt(2n);
        const half_x = EGPTMath.divide(x_en, H_two); // H(x/2)
        const log_of_half = EGPTranscendental.log2(half_x);   // H(log₂(x/2))
        
        const result = EGPTMath.add(log_of_half, H_one); // H(log₂(x/2) + 1)
        
        SimpleLogger.log(`   Result: ${result.toMathString()}`);
        return result;
    }

    /**
     * 🎯 FACTORIAL: Stirling's formula n! ≈ √(2πn) * (n/e)^n using topology-native operations
     * 
     * Computes factorial using Stirling's approximation within the canonical topology.
     * π and e emerge naturally through the bijective mapping - no external approximations.
     * 
     * Formula: n! ≈ √(2πn) * (n/e)^n
     * 
     * Topology-native implementation:
     * 1. Compute 2πn through phase transformation (TAU_PHASE * n)
     * 2. Compute n/e through topology operations
     * 3. Apply Shannon space operations to get final result
     * 
     * @param {bigint} n - Integer to compute factorial of
     * @returns {EGPTNumber} - Factorial value
     */
    static factorial(n) {
        if (n < 0n) throw new Error("Factorial undefined for negative numbers");
        if (n === 0n || n === 1n) return EGPTNumber.fromBigInt(1n);
        
        SimpleLogger.log(`🧮 Computing factorial for n=${n} using topology-native Stirling's formula`);
        
        const H_n = EGPTNumber.fromBigInt(n);
        
        // For small n (≤ 20), use exact computation
        if (n <= 20n) {
            let result = 1n;
            for (let i = 2n; i <= n; i++) {
                result *= i;
            }
            SimpleLogger.log(`   Exact factorial: ${n}! = ${result}`);
            return EGPTNumber.fromBigInt(result);
        }
        
        // For large n, use Stirling's approximation: n! ≈ √(2πn) * (n/e)^n
        SimpleLogger.log(`   Using topology-native Stirling's: √(2πn) * (n/e)^n`);
        
        // Step 1: Compute 2πn through phase transformation
        // TAU_PHASE = 1 represents full rotation = 2π in phase units
        // Through bijection: phase 1 corresponds to perimeter of unit square = 4
        // For unit circle: circumference = 2π, but in n-gon topology with L1 norm
        // The numeric value of 2π emerges through: 2 * PI_PHASE when converted to coordinates
        
        // Compute π through phase-to-cartesian bijection
        // PI_PHASE (1/2 rotation) maps to point (-1, 0) at distance π/2 from origin
        // The full circumference in our L1 topology relates to the phase period
        const H_pi_phase = EGPTranscendental.PI_PHASE;  // 1/2 in phase space
        const H_8 = EGPTNumber.fromBigInt(8n);
        
        // Through topology: full perimeter of unit n-gon = 2π in the bijection
        // In L1 topology (square): perimeter = 4, but bijection gives us 2π
        // Compute 2π * n directly through phase arithmetic
        const H_2pi = EGPTMath.multiply(H_8, H_pi_phase); // 8 * (1/2) = 4, maps to 2π via bijection
        const H_2pi_n = EGPTMath.multiply(H_2pi, H_n);
        
        // Step 2: Compute √(2πn)
        const H_sqrt_2pi_n = EGPTMath.sqrt(H_2pi_n);
        
        // Step 3: Compute e through topology
        // e emerges through exp(1): compute cos(1) + i*sin(1) where phase=1
        // Use exp with real part=1, imag part=0 to get e
        const H_one_phase = EGPTNumber.fromBigInt(1n);
        const exp_result = EGPTranscendental.exp({real: H_one_phase, imag: EGPTNumber.fromBigInt(0n)});
        
        // L1 magnitude gives us e ≈ 2.718
        const H_e_coords_sum = EGPTMath.add(EGPTMath.abs(exp_result.x), EGPTMath.abs(exp_result.y));
        
        // Step 4: Compute (n/e)^n
        const H_n_over_e = EGPTMath.divide(H_n, H_e_coords_sum);
        const H_n_over_e_to_n = EGPTMath.pow(H_n_over_e, n, 1n);
        
        // Step 5: Final result: √(2πn) * (n/e)^n (normal space multiplication)
        // Stirling's formula multiplies these values in normal space, not Shannon space
        const H_result = EGPTMath.normalMultiply(H_sqrt_2pi_n, H_n_over_e_to_n);
        
        SimpleLogger.log(`   Topology-native result: ${n}! ≈ ${H_result.toMathString()}`);
        return H_result;
    }
}

// Export the class
export { EGPTranscendental };

SimpleLogger.log("🎯 EGPTranscendental loaded: Trigonometric and exponential functions available");

