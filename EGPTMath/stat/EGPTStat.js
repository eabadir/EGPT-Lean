import { EGPTNumber } from '../EGPTNumber.js';
import { EGPTMath } from '../EGPTMath.js';
import { EGPTStatData } from './EGPTStatData.js';
import { SimpleLogger } from '../DebugLogger.js';

/**
 * HELPER: BigInt square root using Newton's method
 * @param {bigint} n - Number to take square root of
 * @returns {bigint} - Floor of square root
 * @private
 */
function bigIntSqrt(n) {
    if (n < 0n) throw new Error('Square root of negative number');
    if (n < 2n) return n;
    
    function newtonIteration(n, x0) {
        const x1 = ((n / x0) + x0) >> 1n;
        if (x0 === x1 || x0 === (x1 - 1n)) return x0;
        return newtonIteration(n, x1);
    }
    return newtonIteration(n, 1n);
}

/**
 * 📊 EGPTStat: Statistical Analysis for EGPTNumber Vectors
 * An information vector V(k) is a single EGPTNumber (also denoted in traditional entropy notation as H(k)).
 * 
 * This class provides methods for statistical analysis of EGPTNumber vectors,
 * including mean, variance, absolute difference, and comprehensive statistical analysis.
 * 
 * Key Features:
 * - Mean: Computes arithmetic mean of vectors
 * - Variance: Calculates variance with metadata on negative deviations
 * - Absolute Difference: Computes |H(a) - H(b)| while maintaining PPF integrity
 * - Comprehensive Analysis: Returns EGPTStatData with normalization metadata
 * - Gap Detection: Identifies statistical gaps using ratios in canonical
 */
export class EGPTStat {
    // Prevent instantiation of this static class
    constructor() {
        throw new Error("EGPTStat is a static class and cannot be instantiated.");
    }

    /**
     * 🎯 NORMAL SPACE SQUARE ROOT: √(a/b) = √a / √b
     * 
     * Computes approximate square root in normal space using BigInt sqrt on numerator
     * and denominator separately. Used for statistical calculations like standard deviation.
     * 
     * NOTE: This is approximate for non-perfect-squares, unlike Shannon space sqrt which
     * represents exact irrational values via scaled vectors.
     * 
     * @param {EGPTNumber} a_en - Input vector
     * @returns {EGPTNumber} - Approximate square root in normal space
     * @private
     */
    static _normalSqrt(a_en) {
        const rational = a_en._getPPFRationalParts();
        
        // Use bigIntSqrt helper
        const sqrt_num = rational.numerator < 0n ? 
            -(bigIntSqrt(-rational.numerator)) : 
            bigIntSqrt(rational.numerator);
        const sqrt_den = bigIntSqrt(rational.denominator);
        
        return EGPTNumber.fromRational(sqrt_num, sqrt_den);
    }
    /**
     * 📊 STATISTICAL MEAN: Arithmetic mean of vector array
    * An information vector V(k) is a single EGPTNumber (also denoted in traditional entropy notation as H(k)). 
    * 
     * Calculates mean in normal space: (v₁ + v₂ + ... + vₙ) / n
     * NOT the same as Shannon entropy mean.
     * 
     * @param {Array<EGPTNumber>} information_vectors_en - Array of vectors
     * @returns {EGPTNumber} - Mean vector
     */
    static mean(information_vectors_en) {
        if (information_vectors_en.length === 0) {
            throw new Error("Cannot calculate mean of empty vector array");
        }
        
        SimpleLogger.log(`📊 Statistical Mean: Computing mean of ${information_vectors_en.length} vectors`);
        
        // Sum all vectors using normal space addition
        let sum = information_vectors_en[0].clone();
        for (let i = 1; i < information_vectors_en.length; i++) {
            sum = EGPTMath.add(sum, information_vectors_en[i]);
        }
        
        // Divide by count using NORMAL SPACE division (not Shannon space)
        // Statistical mean is (a+b+c)/n, not (a+b+c)^(1/n)
        const count_en = EGPTNumber.fromBigInt(BigInt(information_vectors_en.length));
        return EGPTMath.normalDivide(sum, count_en);
    }

    /**
     * 📊 STATISTICAL VARIANCE: Variance of vector array with metadata
     * 
     * An information vector V(k) is a single EGPTNumber (also denoted in traditional entropy notation as H(k)).
     * 
     * Calculates variance in normal space: Σ(xᵢ - μ)² / N
     * Uses absolute difference to avoid negative PPF encoding issues.
     * Returns both the variance value and metadata about negative deviations.
     * 
     * @param {Array<EGPTNumber>} information_vectors_en - Array of vectors
     * @returns {Object} - {variance: EGPTNumber, metadata: {negative_deviations: number, total_vectors: number}}
     */
    static variance(information_vectors_en) {
        if (information_vectors_en.length === 0) {
            throw new Error("Cannot calculate variance of empty vector array");
        }
        
        SimpleLogger.log(`📊 Statistical Variance: Computing variance of ${information_vectors_en.length} vectors`);
        
        // Calculate mean
        const mean_vector = EGPTStat.mean(information_vectors_en);
        
        // Calculate sum of squared deviations using absolute difference
        let sum_squared_deviations = EGPTNumber.fromBigInt(0n);
        let negative_deviations = 0;
        
        for (let i = 0; i < information_vectors_en.length; i++) {
            const vector = information_vectors_en[i];
            
            // Check if this would be a negative deviation
            const comparison = EGPTMath.compare(vector, mean_vector);
            if (comparison < 0) {
                negative_deviations++;
            }
            
            // Use absoluteDifference to avoid negative values in PPF encoding
            const deviation = EGPTStat.absoluteDifference(vector, mean_vector);
            
            // squared_deviation = deviation² (NORMAL SPACE multiplication, not Shannon)
            const squared_deviation = EGPTMath.normalMultiply(deviation, deviation);
            
            // sum += squared_deviation
            sum_squared_deviations = EGPTMath.add(sum_squared_deviations, squared_deviation);
        }
        
        // variance = sum / N (NORMAL SPACE division, not Shannon)
        const count = BigInt(information_vectors_en.length);
        const variance_value = EGPTMath.normalDivide(sum_squared_deviations, EGPTNumber.fromBigInt(count));
        
        return {
            variance: variance_value,
            metadata: {
                negative_deviations: negative_deviations,
                total_vectors: information_vectors_en.length,
                has_negative_deviations: negative_deviations > 0
            }
        };
    }


    /**
     * 🎯 CANONICAL ABSOLUTE DIFFERENCE: |H(a) - H(b)| always positive
     * 
     * CRITICAL FOR PPF INTEGRITY: Computes absolute difference while maintaining
     * PPF encoding integrity. Avoids negative intermediate values.
     * 
     * @param {EGPTNumber} H_a - First entropy value
     * @param {EGPTNumber} H_b - Second entropy value
     * @returns {EGPTNumber} Absolute difference |H(a) - H(b)|
     */
    static absoluteDifference(H_a, H_b) {
        SimpleLogger.log("🧮 ABSOLUTE DIFFERENCE: |H(a) - H(b)| maintaining PPF integrity");
        
        // Compare and return larger - smaller to ensure positive result
        const comparison = EGPTMath.compare(H_a, H_b);
        
        if (comparison >= 0) {
            // H_a >= H_b, return H_a - H_b
            return EGPTMath.subtract(H_a, H_b);
        } else {
            // H_a < H_b, return H_b - H_a  
            return EGPTMath.subtract(H_b, H_a);
        }
    }

    /**
     * 🎯 COMPREHENSIVE STATISTICAL ANALYSIS: Ultra-high precision with EGPTStatData
     * 
     * CRITICAL FOR CHARTING: Returns EGPTStatData object with both exact canonical space 
     * calculations AND normalization metadata needed for chart preparation.
     * 
     * @param {Array<EGPTNumber>} H_values - Array of entropy values for analysis
     * @param {Object} [options] - Analysis options
     * @returns {EGPTStatData} Complete statistical analysis as EGPTStatData object
     */
    static comprehensiveStatisticalAnalysis(H_values, options = {}) {
        SimpleLogger.log("📊 COMPREHENSIVE STATISTICAL ANALYSIS: Ultra-high precision with EGPTStatData");
        SimpleLogger.log(`   Analyzing ${H_values.length} entropy values`);
        
        if (H_values.length === 0) {
            throw new Error("Cannot analyze empty array of entropy values");
        }
        
        // Use EGPTStatData for all statistical analysis - this handles negative PPF automatically
        const stat_data = EGPTStatData.fromArray(H_values, {
            include_normalization: true,
            chart_target_range: 1.0,
            min_chart_visibility: 0.1,
            ...options
        });
        
        SimpleLogger.log(`   Mean: ${stat_data.mean.toMathString()}`);
        SimpleLogger.log(`   Std Dev: ${stat_data.std_deviation.toMathString()}`);
        SimpleLogger.log(`   Scale Factor: ${stat_data.metadata.scale_factor || 'N/A'}`);
        
        return stat_data;
    }

    /**
     * 🧮 STATISTICAL GAP DETECTION: Identifies large ratios in canonical space
     * 
     * PEDAGOGICAL PRINCIPLE: Detects outliers by finding ratios significantly
     * larger than typical ratios. Uses coefficient of variation threshold.
     * 
     * @param {Array<EGPTNumber>} H_values - Sorted array of entropy values
     * @param {number} gap_threshold_multiplier - Multiple of std dev for gap detection (default: 2.0)
     * @returns {Array<{index: number, gap_size: EGPTNumber}>} Array of detected gaps
     */
    static detectStatisticalGaps(H_values, gap_threshold_multiplier = 2.0) {
        SimpleLogger.log("📊 STATISTICAL GAP DETECTION: Identifying outliers using ratios");
        SimpleLogger.log(`   Using gap threshold: ${gap_threshold_multiplier}σ above mean`);
        
        if (H_values.length < 2) {
            SimpleLogger.log("   Insufficient data for gap detection");
            return [];
        }
        
        // Step 1: Sort values in canonical space
        const H_sorted = [...H_values].sort((a, b) => EGPTMath.compare(a, b));
        
        // Step 2: Compute adjacent ratios (larger/smaller >= 1)
        const gaps = [];
        for (let i = 1; i < H_sorted.length; i++) {
            const ratio = EGPTMath.divide(H_sorted[i], H_sorted[i-1]);
            gaps.push({
                index: i,
                gap_size: ratio
            });
        }
        
        if (gaps.length === 0) {
            SimpleLogger.log("   No gaps to analyze");
            return [];
        }
        
        // Step 3: Compute statistical threshold using ratios
        const H_ratio_values = gaps.map(g => g.gap_size);
        const H_ratio_mean = EGPTStat.mean(H_ratio_values);
        const H_ratio_variance_result = EGPTStat.variance(H_ratio_values);
        const H_ratio_variance = H_ratio_variance_result.variance; // Extract variance from metadata object
        const H_ratio_stddev = EGPTMath.sqrt(H_ratio_variance);
        
        // Step 4: Create threshold (mean + multiplier * stddev)
        const H_multiplier = EGPTNumber.fromRational(
            BigInt(Math.floor(gap_threshold_multiplier * 1000)), 1000n
        );
        const H_threshold_offset = EGPTMath.multiply(H_ratio_stddev, H_multiplier);
        const H_threshold = EGPTMath.add(H_ratio_mean, H_threshold_offset);
        
        SimpleLogger.log(`   Ratio mean: ${H_ratio_mean.toMathString()}`);
        SimpleLogger.log(`   Ratio std dev: ${H_ratio_stddev.toMathString()}`);
        SimpleLogger.log(`   Detection threshold: ${H_threshold.toMathString()}`);
        
        // Step 5: Identify large gaps
        const large_gaps = gaps.filter(gap => 
            EGPTMath.compare(gap.gap_size, H_threshold) > 0
        );
        
        SimpleLogger.log(`   Detected ${large_gaps.length} statistical gaps`);
        large_gaps.forEach((gap, index) => {
            SimpleLogger.log(`     Gap ${index}: index=${gap.index}, size=${gap.gap_size.toMathString()}`);
        });
        
        return large_gaps;
    }


    /**
     * 🎯 ENTROPY LANDSCAPE MAPPER: O(log n) interval-based factor detection
     * 
     * PEDAGOGICAL PRINCIPLE: Maps entropy landscape using strategic interval sampling
     * to detect factor presence without finding specific factors. Achieves O(log n)
     * complexity by analyzing bit-length intervals rather than individual candidates.
     * 
     * MATHEMATICAL FOUNDATION:
     * 1. Divide search space into logarithmic intervals based on bit length
     * 2. Sample strategic waypoints within each interval using entropy spikes
     * 3. Detect intervals containing factors without identifying specific factors
     * 4. Use EGPTStatData for comprehensive interval analysis with bimodal detection
     * 
     * This enables factor interval detection in O(log n) vs O(√n) exhaustive search.
     * 
     * @param {EGPTNumber} k_en - Target vector H(k) to analyze
     * @param {BigInt} interval_start - Start of analysis interval
     * @param {BigInt} interval_end - End of analysis interval  
     * @param {number} resolution - Number of sub-intervals to create
     * @param {string} spacing_type - "log" for logarithmic spacing, "linear" for linear spacing
     * @returns {Object} - Interval-based landscape analysis with factor detection
     */
    static mapEntropyLandscape(k_en, interval_start, interval_end, resolution, spacing_type = "linear") {
        SimpleLogger.log("🗺️ ENTROPY LANDSCAPE MAPPER: Interval-based factor detection using vector navigation paradigm");
        SimpleLogger.log(`   Target vector H(k): ${k_en.toMathString()}`);
        SimpleLogger.log(`   Analysis interval: [${interval_start}, ${interval_end}]`);
        SimpleLogger.log(`   Resolution: ${resolution} sub-intervals for landscape mapping`);
        SimpleLogger.log(`   Spacing strategy: ${spacing_type}`);

        // Step 1: Validate inputs
        if (interval_start >= interval_end) {
            throw new Error("interval_start must be less than interval_end");
        }

        if (resolution < 1) {
            throw new Error("resolution must be at least 1");
        }

        if (!["log", "linear"].includes(spacing_type)) {
            throw new Error("spacing_type must be 'log' or 'linear'");
        }

        // Step 2: Generate sample points based on spacing type
        const sample_points = EGPTMath._generateIntervalSamplePoints(
            interval_start, interval_end, resolution, spacing_type
        );

        SimpleLogger.log(`   Generated ${sample_points.length} sample points using ${spacing_type} spacing`);

        const conditional_entropies = [];
        const exact_factors = [];
        let total_exact_factors = 0;

        // Step 3: Analyze each sample point
        SimpleLogger.log(`\n   🔍 Analyzing ${sample_points.length} sample points:`);

        const all_conditional_entropies = [];
        const exact_factors_found = [];


        for (let i = 0; i < sample_points.length; i++) {
            const p_value = sample_points[i];
            const H_p = EGPTNumber.fromBigInt(p_value);

            try {
                const conditional_result = EGPTMath.conditionalEntropyVector(k_en, H_p);

                // Check if result indicates exact factor
                const is_exact_factor = conditional_result.isExactFactor ||
                    (conditional_result.toMathString && conditional_result.toMathString().includes('-'));

                SimpleLogger.log(`     p=${p_value}: exact_factor=${is_exact_factor}`);

                // Track exact factors
                if (is_exact_factor) {
                    total_exact_factors++;
                    exact_factors_found.push(p_value);
                }

                // Store conditional entropy for analysis
                const entropy_value = conditional_result.magnitude || conditional_result;
                all_conditional_entropies.push(entropy_value);

            } catch (error) {
                SimpleLogger.log(`     ❌ Error analyzing p=${p_value}: ${error.message}`);
            }
        }

        // Step 4: Calculate gradients between consecutive points (simplified for now)
        SimpleLogger.log(`\n   📈 Computing gradients between consecutive points:`);

        let steep_gradient_count = 0;
        let factor_transition_count = 0;

        for (let i = 0; i < sample_points.length - 1; i++) {
            const p1 = sample_points[i];
            const p2 = sample_points[i + 1];

            try {
                const gradient_result = EGPTMath.analyzeLandscapeGradient(
                    k_en, p1, p2
                );

                const steep_gradient = gradient_result.steep_gradient_detected || false;
                const factor_transition = gradient_result.factor_transition_detected || false;

                if (steep_gradient) steep_gradient_count++;
                if (factor_transition) factor_transition_count++;

                SimpleLogger.log(`     Gradient ${p1}→${p2}: steep=${steep_gradient}, transition=${factor_transition}`);

            } catch (error) {
                SimpleLogger.log(`     ❌ Gradient calculation failed for ${p1}→${p2}: ${error.message}`);
            }
        }

        // Step 5: Analyze overall landscape patterns
        const steep_gradient_regions = sample_points.filter((_, i) => i < sample_points.length - 1);
        const bimodal_distribution_detected = total_exact_factors > 0 && factor_transition_count > 0;

        SimpleLogger.log(`\n   🎯 LANDSCAPE ANALYSIS SUMMARY:`);
        SimpleLogger.log(`     Points sampled: ${sample_points.length}`);
        SimpleLogger.log(`     Exact factors found: ${total_exact_factors} (${exact_factors_found.join(', ')})`);
        SimpleLogger.log(`     Steep gradient regions: ${steep_gradient_count}`);
        SimpleLogger.log(`     Factor transitions: ${factor_transition_count}`);
        SimpleLogger.log(`     Bimodal distribution: ${bimodal_distribution_detected ? '✅ YES' : '❌ NO'}`);

        // Step 6: Return comprehensive analysis result
        return {
            target_k: k_en.toMathString(),
            interval_bounds: { start: interval_start.toString(), end: interval_end.toString() },
            spacing_type: spacing_type,
            resolution: resolution,
            points_sampled: sample_points.length,

            // Core results
            sample_points: sample_points,
            exact_factors_found: exact_factors_found,

            // Statistical analysis (simplified)
            steep_gradient_regions: steep_gradient_regions,
            factor_transitions: factor_transition_count,
            bimodal_distribution_detected: bimodal_distribution_detected,

            // Raw data for further analysis
            conditional_entropies: all_conditional_entropies,

            // Pedagogical insight
            pedagogical_insight: `Interval analysis with ${spacing_type} spacing detected ${total_exact_factors} exact factors with ${factor_transition_count} transitions`
        };

    }

    /**
     * 🎯 LANDSCAPE GRADIENT ANALYZER: Gradient analysis between navigation waypoints
     * 
     * HELPER METHOD: Analyzes the entropy landscape gradient between two specific waypoints
     * in the vector navigation paradigm. Essential for detecting factor transitions and
     * course correction magnitude changes between integer grid points.
     * 
     * MATHEMATICAL FOUNDATION:
     * 1. Calculate course correction magnitude at both waypoints using conditionalEntropyVector
     * 2. Compute landscape gradient: (correction_p2 - correction_p1) / (p2 - p1)
     * 3. Detect factor transitions and entropy spike features in the landscape
     * 
     * @param {EGPTNumber} k_en - Target vector H(k) for navigation analysis
     * @param {BigInt} p1 - First waypoint for gradient calculation
     * @param {BigInt} p2 - Second waypoint for gradient calculation
     * @returns {Object} - Landscape gradient analysis between waypoints
     */
    static analyzeLandscapeGradient(k_en, p1, p2) {
        SimpleLogger.log("🧭 LANDSCAPE GRADIENT ANALYZER: Vector navigation between waypoints");
        SimpleLogger.log(`   Target navigation vector H(k): ${k_en.toMathString()}`);
        SimpleLogger.log(`   Waypoint 1: ${p1}`);
        SimpleLogger.log(`   Waypoint 2: ${p2}`);

        // Step 1: Validate inputs
        if (p1 === p2) {
            throw new Error("Points must be different for gradient calculation");
        }

        // Ensure p1 < p2 for consistent gradient direction
        const [start_point, end_point] = p1 < p2 ? [p1, p2] : [p2, p1];
        const gradient_direction = p1 < p2 ? 1 : -1;

        // Step 2: Calculate conditional entropy at both points
        const H_p1 = EGPTNumber.fromBigInt(start_point);
        const H_p2 = EGPTNumber.fromBigInt(end_point);

        const conditional_p1 = EGPTMath.conditionalEntropyVector(k_en, H_p1);
        const conditional_p2 = EGPTMath.conditionalEntropyVector(k_en, H_p2);

        SimpleLogger.log(`   H(k|${start_point}): ${conditional_p1.toMathString ? conditional_p1.toMathString() : conditional_p1}`);
        SimpleLogger.log(`   H(k|${end_point}): ${conditional_p2.toMathString ? conditional_p2.toMathString() : conditional_p2}`);

        // Step 3: Check for exact factors at either point
        const p1_is_factor = conditional_p1.isExactFactor ||
            (conditional_p1.toMathString && conditional_p1.toMathString().includes('-'));
        const p2_is_factor = conditional_p2.isExactFactor ||
            (conditional_p2.toMathString && conditional_p2.toMathString().includes('-'));

        SimpleLogger.log(`   Point ${start_point} is exact factor: ${p1_is_factor}`);
        SimpleLogger.log(`   Point ${end_point} is exact factor: ${p2_is_factor}`);

        // Step 4: Calculate gradient (handle special cases for exact factors)
        let gradient_magnitude, entropy_change;

        if (p1_is_factor || p2_is_factor) {
            // Special handling for exact factors (use magnitudes)
            const mag1 = conditional_p1.magnitude || EGPTNumber.fromBigInt(1000n);
            const mag2 = conditional_p2.magnitude || EGPTNumber.fromBigInt(1000n);

            entropy_change = EGPTStat.absoluteDifference(mag2, mag1);
            SimpleLogger.log(`   Using magnitude difference for exact factors: ${entropy_change.toMathString()}`);
        } else {
            // Normal gradient calculation
            entropy_change = EGPTStat.absoluteDifference(conditional_p2, conditional_p1);
            SimpleLogger.log(`   Normal entropy difference: ${entropy_change.toMathString()}`);
        }

        // Gradient = entropy_change / distance
        const distance = EGPTNumber.fromBigInt(end_point - start_point);
        gradient_magnitude = EGPTMath.divide(entropy_change, distance);

        SimpleLogger.log(`   Distance: ${distance.toMathString()}`);
        SimpleLogger.log(`   Gradient magnitude: ${gradient_magnitude.toMathString()}`);

        // Step 5: Analyze gradient features
        const has_factor_spike = p1_is_factor || p2_is_factor;
        const factor_transition = p1_is_factor !== p2_is_factor;
        const gradient_steep = EGPTMath.compare(gradient_magnitude, EGPTNumber.fromBigInt(10n)) > 0;

        SimpleLogger.log(`   Has factor spike: ${has_factor_spike}`);
        SimpleLogger.log(`   Factor transition: ${factor_transition}`);
        SimpleLogger.log(`   Steep gradient: ${gradient_steep}`);

        return {
            start_point: start_point,
            end_point: end_point,
            gradient_direction: gradient_direction,
            conditional_entropy_p1: conditional_p1,
            conditional_entropy_p2: conditional_p2,
            entropy_change: entropy_change,
            gradient_magnitude: gradient_magnitude,
            distance: distance,
            p1_is_factor: p1_is_factor,
            p2_is_factor: p2_is_factor,
            has_factor_spike: has_factor_spike,
            factor_transition: factor_transition,
            gradient_steep: gradient_steep,
            pedagogical_insight: `Gradient analysis reveals ${factor_transition ? 'factor transition' : 'landscape continuity'} between points`
        };
    }

    /**
     * 🔧 HELPER: Generate sample points within interval using specified spacing
     * 
     * PEDAGOGICAL PRINCIPLE: Creates strategic sampling points for landscape analysis.
     * Logarithmic spacing clusters more points near the start for factor detection.
     * Linear spacing provides uniform coverage across the interval.
     * 
     * @param {BigInt} interval_start - Start of interval
     * @param {BigInt} interval_end - End of interval
     * @param {number} resolution - Target number of sample points
     * @param {string} spacing_type - "log" or "linear"
     * @returns {Array<BigInt>} - Array of sample points
     */
    static _generateIntervalSamplePoints(interval_start, interval_end, resolution, spacing_type) {
        SimpleLogger.log(`🔧 Generating ${spacing_type} sample points: [${interval_start}, ${interval_end}] with resolution ${resolution}`);

        const sample_points = [];
        const interval_size = interval_end - interval_start;

        if (spacing_type === "linear") {
            // Linear spacing: divide interval into equal parts
            const step_size = Number(interval_size) / resolution;

            for (let i = 0; i <= resolution; i++) {
                const point = interval_start + BigInt(Math.floor(i * step_size));
                if (point <= interval_end) {
                    sample_points.push(point);
                }
            }

        } else if (spacing_type === "log") {
            // Logarithmic spacing: points at interval_start + 1, +2, +4, +8, etc.
            sample_points.push(interval_start); // Always include start point

            let current_offset = 1n;
            while (current_offset <= interval_size && sample_points.length < resolution) {
                const point = interval_start + current_offset;
                if (point <= interval_end) {
                    sample_points.push(point);
                }
                current_offset *= 2n; // Double the offset each time
            }

            // Always include end point if we haven't reached it
            if (sample_points[sample_points.length - 1] !== interval_end) {
                sample_points.push(interval_end);
            }
        }

        SimpleLogger.log(`   Generated ${sample_points.length} points: [${sample_points[0]}, ..., ${sample_points[sample_points.length - 1]}]`);
        return sample_points;
    }



}