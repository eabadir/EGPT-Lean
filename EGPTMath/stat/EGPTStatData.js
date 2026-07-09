// =============================================================================
// EGPT STATISTICAL DATA - STANDARDIZED METADATA CLASS
// Based on EGPT Vector Space Refactor v3.0: Vector/Scalar paradigm
//
// Author: E. Abadir
// Purpose: Standardize statistical metadata with normalized charting support
//         Handle negative magnitudes and ultra-high precision normalization
// =============================================================================

import { EGPTNumber } from '../EGPTNumber.js';
import { EGPTMath } from '../EGPTMath.js';
import { EGPTStat } from './EGPTStat.js';
import { SimpleLogger } from '../DebugLogger.js';

SimpleLogger.log("🎓 EGPT STATISTICAL DATA: Standardized metadata for charting");
SimpleLogger.log("📁 File location: EGPT/js/model/ - Production implementation");

/**
 * 🎯 EGPT STATISTICAL DATA: Standardized metadata container
 * 
 * ARCHITECTURAL PRINCIPLE: Centralizes all statistical metadata with proper
 * normalization support for Chart.js rendering. Handles negative magnitudes
 * and ultra-high precision values that would otherwise be interpreted as zeros.
 * 
 * KEY FEATURES:
 * - Normalized delta calculations against mean
 * - Chart-ready data structures for JavaScript/Chart.js
 * - Negative magnitude preservation
 * - Ultra-high precision scaling for visibility
 * - Standardized metadata format across all EGPT statistical functions
 */
class EGPTStatData {
    constructor({
        raw_values = [],
        mean = null,
        variance = null,
        std_deviation = null,
        coefficient_of_variation = null,
        min_value = null,
        max_value = null,
        range = null,
        negative_count = 0,
        total_count = 0,
        metadata = {}
    }) {
        // Store raw canonical values
        this.raw_values = raw_values;
        this.mean = mean;
        this.variance = variance;
        this.std_deviation = std_deviation;
        this.coefficient_of_variation = coefficient_of_variation;
        this.min_value = min_value;
        this.max_value = max_value;
        this.range = range;
        this.negative_count = negative_count;
        this.total_count = total_count;
        this.metadata = metadata;
        
        // Computed normalization data (lazy evaluation)
        this._normalized_deltas = null;
        this._chart_data = null;
        this._scale_factor = null;
    }

    /**
     * 📊 NORMALIZED DELTAS: Calculate (value - mean) / std_dev for each value
     * 
     * Creates normalized deviations that are Chart.js compatible while preserving
     * the relative magnitude differences that would be lost in raw ultra-high precision.
     * 
     * @returns {Array<{index: number, raw_delta: string, normalized_delta: number, magnitude_class: string}>}
     */
    getNormalizedDeltas() {
        if (this._normalized_deltas) {
            return this._normalized_deltas;
        }

        SimpleLogger.log("📊 Computing normalized deltas against mean");
        
        if (!this.mean || !this.std_deviation) {
            throw new Error("Mean and standard deviation required for normalization");
        }

        // Check for zero standard deviation (all values identical)
        const H_ZERO = EGPTNumber.fromBigInt(0n);
        const is_zero_std_dev = EGPTMath.equals(this.std_deviation, H_ZERO);

        const normalized_deltas = [];
        
        for (let i = 0; i < this.raw_values.length; i++) {
            const value = this.raw_values[i];
            
            // Calculate raw delta: value - mean (canonical)
            const raw_delta = EGPTMath.subtract(value, this.mean);
            
            // Calculate normalized delta: (value - mean) / std_dev (canonical)
            let normalized_delta_egpt;
            if (is_zero_std_dev) {
                // When std_dev is zero, all values are identical, so normalized delta is always 0
                normalized_delta_egpt = EGPTNumber.fromBigInt(0n);
            } else {
                normalized_delta_egpt = EGPTMath.normalDivide(raw_delta, this.std_deviation);
            }
            
            // Classify magnitude using canonical operations
            const magnitude_class = this._classifyMagnitude(normalized_delta_egpt);
            
            // Check sign using canonical comparison
            const is_negative = EGPTMath.compare(normalized_delta_egpt, H_ZERO) < 0;
            
            normalized_deltas.push({
                index: i,
                raw_value: value.toMathString(),
                raw_delta: raw_delta.toMathString(),
                normalized_delta: normalized_delta_egpt.toMathString(),
                normalized_delta_egpt: normalized_delta_egpt, // Keep canonical form
                magnitude_class: magnitude_class,
                is_negative: is_negative
            });
        }
        
        this._normalized_deltas = normalized_deltas;
        return normalized_deltas;
    }

    /**
     * 🎯 MAGNITUDE CLASSIFICATION: Classify normalized values for step function detection
     * 
     * Uses canonical EGPTNumber comparisons to classify magnitude.
     * Thresholds are based on standard statistical practice for normalized deltas.
     * 
     * @param {EGPTNumber} normalized_delta_egpt - Normalized delta as EGPTNumber
     * @returns {string} Classification: 'baseline', 'moderate', 'significant', 'outlier'
     */
    _classifyMagnitude(normalized_delta_egpt) {
        // ADAPTIVE THRESHOLD SYSTEM: Calculate thresholds based on data characteristics
        if (!this._adaptive_thresholds) {
            this._adaptive_thresholds = this._calculateAdaptiveThresholds();
        }
        
        const thresholds = this._adaptive_thresholds;
        
        // Get absolute value using canonical operations
        const abs_delta = EGPTMath.abs(normalized_delta_egpt);
        
        // Canonical comparisons
        if (EGPTMath.compare(abs_delta, thresholds.baseline) < 0) {
            return "baseline";
        } else if (EGPTMath.compare(abs_delta, thresholds.moderate) < 0) {
            return "moderate";
        } else if (EGPTMath.compare(abs_delta, thresholds.significant) < 0) {
            return "significant";
        } else {
            return "outlier";
        }
    }

    /**
     * 🔧 CALCULATE ADAPTIVE THRESHOLDS: Determine appropriate classification thresholds
     * for NORMALIZED deltas (which are already divided by std_deviation).
     * 
     * Returns canonical EGPTNumber thresholds for pure topology-native comparisons.
     * 
     * IMPORTANT: Since normalized deltas are calculated as (value - mean) / std_dev,
     * they are on a standard scale where typical values range from about -3 to +3.
     * Therefore, thresholds should be based on the normalized scale, not raw magnitudes.
     * 
     * @returns {Object} Canonical EGPTNumber thresholds for magnitude classification
     */
    _calculateAdaptiveThresholds() {
        // For normalized deltas, use standard statistical thresholds
        // These are appropriate because normalized_delta = (value - mean) / std_dev
        // 
        // Classification scheme:
        // - baseline: |normalized_delta| < 0.5σ  (within half a standard deviation)
        // - moderate: |normalized_delta| < 1.0σ  (within one standard deviation)
        // - significant: |normalized_delta| < 2.0σ (within two standard deviations)
        // - outlier: |normalized_delta| >= 2.0σ   (beyond two standard deviations)
        
        SimpleLogger.log(`📊 Using standard normalized delta thresholds (canonical EGPTNumbers)`);
        
        return {
            baseline: EGPTNumber.fromRational(1n, 2n),     // 0.5 standard deviations
            moderate: EGPTNumber.fromBigInt(1n),           // 1.0 standard deviation
            significant: EGPTNumber.fromBigInt(2n)         // 2.0 standard deviations
        };
    }

    /**
     * 📈 CHART-READY DATA: Generate Chart.js compatible data structures
     * 
     * CRITICAL FOR VISUALIZATION: Transforms ultra-high precision canonical space
     * data into Chart.js compatible arrays while preserving relative differences.
     * 
     * @param {Object} options - Chart preparation options
     * @returns {Object} Chart.js ready data structure
     */
    getChartData(options = {}) {
        const {
            chart_type = 'scatter',
            use_normalized = true,
            target_range = 1.0,
            min_visibility = 0.001
        } = options;

        if (this._chart_data) {
            return this._chart_data;
        }

        SimpleLogger.log("📈 Preparing Chart.js compatible data structures");

        const normalized_deltas = this.getNormalizedDeltas();
        
        // Prepare Chart.js data arrays
        const chart_data = {
            labels: normalized_deltas.map((_, i) => i.toString()),
            datasets: [{
                label: 'Normalized Entropy Deviations',
                data: normalized_deltas.map(d => ({
                    x: d.index,
                    y: d.normalized_delta_egpt.toNumber() // Convert to JS number for Chart.js
                })),
                backgroundColor: normalized_deltas.map(d => 
                    d.magnitude_class === 'baseline' ? 'rgba(75, 192, 192, 0.6)' :
                    d.magnitude_class === 'elevated' ? 'rgba(255, 206, 86, 0.6)' :
                    d.magnitude_class === 'high' ? 'rgba(255, 99, 132, 0.6)' :
                    'rgba(153, 102, 255, 0.6)'
                ),
                borderColor: normalized_deltas.map(d => 
                    d.magnitude_class === 'baseline' ? 'rgba(75, 192, 192, 1)' :
                    d.magnitude_class === 'elevated' ? 'rgba(255, 206, 86, 1)' :
                    d.magnitude_class === 'high' ? 'rgba(255, 99, 132, 1)' :
                    'rgba(153, 102, 255, 1)'
                ),
                borderWidth: 1
            }]
        };

        // Add step function detection metadata
        const step_analysis = this._analyzeStepFunction(normalized_deltas);
        
        this._chart_data = {
            chart_data: chart_data,
            step_analysis: step_analysis,
            normalization_metadata: {
                scale_factor: this._calculateScaleFactor(),
                original_precision: this.metadata.precision || 'ultra-high',
                negative_preservation: this.negative_count > 0,
                total_points: normalized_deltas.length
            }
        };

        return this._chart_data;
    }

    /**
     * 🔍 STEP FUNCTION ANALYSIS: Detect step function patterns in normalized data
     * 
     * @param {Array} normalized_deltas - Array of normalized delta objects
     * @returns {Object} Step function analysis results
     */
    _analyzeStepFunction(normalized_deltas) {
        const magnitude_groups = {
            baseline: normalized_deltas.filter(d => d.magnitude_class === 'baseline'),
            elevated: normalized_deltas.filter(d => d.magnitude_class === 'elevated'),
            high: normalized_deltas.filter(d => d.magnitude_class === 'high'),
            extreme: normalized_deltas.filter(d => d.magnitude_class === 'extreme')
        };

        const total = normalized_deltas.length;
        
        return {
            groups: Object.fromEntries(
                Object.entries(magnitude_groups).map(([key, group]) => [
                    key, 
                    {
                        count: group.length,
                        percentage: (group.length / total * 100).toFixed(1),
                        indices: group.map(d => d.index)
                    }
                ])
            ),
            step_function_detected: magnitude_groups.baseline.length > 0 && 
                                   (magnitude_groups.elevated.length > 0 || 
                                    magnitude_groups.high.length > 0 || 
                                    magnitude_groups.extreme.length > 0),
            dominant_group: Object.entries(magnitude_groups)
                .sort(([,a], [,b]) => b.length - a.length)[0][0]
        };
    }

    /**
     * 🔧 SCALE FACTOR: Calculate appropriate scaling for ultra-high precision values
     * 
     * @returns {number} Scale factor for visibility preservation
     */
    _calculateScaleFactor() {
        if (this._scale_factor) {
            return this._scale_factor;
        }

        if (!this.range) {
            return 1.0;
        }

        const range_rational = this.range.getRationalParts();
        const range_magnitude = Number(range_rational.numerator) / Number(range_rational.denominator);
        
        // Calculate scale factor to bring ultra-small values into visible range
        this._scale_factor = range_magnitude < 1e-15 ? 1e15 : 
                            range_magnitude < 1e-10 ? 1e10 :
                            range_magnitude < 1e-5 ? 1e5 : 1.0;
        
        return this._scale_factor;
    }

    /**
     * 🎯 CREATE FROM ARRAY: Factory method for creating EGPTStatData from value array
     * 
     * @param {Array<EGPTNumber>} values - Array of EGPTNumber values
     * @param {Object} options - Creation options
     * @returns {EGPTStatData} Complete statistical data object
     */
    static fromArray(values, options = {}) {
        SimpleLogger.log(`🏭 Creating EGPTStatData from ${values.length} values`);
        
        if (values.length === 0) {
            throw new Error("Cannot create EGPTStatData from empty array");
        }

        // Calculate comprehensive statistics using EGPTStat
        const mean = EGPTStat.mean(values);
        const variance_result = EGPTStat.variance(values);
        const variance = variance_result.variance;
        // Use EGPTStat._normalSqrt for statistical standard deviation (normal space √variance)
        const std_deviation = EGPTStat._normalSqrt(variance);
        
        // Handle coefficient of variation carefully (avoid divide by zero)
        let coefficient_of_variation;
        const mean_rational = mean.getRationalParts();
        if (mean_rational.numerator === 0n) {
            // If mean is zero, coefficient of variation is undefined or infinity
            // For statistical purposes, set to zero when variance is also zero
            const variance_rational = variance.getRationalParts();
            if (variance_rational.numerator === 0n) {
                coefficient_of_variation = EGPTNumber.fromBigInt(0n); // All values identical
            } else {
                coefficient_of_variation = EGPTNumber.fromBigInt(1000000n); // Infinite CV approximation
            }
        } else {
            coefficient_of_variation = EGPTMath.normalDivide(std_deviation, mean);
        }

        // Find min and max
        let min_value = values[0];
        let max_value = values[0];
        let negative_count = 0;

        for (const value of values) {
            if (EGPTMath.compare(value, min_value) < 0) min_value = value;
            if (EGPTMath.compare(value, max_value) > 0) max_value = value;
            if (EGPTMath.compare(value, EGPTNumber.fromBigInt(0n)) < 0) negative_count++;
        }

        // Calculate range, handling zero min_value case
        let range;
        const zero = EGPTNumber.fromBigInt(0n);
        if (EGPTMath.compare(min_value, zero) === 0) {
            // If min is zero, range is just max_value (or zero if max is also zero)
            range = max_value.clone();
        } else {
            range = EGPTMath.normalDivide(max_value, min_value);
        }

        return new EGPTStatData({
            raw_values: values,
            mean: mean,
            variance: variance,
            std_deviation: std_deviation,
            coefficient_of_variation: coefficient_of_variation,
            min_value: min_value,
            max_value: max_value,
            range: range,
            negative_count: negative_count,
            total_count: values.length,
            metadata: {
                ...variance_result.metadata,
                precision: 'ultra-high',
                creation_options: options
            }
        });
    }

    /**
     * 📊 GET CHART DATA FOR SEGMENT MANAGER: Specialized method for EGPT algorithm integration
     * 
     * CRITICAL: This method specifically handles the data format needed by SegmentManager
     * and the Chart.js rendering pipeline. It provides proper normalization for extreme
     * values (-1000 for exact factors) that would otherwise cause infinite lines.
     * 
     * @returns {Object} Chart-ready data in SegmentManager expected format
     */
    getChartData() {
        SimpleLogger.log("📊 Generating chart data for SegmentManager integration");
        
        if (!this.raw_values || this.raw_values.length === 0) {
            return {
                deviation_values_for_chart: [],
                use_ordinal_ranking: false,
                unique_groups_count: 0,
                scale_factor: 1.0,
                range_magnitude: 0
            };
        }

        // Calculate range magnitude for decision logic
        const range_rational = this.range.getRationalParts();
        const range_magnitude = Math.abs(Number(range_rational.numerator) / Number(range_rational.denominator));
        
        let use_ordinal_ranking = false;
        let scale_factor = 1.0;

        // Decision logic: Use ordinal ranking for extreme precision cases
        if (range_magnitude < 1e-10 || range_rational.denominator > 2n ** 64n) {
            use_ordinal_ranking = true;
            SimpleLogger.log("📊 Using ordinal ranking due to extreme precision");
        } else {
            const target_range = 1.0;
            scale_factor = range_magnitude > 0 ? Math.min(1.0, target_range / range_magnitude) : 1.0;
            SimpleLogger.log(`📊 Using scaled decimal with factor: ${scale_factor}`);
        }

        const deviation_values_for_chart = new Array(this.raw_values.length);
        let unique_groups_count = 0;

        if (use_ordinal_ranking) {
            // ORDINAL RANKING APPROACH: Convert canonical differences to ordinal values
            // This preserves step function patterns even when decimal conversion fails
            
            // Group deviations by canonical equality
            const deviation_groups = new Map();
            this.raw_values.forEach((val, index) => {
                // Find if this deviation equals any existing group
                let found_group = null;
                for (const [key_deviation, indices] of deviation_groups) {
                    if (val.equals(key_deviation)) {
                        found_group = key_deviation;
                        break;
                    }
                }
                
                if (found_group) {
                    deviation_groups.get(found_group).push(index);
                } else {
                    deviation_groups.set(val, [index]);
                }
            });
            
            unique_groups_count = deviation_groups.size;
            
            // Sort groups by canonical comparison to establish ordinal ranking
            const sorted_groups = Array.from(deviation_groups.entries()).sort((a, b) => {
                return EGPTMath.compare(b[0], a[0]); // Descending order
            });
            
            SimpleLogger.log(`📊 Found ${sorted_groups.length} unique deviation groups (preserves step function)`);
            
            // Assign ordinal values: highest deviation group = 1.0, next = 0.8, etc.
            sorted_groups.forEach((group, group_index) => {
                const ordinal_value = 1.0 - (group_index * 0.2); // Spread groups apart visually
                const [group_deviation, indices] = group;
                
                indices.forEach(div_index => {
                    deviation_values_for_chart[div_index] = Math.max(0.1, ordinal_value); // Minimum 0.1 for visibility
                });
            });
            
        } else {
            // SCALED DECIMAL APPROACH: Traditional scaling for moderate precision cases
            this.raw_values.forEach((val, index) => {
                const rational = val.getRationalParts();
                const decimal = Number(rational.numerator) / Number(rational.denominator);
                
                // Apply scaling and ensure minimum visibility for Chart.js
                const scaled_value = decimal * scale_factor;
                
                // Handle extreme negative values (exact factors) by clamping
                if (scaled_value < -100) {
                    deviation_values_for_chart[index] = -1.0; // Visible but not extreme
                } else if (scaled_value > 100) {
                    deviation_values_for_chart[index] = 1.0; // Visible but not extreme
                } else {
                    deviation_values_for_chart[index] = Math.max(0.001, Math.abs(scaled_value)); // Ensure visibility
                }
            });
            unique_groups_count = this.raw_values.length;
        }

        SimpleLogger.log(`📊 Chart data prepared: ${deviation_values_for_chart.length} points, mode: ${use_ordinal_ranking ? 'ordinal' : 'scaled'}`);

        return {
            deviation_values_for_chart,
            use_ordinal_ranking,
            unique_groups_count,
            scale_factor,
            range_magnitude
        };
    }

    /**
     * 🎯 NEGATIVE MAGNITUDE SUPPORT: Extract negative magnitude with sign preservation
     * 
     * CRITICAL: Handles cases where PPF encoding would lose negative information.
     * Returns both the absolute magnitude and the sign information separately.
     * 
     * @param {EGPTNumber} value - EGPTNumber that may represent negative magnitude
     * @returns {Object} {magnitude: EGPTNumber, is_negative: boolean, signed_js: number}
     */
    static extractNegativeMagnitude(value) {
        const rational = value.getRationalParts();
        const is_negative = rational.numerator < 0n;
        
        // Create absolute magnitude
        const abs_numerator = is_negative ? -rational.numerator : rational.numerator;
        const magnitude = EGPTNumber.fromRational(abs_numerator, rational.denominator);
        
        // JavaScript representation for charting
        const signed_js = Number(rational.numerator) / Number(rational.denominator);
        
        return {
            magnitude: magnitude,
            is_negative: is_negative,
            signed_js: signed_js,
            original_rational: rational
        };
    }
}

export { EGPTStatData };
