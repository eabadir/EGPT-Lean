/**
 * PipelineData.js
 * 
 * This module provides class definitions for data structures used in managing and processing pipeline data.
 * 
 * ARCHITECTURAL PRINCIPLE: These classes standardize and encapsulate the data objects that flow between
 * components in the EGPT analysis pipeline. They provide validation, type safety, and clear contracts
 * between UI, Orchestrator, Algorithm, and Utility layers.
 * 
 * PEDAGOCAL PRINCIPLE: Uses EGPT Vector/Scalar paradigm throughout.
 * EGPTNumber = Information Vectors, BigInt = Scalars, EGPTMath = Vector Algebra
 * 
 * @fileoverview Standardized data structure classes for EGPT pipeline components
 * @author EGPT Development Team
 * @since 2025-08-03
 */

// Import the EGPT production classes from the Vector/Scalar paradigm
import { EGPTNumber } from '../EGPTNumber.js';

console.log("🎓 PIPELINE DATA STRUCTURES: Standardized data encapsulation");
console.log("📁 File location: EGPT/js/model/utils/PipelineData.js");
console.log("🎯 Vector Paradigm: EGPTNumber = Vector, BigInt = Scalar, EGPTMath = Algebra");

/**
 * PARTITION DATA CLASS
 * Represents a single segment (partition) of the number's entropy line.
 * This is the core data structure passed between Orchestrator, Algorithm, and SegmentManager.
 */
export class PartitionData {
    /**
     * Creates a new PartitionData instance
     * @param {object} config - Configuration object
     * @param {number} config.index - Sequential index of this partition in the main array
     * @param {BigInt} config.segment_start - Starting integer of the segment (inclusive)
     * @param {BigInt} config.segment_end - Ending integer of the segment (inclusive)
     * @param {BigInt} config.size - Number of integers in this segment
     * @param {EGPTNumber} config.H_entropy - Canonical entropy of this segment's size
     * @param {EGPTNumber} config.H_deviation - Signed canonical deviation from global average
     * @param {EGPTNumber} config.H_abs_deviation - Absolute canonical deviation
     * @param {boolean} [config.is_refined=false] - Flag indicating if segment has been replaced by children
     * @param {number} [config.refinement_level=0] - Hierarchical depth of this partition
     * @param {number} [config.parent_segment_index] - Index of parent partition this came from
     * @param {boolean} [config.is_converged=false] - True if segment achieved convergence (≤2 integers)
     * @param {boolean} [config.is_final_refined=false] - True if this is final result of convergence refinement
     * @param {string} [config.convergence_method] - Algorithm method that identified this as final refined segment
     * @param {number} [config.bit_length] - Bit length this segment represents (for logarithmic segments)
     * @param {BigInt} [config.interval_start] - Theoretical interval start (for logarithmic segments)
     * @param {BigInt} [config.interval_end] - Theoretical interval end (for logarithmic segments)
     * @param {boolean} [config.is_logarithmic=true] - Flag indicating if this is a logarithmic segment
     * @param {string} [config.algorithm_strategy] - Strategy used to identify this region (for refinement targets)
     * @param {number} [config.discontinuity_strength] - Strength of discontinuity if applicable (for refinement targets)
     * @param {string} [config.convergence_reason] - Explanation of why refinement should stop (for refinement targets)
     */
    constructor(config) {
        // Required properties validation
        this.validateRequiredProperties(config, [
            'index', 'segment_start', 'segment_end', 'size', 'H_entropy', 'H_deviation', 'H_abs_deviation'
        ]);

        // Core segment properties
        this.index = config.index;
        this.segment_start = config.segment_start;
        this.segment_end = config.segment_end;
        this.size = config.size;
        this.H_entropy = config.H_entropy;
        this.H_deviation = config.H_deviation;
        this.H_abs_deviation = config.H_abs_deviation;
        
        // Refinement properties
        this.is_refined = config.is_refined || false;
        this.refinement_level = config.refinement_level || 0;
        this.parent_segment_index = config.parent_segment_index;
        this.is_converged = config.is_converged || false;
        this.is_final_refined = config.is_final_refined || false;
        this.convergence_method = config.convergence_method;

        // Segmentation strategy properties
        this.bit_length = config.bit_length; // Can be undefined for equal subdivisions
        this.interval_start = config.interval_start; // Can be undefined for equal subdivisions
        this.interval_end = config.interval_end; // Can be undefined for equal subdivisions
        this.is_logarithmic = config.is_logarithmic !== undefined ? config.is_logarithmic : true;

        // Algorithm/refinement strategy properties (for refinement targets)
        this.algorithm_strategy = config.algorithm_strategy;
        this.discontinuity_strength = config.discontinuity_strength;
        this.convergence_reason = config.convergence_reason;

        // Validate data types
        this.validateDataTypes();
    }

    /**
     * Validates that required properties exist
     */
    validateRequiredProperties(config, required) {
        const missing = required.filter(prop => config[prop] === undefined || config[prop] === null);
        if (missing.length > 0) {
            throw new Error(`PartitionData missing required properties: ${missing.join(', ')}`);
        }
    }

    /**
     * Validates data types
     */
    validateDataTypes() {
        if (typeof this.index !== 'number') {
            throw new Error('PartitionData.index must be a number');
        }
        if (typeof this.segment_start !== 'bigint') {
            throw new Error('PartitionData.segment_start must be a BigInt');
        }
        if (typeof this.segment_end !== 'bigint') {
            throw new Error('PartitionData.segment_end must be a BigInt');
        }
        if (typeof this.size !== 'bigint') {
            throw new Error('PartitionData.size must be a BigInt');
        }
        
        // Logical consistency checks
        if (this.segment_start > this.segment_end) {
            throw new Error('PartitionData logical error: segment_start must be less than or equal to segment_end');
        }
        if (this.size <= 0n) {
            throw new Error('PartitionData logical error: size must be positive');
        }
        if (this.segment_end - this.segment_start + 1n !== this.size) {
            throw new Error('PartitionData logical error: size must equal (segment_end - segment_start + 1)');
        }
        
        if (!(this.H_entropy instanceof EGPTNumber)) {
            throw new Error('PartitionData.H_entropy must be an EGPTNumber instance');
        }
        if (!(this.H_deviation instanceof EGPTNumber)) {
            throw new Error('PartitionData.H_deviation must be an EGPTNumber instance');
        }
        if (!(this.H_abs_deviation instanceof EGPTNumber)) {
            throw new Error('PartitionData.H_abs_deviation must be an EGPTNumber instance');
        }

        // Validate optional properties when they exist
        if (this.bit_length !== undefined && typeof this.bit_length !== 'number') {
            throw new Error('PartitionData.bit_length must be a number when provided');
        }
        if (this.interval_start !== undefined && typeof this.interval_start !== 'bigint') {
            throw new Error('PartitionData.interval_start must be a BigInt when provided');
        }
        if (this.interval_end !== undefined && typeof this.interval_end !== 'bigint') {
            throw new Error('PartitionData.interval_end must be a BigInt when provided');
        }
        if (typeof this.is_logarithmic !== 'boolean') {
            throw new Error('PartitionData.is_logarithmic must be a boolean');
        }
        if (this.algorithm_strategy !== undefined && typeof this.algorithm_strategy !== 'string') {
            throw new Error('PartitionData.algorithm_strategy must be a string when provided');
        }
        if (this.discontinuity_strength !== undefined && typeof this.discontinuity_strength !== 'number') {
            throw new Error('PartitionData.discontinuity_strength must be a number when provided');
        }
        if (this.convergence_reason !== undefined && typeof this.convergence_reason !== 'string') {
            throw new Error('PartitionData.convergence_reason must be a string when provided');
        }
    }

    /**
     * Creates a deep copy of this PartitionData
     * @returns {PartitionData} Cloned instance
     */
    clone() {
        return new PartitionData({
            index: this.index,
            segment_start: this.segment_start,
            segment_end: this.segment_end,
            size: this.size,
            H_entropy: this.H_entropy.clone(),
            H_deviation: this.H_deviation.clone(),
            H_abs_deviation: this.H_abs_deviation.clone(),
            is_refined: this.is_refined,
            refinement_level: this.refinement_level,
            parent_segment_index: this.parent_segment_index,
            is_converged: this.is_converged,
            is_final_refined: this.is_final_refined,
            convergence_method: this.convergence_method,
            bit_length: this.bit_length,
            interval_start: this.interval_start,
            interval_end: this.interval_end,
            is_logarithmic: this.is_logarithmic,
            algorithm_strategy: this.algorithm_strategy,
            discontinuity_strength: this.discontinuity_strength,
            convergence_reason: this.convergence_reason
        });
    }

    /**
     * Checks if a given integer is contained within this segment
     * @param {BigInt} value - Integer to check
     * @returns {boolean} True if value is in [segment_start, segment_end]
     */
    contains(value) {
        return value >= this.segment_start && value <= this.segment_end;
    }

    /**
     * Checks if this partition has achieved convergence (≤2 integers)
     * @returns {boolean} True if partition has achieved optimal convergence
     */
    hasAchievedConvergence() {
        return this.size <= 2n;
    }

    /**
     * Returns a human-readable string representation
     * @returns {string} Formatted string
     */
    toString() {
        const segmentationType = this.is_logarithmic ? 'log' : 'equal';
        const bitInfo = this.bit_length !== undefined ? ` bit:${this.bit_length}` : '';
        const strategyInfo = this.algorithm_strategy ? ` strategy:${this.algorithm_strategy}` : '';
        return `PartitionData[${this.index}]: [${this.segment_start}, ${this.segment_end}] (size: ${this.size}, ${segmentationType}${bitInfo}${strategyInfo})`;
    }



    /**
     * Factory method to create PartitionData as a refinement region (algorithm decision)
     * @param {object} config - Refinement region configuration
     * @param {BigInt} config.start - Starting integer of refinement region (inclusive)
     * @param {BigInt} config.end - Ending integer of refinement region (inclusive)
     * @param {BigInt} config.size - Total number of integers in the region
     * @param {number} config.parentIndex - Index of primary parent partition being replaced
     * @param {string} [config.algorithm_strategy] - Strategy used to identify this region
     * @param {number} [config.discontinuity_strength] - Strength of discontinuity if applicable
     * @param {boolean} [config.is_converged=false] - True if region achieved convergence
     * @param {string} [config.convergence_reason] - Explanation of why refinement should stop
     * @returns {PartitionData} New PartitionData instance configured as a refinement region
     */
    static asRefinementRegion(config) {
        // Create minimal PartitionData with dummy entropy values for refinement decisions
        const dummyEntropy = EGPTNumber.fromBigInt(1n);
        
        return new PartitionData({
            index: config.parentIndex, // Use parentIndex as the index for now
            segment_start: config.start,
            segment_end: config.end,
            size: config.size,
            H_entropy: dummyEntropy,
            H_deviation: dummyEntropy,
            H_abs_deviation: dummyEntropy,
            parent_segment_index: config.parentIndex,
            is_converged: config.is_converged || false,
            algorithm_strategy: config.algorithm_strategy,
            discontinuity_strength: config.discontinuity_strength,
            convergence_reason: config.convergence_reason,
            is_logarithmic: false // Refinement regions are typically equal subdivisions
        });
    }

    /**
     * VALIDATION METHODS
     * Required by UI integration layer for pipeline data validation
     */

    /**
     * Validates this PartitionData instance
     * @returns {boolean} True if this instance is valid
     */
    isValid() {
        try {
            return (
                typeof this.index === 'number' &&
                typeof this.segment_start === 'bigint' &&
                typeof this.segment_end === 'bigint' &&
                typeof this.size === 'bigint' &&
                this.H_entropy instanceof EGPTNumber &&
                this.H_deviation instanceof EGPTNumber &&
                this.H_abs_deviation instanceof EGPTNumber &&
                this.segment_start <= this.segment_end &&
                this.size > 0n
            );
        } catch (error) {
            return false;
        }
    }

    /**
     * Static validation method for analysis data containing partition arrays
     * @param {Array|object} analysisData - Division analysis data from orchestrator
     * @returns {boolean} True if analysis data is valid for UI consumption
     */
    static isValidAnalysisData(analysisData) {
        try {
            if (!analysisData) return false;
            
            // Handle array of raw partition data objects (from orchestrator)
            if (Array.isArray(analysisData)) {
                return analysisData.length > 0 && analysisData.every(partition => {
                    // Check if it's already a PartitionData instance
                    if (partition instanceof PartitionData) {
                        return partition.isValid();
                    }
                    
                    // Check if raw object has required properties for conversion
                    const requiredProps = ['index', 'segment_start', 'segment_end', 'size'];
                    return requiredProps.every(prop => 
                        partition.hasOwnProperty(prop) && partition[prop] !== null && partition[prop] !== undefined
                    );
                });
            }
            
            // Handle object with partitions array
            if (typeof analysisData === 'object' && analysisData.partitions) {
                return Array.isArray(analysisData.partitions) && 
                       analysisData.partitions.length > 0 &&
                       this.isValidAnalysisData(analysisData.partitions);
            }
            
            return false;
        } catch (error) {
            return false;
        }
    }
}



/**
 * NUMBER STRUCTURE CLASS
 * Contains the results of the factor testing stage.
 * Consolidates both individual factors and factor pairs into a single structure.
 */
export class NumberStructure {
    /**
     * Creates a new NumberStructure instance
     * @param {object} config - Configuration object
     */
    constructor(config = {}) {
        this.performed = config.performed || false;
        this.k_is_prime = config.k_is_prime || false;
        this.factors_found = config.factors_found || [];
        this.traditional_primality_test = config.traditional_primality_test || 'unknown';
        this.fully_factorized = config.fully_factorized || false;
        this.egpt_traditional_agree = config.egpt_traditional_agree || 'unknown';
        this.segments_tested = config.segments_tested || 0;
        this.total_integers_tested = config.total_integers_tested || 0;
        this.success_status = config.success_status || 'NO_FACTORS';
        this.tested_converged_segments = config.tested_converged_segments || false;
        this.converged_segments_count = config.converged_segments_count || 0;
        this.sqrt_optimization = config.sqrt_optimization || false;
        this.sqrt_k = config.sqrt_k || 0n;
        this.has_smaller_factor = config.has_smaller_factor || false;

        this.validateDataTypes();
    }

    validateDataTypes() {
        if (typeof this.performed !== 'boolean') {
            throw new Error('NumberStructure.performed must be a boolean');
        }
        if (typeof this.k_is_prime !== 'boolean') {
            throw new Error('NumberStructure.k_is_prime must be a boolean');
        }
        if (!Array.isArray(this.factors_found)) {
            throw new Error('NumberStructure.factors_found must be an array');
        }
        if (!['agree', 'disagree', 'partial', 'unknown'].includes(this.egpt_traditional_agree)) {
            throw new Error('NumberStructure.egpt_traditional_agree must be agree|disagree|partial|unknown');
        }
        if (typeof this.segments_tested !== 'number') {
            throw new Error('NumberStructure.segments_tested must be a number');
        }
        if (typeof this.total_integers_tested !== 'number') {
            throw new Error('NumberStructure.total_integers_tested must be a number');
        }
        if (!['COMPLETE_SUCCESS', 'PARTIAL_SUCCESS', 'NO_FACTORS', 'NO_TESTABLE_SEGMENTS'].includes(this.success_status)) {
            throw new Error('NumberStructure.success_status must be COMPLETE_SUCCESS|PARTIAL_SUCCESS|NO_FACTORS|NO_TESTABLE_SEGMENTS');
        }
    }

    /**
     * Add a factor to the structure, automatically calculating and storing the cofactor
     * @param {BigInt} factor - The factor to add
     * @param {BigInt} k - The original number being factored
     * @param {BigInt} sqrt_k - Square root of k for optimization checks
     * @param {object} metadata - Additional metadata about where the factor was found
     */
    addFactor(factor, k, sqrt_k, metadata = {}) {
        if (typeof factor !== 'bigint') {
            throw new Error('Factor must be a BigInt');
        }
        if (typeof k !== 'bigint') {
            throw new Error('k must be a BigInt');
        }

        // Skip if factor is 1 or k itself
        if (factor <= 1n || factor >= k) {
            return;
        }

        // Verify this is actually a factor
        if (k % factor !== 0n) {
            console.warn(`⚠️ ${factor} is not a factor of ${k}`);
            return;
        }

        const cofactor = k / factor;

        // Check if we already have this factor or its cofactor
        const existing_factor = this.factors_found.find(f => f.factor === factor || f.factor === cofactor);
        if (existing_factor) {
            console.warn(`⚠️ Factor ${factor} or its cofactor ${cofactor} already exists`);
            return;
        }

        // Determine which is smaller and add both factor and cofactor info
        const smaller_factor = factor < cofactor ? factor : cofactor;
        const larger_factor = factor < cofactor ? cofactor : factor;
        const is_smaller_in_sqrt_range = smaller_factor <= sqrt_k;

        // Add the found factor with cofactor information
        this.factors_found.push({
            factor: factor,
            cofactor: cofactor,
            smaller_factor: smaller_factor,
            larger_factor: larger_factor,
            in_sqrt_range: factor <= sqrt_k,
            cofactor_in_sqrt_range: cofactor <= sqrt_k,
            found_smaller: factor === smaller_factor,
            ...metadata
        });

        // Update derived properties
        this.has_smaller_factor = this.factors_found.some(f => f.smaller_factor <= sqrt_k);
        this.success_status = this.has_smaller_factor ? "COMPLETE_SUCCESS" :
            this.factors_found.length > 0 ? "PARTIAL_SUCCESS" : "NO_FACTORS";
    }

    /**
     * Returns whether any factors were found
     * @returns {boolean} True if factors were discovered
     */
    hasFactors() {
        return this.factors_found.length > 0;
    }

    /**
     * Gets all factors as factor pairs (for backward compatibility)
     * @returns {Array} Array of factor pair objects
     */
    getFactorPairs() {
        return this.factors_found.map(f => ({
            smaller_factor: f.smaller_factor,
            larger_factor: f.larger_factor,
            product: f.smaller_factor * f.larger_factor,
            smaller_in_sqrt_range: f.smaller_factor <= this.sqrt_k,
            larger_in_sqrt_range: f.larger_factor <= this.sqrt_k,
            found_factor: f.factor
        }));
    }

    /**
     * Getter for factor_pairs (for backward compatibility with direct property access)
     */
    get factor_pairs() {
        return this.getFactorPairs();
    }

    /**
     * Gets all unique factors (both found factors and their cofactors)
     * @returns {Array<BigInt>} Array of all unique factors
     */
    getAllFactors() {
        const factors = new Set();
        this.factors_found.forEach(f => {
            factors.add(f.factor);
            factors.add(f.cofactor);
        });
        return Array.from(factors).sort((a, b) => a < b ? -1 : 1);
    }

    /**
     * Returns a summary string
     * @returns {string} Human-readable summary
     */
    getSummary() {
        if (!this.performed) return 'Factor testing not performed';
        if (this.k_is_prime) return 'Number is prime';
        if (this.hasFactors()) return `Found ${this.factors_found.length} factors`;
        return 'No factors found';
    }

    /**
     * VALIDATION METHODS
     * Required by UI integration layer for pipeline data validation
     */

    /**
     * Validates this NumberStructure instance
     * @returns {boolean} True if this instance is valid
     */
    isValid() {
        try {
            return (
                typeof this.performed === 'boolean' &&
                typeof this.k_is_prime === 'boolean' &&
                typeof this.segments_tested === 'number' &&
                typeof this.total_integers_tested === 'number' &&
                typeof this.success_status === 'string' &&
                Array.isArray(this.factors_found) &&
                this.segments_tested >= 0 &&
                this.total_integers_tested >= 0
            );
        } catch (error) {
            return false;
        }
    }

    /**
     * Static validation method for factor test results
     * @param {object} factorResults - Factor test results from orchestrator
     * @returns {boolean} True if factor results are valid for UI consumption
     */
    static isValidFactorResults(factorResults) {
        try {
            if (!factorResults) return false;
            
            // Handle NumberStructure instance
            if (factorResults instanceof NumberStructure) {
                return factorResults.isValid();
            }
            
            // Handle plain object with required properties
            if (typeof factorResults === 'object') {
                return (
                    typeof factorResults.performed === 'boolean' &&
                    typeof factorResults.k_is_prime === 'boolean' &&
                    (factorResults.factors_found === undefined || Array.isArray(factorResults.factors_found)) &&
                    (factorResults.success_status === undefined || typeof factorResults.success_status === 'string')
                );
            }
            
            return false;
        } catch (error) {
            return false;
        }
    }
}

/**
 * CHARTING METADATA CLASS
 * Replaces the ad hoc analysis_summary object created in SegmentManager.finalizeAnalysisForCharting
 * Focuses on statistical and visualization metadata
 */
export class ChartingMetadata {
    /**
     * Creates a new ChartingMetadata instance
     * @param {object} config - Configuration object
     */
    constructor(config = {}) {
        // Statistical analysis properties
        this.total_divisions = config.total_divisions || 0;
        this.unique_deviation_groups = config.unique_deviation_groups || 0;
        this.precision_mode = config.precision_mode || 'scaled_decimal'; // 'ordinal_ranking' | 'scaled_decimal'
        this.range_magnitude = config.range_magnitude || 0;
        
        // Refinement analysis properties
        this.has_refinement = config.has_refinement || false;
        this.refinement_levels_performed = config.refinement_levels_performed || 0;
        this.converged_segments_count = config.converged_segments_count || 0;
        this.final_refined_segments_count = config.final_refined_segments_count || 0;
        
        // Factor testing properties
        this.factor_testing_performed = config.factor_testing_performed || false;
        this.tested_converged_segments = config.tested_converged_segments || false;
        this.convergence_achieved = config.convergence_achieved || false;
        
        // Statistical metadata (preserved from EGPTStatData)
        this.statistics = config.statistics || {
            mean: '0',
            std_deviation: '0', 
            variance: '0',
            min: '0',
            max: '0'
        };

        this.validateDataTypes();
    }

    validateDataTypes() {
        if (typeof this.total_divisions !== 'number') {
            throw new Error('ChartingMetadata.total_divisions must be a number');
        }
        if (typeof this.unique_deviation_groups !== 'number') {
            throw new Error('ChartingMetadata.unique_deviation_groups must be a number');
        }
        if (!['ordinal_ranking', 'scaled_decimal'].includes(this.precision_mode)) {
            throw new Error('ChartingMetadata.precision_mode must be "ordinal_ranking" or "scaled_decimal"');
        }
        if (typeof this.range_magnitude !== 'number') {
            throw new Error('ChartingMetadata.range_magnitude must be a number');
        }
        if (typeof this.has_refinement !== 'boolean') {
            throw new Error('ChartingMetadata.has_refinement must be a boolean');
        }
        if (typeof this.factor_testing_performed !== 'boolean') {
            throw new Error('ChartingMetadata.factor_testing_performed must be a boolean');
        }
    }

    /**
     * Gets refinement effectiveness ratio
     * @returns {number} Ratio of converged segments to total refinement levels
     */
    getRefinementEffectiveness() {
        return this.refinement_levels_performed > 0 
            ? this.converged_segments_count / this.refinement_levels_performed 
            : 0;
    }

    /**
     * Checks if ultra-high precision mode was used
     * @returns {boolean} True if ordinal ranking was necessary
     */
    isUltraHighPrecision() {
        return this.precision_mode === 'ordinal_ranking';
    }

    /**
     * Returns a human-readable summary
     * @returns {string} Formatted summary
     */
    toString() {
        const mode = this.isUltraHighPrecision() ? 'Ultra-High Precision' : 'Standard Precision';
        const refinement = this.has_refinement ? `${this.refinement_levels_performed} levels` : 'None';
        return `Charting: ${this.total_divisions} divisions, ${mode}, Refinement: ${refinement}`;
    }
}

/**
 * ORCHESTRATOR METADATA CLASS
 * Replaces the ad hoc orchestrator_metadata object created in AnalysisOrchestrator.run
 * Focuses on orchestration and algorithm execution metadata
 */
export class OrchestratorMetadata {
    /**
     * Creates a new OrchestratorMetadata instance
     * @param {object} config - Configuration object
     */
    constructor(config = {}) {
        // Algorithm identification
        this.algorithm_used = config.algorithm_used || 'Unknown';
        this.algorithm_metadata = config.algorithm_metadata || null;
        this.algorithm_version = config.algorithm_version || null;
        
        // Orchestration configuration
        this.max_levels_allowed = config.max_levels_allowed || 0;
        this.refinement_levels_performed = config.refinement_levels_performed || 0;
        this.refinement_strategy = config.refinement_strategy || 'logarithmic_convergence';
        
        // Analysis scope
        this.analysis_range_start = config.analysis_range_start || 0n;
        this.analysis_range_end = config.analysis_range_end || 0n;
        this.analysis_range = config.analysis_range || `[0, ${this.analysis_range_end}]`;
        
        // Segment tracking
        this.initial_segments = config.initial_segments || 0;
        this.final_segments = config.final_segments || 0;
        this.segments_delta = this.final_segments - this.initial_segments;
        
        // Performance metrics
        this.execution_time_ms = config.execution_time_ms || 0;
        this.convergence_efficiency = config.convergence_efficiency || 0; // converged_segments / refinement_levels
        this.orchestrator_version = config.orchestrator_version || "Phase 2 - 4096-bit power-of-2 intervals";
        
        // Execution status
        this.completion_status = config.completion_status || 'unknown'; // 'success', 'max_levels_reached', 'algorithm_convergence', 'error'
        this.termination_reason = config.termination_reason || null;

        this.validateDataTypes();
    }

    validateDataTypes() {
        if (typeof this.algorithm_used !== 'string') {
            throw new Error('OrchestratorMetadata.algorithm_used must be a string');
        }
        if (typeof this.max_levels_allowed !== 'number') {
            throw new Error('OrchestratorMetadata.max_levels_allowed must be a number');
        }
        if (typeof this.refinement_levels_performed !== 'number') {
            throw new Error('OrchestratorMetadata.refinement_levels_performed must be a number');
        }
        if (typeof this.analysis_range_start !== 'bigint') {
            throw new Error('OrchestratorMetadata.analysis_range_start must be a BigInt');
        }
        if (typeof this.analysis_range_end !== 'bigint') {
            throw new Error('OrchestratorMetadata.analysis_range_end must be a BigInt');
        }
        if (typeof this.initial_segments !== 'number') {
            throw new Error('OrchestratorMetadata.initial_segments must be a number');
        }
        if (typeof this.final_segments !== 'number') {
            throw new Error('OrchestratorMetadata.final_segments must be a number');
        }
    }

    /**
     * Gets the analysis range size
     * @returns {BigInt} Size of analysis range
     */
    getAnalysisRangeSize() {
        return this.analysis_range_end - this.analysis_range_start + 1n;
    }

    /**
     * Calculates refinement efficiency
     * @returns {number} Ratio of refinement levels to max allowed
     */
    getRefinementEfficiency() {
        return this.max_levels_allowed > 0 
            ? this.refinement_levels_performed / this.max_levels_allowed 
            : 0;
    }

    /**
     * Checks if the orchestrator reached maximum levels
     * @returns {boolean} True if max levels was reached
     */
    reachedMaxLevels() {
        return this.refinement_levels_performed >= this.max_levels_allowed;
    }

    /**
     * Gets segment expansion factor
     * @returns {number} Ratio of final to initial segments
     */
    getSegmentExpansionFactor() {
        return this.initial_segments > 0 
            ? this.final_segments / this.initial_segments 
            : 0;
    }

    /**
     * Returns a human-readable summary
     * @returns {string} Formatted summary
     */
    toString() {
        const efficiency = (this.getRefinementEfficiency() * 100).toFixed(1);
        const expansion = this.getSegmentExpansionFactor().toFixed(1);
        return `Orchestrator: ${this.algorithm_used}, ${this.refinement_levels_performed}/${this.max_levels_allowed} levels (${efficiency}%), ${expansion}x expansion`;
    }

    /**
     * VALIDATION METHODS
     * Required by UI integration layer for pipeline data validation
     */

    /**
     * Static validation method for orchestrator metadata
     * @param {object} orchestratorMetadata - Orchestrator metadata from analysis
     * @returns {boolean} True if orchestrator metadata is valid for UI consumption
     */
    static isValidMetadata(orchestratorMetadata) {
        try {
            if (!orchestratorMetadata) return false;
            
            // Handle OrchestratorMetadata instance
            if (orchestratorMetadata instanceof OrchestratorMetadata) {
                return (
                    typeof orchestratorMetadata.algorithm_used === 'string' &&
                    typeof orchestratorMetadata.max_levels_allowed === 'number' &&
                    typeof orchestratorMetadata.refinement_levels_performed === 'number' &&
                    typeof orchestratorMetadata.execution_time_ms === 'number' &&
                    typeof orchestratorMetadata.completion_status === 'string' &&
                    orchestratorMetadata.max_levels_allowed >= 0 &&
                    orchestratorMetadata.refinement_levels_performed >= 0 &&
                    orchestratorMetadata.execution_time_ms >= 0
                );
            }
            
            // Handle plain object with required properties
            if (typeof orchestratorMetadata === 'object') {
                return (
                    typeof orchestratorMetadata.algorithm_used === 'string' &&
                    (orchestratorMetadata.execution_time_ms === undefined || typeof orchestratorMetadata.execution_time_ms === 'number') &&
                    (orchestratorMetadata.completion_status === undefined || typeof orchestratorMetadata.completion_status === 'string')
                );
            }
            
            return false;
        } catch (error) {
            return false;
        }
    }
}

/**
 * PIPELINE METADATA FACTORY
 * Utility functions for creating metadata objects from pipeline data
 */
export class PipelineMetadataFactory {
    
    /**
     * Creates ChartingMetadata from SegmentManager analysis data
     * @param {Array} finalDivisions - Array of PartitionData objects
     * @param {object} chartData - Chart data package from EGPTStatData
     * @param {object} factorTestResults - Factor testing results
     * @param {object} statistics - Statistical metadata
     * @returns {ChartingMetadata} Configured ChartingMetadata instance
     */
    static createChartingMetadata(finalDivisions, chartData, factorTestResults, statistics) {
        const convergedSegments = finalDivisions.filter(div => div.is_converged || div.is_final_refined);
        const refinementLevels = finalDivisions.filter(div => div.refinement_level !== undefined && div.refinement_level > 0);
        
        return new ChartingMetadata({
            total_divisions: finalDivisions.length,
            unique_deviation_groups: chartData.unique_groups_count,
            precision_mode: chartData.use_ordinal_ranking ? 'ordinal_ranking' : 'scaled_decimal',
            range_magnitude: chartData.range_magnitude,
            has_refinement: refinementLevels.length > 0,
            refinement_levels_performed: refinementLevels.length,
            converged_segments_count: convergedSegments.length,
            final_refined_segments_count: finalDivisions.filter(div => div.is_final_refined).length,
            factor_testing_performed: factorTestResults.performed || false,
            tested_converged_segments: factorTestResults.tested_converged_segments || false,
            convergence_achieved: convergedSegments.length > 0,
            statistics: statistics
        });
    }

    /**
     * Creates OrchestratorMetadata from orchestrator execution data
     * @param {object} algorithm - Algorithm instance
     * @param {object} config - Orchestrator configuration
     * @param {number} actualRefinementLevels - Actual refinement levels performed
     * @param {number} initialSegments - Initial segment count
     * @param {number} finalSegments - Final segment count
     * @param {BigInt} analysisRangeEnd - Analysis range end
     * @param {number} executionTimeMs - Execution time in milliseconds
     * @param {string} completionStatus - Completion status
     * @param {string} terminationReason - Reason for termination
     * @returns {OrchestratorMetadata} Configured OrchestratorMetadata instance
     */
    static createOrchestratorMetadata(
        algorithm, 
        config, 
        actualRefinementLevels, 
        initialSegments, 
        finalSegments, 
        analysisRangeEnd,
        executionTimeMs = 0,
        completionStatus = 'success',
        terminationReason = null
    ) {
        return new OrchestratorMetadata({
            algorithm_used: algorithm.getName(),
            algorithm_metadata: algorithm.getMetadata ? algorithm.getMetadata() : null,
            algorithm_version: algorithm.getVersion ? algorithm.getVersion() : null,
            max_levels_allowed: config.maxLevels,
            refinement_levels_performed: actualRefinementLevels,
            refinement_strategy: config.refinement_strategy || 'logarithmic_convergence',
            analysis_range_start: 0n,
            analysis_range_end: analysisRangeEnd,
            analysis_range: `[0, ${analysisRangeEnd}]`,
            initial_segments: initialSegments,
            final_segments: finalSegments,
            execution_time_ms: executionTimeMs,
            convergence_efficiency: actualRefinementLevels > 0 ? finalSegments / actualRefinementLevels : 0,
            completion_status: completionStatus,
            termination_reason: terminationReason
        });
    }
}

