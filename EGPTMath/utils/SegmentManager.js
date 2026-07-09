/**
 * SEGMENT MANAGER UTILITIES
 * Reusable, stateless functions for algorithmic segment analysis.
 * 
 * ARCHITECTURAL PRINCIPLE: This module provides the standardized toolbox
 * that any analysis algorithm can use. All functions are pure and stateless.
 * 
 * PEDAGOGICAL PRINCIPLE: Uses EGPT Vector/Scalar paradigm throughout.
 * EGPTNumber = Information Vectors, BigInt = Scalars, EGPTMath = Vector Algebra            is_adaptive_subdivision: seg.is_adaptive_subdivision || false // Flag for adaptive subdivisions
        });
    });

    console.log(`[SegmentManager] 📊 SEGMENT CALCULATED: ${division_analysis.length} divisions analyzed`);

    return {
        segment_start,
        segment_end,
        segment_size,
        H_segment,
        H_avg_division,
        D,
        division_analysis
    };
}Uses EGPT Vector/Scalar paradigm throughout.
 * EGPTNumber = Information Vectors, BigInt = Scalars, EGPTMath = Vector Algebra
 * 
 * @fileoverview Reusable segment analysis utilities for EGPT algorithms
 * @author EGPT Development Team
 * @since 2025-08-01
 */

// Import the EGPT production classes from the Vector/Scalar paradigm
import { EGPTNumber } from '../EGPTNumber.js';
import { EGPTMath } from '../EGPTMath.js';
import { EGPTStat } from '../stat/EGPTStat.js';
// --- MODIFICATION: Import EGPTStatData ---
import { EGPTStatData } from '../stat/EGPTStatData.js';
// Import standardized data structures
import { PartitionData, NumberStructure } from './PipelineData.js';
// Import standardized metadata classes
import { ChartingMetadata, PipelineMetadataFactory } from './PipelineData.js';

// Conditional import for isProbablyPrime
let isProbablyPrime;
try {
    // Try browser-specific crypto module first
    const module = await import('../../modules/big-int-crypto.esm.min.js');
    isProbablyPrime = module.isProbablyPrime;
    console.log("✅ SegmentManager: Using browser crypto module for primality testing");
} catch (error) {
    try {
        // Fallback to Node.js bigint-crypto-utils
        const { isProbablyPrime: nodePrime } = await import('bigint-crypto-utils');
        isProbablyPrime = nodePrime;
        console.log("✅ SegmentManager: Using bigint-crypto-utils for primality testing");
    } catch (nodeError) {
        // Final fallback for environments without crypto libraries
        isProbablyPrime = function (n, rounds = 10) {
            console.log("⚠️ SegmentManager: Using simple fallback primality test");
            if (n <= 1n) return false;
            if (n <= 3n) return true;
            if (n % 2n === 0n) return false;

            // Simple trial division
            const limit = Math.min(1000n, BigInt(Math.sqrt(Number(n))));
            for (let i = 3n; i <= limit; i += 2n) {
                if (n % i === 0n) return false;
            }
            return true; // Assume prime if no small factors found
        };
        console.log("⚠️ SegmentManager: Using simple fallback (crypto libraries unavailable)");
    }
}

console.log("🛠️ SEGMENT MANAGER: Reusable utilities for algorithmic analysis loaded.");
console.log("🎓 CANONICAL INFORMATION SPACE: Vector/Scalar paradigm");
console.log("📁 File location: EGPT/js/utils/SegmentManager.js");
console.log("🎯 Vector Paradigm: EGPTNumber = Vector, BigInt = Scalar, EGPTMath = Algebra");

/**
 * ADAPTIVE BINARY SUBDIVISION HELPER
 * Recursively subdivides large segments using binary subdivision until target size is reached.
 * This ensures convergence to 1-bit intervals while maintaining logarithmic structure.
 * 
 * @param {BigInt} start - Segment start (inclusive)
 * @param {BigInt} end - Segment end (inclusive)
 * @param {BigInt} target_max_size - Target maximum segment size
 * @param {number} original_bit_length - Original bit length for reference
 * @returns {Array} Array of subdivision objects
 */
function adaptiveBinarySubdivision(start, end, target_max_size, original_bit_length) {
    const total_size = end - start + 1n;

    // Base case: segment is small enough
    if (total_size <= target_max_size) {
        const H_entropy = EGPTNumber.fromBigInt(total_size);

        return [{
            index: 0, // Will be reassigned by caller
            position: start,
            size: total_size,
            H_entropy: H_entropy,
            interval_start: start,
            interval_end: end,
            bit_length: original_bit_length,
            is_adaptive_subdivision: true
        }];
    }

    // Recursive case: binary subdivision
    const mid_point = start + (end - start) / 2n;

    // Subdivide left and right halves
    const left_subdivisions = adaptiveBinarySubdivision(
        start,
        mid_point,
        target_max_size,
        original_bit_length
    );

    const right_subdivisions = adaptiveBinarySubdivision(
        mid_point + 1n,
        end,
        target_max_size,
        original_bit_length
    );

    return [...left_subdivisions, ...right_subdivisions];
}

/**
 * ANALYZE SEGMENT ENTROPY UNIFORMITY
 * Core mathematical function that analyzes entropy uniformity for a specific integer range.
 * This is the building block for both initial analysis and segment refinement.
 * 
 * EXTRACTED from EntropyUniformity.js analyzeSegmentEntropyUniformity function
 * 
 * @param {BigInt} segment_start - Starting integer of the segment (inclusive)
 * @param {BigInt} segment_end - Ending integer of the segment (inclusive) 
 * @param {BigInt} original_D - Optional: Use original D for uniform refinement
 * @param {EGPTNumber} global_H_avg_division - Optional: Global reference entropy
 * @param {BigInt} full_k - Optional: The full composite number k for global entropy calculation
 * @returns {Object} Segment analysis data with entropy calculations
 */
export function analyzeSegment(segment_start, segment_end, original_D = null, global_H_avg_division = null, full_k = null) {
    const segment_size = segment_end - segment_start + 1n;
    console.log(`[SegmentManager] 🔍 SEGMENT ANALYSIS: Range [${segment_start}, ${segment_end}] (size: ${segment_size})`);

    // STEP 1: Encode segment entropy (RET Iron Law application)
    const H_segment = EGPTNumber.fromBigInt(segment_size);

    // STEP 2: Determine number of logarithmic divisions
    let D;
    if (original_D !== null) {
        // Use the original D for uniform hierarchical refinement
        D = original_D;
        console.log(`[SegmentManager] 🎯 UNIFORM REFINEMENT: Using original D = ${D} for consistent subdivision`);
    } else {
        // Calculate D based on logarithmic bit-length coverage: log2(segment_end)
        const max_bit_length = EGPTMath.getIntegerBitLength(EGPTNumber.fromBigInt(segment_end));
        D = BigInt(max_bit_length);
        console.log(`[SegmentManager] 📊 LOGARITHMIC D: From max bit length = ${D} (covers 2^0 to 2^${D - 1n})`);
    }

    if (D <= 1n) {
        throw new Error(`Segment [${segment_start}, ${segment_end}] is too small to analyze (must have > 1 division).`);
    }

    // STEP 3: Choose subdivision strategy based on segment characteristics
    // PHASE 2 FIX: For refinement levels, use equal subdivisions instead of logarithmic
    const use_equal_subdivision = (original_D !== null); // Any refinement level gets equal subdivisions

    let final_segment_entropies; // Will be assigned based on subdivision strategy
    if (use_equal_subdivision) {
        console.log(`[SegmentManager] 🎯 EQUAL SUBDIVISION: Refinement level will use equal subdivisions for convergence`);

        // PHASE 2 FIX: Create equal-sized subdivisions for progressive convergence
        // Use a reasonable number of subdivisions (8-16) to enable algorithm choice
        const target_subdivision_count = segment_size <= 4n ? Number(segment_size) : 
                                        segment_size <= 64n ? 8 : 
                                        16; // More subdivisions for larger ranges
                                        
        const subdivision_size = segment_size / BigInt(target_subdivision_count);
        const remainder = segment_size % BigInt(target_subdivision_count);

        console.log(`[SegmentManager] 🔬 EQUAL SEGMENTATION: Creating ${target_subdivision_count} equal subdivisions (size ~${subdivision_size} each)`);

        // Create equal subdivisions
        const segment_entropies = [];
        let current_start = segment_start;
        
        for (let i = 0; i < target_subdivision_count; i++) {
            // Calculate end position for this subdivision
            const base_size = subdivision_size;
            const extra = i < remainder ? 1n : 0n; // Distribute remainder across first few segments
            const current_size = base_size + extra;
            const current_end = current_start + current_size - 1n;
            
            // Ensure we don't exceed the segment boundary
            const actual_end = current_end > segment_end ? segment_end : current_end;
            const actual_size = actual_end - current_start + 1n;

            const H_segment_size = EGPTNumber.fromBigInt(actual_size);
            segment_entropies.push({
                index: BigInt(i),
                position: current_start,
                size: actual_size,
                H_entropy: H_segment_size,
                interval_start: current_start,
                interval_end: actual_end,
                bit_length: Number(EGPTMath.getIntegerBitLength(EGPTNumber.fromBigInt(actual_end))),
                is_equal_subdivision: true // Flag for equal subdivisions
            });

            console.log(`[SegmentManager]    📊 Equal Segment ${i}: [${current_start}, ${actual_end}] (size: ${actual_size})`);

            current_start = actual_end + 1n;
            
            // Break if we've covered the entire range
            if (actual_end >= segment_end) break;
        }

        // Use equal subdivisions for the rest of the processing
        final_segment_entropies = segment_entropies;

    } else {
        // Original logarithmic approach for larger segments
        console.log(`[SegmentManager] 🔬 LOGARITHMIC SEGMENTATION: Creating ${D} segments based on bit-length intervals`);

        // STEP 4: First pass - collect all segment entropies (LOGARITHMIC approach)
        const segment_entropies = [];

        for (let i = 0n; i < D; i++) {
            // Define logarithmic interval bounds: [2^i, 2^(i+1) - 1]
            const interval_start = 2n ** i;
            let interval_end = (2n ** (i + 1n)) - 1n;
            
            // SQRT(K) OPTIMIZATION: Cap the final interval at segment_end (sqrt(k))
            // This ensures we only search for the smaller factor, not the larger one
            if (interval_end > segment_end) {
                interval_end = segment_end;
                console.log(`[SegmentManager]    📐 SQRT(K) CAP: Final interval ${i} capped at ${segment_end} (sqrt(k) boundary)`);
            }

            // Intersect with the actual segment bounds
            const actual_start = interval_start < segment_start ? segment_start : interval_start;
            const actual_end = interval_end > segment_end ? segment_end : interval_end;

            // Only include if there's a valid intersection
            if (actual_start <= actual_end) {
                const current_size = actual_end - actual_start + 1n;

                // Calculate H(segment_size) - this matches the OLD working code approach
                const H_segment_size = EGPTNumber.fromBigInt(current_size);
                segment_entropies.push({
                    index: i,
                    position: actual_start,
                    size: current_size,
                    H_entropy: H_segment_size,
                    interval_start: interval_start,  // Store theoretical interval for reference
                    interval_end: interval_end,      // Store theoretical interval for reference
                    bit_length: Number(i)            // Bit length this segment represents
                });

                console.log(`[SegmentManager]    📊 Segment ${i}: [${actual_start}, ${actual_end}] (size: ${current_size}, bit-length: ${i})`);
            }
        }


        // Use enhanced segments for the rest of the processing
        final_segment_entropies = segment_entropies;
    } // Close the else block for logarithmic segmentation

    // STEP 5: Calculate reference entropy (average of all segment entropies at this level)
    let H_avg_division;
    if (global_H_avg_division !== null) {
        // Use global reference for hierarchical refinement
        H_avg_division = global_H_avg_division;
        console.log(`[SegmentManager] 🌍 GLOBAL REFERENCE: Using H(segment_avg) from initial level`);
    } else {
        // Calculate H(segment_avg) = average entropy of all segments at this level
        let total_entropy = EGPTNumber.fromBigInt(0n);
        final_segment_entropies.forEach(seg => {
            total_entropy = EGPTMath.add(total_entropy, seg.H_entropy);
        });
        H_avg_division = EGPTMath.divide(total_entropy, EGPTNumber.fromBigInt(BigInt(final_segment_entropies.length)));
        console.log(`[SegmentManager] 📊 LOCAL REFERENCE: Calculated H(segment_avg) = ${H_avg_division.toString().slice(0, 30)}... for this level`);
    }

    // STEP 6: Compute deviations for each segment (ENHANCED approach with adaptive subdivisions)
    const division_analysis = [];

    final_segment_entropies.forEach((seg, array_index) => {
        // Calculate deviation: H(segment_size) - H(segment_avg)
        const H_deviation = EGPTMath.subtract(seg.H_entropy, H_avg_division);

        // Get absolute deviation (canonical space)
        const deviation_rational = H_deviation.getRationalParts();
        const H_abs_deviation = deviation_rational.numerator < 0n ?
            EGPTMath.subtract(EGPTNumber.fromBigInt(0n), H_deviation) :
            H_deviation;

        // Store analysis data using standardized PartitionData class
        const partitionData = new PartitionData({
            index: array_index,
            segment_start: seg.position,
            segment_end: seg.position + seg.size - 1n,
            size: seg.size,
            H_entropy: seg.H_entropy,
            H_deviation: H_deviation,
            H_abs_deviation: H_abs_deviation,
            is_refined: false,
            refinement_level: 0,
            is_converged: false,
            // Segmentation strategy metadata
            bit_length: seg.bit_length,
            interval_start: seg.interval_start,
            interval_end: seg.interval_end,
            is_logarithmic: !seg.is_adaptive_subdivision
        });

        division_analysis.push(partitionData);
    });

    console.log(`[SegmentManager] 📊 SEGMENT CALCULATED: ${division_analysis.length} divisions analyzed`);

    return {
        segment_start,
        segment_end,
        segment_size,
        H_segment,
        H_avg_division,
        D,
        division_analysis
    };
}

/**
 * MERGE REFINED SEGMENTS INTO PARENT ANALYSIS
 * Combines original coarse analysis with refined segment data for enhanced resolution.
 * 
 * EXTRACTED from EntropyUniformity.js mergeRefinedData function
 * 
 * @param {Array} parentDivisions - Original division analysis array
 * @param {Object} refinedSegmentData - Refined analysis data for a specific segment
 * @param {number} parentIndex - Index of the parent segment being replaced
 * @returns {Array} Merged division analysis with enhanced resolution
 */
export function mergeRefinedSegments(parentDivisions, refinedSegmentData, parentIndex) {
    if (!refinedSegmentData) {
        console.log(`[SegmentManager] ⚠️ No refined data provided, returning original divisions`);
        return parentDivisions;
    }

    const merged_divisions = [];
    const num_child_segments = refinedSegmentData.division_analysis.length;

    console.log(`[SegmentManager] 🔬 MERGING: Replacing 1 parent segment with ${num_child_segments} child segments`);
    console.log(`[SegmentManager] 📊 Expected total: ${parentDivisions.length} - 1 + ${num_child_segments} = ${parentDivisions.length - 1 + num_child_segments}`);

    // STEP 1: Copy all segments before the refined segment (unchanged)
    for (const div of parentDivisions) {
        if (div.index < parentIndex) {
            merged_divisions.push({ ...div }); // Clone to avoid mutation
        }
    }

    // STEP 2: Insert refined subdivisions (replacing the parent segment)
    // Assign new sequential indices starting from where parent was
    let current_index = parentIndex;
    for (const refined_div of refinedSegmentData.division_analysis) {
        const new_refined_div = { ...refined_div };
        new_refined_div.index = current_index++;
        new_refined_div.parent_segment_index = parentIndex; // Track parent relationship
        merged_divisions.push(new_refined_div);
    }

    // STEP 3: Copy all segments after the refined segment with adjusted indices
    // Need to shift indices by (num_child_segments - 1) to account for the replacement
    const index_shift = num_child_segments - 1;
    for (const div of parentDivisions) {
        if (div.index > parentIndex && !div.is_refined) {
            const adjusted_div = { ...div };
            adjusted_div.index = div.index + index_shift;
            merged_divisions.push(adjusted_div);
        }
    }

    console.log(`[SegmentManager] 🔗 MERGED RESULT: ${parentDivisions.length} original → ${merged_divisions.length} enhanced (increased by ${merged_divisions.length - parentDivisions.length})`);
    return merged_divisions;
}

/**
 * FINALIZE ANALYSIS DATA FOR CHARTING
 * Prepares the final, compiled analysis data for the charting layer.
 * This version is refactored to use EGPTStatData for robust normalization.
 * 
 * ENHANCEMENT: Integrates EGPTStatData to handle extreme values (-1000 for exact factors)
 * that would otherwise cause Chart.js infinite line/redraw loop issues.
 * 
 * @param {BigInt} k - Original integer being analyzed
 * @param {Array} finalDivisions - Final division analysis data (potentially refined)
 * @param {BigInt} initialD - Initial D value for reference
 * @param {EGPTNumber} global_H_avg - Global reference entropy
 * @param {Function} factorTestFn - Function to test segments for factors
 * @returns {Object} Complete data object that EGPTCharting.js expects
 */
export async function finalizeAnalysisForCharting(k, finalDivisions, initialD, global_H_avg, factorTestFn) {
    console.log(`[SegmentManager] 📊 FINALIZING with EGPTStatData: ${finalDivisions.length} divisions for visualization`);

    if (finalDivisions.length === 0) {
        return { k, D: initialD, division_analysis: [], deviation_values_for_chart: [] };
    }

    // --- MODIFICATION START: Integrate EGPTStatData ---

    // 1. Collect all raw H_abs_deviation values into an array.
    const raw_deviations = finalDivisions.map(div => div.H_abs_deviation);

    // 2. Create an EGPTStatData instance to handle all statistical processing and normalization.
    const statData = EGPTStatData.fromArray(raw_deviations);

    // 3. Extract the processed, chart-ready data.
    // The EGPTStatData object has already decided whether to use scaling or ordinal ranking.
    const {
        deviation_values_for_chart,
        use_ordinal_ranking,
        unique_groups_count,
        scale_factor,
        range_magnitude
    } = statData.getChartData();

    // --- MODIFICATION END ---

    console.log(`[SegmentManager] Normalization complete. Mode: ${use_ordinal_ranking ? 'Ordinal Ranking' : 'Scaled Decimal'}.`);

    // 4. CRITICAL FIX: Perform factor testing ONLY on segments marked as converged by the algorithm
    // This prevents false positives and ensures we test only the algorithm's final refined segments
    const convergedSegments = [...finalDivisions]
        .filter(s => s.is_converged === true)
        .filter(s => s.size <= 1000n && s.size > 1n);

    console.log(`[SegmentManager] 🎯 CONVERGED SEGMENTS ONLY: Found ${convergedSegments.length} segments marked as converged by algorithm`);
    
    if (convergedSegments.length === 0) {
        console.log(`[SegmentManager] ⚠️  No converged segments found - algorithm may not have achieved convergence`);
        console.log(`[SegmentManager] 📊 Total segments: ${finalDivisions.length}, with convergence flags: ${finalDivisions.filter(s => s.is_converged).length}`);
    }

    const segmentsToTest = convergedSegments.length > 0 ? convergedSegments : [];
    const factor_test_results = await factorTestFn(k, segmentsToTest);

    // 5. Convert raw segments to PartitionData instances before returning
    console.log(`[SegmentManager] 🔄 Converting ${finalDivisions.length} raw segments to PartitionData instances`);
    const partitionDataArray = finalDivisions.map(segment => new PartitionData(segment));
    console.log(`[SegmentManager] ✅ Created ${partitionDataArray.length} PartitionData instances`);

    // 6. Assemble the final, enriched data object for the UI.
    const final_result = {
        // Input parameters
        k,
        D: initialD,

        // Mathematical analysis results
        H_k: EGPTNumber.fromBigInt(k),
        H_avg_division: global_H_avg,
        division_analysis: partitionDataArray,  // ✅ Now PartitionData[] instances instead of raw objects
        deviations_H: raw_deviations, // Keep original deviations for tooltips

        // Normalization and display information from EGPTStatData
        use_ordinal_ranking,
        unique_groups_count,
        scale_factor,
        range_magnitude,
        deviation_values_for_chart,

        // Factor testing results
        factor_test_results,

        // ✅ STANDARDIZED METADATA: Use ChartingMetadata class instead of ad hoc analysis_summary
        charting_metadata: PipelineMetadataFactory.createChartingMetadata(
            finalDivisions,
            {
                unique_groups_count,
                use_ordinal_ranking,
                range_magnitude
            },
            factor_test_results,
            {
                mean: statData.mean.toMathString(),
                std_deviation: statData.std_deviation.toMathString(),
                variance: statData.variance.toMathString(),
                min: statData.min_value.toMathString(),
                max: statData.max_value.toMathString(),
            }
        )
    };

    console.log(`[SegmentManager] Final data object created for UI with standardized ChartingMetadata.`);

    return final_result;
}

/**
 * TEST SEGMENTS FOR FACTORS
 * Tests a given set of segments for actual factors.
 * 
 * EXTRACTED from EntropyUniformity.js finalFactorTest function
 * 
 * @param {BigInt} k - The number to be factored
 * @param {Array} segmentsToTest - Array of segment objects to test for factors
 * @returns {Object} Factor testing result object
 */
export async function testSegmentsForFactors(k, segmentsToTest) {
    console.log(`[SegmentManager] 🔍 Testing ${segmentsToTest.length} segments for factors of ${k}`);

    // Calculate sqrt(k) optimization boundary
    const sqrt_k = BigInt(Math.ceil(Math.sqrt(Number(k))));
    console.log(`[SegmentManager] 📐 SQRT(K) = ${sqrt_k} (search optimization boundary)`);

    // Find testable segments, prioritizing those in sqrt(k) range for optimization
    const testable_segments = segmentsToTest.filter(seg => seg.size <= 1000n && seg.size > 1n);

    // Separate segments: those in sqrt(k) range vs others
    const sqrt_range_segments = testable_segments
        .filter(seg => seg.segment_start <= sqrt_k && seg.segment_end >= 2n)
        .sort((a, b) => Number(a.size) - Number(b.size));

    const other_segments = testable_segments
        .filter(seg => seg.segment_start > sqrt_k || seg.segment_end < 2n)
        .sort((a, b) => Number(a.size) - Number(b.size));

    // Prioritize sqrt(k) range segments, then add others if needed
    const refined_segments = [
        ...sqrt_range_segments.slice(0, 3), // Up to 3 from sqrt(k) range
        ...other_segments.slice(0, 2)       // Up to 2 from other ranges
    ].slice(0, 5); // Maximum 5 total

    console.log(`[SegmentManager] 🎯 Testing ${sqrt_range_segments.length} segments in sqrt(k) range, ${Math.min(2, other_segments.length)} elsewhere`);

    if (refined_segments.length === 0) {
        console.log("[SegmentManager] ⚠️ No segments small enough (≤1000 integers) for factor testing");
        return new NumberStructure({
            performed: false,
            success_status: "NO_TESTABLE_SEGMENTS",
            sqrt_optimization: true,
            sqrt_k: sqrt_k
        });
    }

    // Test if k is prime
    let k_is_prime;
    try {
        const primeTest = isProbablyPrime(k, 10); // 10 rounds for high confidence
        k_is_prime = (primeTest && typeof primeTest.then === 'function') ? await primeTest : primeTest;
    } catch (error) {
        console.log(`[SegmentManager] ⚠️ Primality test failed: ${error.message}, assuming composite`);
        k_is_prime = false;
    }
    console.log(`[SegmentManager] 🔢 Primality test: k is ${k_is_prime ? 'PRIME' : 'COMPOSITE'}`);

    // Create NumberStructure for factor tracking
    const numberStructure = new NumberStructure({
        performed: true,
        k_is_prime: k_is_prime,
        segments_tested: refined_segments.length,
        total_integers_tested: refined_segments.reduce((sum, seg) => sum + Number(seg.size), 0),
        sqrt_optimization: true,
        sqrt_k: sqrt_k
    });

    let egpt_found_factor = false;

    // Test each refined segment
    for (const segment of refined_segments) {
        console.log(`[SegmentManager] 🔬 Testing segment [${segment.segment_start}, ${segment.segment_end}] (size: ${segment.size})`);

        // Test each integer in the segment
        for (let p_candidate = segment.segment_start; p_candidate <= segment.segment_end; p_candidate++) {
            if (p_candidate <= 1n) continue; // Skip 0 and 1

            if (k % p_candidate === 0n) {
                const cofactor = k / p_candidate;
                
                // Add factor to NumberStructure with metadata
                numberStructure.addFactor(p_candidate, k, sqrt_k, {
                    segment_index: segment.index,
                    segment_size: Number(segment.size),
                    refinement_level: segment.refinement_level || 0
                });

                egpt_found_factor = true;

                console.log(`[SegmentManager] 🎉 FACTOR FOUND: ${p_candidate} × ${cofactor} = ${k}`);
                console.log(`[SegmentManager] 🎯 Smaller factor ≤ sqrt(k): ${Math.min(Number(p_candidate), Number(cofactor)) <= Number(sqrt_k) ? '✅ YES' : '❌ NO'}`);

                // For efficiency, stop after finding the first factor in this segment
                break;
            }
        }

        // If we found a factor, we can stop testing other segments
        if (egpt_found_factor) break;
    }

    console.log(`[SegmentManager] 📊 FACTOR TEST COMPLETE:`);
    console.log(`[SegmentManager]    🔢 k is prime: ${numberStructure.k_is_prime}`);
    console.log(`[SegmentManager]    🎯 Factors found: ${numberStructure.factors_found.length}`);
    console.log(`[SegmentManager]    🏆 Success status: ${numberStructure.success_status}`);
    console.log(`[SegmentManager]    📈 Segments tested: ${numberStructure.segments_tested}`);

    return numberStructure;
}
