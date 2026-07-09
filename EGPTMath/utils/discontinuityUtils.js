/**
 * DISCONTINUITY UTILITIES
 * Reusable helper functions for Step Discontinuity algorithm analysis.
 * 
 * ARCHITECTURAL PRINCIPLE: This module provides specialized utilities
 * for detecting and analyzing step discontinuities in entropy patterns.
 * 
 * PEDAGOGICAL PRINCIPLE: Uses EGPT Vector/Scalar paradigm throughout.
 * EGPTNumber = Information Vectors, BigInt = Scalars, EGPTMath = Vector Algebra
 * 
 * @fileoverview Specialized utilities for step discontinuity detection
 * @author EGPT Development Team
 * @since 2025-08-01
 */

// Import the EGPT production classes from the Vector/Scalar paradigm
import { EGPTNumber } from '../../model/EGPTNumber.js';
import { EGPTMath } from '../../model/EGPTMath.js';
import { EGPTStat } from '../../model/stat/EGPTStat.js';

console.log("🛠️ DISCONTINUITY UTILS: EGPT-Compliant Step Discontinuity detection loaded.");
console.log("🎓 CANONICAL INFORMATION SPACE: Vector/Scalar paradigm");
console.log("📁 File location: EGPT/js/model/utils/discontinuityUtils.js");
console.log("🎯 Vector Paradigm: EGPTNumber = Vector, BigInt = Scalar, EGPTStat = Statistics");

/**
 * IDENTIFY STEP DISCONTINUITY REGIONS
 * Finds the single largest step in entropy deviation changes, indicating factor location.
 * 
 * MATHEMATICAL PRINCIPLE: The largest step discontinuity IS the factor location,
 * regardless of absolute magnitude. No thresholds - just find the maximum step.
 * Uses EGPT Vector/Scalar paradigm with EGPTStat for ultra-high precision.
 * 
 * @param {Array} division_analysis - Array of segment analysis objects
 * @returns {Array} Array with the single largest step discontinuity (or empty)
 */
export function identifyStepDiscontinuities(division_analysis) {
    console.log(`[discontinuityUtils] 🎯 EGPT-COMPLIANT STEP DETECTION: Analyzing ${division_analysis.length} segments`);
    console.log(`[discontinuityUtils] 📊 Method: EGPTStat → Find maximum deviation change (no thresholds)`);
    
    if (division_analysis.length < 2) {
        console.log(`[discontinuityUtils] ⚠️  Need at least 2 segments for step detection`);
        return [];
    }
    
    // STEP 1: Extract EGPTNumber vectors (maintain canonical precision)
    const H_deviation_vectors = division_analysis
        .map(segment => segment.H_abs_deviation)
        .filter(h_dev => h_dev !== null && h_dev !== undefined);
    
    if (H_deviation_vectors.length < 2) {
        console.log(`[discontinuityUtils] ⚠️  Insufficient valid deviation vectors: ${H_deviation_vectors.length}`);
        return [];
    }
    
    console.log(`[discontinuityUtils] 📊 Using EGPTStat for ultra-high precision analysis`);
    
    // STEP 2: Use EGPTStat for proper statistical analysis
    const stat_data = EGPTStat.comprehensiveStatisticalAnalysis(H_deviation_vectors, {
        include_normalization: true,
        chart_target_range: 1.0,
        min_chart_visibility: 0.001
    });
    
    // STEP 3: Get normalized deltas (preserves ultra-high precision relationships)
    const normalized_deltas = stat_data.getNormalizedDeltas();
    
    console.log(`[discontinuityUtils] 📊 Statistical Analysis Complete:`);
    console.log(`[discontinuityUtils]    📈 Mean: ${stat_data.mean.toMathString().slice(0, 20)}...`);
    console.log(`[discontinuityUtils]    📊 Std Dev: ${stat_data.std_deviation.toMathString().slice(0, 20)}...`);
    console.log(`[discontinuityUtils]    � Normalized deltas: ${normalized_deltas.length}`);
    
    // STEP 4: Find LARGEST step discontinuity (no thresholds)
    let largest_step_index = -1;
    let largest_step_magnitude = 0;
    
    for (let i = 0; i < normalized_deltas.length - 1; i++) {
        const current_normalized = normalized_deltas[i].normalized_delta;
        const next_normalized = normalized_deltas[i + 1].normalized_delta;
        const step_magnitude = Math.abs(next_normalized - current_normalized);
        
        console.log(`[discontinuityUtils] 🔍 Transition ${i} → ${i+1}: ${current_normalized.toFixed(6)} → ${next_normalized.toFixed(6)}, Δ = ${step_magnitude.toFixed(6)}`);
        
        
        // Track the largest step
        if (step_magnitude > largest_step_magnitude) {
            
            largest_step_magnitude = step_magnitude;
            largest_step_index = i + 1; //the step occurs between segments i and i+1, i+1 is has the potential factor since entropy is always increasing
            console.log(`[discontinuityUtils]  New largest  Range: [${division_analysis[largest_step_index].segment_start}, ${division_analysis[largest_step_index].segment_end}]`);
        }
    }
    
    // STEP 5: Return single largest discontinuity (or empty if none found)
    if (largest_step_index >= 0) {
        const target_segment = division_analysis[largest_step_index];
        const previous_segment = division_analysis[largest_step_index-1];
        
        console.log(`[discontinuityUtils] 🎯 LARGEST STEP DISCONTINUITY found between segments ${largest_step_index -1} and ${largest_step_index}:`);
        console.log(`[discontinuityUtils]    📊 Step magnitude: ${largest_step_magnitude.toFixed(8)} (MAXIMUM via EGPTStat)`);
        console.log(`[discontinuityUtils]    📍 Transition range: [${previous_segment.segment_start}, ${target_segment.segment_end}] `);

        const discontinuity = {
            index: largest_step_index,
            target_segment: target_segment,  // FIXED: Single target segment reference
            deviation_before: normalized_deltas[largest_step_index -1 ].normalized_delta,
            deviation_after: normalized_deltas[largest_step_index].normalized_delta,
            deviation_change: largest_step_magnitude,
            // FIXED: Use single target segment boundaries only
            transition_start: target_segment.segment_start,
            transition_end: target_segment.segment_end,
            transition_size: target_segment.segment_end - target_segment.segment_start + 1n, // FIXED: Calculate directly
            discontinuity_strength: largest_step_magnitude,
            egpt_statistical_metadata: {
                mean: stat_data.mean,
                std_deviation: stat_data.std_deviation,
                coefficient_of_variation: stat_data.coefficient_of_variation,
                analysis_method: "EGPTStat_comprehensiveStatisticalAnalysis"
            }
        };
        
        // PHASE 2 FIX: Calculate focused transition size
        discontinuity.transition_size = discontinuity.transition_end - discontinuity.transition_start + 1n;
        
        // FIXED: Update logging to reflect single target segment selection
        const chosen_segment = Math.abs(normalized_deltas[largest_step_index - 1].normalized_delta) > Math.abs(normalized_deltas[largest_step_index].normalized_delta) ? 
                               "BEFORE" : "AFTER";
        const chosen_deviation = Math.abs(normalized_deltas[largest_step_index -1].normalized_delta) > Math.abs(normalized_deltas[largest_step_index ].normalized_delta) ? 
                                 normalized_deltas[largest_step_index - 1].normalized_delta : normalized_deltas[largest_step_index].normalized_delta;
        
        console.log(`🎯 SINGLE TARGET SEGMENT SELECTION:`);
        console.log(`   Before segment: [${target_segment.segment_start}, ${target_segment.segment_end}] (size: ${target_segment.segment_end - target_segment.segment_start + 1n}) deviation: ${normalized_deltas[largest_step_index].normalized_delta.toFixed(6)}`);
        console.log(`   After segment: [${previous_segment.segment_start}, ${previous_segment.segment_end}] (size: ${previous_segment.segment_end - previous_segment.segment_start + 1n}) deviation: ${normalized_deltas[largest_step_index - 1].normalized_delta.toFixed(6)}`);
        console.log(`   🎯 SELECTED TARGET SEGMENT: ${chosen_segment} (higher absolute deviation: ${chosen_deviation.toFixed(6)})`);
        console.log(`   🔬 Target segment boundaries: [${discontinuity.transition_start}, ${discontinuity.transition_end}] (size: ${discontinuity.transition_size})`);
        console.log(`   📊 Step discontinuity strength: ${largest_step_magnitude.toFixed(6)}`);
        
        console.log(`[discontinuityUtils] 🔍 SINGLE TARGET SEGMENT IDENTIFIED: Found highest deviation segment for binary search refinement`);
        console.log(`[discontinuityUtils]    🎯 Target segment: [${discontinuity.transition_start}, ${discontinuity.transition_end}], Size ${discontinuity.transition_size}, Step strength ${discontinuity.discontinuity_strength.toFixed(8)}`);
        
        return [discontinuity];
    }
    
    console.log(`[discontinuityUtils] 📊 No meaningful step discontinuity found (largest step: ${largest_step_magnitude.toFixed(8)})`);
    return [];
}


/**
 * ANALYZE DISCONTINUITY CONVERGENCE
 * Analyzes refined segments to determine if discontinuity convergence has been achieved.
 * Uses EGPTStat-compliant analysis for ultra-high precision.
 * 
 * @param {Array} refined_segments - Array of refined segment analysis objects
 * @returns {Object} Convergence analysis result
 */
export function analyzeDiscontinuityConvergence(refined_segments) {
    console.log(`[discontinuityUtils] 🔬 EGPT-COMPLIANT CONVERGENCE ANALYSIS: ${refined_segments.length} refined segments`);
    
    // Look for sub-discontinuities in the refined data using EGPTStat
    const sub_discontinuities = identifyStepDiscontinuities(refined_segments);
    
    const convergence_result = {
        has_sub_discontinuities: sub_discontinuities.length > 0,
        sub_discontinuity_count: sub_discontinuities.length,
        sub_discontinuities: sub_discontinuities,
        convergence_achieved: sub_discontinuities.length === 0,
        next_refinement_target: sub_discontinuities.length > 0 ? sub_discontinuities[0] : null
    };
    
    if (convergence_result.convergence_achieved) {
        console.log(`[discontinuityUtils] 📍 CONVERGENCE ACHIEVED: No further discontinuities detected via EGPTStat`);
    } else {
        console.log(`[discontinuityUtils] 🎯 SUB-DISCONTINUITIES FOUND: ${sub_discontinuities.length} finer discontinuities detected`);
        sub_discontinuities.forEach((sub_disc, idx) => {
            console.log(`[discontinuityUtils]    ${idx + 1}. Sub-discontinuity at [${sub_disc.transition_start}, ${sub_disc.transition_end}], strength ${sub_disc.discontinuity_strength.toFixed(8)}`);
        });
    }
    
    return convergence_result;
}

/**
 * CREATE DISCONTINUITY REGION OBJECT
 * Creates a standardized region object for discontinuity refinement.
 * Enhanced with EGPTStat metadata for ultra-high precision tracking.
 * 
 * @param {Object} discontinuity - Discontinuity object from identifyStepDiscontinuities
 * @param {string} region_id - Unique identifier for this region
 * @returns {Object} Standardized region object for refinement
 */
export function createDiscontinuityRegion(discontinuity, region_id = null) {
    const region_obj = {
        id: region_id || `egpt_disc_${discontinuity.index}`,
        start: discontinuity.transition_start,
        end: discontinuity.transition_end,
        size: discontinuity.transition_size,
        strength: discontinuity.discontinuity_strength,
        source_discontinuity: discontinuity,
        region_type: 'egpt_largest_step_discontinuity',
        statistical_metadata: discontinuity.egpt_statistical_metadata || null
    };
    
    console.log(`[discontinuityUtils] 🎯 Created EGPT-compliant discontinuity region: [${region_obj.start}, ${region_obj.end}], strength ${region_obj.strength.toFixed(8)}`);
    
    return region_obj;
}

/**
 * NOTE: filterDiscontinuitiesByStrength function removed
 * 
 * ARCHITECTURAL DECISION: No longer needed since we always return
 * exactly one discontinuity (the largest step) from identifyStepDiscontinuities.
 * This aligns with the mathematical principle that there is exactly one
 * smaller factor to find, creating exactly one largest step discontinuity.
 */
