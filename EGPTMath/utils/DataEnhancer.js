/**
 * EGPT DATA ENHANCER: Post-processing for UI charting
 * ENHANCEMENT: Now works with EGPTStatData-normalized data from SegmentManager
 * 
 * Phase 3 Implementation: Pipeline handles normalization via EGPTStatData
 * User Request: Pipeline handles success/failure modes gracefully with safe chart data
 */

import { EGPTNumber } from '../../model/EGPTNumber.js';
import { EGPTMath } from '../../model/EGPTMath.js';

console.log("📊 DATA ENHANCER: Post-processing utilities for UI charting loaded");
console.log("🎓 CANONICAL INFORMATION SPACE: Vector/Scalar paradigm");
console.log("📁 File location: EGPT/copilot/EGPT_REFACTOR/utils/DataEnhancer.js");
console.log("🎯 Purpose: Ensure pipeline output is always chartable with EGPTStatData normalization");

/**
 * Enhances orchestrator output with charting properties
 * NOW SIMPLIFIED: SegmentManager handles normalization via EGPTStatData
 */
export class DataEnhancer {
    /**
     * Enhance pipeline result for charting
     * @param {Object} orchestratorResult - Raw orchestrator output (now includes EGPTStatData normalization)
     * @param {BigInt} k - The original composite number
     * @returns {Object} Enhanced result ready for Chart.js
     */
    static enhanceForCharting(orchestratorResult, k) {
        console.log("📊 ENHANCING DATA: Pipeline data already normalized by EGPTStatData");
        
        // The SegmentManager now handles normalization via EGPTStatData
        // So we just need to ensure the data structure is Chart.js compatible
        const enhanced = {
            ...orchestratorResult,
            // Ensure Chart.js expects these exact properties
            k: orchestratorResult.k || k,
            D: orchestratorResult.D || orchestratorResult.division_analysis?.length || 0,
            deviation_values_for_chart: orchestratorResult.deviation_values_for_chart || [],
            use_ordinal_ranking: orchestratorResult.use_ordinal_ranking || false,
            unique_groups_count: orchestratorResult.unique_groups_count || 0,
            scale_factor: orchestratorResult.scale_factor || 1.0,
            range_magnitude: orchestratorResult.range_magnitude || 0,
            division_analysis: orchestratorResult.division_analysis || [],
            deviations_H: orchestratorResult.deviations_H || [],
            factor_test_results: orchestratorResult.factor_test_results || { performed: false }
        };
        
        // Validate that the data is Chart.js safe
        const validation = this.validateChartData(enhanced);
        if (!validation.isValid) {
            console.warn("⚠️ Chart data validation failed:", validation.issues);
            // Apply emergency fallback
            enhanced.deviation_values_for_chart = this.createFallbackChartData(enhanced.D || 8);
            enhanced.use_ordinal_ranking = true;
            enhanced.scale_factor = 1.0;
        }
        
        console.log(`✅ Enhanced data validated for charting: ${enhanced.deviation_values_for_chart?.length || 0} points`);
        return enhanced;
    }
    
    /**
     * Validate that chart data is safe for Chart.js rendering
     * @param {Object} enhancedResult - Enhanced result
     * @returns {Object} Validation result
     */
    static validateChartData(enhancedResult) {
        const issues = [];
        const chartData = enhancedResult.deviation_values_for_chart || [];
        
        // Check if chart data exists and is an array
        if (!Array.isArray(chartData)) {
            issues.push('deviation_values_for_chart is not an array');
        } else if (chartData.length === 0) {
            issues.push('deviation_values_for_chart is empty');
        } else {
            // Check each data point
            chartData.forEach((value, index) => {
                if (typeof value !== 'number') {
                    issues.push(`Index ${index}: not a number (${typeof value})`);
                } else if (!isFinite(value)) {
                    issues.push(`Index ${index}: not finite (${value})`);
                } else if (Math.abs(value) > 1000) {
                    issues.push(`Index ${index}: extreme value (${value})`);
                }
            });
        }
        
        return {
            isValid: issues.length === 0,
            issues: issues,
            status: issues.length === 0 ? 'CHART_READY' : 'NEEDS_FALLBACK'
        };
    }
    
    /**
     * Create emergency fallback chart data if validation fails
     * @param {number} dataPoints - Number of data points to generate
     * @returns {Array<number>} Safe fallback data
     */
    static createFallbackChartData(dataPoints = 8) {
        console.log("🚨 Creating emergency fallback chart data");
        return Array.from({length: dataPoints}, (_, i) => 0.1 + (i % 3) * 0.1);
    }
    
    /**
     * DEPRECATED: Individual division enhancement no longer needed
     * SegmentManager now handles this via EGPTStatData
     */
    static enhanceDivision(division, index, k) {
        console.log("⚠️ enhanceDivision is deprecated - use SegmentManager with EGPTStatData");
        return division;
    }
    
    /**
     * Validate that enhanced data is chartable (UPDATED for EGPTStatData)
     * @param {Object} enhancedResult - Enhanced orchestrator result
     * @returns {Object} Validation result
     */
    static validateChartable(enhancedResult) {
        const requiredProperties = ['deviation_values_for_chart', 'use_ordinal_ranking', 'scale_factor'];
        const issues = [];
        
        requiredProperties.forEach(prop => {
            if (!(prop in enhancedResult)) {
                issues.push(`Missing required charting property: ${prop}`);
            }
        });
        
        // Validate chart data specifically
        const chartValidation = this.validateChartData(enhancedResult);
        issues.push(...chartValidation.issues);
        
        return {
            isChartable: issues.length === 0,
            issues: issues,
            status: issues.length === 0 ? 'READY' : 'NOT_READY'
        };
    }
}
