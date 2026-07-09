// =============================================================================
// FAT PROFILER: QFT-SPECIFIC PROFILING
// Profiles individual components of EQFT/IEQFT operations
//
// Author: E. Abadir
// Purpose: Detailed profiling of twiddle generation, phase operations,
//          recursive calls, and other QFT-specific operations
// =============================================================================

import { fat, ifat } from '../FAT/EGPTFAT.js';
import { TwiddleTable } from '../EGPTComplex.js';
import fs from 'fs';
import path from 'path';

/**
 * Profiling result structure
 */
export class ProfilingResult {
    constructor(operation, totalTime, percentage, operationCount, avgTimePerOp) {
        this.operation = operation;
        this.totalTime = totalTime;
        this.percentage = percentage;
        this.operationCount = operationCount;
        this.avgTimePerOp = avgTimePerOp;
    }
}

/**
 * QFT Profiler class
 */
export class FATProfiler {
    constructor(options = {}) {
        this.outputDir = options.outputDir || path.join(path.dirname(new URL(import.meta.url).pathname), 'results');
        this.csvOutput = options.csvOutput !== false;
        this.profilingData = [];
    }

    /**
     * Profile twiddle generation
     */
    profileTwiddleGeneration(size, iterations = 100) {
        const times = [];
        
        for (let i = 0; i < iterations; i++) {
            const start = performance.now();
            const twiddles = new TwiddleTable(size);
            const end = performance.now();
            times.push(end - start);
        }
        
        const avgTime = times.reduce((a, b) => a + b, 0) / iterations;
        return {
            operation: 'twiddle_generation',
            totalTime: avgTime,
            operationCount: iterations,
            avgTimePerOp: avgTime
        };
    }

    /**
     * Profile conjugate twiddle generation
     */
    profileConjugateTwiddleGeneration(size, iterations = 100) {
        const times = [];
        
        for (let i = 0; i < iterations; i++) {
            const start = performance.now();
            const conjugateTwiddles = new TwiddleTable(size);
            const end = performance.now();
            times.push(end - start);
        }
        
        const avgTime = times.reduce((a, b) => a + b, 0) / iterations;
        return {
            operation: 'conjugate_twiddle_generation',
            totalTime: avgTime,
            operationCount: iterations,
            avgTimePerOp: avgTime
        };
    }

    /**
     * Profile TwiddleTable operations
     */
    profileTwiddleTableOperations(size, iterations = 1000) {
        const table = new TwiddleTable(size);
        const operations = {
            getTwiddle: [],
            multiplyByPhase: [],
            powerByPhase: [],
            conjugateByPhase: []
        };

        // Profile getTwiddle
        for (let i = 0; i < iterations; i++) {
            const j = i % size;
            const start = performance.now();
            table.getTwiddle(j);
            const end = performance.now();
            operations.getTwiddle.push(end - start);
        }

        // Profile multiplyByPhase
        for (let i = 0; i < iterations; i++) {
            const a = i % size;
            const b = (i * 2) % size;
            const start = performance.now();
            table.multiplyByPhase(a, b);
            const end = performance.now();
            operations.multiplyByPhase.push(end - start);
        }

        // Profile powerByPhase
        for (let i = 0; i < iterations; i++) {
            const j = i % size;
            const exp = 2;
            const start = performance.now();
            table.powerByPhase(j, exp);
            const end = performance.now();
            operations.powerByPhase.push(end - start);
        }

        // Profile conjugateByPhase
        for (let i = 0; i < iterations; i++) {
            const j = i % size;
            const start = performance.now();
            table.conjugateByPhase(j);
            const end = performance.now();
            operations.conjugateByPhase.push(end - start);
        }

        return {
            getTwiddle: {
                operation: 'twiddle_get',
                avgTime: operations.getTwiddle.reduce((a, b) => a + b, 0) / iterations,
                operationCount: iterations
            },
            multiplyByPhase: {
                operation: 'twiddle_multiply_phase',
                avgTime: operations.multiplyByPhase.reduce((a, b) => a + b, 0) / iterations,
                operationCount: iterations
            },
            powerByPhase: {
                operation: 'twiddle_power_phase',
                avgTime: operations.powerByPhase.reduce((a, b) => a + b, 0) / iterations,
                operationCount: iterations
            },
            conjugateByPhase: {
                operation: 'twiddle_conjugate_phase',
                avgTime: operations.conjugateByPhase.reduce((a, b) => a + b, 0) / iterations,
                operationCount: iterations
            }
        };
    }

    /**
     * Profile complete EQFT operation with breakdown
     */
    async profileEQFT(signal, iterations = 10) {
        const totalTimes = [];
        const twiddleGenTimes = [];
        const transformTimes = [];

        for (let i = 0; i < iterations; i++) {
            // Profile twiddle generation
            const twStart = performance.now();
            const twiddles = new TwiddleTable(signal.length);
            const twEnd = performance.now();
            twiddleGenTimes.push(twEnd - twStart);

            // Profile transform (excluding twiddle generation)
            const tfStart = performance.now();
            const spectrum = fat(signal);
            const tfEnd = performance.now();
            transformTimes.push(tfEnd - tfStart);
            
            totalTimes.push((twEnd - twStart) + (tfEnd - tfStart));
        }

        const avgTwiddleGen = twiddleGenTimes.reduce((a, b) => a + b, 0) / iterations;
        const avgTransform = transformTimes.reduce((a, b) => a + b, 0) / iterations;
        const avgTotal = totalTimes.reduce((a, b) => a + b, 0) / iterations;

        return {
            total: {
                operation: 'eqft_total',
                totalTime: avgTotal,
                percentage: 100,
                operationCount: iterations,
                avgTimePerOp: avgTotal
            },
            twiddleGeneration: {
                operation: 'eqft_twiddle_generation',
                totalTime: avgTwiddleGen,
                percentage: (avgTwiddleGen / avgTotal) * 100,
                operationCount: iterations,
                avgTimePerOp: avgTwiddleGen
            },
            transform: {
                operation: 'eqft_transform',
                totalTime: avgTransform,
                percentage: (avgTransform / avgTotal) * 100,
                operationCount: iterations,
                avgTimePerOp: avgTransform
            }
        };
    }

    /**
     * Profile complete IEQFT operation with breakdown
     */
    async profileIEQFT(spectrum, iterations = 10) {
        const totalTimes = [];
        const twiddleGenTimes = [];
        const transformTimes = [];
        const normalizationTimes = [];

        for (let i = 0; i < iterations; i++) {
            // Profile conjugate twiddle generation
            const twStart = performance.now();
            const conjugateTwiddles = new TwiddleTable(spectrum.length);
            const twEnd = performance.now();
            twiddleGenTimes.push(twEnd - twStart);

            // Profile transform (includes normalization)
            const tfStart = performance.now();
            const signal = ifat(spectrum);
            const tfEnd = performance.now();
            transformTimes.push(tfEnd - tfStart);

            // Profile normalization separately (run again to approximate)
            const normStart = performance.now();
            const signalAgain = ifat(spectrum);
            const normEnd = performance.now();
            normalizationTimes.push(normEnd - normStart);
            
            totalTimes.push((twEnd - twStart) + (tfEnd - tfStart));
        }

        const avgTwiddleGen = twiddleGenTimes.reduce((a, b) => a + b, 0) / iterations;
        const avgTransform = transformTimes.reduce((a, b) => a + b, 0) / iterations;
        const avgNormalization = normalizationTimes.reduce((a, b) => a + b, 0) / iterations;
        const avgTotal = totalTimes.reduce((a, b) => a + b, 0) / iterations;

        return {
            total: {
                operation: 'ieqft_total',
                totalTime: avgTotal,
                percentage: 100,
                operationCount: iterations,
                avgTimePerOp: avgTotal
            },
            twiddleGeneration: {
                operation: 'ieqft_conjugate_twiddle_generation',
                totalTime: avgTwiddleGen,
                percentage: (avgTwiddleGen / avgTotal) * 100,
                operationCount: iterations,
                avgTimePerOp: avgTwiddleGen
            },
            transform: {
                operation: 'ieqft_transform',
                totalTime: avgTransform,
                percentage: (avgTransform / avgTotal) * 100,
                operationCount: iterations,
                avgTimePerOp: avgTransform
            },
            normalization: {
                operation: 'ieqft_normalization',
                totalTime: avgNormalization,
                percentage: (avgNormalization / avgTotal) * 100,
                operationCount: iterations,
                avgTimePerOp: avgNormalization
            }
        };
    }

    /**
     * Profile across multiple FFT sizes
     */
    async profileScalability(sizes, iterations = 10) {
        console.log('\n' + '═'.repeat(70));
        console.log('QFT PROFILING: SCALABILITY');
        console.log('═'.repeat(70));

        const results = [];

        for (const size of sizes) {
            console.log(`\nProfiling FFT size: ${size}`);
            
            // Generate test signal
            const { generateImpulseSignal } = await import('./test_cases.js');
            const signal = generateImpulseSignal(size);
            
            // Profile EQFT
            console.log('  Profiling EQFT...');
            const eqftProfile = await this.profileEQFT(signal, iterations);
            
            // Profile IEQFT
            console.log('  Profiling IEQFT...');
            const spectrum = fat(signal);
            const ieqftProfile = await this.profileIEQFT(spectrum, iterations);
            
            // Profile TwiddleTable operations
            console.log('  Profiling TwiddleTable operations...');
            const twiddleOps = this.profileTwiddleTableOperations(size, 1000);
            
            // Store results
            results.push({
                fftSize: size,
                eqft: eqftProfile,
                ieqft: ieqftProfile,
                twiddleOperations: twiddleOps
            });

            // Log summary
            console.log(`    EQFT total: ${eqftProfile.total.totalTime.toFixed(3)}ms`);
            console.log(`    IEQFT total: ${ieqftProfile.total.totalTime.toFixed(3)}ms`);
            console.log(`    Twiddle get: ${twiddleOps.getTwiddle.avgTime.toFixed(6)}ms`);
        }

        this.profilingData = results;
        return results;
    }

    /**
     * Export profiling results to CSV
     */
    exportToCSV(filename = null) {
        if (!this.csvOutput) return;

        if (!fs.existsSync(this.outputDir)) {
            fs.mkdirSync(this.outputDir, { recursive: true });
        }

        const timestamp = new Date().toISOString().replace(/[:.]/g, '-').split('T')[0];
        const baseFilename = filename || `qft_profiling_${timestamp}.csv`;
        const filepath = path.join(this.outputDir, baseFilename);

        const header = [
            'fft_size',
            'operation',
            'total_time_ms',
            'percentage',
            'operation_count',
            'avg_time_per_op_ms'
        ].join(',');

        const rows = [header];

        for (const result of this.profilingData) {
            const size = result.fftSize;
            
            // EQFT breakdown
            for (const [key, profile] of Object.entries(result.eqft)) {
                rows.push([
                    size,
                    profile.operation,
                    profile.totalTime.toFixed(6),
                    profile.percentage.toFixed(2),
                    profile.operationCount,
                    profile.avgTimePerOp.toFixed(6)
                ].join(','));
            }
            
            // IEQFT breakdown
            for (const [key, profile] of Object.entries(result.ieqft)) {
                rows.push([
                    size,
                    profile.operation,
                    profile.totalTime.toFixed(6),
                    profile.percentage.toFixed(2),
                    profile.operationCount,
                    profile.avgTimePerOp.toFixed(6)
                ].join(','));
            }
            
            // TwiddleTable operations
            for (const [key, op] of Object.entries(result.twiddleOperations)) {
                rows.push([
                    size,
                    op.operation,
                    op.avgTime.toFixed(6),
                    'N/A', // Percentage not applicable for individual ops
                    op.operationCount,
                    op.avgTime.toFixed(6)
                ].join(','));
            }
        }

        fs.writeFileSync(filepath, rows.join('\n'));
        console.log(`✅ Profiling results exported to: ${filepath}`);
        return filepath;
    }
}













