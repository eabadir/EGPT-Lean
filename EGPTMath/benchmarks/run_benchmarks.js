#!/usr/bin/env node --max-old-space-size=8192

// =============================================================================
// FAT BENCHMARK: ENTRY POINT SCRIPT
// Orchestrates all benchmark and profiling tests
//
// Usage: node run_benchmarks.js [options]
// =============================================================================

import { FATBenchmark, BenchmarkConfig } from './FAT_Benchmark.js';
import { FATProfiler } from './FAT_Profiler.js';
import * as testCases from './test_cases.js';

/**
 * Main benchmark execution
 */
async function runBenchmarks() {
    console.log('╔════════════════════════════════════════════════════════════════════════════════╗');
    console.log('║  FAT BENCHMARK SUITE                                                           ║');
    console.log('║  Comprehensive benchmarking and profiling of FAT vs fft.js                    ║');
    console.log('╚════════════════════════════════════════════════════════════════════════════════╝');
    console.log('');

    // Configuration
    const config = new BenchmarkConfig({
        iterations: 20,
        warmup: 5,
        csvOutput: true,
        fftSizes: [2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096]
    });

    const benchmark = new FATBenchmark(config);
    const profiler = new FATProfiler({
        csvOutput: true,
        outputDir: config.outputDir
    });

    try {
        // 1. Scalability benchmarks
        console.log('Starting scalability benchmarks...');
        await benchmark.benchmarkScalability();
        benchmark.exportScalabilityCSV();
        benchmark.exportToCSV('scalability_results.csv');

        // 2. Speed comparison benchmarks
        console.log('\nStarting speed comparison benchmarks...');
        benchmark.clearResults();
        await benchmark.benchmarkSpeedComparison();
        benchmark.exportToCSV('speed_comparison_results.csv');

        // 3. QFT profiling
        console.log('\nStarting QFT profiling...');
        await profiler.profileScalability([8, 16, 32, 64, 128, 256, 512, 1024], 10);
        profiler.exportToCSV('qft_profiling_results.csv');

        // 4. Hard cases (precision tests)
        console.log('\n' + '═'.repeat(70));
        console.log('HARD CASES: PRECISION TESTS');
        console.log('═'.repeat(70));
        
        const hardCaseResults = [];
        const hardSizes = [8, 16, 32, 64];
        
        for (const size of hardSizes) {
            console.log(`\nHard case test: FFT size ${size}`);
            
            // Very large BigInt
            const hugeSignal = testCases.generateHighPrecisionSignal(size, 1234567890123456789012345678901234567890n);
            const hugeSpectrum = await import('../FAT/EGPTFAT.js').then(m => m.fat(hugeSignal));
            const hugeRecovered = await import('../FAT/EGPTFAT.js').then(m => m.ifat(hugeSpectrum));
            
            const precisionPreserved = hugeSignal[0].real.equals(hugeRecovered[0].real);
            hardCaseResults.push({
                size,
                case: 'large_bigint',
                precisionPreserved,
                input: hugeSignal[0].real.toBigInt().toString(),
                recovered: hugeRecovered[0].real.toBigInt().toString()
            });
            console.log(`  Large BigInt: ${precisionPreserved ? '✅ PASS' : '❌ FAIL'}`);
            
            // High precision rational
            const num = 9999999999999999999999999999999999999999n;
            const den = 1234567890123456789012345678901234567890n;
            const rationalSignal = testCases.generateHighPrecisionRationalSignal(size, num, den);
            const rationalSpectrum = await import('../FAT/EGPTFAT.js').then(m => m.fat(rationalSignal));
            const rationalRecovered = await import('../FAT/EGPTFAT.js').then(m => m.ifat(rationalSpectrum));
            
            const rationalPrecisionPreserved = rationalSignal[0].real.equals(rationalRecovered[0].real);
            hardCaseResults.push({
                size,
                case: 'high_precision_rational',
                precisionPreserved: rationalPrecisionPreserved,
                input: rationalSignal[0].real.toMathString(),
                recovered: rationalRecovered[0].real.toMathString()
            });
            console.log(`  High precision rational: ${rationalPrecisionPreserved ? '✅ PASS' : '❌ FAIL'}`);
        }

        // Export hard cases to CSV
        if (config.csvOutput) {
            const fs = await import('fs');
            const path = await import('path');
            const timestamp = new Date().toISOString().replace(/[:.]/g, '-').split('T')[0];
            const filepath = path.join(config.outputDir, `hard_cases_${timestamp}.csv`);
            
            const header = ['fft_size', 'case_type', 'precision_preserved', 'input_value', 'recovered_value'].join(',');
            const rows = [header];
            for (const result of hardCaseResults) {
                rows.push([
                    result.size,
                    result.case,
                    result.precisionPreserved,
                    `"${result.input}"`,
                    `"${result.recovered}"`
                ].join(','));
            }
            
            fs.writeFileSync(filepath, rows.join('\n'));
            console.log(`\n✅ Hard cases exported to: ${filepath}`);
        }

        // Summary
        console.log('\n' + '═'.repeat(70));
        console.log('BENCHMARK SUITE COMPLETE');
        console.log('═'.repeat(70));
        console.log('\n✅ All benchmarks completed successfully');
        console.log('✅ Results exported to CSV files');
        console.log(`\nOutput directory: ${config.outputDir}`);

    } catch (error) {
        console.error('\n❌ Benchmark suite failed:', error.message);
        console.error(error.stack);
        process.exit(1);
    }
}

// Execute if run directly
if (import.meta.url === `file://${process.argv[1]}` || process.argv[1]?.includes('run_benchmarks.js')) {
    runBenchmarks();
}

export { runBenchmarks };













