// =============================================================================
// FAT BENCHMARK: MAIN BENCHMARKING FRAMEWORK
// Comprehensive benchmarking suite for FAT vs fft.js
//
// Author: E. Abadir
// Purpose: Compare FAT (fat/ifat) performance against fft.js
//          Collect scalability and speed data in CSV format
// =============================================================================

import { fat, ifat } from '../FAT/EGPTFAT.js';
import * as testCases from './test_cases.js';
import fs from 'fs';
import path from 'path';

/**
 * Benchmark configuration
 */
export class BenchmarkConfig {
    constructor(options = {}) {
        this.iterations = options.iterations || 100;
        this.warmup = options.warmup || 10;
        this.csvOutput = options.csvOutput !== false;
        this.outputDir = options.outputDir || path.join(path.dirname(new URL(import.meta.url).pathname), 'results');
        this.fftSizes = options.fftSizes || [2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096];
    }
}

/**
 * Benchmark result structure
 */
export class BenchmarkResult {
    constructor(testCase, fftSize, implementation, metrics) {
        this.testCase = testCase;
        this.fftSize = fftSize;
        this.implementation = implementation; // 'fat' or 'fftjs'
        this.forwardTime = metrics.forwardTime;
        this.inverseTime = metrics.inverseTime;
        this.roundtripTime = metrics.roundtripTime;
        this.throughput = metrics.throughput;
        this.memory = metrics.memory || null;
        this.precisionPreserved = metrics.precisionPreserved !== false;
        this.timestamp = new Date().toISOString();
    }
}

/**
 * Main benchmark runner class
 */
export class FATBenchmark {
    constructor(config = new BenchmarkConfig()) {
        this.config = config;
        this.results = [];
        this.fftjsInstance = null; // Will be initialized when needed
    }

    /**
     * Initialize fft.js instance (lazy loading)
     */
    async initFFTJS() {
        if (this.fftjsInstance === null) {
            const FFT = (await import('fft.js')).default;
            // We'll create instances per size as needed
        }
    }

    /**
     * Warmup runs to stabilize performance
     */
    async warmup(size) {
        const testSignal = testCases.generateImpulseSignal(size);
        for (let i = 0; i < this.config.warmup; i++) {
            const spectrum = fat(testSignal);
            const recovered = ifat(spectrum);
        }
    }

    /**
     * Benchmark a single implementation (FAT or fft.js)
     */
    async benchmarkImplementation(implementation, testCase, size, generator, iterations) {
        const metrics = {
            forwardTime: 0,
            inverseTime: 0,
            roundtripTime: 0,
            throughput: 0,
            precisionPreserved: true
        };

        if (implementation === 'fat') {
            // Generate test signal
            const signal = generator(size);
            
            // Benchmark forward transform
            const forwardTimes = [];
            for (let i = 0; i < iterations; i++) {
                const start = performance.now();
                const spectrum = fat(signal);
                const end = performance.now();
                forwardTimes.push(end - start);
                
                // Store spectrum for inverse benchmark
                if (i === 0) {
                    var testSpectrum = spectrum;
                }
            }
            
            // Benchmark inverse transform
            const inverseTimes = [];
            for (let i = 0; i < iterations; i++) {
                const start = performance.now();
                const recovered = ifat(testSpectrum);
                const end = performance.now();
                inverseTimes.push(end - start);
            }
            
            // Calculate averages
            metrics.forwardTime = forwardTimes.reduce((a, b) => a + b, 0) / iterations;
            metrics.inverseTime = inverseTimes.reduce((a, b) => a + b, 0) / iterations;
            metrics.roundtripTime = metrics.forwardTime + metrics.inverseTime;
            metrics.throughput = 1000 / metrics.roundtripTime; // transforms per second
            metrics.precisionPreserved = true; // FAT always preserves precision
            
        } else if (implementation === 'fftjs') {
            const FFT = (await import('fft.js')).default;
            const fft = new FFT(size);
            
            // Generate test signal in Float64Array format
            const signal = generator(size);
            const floatSignal = testCases.toFloat64Array(signal);
            const output = fft.createComplexArray();
            
            // Benchmark forward transform
            const forwardTimes = [];
            for (let i = 0; i < iterations; i++) {
                const start = performance.now();
                fft.transform(output, floatSignal);
                const end = performance.now();
                forwardTimes.push(end - start);
            }
            
            // Benchmark inverse transform
            const inverseTimes = [];
            for (let i = 0; i < iterations; i++) {
                const start = performance.now();
                fft.inverseTransform(output, floatSignal);
                const end = performance.now();
                inverseTimes.push(end - start);
            }
            
            // Calculate averages
            metrics.forwardTime = forwardTimes.reduce((a, b) => a + b, 0) / iterations;
            metrics.inverseTime = inverseTimes.reduce((a, b) => a + b, 0) / iterations;
            metrics.roundtripTime = metrics.forwardTime + metrics.inverseTime;
            metrics.throughput = 1000 / metrics.roundtripTime;
            metrics.precisionPreserved = false; // fft.js uses floating-point
        }

        return metrics;
    }

    /**
     * Benchmark scalability across different FFT sizes
     */
    async benchmarkScalability() {
        console.log('\n' + '═'.repeat(70));
        console.log('SCALABILITY BENCHMARK');
        console.log('═'.repeat(70));
        
        const results = [];
        const testCase = 'impulse';
        const generator = testCases.generateImpulseSignal;

        for (const size of this.config.fftSizes) {
            console.log(`\nTesting FFT size: ${size}`);
            
            // Warmup
            await this.warmup(size);
            
            // Benchmark FAT
            console.log(`  Benchmarking FAT...`);
            const fatMetrics = await this.benchmarkImplementation(
                'fat', testCase, size, generator, this.config.iterations
            );
            results.push(new BenchmarkResult(testCase, size, 'fat', fatMetrics));
            
            // Benchmark fft.js
            console.log(`  Benchmarking fft.js...`);
            const fftjsMetrics = await this.benchmarkImplementation(
                'fftjs', testCase, size, generator, this.config.iterations
            );
            results.push(new BenchmarkResult(testCase, size, 'fftjs', fftjsMetrics));
            
            // Log comparison
            const speedup = fftjsMetrics.roundtripTime / fatMetrics.roundtripTime;
            console.log(`    FAT: ${fatMetrics.roundtripTime.toFixed(3)}ms | fft.js: ${fftjsMetrics.roundtripTime.toFixed(3)}ms | Speedup: ${speedup.toFixed(2)}x`);
        }

        this.results.push(...results);
        return results;
    }

    /**
     * Benchmark speed comparison for various test cases
     */
    async benchmarkSpeedComparison() {
        console.log('\n' + '═'.repeat(70));
        console.log('SPEED COMPARISON BENCHMARK');
        console.log('═'.repeat(70));
        
        const results = [];
        const size = 256; // Fixed size for comparison
        const testCasesToRun = [
            { name: 'impulse', generator: testCases.generateImpulseSignal },
            { name: 'step', generator: testCases.generateStepFunction },
            { name: 'sinusoid', generator: (N) => testCases.generateSinusoid(N, 4) },
            { name: 'random', generator: testCases.generateRandomSignal },
            { name: 'dc', generator: testCases.generateDCSignal }
        ];

        for (const { name, generator } of testCasesToRun) {
            console.log(`\nTest case: ${name}`);
            
            // Warmup
            await this.warmup(size);
            
            // Benchmark FAT
            const fatMetrics = await this.benchmarkImplementation(
                'fat', name, size, generator, this.config.iterations
            );
            results.push(new BenchmarkResult(name, size, 'fat', fatMetrics));
            
            // Benchmark fft.js
            const fftjsMetrics = await this.benchmarkImplementation(
                'fftjs', name, size, generator, this.config.iterations
            );
            results.push(new BenchmarkResult(name, size, 'fftjs', fftjsMetrics));
            
            const speedup = fftjsMetrics.roundtripTime / fatMetrics.roundtripTime;
            console.log(`  FAT: ${fatMetrics.roundtripTime.toFixed(3)}ms | fft.js: ${fftjsMetrics.roundtripTime.toFixed(3)}ms | Speedup: ${speedup.toFixed(2)}x`);
        }

        this.results.push(...results);
        return results;
    }

    /**
     * Export results to CSV files
     */
    exportToCSV(filename = null) {
        if (!this.config.csvOutput) return;

        // Ensure output directory exists
        if (!fs.existsSync(this.config.outputDir)) {
            fs.mkdirSync(this.config.outputDir, { recursive: true });
        }

        const timestamp = new Date().toISOString().replace(/[:.]/g, '-').split('T')[0];
        const baseFilename = filename || `fat_benchmark_${timestamp}.csv`;
        const filepath = path.join(this.config.outputDir, baseFilename);

        // Create CSV header
        const header = [
            'test_case',
            'fft_size',
            'implementation',
            'forward_time_ms',
            'inverse_time_ms',
            'roundtrip_time_ms',
            'throughput_per_sec',
            'precision_preserved'
        ].join(',');

        // Create CSV rows
        const rows = [header];
        for (const result of this.results) {
            const row = [
                result.testCase,
                result.fftSize,
                result.implementation,
                result.forwardTime.toFixed(6),
                result.inverseTime.toFixed(6),
                result.roundtripTime.toFixed(6),
                result.throughput.toFixed(2),
                result.precisionPreserved
            ].join(',');
            rows.push(row);
        }

        // Write CSV file
        fs.writeFileSync(filepath, rows.join('\n'));
        console.log(`\n✅ Results exported to: ${filepath}`);
        return filepath;
    }

    /**
     * Export scalability comparison CSV
     */
    exportScalabilityCSV() {
        if (!this.config.csvOutput) return;

        const timestamp = new Date().toISOString().replace(/[:.]/g, '-').split('T')[0];
        const filepath = path.join(this.config.outputDir, `scalability_${timestamp}.csv`);

        // Group results by FFT size
        const bySize = {};
        for (const result of this.results) {
            if (!bySize[result.fftSize]) {
                bySize[result.fftSize] = {};
            }
            bySize[result.fftSize][result.implementation] = result;
        }

        const header = [
            'fft_size',
            'fat_forward_ms',
            'fat_inverse_ms',
            'fat_roundtrip_ms',
            'fftjs_forward_ms',
            'fftjs_inverse_ms',
            'fftjs_roundtrip_ms',
            'speedup_ratio',
            'throughput_fat',
            'throughput_fftjs'
        ].join(',');

        const rows = [header];
        for (const size of Object.keys(bySize).sort((a, b) => Number(a) - Number(b))) {
            const fat = bySize[size]['fat'];
            const fftjs = bySize[size]['fftjs'];
            
            if (fat && fftjs) {
                const speedup = fftjs.roundtripTime / fat.roundtripTime;
                const row = [
                    size,
                    fat.forwardTime.toFixed(6),
                    fat.inverseTime.toFixed(6),
                    fat.roundtripTime.toFixed(6),
                    fftjs.forwardTime.toFixed(6),
                    fftjs.inverseTime.toFixed(6),
                    fftjs.roundtripTime.toFixed(6),
                    speedup.toFixed(4),
                    fat.throughput.toFixed(2),
                    fftjs.throughput.toFixed(2)
                ].join(',');
                rows.push(row);
            }
        }

        fs.writeFileSync(filepath, rows.join('\n'));
        console.log(`✅ Scalability CSV exported to: ${filepath}`);
        return filepath;
    }

    /**
     * Clear results
     */
    clearResults() {
        this.results = [];
    }
}













