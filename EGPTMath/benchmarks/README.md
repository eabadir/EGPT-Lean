# FAT Benchmark Suite

Comprehensive benchmarking and profiling suite for FAT (Fast Abadir Transform) vs fft.js.

## Overview

This benchmark suite provides:
- **Scalability benchmarks** - Performance across FFT sizes (2 to 4096)
- **Speed comparisons** - FAT vs fft.js for various test cases
- **QFT profiling** - Detailed breakdown of twiddle operations, phase arithmetic, recursion
- **Hard cases** - Precision tests with large BigInt and high-precision rational numbers
- **CSV export** - All results exported to CSV for easy analysis

## Files

- **`test_cases.js`** - Test signal generators (impulse, step, sinusoidal, random, etc.)
- **`FAT_Benchmark.js`** - Main benchmarking framework with CSV export
- **`FAT_Profiler.js`** - QFT-specific profiling (twiddle generation, phase ops, recursion)
- **`run_benchmarks.js`** - Entry point script that orchestrates all benchmarks

## Usage

### Run All Benchmarks

```bash
node EGPT/js/model/benchmarks/run_benchmarks.js
```

### Run Specific Benchmarks

```javascript
import { FATBenchmark, BenchmarkConfig } from './FAT_Benchmark.js';

const config = new BenchmarkConfig({
    iterations: 100,
    warmup: 10,
    fftSizes: [8, 16, 32, 64, 128, 256]
});

const benchmark = new FATBenchmark(config);
await benchmark.benchmarkScalability();
benchmark.exportToCSV();
```

### Run QFT Profiling

```javascript
import { FATProfiler } from './FAT_Profiler.js';

const profiler = new FATProfiler();
await profiler.profileScalability([8, 16, 32, 64], 10);
profiler.exportToCSV();
```

## CSV Output Files

All results are exported to `EGPT/js/model/benchmarks/results/`:

- **`scalability_YYYY-MM-DD.csv`** - Performance across FFT sizes
  - Columns: `fft_size`, `fat_forward_ms`, `fat_inverse_ms`, `fat_roundtrip_ms`, `fftjs_forward_ms`, `fftjs_inverse_ms`, `fftjs_roundtrip_ms`, `speedup_ratio`, `throughput_fat`, `throughput_fftjs`

- **`speed_comparison_results.csv`** - FAT vs fft.js for different test cases
  - Columns: `test_case`, `fft_size`, `implementation`, `forward_time_ms`, `inverse_time_ms`, `roundtrip_time_ms`, `throughput_per_sec`, `precision_preserved`

- **`qft_profiling_results.csv`** - QFT component breakdown
  - Columns: `fft_size`, `operation`, `total_time_ms`, `percentage`, `operation_count`, `avg_time_per_op_ms`

- **`hard_cases_YYYY-MM-DD.csv`** - Precision test results
  - Columns: `fft_size`, `case_type`, `precision_preserved`, `input_value`, `recovered_value`

## Test Cases

Available test case generators (in `test_cases.js`):

- **`generateImpulseSignal(N)`** - Kronecker delta (impulse at index 0)
- **`generateStepFunction(N)`** - Step function
- **`generateSinusoid(N, freq)`** - Sinusoidal signal
- **`generateRandomSignal(N)`** - Random uniform distribution
- **`generateDCSignal(N)`** - DC signal (all ones)
- **`generateZeroSignal(N)`** - Zero signal (all zeros)
- **`generateHighPrecisionSignal(N, magnitude)`** - Large BigInt values
- **`generateHighPrecisionRationalSignal(N, num, den)`** - High precision rational fractions

## Benchmark Metrics

### Performance Metrics
- **Forward time** - Time for forward FFT (time → frequency)
- **Inverse time** - Time for inverse FFT (frequency → time)
- **Round-trip time** - Total time for forward + inverse
- **Throughput** - Transforms per second

### QFT Profiling Metrics
- **Twiddle generation time** - Time to generate twiddle table
- **Transform time** - Core transform computation (excluding twiddle generation)
- **Normalization time** - Time for 1/N normalization (IEQFT only)
- **Twiddle operation times** - Individual twiddle operations (get, multiply, power, conjugate)

### Precision Metrics
- **Precision preserved** - Whether unlimited precision is maintained (FAT: true, fft.js: false)

## Configuration

Customize benchmarks via `BenchmarkConfig`:

```javascript
const config = new BenchmarkConfig({
    iterations: 100,        // Number of iterations per test
    warmup: 10,             // Warmup runs before timing
    csvOutput: true,        // Export to CSV
    outputDir: './results', // Output directory
    fftSizes: [2, 4, 8, ...] // FFT sizes to test
});
```

## Interpreting Results

### Speedup Ratio
- **> 1.0**: FAT is faster than fft.js
- **< 1.0**: fft.js is faster than FAT
- **= 1.0**: Equal performance

### QFT Profiling Percentages
- Shows breakdown of where time is spent in QFT operations
- Helps identify bottlenecks (twiddle generation, recursion, normalization, etc.)

### Precision Tests
- **✅ PASS**: Unlimited precision preserved through round-trip
- **❌ FAIL**: Precision loss detected

## Requirements

- Node.js (ES modules support)
- `fft.js` package (installed via npm)
- `EGPTFAT.js` and `EGPTFATFormatters.js` (in model folder)

## Example Output

```
╔════════════════════════════════════════════════════════════════════════════════╗
║  FAT BENCHMARK SUITE                                                           ║
║  Comprehensive benchmarking and profiling of FAT vs fft.js                    ║
╚════════════════════════════════════════════════════════════════════════════════╝

Testing FFT size: 8
  Benchmarking FAT...
  Benchmarking fft.js...
    FAT: 0.123ms | fft.js: 0.045ms | Speedup: 0.37x

Testing FFT size: 16
  Benchmarking FAT...
  Benchmarking fft.js...
    FAT: 0.234ms | fft.js: 0.089ms | Speedup: 0.38x

...

✅ Results exported to: ./results/scalability_2025-01-XX.csv
✅ Scalability CSV exported to: ./results/scalability_2025-01-XX.csv
```

## Notes

- Benchmarks use `performance.now()` for high-precision timing
- Results may vary based on system load and Node.js version
- For reproducible results, run on a dedicated machine with minimal background processes
- CSV files are timestamped to avoid overwriting previous results













