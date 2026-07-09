# QFT Profiling Explanation

## Key Distinction

**Important:** QFT profiling does NOT compare QFT to FFT. Instead:

1. **QFT Profiling** = Internal profiling of FAT's QFT-specific operations
   - Profiles FAT's unique QFT components (twiddle generation, phase operations)
   - These operations are internal to FAT's implementation
   - fft.js does NOT have these operations (it uses traditional FFT)

2. **Benchmark Comparisons** = FAT vs fft.js on equivalent transforms
   - Compares FAT's EQFT (which produces FFT-equivalent results) vs fft.js's FFT
   - Both produce the same mathematical transform, just different implementations
   - FAT uses exact arithmetic, fft.js uses floating-point

## What QFT Profiling Actually Measures

### FAT's Internal QFT Operations (NOT in fft.js)

The QFT profiling measures FAT-specific operations that fft.js cannot do:

1. **TwiddleTable Generation**
   - FAT: Generates exact rational twiddles using `TwiddleTable`
   - fft.js: Uses pre-computed floating-point twiddles (not profiled separately)

2. **Phase-Based Operations**
   - `multiplyByPhase()` - Phase arithmetic (ω^a × ω^b = ω^(a+b))
   - `powerByPhase()` - Phase exponentiation
   - `conjugateByPhase()` - Phase conjugation
   - fft.js: Uses coordinate multiplication (not phase-based)

3. **EQFT/IEQFT Component Breakdown**
   - Twiddle generation time
   - Transform computation time
   - Normalization time (IEQFT)
   - fft.js: These components are not separable (black box)

## Why QFT Profiling is Separate

### FAT's Architecture (QFT-Style)

```
EQFT = {
  twiddle_generation: 20-25% of time
  transform_computation: 75-80% of time
}

IEQFT = {
  conjugate_twiddle_generation: 20-25% of time
  transform_computation: 75-80% of time
  normalization: 75-80% of time (overlaps with transform)
}
```

### fft.js Architecture (Traditional FFT)

```
fft.js = {
  // Black box - cannot profile internal components
  transform(): Float64Array  // All-in-one operation
  inverseTransform(): Float64Array  // All-in-one operation
}
```

## What the Benchmarks Compare

### Scalability & Speed Benchmarks

These compare **mathematical equivalence**:
- **FAT's EQFT** produces the same frequency domain as **fft.js's FFT**
- **FAT's IEQFT** produces the same time domain as **fft.js's IFFT**
- But FAT uses exact arithmetic, fft.js uses floating-point

### QFT Profiling

This profiles **FAT's unique QFT features** that fft.js doesn't have:
- Phase-based twiddle operations
- Exact rational twiddle generation
- Component breakdown (can't do this for fft.js - it's a black box)

## Summary

| Benchmark Type | What It Measures | Comparison? |
|---------------|------------------|-------------|
| **Scalability** | FAT vs fft.js speed | ✅ Yes - Equivalent transforms |
| **Speed Comparison** | FAT vs fft.js speed | ✅ Yes - Equivalent transforms |
| **QFT Profiling** | FAT's internal QFT ops | ❌ No - FAT-only, fft.js can't do QFT |
| **Hard Cases** | Precision preservation | ❌ No - FAT-only (fft.js has precision limits) |

## Why This Matters

The QFT profiling helps understand:
1. **Bottlenecks** in FAT's QFT implementation
2. **Optimization opportunities** (e.g., cache twiddles if generation is slow)
3. **Component costs** (e.g., how much time is spent on twiddle generation vs transform)

But it does NOT tell us how QFT compares to FFT - that's a meaningless comparison since:
- QFT is a quantum algorithm framework (exact arithmetic, phase-based)
- FFT is a classical algorithm (floating-point, coordinate-based)
- They produce equivalent results but use fundamentally different approaches

The **valid comparison** is:
- **FAT's EQFT** (QFT-style implementation) vs **fft.js's FFT** (classical implementation)
- Both produce the same mathematical transform
- But FAT preserves unlimited precision, fft.js uses floating-point













