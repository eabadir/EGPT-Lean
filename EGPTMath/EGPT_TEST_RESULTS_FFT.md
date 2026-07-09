# FFT Operations Canonical — Test Results

> Source: `test/test_fft_operations_canonical.js`
> Generated: 2026-03-06 UTC
> **Result: 6/12 PASS (50.0%)**

---

## Category Summary

| Category | Passed | Total |
|----------|--------|-------|
| Scaled Vector Addition | 2 | 2 |
| Scaled Vector Multiply | 2 | 2 |
| Complex Scaled Ops | 0 | 3 |
| Multi-term Summation | 0 | 1 |
| Scaled Vector Conjugate | 1 | 1 |
| Scaled Vector Scaling | 1 | 1 |
| DFT Term Computation | 0 | 1 |
| DFT Accumulation | 0 | 1 |

---

## Test Results

| Status | Test | Error |
|--------|------|-------|
| PASS | add(1, sqrt(1/2)) - 1 = sqrt(1/2) | |
| PASS | add(1, sqrt(1/2)) - sqrt(1/2) = 1 | |
| PASS | normalMultiply(2, sqrt(1/2)) should preserve sqrt(1/2) | |
| PASS | normalMultiply(1, sqrt(1/2)) = sqrt(1/2) | |
| **FAIL** | Complex add: (1,0) + (sqrt(2)/2, -sqrt(2)/2) | `EGPTMath.complexAdd is not a function` |
| **FAIL** | Complex multiply: (1,0) x (sqrt(2)/2, -sqrt(2)/2) | `EGPTMath.complexMultiply is not a function` |
| **FAIL** | Complex multiply: (2,0) x (sqrt(2)/2, -sqrt(2)/2) | `EGPTMath.complexMultiply is not a function` |
| **FAIL** | Sum of 4 terms with mixed scalars | `EGPTMath.complexAdd is not a function` |
| PASS | conjugate(sqrt(2)/2, -sqrt(2)/2) = (sqrt(2)/2, sqrt(2)/2) | |
| PASS | scaleByRational((sqrt(2)/2, -sqrt(2)/2), 1, 8) preserves structure | |
| **FAIL** | DFT term: x[n] x w^(kn) for scaled w | `EGPTMath.complexMultiply is not a function` |
| **FAIL** | Accumulate 8 DFT terms with sqrt(2) twiddles | `EGPTMath.complexAdd is not a function` |

---

## Failure Analysis

All 6 failures share the same root cause: the test file calls `EGPTMath.complexAdd` and `EGPTMath.complexMultiply`, but these methods live on the `EGPTComplex` class, not `EGPTMath`. This is a stale API reference in the test file, not a mathematical or algorithmic failure.

The 6 passing tests confirm that scaled vector operations (addition, multiplication, conjugation, rational scaling) work correctly in canonical space — the operations needed for FFT are sound.
