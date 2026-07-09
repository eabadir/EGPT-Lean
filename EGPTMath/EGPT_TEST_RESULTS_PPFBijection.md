# PPF Bijection Verification

> Source: `test/verify_ppf_bijection.js`
> Generated: 2026-03-06 UTC
> **Type: Exploratory verification (no pass/fail framework)**

---

## Result

Every natural number N maps to a unique vertex on its native n-gon via PPF encoding.

## PPF Encoding for N=1..8

| N | PPF | Phase | N-gon |
|---|-----|-------|-------|
| 1 | PPF{0, 0} | 0/2 = 0.000 | 2-gon (2^1 vertices) |
| 2 | PPF{1, 0} | 0/4 = 0.000 | 4-gon (2^2 vertices) |
| 3 | PPF{1, 1} | 1/4 = 0.250 | 4-gon (2^2 vertices) |
| 4 | PPF{2, 0} | 0/8 = 0.000 | 8-gon (2^3 vertices) |
| 5 | PPF{2, 1} | 1/8 = 0.125 | 8-gon (2^3 vertices) |
| 6 | PPF{2, 2} | 2/8 = 0.250 | 8-gon (2^3 vertices) |
| 7 | PPF{2, 3} | 3/8 = 0.375 | 8-gon (2^3 vertices) |
| 8 | PPF{3, 0} | 0/16 = 0.000 | 16-gon (2^4 vertices) |

## Decimation Analysis

When decimating [1,2,3,4,5,6,7,8]:

**Even indices [0,2,4,6] -> N values [1,3,5,7]:**

| N | Phase | N-gon |
|---|-------|-------|
| 1 | 0/2 | 2-gon |
| 3 | 1/4 | 4-gon |
| 5 | 1/8 | 8-gon |
| 7 | 3/8 | 8-gon |

Even branch LCM of denominators = 8 -> Use 8-gon twiddles.

**Odd indices [1,3,5,7] -> N values [2,4,6,8]:**

| N | Phase | N-gon |
|---|-------|-------|
| 2 | 0/4 | 4-gon |
| 4 | 0/8 | 8-gon |
| 6 | 2/8 | 8-gon |
| 8 | 0/16 | 16-gon |

Odd branch LCM of denominators = 16 -> Use 16-gon twiddles.

## Key Insight

Every natural number N is a vertex on its native n-gon. There is no "arbitrary input not on the unit circle." The twiddle table size must match the LCM of phase denominators in the signal to preserve phase relationships through recursion.

PPF Bijection: N <-> Unit Circle Vertices (complete coverage).
