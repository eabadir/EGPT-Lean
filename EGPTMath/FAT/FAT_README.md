# FAT — Fast Abadir Transform (Pedagogical)

**This is a teaching library, not a production implementation.** The code here exists to demonstrate how an exact, integer-only FFT works — how floating-point twiddle factors become rational coordinates on N-gon vertices, and how the Cooley-Tukey butterfly can be performed with zero floating point. It is intentionally unoptimized: clarity over speed, readability over memory efficiency. The optimized FAT is proprietary and not in this repository.

All variants use `ComplexEGPTNumber` and `TwiddleTable` from `EGPTComplex.js` — no floating point anywhere in the transform pipeline.

## How It Works

FAT replaces the traditional Cooley-Tukey FFT's floating-point twiddle factors with exact phase-space arithmetic on N-gon vertices. A `TwiddleTable(N)` precomputes the N-th roots of unity as `ComplexEGPTNumber` values (rational coordinates on the unit circle), and the butterfly operations use exact rational add/subtract/multiply throughout.

The canonical implementation (`EGPTFAT.js`) determines the twiddle table size from the signal's phase structure — for unit-circle inputs this gives exact round-trips; for general inputs the table size is bounded by the signal length.

## Library Files

| File | Purpose | Exports |
|------|---------|---------|
| `EGPTFAT.js` | **Canonical implementation.** Recursive Cooley-Tukey with stride-based twiddle access from a single shared table. | `fat`, `ifat`, `fft`, `ifft`, `qft`, `iqft` |
| `EGPTFAT_PurePPF.js` | Optimized variant using native BigInt arithmetic during computation, encoding/decoding only at I/O boundaries. Matrix-based butterfly with bit-shifting for power-of-2 ops. | `fat_pureppf`, `ifat_pureppf`, `isPowerOfTwo` |
| `EGPTFAT_PhaseAware.js` | Dynamic twiddle generation — detects phase structure (LCM of phase denominators) at each recursion level instead of using a precomputed table. | `fat_phaseaware`, `ifat_phaseaware` |
| `EGPTFAT_LevelTracking.js` | Tracks the n-gon level (`l`) through recursion so that each butterfly stage uses `2^(l+1)` twiddle factors. Includes PPF encoding of natural numbers. | `fat_leveltracking`, `ifat_leveltracking` |
| `EGPTFAT_FIXED.js` | Simplified fix: creates a fresh `TwiddleTable(N)` at each recursion level rather than sharing one table with stride arithmetic. | `fat_fixed`, `ifat_fixed` |
| `EGPTFAT_TypeSafe.js` | Type-safe wrappers that reject wrong-domain inputs (e.g., passing a spectrum to the forward transform). | `fat_safe`, `ifat_safe`, `roundTrip_safe`, `fat_enhanced`, `ifat_enhanced` |
| `FATInterfaces.js` | Domain wrapper classes: `TimeDomainSignal`, `FrequencyDomainSpectrum`. Used by the type-safe layer. | `TimeDomainSignal`, `FrequencyDomainSpectrum`, `wrapForDomain`, `isTimeDomainSignal`, `isFrequencyDomainSpectrum` |
| `EGPTFATFormatters.js` | Format conversion between `ComplexEGPTNumber` arrays and external formats (e.g., `Float64Array` interleaved for `fft.js` compatibility). | `complexEGPTArrayToFloat64Array`, etc. |

## Quick Start

```js
import { EGPTNumber } from '../EGPTNumber.js';
import { ComplexEGPTNumber, TwiddleTable } from '../EGPTComplex.js';
import { fat, ifat } from './EGPTFAT.js';

// Build a signal from unit-circle points (exact round-trip guaranteed)
const table = new TwiddleTable(8);
const signal = Array.from({ length: 8 }, (_, i) => table.getTwiddle(i));

const spectrum = fat(signal);
const reconstructed = ifat(spectrum);
// reconstructed[i] === signal[i] exactly (integer arithmetic, no rounding)
```

## Running the Tests

From the `EGPTMath/` directory:

```bash
# Run individual test files
node FAT/test/test_EGPTFAT_Canonical.js
node FAT/test/test_EGPTFAT_PurePPF.js
node FAT/test/test_EGPTFAT_Traditional.js
node FAT/test/test_EGPTFAT_Validation.js
node FAT/test/test_FAT_TypeSafe.js
node FAT/test/test_PurePPF_Comprehensive.js
```

## Test Results (March 2026)

| Test File | Passed | Total | Status | Notes |
|-----------|--------|-------|--------|-------|
| `test_EGPTFAT_PurePPF.js` | 11 | 11 | **All pass** | Basic functionality + edge cases |
| `test_FAT_TypeSafe.js` | 5 | 5 | **All pass** | Domain safety, error detection, backward compat |
| `test_EGPTFAT_Validation.js` | 27 | 30 | 90% | 3 failures: sequential twiddle round-trips at N=8,16,32 |
| `test_EGPTFAT_Traditional.js` | 14 | 22 | 64% | Round-trips fail for non-trivial signals at N>=8 |
| `test_EGPTFAT_Canonical.js` | 38 | 59 | 64% | Round-trip failures for general signals at N>=8 |
| `test_PurePPF_Comprehensive.js` | 28 | 38 | 74% | Round-trip and linearity fail at N>=8 (same canonical limitation) |

### What Passes

- **Impulse signals** (single nonzero sample): exact round-trip at all sizes up to N=64.
- **DC signals** (all ones): exact round-trip at all sizes.
- **Alternating signals** (`[1,0,1,0,...]`): exact round-trip.
- **Small sizes** (N=2, N=4): all signal patterns round-trip exactly.
- **PurePPF vs Canonical equivalence**: forward transforms match for all tested sizes.
- **Type-safe wrappers**: correctly reject wrong-domain inputs, auto-wrap plain arrays.
- **Phase ring laws**: commutativity, associativity, identity for twiddle multiplication.
- **QFT/IQFT interface**: round-trips for impulse/DC signals.

### What Fails

The canonical implementation's round-trip (`ifat(fat(x)) = x`) breaks for **general signals at N >= 8**. The root cause is the twiddle table sizing strategy in `EGPTFAT.js`: `getSignalMaxNgonSize()` determines table size from phase denominators, but for non-unit-circle inputs (arbitrary integers, rationals, complex numbers), the table size doesn't capture enough resolution for exact reconstruction. This affects:

- Incrementing patterns (`[1,2,3,...]`) at N >= 8
- Modular patterns (`(i % 5) + 1`) at N >= 8
- Non-zero impulses at positions other than index 0 at N >= 8
- Sequential twiddle signals (mixed unit-circle points) at N >= 8
- Rational-valued signals at N >= 8

The PurePPF implementation matches the canonical exactly (same forward transform results), so both share the same round-trip limitation.

## Test Guide

### test_EGPTFAT_PurePPF.js

Validates the PurePPF implementation against the canonical. Tests forward-transform equivalence and round-trip identity at N=2,4,8,16 plus a N=1 base case. Fast, lightweight — good for smoke testing.

### test_FAT_TypeSafe.js

Exercises the type-safe interface layer:
- Forward transform with `TimeDomainSignal` wrappers
- Inverse transform with `FrequencyDomainSpectrum` wrappers
- Error detection when passing wrong-domain inputs (spectrum to `fat_safe`, signal to `ifat_safe`)
- `roundTrip_safe` helper
- Backward compatibility with unwrapped `ComplexEGPTNumber` arrays

### test_EGPTFAT_Validation.js

Unit-circle-only validation suite (5 test groups, 30 tests):
1. **Phase ring laws** — commutativity, associativity, identity of twiddle multiply (N=8,16,32)
2. **Impulse round-trip** — single nonzero sample at index 0 (N=4 through 64)
3. **DC round-trip** — all-ones signal (N=4 through 64)
4. **Mixed twiddle round-trip** — signals built from multiple twiddle values (alternating and sequential patterns)
5. **QFT/IQFT interface** — confirms `qft`/`iqft` aliases work correctly

### test_EGPTFAT_Traditional.js

Tests FAT as a drop-in FFT replacement with traditional (non-unit-circle) inputs (4 test groups, 22 tests):
1. **Real integer signals** — `[1,2,3,...]`, `[1,1,1,...]`, alternating at N=4,8,16
2. **Real rational signals** — `[1/2, 1/3, 1/4, ...]` at N=4,8,16
3. **Arbitrary complex signals** — `[(1+2i), (3+4i), ...]` at N=4,8,16
4. **Impulse response** — validates flat spectrum from impulse at N=4,8,16,32

### test_EGPTFAT_Canonical.js

Deep dive into the canonical implementation (6 test groups, 59 tests):
1. **Deterministic round-trip** — specific failing patterns (`(i%5)+1`) at N=8,16,32
2. **Systematic round-trip** — increment, constant, alternating, wrapping patterns at N=4,8,16
3. **Non-zero impulse** — impulse at various positions
4. **Unnormalized inverse** — verifies `ifat` without 1/N scaling yields N * original
5. **Sparse signals** — even-only, odd-only nonzero samples
6. **Unit-circle signals** — twiddle-based and mixed twiddle signals at N=4,8,16,32

### test_PurePPF_Comprehensive.js

Comparison of PurePPF vs Canonical across sizes N=2 through 16 (5 test groups, 38 tests):
1. **Round-trip identity** — `ifat(fat(x)) = x` for random signals (N=2,4,8,16)
2. **Impulse response** — flat spectrum from delta function (N=2,4,8,16)
3. **Linearity** — `FAT(a*x + b*y) = a*FAT(x) + b*FAT(y)` (N=4,8)
4. **Conjugate symmetry** — real input produces conjugate-symmetric spectrum (N=4,8)
5. **Edge cases** — N=1 base case, zero signal, non-power-of-2 error handling
