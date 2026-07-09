# EGPTMath

Pedagogical JavaScript implementation of EGPT constructive number theory. Demonstrates how FLOPs (floating-point operations) become IOPs (integer operations) — all of mathematics performed with whole numbers.

**This library is intentionally unoptimized.** It exists to teach, not to benchmark.

## Language & Setup

- **JavaScript** ES modules (Node.js, `"type": "module"` in package.json)
- **Dependencies**: only `fft.js` (for canonical comparison against EGPT's integer approach)
- **Install**: `npm install`
- **Test**: `node test/EGPTTestSuite.js` (157 tests, 100% pass rate)

## Core Files

| File | Purpose |
|------|---------|
| `EGPTMath.js` | Static vector algebra engine (~6800 lines), main entry point |
| `EGPTNumber.js` | PPF (Power Plus Fractional) number representation — lossless encoding |
| `EGPTComplex.js` | Complex number operations with scaled vectors |
| `EGPTranscendental.js` | Transcendental functions via integer operations |
| `EGPTPolynomial.js` | Polynomial operations |
| `DebugLogger.js` | Logging utility |

## Key Directories

- **`FAT/`** — Faster Abadir Transform implementations (multiple variants: PurePPF, PhaseAware, LevelTracking, TypeSafe). These are pedagogical — the proprietary optimized FAT is NOT in this repo.
- **`test/`** — Comprehensive test suite (6 test files). Run `node test/EGPTTestSuite.js` for the main suite.
- **`TheoremTests/`** — Formal theorem validations as runnable JS (Wilson's Theorem, EQFT Binary Split, IEQFT Fundamental Ops)
- **`benchmarks/`** — Performance analysis and profiling
- **`utils/`** — Pipeline data, constants, helpers, Chart.js integration
- **`stat/`** — Statistical utilities
- **`theorems/`** — Proof implementations as runnable code

## Documentation

- **`README.md`** — Comprehensive package documentation (PPF representation, test results, RET validation)
- **`EGPTMath_Developer_Guide.md`** — Developer guide: unlimited precision in information space, Shannon coding mindset
- **`FastFactorialEGPT.mjs`** — Fast factorial implementation in EGPT

## Key Concepts

- **PPF Representation**: Power Plus Fractional encoding satisfies Rota's Entropy Theorem. The bijection `H(p × q) = H(p) + H(q)` (RET Iron Law) — multiplication in normal space is addition in Shannon (log) space.
- **No floating point in core logic.** All math uses integer operations only. The `fft.js` dependency is used solely for canonical comparison.
- **Shannon coding**: Every number is represented in its informationally unique form, matching the Lean proof's `ParticlePath` concept.

## Conventions

- All math operations return integer or PPF results — never raw floats
- Test files are self-contained and can be run individually with `node test/<file>.js`
- FAT variants in `FAT/` explore different implementation strategies but share the same mathematical foundation
