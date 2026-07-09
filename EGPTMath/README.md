# EGPTMath: A Pedagogical Implementation of EGPT Constructive Number Theory

## Overview

**EGPTMath** is a pedagogical (unoptimized) JavaScript implementation of the Electronic Graph Paper Theory (EGPT) constructive number theory proofs formalized in Lean 4. This library serves as a verification and educational demonstration of the Pythagorean concept that all mathematics can be performed using whole numbers through modern Interactive Oracle Proofs (IOPs).

> **Author's Note on Current Implementation State & Contribution Guidelines:**
Some things still could be improved and contributions are welcome, especially in extending EGPTMath to the full complex plane - your contributions are welcome! This implementation is not optimized for performance. It is intended to serve as an educational reference.


> **Note on FAT:** This library does **not** disclose the optimized and proprietary **Faster Abadir Transform (FAT)**, which performs QFT-equivalent operations in IOPs on classical chips. EGPTMath is intentionally unoptimized to serve as an educational reference.


## Core Concepts

### The Pythagorean Foundation

EGPTMath demonstrates that the classical Pythagorean ideal—"Everything is number"—can be realized in modern computational terms. All mathematical operations are reduced to discrete, whole-number operations in information space, providing a unified framework for computation and physics.

### PPF (Power Plus Fractional) Representation

The **PPF (Power Plus Fractional)** representation is a Shannon coding scheme that satisfies **Rota's Entropy Theorem**, establishing a topological bijection with the logarithmic function. This bijection enables the reconstruction of Lean's fundamental number type constructions:

- **Natural Numbers (`ℕ`)**: Canonical histories of fair random walks (`ParticlePath`)
- **Integers (`ℤ`)**: Paths with initial direction ("charge")
- **Rational Numbers (`ℚ`)**: Canonical histories of biased random walks (PMFs)
- **Real Numbers (`ℝ`)**: Complete infinite future paths (PDFs)

See `EGPTTranscendental.js` and `EGPTComplex.js` for implementations of these constructions.

### Rota's Entropy Theorem

Rota's Uniqueness of Entropy Theorem establishes Shannon entropy as the canonical, bijective measure linking physical processes to discrete information. This theorem proves that:

1. **Uniqueness**: Any function satisfying physical entropy axioms must be `C × log(n)`
2. **Bijection**: The logarithmic function provides a one-to-one mapping between number systems
3. **Canonical Bridge**: Entropy serves as the universal "exchange rate" between all mathematical objects

In EGPTMath, this manifests as the **RET Iron Law**: `H(p × q) = H(p) + H(q)`, where multiplication in normal space becomes addition in Shannon (log) space.

## Reference Documentation

For the formal proofs and theoretical foundations, see:
- **[EGPT Overview](../EGPT/EGPTOverview.md)**: Complete whitepaper outline of the EGPT proof of P=NP
- **Lean Proofs**: The formal verification in `EGPT/` directory

## Test Suites

### Running the Test Suites

The library includes comprehensive test suites located in `lib/test/`:

```bash
# Main test suite (157 tests covering all core functionality)
node lib/test/EGPTTestSuite.js

# FFT operations with canonical comparisons
node lib/test/test_fft_operations_canonical.js

# PPF bijection verification
node lib/test/verify_ppf_bijection.js

# Conditional entropy tests
node lib/test/test_conditional_entropy.js

# Polynomial operations
node lib/test/EGPTPolynomialTest.js

# Topology tests
node lib/test/EGPTTopologyTestSuite.js
```

### Test Results Summary

The main test suite (`EGPTTestSuite.js`) validates **157 tests** with a **100% success rate**, covering:

#### Core Functionality
- **Vector Creation & Identity**: EGPTNumber as pure data container
- **Negative Number Encoding**: Full support for negative integers and rationals via PPF transformation
- **Scalar Operations**: Mutable chaining operations (add, subtract, multiply, divide)
- **Vector Algebra**: EGPTMath static operations (multiply, divide, pow, sqrt, add, subtract)

#### Fractional Exponentiation

A key feature of EGPTMath is its handling of **fractional exponents** through scaled vectors in Shannon space:

- **Root Operations**: `8^(1/3) = 2`, `16^(1/4) = 2`, `9^(1/2) = 3`
- **Rational Powers**: `27^(2/3) = 9`, `32^(3/5) = 8`
- **Nested Operations**: `√(∛27) = √3`
- **Rational Bases**: `(9/4)^(1/2) = 3/2`
- **Shannon Space Scaling**: Fractional exponents preserve entropy relationships

**Key Insight**: Fractional exponentiation is implemented via **scaled vectors** where `H(√n) = (1/2) × H(n)`. This allows exact representation of irrational numbers (like √2) in the discrete information space, demonstrating that all mathematics can be done with whole numbers.

#### RET Iron Law Validation

All tests verify Rota's Entropy Theorem:
- `H(6) = H(2) + H(3)` via multiplication
- Large number factorization: `H(77) = H(7) + H(11)`
- Inverse operations preserve entropy relationships
- Conditional entropy detects exact factors

#### FFT Operations

The test suite validates **TwiddleTable** operations for FFT:
- Phase-based twiddle generation (k=4, 8, 16, 32, 4096)
- Phase multiplication, power, and conjugation
- FFT requirements: `ω^k = ω₀`, phase additivity, special values, conjugate symmetry
- O(1) time complexity for phase operations at scale

#### Complex Numbers & Transcendental Functions

- Complex number operations with scaled vectors
- Riemann Zeta Function: `ζ(2) ≈ π²/6 ≈ 1.645`
- Exponential and logarithmic functions: `exp2()`, `log2()` with inverse relationships

## Theorem Tests

The `TheoremTests/` directory contains proofs and validations of major theorems:

### Running Theorem Tests

```bash
# Wilson's Theorem Proof
node TheoremTests/Wilsons_Theorem_Proof_EGPT.js

# EQFT Binary Split Proof (QFT = Factorial Structure + Twiddles)
node TheoremTests/EQFT_Binary_Split_Proof.js

# IEQFT Fundamental Operations Test Suite
node TheoremTests/IEQFT_Fundamental_Ops_TestSuite.js
```

### Theorem Test Results

#### Wilson's Theorem Proof
Validates Wilson's Theorem using EGPT number representations, demonstrating that prime number properties can be proven constructively in the information space framework.

#### EQFT Binary Split Proof
**Key Theorem**: The Quantum Fourier Transform can be computed using:
1. Factorial's binary-split decomposition (O(log² N) structure)
2. Twiddle phase multiplication at each split (O(1) per butterfly)
3. Achieving O(log² N) algorithmic complexity vs standard O(log³ N)

This proof establishes the isomorphism between factorial binary-split trees and QFT decimation-in-time decomposition, showing that the same computational pattern underlies both operations.

#### IEQFT Fundamental Operations
Comprehensive validation of all operations needed for Inverse Quantum Fourier Transform:
- Recursive even/odd branch separation
- Twiddle butterfly operations
- Phase arithmetic with unlimited precision
- Normalization and scaling

## Developer Guide

### Library Structure

```
EGPTMath/
├── lib/
│   ├── EGPTNumber.js          # Vector data container (pure data)
│   ├── EGPTMath.js            # Vector algebra engine (static operations)
│   ├── EGPTComplex.js         # Complex numbers with TwiddleTable
│   ├── EGPTranscendental.js   # Real number constructions
│   ├── EGPTPolynomial.js      # Polynomial operations
│   ├── FastFactorialEGPT.mjs  # Efficient factorial computation
│   └── stat/
│       ├── EGPTStat.js        # Statistical functions
│       └── EGPTStatData.js    # Statistical metadata
├── lib/test/                  # Comprehensive test suites
└── TheoremTests/              # Major theorem proofs
```

### Architecture Principles

#### Vector/Scalar Paradigm

The library follows a strict separation of concerns:

1. **EGPTNumber**: Pure vector data container
   - Immutable data structure (though methods return new instances)
   - PPF encoding: `{N_level, offset}` representation
   - Scalar operations: `scalarAdd()`, `scalarMultiply()`, etc. (mutable, chainable)

2. **EGPTMath**: Pure static vector algebra engine
   - All methods are static (cannot be instantiated)
   - Operates on clones to prevent side effects
   - Intuitive normal-space naming: `multiply()`, `divide()`, `pow()`
   - Pedagogical dual naming: `addInLogSpace()` shows Shannon perspective

#### Key Design Patterns

- **Canonical Comparisons**: Always use `.equals()` for comparisons, never decimal conversions
- **Scaled Vectors**: Irrational numbers represented as `(scalar) × H(base)` where scalar is rational
- **Phase-Based FFT**: TwiddleTable uses phase arithmetic for unlimited precision
- **RET Iron Law**: All operations preserve `H(p × q) = H(p) + H(q)`

### For Scientists

#### Exploring the Information-Theoretic Foundation

1. **Start with PPF Bijection**: Run `verify_ppf_bijection.js` to see how every natural number maps to a vertex on an n-gon
2. **Study RET Iron Law**: Examine how `EGPTMath.multiply()` implements entropy addition
3. **Investigate Fractional Exponentiation**: Understand how scaled vectors enable exact irrational representation
4. **Explore Complex Numbers**: See how phase arithmetic enables unlimited-precision FFT operations

### For Developers

#### Getting Started

```javascript
import { EGPTNumber } from './lib/EGPTNumber.js';
import { EGPTMath } from './lib/EGPTMath.js';
import { ComplexEGPTNumber } from './lib/EGPTComplex.js';

// Create numbers
const two = EGPTNumber.fromBigInt(2n);
const three = EGPTNumber.fromBigInt(3n);
const half = EGPTNumber.fromRational(1n, 2n);

// Vector algebra (normal-space naming)
const six = EGPTMath.multiply(two, three);  // 2 × 3 = 6
const sqrt2 = EGPTMath.sqrt(two);            // √2 as scaled vector

// Scalar operations (mutable, chainable)
const result = two.clone()
    .scalarAdd(3n)
    .scalarMultiply(2n)
    .scalarDivide(5n);

// Complex numbers
const z = new ComplexEGPTNumber(two, three);  // 2 + 3i
const w = z.conjugate();                        // 2 - 3i
```

#### Common Patterns

**Fractional Exponentiation**:
```javascript
const cubeRoot8 = EGPTMath.pow(
    EGPTNumber.fromBigInt(8n),
    EGPTNumber.fromRational(1n, 3n)
);  // 8^(1/3) = 2
```

**FFT Twiddles**:
```javascript
import { TwiddleTable } from './lib/EGPTComplex.js';

const table = new TwiddleTable(8);
const omega = table.getTwiddle(1);  // ω₈¹ = e^(2πi/8)
const phase = omega.getPhase();     // Exact phase: 1/8
```

**RET Iron Law Verification**:
```javascript
const p = EGPTNumber.fromBigInt(7n);
const q = EGPTNumber.fromBigInt(11n);
const product = EGPTMath.multiply(p, q);  // H(77) = H(7) + H(11)
```

#### Extending the Library

When adding new functionality:

1. **Vector Operations**: Add to `EGPTMath.js` as static methods
2. **Data Structures**: Extend `EGPTNumber.js` or create new classes
3. **Tests**: Add comprehensive tests to `lib/test/`
4. **Documentation**: Update this README with new features

#### Performance Considerations

- **Pedagogical Focus**: This library prioritizes clarity over optimization
- **BigInt Operations**: All arithmetic uses BigInt for unlimited precision
- **Memory**: Scaled vectors and complex numbers may use more memory than floats
- **For Production**: Use the proprietary FAT implementation for optimized performance

### Contributing

This is an educational reference implementation. Contributions should:
- Maintain pedagogical clarity
- Include comprehensive tests
- Document theoretical foundations
- Preserve the unoptimized nature for educational purposes

## License

See the main repository license. This library is provided for educational and research purposes.

## Acknowledgments

- **Gian-Carlo Rota** (1932-1999): For the Uniqueness of Entropy Theorem
- **Claude Shannon**: For information theory foundations
- **Lean 4 Community**: For the proof assistant framework

---

**Remember**: EGPTMath demonstrates that all mathematics can be done with whole numbers. The optimized implementations (FAT) are proprietary and not included in this educational library.








