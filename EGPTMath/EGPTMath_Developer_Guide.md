# EGPTMath Developer Guide: Unlimited Precision in Information Space

This guide explains how to use **EGPTMath** as an unlimited precision alternative to JavaScript's standard `Number` and `Math` classes. 

## 🧠 The Mindset Switch: Shannon Information Space

Using EGPTMath requires a fundamental shift in how you think about numbers.

### The "Language" Analogy
In standard JavaScript, you work in "Normal Space" (like English). In EGPTMath, you work in **Shannon Information Space** (like French).
*   **Bijective Mapping**: Every concept in English (e.g., "Cat") has a direct equivalent in French ("Chat"). They map 1-to-1.
*   **Different Representation**: The *spelling* and *rules* are different, even though the *meaning* is the same.
*   **Don't Translate Mid-Sentence**: You wouldn't say "The *chat* ate the food." You speak entirely in one language or the other.

**Key Rule**: Once you convert a value into EGPTMath (`EGPTNumber`), **stay in that space** for all your calculations. Do not convert intermediate results back to JavaScript numbers (`toNumber()`) or BigInts unless you absolutely must, as this is where precision loss occurs.

### The Topology
*   **Normal Space**: Linear number line. Operations are standard arithmetic.
*   **Information Space**: Logarithmic topology. 
    *   Multiplication in Normal Space $\leftrightarrow$ **Addition** in Information Space.
    *   Exponentiation in Normal Space $\leftrightarrow$ **Scaling** (Multiplication) in Information Space.

**EGPTMath methods are named for their Normal Space effect**. 
*   `EGPTMath.multiply(a, b)` achieves the effect of $a \times b$, even though internally it performs logarithmic addition $H(a) + H(b)$.

---

## 📚 Core Classes

### 1. `EGPTNumber` (The "Noun")
The pure data container. Think of this as your "Unlimited Precision Number".
*   **Internal Storage**: Stores values in Canonical PPF (Power Plus Fractional) format: `{N, offset}`. This is a bijective logarithmic encoding of the number.
*   **Scalar Multiplier**: Includes a rational scalar component to represent irrational roots exactly (e.g., $\sqrt{2}$ is stored as "half of the vector for 2").
*   **Immutable (mostly)**: Methods in `EGPTMath` return *new* instances. However, `EGPTNumber` has its own *mutable* scalar methods for chaining (see below).

#### Creating Numbers
```javascript
import { EGPTNumber } from './lib/EGPTNumber.js';

// Integer
const a = EGPTNumber.fromBigInt(42n);

// Rational (Fraction)
const b = EGPTNumber.fromRational(3n, 4n); // Represents 3/4

// Irrational (Scaled Vector) - usually created via Math operations
// e.g. H(√2) is created automatically by EGPTMath.sqrt(two)
```

### 2. `EGPTMath` (The "Verb")
The static algebra engine. Use this for all vector-to-vector operations.

```javascript
import { EGPTMath } from './lib/EGPTMath.js';

const p = EGPTNumber.fromBigInt(2n);
const q = EGPTNumber.fromBigInt(3n);

// Multiplication (Normal Space Effect)
// Internally: H(2) + H(3) = H(6)
const product = EGPTMath.multiply(p, q); 

// Division
// Internally: H(6) - H(2) = H(3)
const quotient = EGPTMath.divide(product, p);

// Exponentiation & Roots
const eight = EGPTMath.pow(p, 3n); // 2^3
const rootTwo = EGPTMath.sqrt(p);  // √2 (Exact representation!)
```

### 3. `ComplexEGPTNumber` & `TwiddleTable`
For complex arithmetic and FFT operations.
*   **`ComplexEGPTNumber`**: Holds `real` and `imag` components (both `EGPTNumber`s).
*   **`TwiddleTable`**: Generates high-precision roots of unity for FFT using phase arithmetic (preserving exact group structure $\omega^N = 1$).

### 4. `EGPTranscendental`
For trigonometric and exponential functions.
*   `cos`, `sin`, `exp` mapped to the canonical unit square/circle topology.
*   `factorial`: Uses a topology-native Stirling's approximation.

---

## 🛠️ Usage Guide

### Scalar vs. Vector Operations
This distinction is crucial for understanding the library's architecture.

1.  **Vector Operations (`EGPTMath`)**: Interactions *between* two EGPTNumbers.
    *   Immutable. Returns new instances.
    *   Examples: `EGPTMath.multiply(a, b)`, `EGPTMath.add(a, b)`.

2.  **Scalar Operations (`EGPTNumber` methods)**: Modifying a single EGPTNumber by a standard integer/rational amount.
    *   **Mutable & Chainable**. Returns `this`.
    *   Use these for efficient scaling or translation.
    
```javascript
// Fluent chaining example
const vec = EGPTNumber.fromBigInt(10n);

vec.scalarAdd(5n)        // 10 + 5 = 15
   .scalarMultiply(2n)   // 15 * 2 = 30
   .scalarDivide(3n);    // 30 / 3 = 10
```

### Getting Results (Leaving Information Space)
When your calculation is done, you can inspect the result.

*   **`toMathString()`**: **Preferred**. Returns a string representation like `(1/2) * H(2)` or `3/4`. Shows the exact structure.
*   **`toBigInt()`**: Returns a BigInt approximation. Warns if precision loss occurs (e.g., converting $\sqrt{2}$ to an integer).
*   **`toNumber()`**: Returns a standard JavaScript `Number`. **Warning**: This destroys infinite precision. Only use for final display/UI.

### Helper Functions: Translating "Languages"
Sometimes you need to move between the logarithmic structure and normal space logic explicitly.

*   **`EGPTranscendental.log2(x)`**: Extracts the "entropy" or exponent. 
    *   If $x = 8$, `log2(x)` returns $3$.
    *   Think of this as asking "How much information is in this number?"
*   **`EGPTranscendental.exp2(x)`**: The inverse. Computes $2^x$.
    *   Think of this as "Construct a number with this much information."

---

## 🌟 Key Concepts for Developers

### 1. The RET Iron Law
The library guarantees **Rota's Entropy Theorem (RET)**:
$$H(p \times q) = H(p) + H(q)$$
This is mathematically rigorous. If you find a case where `multiply(p, q)` does not equal the vector sum of `p` and `q`, it is a bug.

### 2. Scaled Vectors (Exact Irrationals)
EGPTMath can represent some irrational numbers **exactly** using scaled vectors.
*   $\sqrt{2}$ is stored as `{ scalar: 1/2, base: 2 }`.
*   Standard float math: $\sqrt{2} \approx 1.41421356...$ (Precision loss!)
*   EGPTMath: $\sqrt{2} \times \sqrt{2} = 2$ (Exact!)

### 3. Canonical Forms
The library automatically reduces numbers to their simplest "Canonical Form".
*   `EGPTMath.pow(16, 1/4)` automatically becomes `2`.
*   `EGPTNumber.fromRational(2, 4)` automatically becomes `1/2`.

---

## 🚀 Example Workflow

```javascript
import { EGPTNumber } from './lib/EGPTNumber.js';
import { EGPTMath } from './lib/EGPTMath.js';

// 1. Enter Information Space
const a = EGPTNumber.fromBigInt(8n);
const b = EGPTNumber.fromBigInt(32n);

// 2. Perform Calculations (Stay in the space!)
// Calculate geometric mean: sqrt(a * b)
const product = EGPTMath.multiply(a, b); // 8 * 32 = 256
const geoMean = EGPTMath.sqrt(product);  // sqrt(256) = 16

// 3. Chain scalar operations
geoMean.scalarAdd(4n).scalarDivide(2n); // (16 + 4) / 2 = 10

// 4. Exit / Inspect
console.log(geoMean.toMathString()); // "10"
console.log(geoMean.toBigInt());     // 10n
```

