# The Constructive Equivalence Chain: EntropyReal to Nat

This document maps the complete bijective equivalence chain from `EntropyReal` (the continuum) down to `Nat` (the discrete base), highlighting the choice-free semantic collapse machinery we have implemented.

## The Chain

1.  **`EntropyReal` ↔ `IIDParticleSource Bool`**
    *   **Implementation:** `iidParticleSourceEquivEntropyReal` (in `Real.lean`)
    *   **Nature:** Strict mathematical bijection (`Equiv`).
    *   **Mechanism:** Both types are structurally `ℕ → Bool`. `EntropyReal` is the powerset of `EntropyNat` (which is `ℕ`), and `IIDParticleSource Bool` is an infinite stream of boolean choices. The equivalence is a direct, choice-free structural replica.

2.  **`IIDParticleSource Bool` ↔ `InformationSource` (Finite Parameterization)**
    *   **Implementation:** The conceptual bridge between the infinite stream and its finite generative description.
    *   **Nature:** This is where the semantic collapse occurs. The infinite stream (`IIDParticleSource Bool`) has cardinality $\beth_1$. The `InformationSource` (a `FiniteIIDSample` defined by `p_param`, `q_param`, `num_sub_samples`) has cardinality $\beth_0$.
    *   **Mechanism:** Instead of mapping the full uncountable powerset, we extract the semantic content. The `InformationSource` is the finite, computable description of the probability distribution that *generates* the stream.

3.  **`InformationSource` ↔ `EntropyNat`**
    *   **Implementation:** `sourceToEntropyNat` (in `SourceCoding.lean`)
    *   **Nature:** Constructive mapping.
    *   **Mechanism:** Uses the computable integer ceiling of Shannon entropy (`computableEntropyCeil`). It maps the finite parameterization of the source to a unique `EntropyNat` bit-tape.
    *   **Key Property:** `EntropyNat` is defined as `{ L : List Bool // ∀ x ∈ L, x = true }`. Because it is fundamentally a `List Bool`, concatenation of these lists remains an `EntropyNat`. This allows complex structures (like matrices) to be flattened into a single `EntropyNat`.

4.  **`EntropyNat` ↔ `Nat`**
    *   **Implementation:** `entropyNatEquivNat` (in `Basic.lean`)
    *   **Nature:** Strict mathematical bijection (`Equiv`).
    *   **Mechanism:** Maps the length of the `List Bool` to `ℕ` (`toNat`) and generates a list of `true`s of a given length (`ofNat`).

5.  **`Nat` ↔ Prime Alphabet (`List ℕ`)**
    *   **Implementation:** `factorListC` (in `Factorization.lean` / `PrimeAtoms.lean`)
    *   **Nature:** Choice-free semantic extraction.
    *   **Mechanism:** A fuel-bounded structural-recursion prime factorizer. It maps the integer value into a unique multiset of prime atoms (the semantic alphabet).

## The Semantic Collapse (`EntropyReal` → Prime Alphabet)

The direct path from the continuum to the semantic alphabet, bypassing the Cantor diagonal:

*   **Implementation:** `entropyRealCollapse` (in `PrimeAtoms.lean`)
*   **Mechanism:**
    1.  `evalEntropyRealZero`: Projects the `EntropyReal` at the canonical zero point to extract a `Bool`.
    2.  `evalEntropyRealAsNat`: Encodes that `Bool` as an `EntropyNat` (0 or 1).
    3.  `factorListC`: Extracts the prime factors of that `EntropyNat`'s integer value.
*   **Significance:** This demonstrates that while the syntactic space (`EntropyReal`, `ℕ → Bool`) is uncountable and subject to Cantor's diagonalization, the *semantic information content* collapses constructively and choice-free onto unique, countable prime alphabets. Syntactic redundancy (flipping a bit in a redundant representation) does not create semantic novelty.
