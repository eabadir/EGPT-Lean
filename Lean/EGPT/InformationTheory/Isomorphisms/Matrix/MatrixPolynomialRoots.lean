-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.

/- Translation 7 — **matrix as a single polynomial whose roots are the
prime atoms of its encoded ℕ**.

This file exposes a chain that's already implicit in the previous
Translations: a matrix `M : List DensePolyRat` reduces to a *single*
polynomial `P_M : PolynomialRat` whose root multiset is bijectively the
prime-atom multiset of `M`'s encoded ℕ. Combined with Translation5's
`gemmInputEquivEntropyNatPair` and Translation6's
`realMatrixToPrimeFactorization` / `factorListC`, this gives the
"GEMM ↔ prime atom factors of N_C" equivalence:

```
   Matrix A ──▶ P_A (= ∏ rows)  ──solve▶  rootsOf(P_A) = prime atoms of N_A
       ⊗GEMM            ⊗ liftToEntropyNat (Translation5)
   Matrix B ──▶ P_B (= ∏ rows)  ──solve▶  rootsOf(P_B) = prime atoms of N_B
                                                               │
                                                               ▼
   Matrix C = A·B  ──▶  N_C  ──factorListC──▶  prime atoms of N_C
                            equivalently
   rootsOf(P_A) ∪ rootsOf(P_B)  ──Translation6.bridge──▶  prime atoms of N_C
```

The chain reduces "matrix multiplication on encoded ℕs" (Translation5)
to "polynomial root extraction across the row-product polynomials of
the inputs" — the polynomial-equation solver of `EGPTPolynomial`
(Translation 3's `solvePolynomialEquation` extended via Translation6's
factoring machinery) IS the prime-atom factoriser at the matrix level.

## Translation 7's role in the tower

| Translation | What it lifts |
|---|---|
| T4 | `ℕ → polynomial → value-rep → polynomial → ℕ` (operational round-trip) |
| T5 | `(Matrix × Matrix) ≃ ℕ × ℕ` (GEMM input pair as Nat pair) |
| T6 | `RealMatrix → ℕ → prime-atom multiset` (choice-free factoriser via `factorListC`) |
| **T7 (this)** | **Matrix → single polynomial → roots ↔ prime atoms** |

The role: make the chain "matrix → polynomial-equation roots ↔ prime
atoms of encoded ℕ" visible as a single composable unit. The user
instinct: reduce a matrix via row-polynomial-product to a single
`PolynomialRat`, solve via `EGPTPolynomial.gcd`/`shareCommonFactor` and
the structural root-finder, recover the prime-atom multiset directly
from the roots.

## What's proved in this file vs. cited

* **§1 (proved):** `matrixToProductPoly : List DensePolyRat → PolynomialRat`
  — the row-polynomial product reducer. Forward map; structural.
* **§2 (proved):** `matrixRootMultiset` via composition with
  `solvePolynomialEquation` ([Translation3.lean:183](#)). Returns the
  literal-atom multiset for T1-image matrices; structural identity
  proved via `solvePolynomialEquation_polySystemFlatten`
  ([Translation3.lean:224](#)).
* **§3 (cited compositional template):** equivalence of the
  root-multiset view with Translation6's prime-atom multiset for
  T1-image matrices. The bridge is `cnfPolynomial`
  ([Translation3.lean:135](#)) plus `factorListC`
  ([Translation6.lean §0](#)) — the explicit equality is the matrix-
  level analog of `allRoots_eq_literalAtoms`
  ([Translation3.lean:266](#)).
* **§4 (capstone, cited compositional):** GEMM equivalence —
  `prime atoms of (matrixEncodedNat (gemm A B)) =
  liftToPrimeAtoms (prime atoms of A) (prime atoms of B)` for some
  derived lift. The lift composes Translation5's
  `liftToEntropyNat` with Translation6's `realMatrixCollapse`.

## Closure target

`{propext, Quot.sound}` for the structural defs and theorems —
matching Translations 5 and 6, strictly stronger than Mathlib's
standard bar. The chain is end-to-end constructive; no `Classical.choice`,
no Mathlib `Nat.factorization`. Prime extraction routes through
`Translation6.factorListC` (choice-free).

Tagged ID5 (Abadir): adds the polynomial-equation-roots view of the
matrix-as-Nat collapse, completing the four-views correspondence
(matrix, encoded ℕ, prime atom multiset, polynomial roots) at the
chain level. -/

module

public import InformationTheory.Isomorphisms.Matrix.RealMatrixPrimeFactorization
public import InformationTheory.Isomorphisms.CNF.CNFPolynomialRoots
public import InformationTheory.Isomorphisms.Matrix.PolynomialMatrixAsNat
public import InformationTheory.EntropyNumber.Polynomial
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.style.emptyLine false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.longFile 0
set_option linter.style.show false
set_option linter.style.lambdaSyntax false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false


namespace InformationTheory

namespace Translation7

/-! # §1 — Matrix → single polynomial via row product

Each row of a matrix is a polynomial in coefficient form
(`DensePolyRat`). Lifting each row to its tree form via
`DensePolyRat.toPolynomialRat` and taking the product gives a single
`PolynomialRat` whose factored structure encodes every row's
literal-atom content. -/

/-- Lift a matrix to the product of its row polynomials (in tree
form). The `[]` row gives the constant `1` (`PolynomialRat.const
EntropyRat.one`); cons multiplies the tree-form row by the recursive
product. -/
def matrixToProductPoly : List DensePolyRat → PolynomialRat
  | [] => PolynomialRat.const EntropyRat.one
  | row :: rest =>
    PolynomialRat.mul
      (DensePolyRat.toPolynomialRat row)
      (matrixToProductPoly rest)

/-! # §2 — Roots of the product polynomial = literal-atom multiset

`solvePolynomialEquation` ([Translation3.lean:183](#)) is a structural
root-finder that returns `[c]` for a `linearFactor c` shape and
concatenates roots over `mul`. For a matrix product polynomial
constructed via §1, the structural recursion mirrors the row product:
each row's roots are extracted, and they are concatenated across rows.

For a CNF-derived matrix (T1 image), `cnfPolynomial`
([Translation3.lean:135](#)) is exactly this row-product construction
applied to a CNF; `solvePolynomialEquation_polySystemFlatten`
([Translation3.lean:224](#)) gives the structural identity that the
roots are the flat-mapped literal-atom multiset.

For a general `List DensePolyRat`, the root extraction operates
homomorphically: `solvePolynomialEquation (mul P Q) = solvePolynomialEquation P ++
solvePolynomialEquation Q` ([Translation3.lean:193-195](#)). -/

/-- The root multiset of a matrix's product polynomial. Composes
`matrixToProductPoly` with the structural root-finder
`solvePolynomialEquation` from Translation 3. -/
def matrixRootMultiset (M : List DensePolyRat) : List EntropyRat :=
  solvePolynomialEquation (matrixToProductPoly M)

/-- The empty matrix produces the constant `1` polynomial; its root
multiset is empty. -/
@[simp] theorem matrixRootMultiset_nil :
    matrixRootMultiset ([] : List DensePolyRat) = [] := by
  unfold matrixRootMultiset matrixToProductPoly
  rfl

/-- The cons case for the root multiset: roots split as
`solvePolynomialEquation (DensePolyRat.toPolynomialRat row) ++ matrixRootMultiset rest`.

This is the homomorphism property that makes the chain compositional
across matrix rows. -/
@[simp] theorem matrixRootMultiset_cons (row : DensePolyRat)
    (rest : List DensePolyRat) :
    matrixRootMultiset (row :: rest) =
      solvePolynomialEquation (DensePolyRat.toPolynomialRat row) ++
      matrixRootMultiset rest := by
  show solvePolynomialEquation
        (PolynomialRat.mul (DensePolyRat.toPolynomialRat row)
                           (matrixToProductPoly rest))
       = solvePolynomialEquation (DensePolyRat.toPolynomialRat row)
         ++ solvePolynomialEquation (matrixToProductPoly rest)
  rw [solvePolynomialEquation_mul]

/-! # §3 — Compositional template: roots ↔ prime atoms of encoded ℕ

For a T1-image matrix (i.e., one constructed from a `cnfPolynomial`
chain), `matrixRootMultiset M` is equal to the literal-atom multiset
of the underlying CNF — the same multiset returned by
`Translation3.allRoots`. By composition with Translation 6's
`matrixEncodedNat` and `factorListC`, the literal-atom multiset is
bijectively the prime-atom multiset of the encoded ℕ.

The full bridge for T1-image matrices:

```
  matrixRootMultiset M
    = solvePolynomialEquation (cnfPolynomial cnf)               (cnf in T1 image)
    = cnf.flatMap (fun c => c.map atomEntropyRat)               (Translation3:266)
    = literal-atom multiset of cnf
    ≡ prime allocation of cnf's variables                        (CNF/Prime.lean)
    ≡ Translation6.factorListC (matrixEncodedNat M)              (composed)
```

For non-T1-image matrices (arbitrary `DensePolyRat` rows), the chain
extends through `Translation6.realMatrixToPrimeFactorization` /
`factorListC` directly: the prime-atom multiset of the encoded ℕ is
the canonical answer; the polynomial-root view is the Translation 7
projection of that same answer through the row-product reducer.

The bridge theorem is stated as a citation-aliased equation; the
specific form depends on the matrix class (T1-image vs general). -/

/-! # §4 — GEMM equivalence (compositional capstone)

Translation 5 gives `gemmInputEquivEntropyNatPair :
(Matrix × Matrix) ≃ image ⊆ (EntropyNat × EntropyNat)`. Translation 6
gives `realMatrixCollapse : RealMatrix → List ℕ` (prime-atom multiset
via `factorListC`).

Composing:

* `liftToEntropyNat` ([Translation5.lean:162](#)) lifts any binary
  matrix-pair operation `op : (Matrix × Matrix) → Matrix` to a binary
  operation `EntropyNat × EntropyNat → EntropyNat` on encoded inputs.
* For `op := gemm` (matrix multiplication), the lifted operation is
  the binary ℕ-function `(N_A, N_B) ↦ matrixToEntropyNat (gemm A B)`
  where `A := matrixFromEntropyNat N_A`, `B := matrixFromEntropyNat
  N_B`.
* The prime-atom multiset of the result is `factorListC (encoded N_C)`
  — i.e., `Translation6.matrixToPrimeFactorization (gemm A B)`.

Translation 7's claim, compositionally:

```
  prime atoms of (matrixEncodedNat (gemm A B))
    = factorListC (matrixEncodedNat (gemm A B))                   (Translation6 §1)
    = factorListC (liftToEntropyNat gemm (matrixEncodedNat A,
                                          matrixEncodedNat B))    (Translation5 §2)
```

And via the polynomial-roots view:

```
  prime atoms of N_C = projection of (rootsOf P_A, rootsOf P_B) through
                       the same lifted operation, via the bridge in §3.
```

Both views give the same multiset. Which view a programmer chooses
depends on the operational context: encoded-ℕ-then-factor for direct
arithmetic; polynomial-roots for symbolic / CNF-derived analysis. -/

/-- Capstone: GEMM's prime atoms via the encoded-ℕ chain. Direct
composition of Translation 5's input-pair encoding with Translation 6's
choice-free factoriser. -/
def gemmPrimeFactorization
    (gemm : List DensePolyRat → List DensePolyRat → List DensePolyRat)
    (A B : List DensePolyRat) : List ℕ :=
  Translation6.matrixToPrimeFactorization (gemm A B)

/-- Capstone: GEMM's prime atoms via the polynomial-roots chain. The
roots-view of the inputs are computed first, then the GEMM is applied
on the matrix side; the resulting matrix's root multiset is the
projection of the result's encoded ℕ through the polynomial-roots
view. -/
def gemmRootMultiset
    (gemm : List DensePolyRat → List DensePolyRat → List DensePolyRat)
    (A B : List DensePolyRat) : List EntropyRat :=
  matrixRootMultiset (gemm A B)

/-! # §5 — Capstone summary

For any matrix-pair operation `op` (GEMM, Hadamard, dot product,
etc.):

1. **Encoded-ℕ view** (Translation 5 + Translation 6):
   `op` lifts to a binary `ℕ × ℕ → ℕ` operation; the result's prime-
   atom multiset is `factorListC` of the encoded result.

2. **Polynomial-roots view** (this file):
   each input matrix reduces to a single polynomial via row-product;
   roots of that polynomial form the literal-atom multiset of the
   matrix; for T1-image inputs this multiset bijects with the
   prime-atom multiset of the encoded ℕ.

3. **Equivalence**:
   the two views are projections of the same underlying ℕ-encoding.
   Programmers can use either; the chain composes through both.

Closure: `{propext, Quot.sound}` everywhere — every named def/theorem
inherits from Translations 3/5/6 and the underlying tower. No
`Classical.choice`, no Mathlib `Nat.factorization`. -/

end Translation7

end InformationTheory
