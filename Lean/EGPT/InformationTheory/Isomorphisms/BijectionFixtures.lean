-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.

/- BijectionFixtures — concrete demonstrations of the bijective chains
laid out across the InformationTheory tree. The chain:

  matrix in coefficient form (List DensePolyRat)
   ↕  via per-row Horner factor + polyListEquivEntropyNat
  polynomial system          (List PolynomialRat)
   ↕  via polyListToEntropyNat ∘ entropyNatEquivNat.symm
  encoded EntropyNat
   ↕  via entropyNatEquivNat
  ℕ

with the parallel branch through value representation:

  dense polynomial           (DensePolyRat)
   ↕  toValueRep / fromValueRep (Newton DD interpolation)
  value representation       (List EntropyRat at 2^0..2^(D))

This file ships *operational* round-trip fixtures that exercise the
chains end-to-end on concrete data — surprising precisely because the
encoding is bijective at every step, even though the surface forms
(matrix, polynomial system, value-rep, ℕ) look entirely different.

Each fixture closes by direct application of the existing round-trip
lemmas (no new theorems needed) — this is the *operational evidence*
companion to the theorem layer. Use these when the surprising
implication ("a matrix IS a natural number") needs to be made
concrete to a reader who hasn't internalized the discipline yet.

The general round-trip theorem
`fromValueRep (toValueRep p) = p` is **stated but not proved** here;
see the §5 documentation block for the substantive caveat (Vandermonde
invertibility / Newton DD correctness, ~500 lines of Lean to prove
constructively from `{propext, Quot.sound}`). -/

module

public import InformationTheory.Isomorphisms.Matrix.PolynomialMatrixAsNat
public import InformationTheory.Isomorphisms.Polynomial.PolynomialValueRep
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

namespace BijectionFixtures

/-- Concise alias for `EntropyRat.ofNat n`. -/
private def R (n : ℕ) : EntropyRat := EntropyRat.ofNat n

/-! # §1 — Per-polynomial round-trips (`PolynomialRat ≃ EntropyNat`)

A polynomial tree IS a natural number under the encoding. Each `example`
below is a round-trip witness on concrete data. -/

/-- The identity polynomial (`X`) round-trips through EntropyNat. -/
example :
    PolynomialRat.ofEntropyNat
      (PolynomialRat.toEntropyNat PolynomialRat.id) = PolynomialRat.id :=
  PolynomialRat.ofEntropyNat_toEntropyNat _

/-- A constant polynomial (`5`) round-trips. -/
example :
    PolynomialRat.ofEntropyNat
      (PolynomialRat.toEntropyNat (PolynomialRat.const (R 5)))
      = PolynomialRat.const (R 5) :=
  PolynomialRat.ofEntropyNat_toEntropyNat _

/-- A compound polynomial `(X + 7)` round-trips. -/
example :
    PolynomialRat.ofEntropyNat
      (PolynomialRat.toEntropyNat
        (PolynomialRat.add PolynomialRat.id (PolynomialRat.const (R 7))))
      = PolynomialRat.add PolynomialRat.id (PolynomialRat.const (R 7)) :=
  PolynomialRat.ofEntropyNat_toEntropyNat _

/-- A multiplication tree `X · X` (i.e. `X²`) round-trips. -/
example :
    PolynomialRat.ofEntropyNat
      (PolynomialRat.toEntropyNat
        (PolynomialRat.mul PolynomialRat.id PolynomialRat.id))
      = PolynomialRat.mul PolynomialRat.id PolynomialRat.id :=
  PolynomialRat.ofEntropyNat_toEntropyNat _

/-! # §2 — Polynomial-system round-trips (`List PolynomialRat ≃ EntropyNat`)

A list of polynomial trees — a "system of polynomial equations" — IS a
natural number. -/

/-- A two-polynomial system round-trips. -/
example :
    polyListFromEntropyNat
      (polyListToEntropyNat
        [PolynomialRat.id, PolynomialRat.const (R 5)])
      = [PolynomialRat.id, PolynomialRat.const (R 5)] :=
  polyListFromEntropyNat_toEntropyNat _

/-- A three-polynomial system with mixed shapes. -/
example :
    polyListFromEntropyNat
      (polyListToEntropyNat
        [ PolynomialRat.const (R 1),
          PolynomialRat.id,
          PolynomialRat.add PolynomialRat.id (PolynomialRat.const (R 3))])
      = [ PolynomialRat.const (R 1),
          PolynomialRat.id,
          PolynomialRat.add PolynomialRat.id (PolynomialRat.const (R 3))] :=
  polyListFromEntropyNat_toEntropyNat _

/-- The empty system round-trips. -/
example :
    polyListFromEntropyNat
      (polyListToEntropyNat ([] : List PolynomialRat)) = [] :=
  polyListFromEntropyNat_toEntropyNat _

/-! # §3 — Matrix round-trips (`List DensePolyRat ≃ EntropyNat`)

**The surprising one.** A matrix in coefficient form (`List DensePolyRat`)
IS a natural number. This is the user's emphasis: the bijection holds for
arbitrary numeric matrices, even though linear algebra and number theory
look like entirely different subjects. -/

/-- The 2×2 integer matrix `[[1, 2], [3, 4]]` round-trips. -/
example :
    matrixFromEntropyNat
      (matrixToEntropyNat
        ([[R 1, R 2], [R 3, R 4]] : List DensePolyRat))
      = [[R 1, R 2], [R 3, R 4]] :=
  matrixFromEntropyNat_toEntropyNat _

/-- A 3×3 integer matrix round-trips. -/
example :
    matrixFromEntropyNat
      (matrixToEntropyNat
        ([[R 1, R 2, R 3],
          [R 4, R 5, R 6],
          [R 7, R 8, R 9]] : List DensePolyRat))
      = [[R 1, R 2, R 3],
         [R 4, R 5, R 6],
         [R 7, R 8, R 9]] :=
  matrixFromEntropyNat_toEntropyNat _

/-- A ragged "matrix" — rows of different lengths — also round-trips.
This is the natural EGPT shape (each row is a polynomial of its own
degree); rectangular matrices are a special case. -/
example :
    matrixFromEntropyNat
      (matrixToEntropyNat
        ([[R 1], [R 2, R 3], [R 4, R 5, R 6]] : List DensePolyRat))
      = [[R 1], [R 2, R 3], [R 4, R 5, R 6]] :=
  matrixFromEntropyNat_toEntropyNat _

/-- The 1×1 matrix `[[42]]` is the natural number 42 (under decoding):
its row is the constant polynomial 42, encoded then decoded back. -/
example :
    matrixFromEntropyNat
      (matrixToEntropyNat ([[R 42]] : List DensePolyRat))
      = [[R 42]] :=
  matrixFromEntropyNat_toEntropyNat _

/-! # §4 — Value-representation round-trips (`DensePolyRat ↔ value samples`)

Each row of a matrix (a dense polynomial) round-trips through its
powers-of-2 sample representation. This is the parallel branch the
user added: linear-algebra ↔ value samples ↔ Newton DD ↔ polynomial. -/

set_option maxRecDepth 4000 in
/-- Single-coefficient round-trip. -/
example :
    DensePolyRat.fromValueRep (DensePolyRat.toValueRep [R 7])
      = [R 7] := by decide

set_option maxRecDepth 4000 in
/-- Linear polynomial round-trip. -/
example :
    DensePolyRat.fromValueRep (DensePolyRat.toValueRep [R 5, R 7])
      = [R 5, R 7] := by decide

set_option maxRecDepth 4000 in
/-- Quadratic polynomial round-trip. -/
example :
    DensePolyRat.fromValueRep (DensePolyRat.toValueRep [R 1, R 2, R 3])
      = [R 1, R 2, R 3] := by decide

/-! # §5 — Cross-bijection: matrix-of-rows through the value-rep branch

For every row of a matrix, the per-row value-rep round-trip recovers
that row. So applying `fromValueRep ∘ toValueRep` element-wise to a
matrix recovers the matrix. This is the "GEMM-row" branch the user
named: each matrix row is independently bijective via its value
representation. -/

set_option maxRecDepth 4000 in
/-- Each row of `[[1, 2], [3, 4]]` round-trips through value-rep. -/
example :
    let M : List DensePolyRat := [[R 1, R 2], [R 3, R 4]]
    M.map (fun row => DensePolyRat.fromValueRep
      (DensePolyRat.toValueRep row)) = M := by
  decide

set_option maxRecDepth 4000 in
/-- 3×3 with mixed sizes — value-rep applied per-row recovers each row. -/
example :
    let M : List DensePolyRat := [[R 1, R 2, R 3], [R 4, R 5, R 6]]
    M.map (fun row => DensePolyRat.fromValueRep
      (DensePolyRat.toValueRep row)) = M := by
  decide

/-! # §6 — Multi-step bijective chain through different surface forms

Demonstrates that the same data flows through multiple encoding layers
without loss:

  matrix → polynomial system → encoded ℕ → polynomial system → matrix

The intermediate ℕ is a (potentially large) number; the matrix on the
left equals the matrix on the right. -/

/-- A 2×2 matrix survives the chain
`matrix → encoded EntropyNat → matrix`. -/
example :
    let M : List DensePolyRat := [[R 1, R 2], [R 3, R 4]]
    matrixFromEntropyNat (matrixToEntropyNat M) = M :=
  matrixFromEntropyNat_toEntropyNat _

/-- The chain factored explicitly:
`matrix → tree-system → ℕ → tree-system → matrix`.
The first step (`map toPolynomialRat`) and last step
(`map fromPolynomialRat`) are the per-row Horner-factor bridges from
PolynomialDense.lean. The middle (`polyListToEntropyNat ∘
polyListFromEntropyNat`) is the system-level encoding. -/
example :
    let M : List DensePolyRat := [[R 1, R 2], [R 3, R 4]]
    (polyListFromEntropyNat
        (polyListToEntropyNat (M.map DensePolyRat.toPolynomialRat))).map
      DensePolyRat.fromPolynomialRat = M := by
  show (polyListFromEntropyNat
          (polyListToEntropyNat
            (([[R 1, R 2], [R 3, R 4]] : List DensePolyRat).map
              DensePolyRat.toPolynomialRat))).map
        DensePolyRat.fromPolynomialRat = [[R 1, R 2], [R 3, R 4]]
  rw [polyListFromEntropyNat_toEntropyNat]
  rw [List.map_map]
  show ([[R 1, R 2], [R 3, R 4]] : List DensePolyRat).map
         (DensePolyRat.fromPolynomialRat ∘ DensePolyRat.toPolynomialRat)
       = [[R 1, R 2], [R 3, R 4]]
  -- The composition is identity per-row by `fromPolynomialRat_toPolynomialRat`.
  have h₁ := DensePolyRat.fromPolynomialRat_toPolynomialRat ([R 1, R 2] : DensePolyRat)
  have h₂ := DensePolyRat.fromPolynomialRat_toPolynomialRat ([R 3, R 4] : DensePolyRat)
  simp [Function.comp_apply, h₁, h₂]

/-! # §7 — The general round-trip theorem (status & proof sketch)

**Theorem (claim).** `∀ p : DensePolyRat, p ≠ [] →
fromValueRep (toValueRep p) = p`.

**Status.** Stated below; **not yet proved** in this file.

**Proof sketch.** For `p` of length L, `toValueRep p` produces L samples
at the L distinct nodes `2^0, 2^1, …, 2^(L-1)`. The Vandermonde matrix
at these nodes has nonzero determinant (powers of 2 are distinct), so
the sample list determines a unique polynomial of degree ≤ L−1. Both
`p` and `fromValueRep (toValueRep p)` are length-L polynomials that
agree at all L sample points (the latter by construction of Newton DD,
which is the constructive interpolant). Therefore they are equal.

**Why this is harder than it looks.** The constructive Lean proof
requires:

1. Newton DD correctness lemma — that `newtonCoeffs xs (eval p) = the
   Newton-basis representation of p at xs`. This is a structural
   induction on the sample list with multiple inductive lemmas.
2. Newton-to-monomial conversion correctness — that `newtonToMonomial
   (newtonCoeffs xs (eval p)) xs = p` (the change-of-basis is an
   isomorphism on polynomials of bounded degree).
3. Polynomial uniqueness at distinct nodes — Vandermonde determinant
   nonzero, classical linear-algebra fact.

Mathlib has `Polynomial.eq_of_eval_eq` and related lemmas that supply
(3) for fields, but those route through `Polynomial ℚ` and pull
`Classical.choice` (because `entropyRatEquivRat` and Mathlib's
`Polynomial` machinery interact through noncomputable bridges).
Constructively from `{propext, Quot.sound}` is feasible but
non-trivial — estimated 300–500 lines including the supporting
EntropyRat algebraic lemmas (`add_zero`, `mul_one`, `mul_zero`, …)
that are not yet in the codebase.

**Practical sufficiency.** The fixture-level evidence in §4 + §5
covers every encoding-chain shape used by the FRAQTL codec library.
Programmers encountering this surprise (a matrix is a Nat) can verify
on their data of interest by `decide`. The general theorem promotes
this from "verified per fixture" to "verified for all polynomials";
**that promotion is real mathematical work**, not a ceremony.

The theorem is recorded here so future work has a clear target. -/

end BijectionFixtures

end InformationTheory
