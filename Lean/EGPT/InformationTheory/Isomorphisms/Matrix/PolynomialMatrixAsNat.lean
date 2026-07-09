-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.

/- PolynomialMatrixAsNat — every matrix in coefficient form is bijectively a
natural number under the canonical encoding.

A "matrix" in this file is a `List DensePolyRat`, i.e. a list of
coefficient rows, where each row is a `List EntropyRat`. Every row is
a polynomial in coefficient form; the matrix is a polynomial system in
that form. (The user's original observation: matrices are just a different
way to write polynomial systems.)

Composing existing pieces:

* `DensePolyRat.toPolynomialRat` (PolynomialDense.lean) — Horner-factor
  a coefficient row into a `PolynomialRat` tree.
* `polyListEquivEntropyNat` (PolynomialSystemAsNat.lean) — bijection
  between systems of polynomial trees and EntropyNat.

The result: `List DensePolyRat ≃ image ⊆ EntropyNat`, with closure
`{propext, Quot.sound}` — same bar as the per-polynomial and per-system
layers, and as the three P=NP capstones.

Tagged ID5 (Abadir): the information-theoretic-number-hierarchy reading
applied to matrices in coefficient form — *every matrix of rational
polynomial coefficients is canonically a natural number under the
encoding chain*. Linear-algebra computation acting on matrices IS,
under this encoding, computation on natural numbers. -/

module

public import InformationTheory.Isomorphisms.Polynomial.PolynomialSystemAsNat
public import InformationTheory.Isomorphisms.Polynomial.PolynomialDense
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

/-! # §1 — `DensePolyRat` ↔ `PolynomialRat` partial inverse

`DensePolyRat.toPolynomialRat` is an injection — it produces a specific
Horner-factored tree shape (`add (const a) (mul id rest)` chains
terminating in `const zero`). To recover the dense form from such a
tree, we pattern-match on that exact shape. Trees outside this image
return `[]` defensively. -/

namespace DensePolyRat

/-- Parse a Horner-factored `PolynomialRat` tree back into a coefficient
list. On trees not produced by `toPolynomialRat`, returns `[]`. -/
def fromPolynomialRat : PolynomialRat → DensePolyRat
  | PolynomialRat.const c =>
      if c = EntropyRat.zero then [] else [c]
  | PolynomialRat.add (PolynomialRat.const a)
                      (PolynomialRat.mul PolynomialRat.id rest) =>
      a :: fromPolynomialRat rest
  | _ => []

/-- Round-trip: parsing the Horner-factored tree of a coefficient list
recovers the list. -/
theorem fromPolynomialRat_toPolynomialRat (p : DensePolyRat) :
    DensePolyRat.fromPolynomialRat
      (DensePolyRat.toPolynomialRat p) = p := by
  induction p with
  | nil =>
    show DensePolyRat.fromPolynomialRat
           (PolynomialRat.const EntropyRat.zero) = []
    -- The `const c` pattern fires; the `if c = zero` test reduces to
    -- the then-branch by decidable equality on the canonical `List Bool`
    -- substrate of EntropyRat.
    decide
  | cons a as ih =>
    show DensePolyRat.fromPolynomialRat
           (PolynomialRat.add
             (PolynomialRat.const a)
             (PolynomialRat.mul PolynomialRat.id
               (DensePolyRat.toPolynomialRat as))) = a :: as
    -- The `add (const _) (mul id _)` pattern fires; recurse on rest.
    show a :: DensePolyRat.fromPolynomialRat
                (DensePolyRat.toPolynomialRat as) = a :: as
    rw [ih]

end DensePolyRat

/-! # §2 — `List DensePolyRat ≃ EntropyNat`

A matrix in coefficient form (`List DensePolyRat`) encodes to an
`EntropyNat` via:

  `M ─[map toPolynomialRat]→ List PolynomialRat
      ─[polyListToEntropyNat]→ EntropyNat`

Round-trip: each row's per-row inverse (`fromPolynomialRat`) recovers
the dense form, and the system-level decoder
(`polyListFromEntropyNat`) recovers the list of trees. -/

/-- A matrix (list of coefficient-list rows) as an `EntropyNat`. -/
def matrixToEntropyNat (M : List DensePolyRat) : EntropyNat :=
  polyListToEntropyNat (M.map DensePolyRat.toPolynomialRat)

/-- Recover a matrix from its `EntropyNat` encoding. -/
def matrixFromEntropyNat (e : EntropyNat) : List DensePolyRat :=
  (polyListFromEntropyNat e).map DensePolyRat.fromPolynomialRat

/-- Round-trip: decoding the encoding of a matrix recovers it. -/
theorem matrixFromEntropyNat_toEntropyNat (M : List DensePolyRat) :
    matrixFromEntropyNat (matrixToEntropyNat M) = M := by
  unfold matrixFromEntropyNat matrixToEntropyNat
  rw [polyListFromEntropyNat_toEntropyNat]
  rw [List.map_map]
  -- Goal: M.map (fromPolynomialRat ∘ toPolynomialRat) = M
  have h_pointwise : ∀ p ∈ M,
      (DensePolyRat.fromPolynomialRat ∘ DensePolyRat.toPolynomialRat) p = p := by
    intro p _
    exact DensePolyRat.fromPolynomialRat_toPolynomialRat p
  rw [show M.map (DensePolyRat.fromPolynomialRat ∘ DensePolyRat.toPolynomialRat)
           = M.map id from List.map_congr_left h_pointwise]
  exact List.map_id M

/-- **The bijection.** `List DensePolyRat ≃ image ⊆ EntropyNat`,
image-subtype shape (matches the per-polynomial and per-system
layers). -/
def matrixEquivEntropyNat :
    List DensePolyRat ≃
      { e : EntropyNat // ∃ M : List DensePolyRat,
          matrixToEntropyNat M = e } where
  toFun M := ⟨matrixToEntropyNat M, ⟨M, rfl⟩⟩
  invFun e := matrixFromEntropyNat e.val
  left_inv M := matrixFromEntropyNat_toEntropyNat M
  right_inv := by
    rintro ⟨e, ⟨M, hM⟩⟩
    apply Subtype.ext
    show matrixToEntropyNat (matrixFromEntropyNat e) = e
    rw [← hM, matrixFromEntropyNat_toEntropyNat]

/-! # §3 — Capstone: every matrix in coefficient form IS a natural number

The four-layer encoding chain is now complete:

| Layer | Object | Bijection |
|---|---|---|
| §0 (this PR) | `DensePolyRat` (single polynomial, coefficient form) | via `toPolynomialRat`, then PolynomialAsNat |
| §1 (PolynomialAsNat) | `PolynomialRat` (single polynomial, tree form) | `≃ image ⊆ EntropyNat` |
| §2 (PolynomialSystemAsNat) | `List PolynomialRat` (polynomial system, tree form) | `≃ image ⊆ EntropyNat` |
| §3 (this file) | `List DensePolyRat` (matrix, coefficient form) | `≃ image ⊆ EntropyNat` |

Under the canonical bit-list encoding, **a matrix in coefficient form is
bijectively a natural number**. Every linear-algebra computation that
proceeds via matrices acts, at the encoded level, on natural numbers. -/

end InformationTheory
