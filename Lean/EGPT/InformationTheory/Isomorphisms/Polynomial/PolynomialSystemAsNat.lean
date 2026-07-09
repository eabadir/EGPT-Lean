-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.

/- PolynomialSystemAsNat — every polynomial *system* (i.e. a finite list of
polynomials, the CNF-as-polynomial-system shape from Translation 1) is a
natural number under the canonical bit-list encoding, and the list
operations (concatenation, cons) are bijectively derived natural-number
operations under that encoding.

This is the system-level companion of
`InformationTheory/Isomorphisms/Polynomial/PolynomialAsNat.lean`:

* `PolynomialAsNat.lean` lands `PolynomialRat ≃ EntropyNat` and the
  `add`/`mul`/`neg` constructor transport theorems.
* This file lands `List PolynomialRat ≃ EntropyNat` and the `++`/`::`
  list-constructor transport theorems.

The list encoder (`polynomialListToNat` / `polynomialListFromNat` from
Translation 2) is already proven `{propext, Quot.sound}`-clean. Composing
with `entropyNatEquivNat.symm` lifts to the EntropyNat side.

Tagged ID5 (Abadir): the information-theoretic-number-hierarchy reading
applied to polynomial systems — *every constructively-presented system of
rational polynomial equations is canonically a natural number, and every
list-level constructor on systems is a derived natural-number
operation under that identification*. -/

module

public import InformationTheory.Isomorphisms.CNF.CNFAsEntropyNat
public import InformationTheory.Isomorphisms.Polynomial.PolynomialAsNat
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

/-! # §1 — The bijection `List PolynomialRat ≃ EntropyNat`

Translation 2's `polynomialListToNat` length-prefixes per-polynomial
encodings via `unaryLen` and concatenates through the same `listBoolToNat`
substrate used everywhere in the InformationTheory tree. The round-trip
`polynomialListFromNat_toNat` is already proven choice-free
(`CNFAsEntropyNat.lean:229`). Composing with `entropyNatEquivNat.symm`
lands it on the EntropyNat side. -/

/-- A polynomial system (list of polynomials) as an `EntropyNat`. -/
def polyListToEntropyNat (P : List PolynomialRat) : EntropyNat :=
  entropyNatEquivNat.symm (polynomialListToNat P)

/-- Recover a polynomial system from its `EntropyNat` encoding. -/
def polyListFromEntropyNat (e : EntropyNat) : List PolynomialRat :=
  polynomialListFromNat (entropyNatEquivNat e)

/-- Round-trip: decoding the `EntropyNat` encoding of a polynomial system
recovers the system. -/
theorem polyListFromEntropyNat_toEntropyNat (P : List PolynomialRat) :
    polyListFromEntropyNat (polyListToEntropyNat P) = P := by
  unfold polyListFromEntropyNat polyListToEntropyNat
  rw [Equiv.apply_symm_apply]
  exact polynomialListFromNat_toNat P

/-- **The bijection.** `List PolynomialRat ≃ image ⊆ EntropyNat`,
image-subtype shape (matches `PolynomialRat.equivEntropyNat` and
Translation 1/2/3 precedent). -/
def polyListEquivEntropyNat :
    List PolynomialRat ≃
      { e : EntropyNat // ∃ P : List PolynomialRat,
          polyListToEntropyNat P = e } where
  toFun P := ⟨polyListToEntropyNat P, ⟨P, rfl⟩⟩
  invFun e := polyListFromEntropyNat e.val
  left_inv P := polyListFromEntropyNat_toEntropyNat P
  right_inv := by
    rintro ⟨e, ⟨P, hP⟩⟩
    apply Subtype.ext
    show polyListToEntropyNat (polyListFromEntropyNat e) = e
    rw [← hP, polyListFromEntropyNat_toEntropyNat]

/-! # §2 — Lifted list operations as functions on `EntropyNat`

The list constructors `::` (cons) and `++` (append) push through the
bijection above to give *derived* natural-number operations. As before,
these are not standard EntropyNat arithmetic — they are the list
constructors expressed in the encoded representation: each lifted op
decodes its inputs to lists, applies the list constructor, and
re-encodes.

The operational reading: under the bit-list encoding, *list concatenation
of polynomial systems is a particular function on natural numbers*. -/

/-- List append (system concatenation) lifted to `EntropyNat`. -/
def appendEntropyNat (e f : EntropyNat) : EntropyNat :=
  polyListToEntropyNat
    (polyListFromEntropyNat e ++ polyListFromEntropyNat f)

/-- List cons (prepend one polynomial) lifted to `EntropyNat`. The first
argument is the encoded polynomial (a `PolynomialRat.toEntropyNat`); the
second is the encoded tail system (a `polyListToEntropyNat`). -/
def consEntropyNat (p : EntropyNat) (rest : EntropyNat) : EntropyNat :=
  polyListToEntropyNat
    (PolynomialRat.ofEntropyNat p :: polyListFromEntropyNat rest)

/-! # §3 — Homomorphism / transport theorems

The diagram-commutes statements: list-level constructors followed by
`polyListToEntropyNat` equal `polyListToEntropyNat` (or
`PolynomialRat.toEntropyNat`) on each input followed by the lifted op.
Each closes by `unfold` + `rw` on the round-trip lemmas. Closure
`{propext, Quot.sound}`. -/

/-- **Append transport.** System concatenation is a derived
natural-number operation under the encoding. -/
theorem append_eq_appendEntropyNat (P Q : List PolynomialRat) :
    polyListToEntropyNat (P ++ Q)
      = appendEntropyNat
          (polyListToEntropyNat P)
          (polyListToEntropyNat Q) := by
  unfold appendEntropyNat
  rw [polyListFromEntropyNat_toEntropyNat P,
      polyListFromEntropyNat_toEntropyNat Q]

/-- **Cons transport.** Prepending a polynomial to a system is a derived
natural-number operation under the encoding. -/
theorem cons_eq_consEntropyNat (p : PolynomialRat) (rest : List PolynomialRat) :
    polyListToEntropyNat (p :: rest)
      = consEntropyNat
          (PolynomialRat.toEntropyNat p)
          (polyListToEntropyNat rest) := by
  unfold consEntropyNat
  rw [PolynomialRat.ofEntropyNat_toEntropyNat p,
      polyListFromEntropyNat_toEntropyNat rest]

/-! # §4 — Capstone: every polynomial system IS a natural number

Combining `PolynomialAsNat.lean` (the per-polynomial layer) with this
file (the per-system layer):

* `PolynomialRat ≃ image ⊆ EntropyNat`, with `add`/`mul`/`neg` transport.
* `List PolynomialRat ≃ image ⊆ EntropyNat`, with `++`/`::` transport.

Under the canonical bit-list encoding, the structure
`(List PolynomialRat, ::, ++)` is bijectively the structure
`(image ⊆ EntropyNat, consEntropyNat, appendEntropyNat)`. **Every
polynomial system of equations is a natural number; every list-level
constructor on systems is a natural-number operation under that
identification.** -/

end InformationTheory
