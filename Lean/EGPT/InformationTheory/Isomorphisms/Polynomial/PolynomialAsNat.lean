-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.

/- PolynomialAsNat — every constructive rational polynomial over `EntropyRat`
*is* a natural number under the canonical bit-list encoding, and the
polynomial constructors (`add`, `mul`, `neg`) are bijectively a derived
natural-number operation under that encoding.

The chain `PolynomialRat ≃ image ⊆ ℕ` is already proven in
`InformationTheory/EntropyNumber/Polynomial.lean` as
`polynomialRatEquivImageNat` (closure `{propext, Quot.sound}`). This file
composes that with `entropyNatEquivNat` (Basic.lean) to land the bijection
on the EntropyNat side, then proves the *homomorphism property*: for any
`p, q : PolynomialRat`,

  `(PolynomialRat.add p q).toEntropyNat
     = addEntropyNat p.toEntropyNat q.toEntropyNat`

(and likewise for `mul`, `neg`). Each is a one-line consequence of
`PolynomialRat.ofNat'_toNat'`, so the closure stays at `{propext,
Quot.sound}` — same bar as the three P=NP capstones.

The system-level bijection `List PolynomialRat ≃ EntropyNat` is supplied
by `InformationTheory.Isomorphisms.CNF.CNFAsEntropyNat.polynomialListToNat` /
`polynomialListFromNat_toNat`; this file is the per-polynomial layer the
list encoder builds on.

Tagged ID5 (Abadir): the information-theoretic-number-hierarchy reading
applied to PolynomialRat — *every constructive rational polynomial is
canonically and computably a natural number, and every polynomial
constructor is a derived natural-number operation under that canonical
identification*. -/

module

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

/-! # §1 — The bijection `PolynomialRat ≃ EntropyNat`

`PolynomialRat.toNat'` / `PolynomialRat.ofNat'` from
`EntropyNumber/Polynomial.lean` are the canonical bit-list ↔ ℕ encoding
of the inductive `PolynomialRat` syntax tree. Composing with
`entropyNatEquivNat.symm : ℕ ≃ EntropyNat` lifts this to the EntropyNat
side.

Per the FORK_README discipline, *EntropyNat is the constructive
information-theoretic encoding of ℕ* — they are the same set up to
canonical isomorphism. Saying "PolynomialRat ≃ EntropyNat" is the same
statement as "every PolynomialRat is, structurally, a natural number
under the canonical bit-list encoding". -/

namespace PolynomialRat

/-- A `PolynomialRat` as an `EntropyNat`: encode the syntax tree to a
bit-list (then to ℕ via `listBoolToNat`), then convert ℕ to EntropyNat
via `entropyNatEquivNat.symm`. Both legs are computable; closure
`{propext, Quot.sound}`. -/
def toEntropyNat (p : PolynomialRat) : EntropyNat :=
  entropyNatEquivNat.symm (PolynomialRat.toNat' p)

/-- Recover a `PolynomialRat` from its `EntropyNat` encoding. Off-image
inputs default to a `PolynomialRat.id` placeholder via the underlying
`ofNat'` parser; on-image inputs round-trip exactly. -/
def ofEntropyNat (e : EntropyNat) : PolynomialRat :=
  PolynomialRat.ofNat' (entropyNatEquivNat e)

/-- Round-trip: decoding the EntropyNat encoding of a polynomial recovers
the polynomial. -/
theorem ofEntropyNat_toEntropyNat (p : PolynomialRat) :
    PolynomialRat.ofEntropyNat (PolynomialRat.toEntropyNat p) = p := by
  unfold PolynomialRat.ofEntropyNat PolynomialRat.toEntropyNat
  rw [Equiv.apply_symm_apply]
  exact PolynomialRat.ofNat'_toNat' p

/-- **The bijection.** `PolynomialRat ≃ image ⊆ EntropyNat`, image-subtype
shape (matches `polynomialRatEquivImageNat` and Translation 1/2/3
precedent). -/
def equivEntropyNat :
    PolynomialRat ≃
      { e : EntropyNat // ∃ p : PolynomialRat,
          PolynomialRat.toEntropyNat p = e } where
  toFun p := ⟨PolynomialRat.toEntropyNat p, ⟨p, rfl⟩⟩
  invFun e := PolynomialRat.ofEntropyNat e.val
  left_inv p := PolynomialRat.ofEntropyNat_toEntropyNat p
  right_inv := by
    rintro ⟨e, ⟨p, hp⟩⟩
    apply Subtype.ext
    show PolynomialRat.toEntropyNat (PolynomialRat.ofEntropyNat e) = e
    rw [← hp, PolynomialRat.ofEntropyNat_toEntropyNat]

end PolynomialRat

/-! # §2 — Lifted polynomial operations as functions on `EntropyNat`

The polynomial constructors `add`, `mul`, `neg` push through the
bijection above to give *derived* natural-number operations:
`addEntropyNat`, `mulEntropyNat`, `negEntropyNat`.

These are **not** standard EntropyNat arithmetic. They are the polynomial
constructors expressed in the encoded representation: each lifted op
decodes its inputs to polynomials, applies the polynomial constructor,
and re-encodes. The operational reading: under the bit-list encoding,
*polynomial addition is a particular function on natural numbers* — the
function that "adds polynomials in their syntactic-tree form". -/

namespace PolynomialRat

/-- Polynomial addition lifted to `EntropyNat`. -/
def addEntropyNat (e f : EntropyNat) : EntropyNat :=
  PolynomialRat.toEntropyNat
    (PolynomialRat.add
      (PolynomialRat.ofEntropyNat e)
      (PolynomialRat.ofEntropyNat f))

/-- Polynomial multiplication lifted to `EntropyNat`. -/
def mulEntropyNat (e f : EntropyNat) : EntropyNat :=
  PolynomialRat.toEntropyNat
    (PolynomialRat.mul
      (PolynomialRat.ofEntropyNat e)
      (PolynomialRat.ofEntropyNat f))

/-- Polynomial negation lifted to `EntropyNat`. -/
def negEntropyNat (e : EntropyNat) : EntropyNat :=
  PolynomialRat.toEntropyNat
    (PolynomialRat.neg (PolynomialRat.ofEntropyNat e))

/-! # §3 — Homomorphism / transport theorems

The key claim — *the sum (or product, or negation) of polynomials is
bijectively the corresponding lifted-Nat operation under the encoding* —
is the diagram-commutes statement: `(constructor) ; toEntropyNat` equals
`toEntropyNat × toEntropyNat ; (lifted constructor)`.

Each proof is a one-liner: `unfold` the lifted op, then rewrite by
`ofEntropyNat_toEntropyNat` on each input. Closure `{propext,
Quot.sound}`. -/

/-- **Add transport.** Polynomial addition is a derived natural-number
operation under the encoding. -/
theorem add_eq_addEntropyNat (p q : PolynomialRat) :
    PolynomialRat.toEntropyNat (PolynomialRat.add p q)
      = PolynomialRat.addEntropyNat
          (PolynomialRat.toEntropyNat p)
          (PolynomialRat.toEntropyNat q) := by
  unfold PolynomialRat.addEntropyNat
  rw [PolynomialRat.ofEntropyNat_toEntropyNat p,
      PolynomialRat.ofEntropyNat_toEntropyNat q]

/-- **Mul transport.** Polynomial multiplication is a derived
natural-number operation under the encoding. -/
theorem mul_eq_mulEntropyNat (p q : PolynomialRat) :
    PolynomialRat.toEntropyNat (PolynomialRat.mul p q)
      = PolynomialRat.mulEntropyNat
          (PolynomialRat.toEntropyNat p)
          (PolynomialRat.toEntropyNat q) := by
  unfold PolynomialRat.mulEntropyNat
  rw [PolynomialRat.ofEntropyNat_toEntropyNat p,
      PolynomialRat.ofEntropyNat_toEntropyNat q]

/-- **Neg transport.** Polynomial negation is a derived natural-number
operation under the encoding. -/
theorem neg_eq_negEntropyNat (p : PolynomialRat) :
    PolynomialRat.toEntropyNat (PolynomialRat.neg p)
      = PolynomialRat.negEntropyNat (PolynomialRat.toEntropyNat p) := by
  unfold PolynomialRat.negEntropyNat
  rw [PolynomialRat.ofEntropyNat_toEntropyNat p]

/-! # §4 — Capstone: every polynomial IS a natural number

The composition of §1 and §3 says: under the canonical bit-list
encoding, the structure `(PolynomialRat, +, *, neg)` is bijectively the
structure `(image ⊆ EntropyNat, addEntropyNat, mulEntropyNat,
negEntropyNat)`. Every polynomial is a natural number; every polynomial
arithmetic operation IS a natural-number operation under that bijection.

The next layer up — `List PolynomialRat ≃ EntropyNat` ("every polynomial
**system** of equations is a natural number") — is supplied by
`InformationTheory.Isomorphisms.CNF.CNFAsEntropyNat.polynomialListToNat`, which
length-prefixes per-polynomial encodings and composes through the same
`listBoolToNat` substrate. The same homomorphism pattern (transport
through encode/decode) lifts list-concatenation and per-clause operations
to derived ℕ operations. -/

end PolynomialRat

end InformationTheory
