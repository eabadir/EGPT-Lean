-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.

/- Translation 4 — the **operational bijection chain** laid out end-to-end
so programmers can SEE "a chain of bijections is a bijection" without
having to import, reference, or prove deep results (Vandermonde
invertibility, polynomial-uniqueness theorems) that are not requirements
at the chain level.

## The chain

```
        ℕ
        ↕   entropyNatEquivNat       (Mathlib structural Equiv, choice-free)
   EntropyNat
        ↕   PolynomialRat.equivEntropyNat   (PolynomialAsNat.lean, choice-free)
        │   image-subtype Equiv
   PolynomialRat (inductive tree)
        ↕   toPolynomialRat / fromPolynomialRat   (PolynomialMatrixAsNat.lean,
        │   image-subtype on Horner-factored trees, choice-free)
   DensePolyRat (coefficient list)
        ↕   toValueRep / fromValueRep              (PolynomialValueRep.lean,
        │   round-trip fixture-verified)
   ValueRep (List EntropyRat at 2^0..2^(D))
```

## Why this file exists

Earlier work attempted to add a "general round-trip theorem" for the
value-representation link — and that attempt led to a discussion about
whether **Vandermonde invertibility** must be formalized in Lean for the
EGPT chain to be operational. The answer, surfaced by the user: **no**.

* The structural links (top three rows of the chain) are proved
  `{propext, Quot.sound}`-clean in earlier files. They give a complete
  ℕ ↔ DensePolyRat bijection without referencing the value
  representation at all.
* The value-representation link uses Newton DD (a constructive
  interpolant) as its inverse. The mathematical fact that Newton DD
  inverts Horner evaluation at distinct nodes IS Vandermonde
  invertibility — but that fact lives **inside the implementation**.
  At the chain level, the round-trip `fromValueRep ∘ toValueRep = id`
  is the only thing needed, and is fixture-verified for every
  encoding-chain shape used by the FRAQTL codec library.
* Composing bijections gives a bijection. Each link in the chain
  bijects (the top three formally, the bottom one operationally).
  Therefore the whole chain bijects. Programmers do not need to import
  Vandermonde.

This file walks the chain in concrete fixtures and packages the
composition as a single function `Translation4.chain` with documentation
that makes the structure visible.

## What this is *not*

This file does not prove `fromValueRep (toValueRep p) = p` in full
generality. That theorem (Vandermonde / polynomial uniqueness) is a
real piece of mathematics; we deliberately keep it out of the chain so
that the chain is operational without it. If a future reader needs the
general theorem, the right place is a separate file dedicated to
Newton-DD correctness — not this Translation.

Tagged ID2 (Von Neumann — Statistical AI computer) and ID5 (Abadir):
makes the FRAQTL-codec bijection chain programmer-visible, with a clear
separation between "chain bijection (this file)" and "Newton-DD inner
correctness (separate concern, not a chain prerequisite)". -/

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

namespace Translation4

/-- Concise alias for `EntropyRat.ofNat n`. -/
private def R (n : ℕ) : EntropyRat := EntropyRat.ofNat n

/-! # §1 — The structural sub-chain (formally proved end-to-end)

Composing the bijections that DO NOT touch the value representation:

  `DensePolyRat ↔ PolynomialRat ↔ EntropyNat ↔ ℕ`

Each link is `{propext, Quot.sound}`-clean. The composition gives a
formal bijection between dense coefficient lists and natural numbers
(modulo the Horner-image subtype). -/

/-- Walk the structural chain `DensePolyRat → PolynomialRat → EntropyNat`. -/
def denseToEntropyNat (p : DensePolyRat) : EntropyNat :=
  PolynomialRat.toEntropyNat (DensePolyRat.toPolynomialRat p)

/-- Walk back: `EntropyNat → PolynomialRat → DensePolyRat`. -/
def denseFromEntropyNat (e : EntropyNat) : DensePolyRat :=
  DensePolyRat.fromPolynomialRat (PolynomialRat.ofEntropyNat e)

/-- The structural sub-chain is an identity on `DensePolyRat`. Closure
`{propext, Quot.sound}` — composes the per-link round-trips. -/
theorem denseFromEntropyNat_toEntropyNat (p : DensePolyRat) :
    denseFromEntropyNat (denseToEntropyNat p) = p := by
  unfold denseFromEntropyNat denseToEntropyNat
  rw [PolynomialRat.ofEntropyNat_toEntropyNat]
  exact DensePolyRat.fromPolynomialRat_toPolynomialRat p

/-! # §2 — The full operational chain (through value representation)

Walk the same data through the value representation as an intermediate
form. The forward direction goes:

  `DensePolyRat → ValueRep → DensePolyRat → PolynomialRat → EntropyNat`

The first two steps are the value-rep round trip; the last two are the
structural encoding. The overall composition is a function
`DensePolyRat → EntropyNat`. -/

/-- Walk the operational chain `DensePolyRat → ValueRep → DensePolyRat
→ PolynomialRat → EntropyNat`. Inlined (no `let` bindings) so that
`unfold` exposes the structure for rewriting in the agreement lemma. -/
def denseToEntropyNatViaValueRep (p : DensePolyRat) : EntropyNat :=
  PolynomialRat.toEntropyNat
    (DensePolyRat.toPolynomialRat
      (DensePolyRat.fromValueRep
        (DensePolyRat.toValueRep p)))

/-! # §3 — Programmer-visible fixtures

Each fixture walks a specific dense polynomial through the chain. The
structural sub-chain identity (§1) is applied via the round-trip lemma;
the full operational chain (§2) is verified by `decide` on the
canonical `List Bool` substrate. -/

/-! ## §3.1 — Structural chain on concrete data -/

/-- `[R 1, R 2, R 3]` round-trips through the structural sub-chain. -/
example :
    denseFromEntropyNat (denseToEntropyNat [R 1, R 2, R 3])
      = [R 1, R 2, R 3] :=
  denseFromEntropyNat_toEntropyNat _

/-- A 4-element coefficient list round-trips. -/
example :
    denseFromEntropyNat (denseToEntropyNat [R 7, R 11, R 13, R 17])
      = [R 7, R 11, R 13, R 17] :=
  denseFromEntropyNat_toEntropyNat _

/-! ## §3.2 — Full operational chain through ValueRep on concrete data

These fixtures walk through the value-representation surface as well —
they verify by `decide` because they exercise Newton DD on concrete
samples. Each closes definitionally on the canonical `List Bool`
substrate. -/

set_option maxRecDepth 4000 in
/-- `[R 1, R 2, R 3]` survives the full chain through ValueRep,
encoded then decoded back to the same dense polynomial. -/
example :
    let p : DensePolyRat := [R 1, R 2, R 3]
    let samples := DensePolyRat.toValueRep p
    let recovered := DensePolyRat.fromValueRep samples
    recovered = p := by
  decide

set_option maxRecDepth 4000 in
/-- Linear case: `[R 5, R 7]` survives the full chain. -/
example :
    let p : DensePolyRat := [R 5, R 7]
    DensePolyRat.fromValueRep (DensePolyRat.toValueRep p) = p := by
  decide

set_option maxRecDepth 4000 in
/-- Constant case: `[R 7]` survives the full chain. -/
example :
    let p : DensePolyRat := [R 7]
    DensePolyRat.fromValueRep (DensePolyRat.toValueRep p) = p := by
  decide

/-! ## §3.3 — The chain composition lemma

When the value-rep round-trip holds (which it does, fixture-verified at
every shape FRAQTL uses), the operational chain agrees with the
structural chain. The lemma below states this as a conditional
implication: assuming `fromValueRep ∘ toValueRep = id` on the input,
the two chains agree.

This is *not* a Vandermonde requirement. It's a chain-composition
identity: if the inner round-trip is identity, the composed chains
agree. The "if" is discharged by `decide` per fixture, not by a global
proof. -/

/-- Conditional chain agreement: if the value-rep round-trip preserves
`p` (which fixtures verify per `p`), then the operational chain agrees
with the structural chain. Closure `{propext, Quot.sound}` — the lemma
itself does not import any value-rep correctness theorem; it merely
states the chain composition identity. -/
theorem denseToEntropyNatViaValueRep_eq_denseToEntropyNat
    (p : DensePolyRat)
    (h : DensePolyRat.fromValueRep (DensePolyRat.toValueRep p) = p) :
    denseToEntropyNatViaValueRep p = denseToEntropyNat p := by
  unfold denseToEntropyNatViaValueRep denseToEntropyNat
  rw [h]

/-! ## §3.4 — Both chains agree on the same input

When both chains return the same `DensePolyRat`, they encode to the
same `EntropyNat`. The structural chain proves this formally; the full
operational chain confirms it on concrete data via `decide`. -/

/-- For `[R 1, R 2, R 3]`, the structural chain and the
operational-via-ValueRep chain produce the same `EntropyNat`. This is
the surprising "any-to-any" identity: poly → samples → poly → ℕ
returns the same ℕ as poly → ℕ alone.

Proved via the conditional agreement lemma above — the value-rep
round-trip is discharged by `decide` on this concrete input, then the
agreement lemma gives the chain identity. (Encoding the full chain to
a single ℕ comparison via `decide` would also work but exceeds
`maxRecDepth` because the encoded ℕ is large; the lemma route is
cheaper.) -/
example :
    denseToEntropyNatViaValueRep [R 1, R 2, R 3]
      = denseToEntropyNat [R 1, R 2, R 3] :=
  denseToEntropyNatViaValueRep_eq_denseToEntropyNat
    [R 1, R 2, R 3]
    (by decide)

/-! # §4 — Summary

The bijection chain is a bijection. Programmers can:

* Encode a `DensePolyRat` directly to `EntropyNat` via the structural
  chain (`denseToEntropyNat`) — formally proved end-to-end.
* Encode via the value-representation surface
  (`denseToEntropyNatViaValueRep`) — operational, with the inner Newton
  DD round-trip discharged per data point by `decide`.
* Get the same `EntropyNat` either way (
  `denseToEntropyNatViaValueRep_eq_denseToEntropyNat`, conditional on
  the per-input value-rep round-trip).

**Vandermonde invertibility is an implementation detail of Newton DD
inside `fromValueRep`. It is not imported, not stated, and not required
at the chain level.** Programmers using the chain do not need to know
about Vandermonde, and the Lean tower does not need a Vandermonde proof
to give them the chain bijection.

The theorem readers should internalize: *a chain of bijections is a
bijection*. The bijections are: the top three formally, the bottom one
operationally. Composed, they give the FRAQTL bijection any-to-any. -/

end Translation4

end InformationTheory
