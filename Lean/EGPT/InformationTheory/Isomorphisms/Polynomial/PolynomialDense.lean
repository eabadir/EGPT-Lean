-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.

/- PolynomialDense — coefficient-list rational polynomials over `EntropyRat`.

Mirrors `EGPTPolynomial.js` (FRAQTL repo / EGPTMath) using the same canonical
`(sign, num, den)` triple substrate the rest of the InformationTheory tree
uses. Built-for-extraction: every operation is a plain `def`, never
`noncomputable`; the JS-fixture round-trips close by `decide` on the
underlying `List Bool` substrate.

Closure target: `{propext, Quot.sound}` — the same bar as the three P=NP
chains and Translation 1/2/3.

Tagged ID5 (Abadir): supplies a constructive, computable polynomial
arithmetic surface that mirrors the JS reference encoder bit-for-bit and
provides the bridge into `PolynomialRat`'s tree form for downstream
proofs. -/

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

/-! ## `EntropyRat.sub` — top-level helper used by the dense polynomial layer. -/

/-- Subtraction on `EntropyRat`: `a - b := a + (-b)`. Computable; mirrors
the existing `PolynomialRat.sub` (which goes through the inductive `neg`
constructor) at the coefficient level. -/
def EntropyRat.sub (a b : EntropyRat) : EntropyRat :=
  EntropyRat.add a (EntropyRat.neg b)

/-! ## Dense rational polynomial (coefficient-list MVP)

Mirrors `EGPTPolynomial.js`: a polynomial `a₀ + a₁·x + a₂·x² + …` is a
`List EntropyRat` where index `i` is the coefficient of `x^i`. The empty
list represents the zero polynomial; `[c]` represents the constant `c`.

We expose the type as an `abbrev` so all `List` machinery (`length`,
`map`, etc.) transfers without wrapper boilerplate. -/

/-- Coefficient-list polynomial over `EntropyRat`: `a₀ + a₁·x + a₂·x² + …`. -/
abbrev DensePolyRat : Type := List EntropyRat

namespace DensePolyRat

/-! ### Coefficient-wise addition / subtraction (T1) -/

/-- Coefficient-wise addition with right-padding. Mirrors
`EGPTPolynomial.add` — `O(max deg)`. -/
def add : DensePolyRat → DensePolyRat → DensePolyRat
  | [],        bs        => bs
  | (a :: as), []        => a :: as
  | (a :: as), (b :: bs) => EntropyRat.add a b :: add as bs

/-- Coefficient-wise subtraction with right-padding. -/
def sub : DensePolyRat → DensePolyRat → DensePolyRat
  | [],        bs        => bs.map EntropyRat.neg
  | (a :: as), []        => a :: as
  | (a :: as), (b :: bs) => EntropyRat.sub a b :: sub as bs

/-! ### Convolution multiplication (T1) -/

/-- Convolution multiplication, `O(deg p · deg q)`.
`(a + x·tail) · bs = (a · bs) + x · (tail · bs)`, expressed structurally
as scaling the second list by `a` and recursing with a one-place shift
(the prepended `EntropyRat.zero`). Mirrors `EGPTPolynomial.multiply`. -/
def mul : DensePolyRat → DensePolyRat → DensePolyRat
  | [],        _  => []
  | (a :: as), bs =>
      add (bs.map (fun b => EntropyRat.mul a b))
          (EntropyRat.zero :: mul as bs)

/-! ### Horner evaluation (T2) -/

/-- Horner evaluation: `a₀ + x·(a₁ + x·(a₂ + …))`. Empty polynomial
evaluates to `EntropyRat.zero`. Mirrors `EGPTPolynomial.evaluateAt`. -/
def eval : DensePolyRat → EntropyRat → EntropyRat
  | [],        _ => EntropyRat.zero
  | (a :: as), x => EntropyRat.add a (EntropyRat.mul x (eval as x))

end DensePolyRat

/-! ## Bridge to `PolynomialRat`

The Horner-factored tree form of a dense polynomial. Every dense `eval`
agrees with `PolynomialRat.eval` on this tree, so downstream proofs that
already speak about `PolynomialRat` (e.g. Translation 1's
`clausePoly` chain) lift to dense form via the bridge lemma below. -/

/-- Convert a dense polynomial to a Horner-factored `PolynomialRat` tree:
`a₀ + X·(a₁ + X·(a₂ + …))`. The empty polynomial maps to the constant
zero. -/
def DensePolyRat.toPolynomialRat : DensePolyRat → PolynomialRat
  | []        => PolynomialRat.const EntropyRat.zero
  | (a :: as) =>
      PolynomialRat.add
        (PolynomialRat.const a)
        (PolynomialRat.mul PolynomialRat.id
          (DensePolyRat.toPolynomialRat as))

/-- **Bridge lemma.** Dense Horner evaluation agrees with
`PolynomialRat.eval` on the Horner-factored tree. Choice-free; closure
`{propext, Quot.sound}`. -/
theorem DensePolyRat.eval_eq_polyEval (p : DensePolyRat) (x : EntropyRat) :
    DensePolyRat.eval p x
      = (DensePolyRat.toPolynomialRat p).eval x := by
  induction p with
  | nil =>
    show EntropyRat.zero
       = (PolynomialRat.const EntropyRat.zero).eval x
    rfl
  | cons a as ih =>
    -- LHS reduces by `DensePolyRat.eval` cons-case;
    -- RHS reduces by `toPolynomialRat` cons-case + `PolynomialRat.eval`
    -- on add/mul/const/id. Both sides land on
    --   `add a (mul x (...as...))`
    -- where the residual differs only by which of
    --   `DensePolyRat.eval as x`   vs   `(toPolynomialRat as).eval x`
    -- appears in the right factor — closed by `ih`.
    show EntropyRat.add a
          (EntropyRat.mul x (DensePolyRat.eval as x))
       = EntropyRat.add a
          (EntropyRat.mul x ((DensePolyRat.toPolynomialRat as).eval x))
    rw [ih]

/-! ## Concrete fixtures from `EGPTPolynomial.js`

T1+T2 surface — three fixtures from the JS test suite, all closing by
`decide` on the underlying canonical `List Bool` substrate of
`EntropyRat`. The kernel reduces both sides to canonical `mk` forms via
the constructive arithmetic and checks list equality.

Procedure (mirrors Translation 1/2/3 fixtures):
* Pick a fixture from `EGPTPolynomialTest.js`.
* Translate the inputs to `EntropyRat.ofNat` / `EntropyRat.mk` literals.
* Close with `decide`. -/

namespace DensePolyRatFixtures

/-- Concise alias for `EntropyRat.ofNat n`. -/
private def R (n : ℕ) : EntropyRat := EntropyRat.ofNat n

/-- T1.1 — coefficient-wise addition: `[1, 2] + [3, 4] = [4, 6]`.
Reference fixture: `EGPTPolynomialTest.js:28`. -/
example :
    DensePolyRat.add [R 1, R 2] [R 3, R 4]
      = [R 4, R 6] := by
  decide

/-- T1.3 — convolution: `(1 + 2x)(3 + 4x) = 3 + 10x + 8x²`.
Reference fixture: `EGPTPolynomialTest.js:52`. -/
example :
    DensePolyRat.mul [R 1, R 2] [R 3, R 4]
      = [R 3, R 10, R 8] := by
  decide

/-- T2.1 — Horner evaluation: `(3 + 2x + x²)|_{x = 2} = 11`.
Reference fixture: `EGPTPolynomialTest.js:106`. -/
example :
    DensePolyRat.eval [R 3, R 2, R 1] (R 2) = R 11 := by
  decide

end DensePolyRatFixtures

end InformationTheory
