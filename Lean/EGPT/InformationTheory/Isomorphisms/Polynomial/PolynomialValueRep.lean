-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.

/- PolynomialValueRep — the **value representation** of a dense polynomial:
samples at integer powers of 2.

Mirrors `EGPTPolynomial.toValueRepresentation` (forward) and
`EGPTPolynomial.fromValueRepresentation` (inverse, Newton DD). Both
directions are computable and bit-for-bit match the JS reference encoder
on the JS fixture corpus.

Combined with the existing PolynomialAsNat / PolynomialSystemAsNat /
PolynomialMatrixAsNat tower, this file exposes another bijective branch:

  GEMM (Mathlib Matrix)
   ↓
  matrix in coefficient form    (List DensePolyRat)
   ↕  (matrixEquivEntropyNat — already proved)
  polynomial system             (List PolynomialRat)
   ↕  (polyListEquivEntropyNat — already proved)
  encoded ℕ                     (EntropyNat)

with the *additional* per-row branch:

  dense polynomial              (DensePolyRat)
   ↕  (toValueRep / fromValueRep — this file)
  value representation          (List EntropyRat, samples at 2^0..2^(D))

Closure of the structural defs: `{propext, Quot.sound}`. The general
round-trip theorem `fromValueRep (toValueRep p) = p` is the standard
Vandermonde-invertibility fact (Newton DD is a constructive interpolant);
this file ships fixture-level round-trips closed by `decide` on the
underlying canonical `List Bool` substrate. The general theorem can be
added later without changing any function in this file.

Tagged ID5 (Abadir): adds the value-representation bijective branch to
the polynomial-as-Nat tower, exposing GEMM ↔ matrix ↔ value-rep ↔ Nat
as the alternate paths. -/

module

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

/-! ## EntropyRat division and `Inhabited` instance

`EntropyRat.inv` (already in `Polynomial.lean`) gives multiplicative
inverse; division is `mul ∘ inv`. The `Inhabited` instance is needed for
total `List.get!` indexing inside the Newton DD machinery. -/

instance : Inhabited EntropyRat := ⟨EntropyRat.zero⟩

/-- Division on `EntropyRat`: `a / b := a · b⁻¹`. -/
def EntropyRat.div (a b : EntropyRat) : EntropyRat :=
  EntropyRat.mul a (EntropyRat.inv b)

namespace DensePolyRat

/-! # §1 — Powers-of-2 sampling base

The EGPT-canonical sample point set is `{2^0, 2^1, 2^2, …}`. For a
polynomial of length L (degree D = L − 1), exactly D+1 samples at
`2^0, …, 2^D` form an invertible Vandermonde system (powers of 2 are
distinct, hence the Vandermonde determinant is nonzero). -/

/-- The k-th canonical sample point: `2^k` as `EntropyRat`. -/
def samplePoint (k : ℕ) : EntropyRat :=
  EntropyRat.ofNat (2 ^ k)

/-- **Forward — `toValueRep`.** Sample a polynomial at integer powers
of 2: returns `[P(2^0), P(2^1), …, P(2^(L-1))]` for `L = max(p.length, 1)`.
Mirrors `EGPTPolynomial.toValueRepresentation`. -/
def toValueRep (p : DensePolyRat) : List EntropyRat :=
  let n := p.length.max 1
  (List.range n).map
    (fun k => DensePolyRat.eval p (DensePolyRat.samplePoint k))

/-! # §2 — Newton divided differences inverse

All recursion is direct/structural — no `List.get!` indexing, no
`List.range.foldl` accumulator pairs. `decide` chases iota+delta on
inductive list patterns very well, but trips on `panic!`-fallback
indexing and accumulator-pair folds when the body involves nested
`Decidable` tests. -/

/-- DD step kernel. Given two x-windows (left starting at index 0,
right shifted by `depth+1`) and a row, produces the next-depth row:
each output entry is `(b - a) / (xR - xL)` for consecutive
`(xL, xR, a, b)` quadruples. Structural recursion on the row. -/
def ddStepRec :
    List EntropyRat → List EntropyRat → List EntropyRat →
    List EntropyRat
  | xL :: xLrest, xR :: xRrest, a :: b :: rest =>
      EntropyRat.div
        (EntropyRat.sub b a)
        (EntropyRat.sub xR xL) ::
          ddStepRec xLrest xRrest (b :: rest)
  | _, _, _ => []

/-- One DD step. Given xs, offset (already 1-indexed: caller passes
`depth + 1` for the depth-`depth+1` round), and current row, produces
the next row via `ddStepRec` over the sliding `(xs, xs.drop offset)`
windows. -/
def ddStep (xs : List EntropyRat) (offset : ℕ)
    (row : List EntropyRat) : List EntropyRat :=
  ddStepRec xs (xs.drop offset) row

/-- Newton-basis coefficients via iterative divided differences.
Fuel-bounded for structural recursion on `fuel`. The natural fuel is
the sample-list length. -/
def newtonCoeffsAux :
    ℕ → List EntropyRat → List EntropyRat → ℕ → List EntropyRat
  | 0,        _,  _,           _      => []
  | _ + 1,    _,  [],          _      => []
  | fuel + 1, xs, s :: ss,     depth  =>
      s :: newtonCoeffsAux fuel xs
            (ddStep xs (depth + 1) (s :: ss)) (depth + 1)

def newtonCoeffs (xs samples : List EntropyRat) : List EntropyRat :=
  newtonCoeffsAux samples.length xs samples 0

/-- Convert Newton-basis coefficients to monomial-basis coefficients via
the standard expansion `c₀ + c₁(X − x₀) + c₂(X − x₀)(X − x₁) + …`.

Direct structural recursion on the coefficient list:
* Empty list: return the accumulated result.
* Single coefficient (last iter): add `c · basis` to result, no basis
  update.
* Cons (intermediate iter): add `c · basis` to result, multiply basis
  by `(X − x_i)` for the next iter, recurse on the tail. -/
def newtonToMonomialAux (xs : List EntropyRat) (basis : DensePolyRat) :
    List EntropyRat → DensePolyRat → DensePolyRat
  | [],          result => result
  | [c],         result =>
      let term := basis.map (fun b => EntropyRat.mul c b)
      DensePolyRat.add result term
  | c :: c' :: rest, result =>
      let term := basis.map (fun b => EntropyRat.mul c b)
      let newResult := DensePolyRat.add result term
      match xs with
      | []           => newResult
      | xi :: xsRest =>
          let factor := [EntropyRat.neg xi, EntropyRat.one]
          let newBasis := DensePolyRat.mul basis factor
          newtonToMonomialAux xsRest newBasis (c' :: rest) newResult

def newtonToMonomial (newtonCoeffs xs : List EntropyRat) : DensePolyRat :=
  newtonToMonomialAux xs [EntropyRat.one] newtonCoeffs ([] : DensePolyRat)

/-- **Inverse — `fromValueRep`.** Recover a dense polynomial from its
powers-of-2 value representation via Newton DD interpolation. Mirrors
`EGPTPolynomial.fromValueRepresentation`. -/
def fromValueRep (samples : List EntropyRat) : DensePolyRat :=
  let N := samples.length
  let xs := (List.range N).map DensePolyRat.samplePoint
  let nc := newtonCoeffs xs samples
  newtonToMonomial nc xs

end DensePolyRat

/-! # §3 — Concrete fixtures from `toValueRepresentation.test.mjs`

Forward + round-trip pairs. Each closes by `decide` on the canonical
`List Bool` substrate of `EntropyRat`. -/

namespace DensePolyRatValueRepFixtures

/-- Concise alias for `EntropyRat.ofNat n`. -/
private def R (n : ℕ) : EntropyRat := EntropyRat.ofNat n

/-- Forward: `P(x) = 1 + 2x + 3x²` samples at `{1, 2, 4}` give `[6, 17, 57]`.
Reference fixture: `toValueRepresentation.test.mjs:87`. -/
example :
    DensePolyRat.toValueRep [R 1, R 2, R 3]
      = [R 6, R 17, R 57] := by
  decide

/-- Degree-0 forward: `P(x) = 42` samples to `[42]`.
Reference fixture: `toValueRepresentation.test.mjs:47`. -/
example :
    DensePolyRat.toValueRep [R 42] = [R 42] := by
  decide

set_option maxRecDepth 4000 in
/-- Degree-0 round-trip: a constant polynomial round-trips through
the value representation unchanged. -/
example :
    DensePolyRat.fromValueRep
        (DensePolyRat.toValueRep [R 42]) = [R 42] := by
  decide

set_option maxRecDepth 4000 in
/-- Degree-2 round-trip: `[1, 2, 3]` survives `fromValueRep ∘ toValueRep`. -/
example :
    DensePolyRat.fromValueRep
        (DensePolyRat.toValueRep [R 1, R 2, R 3]) = [R 1, R 2, R 3] := by
  decide

end DensePolyRatValueRepFixtures

end InformationTheory
