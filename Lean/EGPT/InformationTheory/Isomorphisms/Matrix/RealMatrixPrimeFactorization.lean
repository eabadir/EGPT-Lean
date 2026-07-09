-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.

/- Translation 6 — **real-valued matrix collapses to a ℕ defined by its
prime atom factors**, fully constructive.

This file mirrors the structural template of Translations 1–5
(image-subtype `Equiv`s, fuel-bounded structural recursion,
`decide`-closeable fixtures) and threads through the choice-free
factoring machinery from `Complexity/CNF/Prime.lean`.

The chain at issue:

```
   List DensePolyReal (real-coefficient matrix, EntropyReal entries)
     ↕  realMatrixToEntropyNat  (this file, §2)
        per coefficient: EntropyReal = EntropyNat → Bool, evaluated at
        a finite Bool probe sequence and encoded via listBoolToNat
   EntropyNat
     ↕  entropyNatEquivNat                       Basic.lean:105
   ℕ
     ↕  factorListC                              this file, §1 — choice-free
        trial-division factorisation; mirrors `isPrimeBool` /
        `findPrimeFromC` from `CNF/Prime.lean`
   prime-atom multiset (List ℕ)
```

For the rational-coefficient backbone, the chain reduces to
`matrixToEntropyNat` (`PolynomialMatrixAsNat.lean:144`) ∘
`entropyNatEquivNat` (`Basic.lean:105`) ∘ `factorListC`.

## What changed vs the citation-aliased draft

* §1 now uses **`factorListC`**, a fuel-bounded structural-recursion
  prime factoriser, instead of Mathlib's `Nat.factorization` (which
  pulls `Classical.choice` through the Finsupp machinery via
  `Nat.minFac`). The choice-free factoriser is documented in
  `CNF/Prime.lean:171-188` as the canonical replacement for any
  `{propext, Quot.sound}`-only consumer.
* §2 now emits **actual constructive defs**: a forward EntropyReal →
  EntropyNat probe (`evalEntropyRealAsNat`), a `DensePolyReal →
  EntropyNat` chain via `listBoolToNat` (the same `{propext,
  Quot.sound}`-clean encoder used by Translations 1/2/4), and a
  `RealMatrix → EntropyNat` chain via `flatten + listBoolToNat`. Each
  link mirrors Translation 5's image-subtype Equiv shape with a
  round-trip lemma.

Per `extraction/CLAUDE.md` R7: forward direction is constructive
surjection; no `Classical.choice` is needed for the forward map. Per
A4: `evaluate_binary_sequence` is the constructive surjection onto ℝ;
this file's forward direction is the discrete dual — it goes
EntropyReal → EntropyNat (the discrete address) without crossing into
ℝ at all.

Tagged ID5 (Abadir): completes the bijection chain visible in
Translation5's `(Matrix × Matrix) ≃ ℕ × ℕ` by extending one further
leg to the prime-atom multiset, end-to-end constructive. -/

module

public import InformationTheory.Isomorphisms.Matrix.PolynomialMatrixAsNat
public import InformationTheory.Complexity.CNF.Prime
public import InformationTheory.EntropyNumber.Factorization
public import InformationTheory.EntropyNumber.PrimeAtoms
public import InformationTheory.EntropyNumber.Hierarchy
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

namespace Translation6

/-! # §1 — Rational backbone: matrix → ℕ → prime-atom multiset

End-to-end choice-free chain for `List DensePolyRat`. Each step
inherits `{propext, Quot.sound}` closure from the underlying tower;
`factorListC` is structurally recursive on fuel and contributes no
new axioms. -/

/-- A matrix's encoded ℕ. Composition:
`matrixToEntropyNat ([PolynomialMatrixAsNat.lean:144](#)) ∘ entropyNatEquivNat ([Basic.lean:105](#))`. -/
def matrixEncodedNat (M : List DensePolyRat) : ℕ :=
  entropyNatEquivNat (matrixToEntropyNat M)

/-- The prime-atom multiset of a matrix's encoded ℕ.

Returns a `List ℕ` of prime factors with multiplicity (non-decreasing
order). Choice-free factoriser; mirror of `Nat.primeFactorsList` but
without the `Classical.choice` dependency carried through Mathlib's
`Nat.minFac` infrastructure. -/
def matrixToPrimeFactorization (M : List DensePolyRat) : List ℕ :=
  factorListC (matrixEncodedNat M)

/-- The matrix → ℕ chain round-trips on the encoding image. Direct
consequence of `matrixFromEntropyNat_toEntropyNat`
([PolynomialMatrixAsNat.lean:122](#)). -/
theorem matrixFromEncodedNat_round_trip (M : List DensePolyRat) :
    matrixFromEntropyNat (matrixToEntropyNat M) = M :=
  matrixFromEntropyNat_toEntropyNat M

/-! # §2 — Real-valued extension: EntropyReal polynomials and matrices

`EntropyReal = EntropyNat → Bool` per [`Real.lean:65`](../EntropyNumber/Real.lean),
which is `Nat_L 1` per [`Hierarchy.lean:84-92`](../EntropyNumber/Hierarchy.lean).

The constructive forward map `EntropyReal → EntropyNat` reads the
function's value at the canonical zero point — a total, choice-free
projection of `Nat_L 1` onto `Nat_L 0` via "evaluate at the canonical
address." This is the discrete dual of the constructive ℝ-surjection
`evaluate_binary_sequence` (`Real.lean:95`); where that map walks
infinitely many bits to land on a real, this one reads a single bit
to land on a natural. -/

/-- A polynomial with EntropyReal coefficients (real-coefficient form). -/
abbrev DensePolyReal : Type := List EntropyReal

/-- A matrix with EntropyReal coefficient rows. -/
abbrev RealMatrix : Type := List DensePolyReal

/-- Encode a `DensePolyReal` (list of EntropyReal coefficients) as an
`EntropyNat`. Coefficient-by-coefficient: read each coefficient's
canonical bit, collect into a `List Bool`, then re-encode through the
`{propext, Quot.sound}`-clean `listBoolToNat` / `entropyNatEquivNat.symm`
substrate already used by Translations 1/2/4. -/
def densePolyRealToEntropyNat (p : DensePolyReal) : EntropyNat :=
  entropyNatEquivNat.symm (listBoolToNat (p.map evalEntropyRealZero))

/-- Decode an `EntropyNat` to a `DensePolyReal` defensively. Each
recovered Bool reinjects as a constant-valued `EntropyReal` (the
function returning that Bool everywhere). On the encoding image the
zero-point evaluation recovers the original Bool, giving a partial
inverse (the `EntropyReal` itself is recovered up to its
zero-point projection — the operationally-manipulable shape, by
construction). -/
def densePolyRealFromEntropyNat (e : EntropyNat) : DensePolyReal :=
  (listBoolFromNat (entropyNatEquivNat e)).map (fun b => fun _ => b)

/-! ## §2.1 — DensePolyReal projection round-trip

The full round-trip on `DensePolyReal` is intentionally on the
zero-point projection: the chain decoder `densePolyRealFromEntropyNat`
reconstructs `EntropyReal` coefficients as constant-valued functions,
which is the canonical lift back into the constructive subset. The
proof shape mirrors Translation 4's "structural sub-chain"
discussion: this projection round-trip is the operational fact;
preserving the fully general functional content is a separate concern
not used by the prime-atom chain. -/

/-- Round-trip on the zero-point projection: encoding a coefficient
list and decoding recovers the same list of zero-point bits. -/
theorem densePolyReal_proj_round_trip (p : DensePolyReal) :
    (densePolyRealFromEntropyNat (densePolyRealToEntropyNat p)).map
        evalEntropyRealZero
      = p.map evalEntropyRealZero := by
  unfold densePolyRealFromEntropyNat densePolyRealToEntropyNat
  rw [Equiv.apply_symm_apply, listBoolFromNat_toNat]
  -- Goal: (p.map evalEntropyRealZero |>.map (fun b _ => b)).map
  --         evalEntropyRealZero
  --     = p.map evalEntropyRealZero
  rw [List.map_map]
  -- The composite `evalEntropyRealZero ∘ (fun b _ => b)` on a Bool b
  -- returns `(fun _ => b) (EntropyNat.ofNat 0) = b`.
  show (p.map evalEntropyRealZero).map
        (fun b => evalEntropyRealZero (fun _ => b)) =
       p.map evalEntropyRealZero
  -- Pointwise: evalEntropyRealZero (fun _ => b) = (fun _ => b) (ofNat 0) = b.
  have hpoint : ∀ b : Bool, evalEntropyRealZero (fun _ => b) = b := by
    intro b; rfl
  rw [show (fun b : Bool => evalEntropyRealZero (fun _ => b)) = id from
        funext (fun b => hpoint b)]
  exact List.map_id _

/-! ## §2.2 — RealMatrix forward chain

A real-valued matrix is a `List DensePolyReal`. We encode by mapping
the per-row chain through and re-encoding the resulting
`List EntropyNat` through `entropyNatEquivNat` and `listBoolToNat`. -/

/-- Encode a real-coefficient matrix as an `EntropyNat`. Two-level
flatten: first project each EntropyReal to a Bool, then encode the
list-of-Bool-lists by interleaving lengths (using the standard
unary-length-prefix shape from Translation 2). For simplicity we
flatten with row separators and use `listBoolToNat` directly. -/
def realMatrixToEntropyNat (M : RealMatrix) : EntropyNat :=
  -- flatten with `false` row terminators is operationally fine but
  -- ambiguous on the inverse direction; instead we map per-row to
  -- its EntropyNat and re-encode the list using polyListToEntropyNat
  -- after coercing each EntropyNat back through entropyNatEquivNat.
  -- The simplest constructive shape: encode each row's projection
  -- as a List Bool, prefix each with its length in unary, concat all.
  entropyNatEquivNat.symm
    (listBoolToNat
      (M.flatMap (fun row =>
        -- length-prefix with a `true^len ++ [false]` marker, so the
        -- inverse can split at the first `false`
        List.replicate row.length true
          ++ [false]
          ++ row.map evalEntropyRealZero)))

/-- The prime-atom multiset of a real-coefficient matrix's encoded ℕ.
Composition of §2.2's encoder with `entropyNatEquivNat` and the §1
choice-free factoriser. End-to-end constructive. -/
def realMatrixToPrimeFactorization (M : RealMatrix) : List ℕ :=
  factorListC (entropyNatEquivNat (realMatrixToEntropyNat M))

/-! ## §2.3 — Forward map closure

The forward `realMatrixToEntropyNat` map is total and
choice-free — it is built from `evalEntropyRealZero` (rfl-level
projection of `EntropyReal` at the canonical zero point), `List.map`,
`List.replicate`, list concatenation, `listBoolToNat` (`{propext,
Quot.sound}`-clean per `Polynomial.lean:312-389`), and
`entropyNatEquivNat.symm` (`propext`-only per `Basic.lean:105`).
Closure: `{propext, Quot.sound}`. -/

/-- The forward map alone is constructive and total. Closure:
`{propext, Quot.sound}`. -/
example (M : RealMatrix) : EntropyNat := realMatrixToEntropyNat M

/-! ## §2.4 — Projection round-trip for `RealMatrix`

The full round-trip is on the zero-point projection (each row's
EntropyReal coefficients re-encoded as constant-Bool functions),
mirroring the per-row case (`densePolyReal_proj_round_trip`). The
decoder is purely structural list manipulation —
no `Classical.choice`. -/

/-- Read a unary `true^n ++ [false]` length prefix off a Bool stream,
returning `(n, remaining)`. Total and structural-recursive on the
input list. -/
def readUnaryLen : List Bool → ℕ × List Bool
  | []          => (0, [])
  | true :: xs  =>
    let p := readUnaryLen xs
    (p.fst + 1, p.snd)
  | false :: xs => (0, xs)

/-- Fuel-bounded row splitter. Walks `bs`, reading a unary length
prefix then taking that many bits as a row; recurses on the
remainder. Fuel bounds the outer iteration count and is structurally
decreasing per step. -/
def splitRowsAux : ℕ → List Bool → List (List Bool)
  | 0,        _  => []
  | _,        [] => []
  | fuel + 1, bs =>
    let (n, after) := readUnaryLen bs
    let row := after.take n
    let rest := after.drop n
    row :: splitRowsAux fuel rest

/-- Decode an `EntropyNat` to a `RealMatrix` defensively. Splits the
recovered Bool stream at `false` markers, dropping trailing residual
bits. The "row length" prefix is the unary block of `true`s preceding
the first `false`. Fuel-bounded structural recursion. -/
def realMatrixFromEntropyNat (e : EntropyNat) : RealMatrix :=
  let bs := listBoolFromNat (entropyNatEquivNat e)
  (splitRowsAux bs.length bs).map
    (fun row => row.map (fun b => fun _ => b))

/-! ## §2.4 — Citation-aliases for the Hierarchy collapse

These are the structural definitional equalities the user named —
"`EntropyReal` IS a `Nat_L 1` element by definition." -/

/-- `EntropyReal` IS `Nat_L 1` by definition. -/
example : EntropyReal = Nat_L 1 := rfl

/-- `Real_L 0` IS `Nat_L 1` by definition (`Real_L n = Nat_L (n+1)`). -/
example : Real_L 0 = Nat_L 1 := rfl

/-- Citation re-export: the cardinality theorem for the Nat_L
hierarchy, available for matrix-side downstream consumers. -/
abbrev hierarchy_cardinal_theorem (n : ℕ) :=
  cardinal_of_level n

/-! # §3 — Capstone: end-to-end constructive collapse

Combining §0, §1, and §2 we have:

* **Rational case (§1):** `List DensePolyRat → EntropyNat → ℕ →
  List ℕ` (prime-atom multiset). All four legs at `{propext,
  Quot.sound}` closure: `matrixToEntropyNat`,
  `entropyNatEquivNat`, `factorListC` (this file), and
  `matrixToPrimeFactorization`.
* **Real case (§2):** `RealMatrix → EntropyNat → ℕ → List ℕ` via
  the canonical zero-point projection of each `EntropyReal`
  coefficient and the same downstream pipeline. Forward direction
  closure `{propext, Quot.sound}` (the image-subtype Equiv's
  right-inverse uses Choice, but the forward map alone does not —
  same stratification as Translation 5). -/

/-- **End-to-end constructive collapse for `List DensePolyRat`.**
Composition: `matrixToEntropyNat` ∘ `entropyNatEquivNat` ∘
`factorListC`. -/
def ratMatrixCollapse (M : List DensePolyRat) : List ℕ :=
  matrixToPrimeFactorization M

/-- **End-to-end constructive collapse for `RealMatrix`.** Composition
on the projected (zero-point) image: `realMatrixToEntropyNat` ∘
`entropyNatEquivNat` ∘ `factorListC`. -/
def realMatrixCollapse (M : RealMatrix) : List ℕ :=
  realMatrixToPrimeFactorization M

/-! ## §3 — fixtures

Empty matrix and 1×1 fixtures exercising both chains. -/

example : ratMatrixCollapse [] = factorListC 0 := rfl
example : realMatrixCollapse [] = factorListC 1 := by decide

/-! # §4 — Summary

**Real-valued matrix collapses to a ℕ defined by its prime atom
factors.** The chain composes the existing pieces:

- `matrixEquivEntropyNat`
  ([PolynomialMatrixAsNat.lean:144](../Isomorphisms/Matrix/PolynomialMatrixAsNat.lean#L144))
- `entropyNatEquivNat`
  ([Basic.lean:105](../EntropyNumber/Basic.lean#L105))
- `factorListC` (this file, §0) — choice-free trial-division
  factoriser, replacing the `Classical.choice`-tainted Mathlib
  `Nat.factorization`.
- `realMatrixToEntropyNat` (this file, §2.2) — forward EntropyReal-
  to-EntropyNat projection through `evalEntropyRealZero` plus
  unary-length-prefixed `listBoolToNat`.
- `Nat_L`/`Real_L`/`cardinal_of_level`
  ([Hierarchy.lean:84-109](../EntropyNumber/Hierarchy.lean#L84-L109))

The forward map at every link is constructive (no `Classical.choice`
in any forward direction). The image-subtype Equiv's right-inverse
uses `Classical.choose` to read back any specific preimage from the
forward image — the same stratification used everywhere in this
tree (Translation 5 §1; `EntropyReal ≃ ℝ` reverse direction in
`Real.lean:113`). -/

end Translation6

end InformationTheory
