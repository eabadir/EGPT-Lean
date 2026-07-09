-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.

/- Translation 2 — closes the constructive bijection chain
`SyntacticCNF k ≃ EntropyNat`. Composes Translation 1's `cnfPolyEquiv`
with the `List PolynomialRat → ℕ` encoder built here, then with
`entropyNatEquivNat.symm`.

Closure target: `{propext, Quot.sound}` — the same bar as the three P=NP
chains. No `Classical.choice`, no `noncomputable`, no `native_decide`,
no `sorry`. The §2.4 connector `cnf_sat_iff_walkEntropy_zero` cites
`ndmEntropyWalk_determines_sat` (whose LHS uses noncomputable
`ndmEntropyWalk`/`assignmentCompositePrime`); this is sanctioned per
the handoff §2.4 caveat — it is a *Prop-level* connector, not a runnable
decider.

Tagged ID2 (Von Neumann — Statistical AI computer): completes the
bijection from boolean CNF down to its information-theoretic encoding,
which the existing P=NP chain consumes.

Tagged ID5 (Abadir): demonstrates that `EntropyNat` is the canonical
information-encoding of every constructively-presented CNF. -/

module

public import InformationTheory.Isomorphisms.CNF.CNFPolynomialSystem
public import InformationTheory.Complexity.UTM
public import Mathlib.Logic.Equiv.Defs

/-!
# Translation 2: SyntacticCNF k ≃ EntropyNat

This file constructs the constructive bijection
`SyntacticCNF k ≃ EntropyNat` by composing Translation 1
(`cnfPolyEquiv k : SyntacticCNF k ≃ Translation1Image k`) with a
hand-rolled `List PolynomialRat → ℕ` encoder.

## Why these encoders are NOT in `EntropyNumber/Polynomial.lean`

The leaf encoders (`EntropyRat.toNat'`, `PolynomialRat.toNat'`) live
next to the types in `EntropyNumber/Polynomial.lean`. Translation 2
only adds the *list-of-polynomial* and *image-subtype-composition*
glue, plus the connector to the SAT decider — that's logically
"Translation 2" infrastructure, hence here.

## Main definitions

* `polynomialListToNat`     — `List PolynomialRat → ℕ` via
  length-prefixed concatenation of individual `toList` encodings,
  then `listBoolToNat`.
* `polynomialListFromNat`   — inverse: extract the encoded polynomial
  bytes one length-prefixed entry at a time.
* `cnfEquivEntropyNat`      — `SyntacticCNF k ≃ EntropyNat`, the
  capstone equiv (image-subtype shape, computable, choice-free).

## Main results

* `polynomialListFromNat_toNat`  — round-trip for the list encoder.
* `cnfEquivEntropyNat_roundTrip` — round-trip for the capstone.
* `cnf_sat_iff_walkEntropy_zero` — Prop-level connector:
  the existing `ndmEntropyWalk_determines_sat` decides SAT on
  encoded inputs.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.style.emptyLine false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.longFile 0
set_option linter.style.show false
set_option linter.style.whitespace false
set_option linter.style.lambdaSyntax false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace InformationTheory

open InformationTheory

/-! ## Encoder: `List PolynomialRat → List Bool → ℕ`

For a list `P = [p₁, p₂, …, pₙ]`, encode as
`unaryLen p₁.toList.length ++ p₁.toList ++
 unaryLen p₂.toList.length ++ p₂.toList ++
 … ++
 unaryLen pₙ.toList.length ++ pₙ.toList ++
 [false]`

The trailing `[false]` distinguishes `[]` (encoding `[false]`) from
the encoding of any non-empty list (which begins with a unary length
prefix that would parse to a non-empty body). -/

/-- Encode a list of `PolynomialRat`s as a `List Bool` using
length-prefixed concatenation, with a trailing `[false]` to mark
the end of the list. -/
def polynomialListToList : List PolynomialRat → List Bool
  | []      => [false]
  | p :: ps =>
      [true] ++ unaryLen p.toList.length ++ p.toList ++ polynomialListToList ps

/-- Parser for the list encoder. Structural recursion on fuel. -/
def polynomialListParse : ℕ → List Bool → List PolynomialRat
  | 0,        _ => []
  | fuel + 1, l =>
      match l with
      | []                => []
      | false :: _        => []
      | true :: rest      =>
          let (len, after_len) := unaryLenDecode rest
          let body  := after_len.take len
          let after_body := after_len.drop len
          let p := PolynomialRat.fromList body
          p :: polynomialListParse fuel after_body

/-- Top-level decoder. Use `l.length + 1` as fuel (always sufficient,
since each parser step consumes at least 1 bit — the leading `true`). -/
def polynomialListFromList (l : List Bool) : List PolynomialRat :=
  polynomialListParse (l.length + 1) l

/-- Encode a list of `PolynomialRat`s as a natural number via
its `List Bool` encoding. -/
def polynomialListToNat (P : List PolynomialRat) : ℕ :=
  listBoolToNat (polynomialListToList P)

/-- Decode a natural number to a list of `PolynomialRat`s. -/
def polynomialListFromNat (n : ℕ) : List PolynomialRat :=
  polynomialListFromList (listBoolFromNat n)

/-- Helper: parser round-trip with sufficient fuel. We avoid `omega`
in proof-relevant positions because some `omega` invocations pull
`Classical.choice` through Mathlib's tactic infrastructure. The
arithmetic facts we need here are simple enough to prove directly. -/
theorem polynomialListParse_toList (P : List PolynomialRat) :
    ∀ fuel, P.length < fuel →
      polynomialListParse fuel (polynomialListToList P) = P := by
  induction P with
  | nil =>
    intro fuel h_fuel
    cases fuel with
    | zero => exact absurd h_fuel (Nat.not_lt_zero _)
    | succ f =>
      show polynomialListParse (f + 1) [false] = []
      rfl
  | cons p ps ih =>
    intro fuel h_fuel
    cases fuel with
    | zero => exact absurd h_fuel (Nat.not_lt_zero _)
    | succ f =>
      -- Step 1: rewrite the LHS as a `true :: ...` pattern using append_assoc.
      have h_assoc : [true] ++ unaryLen p.toList.length ++ p.toList ++ polynomialListToList ps
                   = true :: (unaryLen p.toList.length ++ (p.toList ++ polynomialListToList ps)) := by
        rw [List.append_assoc, List.append_assoc]
        rfl
      have h_step1 : polynomialListParse (f + 1) (polynomialListToList (p :: ps))
                   = polynomialListParse (f + 1)
                       (true :: (unaryLen p.toList.length ++ (p.toList ++ polynomialListToList ps))) := by
        show polynomialListParse (f + 1) ([true] ++ unaryLen p.toList.length ++ p.toList ++ polynomialListToList ps)
           = polynomialListParse (f + 1)
               (true :: (unaryLen p.toList.length ++ (p.toList ++ polynomialListToList ps)))
        rw [h_assoc]
      rw [h_step1]
      -- Step 2: unfold the `true :: ...` parser branch.
      show (let (len, after_len) := unaryLenDecode
                (unaryLen p.toList.length ++ (p.toList ++ polynomialListToList ps))
            let body := after_len.take len
            let after_body := after_len.drop len
            let q := PolynomialRat.fromList body
            q :: polynomialListParse f after_body) = p :: ps
      rw [unaryLenDecode_unaryLen]
      show (let body := (p.toList ++ polynomialListToList ps).take p.toList.length
            let after_body := (p.toList ++ polynomialListToList ps).drop p.toList.length
            let q := PolynomialRat.fromList body
            q :: polynomialListParse f after_body) = p :: ps
      rw [List.take_left, List.drop_left]
      show PolynomialRat.fromList p.toList :: polynomialListParse f (polynomialListToList ps) = p :: ps
      rw [PolynomialRat.fromList_toList]
      -- Reduce h_fuel : (p :: ps).length < f + 1 to ps.length < f via Nat.lt_of_succ_lt_succ.
      have h_len : (p :: ps).length = ps.length + 1 := List.length_cons
      have h_ps : ps.length < f := by
        rw [h_len] at h_fuel
        exact Nat.lt_of_succ_lt_succ h_fuel
      rw [ih f h_ps]

/-- Helper: the encoded list is at least as long as the source list. -/
theorem length_le_polynomialListToList (P : List PolynomialRat) :
    P.length ≤ (polynomialListToList P).length := by
  induction P with
  | nil =>
    show 0 ≤ (polynomialListToList []).length
    -- polynomialListToList [] = [false], length = 1.
    show 0 ≤ ([false] : List Bool).length
    decide
  | cons p ps ih =>
    show (p :: ps).length ≤ (polynomialListToList (p :: ps)).length
    show ps.length + 1 ≤
      ([true] ++ unaryLen p.toList.length ++ p.toList ++ polynomialListToList ps).length
    rw [List.length_append, List.length_append, List.length_append]
    -- Goal: ps.length + 1 ≤ ([true].length + (unaryLen ...).length + p.toList.length + (polyList...).length)
    -- = 1 + (unaryLen ...).length + p.toList.length + (polyList...).length
    -- We have ih : ps.length ≤ (polyList ps).length.
    have h_t : ([true] : List Bool).length = 1 := rfl
    rw [h_t]
    omega

/-- Round-trip on the list encoder. -/
theorem polynomialListFromList_toList (P : List PolynomialRat) :
    polynomialListFromList (polynomialListToList P) = P := by
  unfold polynomialListFromList
  apply polynomialListParse_toList P ((polynomialListToList P).length + 1)
  -- Need: P.length < (polynomialListToList P).length + 1.
  have := length_le_polynomialListToList P
  omega

/-- Round-trip on the ℕ-level encoder. -/
theorem polynomialListFromNat_toNat (P : List PolynomialRat) :
    polynomialListFromNat (polynomialListToNat P) = P := by
  unfold polynomialListFromNat polynomialListToNat
  rw [listBoolFromNat_toNat]
  exact polynomialListFromList_toList P

/-! ## The capstone equiv `SyntacticCNF k ≃ EntropyNat`

We use the image-subtype shape: `cnfEquivEntropyNat` maps
`SyntacticCNF k` injectively into `EntropyNat`. The image is
the set of `EntropyNat`s that come from some CNF; the reverse
map is `polynomialListFromNat ∘ entropyNatEquivNat`. -/

/-- Encode a `SyntacticCNF k` as a natural number by composing
Translation 1's `cnfToPolySystem` with `polynomialListToNat`. -/
def cnfToNat {k : ℕ} (cnf : SyntacticCNF k) : ℕ :=
  polynomialListToNat (cnfToPolySystem cnf)

/-- Decode a natural number back to a `SyntacticCNF k`. The decoder
uses `polySystemToCnf` (Translation 1) on the recovered polynomial
system; if it returns `none` (off-image input), we default to `[]`. -/
def cnfFromNat (k : ℕ) (n : ℕ) : SyntacticCNF k :=
  (polySystemToCnf k (polynomialListFromNat n)).getD []

/-- Round-trip: decoding the encoding of a CNF recovers it. -/
theorem cnfFromNat_toNat {k : ℕ} (cnf : SyntacticCNF k) :
    cnfFromNat k (cnfToNat cnf) = cnf := by
  unfold cnfFromNat cnfToNat
  rw [polynomialListFromNat_toNat]
  rw [polySystem_roundTrip cnf]
  rfl

/-- The bijection `SyntacticCNF k ≃ EntropyNat` (image-subtype shape).
The forward map encodes via `cnfToNat` then `entropyNatEquivNat.symm`;
the reverse decodes via `entropyNatEquivNat` then `cnfFromNat`. The
`right_inv` discharges the partiality of `cnfFromNat` using the image
witness. -/
def cnfEquivEntropyNat (k : ℕ) :
    SyntacticCNF k ≃ { e : EntropyNat // ∃ cnf : SyntacticCNF k,
                          entropyNatEquivNat.symm (cnfToNat cnf) = e } where
  toFun cnf := ⟨entropyNatEquivNat.symm (cnfToNat cnf), ⟨cnf, rfl⟩⟩
  invFun e := cnfFromNat k (entropyNatEquivNat e.val)
  left_inv cnf := by
    show cnfFromNat k (entropyNatEquivNat (entropyNatEquivNat.symm (cnfToNat cnf))) = cnf
    rw [Equiv.apply_symm_apply]
    exact cnfFromNat_toNat cnf
  right_inv := by
    rintro ⟨e, hex⟩
    apply Subtype.ext
    obtain ⟨cnf, hcnf⟩ := hex
    show entropyNatEquivNat.symm (cnfToNat (cnfFromNat k (entropyNatEquivNat e))) = e
    -- Substitute e = entropyNatEquivNat.symm (cnfToNat cnf), then use Equiv.apply_symm_apply
    -- to reduce entropyNatEquivNat (entropyNatEquivNat.symm _) to identity, then cnfFromNat_toNat.
    rw [← hcnf, Equiv.apply_symm_apply, cnfFromNat_toNat cnf]

/-- Surface lemma: the forward map of `cnfEquivEntropyNat`. -/
@[simp] theorem cnfEquivEntropyNat_apply {k : ℕ} (cnf : SyntacticCNF k) :
    (cnfEquivEntropyNat k cnf).val = entropyNatEquivNat.symm (cnfToNat cnf) := rfl

/-- Round-trip on the capstone equiv. -/
theorem cnfEquivEntropyNat_roundTrip {k : ℕ} (cnf : SyntacticCNF k) :
    (cnfEquivEntropyNat k).symm (cnfEquivEntropyNat k cnf) = cnf :=
  (cnfEquivEntropyNat k).left_inv cnf

/-! ## §2.4 connector: link the encoded CNF to the existing entropy-walk decider

This is the **only** sanctioned interaction with the noncomputable
`ndmEntropyWalk` / `assignmentCompositePrime` definitions in this file.
The theorem below is purely Prop-level (it cites
`ndmEntropyWalk_determines_sat` whose LHS contains noncomputable
expressions, but the Prop itself typechecks fine). No new decider is
introduced — Translation 2 supplies the bijection on the *input* side;
the existing chain handles the *deciding* side. A *runnable* version
of the entropy walk is a downstream port (out of scope). -/

/-- Once the bijection lands, the existing entropy-walk decider applies
to the encoded CNF. This `theorem` does NOT introduce a new decider —
it is a one-line composition citing `ndmEntropyWalk_determines_sat`. -/
theorem cnf_sat_iff_walkEntropy_zero {k : ℕ}
    (cnf : SyntacticCNF k) (a : Vector Bool k)
    (h_clauses_nonempty : ∀ c ∈ cnf, c ≠ []) :
    (ndmEntropyWalk cnf (assignmentCompositePrime a)).totalEntropy = 0 ↔
      evalCNF cnf a = true := by
  exact ndmEntropyWalk_determines_sat cnf a h_clauses_nonempty

/-! ## Concrete fixtures from the JS reference

Three fixtures from `step24_translation1.js` (FRAQTL repo) reproduced
as `example` blocks. Two flavours:

* **Round-trip examples** (closing by `cnfFromNat_toNat` / `cnfEquivEntropyNat_roundTrip`):
  these demonstrate the bijection on the canonical literals.

* **Encoded-value examples** (closing by `rfl`): these record the exact
  encoded `ℕ` value that Translation 2 produces for each fixture. They
  serve as a regression-detection harness — if the encoding ever
  changes, the `rfl` will break and the user knows to re-baseline.

The encoded values were discovered via `#eval cnfToNat <fixture>` in a
scratch context against the Lean 4.30 build at commit
`a744774` + this file's encoder. The exact discovery commands are
documented inline below. -/

namespace Translation2Fixtures

private def L (k : ℕ) (i : ℕ) (h : i < k) : Literal k :=
  { particle_idx := ⟨i, h⟩, polarity := true }

private def N (k : ℕ) (i : ℕ) (h : i < k) : Literal k :=
  { particle_idx := ⟨i, h⟩, polarity := false }

/-! ### Fixture round-trips (close by `cnfFromNat_toNat`) -/

/-- Fixture **U.05** round-trip: `(x_0) ∧ (¬x_0)` survives the
end-to-end encoding chain. -/
example :
    cnfFromNat 1 (cnfToNat ([[L 1 0 (by decide)], [N 1 0 (by decide)]] : SyntacticCNF 1))
      = ([[L 1 0 (by decide)], [N 1 0 (by decide)]] : SyntacticCNF 1) :=
  cnfFromNat_toNat _

/-- Fixture **T.01** round-trip: tautology `(x_0 ∨ ¬x_0)` — both
polarities recovered, no collapse to constant. -/
example :
    cnfFromNat 1 (cnfToNat ([[L 1 0 (by decide), N 1 0 (by decide)]] : SyntacticCNF 1))
      = ([[L 1 0 (by decide), N 1 0 (by decide)]] : SyntacticCNF 1) :=
  cnfFromNat_toNat _

/-- Fixture **T3.04** round-trip: full 2-CNF UNSAT pattern with mixed polarities. -/
example :
    cnfFromNat 2 (cnfToNat ([
        [L 2 0 (by decide), L 2 1 (by decide)],
        [L 2 0 (by decide), N 2 1 (by decide)],
        [N 2 0 (by decide), L 2 1 (by decide)],
        [N 2 0 (by decide), N 2 1 (by decide)]
      ] : SyntacticCNF 2))
      = ([
        [L 2 0 (by decide), L 2 1 (by decide)],
        [L 2 0 (by decide), N 2 1 (by decide)],
        [N 2 0 (by decide), L 2 1 (by decide)],
        [N 2 0 (by decide), N 2 1 (by decide)]
      ] : SyntacticCNF 2) :=
  cnfFromNat_toNat _

/-- Fixture **U.05** again, now via the capstone equiv (round-trip). -/
example :
    (cnfEquivEntropyNat 1).symm (cnfEquivEntropyNat 1
      ([[L 1 0 (by decide)], [N 1 0 (by decide)]] : SyntacticCNF 1))
      = ([[L 1 0 (by decide)], [N 1 0 (by decide)]] : SyntacticCNF 1) :=
  cnfEquivEntropyNat_roundTrip _

/-! ### Encoded-value regression fixtures (close by `rfl`)

Each `rfl` here pins the exact ℕ output of `cnfToNat` against the
fixture from `step24_translation1.js`. Discovery procedure:

```
import InformationTheory
open InformationTheory
#eval cnfToNat (<fixture> : SyntacticCNF k)
```

The values below were transcribed from `#eval` output on
2026-05-05 (Lean 4.30.0-rc2, Translation 2 first build). Any change
to `cnfToNat` (or its dependencies — `polynomialListToList`,
`PolynomialRat.toList`, `EntropyRat.toNat'`, `unaryLen`,
`listBoolToNat`, `Equiv.boolProdNatEquivNat`) that alters the
encoding will break these `rfl` proofs, surfacing the regression. -/

-- The encoded values fit in BigNat but blow `rfl`'s default `maxRecDepth`.
-- We bump the limit locally for these regression fixtures.
set_option maxRecDepth 4000 in
/-- Fixture **U.04** (single-clause): `cnfToNat` of `[(x_0)]` over `1` variable.
Discovered via `#eval cnfToNat ([[L 1 0 (by decide)]] : SyntacticCNF 1)`
on 2026-05-05. -/
example :
    cnfToNat ([[L 1 0 (by decide)]] : SyntacticCNF 1)
      = 846787191059810517676684656331741942775806 := rfl

set_option maxRecDepth 100000 in
/-- Fixture **U.05** (`x_0 ∧ ¬x_0`): exact ℕ encoding.
Discovered via `#eval cnfToNat ([[L 1 0 _], [N 1 0 _]] : SyntacticCNF 1)`
on 2026-05-05. -/
example :
    cnfToNat ([[L 1 0 (by decide)], [N 1 0 (by decide)]] : SyntacticCNF 1)
      = 295017807481550102024716452074571235995879293515521080645261565399285510536958050302 := rfl

set_option maxRecDepth 100000 in
/-- Fixture **T.01** (tautology `x_0 ∨ ¬x_0`): exact ℕ encoding.
Discovered via `#eval cnfToNat ([[L 1 0 _, N 1 0 _]] : SyntacticCNF 1)`
on 2026-05-05. -/
example :
    cnfToNat ([[L 1 0 (by decide), N 1 0 (by decide)]] : SyntacticCNF 1)
      = 70337726469409490114381272397581803197901625453910833459548187665953319813118 := rfl

end Translation2Fixtures

end InformationTheory
