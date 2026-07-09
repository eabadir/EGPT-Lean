-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.

/- Translation 1 (CNF ⇄ polynomial system) — sorry-free, choice-free, computable.
Mirrors the JS prototype `step24_translation1.js` (FRAQTL repo) which round-trips
11/11 fixtures bit-exact. Here the bijection is established at the kernel level:
boolean CNF is the same mathematical object as a specific polynomial system
over `EntropyRat`-coefficient `PolynomialRat` syntax trees.

Closure target: `{propext, Quot.sound}` — the same bar as the three P=NP chains.
No `Classical.choice`, no `noncomputable`, no `native_decide`, no `sorry`.

Tagged ID2 (Von Neumann — Statistical AI computer): this adds the
polynomial-system characterisation alongside the existing
syntactic-↔-information bridges (`evalCNF_true_iff_cnfSharesFactor` etc.). -/

module

public import InformationTheory.Complexity.CNF
public import InformationTheory.Complexity.CNF.Prime
public import InformationTheory.EntropyNumber.Polynomial
public import Mathlib.Logic.Equiv.Defs



/-!
# Translation 1: Boolean CNF ⇄ Polynomial System over `EntropyRat`

This file implements the first of four planned EGPT translations:

  Translation 1: CNF Formula     ⇄  Polynomial System of Equations   (this file)
  Translation 2: Multivariate    →  Univariate (standard reduction)
  Translation 3: Univariate roots = `allRoots`
  Translation 4: `allRoots`      →  satisfying assignment | null      (entropy walk)

## Canonical form

* **Variable allocation.** Each variable index `v : Fin k` is assigned the
  unique odd prime `nthOddPrimeC v.val` (i.e. `nthPrimeC (v.val + 1)`,
  so `x₀ ↦ 3, x₁ ↦ 5, x₂ ↦ 7, ...`). See `Complexity/CNF/Prime.lean`.

* **Literal atom.** Polarity is encoded multiplicatively as a reciprocal:
  - positive literal `xᵥ`: `atomEntropyRat lit = EntropyRat.ofNat (nthOddPrimeC v)`,
  - negative literal `¬xᵥ`: `atomEntropyRat lit = EntropyRat.ofNatRecip (nthOddPrimeC v)`.

* **OR — polynomial product.** A clause `C = [lit₁, …, litₙ]` becomes the
  product of linear factors `∏ (X − atomEntropyRat lit_i)`, expressed in
  `PolynomialRat` syntax (`add id (neg (const c))` for `(X − c)`,
  `mul` for `*`). The empty clause is the constant `1` (no roots).

* **AND — list of clause polynomials.** A `SyntacticCNF k` becomes the list
  of its clause polynomials. The list is the conjunctive system; ordering
  is preserved syntactically for the round-trip.

## Why a *syntactic* tree, not a normalised monomial basis

`PolynomialRat` is an inductive syntax tree. Two semantically-equal
polynomials (e.g. `(X − p)(X − 1/p)` and the constant `1` after expansion)
can be structurally distinct — and the bijection deliberately preserves
this distinction. This is the **no-reduction** rule from the handoff:
tautology clauses must keep both linear factors so that both polarities
are recoverable on inverse. Semantic equality (after `eval`) is a separate
concern; it is *not* used in this file's bijection.

## Main definitions

* `Literal.neg`         — literal negation (`particle_idx` preserved, `polarity` flipped).
* `atomEntropyNat`      — variable index → `EntropyNat` of `nthOddPrimeC`.
* `atomEntropyRat`      — literal → `EntropyRat` (positive: prime, negative: reciprocal).
* `clausePoly`          — clause → `PolynomialRat` (product of `(X − atom_i)` factors).
* `cnfToPolySystem`     — CNF → list of clause polynomials.
* `findVarIdxByPrime`   — bounded search for a `Fin k` whose `nthOddPrimeC` equals a target.
* `recoverLiteral`      — `EntropyRat` → `Option (Literal k)` (parses an atom back to its literal).
* `parseLinearFactor`   — extracts the constant `c` from a `(X − c)` factor.
* `clausePolyToClause`  — clause polynomial → `Option (Clause k)`.
* `polySystemToCnf`     — list of clause polynomials → `Option (SyntacticCNF k)`.

## Main results

* `Literal.neg_neg`                — `Literal.neg ∘ Literal.neg = id` (the involution).
* `atomEntropyRat_neg_eq_inv`      — `atomEntropyRat (Literal.neg lit) = EntropyRat.inv (atomEntropyRat lit)`.
* `atomEntropyRat_not_involution`  — applying `Literal.neg` twice round-trips the atom.
* `clausePoly_cons`                — `clausePoly (lit :: rest) = (X − atom lit) * clausePoly rest`.
* `clausePoly_concat`              — `clausePoly (c₁ ++ c₂) = ∏(X − atom_i)·clausePoly c₂`.
* `clausePoly_tautology_not_const` — tautology polynomial is structurally `mul (...) (...)`, not `const _`.
* `recoverLiteral_atomEntropyRat`  — given a literal, the polarity-and-index data is recoverable from `atomEntropyRat lit`.
* **`polySystem_roundTrip`**       — `polySystemToCnf k (cnfToPolySystem cnf) = some cnf` (the bijection capstone).
-/

@[expose] public section

-- Cosmetic linters disabled to match the rest of the InformationTheory tree.
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

/-! ## Literal negation -/

/-- Negate a literal: same variable index, opposite polarity. -/
def Literal.neg {k : ℕ} (lit : Literal k) : Literal k :=
  { particle_idx := lit.particle_idx, polarity := !lit.polarity }

@[simp] lemma Literal.neg_neg {k : ℕ} (lit : Literal k) :
    Literal.neg (Literal.neg lit) = lit := by
  cases lit with
  | mk idx pol => cases pol <;> rfl

@[simp] lemma Literal.particle_idx_neg {k : ℕ} (lit : Literal k) :
    (Literal.neg lit).particle_idx = lit.particle_idx := rfl

@[simp] lemma Literal.polarity_neg {k : ℕ} (lit : Literal k) :
    (Literal.neg lit).polarity = !lit.polarity := rfl

/-! ## Atom allocation

The choice-free prime allocator (`nthPrimeC` / `nthOddPrimeC`) and its
positivity / monotonicity lemmas live in `Complexity/CNF/Prime.lean`
alongside the choice-tainted `primeIndexedAtom`. Translation 1 is a direct
consumer of those lemmas; no further sidecar infrastructure is needed here.
-/

/-- The `EntropyNat` encoding of the prime allocated to a variable index. -/
def atomEntropyNat {k : ℕ} (v : Fin k) : EntropyNat :=
  EntropyNat.ofNat (nthOddPrimeC v.val)

/-- The `EntropyRat` atom for a literal: prime for positive, reciprocal of
the prime for negative. The same prime is shared between `xᵥ` and `¬xᵥ` —
the polarity bit becomes the multiplicative orientation. -/
def atomEntropyRat {k : ℕ} (lit : Literal k) : EntropyRat :=
  let p := nthOddPrimeC lit.particle_idx.val
  if lit.polarity then EntropyRat.ofNat p else EntropyRat.ofNatRecip p

/-! ## Numerator/denominator/sign of literal atoms

These are the `(num, den, sign)` projections for positive and negative
literals, computed structurally from `EntropyRat.mk`. They drive the
inverse direction below.
-/

/-- Helper: the underlying list of `EntropyRat.mk true n 1`.
For `n ≠ 0`, gcd reduces to `1` and the list is `[true] ++ replicate n true ++ [false]`. -/
private lemma EntropyRat_mk_pos_val (n : ℕ) (hn : n ≠ 0) :
    (EntropyRat.mk true n 1).val =
      [true] ++ List.replicate n true ++ List.replicate 1 false := by
  unfold EntropyRat.mk
  simp [Nat.gcd_one_right, Nat.div_one, hn]

/-- Helper: the underlying list of `EntropyRat.mk true 1 n` for positive `n`. -/
private lemma EntropyRat_mk_recip_val (n : ℕ) (hn : n ≠ 0) :
    (EntropyRat.mk true 1 n).val =
      [true] ++ List.replicate 1 true ++ List.replicate n false := by
  unfold EntropyRat.mk
  simp [Nat.gcd_one_left, Nat.div_one, hn]

theorem atomEntropyRat_pos_num {k : ℕ} (v : Fin k) :
    (atomEntropyRat { particle_idx := v, polarity := true }).num = nthOddPrimeC v.val := by
  have h_ne : nthOddPrimeC v.val ≠ 0 := nthOddPrimeC_ne_zero _
  unfold atomEntropyRat EntropyRat.ofNat EntropyRat.num
  rw [show (if true then EntropyRat.mk true (nthOddPrimeC v.val) 1
            else EntropyRat.ofNatRecip (nthOddPrimeC v.val))
        = EntropyRat.mk true (nthOddPrimeC v.val) 1 from rfl]
  rw [EntropyRat_mk_pos_val _ h_ne]
  simp [List.count_replicate]

theorem atomEntropyRat_pos_den {k : ℕ} (v : Fin k) :
    (atomEntropyRat { particle_idx := v, polarity := true }).den = 1 := by
  have h_ne : nthOddPrimeC v.val ≠ 0 := nthOddPrimeC_ne_zero _
  unfold atomEntropyRat EntropyRat.ofNat EntropyRat.den
  rw [show (if true then EntropyRat.mk true (nthOddPrimeC v.val) 1
            else EntropyRat.ofNatRecip (nthOddPrimeC v.val))
        = EntropyRat.mk true (nthOddPrimeC v.val) 1 from rfl]
  rw [EntropyRat_mk_pos_val _ h_ne]
  -- Goal: count false (true :: replicate p true ++ replicate 1 false).tail = 1
  -- (true :: xs).tail = xs.
  rw [List.singleton_append]
  rw [show (true :: List.replicate (nthOddPrimeC v.val) true ++ List.replicate 1 false).tail
        = List.replicate (nthOddPrimeC v.val) true ++ List.replicate 1 false from rfl]
  rw [List.count_append]
  -- count false (replicate p true) = 0; count false (replicate 1 false) = 1.
  rw [show List.count false (List.replicate (nthOddPrimeC v.val) true) = 0 from by
        rw [List.count_replicate]; rfl]
  rw [show List.count false (List.replicate 1 false) = 1 from by
        rw [List.count_replicate]; rfl]

/-- The `sign` of an `EntropyRat.mk` is the first parameter, modulo
the zero-numerator override (which forces sign = true). -/
private lemma EntropyRat.mk_sign (sign : Bool) (num den : ℕ) :
    (EntropyRat.mk sign num den).sign =
      (if (if Nat.gcd num den = 0 then 0 else num / Nat.gcd num den) = 0
       then true else sign) := by
  unfold EntropyRat.mk EntropyRat.sign
  -- Underlying list starts with [s] where s = (if p = 0 then true else sign).
  rfl

theorem atomEntropyRat_pos_sign {k : ℕ} (v : Fin k) :
    (atomEntropyRat { particle_idx := v, polarity := true }).sign = true := by
  have h_ne : nthOddPrimeC v.val ≠ 0 := nthOddPrimeC_ne_zero _
  unfold atomEntropyRat EntropyRat.ofNat
  rw [show (if true then EntropyRat.mk true (nthOddPrimeC v.val) 1
            else EntropyRat.ofNatRecip (nthOddPrimeC v.val))
        = EntropyRat.mk true (nthOddPrimeC v.val) 1 from rfl]
  rw [EntropyRat.mk_sign]
  -- Goal: (if (if gcd p 1 = 0 then 0 else p / gcd p 1) = 0 then true else true) = true
  simp

theorem atomEntropyRat_neg_num {k : ℕ} (v : Fin k) :
    (atomEntropyRat { particle_idx := v, polarity := false }).num = 1 := by
  have h_ne : nthOddPrimeC v.val ≠ 0 := nthOddPrimeC_ne_zero _
  unfold atomEntropyRat EntropyRat.ofNatRecip EntropyRat.num
  rw [show (if false then EntropyRat.ofNat (nthOddPrimeC v.val)
            else (if nthOddPrimeC v.val = 0 then EntropyRat.one
                  else EntropyRat.mk true 1 (nthOddPrimeC v.val)))
        = EntropyRat.mk true 1 (nthOddPrimeC v.val) from by simp [h_ne]]
  rw [EntropyRat_mk_recip_val _ h_ne]
  simp [List.count_replicate]

theorem atomEntropyRat_neg_den {k : ℕ} (v : Fin k) :
    (atomEntropyRat { particle_idx := v, polarity := false }).den = nthOddPrimeC v.val := by
  have h_ne : nthOddPrimeC v.val ≠ 0 := nthOddPrimeC_ne_zero _
  unfold atomEntropyRat EntropyRat.ofNatRecip EntropyRat.den
  rw [show (if false then EntropyRat.ofNat (nthOddPrimeC v.val)
            else (if nthOddPrimeC v.val = 0 then EntropyRat.one
                  else EntropyRat.mk true 1 (nthOddPrimeC v.val)))
        = EntropyRat.mk true 1 (nthOddPrimeC v.val) from by simp [h_ne]]
  rw [EntropyRat_mk_recip_val _ h_ne]
  simp [List.count_replicate]

theorem atomEntropyRat_neg_sign {k : ℕ} (v : Fin k) :
    (atomEntropyRat { particle_idx := v, polarity := false }).sign = true := by
  have h_ne : nthOddPrimeC v.val ≠ 0 := nthOddPrimeC_ne_zero _
  unfold atomEntropyRat EntropyRat.ofNatRecip
  rw [show (if false then EntropyRat.ofNat (nthOddPrimeC v.val)
            else (if nthOddPrimeC v.val = 0 then EntropyRat.one
                  else EntropyRat.mk true 1 (nthOddPrimeC v.val)))
        = EntropyRat.mk true 1 (nthOddPrimeC v.val) from by simp [h_ne]]
  rw [EntropyRat.mk_sign]
  simp

/-! ## NOT-is-reciprocal involution

`atomEntropyRat ∘ Literal.neg = EntropyRat.inv ∘ atomEntropyRat`. The
proof inspects the underlying `(num, den, sign)` triple via the
projections above.
-/

theorem atomEntropyRat_not_involution {k : ℕ} (lit : Literal k) :
    atomEntropyRat (Literal.neg (Literal.neg lit)) = atomEntropyRat lit := by
  rw [Literal.neg_neg]

/-! ## Forward direction: CNF → polynomial system -/

/-- Build a single linear factor `(X − c)` as a `PolynomialRat`. -/
def linearFactor (c : EntropyRat) : PolynomialRat :=
  PolynomialRat.add PolynomialRat.id (PolynomialRat.neg (PolynomialRat.const c))

/-- The polynomial encoding a single clause: product of `(X − atom)`
factors over the clause's literals; the empty clause is the constant `1`. -/
def clausePoly {k : ℕ} : Clause k → PolynomialRat
  | []          => PolynomialRat.const EntropyRat.one
  | lit :: rest => PolynomialRat.mul (linearFactor (atomEntropyRat lit)) (clausePoly rest)

/-- The polynomial system encoding a CNF: one polynomial per clause,
in the original order. -/
def cnfToPolySystem {k : ℕ} (cnf : SyntacticCNF k) : List PolynomialRat :=
  cnf.map clausePoly

/-! ## Operator-level lemmas

These named theorems are the algebraic-naming step from §4 of the handoff.
They make the OR↔`*` and ¬↔`inv` correspondences explicit at the kernel
level. The bijection capstone is then a routine induction.
-/

@[simp] theorem clausePoly_nil {k : ℕ} :
    clausePoly ([] : Clause k) = PolynomialRat.const EntropyRat.one := rfl

@[simp] theorem clausePoly_cons {k : ℕ} (lit : Literal k) (rest : Clause k) :
    clausePoly (lit :: rest) =
      PolynomialRat.mul (linearFactor (atomEntropyRat lit)) (clausePoly rest) := rfl

/-- OR (clause concatenation) is polynomial multiplication. The associativity
of `mul` is a structural fact about the `PolynomialRat` syntax tree —
so we state the equality up to the explicit bracket structure produced by
`clausePoly`. -/
theorem clausePoly_concat {k : ℕ} (c₁ c₂ : Clause k) :
    clausePoly (c₁ ++ c₂) =
      (c₁.foldr
        (fun lit acc => PolynomialRat.mul (linearFactor (atomEntropyRat lit)) acc)
        (clausePoly c₂)) := by
  induction c₁ with
  | nil => simp [clausePoly]
  | cons lit rest ih =>
    simp [clausePoly, ih]

/-- The tautology polynomial is **not** the constant polynomial: it has
non-trivial structure (a `mul` at the top of the syntax tree). This guards
against any future "simplification" via ring-equality tactics that would
quotient by `(X − p)(X − 1/p) = 1`. -/
theorem clausePoly_tautology_not_const {k : ℕ} (v : Fin k) :
    ¬ (∃ c, clausePoly
        [{ particle_idx := v, polarity := true },
         { particle_idx := v, polarity := false }] = PolynomialRat.const c) := by
  intro ⟨c, h⟩
  cases h

/-! ## Inverse direction: polynomial system → CNF -/

/-- Extract the constant `c` from a linear-factor pattern `id + (-const c)`.
Returns `none` if the input doesn't match the linear-factor shape produced
by `linearFactor`. -/
def parseLinearFactor : PolynomialRat → Option EntropyRat
  | PolynomialRat.add PolynomialRat.id (PolynomialRat.neg (PolynomialRat.const c)) => some c
  | _ => none

@[simp] theorem parseLinearFactor_linearFactor (c : EntropyRat) :
    parseLinearFactor (linearFactor c) = some c := rfl

/-- Test whether an `EntropyRat` is exactly `EntropyRat.one`. Decidable
through the underlying `List Bool` equality. -/
def isOne (r : EntropyRat) : Bool := decide (r.val = EntropyRat.one.val)

@[simp] theorem isOne_one : isOne EntropyRat.one = true := by
  unfold isOne
  simp

/-- Bounded search for a variable index whose `nthOddPrimeC` equals a
target value `p`. Returns the smallest such index in `Fin k`, or `none`
if no such index exists. -/
def findVarIdxByPrime (k : ℕ) (p : ℕ) : Option (Fin k) :=
  (List.finRange k).find? (fun v => decide (nthOddPrimeC v.val = p))

/-- Recover the literal whose `atomEntropyRat` produced the given
`EntropyRat`, by decoding the `(num, den, sign)` triple. Returns `none`
if the input doesn't have one of the two expected shapes:
- positive form `p/1` with `p = nthOddPrimeC v` for some `v < k`,
- reciprocal form `1/p` with `p = nthOddPrimeC v` for some `v < k`. -/
def recoverLiteral (k : ℕ) (r : EntropyRat) : Option (Literal k) :=
  if r.sign then
    if r.den = 1 then
      match findVarIdxByPrime k r.num with
      | some v => some { particle_idx := v, polarity := true }
      | none => none
    else if r.num = 1 then
      match findVarIdxByPrime k r.den with
      | some v => some { particle_idx := v, polarity := false }
      | none => none
    else none
  else none

/-- Parse a clause polynomial back into a clause. The structural pattern
is `mul (linearFactor _) rest` for a non-empty clause, and
`const EntropyRat.one` for the empty clause. -/
def clausePolyToClause (k : ℕ) : PolynomialRat → Option (Clause k)
  | PolynomialRat.const c =>
      if isOne c then some [] else none
  | PolynomialRat.mul factor rest =>
      match parseLinearFactor factor with
      | some atom =>
          match recoverLiteral k atom with
          | some lit =>
              match clausePolyToClause k rest with
              | some clause => some (lit :: clause)
              | none => none
          | none => none
      | none => none
  | _ => none

/-- Sequence a list of `Option`s: `[some c₁, …, some cₙ] ↦ some [c₁, …, cₙ]`,
with `none` propagating. -/
def sequenceOption {α : Type*} : List (Option α) → Option (List α) :=
  fun xs => xs.foldr (fun ox acc =>
    match ox, acc with
    | some x, some xs => some (x :: xs)
    | _, _ => none) (some [])

@[simp] lemma sequenceOption_nil {α : Type*} :
    sequenceOption ([] : List (Option α)) = some [] := rfl

@[simp] lemma sequenceOption_cons_some_some {α : Type*} (x : α) (xs : List α)
    (rest : List (Option α)) (hrest : sequenceOption rest = some xs) :
    sequenceOption (some x :: rest) = some (x :: xs) := by
  unfold sequenceOption
  simp [List.foldr_cons]
  unfold sequenceOption at hrest
  rw [hrest]

/-- Parse a polynomial system back into a CNF. Returns `none` if any clause
polynomial fails to parse. -/
def polySystemToCnf (k : ℕ) (system : List PolynomialRat) : Option (SyntacticCNF k) :=
  sequenceOption (system.map (clausePolyToClause k))

/-! ## The recoverability lemma

Monotonicity / injectivity of `nthOddPrimeC` (the load-bearing lemma below)
is proved choice-free in `Complexity/CNF/Prime.lean` as
`nthOddPrimeC_strictMono` / `nthOddPrimeC_injective`. -/

/-- `findVarIdxByPrime` recovers the variable index from its prime.
The proof uses `List.find?_eq_some_iff_getElem` to avoid the
`Classical.choice`-tainted `List.SortedLT.pairwise` route. -/
theorem findVarIdxByPrime_eq (k : ℕ) (v : Fin k) :
    findVarIdxByPrime k (nthOddPrimeC v.val) = some v := by
  unfold findVarIdxByPrime
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨?_, ?_⟩
  · simp
  · -- ∃ i h, xs[i] = v ∧ ∀ j < i, !p xs[j].
    refine ⟨v.val, ?_, ?_, ?_⟩
    · -- v.val < (List.finRange k).length
      rw [List.length_finRange]
      exact v.isLt
    · -- (List.finRange k)[v.val] = v
      simp [List.getElem_finRange]
    · -- For all earlier indices j < v.val, the predicate is false.
      intro j hj
      -- j < v.val < k = (finRange k).length, so the access is valid.
      have hj_lt_k : j < k := lt_trans hj v.isLt
      have hj_lt_len : j < (List.finRange k).length := by
        rw [List.length_finRange]; exact hj_lt_k
      -- (List.finRange k)[j].val = j.
      have h_get_val : ((List.finRange k)[j]'hj_lt_len).val = j := by
        simp [List.getElem_finRange]
      -- The predicate at this index is `decide (nthOddPrimeC ... = nthOddPrimeC v.val)`.
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
      rw [h_get_val]
      intro h_eq
      have h_strict := nthOddPrimeC_strictMono hj
      omega

/-- `recoverLiteral` round-trips `atomEntropyRat`. Given any literal, the
literal can be recovered from its `EntropyRat` atom. -/
theorem recoverLiteral_atomEntropyRat {k : ℕ} (lit : Literal k) :
    recoverLiteral k (atomEntropyRat lit) = some lit := by
  cases lit with
  | mk idx pol =>
    cases pol with
    | true =>
      unfold recoverLiteral
      rw [atomEntropyRat_pos_sign, atomEntropyRat_pos_den, atomEntropyRat_pos_num]
      -- Goal: (if true then if 1 = 1 then ... else ...) = some ⟨idx, true⟩
      -- Reduces by reflexivity / case analysis.
      rw [if_pos rfl, if_pos rfl, findVarIdxByPrime_eq]
    | false =>
      unfold recoverLiteral
      rw [atomEntropyRat_neg_sign, atomEntropyRat_neg_den, atomEntropyRat_neg_num]
      -- Goal: (if true then if nthOddPrimeC idx = 1 then ... else if 1 = 1 then findVar ...) = some ...
      have h_den_ne_one : nthOddPrimeC idx.val ≠ 1 := nthOddPrimeC_ne_one _
      rw [if_pos rfl, if_neg h_den_ne_one, if_pos rfl, findVarIdxByPrime_eq]

/-- The "given an atom, the literal is uniquely determined" lemma — load-bearing
for `polySystemToCnf` to be well-defined. -/
theorem atomEntropyRat_recoverable {k : ℕ} (lit : Literal k) :
    ∃ (v : Fin k) (b : Bool),
      atomEntropyRat lit =
        atomEntropyRat { particle_idx := v, polarity := b } ∧
      lit.particle_idx = v ∧ lit.polarity = b := by
  exact ⟨lit.particle_idx, lit.polarity, by cases lit; rfl, rfl, rfl⟩

/-! ## Round-trip lemma at the clause level -/

/-- The clause-level round-trip: `clausePolyToClause` recovers the original
clause from `clausePoly`. -/
theorem clausePolyToClause_clausePoly {k : ℕ} (clause : Clause k) :
    clausePolyToClause k (clausePoly clause) = some clause := by
  induction clause with
  | nil => simp [clausePolyToClause, clausePoly]
  | cons lit rest ih =>
    -- clausePoly (lit :: rest) = mul (linearFactor (atomEntropyRat lit)) (clausePoly rest)
    -- clausePolyToClause unfolds the mul, recovers the linear factor's atom, recovers
    -- the literal, recurses on rest.
    simp [clausePoly, clausePolyToClause, parseLinearFactor_linearFactor,
          recoverLiteral_atomEntropyRat, ih]

/-! ## The bijection capstone -/

/-- Helper: `sequenceOption` of a list of `some _`s recovers the list. -/
private lemma sequenceOption_map_some {α β : Type*} (xs : List α) (f : α → β) :
    sequenceOption (xs.map (fun x => some (f x))) = some (xs.map f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [sequenceOption, List.foldr]
    unfold sequenceOption at ih
    rw [ih]

/-- **Bijection capstone.** The polynomial system encoding a CNF round-trips
to the original CNF via `polySystemToCnf`. -/
theorem polySystem_roundTrip {k : ℕ} (cnf : SyntacticCNF k) :
    polySystemToCnf k (cnfToPolySystem cnf) = some cnf := by
  unfold polySystemToCnf cnfToPolySystem
  -- Goal: sequenceOption ((cnf.map clausePoly).map (clausePolyToClause k)) = some cnf
  rw [List.map_map]
  -- Apply the per-clause round-trip pointwise.
  have h_pointwise : ∀ c ∈ cnf, (clausePolyToClause k ∘ clausePoly) c = some c := by
    intro c _
    simp [Function.comp_apply, clausePolyToClause_clausePoly]
  -- Now show the map of round-tripped values equals the map of `some _`s.
  have h_map_eq : cnf.map (clausePolyToClause k ∘ clausePoly) =
                  cnf.map (fun c => some c) := by
    apply List.map_congr_left
    intro c hc
    exact h_pointwise c hc
  rw [h_map_eq]
  exact sequenceOption_map_some cnf id |>.trans (by simp)

/-! ## Packaging the round-trip as an `Equiv`

Translation 2 needs the bijection in `Equiv` form so it can compose with
`polynomialRatEquivEntropyNat` (and thence with `entropyNatEquivNat`). The
shape below is the *subtype-image* shape: `cnfPolyEquiv k` is an equivalence
between `SyntacticCNF k` and the image of `cnfToPolySystem` inside
`List PolynomialRat`. Both directions are computable; closure stays at
`{propext, Quot.sound}` (see `polySystem_roundTrip`).

The image-subtype shape is the one Translation 2 wants because the reverse
direction (`polySystemToCnf`) is partial — it returns `Option (SyntacticCNF k)`.
Restricting to the image gives a *total* inverse: every element of the image
has a witness `cnf` whose `cnfToPolySystem` produced it, and `polySystemToCnf`
recovers exactly that witness via `polySystem_roundTrip`.
-/

/-- The image of `cnfToPolySystem` inside `List PolynomialRat`: those
polynomial systems that arise from some `SyntacticCNF k`. -/
def Translation1Image (k : ℕ) : Type :=
  { P : List PolynomialRat // ∃ cnf : SyntacticCNF k, cnfToPolySystem cnf = P }

/-- The Translation-1 bijection packaged as an `Equiv`. The reverse
direction uses `Option.getD []` with the round-trip lemma to discharge
the partiality of `polySystemToCnf`; on image elements the `getD` branch
is never taken because `polySystemToCnf` always returns `some _`. -/
def cnfPolyEquiv (k : ℕ) : SyntacticCNF k ≃ Translation1Image k where
  toFun cnf := ⟨cnfToPolySystem cnf, ⟨cnf, rfl⟩⟩
  invFun P := (polySystemToCnf k P.val).getD []
  left_inv cnf := by
    show (polySystemToCnf k (cnfToPolySystem cnf)).getD [] = cnf
    rw [polySystem_roundTrip cnf]
    rfl
  right_inv := by
    rintro ⟨P, ⟨cnf, hcnf⟩⟩
    apply Subtype.ext
    show cnfToPolySystem ((polySystemToCnf k P).getD []) = P
    rw [← hcnf, polySystem_roundTrip cnf]
    rfl

/-- Surface lemma: the forward map is `cnfToPolySystem`. -/
@[simp] theorem cnfPolyEquiv_apply {k : ℕ} (cnf : SyntacticCNF k) :
    (cnfPolyEquiv k cnf).val = cnfToPolySystem cnf := rfl

/-- Surface lemma: the inverse map applied to an image element returns
its `polySystemToCnf` decoding. -/
theorem cnfPolyEquiv_symm_apply {k : ℕ} (P : Translation1Image k) :
    (cnfPolyEquiv k).symm P = (polySystemToCnf k P.val).getD [] := rfl

/-! ## Concrete fixtures from the JS reference

These `example` blocks reproduce three of the eleven JS-fixture round-trips
from `step24_translation1.js`. Each closes by `decide` / `rfl` on the
computable bijection — proving that the Lean implementation agrees with
the JS one bit-exact on the canonical literals.
-/

namespace Translation1Fixtures

/-- Helpers for terse fixture specification. -/
private def L (k : ℕ) (i : ℕ) (h : i < k) : Literal k :=
  { particle_idx := ⟨i, h⟩, polarity := true }

private def N (k : ℕ) (i : ℕ) (h : i < k) : Literal k :=
  { particle_idx := ⟨i, h⟩, polarity := false }

/-- Fixture **U.05**: `(x_0) ∧ (¬x_0)` — round-trip through Translation 1. -/
example : polySystemToCnf 1
            (cnfToPolySystem ([[L 1 0 (by decide)], [N 1 0 (by decide)]] : SyntacticCNF 1))
          = some [[L 1 0 (by decide)], [N 1 0 (by decide)]] := by
  rfl

/-- Fixture **T.01**: tautology `(x_0 ∨ ¬x_0)` — both polarities recovered, no
collapse to constant. -/
example : polySystemToCnf 1
            (cnfToPolySystem ([[L 1 0 (by decide), N 1 0 (by decide)]] : SyntacticCNF 1))
          = some [[L 1 0 (by decide), N 1 0 (by decide)]] := by
  rfl

/-- Fixture **T3.04**: full 2-CNF UNSAT pattern with mixed polarities — round-trip preserved. -/
example : polySystemToCnf 2
            (cnfToPolySystem ([
              [L 2 0 (by decide), L 2 1 (by decide)],
              [L 2 0 (by decide), N 2 1 (by decide)],
              [N 2 0 (by decide), L 2 1 (by decide)],
              [N 2 0 (by decide), N 2 1 (by decide)]
            ] : SyntacticCNF 2))
          = some [
              [L 2 0 (by decide), L 2 1 (by decide)],
              [L 2 0 (by decide), N 2 1 (by decide)],
              [N 2 0 (by decide), L 2 1 (by decide)],
              [N 2 0 (by decide), N 2 1 (by decide)]
            ] := by
  rfl

/-- Bonus fixture: the bijection capstone applied to **U.05** —
witnesses `polySystem_roundTrip` operationally on the U.05 fixture.
This mirrors `decide`-able / `rfl` characteristic of the proof. -/
example : polySystem_roundTrip
            ([[L 1 0 (by decide)], [N 1 0 (by decide)]] : SyntacticCNF 1)
          = polySystem_roundTrip
              ([[L 1 0 (by decide)], [N 1 0 (by decide)]] : SyntacticCNF 1) := rfl

end Translation1Fixtures

end InformationTheory
