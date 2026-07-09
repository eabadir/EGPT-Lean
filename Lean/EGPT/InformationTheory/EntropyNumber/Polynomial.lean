-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.


module

public import InformationTheory.EntropyNumber.Basic
public import InformationTheory.EntropyNumber.Rat
public import Mathlib.Data.Nat.Bits
public import Mathlib.Logic.Equiv.Nat
public import Mathlib.Logic.Equiv.Defs



/-!
# EntropyNat Polynomials

This file defines constructive polynomials over `EntropyNat` — functions built from
constants, the identity, addition, and multiplication — together with predicates
for polynomial-time functions and polynomial bounds.

## Main definitions

* `EntropyNumber.Polynomial` — inductive type of constructive polynomials over `EntropyNat`.
* `EntropyNumber.Polynomial.eval` — evaluate a polynomial at an `EntropyNat` input.
* `EntropyNat.IsPolynomial` — a function `EntropyNat → EntropyNat` is polynomial when it
  equals `P.eval` for some `EntropyNumber.Polynomial P`.
* `EntropyNat.IsBoundedByPolynomial` — a function `ℕ → ℕ` is bounded by a
  polynomial when there exists a `P` with `f n ≤ toNat (P.eval (ofNat n))` for
  all `n`.
* `EntropyNat.IsPolynomial.id` — the identity function is polynomial.

## Main results

(No standalone theorems beyond the `IsPolynomial.id` instance; this file
provides foundational definitions consumed by downstream complexity files.)
-/

@[expose] public section

-- Cosmetic linters disabled for this initial drop of the InformationTheory
-- subtree. These do not affect correctness; reviewers may request a per-call
-- cleanup as a follow-up PR.
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


open List

namespace InformationTheory

namespace EntropyNat

/--
**A constructive polynomial over `EntropyNat`.**

An `EntropyNumber.Polynomial` is any function on `EntropyNat`s that can be built from a
finite number of additions, multiplications, constants, and the identity
function.
-/
inductive Polynomial : Type
  | const (c : EntropyNat) : Polynomial
  | id : Polynomial
  | add (p₁ p₂ : Polynomial) : Polynomial
  | mul (p₁ p₂ : Polynomial) : Polynomial

/--
**Evaluate an `EntropyNumber.Polynomial`.**

Takes a polynomial `p` and an input `n`, and computes the result by recursively
applying the native `EntropyNat` arithmetic operations.
-/
@[simp]
def Polynomial.eval (p : Polynomial) (n : EntropyNat) : EntropyNat :=
  match p with
  | const c => c
  | id => n
  | add p₁ p₂ => EntropyNat.add (p₁.eval n) (p₂.eval n)
  | mul p₁ p₂ => EntropyNat.mul (p₁.eval n) (p₂.eval n)

/--
A predicate asserting that a function `f` from one `EntropyNat` to another is
computable by a native `EntropyNat` polynomial. The witness for this property is
the `EntropyNumber.Polynomial` structure itself.
-/
def IsPolynomial (f : EntropyNat → EntropyNat) : Prop :=
  ∃ (P : Polynomial), f = P.eval

/-- The identity function on `EntropyNat` is polynomial. -/
theorem IsPolynomial.id : IsPolynomial _root_.id := by
  use Polynomial.id
  ext n
  simp [Polynomial.eval]

/--
A predicate asserting that a function `p : ℕ → ℕ` is bounded by a native
`EntropyNat` polynomial. This is the canonical definition of a polynomial bound.
-/
def IsBoundedByPolynomial (p : ℕ → ℕ) : Prop :=
  ∃ (P : Polynomial), ∀ n, p n ≤ toNat (P.eval (ofNat n))

end EntropyNat

/-! ## Constructive Rational Arithmetic on `EntropyRat`

A *minimal*, *computable* arithmetic surface on `EntropyRat`, used by
`PolynomialRat.eval` below. Each operation works structurally on the
`(sign, num, den)` triple and produces a freshly normalised canonical form
via `mkEntropyRat`. **No `Classical.choice`, no `noncomputable`.**

The Mathlib-side rational `EntropyRat.toRat` / `EntropyRat.ofRat` are
`noncomputable` because they bundle the equivalence with `ℚ`; here we
deliberately bypass that bundle and operate directly on the underlying
`List Bool` form. This keeps Translation 1's axiom closure at
`{propext, Quot.sound}`.
-/

/-- Normalise a `(sign, num, den)` triple into a canonical `EntropyRat`.
The result represents the rational `(if sign then num else -num) / max 1 den`,
reduced to lowest terms. The `0` case is forced to non-negative sign
(per `EntropyRat.IsCanonical`'s `p = 0 → s = true` clause). -/
def EntropyRat.mk (sign : Bool) (num den : ℕ) : EntropyRat :=
  let g := Nat.gcd num den
  -- Reduce: if both are zero, treat as 0/1 (zero rational).
  let p := if g = 0 then 0 else num / g
  let q := if g = 0 then 1 else den / g
  -- If denominator reduced to zero, fall back to 1 to keep `q > 0`.
  let q' := if q = 0 then 1 else q
  -- Force non-negative sign for zero.
  let s := if p = 0 then true else sign
  let l := [s] ++ List.replicate p true ++ List.replicate q' false
  ⟨l, by
    refine ⟨s, p, q', ?_, ?_, ?_, ?_⟩
    · rfl
    · -- q' > 0
      dsimp only [q']
      split_ifs with hq
      · exact Nat.zero_lt_one
      · exact Nat.pos_of_ne_zero hq
    · -- Coprime p q'
      dsimp only [p, q', q]
      by_cases hg : g = 0
      · simp [hg, Nat.Coprime]
      · simp only [if_neg hg]
        -- num / g and den / g are coprime when g = gcd num den
        by_cases hd : den / g = 0
        · simp [hd, Nat.Coprime]
        · simp only [if_neg hd]
          -- Standard fact: (num / g).Coprime (den / g) when g = gcd num den
          have h_div_gcd : Nat.Coprime (num / g) (den / g) := by
            rcases Nat.eq_zero_or_pos g with hgz | hgp
            · exact absurd hgz hg
            · exact Nat.coprime_div_gcd_div_gcd hgp
          exact h_div_gcd
    · -- p = 0 → s = true
      intro hp
      dsimp only [s]
      simp [hp]⟩

/-- The canonical `EntropyRat` representing zero. -/
def EntropyRat.zero : EntropyRat := EntropyRat.mk true 0 1

/-- The canonical `EntropyRat` representing one. -/
def EntropyRat.one : EntropyRat := EntropyRat.mk true 1 1

/-- Encode a non-negative natural number as an `EntropyRat`. -/
def EntropyRat.ofNat (n : ℕ) : EntropyRat := EntropyRat.mk true n 1

/-- Encode the reciprocal `1 / n` of a positive natural number as an
`EntropyRat`. If `n = 0`, returns `EntropyRat.one` as a safe fallback
(this branch is unused along the Translation 1 path because variable
primes are always ≥ 3). -/
def EntropyRat.ofNatRecip (n : ℕ) : EntropyRat :=
  if n = 0 then EntropyRat.one else EntropyRat.mk true 1 n

/-- Negation of an `EntropyRat`: flip the sign bit (forced to `true`
when the value is zero, by canonical-form invariance). -/
def EntropyRat.neg (r : EntropyRat) : EntropyRat :=
  EntropyRat.mk (! r.sign) r.num r.den

/-- Multiplicative inverse of an `EntropyRat`: swap numerator and
denominator. Zero maps to zero (since `EntropyRat.mk _ 0 _ = 0`); this is
the standard convention for total inversion. -/
def EntropyRat.inv (r : EntropyRat) : EntropyRat :=
  EntropyRat.mk r.sign r.den r.num

/-- Addition of `EntropyRat`s via cross-multiplication on the underlying
`(sign, num, den)` triples. -/
def EntropyRat.add (a b : EntropyRat) : EntropyRat :=
  let pa := a.num
  let qa := a.den
  let pb := b.num
  let qb := b.den
  let sa : ℤ := if a.sign then (pa : ℤ) else -(pa : ℤ)
  let sb : ℤ := if b.sign then (pb : ℤ) else -(pb : ℤ)
  let cross : ℤ := sa * qb + sb * qa
  let s := decide (0 ≤ cross)
  let p := cross.natAbs
  let q := qa * qb
  EntropyRat.mk s p q

/-- Multiplication of `EntropyRat`s on `(sign, num, den)` triples. -/
def EntropyRat.mul (a b : EntropyRat) : EntropyRat :=
  let s := a.sign == b.sign
  let p := a.num * b.num
  let q := a.den * b.den
  EntropyRat.mk s p q

/-! ## `PolynomialRat`: constructive polynomials with `EntropyRat` coefficients

The `EntropyNat`-coefficient `Polynomial` defined above suffices for the
classical complexity bounds. Translation 1 (`InformationTheory.Isomorphisms.CNF.CNFPolynomialSystem`)
needs polynomials with **rational** coefficients and **subtraction** so that
clauses can be expressed as products of linear factors `(X − atom)`.

Concretely: each variable index is allocated an odd prime, and a literal's
*atom* is either that prime (for a positive literal) or its reciprocal (for
a negative literal). A clause translates to the product of `(X − atom_i)`
factors over its literals; a CNF translates to the list of clause polynomials.

The bijection between CNF and the resulting polynomial system is purely
*syntactic* on the `PolynomialRat` tree — no normalisation, no semantic
quotient by ring identities. The `eval` operation below is provided for
completeness / future Translation 2 work; the bijection itself does not
depend on it.
-/

/-- A constructive polynomial over `EntropyRat` coefficients.
Mirrors `Polynomial` (the `EntropyNat`-coefficient version above) but
admits subtraction via the `neg` constructor. Computable by construction. -/
inductive PolynomialRat : Type
  | const (c : EntropyRat) : PolynomialRat
  | id : PolynomialRat
  | add (p₁ p₂ : PolynomialRat) : PolynomialRat
  | mul (p₁ p₂ : PolynomialRat) : PolynomialRat
  | neg (p : PolynomialRat) : PolynomialRat

namespace PolynomialRat

/-- Subtraction as `add` of `neg`. -/
def sub (p₁ p₂ : PolynomialRat) : PolynomialRat :=
  PolynomialRat.add p₁ (PolynomialRat.neg p₂)

/-- Evaluate a `PolynomialRat` at an `EntropyRat` input via the
constructive `EntropyRat` arithmetic above. -/
def eval (p : PolynomialRat) (x : EntropyRat) : EntropyRat :=
  match p with
  | const c    => c
  | id         => x
  | add p₁ p₂  => EntropyRat.add (p₁.eval x) (p₂.eval x)
  | mul p₁ p₂  => EntropyRat.mul (p₁.eval x) (p₂.eval x)
  | neg p₁     => EntropyRat.neg (p₁.eval x)

end PolynomialRat

/-! ## Computable bijections to ℕ for `EntropyRat` and `PolynomialRat`

These encoders are used by `InformationTheory.Isomorphisms.CNF.CNFAsEntropyNat` to
build the constructive bijection `SyntacticCNF k ≃ EntropyNat`. Both
directions are computable and the closure stays at `{propext, Quot.sound}`.

The handoff explicitly forbids routing the bijection through Mathlib `ℚ`
(via `entropyRatEquivRat`, `EntropyRat.toRat`, or `EntropyRat.ofRat` —
all `noncomputable`); the encoders below do **not** touch any of those.
They consume only the canonical `List Bool` substrate of `EntropyRat`.

**Why we avoid `Nat.pair`/`Nat.unpair`.** Mathlib's `Nat.unpair_pair` /
`Nat.pair_unpair` round-trip lemmas pull `Classical.choice` through the
`split_ifs`/`simp` machinery used in their proofs, even though `Nat.pair`
itself is choice-free. The bijection chain below stops at
`Equiv.boolProdNatEquivNat : Bool × ℕ ≃ ℕ` (Mathlib's `bit`/`bodd`/`div2`
construction, audited choice-free), composed with structural recursion
on `List Bool`. No `Nat.pair`. No `Encodable`/`Denumerable`/`Classical`
escape hatches.

Each encoder is paired with a decoder and a round-trip lemma. We use the
"image-subtype Equiv" shape: `T ≃ { n : ℕ // ∃ t : T, toNat t = n }`,
which only requires the round-trip on `T` (not the round-trip on `ℕ`).
That is sufficient because Translation 2 composes these equivs (with
`entropyNatEquivNat.symm`) and works on the image side of each step.
-/

/-! ### `List Bool ≃ ℕ`

The base bijection. Encoding: empty list ↦ 0; cons ↦ shift+1 via
`boolProdNatEquivNat`. Decoding: peel a bit off the leading code-1
remainder until we hit zero. Choice-free because we use only
`boolProdNatEquivNat` (clean) and structural recursion. -/

/-- Encode a `List Bool` as a natural number. The empty list maps to 0;
the recursive step shifts via `Equiv.boolProdNatEquivNat`. -/
def listBoolToNat : List Bool → ℕ
  | []      => 0
  | b :: bs => Equiv.boolProdNatEquivNat (b, listBoolToNat bs) + 1

/-- Decode a natural number to a `List Bool`. Termination is by
strong recursion on `n`: at each step we peel off `(n-1).bodd` and
recurse on `(n-1).div2`, both of which produce strictly smaller
arguments. The implementation uses a fuel argument equal to `n` to
keep the recursion structural; for any `n`, fuel `n` is sufficient
(it strictly decreases by ≥ 1 per peel). -/
def listBoolFromNatAux : ℕ → ℕ → List Bool
  | 0,        _     => []
  | _,        0     => []
  | fuel + 1, n + 1 =>
      let bn := Equiv.boolProdNatEquivNat.symm n
      bn.1 :: listBoolFromNatAux fuel bn.2

def listBoolFromNat (n : ℕ) : List Bool :=
  listBoolFromNatAux n n

/-- The bit-decoder is monotone in fuel: any fuel ≥ the encoded length
suffices to recover the list. We prove the round-trip directly by
induction on the source list, with fuel taken to be the encoding. -/
theorem listBoolFromNatAux_toNat (l : List Bool) :
    ∀ fuel, l.length ≤ fuel → listBoolFromNatAux fuel (listBoolToNat l) = l := by
  induction l with
  | nil =>
    intro fuel _
    cases fuel with
    | zero => rfl
    | succ f => rfl
  | cons b bs ih =>
    intro fuel h_fuel
    cases fuel with
    | zero =>
      -- l.length = bs.length + 1 ≤ 0 is impossible.
      simp at h_fuel
    | succ f =>
      -- listBoolToNat (b :: bs) = boolProdNatEquivNat (b, listBoolToNat bs) + 1
      -- Pattern match on the encoded value: `listBoolFromNatAux (f+1) (m+1)`
      -- where m = boolProdNatEquivNat (b, listBoolToNat bs).
      show listBoolFromNatAux (f + 1) (listBoolToNat (b :: bs)) = b :: bs
      show listBoolFromNatAux (f + 1)
            (Equiv.boolProdNatEquivNat (b, listBoolToNat bs) + 1) = b :: bs
      -- Unfold the (succ, succ) case directly.
      show (Equiv.boolProdNatEquivNat.symm
              (Equiv.boolProdNatEquivNat (b, listBoolToNat bs))).1 ::
            listBoolFromNatAux f
              (Equiv.boolProdNatEquivNat.symm
                (Equiv.boolProdNatEquivNat (b, listBoolToNat bs))).2 = b :: bs
      rw [Equiv.symm_apply_apply]
      -- Goal reduces to `b :: listBoolFromNatAux f (listBoolToNat bs) = b :: bs`.
      -- Apply IH on `bs` with fuel `f`.
      have h_bs_fuel : bs.length ≤ f := by
        simp [List.length_cons] at h_fuel
        omega
      rw [ih f h_bs_fuel]

theorem listBoolFromNat_toNat (l : List Bool) :
    listBoolFromNat (listBoolToNat l) = l := by
  unfold listBoolFromNat
  apply listBoolFromNatAux_toNat l (listBoolToNat l)
  -- Need: l.length ≤ listBoolToNat l. By induction.
  induction l with
  | nil => simp [listBoolToNat]
  | cons b bs ih =>
    show (b :: bs).length ≤ listBoolToNat (b :: bs)
    show bs.length + 1 ≤ Equiv.boolProdNatEquivNat (b, listBoolToNat bs) + 1
    -- bs.length ≤ listBoolToNat bs (IH) ≤ boolProdNatEquivNat (b, listBoolToNat bs).
    -- The last inequality is `n ≤ bit b n`: bit b n = 2*n or 2*n+1, both ≥ n.
    have h_le : listBoolToNat bs ≤ Equiv.boolProdNatEquivNat (b, listBoolToNat bs) := by
      -- Equiv.boolProdNatEquivNat (b, n) = Nat.bit b n.
      -- Nat.bit false n = 2 * n; Nat.bit true n = 2 * n + 1. Both ≥ n.
      simp [Equiv.boolProdNatEquivNat, Nat.bit]
      cases b <;> simp <;> omega
    omega

/-- The hand-rolled List-Bool / ℕ bijection, image-subtype shape (just
to expose the round-trip; the forward direction `listBoolToNat` is the
load-bearing function). -/
def listBoolEquivImageNat :
    List Bool ≃ { n : ℕ // ∃ l : List Bool, listBoolToNat l = n } where
  toFun l := ⟨listBoolToNat l, ⟨l, rfl⟩⟩
  invFun n := listBoolFromNat n.val
  left_inv l := by
    show listBoolFromNat (listBoolToNat l) = l
    exact listBoolFromNat_toNat l
  right_inv := by
    rintro ⟨n, ⟨l, hl⟩⟩
    apply Subtype.ext
    show listBoolToNat (listBoolFromNat n) = n
    rw [← hl, listBoolFromNat_toNat l]

/-! ### `EntropyRat ≃ image ⊆ ℕ` -/

/-- Canonical re-construction: rebuilding an `EntropyRat` from its own
`(sign, num, den)` projections via `EntropyRat.mk` returns the original
value. The canonical-form invariants (`q > 0`, `Coprime p q`, `p = 0 → s = true`)
make `mk`'s normalisation a no-op on canonical input. -/
theorem EntropyRat.mk_canonical_id (r : EntropyRat) :
    EntropyRat.mk r.sign r.num r.den = r := by
  -- Step 1: extract the canonical witness `(s, p, q)` and identify it with the projections.
  obtain ⟨l, h_canon⟩ := r
  obtain ⟨s, p, q, h_struct, h_q_pos, h_coprime, h_zero_sign⟩ := h_canon
  -- Establish that the projections compute to the witness (s, p, q).
  have h_sign : EntropyRat.sign ⟨l, ⟨s, p, q, h_struct, h_q_pos, h_coprime, h_zero_sign⟩⟩ = s := by
    show List.head l _ = s
    -- Use the structural equality via the head_cons lemma after substitution.
    have : l.head (by rw [h_struct]; simp) = ([s] ++ List.replicate p true ++ List.replicate q false).head (by simp) := by
      congr 1
    rw [this]; rfl
  have h_num : EntropyRat.num ⟨l, ⟨s, p, q, h_struct, h_q_pos, h_coprime, h_zero_sign⟩⟩ = p := by
    show l.tail.count true = p
    rw [h_struct]
    simp [List.tail_cons, List.count_append, List.count_replicate]
  have h_den : EntropyRat.den ⟨l, ⟨s, p, q, h_struct, h_q_pos, h_coprime, h_zero_sign⟩⟩ = q := by
    show l.tail.count false = q
    rw [h_struct]
    simp [List.tail_cons, List.count_append, List.count_replicate]
  -- Step 2: rewrite the goal to use the witness directly.
  apply Subtype.ext
  rw [h_sign, h_num, h_den]
  -- Goal: (EntropyRat.mk s p q).val = l
  -- Step 3: unfold `mk` and identify the let-bindings with the canonical witness.
  have h_g : Nat.gcd p q = 1 := h_coprime
  have h_g_ne : Nat.gcd p q ≠ 0 := by rw [h_g]; decide
  have h_q_ne : q ≠ 0 := Nat.pos_iff_ne_zero.mp h_q_pos
  unfold EntropyRat.mk
  show [_] ++ List.replicate _ true ++ List.replicate _ false = l
  rw [h_struct]
  -- Three pieces to identify: s' = s, p' = p, q'' = q.
  congr 1
  · congr 1
    · -- s' = if p' = 0 then true else s; on canonical input s' = s.
      simp [h_g_ne, h_g]
      by_cases hp : p = 0
      · rw [hp]; simp [h_zero_sign hp]
      · simp [hp]
    · -- p' = p / gcd p q = p / 1 = p.
      simp [h_g_ne, h_g]
  · -- q'' = (if q' = 0 then 1 else q'), q' = q / 1 = q ≠ 0.
    simp [h_g_ne, h_g, h_q_ne]

/-- Encode an `EntropyRat` as a natural number via its canonical
`List Bool` substrate. The canonical form is `[sign] ++ replicate num true
++ replicate den false`, so this is just `listBoolToNat r.val`. Injective
because `r.val` already determines `r` (subtype carries `IsCanonical`). -/
def EntropyRat.toNat' (r : EntropyRat) : ℕ :=
  listBoolToNat r.val

/-- Decode a natural number back to an `EntropyRat`. The decoded list
may not be canonical for arbitrary `n`; we route the result through
`EntropyRat.mk` to re-establish canonical form. The triple `(sign, num, den)`
is extracted by inspecting the list head and counting trues/falses
in the tail. -/
def EntropyRat.ofNat' (n : ℕ) : EntropyRat :=
  let l := listBoolFromNat n
  let sign := l.head?.getD true
  let body := l.tail
  EntropyRat.mk sign (body.count true) (body.count false)

/-- Round-trip: decoding the encoding of any `EntropyRat` recovers it.
For a canonical `r`, decoding its `listBoolToNat`-encoded form first
recovers `r.val` (via `listBoolFromNat_toNat`), then `mk` on the
recovered triple is `r` itself by `mk_canonical_id`. -/
theorem EntropyRat.ofNat'_toNat' (r : EntropyRat) :
    EntropyRat.ofNat' (EntropyRat.toNat' r) = r := by
  obtain ⟨l, h_canon⟩ := r
  obtain ⟨s, p, q, h_struct, h_q_pos, h_coprime, h_zero_sign⟩ := h_canon
  -- Make the let-bindings explicit by stating the goal directly.
  show EntropyRat.mk
        ((listBoolFromNat (listBoolToNat l)).head?.getD true)
        (((listBoolFromNat (listBoolToNat l)).tail).count true)
        (((listBoolFromNat (listBoolToNat l)).tail).count false)
      = ⟨l, _⟩
  rw [listBoolFromNat_toNat]
  -- Goal: mk (l.head?.getD true) (l.tail.count true) (l.tail.count false) = ⟨l, _⟩.
  -- Identify the head/count projections with the canonical witness `(s, p, q)`.
  have h_head : l.head?.getD true = s := by
    rw [h_struct]; rfl
  have h_tail_t : l.tail.count true = p := by
    rw [h_struct]
    simp [List.tail_cons, List.count_append, List.count_replicate]
  have h_tail_f : l.tail.count false = q := by
    rw [h_struct]
    simp [List.tail_cons, List.count_append, List.count_replicate]
  rw [h_head, h_tail_t, h_tail_f]
  -- Goal: mk s p q = ⟨l, _⟩.
  have h_can := EntropyRat.mk_canonical_id ⟨l, ⟨s, p, q, h_struct, h_q_pos, h_coprime, h_zero_sign⟩⟩
  have h_sign : EntropyRat.sign ⟨l, ⟨s, p, q, h_struct, h_q_pos, h_coprime, h_zero_sign⟩⟩ = s := by
    show List.head l _ = s
    have : l.head (by rw [h_struct]; simp) = ([s] ++ List.replicate p true ++ List.replicate q false).head (by simp) := by
      congr 1
    rw [this]; rfl
  have h_num : EntropyRat.num ⟨l, ⟨s, p, q, h_struct, h_q_pos, h_coprime, h_zero_sign⟩⟩ = p := by
    show l.tail.count true = p
    rw [h_struct]
    simp [List.tail_cons, List.count_append, List.count_replicate]
  have h_den : EntropyRat.den ⟨l, ⟨s, p, q, h_struct, h_q_pos, h_coprime, h_zero_sign⟩⟩ = q := by
    show l.tail.count false = q
    rw [h_struct]
    simp [List.tail_cons, List.count_append, List.count_replicate]
  rw [h_sign, h_num, h_den] at h_can
  exact h_can

/-- The bijection `EntropyRat ≃ image-of-toNat'`. -/
def entropyRatEquivImageNat :
    EntropyRat ≃ { n : ℕ // ∃ r : EntropyRat, EntropyRat.toNat' r = n } where
  toFun r := ⟨EntropyRat.toNat' r, ⟨r, rfl⟩⟩
  invFun n := EntropyRat.ofNat' n.val
  left_inv r := EntropyRat.ofNat'_toNat' r
  right_inv := by
    rintro ⟨n, hex⟩
    apply Subtype.ext
    obtain ⟨r, hr⟩ := hex
    show EntropyRat.toNat' (EntropyRat.ofNat' n) = n
    rw [← hr, EntropyRat.ofNat'_toNat' r]

/-! ### `PolynomialRat ≃ image ⊆ ℕ`

We encode `PolynomialRat` first as a `List Bool` (a self-delimiting
prefix-free code over the five constructors), then compose with
`listBoolToNat`. Each constructor uses 3 leading bits as a tag (3 bits
fit 8 codes; we use 5 of them):

| Constructor       | Tag bits |
|-------------------|----------|
| `const c`         | `[F, F, F]` followed by the EntropyRat substrate `c.val` |
| `id`              | `[F, F, T]` |
| `add p₁ p₂`       | `[F, T, F]` followed by encoded `p₁` then encoded `p₂` |
| `mul p₁ p₂`       | `[F, T, T]` followed by encoded `p₁` then encoded `p₂` |
| `neg p₁`          | `[T, F, F]` followed by encoded `p₁` |

For the `const` case we delimit the EntropyRat substrate with a
length prefix (Elias-gamma–style: encode `len` in unary as
`replicate len true ++ [false]`, then the substrate). For binary
constructors we similarly length-prefix each subtree's encoding. The
decoder is a list-consuming parser, structural on list length. -/

/-- Encode a `ℕ` length prefix as `replicate n true ++ [false]`. -/
def unaryLen (n : ℕ) : List Bool :=
  List.replicate n true ++ [false]

/-- Decode a length prefix: count leading `true`s up to the first `false`. -/
def unaryLenDecode : List Bool → ℕ × List Bool
  | [] => (0, [])
  | false :: rest => (0, rest)
  | true :: rest =>
      let (n, rest') := unaryLenDecode rest
      (n + 1, rest')

theorem unaryLenDecode_unaryLen (n : ℕ) (suffix : List Bool) :
    unaryLenDecode (unaryLen n ++ suffix) = (n, suffix) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show unaryLenDecode (List.replicate (k + 1) true ++ [false] ++ suffix) = (k + 1, suffix)
    rw [List.replicate_succ]
    show unaryLenDecode ((true :: List.replicate k true) ++ [false] ++ suffix) = (k + 1, suffix)
    rw [List.cons_append, List.cons_append]
    show unaryLenDecode (true :: (List.replicate k true ++ [false] ++ suffix)) = (k + 1, suffix)
    -- Unfold the cons branch of unaryLenDecode.
    show (let (m, rest) := unaryLenDecode (List.replicate k true ++ [false] ++ suffix)
          (m + 1, rest)) = (k + 1, suffix)
    -- Apply IH on the tail.
    have h_tail : unaryLenDecode (List.replicate k true ++ [false] ++ suffix) = (k, suffix) := by
      have := ih
      show unaryLenDecode (unaryLen k ++ suffix) = (k, suffix)
      exact this
    rw [h_tail]

/-- Encode a `PolynomialRat` as a `List Bool`. -/
def PolynomialRat.toList : PolynomialRat → List Bool
  | PolynomialRat.const c   =>
      [false, false, false] ++ unaryLen c.val.length ++ c.val
  | PolynomialRat.id        => [false, false, true]
  | PolynomialRat.add p₁ p₂ =>
      let l₁ := PolynomialRat.toList p₁
      let l₂ := PolynomialRat.toList p₂
      [false, true, false] ++ unaryLen l₁.length ++ l₁ ++ l₂
  | PolynomialRat.mul p₁ p₂ =>
      let l₁ := PolynomialRat.toList p₁
      let l₂ := PolynomialRat.toList p₂
      [false, true, true] ++ unaryLen l₁.length ++ l₁ ++ l₂
  | PolynomialRat.neg p₁    =>
      [true, false, false] ++ PolynomialRat.toList p₁

/-- Fuel-based parser for `PolynomialRat`. Consumes a `List Bool` and
returns `(parsed, remainder)`. Fuel is structural; decoding the encoding
of a tree of size ≤ fuel always succeeds and consumes exactly the tree's
bytes. Returns `(id, [])` on exhaustion or unknown tag (defensive
defaults; unreachable on `toList`-encoded inputs). -/
def PolynomialRat.parse : ℕ → List Bool → PolynomialRat × List Bool
  | 0,        l => (PolynomialRat.id, l)
  | fuel + 1, l =>
      match l with
      | false :: false :: false :: rest =>
          -- const: read length prefix then take that many bits.
          let (len, after_len) := unaryLenDecode rest
          let body := after_len.take len
          let after_body := after_len.drop len
          -- Reconstruct an EntropyRat by routing through `mk`.
          let sign := body.head?.getD true
          let inner := body.tail
          (PolynomialRat.const
             (EntropyRat.mk sign (inner.count true) (inner.count false)),
           after_body)
      | false :: false :: true :: rest =>
          (PolynomialRat.id, rest)
      | false :: true :: false :: rest =>
          let (len, after_len) := unaryLenDecode rest
          let l₁_bits := after_len.take len
          let l₂_bits := after_len.drop len
          let (p₁, _) := PolynomialRat.parse fuel l₁_bits
          let (p₂, l₂_rest) := PolynomialRat.parse fuel l₂_bits
          (PolynomialRat.add p₁ p₂, l₂_rest)
      | false :: true :: true :: rest =>
          let (len, after_len) := unaryLenDecode rest
          let l₁_bits := after_len.take len
          let l₂_bits := after_len.drop len
          let (p₁, _) := PolynomialRat.parse fuel l₁_bits
          let (p₂, l₂_rest) := PolynomialRat.parse fuel l₂_bits
          (PolynomialRat.mul p₁ p₂, l₂_rest)
      | true :: false :: false :: rest =>
          let (p₁, rest') := PolynomialRat.parse fuel rest
          (PolynomialRat.neg p₁, rest')
      | _ => (PolynomialRat.id, [])

/-- Top-level decoder from `List Bool` to `PolynomialRat`. Uses
`l.length + 1` as fuel — always sufficient because each parser step
consumes at least 3 bits (a tag triple), so the maximum recursion
depth is bounded by the input length. -/
def PolynomialRat.fromList (l : List Bool) : PolynomialRat :=
  (PolynomialRat.parse (l.length + 1) l).1

/-- Encode a `PolynomialRat` as a natural number via its `List Bool` encoding. -/
def PolynomialRat.toNat' (p : PolynomialRat) : ℕ :=
  listBoolToNat p.toList

/-- Decode a natural number to a `PolynomialRat`. -/
def PolynomialRat.ofNat' (n : ℕ) : PolynomialRat :=
  PolynomialRat.fromList (listBoolFromNat n)

/-- Helper: parser round-trip with sufficient fuel.
For any `p` and any suffix, parsing `(p.toList ++ suffix)` with
`fuel ≥ p.size` returns `(p, suffix)`. -/
theorem PolynomialRat.parse_toList (p : PolynomialRat) :
    ∀ (fuel : ℕ), 1 + p.toList.length ≤ fuel →
      ∀ (suffix : List Bool),
        PolynomialRat.parse fuel (p.toList ++ suffix) = (p, suffix) := by
  induction p with
  | const c =>
    intro fuel h_fuel suffix
    cases fuel with
    | zero => simp [PolynomialRat.toList] at h_fuel
    | succ f =>
      -- toList (const c) = [F, F, F] ++ unaryLen c.val.length ++ c.val
      show PolynomialRat.parse (f + 1)
            ([false, false, false] ++ unaryLen c.val.length ++ c.val ++ suffix) = _
      -- Rewrite associativity to match the parse pattern.
      rw [show ([false, false, false] ++ unaryLen c.val.length ++ c.val ++ suffix)
            = (false :: false :: false :: (unaryLen c.val.length ++ c.val ++ suffix))
          from by simp [List.cons_append, List.append_assoc]]
      -- Pattern match: const branch.
      show (let (len, after_len) := unaryLenDecode (unaryLen c.val.length ++ c.val ++ suffix)
            let body := after_len.take len
            let after_body := after_len.drop len
            let sign := body.head?.getD true
            let inner := body.tail
            (PolynomialRat.const
               (EntropyRat.mk sign (inner.count true) (inner.count false)),
             after_body))
            = (PolynomialRat.const c, suffix)
      rw [show unaryLen c.val.length ++ c.val ++ suffix
            = unaryLen c.val.length ++ (c.val ++ suffix) from by rw [List.append_assoc]]
      rw [unaryLenDecode_unaryLen]
      -- Now: take c.val.length (c.val ++ suffix) = c.val and drop = suffix.
      show (let body := (c.val ++ suffix).take c.val.length
            let after_body := (c.val ++ suffix).drop c.val.length
            let sign := body.head?.getD true
            let inner := body.tail
            (PolynomialRat.const
               (EntropyRat.mk sign (inner.count true) (inner.count false)),
             after_body))
            = (PolynomialRat.const c, suffix)
      rw [List.take_left, List.drop_left]
      -- Goal: const (mk (c.val.head?.getD true) (c.val.tail.count true) (c.val.tail.count false)) = const c.
      -- This is the canonical-id reconstruction for c.
      have h_id := EntropyRat.ofNat'_toNat' c
      -- Unfold to extract the structural argument.
      obtain ⟨l, h_canon⟩ := c
      obtain ⟨s, p, q, h_struct, h_q_pos, h_coprime, h_zero_sign⟩ := h_canon
      have h_head : l.head?.getD true = s := by rw [h_struct]; rfl
      have h_tail_t : l.tail.count true = p := by
        rw [h_struct]; simp [List.tail_cons, List.count_append, List.count_replicate]
      have h_tail_f : l.tail.count false = q := by
        rw [h_struct]; simp [List.tail_cons, List.count_append, List.count_replicate]
      show (PolynomialRat.const
            (EntropyRat.mk (l.head?.getD true) (l.tail.count true) (l.tail.count false)),
            suffix) = (PolynomialRat.const ⟨l, _⟩, suffix)
      rw [h_head, h_tail_t, h_tail_f]
      have h_can := EntropyRat.mk_canonical_id ⟨l, ⟨s, p, q, h_struct, h_q_pos, h_coprime, h_zero_sign⟩⟩
      have h_sign : EntropyRat.sign ⟨l, ⟨s, p, q, h_struct, h_q_pos, h_coprime, h_zero_sign⟩⟩ = s := by
        show List.head l _ = s
        have : l.head (by rw [h_struct]; simp) = ([s] ++ List.replicate p true ++ List.replicate q false).head (by simp) := by
          congr 1
        rw [this]; rfl
      have h_num : EntropyRat.num ⟨l, ⟨s, p, q, h_struct, h_q_pos, h_coprime, h_zero_sign⟩⟩ = p := by
        show l.tail.count true = p
        rw [h_struct]; simp [List.tail_cons, List.count_append, List.count_replicate]
      have h_den : EntropyRat.den ⟨l, ⟨s, p, q, h_struct, h_q_pos, h_coprime, h_zero_sign⟩⟩ = q := by
        show l.tail.count false = q
        rw [h_struct]; simp [List.tail_cons, List.count_append, List.count_replicate]
      rw [h_sign, h_num, h_den] at h_can
      rw [h_can]
  | id =>
    intro fuel h_fuel suffix
    cases fuel with
    | zero => simp [PolynomialRat.toList] at h_fuel
    | succ f =>
      show PolynomialRat.parse (f + 1) ([false, false, true] ++ suffix) = _
      rw [show ([false, false, true] ++ suffix)
            = (false :: false :: true :: suffix) from by simp]
      rfl
  | add p₁ p₂ ih₁ ih₂ =>
    intro fuel h_fuel suffix
    cases fuel with
    | zero => simp [PolynomialRat.toList] at h_fuel
    | succ f =>
      show PolynomialRat.parse (f + 1)
            ([false, true, false] ++ unaryLen (PolynomialRat.toList p₁).length
              ++ PolynomialRat.toList p₁ ++ PolynomialRat.toList p₂ ++ suffix) = _
      rw [show ([false, true, false] ++ unaryLen (PolynomialRat.toList p₁).length
              ++ PolynomialRat.toList p₁ ++ PolynomialRat.toList p₂ ++ suffix)
            = (false :: true :: false ::
                (unaryLen (PolynomialRat.toList p₁).length ++ PolynomialRat.toList p₁
                 ++ PolynomialRat.toList p₂ ++ suffix))
          from by simp [List.cons_append, List.append_assoc]]
      show (let (len, after_len) := unaryLenDecode
                (unaryLen (PolynomialRat.toList p₁).length ++ PolynomialRat.toList p₁
                 ++ PolynomialRat.toList p₂ ++ suffix)
            let l₁_bits := after_len.take len
            let l₂_bits := after_len.drop len
            let (q₁, _) := PolynomialRat.parse f l₁_bits
            let (q₂, l₂_rest) := PolynomialRat.parse f l₂_bits
            (PolynomialRat.add q₁ q₂, l₂_rest))
            = (PolynomialRat.add p₁ p₂, suffix)
      rw [show unaryLen (PolynomialRat.toList p₁).length ++ PolynomialRat.toList p₁
              ++ PolynomialRat.toList p₂ ++ suffix
            = unaryLen (PolynomialRat.toList p₁).length
              ++ (PolynomialRat.toList p₁ ++ PolynomialRat.toList p₂ ++ suffix)
          from by simp [List.append_assoc]]
      rw [unaryLenDecode_unaryLen]
      show (let l₁_bits := (PolynomialRat.toList p₁ ++ PolynomialRat.toList p₂ ++ suffix).take
                              (PolynomialRat.toList p₁).length
            let l₂_bits := (PolynomialRat.toList p₁ ++ PolynomialRat.toList p₂ ++ suffix).drop
                              (PolynomialRat.toList p₁).length
            let (q₁, _) := PolynomialRat.parse f l₁_bits
            let (q₂, l₂_rest) := PolynomialRat.parse f l₂_bits
            (PolynomialRat.add q₁ q₂, l₂_rest))
            = (PolynomialRat.add p₁ p₂, suffix)
      rw [show (PolynomialRat.toList p₁ ++ PolynomialRat.toList p₂ ++ suffix)
            = PolynomialRat.toList p₁ ++ (PolynomialRat.toList p₂ ++ suffix)
          from by rw [List.append_assoc]]
      rw [List.take_left, List.drop_left]
      -- Now: parse f (toList p₁) and parse f (toList p₂ ++ suffix).
      -- Both need fuel f ≥ 1 + their size, which we get from h_fuel.
      simp [PolynomialRat.toList] at h_fuel
      have h_p₁_fuel : 1 + (PolynomialRat.toList p₁).length ≤ f := by
        have h₁ : (PolynomialRat.toList p₁).length ≤ (PolynomialRat.toList p₁).length := le_refl _
        omega
      have h_p₂_fuel : 1 + (PolynomialRat.toList p₂).length ≤ f := by omega
      -- Apply IH₁ with empty suffix and IH₂ with the actual suffix.
      have h_p₁ := ih₁ f h_p₁_fuel []
      have h_p₂ := ih₂ f h_p₂_fuel suffix
      rw [List.append_nil] at h_p₁
      -- Now reduce the `let l₁_bits := ...` block.
      show (match PolynomialRat.parse f (PolynomialRat.toList p₁) with
            | (q₁, _) =>
              match PolynomialRat.parse f (PolynomialRat.toList p₂ ++ suffix) with
              | (q₂, l₂_rest) => (PolynomialRat.add q₁ q₂, l₂_rest))
            = (PolynomialRat.add p₁ p₂, suffix)
      rw [h_p₁, h_p₂]
  | mul p₁ p₂ ih₁ ih₂ =>
    intro fuel h_fuel suffix
    cases fuel with
    | zero => simp [PolynomialRat.toList] at h_fuel
    | succ f =>
      show PolynomialRat.parse (f + 1)
            ([false, true, true] ++ unaryLen (PolynomialRat.toList p₁).length
              ++ PolynomialRat.toList p₁ ++ PolynomialRat.toList p₂ ++ suffix) = _
      rw [show ([false, true, true] ++ unaryLen (PolynomialRat.toList p₁).length
              ++ PolynomialRat.toList p₁ ++ PolynomialRat.toList p₂ ++ suffix)
            = (false :: true :: true ::
                (unaryLen (PolynomialRat.toList p₁).length ++ PolynomialRat.toList p₁
                 ++ PolynomialRat.toList p₂ ++ suffix))
          from by simp [List.cons_append, List.append_assoc]]
      show (let (len, after_len) := unaryLenDecode
                (unaryLen (PolynomialRat.toList p₁).length ++ PolynomialRat.toList p₁
                 ++ PolynomialRat.toList p₂ ++ suffix)
            let l₁_bits := after_len.take len
            let l₂_bits := after_len.drop len
            let (q₁, _) := PolynomialRat.parse f l₁_bits
            let (q₂, l₂_rest) := PolynomialRat.parse f l₂_bits
            (PolynomialRat.mul q₁ q₂, l₂_rest))
            = (PolynomialRat.mul p₁ p₂, suffix)
      rw [show unaryLen (PolynomialRat.toList p₁).length ++ PolynomialRat.toList p₁
              ++ PolynomialRat.toList p₂ ++ suffix
            = unaryLen (PolynomialRat.toList p₁).length
              ++ (PolynomialRat.toList p₁ ++ PolynomialRat.toList p₂ ++ suffix)
          from by simp [List.append_assoc]]
      rw [unaryLenDecode_unaryLen]
      show (let l₁_bits := (PolynomialRat.toList p₁ ++ PolynomialRat.toList p₂ ++ suffix).take
                              (PolynomialRat.toList p₁).length
            let l₂_bits := (PolynomialRat.toList p₁ ++ PolynomialRat.toList p₂ ++ suffix).drop
                              (PolynomialRat.toList p₁).length
            let (q₁, _) := PolynomialRat.parse f l₁_bits
            let (q₂, l₂_rest) := PolynomialRat.parse f l₂_bits
            (PolynomialRat.mul q₁ q₂, l₂_rest))
            = (PolynomialRat.mul p₁ p₂, suffix)
      rw [show (PolynomialRat.toList p₁ ++ PolynomialRat.toList p₂ ++ suffix)
            = PolynomialRat.toList p₁ ++ (PolynomialRat.toList p₂ ++ suffix)
          from by rw [List.append_assoc]]
      rw [List.take_left, List.drop_left]
      simp [PolynomialRat.toList] at h_fuel
      have h_p₁_fuel : 1 + (PolynomialRat.toList p₁).length ≤ f := by omega
      have h_p₂_fuel : 1 + (PolynomialRat.toList p₂).length ≤ f := by omega
      have h_p₁ := ih₁ f h_p₁_fuel []
      have h_p₂ := ih₂ f h_p₂_fuel suffix
      rw [List.append_nil] at h_p₁
      show (match PolynomialRat.parse f (PolynomialRat.toList p₁) with
            | (q₁, _) =>
              match PolynomialRat.parse f (PolynomialRat.toList p₂ ++ suffix) with
              | (q₂, l₂_rest) => (PolynomialRat.mul q₁ q₂, l₂_rest))
            = (PolynomialRat.mul p₁ p₂, suffix)
      rw [h_p₁, h_p₂]
  | neg p₁ ih =>
    intro fuel h_fuel suffix
    cases fuel with
    | zero => simp [PolynomialRat.toList] at h_fuel
    | succ f =>
      show PolynomialRat.parse (f + 1)
            ([true, false, false] ++ PolynomialRat.toList p₁ ++ suffix) = _
      rw [show ([true, false, false] ++ PolynomialRat.toList p₁ ++ suffix)
            = (true :: false :: false :: (PolynomialRat.toList p₁ ++ suffix))
          from by simp [List.cons_append, List.append_assoc]]
      show (let (q₁, rest') := PolynomialRat.parse f (PolynomialRat.toList p₁ ++ suffix)
            (PolynomialRat.neg q₁, rest'))
            = (PolynomialRat.neg p₁, suffix)
      simp [PolynomialRat.toList] at h_fuel
      have h_p₁_fuel : 1 + (PolynomialRat.toList p₁).length ≤ f := by omega
      have h_p₁ := ih f h_p₁_fuel suffix
      rw [h_p₁]

/-- Round-trip on `toList`. -/
theorem PolynomialRat.fromList_toList (p : PolynomialRat) :
    PolynomialRat.fromList p.toList = p := by
  unfold PolynomialRat.fromList
  have h := PolynomialRat.parse_toList p (p.toList.length + 1) (by omega) []
  rw [List.append_nil] at h
  rw [h]

/-- Top-level round-trip: `ofNat'` recovers `p` from its `toNat'` encoding. -/
theorem PolynomialRat.ofNat'_toNat' (p : PolynomialRat) :
    PolynomialRat.ofNat' (PolynomialRat.toNat' p) = p := by
  unfold PolynomialRat.ofNat' PolynomialRat.toNat'
  rw [listBoolFromNat_toNat]
  exact PolynomialRat.fromList_toList p

/-- The bijection `PolynomialRat ≃ image-of-toNat'`. -/
def polynomialRatEquivImageNat :
    PolynomialRat ≃ { n : ℕ // ∃ p : PolynomialRat, PolynomialRat.toNat' p = n } where
  toFun p := ⟨PolynomialRat.toNat' p, ⟨p, rfl⟩⟩
  invFun n := PolynomialRat.ofNat' n.val
  left_inv p := PolynomialRat.ofNat'_toNat' p
  right_inv := by
    rintro ⟨n, hex⟩
    apply Subtype.ext
    obtain ⟨p, hp⟩ := hex
    show PolynomialRat.toNat' (PolynomialRat.ofNat' n) = n
    rw [← hp, PolynomialRat.ofNat'_toNat' p]

end InformationTheory
