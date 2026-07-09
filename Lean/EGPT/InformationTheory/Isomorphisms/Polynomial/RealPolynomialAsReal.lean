-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.

/- RealPolynomialAsReal — every coefficient-list real polynomial over `EntropyReal`
*is* an `EntropyReal` under the canonical address-bit encoding, mirroring
`PolynomialAsNat.lean`'s landing of `PolynomialRat ≃ EntropyNat`.

The chain:

```
   DensePolyReal (= List EntropyReal)
     ↕  zero-point projection + unaryLen prefix + listBoolToEntropyReal
   EntropyReal (= EntropyNat → Bool = Nat_L 1 = Real_L 0)
```

Per-polynomial encoding uses the **zero-point projection**
`evalEntropyRealZero : EntropyReal → Bool` (read at `EntropyNat.ofNat 0`),
a unary length prefix (`unaryLen`, same substrate as Translation 2), then
stores coefficient bits at consecutive `EntropyNat` addresses inside one
`EntropyReal`. Decode with `ofEntropyRealFuel fuel` reads `fuel` address
bits, parses the prefix, and lifts each coefficient bit to
`constantEntropyReal`.

On the encoding image, `ofEntropyRealFuel (encFuel p)` round-trips to
`canonicalize p` — the constant-lift representative of `p`'s zero-point
projection. `decodeFuel` finds sufficient read fuel by iterating
`encFuelFromBits` on the bits read so far (mirroring
`PolynomialRat.fromList`'s `l.length + 1` fuel discipline). The bundled
image-subtype `Equiv` `equivEntropyReal` matches
`PolynomialRat.equivEntropyNat`; on canonical polynomials the inverse
round-trips exactly.

Closure target: `{propext, Quot.sound}`. -/

module

public import InformationTheory.EntropyNumber.Real
public import InformationTheory.EntropyNumber.Polynomial
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


set_option maxRecDepth 100000
set_option maxHeartbeats 400000

namespace InformationTheory

/-! # §0 — Base substrate: `List Bool ↔ EntropyReal` -/

def constantEntropyReal (b : Bool) : EntropyReal :=
  fun _ => b

@[simp] theorem evalEntropyRealZero_constant (b : Bool) :
    evalEntropyRealZero (constantEntropyReal b) = b := rfl

def listBoolToEntropyReal (bs : List Bool) : EntropyReal :=
  fun e => bs.getD (entropyNatEquivNat e) false

def listBoolFromEntropyReal (n : ℕ) (r : EntropyReal) : List Bool :=
  (List.range n).map (fun i => r (entropyNatEquivNat.symm i))

private theorem listBool_getD_toReal (bs : List Bool) (i : ℕ) (hi : i < bs.length) :
    (listBoolToEntropyReal bs) (entropyNatEquivNat.symm i) = bs[i] := by
  simp [listBoolToEntropyReal, Equiv.apply_symm_apply, List.getD, hi]

theorem listBoolFromEntropyReal_toReal (bs : List Bool) :
    listBoolFromEntropyReal bs.length (listBoolToEntropyReal bs) = bs := by
  apply List.ext_getElem
  · simp [listBoolFromEntropyReal, List.length_map, List.length_range]
  · intro i hi hi'
    have hi' : i < bs.length := by
      simpa [List.length_map, List.length_range] using hi'
    simp [listBoolFromEntropyReal, List.getElem_map, List.getElem_range]
    exact listBool_getD_toReal bs i hi'

theorem listBoolToEntropyReal_append_false (bs : List Bool) (k : ℕ) :
    listBoolToEntropyReal bs = listBoolToEntropyReal (bs ++ List.replicate k false) := by
  funext e
  simp only [listBoolToEntropyReal, Equiv.symm_apply_apply, List.getD]
  by_cases h : entropyNatEquivNat e < bs.length
  · simp [h, List.getElem?_append_left, List.getElem?_eq_getElem]
  · have hle := Nat.le_of_not_gt h
    simp [h, List.getD]
    rw [List.getElem?_append_right hle]
    by_cases hk : entropyNatEquivNat e - bs.length < k
    · simp [hk, List.getElem?_replicate, List.getD]
    · simp [hk, List.getD]

def encFuel (n : ℕ) : ℕ :=
  n + 1 + n

/-! # §1 — `DensePolyReal` (mirrors `PolynomialAsNat` §1) -/

abbrev DensePolyReal : Type := List EntropyReal

namespace DensePolyReal

def toCoeffBits (p : DensePolyReal) : List Bool :=
  p.map evalEntropyRealZero

def encBits (p : DensePolyReal) : List Bool :=
  unaryLen p.length ++ toCoeffBits p

def encFuel (p : DensePolyReal) : ℕ :=
  InformationTheory.encFuel p.length

/-- A `DensePolyReal` as an `EntropyReal`. Forward map; choice-free. -/
def toEntropyReal (p : DensePolyReal) : EntropyReal :=
  listBoolToEntropyReal (encBits p)

/-- Canonical form: constant-lift of each zero-point coefficient bit. -/
def canonicalize (p : DensePolyReal) : DensePolyReal :=
  p.map (fun c => constantEntropyReal (evalEntropyRealZero c))

def IsCanonical (p : DensePolyReal) : Prop :=
  p = canonicalize p

attribute [irreducible] DensePolyReal.canonicalize

theorem canonicalize_canonicalize (p : DensePolyReal) :
    canonicalize (canonicalize p) = canonicalize p := by
  unfold canonicalize
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp [List.getElem_map, evalEntropyRealZero_constant]

theorem isCanonical_canonicalize (p : DensePolyReal) :
    IsCanonical (canonicalize p) := by
  unfold IsCanonical
  exact (canonicalize_canonicalize p).symm

/-- Recover a dense real polynomial from an `EntropyReal`, given sufficient
read fuel. Off-image / under-fueled inputs default to a prefix parse. -/
def ofEntropyRealFuel (fuel : ℕ) (r : EntropyReal) : DensePolyReal :=
  let bs := listBoolFromEntropyReal fuel r
  let (len, after) := unaryLenDecode bs
  (after.take len).map constantEntropyReal

/-- Estimate sufficient read fuel from a (possibly partial) bit prefix:
`unaryLen len` consumes `len + 1` bits and `len` coefficient bits follow. -/
def encFuelFromBits (bs : List Bool) : ℕ :=
  let (len, _) := unaryLenDecode bs
  InformationTheory.encFuel len

/-- Read-cap for auto fuel discovery (supports `DensePolyReal` length ≤ 32767). -/
def decodeReadCap : ℕ := 65536

/-- Sufficient read fuel for decoding an encoded polynomial from `r`. On the
encoding image with `encFuel p ≤ decodeReadCap`, this equals `encFuel p`. -/
def decodeFuel (r : EntropyReal) : ℕ :=
  encFuelFromBits (listBoolFromEntropyReal decodeReadCap r)

/-- Top-level decoder: read up to `decodeReadCap` addresses, auto-estimate
fuel via `decodeFuel`. On the encoding image with `encFuel p ≤ decodeReadCap`,
round-trips to `canonicalize p`. -/
def ofEntropyReal (r : EntropyReal) : DensePolyReal :=
  ofEntropyRealFuel decodeReadCap r

theorem encBits_length (p : DensePolyReal) :
    (encBits p).length = encFuel p := by
  rw [encBits, encFuel, InformationTheory.encFuel, unaryLen, toCoeffBits]
  simp [List.length_append, List.length_replicate, List.length_map]
  omega

theorem listBoolFromEntropyReal_encBits (p : DensePolyReal) :
    listBoolFromEntropyReal (encFuel p) (toEntropyReal p) = encBits p := by
  rw [← encBits_length]
  exact listBoolFromEntropyReal_toReal (encBits p)

/-- **Round-trip on the encoding image** (operational inverse of
`toEntropyReal`). Matches Translation 6's constant-lift decode shape. -/
theorem ofEntropyRealFuel_toCanonical (p : DensePolyReal) :
    ofEntropyRealFuel (encFuel p) (toEntropyReal p) = canonicalize p := by
  simp only [ofEntropyRealFuel, canonicalize, toCoeffBits, encBits,
    listBoolFromEntropyReal_encBits, unaryLenDecode_unaryLen]
  have hlen : (List.map evalEntropyRealZero p).length = p.length := by simp
  rw [← hlen, List.take_length]
  simp [List.map_map]

theorem toEntropyReal_canonicalize (p : DensePolyReal) :
    toEntropyReal (canonicalize p) = toEntropyReal p := by
  unfold toEntropyReal encBits toCoeffBits canonicalize
  congr 1 <;> simp [List.length_map, evalEntropyRealZero_constant]

/-- Forward round-trip on the encoding image. -/
theorem toEntropyReal_ofEntropyRealFuel (p : DensePolyReal) :
    toEntropyReal (ofEntropyRealFuel (encFuel p) (toEntropyReal p)) = toEntropyReal p := by
  rw [ofEntropyRealFuel_toCanonical, toEntropyReal_canonicalize]

/-- Full round-trip for canonical polynomials. -/
theorem ofEntropyRealFuel_toSelf (p : DensePolyReal) (h : IsCanonical p) :
    ofEntropyRealFuel (encFuel p) (toEntropyReal p) = p := by
  rw [ofEntropyRealFuel_toCanonical]
  exact h.symm

theorem encFuelFromBits_encBits (p : DensePolyReal) (suffix : List Bool) :
    encFuelFromBits (encBits p ++ suffix) = encFuel p := by
  unfold encFuelFromBits encFuel InformationTheory.encFuel encBits toCoeffBits
  simp [unaryLenDecode_unaryLen, List.length_map]

private theorem unaryLenDecode_encBits_suffix (p : DensePolyReal) (suffix : List Bool) :
    unaryLenDecode (encBits p ++ suffix) = (p.length, p.toCoeffBits ++ suffix) := by
  unfold encBits toCoeffBits
  rw [List.append_assoc, unaryLenDecode_unaryLen]

theorem toEntropyReal_append_false (p : DensePolyReal) (k : ℕ) :
    toEntropyReal p = listBoolToEntropyReal (encBits p ++ List.replicate k false) := by
  funext e
  simp only [toEntropyReal, listBoolToEntropyReal, Equiv.symm_apply_apply, List.getD]
  by_cases h : entropyNatEquivNat e < (encBits p).length
  · simp [h, List.getElem?_append_left, List.getElem?_eq_getElem]
  · have hle := Nat.le_of_not_gt h
    have hlhs : ¬entropyNatEquivNat e < (encBits p).length := h
    simp [hlhs, List.getD]
    rw [List.getElem?_append_right hle]
    by_cases hk : entropyNatEquivNat e - (encBits p).length < k
    · simp [hk, List.getElem?_replicate, List.getD]
    · simp [hk, List.getD]

theorem listBoolFromEntropyReal_toEntropyReal_ge (p : DensePolyReal) (fuel : ℕ)
    (h : encFuel p ≤ fuel) :
    listBoolFromEntropyReal fuel (toEntropyReal p)
      = encBits p ++ List.replicate (fuel - encFuel p) false := by
  set k := fuel - encFuel p
  have hk : encFuel p + k = fuel := Nat.add_sub_of_le h
  calc
    listBoolFromEntropyReal fuel (toEntropyReal p)
        = listBoolFromEntropyReal ((encBits p ++ List.replicate k false).length)
            (listBoolToEntropyReal (encBits p ++ List.replicate k false)) := by
          rw [← hk, (encBits_length p).symm, toEntropyReal_append_false p k]
          simp [List.length_append, List.length_replicate]
    _ = encBits p ++ List.replicate k false :=
          listBoolFromEntropyReal_toReal (encBits p ++ List.replicate k false)

private theorem List.take_prefix_append {α} (l1 l2 : List α) :
    (l1 ++ l2).take l1.length = l1 := by
  induction l1 with
  | nil => rfl
  | cons a l ih =>
    simp [List.take_cons, List.length_cons, ih]

theorem ofEntropyRealFuel_ge_toCanonical (p : DensePolyReal) (fuel : ℕ)
    (h : encFuel p ≤ fuel) :
    ofEntropyRealFuel fuel (toEntropyReal p) = canonicalize p := by
  simp only [ofEntropyRealFuel, canonicalize, toCoeffBits]
  rw [listBoolFromEntropyReal_toEntropyReal_ge p fuel h]
  rw [unaryLenDecode_encBits_suffix p (List.replicate (fuel - encFuel p) false)]
  dsimp only
  have hlen : p.toCoeffBits.length = p.length := by simp [toCoeffBits]
  rw [← hlen, List.take_prefix_append]
  simp [canonicalize, toCoeffBits]

theorem encFuelFromBits_listBoolFromEntropyReal_ge (p : DensePolyReal) (fuel : ℕ)
    (h : encFuel p ≤ fuel) :
    encFuelFromBits (listBoolFromEntropyReal fuel (toEntropyReal p)) = encFuel p := by
  rw [listBoolFromEntropyReal_toEntropyReal_ge p fuel h, encFuelFromBits_encBits]

theorem decodeFuel_eq_encFuel (p : DensePolyReal) (h : encFuel p ≤ decodeReadCap) :
    decodeFuel (toEntropyReal p) = encFuel p := by
  unfold decodeFuel
  exact encFuelFromBits_listBoolFromEntropyReal_ge p decodeReadCap h

theorem decodeFuel_ge_encFuel (p : DensePolyReal) (h : encFuel p ≤ decodeReadCap) :
    encFuel p ≤ decodeFuel (toEntropyReal p) := by
  rw [decodeFuel_eq_encFuel p h]

theorem ofEntropyReal_toEntropyReal (p : DensePolyReal) (h : encFuel p ≤ decodeReadCap) :
    ofEntropyReal (toEntropyReal p) = canonicalize p := by
  unfold ofEntropyReal
  exact ofEntropyRealFuel_ge_toCanonical p decodeReadCap h

theorem toEntropyReal_ofEntropyReal (p : DensePolyReal) (h : encFuel p ≤ decodeReadCap) :
    toEntropyReal (ofEntropyReal (toEntropyReal p)) = toEntropyReal p := by
  rw [ofEntropyReal_toEntropyReal p h, toEntropyReal_canonicalize]

theorem ofEntropyReal_toSelf (p : DensePolyReal) (hc : IsCanonical p)
    (h : encFuel p ≤ decodeReadCap) :
    ofEntropyReal (toEntropyReal p) = p := by
  rw [ofEntropyReal_toEntropyReal p h]
  exact hc.symm

theorem ofEntropyReal_isCanonical (e : EntropyReal)
    (h : ∃ p : DensePolyReal, toEntropyReal p = e ∧ encFuel p ≤ decodeReadCap) :
    IsCanonical (ofEntropyReal e) := by
  obtain ⟨p, hp, hcap⟩ := h
  rw [← hp, ofEntropyReal_toEntropyReal p hcap]
  exact isCanonical_canonicalize p

theorem ofEntropyReal_encFuel_le (e : EntropyReal)
    (h : ∃ p : DensePolyReal, toEntropyReal p = e ∧ encFuel p ≤ decodeReadCap) :
    encFuel (ofEntropyReal e) ≤ decodeReadCap := by
  obtain ⟨p, hp, hcap⟩ := h
  rw [← hp, ofEntropyReal_toEntropyReal p hcap, encFuel, canonicalize, List.length_map]
  exact hcap

def equivEntropyRealInv
    (e : { e : EntropyReal //
      ∃ p : DensePolyReal, toEntropyReal p = e ∧ encFuel p ≤ decodeReadCap }) :
    { p : DensePolyReal // IsCanonical p ∧ encFuel p ≤ decodeReadCap } :=
  ⟨ofEntropyReal e.val, ⟨ofEntropyReal_isCanonical e.val e.property,
    ofEntropyReal_encFuel_le e.val e.property⟩⟩

/-- **The bijection.** Canonical `DensePolyReal ≃ bounded encoding image ⊆ EntropyReal`,
image-subtype shape (matches `PolynomialRat.equivEntropyNat`). Requires
`encFuel p ≤ decodeReadCap` (polynomial length ≤ 32767). -/
def equivEntropyReal :
    { p : DensePolyReal // IsCanonical p ∧ encFuel p ≤ decodeReadCap } ≃
      { e : EntropyReal //
        ∃ p : DensePolyReal, toEntropyReal p = e ∧ encFuel p ≤ decodeReadCap } where
  toFun p := ⟨toEntropyReal p.val, ⟨p.val, rfl, p.property.2⟩⟩
  invFun := equivEntropyRealInv
  left_inv p := by
    apply Subtype.ext
    dsimp [equivEntropyRealInv]
    exact ofEntropyReal_toSelf p.val p.property.left p.property.right
  right_inv e := by
    obtain ⟨p, hp, hcap⟩ := e.property
    apply Subtype.ext
    dsimp [equivEntropyRealInv]
    rw [← hp, toEntropyReal_ofEntropyReal p hcap]

end DensePolyReal

/-! # §2 — Bridge to `EntropyNat` (Translation 6 per-row leg) -/

def densePolyRealToEntropyNat (p : DensePolyReal) : EntropyNat :=
  entropyNatEquivNat.symm (listBoolToNat (DensePolyReal.toCoeffBits p))

def densePolyRealFromEntropyNat (e : EntropyNat) : DensePolyReal :=
  (listBoolFromNat (entropyNatEquivNat e)).map constantEntropyReal

theorem densePolyRealFromEntropyNat_proj_round_trip (p : DensePolyReal) :
    (densePolyRealFromEntropyNat (densePolyRealToEntropyNat p)).map
        evalEntropyRealZero
      = DensePolyReal.toCoeffBits p := by
  unfold densePolyRealFromEntropyNat densePolyRealToEntropyNat
  rw [Equiv.apply_symm_apply, listBoolFromNat_toNat]
  rw [List.map_map]
  show (DensePolyReal.toCoeffBits p).map
        (evalEntropyRealZero ∘ constantEntropyReal) =
       DensePolyReal.toCoeffBits p
  rw [show evalEntropyRealZero ∘ constantEntropyReal = id from
        funext (fun b => evalEntropyRealZero_constant b)]
  exact List.map_id _

/-! # §3 — Capstone -/

example : EntropyReal = Nat_L 1 := rfl
example : Real_L 0 = Nat_L 1 := rfl

end InformationTheory
