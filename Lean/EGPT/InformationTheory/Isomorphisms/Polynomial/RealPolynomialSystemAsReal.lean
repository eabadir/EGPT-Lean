-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.

/- RealPolynomialSystemAsReal — every real polynomial *system* (a finite list of
`DensePolyReal`) *is* an `EntropyReal` under the canonical address-bit encoding,
mirroring `PolynomialSystemAsNat.lean`.

Closure target: `{propext, Quot.sound}`. -/

module

public import InformationTheory.Isomorphisms.Polynomial.RealPolynomialAsReal
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

namespace DensePolyReal

theorem encBits_canonicalize (p : DensePolyReal) :
    encBits (canonicalize p) = encBits p := by
  unfold encBits canonicalize toCoeffBits
  congr 1
  · simp [List.length_map]
  · apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp [List.getElem_map, evalEntropyRealZero_constant]

end DensePolyReal

def canonicalizeList (P : List DensePolyReal) : List DensePolyReal :=
  P.map DensePolyReal.canonicalize

def densePolyRealListToList : List DensePolyReal → List Bool
  | []      => [false]
  | p :: ps =>
      [true] ++ DensePolyReal.encBits p ++ densePolyRealListToList ps

def densePolyRealListParse : ℕ → List Bool → List DensePolyReal
  | 0,        _ => []
  | fuel + 1, l =>
      match l with
      | []         => []
      | false :: _ => []
      | true :: rest =>
          let (len, after) := unaryLenDecode rest
          let p := (after.take len).map constantEntropyReal
          let after_body := List.drop len after
          p :: densePolyRealListParse fuel after_body

def densePolyRealListFromList (l : List Bool) : List DensePolyReal :=
  densePolyRealListParse (l.length + 1) l

def densePolyRealListEncFuel (P : List DensePolyReal) : ℕ :=
  (densePolyRealListToList P).length

private theorem decodeEncBits_suffix (p : DensePolyReal) (tail : List Bool) :
    let rest := DensePolyReal.encBits p ++ tail
    let (len, after) := unaryLenDecode rest
    (List.take len after).map constantEntropyReal = DensePolyReal.canonicalize p ∧
    List.drop len after = tail := by
  simp [DensePolyReal.encBits, DensePolyReal.toCoeffBits, DensePolyReal.canonicalize,
    unaryLenDecode_unaryLen, List.take_left, List.drop_left, List.map_map]

theorem densePolyRealListParse_toList (P : List DensePolyReal) :
    ∀ fuel, P.length < fuel →
      densePolyRealListParse fuel (densePolyRealListToList P) = canonicalizeList P := by
  induction P with
  | nil =>
    intro fuel h_fuel
    cases fuel with
    | zero => exact absurd h_fuel (Nat.not_lt_zero _)
    | succ f => rfl
  | cons p ps ih =>
    intro fuel h_fuel
    cases fuel with
    | zero => exact absurd h_fuel (Nat.not_lt_zero _)
    | succ f =>
      simp only [densePolyRealListParse, densePolyRealListToList, canonicalizeList]
      obtain ⟨hp, htail⟩ := decodeEncBits_suffix p (densePolyRealListToList ps)
      have h_len : (p :: ps).length = ps.length + 1 := List.length_cons
      have h_ps : ps.length < f := by
        rw [h_len] at h_fuel
        exact Nat.lt_of_succ_lt_succ h_fuel
      simp [hp, htail, ih f h_ps, canonicalizeList]

theorem length_le_densePolyRealListToList (P : List DensePolyReal) :
    P.length ≤ (densePolyRealListToList P).length := by
  induction P with
  | nil => decide
  | cons p ps ih =>
    simp [densePolyRealListToList, List.length_append]
    omega

theorem densePolyRealListFromList_toList (P : List DensePolyReal) :
    densePolyRealListFromList (densePolyRealListToList P) = canonicalizeList P := by
  unfold densePolyRealListFromList
  apply densePolyRealListParse_toList P ((densePolyRealListToList P).length + 1)
  have := length_le_densePolyRealListToList P
  omega

theorem densePolyRealListToList_canonicalizeList (P : List DensePolyReal) :
    densePolyRealListToList (canonicalizeList P) = densePolyRealListToList P := by
  induction P with
  | nil => rfl
  | cons p ps ih =>
    simp [canonicalizeList, densePolyRealListToList, DensePolyReal.encBits_canonicalize]
    exact ih

theorem densePolyRealListToList_cons (p : DensePolyReal) (rest : List DensePolyReal) :
    densePolyRealListToList (p :: rest)
      = densePolyRealListToList (DensePolyReal.canonicalize p :: canonicalizeList rest) := by
  simp [densePolyRealListToList, canonicalizeList, DensePolyReal.encBits_canonicalize]
  exact (densePolyRealListToList_canonicalizeList rest).symm

theorem densePolyRealListToList_append (P Q : List DensePolyReal) :
    densePolyRealListToList (P ++ Q)
      = densePolyRealListToList (canonicalizeList P ++ canonicalizeList Q) := by
  induction P with
  | nil =>
    simp [canonicalizeList, densePolyRealListToList]
    exact (densePolyRealListToList_canonicalizeList Q).symm
  | cons p ps ih =>
    simp [canonicalizeList, densePolyRealListToList, List.append_assoc,
      DensePolyReal.encBits_canonicalize, ih]

/-! # §2 — `EntropyReal` landing -/

def densePolyRealListToEntropyReal (P : List DensePolyReal) : EntropyReal :=
  listBoolToEntropyReal (densePolyRealListToList P)

def densePolyRealListFromEntropyRealFuel (fuel : ℕ) (r : EntropyReal) :
    List DensePolyReal :=
  densePolyRealListFromList (listBoolFromEntropyReal fuel r)

theorem listBoolFromEntropyReal_densePolyRealListToList (P : List DensePolyReal) :
    listBoolFromEntropyReal (densePolyRealListEncFuel P)
      (densePolyRealListToEntropyReal P)
      = densePolyRealListToList P := by
  unfold densePolyRealListEncFuel densePolyRealListToEntropyReal
  exact listBoolFromEntropyReal_toReal (densePolyRealListToList P)

theorem densePolyRealListFromEntropyRealFuel_toList (P : List DensePolyReal) :
    densePolyRealListFromEntropyRealFuel (densePolyRealListEncFuel P)
      (densePolyRealListToEntropyReal P)
      = canonicalizeList P := by
  unfold densePolyRealListFromEntropyRealFuel
  rw [listBoolFromEntropyReal_densePolyRealListToList]
  exact densePolyRealListFromList_toList P

def densePolyRealListDecodeReadCap : ℕ := DensePolyReal.decodeReadCap

def densePolyRealListFromEntropyReal (r : EntropyReal) : List DensePolyReal :=
  densePolyRealListFromEntropyRealFuel densePolyRealListDecodeReadCap r

theorem listBoolFromEntropyReal_densePolyRealListToList_ge (P : List DensePolyReal) (fuel : ℕ)
    (h : densePolyRealListEncFuel P ≤ fuel) :
    listBoolFromEntropyReal fuel (densePolyRealListToEntropyReal P)
      = densePolyRealListToList P ++ List.replicate (fuel - densePolyRealListEncFuel P) false := by
  set k := fuel - densePolyRealListEncFuel P
  have hk : densePolyRealListEncFuel P + k = fuel := Nat.add_sub_of_le h
  have hlen :
      (densePolyRealListToList P ++ List.replicate k false).length = fuel := by
    simp only [List.length_append, List.length_replicate, densePolyRealListEncFuel]
    exact hk
  unfold densePolyRealListToEntropyReal
  calc
    listBoolFromEntropyReal fuel (listBoolToEntropyReal (densePolyRealListToList P))
        = listBoolFromEntropyReal fuel
            (listBoolToEntropyReal (densePolyRealListToList P ++ List.replicate k false)) := by
          rw [listBoolToEntropyReal_append_false (densePolyRealListToList P) k]
    _ = densePolyRealListToList P ++ List.replicate k false := by
          rw [← hlen]
          exact listBoolFromEntropyReal_toReal _

private theorem densePolyRealListParse_suffix (P : List DensePolyReal) (k : ℕ) (fuel : ℕ)
    (hf : P.length < fuel) :
    densePolyRealListParse (fuel + k)
      (densePolyRealListToList P ++ List.replicate k false)
      = densePolyRealListParse fuel (densePolyRealListToList P) := by
  induction P generalizing fuel k with
  | nil =>
    cases fuel with
    | zero => exact absurd hf (Nat.not_lt_zero _)
    | succ fuel =>
      cases k with
      | zero => simp [densePolyRealListToList, densePolyRealListParse]
      | succ k => simp [densePolyRealListToList, densePolyRealListParse, List.replicate]
  | cons p ps ih =>
    cases fuel with
    | zero => exact absurd hf (Nat.not_lt_zero _)
    | succ fuel =>
      have h_ps : ps.length < fuel := by
        rw [List.length_cons] at hf
        exact Nat.lt_of_succ_lt_succ hf
      have h_lhs :
          densePolyRealListParse (fuel + 1 + k)
              ([true] ++ DensePolyReal.encBits p ++ densePolyRealListToList ps ++
                List.replicate k false)
            = DensePolyReal.canonicalize p ::
                densePolyRealListParse (fuel + k)
                  (densePolyRealListToList ps ++ List.replicate k false) := by
        have hfuel' : fuel + 1 + k = Nat.succ (fuel + k) := by omega
        rw [hfuel']
        dsimp [densePolyRealListParse]
        simp only [List.append_assoc]
        obtain ⟨hp, htail⟩ :=
          decodeEncBits_suffix p (densePolyRealListToList ps ++ List.replicate k false)
        rw [hp, htail]
      have h_rhs :
          densePolyRealListParse (fuel + 1)
              ([true] ++ DensePolyReal.encBits p ++ densePolyRealListToList ps)
            = DensePolyReal.canonicalize p ::
                densePolyRealListParse fuel (densePolyRealListToList ps) := by
        dsimp [densePolyRealListParse]
        obtain ⟨hp, htail⟩ := decodeEncBits_suffix p (densePolyRealListToList ps)
        rw [hp, htail]
      have htol :
          densePolyRealListToList (p :: ps) ++ List.replicate k false
            = [true] ++ DensePolyReal.encBits p ++ densePolyRealListToList ps ++
                List.replicate k false := by
        simp [densePolyRealListToList, List.append_assoc]
      rw [htol, h_lhs, ih k fuel h_ps]
      simpa [densePolyRealListToList, List.append_assoc] using h_rhs.symm

theorem densePolyRealListFromList_suffix (P : List DensePolyReal) (k : ℕ) :
    densePolyRealListFromList (densePolyRealListToList P ++ List.replicate k false)
      = densePolyRealListFromList (densePolyRealListToList P) := by
  unfold densePolyRealListFromList
  rw [List.length_append, List.length_replicate]
  have hfuel :
      (densePolyRealListToList P).length + k + 1
        = (densePolyRealListToList P).length + 1 + k := by
    omega
  rw [hfuel]
  exact densePolyRealListParse_suffix P k ((densePolyRealListToList P).length + 1)
    (Nat.lt_succ_of_le (length_le_densePolyRealListToList P))

theorem densePolyRealListFromEntropyRealFuel_ge_toList (P : List DensePolyReal) (fuel : ℕ)
    (h : densePolyRealListEncFuel P ≤ fuel) :
    densePolyRealListFromEntropyRealFuel fuel (densePolyRealListToEntropyReal P)
      = canonicalizeList P := by
  unfold densePolyRealListFromEntropyRealFuel
  rw [listBoolFromEntropyReal_densePolyRealListToList_ge P fuel h,
      densePolyRealListFromList_suffix P (fuel - densePolyRealListEncFuel P),
      densePolyRealListFromList_toList]

theorem densePolyRealListFromEntropyReal_toCanonicalList (P : List DensePolyReal)
    (h : densePolyRealListEncFuel P ≤ densePolyRealListDecodeReadCap) :
    densePolyRealListFromEntropyReal (densePolyRealListToEntropyReal P) = canonicalizeList P := by
  unfold densePolyRealListFromEntropyReal
  exact densePolyRealListFromEntropyRealFuel_ge_toList P densePolyRealListDecodeReadCap h

theorem toEntropyReal_canonicalizeList (P : List DensePolyReal) :
    densePolyRealListToEntropyReal (canonicalizeList P)
      = densePolyRealListToEntropyReal P := by
  unfold densePolyRealListToEntropyReal
  rw [densePolyRealListToList_canonicalizeList]

theorem densePolyRealListToEntropyReal_ofFuel (P : List DensePolyReal) :
    densePolyRealListToEntropyReal
      (densePolyRealListFromEntropyRealFuel (densePolyRealListEncFuel P)
        (densePolyRealListToEntropyReal P))
      = densePolyRealListToEntropyReal P := by
  rw [densePolyRealListFromEntropyRealFuel_toList, toEntropyReal_canonicalizeList]

/-! # §3 — Lifted list ops (fuel-parameterised decode, image transport) -/

def appendEntropyRealAtFuel (fuelE fuelF : ℕ) (e f : EntropyReal) : EntropyReal :=
  densePolyRealListToEntropyReal
    (densePolyRealListFromEntropyRealFuel fuelE e ++
      densePolyRealListFromEntropyRealFuel fuelF f)

def consEntropyRealAtFuel (polyFuel listFuel : ℕ) (pEnc restEnc : EntropyReal) :
    EntropyReal :=
  densePolyRealListToEntropyReal
    (DensePolyReal.ofEntropyRealFuel polyFuel pEnc ::
      densePolyRealListFromEntropyRealFuel listFuel restEnc)

theorem densePolyRealListToEntropyReal_append (P Q : List DensePolyReal) :
    densePolyRealListToEntropyReal (P ++ Q)
      = densePolyRealListToEntropyReal (canonicalizeList P ++ canonicalizeList Q) := by
  unfold densePolyRealListToEntropyReal
  rw [densePolyRealListToList_append]

theorem densePolyRealListToEntropyReal_cons (p : DensePolyReal) (rest : List DensePolyReal) :
    densePolyRealListToEntropyReal (p :: rest)
      = densePolyRealListToEntropyReal (DensePolyReal.canonicalize p :: canonicalizeList rest) := by
  unfold densePolyRealListToEntropyReal
  rw [densePolyRealListToList_cons]

theorem append_eq_appendEntropyRealAtFuel (P Q : List DensePolyReal) :
    densePolyRealListToEntropyReal (P ++ Q)
      = appendEntropyRealAtFuel
          (densePolyRealListEncFuel P) (densePolyRealListEncFuel Q)
          (densePolyRealListToEntropyReal P) (densePolyRealListToEntropyReal Q) := by
  rw [densePolyRealListToEntropyReal_append]
  unfold appendEntropyRealAtFuel
  rw [densePolyRealListFromEntropyRealFuel_toList P,
      densePolyRealListFromEntropyRealFuel_toList Q]

theorem cons_eq_consEntropyRealAtFuel (p : DensePolyReal) (rest : List DensePolyReal) :
    densePolyRealListToEntropyReal (p :: rest)
      = consEntropyRealAtFuel
          (DensePolyReal.encFuel p) (densePolyRealListEncFuel rest)
          (DensePolyReal.toEntropyReal p) (densePolyRealListToEntropyReal rest) := by
  rw [densePolyRealListToEntropyReal_cons]
  unfold consEntropyRealAtFuel
  rw [DensePolyReal.ofEntropyRealFuel_toCanonical,
      densePolyRealListFromEntropyRealFuel_toList rest]

end InformationTheory
