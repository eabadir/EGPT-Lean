-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.

/- RealMatrixAsReal — every real-coefficient matrix (`List DensePolyReal`) *is* an
`EntropyReal` under the canonical address-bit encoding, mirroring
`PolynomialMatrixAsNat.lean`'s landing of `List DensePolyRat ≃ EntropyNat`.

Composes `RealPolynomialSystemAsReal` (system-level list encoder) with the
matrix-as-row-list identification from Translation 6.

Closure target: `{propext, Quot.sound}`. -/

module

public import InformationTheory.Isomorphisms.Polynomial.RealPolynomialSystemAsReal
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

namespace Translation6RealMatrix

/-- A matrix with `EntropyReal` coefficient rows. -/
abbrev RealMatrix : Type := List DensePolyReal

/-- A real-coefficient matrix as an `EntropyReal`. -/
def realMatrixToEntropyReal (M : RealMatrix) : EntropyReal :=
  densePolyRealListToEntropyReal M

def realMatrixEncFuel (M : RealMatrix) : ℕ :=
  densePolyRealListEncFuel M

def realMatrixFromEntropyRealFuel (fuel : ℕ) (r : EntropyReal) : RealMatrix :=
  densePolyRealListFromEntropyRealFuel fuel r

def realMatrixFromEntropyReal (r : EntropyReal) : RealMatrix :=
  densePolyRealListFromEntropyReal r

theorem realMatrixFromEntropyRealFuel_toCanonicalList (M : RealMatrix) :
    realMatrixFromEntropyRealFuel (realMatrixEncFuel M) (realMatrixToEntropyReal M)
      = canonicalizeList M := by
  unfold realMatrixFromEntropyRealFuel realMatrixToEntropyReal realMatrixEncFuel
  exact densePolyRealListFromEntropyRealFuel_toList M

theorem realMatrixFromEntropyRealFuel_ge_toCanonicalList (M : RealMatrix) (fuel : ℕ)
    (h : realMatrixEncFuel M ≤ fuel) :
    realMatrixFromEntropyRealFuel fuel (realMatrixToEntropyReal M) = canonicalizeList M := by
  simp only [realMatrixFromEntropyRealFuel, realMatrixToEntropyReal, realMatrixEncFuel]
  exact densePolyRealListFromEntropyRealFuel_ge_toList M fuel h

theorem realMatrixFromEntropyReal_toCanonicalList (M : RealMatrix)
    (h : realMatrixEncFuel M ≤ densePolyRealListDecodeReadCap) :
    realMatrixFromEntropyReal (realMatrixToEntropyReal M) = canonicalizeList M := by
  simp only [realMatrixFromEntropyReal]
  exact densePolyRealListFromEntropyReal_toCanonicalList M h

private theorem canonicalizeList_idem (P : List DensePolyReal) :
    canonicalizeList (canonicalizeList P) = canonicalizeList P := by
  unfold canonicalizeList
  simp [List.map_map, DensePolyReal.canonicalize_canonicalize]

def IsCanonical (M : RealMatrix) : Prop :=
  canonicalizeList M = M

theorem isCanonical_canonicalizeList (M : RealMatrix) :
    IsCanonical (canonicalizeList M) := by
  unfold IsCanonical
  exact canonicalizeList_idem M

theorem realMatrixFromEntropyReal_toSelf (M : RealMatrix) (hc : IsCanonical M)
    (h : realMatrixEncFuel M ≤ densePolyRealListDecodeReadCap) :
    realMatrixFromEntropyReal (realMatrixToEntropyReal M) = M := by
  rw [realMatrixFromEntropyReal_toCanonicalList M h, hc]

theorem realMatrixFromEntropyReal_isCanonical (r : EntropyReal)
    (h : ∃ M : RealMatrix, realMatrixToEntropyReal M = r ∧
      realMatrixEncFuel M ≤ densePolyRealListDecodeReadCap) :
    IsCanonical (realMatrixFromEntropyReal r) := by
  obtain ⟨M, hm, hcap⟩ := h
  rw [← hm, realMatrixFromEntropyReal_toCanonicalList M hcap]
  exact isCanonical_canonicalizeList M

theorem realMatrixFromEntropyReal_encFuel_le (r : EntropyReal)
    (h : ∃ M : RealMatrix, realMatrixToEntropyReal M = r ∧
      realMatrixEncFuel M ≤ densePolyRealListDecodeReadCap) :
    realMatrixEncFuel (realMatrixFromEntropyReal r) ≤ densePolyRealListDecodeReadCap := by
  obtain ⟨M, hm, hcap⟩ := h
  rw [← hm, realMatrixFromEntropyReal_toCanonicalList M hcap]
  simp only [realMatrixEncFuel, densePolyRealListEncFuel, densePolyRealListToList_canonicalizeList]
  exact hcap

theorem realMatrixFromEntropyReal_eq_fromFuel (M : RealMatrix)
    (h : realMatrixEncFuel M ≤ densePolyRealListDecodeReadCap) :
    realMatrixFromEntropyReal (realMatrixToEntropyReal M)
      = realMatrixFromEntropyRealFuel (realMatrixEncFuel M) (realMatrixToEntropyReal M) := by
  simp only [realMatrixFromEntropyReal, realMatrixFromEntropyRealFuel, realMatrixToEntropyReal,
    realMatrixEncFuel]
  rw [densePolyRealListFromEntropyReal_toCanonicalList M h,
      ← densePolyRealListFromEntropyRealFuel_toList M]

theorem realMatrixToEntropyReal_ofFuel (M : RealMatrix) :
    realMatrixToEntropyReal
      (realMatrixFromEntropyRealFuel (realMatrixEncFuel M) (realMatrixToEntropyReal M))
      = realMatrixToEntropyReal M := by
  unfold realMatrixToEntropyReal realMatrixFromEntropyRealFuel realMatrixEncFuel
  exact densePolyRealListToEntropyReal_ofFuel M

def equivEntropyRealInv
    (e : { e : EntropyReal //
      ∃ M : RealMatrix, realMatrixToEntropyReal M = e ∧
        realMatrixEncFuel M ≤ densePolyRealListDecodeReadCap }) :
    { M : RealMatrix // IsCanonical M ∧
      realMatrixEncFuel M ≤ densePolyRealListDecodeReadCap } :=
  ⟨realMatrixFromEntropyReal e.val, ⟨realMatrixFromEntropyReal_isCanonical e.val e.property,
    realMatrixFromEntropyReal_encFuel_le e.val e.property⟩⟩

/-- **The bijection.** Canonical `RealMatrix ≃ bounded encoding image ⊆ EntropyReal`. -/
def equivEntropyReal :
    { M : RealMatrix // IsCanonical M ∧
      realMatrixEncFuel M ≤ densePolyRealListDecodeReadCap } ≃
      { e : EntropyReal //
        ∃ M : RealMatrix, realMatrixToEntropyReal M = e ∧
          realMatrixEncFuel M ≤ densePolyRealListDecodeReadCap } where
  toFun M := ⟨realMatrixToEntropyReal M.val, ⟨M.val, rfl, M.property.right⟩⟩
  invFun := equivEntropyRealInv
  left_inv M := by
    apply Subtype.ext
    dsimp [equivEntropyRealInv]
    exact realMatrixFromEntropyReal_toSelf M.val M.property.left M.property.right
  right_inv e := by
    obtain ⟨M, hm, hcap⟩ := e.property
    apply Subtype.ext
    dsimp [equivEntropyRealInv]
    rw [← hm, realMatrixFromEntropyReal_eq_fromFuel M hcap, realMatrixToEntropyReal_ofFuel M]

end Translation6RealMatrix

end InformationTheory
