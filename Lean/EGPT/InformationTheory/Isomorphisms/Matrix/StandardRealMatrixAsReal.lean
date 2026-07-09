-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.

/- StandardRealMatrixAsReal — every real-coefficient matrix in standard Mathlib form
*is* a standard real under the canonical encoding, mirroring
`RealMatrixAsReal.lean`'s constructive `List DensePolyReal ≃ EntropyReal` tower and
`StandardRealPolynomialAsReal.lean`'s per-row coefficient bridge.

The chain (non-constructive / standard surface):

```
   StandardRealMatrix (= List (List ℝ))
     ↕  row-wise `StandardDensePolyReal.listRealEquivDensePolyReal`
   RealMatrix (= List DensePolyReal)
     ↕  `Translation6RealMatrix.realMatrixToEntropyReal`  (constructive)
   EntropyReal
     ↕  `entropyRealEquivReal`  (`Classical.choice`)
   ℝ
```

Bundled `equivReal` composes the row-wise coefficient bridge, `Translation6RealMatrix.equivEntropyReal`,
and `entropyRealEquivReal`. Round-trip at `decodeReadCap` uses
`realMatrixFromEntropyReal_toCanonicalList`.

Closure target: `{propext, Classical.choice, Quot.sound}`. -/

module

public import InformationTheory.Isomorphisms.Polynomial.StandardRealPolynomialAsReal
public import InformationTheory.Isomorphisms.Matrix.RealMatrixAsReal
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

set_option linter.dupNamespace false
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

namespace StandardRealMatrix

open StandardDensePolyReal
open Translation6RealMatrix

private theorem realMatrixEncFuel_canonicalizeList (M : RealMatrix) :
    realMatrixEncFuel (canonicalizeList M) = realMatrixEncFuel M := by
  unfold realMatrixEncFuel densePolyRealListEncFuel
  rw [densePolyRealListToList_canonicalizeList]

private theorem canonicalizeList_idem (P : List DensePolyReal) :
    canonicalizeList (canonicalizeList P) = canonicalizeList P := by
  unfold canonicalizeList
  simp [List.map_map, DensePolyReal.canonicalize_canonicalize]

/-- A matrix with standard Mathlib real coefficient rows. -/
abbrev StandardRealMatrix : Type := List (List ℝ)

/-- Lift a standard matrix to the constructive carrier row-wise. -/
noncomputable def toRealMatrix (M : StandardRealMatrix) : RealMatrix :=
  M.map toConstructive

/-- Project a constructive matrix back to standard Mathlib form row-wise. -/
noncomputable def fromRealMatrix (M : RealMatrix) : StandardRealMatrix :=
  M.map fromConstructive

theorem toRealMatrix_fromRealMatrix (p : RealMatrix) :
    toRealMatrix (fromRealMatrix p) = p := by
  simp only [toRealMatrix, fromRealMatrix, List.map_map, Function.comp]
  refine List.ext_getElem (by simp [List.length_map]) (fun i hi _ => ?_)
  simp [List.getElem_map]
  exact toConstructive_fromConstructive (p[i])

theorem fromRealMatrix_toRealMatrix (M : StandardRealMatrix) :
    fromRealMatrix (toRealMatrix M) = M := by
  simp only [toRealMatrix, fromRealMatrix, List.map_map, Function.comp]
  refine List.ext_getElem (by simp [List.length_map]) (fun i hi _ => ?_)
  simp [List.getElem_map]
  exact fromConstructive_toConstructive (M[i])

/-- Row-wise round-trip on the coefficient bridge. -/
noncomputable def listRealMatrixEquivRealMatrix : StandardRealMatrix ≃ RealMatrix where
  toFun := toRealMatrix
  invFun := fromRealMatrix
  left_inv := fromRealMatrix_toRealMatrix
  right_inv := toRealMatrix_fromRealMatrix

/-- Canonical form on the standard side: canonical after constructive lift. -/
def IsCanonical (M : StandardRealMatrix) : Prop :=
  toRealMatrix M = canonicalizeList (toRealMatrix M)

noncomputable def encFuel (M : StandardRealMatrix) : ℕ :=
  realMatrixEncFuel (toRealMatrix M)

noncomputable def toReal (M : StandardRealMatrix) : ℝ :=
  entropyRealEquivReal (realMatrixToEntropyReal (toRealMatrix M))

/-- Decode at the supplied read fuel (use `encFuel M` on the encoding image). -/
noncomputable def fromRealAtFuel (fuel : ℕ) (r : ℝ) : StandardRealMatrix :=
  fromRealMatrix
    (realMatrixFromEntropyRealFuel fuel (entropyRealEquivReal.symm r))

/-- Top-level decoder at `decodeReadCap` (mirrors `StandardDensePolyReal.fromReal`).
Exact round-trip on the image currently uses `fromRealAtFuel (encFuel M)`. -/
noncomputable def fromReal (r : ℝ) : StandardRealMatrix :=
  fromRealAtFuel DensePolyReal.decodeReadCap r

theorem toReal_spec (M : StandardRealMatrix) :
    entropyRealEquivReal.symm (toReal M) = realMatrixToEntropyReal (toRealMatrix M) := by
  unfold toReal
  exact entropyRealEquivReal.symm_apply_apply _

theorem fromRealAtFuel_toReal (M : StandardRealMatrix) (hc : IsCanonical M) :
    fromRealAtFuel (encFuel M) (toReal M) = M := by
  unfold fromRealAtFuel toReal IsCanonical encFuel at *
  rw [entropyRealEquivReal.symm_apply_apply,
      realMatrixFromEntropyRealFuel_toCanonicalList (toRealMatrix M),
      show canonicalizeList (toRealMatrix M) = toRealMatrix M from hc.symm]
  exact fromRealMatrix_toRealMatrix M

theorem fromReal_toReal (M : StandardRealMatrix) (hc : IsCanonical M)
    (hcap : encFuel M ≤ DensePolyReal.decodeReadCap) :
    fromReal (toReal M) = M := by
  unfold fromReal fromRealAtFuel toReal encFuel at *
  rw [entropyRealEquivReal.symm_apply_apply,
      realMatrixFromEntropyRealFuel_ge_toCanonicalList (toRealMatrix M)
        DensePolyReal.decodeReadCap hcap,
      ← hc]
  exact fromRealMatrix_toRealMatrix M

theorem toReal_fromRealAtFuel (M : StandardRealMatrix) :
    toReal (fromRealAtFuel (encFuel M) (toReal M)) = toReal M := by
  unfold fromRealAtFuel toReal encFuel
  rw [entropyRealEquivReal.symm_apply_apply, toRealMatrix_fromRealMatrix,
      realMatrixToEntropyReal_ofFuel (toRealMatrix M)]

theorem fromRealAtFuel_isCanonical (M : StandardRealMatrix) :
    IsCanonical (fromRealAtFuel (encFuel M) (toReal M)) := by
  dsimp [IsCanonical, fromRealAtFuel, encFuel]
  rw [toReal_spec M, realMatrixFromEntropyRealFuel_toCanonicalList (toRealMatrix M),
      toRealMatrix_fromRealMatrix, canonicalizeList_idem]

theorem fromRealAtFuel_encFuel_le (M : StandardRealMatrix)
    (hcap : encFuel M ≤ DensePolyReal.decodeReadCap) :
    encFuel (fromRealAtFuel (encFuel M) (toReal M)) ≤ DensePolyReal.decodeReadCap := by
  dsimp [encFuel, fromRealAtFuel]
  rw [toReal_spec M, realMatrixFromEntropyRealFuel_toCanonicalList (toRealMatrix M),
      toRealMatrix_fromRealMatrix, realMatrixEncFuel_canonicalizeList]
  exact hcap

theorem toReal_fromReal (M : StandardRealMatrix) (hcap : encFuel M ≤ DensePolyReal.decodeReadCap) :
    toReal (fromReal (toReal M)) = toReal M := by
  unfold toReal fromReal fromRealAtFuel
  rw [entropyRealEquivReal.symm_apply_apply, toRealMatrix_fromRealMatrix,
      realMatrixFromEntropyRealFuel_ge_toCanonicalList (toRealMatrix M)
        DensePolyReal.decodeReadCap hcap]
  simp only [realMatrixToEntropyReal]
  rw [toEntropyReal_canonicalizeList (toRealMatrix M)]

theorem fromReal_isCanonical (r : ℝ)
    (h : ∃ M : StandardRealMatrix, toReal M = r ∧
      encFuel M ≤ DensePolyReal.decodeReadCap) :
    IsCanonical (fromReal r) := by
  obtain ⟨M, hm, hcap⟩ := h
  rw [show r = toReal M from hm.symm]
  dsimp [IsCanonical, fromReal, fromRealAtFuel]
  rw [toReal_spec M,
      realMatrixFromEntropyRealFuel_ge_toCanonicalList (toRealMatrix M)
        DensePolyReal.decodeReadCap hcap,
      toRealMatrix_fromRealMatrix, canonicalizeList_idem (toRealMatrix M)]

theorem fromReal_encFuel_le (r : ℝ)
    (h : ∃ M : StandardRealMatrix, toReal M = r ∧
      encFuel M ≤ DensePolyReal.decodeReadCap) :
    encFuel (fromReal r) ≤ DensePolyReal.decodeReadCap := by
  obtain ⟨M, hm, hcap⟩ := h
  rw [show r = toReal M from hm.symm]
  dsimp [encFuel, fromReal, fromRealAtFuel]
  rw [toReal_spec M,
      realMatrixFromEntropyRealFuel_ge_toCanonicalList (toRealMatrix M)
        DensePolyReal.decodeReadCap hcap,
      toRealMatrix_fromRealMatrix, realMatrixEncFuel_canonicalizeList]
  exact hcap

noncomputable def equivRealInv
    (r : { r : ℝ //
      ∃ M : StandardRealMatrix, toReal M = r ∧
        encFuel M ≤ DensePolyReal.decodeReadCap }) :
    { M : StandardRealMatrix //
      IsCanonical M ∧ encFuel M ≤ DensePolyReal.decodeReadCap } :=
  ⟨fromReal r.val, ⟨fromReal_isCanonical r.val r.property,
    fromReal_encFuel_le r.val r.property⟩⟩

/-- **The standard bijection.** Canonical `List (List ℝ) ≃ bounded encoding image ⊆ ℝ`. -/
noncomputable def equivReal :
    { M : StandardRealMatrix //
      IsCanonical M ∧ encFuel M ≤ DensePolyReal.decodeReadCap } ≃
      { r : ℝ //
        ∃ M : StandardRealMatrix, toReal M = r ∧
          encFuel M ≤ DensePolyReal.decodeReadCap } where
  toFun M := ⟨toReal M.val, ⟨M.val, rfl, M.property.right⟩⟩
  invFun := equivRealInv
  left_inv M := by
    apply Subtype.ext
    dsimp [equivRealInv]
    exact fromReal_toReal M.val M.property.left M.property.right
  right_inv r := by
    obtain ⟨M, hm, hcap⟩ := r.property
    apply Subtype.ext
    dsimp [equivRealInv]
    rw [← hm, toReal_fromReal M hcap]

end StandardRealMatrix

end InformationTheory
