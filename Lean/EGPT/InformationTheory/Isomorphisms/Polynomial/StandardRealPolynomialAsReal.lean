-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.

/- StandardRealPolynomialAsReal — every coefficient-list polynomial over Mathlib `ℝ`
*is* a standard real under the canonical encoding, mirroring
`RealPolynomialAsReal.lean`'s constructive `DensePolyReal ≃ EntropyReal` tower.

The chain (non-constructive / standard surface):

```
   StandardDensePolyReal (= List ℝ)
     ↕  entrywise `entropyRealEquivReal.symm` / `.toFun`
   DensePolyReal (= List EntropyReal)
     ↕  `DensePolyReal.equivEntropyReal`  (constructive; `{propext, Quot.sound}`)
   EntropyReal
     ↕  `entropyRealEquivReal`  (`Classical.choice`; Real.lean)
   ℝ
```

`Classical.choice` is isolated to the `EntropyReal ↔ ℝ` boundary exactly as in
`EntropyNumber/Real.lean`. The bit-list encoder and fuel discipline live only
in `RealPolynomialAsReal.lean`.

Closure target: `{propext, Classical.choice, Quot.sound}`. -/

module

public import InformationTheory.Isomorphisms.Polynomial.RealPolynomialAsReal
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

namespace StandardDensePolyReal

/-- A dense real polynomial in standard Mathlib coefficient form. -/
abbrev StandardDensePolyReal : Type := List ℝ

/-- Classical bridge: one Mathlib real ↔ one `EntropyReal` address function. -/
noncomputable def realCoeffEquivEntropyReal : ℝ ≃ EntropyReal :=
  entropyRealEquivReal.symm

/-- Lift a standard coefficient list to the constructive carrier. -/
noncomputable def toConstructive (c : StandardDensePolyReal) : DensePolyReal :=
  c.map realCoeffEquivEntropyReal

/-- Project a constructive coefficient list back to Mathlib reals. -/
noncomputable def fromConstructive (p : DensePolyReal) : StandardDensePolyReal :=
  p.map entropyRealEquivReal

theorem toConstructive_fromConstructive (p : DensePolyReal) :
    toConstructive (fromConstructive p) = p := by
  simp [toConstructive, fromConstructive, List.map_map, realCoeffEquivEntropyReal,
    entropyRealEquivReal.self_trans_symm]

theorem fromConstructive_toConstructive (c : StandardDensePolyReal) :
    fromConstructive (toConstructive c) = c := by
  simp [toConstructive, fromConstructive, List.map_map, realCoeffEquivEntropyReal,
    entropyRealEquivReal.symm_trans_self]

/-- Entrywise round-trip on the coefficient bridge (no encoding-image restriction). -/
noncomputable def listRealEquivDensePolyReal : StandardDensePolyReal ≃ DensePolyReal where
  toFun := toConstructive
  invFun := fromConstructive
  left_inv := fromConstructive_toConstructive
  right_inv := toConstructive_fromConstructive

/-- Canonical form on the standard side: canonical after constructive lift. -/
def IsCanonical (c : StandardDensePolyReal) : Prop :=
  DensePolyReal.IsCanonical (toConstructive c)

/-- Read fuel for the lifted constructive polynomial. -/
noncomputable def encFuel (c : StandardDensePolyReal) : ℕ :=
  DensePolyReal.encFuel (toConstructive c)

/-- Encode a standard coefficient list as a Mathlib real (via the full tower). -/
noncomputable def toReal (c : StandardDensePolyReal) : ℝ :=
  entropyRealEquivReal (DensePolyReal.toEntropyReal (toConstructive c))

/-- Decode a Mathlib real to a standard coefficient list. -/
noncomputable def fromReal (r : ℝ) : StandardDensePolyReal :=
  fromConstructive
    (DensePolyReal.ofEntropyReal (entropyRealEquivReal.symm r))

theorem toReal_spec (c : StandardDensePolyReal) :
    entropyRealEquivReal.symm (toReal c) = DensePolyReal.toEntropyReal (toConstructive c) := by
  unfold toReal
  exact entropyRealEquivReal.symm_apply_apply _

theorem fromReal_toReal (c : StandardDensePolyReal) (hc : IsCanonical c)
    (h : encFuel c ≤ DensePolyReal.decodeReadCap) :
    fromReal (toReal c) = c := by
  unfold fromReal toReal IsCanonical at *
  rw [entropyRealEquivReal.symm_apply_apply]
  rw [DensePolyReal.ofEntropyReal_toSelf (toConstructive c) hc h]
  exact fromConstructive_toConstructive c

theorem toReal_fromReal (c : StandardDensePolyReal) (h : encFuel c ≤ DensePolyReal.decodeReadCap) :
    toReal (fromReal (toReal c)) = toReal c := by
  unfold fromReal toReal
  rw [entropyRealEquivReal.symm_apply_apply, toConstructive_fromConstructive,
      DensePolyReal.toEntropyReal_ofEntropyReal (toConstructive c) h]

theorem fromReal_isCanonical (r : ℝ)
    (h : ∃ c : StandardDensePolyReal, toReal c = r ∧ encFuel c ≤ DensePolyReal.decodeReadCap) :
    IsCanonical (fromReal r) := by
  obtain ⟨c, hc, hcap⟩ := h
  rw [show r = toReal c from hc.symm]
  dsimp [IsCanonical, fromReal]
  rw [toReal_spec c, toConstructive_fromConstructive,
      DensePolyReal.ofEntropyReal_toEntropyReal (toConstructive c) hcap]
  exact DensePolyReal.isCanonical_canonicalize (toConstructive c)

theorem fromReal_encFuel_le (r : ℝ)
    (h : ∃ c : StandardDensePolyReal, toReal c = r ∧ encFuel c ≤ DensePolyReal.decodeReadCap) :
    encFuel (fromReal r) ≤ DensePolyReal.decodeReadCap := by
  obtain ⟨c, hc, hcap⟩ := h
  rw [show r = toReal c from hc.symm]
  dsimp [encFuel, fromReal]
  rw [toReal_spec c, toConstructive_fromConstructive,
      DensePolyReal.ofEntropyReal_toEntropyReal (toConstructive c) hcap,
      DensePolyReal.encFuel, DensePolyReal.canonicalize, List.length_map]
  exact hcap

noncomputable def equivRealInv
    (r : { r : ℝ //
      ∃ c : StandardDensePolyReal, toReal c = r ∧ encFuel c ≤ DensePolyReal.decodeReadCap }) :
    { c : StandardDensePolyReal //
      IsCanonical c ∧ encFuel c ≤ DensePolyReal.decodeReadCap } :=
  ⟨fromReal r.val, ⟨fromReal_isCanonical r.val r.property,
    fromReal_encFuel_le r.val r.property⟩⟩

/-- **The standard bijection.** Canonical `List ℝ ≃ bounded encoding image ⊆ ℝ`.
Composes the row-wise coefficient bridge, `DensePolyReal.equivEntropyReal`, and
`entropyRealEquivReal`. Requires `encFuel c ≤ decodeReadCap`. -/
noncomputable def equivReal :
    { c : StandardDensePolyReal //
      IsCanonical c ∧ encFuel c ≤ DensePolyReal.decodeReadCap } ≃
      { r : ℝ //
        ∃ c : StandardDensePolyReal, toReal c = r ∧ encFuel c ≤ DensePolyReal.decodeReadCap } where
  toFun c := ⟨toReal c.val, ⟨c.val, rfl, c.property.right⟩⟩
  invFun := equivRealInv
  left_inv c := by
    apply Subtype.ext
    dsimp [equivRealInv]
    exact fromReal_toReal c.val c.property.left c.property.right
  right_inv r := by
    obtain ⟨c, hc, hcap⟩ := r.property
    apply Subtype.ext
    dsimp [equivRealInv]
    rw [← hc, toReal_fromReal c hcap]

end StandardDensePolyReal

end InformationTheory
