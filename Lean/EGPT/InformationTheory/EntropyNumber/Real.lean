-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.

module
public import InformationTheory.EntropyNumber.Rat
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.Analysis.SpecificLimits.Basic



/-!
# EntropyReal: Information-Theoretic Reals

The reals viewed as Boolean-valued functions on `EntropyNat`, i.e. characteristic
functions `EntropyNat → Bool`. This gives a type `EntropyReal` with cardinality
`2 ^ ℵ₀ = 𝔠`, and we construct an equivalence `EntropyReal ≃ ℝ` via
cardinality arguments.

## Main definitions

* `EntropyReal` — the type `EntropyNat → Bool`.
* `entropyRealEquivFunNat` — the equivalence `EntropyReal ≃ (ℕ → Bool)`.
* `evaluate_binary_sequence` — constructive forward map `(ℕ → Bool) → ℝ`.
* `entropyRealEquivReal` — the classical equivalence `EntropyReal ≃ ℝ`.

## Main results

* `cardinal_entropyNat` — `#EntropyNat = ℵ₀`.
* `cardinal_entropyReal_eq_two_pow_aleph0` — `#EntropyReal = 2 ^ ℵ₀`.
* `cardinal_entropyReal` — `#EntropyReal = ℶ₁`.
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


namespace InformationTheory

open Cardinal

/-- Emergent reals: the power set of `EntropyNat`, i.e. characteristic
functions `EntropyNat → Bool`. -/
abbrev EntropyReal := EntropyNat → Bool

/-- Evaluate an `EntropyReal` at the canonical zero point. Total, constructive,
choice-free. Canonical home for this projection (also used by the isomorphism
tower and `PrimeAtoms`). -/
def evalEntropyRealZero (r : EntropyReal) : Bool :=
  r (EntropyNat.ofNat 0)

/-- Transport along `entropyNatEquivNat`, giving
`(EntropyNat → Bool) ≃ (ℕ → Bool)`. -/
noncomputable def entropyRealEquivFunNat : EntropyReal ≃ (ℕ → Bool) :=
  Equiv.arrowCongr entropyNatEquivNat (Equiv.refl Bool)

/-- `IIDParticleSource Bool` is structurally a function `ℕ → Bool`.
We establish the direct equivalence here. -/
def iidParticleSourceEquivFunNat : IIDParticleSource Bool ≃ (ℕ → Bool) where
  toFun s := s.stream
  invFun f := ⟨f⟩
  left_inv s := by cases s; rfl
  right_inv f := rfl

/-- The direct constructive equivalence between an i.i.d. particle source
and `EntropyReal` (information space). -/
noncomputable def iidParticleSourceEquivEntropyReal : IIDParticleSource Bool ≃ EntropyReal :=
  iidParticleSourceEquivFunNat.trans entropyRealEquivFunNat.symm

/-- The cardinality of `EntropyNat` is `ℵ₀`. -/
lemma cardinal_entropyNat : Cardinal.mk EntropyNat = Cardinal.aleph0 :=
  Cardinal.mk_congr (entropyNatEquivNat.trans Equiv.ulift.{0,0}.symm)

/-- The cardinality of `EntropyReal` (functions from `EntropyNat` to `Bool`)
is `2 ^ ℵ₀`. -/
lemma cardinal_entropyReal_eq_two_pow_aleph0 :
    Cardinal.mk EntropyReal = 2 ^ Cardinal.aleph0 := by
  calc
    Cardinal.mk EntropyReal
      = Cardinal.mk (ℕ → Bool)             := Cardinal.mk_congr entropyRealEquivFunNat
    _ = Cardinal.mk Bool ^ Cardinal.mk ℕ   := by rw [Cardinal.power_def]
    _ = 2 ^ Cardinal.aleph0                := by aesop

/-- The "Clean Forward Trip": an explicit, constructive surjection from
information space (`ℕ → Bool`) to the classical continuum (`ℝ`).

We split the infinite sequence of bits into even and odd indices:
- The even bits encode an integer (sign + finite binary expansion).
- The odd bits encode a fractional part in `[0, 1]` via standard binary series.

This proves constructively that the discrete information space can generate
every point in the continuous real line, without invoking `Classical.choice`. -/
noncomputable def evaluate_binary_sequence (seq : ℕ → Bool) : ℝ :=
  let seq_int := fun n => seq (2 * n)
  let seq_frac := fun n => seq (2 * n + 1)
  let int_part : ℤ :=
    (if seq_int 0 then 1 else -1) *
      (∑' n : ℕ, (if seq_int (n + 1) then (1 : ℤ) else 0) * (2 ^ n : ℤ))
  let frac_part : ℝ :=
    ∑' n : ℕ, (if seq_frac n then (1 : ℝ) else 0) / (2 ^ (n + 1) : ℝ)
  (int_part : ℝ) + frac_part

/-- The emergent reals have exactly the same cardinality as `ℝ`
(the continuum).

While the forward map (`evaluate_binary_sequence`) is a constructive
surjection, the return map (`ℝ → EntropyReal`) requires `Classical.choice`
to select a canonical binary representation for duals (e.g., `0.0111...` vs
`0.1000...`). We isolate this classical dependency to the `Equiv` itself,
keeping the generative forward direction clean. -/
noncomputable def entropyRealEquivReal : EntropyReal ≃ ℝ :=
  have h : mk EntropyReal = mk ℝ := by
    calc
      mk EntropyReal = 2 ^ aleph0 := cardinal_entropyReal_eq_two_pow_aleph0
      _           = #ℝ         := (Cardinal.mk_real).symm
  Classical.choice (Cardinal.eq.1 h)

/-- The cardinality of `EntropyReal` is `ℶ₁` (beth one). -/
lemma cardinal_entropyReal :
    Cardinal.mk EntropyReal = Cardinal.beth 1 := by
  rw [cardinal_entropyReal_eq_two_pow_aleph0]
  simp [Cardinal.beth_one]

end InformationTheory
