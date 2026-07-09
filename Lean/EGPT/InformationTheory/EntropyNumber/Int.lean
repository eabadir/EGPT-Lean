-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.

module
public import InformationTheory.EntropyNumber.Basic
public import Mathlib.Logic.Equiv.Nat



/-!
# EntropyInt: Information-Theoretic Integers

The integers viewed as charged particle paths. An `EntropyInt` is a pair `EntropyNat × Bool`
where the `EntropyNat` component encodes the magnitude and the `Bool` encodes the sign
(the initial direction of the particle). This gives a bijection `EntropyInt ≃ ℤ`.

## Main definitions

* `EntropyInt` — the type `EntropyNat × Bool`.
* `intEquivNatProdBool` — a helper equivalence `ℤ ≃ ℕ × Bool`.
* `entropyIntEquivInt` — the bundled equivalence `EntropyInt ≃ ℤ`.

## Main results

(No standalone theorems; the key result is the construction of the
equivalence `entropyIntEquivInt : EntropyInt ≃ ℤ`.)
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

/-- An `EntropyInt` is a pair of an `EntropyNat` (magnitude) and a `Bool` (sign/charge). -/
def EntropyInt : Type := EntropyNat × Bool

/-- Helper equivalence between `ℤ` and `ℕ × Bool`, built from `Equiv.intEquivNatSumNat`
and `Equiv.boolProdEquivSum`. -/
noncomputable def intEquivNatProdBool : ℤ ≃ ℕ × Bool :=
  Equiv.intEquivNatSumNat.trans ((Equiv.boolProdEquivSum ℕ).symm.trans (Equiv.prodComm Bool ℕ))

/-- The canonical equivalence `EntropyInt ≃ ℤ`. -/
noncomputable def entropyIntEquivInt : EntropyInt ≃ ℤ :=
  (Equiv.prodCongr entropyNatEquivNat (Equiv.refl Bool)).trans intEquivNatProdBool.symm

end InformationTheory
