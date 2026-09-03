import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Analysis.Real.Cardinality

/-! # The Clean Forward Boundary

Forward: `EntropyNat` generates the beth staircase — zero `Classical.choice`.
Return: `(EntropyNat → Bool) ≃ ℝ` requires `Classical.choice`. -/

set_option autoImplicit false
open Cardinal

-- ═══ FORWARD: zero Classical.choice ═══

-- Shannon-optimal encoding: all-true bits ≃ length. Address is the value.
abbrev EntropyNat := { L : List Bool // ∀ x ∈ L, x = true }

namespace EntropyNat
def toNat (u : EntropyNat) : ℕ := u.val.length
def ofNat (n : ℕ) : EntropyNat :=
  ⟨List.replicate n true, fun _ h => (List.mem_replicate.mp h).2⟩
lemma ofNat_toNat (n : ℕ) : toNat (ofNat n) = n := by simp [toNat, ofNat]
lemma toNat_ofNat (u : EntropyNat) : ofNat (toNat u) = u := by
  cases u with
  | mk L hL => simp [toNat, ofNat]
               exact (List.eq_replicate_of_mem hL).symm
end EntropyNat

def entropyNatEquivNat : EntropyNat ≃ ℕ where
  toFun := EntropyNat.toNat; invFun := EntropyNat.ofNat
  left_inv := EntropyNat.toNat_ofNat; right_inv := EntropyNat.ofNat_toNat

def Nat_L : ℕ → Type
  | 0     => EntropyNat
  | n + 1 => Nat_L n → Bool

-- ═══ RETURN: requires Classical.choice ═══

noncomputable def entropyRealEquivReal : (EntropyNat → Bool) ≃ ℝ :=
  have h : mk (EntropyNat → Bool) = mk ℝ := by
    have : mk (EntropyNat → Bool) = 2 ^ aleph0 := by
      calc mk (EntropyNat → Bool)
          = mk (ℕ → Bool) := mk_congr (Equiv.arrowCongr entropyNatEquivNat (.refl _))
        _ = mk Bool ^ mk ℕ := by rw [power_def]
        _ = 2 ^ aleph0 := by aesop
    rw [this]; exact mk_real.symm
  Classical.choice (Cardinal.eq.1 h)

#print axioms entropyNatEquivNat
#print axioms Nat_L
#print axioms entropyRealEquivReal
