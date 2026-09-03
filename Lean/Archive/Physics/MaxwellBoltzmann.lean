import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.BigOperators

import Archive.Core
import Archive.Entropy.Common
import Archive.Physics.Common
import Archive.Entropy.RET
import Archive.Physics.UniformSystems

namespace EGPT.Physics.MB

open Multiset NNReal Finset Function
open EGPT.Entropy.RET
open Multiset NNReal
open EGPT EGPT.Basic
open EGPT.Entropy.Common
open EGPT.Physics.Common
open EGPT.Physics.UniformSystems

/-!
## Maxwell-Boltzmann Statistics: Distinguishable Balls, No Occupancy Limit

The Maxwell-Boltzmann state space consists of all functions `Fin M → Fin N`,
representing the allocation of `M` distinguishable (labeled) particles into `N`
distinguishable states with no occupancy constraint.

Cardinality: `N ^ M`.
-/

/-- The Maxwell-Boltzmann microstate space: functions from `Fin M` (labeled balls)
    to `Fin N` (labeled boxes). Each function assigns each ball to a box. -/
def OmegaMB (N M : ℕ) := Fin M → Fin N

/-- Fintype instance for OmegaMB. Lean/Mathlib provides `Pi.instFintype` for functions
    from a Fintype to a Fintype. -/
instance fintypeOmegaMB (N M : ℕ) : Fintype (OmegaMB N M) :=
  show Fintype (Fin M → Fin N) from inferInstance

/-- The cardinality of the MB state space is `N ^ M`. -/
lemma card_omega_MB (N M : ℕ) :
    Fintype.card (OmegaMB N M) = N ^ M := by
  unfold OmegaMB
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- The cardinality of the MB state space is positive when `N ≠ 0 ∨ M = 0`. -/
lemma card_omega_MB_pos (N M : ℕ) (h : N ≠ 0 ∨ M = 0) :
    0 < Fintype.card (OmegaMB N M) := by
  rw [card_omega_MB]
  cases h with
  | inl hN => exact Nat.pos_of_ne_zero (pow_ne_zero M (Nat.pos_iff_ne_zero.mp (Nat.pos_of_ne_zero hN)))
  | inr hM => simp [hM]

/-!
## Probability Distribution

The uniform MB distribution assigns equal probability `1 / (N ^ M)` to each microstate.
-/

/-- The MB probability distribution over the original state space. -/
noncomputable def p_MB (N M : ℕ) : OmegaMB N M → NNReal :=
  fun _q => uniformProb (Fintype.card (OmegaMB N M))

/-- The MB probability distribution indexed over `Fin (Fintype.card (OmegaMB N M))`. -/
noncomputable def p_MB_fin (N M : ℕ) : Fin (Fintype.card (OmegaMB N M)) → NNReal :=
  fun _i => uniformProb (Fintype.card (OmegaMB N M))

/-- The MB distribution sums to 1. -/
lemma p_MB_sums_to_one (N M : ℕ) (h : N ≠ 0 ∨ M = 0) :
    ∑ q : OmegaMB N M, (p_MB N M q) = 1 := by
  have h_card_pos : Fintype.card (OmegaMB N M) > 0 := card_omega_MB_pos N M h
  simp_rw [p_MB, uniformProb, dif_pos h_card_pos]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_inv_cancel₀]
  norm_cast
  exact Nat.pos_iff_ne_zero.mp h_card_pos

/-- The Fin-indexed MB distribution sums to 1. -/
lemma p_MB_fin_sums_to_one (N M : ℕ) (h : N ≠ 0 ∨ M = 0) :
    ∑ i : Fin (Fintype.card (OmegaMB N M)), (p_MB_fin N M i) = 1 := by
  have hk_pos : Fintype.card (OmegaMB N M) > 0 := card_omega_MB_pos N M h
  simp_rw [p_MB_fin]
  exact sum_uniform_eq_one hk_pos

/-- The Fin-indexed MB distribution is the canonical uniform distribution. -/
lemma p_MB_fin_is_uniformDist (N M : ℕ) (h : N ≠ 0 ∨ M = 0) :
    let k_card := Fintype.card (OmegaMB N M)
    have hk_card_pos : k_card > 0 := card_omega_MB_pos N M h
    p_MB_fin N M = uniformDist (Fintype_card_fin_pos hk_card_pos) := by
  have hk_card_pos : Fintype.card (OmegaMB N M) > 0 := card_omega_MB_pos N M h
  funext i
  simp only [p_MB_fin, uniformProb, uniformDist, Fintype.card_fin]
  rw [dif_pos hk_card_pos]

/-- `p_MB_fin` is recognized as uniform input by `H_physical_system`. -/
lemma p_MB_fin_is_H_physical_system_uniform_input (N M : ℕ) (h : N ≠ 0 ∨ M = 0) :
    p_MB_fin N M = uniformDist (α := Fin (Fintype.card (OmegaMB N M))) (by {
      simp only [Fintype.card_fin]
      exact card_omega_MB_pos N M h
    }) := by
  have hk_card_pos : Fintype.card (OmegaMB N M) > 0 := card_omega_MB_pos N M h
  funext i
  simp [p_MB_fin, uniformProb, uniformDist, Fintype.card_fin, if_pos hk_card_pos]

/-- Evaluating `H_physical_system` on `p_MB_fin`. -/
lemma eval_H_physical_system_on_p_MB_fin (N M : ℕ) (h : N ≠ 0 ∨ M = 0) :
    H_physical_system (p_MB_fin N M) =
      H_physical_system_uniform_only_calc
        (Fintype.card (OmegaMB N M))
        (Nat.one_le_of_lt (card_omega_MB_pos N M h)) := by
  have hk_card_pos : Fintype.card (OmegaMB N M) > 0 := card_omega_MB_pos N M h
  simp only [H_physical_system, Fintype.card_fin]
  rw [dif_neg (Nat.ne_of_gt hk_card_pos)]
  simp only [p_MB_fin_is_H_physical_system_uniform_input N M h]
  rfl

/-- Shannon entropy of `p_MB_fin` when cardinality is 1. -/
lemma stdShannon_of_p_MB_fin_when_k_is_1 (N M : ℕ)
    (h_k_is_1 : Fintype.card (OmegaMB N M) = 1) :
    stdShannonEntropyLn (p_MB_fin N M) = 0 := by
  unfold stdShannonEntropyLn
  conv_lhs =>
    arg 1
    simp [h_k_is_1]
  simp [p_MB_fin, h_k_is_1, uniformProb, inv_one, NNReal.coe_one, Real.negMulLog_one]

/-!
## Main Theorem: MB Entropy = C × Shannon Entropy
-/

/-- **Rota's Entropy Theorem applied to Maxwell-Boltzmann statistics.**
    The physical entropy of the MB distribution equals `C` times its Shannon entropy. -/
theorem H_MB_eq_C_shannon (N M : ℕ) (h : N ≠ 0 ∨ M = 0) :
    (EGPT.Physics.Common.H_physical_system (p_MB_fin N M) : ℝ) =
      (EGPT.Physics.Common.C_physical_NNReal : ℝ) *
      stdShannonEntropyLn (p_MB_fin N M) := by
  let k_card := Fintype.card (OmegaMB N M)
  have hk_card_ge1 : k_card ≥ 1 := Nat.one_le_of_lt (card_omega_MB_pos N M h)

  rw [eval_H_physical_system_on_p_MB_fin N M h]
  rw [H_physical_system_uniform_only_calc]

  if hk_eq_1 : k_card = 1 then
    rw [dif_pos hk_eq_1]
    simp only [NNReal.coe_zero]
    rw [stdShannon_of_p_MB_fin_when_k_is_1 N M hk_eq_1]
    simp only [mul_zero]
  else
    rw [dif_neg hk_eq_1]
    simp only [RealLogNatToNNReal, NNReal.coe_mul,
      (Real.log_nonneg (Nat.one_le_cast.mpr hk_card_ge1))]
    have h_shannon_eq_log_k : stdShannonEntropyLn (p_MB_fin N M) = Real.log (k_card : ℝ) := by
      rw [p_MB_fin_is_H_physical_system_uniform_input N M h]
      rw [stdShannonEntropyLn_uniform_eq_log_card]
      simp only [Fintype.card_fin]
      rfl
    rw [h_shannon_eq_log_k]
    rfl

end EGPT.Physics.MB
