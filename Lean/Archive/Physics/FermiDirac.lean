import Mathlib.Data.Sym.Card

import Archive.Core
import Archive.Entropy.Common
import Archive.Physics.Common
import Archive.Entropy.RET
import Archive.Physics.UniformSystems

namespace EGPT.Physics.FD

open Multiset NNReal Finset Function
open EGPT.Entropy.RET
open Multiset NNReal
open EGPT EGPT.Basic
open EGPT.Entropy.Common
open EGPT.Physics.Common
open EGPT.Physics.UniformSystems

/-!
## Fermi-Dirac Statistics: At Most One Ball Per Box

The Fermi-Dirac state space consists of all subsets of `Fin N` of size `M`,
representing the allocation of `M` indistinguishable particles into `N`
distinguishable states with the exclusion constraint (at most one per state).

Cardinality: `Nat.choose N M` (N choose M).
-/

/-- The Fermi-Dirac microstate space: subsets of `Fin N` of size exactly `M`.
    Each element represents a valid FD configuration (at most one particle per box). -/
def OmegaFD (N M : ℕ) := { s : Finset (Fin N) // s.card = M }

/-- Fintype instance for OmegaFD. Since `Finset (Fin N)` is finite and the
    predicate `s.card = M` is decidable, the subtype is finite. -/
instance fintypeOmegaFD (N M : ℕ) : Fintype (OmegaFD N M) :=
  Fintype.subtype ((Finset.univ : Finset (Finset (Fin N))).filter (fun s => s.card = M))
    (by simp [OmegaFD])

/-- The cardinality of the FD state space is `Nat.choose N M`. -/
lemma card_omega_FD (N M : ℕ) :
    Fintype.card (OmegaFD N M) = Nat.choose N M := by
  -- Use card_of_subtype with powersetCard as the witnessing finset
  have h : Fintype.card (OmegaFD N M) =
      ((Finset.univ : Finset (Fin N)).powersetCard M).card := by
    unfold OmegaFD
    apply Fintype.card_of_subtype
    intro x
    simp [Finset.mem_powersetCard, Finset.subset_univ]
  rw [h, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- The cardinality of the FD state space is positive when `M ≤ N`. -/
lemma card_omega_FD_pos (N M : ℕ) (h : M ≤ N) :
    0 < Fintype.card (OmegaFD N M) := by
  rw [card_omega_FD]
  exact Nat.choose_pos h

/-- The domain validity condition for FD: `M ≤ N` implies `N ≠ 0 ∨ M = 0`. -/
lemma fd_domain_valid_of_le (N M : ℕ) (h : M ≤ N) : N ≠ 0 ∨ M = 0 := by
  by_cases hm : M = 0
  · exact Or.inr hm
  · exact Or.inl (Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hm) h))

/-!
## Probability Distribution

The uniform FD distribution assigns equal probability `1 / (N choose M)` to each microstate.
-/

/-- The FD probability distribution over the original state space. -/
noncomputable def p_FD (N M : ℕ) : OmegaFD N M → NNReal :=
  fun _q => uniformProb (Fintype.card (OmegaFD N M))

/-- The FD probability distribution indexed over `Fin (Fintype.card (OmegaFD N M))`. -/
noncomputable def p_FD_fin (N M : ℕ) : Fin (Fintype.card (OmegaFD N M)) → NNReal :=
  fun _i => uniformProb (Fintype.card (OmegaFD N M))

/-- The FD distribution sums to 1. -/
lemma p_FD_sums_to_one (N M : ℕ) (h : M ≤ N) :
    ∑ q : OmegaFD N M, (p_FD N M q) = 1 := by
  have h_card_pos : Fintype.card (OmegaFD N M) > 0 := card_omega_FD_pos N M h
  simp_rw [p_FD, uniformProb, dif_pos h_card_pos]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_inv_cancel₀]
  norm_cast
  exact Nat.pos_iff_ne_zero.mp h_card_pos

/-- The Fin-indexed FD distribution sums to 1. -/
lemma p_FD_fin_sums_to_one (N M : ℕ) (h : M ≤ N) :
    ∑ i : Fin (Fintype.card (OmegaFD N M)), (p_FD_fin N M i) = 1 := by
  have hk_pos : Fintype.card (OmegaFD N M) > 0 := card_omega_FD_pos N M h
  simp_rw [p_FD_fin]
  exact sum_uniform_eq_one hk_pos

/-- The Fin-indexed FD distribution is the canonical uniform distribution. -/
lemma p_FD_fin_is_uniformDist (N M : ℕ) (h : M ≤ N) :
    let k_card := Fintype.card (OmegaFD N M)
    have hk_card_pos : k_card > 0 := card_omega_FD_pos N M h
    p_FD_fin N M = uniformDist (Fintype_card_fin_pos hk_card_pos) := by
  have hk_card_pos : Fintype.card (OmegaFD N M) > 0 := card_omega_FD_pos N M h
  funext i
  simp only [p_FD_fin, uniformProb, uniformDist, Fintype.card_fin]
  rw [dif_pos hk_card_pos]

/-- `p_FD_fin` is recognized as uniform input by `H_physical_system`. -/
lemma p_FD_fin_is_H_physical_system_uniform_input (N M : ℕ) (h : M ≤ N) :
    p_FD_fin N M = uniformDist (α := Fin (Fintype.card (OmegaFD N M))) (by {
      simp only [Fintype.card_fin]
      exact card_omega_FD_pos N M h
    }) := by
  have hk_card_pos : Fintype.card (OmegaFD N M) > 0 := card_omega_FD_pos N M h
  funext i
  simp [p_FD_fin, uniformProb, uniformDist, Fintype.card_fin, if_pos hk_card_pos]

/-- Evaluating `H_physical_system` on `p_FD_fin`. -/
lemma eval_H_physical_system_on_p_FD_fin (N M : ℕ) (h : M ≤ N) :
    H_physical_system (p_FD_fin N M) =
      H_physical_system_uniform_only_calc
        (Fintype.card (OmegaFD N M))
        (Nat.one_le_of_lt (card_omega_FD_pos N M h)) := by
  have hk_card_pos : Fintype.card (OmegaFD N M) > 0 := card_omega_FD_pos N M h
  simp only [H_physical_system, Fintype.card_fin]
  rw [dif_neg (Nat.ne_of_gt hk_card_pos)]
  simp only [p_FD_fin_is_H_physical_system_uniform_input N M h]
  rfl

/-- Shannon entropy of `p_FD_fin` when cardinality is 1. -/
lemma stdShannon_of_p_FD_fin_when_k_is_1 (N M : ℕ)
    (h_k_is_1 : Fintype.card (OmegaFD N M) = 1) :
    stdShannonEntropyLn (p_FD_fin N M) = 0 := by
  unfold stdShannonEntropyLn
  conv_lhs =>
    arg 1
    simp [h_k_is_1]
  simp [p_FD_fin, h_k_is_1, uniformProb, inv_one, NNReal.coe_one, Real.negMulLog_one]

/-!
## Main Theorem: FD Entropy = C × Shannon Entropy
-/

/-- **Rota's Entropy Theorem applied to Fermi-Dirac statistics.**
    The physical entropy of the FD distribution equals `C` times its Shannon entropy. -/
theorem H_FD_eq_C_shannon (N M : ℕ) (h : M ≤ N) :
    (EGPT.Physics.Common.H_physical_system (p_FD_fin N M) : ℝ) =
      (EGPT.Physics.Common.C_physical_NNReal : ℝ) *
      stdShannonEntropyLn (p_FD_fin N M) := by
  let k_card := Fintype.card (OmegaFD N M)
  have hk_card_ge1 : k_card ≥ 1 := Nat.one_le_of_lt (card_omega_FD_pos N M h)

  rw [eval_H_physical_system_on_p_FD_fin N M h]
  rw [H_physical_system_uniform_only_calc]

  if hk_eq_1 : k_card = 1 then
    rw [dif_pos hk_eq_1]
    simp only [NNReal.coe_zero]
    rw [stdShannon_of_p_FD_fin_when_k_is_1 N M hk_eq_1]
    simp only [mul_zero]
  else
    rw [dif_neg hk_eq_1]
    simp only [RealLogNatToNNReal, NNReal.coe_mul,
      (Real.log_nonneg (Nat.one_le_cast.mpr hk_card_ge1))]
    have h_shannon_eq_log_k : stdShannonEntropyLn (p_FD_fin N M) = Real.log (k_card : ℝ) := by
      rw [p_FD_fin_is_H_physical_system_uniform_input N M h]
      rw [stdShannonEntropyLn_uniform_eq_log_card]
      simp only [Fintype.card_fin]
      rfl
    rw [h_shannon_eq_log_k]
    rfl

end EGPT.Physics.FD
