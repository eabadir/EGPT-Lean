import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog -- For negMulLog, Real.log
import Mathlib.Data.NNReal.Basic -- For NNReal
import Mathlib.Topology.Basic -- For ContinuousOn (placeholder)
import Mathlib.Order.Monotone.Basic -- For Monotone
import Mathlib.Algebra.BigOperators.Fin -- For sum over Fin n
import Mathlib.Data.Fin.Basic -- Basic Fin definitions and lemmas
import Mathlib.Data.Fintype.Fin -- Instances for Fin n
import Mathlib.Algebra.Order.Field.Basic -- For inv_one etc.
import Mathlib.Algebra.GroupWithZero.Units.Basic -- Provides mul_inv_cancel₀
import Mathlib.Analysis.SpecialFunctions.Log.Base -- Real.logb
import Mathlib.Analysis.SpecialFunctions.Pow.Real -- Real.rpow
import Mathlib.Data.Complex.Basic -- For Complex.exp_re if needed
import Mathlib.Analysis.SpecificLimits.Basic -- tendsto_one_div_atTop_zero
import Mathlib.Data.Real.Basic -- Basic Real properties
import Mathlib.Order.Filter.Basic -- Filter bases etc.
import Mathlib.Topology.Order.Basic -- OrderTopology
import Mathlib.Data.Nat.Basic -- Basic Nat properties
import Mathlib.Data.Nat.Log -- Nat.log
import Mathlib.Algebra.Order.Floor.Defs -- Floor definitions
import Mathlib.Tactic.Linarith -- Inequality solver
import Mathlib.Algebra.Ring.Nat -- For Nat.cast_pow
import Mathlib.Logic.Equiv.Defs -- For Equiv

import Archive.Core
import Archive.Basic
import Archive.Entropy.Common

/-!
# Rota's Entropy Theorem — Abstract/Axiomatic Uniqueness Proof (`Entropy/RET.lean`)

This file is a faithful Lean 4 rendition of the uniqueness-of-entropy proof
from Gian-Carlo Rota and Kenneth Baclawski, *Introduction to Probability and
Random Processes* (1979, Chapter 7; revised 1992, Chapter 8).

## Approach

The proof works entirely with **abstract** entropy functions: it assumes an
`H_func` satisfying the 7 axioms in `HasRotaEntropyProperties` (defined in
`Entropy/Common.lean`) and derives that H must be a constant multiple of the
logarithm. No concrete Shannon entropy formula is assumed or constructed here.

## Key Results

- `f0_mul_eq_add_f0` — The function `f0(n) = H(uniform_n)` satisfies the
  Cauchy functional equation `f0(m * n) = f0(m) + f0(n)`, following Rota's
  original derivation from conditional additivity on product distributions.
- `logarithmic_trapping` — The monotone solution of the Cauchy equation is
  trapped between consecutive integer logarithms, forcing `f0(n) = C * log n`.
- `RotaUniformTheorem` / `RotaUniformTheorem_formula_with_C_constant` — For
  uniform distributions, H(uniform_n) = C * log n for a universal constant C.

These results establish that any function satisfying Rota's axioms agrees with
Shannon entropy up to a positive scalar — the classical Rota-Khinchin
uniqueness theorem.

## Relationship to the Modernized Proof

This file takes the 7 axioms as *given* (via `HasRotaEntropyProperties`). The
modernized capstone in `NumberTheory/Analysis.lean` eliminates this assumption:
there, `RET_All_Entropy_Is_Scaled_Shannon_Entropy` operates on `EntropyFunction`
instances whose axioms are fully proven theorems (see `Entropy/H.lean`), making
the entire chain axiom-free and sorry-free.
-/

namespace EGPT.Entropy.RET

open Nat Real NNReal Multiset NNReal Fin Set Finset Filter Function BigOperators Topology
open EGPT EGPT.Basic EGPT.Entropy.Common


/--
Property: `f0 H 1 = 0`.
This follows from the `normalized` axiom of `HasRotaEntropyProperties`.
-/
theorem f0_1_eq_0 {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyProperties H) : f0 hH_axioms 1 = 0 := by
  have h1_pos : 1 > 0 := Nat.one_pos
  -- Unfold f0 using h1_pos
  simp only [f0, dif_pos h1_pos]
  -- Unfold f
  simp only [f]
  -- Rewrite the uniform distribution on Fin 1
  rw [uniformDist_fin_one_eq_dist_one]
  -- Apply the normalization axiom
  exact hH_axioms.normalized (fun (_ : Fin 1) => 1) sum_dist_one_fin_one_eq_1

/--
Property: `f0 H n` is monotone non-decreasing.
Uses `zero_invariance` and `max_uniform` axioms.
-/
theorem f0_mono {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyProperties H) : Monotone (f0 hH_axioms) := by
  apply monotone_nat_of_le_succ
  intro n
  -- Case n = 0
  if hn_is_zero : n = 0 then
    rw [hn_is_zero] -- Goal: f0 hH_axioms 0 ≤ f0 hH_axioms (0 + 1)
    simp [Nat.add_zero] -- Goal: f0 hH_axioms 0 ≤ f0 hH_axioms 1

    -- Simplify RHS using f0_1_eq_0
    have h0_1_eq_0 : f0 hH_axioms 1 = 0 := f0_1_eq_0 hH_axioms
    rw [h0_1_eq_0] -- Goal: f0 hH_axioms 0 ≤ 0

    -- Simplify LHS: f0 hH_axioms 0 is 0 by definition of f0
    simp [f0, Nat.not_lt_zero] -- Goal: 0 ≤ 0
  else
    -- Case n > 0
    have hn_pos : n > 0 := Nat.pos_of_ne_zero hn_is_zero
    have hn1_pos : n + 1 > 0 := Nat.succ_pos n

    -- Unfold f0 for n and n+1
    rw [f0, dif_pos hn_pos, f0, dif_pos hn1_pos]
    -- Goal: f hH_axioms hn_pos ≤ f hH_axioms hn1_pos
    -- This is H (uniformDist_on_Fin_n) ≤ H (uniformDist_on_Fin_{n+1})

    -- Let unif_n be the uniform distribution on Fin n
    let α_n := Fin n
    have h_card_n_pos : 0 < Fintype.card α_n := by
      unfold α_n
      simp only [Fintype.card_fin, hn_pos]
    let unif_n_dist := uniformDist h_card_n_pos

    -- Let p_ext be unif_n_dist extended with a zero to Fin (n+1)
    let p_ext : Fin (n+1) → NNReal :=
      fun (i : Fin (n+1)) => if h_lt : i.val < n then unif_n_dist (Fin.castLT i h_lt) else 0

    -- Show p_ext sums to 1
    have h_sum_unif_n_dist : (∑ i, unif_n_dist i) = 1 := sum_uniformDist h_card_n_pos
    have h_sum_p_ext_eq_1 : (∑ i, p_ext i) = 1 :=
      sum_p_ext_eq_one_of_sum_p_orig_eq_one unif_n_dist h_sum_unif_n_dist

    -- Relate H p_ext to H unif_n_dist using zero_invariance
    -- hH_axioms.zero_invariance requires p_orig (unif_n_dist) and its sum.
    have h_H_p_ext_eq_H_unif_n : H p_ext = H unif_n_dist := by
      -- The let binding in zero_invariance means we need to match the definition
      -- or prove our p_ext is equivalent to the one in the axiom.
      -- The axiom structure is:
      -- zero_invariance: ∀ {m : ℕ} (p_orig_ax : Fin m → NNReal) (_hp_sum_1_ax : ∑ i, p_orig_ax i = 1),
      --   let p_ext_ax := (fun (i : Fin (m + 1)) => ...); H p_ext_ax = H p_orig_ax
      -- Here, m = n, p_orig_ax = unif_n_dist.
      -- Our p_ext is definitionally the same as p_ext_ax.
      exact hH_axioms.zero_invariance unif_n_dist h_sum_unif_n_dist

    -- Relate H p_ext to H (uniformDist_on_Fin_{n+1}) using max_uniform
    let α_n1 := Fin (n+1)
    have h_card_n1_pos : 0 < Fintype.card α_n1 := by
      unfold α_n1
      simp only [Fintype.card_fin, hn1_pos]
    let unif_n1_dist := uniformDist h_card_n1_pos

    have h_H_p_ext_le_H_unif_n1 : H p_ext ≤ H unif_n1_dist := by
      -- max_uniform: ∀ {α} [Fintype α] (h_card_α_pos) (p_check) (h_sum_p_check), H p_check ≤ H (uniformDist h_card_α_pos)
      -- Here, α = Fin (n+1), p_check = p_ext.
      exact hH_axioms.max_uniform h_card_n1_pos p_ext h_sum_p_ext_eq_1

    -- Combine: H unif_n_dist = H p_ext ≤ H unif_n1_dist
    -- The goal is f hH_axioms hn_pos ≤ f hH_axioms hn1_pos.
    -- We show this is definitionally H unif_n_dist ≤ H unif_n1_dist.
    change H unif_n_dist ≤ H unif_n1_dist
    rw [← h_H_p_ext_eq_H_unif_n] -- Goal is now H p_ext ≤ H unif_n1_dist
    exact h_H_p_ext_le_H_unif_n1

/--
Helper function: Defines P(i,j) = prior(i) * q_const(j) using DependentPairDistSigma.
-/
noncomputable def dependentPairDistSigma_of_independent
  {N M : ℕ} [NeZero N] [NeZero M]
  (prior : Fin N → NNReal) (q_const : Fin M → NNReal) :
  (Σ _ : Fin N, Fin M) → NNReal :=
  DependentPairDistSigma prior (fun _ => M) (fun _ => q_const)

-- New helper
/--
If weights `w` sum to `1`, then `∑ w i * C = C`.
-/
lemma sum_weighted_constant {β : Type*} [Fintype β]
    {C_val : NNReal} {w : β → NNReal} (h_w_sum_1 : ∑ i, w i = 1) : -- Renamed C to C_val
    (∑ i, w i * C_val) = C_val := by
  rw [← Finset.sum_mul, h_w_sum_1, one_mul]


/--
If P(j|i) = q_const(j) (i.e., conditional is independent of prior index i),
then H(joint) = H(prior) + H(q_const).
This uses the generalized `cond_add_sigma`.
The joint distribution is on `(Σ i : Fin N, Fin M)`, which is equiv to `Fin (N*M)`.
-/
lemma cond_add_for_independent_distributions
    {H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal} -- Changed Type u to Type
    (hH_axioms : HasRotaEntropyProperties H_func)
    {N M : ℕ} [NeZero N] [NeZero M] -- NeZero M implies M > 0
    (prior : Fin N → NNReal) (q_const : Fin M → NNReal)
    (hprior_sum_1 : ∑ i, prior i = 1) (hq_const_sum_1 : ∑ j, q_const j = 1) :
    -- The LHS H_func is applied to a distribution on (Σ i : Fin N, Fin M).
    -- By symmetry, this should be equal to H_func of the equivalent distribution on Fin (N*M).
    -- Let's state the theorem for H_func on the sigma type first.
    H_func (DependentPairDistSigma prior (fun _ => M) (fun _ => q_const)) =
      H_func prior + H_func q_const := by
  -- Check preconditions for hH_axioms.cond_add_sigma
  have hP_cond_props_for_sigma : ∀ i : Fin N, prior i > 0 → ((fun (_ : Fin N) => M) i > 0 ∧ ∑ j, (fun (_ : Fin N) => q_const) i j = 1) := by
    intro i_idx _h_prior_i_pos
    constructor
    · -- Prove M > 0
      simp only [gt_iff_lt] -- M_map i is M
      exact NeZero.pos M   -- From [NeZero M] instance
    · -- Prove ∑ j, q_const j = 1
      exact hq_const_sum_1

  have hH_P_cond_M_map_zero_is_zero_for_sigma : ∀ i : Fin N, (fun (_ : Fin N) => M) i = 0 → H_func ((fun (_ : Fin N) => q_const) i) = 0 := by
    intro i_idx h_M_eq_0
    -- M_map i is M. So h_M_eq_0 is M = 0.
    -- This contradicts [NeZero M] which implies M > 0.
    have h_M_ne_zero : M ≠ 0 := NeZero.ne M
    exfalso
    exact h_M_ne_zero h_M_eq_0

  -- Apply the generalized conditional additivity axiom
  rw [hH_axioms.cond_add_sigma prior (fun _ => M) (fun _ => q_const) hprior_sum_1 hP_cond_props_for_sigma hH_P_cond_M_map_zero_is_zero_for_sigma]
  -- Goal: H_func prior + (∑ i, prior i * H_func q_const) = H_func prior + H_func q_const
  -- Need to show (∑ i, prior i * H_func q_const) = H_func q_const
  rw [add_left_cancel_iff] -- Cancels H_func prior from both sides using a standard iff lemma
  -- Goal: (∑ i, prior i * H_func q_const) = H_func q_const
  -- This is sum_weighted_constant from EGPT.Entropy.RET (already proven)
  exact sum_weighted_constant hprior_sum_1
-- This helper can be local to f0_mul_eq_add_f0 proof or kept if generally useful


/--
Helper Lemma: The joint distribution of two independent uniform random variables
(on Fin N and Fin M) is equivalent to a uniform distribution on the Sigma type.
The result of `dependentPairDistSigma_of_independent (uniformDist_N) (uniformDist_M)`
is pointwise equal to the uniform distribution on `(Σ _ : Fin N, Fin M)`.
-/
lemma joint_uniform_is_sigma_uniform
    {N M : ℕ} (hN_pos : N > 0) (hM_pos : M > 0) :
    -- Local NeZero instances for the definition
    haveI : NeZero N := NeZero.of_pos hN_pos
    haveI : NeZero M := NeZero.of_pos hM_pos
    let unif_N_dist := uniformDist (by simp only [Fintype.card_fin]; exact hN_pos : 0 < Fintype.card (Fin N))
    let unif_M_dist := uniformDist (by simp only [Fintype.card_fin]; exact hM_pos : 0 < Fintype.card (Fin M))
    let joint_dist := dependentPairDistSigma_of_independent unif_N_dist unif_M_dist
    let sigma_uniform_dist := uniformDist (by simp only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const, Finset.card_univ]; exact Nat.mul_pos hN_pos hM_pos : 0 < Fintype.card (Σ _ : Fin N, Fin M))
    joint_dist = sigma_uniform_dist := by
  -- Functional extensionality
  funext sigma_pair
  rcases sigma_pair with ⟨i, j⟩

  -- Unfold all relevant definitions.
  simp only [dependentPairDistSigma_of_independent, DependentPairDistSigma, uniformDist]

  -- At this point, the goal should be:
  -- (Fintype.card (Fin N))⁻¹ * (Fintype.card (Fin M))⁻¹ = (Fintype.card (Σ _ : Fin N, Fin M))⁻¹

  -- Simplify Fintype.card values
  simp only [Fintype.card_fin, Fintype.card_sigma, Finset.sum_const, Finset.card_univ]
  -- Goal: (↑N)⁻¹ * (↑M)⁻¹ = (↑(N * M))⁻¹

  -- Use NNReal properties for inverses and Nat.cast properties
  simp [Nat.cast_mul, mul_comm] -- Changes LHS to (↑N * ↑M)⁻¹




/--
Property: `f0 H (n*m) = f0 H n + f0 H m` for `n, m > 0`.
Derived from the generalized conditional additivity axiom.
Output is `NNReal`.
-/
theorem f0_mul_eq_add_f0 {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyProperties H) {n m : ℕ} (hn_pos : n > 0) (hm_pos : m > 0) :
    f0 hH_axioms (n * m) = f0 hH_axioms n + f0 hH_axioms m := by
  have hnm_pos : n * m > 0 := Nat.mul_pos hn_pos hm_pos
  haveI hN_ne_zero : NeZero n := NeZero.of_pos hn_pos
  haveI hM_ne_zero : NeZero m := NeZero.of_pos hm_pos
  haveI hNM_ne_zero : NeZero (n*m) := NeZero.of_pos hnm_pos -- Added for inv_inj later

  -- Define distributions explicitly to control unfolding
  let P_n := uniformDist (Fintype_card_fin_pos hn_pos)
  let P_m := uniformDist (Fintype_card_fin_pos hm_pos)
  let P_nm := uniformDist (Fintype_card_fin_pos hnm_pos)
  let M_map_const_m (_ : Fin n) : ℕ := m
  let P_cond_const_P_m (_ : Fin n) : Fin m → NNReal := P_m

  have h_sum_P_n : ∑ i, P_n i = 1 := sum_uniformDist (Fintype_card_fin_pos hn_pos)
  have h_sum_P_m : ∑ j, P_m j = 1 := sum_uniformDist (Fintype_card_fin_pos hm_pos)


  -- Unfold each `f0 … k` to `H (uniformDist …)`.
  simp [f0, hn_pos, hm_pos, hnm_pos] at *

  ----------------------------------------------------------------
  -- 1.  Additivity for independent distributions
  ----------------------------------------------------------------
  have h_indep :
      H (DependentPairDistSigma P_n M_map_const_m P_cond_const_P_m) =
        H P_n + H P_m := by
    simpa using
      (cond_add_for_independent_distributions hH_axioms P_n P_m
          h_sum_P_n h_sum_P_m)

  ----------------------------------------------------------------
  -- 2.  Relate the joint uniform distribution to `P_nm`
  ----------------------------------------------------------------
  -- Define U_sigma, the uniform distribution on the Sigma type (Σ i : Fin n, Fin m)
  let U_sigma := uniformDist (α := (Σ i : Fin n, Fin m)) (by {
        simp only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        exact hnm_pos
      })

  -- Prove DependentPairDistSigma P_n M_map_const_m P_cond_const_P_m is U_sigma
  have h_dep_pair_dist_eq_U_sigma : DependentPairDistSigma P_n M_map_const_m P_cond_const_P_m = U_sigma := by {
    funext x_sig; rcases x_sig with ⟨i_idx, j_idx⟩;
    -- LHS DependentPairDistSigma ... x_sig evaluates to (↑n)⁻¹ * (↑m)⁻¹
    conv_lhs =>
      simp only [DependentPairDistSigma, P_n, P_m, M_map_const_m, P_cond_const_P_m,
                 uniformDist, Fintype.card_fin]
    -- RHS U_sigma x_sig evaluates to (↑(Fintype.card (Σ _ : Fin n, Fin m)))⁻¹ which is (↑(n*m))⁻¹
    conv_rhs =>
      simp only [U_sigma, uniformDist, Fintype.card_sigma, Fintype.card_fin, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    -- Goal: (↑n)⁻¹ * (↑m)⁻¹ = (↑(n*m))⁻¹
    have hn_ne : (n : NNReal) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn_pos)
    have hm_ne : (m : NNReal) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm_pos)
    simpa [Nat.cast_mul] using
      (nnreal_inv_mul_inv_eq_inv_mul (a := (n : NNReal)) (b := (m : NNReal)) hn_ne hm_ne)
  }

  -- Define the equivalence.
  let e_final_for_symmetry : (Σ i : Fin n, Fin m) ≃ Fin (n * m) :=
    (Equiv.sigmaEquivProd (Fin n) (Fin m)).trans finProdFinEquiv

  have sum_U_sigma_is_1 : ∑ x, U_sigma x = 1 := by {
    simp [U_sigma]; -- unfolds U_sigma to uniformDist definitionally
    apply sum_uniformDist; -- sum_uniformDist requires proof of card > 0, which is in U_sigma's def
  }

  -- Prove that (U_sigma ∘ e_final_for_symmetry.symm) = P_nm
  have h_comp_eq_P_nm : (U_sigma ∘ e_final_for_symmetry.symm) = P_nm := by {
    funext y_fin_nm; -- y_fin_nm : Fin (n*m)
    simp only [comp_apply, U_sigma, P_nm, uniformDist]
    -- Goal after unfolding:
    -- (↑(Fintype.card ((i : Fin n) × Fin m)))⁻¹ = (↑(Fintype.card (Fin (n*m))))⁻¹
    simp [inv_eq_iff_eq_inv ] -- this proves the equality, DON'T CHANGE IT!!!
  }

  ----------------------------------------------------------------
  -- 3.  Chain the equalities
  ----------------------------------------------------------------
  -- Symmetry axiom: `H U_sigma = H (U_sigma ∘ e_final_for_symmetry.symm)`.
  have h_sym :
      H U_sigma = H (U_sigma ∘ e_final_for_symmetry.symm) := by
    -- `symmetry` gives the equality in the opposite direction, so we take `.symm`.
    simpa using
      (hH_axioms.symmetry U_sigma sum_U_sigma_is_1 e_final_for_symmetry.symm).symm

  have : H P_nm = H P_n + H P_m := by
    calc
      H P_nm
          = H (U_sigma ∘ e_final_for_symmetry.symm) := by
            simpa [h_comp_eq_P_nm]
      _ = H U_sigma := by
            simpa [h_sym] using (Eq.symm h_sym)
      _ = H (DependentPairDistSigma P_n M_map_const_m P_cond_const_P_m) := by
            simpa [h_dep_pair_dist_eq_U_sigma]
      _ = H P_n + H P_m := h_indep
  simpa using this


/-!
Helper lemma for the inductive step of `uniformEntropy_power_law_new`.
Shows `f0 H (n^(m+1)) = f0 H (n^m) + f0 H n`.
-/
lemma f0_pow_succ_step {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyProperties H) {n m : ℕ} (hn_pos : n > 0) (_hm_pos : m > 0) :
    f0 hH_axioms (n ^ (m + 1)) = f0 hH_axioms (n ^ m) + f0 hH_axioms n := by
  -- Assuming pow_succ' n m results in n * n^m based on the error message.
  -- If it results in n^m * n, the original argument order for f0_mul_eq_add_f0_new was correct,
  -- and the issue might be more subtle or the error message slightly misleading.
  -- Proceeding based on the error message's "with" clause indicating goal has n * n^m.
  rw [pow_succ' n m] -- This should be n * n^m if the error message is precise about the goal state

  -- Apply f0_mul_eq_add_f0_new. Need hypotheses for it:
  -- 1. n^m > 0
  have h_pow_nm_pos : n ^ m > 0 := by
    exact Nat.pow_pos hn_pos -- The exponent m is implicit here
  -- 2. n > 0 (given by hn_pos)

  -- Apply the multiplicative property.
  -- The factors in the goal's LHS (n * n^m) are n and n^m.
  -- Their positivity proofs are hn_pos and h_pow_nm_pos respectively.
  rw [f0_mul_eq_add_f0 hH_axioms hn_pos h_pow_nm_pos]
  -- The goal is now:
  -- f0 hH_axioms n + f0 hH_axioms (n ^ m) = f0 hH_axioms (n ^ m) + f0 hH_axioms n
  rw [add_comm (f0 hH_axioms n) (f0 hH_axioms (n ^ m))]




/-
The proof is by induction on `k`, using the “multiplicativity ⇒
additivity” lemma `f0_pow_succ_step` and the distributive identity
`add_mul`.  All algebra is carried out in `NNReal`, so no special coercions
are needed.
-/
theorem uniformEntropy_power_law
    {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyProperties H)
    {n k : ℕ} (hn_pos : n > 0) (hk_pos : k > 0) :
    f0 hH_axioms (n ^ k) = (k : NNReal) * f0 hH_axioms n := by
  ------------------------------------------------------------------
  --  Step 0  ·  Rephrase the goal as a proposition `P k`.
  ------------------------------------------------------------------
  let P : ℕ → Prop :=
    fun k' ↦ f0 hH_axioms (n ^ k') = (k' : NNReal) * f0 hH_axioms n

  ------------------------------------------------------------------
  --  Step 1  ·  Establish the base case  k = 1.
  ------------------------------------------------------------------
  have base : P 1 := by
    simp [P, pow_one, Nat.cast_one, one_mul]

  ------------------------------------------------------------------
  --  Step 2  ·  Prove the inductive step  P m → P (m+1)  for m ≥ 1.
  ------------------------------------------------------------------
  have step : ∀ m, m ≥ 1 → P m → P (m + 1) := by
    intro m hm_ge1 hPm       -- inductive hypothesis `hPm`
    -- positivity of `m`
    have hm_pos : m > 0 := hm_ge1

    -- use the additive recursion lemma
    have h_rec := f0_pow_succ_step hH_axioms hn_pos hm_pos
        -- `h_rec : f0 … (n^(m+1)) = f0 … (n^m) + f0 … n`

    -- rewrite the right-hand `f0 n^m` via the I.H.
    have h_rw : f0 hH_axioms (n ^ (m + 1)) =
                (m : NNReal) * f0 hH_axioms n + f0 hH_axioms n := by
      rw [h_rec] -- Goal: f0 hH_axioms (n^m) + f0 hH_axioms n = (↑m) * f0 hH_axioms n + f0 hH_axioms n
      rw [hPm]   -- Goal: (↑m) * f0 hH_axioms n + f0 hH_axioms n = (↑m) * f0 hH_axioms n + f0 hH_axioms n
                 -- This is true by reflexivity.

    -- Factor the common `f0 hH_axioms n` using `add_mul`.
    -- (↑m + 1) * C   =   ↑m * C + 1 * C
    have h_factor :
        (m : NNReal) * f0 hH_axioms n + f0 hH_axioms n =
        ((m + 1 : ℕ) : NNReal) * f0 hH_axioms n := by
      -- turn the lone `f0` into `1 * f0`, then apply `add_mul`
      simpa [one_mul, add_mul, Nat.cast_add, Nat.cast_one] using
        congrArg (fun x => x) (rfl :
          (m : NNReal) * f0 hH_axioms n + 1 * f0 hH_axioms n =
          ((m : NNReal) + 1) * f0 hH_axioms n)

    -- Combine the two equalities
    simpa [P] using h_rw.trans h_factor

  ------------------------------------------------------------------
  --  Step 3  ·  Apply `Nat.le_induction` starting from k = 1.
  ------------------------------------------------------------------
  have hk_ge1 : k ≥ 1 := Nat.one_le_of_lt hk_pos
  have : P k := Nat.le_induction base step k hk_ge1
  simpa [P] using this


-- Replaced: old `f0_nonneg`
/-- Property: `f0 H n ≥ 0` for `n ≥ 1`. (Trivial since `f0` outputs `NNReal`). -/
lemma f0_nonneg {H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal} -- Renamed H to H_func
    (hH_axioms : HasRotaEntropyProperties H_func) {n : ℕ} (_hn_ge1 : n ≥ 1) :
    ((f0 hH_axioms n) : ℝ) ≥ 0 := -- Coerced to Real for comparison with old version.
  NNReal.coe_nonneg _

-- Replaced: old `f0_2_eq_zero_of_f0_b_eq_zero`
/-- If `f0 H b = 0` for `b ≥ 2`, then `f0 H 2 = 0`. Output `NNReal`. -/
lemma f0_2_eq_zero_of_f0_b_eq_zero {H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal} -- Renamed H to H_func
    (hH_axioms : HasRotaEntropyProperties H_func) {b : ℕ} (hb_ge2 : b ≥ 2) (hf0b_eq_0 : f0 hH_axioms b = 0) :
    f0 hH_axioms 2 = 0 := by
  have h_mono := f0_mono hH_axioms
  have h_f0_2_ge_0 : f0 hH_axioms 2 ≥ 0 := zero_le (f0 hH_axioms 2)
  have h2_le_b : 2 ≤ b := by linarith
  have h_f0_2_le_b : f0 hH_axioms 2 ≤ f0 hH_axioms b := h_mono h2_le_b
  rw [hf0b_eq_0] at h_f0_2_le_b
  exact le_antisymm h_f0_2_le_b h_f0_2_ge_0

/-- If `f0 H 2 = 0`, then `f0 H (2^k) = 0` for `k ≥ 1`. (Output `NNReal`) -/
lemma f0_pow2_eq_zero_of_f0_2_eq_zero {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyProperties H) {k : ℕ} (hf0_2_eq_0 : f0 hH_axioms 2 = 0) (hk_ge1 : k ≥ 1) :
    f0 hH_axioms (2 ^ k) = 0 := by
  have h2_pos : 2 > 0 := by norm_num
  have hk_pos : k > 0 := pos_of_one_le hk_ge1
  have h_pow_law := uniformEntropy_power_law hH_axioms h2_pos hk_pos
  -- h_pow_law: f0 hH_axioms (2^k) = (k : NNReal) * f0 hH_axioms 2
  rw [hf0_2_eq_0, mul_zero] at h_pow_law
  exact h_pow_law



/-- If `f0 H (2^k) = 0` for all `k ≥ 1`, then `f0 H n = 0` for all `n ≥ 1`. (Output `NNReal`) -/
lemma f0_n_eq_zero_of_f0_pow2_zero {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyProperties H)
    (h_all_f0_pow2_zero : ∀ k ≥ 1, f0 hH_axioms (2 ^ k) = 0)
    {n : ℕ} (hn_ge1 : n ≥ 1) :
    f0 hH_axioms n = 0 := by
  have hn_pos : n > 0 := pos_of_one_le hn_ge1
  rcases @exists_pow_ge 2 n (by norm_num : 1 < 2) with ⟨k, h_n_le_2k⟩
  -- Need k ≥ 1 for h_all_f0_pow2_zero.
  -- If 2^k ≥ n ≥ 1, then k cannot be 0 unless n=1.
  if hn_eq_1 : n = 1 then
    rw [hn_eq_1]
    exact f0_1_eq_0 hH_axioms
  else
    have k_ge_1 : k ≥ 1 := by
      contrapose! hn_eq_1 -- if k=0, then n=1. After contrapose, hn_eq_1 : k < 1, goal is n = 1
      have k_eq_zero : k = 0 := (Nat.lt_one_iff.mp hn_eq_1)
      rw [k_eq_zero, pow_zero] at h_n_le_2k
      exact Nat.le_antisymm h_n_le_2k hn_ge1

    have h_f0_n_le_f0_2k : f0 hH_axioms n ≤ f0 hH_axioms (2^k) :=
      (f0_mono hH_axioms) h_n_le_2k
    rw [h_all_f0_pow2_zero k k_ge_1] at h_f0_n_le_f0_2k -- f0 H n ≤ 0
    exact le_antisymm h_f0_n_le_f0_2k (by apply @_root_.zero_le : f0 hH_axioms n ≥ 0)



/-- `f0 H b > 0` (as NNReal, so `f0 H b ≠ 0`) if `H` is non-trivial and `b ≥ 2`. -/
lemma uniformEntropy_pos_of_nontrivial {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyProperties H) (hH_nontrivial : ∃ n' ≥ 1, f0 hH_axioms n' ≠ 0)
    {b : ℕ} (hb_ge2 : b ≥ 2) :
    f0 hH_axioms b ≠ 0 := by
  by_contra hf0b_eq_0
  -- hf0b_eq_0 : f0 hH_axioms b = 0
  have hf0_2_eq_0 : f0 hH_axioms 2 = 0 :=
    f0_2_eq_zero_of_f0_b_eq_zero hH_axioms hb_ge2 hf0b_eq_0
  have h_all_f0_pow2_zero : ∀ k ≥ 1, f0 hH_axioms (2^k) = 0 :=
    fun k hk_ge1 => f0_pow2_eq_zero_of_f0_2_eq_zero hH_axioms hf0_2_eq_0 hk_ge1

  rcases hH_nontrivial with ⟨n', hn'_ge1, h_f0_n'_neq_0⟩
  have h_f0_n'_eq_0 : f0 hH_axioms n' = 0 :=
    f0_n_eq_zero_of_f0_pow2_zero hH_axioms h_all_f0_pow2_zero hn'_ge1
  exact h_f0_n'_neq_0 h_f0_n'_eq_0



-- New helper
/-- If `f0 H n ≠ 0` for `n > 0`, then `H` is non-trivial. -/
lemma hf0n_ne_0_implies_nontrivial
    {H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal} -- Renamed H to H_func
    (hH_axioms : HasRotaEntropyProperties H_func)
    {n : ℕ} (hf0n_ne_0 : f0 hH_axioms n ≠ 0) (hn_pos : n > 0) :
    ∃ n' ≥ 1, f0 hH_axioms n' ≠ 0 := by
  use n; exact ⟨Nat.one_le_of_lt hn_pos, hf0n_ne_0⟩

/-- `f0 H b > 0` (as NNReal) if `H` is non-trivial and `b ≥ 2`.
    This is a version of `uniformEntropy_pos_of_nontrivial` that directly gives `0 < f0 ...`. -/
lemma f0_pos_of_nontrivial_nnreal_version {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyProperties H) (hH_nontrivial : ∃ n' ≥ 1, f0 hH_axioms n' ≠ 0)
    {b : ℕ} (hb_ge2 : b ≥ 2) :
    0 < f0 hH_axioms b := by
  have h_ne_zero : f0 hH_axioms b ≠ 0 :=
    uniformEntropy_pos_of_nontrivial hH_axioms hH_nontrivial hb_ge2
  exact (@_root_.pos_iff_ne_zero _).mpr h_ne_zero

-- The trapping argument will now mostly deal with `Real` numbers due to division and logarithms.
-- `f0 H n` will be coerced to `Real` using `(f0 H n : Real)`.

/-- `k_from_f0_trap_satisfies_pow_bounds` but with `f0` outputting `NNReal` and coercing.
    The inequalities for `f0` ratios will be in `Real`.
    `k_val / m_val ≤ (f0 H n : ℝ) / (f0 H b : ℝ)`
-/
lemma k_from_f0_trap_satisfies_pow_bounds_real {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyProperties H) (hH_nontrivial : ∃ n' ≥ 1, f0 hH_axioms n' ≠ 0)
    {n m b : ℕ} (hn_pos : n > 0) (hm_pos : m > 0) (hb_ge2 : b ≥ 2) :
    ∃ k : ℕ,
      -- Power bounds (Real numbers, Nat powers)
      ((b : ℝ) ^ k ≤ (n : ℝ) ^ m ∧ (n : ℝ) ^ m < (b : ℝ) ^ (k + 1)) ∧
      -- Ratio bounds (Real numbers)
      (((k : ℝ) / (m : ℝ) ≤ (f0 hH_axioms n : ℝ) / (f0 hH_axioms b : ℝ)) ∧
       ((f0 hH_axioms n : ℝ) / (f0 hH_axioms b : ℝ) ≤ ((k : ℝ) + 1) / (m : ℝ))) := by
  let x_real : ℝ := (n : ℝ) ^ m
  have hx_real_ge_1 : x_real ≥ 1 := by
    exact one_le_pow_cast (Nat.one_le_of_lt hn_pos)
  have hb_real_gt_1 : (b : ℝ) > 1 := Nat.one_lt_cast.mpr (by linarith : b > 1)

  rcases exists_nat_pow_bounds hb_ge2 hx_real_ge_1 with ⟨k, h_bk_le_x, h_x_lt_bkp1⟩
  -- h_bk_le_x : (b:ℝ)^k ≤ x_real
  -- h_x_lt_bkp1 : x_real < (b:ℝ)^(k+1)

  use k
  constructor
  · exact ⟨h_bk_le_x, h_x_lt_bkp1⟩
  · -- Prove Ratio bounds using f0 (NNReal) properties, then coerce and divide in Real
    let f0n_nnreal := f0 hH_axioms n
    let f0b_nnreal := f0 hH_axioms b
    let f0_nm_pow_nnreal := f0 hH_axioms (n ^ m)
    let f0_bk_pow_nnreal := f0 hH_axioms (b ^ k)
    let f0_bkp1_pow_nnreal := f0 hH_axioms (b ^ (k+1))

    have h_nm_pow_pos : n^m > 0 := Nat.pow_pos hn_pos
    have h_bk_pow_pos : b^k > 0 := Nat.pow_pos (by linarith : b > 0)
    have h_bkp1_pow_pos : b^(k+1) > 0 := Nat.pow_pos (by linarith : b > 0)
    have m_pos_real : (m:ℝ) > 0 := Nat.cast_pos.mpr hm_pos

    -- Nat bounds from Real bounds on powers: b^k ≤ n^m < b^(k+1)
    have h_nat_bounds : b^k ≤ n^m ∧ n^m < b^(k+1) :=
      nat_bounds_from_cast_pow_bounds h_bk_le_x h_x_lt_bkp1
    have h_nat_le := h_nat_bounds.left
    have h_nat_lt := h_nat_bounds.right

    -- Monotonicity of f0 for these Nat bounds
    have h_f0_mono1 : f0_bk_pow_nnreal ≤ f0_nm_pow_nnreal := (f0_mono hH_axioms) h_nat_le
    have h_f0_mono2 : f0_nm_pow_nnreal ≤ f0_bkp1_pow_nnreal := (f0_mono hH_axioms) (Nat.le_of_lt h_nat_lt)

    -- Apply power law (outputs NNReal)
    -- f0 H (n^m) = m * f0 H n
    have pl_nm : f0_nm_pow_nnreal = (m : NNReal) * f0n_nnreal :=
      uniformEntropy_power_law hH_axioms hn_pos hm_pos
    -- f0 H (b^k) = k * f0 H b (if k>0, else f0 H 1 = 0)
    have pl_bk : f0_bk_pow_nnreal = (if k_is_0 : k = 0 then 0 else (k : NNReal) * f0b_nnreal) := by
      split_ifs with hk_cond
      · -- Case k = 0. Goal is f0_bk_pow_nnreal = 0.
        -- hk_cond : k = 0
        change f0 hH_axioms (b ^ k) = 0 -- Unfold f0_bk_pow_nnreal
        rw [hk_cond, pow_zero]          -- Goal: f0 hH_axioms 1 = 0
        exact f0_1_eq_0 hH_axioms
      · -- Case k ≠ 0. Goal is f0_bk_pow_nnreal = (k : NNReal) * f0b_nnreal.
        -- hk_cond : k ≠ 0
        change f0 hH_axioms (b ^ k) = (k : NNReal) * f0b_nnreal -- Unfold f0_bk_pow_nnreal
        exact uniformEntropy_power_law hH_axioms (by linarith) (Nat.pos_of_ne_zero hk_cond)
    -- f0 H (b^(k+1)) = (k+1) * f0 H b
    have pl_bkp1 : f0_bkp1_pow_nnreal = ((k+1 : ℕ) : NNReal) * f0b_nnreal :=
      uniformEntropy_power_law hH_axioms (by linarith) (Nat.succ_pos k)

    -- Substitute power laws into mono inequalities (still in NNReal)
    rw [pl_bk, pl_nm] at h_f0_mono1
    rw [pl_nm, pl_bkp1] at h_f0_mono2

    -- Coerce to Real and divide
    have h_f0b_real_pos : (f0b_nnreal : ℝ) > 0 := by
      simp only [NNReal.coe_pos] -- coe_pos is NNReal.coe_pos, needs f0b_nnreal > 0 (as NNReal)
      exact f0_pos_of_nontrivial_nnreal_version hH_axioms hH_nontrivial hb_ge2

    constructor
    · -- Left inequality: k/m ≤ (f0n)/(f0b)
      -- from: (if k=0 then 0 else k*f0b) ≤ m*f0n
      by_cases hk0_case : k = 0
      · -- Case k = 0
        -- First, simplify h_f0_mono1 using k=0, though it's not directly used for this goal.
        rw [hk0_case] at h_f0_mono1; simp only [if_pos] at h_f0_mono1
        -- h_f0_mono1 is now `0 ≤ (m : NNReal) * f0n_nnreal`

        -- Now, simplify the goal using k=0.
        -- Goal was: (k:ℝ)/(m:ℝ) ≤ (f0n_nnreal:ℝ)/(f0b_nnreal:ℝ)
        simp only [hk0_case, Nat.cast_zero, zero_div]
        -- Goal is now: 0 ≤ (f0n_nnreal:ℝ)/(f0b_nnreal:ℝ)
        -- This simp uses m_pos_real (↑m > 0) to simplify 0/(m:ℝ) to 0.

        -- Prove 0 ≤ (f0n_nnreal:ℝ)/(f0b_nnreal:ℝ)
        apply div_nonneg
        · -- Numerator f0n_nnreal ≥ 0
          exact NNReal.coe_nonneg f0n_nnreal
        · -- Denominator f0b_nnreal > 0, so f0b_nnreal ≥ 0
          exact le_of_lt h_f0b_real_pos
      · -- k > 0 case
        -- h_f0_mono1 was: (if k_is_0 : k = 0 then 0 else (k:NNReal)*f0b_nnreal) ≤ (m:NNReal)*f0n_nnreal
        -- hk0_case : ¬(k = 0)
        -- We want to simplify h_f0_mono1 using hk0_case.
        simp [hk0_case] at h_f0_mono1
        -- h_f0_mono1 is now: (k:NNReal)*f0b_nnreal ≤ (m:NNReal)*f0n_nnreal
        -- Goal: (k:ℝ)/(m:ℝ) ≤ (f0n_nnreal:ℝ)/(f0b_nnreal:ℝ)
        -- Rewrite as k * f0b ≤ m * f0n using mul_le_mul_iff_of_pos (for Real)
        rw [div_le_div_iff₀ m_pos_real h_f0b_real_pos]
        -- Goal is now (k:ℝ)*(f0b_nnreal:ℝ) ≤ (f0n_nnreal:ℝ)*(m:ℝ) due to div_le_div_iff₀ structure
        -- Transform goal to match NNReal.coe_le_coe structure
        rw [← NNReal.coe_natCast k, ← NNReal.coe_natCast m] -- Converts (k:ℝ) to ↑(k:NNReal) etc.
                                                        -- Goal: ↑k * ↑f0b ≤ ↑f0n * ↑m (all terms now coe from NNReal)
        rw [← NNReal.coe_mul, ← NNReal.coe_mul] -- Converts ↑X * ↑Y to ↑(X * Y)
                                            -- Goal: ↑(k*f0b) ≤ ↑(f0n*m) (ops inside coe are NNReal)
        rw [NNReal.coe_le_coe] -- Applies ↑A ≤ ↑B ↔ A ≤ B
                                -- Goal: (k:NNReal)*f0b_nnreal ≤ (f0n_nnreal:NNReal)*(m:NNReal)
        conv_rhs => rw [mul_comm] -- Goal: (k:NNReal)*f0b_nnreal ≤ (m:NNReal)*(f0n_nnreal:NNReal)
        exact h_f0_mono1
    · -- Right inequality: (f0n)/(f0b) ≤ (k+1)/m
      -- from: m*f0n ≤ (k+1)*f0b
      -- h_f0_mono2: (m:NNReal)*f0n_nnreal ≤ ((k+1):NNReal)*f0b_nnreal
      rw [div_le_div_iff₀ h_f0b_real_pos m_pos_real]
      -- Goal: (f0n_nnreal:ℝ)*(m:ℝ) ≤ (((k+1):ℕ):ℝ)*(f0b_nnreal:ℝ)
      rw [mul_comm (f0n_nnreal:ℝ) _] -- match order for next steps
      -- Goal: (m:ℝ)*(f0n_nnreal:ℝ) ≤ (((k+1):ℕ):ℝ)*(f0b_nnreal:ℝ)
      -- Note: by Nat.cast_add_one, the term (((k+1):ℕ):ℝ) is (↑k + 1) in Real.

      -- Transform goal to match NNReal.coe_le_coe structure
      rw [← NNReal.coe_natCast m] -- Handles LHS factor (m:ℝ) becoming ↑(↑m:NNReal)
      -- At this point, the RHS factor involving k is (↑k + 1):ℝ
      rw [← Nat.cast_add_one k]   -- Changes (↑k + 1) on RHS to ↑(k+1:ℕ)
      rw [← NNReal.coe_natCast (k+1)] -- Changes ↑(k+1:ℕ) on RHS to ↑(↑(k+1:ℕ):NNReal)

      -- Goal should now be:
      -- ↑(↑m:NNReal) * ↑f0n_nnreal ≤ ↑(↑(k+1:ℕ):NNReal) * ↑f0b_nnreal
      rw [← NNReal.coe_mul, ← NNReal.coe_mul]
      rw [NNReal.coe_le_coe]
      -- Goal: (m:NNReal)*f0n_nnreal ≤ ((k+1):NNReal)*f0b_nnreal
      exact h_f0_mono2


-- Replaced: old `le_logb_rpow_self_of_le`
/-- `k ≤ logb b X` given `b > 1, X > 0, b^k ≤ X`. -/
lemma le_logb_rpow_self_of_le {b k X : ℝ} (hb_gt_1 : b > 1) (hX_pos : 0 < X) (hkX : b^k ≤ X) :
    k ≤ Real.logb b X := by
  have b_pos : 0 < b := lt_trans zero_lt_one hb_gt_1
  have b_ne_one : b ≠ 1 := ne_of_gt hb_gt_1
  rw [← Real.logb_rpow b_pos b_ne_one (x := k)]
  apply (Real.logb_le_logb hb_gt_1 (Real.rpow_pos_of_pos b_pos k) hX_pos).mpr
  exact hkX

-- Replaced: old `logb_rpow_self_lt_of_lt`
/-- `logb b X < k_plus_1` given `b > 1, X > 0, X < b^(k_plus_1)`. -/
lemma logb_rpow_self_lt_of_lt {b X k_plus_1 : ℝ} (hb_gt_1 : b > 1) (hX_pos : 0 < X) (hXlt : X < b^k_plus_1) :
    Real.logb b X < k_plus_1 := by
  have b_pos : 0 < b := lt_trans zero_lt_one hb_gt_1
  have b_ne_one : b ≠ 1 := ne_of_gt hb_gt_1
  rw [← Real.logb_rpow b_pos b_ne_one (x := k_plus_1)]
  apply Real.logb_lt_logb hb_gt_1 hX_pos hXlt

/-!  Helper for `abs_sub_le_iff`  -/
structure AbsPair (a b r : ℝ) : Prop where
  left  : a - b ≤ r       -- 1ˢᵗ inequality
  right : b - a ≤ r       -- 2ⁿᵈ inequality

instance {a b r : ℝ} : Coe (AbsPair a b r)
    (a - b ≤ r ∧ b - a ≤ r) where
  coe := fun h => ⟨h.left, h.right⟩


/--
Logarithmic trapping: `| (f0 H n : ℝ) / (f0 H b : ℝ) - logb b n | ≤ 1 / (m : ℝ)`.
This uses the Real‐valued bounds from `k_from_f0_trap_satisfies_pow_bounds_real`.
-/
theorem logarithmic_trapping
  {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
  (hH_axioms     : HasRotaEntropyProperties H)
  (hH_nontrivial : ∃ n' ≥ 1, f0 hH_axioms n' ≠ 0)
  {n m b : ℕ} (hn_pos  : n > 0) (hm_pos  : m > 0) (hb_ge2 : b ≥ 2) :
  |(f0 hH_axioms n : ℝ) / (f0 hH_axioms b : ℝ) - Real.logb b n| ≤ 1 / (m : ℝ) :=
by
  -- Unpack the “k from f0” bounds:
  rcases k_from_f0_trap_satisfies_pow_bounds_real
    hH_axioms hH_nontrivial hn_pos hm_pos hb_ge2
    with ⟨k, ⟨h_pow_le_nm,   h_nm_lt_pow_kp1⟩,
              ⟨h_f0_ratio_lower_bound, h_f0_ratio_upper_bound⟩⟩

  let f0_ratio  := (f0 hH_axioms n : ℝ) / (f0 hH_axioms b : ℝ)
  let logb_n_val := Real.logb b n
  let k_real    := (k : ℝ)
  let m_real    := (m : ℝ)

  -- Basic casts and positivity facts
  have hb_real_gt_1 : (b : ℝ) > 1 := Nat.one_lt_cast.mpr (by linarith : b > 1)
  have hn_real_pos : (n : ℝ) > 0 := Nat.cast_pos.mpr hn_pos
  have hm_real_pos : m_real > 0   := Nat.cast_pos.mpr hm_pos

  -- Derive     k_real ≤ m_real * logb_n_val   <   k_real + 1
  have h_k_le_m_logbn : k_real ≤ m_real * logb_n_val := by
    -- rewrite m * logb b n as logb b ((n^m : ℝ))
    rw [← Real.logb_rpow_eq_mul_logb_of_pos hn_real_pos (y := m_real)]
    -- reduce to proving (b^k : ℝ) ≤ (n^m : ℝ)
    have : (b : ℝ)^k_real ≤ (n : ℝ)^m_real := by
      simp_rw [k_real, m_real]
      rw [Real.rpow_natCast, Real.rpow_natCast]
      exact h_pow_le_nm
    apply le_logb_rpow_self_of_le hb_real_gt_1 (Real.rpow_pos_of_pos hn_real_pos m_real) this

  have h_m_logbn_lt_kp1 : m_real * logb_n_val < k_real + 1 := by
    rw [← Real.logb_rpow_eq_mul_logb_of_pos hn_real_pos (y := m_real)]
    have : (n : ℝ)^m_real < (b : ℝ)^(k_real + 1) := by
      simp_rw [m_real, k_real]
      rw [Real.rpow_natCast, ← Nat.cast_add_one, Real.rpow_natCast] -- Corrected order
      exact h_nm_lt_pow_kp1
    apply logb_rpow_self_lt_of_lt hb_real_gt_1 (Real.rpow_pos_of_pos hn_real_pos m_real) this

  -- Convert to the two sided‐inequalities on logb_n_val
  have h_logb_lt_kp1_m : logb_n_val < (k_real + 1) / m_real := by
    rw [lt_div_iff₀ hm_real_pos, mul_comm]
    exact h_m_logbn_lt_kp1

  have h_km_le_logb : k_real / m_real ≤ logb_n_val := by
    rw [div_le_iff₀ hm_real_pos, mul_comm]
    exact h_k_le_m_logbn

  have h_logb_minus_1m_lt_km : logb_n_val - 1 / m_real < k_real / m_real := by
    rw [sub_lt_iff_lt_add, div_add_div_same]
    exact h_logb_lt_kp1_m

  ----------------------------------------------------------------
  --  NEW: prove the two sides in the correct orientations:
  ----------------------------------------------------------------
  -- (1) logb_n_val - f0_ratio ≤ 1 / m_real
  have h_right : logb_n_val - f0_ratio ≤ 1 / m_real := by
    have : logb_n_val - f0_ratio < 1 / m_real := by
      -- f0_ratio ≥ k/m and logb_n_val - 1/m < k/m
      linarith [h_logb_minus_1m_lt_km, h_f0_ratio_lower_bound]
    exact le_of_lt this

  -- (2)  –(1/m_real) ≤  logb_n_val - f0_ratio
  --     ↔  f0_ratio - logb_n_val ≤ 1/m_real
  have h_left : f0_ratio - logb_n_val ≤ 1 / m_real := by
    -- first prove  f0_ratio ≤ logb_n_val + 1/m_real
    have h_aux : f0_ratio ≤ logb_n_val + 1 / m_real := by
      have h2 : f0_ratio ≤ (k_real + 1) / m_real := h_f0_ratio_upper_bound
      have h3 : (k_real + 1) / m_real ≤ logb_n_val + 1 / m_real := by
        have h_base : k_real + 1 ≤ m_real * logb_n_val + 1 := by
          exact add_le_add_right h_k_le_m_logbn 1
        -- rewrite logb_n_val + 1/m_real as (m_real * logb_n_val + 1)/m_real
        rw [show logb_n_val + 1 / m_real = (m_real * logb_n_val + 1) / m_real by
              field_simp [mul_comm, ne_of_gt hm_real_pos]]
        exact (div_le_div_iff_of_pos_right hm_real_pos).mpr h_base
      exact h2.trans h3
    -- now sub_le_iff_le_add turns `f0_ratio ≤ logb_n_val + 1/m` into the goal
    -- The simplified goal becomes `f0_ratio ≤ 1 / m_real + logb_n_val` (due to simpa's canonicalization).
    -- h_aux is `f0_ratio ≤ logb_n_val + 1 / m_real`.
    -- Adding `add_comm` allows simpa to match these.
    simpa [sub_le_iff_le_add, add_comm] using h_aux

  -- Assemble and finish
  rw [abs_sub_comm f0_ratio logb_n_val]
  have h_bounds : AbsPair logb_n_val f0_ratio (1 / m_real) := ⟨h_right, h_left⟩
  exact abs_sub_le_iff.mpr h_bounds


/--
The ratio `(f0 H n : ℝ) / (f0 H b : ℝ)` is exactly `logb b n`.
Requires `H` to be non-trivial.
-/
theorem uniformEntropy_ratio_eq_logb {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyProperties H) (hH_nontrivial : ∃ n' ≥ 1, f0 hH_axioms n' ≠ 0)
    {n b : ℕ} (hn_pos : n > 0) (hb_ge2 : b ≥ 2) :
    (f0 hH_axioms n : ℝ) / (f0 hH_axioms b : ℝ) = Real.logb b n := by
  apply eq_of_abs_sub_le_inv_ge_one_nat
  intro m hm_ge1
  exact logarithmic_trapping hH_axioms hH_nontrivial hn_pos (pos_of_one_le hm_ge1) hb_ge2




/--
Rota's Uniform Theorem (final part of Phase 2):
`f0 H n` (coerced to Real) is `C * Real.log n`.
-/
theorem RotaUniformTheorem_formula_with_C_constant {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyProperties H) :
    let C_val := C_constant_real hH_axioms
    (C_val ≥ 0 ∧
     ∀ (n : ℕ) (_hn_pos : n > 0), (f0 hH_axioms n : ℝ) = C_val * Real.log n) := by
  let C_val := C_constant_real hH_axioms
  constructor
  · exact C_constant_real_nonneg hH_axioms
  · intro n hn_pos
    -- Goal: (f0 hH_axioms n : ℝ) = C_val * Real.log n
    simp_rw [C_constant_real] -- Unfold C_val definition in the goal
    split_ifs with h_nontrivial
    · -- Case: H non-trivial. C_val_expanded = (f0 hH_axioms 2 : ℝ) / Real.log 2
      -- Goal: (f0 hH_axioms n : ℝ) = ((f0 hH_axioms 2 : ℝ) / Real.log 2) * Real.log n
      let F0N := (f0 hH_axioms n : ℝ)
      let F02 := (f0 hH_axioms 2 : ℝ)
      let LOGN := Real.log n
      let LOG2 := Real.log 2
      change F0N = (F02 / LOG2) * LOGN -- Makes the goal structure explicit with local names

      have h_ratio_eq_logb : F0N / F02 = Real.logb 2 n :=
        uniformEntropy_ratio_eq_logb hH_axioms h_nontrivial hn_pos (by norm_num : 2 ≥ 2)

      have hf02_ne_zero : F02 ≠ 0 := by
        exact NNReal.coe_ne_zero.mpr (uniformEntropy_pos_of_nontrivial hH_axioms h_nontrivial (by norm_num))
      have hlog2_ne_zero : LOG2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (2:ℝ) > 1))
      have hn_real_pos : (n:ℝ) > 0 := Nat.cast_pos.mpr hn_pos
      have h2_real_pos : (2:ℝ) > 0 := by norm_num

      -- Rewrite logb using log: F0N / F02 = LOGN / LOG2
      rw [Real.logb] at h_ratio_eq_logb
      -- Note: Real.logb_def is logb b x = log x / log b.
      -- This changes h_ratio_eq_logb to: F0N / F02 = LOGN / LOG2

      -- Now we have F0N / F02 = LOGN / LOG2
      -- Goal is F0N = (F02 / LOG2) * LOGN
      rw [div_eq_iff hf02_ne_zero] at h_ratio_eq_logb
      -- h_ratio_eq_logb is now: F0N = (LOGN / LOG2) * F02
      -- Goal is:                F0N = (F02 / LOG2) * LOGN
      rw [h_ratio_eq_logb]
      -- Goal: (LOGN / LOG2) * F02 = (F02 / LOG2) * LOGN
      -- This can be rearranged using field properties
      -- field_simp [hlog2_ne_zero] -- Should simplify both sides to (LOGN * F02) / LOG2
      -- The goal is (Real.log ↑n / Real.log 2) * F02 = F02 / Real.log 2 * Real.log ↑n
      -- which simplifies to (Real.log n * F02) / Real.log 2 = (F02 * Real.log n) / Real.log 2.
      -- This is true by commutativity of multiplication. `ring` handles this.
      ring

    · -- Case: H trivial (¬h_nontrivial). C_val_expanded = 0
      -- Goal: (f0 hH_axioms n : ℝ) = 0 * Real.log n
      have hf0n_eq_0_nnreal : f0 hH_axioms n = 0 := by
        by_contra hf0n_ne_0_hyp
        -- Use the externalized lemma:
        -- hf0n_ne_0_implies_nontrivial takes (f0 H n ≠ 0) and (n > 0)
        -- and returns (∃ n' ≥ 1, f0 H n' ≠ 0)
        -- This contradicts h_nontrivial (which is ¬(∃ n' ≥ 1, f0 H n' ≠ 0))
        exact h_nontrivial (hf0n_ne_0_implies_nontrivial hH_axioms hf0n_ne_0_hyp hn_pos)
      simp only [hf0n_eq_0_nnreal, NNReal.coe_zero, zero_mul]

theorem RotaUniformTheorem {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyProperties H) :
    ∃ C ≥ 0, ∀ (n : ℕ) (_hn_pos : n > 0), (f0 hH_axioms n : ℝ) = C * Real.log n := by
  use C_constant_real hH_axioms
  exact RotaUniformTheorem_formula_with_C_constant hH_axioms

/--
The `EntropyFunction` type encapsulates a function `H_func` that calculates
an entropy value (as NNReal) for a given probability distribution `p` over a
finite type `α`. Crucially, it bundles proof `props` that `H_func`
satisfies `HasRotaEntropyProperties`.
-/
structure EntropyFunction where
  (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal)
  (props : HasRotaEntropyProperties H_func)

/--
A helper to evaluate an EntropyFunction and get a Real value.
-/
noncomputable def evalEntropyFunction {ef : EntropyFunction}
    {α : Type} [Fintype α] (p : α → NNReal) : ℝ :=
  (ef.H_func p : ℝ)

/--
The Rota-Khinchin constant associated with an EntropyFunction.
This is derived from its `H_func` and `props`.
-/
noncomputable def C_constant_of_EntropyFunction (ef : EntropyFunction) : ℝ :=
  C_constant_real ef.props

/--
Helper lemma demonstrating that if M is asserted to be non-zero (via `NeZero M`),
then an assumption `M = 0` leads to a contradiction.
This is analogous to the internal helper in `cond_add_for_independent_distributions`.
The conclusion `H_func q_const = 0` is reached via `exfalso`.
-/
lemma H_func_of_cond_dist_on_empty_domain_from_false_assumption
    {H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    {N M : ℕ} [hM_is_nonzero : NeZero M] (q_const : Fin M → NNReal)
    (_i_idx : Fin N) (h_M_eq_0 : (fun (_ : Fin N) => M) _i_idx = 0) :
    H_func ((fun (_ : Fin N) => q_const) _i_idx) = 0 := by
  simp only at h_M_eq_0 -- Simplifies `(fun (_ : Fin N) => M) i_idx = 0` to `M = 0`
  have h_M_ne_zero : M ≠ 0 := NeZero.ne M -- From the [NeZero M] instance
  exfalso -- From M = 0 and M ≠ 0, we can prove anything.
  exact h_M_ne_zero h_M_eq_0

/--
Core definition for the conditional distribution based on a natural number `val`.
If `val = 0`, it's the distribution on `Fin 0`.
If `val = k + 1`, it's uniform on `Fin (k + 1)`.
-/
noncomputable def P_cond_sigma_def_core (val : ℕ) : Fin val → NNReal :=
  match h : val with
  | 0      => h ▸ (Fin.elim0 : Fin 0 → NNReal)
  | k + 1  => uniformDist (Fintype_card_fin_pos (Nat.succ_pos k))

/--
Defines the conditional distribution for the i-th component in Rota's rational setup.
It uses `P_cond_sigma_def_core` with `a_map i`.
-/
noncomputable def P_cond_sigma_def {n : ℕ} (a_map : Fin n → ℕ) (i : Fin n) :
    Fin (a_map i) → NNReal :=
  P_cond_sigma_def_core (a_map i)




/--
`H_func` evaluated on `P_cond_sigma_def` is `f0 hH` at the same
cardinality.
-/
lemma H_func_P_cond_sigma_def_eq_f0
    {n : ℕ}
    (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal)
    (hH : HasRotaEntropyProperties H_func)
    (a_map : Fin n → ℕ) (i : Fin n)
    {h0 : IsEntropyZeroOnEmptyDomain H_func} :
  H_func (P_cond_sigma_def a_map i) = f0 hH (a_map i) := by
  dsimp [P_cond_sigma_def] -- Exposes P_cond_sigma_def_core (a_map i)
  cases h_ai : a_map i with
  | zero =>
      -- h_ai : a_map i = 0
      -- Goal: H_func (P_cond_sigma_def_core 0) = f0 hH 0
      rw [P_cond_sigma_def_core] -- Unfold with val = 0
      -- LHS becomes H_func ((rfl : 0=0) ▸ Fin.elim0) which simplifies to H_func Fin.elim0
      --simp only [eq_rec_rfl, eq_symm_rfl] -- Handles `rfl ▸ E`
      -- Goal: H_func Fin.elim0 = f0 hH 0
      rw [f0, dif_neg (Nat.not_lt_zero 0)] -- RHS becomes 0
      rw [h0.apply_to_empty_domain] -- LHS becomes 0
      -- Goal: 0 = 0
  | succ k =>
      -- h_ai : a_map i = k.succ
      -- Goal: H_func (P_cond_sigma_def_core (k.succ)) = f0 hH (k.succ)
      rw [P_cond_sigma_def_core] -- Unfold with val = k.succ
      -- LHS becomes H_func (uniformDist (Fintype_card_fin_pos (Nat.succ_pos k)))
      have hk_pos : (k.succ) > 0 := Nat.succ_pos k
      rw [f0, dif_pos hk_pos] -- RHS becomes f hH hk_pos
      rw [f] -- RHS becomes H_func (uniformDist (Fintype_card_fin_pos hk_pos))
      -- Goal: H_func (uniformDist ...) = H_func (uniformDist ...)

lemma sum_P_cond_sigma_def_eq_one_of_pos {n : ℕ} (a_map : Fin n → ℕ) (i : Fin n) (ha_i_pos : a_map i > 0) :
    ∑ j, (P_cond_sigma_def a_map i) j = 1 := by
  simp_rw [P_cond_sigma_def, P_cond_sigma_def_core]
  -- Since ha_i_pos, a_map i cannot be 0. So it must be k.succ for some k.
  cases h_ai_cases : a_map i with -- Use cases on a_map i
  | zero => exact (Nat.not_succ_le_zero 0 (h_ai_cases ▸ ha_i_pos)).elim -- Contradiction from ha_i_pos
  | succ k => -- a_map i = k.succ
    -- The match in P_cond_sigma_def_core will take the succ k branch.
    simp only [h_ai_cases] -- Substitute a_map i = k.succ into the goal if needed by simp context
    -- LHS is now ∑ j : Fin (k.succ), uniformDist (Fintype_card_fin_pos (Nat.succ_pos k)) j
    exact sum_uniformDist (Fintype_card_fin_pos (Nat.succ_pos k))


-- -- FOR REFERENCE IN DEALING WITH ZERO In EGPT.Entropy.Common.lean, add this structure:
-- structure IsEntropyZeroOnEmptyDomain
--   (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) : Prop where
--   apply_to_empty_domain : H_func Fin.elim0 = 0
--   -- Fin.elim0 here denotes the unique function Fin 0 → NNReal.
--   -- The specific instance H_func {α := Fin 0} [Fintype (Fin 0)] Fin.elim0 is used.

/-- **(A)** Value of the conditional density at index `j`. -/
@[simp] lemma P_cond_sigma_def_core_eval {val : ℕ} :
    (P_cond_sigma_def_core val) =
      (match val with
       | 0      => Fin.elim0
       | m + 1  => λ _j => ((m+1 : NNReal)⁻¹)) := by
  cases val with
  | zero    => simp [P_cond_sigma_def_core]
  | succ m  => -- val is m + 1
      -- The goal is P_cond_sigma_def_core (m+1) = (λ _j => ((m+1 : NNReal)⁻¹))
      -- Unfolding P_cond_sigma_def_core (m+1) gives uniformDist (Fintype_card_fin_pos (Nat.succ_pos m))
      -- So, goal becomes: uniformDist (Fintype_card_fin_pos (Nat.succ_pos m)) = (λ _j => ((m+1 : NNReal)⁻¹))
      funext j -- Apply function extensionality: prove for an arbitrary argument j
      -- New goal: P_cond_sigma_def_core (m+1) j = ((m+1 : NNReal)⁻¹)
      -- (or (uniformDist ...) j = ((m+1 : NNReal)⁻¹) if P_cond_sigma_def_core was already unfolded by `cases`)
      -- Now simp should work:
      -- LHS: P_cond_sigma_def_core (m+1) j
      --   -> (uniformDist (Fintype_card_fin_pos (Nat.succ_pos m))) j  (by P_cond_sigma_def_core)
      --   -> (↑(Fintype.card (Fin (m+1))))⁻¹                         (by uniformDist)
      --   -> (↑(m+1))⁻¹                                              (by Fintype.card_fin)
      -- RHS: ((m+1 : NNReal)⁻¹)
      simp [P_cond_sigma_def_core, uniformDist, Fintype.card_fin]

/-- **(B)** Value of the uniform distribution on the σ-type. -/
@[simp] lemma uniform_sigma_eval
    {n : ℕ} {a : Fin n → ℕ} {N : ℕ}
    (h_sum : ∑ k, a k = N) (hN : 0 < N)
    (i : Fin n) (j : Fin (a i)) :
    (uniformDist
       (α := Σ k, Fin (a k))
       (by simpa [Fintype.card_sigma, Fintype.card_fin, h_sum] using hN)) ⟨i, j⟩
      = (N : NNReal)⁻¹ := by
  simp [uniformDist, h_sum]

/-- **(C)** Cancelling the `m` in front. -/
@[simp] lemma rational_factor_cancel {m N : ℕ} (hm : 0 < m) (hN : 0 < N) :
    ((m : NNReal) / N) * (m : NNReal)⁻¹ = (N : NNReal)⁻¹ := by
  have m_ne_zero : (m : NNReal) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have N_ne_zero : (N : NNReal) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  -- Use field_simp with the non-zero hypotheses.
  -- This should simplify expressions involving division and inverses.
  field_simp [m_ne_zero, N_ne_zero]
  -- If field_simp leaves a goal that is true by associativity and/or commutativity
  -- (e.g., X * Y = Y * X), ac_rfl can solve it.
  -- NNReal multiplication is associative and commutative.
  ac_rfl
-- In EGPT.Entropy.RET.lean (or Dev.lean)


/-! ### New point-wise helper ------------------------------------------ -/

/-- Point-wise value of P_cond_sigma_def_core when the size is `k.succ`. -/
@[simp] lemma P_cond_sigma_def_core_apply_succ
    {k : ℕ} {j : Fin (k.succ)} :
    P_cond_sigma_def_core (k.succ) j = ((k.succ : NNReal)⁻¹) := by
  simp [P_cond_sigma_def_core, uniformDist, Fintype.card_fin]

-- The new micro-lemma:
lemma LHS_eval_when_ai_is_succ (N_den k : ℕ) (j_val : Fin (k.succ)) (h_N_den_pos_lemma : N_den > 0) :
    (↑(k.succ) / ↑N_den : NNReal) * P_cond_sigma_def_core (k.succ) j_val = (N_den : NNReal)⁻¹ := by
  rw [P_cond_sigma_def_core_apply_succ (k := k) (j := j_val)]
  have hk_succ_pos_lemma : 0 < k.succ := Nat.succ_pos k
  exact rational_factor_cancel hk_succ_pos_lemma h_N_den_pos_lemma

/--
Rota’s marginal distribution `P_rat` together with the conditional
distributions `P_cond_sigma_def` yields the uniform distribution on
`Σ i : Fin n, Fin (a i)`.
-/
lemma P_joint_sigma_is_uniform_for_rota
    {n : ℕ}
    (a : Fin n → ℕ) (N_den : ℕ)
    (h_sum_a_eq_N : ∑ k, a k = N_den) (hN_den_pos : N_den > 0)
    (P_rat : Fin n → NNReal)
    (hP_rat_def :
      P_rat = create_rational_dist n a N_den h_sum_a_eq_N hN_den_pos) :
  DependentPairDistSigma P_rat a (P_cond_sigma_def a) =
    uniformDist
      (α := Σ i : Fin n, Fin (a i))
      (by
        simpa [Fintype.card_sigma, Fintype.card_fin, h_sum_a_eq_N]
          using hN_den_pos) := by
  -- 1.  Point-wise equality
  funext x
  rcases x with ⟨i, j⟩

  -- 2.  Expand definitions of the LHS's main components
  dsimp [DependentPairDistSigma, P_cond_sigma_def]
  simp_rw [hP_rat_def, create_rational_dist]
  -- LHS: ↑(a i) / ↑N_den * P_cond_sigma_def_core (a i) j

  -- 3.  Simplify the RHS to (N_den)⁻¹ using the helper
  conv_rhs =>
    rw [uniform_sigma_eval h_sum_a_eq_N hN_den_pos i j]
  -- Goal: ↑(a i) / ↑N_den * P_cond_sigma_def_core (a i) j = (N_den)⁻¹

  -- 4.  Since `j : Fin (a i)` exists, `a i` must be positive.
  --     So, `a i = k.succ` for some `k`.
  have hai_pos : 0 < a i := Fin.pos j
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hai_pos) with ⟨k, hk_eq_succ_ai⟩
  -- hk_eq_succ_ai : a i = k.succ

  -- 5.  Show that the LHS of the current goal is equal to the LHS of the micro-lemma,
  --     then use the micro-lemma.
  --     We use `hk_eq_succ_ai` to rewrite `a i` instances.
  --     The term `j : Fin (a i)` needs to be related to `j_val : Fin (k.succ)`.
  --     `Eq.subst` allows substituting along an equality and handles dependent types.
  --     Alternatively, `Fin.cast` can be used.

  -- Rewrite the LHS of the goal using hk_eq_succ_ai.
  -- `Eq.subst hk_eq_succ_ai (λ val => ...)` allows us to substitute `a i` with `k.succ`
  -- inside the expression, and `j` will be correctly typed for the new `val`.
  revert j -- Temporarily remove j from the context to make the substitution cleaner
  rw [hk_eq_succ_ai] -- Now `a i` is `k.succ` in the type of what `j` would be
  intro j -- Reintroduce j, now its type is Fin (k.succ)

  -- Now the goal is: ↑(k.succ) / ↑N_den * P_cond_sigma_def_core (k.succ) j = (N_den)⁻¹
  -- This matches the micro-lemma directly.
  exact LHS_eval_when_ai_is_succ N_den k j hN_den_pos

/--
`H_func` applied to the joint distribution `DependentPairDistSigma P_rat a (P_cond_sigma_def a)`
is `f0 hH_axioms N_den`.
This means H_func of (uniform on Σ type of card N_den) equals H_func of (uniform on Fin N_den).
-/
lemma H_P_joint_sigma_for_rota_eq_f0_N_den {n : ℕ} [NeZero n]
    (H_func : ∀ {α_aux : Type} [Fintype α_aux], (α_aux → NNReal) → NNReal)
    (hH_axioms : HasRotaEntropyProperties H_func)
    (a : Fin n → ℕ) (N_den : ℕ)
    (h_sum_a_eq_N : ∑ k, a k = N_den) (hN_den_pos : N_den > 0)
    (P_rat : Fin n → NNReal) (hP_rat_def : P_rat = create_rational_dist n a N_den h_sum_a_eq_N hN_den_pos) :
    H_func (DependentPairDistSigma P_rat a (P_cond_sigma_def a)) =
      f0 hH_axioms N_den := by

  -- 1. Rewrite the argument of H_func on the LHS
  rw [P_joint_sigma_is_uniform_for_rota a N_den h_sum_a_eq_N hN_den_pos P_rat hP_rat_def]
  -- LHS is now: H_func (uniformDist (α := (Σ i, Fin (a i))) ...)

  -- 2. Unfold f0 and f on the RHS
  rw [f0, dif_pos hN_den_pos, f]
  -- RHS is now: H_func (uniformDist (α := Fin N_den) ...)

  -- Define the Sigma type for brevity
  let SigmaType := (Σ i : Fin n, Fin (a i))

  -- Define the uniform distributions
  let U_sigma_domain_card_pos : 0 < Fintype.card SigmaType := by
    rw [Fintype.card_sigma]    -- Converts Fintype.card (Σ i, Fin (a i)) to ∑ i, Fintype.card (Fin (a i))
    simp_rw [Fintype.card_fin] -- Converts ∑ i, Fintype.card (Fin (a i)) to ∑ i, (a i)
    rw [h_sum_a_eq_N]          -- Converts ∑ i, (a i) to N_den
    exact hN_den_pos           -- Asserts 0 < N_den, which is given by hN_den_pos
  -- Removed: let U_sigma := uniformDist U_sigma_domain_card_pos

  let U_fin_Nden_domain_card_pos : 0 < Fintype.card (Fin N_den) := by
    simp only [Fintype.card_fin]
    exact hN_den_pos
  -- Removed: let U_fin_Nden := uniformDist U_fin_Nden_domain_card_pos

  -- Goal is now: H_func (uniformDist U_sigma_domain_card_pos) = H_func (uniformDist U_fin_Nden_domain_card_pos)

  -- The equivalence:
  let e_sigma_to_card_sigma : SigmaType ≃ Fin (Fintype.card SigmaType) :=
    Fintype.equivFin SigmaType

  have h_card_sigma_eq_N_den : Fintype.card SigmaType = N_den := by
    rw [Fintype.card_sigma]
    simp_rw [Fintype.card_fin]
    rw [h_sum_a_eq_N]
    -- Implicit rfl here as goal becomes N_den = N_den

  let e_sigma_to_fin_Nden : SigmaType ≃ Fin N_den :=
    e_sigma_to_card_sigma.trans (Equiv.cast (congrArg Fin h_card_sigma_eq_N_den))

  -- Prove that (uniformDist U_sigma_domain_card_pos) = (uniformDist U_fin_Nden_domain_card_pos) ∘ e_sigma_to_fin_Nden
  have h_dist_equality_with_comp :
      (uniformDist U_sigma_domain_card_pos) = (uniformDist U_fin_Nden_domain_card_pos) ∘ e_sigma_to_fin_Nden := by
    funext x_s
    simp_rw [uniformDist, comp_apply]
    -- LHS after simp: (↑(Fintype.card SigmaType))⁻¹
    -- RHS after simp: (↑(Fintype.card (Fin N_den)))⁻¹
    apply inv_inj.mpr
    apply Nat.cast_inj.mpr
    rw [h_card_sigma_eq_N_den] -- Converts Fintype.card SigmaType to N_den
    rw [Fintype.card_fin]      -- Converts Fintype.card (Fin N_den) to N_den

  -- Rewrite the LHS of the main goal
  rw [h_dist_equality_with_comp]
  -- Goal is now: H_func ((uniformDist U_fin_Nden_domain_card_pos) ∘ e_sigma_to_fin_Nden) = H_func (uniformDist U_fin_Nden_domain_card_pos)

  -- Apply symmetry axiom
  let P_target_dist := uniformDist U_fin_Nden_domain_card_pos
  have h_sum_P_target_dist_eq_1 : ∑ y, P_target_dist y = 1 :=
    sum_uniformDist U_fin_Nden_domain_card_pos

  exact hH_axioms.symmetry P_target_dist h_sum_P_target_dist_eq_1 e_sigma_to_fin_Nden

/--
Rota's intermediate formula for rational probabilities:
`H(P_rat) = f0(N_den) - ∑ (P_rat i) * f0(a i)`
This is derived from the generalized conditional additivity axiom.
-/
lemma rota_rational_intermediate_formula {n : ℕ} [h_n_ne_zero : NeZero n]
    (H_func : ∀ {α_aux : Type} [Fintype α_aux], (α_aux → NNReal) → NNReal) -- Changed Type u to Type
    (hH_axioms : HasRotaEntropyProperties H_func)
    (a : Fin n → ℕ) (N_den : ℕ)
    (h_sum_a_eq_N : ∑ k, a k = N_den) (hN_den_pos : N_den > 0)
    (P_rat_param : Fin n → NNReal) (hP_rat_def : P_rat_param = create_rational_dist n a N_den h_sum_a_eq_N hN_den_pos) : -- Renamed P_rat to P_rat_param to avoid clash with let
    (H_func P_rat_param : ℝ) = (f0 hH_axioms N_den : ℝ) - ∑ i : Fin n, (P_rat_param i : ℝ) * (f0 hH_axioms (a i) : ℝ) := by

  -- Define the components for cond_add_sigma
  let P_prior_fn := P_rat_param -- P_rat_param is the input parameter
  let M_map_fn := a
  let P_cond_fn (i_idx : Fin n) := P_cond_sigma_def a i_idx

  -- Premise 1: Sum of prior probabilities is 1
  have hprior_sum_1 : ∑ i, P_prior_fn i = 1 := by
    dsimp [P_prior_fn] -- Crucial: unfolds P_prior_fn to P_rat_param
    rw [hP_rat_def]
    exact sum_create_rational_dist_eq_one n a N_den h_sum_a_eq_N hN_den_pos

  -- Premise 2: Properties of conditional distributions when prior is positive
  have hP_cond_props : ∀ i_idx : Fin n, P_prior_fn i_idx > 0 → (M_map_fn i_idx > 0 ∧ ∑ j, P_cond_fn i_idx j = 1) := by
    intro i_idx hP_prior_i_pos
    dsimp [P_prior_fn] at hP_prior_i_pos
    -- Derive positivity of `a i_idx` *once* so we can reuse it in both sub‑goals.
    have hai_pos : a i_idx > 0 := by
      -- unfold the definition of the prior probability at `i_idx`
      rw [hP_rat_def] at hP_prior_i_pos
      -- `create_rational_dist` is `(a i_idx : NNReal) / N_den`
      simp only [create_rational_dist] at hP_prior_i_pos
      -- Use positivity of the NNReal numerator
      have hnum_ne_zero : (a i_idx : NNReal) ≠ 0 := by
        have : (a i_idx : NNReal) / (N_den : NNReal) ≠ 0 :=
          ne_of_gt hP_prior_i_pos
        have hN_ne : (N_den : NNReal) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt hN_den_pos)
        simpa [hN_ne] using (div_ne_zero_iff.mp this).1
      have hnum_pos : 0 < (a i_idx : NNReal) := by
        have : (a i_idx : NNReal) ≥ 0 := zero_le _
        exact lt_of_le_of_ne this hnum_ne_zero.symm
      exact (by exact_mod_cast hnum_pos)

    constructor
    · exact hai_pos
    · exact sum_P_cond_sigma_def_eq_one_of_pos a i_idx hai_pos

  -- Premise 3: H_func of conditional distribution is 0 if M_map i is 0
  have hH_P_cond_M_map_zero :
    ∀ i_idx : Fin n,
      M_map_fn i_idx = 0 →
      H_func (P_cond_fn i_idx) = 0 := by
    intro i_idx h_M_map_fn_i_idx_eq_zero
    -- Unfold P_cond_fn to expose P_cond_sigma_def
    dsimp only [P_cond_fn]
    -- Rewrite H_func application using H_func_P_cond_sigma_def_eq_f0
    -- hH_axioms.toIsEntropyZeroOnEmptyDomain provides the required IsEntropyZeroOnEmptyDomain instance
    rw [H_func_P_cond_sigma_def_eq_f0 H_func hH_axioms a i_idx (h0 := hH_axioms.toIsEntropyZeroOnEmptyDomain)]
    -- Goal is now: f0 hH_axioms (a i_idx) = 0
    -- Use the fact that M_map_fn i_idx = 0 implies a i_idx = 0
    have h_ai_eq_zero : a i_idx = 0 := by
      simpa [M_map_fn] using h_M_map_fn_i_idx_eq_zero
    rw [h_ai_eq_zero]
    -- Goal is now: f0 hH_axioms 0 = 0
    -- Simplify f0 hH_axioms 0, which is 0 by definition of f0
    simp [f0]

  -- Apply IsEntropyCondAddSigma.cond_add_sigma
  have h_cond_add_nnreal_stmt := hH_axioms.cond_add_sigma
    P_prior_fn M_map_fn P_cond_fn
    hprior_sum_1 hP_cond_props hH_P_cond_M_map_zero

  -- Substitute known values into h_cond_add_nnreal_stmt (NNReal equation)
  rw [H_P_joint_sigma_for_rota_eq_f0_N_den H_func hH_axioms a N_den h_sum_a_eq_N hN_den_pos P_rat_param hP_rat_def] at h_cond_add_nnreal_stmt
  -- Unfold P_cond_fn and rewrite H_func(P_cond_fn i) to f0 hH_axioms (a i)
  -- P_cond_fn i is P_cond_sigma_def a i
  -- H_func_P_cond_sigma_def_eq_f0 requires h0, which is hH_axioms.toIsEntropyZeroOnEmptyDomain
  simp_rw [P_cond_fn, fun i => H_func_P_cond_sigma_def_eq_f0 H_func hH_axioms a i (h0 := hH_axioms.toIsEntropyZeroOnEmptyDomain)] at h_cond_add_nnreal_stmt
  -- h_cond_add_nnreal_stmt is now:
  -- f0 hH_axioms N_den = H_func P_prior_fn + ∑ (i : Fin n), P_prior_fn i * f0 hH_axioms (a i)

  -- Coerce to Real and rearrange
  rw [eq_sub_iff_add_eq']
  -- The goal is now of the form `TermC + TermA = TermB`
  -- TermA = (↑(H_func P_rat_param) : ℝ)
  -- TermC = (∑ i, (↑(P_rat_param i) : ℝ) * (↑(f0 hH_axioms (a i)) : ℝ))
  -- TermB = (↑(f0 hH_axioms N_den) : ℝ)
  -- The tactic state shows TermC + TermA = TermB.
  calc
    (∑ i, (↑(P_rat_param i) : ℝ) * (↑(f0 hH_axioms (a i)) : ℝ)) + (↑(H_func P_rat_param) : ℝ)
    -- Step 1: Reorder terms to group H_func P_rat_param with the sum for NNReal operations
    _ = (↑(H_func P_rat_param) : ℝ) + (∑ i, (↑(P_rat_param i) : ℝ) * (↑(f0 hH_axioms (a i)) : ℝ)) := by rw [add_comm]
    -- Step 2: Move NNReal.coe outside of the product in each term of the sum
    _ = (↑(H_func P_rat_param) : ℝ) + (∑ i, (↑(P_rat_param i * f0 hH_axioms (a i)) : ℝ)) := by simp_rw [NNReal.coe_mul]
    -- Step 3: Move NNReal.coe outside of the sum
    _ = (↑(H_func P_rat_param) : ℝ) + (↑(∑ i, P_rat_param i * f0 hH_axioms (a i)) : ℝ) := by rw [NNReal.coe_sum]
    -- Step 4: Move NNReal.coe outside of the addition
    _ = (↑( (H_func P_rat_param) + (∑ i, P_rat_param i * f0 hH_axioms (a i)) ) : ℝ) := by rw [NNReal.coe_add]
    -- Step 5: Use the h_cond_add_nnreal_stmt (which is in NNReal)
    -- h_cond_add_nnreal_stmt is: f0 hH_axioms N_den = H_func P_prior_fn + ∑ x, P_prior_fn x * f0 hH_axioms (a x)
    -- P_prior_fn is definitionally P_rat_param.
    _ = (↑(f0 hH_axioms N_den) : ℝ) := by rw [← h_cond_add_nnreal_stmt]


/-! ### Micro helpers for shannon_entropy_rational_identity ------------------------------------------------- -/
--Replaces the missing theorem from Mathlib3 which is no longer available in Mathlib4.
@[simp] lemma Real.log_inv_eq_neg_log {x : ℝ} (_hx : 0 < x) :
    Real.log (x⁻¹) = -Real.log x := by
  -- Use the properties of logarithms
  simp [Real.log_inv]
/--
(A)  Expand `negMulLog x_nnreal` into the `if x_nnreal = 0 then 0 else x_nnreal * log (1/x_nnreal)` form.
     Handles the `x_nnreal > 0` condition for `log (1/x_nnreal) = -log x_nnreal`.
-/
@[simp] lemma negMulLog_to_mul_log_one_div {x_nnreal : NNReal} :
    (negMulLog (x_nnreal : ℝ)) =
      (if (x_nnreal : ℝ) = 0 then 0 else (x_nnreal : ℝ) * Real.log (1 / (x_nnreal : ℝ))) := by
  -- Use the definition of negMulLog
  rw [negMulLog_def] -- LHS becomes: if (x_nnreal:ℝ) = 0 then 0 else -(x_nnreal:ℝ) * Real.log (x_nnreal:ℝ)
  -- Now, prove equality by cases on (x_nnreal : ℝ) = 0
  split_ifs with h_coe_is_zero
  · -- Case: (x_nnreal : ℝ) = 0. After split_ifs, both sides simplify to 0.
    -- Goal should be 0 = 0. If not immediately, simp will make it so.
    simp [h_coe_is_zero]
  · -- Case: (x_nnreal : ℝ) ≠ 0.
    -- Goal: -(x_nnreal:ℝ) * Real.log (x_nnreal:ℝ) = (x_nnreal:ℝ) * Real.log (1 / (x_nnreal:ℝ))
    -- Since x_nnreal : NNReal and (x_nnreal : ℝ) ≠ 0, we have (x_nnreal : ℝ) > 0
    have h_coe_pos : (x_nnreal : ℝ) > 0 := by
      apply lt_of_le_of_ne (NNReal.coe_nonneg x_nnreal)
      exact Ne.symm h_coe_is_zero -- Use Ne.symm explicitly
    -- Use Real.log_inv_eq_neg_log (available as log_inv_eq_neg_log in EGPT.Basic),
    -- which states log (x⁻¹) = -log x for x > 0.
    -- 1 / x_nnreal is x_nnreal⁻¹
    rw [one_div] -- Change 1 / ↑x_nnreal to (↑x_nnreal)⁻¹
    rw [Real.log_inv_eq_neg_log h_coe_pos]
    -- Goal: -(x_nnreal:ℝ) * Real.log (x_nnreal:ℝ) = (x_nnreal:ℝ) * (-Real.log (x_nnreal:ℝ))
    simp [mul_neg]
    -- Goal: -(x_nnreal:ℝ) * Real.log (x_nnreal:ℝ) = -((x_nnreal:ℝ) * Real.log (x_nnreal:ℝ))
    -- This is true by reflexivity


/--
(B) For `P_rat i = (a i / N_den)`, if `P_rat i ≠ 0` (which implies `a i > 0`),
    then `log (1 / (P_rat i : ℝ))` simplifies to `log N_den - log (a i)`.
    Requires `N_den > 0`.
-/
lemma log_one_div_P_rat_to_log_N_den_sub_log_a_i
    {n : ℕ} (a : Fin n → ℕ) (N_den : ℕ) (i : Fin n) (P_rat_i : NNReal)
    (h_P_rat_i_def_val : P_rat_i = (a i : NNReal) / (N_den : NNReal)) -- Definition for specific i
    (h_P_rat_i_ne_zero : (P_rat_i : ℝ) ≠ 0)
    (h_N_den_pos : N_den > 0) :
    Real.log (1 / (P_rat_i : ℝ)) = Real.log N_den - Real.log (a i : ℝ) := by
  -- From h_P_rat_i_ne_zero and P_rat_i being NNReal, we have (P_rat_i : ℝ) > 0
  have h_P_rat_i_pos_real : (P_rat_i : ℝ) > 0 :=
    lt_of_le_of_ne (NNReal.coe_nonneg P_rat_i) h_P_rat_i_ne_zero.symm

  -- From P_rat_i ≠ 0 and its definition, deduce a i > 0
  have h_a_i_pos_nat : a i > 0 := by
    have h_P_rat_i_ne_zero_nnreal : P_rat_i ≠ 0 := NNReal.coe_ne_zero.mp h_P_rat_i_ne_zero
    rw [h_P_rat_i_def_val] at h_P_rat_i_ne_zero_nnreal
    have h_N_den_nnreal_ne_zero : (N_den : NNReal) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt h_N_den_pos)
    rw [div_ne_zero_iff] at h_P_rat_i_ne_zero_nnreal
    -- h_prat_i_ne_zero_nnreal is now (a i:NNReal) ≠ 0 ∧ (N_den:NNReal) ≠ 0
    exact Nat.pos_of_ne_zero (NNReal.coe_nat_ne_zero_iff_ne_zero.mp h_P_rat_i_ne_zero_nnreal.left)

  have h_a_i_pos_real : (a i : ℝ) > 0 := Nat.cast_pos.mpr h_a_i_pos_nat
  have h_N_den_pos_real : (N_den : ℝ) > 0 := Nat.cast_pos.mpr h_N_den_pos

  -- Substitute P_rat_i definition into the log expression
  simp only [h_P_rat_i_def_val, NNReal.coe_div, NNReal.coe_natCast]
  -- Expected Goal after simp: Real.log (1 / (↑(a i) / ↑N_den)) = Real.log ↑N_den - Real.log ↑(a i)

  -- Explicitly state the non-zero hypotheses for the terms in the fraction
  have h_num_ne_zero : (↑(a i) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h_a_i_pos_nat)
  have h_den_ne_zero : (↑N_den : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h_N_den_pos)

  -- State the specific instance of one_div_div we want to use
  have key_rewrite : 1 / ( (↑(a i) : ℝ) / (↑N_den : ℝ) ) = (↑N_den : ℝ) / (↑(a i) : ℝ) := by
    -- Apply one_div_div with explicit terms.
    -- The non-zero proofs h_num_ne_zero and h_den_ne_zero are used by the tactics within one_div_div's proof.
    exact one_div_div (↑(a i) : ℝ) (↑N_den : ℝ)

  -- Rewrite the argument of Real.log using our specific lemma
  rw [key_rewrite]
  -- Goal: Real.log (↑N_den / ↑(a i)) = Real.log ↑N_den - Real.log ↑(a i)
  apply Real.log_div
  · -- Assuming the goal here is (↑N_den : ℝ) ≠ 0, convert h_N_den_pos_real
    exact ne_of_gt h_N_den_pos_real
  · -- Assuming the goal here is (↑(a i) : ℝ) ≠ 0, convert h_a_i_pos_real
    exact ne_of_gt h_a_i_pos_real

lemma P_rat_i_coe_zero_iff_a_i_zero {n : ℕ} (a : Fin n → ℕ) (N_den : ℕ) (i : Fin n) (P_rat_i : NNReal)
    (h_P_rat_i_def_val : P_rat_i = (a i : NNReal) / (N_den : NNReal))
    (h_N_den_pos : N_den > 0) :
    (P_rat_i : ℝ) = 0 ↔ a i = 0 := by
  constructor
  · intro h
    -- Coerce `(P_rat_i : ℝ) = 0` back to `NNReal`
    have hNN : P_rat_i = 0 := NNReal.coe_eq_zero.mp h
    -- Substitute definition and clear denominator
    rw [h_P_rat_i_def_val] at hNN
    have hN : (N_den : NNReal) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h_N_den_pos)
    simpa [hN] using div_eq_zero_iff.1 hNN
  · intro ha
    -- `simp` handles nat-casts, `NNReal.coe_zero`, and `zero_div`
    simp [h_P_rat_i_def_val, ha]

/--
(D)  Factoring a constant `C` out of a sum with an `if` condition.
     `∑ i, (if cond i then 0 else term_i * C) = (∑ i, (if cond i then 0 else term_i)) * C`
-/
lemma sum_ite_mul_const_right {α : Type*} [Fintype α] {β : Type*} [CommSemiring β]
    (P_fn : α → β) (C : β) (cond_fn : α → Prop) [DecidablePred cond_fn] :
    (∑ i, (if cond_fn i then 0 else P_fn i * C)) =
    (∑ i, (if cond_fn i then 0 else P_fn i)) * C := by
  calc
    (∑ i, (if cond_fn i then 0 else P_fn i * C))
    _ = ∑ i, (if cond_fn i then 0 * C else P_fn i * C) := by
        apply Finset.sum_congr rfl; intro i _; by_cases h_cond : cond_fn i <;> simp [h_cond]
    _ = ∑ i, (if cond_fn i then 0 else P_fn i) * C := by
        -- Need to show (if cond then A else B) * C = (if cond then A*C else B*C)
        -- This is `ite_mul_right C (cond_fn i) 0 (P_fn i)` (if P_fn i is non-zero)
        -- Or more generally, `(ite c t e) * m = ite c (t*m) (e*m)`
        simp [ite_mul] -- General: (if c then t else e) * C = if c then t*C else e*C
    _ = (∑ i, (if cond_fn i then 0 else P_fn i)) * C := by
        rw [Finset.sum_mul]

/-- Main identity: rational‐distribution Shannon entropy --/
lemma shannon_entropy_rational_identity {n : ℕ} [NeZero n]
    (a : Fin n → ℕ) (N_den : ℕ)
    (h_sum : ∑ i, a i = N_den) (hN : 0 < N_den)
    (P : Fin n → NNReal)
    (hP_def : P = create_rational_dist n a N_den h_sum hN) : -- Renamed hP to hP_def
    stdShannonEntropyLn P =
      Real.log N_den
        - ∑ i, if a i = 0 then 0 else (P i : ℝ) * Real.log (a i : ℝ) := by

  -- 1. Unfold entropy and expand negMulLog using micro-lemma (A)
  simp_rw [stdShannonEntropyLn, negMulLog_to_mul_log_one_div]
  -- Goal: ∑ i, (if (P i:ℝ)=0 then 0 else (P i:ℝ)*log(1/(P i:ℝ))) = log N_den - ...

  -- 2. Replace `log (1/(P i:ℝ))` by `log N_den - log (a i:ℝ)` using micro-lemma (B)
  --    This applies only when (P i : ℝ) ≠ 0.
  have step2_sum_eq :
      ∑ i, (if (P i : ℝ) = 0 then 0 else (P i : ℝ) * Real.log (1 / (P i : ℝ)))
    = ∑ i, (if (P i : ℝ) = 0 then 0 else (P i : ℝ) * (Real.log N_den - Real.log (a i : ℝ))) := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs with h_Pi_zero -- Condition: (P i : ℝ) = 0
      · rfl -- if true, 0 = 0
      · -- if false, (P i : ℝ) ≠ 0. Apply congr_arg to factor out (P i : ℝ)
        apply congr_arg ((P i : ℝ) * ·)
        -- Goal: Real.log (1 / (P i : ℝ)) = Real.log N_den - Real.log (a i : ℝ)
        exact log_one_div_P_rat_to_log_N_den_sub_log_a_i a N_den i (P i) (by rw [hP_def]; rfl) h_Pi_zero hN

  rw [step2_sum_eq]
  -- Goal: ∑ i, (if (P i:ℝ)=0 then 0 else (P i:ℝ)*(Real.log N_den - Real.log (a i:ℝ))) = log N_den - ...

  -- 3. Distribute subtraction over sum.
  --    First, show that each term in the sum can be written as a difference:
  --    (if Pᵢ=0 then 0 else 0)  =  (if Pᵢ=0 then 0 else Pᵢ*logN) - (if Pᵢ=0 then 0 else Pᵢ*logAᵢ)
  have h_term_sub_distrib (i : Fin n) :
      (if (P i : ℝ) = 0 then 0 else (P i : ℝ) * (Real.log N_den - Real.log (a i : ℝ))) =
      ((if (P i : ℝ) = 0 then 0 else (P i : ℝ) * Real.log N_den) -
       (if (P i : ℝ) = 0 then 0 else (P i : ℝ) * Real.log (a i : ℝ))) := by
    split_ifs with h_Pi_zero
    · simp -- if true, 0 = 0 - 0
    · simp [mul_sub] -- if false, P_i*(logN - log_ai) = P_i*logN - P_i*log_ai

  -- Apply this per-term equality to the sum on the LHS of the goal
  simp_rw [h_term_sub_distrib]
  -- Now the LHS of the goal is in the form: ∑ i, (Aᵢ - Bᵢ)
  -- So we can apply Finset.sum_sub_distrib

  rw [Finset.sum_sub_distrib]
  -- Goal: (∑ i, if (P i:ℝ)=0 then 0 else (P i:ℝ)*Real.log N_den) - (∑ i, if (P i:ℝ)=0 then 0 else (P i:ℝ)*Real.log (a i:ℝ)) = log N_den - ...

  -- 4. Simplify the first sum term using micro-lemma (D) and sum P i = 1
  have h_first_sum_eq_log_Nden :
      (∑ i, (if (P i : ℝ) = 0 then 0 else (P i : ℝ) * Real.log N_den)) = Real.log N_den := by
    rw [sum_ite_mul_const_right (fun i => (P i : ℝ)) (Real.log N_den) (fun i => (P i : ℝ) = 0)]
    -- Goal: (∑ i, (if (P i : ℝ) = 0 then 0 else (P i : ℝ))) * Real.log N_den = Real.log N_den
    have h_sum_if_P_rat_eq_sum_P_rat :
        (∑ (i : Fin n), if (P i : ℝ) = 0 then 0 else (P i : ℝ)) = (∑ (i : Fin n), (P i : ℝ)) := by
      apply Finset.sum_congr rfl; intro i _;
      by_cases h_prat_i_zero : (P i : ℝ) = 0 <;> simp [h_prat_i_zero]
    rw [h_sum_if_P_rat_eq_sum_P_rat]
    have sumP_eq_1 : ∑ i, (P i : ℝ) = 1 := by
      rw [← NNReal.coe_sum, hP_def, sum_create_rational_dist_eq_one n a N_den h_sum hN, NNReal.coe_one]
    rw [sumP_eq_1, one_mul]
  rw [h_first_sum_eq_log_Nden]
  -- Goal: Real.log N_den - (∑ i, if (P i:ℝ)=0 then 0 else (P i:ℝ)*log (a i:ℝ)) = Real.log N_den - ...

  -- 5. The second sum term needs its `if` condition changed using micro-lemma (C)
  apply congr_arg (Real.log N_den - ·) -- Focus on proving the sums are equal
  apply Finset.sum_congr rfl; intro i _;
  have h_cond_equiv : ((P i : ℝ) = 0) ↔ (a i = 0) := by
    apply P_rat_i_coe_zero_iff_a_i_zero a N_den i (P i)
    · -- Prove P i = (a i : NNReal) / (N_den : NNReal)
      -- hP_def expands P. create_rational_dist_val shows the definition of (P i)
      -- which is definitionally (a i : NNReal) / (N_den : NNReal).
      rw [hP_def]; rfl
    · exact hN
  -- Rewrite the condition of the if statement on the left-hand side of the per-term goal
  -- (if (P i : ℝ) = 0 then 0 else (P i : ℝ) * Real.log (a i : ℝ)) =
  -- (if a i = 0 then 0 else (P i : ℝ) * Real.log (a i : ℝ))
  -- using the equivalence.
  simp [h_cond_equiv]
  -- Now both sides are syntactically identical:
  -- (if a i = 0 then 0 else (P i : ℝ) * Real.log (a i : ℝ)) =
  -- (if a i = 0 then 0 else (P i : ℝ) * Real.log (a i : ℝ))


/--
(E) Relates `(f0 hH_axioms (a i) : ℝ)` to `C_const * Real.log (a i : ℝ)` using `RotaUniformTheorem`.
    Handles the `a i = 0` case where `f0` is 0.
-/
lemma f0_ai_to_C_log_ai {H_func : ∀ {α_aux : Type} [Fintype α_aux], (α_aux → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyProperties H_func) (C_const : ℝ) (a_i_val : ℕ) (_i : Fin n) -- Added i for context if needed by RotaUniform
    (hC_def : C_const = C_constant_real hH_axioms) :
    (f0 hH_axioms a_i_val : ℝ) = if a_i_val = 0 then 0 else C_const * Real.log (a_i_val : ℝ) := by
  rw [hC_def] -- Substitute C_const definition if RotaUniformTheorem uses C_constant_real directly
  by_cases h_ai_zero : a_i_val = 0
  · -- Case: a i = 0
    rw [if_pos h_ai_zero] -- RHS is 0
    -- LHS: (f0 hH_axioms 0 : ℝ)
    simp [f0, h_ai_zero, NNReal.coe_zero] -- f0 hH_axioms 0 = 0, then coe to 0
  · -- Case: a i ≠ 0
    rw [if_neg h_ai_zero] -- RHS is C_const * Real.log (a i : ℝ)
    have h_ai_pos : a_i_val > 0 := Nat.pos_of_ne_zero h_ai_zero
    -- LHS is (f0 hH_axioms (a i) : ℝ). Apply RotaUniformTheorem.
    -- RotaUniformTheorem_formula_with_C_constant.right states:
    -- (f0 hH_axioms k : ℝ) = (C_constant_real hH_axioms) * Real.log k for k > 0
    rw [(RotaUniformTheorem_formula_with_C_constant hH_axioms).right a_i_val h_ai_pos]
    -- Now both sides should be definitionally (C_constant_real hH_axioms) * Real.log (a i : ℝ)
    -- if C_const was substituted by hC_def. If not, they are C_const * log (a i)
    -- if hC_def ensures C_const = C_constant_real hH_axioms.

/--
(F) Simplifies the sum `∑ i, P_rat i * (f0_ai_term)` using lemma (E).
    The sum becomes `∑ i, if a i = 0 then 0 else P_rat i * C_const * Real.log (a i)`.
-/
lemma sum_Prat_f0_ai_to_sum_Prat_C_log_ai {n : ℕ}
    {H_func : ∀ {α_aux : Type} [Fintype α_aux], (α_aux → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyProperties H_func) (C_const : ℝ)
    (a : Fin n → ℕ) (P_rat : Fin n → NNReal)
    (hC_def : C_const = C_constant_real hH_axioms) :
    (∑ i, (P_rat i : ℝ) * (f0 hH_axioms (a i) : ℝ)) =
    (∑ i, (if a i = 0 then 0 else (P_rat i : ℝ) * (C_const * Real.log (a i : ℝ)))) := by
  apply Finset.sum_congr rfl
  intro i _
  -- Per-term goal: (P_rat i : ℝ) * (f0 hH_axioms (a i) : ℝ) = if a i = 0 then 0 else (P_rat i : ℝ) * (C_const * Real.log (a i : ℝ))
  rw [f0_ai_to_C_log_ai hH_axioms C_const (a i) i hC_def]
  -- Goal: (P_rat i : ℝ) * (if a i = 0 then 0 else C_const * Real.log (a i : ℝ)) = ...
  -- This is ite_mul_left_distrib: x * (if c then t else e) = if c then x*t else x*e
  -- Here, x = (P_rat i : ℝ), c = (a i = 0), t = 0, e = C_const * Real.log (a i : ℝ)
  by_cases h_ai_zero : a i = 0
  · simp [h_ai_zero] -- if true, (P i)*0 = 0
  · simp [h_ai_zero] -- if false, (P i)*(C*log ai) = (P i)*(C*log ai)


/--
(G) Factors `C_const` out of the sum `∑ i, (if a i = 0 then 0 else P_rat i * C_const * Real.log (a i))`.
    Result: `C_const * (∑ i, (if a i = 0 then 0 else P_rat i * Real.log (a i)))`.
-/
lemma sum_Prat_C_log_ai_factor_C {n : ℕ} (C_const : ℝ)
    (a : Fin n → ℕ) (P_rat : Fin n → NNReal) :
    (∑ i, (if a i = 0 then 0 else (P_rat i : ℝ) * (C_const * Real.log (a i : ℝ)))) =
    C_const * (∑ i, (if a i = 0 then 0 else (P_rat i : ℝ) * Real.log (a i : ℝ))) := by
  calc
    (∑ i, (if a i = 0 then 0 else (P_rat i : ℝ) * (C_const * Real.log (a i : ℝ))))
    -- Step 1: Move C_const inside the product with P_rat i (or use mul_assoc)
    -- Term is: if a i = 0 then 0 else P_rat i * C_const * log (a i)
    -- This is fine, but we want to factor C_const out of the sum.
    _ = ∑ i, (if a i = 0 then 0 else C_const * ((P_rat i : ℝ) * Real.log (a i : ℝ))) := by
        apply Finset.sum_congr rfl; intro i _;
        by_cases h_ai_zero : a i = 0
        · -- Case: a i = 0
          simp [h_ai_zero] -- Simplifies both sides to 0 using the hypothesis a i = 0
        · -- Case: ¬(a i = 0)
          simp [h_ai_zero] -- Simplifies the 'if' using the hypothesis ¬(a i = 0)
          ac_rfl          -- Solves the remaining algebraic equality
    -- Step 2: Factor C_const out of the sum using Finset.sum_ite_const_mul
    -- The LHS of this step is the result of Step 1:
    --   ∑ i, (if a i = 0 then 0 else C_const * ((P_rat i : ℝ) * Real.log (a i : ℝ)))
    -- The RHS is the final form required by the lemma.
    _ = C_const * (∑ i, ite (a i = 0) 0 ((P_rat i : ℝ) * Real.log (a i : ℝ))) := by
      simp [Finset.mul_sum, mul_ite]   -- `mul_ite` is the `@[simp]` lemma `z * ite c x y = ite c (z*x) (z*y)`
    _ = C_const * (∑ i, (if a i = 0 then 0 else (P_rat i : ℝ) * Real.log (a i : ℝ))) := by
        rw [mul_comm]

/--
Rota's Uniqueness of Entropy theorem for distributions with rational probabilities.
States that `(H_func P_rat : ℝ) = C * stdShannonEntropyLn P_rat`.
-/
theorem RUE_rational_case {n : ℕ} [h_n_ne_zero : NeZero n]
    (H_func : ∀ {α_aux : Type } [Fintype α_aux], (α_aux → NNReal) → NNReal)
    (hH_axioms : HasRotaEntropyProperties H_func)
    (a : Fin n → ℕ) (N_den : ℕ)
    (h_sum_a_eq_N : ∑ i, a i = N_den) (hN_den_pos : N_den > 0) :
    let P_rat := create_rational_dist n a N_den h_sum_a_eq_N hN_den_pos
    (H_func P_rat : ℝ) = (C_constant_real hH_axioms) * stdShannonEntropyLn P_rat := by
  let P_rat_val := create_rational_dist n a N_den h_sum_a_eq_N hN_den_pos
  let C_const_val := C_constant_real hH_axioms

  -- LHS of main goal: (H_func P_rat_val : ℝ)
  calc
    (H_func P_rat_val : ℝ)
    -- Step 1: Apply rota_rational_intermediate_formula
    _ = (f0 hH_axioms N_den : ℝ) - ∑ i, (P_rat_val i : ℝ) * (f0 hH_axioms (a i) : ℝ) := by
        rw [rota_rational_intermediate_formula H_func hH_axioms a N_den h_sum_a_eq_N hN_den_pos P_rat_val rfl]

    -- Step 2: Substitute f0 N_den using RotaUniformTheorem
    _ = (C_const_val * Real.log N_den) - ∑ i, (P_rat_val i : ℝ) * (f0 hH_axioms (a i) : ℝ) := by
        rw [(RotaUniformTheorem_formula_with_C_constant hH_axioms).right N_den hN_den_pos]
        -- Ensure C_const_val is correctly used by RotaUniformTheorem
        -- This is implicitly handled if C_const_val := C_constant_real hH_axioms is used by the theorem.

    -- Step 3: Substitute the sum term using micro-lemma (F)
    _ = (C_const_val * Real.log N_den) - (∑ i, (if a i = 0 then 0 else (P_rat_val i : ℝ) * (C_const_val * Real.log (a i : ℝ)))) := by
        rw [congr_arg (C_const_val * Real.log N_den - ·)] -- Focus on the sum
        exact sum_Prat_f0_ai_to_sum_Prat_C_log_ai hH_axioms C_const_val a P_rat_val rfl

    -- Step 4: Factor C_const_val out of the sum using micro-lemma (G)
    _ = (C_const_val * Real.log N_den) - C_const_val * (∑ i, (if a i = 0 then 0 else (P_rat_val i : ℝ) * Real.log (a i : ℝ))) := by
        rw [congr_arg (C_const_val * Real.log N_den - ·)] -- Focus on the sum
        exact sum_Prat_C_log_ai_factor_C C_const_val a P_rat_val

    -- Step 5: Factor C_const_val out of the whole expression (C*X - C*Y = C*(X-Y))
    _ = C_const_val * (Real.log N_den - (∑ i, (if a i = 0 then 0 else (P_rat_val i : ℝ) * Real.log (a i : ℝ)))) := by
        rw [← mul_sub]

    -- Step 6: Use shannon_entropy_rational_identity for the term in parenthesis
    _ = C_const_val * stdShannonEntropyLn P_rat_val := by
        rw [congr_arg (C_const_val * ·)] -- Focus on the term being multiplied by C_const_val
        exact (shannon_entropy_rational_identity a N_den h_sum_a_eq_N hN_den_pos P_rat_val rfl).symm

theorem H_canonical_uniform_eq_C_shannon
    (H_func : ∀ {α_aux : Type} [Fintype α_aux], (α_aux → NNReal) → NNReal)
    (hH_axioms : HasRotaEntropyProperties H_func)
    (k : ℕ) (hk_pos : k > 0) :
    -- Removed 'let p_unif_k := canonicalUniformDist k hk_pos' from the statement
    (H_func (canonicalUniformDist k hk_pos) : ℝ) = (C_constant_real hH_axioms) * stdShannonEntropyLn (canonicalUniformDist k hk_pos) := by
  let p_unif_k := canonicalUniformDist k hk_pos

  -- Explicitly show that (H_func p_unif_k : ℝ) is equivalent to (f0 hH_axioms k : ℝ)
  have h_lhs_eq_f0_val : (H_func p_unif_k : ℝ) = (f0 hH_axioms k : ℝ) := by
    -- Unfold definitions to show both sides are definitionally equal to
    -- (H_func (uniformDist (Fintype_card_fin_pos hk_pos)) : ℝ)
    simp only [p_unif_k, canonicalUniformDist, uniformDist, Fintype_card_fin_pos,
               f0, f, dif_pos hk_pos]
    -- At this point, both sides should be identical after simp.

  -- Rewrite the LHS of the main goal using this equality
  rw [h_lhs_eq_f0_val]
  -- Now the goal is: (f0 hH_axioms k : ℝ) = (C_constant_real hH_axioms) * stdShannonEntropyLn p_unif_k

  -- Now use RotaUniformTheorem, which applies to (f0 hH_axioms k : ℝ)
  rw [(RotaUniformTheorem_formula_with_C_constant hH_axioms).right k hk_pos]
  -- Goal: C_constant_real hH_axioms * Real.log k = C_constant_real hH_axioms * stdShannonEntropyLn p_unif_k
  -- Need stdShannonEntropyLn p_unif_k = Real.log k
  rw [stdShannonEntropyLn_canonicalUniform_eq_log_k k hk_pos]
  -- Goal is now an identity: C * log k = C * log k

-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.
