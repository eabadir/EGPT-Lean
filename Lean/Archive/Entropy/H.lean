import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic -- `strictConcaveOn_log_Ioi`
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Algebra.Order.Ring.Basic -- for le_iff_sub_nonneg
import Archive.NumberTheory.Filter
import Archive.NumberTheory.Core -- For ParticlePath bijection with ℕ
import Archive.Complexity.SetRFL -- For the final, canonical NP-Completeness proofs
import Archive.Physics.PhotonicCA -- For the_system_has_equivalent_program
import Archive.Entropy.Common -- For rect_program_for_dist and ShannonEntropyOfDist
import Archive.Entropy.RET -- For the RET entropy function

open EGPT.Complexity EGPT.Constraints EGPT.Physics.PCA EGPT.Entropy.Common EGPT.NumberTheory.Filter EGPT.Complexity.SetRFL EGPT.NumberTheory.Core EGPT.Entropy.RET Real Finset

/-!
# Concrete Shannon Entropy — All 7 Rota Axioms Proven (`Entropy/H.lean`)

This file defines the concrete Shannon entropy function (`H_canonical_ln`,
base-e; `H_canonical_log2`, base-2) and proves that it satisfies all 7 axioms
from `HasRotaEntropyProperties` (defined in `Entropy/Common.lean`).

## Structure

Each `h_canonical_is_*` theorem converts what was an *axiom* (assumption) in
`RET.lean` into a *proven property* of the concrete Shannon entropy:

| Rota axiom (abstract)         | Proven theorem (concrete)               |
|-------------------------------|-----------------------------------------|
| `IsEntropyNormalized`         | `h_canonical_is_normalized`             |
| `IsEntropySymmetric`          | `h_canonical_is_symmetric`              |
| `IsEntropyZeroInvariance`     | `h_canonical_is_zero_invariance`        |
| `IsEntropyContinuous`         | `h_canonical_is_continuous`             |
| `IsEntropyCondAddSigma`       | `h_canonical_is_cond_add_sigma`         |
| `IsEntropyMaxUniform`         | `h_canonical_is_max_uniform`            |
| `IsEntropyZeroOnEmptyDomain`  | `h_canonical_is_zero_on_empty`          |

All 7 proofs are bundled into `TheCanonicalEntropyFunction_Ln`, an
`EntropyFunction` instance that packages the concrete function together with
its verified axioms. This bundle is the bridge from abstract axioms to
concrete construction: it is consumed by the modernized capstone theorem
`RET_All_Entropy_Is_Scaled_Shannon_Entropy` in `NumberTheory/Analysis.lean`,
where the "axioms" become fully proven foundations rather than assumptions.
-/

namespace EGPT.Entropy.H
-- ==================================================================
-- SECTION: The Canonical Entropy Function (H_shannon)
-- ==================================================================


/--
The canonical entropy function is the standard Shannon Entropy in **bits** (base 2).
This is the standard measure of information content.

This version replaces the previous `H_canonical` to align the base unit of
measurement, which makes the Rota constant `C` well-defined and provable.
-/
noncomputable def H_canonical {α : Type} [Fintype α] (p : α → NNReal) : NNReal :=
  -- stdShannonEntropyLn returns a Real. We convert it to NNReal.
  -- This is safe because entropy is always non-negative.
  --Real.toNNReal (stdShannonEntropyLn p)
    ((stdShannonEntropyLn p) / Real.log 2).toNNReal

/-- The canonical entropy function is the standard Shannon Entropy (base e). -/
noncomputable def H_canonical_ln {α : Type} [Fintype α] (p : α → NNReal) : NNReal :=
  -- stdShannonEntropyLn returns a Real. We convert it to NNReal.
  -- This is safe because entropy is always non-negative.
  Real.toNNReal (stdShannonEntropyLn p)

-- ==================================================================
-- SECTION: Proving H_canonical satisfies Rota's Axioms
-- ==================================================================

-- This is the helper lemma from the previous step, needed here.
lemma stdShannonEntropyLn_nonneg {α : Type*} [Fintype α] (p : α → NNReal) (hp_sum_1 : ∑ i, p i = 1) :
    0 ≤ stdShannonEntropyLn p := by
  -- stdShannonEntropyLn is defined as ∑ i : α, Real.negMulLog (p i : Real)
  -- We need to show this sum is nonnegative
  apply Finset.sum_nonneg
  intro i _
  -- For each term, we need to show negMulLog (p i : ℝ) ≥ 0
  -- negMulLog is nonnegative for all real numbers in [0,1]
  apply Real.negMulLog_nonneg
  · -- Show 0 ≤ (p i : ℝ)
    exact NNReal.coe_nonneg (p i)
  · -- Show (p i : ℝ) ≤ 1
    rw [← NNReal.coe_one, NNReal.coe_le_coe]
    -- Since ∑ j, p j = 1 and all p j ≥ 0, we have p i ≤ ∑ j, p j = 1
    calc p i
      ≤ ∑ j, p j := Finset.single_le_sum (fun j _ => zero_le (p j)) (Finset.mem_univ i)
      _ = 1 := hp_sum_1

-- We need to build the proofs for each axiom in HasRotaEntropyProperties.
-- Many of these are already theorems in Mathlib or our codebase.

-- Proof for IsEntropySymmetric
theorem h_canonical_is_symmetric : IsEntropySymmetric H_canonical_ln :=
  ⟨by
    intro α β _ _ p_target _ e
    -- Goal: H_canonical (fun x => p_target (e x)) = H_canonical p_target
    -- H_canonical is Real.toNNReal (stdShannonEntropyLn p)
    unfold H_canonical_ln
    -- Goal: (stdShannonEntropyLn (fun x => p_target (e x))).toNNReal = (stdShannonEntropyLn p_target).toNNReal
    congr 1
    -- Goal: stdShannonEntropyLn (fun x => p_target (e x)) = stdShannonEntropyLn p_target
    -- (fun x => p_target (e x)) is definitionally equal to (p_target ∘ e)
    show stdShannonEntropyLn (p_target ∘ e) = stdShannonEntropyLn p_target
    exact stdShannonEntropyLn_comp_equiv p_target e⟩

-- Proof for IsEntropyZeroOnEmptyDomain
theorem h_canonical_is_zero_on_empty : IsEntropyZeroOnEmptyDomain H_canonical_ln :=
  ⟨by
    -- Goal: H_canonical (Fin.elim0) = 0
    simp [H_canonical_ln, stdShannonEntropyLn, Finset.sum_empty]⟩

-- Proof for IsEntropyNormalized
theorem h_canonical_is_normalized : IsEntropyNormalized H_canonical_ln :=
  ⟨by
    intro p hp_sum_1
    -- Goal: H_canonical p = 0
    unfold H_canonical_ln
    -- Goal: (stdShannonEntropyLn p).toNNReal = 0
    -- For Fin 1, there's only one element (0 : Fin 1)
    -- Since ∑ i, p i = 1 and there's only one element, p 0 = 1
    have h_p_zero_eq_one : p 0 = 1 := by
      have : ∑ i : Fin 1, p i = p 0 := by
        -- For Fin 1, there's only one element (0 : Fin 1), so the sum is just that element
        -- This uses the fact that Finset.univ for Fin 1 contains only (0 : Fin 1)
        simp [Finset.sum_const, Finset.card_fin]
      rw [← this]
      exact hp_sum_1
    -- Since p is fully determined by p 0, we have p = λ _ => 1
    have h_p_eq_one : p = λ _ => 1 := by
      funext i
      rw [Fin.eq_zero i, h_p_zero_eq_one]
    rw [h_p_eq_one]
    -- Goal: (stdShannonEntropyLn (λ _ : Fin 1 => 1)).toNNReal = 0
    -- Use the fact that entropy of uniform distribution over singleton is 0
    simp [stdShannonEntropyLn, Real.negMulLog_one, Finset.sum_const, Finset.card_fin]⟩


-- The main theorem for this section.
theorem h_canonical_is_zero_invariance : IsEntropyZeroInvariance H_canonical_ln :=
  ⟨by
    -- Introduce the universally quantified variables.
    intro n p_orig hp_sum_1

    -- The goal is `let p_ext := ...; H_canonical p_ext = H_canonical p_orig`.
    -- We need to show the equality following the exact structure from IsEntropyZeroInvariance.
    -- Let's unfold H_canonical and work with the Real.toNNReal structure.
    simp only [H_canonical_ln]

    -- Goal: Real.toNNReal (stdShannonEntropyLn (let p_ext := ... in p_ext)) = Real.toNNReal (stdShannonEntropyLn p_orig)
    -- Since Real.toNNReal is injective on non-negative reals, and Shannon entropy is non-negative,
    -- it suffices to show the underlying Real values are equal.

    congr 1
    -- Goal: stdShannonEntropyLn (let p_ext := ... in p_ext) = stdShannonEntropyLn p_orig

    -- Simplify the let expression
    dsimp only
    -- Goal: stdShannonEntropyLn (fun i => if h_lt : i.val < n then p_orig (Fin.castLT i h_lt) else 0) = stdShannonEntropyLn p_orig

    -- This follows from the fact that adding a zero probability outcome doesn't change Shannon entropy
    -- Let's prove this by expanding the Shannon entropy definition and showing the sums are equal
    simp only [stdShannonEntropyLn]

    -- Use Fin.sum_univ_castSucc to split the left sum
    rw [Fin.sum_univ_castSucc]

    -- The last term (where i = Fin.last n) contributes 0 because the probability is 0
    have h_last_term_zero : Real.negMulLog ↑(if h_lt : (Fin.last n).val < n then p_orig (Fin.castLT (Fin.last n) h_lt) else 0) = 0 := by
      simp only [Fin.val_last, lt_irrefl, dif_neg, not_false_iff, NNReal.coe_zero, Real.negMulLog_zero]

    rw [h_last_term_zero, add_zero]

    -- Now we need to show the sum over Fin n is the same
    -- Goal: ∑ i : Fin n, Real.negMulLog ↑(if h_lt : i.castSucc.val < n then p_orig (Fin.castLT i.castSucc h_lt) else 0) = ∑ i : Fin n, Real.negMulLog ↑(p_orig i)

    apply Finset.sum_congr rfl
    intro i _

    -- For each i : Fin n, we have i.castSucc.val = i.val < n, so the condition is true
    have h_cond_true : i.castSucc.val < n := i.is_lt
    rw [dif_pos h_cond_true]

    -- Now we use the fact that Fin.castLT i.castSucc h_cond_true = i
    rw [Fin.castLT_castSucc]⟩


-- The main theorem for this section.
theorem h_canonical_is_continuous : IsEntropyContinuous H_canonical_ln :=
  -- To prove this, we must provide a proof for the `continuity` field of the structure.
  ⟨by
    -- Introduce all the universally quantified variables from the definition.
    intro α _inst_fintype p_center hp_sum_1 ε hε_pos

    -- The core of the proof is that `stdShannonEntropyLn` is a continuous function
    -- from the space of distributions (α → NNReal) to ℝ.
    have h_cont : Continuous (fun (p : α → NNReal) => stdShannonEntropyLn p) := by
      apply continuous_finset_sum (Finset.univ : Finset α)
      intro i _
      exact Real.continuous_negMulLog.comp (continuous_subtype_val.comp (continuous_apply i))

    -- Use the epsilon-delta property directly from the continuous function
    rw [Metric.continuous_iff] at h_cont
    specialize h_cont p_center ε hε_pos
    rcases h_cont with ⟨δ, hδ_pos, h_ball⟩

    use δ
    constructor
    · exact hδ_pos
    · intro q hq_sum_1 hq_dist
      -- Our goal is `|H_canonical q - H_canonical p_center| < ε`.

      -- First, establish that H_canonical p = stdShannonEntropyLn p (as real numbers)
      -- for any valid probability distribution p.
      have H_eq_std (p : α → NNReal) (hp_sum : ∑ i, p i = 1) : (H_canonical_ln p : ℝ) = stdShannonEntropyLn p := by
        simp [H_canonical_ln]
        -- After simp, the goal is `0 ≤ stdShannonEntropyLn p`
        -- We can prove this directly using our lemma
        exact stdShannonEntropyLn_nonneg p hp_sum


      -- Now we can rewrite the goal using our helper, providing the necessary proofs.
      rw [H_eq_std q hq_sum_1, H_eq_std p_center hp_sum_1]
      -- The goal is now `|stdShannonEntropyLn q - stdShannonEntropyLn p_center| < ε`.

      -- This is the conclusion of `h_ball`. We need to prove its premise.
      apply h_ball

      -- Show that our pointwise condition `∀ i, |↑(q i) - ↑(p_center i)| < δ`
      -- implies the distance condition `dist q p_center < δ`.
      rw [dist_pi_lt_iff hδ_pos]
      intro i
      -- The goal is `dist (q i) (p_center i) < δ`.
      -- The distance between `NNReal` numbers is the absolute difference of their `Real` coercions.
      rw [NNReal.dist_eq]
      exact hq_dist i⟩

/--
**Rota's Iron Law of Entropy: The product rule for `negMulLog`.**
This is the helper we need to prove the core identity needed to prove everything else. H(k)= H(p) + H(q) ALWAYS because Shannon Encoding IS THE LOG2 FUNCTION in discrete space.

Proves that `negMulLog(x*y) = y*negMulLog(x) + x*negMulLog(y)`.
This is the analogue of `log(xy) = logx + logy`.
-/
lemma negMulLog_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.negMulLog (x * y) = y * Real.negMulLog x + x * Real.negMulLog y := by
  have hxy : 0 < x * y := mul_pos hx hy
  -- Unfold the definition of negMulLog
  simp only [Real.negMulLog_def, hx.ne', hy.ne', hxy.ne']
  -- Use the logarithm product rule: log(x*y) = log(x) + log(y)
  rw [Real.log_mul hx.ne' hy.ne']
  -- The rest is algebra
  ring


/--
**Helper A: Sum over a Sigma type is a double sum.**
This lemma simply applies `Finset.sum_sigma` to our context, making the main
proof cleaner. `Finset.sum_sigma` states that `∑ x : (Σ i, τ i), f x` is equal to
`∑ i, ∑ j : τ i, f ⟨i, j⟩`.
-/
lemma sum_over_sigma_is_double_sum {N : ℕ} {M_map : Fin N → ℕ}
    (f : (Σ _i : Fin N, Fin (M_map _i)) → ℝ) :
    ∑ x, f x = ∑ i, ∑ j, f ⟨i, j⟩ := by
  -- The theorem Finset.sum_sigma is exactly what we need.
  -- We need to specify the finsets explicitly: Finset.univ for the outer sum
  -- and (fun i => Finset.univ) for the inner sums.
  exact Finset.sum_sigma Finset.univ (fun i => Finset.univ) f

/--
**Helper B: Equivalence of `negMulLog` sum and `stdShannonEntropyLn`.**
This lemma proves that `∑ i, negMulLog(p i)` is definitionally equivalent to
`stdShannonEntropyLn p`, which is defined using an `if/then` structure.
-/
lemma sum_negMulLog_eq_stdShannonEntropyLn {α : Type*} [Fintype α] (p : α → NNReal) :
    ∑ i, negMulLog (p i : ℝ) = stdShannonEntropyLn p := by
  -- Unfold the definition of stdShannonEntropyLn to expose the sum.
  simp [stdShannonEntropyLn]
  -- Now both sides are identical sums over `negMulLog`, so this is true by reflexivity.
  -- In some Lean versions, a simple `rfl` might not work if the definition of
  -- `stdShannonEntropyLn` uses a different but equivalent expression.
  -- However, in our codebase, `stdShannonEntropyLn` is defined directly as this sum.

/--
**Helper 2: The Chain Rule for `stdShannonEntropyLn` over a Sigma type.**
This is the core mathematical identity we need to prove.
`H(P_joint) = H(P_prior) + ∑ᵢ P_prior(i) * H(P_cond_i)`
-/
lemma stdShannonEntropyLn_chain_rule_sigma {N : ℕ}
    (prior   : Fin N → NNReal) (M_map : Fin N → ℕ)
    (P_cond  : Π (i : Fin N), (Fin (M_map i) → NNReal))
    (_hprior_sum_1 : ∑ i, prior i = 1)
    (hP_cond_props : ∀ i : Fin N, prior i > 0 → (∑ j, P_cond i j = 1)) :
    stdShannonEntropyLn (DependentPairDistSigma prior M_map P_cond) =
      stdShannonEntropyLn prior + ∑ i, (prior i : ℝ) * stdShannonEntropyLn (P_cond i) := by
  -- Let's work with the real-valued coercions directly.
  let P_joint (x : Σ i, Fin (M_map i)) : ℝ := (DependentPairDistSigma prior M_map P_cond x : ℝ)
  let P_prior (i : Fin N) : ℝ := (prior i : ℝ)
  let P_cond_i (i : Fin N) (j : Fin (M_map i)) : ℝ := (P_cond i j : ℝ)

  -- Unfold the LHS definition and use the sum-over-sigma rule.
  calc
    stdShannonEntropyLn (DependentPairDistSigma prior M_map P_cond)
      = ∑ x, (P_joint x).negMulLog := by
        simp only [stdShannonEntropyLn, Real.negMulLog_def, P_joint]
    _ = ∑ i, ∑ j, (P_joint ⟨i, j⟩).negMulLog := by
        exact sum_over_sigma_is_double_sum (fun x => (P_joint x).negMulLog)
    _ = ∑ i, ∑ j, (P_prior i * P_cond_i i j).negMulLog := by rfl

    -- Apply the product rule for negMulLog.
    _ = ∑ i, ∑ j, (P_cond_i i j * (P_prior i).negMulLog + P_prior i * (P_cond_i i j).negMulLog) := by
      apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _;
      -- We need to handle the case where probabilities are zero.
      by_cases hp_zero : P_prior i = 0
      · simp [hp_zero, Real.negMulLog_zero]
      by_cases hc_zero : P_cond_i i j = 0
      · simp [hc_zero, Real.negMulLog_zero]
      · -- The main case where both are positive.
        have hp_pos : 0 < P_prior i := lt_of_le_of_ne (NNReal.coe_nonneg _) (Ne.symm hp_zero)
        have hc_pos : 0 < P_cond_i i j := lt_of_le_of_ne (NNReal.coe_nonneg _) (Ne.symm hc_zero)
        rw [negMulLog_mul hp_pos hc_pos]

    -- Split the sum into two parts.
    _ = (∑ i, ∑ j, P_cond_i i j * (P_prior i).negMulLog) +
        (∑ i, ∑ j, P_prior i * (P_cond_i i j).negMulLog) := by simp_rw [Finset.sum_add_distrib]

    -- Simplify each part separately.
    _ = (stdShannonEntropyLn prior) + (∑ i, (prior i : ℝ) * stdShannonEntropyLn (P_cond i)) := by
      -- Prove the two parts are equal to the two terms on the RHS.
      apply congr_arg₂ (·+·)
      · -- First part: prove `∑ i, ∑ j, ... = stdShannonEntropyLn prior`
        calc
          ∑ i, ∑ j, P_cond_i i j * (P_prior i).negMulLog
            = ∑ i, (∑ j, P_cond_i i j) * (P_prior i).negMulLog := by
              simp_rw [Finset.sum_mul]
          _ = ∑ i, 1 * (P_prior i).negMulLog := by
              apply Finset.sum_congr rfl; intro i _;
              -- If prior i = 0, then P_prior i = 0 and negMulLog(P_prior i) = 0.
              by_cases hp_zero : prior i = 0
              · simp [P_prior, hp_zero, Real.negMulLog_zero, NNReal.coe_zero]
              · -- If prior i > 0, we can use the hypothesis.
                have h_sum_cond_is_1 : ∑ j, P_cond i j = 1 := by
                  exact hP_cond_props i (NNReal.coe_pos.mp (lt_of_le_of_ne (NNReal.coe_nonneg _) (Ne.symm (NNReal.coe_ne_zero.mpr hp_zero))))
                simp [P_cond_i, ← NNReal.coe_sum, h_sum_cond_is_1, NNReal.coe_one]
          _ = stdShannonEntropyLn prior := by
              -- We need to show that ∑ i, 1 * (P_prior i).negMulLog = stdShannonEntropyLn prior
              -- Since P_prior i = (prior i : ℝ), we have:
              simp only [one_mul, P_prior]
              exact sum_negMulLog_eq_stdShannonEntropyLn prior
      · -- Second part: prove `∑ i, ∑ j, ... = ∑ i, prior i * H(P_cond i)`
        calc
          ∑ i, ∑ j, P_prior i * (P_cond_i i j).negMulLog
            = ∑ i, P_prior i * (∑ j, (P_cond_i i j).negMulLog) := by
              simp_rw [Finset.mul_sum]
          _ = ∑ i, (prior i : ℝ) * stdShannonEntropyLn (P_cond i) := by
              apply Finset.sum_congr rfl; intro i _;
              simp [P_prior, P_cond_i, stdShannonEntropyLn]


/--
**Helper 1: The joint distribution `DependentPairDistSigma` sums to 1.**
This lemma externalizes the proof for `h_joint_sums_1`.
-/
lemma sum_DependentPairDistSigma_eq_one {N : ℕ}
    (prior : Fin N → NNReal) (M_map : Fin N → ℕ)
    (P_cond : Π i, Fin (M_map i) → NNReal)
    (hprior_sum_1 : ∑ i, prior i = 1)
    (hP_cond_props : ∀ i, prior i > 0 → ∑ j, P_cond i j = 1) :
    ∑ x, DependentPairDistSigma prior M_map P_cond x = 1 := by
  -- The sum over a sigma type is a double sum.
  calc
    ∑ x, DependentPairDistSigma prior M_map P_cond x
      = ∑ i, ∑ j, prior i * P_cond i j := by
        -- Use the library lemma for summing over a Sigma type and unfold the definition.
        rw [Fintype.sum_sigma, Finset.sum_congr rfl]
        intro i _; rfl
    _ = ∑ i, prior i * (∑ j, P_cond i j) := by
        -- Factor `prior i` out of the inner sum using `Finset.mul_sum`.
        apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
    _ = ∑ i, prior i := by
        -- We show each term `prior i * (∑ j, P_cond i j)` simplifies to `prior i`.
        apply Finset.sum_congr rfl; intro i _;
        -- If `prior i = 0`, the term is `0 * ... = 0 = prior i`.
        by_cases h_prior_zero : prior i = 0
        · simp [h_prior_zero]
        · -- If `prior i > 0`, then the inner sum is 1 by hypothesis.
          have h_prior_pos : 0 < prior i := by exact lt_of_le_of_ne' (zero_le _) h_prior_zero
          have h_sum_cond_is_1 := hP_cond_props i h_prior_pos
          simp [h_sum_cond_is_1]
    _ = 1 := hprior_sum_1



/--
**Helper 2: The conditional entropy term is always non-negative in the sum context.**
This lemma removes the `sorry` from `h_cond_nonneg`.
-/
lemma cond_entropy_term_nonneg {N : ℕ} (i : Fin N)
    (prior : Fin N → NNReal) (M_map : Fin N → ℕ)
    (P_cond : Π i, Fin (M_map i) → NNReal)
    (hP_cond_props : ∀ i, prior i > 0 → ∑ j, P_cond i j = 1) :
    0 ≤ (prior i : ℝ) * stdShannonEntropyLn (P_cond i) := by
  -- We proceed by cases on whether `prior i` is zero.
  by_cases h_prior_zero : prior i = 0
  · -- If `prior i` is 0, the entire term is 0, which is non-negative.
    simp [h_prior_zero]
  · -- If `prior i` is positive, then `P_cond i` is a valid probability distribution
    -- and its entropy is non-negative. The product of non-negatives is non-negative.
    have h_prior_pos_real : 0 ≤ (prior i : ℝ) := NNReal.coe_nonneg _
    have h_cond_entropy_nonneg : 0 ≤ stdShannonEntropyLn (P_cond i) := by
      -- Use the main non-negativity lemma, which requires proving the distribution sums to 1.
      -- This is guaranteed by our hypothesis `hP_cond_props`.
      have h_prior_pos : 0 < prior i := by exact lt_of_le_of_ne' (zero_le _) h_prior_zero
      exact stdShannonEntropyLn_nonneg (P_cond i) (hP_cond_props i h_prior_pos)
    exact mul_nonneg h_prior_pos_real h_cond_entropy_nonneg


-- ==================================================================
-- SECTION: The Main Additivity Proof (Finalized)
-- ==================================================================

theorem h_canonical_is_cond_add_sigma : IsEntropyCondAddSigma H_canonical_ln :=
  ⟨by
    -- Introduce all the universally quantified variables.
    intro N _inst_nezero_N prior M_map P_cond hprior_sum_1 hP_cond_props hH_P_cond_zero

    -- We will prove the identity in `ℝ` and then use `NNReal.eq` to finish.
    apply NNReal.eq
    -- Unfold H_canonical and coercions.
    simp only [H_canonical_ln]

    -- We need to show that the coercions work correctly
    have h_joint_nonneg : 0 ≤ stdShannonEntropyLn (DependentPairDistSigma prior M_map P_cond) := by
      have h_joint_sums_1 := sum_DependentPairDistSigma_eq_one prior M_map P_cond hprior_sum_1 (fun i h => (hP_cond_props i h).2)
      exact stdShannonEntropyLn_nonneg _ h_joint_sums_1
    have h_prior_nonneg : 0 ≤ stdShannonEntropyLn prior := stdShannonEntropyLn_nonneg _ hprior_sum_1

    -- Simplify the coercions using toNNReal_of_nonneg
    rw [Real.toNNReal_of_nonneg h_joint_nonneg, Real.toNNReal_of_nonneg h_prior_nonneg]
    simp only [NNReal.coe_add, NNReal.coe_sum, NNReal.coe_mul]

    -- Simplify the toNNReal terms
    have h_sum_simp : ∑ i, (prior i : ℝ) * (stdShannonEntropyLn (P_cond i)).toNNReal =
                      ∑ i, (prior i : ℝ) * stdShannonEntropyLn (P_cond i) := by
      apply Finset.sum_congr rfl
      intro i _
      -- We need to show ↑(prior i) * ↑(stdShannonEntropyLn (P_cond i)).toNNReal = ↑(prior i) * stdShannonEntropyLn (P_cond i)
      by_cases h_prior_zero : prior i = 0
      · -- If prior i = 0, both sides are 0
        rw [h_prior_zero, NNReal.coe_zero, zero_mul, zero_mul]
      · -- If prior i > 0, we can use the non-negativity of entropy
        have h_prior_pos : 0 < prior i := lt_of_le_of_ne' (zero_le _) h_prior_zero
        have h_entropy_nonneg := stdShannonEntropyLn_nonneg (P_cond i) ((hP_cond_props i h_prior_pos).2)
        rw [Real.coe_toNNReal _ h_entropy_nonneg]

    rw [h_sum_simp]

    -- Now apply the chain rule
    exact stdShannonEntropyLn_chain_rule_sigma prior M_map P_cond hprior_sum_1 (fun i h => (hP_cond_props i h).2)⟩


/--
**Helper 1 (placeholder):**
A temporary reflexivity lemma for `stdShannonEntropyLn`.
It sidesteps the still-missing `PMF.ofNNReal` / `PMF.entropy`
definitions in Mathlib 4.  Once the official PMF entropy API
lands, this lemma can be upgraded without affecting downstream code.
-/
lemma stdShannonEntropyLn_eq_pmf_entropy {α : Type*} [Fintype α]
    (p : α → NNReal) (_h_sum : ∑ i, p i = 1) :
    stdShannonEntropyLn p = stdShannonEntropyLn p :=
  rfl



/--
**Helper 1: The difference between max entropy and H(p) is the KL Divergence.**
This lemma handles the initial algebraic transformation of `log n - H(p)`.
The result, `∑ i, p i * log (n * p i)`, is the Kullback-Leibler divergence
`D_KL(p || u)` between the distribution `p` and the uniform distribution `u`
(where `u i = 1/n`), expressed in nats.
-/
lemma entropy_diff_eq_kl_divergence_sum {α : Type*} [Fintype α] (p : α → NNReal)
    (hp_sum : ∑ i, p i = 1) :
    Real.log (Fintype.card α) - stdShannonEntropyLn p =
      ∑ i, (p i : ℝ) * Real.log (Fintype.card α * (p i : ℝ)) := by
  let n := Fintype.card α
  calc
    Real.log n - stdShannonEntropyLn p
      -- Rewrite `log n` as `(∑ p i) * log n` since `∑ p i = 1`.
      = (∑ i, (p i : ℝ)) * Real.log n - stdShannonEntropyLn p := by
        rw [← NNReal.coe_sum, hp_sum, NNReal.coe_one, one_mul]
    _ = (∑ i, (p i : ℝ) * Real.log n) - ∑ i, Real.negMulLog (p i : ℝ) := by
        simp [stdShannonEntropyLn]
        rw [Finset.sum_mul]
    _ = ∑ i, ((p i : ℝ) * Real.log n - Real.negMulLog (p i : ℝ)) := by
        rw [Finset.sum_sub_distrib]
    _ = ∑ i, (p i : ℝ) * Real.log (n * (p i : ℝ)) := by
        -- Combine terms using log rules.
        apply sum_congr rfl; intro i _;
        by_cases h_pi_zero : p i = 0
        · simp [h_pi_zero, negMulLog_zero]
        · have h_pi_pos : 0 < (p i : ℝ) := NNReal.coe_pos.mpr (lt_of_le_of_ne' (zero_le _) h_pi_zero)
          have hn_pos_real : 0 < (n : ℝ) := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨i⟩)
          simp [negMulLog_def, h_pi_pos.ne']
          rw [← mul_add]
          rw [← Real.log_mul hn_pos_real.ne' h_pi_pos.ne']



/--
**Helper 2: The Kullback-Leibler divergence is non-negative.**
This is the core of Gibbs' inequality, proven from the fundamental
lemma `log x ≤ x - 1`.
-/
lemma kl_divergence_nonneg {α : Type*} [Fintype α] [Nonempty α] (p : α → NNReal)
    (hp_sum : ∑ i, p i = 1) :
    0 ≤ ∑ i, (p i : ℝ) * Real.log (Fintype.card α * (p i : ℝ)) := by
  let n := Fintype.card α
  let kl_sum := ∑ i, (p i : ℝ) * Real.log (n * (p i : ℝ))
  calc
    kl_sum ≥ - ∑ i, (p i : ℝ) * ((n * (p i : ℝ))⁻¹ - 1) := by
      -- This calc step is the core application of `log x ≤ x - 1`.
      -- We prove `kl_sum = - ∑ ... * -log(...) ≥ - ∑ ... * (...)`

      simp only [ge_iff_le]
      rw [← neg_neg kl_sum, neg_le_neg_iff]
      -- Now we need to show: kl_sum ≤ -∑ i, ↑(p i) * ((↑n * ↑(p i))⁻¹ - 1)
      rw [← sum_neg_distrib]
      -- Goal: ∑ i, ↑(p i) * log (↑n * ↑(p i)) ≤ ∑ i, -(↑(p i) * ((↑n * ↑(p i))⁻¹ - 1))
      -- Simplify the RHS: -(p i * ((n * p i)⁻¹ - 1)) = p i * (1 - (n * p i)⁻¹)
      conv_rhs =>
        arg 2; ext i
        ring_nf
      apply sum_le_sum; intro i _;
      by_cases h_pi_zero : p i = 0
      · simp [h_pi_zero]
      · -- For p i > 0, use the inequality log x ≤ x - 1
        -- We need: -(p i * log (n * p i)) ≤ -p i + p i * (p i)⁻¹ * n⁻¹
        -- Rearranging: -p i * log (n * p i) ≤ -p i + p i * (p i)⁻¹ * n⁻¹
        -- Which is: p i * log (n * p i) ≥ p i - p i * (p i)⁻¹ * n⁻¹
        -- Goal: -(↑(p i) * log (↑n * ↑(p i))) ≤ -↑(p i) + ↑(p i) * (↑(p i))⁻¹ * (↑n)⁻¹
        -- Multiply by -1: ↑(p i) * log (↑n * ↑(p i)) ≥ ↑(p i) - ↑(p i) * (↑(p i))⁻¹ * (↑n)⁻¹
        rw [← neg_le_neg_iff]
        rw [neg_neg, neg_add, neg_neg]
        -- Goal: ↑(p i) - ↑(p i) * (↑(p i))⁻¹ * (↑n)⁻¹ ≤ ↑(p i) * log (↑n * ↑(p i))
        have h_pi_pos : (0 : ℝ) < p i := NNReal.coe_pos.mpr (lt_of_le_of_ne' (zero_le _) h_pi_zero)
        have h_n_pos : (0 : ℝ) < n := Nat.cast_pos.mpr Fintype.card_pos
        -- The multiplication (p i) * (p i)⁻¹ = 1 when p i ≠ 0
        have h_ne_zero : (p i : ℝ) ≠ 0 := ne_of_gt h_pi_pos
        have h_simplify : (p i : ℝ) * ((p i : ℝ))⁻¹ = 1 := by
          simp [h_ne_zero]
        rw [h_simplify, one_mul]
        -- Goal: ↑(p i) + -(↑n)⁻¹ ≤ ↑(p i) * log (↑n * ↑(p i))
        -- This is equivalent to: ↑(p i) * log (↑n * ↑(p i)) - ↑(p i) ≥ -(↑n)⁻¹
        -- Factor out: ↑(p i) * (log (↑n * ↑(p i)) - 1) ≥ -(↑n)⁻¹
        -- We use the lower bound for log: log x ≥ 1 - x⁻¹ for x > 0
        let h_y := n * (p i : ℝ)
        have h_y_pos : 0 < h_y := mul_pos h_n_pos h_pi_pos
        -- Use the fundamental inequality: for x > 0, log x ≥ 1 - 1/x
        have h_log_lower : Real.log h_y ≥ 1 - h_y⁻¹ := by
          -- `Real.one_sub_inv_le_log_of_pos` states `1 - x⁻¹ ≤ log x` for any `x > 0`.
          -- This is definitionally the same inequality as our goal (just the sides swapped),
          -- so `simpa` closes the goal immediately.
          have h := Real.one_sub_inv_le_log_of_pos h_y_pos
          simpa [ge_iff_le] using h
        -- So log(n * p i) - 1 ≥ -(n * p i)⁻¹
        have h_log_bound : Real.log h_y - 1 ≥ -h_y⁻¹ := by linarith [h_log_lower]
        -- Multiply by p i > 0: p i * (log(n * p i) - 1) ≥ p i * (-(n * p i)⁻¹) = -n⁻¹
        have h_final : (p i : ℝ) * (Real.log h_y - 1) ≥ -(n : ℝ)⁻¹ := by
          have h_mul : (p i : ℝ) * (Real.log h_y - 1) ≥ (p i : ℝ) * (-h_y⁻¹) := by
            exact mul_le_mul_of_nonneg_left h_log_bound (le_of_lt h_pi_pos)
          rw [mul_neg] at h_mul
          have h_cancel : (p i : ℝ) * h_y⁻¹ = (n : ℝ)⁻¹ := by
            simp only [h_y]
            -- p_i * (n * p_i)⁻¹ = p_i * (n⁻¹ * (p_i)⁻¹) = n⁻¹ * p_i * (p_i)⁻¹ = n⁻¹ * 1 = n⁻¹
            calc (p i : ℝ) * (n * (p i : ℝ))⁻¹
              = (p i : ℝ) * ((n : ℝ)⁻¹ * ((p i : ℝ))⁻¹) := by rw [mul_inv]
              _ = ((p i : ℝ) * (n : ℝ)⁻¹) * ((p i : ℝ))⁻¹ := by ring
              _ = (n : ℝ)⁻¹ * ((p i : ℝ) * ((p i : ℝ))⁻¹) := by ring
              _ = (n : ℝ)⁻¹ * 1 := by rw [mul_inv_cancel₀ h_ne_zero]
              _ = (n : ℝ)⁻¹ := by rw [mul_one]
          rw [h_cancel] at h_mul
          exact h_mul
        -- Now we need to show: ↑(p i) + -(↑n)⁻¹ ≤ ↑(p i) * log (↑n * ↑(p i))
        -- This is equivalent to: -(↑n)⁻¹ ≤ ↑(p i) * log (↑n * ↑(p i)) - ↑(p i)
        -- Which is: -(↑n)⁻¹ ≤ ↑(p i) * (log (↑n * ↑(p i)) - 1)
        suffices h_suff : -(n : ℝ)⁻¹ ≤ (p i : ℝ) * (Real.log (n * (p i : ℝ)) - 1) by
          -- h_y is n * (p i : ℝ), so this is exactly h_final
          simp only [h_y] at h_final
          linarith [h_final]
        exact h_final
    _ ≥ 0 := by
        -- We need to prove `- ∑ i, pᵢ * ((n * pᵢ)⁻¹ - 1) ≥ 0`.
        -- Rewrite as `∑ i, pᵢ * (1 - (n * pᵢ)⁻¹) ≥ 0`
        rw [← sum_neg_distrib]
        -- Goal: `∑ i, -(p i * ((n * p i)⁻¹ - 1)) ≥ 0`
        conv_lhs =>
          arg 2; ext i
          rw [← mul_neg, neg_sub]
        -- Goal: `∑ i, p i * (1 - (n * p i)⁻¹) ≥ 0`
        conv_lhs =>
          arg 2; ext i
          rw [mul_sub, mul_one]
        -- Goal: `∑ i, (p i - p i * (n * p i)⁻¹) ≥ 0`
        rw [sum_sub_distrib]
        -- Goal: `(∑ i, p i) - (∑ i, p i * (n * p i)⁻¹) ≥ 0`
        -- The first sum equals 1 since ∑ p i = 1 and p i are NNReal coerced to ℝ
        have h_sum_one : ∑ i, (p i : ℝ) = 1 := by rw [← NNReal.coe_sum, hp_sum, NNReal.coe_one]
        rw [h_sum_one]
        -- Goal: `1 - (∑ i, p i * (n * p i)⁻¹) ≥ 0`
        -- This is equivalent to `(∑ i, p i * (n * p i)⁻¹) ≤ 1`
        suffices h : (∑ i, (p i : ℝ) * (n * (p i : ℝ))⁻¹) ≤ 1 by linarith
        -- Goal: `(∑ i, p i * (n * p i)⁻¹) ≤ 1`
        -- Simplify the sum using the fact that p i * (n * p i)⁻¹ = n⁻¹ when p i ≠ 0
        have h_sum_simplify : ∑ i, (p i : ℝ) * (n * (p i : ℝ))⁻¹ = (Finset.univ.filter (fun j => p j ≠ 0)).card * (n:ℝ)⁻¹ := by
          calc
            ∑ i, (p i : ℝ) * (n * (p i : ℝ))⁻¹
              = ∑ i in (Finset.univ.filter (fun j => p j ≠ 0)), (p i : ℝ) * (n * (p i : ℝ))⁻¹ := by
                symm; apply sum_filter_of_ne; intro i _ h_ne; contrapose! h_ne; simp [h_ne]
            _ = ∑ i in (Finset.univ.filter (fun j => p j ≠ 0)), (n:ℝ)⁻¹ := by
                apply sum_congr rfl; intro i hi;
                simp only [mem_filter] at hi
                -- (p i) * (n * p i)⁻¹ = (p i) / (n * p i) = 1/n = n⁻¹
                field_simp [NNReal.coe_ne_zero.mpr hi.2, Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)]
                -- Goal: ↑(p i) * ↑n = ↑n * ↑(p i)
                ring
            _ = (Finset.univ.filter (fun j => p j ≠ 0)).card * (n:ℝ)⁻¹ := by simp [sum_const, nsmul_eq_mul]
        rw [h_sum_simplify]
        -- Goal: `card * n⁻¹ ≤ 1`
        -- This follows from card ≤ n since n > 0
        have h_pos : (0 : ℝ) < n := Nat.cast_pos.mpr Fintype.card_pos
        have h_card_le_n : (Finset.univ.filter (fun j => p j ≠ 0)).card ≤ n := Finset.card_filter_le _ _
        -- Convert to real inequality and apply the bound
        calc
          ((Finset.univ.filter (fun j => p j ≠ 0)).card : ℝ) * (n : ℝ)⁻¹
            ≤ (n : ℝ) * (n : ℝ)⁻¹ := by
              apply mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h_card_le_n) (inv_nonneg.mpr (le_of_lt h_pos))
          _ = 1 := by simp [mul_inv_cancel, ne_of_gt h_pos]

/--
**Helper: Information inequality for Shannon entropy.**
This lemma is now a clean combination of the two helpers above.
-/
lemma stdShannonEntropyLn_le_log_card {α : Type*} [Fintype α] (p : α → NNReal)
    (hp_sum : ∑ i, p i = 1) :
    stdShannonEntropyLn p ≤ Real.log (Fintype.card α) := by
  -- Handle the empty case first
  by_cases h_empty : IsEmpty α
  · -- If α is empty, then the sum condition hp_sum would be 0 = 1, which is impossible
    exfalso
    have h_zero_sum : ∑ i, p i = 0 := by
      rw [Finset.sum_eq_zero]
      intro i hi
      exact False.elim (h_empty.false i)
    rw [h_zero_sum] at hp_sum
    exact zero_ne_one hp_sum
  · -- If α is nonempty, use the KL divergence approach
    haveI : Nonempty α := not_isEmpty_iff.mp h_empty
    have h : 0 ≤ Real.log (Fintype.card α) - stdShannonEntropyLn p := by
      rw [entropy_diff_eq_kl_divergence_sum p hp_sum]
      exact kl_divergence_nonneg p hp_sum
    linarith


-- ==================================================================
-- SECTION: The Main Max Uniform Proof (Finalized)
-- ==================================================================

theorem h_canonical_is_max_uniform : IsEntropyMaxUniform H_canonical_ln :=
  ⟨by
    -- Introduce all the universally quantified variables.
    intro α _inst_fintype h_card_pos p hp_sum_1

    -- The goal is `H_canonical p ≤ H_canonical (uniformDist h_card_pos)`.
    -- We will prove the equivalent inequality in ℝ.
    simp only [H_canonical_ln]
    rw [Real.toNNReal_le_toNNReal_iff]
    · -- The goal is now in ℝ: `stdShannonEntropyLn p ≤ stdShannonEntropyLn (uniformDist h_card_pos)`.

      -- Step 1: Rewrite the RHS using the known identity for uniform entropy.
      -- This comes from our codebase in EGPT.Entropy.Common.
      rw [stdShannonEntropyLn_uniform_eq_log_card h_card_pos]

      -- The goal is now `stdShannonEntropyLn p ≤ Real.log (Fintype.card α)`.

      -- Step 2: Apply the information inequality (Gibbs' inequality).
      apply stdShannonEntropyLn_le_log_card
      exact hp_sum_1

    · -- The proof obligation for `toNNReal_le_toNNReal_iff`.
      -- We need to show that the RHS is non-negative.
      have h_uniform_sums : ∑ i, uniformDist h_card_pos i = 1 := sum_uniformDist h_card_pos
      exact stdShannonEntropyLn_nonneg (uniformDist h_card_pos) h_uniform_sums⟩


-- Let's package everything into a single, concrete instance.
noncomputable def TheCanonicalEntropyFunction_Ln : EntropyFunction := {
  H_func := H_canonical_ln,
  props := {
    -- We place the completed proofs for all 7 axioms here.
    toIsEntropySymmetric := h_canonical_is_symmetric,
    toIsEntropyZeroOnEmptyDomain := h_canonical_is_zero_on_empty,
    toIsEntropyNormalized := h_canonical_is_normalized,
    toIsEntropyZeroInvariance := h_canonical_is_zero_invariance,
    toIsEntropyContinuous := h_canonical_is_continuous,
    toIsEntropyCondAddSigma := h_canonical_is_cond_add_sigma,
    toIsEntropyMaxUniform := h_canonical_is_max_uniform,
  }
}



/--
The canonical entropy function for computer science is the standard Shannon
Entropy measured in **bits** (using log base 2).
-/
noncomputable def H_canonical_log2 {α : Type} [Fintype α] (p : α → NNReal) : NNReal :=
  ((stdShannonEntropyLn p) / Real.log 2).toNNReal

/--
**Theorem:** For the canonical base-2 Shannon entropy function (`H_canonical_log2`),
the entropy of a single fair coin flip is exactly 1 bit.

**Interpretation:** This is the formal "unit test" confirming that our EGPT
entropy engine is perfectly calibrated for computer science applications, where
the bit is the fundamental unit of information.
-/
theorem entropy_of_fair_coin_is_one_bit :
    -- We model a fair coin flip as the uniform distribution on a set of 2 outcomes (Fin 2).
    let coin_flip_dist := canonicalUniformDist 2 (by norm_num)
    H_canonical_log2 coin_flip_dist = 1 := by

  -- Let's define our distribution for clarity.
  let coin_flip_dist := canonicalUniformDist 2 (by norm_num)
  -- Unfold the definition of our base-2 entropy function.
  simp only [H_canonical_log2, coin_flip_dist, canonicalUniformDist]

  -- The expression is now `((stdShannonEntropyLn (uniformDist ...)) / log 2).toNNReal`.
  -- From our previous proofs, we know that `stdShannonEntropyLn (uniformDist h_card_pos)` is `log (card)`.
  have h2_pos : (2 : ℕ) > 0 := by norm_num
  have h_uniform_entropy : stdShannonEntropyLn (uniformDist (Fintype_card_fin_pos h2_pos)) = log 2 := by
    rw [stdShannonEntropyLn_uniform_eq_log_card (Fintype_card_fin_pos h2_pos)]
    simp [Fintype.card_fin]

  -- Substitute this into our goal.
  rw [h_uniform_entropy]

  -- The goal is now `((log 2 / log 2)).toNNReal = 1`.
  -- `log 2 / log 2` simplifies to 1.
  have h_log2_ne_zero : log 2 ≠ 0 := ne_of_gt (log_pos (by norm_num : (2:ℝ) > 1))
  rw [div_self h_log2_ne_zero]

  -- The goal is now `(1:ℝ).toNNReal = 1`. This is true by definition.
  rw [Real.toNNReal_one]
