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
import Archive.Entropy.H -- For the canonical entropy function

open EGPT.Complexity EGPT.Constraints EGPT.Physics.PCA EGPT.Entropy.Common EGPT.NumberTheory.Filter EGPT.Complexity.SetRFL EGPT.NumberTheory.Core EGPT.Entropy.RET Real Finset EGPT.Entropy.H


-- ==================================================================
-- Transporting Rota Entropy Properties Over Scaling:
-- Replica of EGPT.Entropy.Analysis.RET_All_Entropy_Is_Scaled_Shannon_Entropy
-- separated out here for exemplary clarity.
-- ==================================================================

/--
**ALL ENTROPY IS SCALED SHANNON ENTROPY: Theorem (Rota Properties Transport Over Scaling):** If a function `H` satisfies
the properties of an entropy function, then any positive constant multiple of `H`
also satisfies those properties.

This transport also allows us to change the base of the logarithm in the entropy function
without re-writing all the axiom proofs which were more easily
done in nats.
-/
theorem RET_All_Entropy_Is_Scaled_Shannon_Entropy (ef : EntropyFunction) (C : ℝ) (hC_pos : 0 < C) :
    HasRotaEntropyProperties (fun p => (C * (ef.H_func p : ℝ)).toNNReal) :=
  let C_nn : NNReal := C.toNNReal
  have hC_nn_pos : 0 < C_nn := by
    simp only [C_nn]
    exact Real.toNNReal_pos.mpr hC_pos
  {
    -- Each axiom proof for the scaled function follows from the original proof by distributing the constant C.
    symmetry := by
      intro α β _ _ p_target hp e
      -- Goal: (C * ↑(ef.H_func (fun x => p_target (e x)))).toNNReal = (C * ↑(ef.H_func p_target)).toNNReal
      congr 2
      simp only [NNReal.coe_inj]
      exact ef.props.symmetry p_target hp e
    ,
    zero_invariance := by
      intro n p_orig hp_sum_1
      -- Goal: (C * ↑(ef.H_func p_ext)).toNNReal = (C * ↑(ef.H_func p_orig)).toNNReal
      congr 2
      simp only [NNReal.coe_inj]
      exact ef.props.zero_invariance p_orig hp_sum_1
    ,
    normalized := by
      intro p hp_sum_1
      -- Goal: (C * ↑(ef.H_func p)).toNNReal = 0
      simp only [ef.props.normalized p hp_sum_1, NNReal.coe_zero, mul_zero, Real.toNNReal_zero]
    ,
    max_uniform := by
      intro α _ h_card_pos p hp_sum_1
      -- Goal: (C * ↑(ef.H_func p)).toNNReal ≤ (C * ↑(ef.H_func (uniformDist h_card_pos))).toNNReal
      -- This follows from the monotonicity of toNNReal and multiplication by positive constants
      apply Real.toNNReal_le_toNNReal
      apply mul_le_mul_of_nonneg_left
      · exact NNReal.coe_le_coe.mpr (ef.props.max_uniform h_card_pos p hp_sum_1)
      · exact le_of_lt hC_pos
    ,
    continuity := by
      intro α _ p_center hp_sum_1 ε hε_pos
      -- Goal: ∃ δ > 0, ∀ (q : α → NNReal) (_hq_sum_1 : ∑ i, q i = 1),
      --       (∀ i, |(q i : ℝ) - (p_center i : ℝ)| < δ) →
      --       |((C * ↑(ef.H_func q)).toNNReal : ℝ) - ((C * ↑(ef.H_func p_center)).toNNReal : ℝ)| < ε

      -- Use continuity of the original entropy function ef.H_func
      -- We want: |C * ↑(ef.H_func q) - C * ↑(ef.H_func p_center)| < ε
      -- This gives us: |C| * |↑(ef.H_func q) - ↑(ef.H_func p_center)| < ε
      -- So we need: |↑(ef.H_func q) - ↑(ef.H_func p_center)| < ε / |C|

      have hC_abs_pos : |C| > 0 := abs_pos.mpr (ne_of_gt hC_pos)
      let ε_scaled := ε / |C|
      have hε_scaled_pos : ε_scaled > 0 := div_pos hε_pos hC_abs_pos

      -- Apply continuity of ef.H_func
      obtain ⟨δ, hδ_pos, hδ_works⟩ := ef.props.continuity p_center hp_sum_1 ε_scaled hε_scaled_pos

      use δ, hδ_pos
      intro q hq_sum_1 hq_close

      -- Apply the continuity property of ef.H_func
      have h_ef_close := hδ_works q hq_sum_1 hq_close

      -- Since ef.H_func returns NNReal, both values are non-negative, so toNNReal is identity
      have h_nonneg_q : (C * (ef.H_func q : ℝ)) ≥ 0 :=
        mul_nonneg (le_of_lt hC_pos) (NNReal.coe_nonneg _)
      have h_nonneg_p : (C * (ef.H_func p_center : ℝ)) ≥ 0 :=
        mul_nonneg (le_of_lt hC_pos) (NNReal.coe_nonneg _)

      rw [Real.coe_toNNReal _ h_nonneg_q, Real.coe_toNNReal _ h_nonneg_p]

      -- Now we have: |C * ↑(ef.H_func q) - C * ↑(ef.H_func p_center)| < ε
      rw [← mul_sub, abs_mul]

      -- Since C > 0, |C| = C
      rw [abs_of_pos hC_pos]

      -- Apply the bound from ef.H_func continuity
      have h_bound : |((ef.H_func q) : ℝ) - ((ef.H_func p_center) : ℝ)| < ε_scaled := h_ef_close

      -- Conclude: C * |↑(ef.H_func q) - ↑(ef.H_func p_center| < C * (ε / C) = ε
      calc C * |((ef.H_func q) : ℝ) - ((ef.H_func p_center) : ℝ)|
        < C * ε_scaled := by apply mul_lt_mul_of_pos_left h_bound hC_pos
        _ = C * (ε / |C|) := rfl
        _ = C * (ε / C) := by rw [abs_of_pos hC_pos]
        _ = ε := by field_simp [ne_of_gt hC_pos]
    ,
    cond_add_sigma := by
      -- Introduce all the universally quantified variables.
      intro N _inst prior M_map P_cond hprior_sum_1 hP_cond_props hH_P_cond_zero

      -- We will prove the equality in `ℝ` and then use `NNReal.eq` to finish.
      apply NNReal.eq
      symm  -- Flip the goal so calc starts with the correct side

      -- First, we establish that all scaled entropy terms are non-negative, so `toNNReal` behaves predictably.
      have h_joint_nonneg : 0 ≤ C * (ef.H_func (DependentPairDistSigma prior M_map P_cond) : ℝ) :=
        mul_nonneg (le_of_lt hC_pos) (NNReal.coe_nonneg _)
      have h_prior_nonneg : 0 ≤ C * (ef.H_func prior : ℝ) :=
        mul_nonneg (le_of_lt hC_pos) (NNReal.coe_nonneg _)
      have h_cond_i_nonneg (i : Fin N) : 0 ≤ C * (ef.H_func (P_cond i) : ℝ) :=
        mul_nonneg (le_of_lt hC_pos) (NNReal.coe_nonneg _)

      -- Now, let's work with the `ℝ`-valued equation.
      -- The `calc` block transforms the RHS into the LHS.
      calc
        -- Start with the expected LHS coerced to ℝ
        ↑((C * ↑(ef.H_func prior)).toNNReal + ∑ i, prior i * (C * ↑(ef.H_func (P_cond i))).toNNReal)

        -- Simplify coercions using toNNReal properties for nonnegative values.
        _ = (C * (ef.H_func prior : ℝ)) + ∑ i, (prior i : ℝ) * (C * (ef.H_func (P_cond i) : ℝ)) := by
            rw [NNReal.coe_add, NNReal.coe_sum]
            congr 1
            · rw [Real.coe_toNNReal _ h_prior_nonneg]
            · congr 1
              ext i
              rw [NNReal.coe_mul, Real.coe_toNNReal _ (h_cond_i_nonneg i)]

        -- Factor out the constant C in ℝ.
        _ = C * ((ef.H_func prior : ℝ) + ∑ i, (prior i : ℝ) * (ef.H_func (P_cond i) : ℝ)) := by
            rw [mul_add]
            congr 1
            rw [mul_sum]
            congr 1
            ext i
            ring

        -- Apply the original axiom for `ef`, coercing to ℝ.
        _ = C * (ef.H_func (DependentPairDistSigma prior M_map P_cond) : ℝ) := by
            congr 1
            -- We need to construct the proper hypothesis for the original axiom
            have hH_P_cond_zero_orig : ∀ (i : Fin N), M_map i = 0 → ef.H_func (P_cond i) = 0 := by
              intro i hi
              -- From hH_P_cond_zero, we have (C * ↑(ef.H_func (P_cond i))).toNNReal = 0
              have h := hH_P_cond_zero i hi
              -- Since C > 0, if (C * ↑(ef.H_func (P_cond i))).toNNReal = 0,
              -- then C * ↑(ef.H_func (P_cond i)) = 0, which implies ef.H_func (P_cond i) = 0
              have h_zero : C * ↑(ef.H_func (P_cond i)) = 0 := by
                have h_nonneg := h_cond_i_nonneg i
                -- From toNNReal a = 0 and a ≥ 0, we get a = 0
                have h_le_zero : C * ↑(ef.H_func (P_cond i)) ≤ 0 := Real.toNNReal_eq_zero.mp h
                exact le_antisymm h_le_zero h_nonneg
              have h_coe_zero : ↑(ef.H_func (P_cond i)) = (0 : ℝ) := by
                have h_nonzero : C ≠ 0 := ne_of_gt hC_pos
                rw [mul_eq_zero] at h_zero
                cases h_zero with
                | inl h => contradiction
                | inr h => exact h
              -- From coe zero to NNReal zero
              exact NNReal.coe_eq_zero.mp h_coe_zero
            have h_orig_axiom := ef.props.cond_add_sigma prior M_map P_cond hprior_sum_1 hP_cond_props hH_P_cond_zero_orig
            -- Apply coercion to both sides of the equality
            have h_real : (ef.H_func (DependentPairDistSigma prior M_map P_cond) : ℝ) =
                          (ef.H_func prior : ℝ) + ∑ i, (prior i : ℝ) * (ef.H_func (P_cond i) : ℝ) := by
              rw [h_orig_axiom]
              simp only [NNReal.coe_add, NNReal.coe_sum, NNReal.coe_mul]
            exact h_real.symm

        -- This is now the definition of the LHS coerced to ℝ.
        _ = ↑((C * ↑(ef.H_func (DependentPairDistSigma prior M_map P_cond))).toNNReal) := by
            rw [Real.coe_toNNReal _ h_joint_nonneg]
    ,
    apply_to_empty_domain := by
      -- Goal: (C * ↑(ef.H_func (fun (_ : Empty) => 0))).toNNReal = 0
      simp only [ef.props.apply_to_empty_domain, NNReal.coe_zero, mul_zero, Real.toNNReal_zero]
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
