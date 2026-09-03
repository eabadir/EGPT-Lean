import Archive
-- NOTE: `import PPNP` removed during rehabilitation.
-- The PPNP library (`PPNP/Proofs/*.lean`, `PPNP/Dev/Dev.lean`) still uses the
-- pre-rename module paths `EGPT.*` for its imports (e.g. `import EGPT.NumberTheory.Filter`).
-- Those files were relocated under `Archive/*` and are now imported via `import Archive`.
-- The *namespace* inside each Archive file is still `EGPT.*` (e.g. `namespace EGPT.NumberTheory.Core`),
-- so every theorem reference below using `EGPT.*` resolves correctly through `import Archive` alone.
-- The two Wave-Particle theorems that lived only in PPNP/Proofs/WaveParticleDualityDisproved.lean
-- are deferred — see the commented section near the end of this file.

/-!
# EGPT Build Report

This file generates a build verification report by importing the entire
proof chain and printing axiom usage for every key theorem.

Run with: `cd Lean && lake env lean build_report.lean`

A clean run (exit code 0) with no `sorry` in the output confirms:
  1. All files typecheck against mathlib4
  2. The proof chain is sorry-free
  3. Only Lean's built-in axioms are used (no custom axioms)
-/

-- ═══════════════════════════════════════════════════════════════
-- Physics/RealityIsComputation: Reality Is Computation (capstone)
-- ═══════════════════════════════════════════════════════════════
#print axioms EGPT.Physics.RealityIsComputation.RealityIsComputation'
#print axioms EGPT.Physics.RealityIsComputation.RealityIsComputation
#print axioms EGPT.Physics.RealityIsComputation.ContinuousFieldsAreComputation

-- ═══════════════════════════════════════════════════════════════
-- NumberTheory/Core: ParticlePath ↔ ℕ bijection & arithmetic
-- ═══════════════════════════════════════════════════════════════
#print axioms EGPT.NumberTheory.Core.equivParticlePathToNat
#print axioms EGPT.NumberTheory.Core.fromNat
#print axioms EGPT.NumberTheory.Core.toNat
#print axioms EGPT.NumberTheory.Core.left_inv
#print axioms EGPT.NumberTheory.Core.right_inv
#print axioms EGPT.NumberTheory.Core.toNat_add_ParticlePath
#print axioms EGPT.NumberTheory.Core.toNat_mul_ParticlePath
#print axioms EGPT.NumberTheory.Core.EGPT_Polynomial.eval
#print axioms EGPT.NumberTheory.Core.cardinal_of_egpt_level

-- ═══════════════════════════════════════════════════════════════
-- NumberTheory/ContinuumHypothesis: CH & GCH Decidable (Hilbert #1)
-- ═══════════════════════════════════════════════════════════════
#print axioms EGPT.NumberTheory.ContinuumHypothesis.EGPT_cardinality_is_beth
#print axioms EGPT.NumberTheory.ContinuumHypothesis.EGPT_ContinuumHypothesis
#print axioms EGPT.NumberTheory.ContinuumHypothesis.EGPT_GeneralizedContinuumHypothesis
#print axioms EGPT.NumberTheory.ContinuumHypothesis.EGPT_all_infinities_indexed_by_Nat

-- ═══════════════════════════════════════════════════════════════
-- NumberTheory/Filter: RejectionFilter & probability
-- ═══════════════════════════════════════════════════════════════
#print axioms EGPT.NumberTheory.Filter.RejectionFilter.get_witness
#print axioms EGPT.NumberTheory.Filter.RejectionFilter.of_satisfying_example
#print axioms EGPT.NumberTheory.Filter.distOfRejectionFilter
#print axioms EGPT.NumberTheory.Filter.eventsPMF
#print axioms EGPT.NumberTheory.Filter.construct_real_solution_space

-- ═══════════════════════════════════════════════════════════════
-- NumberTheory/Analysis: Fundamental Theorem of Arithmetic (EGPT)
-- ═══════════════════════════════════════════════════════════════
#print axioms RET_All_Entropy_Is_Scaled_Shannon_Entropy
#print axioms EGPT_Fundamental_Theorem_of_Arithmetic_via_Information
#print axioms EGPT_Fundamental_Theorem_of_Arithmetic_via_Entropy_Bits
#print axioms total_entropy_from_classes_eq_shannon_formula
#print axioms PrimeAtoms.factorial_information_decomposition
#print axioms PrimeAtoms.factorial_information_increment

-- ═══════════════════════════════════════════════════════════════
-- Constraints: CNF encoding & canonical form
-- ═══════════════════════════════════════════════════════════════
#print axioms EGPT.Constraints.evalCNF
#print axioms EGPT.Constraints.encodeCNF
#print axioms EGPT.Constraints.normalizeCNF
#print axioms EGPT.Constraints.evalCNF_normalize_eq_evalCNF
#print axioms EGPT.Constraints.encodeCNF_normalize_length_eq
#print axioms EGPT.Constraints.encodeCNF_size_ge_k
#print axioms EGPT.Constraints.cnf_length_le_encoded_length

-- ═══════════════════════════════════════════════════════════════
-- Entropy/Common: Shannon entropy & source coding
-- ═══════════════════════════════════════════════════════════════
#print axioms EGPT.Entropy.Common.ShannonEntropyOfDist
#print axioms EGPT.Entropy.Common.stdShannonEntropyLn
#print axioms EGPT.Entropy.Common.stdShannonEntropyLn_uniform_eq_log_card
#print axioms EGPT.Entropy.Common.rect_program_for_dist
#print axioms EGPT.Entropy.Common.RECT_Entropy_to_Program
#print axioms EGPT.Entropy.Common.IRECT_RECT_inverse_for_integer_complexity
#print axioms EGPT.Entropy.Common.program_source_complexity_matches

-- ═══════════════════════════════════════════════════════════════
-- Entropy/RET: Rota Entropy Theorem
-- ═══════════════════════════════════════════════════════════════
#print axioms EGPT.Entropy.RET.f0_1_eq_0
#print axioms EGPT.Entropy.RET.f0_mono
#print axioms EGPT.Entropy.RET.f0_mul_eq_add_f0
#print axioms EGPT.Entropy.RET.uniformEntropy_power_law
#print axioms EGPT.Entropy.RET.logarithmic_trapping
#print axioms EGPT.Entropy.RET.uniformEntropy_ratio_eq_logb
#print axioms EGPT.Entropy.RET.RotaUniformTheorem_formula_with_C_constant
#print axioms EGPT.Entropy.RET.RotaUniformTheorem
#print axioms EGPT.Entropy.RET.RUE_rational_case
#print axioms EGPT.Entropy.RET.H_canonical_uniform_eq_C_shannon

-- ═══════════════════════════════════════════════════════════════
-- Entropy/H: Shannon entropy properties & chain rule
-- ═══════════════════════════════════════════════════════════════
#print axioms EGPT.Entropy.H.h_canonical_is_symmetric
#print axioms EGPT.Entropy.H.h_canonical_is_normalized
#print axioms EGPT.Entropy.H.h_canonical_is_zero_on_empty
#print axioms EGPT.Entropy.H.h_canonical_is_zero_invariance
#print axioms EGPT.Entropy.H.h_canonical_is_continuous
#print axioms EGPT.Entropy.H.h_canonical_is_cond_add_sigma
#print axioms EGPT.Entropy.H.h_canonical_is_max_uniform
#print axioms EGPT.Entropy.H.entropy_of_fair_coin_is_one_bit
#print axioms EGPT.Entropy.H.stdShannonEntropyLn_le_log_card
#print axioms EGPT.Entropy.H.stdShannonEntropyLn_chain_rule_sigma

-- ═══════════════════════════════════════════════════════════════
-- Complexity/Core & TableauFromCNF: certificates & polynomial bounds
-- ═══════════════════════════════════════════════════════════════
#print axioms EGPT.Complexity.PathToConstraint
#print axioms EGPT.Complexity.walkCNFPaths
#print axioms EGPT.Complexity.walkComplexity_upper_bound
#print axioms EGPT.Complexity.walkComplexity_eq_sum_of_paths

-- ═══════════════════════════════════════════════════════════════
-- Complexity/ComplexityInformationBridge: time = information complexity
-- ═══════════════════════════════════════════════════════════════
#print axioms EGPT.Complexity.Interpretation.nSquared_time_complexity_is_information_complexity
#print axioms EGPT.Complexity.Interpretation.walk_nSquared_bound_is_time_and_information

-- ═══════════════════════════════════════════════════════════════
-- Complexity/SetRFL: P = NP proof chain (definitional identity)
-- ═══════════════════════════════════════════════════════════════
#print axioms EGPT.Complexity.SetRFL.L_SAT_Canonical
#print axioms EGPT.Complexity.SetRFL.NP_def
#print axioms EGPT.Complexity.SetRFL.P_def
#print axioms EGPT.Complexity.SetRFL.L_SAT_in_NP_def
#print axioms EGPT.Complexity.SetRFL.L_SAT_in_P_def
#print axioms EGPT.Complexity.SetRFL.L_SAT_in_NP_def_Hard
#print axioms EGPT.Complexity.SetRFL.EGPT_CookLevin_def_Theorem
#print axioms EGPT.Complexity.SetRFL.P_def_eq_NP_def

-- ═══════════════════════════════════════════════════════════════
-- Complexity/UTM: ReadHead model, time = information
-- ═══════════════════════════════════════════════════════════════
#print axioms EGPT.Complexity.UTM.timeComplexity_eq_length
#print axioms EGPT.Complexity.UTM.time_eq_information_eq_complexity

-- ═══════════════════════════════════════════════════════════════
-- Complexity/PPNP: P = NP (constructive information-theoretic chain)
-- ═══════════════════════════════════════════════════════════════
#print axioms EGPT.Complexity.PPNP.P_eq_NP
#print axioms EGPT.Complexity.PPNP.complete_information_extraction

-- ═══════════════════════════════════════════════════════════════
-- PPNP/Proofs: Wave-Particle Duality Disproved   (DEFERRED)
-- ═══════════════════════════════════════════════════════════════
-- The two theorems below live only in PPNP/Proofs/WaveParticleDualityDisproved.lean,
-- which still uses the legacy `import EGPT.*` paths. Re-enable these once that file
-- has been migrated to `import Archive.*`. The theorems themselves are unchanged.
-- #print axioms PhotonDistributionsHaveClassicalExplanationFromIndividualPaths
-- #print axioms Wave_Particle_Duality_Disproved_QED

-- ═══════════════════════════════════════════════════════════════
-- Physics/Common: physical entropy
-- ═══════════════════════════════════════════════════════════════
#print axioms EGPT.Physics.Common.H_physical_system

-- ═══════════════════════════════════════════════════════════════
-- Physics/UniformSystems: uniform distribution proofs
-- ═══════════════════════════════════════════════════════════════
#print axioms EGPT.Physics.UniformSystems.H_physical_dist_eq_C_shannon_if_uniform_and_equiv
#print axioms EGPT.Physics.UniformSystems.H_physical_system_is_rota_uniform
#print axioms EGPT.Physics.UniformSystems.H_canonical_uniform_eq_C_shannon
#print axioms EGPT.Physics.UniformSystems.stdShannonEntropyLn_comp_equiv

-- ═══════════════════════════════════════════════════════════════
-- Physics/BoseEinstein: Bose-Einstein statistics
-- ═══════════════════════════════════════════════════════════════
#print axioms EGPT.Physics.BE.H_BE_from_Multiset_eq_C_shannon
#print axioms EGPT.Physics.BE.p_BE_sums_to_one
#print axioms EGPT.Physics.BE.p_BE_fin_is_uniformDist

-- ═══════════════════════════════════════════════════════════════
-- Physics/PhotonicCA: photonic cellular automata
-- ═══════════════════════════════════════════════════════════════
#print axioms EGPT.Physics.PCA.be_system_has_equivalent_program
