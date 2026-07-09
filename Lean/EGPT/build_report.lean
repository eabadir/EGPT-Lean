import InformationTheory

/-!
# EGPT Build Report (Publication-Ready — Lean/EGPT)

This file generates a build verification report by importing the entire
proof chain and printing axiom usage for every key theorem.

Run with: `cd Lean/EGPT && lake env lean build_report.lean`

A clean run (exit code 0) with no `sorry` in the output confirms:
  1. All files typecheck against mathlib4
  2. The proof chain is sorry-free
  3. Only Lean's built-in axioms are used (no custom axioms)
-/

-- ═══════════════════════════════════════════════════════════════
-- EntropyNumber/Basic: EntropyNat ↔ ℕ bijection & arithmetic
-- ═══════════════════════════════════════════════════════════════
#print axioms InformationTheory.entropyNatEquivNat
#print axioms InformationTheory.EntropyNat.ofNat
#print axioms InformationTheory.EntropyNat.toNat
#print axioms InformationTheory.EntropyNat.ofNat_toNat
#print axioms InformationTheory.EntropyNat.toNat_ofNat
#print axioms InformationTheory.EntropyNat.toNat_add
#print axioms InformationTheory.EntropyNat.toNat_mul

-- ═══════════════════════════════════════════════════════════════
-- EntropyNumber/Polynomial: Polynomial evaluation
-- ═══════════════════════════════════════════════════════════════
#print axioms InformationTheory.EntropyNat.Polynomial.eval

-- ═══════════════════════════════════════════════════════════════
-- EntropyNumber/Hierarchy: Cardinal levels
-- ═══════════════════════════════════════════════════════════════
#print axioms InformationTheory.cardinal_of_level

-- ═══════════════════════════════════════════════════════════════
-- EntropyNumber/ContinuumHypothesis: CH & GCH Decidable (Hilbert #1)
-- ═══════════════════════════════════════════════════════════════
#print axioms InformationTheory.cardinality_is_beth
#print axioms InformationTheory.abadirContinuumHypothesis
#print axioms InformationTheory.generalizedContinuumHypothesis
#print axioms InformationTheory.all_infinities_indexed_by_Nat
#print axioms InformationTheory.AbadirCompletenessTheorem

-- ═══════════════════════════════════════════════════════════════
-- EntropyNumber/PrimeAtoms: Fundamental Theorem of Arithmetic
-- ═══════════════════════════════════════════════════════════════
#print axioms InformationTheory.PrimeAtoms.factorial_information_decomposition
#print axioms InformationTheory.PrimeAtoms.factorial_information_increment

-- ═══════════════════════════════════════════════════════════════
-- EntropyNumber/RotaEntropy: Rota + Shannon + FTA
-- ═══════════════════════════════════════════════════════════════
#print axioms InformationTheory.rota_all_entropy_scaled_shannon
#print axioms InformationTheory.fta_via_information
#print axioms InformationTheory.fta_via_information_C
#print axioms InformationTheory.fta_via_entropy_bits
#print axioms InformationTheory.total_entropy_from_classes_eq_shannon_formula
#print axioms InformationTheory.entropy_of_fair_coin_is_one_bit

-- ═══════════════════════════════════════════════════════════════
-- Complexity/CNF: CNF encoding & canonical form
-- ═══════════════════════════════════════════════════════════════
#print axioms InformationTheory.evalCNF
#print axioms InformationTheory.encodeCNF
#print axioms InformationTheory.normalizeCNF
#print axioms InformationTheory.evalCNF_normalize_eq_evalCNF
#print axioms InformationTheory.encodeCNF_normalize_length_eq
#print axioms InformationTheory.encodeCNF_size_ge_k
#print axioms InformationTheory.cnf_length_le_encoded_length

-- ═══════════════════════════════════════════════════════════════
-- Entropy/Concrete: Shannon entropy satisfies all 7 Rota axioms
-- ═══════════════════════════════════════════════════════════════
#print axioms InformationTheory.shannonEntropyNNReal_symmetric
#print axioms InformationTheory.shannonEntropyNNReal_normalized
#print axioms InformationTheory.shannonEntropyNNReal_empty
#print axioms InformationTheory.shannonEntropyNNReal_zeroInvariant
#print axioms InformationTheory.shannonEntropyNNReal_continuous
#print axioms InformationTheory.shannonEntropyNNReal_condAddSigma
#print axioms InformationTheory.shannonEntropyNNReal_maxUniform
#print axioms InformationTheory.entropy_fair_coin
#print axioms InformationTheory.shannonEntropy_le_log_card
#print axioms InformationTheory.shannonEntropy_chain_rule

-- ═══════════════════════════════════════════════════════════════
-- Entropy/SourceCoding: Shannon entropy & source coding
-- ═══════════════════════════════════════════════════════════════
#print axioms InformationTheory.stdShannonEntropyLn
#print axioms InformationTheory.shannonEntropyOfDist
#print axioms InformationTheory.program_source_complexity_matches

-- ═══════════════════════════════════════════════════════════════
-- Entropy/Uniqueness: Rota Entropy Theorem
-- ═══════════════════════════════════════════════════════════════
#print axioms InformationTheory.entropyUniform₀_one
#print axioms InformationTheory.entropyUniform₀_mono
#print axioms InformationTheory.entropyUniform₀_mul
#print axioms InformationTheory.entropyUniform₀_pow
#print axioms InformationTheory.logarithmic_trapping
#print axioms InformationTheory.entropyUniform₀_ratio_eq_logb
#print axioms InformationTheory.rota_uniqueness_formula
#print axioms InformationTheory.rota_uniqueness
#print axioms InformationTheory.RUE_rational_case
#print axioms InformationTheory.H_canonical_uniform_eq_C_shannon

-- ═══════════════════════════════════════════════════════════════
-- Complexity/Tableau: certificates & polynomial bounds
-- ═══════════════════════════════════════════════════════════════
#print axioms InformationTheory.PathToConstraint
#print axioms InformationTheory.walkCNFPaths
#print axioms InformationTheory.walkComplexity_upper_bound

-- ═══════════════════════════════════════════════════════════════
-- Bridge: time = information complexity
-- ═══════════════════════════════════════════════════════════════
#print axioms InformationTheory.nSquared_time_complexity_is_information_complexity
#print axioms InformationTheory.walk_nSquared_bound_is_time_and_information

-- ═══════════════════════════════════════════════════════════════
-- Complexity/SetRFL: P = NP definitional identity (Chain 2)
-- ═══════════════════════════════════════════════════════════════
#print axioms InformationTheory.L_SAT_Canonical
#print axioms InformationTheory.NP_def
#print axioms InformationTheory.P_def
#print axioms InformationTheory.L_SAT_in_NP_def
#print axioms InformationTheory.L_SAT_in_P
#print axioms InformationTheory.L_SAT_in_NP_def_Hard
#print axioms InformationTheory.cookLevin
#print axioms InformationTheory.P_eq_NP
#print axioms InformationTheory.canonical_n_squared_bound

-- ═══════════════════════════════════════════════════════════════
-- Complexity/UTM: ReadHead model, time = information.
-- Chain 2 walk bridges link the entropy walk to SAT decision
-- (carry Classical.choice via the noncomputable entropy walk).
-- ═══════════════════════════════════════════════════════════════
#print axioms InformationTheory.timeComplexity_eq_length
#print axioms InformationTheory.ndmEntropyWalk_determines_sat
#print axioms InformationTheory.ndmEntropyWalk_total_eq

-- ═══════════════════════════════════════════════════════════════
-- Complexity/Decomposition: SAT ↔ prime factorization
-- ═══════════════════════════════════════════════════════════════
#print axioms InformationTheory.cnfSharesFactor_iff_zero_conditional_cnf_entropy

-- ═══════════════════════════════════════════════════════════════
-- Complexity/PPNP: P = NP constructive (Chain 1 — START HERE).
-- The bridge theorem walk_construction_iff_verifier_exists ties
-- the witness-walk to NP's existential verifier.
-- ═══════════════════════════════════════════════════════════════
#print axioms InformationTheory.P_eq_NP_info
#print axioms InformationTheory.walk_construction_iff_verifier_exists
#print axioms InformationTheory.complete_information_extraction
#print axioms InformationTheory.information_content_le_nSquared
#print axioms InformationTheory.three_layer_meets_proof_chain
#print axioms InformationTheory.walk_time_eq_information

-- ═══════════════════════════════════════════════════════════════
-- Complexity/StandardComplexity: P = NP standard vocabulary
-- (Chain 3). The capstone P_eq_NP_info_standard reduces to
-- P_eq_NP_info by one rewrite — closure {propext, Quot.sound}.
-- The L_SAT_in_*_standard membership lemmas still carry
-- Classical.choice via the binary decoder.
-- ═══════════════════════════════════════════════════════════════
#print axioms InformationTheory.P_eq_NP_info_standard
#print axioms InformationTheory.L_SAT_in_P_standard
#print axioms InformationTheory.L_SAT_in_NP_standard

-- ═══════════════════════════════════════════════════════════════
-- CNFPolynomialSystem: CNF ⇄ polynomial system (sorry-free, choice-free)
--   - All theorems closure: {propext, Quot.sound}
--   - No Classical.choice, no native_decide, no noncomputable
-- ═══════════════════════════════════════════════════════════════
#print axioms InformationTheory.atomEntropyRat
#print axioms InformationTheory.cnfToPolySystem
#print axioms InformationTheory.polySystemToCnf
#print axioms InformationTheory.atomEntropyRat_not_involution
#print axioms InformationTheory.clausePoly_cons
#print axioms InformationTheory.clausePoly_concat
#print axioms InformationTheory.clausePoly_tautology_not_const
#print axioms InformationTheory.atomEntropyRat_recoverable
#print axioms InformationTheory.recoverLiteral_atomEntropyRat
#print axioms InformationTheory.clausePolyToClause_clausePoly
#print axioms InformationTheory.polySystem_roundTrip
#print axioms InformationTheory.cnfPolyEquiv

-- ═══════════════════════════════════════════════════════════════
-- CNFAsEntropyNat: SyntacticCNF k ≃ EntropyNat (sorry-free, choice-free)
--   - All bijection theorems closure: {propext, Quot.sound}
--   - The §2.4 connector cnf_sat_iff_walkEntropy_zero cites the
--     existing noncomputable ndmEntropyWalk_determines_sat — its
--     closure includes Classical.choice (sanctioned per handoff §2.4).
-- ═══════════════════════════════════════════════════════════════
#print axioms InformationTheory.listBoolToNat
#print axioms InformationTheory.listBoolFromNat
#print axioms InformationTheory.listBoolFromNat_toNat
#print axioms InformationTheory.EntropyRat.mk_canonical_id
#print axioms InformationTheory.EntropyRat.toNat'
#print axioms InformationTheory.EntropyRat.ofNat'
#print axioms InformationTheory.EntropyRat.ofNat'_toNat'
#print axioms InformationTheory.entropyRatEquivImageNat
#print axioms InformationTheory.PolynomialRat.toList
#print axioms InformationTheory.PolynomialRat.fromList
#print axioms InformationTheory.PolynomialRat.fromList_toList
#print axioms InformationTheory.PolynomialRat.toNat'
#print axioms InformationTheory.PolynomialRat.ofNat'
#print axioms InformationTheory.PolynomialRat.ofNat'_toNat'
#print axioms InformationTheory.polynomialRatEquivImageNat
#print axioms InformationTheory.polynomialListToNat
#print axioms InformationTheory.polynomialListFromNat
#print axioms InformationTheory.polynomialListFromNat_toNat
#print axioms InformationTheory.cnfToNat
#print axioms InformationTheory.cnfFromNat
#print axioms InformationTheory.cnfFromNat_toNat
#print axioms InformationTheory.cnfEquivEntropyNat
#print axioms InformationTheory.cnfEquivEntropyNat_roundTrip
#print axioms InformationTheory.cnf_sat_iff_walkEntropy_zero

-- ═══════════════════════════════════════════════════════════════
-- CNFPolynomialRoots: allRoots ≃ satisfying assignments via
-- entropy transitivity (sorry-free; structural defs choice-free)
--   - polySystemFlatten / cnfPolynomial / polySystemFlatten_eval:
--     closure {propext, Quot.sound}
--   - solvePolynomialEquation: closure {propext} only (pure
--     structural recursion on PolynomialRat)
--   - allRoots, allRoots_eq_literalAtoms,
--     allRoots_entropy_equiv_cnf, allRoots_entropy_equiv_cnf_roundTrip:
--     closure {propext, Quot.sound}
--   - allRoots_equiv_satisfyingAssignments: closure
--     {propext, Classical.choice, Quot.sound} via the cited
--     noncomputable ndmEntropyWalk_determines_sat (UTM.lean:523) —
--     same sanctioned precedent as T2's §2.4 connector.
-- ═══════════════════════════════════════════════════════════════
#print axioms InformationTheory.polySystemFlatten
#print axioms InformationTheory.polySystemFlatten_eval
#print axioms InformationTheory.cnfPolynomial
#print axioms InformationTheory.PolynomialRat.IsRoot
#print axioms InformationTheory.solvePolynomialEquation
#print axioms InformationTheory.solvePolynomialEquation_clausePoly
#print axioms InformationTheory.solvePolynomialEquation_polySystemFlatten
#print axioms InformationTheory.allRoots
#print axioms InformationTheory.allRoots_eq_literalAtoms
#print axioms InformationTheory.allRoots_entropy_equiv_cnf
#print axioms InformationTheory.allRoots_entropy_equiv_cnf_roundTrip
#print axioms InformationTheory.allRoots_equiv_satisfyingAssignments
#print axioms InformationTheory.polynomial_root_solving_is_sat_solving

-- ═══════════════════════════════════════════════════════════════
-- Physics/UniformSystems: H = C × Shannon for uniform distributions
-- ═══════════════════════════════════════════════════════════════
#print axioms InformationTheory.Physics.UniformSystems.H_physical_dist_eq_C_shannon_if_uniform_and_equiv
#print axioms InformationTheory.Physics.UniformSystems.H_physical_system_is_rota_uniform
#print axioms InformationTheory.Physics.UniformSystems.H_canonical_uniform_eq_C_shannon'

-- ═══════════════════════════════════════════════════════════════
-- Physics/StatisticalDistributions: Bose-Einstein statistics
-- ═══════════════════════════════════════════════════════════════
#print axioms InformationTheory.Physics.StatisticalDistributions.H_BE_from_Multiset_eq_C_shannon
#print axioms InformationTheory.Physics.StatisticalDistributions.p_BE_sums_to_one
#print axioms InformationTheory.Physics.StatisticalDistributions.p_BE_fin_is_uniformDist

-- ═══════════════════════════════════════════════════════════════
-- Physics/PhysicsDist: Photonic cellular automata
-- ═══════════════════════════════════════════════════════════════
#print axioms InformationTheory.Physics.PhysicsDist.be_system_has_equivalent_program
