# EGPT Build Report — Axiom Flag Matrix (top-level `Lean/build_report.lean`)

> Build invocation: `cd Lean && lake env lean build_report.lean` — exit 0, 11.3 s, 88 theorems printed.
> Source: rehabilitated [`build_report.lean`](build_report.lean), imports [`Archive`](Archive.lean) only (PPNP omitted — see "Deferred" note below).

## Summary

| Check | Value |
|---|---|
| Total theorems | **88** |
| Sorry-free | **88 / 88** ✅ |
| No custom axioms | **88 / 88** ✅ (only `{propext, Classical.choice, Quot.sound}` appear) |
| Classical.choice-free | **20 / 88** ✅ (remaining 68 use `Classical.choice` via Mathlib `ℝ` / measure chains) |
| P = NP capstone (`P_def_eq_NP_def`) closes to `{propext, Quot.sound}` | **1 / 1** ✅ (no `Classical.choice`) |

## Column legend

| Flag | Meaning | ✅ | ❌ |
|---|---|---|---|
| **No custom axioms** | Closure ⊆ Lean built-ins | only `{propext, Classical.choice, Quot.sound}` | any user-declared axiom present |
| **No sorry** | Proof complete | typechecks without `sorry` | `sorry` appears |
| **No Classical.choice** | Choice-free | `Classical.choice` absent | `Classical.choice` appears |
| **`propext`** | Propositional extensionality (Lean built-in, safe) | axiom present | not used |
| **`Quot.sound`** | Quotient soundness (Lean built-in, safe) | axiom present | not used |


## Physics/RealityIsComputation: Reality Is Computation (capstone)

Source: [`Archive/Physics/RealityIsComputation.lean`](Archive/Physics/RealityIsComputation.lean)

| Theorem | No custom axioms | No sorry | No Classical.choice | `propext` | `Quot.sound` |
|---|:--:|:--:|:--:|:--:|:--:|
| `EGPT.Physics.RealityIsComputation.RealityIsComputation'` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Physics.RealityIsComputation.RealityIsComputation` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Physics.RealityIsComputation.ContinuousFieldsAreComputation` | ✅ | ✅ | ❌ | ✅ | ✅ |

## NumberTheory/Core: ParticlePath ↔ ℕ bijection & arithmetic

Source: [`Archive/NumberTheory/Core.lean`](Archive/NumberTheory/Core.lean)

| Theorem | No custom axioms | No sorry | No Classical.choice | `propext` | `Quot.sound` |
|---|:--:|:--:|:--:|:--:|:--:|
| `EGPT.NumberTheory.Core.equivParticlePathToNat` | ✅ | ✅ | ✅ | ✅ | — |
| `EGPT.NumberTheory.Core.fromNat` | ✅ | ✅ | ✅ | ✅ | — |
| `EGPT.NumberTheory.Core.toNat` | ✅ | ✅ | ✅ | — | — |
| `EGPT.NumberTheory.Core.left_inv` | ✅ | ✅ | ✅ | ✅ | — |
| `EGPT.NumberTheory.Core.right_inv` | ✅ | ✅ | ✅ | ✅ | — |
| `EGPT.NumberTheory.Core.toNat_add_ParticlePath` | ✅ | ✅ | ✅ | ✅ | — |
| `EGPT.NumberTheory.Core.toNat_mul_ParticlePath` | ✅ | ✅ | ✅ | ✅ | — |
| `EGPT.NumberTheory.Core.EGPT_Polynomial.eval` | ✅ | ✅ | ✅ | ✅ | — |
| `EGPT.NumberTheory.Core.cardinal_of_egpt_level` | ✅ | ✅ | ❌ | ✅ | ✅ |

## NumberTheory/ContinuumHypothesis: CH & GCH Decidable (Hilbert #1)

Source: [`Archive/NumberTheory/ContinuumHypothesis.lean`](Archive/NumberTheory/ContinuumHypothesis.lean)

| Theorem | No custom axioms | No sorry | No Classical.choice | `propext` | `Quot.sound` |
|---|:--:|:--:|:--:|:--:|:--:|
| `EGPT.NumberTheory.ContinuumHypothesis.EGPT_cardinality_is_beth` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.NumberTheory.ContinuumHypothesis.EGPT_ContinuumHypothesis` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.NumberTheory.ContinuumHypothesis.EGPT_GeneralizedContinuumHypothesis` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.NumberTheory.ContinuumHypothesis.EGPT_all_infinities_indexed_by_Nat` | ✅ | ✅ | ❌ | ✅ | ✅ |

## NumberTheory/Filter: RejectionFilter & probability

Source: [`Archive/NumberTheory/Filter.lean`](Archive/NumberTheory/Filter.lean)

| Theorem | No custom axioms | No sorry | No Classical.choice | `propext` | `Quot.sound` |
|---|:--:|:--:|:--:|:--:|:--:|
| `EGPT.NumberTheory.Filter.RejectionFilter.get_witness` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.NumberTheory.Filter.RejectionFilter.of_satisfying_example` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.NumberTheory.Filter.distOfRejectionFilter` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.NumberTheory.Filter.eventsPMF` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.NumberTheory.Filter.construct_real_solution_space` | ✅ | ✅ | ❌ | ✅ | ✅ |

## NumberTheory/Analysis: Fundamental Theorem of Arithmetic (EGPT)

Source: [`Archive/NumberTheory/Analysis.lean`](Archive/NumberTheory/Analysis.lean)

| Theorem | No custom axioms | No sorry | No Classical.choice | `propext` | `Quot.sound` |
|---|:--:|:--:|:--:|:--:|:--:|
| `RET_All_Entropy_Is_Scaled_Shannon_Entropy` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT_Fundamental_Theorem_of_Arithmetic_via_Information` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT_Fundamental_Theorem_of_Arithmetic_via_Entropy_Bits` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `total_entropy_from_classes_eq_shannon_formula` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `PrimeAtoms.factorial_information_decomposition` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `PrimeAtoms.factorial_information_increment` | ✅ | ✅ | ❌ | ✅ | ✅ |

## Constraints: CNF encoding & canonical form

Source: [`Archive/Constraints.lean`](Archive/Constraints.lean)

| Theorem | No custom axioms | No sorry | No Classical.choice | `propext` | `Quot.sound` |
|---|:--:|:--:|:--:|:--:|:--:|
| `EGPT.Constraints.evalCNF` | ✅ | ✅ | ✅ | ✅ | — |
| `EGPT.Constraints.encodeCNF` | ✅ | ✅ | ✅ | — | — |
| `EGPT.Constraints.normalizeCNF` | ✅ | ✅ | ✅ | ✅ | ✅ |
| `EGPT.Constraints.evalCNF_normalize_eq_evalCNF` | ✅ | ✅ | ✅ | ✅ | ✅ |
| `EGPT.Constraints.encodeCNF_normalize_length_eq` | ✅ | ✅ | ✅ | ✅ | ✅ |
| `EGPT.Constraints.encodeCNF_size_ge_k` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Constraints.cnf_length_le_encoded_length` | ✅ | ✅ | ❌ | ✅ | ✅ |

## Entropy/Common: Shannon entropy & source coding

Source: [`Archive/Entropy/Common.lean`](Archive/Entropy/Common.lean)

| Theorem | No custom axioms | No sorry | No Classical.choice | `propext` | `Quot.sound` |
|---|:--:|:--:|:--:|:--:|:--:|
| `EGPT.Entropy.Common.ShannonEntropyOfDist` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Entropy.Common.stdShannonEntropyLn` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Entropy.Common.stdShannonEntropyLn_uniform_eq_log_card` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Entropy.Common.rect_program_for_dist` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Entropy.Common.RECT_Entropy_to_Program` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Entropy.Common.IRECT_RECT_inverse_for_integer_complexity` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Entropy.Common.program_source_complexity_matches` | ✅ | ✅ | ❌ | ✅ | ✅ |

## Entropy/RET: Rota Entropy Theorem

Source: [`Archive/Entropy/RET.lean`](Archive/Entropy/RET.lean)

| Theorem | No custom axioms | No sorry | No Classical.choice | `propext` | `Quot.sound` |
|---|:--:|:--:|:--:|:--:|:--:|
| `EGPT.Entropy.RET.f0_1_eq_0` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Entropy.RET.f0_mono` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Entropy.RET.f0_mul_eq_add_f0` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Entropy.RET.uniformEntropy_power_law` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Entropy.RET.logarithmic_trapping` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Entropy.RET.uniformEntropy_ratio_eq_logb` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Entropy.RET.RotaUniformTheorem_formula_with_C_constant` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Entropy.RET.RotaUniformTheorem` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Entropy.RET.RUE_rational_case` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Entropy.RET.H_canonical_uniform_eq_C_shannon` | ✅ | ✅ | ❌ | ✅ | ✅ |

## Entropy/H: Shannon entropy properties & chain rule

Source: [`Archive/Entropy/H.lean`](Archive/Entropy/H.lean)

| Theorem | No custom axioms | No sorry | No Classical.choice | `propext` | `Quot.sound` |
|---|:--:|:--:|:--:|:--:|:--:|
| `EGPT.Entropy.H.h_canonical_is_symmetric` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Entropy.H.h_canonical_is_normalized` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Entropy.H.h_canonical_is_zero_on_empty` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Entropy.H.h_canonical_is_zero_invariance` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Entropy.H.h_canonical_is_continuous` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Entropy.H.h_canonical_is_cond_add_sigma` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Entropy.H.h_canonical_is_max_uniform` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Entropy.H.entropy_of_fair_coin_is_one_bit` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Entropy.H.stdShannonEntropyLn_le_log_card` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Entropy.H.stdShannonEntropyLn_chain_rule_sigma` | ✅ | ✅ | ❌ | ✅ | ✅ |

## Complexity/Core & TableauFromCNF: certificates & polynomial bounds

Source: [`Archive/Complexity/Core.lean + TableauFromCNF.lean`](Archive/Complexity/Core.lean + TableauFromCNF.lean)

| Theorem | No custom axioms | No sorry | No Classical.choice | `propext` | `Quot.sound` |
|---|:--:|:--:|:--:|:--:|:--:|
| `EGPT.Complexity.PathToConstraint` | ✅ | ✅ | ✅ | ✅ | — |
| `EGPT.Complexity.walkCNFPaths` | ✅ | ✅ | ✅ | ✅ | — |
| `EGPT.Complexity.walkComplexity_upper_bound` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Complexity.walkComplexity_eq_sum_of_paths` | ✅ | ✅ | ✅ | ✅ | — |

## Complexity/ComplexityInformationBridge: time = information complexity

Source: [`Archive/Complexity/Interpretation.lean`](Archive/Complexity/Interpretation.lean)

| Theorem | No custom axioms | No sorry | No Classical.choice | `propext` | `Quot.sound` |
|---|:--:|:--:|:--:|:--:|:--:|
| `EGPT.Complexity.Interpretation.nSquared_time_complexity_is_information_complexity` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Complexity.Interpretation.walk_nSquared_bound_is_time_and_information` | ✅ | ✅ | ❌ | ✅ | ✅ |

## Complexity/SetRFL: P = NP proof chain (definitional identity)

Source: [`Archive/Complexity/SetRFL.lean`](Archive/Complexity/SetRFL.lean)

| Theorem | No custom axioms | No sorry | No Classical.choice | `propext` | `Quot.sound` |
|---|:--:|:--:|:--:|:--:|:--:|
| `EGPT.Complexity.SetRFL.L_SAT_Canonical` | ✅ | ✅ | ✅ | ✅ | — |
| `EGPT.Complexity.SetRFL.NP_def` | ✅ | ✅ | ✅ | ✅ | — |
| `EGPT.Complexity.SetRFL.P_def` | ✅ | ✅ | ✅ | ✅ | — |
| `EGPT.Complexity.SetRFL.L_SAT_in_NP_def` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Complexity.SetRFL.L_SAT_in_P_def` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Complexity.SetRFL.L_SAT_in_NP_def_Hard` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Complexity.SetRFL.EGPT_CookLevin_def_Theorem` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Complexity.SetRFL.P_def_eq_NP_def` | ✅ | ✅ | ✅ | ✅ | ✅ |

## Complexity/UTM: ReadHead model, time = information

Source: [`Archive/Complexity/UTM.lean`](Archive/Complexity/UTM.lean)

| Theorem | No custom axioms | No sorry | No Classical.choice | `propext` | `Quot.sound` |
|---|:--:|:--:|:--:|:--:|:--:|
| `EGPT.Complexity.UTM.timeComplexity_eq_length` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Complexity.UTM.time_eq_information_eq_complexity` | ✅ | ✅ | ❌ | ✅ | ✅ |

## Complexity/PPNP: P = NP (constructive information-theoretic chain)

Source: [`Archive/Complexity/PPNP.lean`](Archive/Complexity/PPNP.lean)

| Theorem | No custom axioms | No sorry | No Classical.choice | `propext` | `Quot.sound` |
|---|:--:|:--:|:--:|:--:|:--:|
| `EGPT.Complexity.PPNP.P_eq_NP` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Complexity.PPNP.complete_information_extraction` | ✅ | ✅ | ❌ | ✅ | ✅ |

## Physics/Common: physical entropy

Source: [`Archive/Physics/Common.lean`](Archive/Physics/Common.lean)

| Theorem | No custom axioms | No sorry | No Classical.choice | `propext` | `Quot.sound` |
|---|:--:|:--:|:--:|:--:|:--:|
| `EGPT.Physics.Common.H_physical_system` | ✅ | ✅ | ❌ | ✅ | ✅ |

## Physics/UniformSystems: uniform distribution proofs

Source: [`Archive/Physics/UniformSystems.lean`](Archive/Physics/UniformSystems.lean)

| Theorem | No custom axioms | No sorry | No Classical.choice | `propext` | `Quot.sound` |
|---|:--:|:--:|:--:|:--:|:--:|
| `EGPT.Physics.UniformSystems.H_physical_dist_eq_C_shannon_if_uniform_and_equiv` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Physics.UniformSystems.H_physical_system_is_rota_uniform` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Physics.UniformSystems.H_canonical_uniform_eq_C_shannon` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Physics.UniformSystems.stdShannonEntropyLn_comp_equiv` | ✅ | ✅ | ❌ | ✅ | ✅ |

## Physics/BoseEinstein: Bose-Einstein statistics

Source: [`Archive/Physics/BoseEinstein.lean`](Archive/Physics/BoseEinstein.lean)

| Theorem | No custom axioms | No sorry | No Classical.choice | `propext` | `Quot.sound` |
|---|:--:|:--:|:--:|:--:|:--:|
| `EGPT.Physics.BE.H_BE_from_Multiset_eq_C_shannon` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Physics.BE.p_BE_sums_to_one` | ✅ | ✅ | ❌ | ✅ | ✅ |
| `EGPT.Physics.BE.p_BE_fin_is_uniformDist` | ✅ | ✅ | ❌ | ✅ | ✅ |

## Physics/PhotonicCA: photonic cellular automata

Source: [`Archive/Physics/PhotonicCA.lean`](Archive/Physics/PhotonicCA.lean)

| Theorem | No custom axioms | No sorry | No Classical.choice | `propext` | `Quot.sound` |
|---|:--:|:--:|:--:|:--:|:--:|
| `EGPT.Physics.PCA.be_system_has_equivalent_program` | ✅ | ✅ | ❌ | ✅ | ✅ |

---

## Deferred (legacy PPNP namespace)

The original `build_report.lean` also referenced two theorems from `PPNP/Proofs/WaveParticleDualityDisproved.lean`:

- `PhotonDistributionsHaveClassicalExplanationFromIndividualPaths`
- `Wave_Particle_Duality_Disproved_QED`

These are commented out pending a parallel rehabilitation of `PPNP/Proofs/*.lean` (those files still use the pre-rename `import EGPT.*` module paths, which were moved under `Archive/`). The theorems themselves are unchanged in source — they're just not currently importable from this build_report.

## Where Classical.choice appears (and where it does not)

### Classical.choice-free (20 theorems) ✅

These close to `{propext}`, `{propext, Quot.sound}`, or `{}` — the most constructive layer.

| Theorem | Section |
|---|---|
| `EGPT.NumberTheory.Core.equivParticlePathToNat` | NumberTheory/Core: ParticlePath ↔ ℕ bijection & arithmetic |
| `EGPT.NumberTheory.Core.fromNat` | NumberTheory/Core: ParticlePath ↔ ℕ bijection & arithmetic |
| `EGPT.NumberTheory.Core.toNat` | NumberTheory/Core: ParticlePath ↔ ℕ bijection & arithmetic |
| `EGPT.NumberTheory.Core.left_inv` | NumberTheory/Core: ParticlePath ↔ ℕ bijection & arithmetic |
| `EGPT.NumberTheory.Core.right_inv` | NumberTheory/Core: ParticlePath ↔ ℕ bijection & arithmetic |
| `EGPT.NumberTheory.Core.toNat_add_ParticlePath` | NumberTheory/Core: ParticlePath ↔ ℕ bijection & arithmetic |
| `EGPT.NumberTheory.Core.toNat_mul_ParticlePath` | NumberTheory/Core: ParticlePath ↔ ℕ bijection & arithmetic |
| `EGPT.NumberTheory.Core.EGPT_Polynomial.eval` | NumberTheory/Core: ParticlePath ↔ ℕ bijection & arithmetic |
| `EGPT.Constraints.evalCNF` | Constraints: CNF encoding & canonical form |
| `EGPT.Constraints.encodeCNF` | Constraints: CNF encoding & canonical form |
| `EGPT.Constraints.normalizeCNF` | Constraints: CNF encoding & canonical form |
| `EGPT.Constraints.evalCNF_normalize_eq_evalCNF` | Constraints: CNF encoding & canonical form |
| `EGPT.Constraints.encodeCNF_normalize_length_eq` | Constraints: CNF encoding & canonical form |
| `EGPT.Complexity.PathToConstraint` | Complexity/Core & TableauFromCNF: certificates & polynomial bounds |
| `EGPT.Complexity.walkCNFPaths` | Complexity/Core & TableauFromCNF: certificates & polynomial bounds |
| `EGPT.Complexity.walkComplexity_eq_sum_of_paths` | Complexity/Core & TableauFromCNF: certificates & polynomial bounds |
| `EGPT.Complexity.SetRFL.L_SAT_Canonical` | Complexity/SetRFL: P = NP proof chain (definitional identity) |
| `EGPT.Complexity.SetRFL.NP_def` | Complexity/SetRFL: P = NP proof chain (definitional identity) |
| `EGPT.Complexity.SetRFL.P_def` | Complexity/SetRFL: P = NP proof chain (definitional identity) |
| `EGPT.Complexity.SetRFL.P_def_eq_NP_def` | Complexity/SetRFL: P = NP proof chain (definitional identity) |

### Uses Classical.choice (68 theorems)

Still inside the built-in axiom set — no custom axiom and no `sorry`. `Classical.choice` enters via Mathlib's `ℝ` and measure-theoretic chains.

| Theorem | Section |
|---|---|
| `EGPT.Physics.RealityIsComputation.RealityIsComputation'` | Physics/RealityIsComputation: Reality Is Computation (capstone) |
| `EGPT.Physics.RealityIsComputation.RealityIsComputation` | Physics/RealityIsComputation: Reality Is Computation (capstone) |
| `EGPT.Physics.RealityIsComputation.ContinuousFieldsAreComputation` | Physics/RealityIsComputation: Reality Is Computation (capstone) |
| `EGPT.NumberTheory.Core.cardinal_of_egpt_level` | NumberTheory/Core: ParticlePath ↔ ℕ bijection & arithmetic |
| `EGPT.NumberTheory.ContinuumHypothesis.EGPT_cardinality_is_beth` | NumberTheory/ContinuumHypothesis: CH & GCH Decidable (Hilbert #1) |
| `EGPT.NumberTheory.ContinuumHypothesis.EGPT_ContinuumHypothesis` | NumberTheory/ContinuumHypothesis: CH & GCH Decidable (Hilbert #1) |
| `EGPT.NumberTheory.ContinuumHypothesis.EGPT_GeneralizedContinuumHypothesis` | NumberTheory/ContinuumHypothesis: CH & GCH Decidable (Hilbert #1) |
| `EGPT.NumberTheory.ContinuumHypothesis.EGPT_all_infinities_indexed_by_Nat` | NumberTheory/ContinuumHypothesis: CH & GCH Decidable (Hilbert #1) |
| `EGPT.NumberTheory.Filter.RejectionFilter.get_witness` | NumberTheory/Filter: RejectionFilter & probability |
| `EGPT.NumberTheory.Filter.RejectionFilter.of_satisfying_example` | NumberTheory/Filter: RejectionFilter & probability |
| `EGPT.NumberTheory.Filter.distOfRejectionFilter` | NumberTheory/Filter: RejectionFilter & probability |
| `EGPT.NumberTheory.Filter.eventsPMF` | NumberTheory/Filter: RejectionFilter & probability |
| `EGPT.NumberTheory.Filter.construct_real_solution_space` | NumberTheory/Filter: RejectionFilter & probability |
| `RET_All_Entropy_Is_Scaled_Shannon_Entropy` | NumberTheory/Analysis: Fundamental Theorem of Arithmetic (EGPT) |
| `EGPT_Fundamental_Theorem_of_Arithmetic_via_Information` | NumberTheory/Analysis: Fundamental Theorem of Arithmetic (EGPT) |
| `EGPT_Fundamental_Theorem_of_Arithmetic_via_Entropy_Bits` | NumberTheory/Analysis: Fundamental Theorem of Arithmetic (EGPT) |
| `total_entropy_from_classes_eq_shannon_formula` | NumberTheory/Analysis: Fundamental Theorem of Arithmetic (EGPT) |
| `PrimeAtoms.factorial_information_decomposition` | NumberTheory/Analysis: Fundamental Theorem of Arithmetic (EGPT) |
| `PrimeAtoms.factorial_information_increment` | NumberTheory/Analysis: Fundamental Theorem of Arithmetic (EGPT) |
| `EGPT.Constraints.encodeCNF_size_ge_k` | Constraints: CNF encoding & canonical form |
| `EGPT.Constraints.cnf_length_le_encoded_length` | Constraints: CNF encoding & canonical form |
| `EGPT.Entropy.Common.ShannonEntropyOfDist` | Entropy/Common: Shannon entropy & source coding |
| `EGPT.Entropy.Common.stdShannonEntropyLn` | Entropy/Common: Shannon entropy & source coding |
| `EGPT.Entropy.Common.stdShannonEntropyLn_uniform_eq_log_card` | Entropy/Common: Shannon entropy & source coding |
| `EGPT.Entropy.Common.rect_program_for_dist` | Entropy/Common: Shannon entropy & source coding |
| `EGPT.Entropy.Common.RECT_Entropy_to_Program` | Entropy/Common: Shannon entropy & source coding |
| `EGPT.Entropy.Common.IRECT_RECT_inverse_for_integer_complexity` | Entropy/Common: Shannon entropy & source coding |
| `EGPT.Entropy.Common.program_source_complexity_matches` | Entropy/Common: Shannon entropy & source coding |
| `EGPT.Entropy.RET.f0_1_eq_0` | Entropy/RET: Rota Entropy Theorem |
| `EGPT.Entropy.RET.f0_mono` | Entropy/RET: Rota Entropy Theorem |
| `EGPT.Entropy.RET.f0_mul_eq_add_f0` | Entropy/RET: Rota Entropy Theorem |
| `EGPT.Entropy.RET.uniformEntropy_power_law` | Entropy/RET: Rota Entropy Theorem |
| `EGPT.Entropy.RET.logarithmic_trapping` | Entropy/RET: Rota Entropy Theorem |
| `EGPT.Entropy.RET.uniformEntropy_ratio_eq_logb` | Entropy/RET: Rota Entropy Theorem |
| `EGPT.Entropy.RET.RotaUniformTheorem_formula_with_C_constant` | Entropy/RET: Rota Entropy Theorem |
| `EGPT.Entropy.RET.RotaUniformTheorem` | Entropy/RET: Rota Entropy Theorem |
| `EGPT.Entropy.RET.RUE_rational_case` | Entropy/RET: Rota Entropy Theorem |
| `EGPT.Entropy.RET.H_canonical_uniform_eq_C_shannon` | Entropy/RET: Rota Entropy Theorem |
| `EGPT.Entropy.H.h_canonical_is_symmetric` | Entropy/H: Shannon entropy properties & chain rule |
| `EGPT.Entropy.H.h_canonical_is_normalized` | Entropy/H: Shannon entropy properties & chain rule |
| `EGPT.Entropy.H.h_canonical_is_zero_on_empty` | Entropy/H: Shannon entropy properties & chain rule |
| `EGPT.Entropy.H.h_canonical_is_zero_invariance` | Entropy/H: Shannon entropy properties & chain rule |
| `EGPT.Entropy.H.h_canonical_is_continuous` | Entropy/H: Shannon entropy properties & chain rule |
| `EGPT.Entropy.H.h_canonical_is_cond_add_sigma` | Entropy/H: Shannon entropy properties & chain rule |
| `EGPT.Entropy.H.h_canonical_is_max_uniform` | Entropy/H: Shannon entropy properties & chain rule |
| `EGPT.Entropy.H.entropy_of_fair_coin_is_one_bit` | Entropy/H: Shannon entropy properties & chain rule |
| `EGPT.Entropy.H.stdShannonEntropyLn_le_log_card` | Entropy/H: Shannon entropy properties & chain rule |
| `EGPT.Entropy.H.stdShannonEntropyLn_chain_rule_sigma` | Entropy/H: Shannon entropy properties & chain rule |
| `EGPT.Complexity.walkComplexity_upper_bound` | Complexity/Core & TableauFromCNF: certificates & polynomial bounds |
| `EGPT.Complexity.Interpretation.nSquared_time_complexity_is_information_complexity` | Complexity/ComplexityInformationBridge: time = information complexity |
| `EGPT.Complexity.Interpretation.walk_nSquared_bound_is_time_and_information` | Complexity/ComplexityInformationBridge: time = information complexity |
| `EGPT.Complexity.SetRFL.L_SAT_in_NP_def` | Complexity/SetRFL: P = NP proof chain (definitional identity) |
| `EGPT.Complexity.SetRFL.L_SAT_in_P_def` | Complexity/SetRFL: P = NP proof chain (definitional identity) |
| `EGPT.Complexity.SetRFL.L_SAT_in_NP_def_Hard` | Complexity/SetRFL: P = NP proof chain (definitional identity) |
| `EGPT.Complexity.SetRFL.EGPT_CookLevin_def_Theorem` | Complexity/SetRFL: P = NP proof chain (definitional identity) |
| `EGPT.Complexity.UTM.timeComplexity_eq_length` | Complexity/UTM: ReadHead model, time = information |
| `EGPT.Complexity.UTM.time_eq_information_eq_complexity` | Complexity/UTM: ReadHead model, time = information |
| `EGPT.Complexity.PPNP.P_eq_NP` | Complexity/PPNP: P = NP (constructive information-theoretic chain) |
| `EGPT.Complexity.PPNP.complete_information_extraction` | Complexity/PPNP: P = NP (constructive information-theoretic chain) |
| `EGPT.Physics.Common.H_physical_system` | Physics/Common: physical entropy |
| `EGPT.Physics.UniformSystems.H_physical_dist_eq_C_shannon_if_uniform_and_equiv` | Physics/UniformSystems: uniform distribution proofs |
| `EGPT.Physics.UniformSystems.H_physical_system_is_rota_uniform` | Physics/UniformSystems: uniform distribution proofs |
| `EGPT.Physics.UniformSystems.H_canonical_uniform_eq_C_shannon` | Physics/UniformSystems: uniform distribution proofs |
| `EGPT.Physics.UniformSystems.stdShannonEntropyLn_comp_equiv` | Physics/UniformSystems: uniform distribution proofs |
| `EGPT.Physics.BE.H_BE_from_Multiset_eq_C_shannon` | Physics/BoseEinstein: Bose-Einstein statistics |
| `EGPT.Physics.BE.p_BE_sums_to_one` | Physics/BoseEinstein: Bose-Einstein statistics |
| `EGPT.Physics.BE.p_BE_fin_is_uniformDist` | Physics/BoseEinstein: Bose-Einstein statistics |
| `EGPT.Physics.PCA.be_system_has_equivalent_program` | Physics/PhotonicCA: photonic cellular automata |
