--import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog -- For negMulLog, Real.log
--import Mathlib.Algebra.BigOperators.Fin -- For sum over Fin n
--import Mathlib.Data.Fin.Basic -- Basic Fin definitions and lemmas
--import Mathlib.Data.Fintype.Fin -- Instances for Fin n
--import Mathlib.Algebra.GroupWithZero.Units.Basic -- Provides mul_inv_cancel₀
--import Mathlib.Data.Nat.Basic -- Basic Nat properties
import Mathlib.Data.Sym.Card

--import Mathlib.Data.Multiset.Bind
--import Mathlib.Data.Multiset.Basic
--import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Archive.Core
import Archive.Entropy.Common
import Archive.Physics.Common
import Archive.Entropy.RET
import Archive.Physics.UniformSystems
import Archive.Physics.BoseEinstein
import Archive.Physics.FermiDirac
import Archive.Physics.MaxwellBoltzmann

namespace EGPT.Physics.PhysicsDist

open EGPT.Entropy.RET

open Multiset NNReal
open EGPT
open EGPT.Entropy.Common
open EGPT.Physics.Common
open EGPT.Physics.UniformSystems
open EGPT.Physics.BE
open EGPT.Physics.FD
open EGPT.Physics.MB

/-! # Formalizing "Physics Distribution" To Mean A Combinatorial State Spaces, Or, Counting Problem Under Constraints

## Three Disjoint Constraint Cases Describe All Physical Systems

> Let $N$ boxes (states) and $M$ balls (particles). A microstate is a way of allocating the $M$ balls among the $N$ boxes. For convenience, we will refer to distinguishability interchangeably with the notion of constraint—e.g., distinguishable = constrained (trackable), indistinguishable = unconstrained (untrackable).
>
> There are exactly three—and only three—canonical constraint families for how balls may occupy boxes in statistical mechanics:
>
> * **Maxwell-Boltzmann (MB)**: Balls are **distinguishable** (constrained), boxes are **distinguishable** (constrained). Any number of balls may occupy a box.
> * **Fermi-Dirac (FD)**: Balls are **indistinguishable** (unconstrained), boxes are **distinguishable** (constrained), **with at most one ball per box** (exclusive occupancy constraint).
> * **Bose-Einstein (BE)**: Balls are **indistinguishable** (unconstrained), boxes are **distinguishable** (constrained), **with any number of balls per box** (inclusive occupancy).
>
> Note: If both balls and boxes are **indistinguishable**, the configuration space corresponds to the set of **integer partitions** of $M$, not to any of the three classical statistics. This case is **not** described by a multinomial distribution since multisets require distinguishable labels on the boxes.

This file consumes the proofs from each of the three statistics files (BoseEinstein.lean, FermiDirac.lean, and MaxwellBoltzmann.lean) which each establish equivalence to:
* the combinatorial state space (`OmegaC`), which is the standard combinatorial object: multisets of a fixed size (`SymFin`).
* the uniform distribution over the combinatorial state space (`OmegaC`), which is the standard uniform distribution over multisets of a fixed size (`SymFin`).
* equivlance to Shannon entropy via Rota's Entropy Theorem.

Consequently, leveraging the proofs in UniformSystems.lean allowing the additivity of uniform distributions and the the conditional entropy additivity proofs in Entropy.Common.lean, we define PhysicsDist as any linear combination of the three canonical distributions (MB, FD, BE) and further that this generalized distribution is mathematically equivalent to a combinatorial state space (multisets) i.e. computation of the evolution a physics distribution is the computation of a counting problem under constraints.


-/



noncomputable def C_axiom_val : ℝ := (C_physical_NNReal : ℝ)
-- Define an enum for the type of statistical system
inductive StatSystemType | BoseEinstein | FermiDirac | MaxwellBoltzmann

-- Define parameters for each system. For simplicity, (N, M) for all.
-- More complex systems might need richer parameter types.
structure SystemParams where
  N : ℕ
  M : ℕ
  -- Could add constraints like N_pos : N > 0, etc., if always needed
  -- Or pass h_domain_valid separately.

/--
Calculates the entropy of a given statistical system (BE, FD, MB)
using the axiomatic H_physical_system.
The result is a Real value.
This function will dispatch to the appropriate underlying probability distribution
and apply H_axiom.
-/
noncomputable def entropy_of_stat_system (type : StatSystemType) (params : SystemParams)
    (_h_domain_valid : params.N ≠ 0 ∨ params.M = 0) : ℝ :=
  match type with
  | StatSystemType.BoseEinstein =>
    -- p_UD_fin is the uniform distribution on Fin (Fintype.card (OmegaUD N M))
    -- Using EGPT.Physics.Common.H_physical_system directly
    (EGPT.Physics.Common.H_physical_system (EGPT.Physics.UniformSystems.p_UD_fin params.N params.M) : ℝ)
  | StatSystemType.FermiDirac =>
    (EGPT.Physics.Common.H_physical_system (EGPT.Physics.FD.p_FD_fin params.N params.M) : ℝ)
  | StatSystemType.MaxwellBoltzmann =>
    (EGPT.Physics.Common.H_physical_system (EGPT.Physics.MB.p_MB_fin params.N params.M) : ℝ)

/--
Calculates the standard Shannon entropy (ln-based) of a given statistical system's
canonical (uniform) probability distribution.
Result is Real.
-/
noncomputable def shannon_entropy_of_stat_system (type : StatSystemType) (params : SystemParams)
    (_h_domain_valid : params.N ≠ 0 ∨ params.M = 0) : ℝ :=
  match type with
  | StatSystemType.BoseEinstein =>
    stdShannonEntropyLn (EGPT.Physics.UniformSystems.p_UD_fin params.N params.M)
  | StatSystemType.FermiDirac =>
    stdShannonEntropyLn (EGPT.Physics.FD.p_FD_fin params.N params.M)
  | StatSystemType.MaxwellBoltzmann =>
    stdShannonEntropyLn (EGPT.Physics.MB.p_MB_fin params.N params.M)

/--
Theorem: The axiomatic entropy of a Bose-Einstein system is C_axiom * its Shannon entropy.
-/
theorem entropy_BE_eq_C_shannon (params : SystemParams)
    (h_domain_valid : params.N ≠ 0 ∨ params.M = 0) :
    entropy_of_stat_system StatSystemType.BoseEinstein params h_domain_valid =
    C_axiom_val * shannon_entropy_of_stat_system StatSystemType.BoseEinstein params h_domain_valid := by
  -- 1. Unfold definitions
  simp only [entropy_of_stat_system, shannon_entropy_of_stat_system]
  -- Goal is now:
  -- (EGPT.Physics.Common.H_physical_system (p_UD_fin params.N params.M) : ℝ) =
  --  C_axiom_val * stdShannonEntropyLn (p_UD_fin params.N params.M)

  -- 2. This directly matches the statement of H_BE_from_Multiset_eq_C_shannon
  --    Need to ensure the C_axiom_val here is the same as the one used in that theorem.
  --    `H_BE_from_Multiset_eq_C_shannon` uses `C_constant_real EGPT.Physics.Common.H_physical_system_has_Rota_entropy_properties`
  --    Our `C_axiom_val` is defined identically.
  --    `axiomatic_entropy_of_stat_system` now directly uses `EGPT.Physics.Common.H_physical_system`.
  exact H_BE_from_Multiset_eq_C_shannon params.N params.M h_domain_valid

/--
Theorem: The axiomatic entropy of a Fermi-Dirac system is C_axiom * its Shannon entropy.
Note: FD requires `M ≤ N` (at most one particle per box), which is stronger than
the general domain validity condition `N ≠ 0 ∨ M = 0`.
-/
theorem entropy_FD_eq_C_shannon (params : SystemParams)
    (_h_domain_valid : params.N ≠ 0 ∨ params.M = 0)
    (h_fd : params.M ≤ params.N) :
    entropy_of_stat_system StatSystemType.FermiDirac params _h_domain_valid =
    C_axiom_val * shannon_entropy_of_stat_system StatSystemType.FermiDirac params _h_domain_valid := by
  simp only [entropy_of_stat_system, shannon_entropy_of_stat_system]
  exact H_FD_eq_C_shannon params.N params.M h_fd

/--
Theorem: The axiomatic entropy of a Maxwell-Boltzmann system is C_axiom * its Shannon entropy.
-/
theorem entropy_MB_eq_C_shannon (params : SystemParams)
    (h_domain_valid : params.N ≠ 0 ∨ params.M = 0) :
    entropy_of_stat_system StatSystemType.MaxwellBoltzmann params h_domain_valid =
    C_axiom_val * shannon_entropy_of_stat_system StatSystemType.MaxwellBoltzmann params h_domain_valid := by
  simp only [entropy_of_stat_system, shannon_entropy_of_stat_system]
  exact H_MB_eq_C_shannon params.N params.M h_domain_valid


-- Structure to hold weights for each system type.
-- These are NNReal because they often represent probabilities or positive contributions.
structure SystemWeights where
  w_BE : NNReal
  w_FD : NNReal
  w_MB : NNReal
  -- Optional: constraint that they sum to 1 if representing probabilities of system type
  -- h_sum_to_one : w_BE + w_FD + w_MB = 1 -- If it's a convex combination

/--
Defines the total entropy of a "Physics Distribution" as a weighted sum
of the axiomatic entropies of its constituent statistical components (BE, FD, MB).
`params_map` provides the (N, M) parameters for each type of system.
`valid_map` provides the domain validity proofs.
-/
noncomputable def H_physics_dist_linear_combination
    (weights : SystemWeights)
    (params_BE : SystemParams) (h_valid_BE : params_BE.N ≠ 0 ∨ params_BE.M = 0)
    (params_FD : SystemParams) (h_valid_FD : params_FD.N ≠ 0 ∨ params_FD.M = 0) -- Placeholder
    (params_MB : SystemParams) (h_valid_MB : params_MB.N ≠ 0 ∨ params_MB.M = 0) -- Placeholder
    : ℝ :=
  (weights.w_BE : ℝ) * entropy_of_stat_system StatSystemType.BoseEinstein params_BE h_valid_BE +
  (weights.w_FD : ℝ) * entropy_of_stat_system StatSystemType.FermiDirac params_FD h_valid_FD + -- Will use actual FD params
  (weights.w_MB : ℝ) * entropy_of_stat_system StatSystemType.MaxwellBoltzmann params_MB h_valid_MB -- Will use actual MB params

/--
The "Generalized PhysicsDistCShannon definition".
This is C_axiom multiplied by the weighted sum of the Shannon entropies
of the constituent statistical components.
-/
noncomputable def generalized_PhysicsDist_C_times_Shannon
    (weights : SystemWeights)
    (params_BE : SystemParams) (h_valid_BE : params_BE.N ≠ 0 ∨ params_BE.M = 0)
    (params_FD : SystemParams) (h_valid_FD : params_FD.N ≠ 0 ∨ params_FD.M = 0) -- Placeholder
    (params_MB : SystemParams) (h_valid_MB : params_MB.N ≠ 0 ∨ params_MB.M = 0) -- Placeholder
    : ℝ :=
  C_axiom_val * (
    (weights.w_BE : ℝ) * shannon_entropy_of_stat_system StatSystemType.BoseEinstein params_BE h_valid_BE +
    (weights.w_FD : ℝ) * shannon_entropy_of_stat_system StatSystemType.FermiDirac params_FD h_valid_FD +
    (weights.w_MB : ℝ) * shannon_entropy_of_stat_system StatSystemType.MaxwellBoltzmann params_MB h_valid_MB
  )

/--
Main Theorem for PhysicsDist:
The linearly combined axiomatic entropy is equal to the
generalized C * Shannon form.
-/
theorem H_physics_dist_linear_combination_eq_generalized_C_Shannon
    (weights : SystemWeights)
    (params_BE : SystemParams) (h_valid_BE : params_BE.N ≠ 0 ∨ params_BE.M = 0)
    (params_FD : SystemParams) (h_valid_FD : params_FD.N ≠ 0 ∨ params_FD.M = 0)
    (h_fd : params_FD.M ≤ params_FD.N)
    (params_MB : SystemParams) (h_valid_MB : params_MB.N ≠ 0 ∨ params_MB.M = 0)
    : H_physics_dist_linear_combination weights params_BE h_valid_BE params_FD h_valid_FD params_MB h_valid_MB =
      generalized_PhysicsDist_C_times_Shannon weights params_BE h_valid_BE params_FD h_valid_FD params_MB h_valid_MB := by
  simp only [H_physics_dist_linear_combination, generalized_PhysicsDist_C_times_Shannon]
  rw [entropy_BE_eq_C_shannon params_BE h_valid_BE]
  rw [entropy_FD_eq_C_shannon params_FD h_valid_FD h_fd]
  rw [entropy_MB_eq_C_shannon params_MB h_valid_MB]
  ring

-- In EGPT.Physics.PhysicsDist

structure PhysicsSystemConfig where
  weights   : SystemWeights -- w_BE, w_FD, w_MB
  params_BE : SystemParams  -- N, M for BE
  params_FD : SystemParams  -- N, M for FD (placeholder usage)
  params_MB : SystemParams  -- N, M for MB (placeholder usage)
  -- We might need validity proofs here, or pass them separately later

/--
Calculates the weighted sum of Shannon entropies for a given configuration.
Handles domain validity internally for each component.
Returns 0 if a component's domain is invalid and its weight is non-zero.
(Or adjust error handling as preferred - returning 0 is simple for the decision problem).
-/
noncomputable def generalized_shannon_entropy_for_config (config : PhysicsSystemConfig) : ℝ :=
  let h_valid_BE := config.params_BE.N ≠ 0 ∨ config.params_BE.M = 0
  let entropy_BE := if h : h_valid_BE then
                     shannon_entropy_of_stat_system StatSystemType.BoseEinstein config.params_BE h
                   else 0

  let h_valid_FD := config.params_FD.N ≠ 0 ∨ config.params_FD.M = 0 -- Placeholder check
  let entropy_FD := if h : h_valid_FD then
                     shannon_entropy_of_stat_system StatSystemType.FermiDirac config.params_FD h
                   else 0 -- Currently returns 0 anyway due to placeholder

  let h_valid_MB := config.params_MB.N ≠ 0 ∨ config.params_MB.M = 0 -- Placeholder check
  let entropy_MB := if h : h_valid_MB then
                     shannon_entropy_of_stat_system StatSystemType.MaxwellBoltzmann config.params_MB h
                   else 0 -- Currently returns 0 anyway due to placeholder

  (config.weights.w_BE : ℝ) * entropy_BE +
  (config.weights.w_FD : ℝ) * entropy_FD +
  (config.weights.w_MB : ℝ) * entropy_MB
