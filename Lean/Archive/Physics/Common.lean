import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog -- For negMulLog, Real.log
import Mathlib.Algebra.BigOperators.Fin -- For sum over Fin n
import Mathlib.Data.Fin.Basic -- Basic Fin definitions and lemmas
import Mathlib.Data.Fintype.Fin -- Instances for Fin n
import Mathlib.Algebra.GroupWithZero.Units.Basic -- Provides mul_inv_cancel₀
import Mathlib.Data.Nat.Basic -- Basic Nat properties
--import Mathlib.Data.NNReal.Basic -- For NNReal
--import Mathlib.Topology.Basic -- For ContinuousOn (placeholder)
--import Mathlib.Order.Monotone.Basic -- For Monotone
--import Mathlib.Algebra.Order.Field.Basic -- For inv_one etc.
--import Mathlib.Analysis.SpecialFunctions.Log.Base -- Real.logb
--import Mathlib.Analysis.SpecialFunctions.Pow.Real -- Real.rpow
--import Mathlib.Data.Complex.Basic -- For Complex.exp_re if needed
--import Mathlib.Analysis.SpecificLimits.Basic -- tendsto_one_div_atTop_zero
--import Mathlib.Data.Real.Basic -- Basic Real properties
--import Mathlib.Order.Filter.Basic -- Filter bases etc.
--import Mathlib.Topology.Order.Basic -- OrderTopology
--import Mathlib.Data.Nat.Log -- Nat.log
--import Mathlib.Algebra.Order.Floor.Defs -- Floor definitions
--import Mathlib.Tactic.Linarith -- Inequality solver
--import Mathlib.Algebra.Ring.Nat -- For Nat.cast_pow
--import Mathlib.Logic.Equiv.Fin.Basic
--import Mathlib.Logic.Equiv.Defs
--import Mathlib.GroupTheory.Congruence.Basic

import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Archive.Core
import Archive.Basic
import Archive.Entropy.Common

namespace EGPT.Physics.Common

open EGPT EGPT.Basic Entropy.Common



-- Define the type for Macrostates (occupancy vectors summing to M)
-- Needed for both MB and BE state space definitions
def MBMacrostate (N M : ℕ) := { q : Fin N → ℕ // ∑ i, q i = M }
def UDMacrostate (N M : ℕ) := { q : Fin N → ℕ // ∑ i, q i = M }
-- Define the type for multisets of size M over Fin N
-- This uses the standard Mathlib definition `Sym α n := {s : Multiset α // card s = n}`
@[reducible] def SymFin (N M : ℕ) := Sym (Fin N) M

-- This is the actual function that calculates entropy for a physical system's distribution.


-- This axiom states that the true entropy of physical systems behaves according to Rota's postulates.
--axiom H_physical_system_has_Rota_entropy_properties : HasRotaEntropyProperties H_physical_system

/-- `Multiset.count` distributes over a `Finset` sum of multisets. -/
@[simp] lemma Multiset.count_finset_sum
    {α β : Type*} [DecidableEq α] {s : Finset β} (f : β → Multiset α) (a : α) :
    Multiset.count a (∑ i in s, f i) = ∑ i in s, Multiset.count a (f i) := by
  classical
  -- We proceed by induction on the structure of `s`.
  refine Finset.induction ?base ?step s
  · -- base case: `s = ∅`
    simp
  · -- inductive step: `s = insert b s'` with `b ∉ s'`
    intro b s' hb_not_mem ih
    simp [Finset.sum_insert hb_not_mem, Multiset.count_add, ih]


-- Define the physical constant C as an NNReal.
-- For now, let's set it to 1.0 for simplicity.
-- It could also be defined based on f0 H_physical_system 2 / log 2 if we had a way to
-- determine f0 H_physical_system 2 without full Rota properties.
-- Since we are defining H_physical_system FROM C*log k, C is now a primary definition.
noncomputable def C_physical_NNReal : NNReal := 1.0



/--
Calculates `C_physical_NNReal * log k` for a uniform distribution over `k` states.
Requires `k ≥ 1` (as `k=0` has no uniform dist and `log 0` is undefined).
Outputs NNReal.
-/
noncomputable def H_physical_system_uniform_only_calc (k : ℕ) (hk_ge1 : k ≥ 1) : NNReal :=
  if _hk_eq_1 : k = 1 then
    0 -- H(uniform_1) = C * log 1 = 0
  else
    C_physical_NNReal * RealLogNatToNNReal k hk_ge1


/--
Phase 1 concrete definition of H_physical_system.
For uniform distributions, it computes C * log k.
For non-uniform distributions, its behavior is currently 0 for this phase.
This is a placeholder until general distributions are handled in Phase 2.
-/
noncomputable def H_physical_system {α : Type} [Fintype α] (p : α → NNReal) : NNReal :=
  let k := Fintype.card α
  if hk_is_0 : k = 0 then
    0 -- No states, entropy is 0
  else
    -- Check if p is the uniform distribution for this k
    -- This requires a proof `p_sums_to_1` to use uniformDist
    -- For simplicity in this phase, we might need to pass this proof or make assumptions
    -- A full `is_uniform p` check is `∀ x y, p x = p y ∧ (k : NNReal) * p (Classical.arbitrary α) = 1` (if k > 0)
    -- More simply: p = uniformDist (proof that k > 0)
    -- For this placeholder, we'll be a bit loose on proving p is uniform,
    -- as it will only be *called* with uniform distributions from BE/FD/MB.
    -- The crucial part is that *when called with uniformDist*, it behaves as C*log k.
    -- We assume p is a valid probability distribution (sums to 1) implicitly for uniformDist.
    let k_pos_proof : 0 < k := Nat.pos_of_ne_zero hk_is_0
    if _h_is_uniform : p = uniformDist k_pos_proof then
        H_physical_system_uniform_only_calc k (Nat.one_le_of_lt k_pos_proof)
    else
        0 -- Placeholder for non-uniform distributions in Phase 1

noncomputable def eval_H_phys_system_on_fin_dist_to_real
    {k : ℕ} (p_dist : Fin k → NNReal) : ℝ :=
  (EGPT.Physics.Common.H_physical_system (α := Fin k) p_dist : ℝ)


-- Helper lemma from previous step (or ensure it's available)
lemma card_fin_eq_self (k : ℕ) : Fintype.card (Fin k) = k := by
  simp only [Fintype.card_fin]
