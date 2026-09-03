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
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.GroupTheory.Congruence.Basic

import Archive.Core
import Archive.Complexity.Core

/-!
# Entropy Axioms and Common Definitions (`Entropy/Common.lean`)

This file defines `HasRotaEntropyProperties`, the axiomatic structure that any
entropy function must satisfy. It formalizes — and extends — the properties
that Gian-Carlo Rota used in his uniqueness-of-entropy proof.

## Relationship to Rota's Original 5 Properties

Rota's original proof (Rota-Baclawski, *Introduction to Probability and
Random Processes*, 1979 Ch. 7; 1992 revised edition Ch. 8) established five
properties for a function H on finite probability distributions:

  1. **Defined on probability sets** — H takes distributions summing to 1.
  2. **Zero invariance** — adding outcomes with probability 0 does not change H.
  3. **Continuity** — H is continuous in the distribution parameters.
  4. **Conditional additivity** — H(joint) = H(prior) + expected H(conditional).
  5. **Maximum at uniform** — H is maximized by the uniform distribution.

The Lean formalization adds two properties that were implicit in Rota's
pen-and-paper treatment and one edge case required by Lean's type system:

  - **Normalization** (`IsEntropyNormalized`) — H({1}) = 0. In Rota's work
    this follows from Properties 1 and 2, but making it explicit simplifies
    the formal chain.
  - **Symmetry** (`IsEntropySymmetric`) — H is invariant under relabeling of
    outcomes. Rota implicitly assumed this by treating probability distributions
    as *sets* (unordered); Lean's `Fin n → NNReal` representation is ordered,
    so symmetry must be stated explicitly.
  - **Empty-domain handling** (`IsEntropyZeroOnEmptyDomain`) — H(empty) = 0.
    Lean's type system admits `Fin 0` as a valid domain; Rota never considered
    this edge case. It is needed for well-definedness in the Lean formalization.

Together these yield the 7-axiom `HasRotaEntropyProperties` structure below.
All 7 axioms are proven as theorems for the concrete Shannon entropy function
in `Entropy/H.lean` (see `TheCanonicalEntropyFunction_Ln`).
-/

namespace EGPT.Entropy.Common

open BigOperators Fin Real Topology NNReal Filter Nat Function
open EGPT EGPT.Complexity EGPT.NumberTheory.Core

universe u


/-- A PathProgram is defined by an initial state and a tape of instructions
    that drives its evolution. -/
structure PathProgram where
  current_state : ℤ
  tape : ComputerTape

-- Helper to create a new program at a starting position.
def mkPathProgram (initial_pos : Int) : PathProgram :=
  { tape := [], current_state := initial_pos }


-- ADD THE NEW HELPER FUNCTION HERE
namespace PathProgram
/--
Defines the computational complexity of a `PathProgram` in this model.
It is defined as the length of its input `ComputerTape`, representing the
number of i.i.d. binary choices processed.
-/
def complexity (prog : PathProgram) : ℕ :=
  prog.tape.length
/--
**Updates the tape of a PathProgram, returning a new program.**

This function takes an existing program `prog` and a new `ComputerTape`. It produces
a new `PathProgram` that has the same initial state as the original but uses the
new tape as its instructions.

This is a key helper for defining computations. It allows us to treat a `PathProgram`
as a reusable "machine" and `update_tape` as the mechanism for loading a new
input tape into that machine before running it.
-/
def update_tape (prog : PathProgram) (new_tape : ComputerTape) : PathProgram :=
  { current_state := prog.current_state,
    tape := new_tape }

end PathProgram


/-!
==================================================================
###  The EGPT Foundational Equivalence Cycle

This section establishes the core, bidirectional relationships between the
four fundamental concepts of EGPT: physical particle movement, entropy, information content,
and computational programs. We provide canonical names for each direction
of the equivalence.
==================================================================
-/

/--
Represents a finite sample an IID (Independent and Identically Distributed) Source.
The total number of choices is determined by `num_sub_samples`, `p_param`, and `q_param`.
If `p_param = 1` and `q_param = 0`, then `sample_size_num_choices` = `num_sub_samples`,
aligning with a simple sequence of `num_sub_samples` bits.
The parameters `p_param` and `q_param` allow for a more complex definition of sample size,
potentially reflecting underlying structures or biases in how samples are grouped or generated,
similar to how `p` and `q` might be used in `mkBiasedIIDParticleSource`.
-/
structure FiniteIIDSample where
  p_param : ℕ
  q_param : ℕ
  num_sub_samples : ℕ
  h_is_nontrivial : p_param + q_param > 0 -- Invariant

namespace FiniteIIDSample

/-- Computes the total number of choices for a FiniteIIDSample. -/
def sample_size_num_choices (s : FiniteIIDSample) : ℕ :=
  s.num_sub_samples * (s.p_param + s.q_param)

end FiniteIIDSample

-- === Type Aliases for Clarity ===

/--
An `InformationSource` is a physical or abstract process that generates
choices with a given probability distribution. Alias for `FiniteIIDSample`.
-/
abbrev InformationSource := FiniteIIDSample

/--
`InformationContentR` is the measure of uncertainty or information in a Real valued system,
quantified in bits. It is represented by a non-negative Real number.
-/
abbrev InformationContentR := ℝ

/--
A `ComputationalDescription` is a deterministic set of instructions that
encodes the outcome of a process. Alias for `PathProgram`.
-/
abbrev ComputationalDescription := PathProgram

/--
The Shannon entropy (in bits) of a single choice from an FiniteIIDSample.
Assuming each fundamental choice is a raw bit, its entropy contribution is 1 bit.
Formally: - (0.5 * Real.logb 2 0.5 + (1-0.5) * Real.logb 2 (1-0.5)) = 1 for a fair bit.
This definition assumes we are counting raw bits from the source.
-/
def BitsPerChoice_IIDParticleSource (_source : FiniteIIDSample) : ℕ  :=
  1

/--
If ordering doesn't matter, a sample of 1's and 0's can be represented using only a sign bit and the lesser of the two parameters.
--/
def BitsPerSubSample_IIDParticleSource (s : FiniteIIDSample) : ℤ :=
  BitsPerChoice_IIDParticleSource s * (Int.natAbs ((s.p_param : ℤ) - (s.q_param : ℤ)))

/--
The Shannon entropy (in bits) of a single trial from a biased source with
`true` probability `p / (p+q)`.
-/
noncomputable def shannonEntropyOfBiasedSource (p q : ℕ) (_h_pos : p + q > 0) : ℝ :=
  let p_real := (p : ℝ)
  let q_real := (q : ℝ)
  let total := p_real + q_real
  let P_true := p_real / total
  let P_false := q_real / total
  -- The entropy formula: - (P_true * log₂ P_true + P_false * log₂ P_false)
  -- Real.negMulLog is -x * log(x) (natural log), so we divide by log 2 for bits.
  (Real.negMulLog P_true + Real.negMulLog P_false) / Real.log 2

/-- Standard Shannon entropy of `p : α → NNReal`. Uses natural logarithm. -/
noncomputable def stdShannonEntropyLn {α : Type*} [Fintype α] (p : α → NNReal) : Real :=
  ∑ i : α, Real.negMulLog (p i : Real)

/-- Standard Shannon Entropy (base 2) for a system of k equiprobable states. -/
noncomputable def shannonEntropyOfSystem (k : ℕ) : ℝ :=
  if k > 0 then Real.logb 2 k else 0


/--
## ENTROPY
The efficient encoding length for a sequence of trials from
a biased source. The length is the number of trials multiplied by the Shannon
entropy per trial, reflecting the true information content. A source with lower
entropy (more predictability) requires fewer bits to encode.
-/
noncomputable def EntropyEncoder (s : FiniteIIDSample) : ℝ :=
  (s.num_sub_samples : ℝ) * shannonEntropyOfBiasedSource s.p_param s.q_param s.h_is_nontrivial

/--
Calculates the Shannon entropy (in bits) of any given discrete
probability distribution `dist` over `Fin k`. This generalizes
`shannonEntropyOfSystem`, which is the special case for a uniform distribution.
-/
noncomputable def ShannonEntropyOfDist {k : ℕ} (dist : Fin k → NNReal) : ℝ :=
  -- stdShannonEntropyLn calculates entropy in nats (-Σ pᵢ ln pᵢ).
  -- We divide by ln 2 to convert to bits.
  (stdShannonEntropyLn dist) / Real.log 2

-- Definition: f(n) = H(uniform distribution on n outcomes)
noncomputable def uniformProb (n : ℕ) : NNReal :=
  if _hn : n > 0 then (n⁻¹ : NNReal) else 0

/-- *Uniform distribution on a finite non-empty type.*
    The proof `h_card_pos` guarantees the denominator is non-zero. -/
noncomputable def uniformDist {α : Type*} [Fintype α]
    (_h_card_pos : 0 < Fintype.card α) : α → NNReal :=
λ _ ↦ (Fintype.card α : NNReal)⁻¹


/-- The uniform distribution sums to 1. -/
lemma sum_uniformDist {α : Type*} [Fintype α]
    (h_card_pos : 0 < Fintype.card α) : (∑ x, uniformDist h_card_pos x) = 1 := by
  have h_card_nnreal_ne_zero : (Fintype.card α : NNReal) ≠ 0 := by
      have h_card_nat_ne_zero : (Fintype.card α : ℕ) ≠ 0 := Nat.ne_of_gt h_card_pos
      simpa using h_card_nat_ne_zero
  simp only [uniformDist, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_inv_cancel₀ h_card_nnreal_ne_zero]

/--
Helper lemma: If `k > 0`, then `0 < Fintype.card (Fin k)`.
This provides a clean proof term for the positivity argument required by `uniformDist`.
-/
lemma Fintype_card_fin_pos {k : ℕ} (hk_pos : k > 0) : 0 < Fintype.card (Fin k) := by
  simp only [Fintype.card_fin] -- Fintype.card (Fin k) is definitionally k
  exact hk_pos




/-- The set of valid probability distributions over `Fin n`. -/
def probabilitySimplex {n : ℕ} : Set (Fin n → NNReal) :=
  { p | ∑ i, p i = 1 }

/-- Product distribution `P((i,j)) = p(i)q(j)` for independent `p` and `q`. -/
noncomputable def product_dist {n m : ℕ} (p : Fin n → NNReal) (q : Fin m → NNReal) : Fin (n * m) → NNReal :=
  fun k =>
    let k' : Fin (m * n) := Equiv.cast (congrArg Fin (Nat.mul_comm n m)) k
    let ji := finProdFinEquiv.symm k'
    p ji.2 * q ji.1



-- noncomputable instance {α β : Type*} :
--   CoeTC ((β → NNReal) × (α ≃ β)) (α → NNReal) where
--   coe := fun (⟨p, e⟩ : (β → NNReal) × (α ≃ β)) => p ∘ e

-- Component Structures for HasRotaEntropyProperties
-- H maps (α → NNReal) to NNReal.

structure IsEntropyNormalized
  (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) -- Renamed H to H_func
: Prop where
  normalized : ∀ (p : Fin 1 → NNReal), (∑ i, p i = 1) → H_func p = 0

structure IsEntropySymmetric
  (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) : Prop where
  symmetry :
    ∀ {α β : Type} [Fintype α] [Fintype β]
      (p_target : β → NNReal) (_hp : ∑ y, p_target y = 1)
      (e : α ≃ β),
      H_func (α := α) (fun x : α => p_target (e x)) =
      H_func (α := β) p_target

structure IsEntropyContinuous
  (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) -- Renamed H to H_func
: Prop where
  continuity : ∀ {α : Type} [Fintype α] (p_center : α → NNReal) (_hp_sum_1 : ∑ i, p_center i = 1)
                  (ε : ℝ), ε > 0 →
                ∃ δ > 0, ∀ (q : α → NNReal) (_hq_sum_1 : ∑ i, q i = 1),
                (∀ i, |(q i : ℝ) - (p_center i : ℝ)| < δ) → |((H_func q) : ℝ) - ((H_func p_center) : ℝ)| < ε
                -- Assuming H_func output is NNReal, so coercion to ℝ is needed for absolute difference.



structure IsEntropyZeroInvariance
  (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) -- Renamed H to H_func
: Prop where
  zero_invariance :
    ∀ {n : ℕ} (p_orig : Fin n → NNReal) (_hp_sum_1 : ∑ i, p_orig i = 1),
      let p_ext := (fun (i : Fin (n + 1)) =>
                     if h_lt : i.val < n then p_orig (Fin.castLT i h_lt)
                     else 0)
    H_func p_ext = H_func p_orig


-- In EGPT.Entropy.Common.lean, add this structure:
structure IsEntropyZeroOnEmptyDomain
  (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) : Prop where
  apply_to_empty_domain : H_func Fin.elim0 = 0
  -- Fin.elim0 here denotes the unique function Fin 0 → NNReal.
  -- The specific instance H_func {α := Fin 0} [Fintype (Fin 0)] Fin.elim0 is used.



structure IsEntropyMaxUniform
  (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) : Prop where -- Renamed H to H_func
  max_uniform :
    ∀ {α : Type} [Fintype α] (h_card_pos : 0 < Fintype.card α)
      (p : α → NNReal) (_hp_sum_1 : (∑ x, p x) = 1),
      H_func p ≤ H_func (uniformDist h_card_pos)

/--
Generalized joint distribution (dependent pair distribution) over a sigma type.
`P(⟨i,j⟩) = prior(i) * P_cond(i)(j)`.
The type of `j` depends on `i` via `M_map i`.
Requires `Fintype` instances for `Fin N` and `Fin (M_map i)`.
Implicitly, `N > 0` if `prior` is on `Fin N` and non-trivial.
If `M_map i = 0`, then `Fin (M_map i)` is empty, and no `j` exists for such `i`.
The domain `(Σ i : Fin N, Fin (M_map i))` will not contain pairs `⟨i,j⟩` if `M_map i = 0`.
-/
noncomputable def DependentPairDistSigma {N : ℕ}
    (prior : Fin N → NNReal) (M_map : Fin N → ℕ)
    (P_cond : Π (i : Fin N), (Fin (M_map i) → NNReal)) :
    (Σ i : Fin N, Fin (M_map i)) → NNReal :=
  fun sigma_pair => -- sigma_pair is ⟨i, j⟩ where j : Fin (M_map i)
    let i := sigma_pair.fst
    let j := sigma_pair.snd
    prior i * P_cond i j



/--
Axiom for conditional additivity of entropy, generalized for Sigma types.
`H(P_joint) = H(P_prior) + ∑_i P_prior(i) * H(P_conditional_i)`.
Preconditions:
- `prior` must sum to 1.
- For each `i` where `prior i > 0`:
    - `M_map i` must be greater than 0 (so `Fin (M_map i)` is non-empty and `P_cond i` is on a non-empty type).
    - `P_cond i` (the conditional distribution for that `i`) must sum to 1.
If `prior i = 0`, the term `prior i * H_func (P_cond i)` is zero, so the properties of `P_cond i`
(like summing to 1 or `M_map i > 0`) for that specific `i` do not affect the sum's value.
However, `H_func (P_cond i)` still needs to be well-defined. If `M_map i = 0`, then `P_cond i`
is a distribution on `Fin 0`. `H_func` applied to this should be `f0 H_func 0 = 0`.
The axiom states the equality assuming these conditions are met by the caller.
-/
structure IsEntropyCondAddSigma
  (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) : Prop where -- Changed Type u to Type
  cond_add_sigma :
    ∀ {N : ℕ} [NeZero N] -- Ensures Fin N is non-empty, prior is on a meaningful domain
      (prior   : Fin N → NNReal) (M_map : Fin N → ℕ)
      (P_cond  : Π (i : Fin N), (Fin (M_map i) → NNReal))
      (_hprior_sum_1    : ∑ i, prior i = 1)
      (_hP_cond_props : ∀ i : Fin N, prior i > 0 → (M_map i > 0 ∧ ∑ j, P_cond i j = 1))
      (_hH_P_cond_M_map_zero_is_zero : ∀ i : Fin N, M_map i = 0 →
        @H_func (Fin (M_map i)) (Fin.fintype (M_map i)) (P_cond i) = 0),
    H_func (DependentPairDistSigma prior M_map P_cond) =
      H_func prior + ∑ i, prior i * H_func (P_cond i)

/--
**Axiomatic Entropy Function — 7-axiom Lean formalization of Rota's entropy properties.**

`HasRotaEntropyProperties H_func` bundles the 7 properties that uniquely
characterize entropy up to a positive scalar (Rota's Entropy Theorem).

Five of these correspond directly to Rota's original properties
(Rota-Baclawski 1979/1992): zero invariance, continuity, conditional
additivity, and maximum-at-uniform, plus the implicit "defined on probability
sets" constraint enforced by the `∑ i, p i = 1` preconditions throughout.

The remaining two — `normalized` (H on a single certain outcome is 0) and
`symmetry` (H is invariant under relabeling) — were implicit in Rota's
presentation and are made explicit here for formal rigor. A seventh axiom,
`apply_to_empty_domain` (H on the empty type is 0), handles an edge case
in Lean's type system that Rota's pen-and-paper proof did not address.

All 7 axioms are proven as theorems for the concrete Shannon entropy
function `H_canonical_ln` in `Entropy/H.lean`.
-/
structure HasRotaEntropyProperties -- This is the new definition
  (H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal) -- Changed Type u to Type
  : Prop
  extends IsEntropyZeroInvariance H_func,
          IsEntropyNormalized H_func,
          IsEntropySymmetric H_func,
          IsEntropyContinuous H_func,
          IsEntropyCondAddSigma H_func, -- UPDATED
          IsEntropyMaxUniform H_func,
          IsEntropyZeroOnEmptyDomain H_func



lemma product_coe_inv_coe_mul_log_eq_log {k : ℕ} (hk_pos_nat : k > 0) :
    ((k : ℝ) * (k : ℝ)⁻¹) * Real.log k = Real.log k := by
  have hk_real_ne_zero : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hk_pos_nat)
  rw [mul_inv_cancel₀ hk_real_ne_zero, one_mul]

theorem stdShannonEntropyLn_uniform_eq_log_card {α : Type*} [Fintype α]
    (h_card_pos : 0 < Fintype.card α) :
  stdShannonEntropyLn (uniformDist h_card_pos) = Real.log (Fintype.card α) := by
  let k := Fintype.card α
  have hk_pos_nat : k > 0 := h_card_pos

  -- Unfold the definition of Shannon entropy, uniformDist, negMulLog, and the
  -- real/Nnreal coercions all at once:
  simp [stdShannonEntropyLn, uniformDist, negMulLog_def, NNReal.coe_inv, NNReal.coe_natCast]

  -- Now the goal is
  --   (k : ℝ) * ((k : ℝ)⁻¹ * Real.log k) = Real.log k

  -- Rearrange and finish
  rw [← mul_assoc]
  exact product_coe_inv_coe_mul_log_eq_log hk_pos_nat


/-! ### Phase 2: Properties of `f(n) = H(uniform_n)` -/

-- Replaced: old `f` definition
/--
Defines `f H n = H(uniform distribution on n outcomes)`.
`H` is an entropy function satisfying `HasRotaEntropyProperties`.
Requires `n > 0`. Output is `NNReal`.
-/
noncomputable def f {H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal} -- Renamed H to H_func for clarity
    (_hH_axioms : HasRotaEntropyProperties H_func) {n : ℕ} (hn_pos : n > 0) : NNReal :=
  let α_n := Fin n
  have h_card_pos : 0 < Fintype.card α_n := by
    rw [Fintype.card_fin]
    exact hn_pos
  H_func (uniformDist h_card_pos)

-- Replaced: old `f0` definition
/--
Defines `f0 H n` which extends `f H n` to include `n=0` by setting `f0 H 0 = 0`.
Output is `NNReal`.
-/
noncomputable def f0 {H_func : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal} -- Renamed H to H_func
    (hH_axioms : HasRotaEntropyProperties H_func) (n : ℕ) : NNReal :=
  if hn_pos : n > 0 then f hH_axioms hn_pos else 0

-- New helper
/--
Helper lemma: The uniform distribution on `Fin 1` is `λ _ => 1`.
-/
lemma uniformDist_fin_one_eq_dist_one :
    uniformDist (by {rw [Fintype.card_fin]; exact Nat.one_pos} : 0 < Fintype.card (Fin 1)) =
    (fun (_ : Fin 1) => 1) := by
  funext x
  simp only [uniformDist, Fintype.card_fin, Nat.cast_one, inv_one]

-- New helper
/--
Helper lemma: The distribution `λ (_ : Fin 1) => 1` sums to 1.
-/
lemma sum_dist_one_fin_one_eq_1 :
    (∑ (_ : Fin 1), (1 : NNReal)) = 1 := by
  simp [Finset.sum_const, Finset.card_fin, nsmul_one]



/--
If `p_orig` sums to `1` on `Fin n`, the extension that appends a zero at
index `n` still sums to `1`.  This Lean 4 version uses
`Fin.sum_univ_castSucc` directly. -/
lemma sum_p_ext_eq_one_of_sum_p_orig_eq_one
    {n : ℕ} (p_orig : Fin n → NNReal) (hp : ∑ i, p_orig i = 1) :
    (∑ i : Fin (n + 1),
        (if h : (i : ℕ) < n then p_orig (Fin.castLT i h) else 0)) = 1 := by
  -- Define the extended vector once so we can name it.
  set p_ext : Fin (n + 1) → NNReal :=
      fun i => if h : (i : ℕ) < n then p_orig (Fin.castLT i h) else 0

  -- Canonical split of the sum over `Fin (n+1)`.
  have h_split :
      (∑ i, p_ext i) =
        (∑ i : Fin n, p_ext i.castSucc) + p_ext (Fin.last n) := by
        rw [Fin.sum_univ_castSucc]

  -- The new last entry is zero.
  have h_last : p_ext (Fin.last n) = 0 := by
    simp [p_ext]

  -- The first summand coincides with the original sum.
  have h_cast :
      (∑ i : Fin n, p_ext i.castSucc) = ∑ i : Fin n, p_orig i := by
    apply Finset.sum_congr rfl
    intro i _
    have : ((i.castSucc : Fin (n + 1)) : ℕ) < n := by
      rw [Fin.castSucc] -- Goal becomes i.val < n
      exact i.is_lt         -- Proof of i.val < n
    simp [p_ext, this, Fin.castLT_castSucc]

  -- Put the pieces together.
  simp [h_split, h_last, h_cast, hp, p_ext]


/--The constant `C_H` relating `f0 H n` to `Real.log n`.
Defined as `(f0 H 2 : ℝ) / Real.log 2` if H is non-trivial, else 0.
This constant is `Real`-valued.
-/
noncomputable def C_constant_real {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyProperties H) : Real :=
  by classical -- Use classical logic to ensure the condition is decidable
  exact if h_nontrivial : (∃ n' ≥ 1, f0 hH_axioms n' ≠ 0) then
    (f0 hH_axioms 2 : ℝ) / Real.log 2
  else
    0

/-- `C_constant_real` is non-negative. -/
lemma C_constant_real_nonneg {H : ∀ {α : Type} [Fintype α], (α → NNReal) → NNReal}
    (hH_axioms : HasRotaEntropyProperties H) : C_constant_real hH_axioms ≥ 0 := by
  rw [C_constant_real]
  split_ifs with h_nontrivial
  · -- Case: H non-trivial
    have hf02_real_nonneg : (f0 hH_axioms 2 : ℝ) ≥ 0 := NNReal.coe_nonneg _
    have hlog2_pos : Real.log 2 > 0 := Real.log_pos (by norm_num : (2:ℝ) > 1)
    exact div_nonneg hf02_real_nonneg (le_of_lt hlog2_pos)
  · -- Case: H trivial
    exact le_refl 0



/--
**Generalized RECT (Rota's Entropy & Computability Theorem for any Distribution):**

For any system described by a discrete probability distribution `dist`, there
exists a `PathProgram` whose complexity is equivalent to the Shannon
entropy of that distribution. This theorem provides the constructive bridge
from any probability-theoretic decision problem system to a computational one.
-/
theorem rect_program_for_dist {k : ℕ} (dist : Fin k → NNReal) (_h_sum : ∑ i, dist i = 1) :
    ∃ (prog : PathProgram), prog.complexity = Nat.ceil (ShannonEntropyOfDist dist) :=
by
  -- The required complexity L is the smallest integer number of bits that can
  -- represent the information content H(dist).
  let L := Nat.ceil (ShannonEntropyOfDist dist)

  -- The existence of a program with this complexity is constructive. We only need
  -- to show that a tape of this length can be created. The specific content of
  -- the tape would be determined by an optimal compression algorithm (like
  -- Huffman or Arithmetic coding), but for complexity theory, its length is what matters.
  let example_tape := List.replicate L true
  let initial_st_example : ParticlePosition := 0
  let prog_exists : PathProgram := {
    current_state := initial_st_example,
    tape := example_tape
  }
  use prog_exists

  -- The proof goal is to show that the complexity of our created program
  -- matches the required complexity L. This is true by construction.
  simp [PathProgram.complexity, L, example_tape, prog_exists]



/--
Inverse SCT (Part A): Any program of complexity L corresponds to a single microstate
in a system of 2^L equiprobable states, which has Shannon Entropy L.
-/
theorem invSCT_entropy_of_program (prog : PathProgram) :
    shannonEntropyOfSystem (2^(PathProgram.complexity prog)) = ((PathProgram.complexity prog) : ℝ) :=
by
  simp only [shannonEntropyOfSystem]
  -- After simp, the goal is:
  -- (if 0 < 2 ^ (PathProgram.complexity prog) then Real.logb 2 (2 ^ (PathProgram.complexity prog)) else 0)
  --   = ↑(PathProgram.complexity prog)

  have h_pow_pos : 0 < 2^(PathProgram.complexity prog) := Nat.pow_pos (by norm_num)

  rw [if_pos h_pow_pos]
  -- Goal is now: Real.logb 2 (2 ^ (PathProgram.complexity prog)) = ↑(PathProgram.complexity prog)

  simp [Real.logb_pow]


/-!
Shannon Entropy of a Specific Equiprobable Tape Choice
Calculates the Shannon entropy (using natural logarithm, in nats) associated with
the event of observing one specific `m_bits`-length binary tape, assuming all
$2^{m_{bits}}$ such tapes are equiprobable.
The probability of one specific tape is $1 / 2^{m_{bits}} = 2^{-m_{bits}}$.
Shannon entropy for one outcome is $-P \ln P = -(2^{-m_{bits}}) \ln(2^{-m_{bits}})$.
However, we are interested in the entropy of the *uniform distribution over all possible tapes*.
This distribution has $2^{m_{bits}}$ outcomes, each with probability $2^{-m_{bits}}$.
The Shannon entropy of this uniform distribution is $\ln(\text{Number of outcomes}) = \ln(2^{m_{bits}})$.

Note: `(2^m_bits : ℝ)` is `Nat.cast (Nat.pow 2 m_bits)`.
-/
noncomputable def ShannonEntropyOfEquiprobableTapeChoice (m_bits : ℕ) : ℝ :=
  if _hm_pos : m_bits > 0 then Real.log (2^m_bits : ℝ) else 0 * Real.log 2



/--
Helper lemma: Equivalent to a potentially missing `Real.log_nat_cast_pow_of_pos`.
Proves that `log (↑(x^n)) = n • log (↑x)` for natural numbers `x, n` where `x > 0`.
-/
lemma log_nat_cast_pow_of_pos (x n : ℕ) [_h : NeZero x] :
  Real.log (↑x ^ n) = n • Real.log (↑x) := by
  let x_real : ℝ := ↑x
  let n_real : ℝ := ↑n
  let real_pow_x_n : ℝ := (x ^ n : ℝ)
  simp [x_real, n_real, real_pow_x_n]


lemma shannon_entropy_of_tape_choice_eq_m_log2 (m_bits : ℕ) (hm_pos : m_bits > 0) :
    ShannonEntropyOfEquiprobableTapeChoice m_bits = ↑(m_bits : ℝ) * Real.log 2 := by
  simp [ShannonEntropyOfEquiprobableTapeChoice, dif_pos hm_pos, log_nat_cast_pow_of_pos]

lemma shannon_entropy_of_tape_choice_zero_div_log_two_eq_zero :
    ShannonEntropyOfEquiprobableTapeChoice 0 / Real.log 2 = 0 := by
  have h_cond_false : ¬ (0 > 0) := Nat.lt_irrefl 0
  simp [ShannonEntropyOfEquiprobableTapeChoice, dif_neg h_cond_false, zero_mul, zero_div]


/--
The amount of information (in bits) required to distinguish one state from
an ensemble of `2^L` equiprobable states. This is simply `L`.
-/
abbrev InformationContent := ℕ

/--
**Simplified RECT (Information → Program):**

For any given amount of information content `L`, there exists a computer program
whose complexity is exactly `L`.

This is provable by construction using our `ParticlePath` number system.
-/
theorem rect_program_for_information (L : InformationContent) :
    ∃ (prog : PathProgram), prog.complexity = L :=
by
  -- 1. In EGPT, a program tape is a `ParticlePath`. A `ParticlePath` of length L
  --    is constructed from the natural number L using `fromNat`.
  let gnat_L : ParticlePath := fromNat L
  -- A `ParticlePath` is definitionally a `List Bool` satisfying `AllTrue`.
  let tape_L : ComputerTape := gnat_L.val

  -- 2. Construct the program with this tape.
  let prog_exists : PathProgram := {
    current_state := 0, -- Initial state is 0
    tape := tape_L
  }
  use prog_exists

  -- 3. Prove its complexity is L.
  -- The complexity is the tape length, which is the length of the ParticlePath's list.
  simp [PathProgram.complexity, tape_L]
  -- The length of the ParticlePath from `fromNat L` is L by definition.
  -- This is proven by `left_inv` in the `equivParticlePathToNat` equivalence.
  exact left_inv L

/-!
==================================================================
### The Equivalence of Biased Sources and Programs

This section provides the final, general theorem that connects any
`FiniteIIDSample` (representing a potentially biased physical source)
to a `PathProgram`. It replaces the older, special-case theorems
that only handled fair (uniform) sources.

The complexity of the resulting program is not its raw tape length, but
is determined by the *true information content* (Shannon entropy) of
the source, as calculated by `EntropyEncoder`.
==================================================================
-/

/--
**Rota's Entropy & Computability Theorem of IID Source: The Generalized Equivalence Theorem (Source ↔ Program):**

For any well-defined information source (`FiniteIIDSample`), there exists a
`PathProgram` whose complexity is precisely the amount of information
(in integer bits) that the source produces.

This is the ultimate expression of RECT in our framework.
-/
theorem rect_program_for_biased_source (src : FiniteIIDSample) :
    ∃ (prog : PathProgram), prog.complexity = Nat.ceil (EntropyEncoder src) :=
by
  -- 1. Let H be the total Shannon entropy (information content in bits)
  --    produced by the source. This is calculated by our `EntropyEncoder`.
  let H_src := EntropyEncoder src

  -- 2. In information theory, a source producing H bits of information can generate
  --    one of roughly 2^H "typical" outcomes. The entropy of a system with
  --    that many equiprobable states is H.
  --    We can create a fictional probability distribution `dist_equiv` over a
  --    sufficiently large number of states `k` such that its entropy is H_src.
  --    However, a more direct approach is to use the core principle of RECT.

  -- 3. The core principle of RECT (`rect_program_for_dist`) states that for *any*
  --    amount of entropy `H`, there exists a program of complexity `ceil(H)`.
  --    We can construct a dummy distribution that has this entropy.
  --    Let's construct a distribution over `k` states, where `k` is chosen
  --    such that `logb 2 k` is close to `H_src`.

  -- A more direct proof:
  -- The information content H_src represents the number of bits needed for an optimal code.
  -- A program tape is a realization of such a code.
  -- Therefore, a program of complexity `ceil(H_src)` must exist.
  let L := Nat.ceil H_src
  let example_tape := List.replicate L true
  let prog_exists : PathProgram := {
    current_state := 0,
    tape := example_tape
  }
  use prog_exists
  simp [PathProgram.complexity, L, example_tape]
  aesop

/--
The "Information" represented by a canonical program is the pair of numbers
(outcome, runtime) that uniquely defines it.
-/
abbrev CanonicalInformation := ChargedParticlePath × ComputerTape

/--
**The Final EGPT Equivalence Theorem (Program ≃ Information):**

There is a direct, computable, and sorry-free bijection between the original
`PathProgram` structure and the `CanonicalInformation` pair that defines it.
This formalizes the idea that a program *is* its initial state plus its path.
-/
noncomputable def equivProgramToCanonicalInfo : PathProgram ≃ CanonicalInformation :=
{
  toFun := fun prog =>
    -- The forward function encodes the initial state to its GInt form.
    let initialStateInfo := ParticlePathIntEquiv.symm prog.current_state
    (initialStateInfo, prog.tape),

  invFun := fun info =>
    -- The inverse function decodes the GInt back to a ℤ.
    let initialStateVal := ParticlePathIntEquiv info.fst
    {
      current_state := initialStateVal ,
      tape := info.snd
    },

  left_inv := by
    -- Proving `invFun(toFun(p)) = p`.
    intro p
    -- This will succeed with `simp` because we are applying an equivalence
    -- and its inverse (`ParticlePathIntEquiv`), which cancel out,
    -- and the tape component is passed through directly.
    simp,

  right_inv := by
    -- Proving `toFun(invFun(i)) = i`.
    intro i
    -- This will succeed with `simp` for similar reasons.
    simp
}




-- === The Equivalence Theorems ===

/-!
###  IIDSource ↔ ShannonEntropy
-/

/--
**SCT (Source Coding Theorem): An InformationSource has a quantifiable InformationContentR.**
The total information produced by a source is its number of trials multiplied by the
entropy per trial.
-/
noncomputable def SCT_Source_to_Entropy (src : InformationSource) : InformationContentR :=
  EntropyEncoder src

/--
**ISCT (Inverse Source Coding Theorem): Any InformationContentR can be modeled by a Source.**
For any amount of information `H`, we can construct a source that produces it. This is
achieved by creating a fair source (1 bit/trial) with `ceil(H)` trials.
-/
noncomputable def ISCT_Entropy_to_Source (H : InformationContentR) : InformationSource :=
  let L := Nat.ceil H
  { p_param := 1, q_param := 1, num_sub_samples := L, h_is_nontrivial := by norm_num }

-- We can prove that ISCT is a valid inverse for SCT for integer information contents.
theorem ISCT_SCT_inverse_for_integer_entropy (L : ℕ) :
    SCT_Source_to_Entropy (ISCT_Entropy_to_Source (L : ℝ)) = (L : ℝ) :=
by
  simp [SCT_Source_to_Entropy, ISCT_Entropy_to_Source, EntropyEncoder]
  -- We need to prove shannonEntropyOfBiasedSource 1 1 = 1.
  have h_entropy_one : shannonEntropyOfBiasedSource 1 1 (by norm_num) = 1 := by
    -- Assuming shannonEntropyOfBiasedSource p q _ := ( (p/(p+q)).negMulLog + (q/(p+q)).negMulLog ) / Real.log 2
    -- And Real.negMulLog x := -x * Real.log x for x > 0 (if x=0, then 0)
    simp only [shannonEntropyOfBiasedSource, Real.negMulLog]

    -- Simplify the fraction (↑1 / (↑1 + ↑1)) which appears as arguments to negMulLog.
    have h_frac : (↑1 : ℝ) / (↑1 + ↑1) = (1/2 : ℝ) := by norm_num
    -- The simp tactic below will use h_frac, simplify Real.negMulLog for 1/2,
    -- apply Real.log_inv (which is a simp lemma) to Real.log (1/2),
    -- and perform arithmetic simplification on the terms.
    simp [h_frac]

    -- Goal is now (2⁻¹ * Real.log 2 + 2⁻¹ * Real.log 2) / Real.log 2 = 1
    -- Introduce hypothesis that Real.log 2 is non-zero for field_simp.
    have h_log_nz : Real.log 2 ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)

    -- field_simp will simplify the numerator (2⁻¹ * X + 2⁻¹ * X) to X,
    -- then X / X to 1, given X ≠ 0.
    field_simp [h_log_nz]

  rw [h_entropy_one, mul_one]

/-!
### Shannon Entropy ↔ PathProgram
-/

/--
**RECT (Rota's Entropy & Computability Theorem): InformationContentR implies a Program.**
For any amount of information `H`, there exists a program whose complexity
(tape length) is the smallest integer number of bits that can represent `H`.
-/
theorem RECT_Entropy_to_Program (H : InformationContentR) :
    ∃ (prog : ComputationalDescription), prog.complexity = Nat.ceil H :=
by
  let L := Nat.ceil H
  use { current_state := 0, tape := List.replicate L true }
  simp [PathProgram.complexity]
  aesop

/--
**IRECT (Inverse RECT): A Program has an equivalent InformationContentR.**
Any program of complexity `L` represents a single choice from an ensemble of
`2^L` equiprobable states, which has an information content of `L` bits.
-/
noncomputable def IRECT_Program_to_Entropy (prog : ComputationalDescription) :
InformationContentR :=
  (prog.complexity : ℝ)

-- The inverse relationship is definitional.
theorem IRECT_RECT_inverse_for_integer_complexity (L : ℕ) :
    ∃ (prog : ComputationalDescription),
      IRECT_Program_to_Entropy prog = (L : ℝ) ∧ prog.complexity = L :=
by
  use { current_state := 0, tape := List.replicate L true }
  simp [IRECT_Program_to_Entropy, PathProgram.complexity]

/-!
### IIDSource ↔ PathProgram (The Direct Bridge)
-/

/--
**SCT → RECT Bridge: A Source implies a Program.**
Any information source can be encoded by a program whose complexity matches the
source's information content.
-/
theorem IID_Source_to_Program (src : InformationSource) :
    ∃ (prog : ComputationalDescription), prog.complexity = Nat.ceil (SCT_Source_to_Entropy src) :=
by
  -- This is just applying RECT to the output of SCT.
  exact RECT_Entropy_to_Program (SCT_Source_to_Entropy src)

/--
**IRECT → ISCT Bridge: A Program implies a Source.**
Any program can be modeled as the output of an information source with equivalent
information content.
-/
noncomputable def Program_to_IID_Source (prog : ComputationalDescription) : InformationSource :=
  -- Apply IRECT, then ISCT.
  ISCT_Entropy_to_Source (IRECT_Program_to_Entropy prog)

-- Prove the consistency of the direct bridge.
theorem program_source_complexity_matches (prog : ComputationalDescription) :
    let src := Program_to_IID_Source prog
    SCT_Source_to_Entropy src = IRECT_Program_to_Entropy prog :=
by
  -- Unfold definitions and use the previous inverse proof.
  simp [Program_to_IID_Source, IRECT_Program_to_Entropy]
  exact ISCT_SCT_inverse_for_integer_entropy prog.complexity



/--
The canonical uniform distribution on `Fin k`.
Defined as `fun (_ : Fin k) => (k : NNReal)⁻¹`.
This is a specialization of `uniformDist` for clarity and specific use with `Fin k`.
-/
noncomputable def canonicalUniformDist (k : ℕ) (hk_pos : k > 0) : Fin k → NNReal :=
  uniformDist (Fintype_card_fin_pos hk_pos)

/--
Proof that `canonicalUniformDist k hk_pos` sums to 1.
This directly uses `sum_uniformDist` with the appropriate proof of positivity
for `Fintype.card (Fin k)`.
-/
lemma sum_canonicalUniformDist_eq_one (k : ℕ) (hk_pos : k > 0) :
    (∑ i, canonicalUniformDist k hk_pos i) = 1 := by
  simp only [canonicalUniformDist] -- Unfold to uniformDist (Fintype_card_fin_pos hk_pos)
  exact sum_uniformDist (Fintype_card_fin_pos hk_pos)

/--
Symmetry of `stdShannonEntropyLn`: `stdShannonEntropyLn (p ∘ e) = stdShannonEntropyLn p`
for an `Equiv e : α ≃ β` between two Fintypes `α` and `β`,
and a target distribution `p_target : β → NNReal`.
The sum `∑ x:α, negMulLog(p_target(e x))` is transformed to `∑ y:β, negMulLog(p_target y)`.
-/
theorem stdShannonEntropyLn_comp_equiv {α β : Type*} [Fintype α] [Fintype β]
    (p_target : β → NNReal) (e : α ≃ β) :
    stdShannonEntropyLn (p_target ∘ e) = stdShannonEntropyLn p_target := by
  -- Unfold stdShannonEntropyLn on both sides to expose the sums.
  unfold stdShannonEntropyLn
  -- LHS: ∑ (x : α), negMulLog ((p_target (e x)) : ℝ)
  -- RHS: ∑ (y : β), negMulLog ((p_target y) : ℝ)
  -- Apply Function.comp_apply to the term inside the sum on the LHS.
  simp_rw [Function.comp_apply]
  -- LHS is now: ∑ (x : α), negMulLog ((p_target (e x)) : ℝ)
  -- Let g(y) := negMulLog ((p_target y) : ℝ).
  -- LHS is ∑ (x : α), g (e x).
  -- Equiv.sum_comp states: (∑ x, g (e x)) = (∑ y, g y).
  exact Equiv.sum_comp e (fun (y : β) => negMulLog ((p_target y) : ℝ))

-- We'll continue with `stdShannonEntropyLn_canonicalUniform_eq_log_k` and the main theorem
-- `H_uniform_mapped_dist_eq_C_shannon` once this part is verified.

lemma stdShannonEntropyLn_canonicalUniform_eq_log_k (k : ℕ) (hk_pos : k > 0) :
    stdShannonEntropyLn (canonicalUniformDist k hk_pos) = Real.log k := by
  simp only [canonicalUniformDist] -- Unfold to stdShannonEntropyLn (uniformDist (Fintype_card_fin_pos hk_pos))
  rw [stdShannonEntropyLn_uniform_eq_log_card (Fintype_card_fin_pos hk_pos)] -- from Entropy.Common
  -- Goal is Real.log (Fintype.card (Fin k)) = Real.log k
  rw [Fintype.card_fin k] -- from Mathlib
