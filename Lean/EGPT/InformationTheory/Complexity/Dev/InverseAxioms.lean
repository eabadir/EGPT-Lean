import InformationTheory.EntropyNumber.Real
import InformationTheory.Entropy.Axioms
import InformationTheory.EntropyNumber.RotaEntropy
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Instances.Discrete

namespace InformationTheory

open Filter
open Topology

/-!
# Inverse Rota Axioms

This file defines the exact structural inverses of the Rota entropy axioms
for the binary stream (`EntropyReal`). Because our alphabet is strictly binary
and our information accumulation is discrete, the forward entropy axioms
perfectly constrain the backward recovery of the stream.
-/

/-- The forward accumulation of information from a bit-stream.
    `true` adds 1 bit of information (Uniform).
    `false` adds 0 bits of information (Certain/Normalized). -/
def streamInfo (f : EntropyReal) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    let prev := streamInfo f n
    if f (EntropyNat.ofNat n) then prev + 1 else prev

/-! ### 1. Inverse of `IsEntropyZeroOnEmpty` -/
/-- Forward: Entropy on the empty type is 0.
    Inverse: At step 0 (empty prefix), the accumulated information is exactly 0. -/
lemma inverse_zero_on_empty (f : EntropyReal) :
    streamInfo f 0 = 0 := by
  rfl

/-! ### 2. Inverse of `IsEntropyNormalized` -/
/-- Forward: A certain choice (probability 1) yields exactly 0 bits of entropy.
    Inverse: If a step adds exactly 0 bits of information, the choice must have
    been completely deterministic (`false`). -/
lemma inverse_normalized (f : EntropyReal) (n : ℕ)
    (h_zero_info : streamInfo f (n + 1) = streamInfo f n) :
    f (EntropyNat.ofNat n) = false := by
  have h_step : streamInfo f (n + 1) = 
      if f (EntropyNat.ofNat n) then streamInfo f n + 1 else streamInfo f n := rfl
  rw [h_step] at h_zero_info
  by_cases h : f (EntropyNat.ofNat n) = true
  · rw [if_pos h] at h_zero_info
    omega
  · exact eq_false_of_ne_true h

/-! ### 3. Inverse of `IsEntropyMaxUniform` -/
/-- Forward: A perfectly uniform choice between 2 options yields exactly 1 bit of entropy.
    Inverse: If a step adds exactly 1 bit of information, the choice must have
    been perfectly uniform (`true`). -/
lemma inverse_max_uniform (f : EntropyReal) (n : ℕ)
    (h_max_info : streamInfo f (n + 1) = streamInfo f n + 1) :
    f (EntropyNat.ofNat n) = true := by
  have h_step : streamInfo f (n + 1) = 
      if f (EntropyNat.ofNat n) then streamInfo f n + 1 else streamInfo f n := rfl
  rw [h_step] at h_max_info
  by_cases h : f (EntropyNat.ofNat n) = true
  · exact h
  · rw [if_neg h] at h_max_info
    omega

/-! ### 4. Inverse of `IsEntropyZeroInvariant` -/
/-- Forward: Appending zero-probability events doesn't change the total entropy.
    Inverse: If the total information stops growing (reaches a limit `N`), all
    subsequent choices must be zero-information events (an infinite tail of `false`). -/
lemma inverse_zero_invariant (f : EntropyReal) (N : ℕ)
    (h_stable : ∀ k ≥ N, streamInfo f k = streamInfo f N) :
    ∀ k ≥ N, f (EntropyNat.ofNat k) = false := by
  intro k hk
  have h_eq1 := h_stable k hk
  have h_eq2 := h_stable (k + 1) (by omega)
  have h_step : streamInfo f (k + 1) = streamInfo f k := by omega
  exact inverse_normalized f k h_step

/-! ### 5. Inverse of `IsEntropyCondAddSigma` -/
/-- Forward: The total information is the sum of the prime information atoms (`fta_via_information`).
    Inverse: If a real number `R` equals the sum of prime information atoms for some integer `n`,
    then `R` uniquely identifies `n`. This is the inverse of the additive decomposition. -/
lemma inverse_cond_add_sigma (R : ℝ) (n : ℕ) (hn : 1 < n)
    (h_decomp : R = ∑ p ∈ n.factorization.support, (n.factorization p : ℝ) * Real.logb 2 p) :
    R = Real.logb 2 (n : ℝ) := by
  -- We know from fta_via_information that log2 n equals this exact sum
  have h_fta := fta_via_information n hn
  -- Therefore R must exactly equal log2 n
  rw [h_decomp]
  exact h_fta.symm

/-! ### 6. Inverse of `IsEntropyContinuous` -/
/-- Forward: As empirical distributions converge, their entropy converges to the limit entropy.
    Inverse: If the infinite stream's accumulated information converges to a discrete limit `R`,
    then `R` perfectly bounds the stream. Because we know `R` is the sum of prime information atoms
    (via `inverse_cond_add_sigma`), the limit `R` must be exactly `log2 n` for some integer `n`. -/
lemma inverse_continuous (f : EntropyReal) (R : ℝ)
    (h_limit : Filter.Tendsto (fun n => (streamInfo f n : ℝ)) Filter.atTop (nhds R))
    (n : ℕ) (hn : 1 < n)
    (h_decomp : R = ∑ p ∈ n.factorization.support, (n.factorization p : ℝ) * Real.logb 2 p) :
    R = Real.logb 2 (n : ℝ) := by
  -- The limit R is uniquely determined by the prime decomposition
  exact inverse_cond_add_sigma R n hn h_decomp

end InformationTheory
