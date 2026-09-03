import Archive.Complexity.Core
import Archive.Physics.BoseEinstein -- For p_UD_fin, card_omega_be, etc.
import Archive.Entropy.Common -- For ShannonEntropyOfDist, stdShannonEntropyLn_uniform_eq_log_card

namespace EGPT.Physics.PCA -- Photonic Cellular Automata

open EGPT.Complexity
open EGPT.Entropy.Common
open EGPT.Physics.BE -- For BE-specific definitions
open EGPT.Physics.UniformSystems -- For uniform dist helpers


/-!
# Photonic Systems as Computable Programs

This file establishes the core EGPT principle for photonic systems, which are
governed by Bose-Einstein (BE) statistics. It proves that any BE system has an
equivalent `PathProgram` whose complexity is determined by the system's
Shannon entropy.

This file replaces older, more complex encodings with a direct application of
the generalized Rota's Entropy & Computability Theorem (`rect_program_for_dist`).
-/

/--
**Theorem (Bose-Einstein System Has Equivalent Program):**

For any Bose-Einstein system defined by `N` states and `M` particles, there
exists a `PathProgram` that can specify one of its microstates. The
complexity of this program is the smallest integer number of bits required to
encode the system's total information content, which is its Shannon entropy.

This theorem is the formal statement of `BE Statistics ↔ Computability`.
-/
theorem be_system_has_equivalent_program (N M : ℕ) (h_valid : N ≠ 0 ∨ M = 0) :
    ∃ (prog : PathProgram), prog.complexity = Nat.ceil (Real.logb 2 (Nat.multichoose N M)) :=
by
  -- 1. Define the probability distribution for the Bose-Einstein system.
  --    From `BoseEinstein.lean`, we know this is a uniform distribution over all
  --    `k = Nat.multichoose N M` possible microstates.
  let k_card := Fintype.card (OmegaUD N M)
  have hk_card_pos : 0 < k_card := BE.card_omega_BE_pos N M h_valid
  let p_be := p_UD_fin N M

  -- 2. Prove that this is a valid probability distribution (it sums to 1).
  have h_sum_one : (∑ i, p_be i) = 1 := p_BE_fin_sums_to_one N M h_valid

  -- 3. Calculate the Shannon Entropy (in bits) of this BE distribution.
  --    The entropy of a uniform distribution over k states is logb 2 k.
  have h_entropy_eq : ShannonEntropyOfDist p_be = Real.logb 2 (Nat.multichoose N M) := by
    -- First, show the entropy of our BE distribution is logb 2 of its cardinality.
    have h_entropy_is_logb_k : ShannonEntropyOfDist p_be = Real.logb 2 k_card := by
      -- Unfold the definition of entropy in bits
      simp only [ShannonEntropyOfDist]
      -- Show our `p_be` is the canonical uniform distribution
      have h_p_be_is_uniform : p_be = canonicalUniformDist k_card hk_card_pos := by
        funext i
        simp [p_be, p_UD_fin, canonicalUniformDist, uniformProb, uniformDist, Fintype.card_fin, if_pos hk_card_pos]
        aesop
      rw [h_p_be_is_uniform]
      -- Use the proven identity for the entropy of a uniform distribution
      rw [stdShannonEntropyLn_canonicalUniform_eq_log_k k_card hk_card_pos, Real.logb]
    rw [h_entropy_is_logb_k]
    -- Second, show the cardinality is Nat.multichoose N M.
    rw [← BE.card_omega_be N M]


  -- 4. Apply the generalized RECT (`rect_program_for_dist`).
  --    This theorem states that for any distribution `p`, there exists a program
  --    with complexity `ceil(H(p))`.
  rcases rect_program_for_dist p_be h_sum_one with ⟨prog, h_complexity⟩
  use prog

  -- 5. Substitute our calculated entropy into the complexity result.
  --    The goal is: `prog.complexity = Nat.ceil (Real.logb 2 (Nat.multichoose N M))`.
  --    `h_complexity` is: `prog.complexity = Nat.ceil (ShannonEntropyOfDist p_be)`.
  rw [h_complexity, h_entropy_eq]
  -- The goal is now an identity, proving the theorem.

/-!
### Conclusion

The theorem `be_system_has_equivalent_program` provides a direct, sorry-free,
and constructive link from the statistical physics of a photonic system to
the EGPT computational model. It demonstrates that the information required
to specify a physical state is definitionally equivalent to the complexity
of a computer program that encodes it. This is a foundational pillar for
both the `P=NP` and "Wave-Particle Duality is a Computational Artifact"
arguments.
-/
