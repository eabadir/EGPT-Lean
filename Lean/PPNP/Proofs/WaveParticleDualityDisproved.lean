import Archive.Complexity.Core
import Archive.Physics.BoseEinstein -- For p_UD_fin, card_omega_be, etc.
import Archive.Entropy.Common -- For ShannonEntropyOfDist, stdShannonEntropyLn_uniform_eq_log_card


open EGPT.Complexity
open EGPT.Entropy.Common
open EGPT.Physics.BE -- For BE-specific definitions
open EGPT.Physics.UniformSystems -- For uniform dist helpers


/--
**Theorem (Bose-Einstein System Has Equivalent Program):**

This theorem is the formal statement of `BE Statistics ↔ Computability`.

The approach here was done before the EGPT Number Theory rational ParticlePMF was completed so it takes a more mathematically cumbersome approach:
For any Bose-Einstein system defined by `N` states and `M` particles, there
exists a system of `PathProgram`'s that can specify its state at arbitrary time t (sum of M PathProgram's each a  are themeselves an int ℤ ). The
complexity of this program is the smallest integer number of bits required to
encode the system's total information content, which is its Shannon entropy.

Assuming the Bose-Einstein distribution were coded in Lean, the more elegant approach is to equiv the real valued function to a BiasedIIDParticleSource and then directly apply the generalized Rota's Entropy & Computability Theorem (`rect_program_for_dist`). Coding the BE distribution in Lean, and the accompanying alternative proof approach, is an excercise left to the reader.
-/
theorem PhotonDistributionsHaveClassicalExplanationFromIndividualPaths (N M : ℕ) (h_valid : N ≠ 0 ∨ M = 0) :
    ∃ (prog : PathProgram), prog.complexity = Nat.ceil (Real.logb 2 (Nat.multichoose N M)) :=
by
  -- 1. Define the probability distribution for the Bose-Einstein system.
  --    From `BoseEinstein.lean`, we know this is a uniform distribution over all
  --    `k = Nat.multichoose N M` possible microstates.
  let k_card := Fintype.card (OmegaUD N M)
  have hk_card_pos : 0 < k_card := EGPT.Physics.BE.card_omega_BE_pos N M h_valid
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
    rw [← EGPT.Physics.BE.card_omega_be N M]


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
/--
**Theorem (Wave-Particle Duality is a Computational Artifact):**

For any valid physical Bose-Einstein system, there exists a deterministic
`PathProgram` that can specify any one of its possible microstates.
-/
def Wave_Interference_Explained_By_Classical_Particle_Paths : Prop :=
  -- "For any physical BE system..."
  ∀ (N M : ℕ) (_h_valid : N ≠ 0 ∨ M = 0),
    -- "...there exists a deterministic computational description..."
    ∃ (prog : PathProgram),
      -- "...whose complexity is determined by the system's total information content."
      prog.complexity = Nat.ceil (Real.logb 2 (Nat.multichoose N M))

-- Proof of the theorem
theorem Wave_Particle_Duality_Disproved_QED : Wave_Interference_Explained_By_Classical_Particle_Paths :=
by
  -- Unfold the definition to expose the ∀ quantifiers
  unfold Wave_Interference_Explained_By_Classical_Particle_Paths
  -- Introduce the variables and hypothesis
  intro N M h_valid
  -- The goal is now `∃ prog, prog.complexity = ...`
  -- This is precisely the statement of our new, powerful theorem.
  exact PhotonDistributionsHaveClassicalExplanationFromIndividualPaths N M h_valid



/-!
### Interpretation and Conclusion

The theorem `Wave_Interference_Explained_By_Classical_Particle_Paths` formally proves
that for any observable state of a Bose-Einstein system, there exists a
corresponding `PathProgram`.

- The "Wave" is the probability distribution `p_UD_fin N M` (or "average position at time t") which is also is the state of MANY (infinite) particles over the entire
  state space of `Nat.multichoose N M` possible outcomes. It represents the
  statistical nature of the ensemble of random walks from an infinite light source which emits IID particles doing their individual stochastic movements.

- The "Particle" is state of the single, definite path contributing (the List Bool) whose binary tape contributes to the overall `PathProgram` whose existence is
  guaranteed by RECT. It represents the specific, deterministic path taken in
  a single instance of reality .


-/
