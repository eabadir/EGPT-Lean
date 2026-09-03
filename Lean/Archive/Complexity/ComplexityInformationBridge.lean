import Archive.Core
import Archive.Constraints
import Archive.NumberTheory.Core
import Archive.Complexity.Core
import Archive.Complexity.TableauFromCNF
import Archive.Entropy.Common

namespace EGPT.Complexity.Interpretation

open EGPT EGPT.Complexity EGPT.NumberTheory.Core EGPT.Constraints
open EGPT.Entropy.Common

/--
For any integer budget `n²`, there exists a concrete program whose
time complexity and information complexity are both exactly `n²`.

This theorem addresses the common misconception that `n²` in EGPT is only an
information measure: in the EGPT machine model, the same quantity is also tape
length (step count), so the two notions coincide.
-/
theorem nSquared_time_complexity_is_information_complexity (n : ℕ) :
    ∃ (prog : ComputationalDescription),
      prog.complexity = n * n ∧
      IRECT_Program_to_Entropy prog = (n * n : ℝ) := by
  rcases IRECT_RECT_inverse_for_integer_complexity (n * n) with ⟨prog, h_entropy, h_complexity⟩
  refine ⟨prog, h_complexity, ?_⟩
  simpa [Nat.cast_mul] using h_entropy

/--
For a satisfiable CNF walk, there exists a program whose time complexity and
information complexity are the same value, and this shared value is bounded by
the canonical `n²` input bound.
-/
theorem walk_nSquared_bound_is_time_and_information
    {k : ℕ} (cnf : SyntacticCNF_EGPT k)
    (endpoint : { v : Vector Bool k // evalCNF cnf v = true }) :
    let n := (encodeCNF cnf).length
    ∃ (prog : ComputationalDescription),
      prog.complexity = (walkCNFPaths cnf endpoint).complexity ∧
      IRECT_Program_to_Entropy prog = ((walkCNFPaths cnf endpoint).complexity : ℝ) ∧
      prog.complexity ≤ n * n := by
  intro n
  have h_walk_bound : (walkCNFPaths cnf endpoint).complexity ≤ n * n := by
    calc
      (walkCNFPaths cnf endpoint).complexity
          ≤ cnf.length * k := walkComplexity_upper_bound _ endpoint
      _ ≤ n * n := by
        apply Nat.mul_le_mul
        · simpa [n] using cnf_length_le_encoded_length cnf
        · simpa [n] using encodeCNF_size_ge_k k cnf

  rcases IRECT_RECT_inverse_for_integer_complexity ((walkCNFPaths cnf endpoint).complexity) with
    ⟨prog, h_entropy, h_complexity⟩
  refine ⟨prog, h_complexity, h_entropy, ?_⟩
  simpa [h_complexity] using h_walk_bound

end EGPT.Complexity.Interpretation

