import Mathlib.Tactic.NormNum
import Archive.Core
import Archive.NumberTheory.Core
import Archive.Constraints

namespace EGPT.Complexity

open EGPT EGPT.NumberTheory.Core EGPT.Constraints

/-!
### Core Complexity Definitions (The "Logic" Preliminaries)

This file contains the minimal definitions required for the formal proof of P=NP.
It defines what constitutes a polynomial-time function and a polynomial bound
within the EGPT framework.
-/

/--
A predicate asserting that a function `f` from one ParticlePath to another is
computable by a native EGPT polynomial. The witness for this property is the
`EGPT_Polynomial` structure itself.
-/
def IsPolynomialEGPT (f : ParticlePath → ParticlePath) : Prop :=
  ∃ (P : EGPT_Polynomial), f = P.eval

/-- The identity function on `ParticlePath` is polynomial. -/
instance IsPolynomialEGPT.id : IsPolynomialEGPT id := by
  -- 1. The goal is `∃ (P : EGPT_Polynomial), id = P.eval`.
  -- 2. We provide the native identity polynomial as the witness.
  use EGPT_Polynomial.id
  -- 3. The goal becomes `id = EGPT_Polynomial.id.eval`.
  --    We use function extensionality to prove this.
  ext n
  -- 4. The goal is now `id n = EGPT_Polynomial.id.eval n`.
  --    This simplifies by definition.
  simp [EGPT_Polynomial.eval]
  -- The proof is complete.

/--
A predicate asserting that a function `p : ℕ → ℕ` is bounded by a native
EGPT polynomial. This is the canonical EGPT definition of a polynomial bound.
-/
def IsBoundedByEGPT_Polynomial (p : ℕ → ℕ) : Prop :=
  ∃ (P : EGPT_Polynomial), ∀ n, p n ≤ toNat (P.eval (fromNat n))


/--
**Calculates the EGPT "Path Cost" to verify a single literal.**

In the EGPT model, verifying the `i`-th literal in a `k`-variable system
requires a computational path of complexity `i`. This represents the
information needed to "address" or "focus on" the `i`-th component of the
state vector.

The path is a `ParticlePath` (EGPT Natural Number), making the cost a
direct, physical quantity.
-/
def PathToConstraint {k : ℕ} (l : Literal_EGPT k) : ParticlePath :=
  -- The complexity is the index of the particle/variable being constrained.
  fromNat l.particle_idx.val

/--
`CanonicalCNFProgram` is the program-level view of an encoded canonical CNF.
This is a readability alias for reviewers: canonical SAT instances are handled
as executable binary programs in the EGPT machine model.
-/
abbrev CanonicalCNFProgram (_k : ℕ) := ComputerProgram

/-- Complexity-facing alias for the foundational `ParticlePath ≃ ℕ` equivalence. -/
abbrev equivPathNat := EGPT.NumberTheory.Core.equivParticlePathToNat

/-- Complexity-facing alias for the CNF-to-path equivalence. -/
noncomputable abbrev equivCNFPath {k : ℕ} := EGPT.Constraints.equivSyntacticCNF_to_ParticlePath (k := k)

/-- Complexity-facing alias: interpret a path as its native `ℕ` size. -/
abbrev pathNat := EGPT.NumberTheory.Core.toNat

/-- Complexity-facing alias: build a path from native `ℕ`. -/
abbrev natPath := EGPT.NumberTheory.Core.fromNat

/-- Encode a canonical CNF as a `ComputerProgram`. -/
def encodeCanonicalCNFAsProgram {k : ℕ} (ccnf : CanonicalCNF k) : CanonicalCNFProgram k :=
  encodeCNF ccnf.val

/-- The encoded canonical CNF is definitionally a program tape. -/
@[simp] theorem encodeCanonicalCNFAsProgram_eq_encodeCNF {k : ℕ} (ccnf : CanonicalCNF k) :
    encodeCanonicalCNFAsProgram ccnf = encodeCNF ccnf.val := rfl

/-- Program size for canonical CNF is just encoded tape length. -/
@[simp] theorem encodeCanonicalCNFAsProgram_length {k : ℕ} (ccnf : CanonicalCNF k) :
    (encodeCanonicalCNFAsProgram ccnf).length = (encodeCNF ccnf.val).length := rfl

/--
Program composition is closed: the sum/composition of two programs is a program.
In this binary machine model, composition is concatenation.
-/
def combinePrograms (p q : ComputerProgram) : ComputerProgram := List.append p q

/-- Combined programs are definitionally append. -/
@[simp] theorem combinePrograms_eq_append (p q : ComputerProgram) :
    combinePrograms p q = List.append p q := rfl

/-- Composition cost is additive in program length. -/
@[simp] theorem combinePrograms_length (p q : ComputerProgram) :
    (combinePrograms p q).length = p.length + q.length := by
  simp [combinePrograms]

/-- Existential closure form: sum of two programs is itself a program. -/
theorem computerProgram_sum_is_program (p q : ComputerProgram) :
    ∃ r : ComputerProgram, r = List.append p q := by
  refine ⟨combinePrograms p q, ?_⟩
  simp [combinePrograms]

end EGPT.Complexity
