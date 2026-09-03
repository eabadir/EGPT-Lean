import Archive.Constraints
import Archive.Complexity.Core
import Archive.Complexity.SetRFL
import Archive.Complexity.TableauFromCNF
import Archive.NumberTheory.Core

namespace EGPT.Complexity

open EGPT.Constraints EGPT.NumberTheory.Core

/-!
# Constructive Decomposition

This module isolates an assignment-free SAT criterion for experimentation,
without changing the load-bearing proof chain in `SetRFL.lean`. It is aligned to
the explicit CNF-derived semantic layer `SetRFL.AllSatisfyingAssignments`.

The criterion is grounded in a 2D walk view:
- Clause rows must all be covered by selected gates (literals).
- Global polarity must remain consistent (`x_i` and `¬x_i` cannot both be selected).
-/

/--
A decomposition record for a CNF.
`factors` are atom codes derived from all clause literals.
-/
structure ConstructiveDecomposition (k : ℕ) where
  cnf : SyntacticCNF_EGPT k
  factors : List EGPTPrime

/--
The concrete walk-cost model used in this experimental file:
walk each clause row against all `k` variable columns.
-/
def ConstructiveDecomposition.complexity {k : ℕ} (d : ConstructiveDecomposition k) : ℕ :=
  d.cnf.length * k

/--
Decompose a CNF by collecting all literal atom codes.
This function takes only the CNF (no assignment input).
-/
def decomposeCNF {k : ℕ} (cnf : SyntacticCNF_EGPT k) : ConstructiveDecomposition k :=
  let factors := (cnf.flatten.map LiteralToPrime)
  { cnf := cnf, factors := factors }

/--
Literal negation at the same variable address.
-/
def negateLiteral {k : ℕ} (l : Literal_EGPT k) : Literal_EGPT k :=
  { l with polarity := !l.polarity }

/--
A witness function for gate-selection decisions.
`true` means "selected in the walk".
-/
abbrev WalkWitness (k : ℕ) := Literal_EGPT k → Bool

/-- A clause is covered if one of its literals is selected. -/
def ClauseCoveredBy {k : ℕ} (w : WalkWitness k) (clause : Clause_EGPT k) : Prop :=
  ∃ lit, lit ∈ clause ∧ w lit = true

/-- Every clause row is covered by the selected gates. -/
def CoversAllClauses {k : ℕ} (cnf : SyntacticCNF_EGPT k) (w : WalkWitness k) : Prop :=
  ∀ clause ∈ cnf, ClauseCoveredBy w clause

/-- Global polarity consistency: never select both `xᵢ` and `¬xᵢ`. -/
def PolarityConsistent {k : ℕ} (w : WalkWitness k) : Prop :=
  ∀ lit, w lit = true → w (negateLiteral lit) = false

/--
Assignment-free SAT criterion:
there exists a clause-covering, polarity-consistent walk witness.
-/
def AssignmentFreeSAT {k : ℕ} (cnf : SyntacticCNF_EGPT k) : Prop :=
  ∃ w : WalkWitness k, CoversAllClauses cnf w ∧ PolarityConsistent w

/-- Build a concrete assignment from a walk witness. -/
def assignmentFromWitness {k : ℕ} (w : WalkWitness k) : Vector Bool k :=
  Vector.ofFn (fun i => w { particle_idx := i, polarity := true })

/--
If a literal is selected by a polarity-consistent witness, it evaluates to `true`
under the assignment induced by that witness.
-/
lemma witness_true_implies_eval_true {k : ℕ}
    (w : WalkWitness k) (h_cons : PolarityConsistent w)
    (lit : Literal_EGPT k) (h_w : w lit = true) :
    evalLiteral lit (assignmentFromWitness w) = true := by
  cases lit with
  | mk idx pol =>
    cases h_pol : pol
    · -- negative literal selected
      have h_neg : w { particle_idx := idx, polarity := true } = false := by
        simpa [negateLiteral, h_pol] using
          (h_cons { particle_idx := idx, polarity := false } (by simpa [h_pol] using h_w))
      have h_get : (assignmentFromWitness w).get idx = w { particle_idx := idx, polarity := true } := by
        simp [assignmentFromWitness, Vector.get]
      simp [evalLiteral, h_pol, h_get, h_neg]
    · -- positive literal selected
      have h_pos : w { particle_idx := idx, polarity := true } = true := by
        simpa [h_pol] using h_w
      have h_get : (assignmentFromWitness w).get idx = w { particle_idx := idx, polarity := true } := by
        simp [assignmentFromWitness, Vector.get]
      simp [evalLiteral, h_pol, h_get, h_pos]

/--
Soundness: any assignment-free witness yields a satisfying assignment.
-/
theorem assignmentFree_sound {k : ℕ} (cnf : SyntacticCNF_EGPT k) :
    AssignmentFreeSAT cnf → ∃ assignment : Vector Bool k, evalCNF cnf assignment = true := by
  intro h_sat
  rcases h_sat with ⟨w, h_cover, h_cons⟩
  refine ⟨assignmentFromWitness w, ?_⟩
  unfold evalCNF
  rw [List.all_eq_true]
  intro clause h_clause_mem
  rcases h_cover clause h_clause_mem with ⟨lit, h_lit_mem, h_lit_selected⟩
  unfold evalClause
  rw [List.any_eq_true]
  refine ⟨lit, h_lit_mem, ?_⟩
  exact witness_true_implies_eval_true w h_cons lit h_lit_selected

/-- The canonical witness extracted from a concrete assignment. -/
def witnessFromAssignment {k : ℕ} (assignment : Vector Bool k) : WalkWitness k :=
  fun lit => evalLiteral lit assignment

/-- Coverage of every clause by the witness induced from a satisfying assignment. -/
lemma witnessFromAssignment_covers {k : ℕ}
    (cnf : SyntacticCNF_EGPT k) (assignment : Vector Bool k)
    (h_sat : evalCNF cnf assignment = true) :
    CoversAllClauses cnf (witnessFromAssignment assignment) := by
  intro clause h_clause_mem
  have h_clause_true : evalClause clause assignment = true := by
    unfold evalCNF at h_sat
    rw [List.all_eq_true] at h_sat
    exact h_sat clause h_clause_mem
  unfold evalClause at h_clause_true
  rw [List.any_eq_true] at h_clause_true
  rcases h_clause_true with ⟨lit, h_lit_mem, h_lit_true⟩
  refine ⟨lit, h_lit_mem, ?_⟩
  simpa [witnessFromAssignment] using h_lit_true

/-- Polarity consistency of the witness induced from any assignment. -/
lemma witnessFromAssignment_consistent {k : ℕ} (assignment : Vector Bool k) :
    PolarityConsistent (witnessFromAssignment assignment) := by
  intro lit h_lit_true
  cases h_val : assignment.get lit.particle_idx <;>
    cases h_pol : lit.polarity <;>
    simp [witnessFromAssignment, evalLiteral, negateLiteral, h_val, h_pol] at h_lit_true ⊢

/--
Completeness: a satisfying assignment induces an assignment-free witness.
-/
theorem assignmentFree_complete {k : ℕ} (cnf : SyntacticCNF_EGPT k) :
    (∃ assignment : Vector Bool k, evalCNF cnf assignment = true) → AssignmentFreeSAT cnf := by
  rintro ⟨assignment, h_sat⟩
  refine ⟨witnessFromAssignment assignment, ?_, ?_⟩
  · exact witnessFromAssignment_covers cnf assignment h_sat
  · exact witnessFromAssignment_consistent assignment

/-- SAT is equivalent to the assignment-free clause-coverage + polarity criterion. -/
theorem assignmentFree_iff_sat {k : ℕ} (cnf : SyntacticCNF_EGPT k) :
    AssignmentFreeSAT cnf ↔ ∃ assignment : Vector Bool k, evalCNF cnf assignment = true := by
  constructor
  · exact assignmentFree_sound cnf
  · exact assignmentFree_complete cnf

/--
Alignment theorem to the explicit semantic layer:
assignment-free criterion is equivalent to nonempty CNF-derived satisfying set.
-/
theorem assignmentFree_iff_nonempty_allSatisfyingAssignments {k : ℕ} (cnf : SyntacticCNF_EGPT k) :
    AssignmentFreeSAT cnf ↔ (SetRFL.AllSatisfyingAssignments cnf).Nonempty := by
  simpa [SetRFL.AllSatisfyingAssignments] using (assignmentFree_iff_sat (cnf := cnf))

/--
Native polynomial used for the walk bound: `n²`.
-/
def decomposition_poly : EGPT_Polynomial :=
  EGPT_Polynomial.mul EGPT_Polynomial.id EGPT_Polynomial.id

@[simp] lemma eval_decomposition_poly (n : ℕ) :
    toNat ((decomposition_poly).eval (fromNat n)) = n * n := by
  simp [decomposition_poly, EGPT_Polynomial.eval, toNat_mul_ParticlePath, left_inv]

/-- Polynomial bound of the decomposition walk complexity by encoded input size. -/
theorem decomposition_is_poly_bounded {k : ℕ} (cnf : SyntacticCNF_EGPT k) :
    (decomposeCNF cnf).complexity ≤ toNat (decomposition_poly.eval (fromNat (encodeCNF cnf).length)) := by
  calc
    (decomposeCNF cnf).complexity
        = cnf.length * k := by simp [decomposeCNF, ConstructiveDecomposition.complexity]
    _ ≤ (encodeCNF cnf).length * (encodeCNF cnf).length := by
      apply Nat.mul_le_mul
      · exact cnf_length_le_encoded_length cnf
      · exact encodeCNF_size_ge_k k cnf
    _ = toNat (decomposition_poly.eval (fromNat (encodeCNF cnf).length)) := by
      rw [eval_decomposition_poly]

/-!
### SAT-Compatible Common-Factor Predicate (Prime-Indexed)

This section defines an arithmetic SAT criterion where each literal is mapped to
a prime-indexed atom (`literalAtom`), assignments are encoded as products of the
selected literal atoms, and clause/CNF satisfaction is characterized by shared
prime factors.
-/

/-- The literal selected by assignment `a` at variable index `i`. -/
def chosenLiteral {k : ℕ} (a : Vector Bool k) (i : Fin k) : Literal_EGPT k :=
  { particle_idx := i, polarity := a.get i }

/--
Prime-indexed assignment composite:
product of one selected literal atom per variable index.
-/
noncomputable def assignmentCompositePrime {k : ℕ} (a : Vector Bool k) : ℕ :=
  ((Finset.univ : Finset (Fin k)).toList.map (fun i => literalAtom (chosenLiteral a i))).prod

/-- A literal shares a factor with assignment composite iff its atom divides it. -/
def literalSharesFactor {k : ℕ} (a : Vector Bool k) (lit : Literal_EGPT k) : Prop :=
  literalAtom lit ∣ assignmentCompositePrime a

/-- A clause shares a factor with assignment composite if some member literal does. -/
def clauseSharesFactor {k : ℕ} (a : Vector Bool k) (clause : Clause_EGPT k) : Prop :=
  ∃ lit, lit ∈ clause ∧ literalSharesFactor a lit

/-- A CNF shares factors with assignment composite when all clauses do. -/
def cnfSharesFactor {k : ℕ} (a : Vector Bool k) (cnf : SyntacticCNF_EGPT k) : Prop :=
  ∀ clause ∈ cnf, clauseSharesFactor a clause

/-- CNF-level common-factor satisfiability (assignment-free existential form). -/
def CNFSharesFactor {k : ℕ} (cnf : SyntacticCNF_EGPT k) : Prop :=
  ∃ a : Vector Bool k, cnfSharesFactor a cnf

/-- Any assignment-selected literal evaluates to `true` by definition. -/
lemma evalLiteral_chosenLiteral_true {k : ℕ} (a : Vector Bool k) (i : Fin k) :
    evalLiteral (chosenLiteral a i) a = true := by
  cases hval : a.get i <;> simp [chosenLiteral, evalLiteral, hval]

/-- `evalLiteral` in equality form: literal polarity must match assignment bit. -/
lemma evalLiteral_eq_true_iff_polarity_eq {k : ℕ} (lit : Literal_EGPT k) (a : Vector Bool k) :
    evalLiteral lit a = true ↔ lit.polarity = a.get lit.particle_idx := by
  cases hval : a.get lit.particle_idx <;> cases hpol : lit.polarity <;>
    simp [evalLiteral, hval, hpol]

/--
Literal-level SAT/common-factor equivalence:
`evalLiteral = true` iff literal atom divides assignment composite.
-/
lemma evalLiteral_true_iff_literalSharesFactor {k : ℕ} (a : Vector Bool k) (lit : Literal_EGPT k) :
    evalLiteral lit a = true ↔ literalSharesFactor a lit := by
  constructor
  · intro h_eval
    have h_pol : lit.polarity = a.get lit.particle_idx :=
      (evalLiteral_eq_true_iff_polarity_eq lit a).1 h_eval
    have h_lit_eq : lit = chosenLiteral a lit.particle_idx := by
      cases lit with
      | mk idx pol =>
          simp [chosenLiteral] at h_pol ⊢
          cases h_pol
          rfl
    have h_mem : lit.particle_idx ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ _
    have h_mem_list :
        literalAtom (chosenLiteral a lit.particle_idx) ∈
          (Finset.univ : Finset (Fin k)).toList.map (fun i => literalAtom (chosenLiteral a i)) := by
      rw [List.mem_map]
      exact ⟨lit.particle_idx, Finset.mem_toList.mpr h_mem, rfl⟩
    have h_dvd_selected :
        literalAtom (chosenLiteral a lit.particle_idx) ∣
          ((Finset.univ : Finset (Fin k)).toList.map (fun i => literalAtom (chosenLiteral a i))).prod := by
      exact List.dvd_prod h_mem_list
    unfold literalSharesFactor assignmentCompositePrime
    rw [h_lit_eq]
    exact h_dvd_selected
  · intro h_dvd
    have h_prime_nat : Nat.Prime (literalAtom lit) := literalAtom_prime lit
    have h_prime : Prime (literalAtom lit) := Nat.prime_iff.mp h_prime_nat
    have h_dvd_prod :
        literalAtom lit ∣ ((Finset.univ : Finset (Fin k)).toList.map (fun i => literalAtom (chosenLiteral a i))).prod := by
      simpa [literalSharesFactor, assignmentCompositePrime] using h_dvd
    rcases (Prime.dvd_prod_iff h_prime).1 h_dvd_prod with ⟨atom, h_atom_mem, h_dvd_i⟩
    rw [List.mem_map] at h_atom_mem
    rcases h_atom_mem with ⟨i, hi_mem, h_atom_eq⟩
    have _ : i ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_toList.mp hi_mem
    have h_prime_i : Nat.Prime (literalAtom (chosenLiteral a i)) := literalAtom_prime (chosenLiteral a i)
    have h_dvd_i' : literalAtom lit ∣ literalAtom (chosenLiteral a i) := by
      simpa [h_atom_eq] using h_dvd_i
    have h_atom_eq_rev : literalAtom (chosenLiteral a i) = literalAtom lit := by
      exact (Nat.Prime.dvd_iff_eq h_prime_i h_prime_nat.ne_one).1 h_dvd_i'
    have h_lit_eq : lit = chosenLiteral a i := by
      exact literalAtom_injective h_atom_eq_rev.symm
    simpa [h_lit_eq] using evalLiteral_chosenLiteral_true a i

/--
Clause-level SAT/common-factor equivalence:
`evalClause = true` iff clause shares a factor with assignment composite.
-/
lemma evalClause_true_iff_clauseSharesFactor {k : ℕ} (a : Vector Bool k) (clause : Clause_EGPT k) :
    evalClause clause a = true ↔ clauseSharesFactor a clause := by
  constructor
  · intro h_clause
    unfold evalClause at h_clause
    rw [List.any_eq_true] at h_clause
    rcases h_clause with ⟨lit, h_mem, h_eval_lit⟩
    exact ⟨lit, h_mem, (evalLiteral_true_iff_literalSharesFactor a lit).1 h_eval_lit⟩
  · rintro ⟨lit, h_mem, h_share⟩
    unfold evalClause
    rw [List.any_eq_true]
    exact ⟨lit, h_mem, (evalLiteral_true_iff_literalSharesFactor a lit).2 h_share⟩

/--
CNF-level SAT/common-factor equivalence:
`evalCNF = true` iff every clause shares a factor with assignment composite.
-/
theorem evalCNF_true_iff_cnfSharesFactor {k : ℕ} (a : Vector Bool k) (cnf : SyntacticCNF_EGPT k) :
    evalCNF cnf a = true ↔ cnfSharesFactor a cnf := by
  constructor
  · intro h_cnf
    intro clause h_clause_mem
    have h_all : ∀ c ∈ cnf, evalClause c a = true := by
      simpa [evalCNF, List.all_eq_true] using h_cnf
    exact (evalClause_true_iff_clauseSharesFactor a clause).1 (h_all clause h_clause_mem)
  · intro h_share
    rw [evalCNF, List.all_eq_true]
    intro clause h_clause_mem
    exact (evalClause_true_iff_clauseSharesFactor a clause).2 (h_share clause h_clause_mem)

/--
Bridge theorem: CNF common-factor satisfiability is equivalent to nonempty
`AllSatisfyingAssignments`.
-/
theorem cnfSharesFactor_iff_nonempty_allSatisfyingAssignments {k : ℕ} (cnf : SyntacticCNF_EGPT k) :
    CNFSharesFactor cnf ↔ (SetRFL.AllSatisfyingAssignments cnf).Nonempty := by
  constructor
  · rintro ⟨a, h_share⟩
    exact ⟨a, (evalCNF_true_iff_cnfSharesFactor a cnf).2 h_share⟩
  · rintro ⟨a, h_eval⟩
    exact ⟨a, (evalCNF_true_iff_cnfSharesFactor a cnf).1 h_eval⟩

/-- Constructor-facing bridge: common-factor success yields a satisfying assignment. -/
theorem exists_assignment_of_cnfSharesFactor {k : ℕ} (cnf : SyntacticCNF_EGPT k) :
    CNFSharesFactor cnf → ∃ assignment : Vector Bool k, evalCNF cnf assignment = true := by
  intro h
  rcases (cnfSharesFactor_iff_nonempty_allSatisfyingAssignments (cnf := cnf)).1 h with ⟨a, ha⟩
  exact ⟨a, ha⟩

/-- Constructor-facing bridge: satisfying assignment yields common-factor success. -/
theorem cnfSharesFactor_of_exists_assignment {k : ℕ} (cnf : SyntacticCNF_EGPT k) :
    (∃ assignment : Vector Bool k, evalCNF cnf assignment = true) → CNFSharesFactor cnf := by
  rintro ⟨a, ha⟩
  exact (cnfSharesFactor_iff_nonempty_allSatisfyingAssignments (cnf := cnf)).2 ⟨a, ha⟩

/-! ## Examples and tests

These definitions demonstrate the assignment-free SAT criterion on concrete
CNF instances. They are not part of the proof chain.
-/

/-!
### Representative Lean Validation Cases
-/

private def lit0Pos : Literal_EGPT 1 :=
  { particle_idx := ⟨0, by decide⟩, polarity := true }

private def lit0Neg : Literal_EGPT 1 :=
  { particle_idx := ⟨0, by decide⟩, polarity := false }

private def satUnitCNF : SyntacticCNF_EGPT 1 := [[lit0Pos]]
private def unsatUnitCNF : SyntacticCNF_EGPT 1 := [[lit0Pos], [lit0Neg]]

private def aTrue1 : Vector Bool 1 := ⟨#[true], by decide⟩
private def aFalse1 : Vector Bool 1 := ⟨#[false], by decide⟩

private lemma aTrue1_get0 : aTrue1.get 0 = true := by
  rfl

private lemma aFalse1_get0 : aFalse1.get 0 = false := by
  rfl

example : evalCNF satUnitCNF aTrue1 = true := by
  simp [satUnitCNF, lit0Pos, evalCNF, evalClause, evalLiteral, aTrue1_get0]

example : cnfSharesFactor aTrue1 satUnitCNF := by
  exact (evalCNF_true_iff_cnfSharesFactor aTrue1 satUnitCNF).1 (by
    simp [satUnitCNF, lit0Pos, evalCNF, evalClause, evalLiteral, aTrue1_get0])

example : evalCNF satUnitCNF aFalse1 = false := by
  simp [satUnitCNF, lit0Pos, evalCNF, evalClause, evalLiteral, aFalse1_get0]

example : ¬ CNFSharesFactor unsatUnitCNF := by
  intro h
  rcases exists_assignment_of_cnfSharesFactor (cnf := unsatUnitCNF) h with ⟨a, h_eval⟩
  have h_cases : a.get ⟨0, by decide⟩ = true ∨ a.get ⟨0, by decide⟩ = false := by
    cases hbit : a.get ⟨0, by decide⟩ <;> simp [hbit]
  cases h_cases with
  | inl h_true =>
      have : evalCNF unsatUnitCNF a = false := by
        simp [unsatUnitCNF, lit0Pos, lit0Neg, evalCNF, evalClause, evalLiteral, h_true]
      rw [this] at h_eval
      contradiction
  | inr h_false =>
      have : evalCNF unsatUnitCNF a = false := by
        simp [unsatUnitCNF, lit0Pos, lit0Neg, evalCNF, evalClause, evalLiteral, h_false]
      rw [this] at h_eval
      contradiction

/--
**UNSAT Detection via Prime Structure.**

If no assignment's prime-indexed composite shares factors with every clause of the
CNF (`¬ CNFSharesFactor cnf`), then `computeTableau?` returns `none` for every
candidate. This connects the prime factorization layer to the computational layer:

- `¬ CNFSharesFactor cnf` means no assignment satisfies the CNF (via
  `evalCNF_true_iff_cnfSharesFactor`).
- `computeTableau?` returns `none` exactly when `evalCNF` returns `false`
  (via `computeTableau_none_iff_not_sat`).

The prime factorization encoding faithfully detects unsatisfiability.
-/
theorem unsat_detected_by_prime_structure {k : ℕ} (cnf : SyntacticCNF_EGPT k) :
    (¬ CNFSharesFactor cnf) → ∀ v : Vector Bool k, computeTableau? cnf v = none := by
  intro h_not_share v
  rw [computeTableau_none_iff_not_sat]
  -- h_not_share : ¬ ∃ a, cnfSharesFactor a cnf
  -- Goal: evalCNF cnf v = false
  -- If evalCNF cnf v were true, then cnfSharesFactor v cnf, contradicting h_not_share
  cases h_eval : evalCNF cnf v with
  | false => rfl
  | true =>
    exfalso
    exact h_not_share ⟨v, (evalCNF_true_iff_cnfSharesFactor v cnf).mp h_eval⟩

/-!
### Conditional Entropy Formulation: H(k|p) ↔ GCD

The information-theoretic characterization of `literalSharesFactor`.
Conditional entropy of a literal given an assignment composite is zero
iff the literal's prime divides the composite — the GCD analog of
Euclidean reduction in information space.

By the LFTA (`log(n) = Σ v_p(n) · log(p)`), information decomposes
additively under prime factorization. The conditional entropy of a literal
given a composite measures how much NEW information the literal provides:
- Zero when the literal's prime already divides the composite (GCD captures it)
- `log(p)` when the literal's prime is absent (full new information)

This is the bijective analog of GCD: just as `gcd(n, p) = p` iff `p | n`,
`H(literal | composite) = 0` iff `literalSharesFactor`.
-/

/--
Conditional entropy of a literal given a composite number.
`H(literal | composite) = 0` when the literal's prime divides the composite
(the literal's information is already present — zero new information), and
`H(literal | composite) = Real.log(literalAtom lit)` when it does not
(the literal provides full new information of `log(p)` nats).

This is the information-theoretic formulation of prime divisibility:
checking a literal is measuring its conditional entropy.
-/
noncomputable def conditionalLiteralEntropy {k : ℕ}
    (composite : ℕ) (lit : Literal_EGPT k) : ℝ :=
  if literalAtom lit ∣ composite then 0
  else Real.log (literalAtom lit)

/--
Conditional entropy of a clause given a composite: zero iff at least one
literal in the clause has zero conditional entropy (shares a factor).
A clause is satisfied iff some literal contributes no new information.
-/
noncomputable def conditionalClauseEntropy {k : ℕ}
    (composite : ℕ) (clause : Clause_EGPT k) : ℝ :=
  if ∃ lit ∈ clause, conditionalLiteralEntropy composite lit = 0 then 0
  else (clause.map (conditionalLiteralEntropy composite)).sum

/--
Conditional entropy of a CNF given a composite: the sum of clause-level
conditional entropies. Zero iff every clause has zero conditional entropy.
-/
noncomputable def conditionalCNFEntropy {k : ℕ}
    (composite : ℕ) (cnf : SyntacticCNF_EGPT k) : ℝ :=
  (cnf.map (conditionalClauseEntropy composite)).sum

/-- Literal conditional entropy is non-negative. -/
theorem conditionalLiteralEntropy_nonneg {k : ℕ}
    (composite : ℕ) (lit : Literal_EGPT k) :
    0 ≤ conditionalLiteralEntropy composite lit := by
  unfold conditionalLiteralEntropy
  split
  · exact le_refl 0
  · exact le_of_lt (Real.log_pos (by exact_mod_cast (literalAtom_prime lit).one_lt))

/--
The key bridge: `literalSharesFactor ↔ zero conditional entropy`.
A literal shares a factor with the assignment composite iff its
conditional entropy is zero — the information-theoretic reformulation
of prime divisibility.
-/
theorem literalSharesFactor_iff_zero_conditional_entropy {k : ℕ}
    (a : Vector Bool k) (lit : Literal_EGPT k) :
    literalSharesFactor a lit ↔
      conditionalLiteralEntropy (assignmentCompositePrime a) lit = 0 := by
  unfold literalSharesFactor conditionalLiteralEntropy
  constructor
  · intro h; simp [h]
  · intro h
    split at h
    · assumption
    · exact absurd h (ne_of_gt (Real.log_pos (by exact_mod_cast (literalAtom_prime lit).one_lt)))

/-- Positive conditional entropy means the literal does NOT share a factor. -/
theorem conditionalLiteralEntropy_pos_iff_not_shares {k : ℕ}
    (composite : ℕ) (lit : Literal_EGPT k) :
    0 < conditionalLiteralEntropy composite lit ↔ ¬ literalAtom lit ∣ composite := by
  unfold conditionalLiteralEntropy
  constructor
  · intro h
    split at h
    · exact absurd (le_refl 0) (not_le.mpr h)
    · assumption
  · intro h; simp [h]; exact Real.log_pos (by exact_mod_cast (literalAtom_prime lit).one_lt)

/--
GCD characterization — the explicit GCD ↔ entropy bridge.
Conditional entropy is zero iff `gcd(composite, literalAtom) = literalAtom`,
i.e. the literal's prime divides the composite.
-/
theorem conditional_entropy_gcd_characterization {k : ℕ}
    (composite : ℕ) (_hc : 0 < composite) (lit : Literal_EGPT k) :
    conditionalLiteralEntropy composite lit = 0 ↔
      Nat.gcd composite (literalAtom lit) = literalAtom lit := by
  unfold conditionalLiteralEntropy
  constructor
  · intro h
    split at h
    · next h_dvd =>
      exact Nat.dvd_antisymm
        (Nat.gcd_dvd_right composite (literalAtom lit))
        (Nat.dvd_gcd h_dvd (dvd_refl _))
    · next h_not_dvd =>
      exact absurd h (ne_of_gt (Real.log_pos (by exact_mod_cast (literalAtom_prime lit).one_lt)))
  · intro h
    have h_dvd : literalAtom lit ∣ composite := by
      have := Nat.gcd_dvd_left composite (literalAtom lit)
      rwa [h] at this
    simp [h_dvd]

/-- Clause-level conditional entropy is non-negative. -/
theorem conditionalClauseEntropy_nonneg {k : ℕ}
    (composite : ℕ) (clause : Clause_EGPT k) :
    0 ≤ conditionalClauseEntropy composite clause := by
  unfold conditionalClauseEntropy
  split
  · exact le_refl 0
  · exact List.sum_nonneg (fun x hx => by
      rw [List.mem_map] at hx
      rcases hx with ⟨lit, _, rfl⟩
      exact conditionalLiteralEntropy_nonneg composite lit)

/--
Clause-level bridge: `clauseSharesFactor ↔ zero conditional clause entropy`
for nonempty clauses. The nonempty hypothesis is needed because an empty
clause has zero entropy (empty sum) but `clauseSharesFactor` is vacuously false.
-/
theorem clauseSharesFactor_iff_zero_conditional_clause_entropy {k : ℕ}
    (a : Vector Bool k) (clause : Clause_EGPT k) (h_nonempty : clause ≠ []) :
    clauseSharesFactor a clause ↔
      conditionalClauseEntropy (assignmentCompositePrime a) clause = 0 := by
  unfold clauseSharesFactor conditionalClauseEntropy
  constructor
  · rintro ⟨lit, h_mem, h_share⟩
    have h_zero := (literalSharesFactor_iff_zero_conditional_entropy a lit).mp h_share
    simp [show ∃ lit ∈ clause, conditionalLiteralEntropy (assignmentCompositePrime a) lit = 0 from ⟨lit, h_mem, h_zero⟩]
  · intro h
    split at h
    · next h_exists =>
      rcases h_exists with ⟨lit, h_mem, h_zero⟩
      exact ⟨lit, h_mem, (literalSharesFactor_iff_zero_conditional_entropy a lit).mpr h_zero⟩
    · -- In the else branch, h says the sum = 0. Every term is non-negative
      -- and each term is positive (since no term is zero). For a nonempty clause,
      -- the sum must be strictly positive — contradiction.
      next h_not_exists =>
      push_neg at h_not_exists
      exfalso
      have h_all_pos : ∀ lit ∈ clause, 0 < conditionalLiteralEntropy (assignmentCompositePrime a) lit := by
        intro lit h_mem
        exact lt_of_le_of_ne (conditionalLiteralEntropy_nonneg _ lit) (Ne.symm (h_not_exists lit h_mem))
      -- Get a witness literal from nonempty clause
      obtain ⟨wit, h_wit_mem⟩ : ∃ w, w ∈ clause := by
        cases clause with
        | nil => exact absurd rfl h_nonempty
        | cons hd _ => exact ⟨hd, .head _⟩
      have h_wit_pos := h_all_pos wit h_wit_mem
      -- The sum of the mapped list is positive because each entry is ≥ 0
      -- and at least one (wit's entropy) is strictly positive.
      have h_sum_pos : 0 < (clause.map (conditionalLiteralEntropy (assignmentCompositePrime a))).sum := by
        obtain ⟨pre, post, h_eq⟩ := List.append_of_mem h_wit_mem
        rw [h_eq, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
        have h_pre_nonneg : 0 ≤ (pre.map (conditionalLiteralEntropy (assignmentCompositePrime a))).sum :=
          List.sum_nonneg (fun x hx => by
            rw [List.mem_map] at hx; rcases hx with ⟨lit, _, rfl⟩
            exact conditionalLiteralEntropy_nonneg _ lit)
        have h_post_nonneg : 0 ≤ (post.map (conditionalLiteralEntropy (assignmentCompositePrime a))).sum :=
          List.sum_nonneg (fun x hx => by
            rw [List.mem_map] at hx; rcases hx with ⟨lit, _, rfl⟩
            exact conditionalLiteralEntropy_nonneg _ lit)
        linarith
      linarith

/-!
### CNF-Level Conditional Entropy Bridge (Exchange 17, Theorem A)

Extends the clause-level bridge (`clauseSharesFactor_iff_zero_conditional_clause_entropy`)
to full CNFs: `cnfSharesFactor a cnf ↔ conditionalCNFEntropy(composite, cnf) = 0`.

The proof: forward, if all clauses share factors then each clause entropy is zero
(by clause-level bridge), so the sum is zero. Backward, if the sum of non-negative
terms is zero, each term is zero, so each clause shares a factor.
-/

/--
CNF-level bridge: `cnfSharesFactor ↔ zero conditional CNF entropy`.
A CNF shares factors with the assignment composite iff the total conditional
entropy is zero — every clause's information is already present.

Requires each clause to be nonempty (same condition as clause-level bridge).
-/
theorem cnfSharesFactor_iff_zero_conditional_cnf_entropy {k : ℕ}
    (a : Vector Bool k) (cnf : SyntacticCNF_EGPT k)
    (h_clauses_nonempty : ∀ c ∈ cnf, c ≠ []) :
    cnfSharesFactor a cnf ↔
      conditionalCNFEntropy (assignmentCompositePrime a) cnf = 0 := by
  unfold cnfSharesFactor conditionalCNFEntropy
  constructor
  · intro h_all_share
    apply List.sum_eq_zero
    intro x hx
    rw [List.mem_map] at hx
    rcases hx with ⟨clause, h_mem, rfl⟩
    exact (clauseSharesFactor_iff_zero_conditional_clause_entropy a clause
      (h_clauses_nonempty clause h_mem)).mp (h_all_share clause h_mem)
  · intro h_sum_zero
    intro clause h_clause_mem
    -- Each clause entropy is non-negative
    have h_nonneg : ∀ c ∈ cnf, 0 ≤ conditionalClauseEntropy (assignmentCompositePrime a) c :=
      fun c _ => conditionalClauseEntropy_nonneg _ c
    -- If a sum of non-negative reals equals zero, each term must be zero
    -- We prove this by contradiction: if some term were positive, the sum would be positive
    have h_clause_zero : conditionalClauseEntropy (assignmentCompositePrime a) clause = 0 := by
      by_contra h_ne
      have h_pos : 0 < conditionalClauseEntropy (assignmentCompositePrime a) clause :=
        lt_of_le_of_ne (h_nonneg clause h_clause_mem) (Ne.symm h_ne)
      -- Split cnf at clause
      obtain ⟨pre, post, h_eq⟩ := List.append_of_mem h_clause_mem
      rw [h_eq, List.map_append, List.map_cons, List.sum_append, List.sum_cons] at h_sum_zero
      have h_pre_nn : 0 ≤ (pre.map (conditionalClauseEntropy (assignmentCompositePrime a))).sum :=
        List.sum_nonneg (fun x hx => by
          rw [List.mem_map] at hx; rcases hx with ⟨c, hc, rfl⟩
          exact conditionalClauseEntropy_nonneg _ c)
      have h_post_nn : 0 ≤ (post.map (conditionalClauseEntropy (assignmentCompositePrime a))).sum :=
        List.sum_nonneg (fun x hx => by
          rw [List.mem_map] at hx; rcases hx with ⟨c, _, rfl⟩
          exact conditionalClauseEntropy_nonneg _ c)
      linarith
    exact (clauseSharesFactor_iff_zero_conditional_clause_entropy a clause
      (h_clauses_nonempty clause h_clause_mem)).mpr h_clause_zero

end EGPT.Complexity
