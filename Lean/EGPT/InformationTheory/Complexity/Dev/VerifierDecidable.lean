/-
Copyright (c) 2026 Essam Abadir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Essam Abadir
-/

/-!
⚠️  **REWRITE PENDING** — sourced from `eabadir/EGPT-dev-backup` (Dev branch),
originally `Lean/PR/InformationTheory/Complexity/Dev/VerifierDecidableWS.lean`.

Imported as `InformationTheory.Complexity.Dev.VerifierDecidable` by `Tests.lean`,
`TestSAT64/128.lean`, `TestSATLIB.lean`, `TestCompetition*.lean`,
`VerifierWIP*.lean` under `Complexity/Dev/`.

The current implementation is variable-driven (unit-propagation +
knock-out completion with score-based polarity + fallback). This must be
rewritten as a clause-driven walk over a CNF / sorted-merge of signed
prime composites — see EGPT proof discipline IN42 / E35 and FRAQTL
`CLAUDE.md` ("Library coding discipline" / "Library anti-patterns").
The framework (signatures, signed-atom structure, tableau plumbing) is
the starting point; the propagation core is the part that has to go.
-/

import InformationTheory.Complexity.CNF
import InformationTheory.Complexity.CNF.Prime
import InformationTheory.Complexity.Tableau
import InformationTheory.EntropyNumber.Int

/-!
# Prime Dictionary, Signed Atoms, and the NP Verifier

This file builds the prime-dictionary-based verification pipeline for CNF
formulas. Each variable maps to a unique prime via `variablePrime`. The
prime dictionary (`allVectors`) is the deduplicated list of variable primes
from the entire CNF. The NP verifier uses unit propagation followed by
knock-out completion (score-based polarity choice with fallback) to find a
satisfying assignment, then records the verification trace as signed atoms
(`EntropyInt`).

## Main definitions

* `clauseVariablePrimes` -- variable primes from a single clause.
* `allVectors` -- the deduplicated prime dictionary of the CNF.
* `allVectorsProduct` / `allVectorsEntropy` / `allVectorsProgram` -- derived forms.
* `hasExtractableAtoms` -- does the CNF have any variable primes?
* `literalToSignedAtom` -- maps a literal to its signed prime atom (`EntropyInt`).
* `Assignment` -- per-variable committed polarity state.
* `literalSatisfied` / `literalFalsified` / `clauseSatisfied` -- assignment queries.
* `uncommittedLiterals` -- free literals in a clause.
* `propagateOnce` / `unitPropagate` -- unit propagation loop.
* `polarityScore` / `bestPolarity` -- score-based polarity choice.
* `freeVariables` / `knockOutComplete` -- knock-out completion with fallback.
* `assignmentToVector` -- convert a complete assignment to `Vector Bool k`.
* `npVerifier` -- the NP verifier: unit propagation + knock-out completion.
* `constructTableauAndDecide` -- wraps `npVerifier` to produce `(Bool, ComputerTape)`.
* `verificationComplexity` -- sum of atom magnitudes in the verification trace.
* `computeTableauDecidable` -- extract `List EntropyNat` from the trace.

## Main results

* `hasExtractableAtoms_sound` / `hasExtractableAtoms_complete` / `hasExtractableAtoms_iff`
* `constructTableauAndDecide_iff` -- mirrors `npVerifier` isSome.
-/

namespace InformationTheory

/-!
## Section 1: Prime Dictionary

Each literal maps to a variable prime via `variablePrime lit.particle_idx`.
The prime dictionary is the deduplicated list of all variable primes from
the CNF. One prime per variable that appears, regardless of polarity.
Every entry is a genuine prime -- a vector, not a scalar.
-/

/-- Extract the variable primes from a clause (ignoring polarity). -/
def clauseVariablePrimes {k : ℕ} (clause : Clause k) : List ℕ :=
  clause.map (fun lit => variablePrime lit.particle_idx)

/-- The prime dictionary: deduplicated variable primes from the CNF.
One prime per variable that appears, regardless of polarity.
Every entry is a genuine prime -- a vector, not a scalar. -/
def allVectors {k : ℕ} (cnf : SyntacticCNF k) : List ℕ :=
  (cnf.flatMap clauseVariablePrimes).eraseDups

/-- Backward-compatible alias: the deduplicated prime atoms. -/
abbrev cnfPrimeAtoms {k : ℕ} (cnf : SyntacticCNF k) : List ℕ :=
  allVectors cnf

/-!
## Section 2: Derived Products and Tape Forms
-/

/-- The global composite as the product of all prime vectors. -/
def allVectorsProduct {k : ℕ} (cnf : SyntacticCNF k) : ℕ :=
  (allVectors cnf).prod

/-- The prime vectors encoded as `EntropyNat` for the tape representation. -/
def allVectorsEntropy {k : ℕ} (cnf : SyntacticCNF k) : List EntropyNat :=
  (allVectors cnf).map EntropyNat.ofNat

/-- Flatten the prime vectors into a `ComputerProgram`. -/
def allVectorsProgram {k : ℕ} (cnf : SyntacticCNF k) : ComputerProgram :=
  List.flatten ((allVectorsEntropy cnf).map (fun p => p.val))

/-!
## Section 3: Prime Atom Detection
-/

/-- Does the CNF have extractable prime atoms? Returns `true` iff
at least one prime vector appears across the CNF's clauses. -/
def hasExtractableAtoms {k : ℕ} (cnf : SyntacticCNF k) : Bool :=
  (allVectors cnf).length > 0

/-- If `hasExtractableAtoms` returns `true`, the CNF has prime atoms. -/
theorem hasExtractableAtoms_sound {k : ℕ} (cnf : SyntacticCNF k)
    (h : hasExtractableAtoms cnf = true) :
    (cnfPrimeAtoms cnf).length > 0 := by
  simp [hasExtractableAtoms] at h
  exact h

/-- If the CNF has clauses with literals, then
`hasExtractableAtoms` returns `true`. -/
theorem hasExtractableAtoms_complete {k : ℕ} (cnf : SyntacticCNF k)
    (h : (cnfPrimeAtoms cnf).length > 0) :
    hasExtractableAtoms cnf = true := by
  simp [hasExtractableAtoms]
  exact h

/-- `hasExtractableAtoms` iff the CNF has at least one prime atom. -/
theorem hasExtractableAtoms_iff {k : ℕ} (cnf : SyntacticCNF k) :
    (cnfPrimeAtoms cnf).length > 0 ↔
    hasExtractableAtoms cnf = true :=
  ⟨hasExtractableAtoms_complete cnf, hasExtractableAtoms_sound cnf⟩

/-!
## Section 4: Signed Atoms
-/

/-- Map a literal to its signed atom representation.
The magnitude is the variable index (as `EntropyNat`), the sign is the polarity.
`x₀` and `¬x₀` produce the same magnitude with opposite signs.
The variable's PRIME is accessible separately via `variablePrime`. -/
def literalToSignedAtom {k : ℕ} (lit : Literal k) : EntropyInt :=
  (EntropyNat.ofNat lit.particle_idx.val, lit.polarity)

/-!
## Section 5: Unit Propagation and Knock-Out Completion

The NP verifier uses a two-phase algorithm:
1. **Unit propagation**: scan clauses repeatedly. A unit clause (exactly
   one uncommitted literal, all others falsified) forces that literal's
   variable to its polarity. Repeat until stable. Contradiction = UNSAT.
2. **Knock-out completion**: for each remaining free variable, score both
   polarities (how many alive clauses each would directly satisfy), commit
   the higher-scoring polarity, and propagate. If the preferred polarity
   leads to contradiction, try the other. Both fail = UNSAT.

This replaces the old greedy-walk approach which failed on instances
like `(x₀ ∨ ¬x₁), (¬x₀ ∨ x₂), (¬x₂)` where clause ordering matters,
and the greedy-complete approach which failed on the 4-variable instance
`(¬x₀∨x₁∨x₂), (¬x₀∨x₁∨¬x₂), (¬x₀∨¬x₁∨x₂), (¬x₀∨¬x₁∨¬x₂), (x₀∨x₃)`
where always choosing `true` first picks the wrong polarity for x₀.
-/

/-- The committed assignment state: for each variable, either committed
to a polarity or free (`none`). -/
def Assignment (k : ℕ) := Fin k → Option Bool

/-- Check if a literal is satisfied by the current assignment. -/
def literalSatisfied {k : ℕ} (asgn : Assignment k) (lit : Literal k) : Bool :=
  match asgn lit.particle_idx with
  | some pol => pol == lit.polarity
  | none => false

/-- Check if a literal is falsified by the current assignment. -/
def literalFalsified {k : ℕ} (asgn : Assignment k) (lit : Literal k) : Bool :=
  match asgn lit.particle_idx with
  | some pol => pol != lit.polarity
  | none => false

/-- Check if a clause is satisfied by the current assignment
(at least one literal evaluates to true). -/
def clauseSatisfied {k : ℕ} (asgn : Assignment k) (clause : Clause k) : Bool :=
  clause.any (literalSatisfied asgn)

/-- Get the uncommitted literals in a clause (those whose variable
has not yet been assigned). -/
def uncommittedLiterals {k : ℕ} (asgn : Assignment k) (clause : Clause k) :
    List (Literal k) :=
  clause.filter (fun lit => asgn lit.particle_idx == none)

/-- One pass of unit propagation over the CNF. Returns the updated
assignment and whether anything changed. Returns `none` if a
contradiction is found (a clause with all literals falsified). -/
def propagateOnce {k : ℕ} (cnf : SyntacticCNF k) (asgn : Assignment k) :
    Option (Assignment k × Bool) :=
  cnf.foldlM (init := (asgn, false)) (fun (acc : Assignment k × Bool) clause =>
    let (asgn, changed) := acc
    if clauseSatisfied asgn clause then
      some (asgn, changed)  -- already satisfied, skip
    else
      let uncom := uncommittedLiterals asgn clause
      match uncom with
      | [] => none  -- contradiction: all literals falsified, clause unsatisfied
      | [lit] =>    -- unit clause: force this literal
        let newAsgn := Function.update asgn lit.particle_idx (some lit.polarity)
        some (newAsgn, true)
      | _ => some (asgn, changed))  -- multiple free literals, skip for now

/-- Full unit propagation: repeat until stable. Uses `fuel` to guarantee
termination -- at most `k` variables can be committed. -/
def unitPropagate {k : ℕ} (cnf : SyntacticCNF k) (asgn : Assignment k)
    (fuel : ℕ := k) : Option (Assignment k) :=
  match fuel with
  | 0 => some asgn
  | fuel + 1 =>
    match propagateOnce cnf asgn with
    | none => none  -- contradiction found
    | some (asgn', true) => unitPropagate cnf asgn' fuel  -- changed, iterate
    | some (asgn', false) => some asgn'  -- stable, done

/-- Get the list of free (uncommitted) variable indices. -/
def freeVariables {k : ℕ} (asgn : Assignment k) : List (Fin k) :=
  (List.range k).filterMap (fun i =>
    if h : i < k then
      let idx : Fin k := ⟨i, h⟩
      if asgn idx == none then some idx else none
    else none)

/-- Score a polarity: how many alive (unsatisfied) clauses does committing
variable `var` to `pol` directly satisfy? -/
def polarityScore {k : ℕ} (cnf : SyntacticCNF k) (asgn : Assignment k)
    (var : Fin k) (pol : Bool) : ℕ :=
  cnf.countP (fun clause =>
    !clauseSatisfied asgn clause &&
    clause.any (fun lit => decide (lit.particle_idx = var) && (lit.polarity == pol)))

/-- Choose the polarity that satisfies more alive clauses.
Break ties by choosing `true`. -/
def bestPolarity {k : ℕ} (cnf : SyntacticCNF k) (asgn : Assignment k)
    (var : Fin k) : Bool :=
  polarityScore cnf asgn var true ≥ polarityScore cnf asgn var false

/-- Knock-out completion with propagation after each commitment.
For each free variable, score both polarities, commit the higher-scoring
one, and propagate. If the preferred polarity leads to contradiction,
try the other. Both fail = UNSAT. -/
def knockOutComplete {k : ℕ} (cnf : SyntacticCNF k) (asgn : Assignment k) :
    Option (Assignment k) :=
  (freeVariables asgn).foldlM (init := asgn) (fun asgn var =>
    if asgn var != none then some asgn  -- already committed by prior propagation
    else
      let preferred := bestPolarity cnf asgn var
      -- Try preferred polarity first
      let tryPreferred := Function.update asgn var (some preferred)
      match unitPropagate cnf tryPreferred with
      | some asgn' => some asgn'
      | none =>
        -- Try other polarity
        let tryOther := Function.update asgn var (some (!preferred))
        match unitPropagate cnf tryOther with
        | some asgn' => some asgn'
        | none => none)  -- both fail: UNSAT

/-- Convert a (possibly partial) assignment to a `Vector Bool k`.
Free variables default to `true`. -/
def assignmentToVector {k : ℕ} (asgn : Assignment k) : Vector Bool k :=
  Vector.ofFn (fun i => match asgn i with | some b => b | none => true)

/-!
## Section 6: The NP Verifier (unit propagation + knock-out completion)

The verifier finds a satisfying assignment via unit propagation and
knock-out completion, then verifies it against the CNF using `evalCNF`.
The verification trace records one signed atom per clause -- the
literal that satisfies that clause under the found assignment.
-/

/-- The NP verifier with unit propagation + knock-out completion.
Takes only a CNF. Produces the verification trace (signed atoms)
or `none` (UNSAT).

Phase 1: Unit propagation commits forced variables.
Phase 2: Knock-out completion decides remaining free variables
         (score-based polarity choice with fallback).
Phase 3: Verify the assignment and record the trace. -/
def npVerifier {k : ℕ} (cnf : SyntacticCNF k) :
    Option (List EntropyInt) :=
  let initAsgn : Assignment k := fun _ => none
  match unitPropagate cnf initAsgn with
  | none => none
  | some asgn =>
    match knockOutComplete cnf asgn with
    | none => none
    | some finalAsgn =>
      let vec := assignmentToVector finalAsgn
      if evalCNF cnf vec then
        some (cnf.map (fun clause =>
          match clause.find? (fun lit => evalLiteral lit vec) with
          | some lit => literalToSignedAtom lit
          | none => (EntropyNat.ofNat 0, true)))  -- fallback, unreachable when evalCNF is true
      else
        none

/-!
## Section 7: constructTableauAndDecide
-/

/-- The constructive NP verifier and solution builder.

Takes only a CNF. Runs `npVerifier` to find a satisfying assignment
via unit propagation + knock-out completion. If verification succeeds,
produces:
- The decision: `true` (the CNF is satisfiable)
- The witness: `ComputerTape` (concatenated signed atoms)

If the CNF is unsatisfiable, returns `none`. -/
def constructTableauAndDecide {k : ℕ} (cnf : SyntacticCNF k) :
    Option (Bool × ComputerTape) :=
  (npVerifier cnf).map (fun atoms =>
    let tape : ComputerTape :=
      List.flatten (atoms.map (fun (nat, _sign) => nat.val))
    (true, tape))

/-!
## Section 8: Derived Definitions
-/

/-- The verification complexity: sum of atom magnitudes in the
verification trace. -/
def verificationComplexity {k : ℕ} (cnf : SyntacticCNF k) :
    Option ℕ :=
  (npVerifier cnf).map (fun atoms =>
    (atoms.map (fun (nat, _sign) => EntropyNat.toNat nat)).sum)

/-- `constructTableauAndDecide` succeeds iff `npVerifier` succeeds. -/
theorem constructTableauAndDecide_iff {k : ℕ} (cnf : SyntacticCNF k) :
    (constructTableauAndDecide cnf).isSome = true ↔
    (npVerifier cnf).isSome = true := by
  simp [constructTableauAndDecide, Option.isSome_map]

/-- Backward-compatible wrapper: extract the `EntropyNat` path costs
from the verification trace. -/
def computeTableauDecidable {k : ℕ} (cnf : SyntacticCNF k) :
    Option (List EntropyNat) :=
  (npVerifier cnf).map (fun atoms =>
    atoms.map (fun (nat, _sign) => nat))


/-!
## Section 9: SatCompatible Invariant and Verifier Properties

We prove structural properties of the NP verifier, centered on the
*SatCompatible* invariant: a partial assignment is SatCompatible if there
exists a satisfying vector that agrees with all committed variables.

### Key results

* `propagateOnce_satCompatible` -- one pass of unit propagation preserves
  SatCompatible and always succeeds.
* `unitPropagate_satCompatible` -- iterated unit propagation preserves
  SatCompatible and always succeeds.
* `npVerifier_sound` -- if `npVerifier` returns `some`, the CNF is satisfiable.
* `unitPropagate_initial_succeeds` -- initial unit propagation succeeds on
  satisfiable CNFs.
* `assignmentToVector_satCompatible_satisfies` -- a total SatCompatible
  assignment converted to a vector satisfies the CNF.

### Note on completeness

The knock-out completion phase uses a score-based heuristic to choose
variable polarities. When the heuristic chooses a polarity that is NOT
SAT-extendable, unit propagation (which is incomplete for UNSAT detection
on general CNF) may fail to detect the inconsistency. In that case, the
foldlM invariant is lost and subsequent steps may fail on both polarities.
Full completeness (SAT implies npVerifier returns some) would require either
backtracking (DPLL-style) or a proof that unit propagation detects all
inconsistencies introduced by single-variable commitments. The theorems
below establish the invariant chain up to and including unitPropagate,
plus soundness of the full verifier.
-/

/-- An assignment is SatCompatible with a CNF if there exists a satisfying
vector that agrees with all committed variables. -/
def SatCompatible {k : ℕ} (cnf : SyntacticCNF k) (asgn : Assignment k) : Prop :=
  ∃ a : Vector Bool k, evalCNF cnf a = true ∧
    ∀ (i : Fin k) (b : Bool), asgn i = some b → a.get i = b

/-- The witness-level consistency predicate: `a` agrees with all committed
variables in `asgn`. -/
def Consistent {k : ℕ} (a : Vector Bool k) (asgn : Assignment k) : Prop :=
  ∀ (i : Fin k) (b : Bool), asgn i = some b → a.get i = b

/-- `evalLiteral lit a = true` iff `a.get lit.particle_idx = lit.polarity`. -/
lemma evalLiteral_true_iff {k : ℕ} (lit : Literal k) (a : Vector Bool k) :
    evalLiteral lit a = true ↔ a.get lit.particle_idx = lit.polarity := by
  cases hval : a.get lit.particle_idx <;>
    cases hpol : lit.polarity <;>
    simp [evalLiteral, hval, hpol]

/-- If the CNF is satisfied by `a` and a clause is in the CNF, the clause
is satisfied by `a`. -/
lemma evalClause_of_evalCNF_mem {k : ℕ} (cnf : SyntacticCNF k) (a : Vector Bool k)
    (clause : Clause k) (h_sat : evalCNF cnf a = true) (h_mem : clause ∈ cnf) :
    evalClause clause a = true := by
  rw [evalCNF, List.all_eq_true] at h_sat
  exact h_sat clause h_mem

/-- When a unit clause forces a literal, the resulting assignment
preserves consistency. -/
lemma update_preserves_consistent {k : ℕ}
    (a : Vector Bool k) (asgn : Assignment k)
    (h_con : Consistent a asgn)
    (lit : Literal k)
    (h_pol : a.get lit.particle_idx = lit.polarity) :
    Consistent a (Function.update asgn lit.particle_idx (some lit.polarity)) := by
  intro i b h_upd
  by_cases h_eq : i = lit.particle_idx
  · subst h_eq
    rw [Function.update_self] at h_upd
    cases h_upd; exact h_pol
  · rw [Function.update_of_ne h_eq] at h_upd
    exact h_con i b h_upd

/-- A clause cannot be both unsatisfied and have no uncommitted literals
when the assignment is consistent with a satisfying vector.
This is the load-bearing semantic fact. -/
lemma no_dead_clause {k : ℕ}
    (clause : Clause k) (a : Vector Bool k)
    (h_clause_sat : evalClause clause a = true)
    (asgn : Assignment k)
    (h_con : Consistent a asgn) :
    clauseSatisfied asgn clause = true ∨ uncommittedLiterals asgn clause ≠ [] := by
  rw [evalClause, List.any_eq_true] at h_clause_sat
  obtain ⟨lit, h_lit_mem, h_lit_eval⟩ := h_clause_sat
  rw [evalLiteral_true_iff] at h_lit_eval
  cases h_asgn : asgn lit.particle_idx with
  | none =>
    right
    intro h_empty
    have h_uncom : lit ∈ uncommittedLiterals asgn clause := by
      simp [uncommittedLiterals, List.mem_filter]
      exact ⟨h_lit_mem, by simp [h_asgn]⟩
    rw [h_empty] at h_uncom
    exact List.not_mem_nil h_uncom
  | some b =>
    left
    have h_b : a.get lit.particle_idx = b := h_con _ _ h_asgn
    have h_b_eq_pol : b = lit.polarity := by rw [← h_lit_eval, h_b]
    simp [clauseSatisfied, List.any_eq_true]
    exact ⟨lit, h_lit_mem, by simp [literalSatisfied, h_asgn, h_b_eq_pol]⟩

/-- In a unit clause (one uncommitted literal, clause not satisfied),
the forced literal's polarity must match the witness. -/
lemma unit_clause_forced_polarity {k : ℕ}
    (clause : Clause k) (a : Vector Bool k)
    (h_clause_sat : evalClause clause a = true)
    (asgn : Assignment k)
    (h_con : Consistent a asgn)
    (h_not_sat : clauseSatisfied asgn clause = false)
    (lit : Literal k)
    (h_unit : uncommittedLiterals asgn clause = [lit]) :
    a.get lit.particle_idx = lit.polarity := by
  have h_lit_uncom : lit ∈ uncommittedLiterals asgn clause := by
    rw [h_unit]; exact List.mem_cons_self
  have h_lit_mem : lit ∈ clause := by
    simp [uncommittedLiterals, List.mem_filter] at h_lit_uncom
    exact h_lit_uncom.1
  rw [evalClause, List.any_eq_true] at h_clause_sat
  obtain ⟨lit', h_lit'_mem, h_lit'_eval⟩ := h_clause_sat
  rw [evalLiteral_true_iff] at h_lit'_eval
  suffices lit' = lit by subst this; exact h_lit'_eval
  by_contra h_neq
  have h_lit'_not_uncom : lit' ∉ uncommittedLiterals asgn clause := by
    rw [h_unit]; simp [h_neq]
  -- lit' is committed (not in uncommittedLiterals but in clause)
  simp [uncommittedLiterals, List.mem_filter] at h_lit'_not_uncom
  have h_lit'_committed : asgn lit'.particle_idx ≠ none := h_lit'_not_uncom h_lit'_mem
  obtain ⟨b, h_b⟩ := Option.ne_none_iff_exists'.mp h_lit'_committed
  have h_b_val : a.get lit'.particle_idx = b := h_con _ _ h_b
  have h_b_eq_pol : b = lit'.polarity := by rw [← h_lit'_eval, h_b_val]
  have h_lit'_sat : literalSatisfied asgn lit' = true := by
    simp [literalSatisfied, h_b, h_b_eq_pol]
  have : clauseSatisfied asgn clause = true := by
    simp [clauseSatisfied, List.any_eq_true]
    exact ⟨lit', h_lit'_mem, h_lit'_sat⟩
  rw [this] at h_not_sat
  exact absurd h_not_sat (by decide)

/-!
### foldlM invariant for propagateOnce

The step function processes a single clause: skip if satisfied, fail if dead,
force if unit, pass if multi-free. We prove it preserves consistency, then
lift to the full foldlM.
-/

/-- The step function for propagateOnce's foldlM. -/
private def propStep {k : ℕ} (acc : Assignment k × Bool) (clause : Clause k) :
    Option (Assignment k × Bool) :=
  let (asgn, changed) := acc
  if clauseSatisfied asgn clause then some (asgn, changed)
  else match uncommittedLiterals asgn clause with
    | [] => none
    | [lit] => some (Function.update asgn lit.particle_idx (some lit.polarity), true)
    | _ => some (asgn, changed)

/-- propagateOnce equals foldlM with propStep. -/
private lemma propagateOnce_eq_foldlM {k : ℕ}
    (cnf : SyntacticCNF k) (asgn : Assignment k) :
    propagateOnce cnf asgn =
      cnf.foldlM (init := (asgn, false)) propStep := by
  unfold propagateOnce propStep
  rfl

/-- Processing a single clause preserves consistency. -/
private lemma propStep_preserves_consistent {k : ℕ}
    (clause : Clause k) (a : Vector Bool k)
    (h_clause_sat : evalClause clause a = true)
    (asgn : Assignment k) (changed : Bool)
    (h_con : Consistent a asgn) :
    ∃ result, propStep (asgn, changed) clause = some result ∧
      Consistent a result.1 := by
  -- Reduce the let-pattern match on the pair
  show ∃ result, (if clauseSatisfied asgn clause then some (asgn, changed) else
      match uncommittedLiterals asgn clause with
      | [] => none
      | [lit] => some (Function.update asgn lit.particle_idx (some lit.polarity), true)
      | _ => some (asgn, changed)) = some result ∧ Consistent a result.1
  by_cases h_cls : clauseSatisfied asgn clause = true
  · exact ⟨(asgn, changed), by simp [h_cls], h_con⟩
  · have h_cls_false : clauseSatisfied asgn clause = false :=
      Bool.eq_false_iff.mpr h_cls
    simp only [h_cls_false]
    have h_or := no_dead_clause clause a h_clause_sat asgn h_con
    have h_uncom_ne : uncommittedLiterals asgn clause ≠ [] := by
      cases h_or with
      | inl h => rw [h] at h_cls_false; exact absurd h_cls_false (by decide)
      | inr h => exact h
    match h_uncom : uncommittedLiterals asgn clause with
    | [] => exact absurd h_uncom h_uncom_ne
    | [lit] =>
      exact ⟨_, rfl,
        update_preserves_consistent a asgn h_con lit
          (unit_clause_forced_polarity clause a h_clause_sat asgn h_con h_cls_false lit h_uncom)⟩
    | _ :: _ :: _ =>
      exact ⟨_, rfl, h_con⟩

/-- foldlM over a clause list preserves consistency when every clause
in the list is satisfied by the witness `a`. -/
private lemma foldlM_preserves_consistent {k : ℕ}
    (clauses : List (Clause k)) (a : Vector Bool k)
    (h_all_sat : ∀ c ∈ clauses, evalClause c a = true)
    (asgn : Assignment k) (changed : Bool)
    (h_con : Consistent a asgn) :
    ∃ result,
      clauses.foldlM (init := (asgn, changed)) propStep = some result ∧
      Consistent a result.1 := by
  induction clauses generalizing asgn changed with
  | nil => exact ⟨(asgn, changed), rfl, h_con⟩
  | cons clause rest ih =>
    simp only [List.foldlM_cons]
    have h_clause_sat := h_all_sat clause List.mem_cons_self
    have h_rest_sat : ∀ c ∈ rest, evalClause c a = true :=
      fun c hc => h_all_sat c (List.mem_cons_of_mem _ hc)
    obtain ⟨mid, h_mid_eq, h_mid_con⟩ :=
      propStep_preserves_consistent clause a h_clause_sat asgn changed h_con
    rw [h_mid_eq]
    exact ih h_rest_sat mid.1 mid.2 h_mid_con

/-- propagateOnce preserves SatCompatible and always returns some. -/
theorem propagateOnce_satCompatible {k : ℕ}
    (cnf : SyntacticCNF k) (asgn : Assignment k)
    (h_compat : SatCompatible cnf asgn) :
    ∃ result, propagateOnce cnf asgn = some result ∧
      SatCompatible cnf result.1 := by
  obtain ⟨a, h_sat, h_con⟩ := h_compat
  rw [propagateOnce_eq_foldlM]
  have h_all_sat : ∀ c ∈ cnf, evalClause c a = true :=
    fun c hc => evalClause_of_evalCNF_mem cnf a c h_sat hc
  obtain ⟨result, h_eq, h_con'⟩ :=
    foldlM_preserves_consistent cnf a h_all_sat asgn false h_con
  exact ⟨result, h_eq, ⟨a, h_sat, h_con'⟩⟩

/-- unitPropagate preserves SatCompatible and always returns some. -/
theorem unitPropagate_satCompatible {k : ℕ}
    (cnf : SyntacticCNF k) (asgn : Assignment k) (fuel : ℕ)
    (h_compat : SatCompatible cnf asgn) :
    ∃ result, unitPropagate cnf asgn fuel = some result ∧
      SatCompatible cnf result := by
  induction fuel generalizing asgn with
  | zero => exact ⟨asgn, rfl, h_compat⟩
  | succ n ih =>
    simp only [unitPropagate]
    obtain ⟨⟨asgn', changed⟩, h_prop_eq, h_prop_compat⟩ :=
      propagateOnce_satCompatible cnf asgn h_compat
    rw [h_prop_eq]
    cases changed with
    | true => exact ih asgn' h_prop_compat
    | false => exact ⟨asgn', rfl, h_prop_compat⟩

/-!
### Soundness and initial conditions
-/

/-- The initial all-none assignment is SatCompatible with any satisfiable CNF. -/
lemma initAsgn_satCompatible {k : ℕ} (cnf : SyntacticCNF k)
    (h_sat : ∃ a : Vector Bool k, evalCNF cnf a = true) :
    SatCompatible cnf (fun (_ : Fin k) => none) := by
  obtain ⟨a, ha⟩ := h_sat
  exact ⟨a, ha, fun _ _ h => by simp at h⟩

/-- Initial unit propagation succeeds on satisfiable CNFs. -/
theorem unitPropagate_initial_succeeds {k : ℕ} (cnf : SyntacticCNF k)
    (h_sat : ∃ a : Vector Bool k, evalCNF cnf a = true) :
    ∃ result, unitPropagate cnf (fun _ => none) k = some result ∧
      SatCompatible cnf result :=
  unitPropagate_satCompatible cnf (fun _ => none) k
    (initAsgn_satCompatible cnf h_sat)

/-- npVerifier is sound: if it returns some, the CNF is satisfiable. -/
theorem npVerifier_sound {k : ℕ} (cnf : SyntacticCNF k)
    (h : (npVerifier cnf).isSome = true) :
    ∃ a : Vector Bool k, evalCNF cnf a = true := by
  unfold npVerifier at h
  -- Extract the evalCNF check from the nested match/let structure.
  -- unitPropagate result
  match h_up : unitPropagate cnf (fun _ => none) k with
  | none => simp [h_up] at h
  | some asgn =>
    simp [h_up] at h
    -- knockOutComplete result
    match h_ko : knockOutComplete cnf asgn with
    | none => simp [h_ko] at h
    | some finalAsgn =>
      simp [h_ko] at h
      -- evalCNF check
      by_cases h_eval : evalCNF cnf (assignmentToVector finalAsgn) = true
      · exact ⟨assignmentToVector finalAsgn, h_eval⟩
      · simp [h_eval] at h

/-- A total assignment that is SatCompatible produces a satisfying vector
via `assignmentToVector`. An assignment is total if every variable is
committed. -/
theorem assignmentToVector_satCompatible_satisfies {k : ℕ}
    (cnf : SyntacticCNF k) (asgn : Assignment k)
    (h_compat : SatCompatible cnf asgn)
    (h_total : ∀ i : Fin k, asgn i ≠ none) :
    evalCNF cnf (assignmentToVector asgn) = true := by
  obtain ⟨a, h_sat, h_con⟩ := h_compat
  suffices h_eq : assignmentToVector asgn = a by rw [h_eq]; exact h_sat
  apply Vector.ext
  intro i hi
  obtain ⟨b, h_b⟩ := Option.ne_none_iff_exists'.mp (h_total ⟨i, hi⟩)
  simp only [assignmentToVector, Vector.getElem_ofFn, h_b]
  have := h_con ⟨i, hi⟩ b h_b
  simp [Vector.get] at this
  exact this.symm

/-- Committing a free variable to the witness's polarity preserves
SatCompatible. -/
lemma commit_witness_polarity_satCompatible {k : ℕ}
    (cnf : SyntacticCNF k) (asgn : Assignment k)
    (a : Vector Bool k) (h_sat : evalCNF cnf a = true)
    (h_con : Consistent a asgn)
    (var : Fin k) :
    SatCompatible cnf (Function.update asgn var (some (a.get var))) := by
  refine ⟨a, h_sat, fun i b h_upd => ?_⟩
  by_cases h_eq : i = var
  · subst h_eq
    rw [Function.update_self] at h_upd
    cases h_upd; rfl
  · rw [Function.update_of_ne h_eq] at h_upd
    exact h_con i b h_upd

/-- For a SatCompatible assignment and any variable, committing the
witness's polarity and propagating succeeds and preserves SatCompatible.
This shows that the fallback-to-both-polarities always has at least one
viable path per variable. -/
theorem witness_polarity_propagation_succeeds {k : ℕ}
    (cnf : SyntacticCNF k) (asgn : Assignment k)
    (h_compat : SatCompatible cnf asgn) (var : Fin k) :
    ∃ a : Vector Bool k, evalCNF cnf a = true ∧
      ∃ result,
        unitPropagate cnf (Function.update asgn var (some (a.get var))) k = some result ∧
        SatCompatible cnf result := by
  obtain ⟨a, h_sat, h_con⟩ := h_compat
  exact ⟨a, h_sat, unitPropagate_satCompatible cnf _ k
    (commit_witness_polarity_satCompatible cnf asgn a h_sat h_con var)⟩

end InformationTheory
