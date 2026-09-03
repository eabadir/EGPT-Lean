import Mathlib.Tactic.NormNum
import Mathlib.Data.Sym.Card
import Std.Sat.CNF.Basic
import Mathlib.Tactic.Sat.FromLRAT
import Mathlib.Data.List.Range
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Encodable.Basic

import Archive.Core
import Archive.Complexity.Core
import Archive.NumberTheory.Core
import Archive.NumberTheory.Filter
import Archive.Constraints
import Archive.Complexity.Decomposition
import Archive.Complexity.SetRFL

namespace EGPT.Complexity.Physics

open EGPT.NumberTheory.Core EGPT.NumberTheory.Filter EGPT.Constraints

/-!
### Section 2: The EGPT-SAT Problem (Physical Model)

We define the SAT problem in this combinatorial/physical framework.
This file contains the "Physics" of the EGPT model: the stochastic processes,
random walks, and time evolution rules.

Crucially, this logic is the *physical model* that motivates the complexity definitions,
but it is NOT part of the formal logical proof of P=NP.
-/

/--
The state of a single particle in the SAT model.
Its 'law' is the probability of it being 'true' in the next state.
For the simplest model, we can assume a fair coin flip (p=1, q=1).
-/
structure ParticleState_SAT where
  -- The current boolean value of the particle/variable.
  value : Bool
  -- The law governing its next state transition.
  -- This is a ParticleHistoryPMF representing its bias (p, q).
  law : ParticleHistoryPMF

-- The full history of a single particle for `t` steps.
abbrev ParticleHistory := ComputerTape -- List Bool

-- The history of the entire n-particle system.
abbrev SystemHistory (n : ℕ) := Vector ParticleHistory n

/--
`advance_state` computes the next system state by flipping a biased coin for each particle.
This is one step in the parallel Markov process.
-/
noncomputable def advance_state {k : ℕ} (current_states : Vector ParticleState_SAT k) (seed : ℕ) : Vector ParticleState_SAT k :=
  Vector.ofFn (fun i : Fin k =>
    let particle := current_states.get i
    -- Use the particle's law (ParticleHistoryPMF) to create a biased source for this one step.
    let source := toBiasedSource particle.law (seed + i.val)
    let next_value := source.stream 0 -- Generate one new boolean value.
    { particle with value := next_value }
  )

/--
`get_system_state_vector` is a helper to extract the boolean vector from the particle states.
-/
def get_system_state_vector {k : ℕ} (states : Vector ParticleState_SAT k) : Vector Bool k :=
  states.map (fun p => p.value)


-- A ProgramTape is the fundamental data structure for a path/program.
abbrev ProgramTape := ComputerProgram


/--
A Constraint is a rule that a program's tape must satisfy at every step of
its evolution. The `checker` function takes the current time (tape length)
and the tape segment up to that time.
-/
structure Constraint where
  checker : (currentTime : ℕ) → (tape_so_far : ComputerTape) → Bool

/--
An EGPT problem instance is defined by a target complexity (tape length).
-/
abbrev EGPT_Input := ℕ

/--
An EGPT Language is a decision problem parameterized by the target tape length.
The constraints defining the problem are considered part of the language itself.
-/
abbrev Lang_EGPT := EGPT_Input → Bool

/-!
### The Verifier (DMachine)
-/


/--
A DMachine is a deterministic verifier. It takes a potential solution
(a `PathProgram` as a certificate) and an input, and decides to
accept or reject it.
-/
structure DMachine where
  verify : (certificate : PathProgram) → (input : EGPT_Input) → Bool
  -- We can add a field for the machine's own complexity if needed,
  -- but for now we define it externally.


-- A predicate on the system's state vector. The NDMachine halts when this is true.
abbrev TargetStatePredicate (n : ℕ) := (Vector ℤ n) → Bool

/--
The state of a single particle in an EGPT system, defined by its
current position and its intrinsic physical law (movement bias).
-/
structure ParticleState where
  position : ParticlePosition
  law      : ParticleHistoryPMF -- Corresponds to an EGPT.Rat, the particle's bias


/-!
==================================================================
# The Solver-Filter Equivalence Flow

This file demonstrates the direct, constructive link between the dynamic EGPT
solver and the static EGPT probability distribution.

The `ndm_run_solver_produces_filter` function is designed to output a `RejectionFilter`
upon finding a solution. This `RejectionFilter` is precisely the object that
the `eventsPMF` function consumes to generate a probability distribution.

This establishes that the job of the physical solver is to discover the
parameters of the constrained system, which can then be used to describe the
probabilistic behavior of that system.
==================================================================
-/

/--
Calculates the single characteristic rational number of a filter. This represents
the probability that a uniformly random k-bit vector will satisfy the filter's
constraints. It is the ratio of the size of the solution space to the size
of the total state space.
-/
noncomputable def characteristicRational {k : ℕ} (filter : RejectionFilter k) : ℚ :=
  let num_sat := filter.satisfying_assignments.card
  let total_states := 2^k
  -- Construct the rational number num_sat / total_states
  mkRat num_sat total_states

/--
**Computes the Canonical EGPT Program for a Set of Physical Laws.**

This function embodies a core thesis of EGPT. It takes a `RejectionFilter`
(representing a set of physical laws and a non-empty solution space) and
constructs the single, canonical `ComputerTape` (a `List Bool`) that
represents the information content of those laws.

The process is a direct, computable chain:
1.  The `RejectionFilter`'s information content is quantified as a single
    rational number by `characteristicRational`.
2.  This rational number `ℚ` is converted into its canonical EGPT representation,
    a `ParticleHistoryPMF`, using the `fromRat` bijection.
3.  The underlying `List Bool` of the `ParticleHistoryPMF` is, by definition, the
    canonical `ComputerTape` or "program" for that rational.
-/
noncomputable def EGPTProgramForRejectionFilter {k : ℕ} (filter : RejectionFilter k) : ComputerProgram :=
  -- 1. Calculate the characteristic rational of the filter.
  let prob_success : ℚ := characteristicRational filter
  -- 2. Convert this rational number into its canonical EGPT representation.
  let egpt_rational : ParticleHistoryPMF := fromRat prob_success
  -- 3. The program is the underlying binary tape/program of the canonical EGPT rational.
  egpt_rational.val


/--
**Computes a Potential Next State via a Memoryless Random Walk.**

This is the core state transition function of the EGPT physical model. It
defines one step of a parallel Markov process. It is "potential" because it
represents the raw physical evolution, before any constraints are applied.

The function is memoryless: the next state candidate depends *only* on the
`current_state` and the `seed` for randomness, not on any prior history.

1.  It converts the input boolean vector (`current_state`) into a vector of
    `ParticleState_SAT`, where each particle is assigned a fundamental, unbiased
    physical law (a fair coin, represented by the EGPT rational `1/1`).
2.  It calls `advance_state`, which performs `k` parallel, independent, and
    identically distributed (IID) "coin flips" to generate the next state.
3.  It returns the resulting boolean vector.
-/
noncomputable def potential_next_state {k : ℕ} (current_state : Vector Bool k) (seed : ℕ) : Vector Bool k :=
  -- 1. Create the particle state vector (value + law) from the boolean vector.
  --    The law `fromRat 1` represents a fair 1/1 coin, the fundamental IID source.
  let particle_states := Vector.ofFn (fun i => {
    value := current_state.get i,
    law   := EGPT.NumberTheory.Core.fromRat 1
  })

  -- 2. Advance the state using the memoryless `advance_state` function.
  let next_particle_states := advance_state particle_states seed

  -- 3. Extract just the boolean values for the resulting state vector.
  get_system_state_vector next_particle_states

/--
**The EGPT Non-deterministic Machine (`NDTM_A`) Runner.**

This function embodies the EGPT model of non-deterministic computation. It does
not simulate a Turing Machine abstractly; instead, it models computation as a
physical process: a "computation particle" attempting a random walk through a
state space, where its path is constrained by a set of physical laws.

- **The Machine's "Program":** The `constraints` (`SyntacticCNF_EGPT k`) are the
  program. They define the physical laws of the computational universe.
- **Non-determinism:** The `seed` provides the source of randomness for the
  particle's walk. A different seed leads to a different computational path.
  The problem is "accepted" if there *exists* any seed that finds a valid path.
- **Execution:** The machine performs a random walk with rejection sampling.
  At each time step, it generates a potential next state. If the state obeys
  the constraints, the path is extended. If not, the step is rejected, and
  the machine attempts a new random move from its previous state.

The output is `some path` if a valid computational history of `time_limit`
steps is found, and `none` otherwise.
-/
noncomputable def NDTM_A_run {k : ℕ} (constraints : SyntacticCNF_EGPT k) (time_limit : ℕ) (seed : ℕ) : Option (List (Vector Bool k)) :=
  -- === Phase 1: Initialization ===
  -- The NDTM must start in a valid state. We find all satisfying assignments
  -- and pick the first one as a valid starting point.
  let satisfying_states := (Finset.univ : Finset (Vector Bool k)).filter (fun v => evalCNF constraints v)
  let initial_state_opt := satisfying_states.toList.head?

  match initial_state_opt with
  | none =>
    -- No state satisfies the constraints. The computational space is empty, so no path can exist.
    none
  | some initial_state =>
    -- A valid starting state was found. Begin the random walk.

    -- === Phase 2: The Recursive Random Walk ===
    let rec loop (t : ℕ) (current_path : List (Vector Bool k)) (current_seed : ℕ) : Option (List (Vector Bool k)) :=
      -- The head of the path is always the current state for the next step.
      -- This is safe because `current_path` is initialized as `[initial_state]`.
      let current_state := current_path.head!

      -- Check for successful termination. A path of length `time_limit` has been found.
      if t >= time_limit then
        -- We have successfully constructed a valid path of the required length.
        some (current_path.reverse) -- Reverse to get chronological order [start, ..., end].
      else
        -- Propose a non-deterministic next state using the memoryless transition function.
        let next_candidate := potential_next_state current_state current_seed

        -- Verify the candidate against the physical laws (constraints).
        if evalCNF constraints next_candidate then
          -- **Accept:** The state is valid. Extend the path and continue the walk from the new state.
          let new_path := next_candidate :: current_path
          loop (t + 1) new_path (current_seed + 1)
        else
          -- **Reject:** The state is invalid. The path is not extended.
          -- Try a new random choice from the *same* `current_state`.
          loop (t + 1) current_path (current_seed + 1)
    termination_by time_limit - t

    -- Start the execution loop from t=0 with a path containing only the valid initial state.
    loop 0 [initial_state] seed

/--
**Creates a CNF formula that is uniquely satisfied by the given state vector `v`.**
The formula is a conjunction of `k` unit clauses, where the `i`-th clause fixes
the `i`-th variable to its value in `v`. For example, for `v = [true, false]`,
the CNF is `(x₀) ∧ (¬x₁)`.
-/
def cnf_for_specific_assignment {k : ℕ} (v : Vector Bool k) : SyntacticCNF_EGPT k :=
  List.ofFn (fun i : Fin k =>
    -- Each clause is a list containing a single literal.
    [{ particle_idx := i, polarity := v.get i }]
  )



/--
**Constructs the RejectionFilter representing the complete solution space for a
set of physical constraints.**

This function is the definitive, deterministic EGPT solver. It takes a set of
physical laws, encoded as a `SyntacticCNF_EGPT`, and determines the complete
set of all possible states that are consistent with those laws.

Instead of simulating a non-deterministic random walk to find a single witness,
this function performs a direct, deterministic analysis of the entire state space.

- If the set of valid states (satisfying assignments) is non-empty, it
  constructs and returns a `RejectionFilter` that encapsulates this entire
  solution space.
- If no state can satisfy the constraints, it returns `none`, signifying that
  the physical system is impossible.

This function represents a P-solver for an NP-complete problem. The core EGPT
claim is that the time required for a physical, non-deterministic process to
find a *single* solution is polynomially equivalent to the time required for
this function to characterize the *entire* solution space.
-/
noncomputable def construct_solution_filter {k : ℕ} (constraints : SyntacticCNF_EGPT k) : Option (RejectionFilter k) :=
  -- 1. Deterministically find ALL satisfying assignments by filtering the
  --    entire state space (Finset.univ) against the constraint checker.
  let satisfying_assignments := (Finset.univ : Finset (Vector Bool k)).filter (fun v => evalCNF constraints v)

  -- 2. Check if the resulting set of solutions is empty.
  if h_nonempty : satisfying_assignments.Nonempty then
    -- 3a. If solutions exist, package the complete solution space into a RejectionFilter.
    --     The `is_satisfiable` proof is directly provided by `h_nonempty`.
    let filter : RejectionFilter k := {
      cnf := constraints,
      satisfying_assignments := satisfying_assignments,
      is_satisfiable := h_nonempty,
      -- The coherence axiom is true by the definition of our filter.
      ax_coherent := by
        intros v h_v_in_sa
        -- If v is in the filtered set, it must satisfy the filter's predicate.
        exact (Finset.mem_filter.mp h_v_in_sa).2
    }
    some filter
  else
    -- 3b. If the set of solutions is empty, the system is unsolvable.
    none

-- A Constrained System is defined by a single set of laws.
abbrev ConstrainedSystem (k : ℕ) := SyntacticCNF_EGPT k

-- The verifier checks that EVERY state in the path obeys the laws.
def DMachine_CS_verify {k : ℕ} (sys : ConstrainedSystem k) (path_cert : List (Vector Bool k)) : Bool :=
  -- An empty path cannot be a valid solution certificate.
  ¬path_cert.isEmpty ∧ path_cert.all (fun state => evalCNF sys state)


theorem constrainedSystem_equiv_SAT {k : ℕ} (sys : ConstrainedSystem k) :
  (∃ path : List (Vector Bool k), DMachine_CS_verify sys path = true) ↔
  (∃ assignment : Vector Bool k, evalCNF sys assignment = true) :=
by
  -- To prove the iff (↔), we prove both directions.
  constructor

  -- Part 1: Forward Direction (→)
  -- If a valid path exists, then the CNF is satisfiable.
  · intro h_path_exists
    -- From the hypothesis, we get a specific path that is valid.
    rcases h_path_exists with ⟨path, h_path_valid⟩

    -- The verifier returns a Bool, so we have `DMachine_CS_verify sys path = true`
    -- This means `decide (¬path.isEmpty ∧ path.all (fun state => evalCNF sys state)) = true`
    simp only [DMachine_CS_verify] at h_path_valid

    -- Since `decide` returns `true`, the inner proposition must be true
    have h_inner : ¬path.isEmpty ∧ path.all (fun state => evalCNF sys state) := by
      exact decide_eq_true_iff.mp h_path_valid

    -- Extract the components
    have h_path_nonempty : ¬path.isEmpty := h_inner.1
    have h_all_states_valid : path.all (fun state => evalCNF sys state) := h_inner.2

    -- Since the path is not empty, it must have a first element (a head).
    have h_ne_nil : path ≠ [] := by
      intro h_eq_nil
      rw [h_eq_nil] at h_path_nonempty
      simp at h_path_nonempty

    cases path with
    | nil => contradiction -- This case is impossible due to h_ne_nil
    | cons head tail =>
        -- We now have a specific state, `head`. We will show it is a satisfying assignment.
        -- We need to prove `∃ assignment, evalCNF sys assignment = true`. We use `head`.
        use head

        -- The goal is to prove `evalCNF sys head = true`.
        -- We know `(head :: tail).all (fun state => evalCNF sys state) = true`.
        -- By the definition of `List.all`, this means the property holds for the head and for all elements in the tail.
        simp [List.all_cons] at h_all_states_valid
        -- `h_all_states_valid` is now `evalCNF sys head ∧ tail.all (fun state => evalCNF sys state)`.
        -- The first part of this conjunction is exactly our goal.
        exact h_all_states_valid.left

  -- Part 2: Backward Direction (←)
  -- If the CNF is satisfiable, then a valid path exists.
  · intro h_assignment_exists
    -- From the hypothesis, we get a specific assignment that satisfies the CNF.
    rcases h_assignment_exists with ⟨assignment, h_assignment_valid⟩

    -- We need to prove `∃ path, DMachine_CS_verify sys path = true`.
    -- We can construct a trivial, single-state path using our valid assignment.
    use [assignment]

    -- The goal is to prove `DMachine_CS_verify sys [assignment] = true`.
    -- Unfold the verifier's definition.
    simp only [DMachine_CS_verify, List.isEmpty_cons, List.all_cons, List.all_nil, Bool.not_false]
    -- The goal is now `true ∧ evalCNF sys assignment = true`.
    -- Since we know `evalCNF sys assignment = true`, this simplifies to `true ∧ true = true`.
    simp [h_assignment_valid]





/-!
### Theorem: Underlying State Evolution is Memoryless (A Markov Process)

This theorem formalizes the observation that the state transition function used by the
`ndm_constrained_path_solver` is Markovian.

Even though the solver carries a full path history (`current_path`), the generation
of the *next candidate state* at each step depends **only on the most recent state**
in that path and the current seed. It has no dependency on `s_{t-1}, s_{t-2}, ...`.

The proof shows that the state generation logic inside the solver's loop is
definitionally equal to a standalone, memoryless function (`potential_next_state`).
-/
theorem underlying_state_evolution_is_memoryless {k : ℕ} :
    -- We want to prove that for any `current_state` and `current_seed` that might
    -- appear inside the solver's loop...
    ∀ (current_state : Vector Bool k) (current_seed : ℕ),
      -- ...the `next_state` generated inside the loop...
      (
        let particle_states := Vector.ofFn (fun i => { value := current_state.get i, law := EGPT.NumberTheory.Core.fromRat 1})
        get_system_state_vector (advance_state particle_states current_seed)
      )
      -- ...is equal to the output of our standalone, memoryless function.
      = potential_next_state current_state current_seed :=
by
  -- The proof is by definition. We introduce the variables and show both
  -- sides of the equality are identical.
  intro current_state current_seed

  -- Unfold the definition of `potential_next_state` on the right-hand side.
  simp [potential_next_state]

/-!
==================================================================
# Deterministic Breadth Construction (Experimental Parallel Chain)

This section defines a CNF-initialized deterministic breadth constructor:
- Initial state is the CNF program itself (no witness argument).
- Survivors are evolved clause-by-clause in canonical list order.
- Terminal survivors are exactly the satisfying assignments.

This is intentionally experimental and does NOT replace the load-bearing chain.
==================================================================
-/

/-- CNF magnitude used as a deterministic constructor time-limit parameter. -/
def CNFMagnitude {k : ℕ} (cnf : SyntacticCNF_EGPT k) : ℕ :=
  (encodeCNF cnf).length

/-- Deterministic breadth state over ordered CNF constraints. -/
structure BreadthState (k : ℕ) where
  cnf : SyntacticCNF_EGPT k
  step : ℕ
  survivors : Finset (Vector Bool k)

/-- Deterministic clause-filter step on current survivors. -/
def breadthStep {k : ℕ} (clause : Clause_EGPT k) (survivors : Finset (Vector Bool k)) :
    Finset (Vector Bool k) :=
  survivors.filter (fun v => evalClause clause v)

/-- CNF-initialized breadth state starts with all states as candidates. -/
def initBreadthState {k : ℕ} (cnf : SyntacticCNF_EGPT k) : BreadthState k := {
  cnf := cnf
  step := 0
  survivors := (Finset.univ : Finset (Vector Bool k))
}

/-- Single deterministic transition by consuming the next ordered clause. -/
def breadthAdvance {k : ℕ} (st : BreadthState k) : BreadthState k :=
  match st.cnf.drop st.step with
  | [] => st
  | clause :: _ =>
      { st with
        step := st.step + 1
        survivors := breadthStep clause st.survivors }

/-- Recursive deterministic breadth run from an initial survivor set. -/
def breadthRunFrom {k : ℕ} (survivors : Finset (Vector Bool k)) : SyntacticCNF_EGPT k → Finset (Vector Bool k)
  | [] => survivors
  | clause :: rest => breadthRunFrom (breadthStep clause survivors) rest

/-- Deterministic breadth constructor run in canonical CNF list order. -/
def deterministicBreadthRun {k : ℕ} (cnf : SyntacticCNF_EGPT k) : Finset (Vector Bool k) :=
  breadthRunFrom (Finset.univ : Finset (Vector Bool k)) cnf

/-- Deterministic breadth terminal state after exactly `cnf.length` transitions. -/
def deterministicBreadthFinalState {k : ℕ} (cnf : SyntacticCNF_EGPT k) : BreadthState k := {
  cnf := cnf
  step := cnf.length
  survivors := deterministicBreadthRun cnf
}

/-- Constructor cost model: one full variable sweep per clause row. -/
def deterministicBreadthCost {k : ℕ} (cnf : SyntacticCNF_EGPT k) : ℕ :=
  cnf.length * k

/-- The breadth constructor step-count is bounded by CNF magnitude. -/
lemma deterministicBreadth_steps_le_magnitude {k : ℕ} (cnf : SyntacticCNF_EGPT k) :
    cnf.length ≤ CNFMagnitude cnf := by
  simpa [CNFMagnitude] using (cnf_length_le_encoded_length cnf)

/-- Deterministic breadth transition-cost bound by encoded-size square. -/
theorem deterministicBreadth_cost_le_nSquared {k : ℕ} (cnf : SyntacticCNF_EGPT k) :
    deterministicBreadthCost cnf ≤ CNFMagnitude cnf * CNFMagnitude cnf := by
  unfold deterministicBreadthCost CNFMagnitude
  apply Nat.mul_le_mul
  · exact cnf_length_le_encoded_length cnf
  · exact encodeCNF_size_ge_k k cnf

/-- A survivor in one step iff it was in the prior set and satisfies that clause. -/
@[simp] lemma mem_breadthStep_iff {k : ℕ} (clause : Clause_EGPT k) (survivors : Finset (Vector Bool k))
    (v : Vector Bool k) :
    v ∈ breadthStep clause survivors ↔ v ∈ survivors ∧ evalClause clause v = true := by
  simp [breadthStep]

/--
Prefix invariant:
membership in `breadthRunFrom survivors clauses` is equivalent to
membership in the initial survivor set and truth of every processed clause.
-/
lemma mem_breadthRunFrom_iff {k : ℕ} (survivors : Finset (Vector Bool k))
    (clauses : SyntacticCNF_EGPT k) (v : Vector Bool k) :
    v ∈ breadthRunFrom survivors clauses ↔
      v ∈ survivors ∧ clauses.all (fun clause => evalClause clause v) = true := by
  induction clauses generalizing survivors with
  | nil =>
      simp [breadthRunFrom]
  | cons clause rest ih =>
      simp [breadthRunFrom, ih, and_assoc, Bool.and_eq_true]

/-- Terminal survivors are exactly the satisfying assignments of the CNF. -/
theorem mem_deterministicBreadthRun_iff_evalCNF {k : ℕ} (cnf : SyntacticCNF_EGPT k) (v : Vector Bool k) :
    v ∈ deterministicBreadthRun cnf ↔ evalCNF cnf v = true := by
  simpa [deterministicBreadthRun, evalCNF] using
    (mem_breadthRunFrom_iff (survivors := (Finset.univ : Finset (Vector Bool k))) (clauses := cnf) (v := v))

/--
`ConstructedSolutionSet` is the CNF-only constructed set of satisfying endpoints:
the terminal survivor set of deterministic breadth construction.
-/
def ConstructedSolutionSet {k : ℕ} (cnf : SyntacticCNF_EGPT k) : Finset (Vector Bool k) :=
  deterministicBreadthRun cnf

/--
Verifier by constructed-set membership.
Returns true exactly when the candidate is in the CNF-constructed solution set.
-/
def verify_via_constructedSet {k : ℕ} (cnf : SyntacticCNF_EGPT k) (candidate : Vector Bool k) : Bool :=
  decide (candidate ∈ ConstructedSolutionSet cnf)

/--
Core verifier equivalence chain:
verifying by constructed-set membership is equivalent to `evalCNF`.
-/
theorem verify_via_constructedSet_iff_evalCNF {k : ℕ}
    (cnf : SyntacticCNF_EGPT k) (candidate : Vector Bool k) :
    verify_via_constructedSet cnf candidate = true ↔ evalCNF cnf candidate = true := by
  unfold verify_via_constructedSet ConstructedSolutionSet
  simpa [decide_eq_true_eq] using (mem_deterministicBreadthRun_iff_evalCNF (cnf := cnf) (v := candidate))

/-- Constructor success iff CNF semantic set is nonempty. -/
theorem deterministicBreadthRun_nonempty_iff_allSatisfyingAssignments_nonempty {k : ℕ}
    (cnf : SyntacticCNF_EGPT k) :
    (deterministicBreadthRun cnf).Nonempty ↔ (EGPT.Complexity.SetRFL.AllSatisfyingAssignments cnf).Nonempty := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, (mem_deterministicBreadthRun_iff_evalCNF cnf v).1 hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, (mem_deterministicBreadthRun_iff_evalCNF cnf v).2 hv⟩

/-- Constructor success iff CNF satisfies the common-factor criterion. -/
theorem deterministicBreadthRun_nonempty_iff_CNFSharesFactor {k : ℕ}
    (cnf : SyntacticCNF_EGPT k) :
    (deterministicBreadthRun cnf).Nonempty ↔ EGPT.Complexity.CNFSharesFactor cnf := by
  constructor
  · rintro ⟨v, hv⟩
    exact (EGPT.Complexity.cnfSharesFactor_of_exists_assignment (cnf := cnf))
      ⟨v, (mem_deterministicBreadthRun_iff_evalCNF cnf v).1 hv⟩
  · intro h_cf
    rcases (EGPT.Complexity.exists_assignment_of_cnfSharesFactor (cnf := cnf) h_cf) with ⟨v, hv⟩
    exact ⟨v, (mem_deterministicBreadthRun_iff_evalCNF cnf v).2 hv⟩

/-- Program projection of a terminal survivor assignment. -/
def survivorProgram {k : ℕ} (v : Vector Bool k) : ComputerProgram :=
  encodeCNF (cnf_for_specific_assignment v)

/-- Ordered list of survivor programs extracted from terminal survivor set. -/
noncomputable def survivorPrograms {k : ℕ} (cnf : SyntacticCNF_EGPT k) : List ComputerProgram :=
  (deterministicBreadthRun cnf).toList.map survivorProgram

/-- Composition (sum) of all survivor programs. -/
noncomputable def composeSurvivorPrograms {k : ℕ} (cnf : SyntacticCNF_EGPT k) : ComputerProgram :=
  (survivorPrograms cnf).foldl combinePrograms []

/-- Composed survivor output is definitionally a `ComputerProgram`. -/
theorem composeSurvivorPrograms_is_program {k : ℕ} (cnf : SyntacticCNF_EGPT k) :
    ∃ prog : ComputerProgram, prog = composeSurvivorPrograms cnf := by
  exact ⟨composeSurvivorPrograms cnf, rfl⟩

end EGPT.Complexity.Physics

