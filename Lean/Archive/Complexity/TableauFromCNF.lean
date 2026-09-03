import Archive.Core
import Archive.Complexity.Core
import Archive.Entropy.Common
import Archive.Physics.PhysicsDist
import Archive.NumberTheory.Core -- For ParticlePath, fromNat, toNat

open EGPT EGPT.Complexity EGPT.NumberTheory.Core EGPT.Constraints

namespace EGPT.Complexity

/-!
# The Physical Walk Construction

In EGPT, natural numbers are physical paths on a 2D grid (`ParticlePath ≃ ℕ`,
proved by `equivParticlePathToNat`). A CNF formula is a list of clauses, each
clause a list of literals, each literal an address (`Fin k`) on that grid.

The **Full Walk** is the process of visiting every clause and recording which
address (literal) is reached. This walk produces a `List ParticlePath` — the
`witness_paths` — whose total length (the `complexity`) is bounded by
`|cnf| × k ≤ n²`. This bound depends only on the dimensions of the CNF
(how many clauses, how many variables), not on the specific endpoint reached.

Since `List ParticlePath` is `List (List Bool)` which flattens to `List Bool`
which IS both `ComputerTape` and `ComputerProgram` (by definition in `Core.lean`), the walk itself
**constructs** the polynomial-time computation tape. The address is the map.
-/

/--
**The Satisfying Tableau (Certificate Structure).**

A `SatisfyingTableau` bundles:
1. `cnf`: The constraint formula (the "maze" of addresses).
2. `assignment`: A `Vector Bool k` — the endpoint on the grid.
3. `witness_paths`: A `List ParticlePath` — the recorded walk through the maze.
   For each clause, this records the `PathToConstraint` of the literal reached.
4. `h_valid`: A proof that the endpoint satisfies all constraints.

The `witness_paths` field is the physical record of the walk. Its sum
(`complexity`) measures the total path length — the information cost of the
certificate. This is bounded by the CNF's structure alone.
-/
structure SatisfyingTableau (k : ℕ) where
  cnf : SyntacticCNF_EGPT k
  assignment : Vector Bool k
  witness_paths : List ParticlePath
  h_valid : evalCNF cnf assignment = true

/--
**Measures the complexity of a Satisfying Tableau.**

The complexity is the sum of the `ParticlePath` lengths in the walk record.
Each path is bijectively a natural number (`toNat`), so this sum is a concrete
`ℕ` — the total information cost of the certificate.
-/
def SatisfyingTableau.complexity {k : ℕ} (tableau : SatisfyingTableau k) : ℕ :=
  (tableau.witness_paths.map toNat).sum

/--
**The Full Walk: Visits every clause and records the path to its satisfied literal.**

Given a CNF and an endpoint (a satisfying assignment), `walkCNFPaths` walks
every clause in the CNF. For each clause, it finds the first literal satisfied
by the endpoint and records the `PathToConstraint` — the physical distance to
that literal's variable index on the 2D grid.

The endpoint is the "output address" on the grid — analogous to the exit of a
maze. Knowing where the exit is does NOT tell you the path through the maze;
the walk must still visit every clause. The endpoint merely determines WHICH
literal is recorded at each clause, not WHETHER the clause is visited.

The walk visits |cnf| clauses. Each clause's literal index is at most k.
Therefore the total walk cost is bounded by |cnf| × k, which is bounded by n²
where n = |encodeCNF cnf|. This bound is a property of the CNF's dimensions,
not of the specific endpoint.

Since `witness_paths : List ParticlePath` is `List (List Bool)` which flattens
to `List Bool` = `ComputerTape` = `ComputerProgram`, the walk itself constructs the computation tape.
-/
noncomputable def walkCNFPaths {k : ℕ} (cnf : SyntacticCNF_EGPT k) (endpoint : { v : Vector Bool k // evalCNF cnf v = true }) : SatisfyingTableau k :=
  let assignment := endpoint.val
  let h_valid := endpoint.property

  let witness_paths := cnf.map (fun clause =>
    let witness_literal_opt := clause.find? (fun lit => evalLiteral lit assignment)
    match witness_literal_opt with
    | some lit => PathToConstraint lit
    | none => fromNat 0
  )

  {
    cnf := cnf,
    assignment := assignment,
    witness_paths := witness_paths,
    h_valid := h_valid
  }

/--
Flatten the witness-path trace into a `ComputerProgram`.
This makes explicit that the certificate trace is an executable tape/program.
-/
def SatisfyingTableau.toComputerProgram {k : ℕ} (tableau : SatisfyingTableau k) : ComputerProgram :=
  List.flatten (tableau.witness_paths.map (fun p => p.val))

/-- The flattened witness trace is a program by definition. -/
@[simp] theorem SatisfyingTableau.toComputerProgram_eq_bind {k : ℕ} (tableau : SatisfyingTableau k) :
    tableau.toComputerProgram = List.flatten (tableau.witness_paths.map (fun p => p.val)) := rfl

/--
**The walk complexity equals the sum of path costs.**
-/
theorem walkComplexity_eq_sum_of_paths {k : ℕ} (cnf : SyntacticCNF_EGPT k) (endpoint : { v : Vector Bool k // evalCNF cnf v = true }) :
  let tableau := walkCNFPaths cnf endpoint
  tableau.complexity = (tableau.witness_paths.map toNat).sum :=
by
  intro tableau
  simp [SatisfyingTableau.complexity]

/--
**The cost to walk to any single literal is bounded by `k`.**

Each literal's variable index is `Fin k`, so `PathToConstraint lit` has length
at most `k - 1 < k`. The walk to any clause address costs at most `k` steps.
-/
lemma cost_of_walk_le_k {k : ℕ} (cnf : SyntacticCNF_EGPT k) (endpoint : { v : Vector Bool k // evalCNF cnf v = true }) (clause : Clause_EGPT k) (h_clause_in_cnf : clause ∈ cnf) :
  let witness_literal_opt := clause.find? (fun lit => evalLiteral lit endpoint.val)
  match witness_literal_opt with
  | some lit => (PathToConstraint lit).val.length ≤ k
  | none => 0 ≤ k
:= by
  let assignment := endpoint.val
  have h_valid_assignment : evalCNF cnf assignment = true := endpoint.property

  unfold evalCNF at h_valid_assignment
  have h_clause_is_sat : evalClause clause assignment = true := by
    rw [List.all_eq_true] at h_valid_assignment
    exact h_valid_assignment clause h_clause_in_cnf

  unfold evalClause at h_clause_is_sat

  cases h_find_result : clause.find? (fun lit => evalLiteral lit assignment) with
  | none =>
    rw [List.any_eq_true] at h_clause_is_sat
    obtain ⟨lit, h_mem, h_eval⟩ := h_clause_is_sat
    have h_find_none := List.find?_eq_none.mp h_find_result
    have h_not_eval := h_find_none lit h_mem
    rw [h_eval] at h_not_eval
    exact absurd rfl h_not_eval
  | some witness_lit =>
    simp only [PathToConstraint, toNat, fromNat, List.length_replicate]
    have h_lt : witness_lit.particle_idx.val < k := witness_lit.particle_idx.isLt
    exact Nat.le_of_lt h_lt

lemma path_complexity_le_k {k : ℕ} (clause : Clause_EGPT k) (endpoint : Vector Bool k) :
  (toNat (match clause.find? (fun lit => evalLiteral lit endpoint) with
   | some lit => fromNat lit.particle_idx.val
   | none => fromNat 0)) ≤ k := by
  cases h_find : clause.find? (fun lit => evalLiteral lit endpoint) with
  | none =>
    simp only [toNat, fromNat, List.length_replicate]
    exact Nat.zero_le k
  | some witness_lit =>
    simp only [toNat, fromNat, List.length_replicate]
    exact Nat.le_of_lt witness_lit.particle_idx.isLt

/--
**The N² Walk Bound: Total walk cost is bounded by |cnf| × k.**

The walk visits |cnf| clauses. At each clause, the farthest reachable literal
has index < k. Therefore the total cost is at most |cnf| × k. Since both
|cnf| ≤ n and k ≤ n (where n = |encodeCNF cnf|, proved by
`cnf_length_le_encoded_length` and `encodeCNF_size_ge_k`), the total cost
is bounded by n × n = n².

This bound depends ONLY on the CNF's dimensions — not on the endpoint.
Any endpoint that satisfies the CNF produces a walk with cost ≤ |cnf| × k.
-/
theorem walkComplexity_upper_bound {k : ℕ} (cnf : SyntacticCNF_EGPT k) (endpoint : { v : Vector Bool k // evalCNF cnf v = true }) :
  (walkCNFPaths cnf endpoint).complexity ≤ cnf.length * k :=
by
  have h_bound_element : ∀ clause ∈ cnf,
    (toNat (match clause.find? (fun lit => evalLiteral lit endpoint.val) with
    | some lit => fromNat lit.particle_idx.val
    | none => fromNat 0)) ≤ k := by
    intro clause _
    exact path_complexity_le_k clause endpoint.val

  unfold walkCNFPaths SatisfyingTableau.complexity
  simp [PathToConstraint, List.map_map, Function.comp]

  induction cnf with
  | nil => simp
  | cons head tail ih =>
    simp [List.map_cons, List.sum_cons, List.length_cons]
    have h_head : (toNat (match head.find? (fun lit => evalLiteral lit endpoint.val) with
      | some lit => fromNat lit.particle_idx.val
      | none => fromNat 0)) ≤ k := path_complexity_le_k head endpoint.val

    have h_tail : (tail.map (toNat ∘ fun clause =>
      match clause.find? (fun lit => evalLiteral lit endpoint.val) with
      | some lit => fromNat lit.particle_idx.val
      | none => fromNat 0)).sum ≤ tail.length * k := by
      have h_tail_sat : evalCNF tail endpoint.val = true := by
        have h_full_sat := endpoint.property
        unfold evalCNF at h_full_sat ⊢
        rw [List.all_cons] at h_full_sat
        simp only [Bool.and_eq_true] at h_full_sat
        exact h_full_sat.2

      let tail_endpoint : { v : Vector Bool k // evalCNF tail v = true } := ⟨endpoint.val, h_tail_sat⟩

      apply ih tail_endpoint

      intro clause h_mem_tail
      exact path_complexity_le_k clause endpoint.val

    linarith [h_head, h_tail]

/--
**Computable Walk (The Universal Tableau Generator).**

This is the computable version of `walkCNFPaths`. It takes a CNF and a
candidate endpoint (`Vector Bool k`) and returns `some SatisfyingTableau`
if the candidate is valid, `none` otherwise.

This function does NOT use `Exists.choose` or Classical.choice.
It is purely computable — executable Lean code.

The walk logic is identical to `walkCNFPaths`: visit every clause, record the
path to the satisfied literal. The only difference is that the validity check
(`evalCNF cnf candidate`) is performed computationally via `if h_valid : ...`.
-/
def computeTableau? {k : ℕ} (cnf : SyntacticCNF_EGPT k)
  (candidate : Vector Bool k) : Option (SatisfyingTableau k) :=
  if h_valid : evalCNF cnf candidate = true then
    let witness_paths := cnf.map (fun clause =>
      match clause.find? (fun lit => evalLiteral lit candidate) with
      | some lit => PathToConstraint lit
      | none     => fromNat 0
    )
    some {
      cnf := cnf,
      assignment := candidate,
      witness_paths := witness_paths,
      h_valid := h_valid
    }
  else
    none

/--
**Lemma: `computeTableau?` returns `none` iff the candidate does not satisfy the CNF.**

This follows directly from the `if`/`else` branch structure of `computeTableau?`.
-/
theorem computeTableau_none_iff_not_sat {k : ℕ} (cnf : SyntacticCNF_EGPT k) (v : Vector Bool k) :
    computeTableau? cnf v = none ↔ evalCNF cnf v = false := by
  constructor
  · intro h_none
    unfold computeTableau? at h_none
    by_contra h_not_false
    push_neg at h_not_false
    have h_true : evalCNF cnf v = true := by
      cases evalCNF cnf v <;> simp_all
    simp [h_true] at h_none
  · intro h_false
    unfold computeTableau?
    simp [h_false]

/--
**Lemma: When `computeTableau?` returns `some`, the resulting tableau's
complexity is bounded by `cnf.length * k`.**

This matches the `walkComplexity_upper_bound` bound. The walk logic in
`computeTableau?` constructs the same `witness_paths` structure as
`walkCNFPaths`, so the same per-clause bound applies.
-/
theorem computeTableau_time_bounded {k : ℕ} (cnf : SyntacticCNF_EGPT k) (v : Vector Bool k)
    (tableau : SatisfyingTableau k)
    (h : computeTableau? cnf v = some tableau) :
    tableau.complexity ≤ cnf.length * k := by
  -- Extract that evalCNF cnf v = true from the `some` branch
  have h_valid : evalCNF cnf v = true := by
    unfold computeTableau? at h
    split at h
    · case isTrue h_true => exact h_true
    · case isFalse => simp at h
  -- The tableau from computeTableau? has specific structure
  have h_tableau : tableau = {
      cnf := cnf,
      assignment := v,
      witness_paths := cnf.map (fun clause =>
        match clause.find? (fun lit => evalLiteral lit v) with
        | some lit => PathToConstraint lit
        | none     => fromNat 0),
      h_valid := h_valid
    } := by
    unfold computeTableau? at h
    simp [h_valid] at h
    exact h.symm
  -- The tableau equals the one produced by walkCNFPaths, so reuse its bound
  let endpoint : { w : Vector Bool k // evalCNF cnf w = true } := ⟨v, h_valid⟩
  have h_eq : tableau.complexity = (walkCNFPaths cnf endpoint).complexity := by
    rw [h_tableau]
    rfl
  rw [h_eq]
  exact walkComplexity_upper_bound cnf endpoint

-- Backward-compatible alias used by SetRFL.lean
noncomputable abbrev constructSatisfyingTableau {k : ℕ} := @walkCNFPaths k
noncomputable abbrev tableauComplexity_upper_bound {k : ℕ} := @walkComplexity_upper_bound k

-- EGPT — Electronic Graph Paper Theory
-- Copyright (C) 2026 Essam Abadir
-- Licensed under the DeSciX Community Source Code License (DCSL) v1.0.
-- See LICENSE and DeSciX_Community_License_v1.pdf in the repository root.
-- Provided WITHOUT ANY WARRANTY. See the DCSL for details.
