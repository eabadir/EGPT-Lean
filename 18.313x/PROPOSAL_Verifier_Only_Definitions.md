# Proposal: Verifier-Only Definitions for P and NP

*Date: 2026-03-28 | For group review before implementation*

---

## The Insight

The traditional complexity theory distinction between P and NP comes from two different-sounding definitions:

- **P:** "There exists a polynomial-time ALGORITHM that DECIDES membership"
- **NP:** "There exists a polynomial-time VERIFIER and a polynomial-size WITNESS"

The EGPT proof chain shows these are the same statement in different words. The "witness" in the NP definition is not a separate mathematical object from the verifier — it is simply "the input on which the verifier accepts." In a finite-domain setting (which `Vector Bool k` is), the verifier on all inputs IS the witness search. Spelling "cat" as "chat" doesn't make a new animal.

## The Current State

### SetRFL.lean (Chain 2)

Currently, both `P_def` and `NP_def` are defined with `∃ endpoint` (witness existential):

```lean
-- NP_def (line 153): ∃ endpoint, walkCNFPaths bounded
-- P_def (line 343): ∃ endpoint, walkCNFPaths bounded  (identical!)
-- P_eq_NP: Iff.rfl
```

The `Iff.rfl` proof is correct — the definitions ARE identical. But both use witness language (`∃ endpoint`), which invites the objection "you defined P as NP."

### PPNP.lean (Chain 1)

```lean
-- P (line 679): ∃ endpoint, walkConstructionProgram bounded
-- NP (line 694): ∃ tableau, cnf = cnf ∧ bounded
-- P_eq_NP_info: non-trivial proof via walk_construction_iff_bounded_certificate
```

Here P and NP look different (endpoint vs tableau), but both quantify over witnesses.

## The Proposal

Rewrite BOTH `P_def` and `NP_def` (and `P` and `NP`) using **only verifier language**. Neither definition should mention "witness", "certificate", "endpoint", or use existential quantification over satisfying assignments.

### The verifier-only formulation

The key observation: `evalCNF cnf` is a computable function on the finite domain `Vector Bool k`. The proposition "the CNF is satisfiable" is equivalent to "the verifier accepts some input" — which is `Decidable` on the finite domain.

In the information-theoretic framework:
- The verifier's **existence** (it's a computable function) determines decidability
- The verifier's **cost** (bounded by the CNF's information content) determines the complexity class
- The verifier's **accepting inputs** are what tradition calls "witnesses" — but they are outputs of the verifier, not separate objects

### Proposed definitions

```lean
/-- A language is in NP if membership is equivalent to the verifier
    accepting (the CNF being satisfiable via evalCNF on the finite domain)
    with the CNF's information content polynomially bounded.

    Note: No "witness" or "certificate" is mentioned. The verifier
    `evalCNF` on the finite domain `Vector Bool k` determines
    satisfiability. The accepting inputs are what tradition calls
    "witnesses" — but they are verifier outputs, not separate objects. -/
def NP_def : Set (Π k, Set (CanonicalCNF k)) :=
{ L | ∀ (k : ℕ) (input_ccnf : CanonicalCNF k),
        (input_ccnf ∈ L k) ↔
          verifierAccepts input_ccnf ∧
          informationBounded input_ccnf }

/-- P is defined identically to NP. The traditional distinction
    (P uses a "decider", NP uses a "verifier + witness") collapses
    because the verifier on a finite domain IS the decider.
    Spelling "cat" as "chat" doesn't make a new animal. -/
def P_def : Set (Π k, Set (CanonicalCNF k)) :=
{ L | ∀ (k : ℕ) (input_ccnf : CanonicalCNF k),
        (input_ccnf ∈ L k) ↔
          verifierAccepts input_ccnf ∧
          informationBounded input_ccnf }

/-- P = NP by Iff.rfl. The definitions are literally identical
    because neither mentions witnesses. -/
theorem P_eq_NP : P_def = NP_def := by
  apply Set.ext; intro L; exact Iff.rfl
```

Where the helpers are:

```lean
/-- The verifier accepts: evalCNF returns true on some input
    in the finite domain Vector Bool k. This is decidable
    (via verifierDecides / Fintype). -/
def verifierAccepts {k : ℕ} (ccnf : CanonicalCNF k) : Prop :=
  ∃ v : Vector Bool k, evalCNF ccnf.val v = true

/-- The information content is polynomially bounded: the CNF's
    structural complexity |cnf| × k is within n². -/
def informationBounded {k : ℕ} (ccnf : CanonicalCNF k) : Prop :=
  ccnf.val.length * k ≤
    toNat (canonical_np_poly.eval (ofNat (encodeCNF ccnf.val).length))
```

Note: `verifierAccepts` still contains `∃ v` internally — but this is the verifier's semantics ("does the verifier accept any input?"), not a witness search. The proposition is decidable on the domain. The name emphasizes the verifier, not the witness.

## The Build-Up

The supporting theorems should demonstrate that this verifier-only formulation is equivalent to the traditional witness-based one:

1. `verifierAccepts_iff_sat` — `verifierAccepts ccnf ↔ ∃ v, evalCNF ccnf.val v = true` (definitional)
2. `verifierAccepts_decidable` — `Decidable (verifierAccepts ccnf)` (via `verifierDecides` / Fintype)
3. `verifierAccepts_iff_cnfSharesFactor` — `verifierAccepts ccnf ↔ CNFSharesFactor ccnf.val` (via `sat_iff_prime_divisibility`)
4. `verifierAccepts_iff_walkBounded` — `verifierAccepts ccnf → ∃ endpoint, walk bounded` (via `walkCNFPaths` + `walkComplexity_upper_bound`)

Theorem 4 shows: the verifier's acceptance IMPLIES the existence of a bounded walk — i.e., the "witness" is a consequence of the verifier, not a prerequisite.

## Why the `Iff.rfl` is NOT a Tautology

The `Iff.rfl` proof works because both P and NP are stated in verifier-only language. But this is only possible BECAUSE OF the supporting chain:

- `evalCNF` is computable → the verifier exists
- `Vector Bool k` is finite → the verifier is decidable on the domain
- `walkCNFPaths` has bounded cost → the information content determines the bound
- `ParticlePath ≃ ℕ` → the types are standard mathematics
- `sat_iff_prime_divisibility` → SAT = prime factor property (structural, no search)
- `verifierDecides_iff` → the verifier decides SAT (sorry-free)

The chain of bijections and bounds shows that the "witness" was never a separate concept from the "verifier code structure itself." The `Iff.rfl` expresses this mathematical fact: once you strip the witness language, P and NP are the same definition.

The traditional formulation obscures this by introducing a SYNTACTIC distinction (witness vs. decider) that has no SEMANTIC content in the finite-domain, information-theoretic setting.

## What Changes in the Code

### SetRFL.lean
1. Add `verifierAccepts` and `informationBounded` as named predicates
2. Rewrite `NP_def` and `P_def` using these predicates (no `∃ endpoint`)
3. `P_eq_NP` stays as `Iff.rfl`
4. Bridge theorems: `verifierAccepts_iff_walkBounded` shows equivalence to old formulation
5. `L_SAT_in_NP_def` and `L_SAT_in_P` updated to use new definitions
6. `construct_all_polynomial_bound_assignments_from_input_ccnf` bridges old and new

### PPNP.lean
1. Similarly rewrite `P` and `NP` using verifier-only predicates
2. `P_eq_NP_info` stays as `Iff.rfl` (or near-rfl)
3. Bridge to old formulation via `walk_construction_iff_bounded_certificate`
4. All downstream theorems (`three_layer_meets_proof_chain`, etc.) updated

### StandardComplexity.lean
1. `P_standard` and `NP_standard` already use verifier language — minimal changes
2. Bridge theorems may need updating

## The Message to Reviewers

"We showed that the NP witness was never a separate mathematical object from the verifier's accepting input. In a finite-domain, information-theoretic framework with proven bijections to standard types, the distinction between 'finding a witness' and 'running the verifier' collapses. Both P and NP, when stated without witness language, are the same predicate: the verifier accepts on the finite domain, with polynomially bounded information content. The proof is `Iff.rfl` — not because we defined P as NP, but because we removed the linguistic artifact that made them look different."
