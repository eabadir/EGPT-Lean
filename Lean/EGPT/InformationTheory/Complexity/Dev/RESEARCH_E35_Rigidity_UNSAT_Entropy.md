# Research: Rigidity of Zero, UNSAT Detection, and the Conditional Entropy Decomposition

**Date:** 2026-03-30
**Context:** Exchange 35 closeout preparation — briefing for JvM and Rota
**Sources:** Concordance JSON, debate_log.jsonl, Lean/EGPT/ and Lean/PR/ codebases

---

## The Core Chain (all sorry-free)

The UNSAT detection argument chains through four levels:

```
evalCNF cnf a = true
  ↔ cnfSharesFactor a cnf                    [Decomposition.lean:250+]
  ↔ conditionalCNFEntropy composite cnf = 0  [Decomposition.lean:630]
  ↔ ndmEntropyWalk(composite).totalEntropy=0 [UTM.lean:1207]
  ↔ ndmCircuitEval cnf a = true              [UTM.lean:1515]
```

The CONTRAPOSITIVE gives UNSAT:

```
¬(∃ a, evalCNF cnf a = true)
  ↔ ¬(CNFSharesFactor cnf)                   [sat_iff_prime_divisibility]
  → ∀ v, computeTableau? cnf v = none        [unsat_detected_by_prime_structure]
  → ∀ composite, conditionalCNFEntropy > 0   [rigidity of zero, backward]
```

---

## 1. Rigidity of Zero (C24)

### Consensus point

**C24 (Exchange 20, all agree):**
> "Rigidity of zero: sum of non-negative independent conditional entropy
> terms = 0 iff each term = 0. One unsatisfied clause makes total
> positive. The composite acts as sufficient statistic making clauses
> conditionally independent."

### Debate dialog

**Rota (Exchange 20, 20_Circuit_SAT_Three_Layer.md:53):**
> "The zero is RIGID. `ndmEntropyWalk_nonneg` + sum-of-independent-
> nonneg-terms means a single unsatisfied clause makes the total strictly
> positive. You are not searching for a needle in a haystack — you are
> asking whether a sum of non-negative independent terms can be driven
> to zero."

**RECAP (RECAP_Entropy_Rigidity_and_Address_Compression.md:109):**
> "Proof (Decomposition.lean:832-859): Forward: if all clause entropies
> are zero, the sum is zero. Backward: if the sum of non-negative terms
> is zero, each must be zero (otherwise the sum would be positive)."

**COURSE_PLAN.md:264:**
> "The rigidity of zero: sum of non-negative independent terms = 0 iff
> each = 0."

### Lean theorem

**`cnfSharesFactor_iff_zero_conditional_cnf_entropy`**
(Decomposition.lean:630-634):
```lean
theorem cnfSharesFactor_iff_zero_conditional_cnf_entropy {k : ℕ}
    (a : Vector Bool k) (cnf : SyntacticCNF_EGPT k)
    (h_clauses_nonempty : ∀ c ∈ cnf, c ≠ []) :
    cnfSharesFactor a cnf ↔
      conditionalCNFEntropy (assignmentCompositePrime a) cnf = 0
```

The proof uses `List.sum_eq_zero` on non-negative clause entropies.
Sorry-free.

---

## 2. UNSAT Detection via Prime Structure

### Lean theorem

**`unsat_detected_by_prime_structure`**
(Decomposition.lean:422-433):
```lean
theorem unsat_detected_by_prime_structure {k : ℕ}
    (cnf : SyntacticCNF_EGPT k) :
    (¬ CNFSharesFactor cnf) →
      ∀ v : Vector Bool k, computeTableau? cnf v = none
```

If no assignment's composite shares factors with the CNF (global UNSAT),
then `computeTableau?` returns `none` for every candidate. Sorry-free.

### The contrapositive chain

For UNSAT instances:
1. No satisfying assignment exists → `¬ CNFSharesFactor cnf`
2. → every composite has positive conditional entropy (rigidity backward)
3. → `computeTableau?` returns `none` for all candidates
4. → the ndm entropy walk never reaches zero total entropy

---

## 3. The Entropy Walk Determines SAT

### Lean theorems

**`ndmEntropyWalk`** (UTM.lean:1140-1143):
```lean
noncomputable def ndmEntropyWalk {k : ℕ}
    (cnf : SyntacticCNF_EGPT k) (composite : ℕ) :
    NDMEntropyWalkState k :=
  cnf.foldl (fun state clause => ndmEntropyStep clause state)
    (NDMEntropyWalkState.init composite)
```

The walk folds over clauses, accumulating conditional entropy. This IS
the chain rule decomposition computed as a machine operation.

**`ndmEntropyWalk_total_eq`** (UTM.lean:1185-1191):
```lean
theorem ndmEntropyWalk_total_eq {k : ℕ}
    (cnf : SyntacticCNF_EGPT k) (composite : ℕ) :
    (ndmEntropyWalk cnf composite).totalEntropy =
      conditionalCNFEntropy composite cnf
```

The walk's total equals the conditional CNF entropy. Sorry-free.

**`ndmEntropyWalk_determines_sat`** (UTM.lean:1207-1213):
```lean
theorem ndmEntropyWalk_determines_sat {k : ℕ}
    (cnf : SyntacticCNF_EGPT k)
    (a : Vector Bool k)
    (h_clauses_nonempty : ∀ c ∈ cnf, c ≠ []) :
    (ndmEntropyWalk cnf (assignmentCompositePrime a)).totalEntropy
      = 0 ↔ evalCNF cnf a = true
```

Walk total entropy = 0 iff the CNF is satisfiable under `a`. Sorry-free.

---

## 4. Walk Exhausts CNF Entropy (Zero Remaining)

### Lean theorems

**`walk_exhausts_cnf_entropy_explicit`** (PPNP.lean:355-369):
```lean
theorem walk_exhausts_cnf_entropy_explicit {k : ℕ}
    (cnf : SyntacticCNF_EGPT k)
    (endpoint : { v : Vector Bool k // evalCNF cnf v = true }) :
    let tableau := walkCNFPaths cnf endpoint
    tableau.witness_paths.length = cnf.length ∧
    (cnf.length - tableau.witness_paths.length = 0) ∧
    tableau.cnf = cnf ∧
    H_canonical_ln (α := Fin 0) Fin.elim0 = 0 ∧
    IsEntropyZeroInvariance H_canonical_ln ∧
    tableau.complexity ≤ cnfInformationContent cnf
```

Five components bundled sorry-free:
1. All clauses visited (`witness_paths.length = cnf.length`)
2. Residual clause count is zero
3. CNF preserved
4. Canonical entropy on empty domain is zero (`H(∅) = 0`)
5. Zero-invariance available
6. Extraction cost bounded by information content

### Debate dialog on ZeroOnEmptyDomain

**Exchange 11 (11_QA.md:13):**
> "`IsEntropyZeroOnEmptyDomain` (`H(∅) = 0`) is the more directly
> relevant of the two. After the walk has visited every clause, the
> domain of unprocessed clauses is empty. This axiom formalizes the
> claim that the remaining information to be extracted is exactly zero."

**Exchange 11 (11_QA.md:17):**
> "Together they close the entropy argument from both sides:
> ZeroOnEmptyDomain says 'nothing left to process → zero entropy,' and
> ZeroInvariance says 'adding vacuous alternatives doesn't change that.'"

### Lean axiom structures

**`IsEntropyZeroOnEmptyDomain`** (Entropy/Common.lean:313-317):
```lean
structure IsEntropyZeroOnEmptyDomain
  (H_func : ...) : Prop where
  apply_to_empty_domain : H_func Fin.elim0 = 0
```

**`IsEntropyZeroInvariance`** (Entropy/Common.lean:301-309):
```lean
structure IsEntropyZeroInvariance
  (H_func : ...) : Prop where
  zero_invariance : ∀ ... H_func p_ext = H_func p_orig
```

Both proven for `H_canonical_ln`:
- `h_canonical_is_zero_on_empty` (H.lean:110)
- `h_canonical_is_zero_invariance` (H.lean:142)

---

## 5. The NDM Circuit Bridge

### Lean theorems

**`ndmCircuitEval_eq_evalCNF`** (UTM.lean:1458-1470):
```lean
theorem ndmCircuitEval_eq_evalCNF {k : ℕ}
    (cnf : SyntacticCNF_EGPT k) (a : Vector Bool k) :
    ndmCircuitEval cnf a = evalCNF cnf a
```

The NDM circuit IS evalCNF, operating in address space. Sorry-free.

**`ndmCircuit_entropy_bridge`** (UTM.lean:1515-1520):
```lean
theorem ndmCircuit_entropy_bridge {k : ℕ}
    (cnf : SyntacticCNF_EGPT k) (a : Vector Bool k)
    (h_clauses_nonempty : ∀ c ∈ cnf, c ≠ []) :
    ndmCircuitEval cnf a = true ↔
      (ndmEntropyWalk cnf (assignmentCompositePrime a))
        .totalEntropy = 0
```

Circuit evaluation = true ↔ entropy walk total = 0. Sorry-free.

---

## 6. Entropy Determines SAT via Tableau

### Lean theorem

**`entropy_determines_sat_via_tableau`** (PPNP.lean:709-725):
```lean
theorem entropy_determines_sat_via_tableau {k : ℕ}
    (cnf : SyntacticCNF_EGPT k) :
    IsEntropyCondAddSigma H_canonical_ln ∧
    ((¬ CNFSharesFactor cnf) →
      ∀ v : Vector Bool k, computeTableau? cnf v = none) ∧
    (∀ v : Vector Bool k, ∃ tableau,
      computeTableau? cnf v = some tableau →
      tableau.complexity ≤ cnfInformationContent cnf) ∧
    cnfInformationContent cnf ≤
      toNat (SetRFL.canonical_np_poly.eval
        (fromNat (encodeCNF cnf).length))
```

Bundles: (1) chain rule, (2) UNSAT detection, (3) bounded tableau,
(4) polynomial bound. Sorry-free.

---

## 7. The Sufficient Statistic Property

### Debate dialog

**RECAP (RECAP_Entropy_Rigidity.md:75):**
> "The composite acts as a sufficient statistic (C24, Rota Exchange 20):
> given the composite, clauses are conditionally independent. The chain
> rule collapses to a simple sum."

This is why the entropy decomposition works clause-by-clause: the
composite (assignment encoding) makes the clause entropies independent.
Each `H(clause_j | composite)` depends only on whether that clause
shares a factor with the composite — not on any other clause.

---

## Summary: The UNSAT Argument

For a CNF that is UNSAT:

1. No satisfying assignment exists
2. → `¬ CNFSharesFactor cnf` (`sat_iff_prime_divisibility`, contrapositive)
3. → For every composite, at least one clause has positive conditional
   entropy (rigidity of zero, backward direction)
4. → `conditionalCNFEntropy composite cnf > 0` for all composites
5. → `ndmEntropyWalk(composite).totalEntropy > 0` for all composites
6. → `computeTableau? cnf v = none` for all `v`
   (`unsat_detected_by_prime_structure`)

The key insight: you don't need to check all composites. Unit
propagation detects contradictions locally — a clause forced to have
zero uncommitted literals with no satisfied literal is a local witness
of `conditionalClauseEntropy > 0`. This local witness propagates
through the clause structure. When propagation exhausts without
contradiction and greedy completion succeeds, the total conditional
entropy IS zero — the rigidity theorem guarantees it.

---

## Cross-Reference Table

| Concept | Debate | Lean File | Theorem | Line |
|---------|--------|-----------|---------|------|
| Rigidity of zero | C24, E20 | Decomposition.lean | cnfSharesFactor_iff_zero_conditional_cnf_entropy | 630 |
| UNSAT via primes | E20 | Decomposition.lean | unsat_detected_by_prime_structure | 422 |
| Walk total = cond entropy | E19 | UTM.lean | ndmEntropyWalk_total_eq | 1185 |
| Walk determines SAT | E19 | UTM.lean | ndmEntropyWalk_determines_sat | 1207 |
| Walk exhausts entropy | E11 | PPNP.lean | walk_exhausts_cnf_entropy_explicit | 355 |
| Entropy → SAT via tableau | E14 | PPNP.lean | entropy_determines_sat_via_tableau | 709 |
| Circuit = evalCNF | E20 | UTM.lean | ndmCircuitEval_eq_evalCNF | 1458 |
| Circuit ↔ entropy | E20 | UTM.lean | ndmCircuit_entropy_bridge | 1515 |
| H(∅) = 0 | E11 | Entropy/H.lean | h_canonical_is_zero_on_empty | 110 |
| Zero invariance | E11 | Entropy/H.lean | h_canonical_is_zero_invariance | 142 |
| Sufficient statistic | C24 | RECAP.md | (narrative) | 75 |
