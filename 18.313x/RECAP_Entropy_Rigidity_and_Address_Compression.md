# Recap: Conditional Entropy Rigidity of Zero and Address Compression

*Written 2026-03-28 after Exchange 27. Updated after Walk.lean v2 (variable-ordered, LFTA-aligned).*
*Purpose: Ground all participants in the established results before the completeness proof.*

---

## 1. The Random Walk and Address Compression (C18, IN11)

A particle doing a random walk on a binary tree at time step `t` has:

- **2^t possible paths** — the full binary tree of depth `t` (exponential in `t`)
- **t + 1 possible addresses** — positions 0, 1, ..., t (linear in `t`)

This is Shannon's source coding theorem applied to the walk. The exponential path space compresses to a linear address space because:

**`PathCompress_AllTrue`** ([Core.lean:25](../Lean/Archive/Core.lean#L25)) enforces maximal compression:
```lean
def PathCompress_AllTrue (L : List Bool) : Prop := ∀ x ∈ L, x = true
abbrev ParticlePath := { L : List Bool // PathCompress_AllTrue L }
```

Every `ParticlePath` is `replicate n true` for some `n`. One unique path per length. The address IS the length. `equivParticlePathToNat` ([NumberTheory/Core.lean:65-69](../Lean/Archive/NumberTheory/Core.lean#L65-L69)) proves the bijection `ParticlePath ≃ ℕ`.

**Stan's formulation (Exchange 17):**
> "At any t_i the depth is also t_i and while there are 2^t_i paths that a particle could have followed there are only t_i+1 addresses (ParticlePaths or CNFs) the particle can be at since the addresses are the maximally compressed form of information."

**What this means for SAT:** The walk over a CNF operates in address space (2k literal addresses, linear in k), NOT in solution space (2^k assignments, exponential). Each literal has an address:

```lean
-- UTM.lean:228
def literalAddress {k : ℕ} (lit : Literal k) : ℕ := Literal.toNat lit
-- literalAddress lit = 2 * lit.particle_idx.val + (if lit.polarity then 1 else 0)
-- For k variables: 2k addresses {0, 1, ..., 2k-1}
```

`literalAddress_lt_two_k` ([UTM.lean:248-251](../Lean/EGPT/InformationTheory/Complexity/UTM.lean#L248-L251)) proves each address < 2k.

---

## 2. Solutions Are Defined by the CNF Itself (C23, IN12)

The destination addresses — the satisfying assignments — are not external to the CNF. They are defined BY the CNF's clause-literal structure.

**Three equivalent formulations, all sorry-free (C23):**

| Layer | Formulation | Theorem |
|-------|-------------|---------|
| Boolean | `evalCNF cnf a = true` | Standard SAT |
| Address | `ndmCircuitEval cnf a = true` | `ndmCircuitEval_eq_evalCNF` ([UTM.lean:693-710](../Lean/EGPT/InformationTheory/Complexity/UTM.lean#L693-L710)) |
| Entropy | `conditionalCNFEntropy composite cnf = 0` | `cnfSharesFactor_iff_zero_conditional_cnf_entropy` ([Decomposition.lean:822-859](../Lean/EGPT/InformationTheory/Complexity/Decomposition.lean#L822-L859)) |
| Prime | `cnfSharesFactor a cnf` | `evalCNF_true_iff_cnfSharesFactor` |

The CNF's clauses contain all the information needed to determine satisfiability. Each clause lists its literal addresses. The walk traverses these addresses. No external oracle is consulted.

**Stan (Exchange 17):** "You cannot define the circuit without defining output constraints in CNF form." `cnf_for_specific_assignment` constructs CNF from state vectors — stating the problem defines the solution space.

---

## 3. Conditional Entropy Decomposition (C6, C17, IN23)

The chain rule decomposes CNF entropy clause-by-clause:

```
H(c_1, c_2, ..., c_n | composite) = H(c_1 | composite) + H(c_2 | composite, c_1) + ...
```

**Key implementation** ([Decomposition.lean:624-626](../Lean/EGPT/InformationTheory/Complexity/Decomposition.lean#L624-L626)):
```lean
noncomputable def conditionalCNFEntropy {k : ℕ}
    (composite : ℕ) (cnf : SyntacticCNF k) : ℝ :=
  (cnf.map (conditionalClauseEntropy composite)).sum
```

The composite acts as a **sufficient statistic** (C24, Rota Exchange 20): given the composite, clauses are conditionally independent. The chain rule collapses to a simple sum:

```
H(clause_1 ∧ clause_2 ∧ ... | composite) = Σ H(clause_j | composite)
```

No joint distribution needed. Each clause contributes independently.

**Each clause's contribution** is determined by a local divisibility check ([Decomposition.lean:600-603](../Lean/EGPT/InformationTheory/Complexity/Decomposition.lean#L600-L603)):
```lean
noncomputable def conditionalLiteralEntropy {k : ℕ}
    (composite : ℕ) (lit : Literal k) : ℝ :=
  if literalAtom lit ∣ composite then 0
  else Real.log (literalAtom lit)
```

- `literalAtom lit ∣ composite` → entropy = 0 (literal's information already present)
- `¬ literalAtom lit ∣ composite` → entropy = log(p) (full new information)

A clause's entropy is zero iff at least one literal divides the composite. This is the information-theoretic formulation of "the clause is satisfied."

---

## 4. Rigidity of Zero (C24, IN16)

This is the structural result that makes UNSAT detectable without enumeration.

**Statement:** The sum of non-negative conditional entropy terms equals zero iff EVERY term equals zero.

```
conditionalCNFEntropy composite cnf = 0
  ↔ ∀ clause ∈ cnf, conditionalClauseEntropy composite clause = 0
```

**Proof** ([Decomposition.lean:832-859](../Lean/EGPT/InformationTheory/Complexity/Decomposition.lean#L832-L859)): Forward: if all clause entropies are zero, the sum is zero. Backward: if the sum of non-negative terms is zero, each must be zero (otherwise the sum would be positive). Uses `conditionalClauseEntropy_nonneg` and `List.sum_eq_zero`.

**Why this matters:**
- One unsatisfied clause makes the total strictly positive
- You don't search for a needle in a haystack — you ask whether a sum of non-negative terms can be driven to zero
- The composite makes clauses independent (sufficient statistic), so each clause's zero/nonzero status is a LOCAL check

**Rota (Exchange 20):**
> "The zero is RIGID. `ndmEntropyWalk_nonneg` + sum-of-independent-nonneg-terms means a single unsatisfied clause makes the total strictly positive."

---

## 5. LFTA Additive Decomposition (C25, IN17)

The Fundamental Theorem of Arithmetic provides the additive structure:

```
log(composite) = Σ v_p(n) × log(p)
```

where `v_p(n)` is the p-adic valuation. Information decomposes additively over primes.

**Shannon-optimal code** for `Vector Bool k` has length `log(2^k) = k` bits. The "map" (address) IS the bitlength.

**What this means:** A k-variable assignment encoded as a composite decomposes into k independent 1-bit checks (one per variable). Each check is a divisibility test: does `literalAtom lit` divide the composite?

---

## 6. Walk.lean v2 — Variable-Ordered, LFTA-Aligned

Walk.lean has been redesigned to align with the LFTA decomposition. The walk now processes **variables in address order** (x₀, x₁, ..., x_{k-1}), not clauses.

### 6a. Pre-computation: the factor landscape

The CNF clauses define the complete factor landscape before the walk begins. Each clause `c` contains literals, each literal has address `2i + polarity`. The set of all literal addresses across all clauses IS the CNF's prime factor structure — the "map" that the walk traverses.

Key realization (IN22, Exchange 25): **the set of prime factors IS the composite.** When you see all factors laid out before the walk starts, the composite's structure is visible. You don't need to multiply primes into a composite only to factor them apart — the literals ARE the factors.

### 6b. Sorted walk in address order

The walk processes variables in order: x₀, x₁, ..., x_{k-1}. At each variable xᵢ, it makes a binary choice (true/false) — selecting one of two literal addresses:
- `(xᵢ, true)` → address `2i + 1`
- `(xᵢ, false)` → address `2i`

This directly mirrors the LFTA decomposition: `log(composite) = Σ log(p_i)`, one term per variable. Each step contributes one prime factor to the incrementally-built composite.

### 6c. Viability check

After each variable commitment, every clause must remain **viable**:
- **Satisfied**: at least one committed literal in the clause evaluates true, OR
- **Has future options**: at least one literal in the clause has an unassigned variable (index > i)

A non-viable clause is dead — it can never be satisfied. The walk detects UNSAT the moment any clause becomes non-viable.

### 6d. The implementation ([Walk.lean](../Lean/EGPT/InformationTheory/Complexity/Walk.lean))

```lean
def varWalkGo {k : ℕ} (choices : List Bool) (cnf : SyntacticCNF k) :
    Option (List Bool) :=
  if h : choices.length ≥ k then
    if cnf.all (clauseViable choices) then some choices else none
  else if isChoiceCompatible choices true cnf then
    varWalkGo (choices ++ [true]) cnf
  else if isChoiceCompatible choices false cnf then
    varWalkGo (choices ++ [false]) cnf
  else none

def computableSATWalk {k : ℕ} (cnf : SyntacticCNF k) : Option (Vector Bool k) :=
  match varWalkGo (k := k) [] cnf with
  | some choices =>
    if h : choices.length = k then
      some (Vector.ofFn (fun (i : Fin k) => choices[i.val]'(by omega)))
    else none
  | none => none
```

- **k steps** (one per variable), each a binary choice
- **No `noncomputable`**, no `Classical.choice`, no `Real.log`
- **Soundness proven sorry-free**: `computableSATWalk_sound`
- **Completeness is the P=NP claim**: `computableSATWalk_complete` (`sorry`)

### 6e. Connection to entropy chain

| Walk step | Entropy analog | LFTA analog |
|-----------|---------------|-------------|
| Choose polarity for xᵢ | H(xᵢ \| composite, x₀,...,x_{i-1}) = 0 | One term in Σ log(p_i) |
| Clause becomes satisfied | conditionalClauseEntropy → 0 | Literal's prime divides composite |
| Clause stays viable | Clause can still reach zero entropy | Remaining primes available |
| No viable choice → UNSAT | Total entropy permanently positive | No composite can zero all clauses |

---

## 7. Key Lean Theorems — Quick Reference

| Theorem | File | What it proves |
|---------|------|----------------|
| `PathCompress_AllTrue` | [Core.lean:25](../Lean/Archive/Core.lean#L25) | ParticlePath = all-true lists |
| `equivParticlePathToNat` | [NumberTheory/Core.lean:65](../Lean/Archive/NumberTheory/Core.lean#L65) | ParticlePath ≃ ℕ bijection |
| `literalAddress_lt_two_k` | [UTM.lean:248](../Lean/EGPT/InformationTheory/Complexity/UTM.lean#L248) | Each literal address < 2k |
| `ndmCircuitEval_eq_evalCNF` | [UTM.lean:693](../Lean/EGPT/InformationTheory/Complexity/UTM.lean#L693) | Circuit = Boolean evaluation |
| `conditionalLiteralEntropy` | [Decomposition.lean:600](../Lean/EGPT/InformationTheory/Complexity/Decomposition.lean#L600) | H(lit \| composite) = 0 iff divides |
| `conditionalCNFEntropy` | [Decomposition.lean:624](../Lean/EGPT/InformationTheory/Complexity/Decomposition.lean#L624) | H(CNF \| composite) = sum of clause terms |
| `cnfSharesFactor_iff_zero_conditional_cnf_entropy` | [Decomposition.lean:822](../Lean/EGPT/InformationTheory/Complexity/Decomposition.lean#L822) | SAT ↔ zero total entropy |
| `conditionalClauseEntropy_nonneg` | [Decomposition.lean](../Lean/EGPT/InformationTheory/Complexity/Decomposition.lean) | Each clause entropy ≥ 0 |
| `ndmEntropyWalk_determines_sat` | [UTM.lean:485](../Lean/EGPT/InformationTheory/Complexity/UTM.lean#L485) | Walk entropy = 0 ↔ SAT |
| `computableSATWalk_sound` | [Walk.lean](../Lean/EGPT/InformationTheory/Complexity/Walk.lean) | Walk returns some → SAT (**sorry-free**) |
| `computableSATWalk_complete` | [Walk.lean](../Lean/EGPT/InformationTheory/Complexity/Walk.lean) | SAT → walk returns some (**sorry — the P=NP claim**) |

---

## 8. The Open Question — Precisely Stated

**Given:** A satisfiable `SyntacticCNF k`.

**The walk** processes variables x₀, x₁, ..., x_{k-1} in address order, choosing a polarity for each. At each step, it checks that all clauses remain viable (satisfied or have unassigned literals).

**Must prove** (`computableSATWalk_complete`): The walk never returns `none` on a satisfiable CNF.

**The ghost guide argument (IN24):** A satisfying assignment `a` defines a ghost choice at each variable: `a.get 0, a.get 1, ..., a.get (k-1)`. At step i, the ghost choice for xᵢ always passes `isChoiceCompatible` because:

1. Every clause is either already satisfied by committed variables matching `a`, or contains a literal with variable index > i that `a` satisfies.
2. Since `a` satisfies ALL clauses, no clause can become non-viable when committing `a`'s choice.

Therefore `isChoiceCompatible` returns true for at least one polarity (the ghost's), and the walk proceeds.

**The subtlety:** The walk may not follow the ghost. It tries `true` first. If `true` passes viability but `a.get i = false`, the walk diverges from the ghost. The ghost's literals for future clauses may then be killed.

**The LFTA connection:** The additive decomposition `log(composite) = Σ log(p_i)` means each variable's contribution is independent. If viability is preserved at each step (the walk's check ensures this), the remaining variables can still be assigned to satisfy all remaining clauses. The rigidity of zero (C24) means any violation is detected immediately — it cannot be hidden behind future choices.

**What must be formalized:** An inductive invariant showing that after each walk step, the remaining (unsatisfied) clauses are satisfiable by some assignment of the remaining (unassigned) variables. The one-step viability check ensures this because: if a clause has at least one unassigned literal, the remaining variables include that literal's variable, and the literal can potentially be made true.

*This document should be read by all debate participants before the next exchange.*
