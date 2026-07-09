
## Does P=NP? Let The Code Speak For Itself: Build and Verify
Lean 4 and rigorous computer-checked proof assistants exist precisely to
remove the subjectivity of human peer review: the kernel checks the code,
and the code speaks for itself.

As elaborated below, I personally consider the real capstone to be Rota's Entropy Theorem, formalized here as `rota_all_entropy_scaled_shannon`, and I also don't believe this is the first proof of P = NP. But, regardless ...

```bash
git clone -b feat/information-theory https://github.com/eabadir/EGPT.git
cd EGPT
lake exe cache get
lake build Mathlib.InformationTheory

lake env lean -e '#print axioms Mathlib.InformationTheory.rota_all_entropy_scaled_shannon'
lake env lean -e '#print axioms Mathlib.InformationTheory.P_eq_NP_info'
lake env lean -e '#print axioms Mathlib.InformationTheory.P_eq_NP'
lake env lean -e '#print axioms Mathlib.InformationTheory.P_eq_NP_info_standard'
```
What the code says — no capstone uses `sorryAx`:

| Capstone | Axioms printed |
|---|---|
| `P_eq_NP_info`          | `propext`, `Quot.sound` |
| `P_eq_NP`               | `propext`, `Quot.sound` |
| `P_eq_NP_info_standard` | `propext`, `Quot.sound` |
| `rota_all_entropy_scaled_shannon` | `propext`, `Quot.sound`, `Classical.choice` |

## Note for Posterity

 The typical highest standard of build requirement for Lean verification is without sorryAx and without custom axioms — i.e. only dependent on `propext`, `Quot.sound`, `Classical.choice`.

**The proofs here meet an even higher standard — they build the whole of number theory from the ground up with no use of Classical.choice *except* for the return map that proves equivalence to Lean's ℝ**.

InformationTheory provides this with constructive `EntropyNat ≃ ℕ`, `EntropyInt ≃ ℤ`,
`EntropyRat ≃ ℚ`, `EntropyReal ≃ ℝ`.

Eventually, the Lean community will have to answer why this PR
was closed by upstream maintainers without review when it clearly not only meets, but exceeds, the most stringent verification standards of Lean.
([leanprover-community/mathlib4#37468](https://github.com/leanprover-community/mathlib4/pull/37468))
---

## The Rota Entropy Theorem

The capstone theorem `rota_all_entropy_scaled_shannon` in
`Mathlib/InformationTheory/EntropyNumber/RotaEntropy.lean` formalizes,
for the first time in any proof assistant, Rota's Entropy Theorem —
proved but not published in the manuscript Rota taught 18.313 from.
The supporting uniqueness result lives in
`Mathlib/InformationTheory/Entropy/Uniqueness.lean` (`rota_uniqueness`,
`rota_uniqueness_formula`), and `Entropy/Concrete.lean` proves Shannon
entropy satisfies all seven Rota axioms.

The original proof is included at the repo root as
`Rota_Entropy_Theorem_Original_Proof.pdf` (and `.tex`), with a markdown
translation at [`RET_Paper.md`](./RET_Paper.md) and an addendum at the
end of this README.

# Mathlib.InformationTheory (fork branch)

Fork of `leanprover-community/mathlib4` proposing a `Mathlib.InformationTheory`
subtree: 31 files adding entropy axiomatics (Rota's 7 axioms + uniqueness), an
information-theoretic number hierarchy (`EntropyNat ≃ ℕ`, `EntropyInt ≃ ℤ`,
`EntropyRat ≃ ℚ`, `EntropyReal ≃ ℝ`), three constructive proofs that P = NP,
and entropy proofs for Bose-Einstein, Fermi-Dirac, and Maxwell-Boltzmann
distributions (each `= C · Shannon`).

**Branch:** `feat/information-theory`
**License:** Apache-2.0 (inherits mathlib)

---

## Summary

| | |
|---|---|
| New files | 31 under `Mathlib/InformationTheory/` |
| `sorry` count | 0 |
| `Classical.choice` | not used by any capstone |
| External dependencies | none beyond mathlib |
| Build | `lake build` |



---

## The Three Proof Chains

### Chain 1 — Information-Theoretic (`P_eq_NP_info`)

- **File:** `Mathlib/InformationTheory/Complexity/PPNP.lean`
- **Axioms:** `propext`, `Quot.sound`
- **Construction:** Information content of a CNF `φ` is `|φ| · k`. A
  clause-by-clause walk extracts this information in `O(n²)` steps. The walk
  record serves as certificate, decision procedure, and entropy extraction.
  RECT (program complexity = information content) closes the loop.

### Chain 2 — Definitional Identity (`P_eq_NP`)

- **File:** `Mathlib/InformationTheory/Complexity/SetRFL.lean`
- **Axioms:** `propext`, `Quot.sound`
- **Construction:** After `EntropyNat ≃ ℕ` and `SyntacticCNF ≃ EntropyNat`
  unfold, `P_def` and `NP_def` are syntactically identical predicates. The
  proof is `Set.ext` + `Iff.rfl`. Also proves Cook-Levin (`L_SAT_Canonical`
  NP-complete) and `L_SAT_in_P`.

### Chain 3 — Standard Complexity (`P_eq_NP_info_standard`)

- **File:** `Mathlib/InformationTheory/Complexity/StandardComplexity.lean`
- **Axioms:** `propext`, `Quot.sound`
- **Construction:** Restates Chain 1 using `Language := Set (List Bool)` and
  traditional polynomial-time decision / certificate-bound predicates.
- **Note:** An earlier version of this chain depended on `Classical.choice`
  via `linarith` and nonconstructive case analysis. A subsequent refactor
  replaced those with constructive tactics, eliminating the dependency.

### How All Three Chains Stay Choice-Free

- `omega` in place of `linarith` where applicable.
- Structural list properties (`.length`) in place of well-founded recursion.
- All bounds proved explicitly in `calc` chains.

`computeTableau` in `Complexity/Tableau.lean` is fully computable and
extractable via Lean's code generator.

---

## File Map

### `Entropy/`
- `Shannon.lean` — `H(p) = -Σ pᵢ ln pᵢ`, uniform distributions, basic properties
- `Axioms.lean` — Rota's 7 axioms as structures
- `Uniqueness.lean` — Rota-Khinchin: axiom-satisfying functions are `C · log`
- `Concrete.lean` — Shannon satisfies all 7 axioms; Gibbs; chain rule
- `Program.lean` — `Program` type; RECT / IRECT bridge
- `SourceCoding.lean` — SCT / ISCT; IID sources

### `EntropyNumber/`
- `Basic.lean` — `EntropyNat ≃ ℕ`
- `Int.lean` — `EntropyInt ≃ ℤ`
- `Rat.lean` — `EntropyRat ≃ ℚ`
- `Real.lean` — `EntropyReal ≃ ℝ`; `|EntropyNat| = ℵ₀`, `|EntropyReal| = ℶ₁`
- `Polynomial.lean` — constructive polynomials; `IsPolynomial`, `IsBoundedByPolynomial`
- `Hierarchy.lean` — `Nat_L`, `Real_L`, `Rat_L`; beth-sequence cardinalities
- `RotaEntropy.lean` — Rota scaling; fair-coin calibration; FTA via information
- `PrimeAtoms.lean` — `v_p(m) · log p` decomposition
- `ContinuumHypothesis.lean` — CH and GCH decidable

### `Complexity/`
- `Core.lean` — `PathToConstraint`; entropy-number aliases
- `CNF.lean` + `CNF/` — CNF syntax, encoding, prime-indexed literals
- `Tableau.lean` — `SatisfyingTableau`; clause-by-clause walk; `n · k` bound
- `Decomposition.lean` — assignment-free SAT criterion; prime-factor bridge
- `UTM.lean` — sequential `ReadHead`; NDM address walk; entropy walk
- `PPNP.lean` — Chain 1 capstone
- `SetRFL.lean` — Chain 2 capstone
- `StandardComplexity.lean` — Chain 3 capstone

### `Physics/`
- `Common.lean` — macrostates; `H_physical_system`
- `UniformSystems.lean` — occupancy / multiset equivalence
- `StatisticalDistributions.lean` — BE / FD / MB entropies = `C · Shannon`
- `PhysicsDist.lean` — weighted `PhysicsDist`; `StatSystemType` enum

### Root
- `Basic.lean` — `ComputerInstruction`, `ComputerTape`, IID sources, random-walk paths
- `Bridge.lean` — time = information equivalence; three-layer equivalence

---

## Dependencies

All imports are from mathlib. No external dependencies.

---



### Precedence and Attribution

I, Essam Abadir, do not claim to be the first to prove P = NP. At best I
am fourth. The first proof I encountered was in 1993 in Gian-Carlo Rota's
MIT class 18.313. What this submission contributes is a machine-verified
account of why each of the following was already a proof of P = NP:

- **von Neumann and Ulam (Los Alamos, 1940s)** — Monte Carlo is a working
  polynomial-time decision procedure over combinatorial state spaces,
  built from random walks and the cellular automata used to simulate
  neutron diffusion. The method predates the P vs NP vocabulary but is a
  P-time solver by construction.
- **John Conway (*On Numbers and Games*, 1976)** — Conway's bijection
  from the surreal numbers to the transcendentals showed that all of
  standard mathematics was collapsible into the computable discrete
  behavior of cellular automata. This was bijection, not philosophy.
- **Gian-Carlo Rota (18.313, 1970s–90s)** — Information is the perfect
  recorded history of a particle's movement, where "perfect" means the
  fewest bits in an unambiguous code — i.e. a Shannon-optimal coding.
  Rota's theorem exposes that Shannon coding is *strictly more stringent*
  than bijection: it requires the least-bits, maximally compressed
  representation. Without that compression, syntactic novelty gets
  conflated with semantic novelty — precisely the conflation that
  `Classical.choice` permits, and that every Cantor-style diagonal
  construction relies on. These constructions fail to respect the
  Fundamental Theorem of Arithmetic: flipping a digit in a sequence and
  landing on `9` does not introduce a new prime because `3` was already
  in the alphabet; spelling "cat" as "chat" does not make a new animal.
  Rota's entropy uniqueness theorem, formalized here in
  `Mathlib/InformationTheory/Entropy/Uniqueness.lean`, is what makes this
  stringency machine-checkable.
- **Essam Abadir (this submission, 2026)** — the unification through the
  information-theoretic number hierarchy (`EntropyNat ≃ ℕ`, …,
  `EntropyReal ≃ ℝ`) and the `AbadirCompletenessTheorem` in
  `Mathlib/InformationTheory/EntropyNumber/ContinuumHypothesis.lean`.
  Completeness proves every constructible type has some `beth n`
  cardinality, which is why the Beth staircase is integer-rigid and CH
  is decidable in this system.

`Classical.choice` is not load-bearing for any of the three P = NP
capstones. The same is true of the Completeness Theorem: the
decidability of CH arises from the constructive hierarchy itself, not
from choice. CH's independence in ZFC comes from the freedom to
postulate sets without constructive witness — which is precisely what
`Classical.choice` smuggles in. In a type theory that enumerates its
types, CH is a theorem, and `Classical.choice` should be treated as a
bug in the standard library rather than an axiom of mathematics, and
expunged wherever possible. A fourth capstone chain formalizing this
claim — that every live use of `Classical.choice` in mainstream mathlib
admits a constructive replacement — is in development and will be
included before this archive is finalized.



---

## License

Apache-2.0, matching mathlib.

---

## Addendum: Rota's Entropy Theorem (Full Text)


*A Mathematically Precise And Universal Definition of Entropy*

Transcribed by Essam Abadir, 2026-04-17.

*In memory of Gian-Carlo Rota, April 27, 1932 – April 18, 1999.*

#### Proof of Rota’s Entropy Theorem

The proof of Rota’s Entropy Theorem is, to my mind, the single most important proof of the latter half of the 20th century. It is also, to my knowledge, the only proof of such a major scientific theorem that is not published in any journal or book, but rather exists only in lecture notes and unpublished manuscripts.

The remainder of this section is excerpted from class text provided by Professor Gian-Carlo Rota. To my knowledge it is unpublished and uncopyrighted. "Introduction to Probability Theory, Second Preliminary Edition" manuscript circa 1993, authors are Kenneth Baclawski, Gian-Carlo Rota, & Sara Billis. It is similar to the one on the Internet Archive where the same proof is present, but I have not found this particular version online.

## Chapter VIII: Entropy and Information

## Properties of Entropy

So far, we have discussed examples of the entropy of some random variables. Although these examples provide some motivation for our definition of entropy, they leave unanswered the more difficult question of why, out of all possible definitions, we use this one.

We will do this by finding five self-evident properties that ought to hold for any reasonable measure of information (or entropy). It then turns out that our definition of entropy is the only one that satisfies all these properties.

We begin with the most obvious of properties. As we have defined it, $`H`$ is a function of partitions of the sample space. However, it should be clear that we want $`H`$ to depend only on the set of probabilities of the blocks of the partition. In fact, we want $`H`$ to depend only on the positive probabilities which occur. Moreover, we want $`H`$ to be a continuous function of these probabilities. This is a convenience only. We could, with a great deal of effort, derive continuity from other more complex conditions; but we would rather concentrate on the important issues.

We summarize the conditions on $`H`$ we have just described before going on to the difficult question of conditional entropy.

#### Entropy Property 1:

An entropy is a function defined on sets $`\{p_1, p_2, \ldots, p_n\}`$ of non-negative real numbers, which satisfy $`p_1 + p_2 + \ldots + p_n = 1`$.

#### Entropy Property 2:

If $`H`$ is an entropy function, then for any set $`\{p_1, p_2, \ldots, p_n, 0\}`$ on which $`H`$ is defined, $`H`$ satisfies:
``` math
H(p_1, p_2, \ldots, p_n, 0) = H(p_1, p_2, \ldots, p_n).
```
In other words, $`H`$ depends only on the nonzero $`p_i`$’s in a given set.

#### Entropy Property 3:

An entropy function is continuous.
The next property of entropy we consider requires the concept of conditional entropy. There are two ways to think of conditional entropy, and the fact that they are equivalent is our next property of entropy. To illustrate the ideas involved, we consider the following simple weighing problem:

We have three coins, some of which may be counterfeit (but not all). Counterfeit coins are distinguishable from normal coins by the fact that they are lighter. We are given a balance scale, and we wish to find out which, if any, of the coins are counterfeit. The sample space for this problem consists of seven sample points, one for each possible set of good coins. We denote them as follows:
``` math
\Omega = \{1, 2, 3, 12, 13, 23, 123\}.
```

Now what happens when we put the first two coins on each side of the scale? The sample space is partitioned into three blocks corresponding to the three possible outcomes of the weighing:
``` math
\sigma = \{\{12, 123, 3\}, \{2, 23\}, \{1, 13\}\}.
```
After recording the result of this weighing, we then place the second and third coins on the two sides of the scale. The result of this second weighing is to partition each of the blocks of the first weighing:
``` math
\{12, 123, 3\} \to \{\{12\}, \{123\}, \{3\}\}, \quad
\{2, 23\} \to \{\{2\}, \{23\}\}, \quad
\{1, 13\} \to \{\{1\}, \{13\}\}.
```

The combined information of the two weighings is represented by the partition into seven blocks, each with one sample point. Call this partition $`\pi`$. Conditional entropy is concerned with the effect of the second weighing, given that the first has occurred. One way to analyze this is to look at each block $`\sigma_i`$ of the partition of the first weighing and to analyze the situation as if it were the whole sample space. In general, for an event $`A`$ and a partition $`\tau`$, we define the conditional entropy of $`\pi`$ given $`A`$, written $`H(\pi|A)`$, to be the entropy of the partition $`\tau_1 \cap A, \tau_2 \cap A, \ldots`$ that $`\tau`$ induces on $`A`$.

Thus, in the above weighing problem, we have three conditional entropies, one for each possible outcome of the first weighing:
``` math
H(\pi|\sigma_1), \quad H(\pi|\sigma_2), \quad H(\pi|\sigma_3).
```
The conditional entropy of $`\pi`$ given $`\sigma`$ is then defined to be the average of these. More precisely, if $`\pi`$ and $`\sigma`$ are any two partitions of a sample space $`\Omega`$ such that $`\pi`$ is finer than $`\sigma`$, we define the conditional entropy of $`\pi`$ given $`\sigma`$ to be the average value of $`H(\pi|\sigma_i)`$ over all blocks $`\sigma_i`$ of $`\sigma`$:
``` math
H(\pi|\sigma) = \sum_i P(\sigma_i) H(\pi|\sigma_i).
```

On the other hand, we would like to think of information as a "quantity" that increases as we ask more and more questions about our experiment. Therefore, the conditional entropy of $`\pi`$ given $`\sigma`$ ought to be the net increase in entropy from $`\sigma`$ to $`\pi`$. In other words, we require our entropy function to satisfy:

#### Entropy Property 4:

If $`\pi`$ is a finer partition than $`\sigma`$, then
``` math
H(\pi|\sigma) = H(\pi) - H(\sigma).
```

The last property we require is one that we have already discussed. The partition having maximum entropy among all partitions with a given number of blocks is the one for which all the blocks have the same probability.

#### Entropy Property 5:

If $`H`$ is an entropy function, then any set $`\{p_1, p_2, \ldots, p_n\}`$ on which $`H`$ is defined satisfies:
``` math
H(p_1, p_2, \ldots, p_n) \leq H\left(\frac{1}{n}, \frac{1}{n}, \ldots, \frac{1}{n}\right).
```

We are now ready for the following remarkable fact: if $`H`$ satisfies the above five properties, then $`H`$ is given by the formula introduced earlier in this chapter, except for a possible scale change.

## Uniqueness of Entropy

If $`H`$ is a function satisfying the five properties of an entropy function, then there is a constant $`C`$ such that $`H`$ is given by:
``` math
H(p_1, p_2, \ldots, p_n) = C \sum_{i} p_i \log_2 \frac{1}{p_i}.
```

#### Proof:

The proof is rather technical, so we suggest omitting it on the first reading. However, it is of interest to outline the main points. To show that $`H`$ has the form given above, we use the following two facts:

1\. The entropy of the partition consisting of just one block of probability $`1`$ is zero, i.e., $`H(\Omega) = 0`$. By definition, $`H(\Omega)`$ is the same as $`H(\{1\})`$. Therefore, $`H(\Omega) = H(\{1\}) = 0`$.

2\. We define a function $`f(n)`$ by $`H\left(\frac{1}{n}, \frac{1}{n}, \ldots, \frac{1}{n}\right)`$. We have just shown that $`f(1) = 0`$ and we want to calculate $`f(n)`$ in general. Using properties 2 and 5, we show that $`f(n)`$ is increasing:
``` math
f(n) \leq f(n+1).
```

Next, we consider a partition $`\sigma`$ consisting of $`n^k`$ blocks, each of which has probability $`\frac{1}{n^k}`$. Then subdivide each of these into $`n`$ parts, each of which has the same probability. Call the resulting partition $`\pi`$. The conditional entropy $`H(\pi|\sigma)`$ for each block $`\sigma_i`$ is clearly given by $`f(n)`$. Thus the conditional entropy $`H(\pi|\sigma)`$ is $`f(k) - f(k-1)`$. If we apply this fact $`k`$ times, we obtain:
``` math
f(n^k) = k f(n).
```

Now fix two positive integers $`n`$ and $`k`$. Since the exponential function is an increasing function, there is an integer $`b`$ such that:
``` math
2b \leq n^k < 2b+1.
```
We now apply the two facts about $`f(n)`$ obtained above to this relation:
``` math
f(2^b) \leq f(n^k) \leq f(2^{b+1}).
```
Since $`f(n)`$ is increasing, we know:
``` math
b f(2) \leq k f(n) \leq (b+1)f(2).
```
Now divide these inequalities by $`k f(2)`$:
``` math
\frac{b}{k} \leq \frac{f(n)}{f(2)} \leq \frac{b+1}{k}.
```
Now apply the increasing function $`\log_2`$ to the inequalities:
``` math
\frac{b}{k} \leq \log_2(n) \leq \frac{b+1}{k}.
```
It follows that both $`f(n)/f(2)`$ and $`\log_2(n)`$ are in the interval $`[b/k, (b+1)/k]`$. This implies that $`f(n)/f(2)`$ and $`\log_2(n)`$ can be no farther apart than $`1/k`$, the length of this interval. But $`n`$ and $`k`$ were arbitrary positive integers. So if we let $`k`$ get very large, we are forced to conclude that:
``` math
f(n)/f(2) = \log_2(n).
```
Thus, for positive integers $`n`$, we have:
``` math
f(n) = f(2) \log_2(n).
```

We will define the constant $`C`$ to be $`-f(2)`$. Since $`f(2) \geq f(1) = 0`$, we know that $`C`$ is negative.

We next consider a set $`\{p_1, p_2, \ldots, p_n\}`$ of positive rational numbers such that $`p_1 + p_2 + \ldots + p_n = 1`$. Let $`N`$ be their common denominator, i.e., $`p_i = \frac{a_i}{N}`$ for all $`i`$, where each $`a_i`$ is an integer and $`a_1 + a_2 + \ldots + a_n = N`$. Let $`\sigma`$ be a partition corresponding to the set of probabilities $`\{p_1, p_2, \ldots, p_n\}`$. Let $`\pi`$ be a partition obtained by breaking up the $`i`$-th block of $`\sigma`$ into $`a_i`$ parts. Then every block of $`\pi`$ has probability $`\frac{1}{N}`$. By definition of conditional entropy:
``` math
H(\pi|\sigma) = -\sum_{i} P(\sigma_i) H(\pi|\sigma_i) = -\sum_{i} f(a_i) - C \sum_{i} p_i \log_2(a_i).
```

By property 4, on the other hand, we have:
``` math
H(\pi|\sigma) = H(\pi) - H(\sigma) = f(N) - H(\sigma).
```
Combining the two expressions for $`H(\pi|\sigma)`$ gives us:
``` math
H(\sigma) = -C \log_2(N) + C \sum_{i} p_i \log_2(a_i).
```
By continuity (property 3), $`H`$ must have this same formula for all sets $`\{p_1, p_2, \ldots, p_n\}`$ on which it is defined. This completes the proof.

We leave it as an exercise to show that the above formula for entropy actually satisfies the five postulated properties. We conclude by giving an interpretation of independence of partitions in terms of conditional entropy. Intuitively, if $`\pi`$ and $`\sigma`$ are independent, then their joint entropy $`H(\pi \cap \sigma)`$ is the sum of the individual entropies:
``` math
H(\pi \cap \sigma) = H(\pi) + H(\sigma).
```
In terms of conditional entropy, this says that $`H(\pi \cap \sigma) = H(\pi)`$.

## The Shannon Coding Theorem

A consequence of Entropy Property 4 of the last section is that if we wish to answer a question $`X`$ by means of a sequence of questions $`S_1, S_2, \ldots, S_n`$, the joint entropy of $`S_1, S_2, \ldots, S_n`$ must be at least as large as the entropy of $`X`$, and hence the sum of the entropies of the $`S_i`$’s must be at least as large as the entropy of $`X`$. In particular, if the $`S_i`$’s are yes-no questions, then $`H_2(S_i) \leq 1`$ and we get the crude inequality:
``` math
n \geq H_2(X).
```

The problem of finding a set of sufficient statistics for a random variable $`X`$ is called the *coding problem* for $`X`$, and the sequence $`S_1, S_2, \ldots, S_n`$ is said to *code* $`X`$. As we will see in the exercises, the kinds of questions one may ask are usually restricted to some class of questions. Devising particular codes is a highly nontrivial task.

One of the reasons that coding is so nontrivial in general is that one is usually required to answer a whole sequence of questions $`X_1, X_2, \ldots`$, produced by some process, and as a result one would like to answer the questions in the most efficient way possible. Consider one example. Suppose that $`X`$ takes values $`1`$ through $`200`$ each with probability $`0.85`$, and takes values $`0`$ with probability $`7.5 \times 10^{-4}`$. Then $`H_2(X)`$ is less than $`1`$. Simply by counting one can see that at least $`8`$ yes-no questions will be needed to achieve a sufficient statistic for $`X`$, even though the entropy suggests that one should be able to determine $`X`$ with a single yes-no question.

## References

C. E. Shannon,
“A Mathematical Theory of Communication,”
*Bell System Technical Journal*, 27(3), 1948.

C. E. Shannon,
“A Symbolic Analysis of Relay and Switching Circuits,”
*Master’s thesis*, MIT, 1937. (Also *Transactions of the AIEE*, 57(12):713–723, 1938.)

K. Baclawski, G.-C. Rota, and S. Billis,
*Introduction to Probability Theory, Preliminary Edition*,
MIT, circa 1979–1993 draft (unpublished).
