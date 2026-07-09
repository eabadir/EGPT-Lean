# Cross-Reference Table — Build Plan

*For parallelized execution via Claude Code agents*

## Objective

Build a structured cross-reference that lets a developer who clones this repo start from a question they already care about — "Can a machine replace a mathematician?" — and follow a thread that pulls them through Gödel writing to a dying von Neumann, through a 26-year-old von Neumann telling Gödel he's wrong about the limits of formalism, through Ulam and Rota walking through Santa Fe talking about the barrier of meaning, and land in a specific Lean theorem with a specific polynomial bound that answers the question they started with.

The philosophical issues are not taxonomy labels. They are **doors anyone would walk through**. Each door opens onto a thread: a human question → a historical moment → a mathematical claim → a line of code.

## Output Files

1. **`18.313x/cross_reference.jsonl`** — Machine-readable cross-reference (one JSON line per event)
2. **`18.313x/CROSS_REFERENCE.md`** — Human-readable rendering grouped by question/thread

## Schema

Each line in `cross_reference.jsonl`:

```json
{
  "event_id": "C9",
  "event_type": "consensus",
  "event_text": "The von Neumann–Gödel 1931 parallel is the correct frame...",
  "exchange": 12,
  "thread": "can_you_formalize_intuition",
  "thread_name": "Can You Formalize Intuition?",
  "letters": [
    {
      "file": "content/SSG_History/JvM_Letters/Letter3_Jan12_1931.md",
      "author": "von Neumann",
      "date": "1931-01-12",
      "excerpt_marker": "I absolutely disagree with your view on the formalizability of intuitionism"
    }
  ],
  "lean_refs": [
    {
      "file": "Lean/EGPT/InformationTheory/Complexity/PPNP.lean",
      "symbol": "P_eq_NP",
      "comment": "P and NP receive identical definitions. The proof is Set.ext + Iff.rfl. Von Neumann was right."
    }
  ],
  "historical_context": "A 26-year-old von Neumann told Gödel: name one intuitionistic construction that resists formalization, or accept that it can all be axiomatized. Gödel never produced a counterexample. 95 years later, the Lean skeptic reached the same wall: 'The code is clean. The types are standard. I have no line to cite.'"
}
```

## Narrative Threads (the doors)

These are the questions a developer walks through. Each thread connects a universally compelling human question → historical letters/documents → the mathematical issue at stake → specific Lean code that resolves (or sharpens) it.

---

### Thread 1: "Can a Machine Replace a Mathematician?"
**Key:** `can_a_machine_think`

**The human question:** If you could build a machine that searches for proofs, would it make human mathematical reasoning obsolete?

**The historical moment:** Gödel, March 20, 1956, writing to a dying von Neumann: "If the answer were affirmative, it would mean that the mental work of the mathematician concerning yes-or-no questions could be completely replaced by a machine." He conjectured the bound was φ(N) ≤ KN². Von Neumann died before he could answer.

**The mathematical issue:** Is there a polynomial bound on proof search? This is P vs NP in its original, pre-Cook-Levin form — not about SAT solvers, but about whether thought itself has a shortcut.

**The code:** The Lean proof chain answers with `walk_complexity_le_nSquared` — the walk cost is bounded by |cnf| × k ≤ n². Gödel guessed KN². The code says ≤ n². The bound is the same.

**Primary letters:**
- `Godel_Letter_to_Von_Neumann.md` (1956) — "φ(N) ≤ KN²"
- `JvM_vs_Godel_EGPT_History.md` — Narrative connecting 1956 to the code

**Primary Lean symbols:**
- `walkComplexity_upper_bound` (TableauFromCNF.lean) — Walk cost ≤ |cnf| × k
- `walk_complexity_le_nSquared` (PPNP.lean) — |cnf| × k ≤ n²
- `canonical_n_squared_bound` (PPNP.lean) — The polynomial is n²
- `P_eq_NP` (PPNP.lean) — The theorem Gödel was asking about

**Debate events:** C2, C12, C13, Y1, Y5, F2, F5, I5, I6, IN3, IN7, IN13, OQ1

---

### Thread 2: "Can You Formalize Intuition?"
**Key:** `can_you_formalize_intuition`

**The human question:** Is there something about how humans think — call it intuition, construction, insight — that can never be captured in a formal system? Or can everything we do be written down as rules?

**The historical moment:** Von Neumann to Gödel, January 12, 1931: "I absolutely disagree with your view on the formalizability of intuitionism... is it not a fact, that not a single construction of the kind mentioned is known that cannot be formalized?" Gödel believed formal systems have inherent limits (his own incompleteness theorems). Von Neumann believed the limits were of particular formalisms, not of formalization itself.

**The mathematical issue:** Does EGPT's Lean formalization capture the real P vs NP problem, or is it a different problem dressed in the same clothes? This is the 1931 dispute transposed to 2026: the skeptic says "your formalism doesn't capture the concept," the advocate says "name one construct that a complexity theorist would reject."

**The code:** After 21 exchanges, the AI skeptic conceded (Y14): "The code is clean. The types are standard. I have no line to cite." Every construct uses standard mathlib types (C26). The remaining objection is about which formalization tradition to prefer, not mathematical validity (C27). Exactly where von Neumann and Gödel left things in 1931.

**Primary letters:**
- `Letter3_Jan12_1931.md` — "I absolutely disagree"
- `Letter1_Nov20_1930.md` — Von Neumann's independent discovery of second incompleteness

**Primary Lean symbols:**
- `P_eq_NP` (PPNP.lean) — sorry-free, uses only standard mathlib types
- `P_eq_NP` (PPNP.lean) — The constructive chain's capstone

**Debate events:** C1, C8, C9, C26, C27, Y2, Y4, Y14, IN2, IN19, IN20

---

### Thread 3: "Does Stating a Problem Solve It?"
**Key:** `does_stating_solve`

**The human question:** If you could describe a problem with perfect precision — every constraint, every variable, every relationship — would the answer already be contained in the description? Is "searching" for solutions an illusion created by imprecise descriptions?

**The historical moment:** This is the deepest thread — it runs from Rota and Ulam in Santa Fe ("what you are describing is not an object, but a function, a role that is inextricably tied to some context — take away the context, and the meaning also disappears") through von Neumann's constructivism ("the search IS the construction") to EGPT's central principle: "the address is the map."

**The mathematical issue:** In EGPT's information space, defining a CNF formula with k variables and n clauses creates a structure whose address space has exactly |cnf| × k navigable locations. Walking this address space IS solving the problem. The walk doesn't search for the answer — it reads the answer that the problem statement already encodes.

**The code:** `ndmCircuitEval_eq_evalCNF` (UTM.lean) — the NDM circuit IS evalCNF in address space. Defining the circuit defines the evaluation. `ndmAddressWalk` walks literal addresses (2k per clause, polynomial), not assignment bit-strings (2^k, exponential). The three-layer equivalence (C23): Boolean ↔ address ↔ entropy ↔ prime, all sorry-free.

**Primary letters:**
- `The_Barrier_of_Meaning_Rota.md` — Ulam: "what you are describing is not an object, but a function"
- `Letter3_Jan12_1931.md` — Von Neumann's constructivism

**Primary Lean symbols:**
- `ndmCircuitEval_eq_evalCNF` (UTM.lean) — Circuit = evalCNF in address space
- `ndmAddressWalk` (UTM.lean) — Endpoint-free walk over literal addresses
- `literalAddress` (UTM.lean) — Maps each literal to 2k addresses
- `three_equivalent_sat_formulations` (PPNP.lean) — Boolean = prime = walk

**Debate events:** C4, C5, C17, C18, C20, C23, C25, Y11, Y13, IN12, IN18, I19, I22-I26

---

### Thread 4: "Is There Only One Way to Measure Information?"
**Key:** `one_measure_of_information`

**The human question:** When you measure how much a message tells you — whether it's a DNA sequence, a radio signal, a thermometer reading, or a mathematical proof — are all these measurements fundamentally the same thing? Or are there many different kinds of information?

**The historical moment:** Gian-Carlo Rota spent thirty years at MIT teaching an unpublished 400-page manuscript whose capstone was the proof that the logarithm is the unique information measure satisfying seven natural axioms. All valid entropy — Boltzmann's (physics), Gibbs's (statistical mechanics), von Neumann's (quantum), Shannon's (information theory) — is a scalar multiple of Shannon entropy. Rota told his student Essam Abadir never to say he was working on "AI" because people would think he was crazy, then pointed him to von Neumann's *The Computer and the Brain*.

**The mathematical issue:** If all entropy is Shannon entropy, then physics IS information theory. Computation IS physics. The bridge is the logarithm, and Rota proved there is no other. The chain rule decomposes H(CNF) clause-by-clause. The conditional entropy H(k|p) equals GCD in prime space. The rigidity of zero: sum of non-negative independent conditional entropy terms = 0 iff each = 0.

**The code:** `RET_All_Entropy_Is_Scaled_Shannon_Entropy` (RET.lean) — all 7 axioms. `canonical_entropy_has_rota_properties` (PPNP.lean) bundles them. `canonical_entropy_bounded_by_log` — H(p) ≤ H(uniform) for ANY distribution (not just uniform — this resolved the skeptic's uniformity objection). `conditional_entropy_gcd_characterization` — GCD ↔ entropy = 0.

**Primary letters/documents:**
- `The_Barrier_of_Meaning_Rota.md` — Rota on Ulam, the barrier of meaning
- `Ulam_Rota_Discuss_Von_Neumann.md` — Ulam and Rota on von Neumann's breadth
- `JvM_vs_Godel_EGPT_History.md` — Rota's 30-year manuscript → RET.lean

**Primary Lean symbols:**
- `RET_All_Entropy_Is_Scaled_Shannon_Entropy` (Entropy/RET.lean) — The capstone
- `canonical_entropy_bounded_by_log` (PPNP.lean) — H ≤ H(uniform) for all distributions
- `conditional_entropy_gcd_characterization` (Decomposition.lean) — GCD ↔ zero entropy
- `h_canonical_is_cond_add_sigma` (Entropy/H.lean) — Chain rule as proven log identity
- `ndmEntropyWalk_total_eq` (UTM.lean) — Walk entropy = conditionalCNFEntropy

**Debate events:** C3, C6, C7, C14, C15, C17, C19, C21, C24, Y9, IN5, IN6, IN8, IN11, IN16, IN17, I1, I4, I8-I14, I21, OQ2, OQ6

---

### Thread 5: "Can You Ask About Something That Doesn't Exist?"
**Key:** `asking_about_nothing`

**The human question:** If you ask me to find something in a room, and the thing isn't in the room, how much work should I do before I'm allowed to say "it's not here"? Is the work of proving absence fundamentally different from the work of finding presence?

**The historical moment:** This thread has no single letter — it's the insight that emerged from the debate itself. The Cantor diagonal argument (and Gödel's incompleteness proof, which uses the same technique) works by constructing something that "should" exist but doesn't. EGPT's response: in maximally compressed space, asking about a zero-probability event is asking about nothing. Rota's `IsEntropyZeroInvariance` says appending a zero-probability outcome doesn't change the entropy. You can't extract information from what isn't there.

**The mathematical issue:** UNSAT instances are zero-probability events in information space. `IsEntropyZeroInvariance` (appending p=0 doesn't change H) and `IsEntropyZeroOnEmptyDomain` (H(∅)=0) together say: the absence of a solution contributes no information to extract. The walk reaches an empty domain, and the entropy is zero. The work of proving absence IS the work of walking the address space and finding it empty.

**The code:** `IsEntropyZeroInvariance` and `IsEntropyZeroOnEmptyDomain` (Entropy/Common.lean). `walk_empty_domain_implies_zero_entropy` (PPNP.lean). `unsat_detected_by_prime_structure` (Decomposition.lean) — UNSAT detected via prime factorization, no enumeration needed.

**Primary Lean symbols:**
- `IsEntropyZeroInvariance` (Entropy/Common.lean) — Adding a zero-probability event changes nothing
- `IsEntropyZeroOnEmptyDomain` (Entropy/Common.lean) — H(∅) = 0
- `walk_empty_domain_implies_zero_entropy` (PPNP.lean) — Walk finds empty → entropy is zero
- `unsat_detected_by_prime_structure` (Decomposition.lean) — UNSAT via primes
- `ndmEntropyWalk_determines_sat` (UTM.lean) — Entropy = 0 ↔ evalCNF = true

**Debate events:** C7, C24, Y3, IN1, IN2, IN16, I2, I3, OQ2

---

### Thread 6: "Is the Universe Built from Numbers?"
**Key:** `universe_from_numbers`

**The human question:** Is reality made of smooth, continuous stuff — fields, waves, flows — or is it made of discrete, countable things: particles, atoms, bits? If you could zoom in far enough, would you find equations or would you find integers?

**The historical moment:** Einstein, 1954, a year before his death, to Michele Besso: "I consider it quite possible that physics cannot be based on the field concept, i.e., on continuous structures." To David Bohm: "I have not the slightest idea what kind of elementary concepts could be used in such a theory." Von Neumann, on his deathbed, writing about "a radically divergent system of notation" — a stochastic computer operating at 2-3 decimal digits of precision with "statistical" message passing. Two of the greatest minds of the 20th century reaching the same conclusion from opposite directions: their life's work was built on the wrong foundation.

**The mathematical issue:** EGPT's ParticlePath = List Bool = ℕ. A natural number IS a particle's random walk through a discrete grid. The hierarchy: ParticlePath ↔ ℕ, ChargedParticlePath ↔ ℤ, ParticleHistoryPMF ↔ ℚ, ParticleFuturePDF ↔ ℝ. Each level carries the correct Beth cardinality. Shannon compression: 2^t_i paths compress to t_i+1 addresses. The address space is linear, not exponential.

**The code:** `equivParticlePathToNat` (NumberTheory/Core.lean). `PathCompress_AllTrue` (Core.lean) — maximal compression, one unique ParticlePath per length. `Shannon compression` at C18: 2^t_i → t_i+1. The PPF number representation in EGPTMath: every number stored as its prime power factorization, literally Shannon coding applied to number representation.

**Primary letters/documents:**
- `Einstein_Field_Theory.md` — "nothing remains of my entire castle in the air"
- `JvM_vs_Godel_EGPT_History.md` — Von Neumann's stochastic computer, Einstein's discrete physics
- `The_Mathematician_JvM.md` — Mathematics and natural science
- `Ulam_Rota_Discuss_Von_Neumann.md` — Ulam on von Neumann's vision

**Primary Lean symbols:**
- `equivParticlePathToNat` (NumberTheory/Core.lean) — ParticlePath ↔ ℕ bijection
- `PathCompress_AllTrue` (Core.lean) — Maximal compression
- `assignmentCompositePrime` (Decomposition.lean) — Assignments as prime composites

**Debate events:** C18, C25, Y10, IN9, IN11, F7

---

### Thread 7: "What Makes a Proof Valid?"
**Key:** `what_makes_proof_valid`

**The human question:** If two people agree on every fact but disagree on whether those facts constitute a proof, who's right? Is "proof" something objective, or does it depend on which rules you agreed to play by?

**The historical moment:** This is where the debate ended — and where von Neumann and Gödel ended in 1931. Von Neumann: name one construction that can't be formalized. Gödel: the concept of "intuitionistic construction" is itself unformalizable. Neither was wrong. They were disagreeing about the rules, not the game. In 2026, after 21 exchanges: the skeptic concedes every technical point but holds that standard complexity theory defines P via Turing machines, and EGPT defines it via certificates. The skeptic says: "The code is clean. The types are standard. I have no line to cite." But the definition of P is different.

**The mathematical issue:** Standard P = decidable in poly-time by a DTM. EGPT's P = existence of a polynomially-bounded SatisfyingTableau. Standard NP = existence of a poly-bounded certificate verifiable in poly-time. EGPT's NP = same predicate. When P and NP have the same definition, P=NP is definitional. The question is: is EGPT's definition the right one?

**The code:** `P` vs `P` (PPNP.lean vs PPNP.lean). The walk construction makes certificate cost = verification cost. `walk_construction_iff_bounded_certificate` (PPNP.lean) — the bridge theorem. `time_eq_information_eq_complexity` (UTM.lean) — the RECT identity: time = information = complexity.

**Primary letters:**
- `Letter3_Jan12_1931.md` — "intuitionism is undefined and undefinable"
- `Godel_Letter_to_Von_Neumann.md` — "the question of whether there exists a finite procedure"
- `IntroComments_02_Logic_and_Foundations.md` — Editorial context on the dispute

**Primary Lean symbols:**
- `P` (PPNP.lean) — Certificate-based P
- `NP` (PPNP.lean) — Same predicate as P
- `P_eq_NP` (PPNP.lean) — The equality
- `walk_construction_iff_bounded_certificate` (PPNP.lean) — Walk = certificate
- `time_eq_information_eq_complexity` (UTM.lean) — RECT: time = information

**Debate events:** C10, C22, C27, Y4, Y8, Y12, Y14, IN7, IN15, IN20, F4, OQ9

---

### Thread 8: "Why Does This Cost So Much?"
**Key:** `why_so_expensive`

**The human question:** We're boiling rivers to cool data centers. We're spending more electricity on AI than some countries use in total. Is this inevitable, or are we doing something fundamentally wrong?

**The historical moment:** Von Neumann, dying, wrote that his computer architecture was wrong. He wanted a machine that operates "not in the digital but in the statistical domain" — 2-3 decimal digits of precision, statistical message passing, "a lower level of arithmetical precision but a higher level of logical reliability." We ignored this and built a trillion-dollar industry on his first design. EGPT says: the cost comes from floating-point arithmetic. FLOPs are the wrong unit. The right unit is IOPs — integer operations. Exact arithmetic, no error accumulation, no rounding, no IEEE 754.

**The mathematical issue:** The exponential blowup in computation comes from representing problems in the wrong space. 2^k assignments in Boolean space compress to k × |cnf| walk steps in address space (C18, Y10). The walk in address space costs |cnf| × k ≤ n² (C2). The Shannon Coding Theorem compresses 2^t_i binary tree paths into t_i+1 ParticlePath addresses. The exponential was always an artifact of the representation, not the problem.

**The code:** EGPTMath — 157 tests, zero floating-point operations. `walkComplexity_upper_bound` — the walk cost is polynomial, not exponential. `ndmAddressWalk` operates on 2k literal addresses per clause, not 2^k assignment bit-strings. `PathCompress_AllTrue` — maximal compression.

**Primary letters/documents:**
- `JvM_vs_Godel_EGPT_History.md` — "a radically divergent system of notation"
- `The_Mathematician_JvM.md` — Mathematics and its relationship to science

**Primary Lean symbols:**
- `walkComplexity_upper_bound` (TableauFromCNF.lean) — Walk cost ≤ |cnf| × k
- `ndmWalkComplexity_polynomial` (UTM.lean) — NDM walk is polynomial
- `walk_per_clause_cost_independent_of_history` (UTM.lean) — Cost independent of history
- `deterministicBreadth_cost_le_nSquared` (UTM.lean) — n² bound

**Debate events:** C2, C18, C20, Y10, Y11, F1, F6, IN9, IN10, IN14, I19, I20, OQ3, OQ7

---

### Thread 9: "Does Every Part Reveal the Whole?"
**Key:** `parts_reveal_whole`

**The human question:** If you break something into pieces and examine each piece separately, can you always reconstruct the whole? Or are there wholes that are more than the sum of their parts — things you can only understand by looking at everything at once?

**The historical moment:** This is the deep mathematical content of EGPT — prime factorization makes consistency local. The Fundamental Theorem of Arithmetic guarantees unique decomposition. It's the mathematical formalization of a very old intuition: if every piece is consistent, the whole must be consistent. (And the contrapositive: if any piece is inconsistent, you can detect it locally without examining the whole.)

**The mathematical issue:** `evalLiteral_true_iff_literalSharesFactor` — each literal's truth value is checkable via a single prime divisibility test. `consistency_is_local` — local literal checks determine global CNF satisfiability. The four-way equivalence: Boolean evaluation = prime divisibility = zero conditional entropy = GCD captures the prime. Each literal is independent under conditioning by the composite (sufficient statistic).

**The code:** The prime factorization layer in Decomposition.lean. `assignmentCompositePrime` maps assignments to composites. `evalCNF_true_iff_cnfSharesFactor` bridges Boolean and prime worlds. `cnfSharesFactor_iff_zero_conditional_cnf_entropy` bridges prime and entropy worlds. The rigidity of zero (C24): sum of non-negative independent terms = 0 iff each = 0.

**Primary Lean symbols:**
- `evalLiteral_true_iff_literalSharesFactor` (Decomposition.lean) — Literal eval = prime divisibility
- `consistency_is_local` (PPNP.lean) — Local checks determine global truth
- `cnfSharesFactor_iff_zero_conditional_cnf_entropy` (Decomposition.lean) — Prime ↔ entropy bridge
- `evalCNF_true_iff_cnfSharesFactor` (Decomposition.lean) — Boolean ↔ prime bridge
- `literalSharesFactor_iff_zero_conditional_entropy` (Decomposition.lean) — Literal-level entropy bridge

**Debate events:** C4, C5, C13, C16, C23, C24, Y7, Y13, IN3, IN4, IN5, IN9, IN18, F3, I7, I15-I18, OQ5, OQ8

---

## Event-to-Thread Mapping

Below is the complete mapping of all 82 debate events to their primary thread(s). Each event maps to 1-2 threads.

### Consensus Points (C1-C27)

| Event | Primary Thread | Secondary Thread |
|-------|---------------|-----------------|
| C1 | `can_you_formalize_intuition` | |
| C2 | `can_a_machine_think` | `why_so_expensive` |
| C3 | `one_measure_of_information` | |
| C4 | `parts_reveal_whole` | `does_stating_solve` |
| C5 | `parts_reveal_whole` | `does_stating_solve` |
| C6 | `one_measure_of_information` | |
| C7 | `asking_about_nothing` | `one_measure_of_information` |
| C8 | `can_you_formalize_intuition` | |
| C9 | `can_you_formalize_intuition` | |
| C10 | `what_makes_proof_valid` | `can_you_formalize_intuition` |
| C11 | `universe_from_numbers` | |
| C12 | `can_a_machine_think` | |
| C13 | `can_a_machine_think` | `parts_reveal_whole` |
| C14 | `one_measure_of_information` | `parts_reveal_whole` |
| C15 | `one_measure_of_information` | |
| C16 | `parts_reveal_whole` | `one_measure_of_information` |
| C17 | `one_measure_of_information` | `does_stating_solve` |
| C18 | `universe_from_numbers` | `why_so_expensive` |
| C19 | `one_measure_of_information` | |
| C20 | `why_so_expensive` | `does_stating_solve` |
| C21 | `one_measure_of_information` | `asking_about_nothing` |
| C22 | `why_so_expensive` | `what_makes_proof_valid` |
| C23 | `does_stating_solve` | `parts_reveal_whole` |
| C24 | `asking_about_nothing` | `parts_reveal_whole` |
| C25 | `universe_from_numbers` | `does_stating_solve` |
| C26 | `can_you_formalize_intuition` | `what_makes_proof_valid` |
| C27 | `what_makes_proof_valid` | `can_you_formalize_intuition` |

### Concessions (Y1-Y14)

| Event | Primary Thread | Secondary Thread |
|-------|---------------|-----------------|
| Y1 | `can_a_machine_think` | |
| Y2 | `can_you_formalize_intuition` | |
| Y3 | `asking_about_nothing` | |
| Y4 | `what_makes_proof_valid` | `can_you_formalize_intuition` |
| Y5 | `can_a_machine_think` | |
| Y6 | `universe_from_numbers` | |
| Y7 | `parts_reveal_whole` | |
| Y8 | `what_makes_proof_valid` | |
| Y9 | `one_measure_of_information` | |
| Y10 | `why_so_expensive` | `universe_from_numbers` |
| Y11 | `why_so_expensive` | `does_stating_solve` |
| Y12 | `what_makes_proof_valid` | `why_so_expensive` |
| Y13 | `does_stating_solve` | `parts_reveal_whole` |
| Y14 | `what_makes_proof_valid` | `can_you_formalize_intuition` |

### Insights (IN1-IN20)

| Event | Primary Thread | Secondary Thread |
|-------|---------------|-----------------|
| IN1 | `asking_about_nothing` | `does_stating_solve` |
| IN2 | `asking_about_nothing` | `can_you_formalize_intuition` |
| IN3 | `parts_reveal_whole` | `can_a_machine_think` |
| IN4 | `parts_reveal_whole` | |
| IN5 | `one_measure_of_information` | `parts_reveal_whole` |
| IN6 | `one_measure_of_information` | |
| IN7 | `what_makes_proof_valid` | `can_a_machine_think` |
| IN8 | `one_measure_of_information` | `why_so_expensive` |
| IN9 | `why_so_expensive` | `parts_reveal_whole` |
| IN10 | `why_so_expensive` | |
| IN11 | `universe_from_numbers` | `one_measure_of_information` |
| IN12 | `does_stating_solve` | |
| IN13 | `can_a_machine_think` | |
| IN14 | `why_so_expensive` | `one_measure_of_information` |
| IN15 | `what_makes_proof_valid` | `why_so_expensive` |
| IN16 | `asking_about_nothing` | `one_measure_of_information` |
| IN17 | `one_measure_of_information` | `does_stating_solve` |
| IN18 | `does_stating_solve` | `parts_reveal_whole` |
| IN19 | `can_you_formalize_intuition` | |
| IN20 | `what_makes_proof_valid` | `can_you_formalize_intuition` |

### Failed Approaches (F1-F7)

| Event | Primary Thread |
|-------|---------------|
| F1 | `why_so_expensive` |
| F2 | `can_a_machine_think` |
| F3 | `parts_reveal_whole` |
| F4 | `what_makes_proof_valid` |
| F5 | `can_a_machine_think` |
| F6 | `why_so_expensive` |
| F7 | `universe_from_numbers` |

### Implementations (I1-I26)

| Event | Primary Thread | Lean File |
|-------|---------------|-----------|
| I1 | `one_measure_of_information` | PPNP.lean |
| I2 | `asking_about_nothing` | PPNP.lean |
| I3 | `asking_about_nothing` | PPNP.lean |
| I4 | `one_measure_of_information` | PPNP.lean |
| I5 | `can_a_machine_think` | TableauFromCNF.lean |
| I6 | `can_a_machine_think` | TableauFromCNF.lean |
| I7 | `parts_reveal_whole` | Decomposition.lean |
| I8 | `one_measure_of_information` | PPNP.lean |
| I9 | `one_measure_of_information` | PPNP.lean |
| I10 | `one_measure_of_information` | PPNP.lean |
| I11 | `one_measure_of_information` | PPNP.lean |
| I12 | `one_measure_of_information` | PPNP.lean |
| I13 | `one_measure_of_information` | PPNP.lean |
| I14 | `one_measure_of_information` | PPNP.lean |
| I15 | `parts_reveal_whole` | Decomposition.lean |
| I16 | `parts_reveal_whole` | Decomposition.lean |
| I17 | `parts_reveal_whole` | Decomposition.lean |
| I18 | `parts_reveal_whole` | Decomposition.lean |
| I19 | `does_stating_solve` | UTM.lean |
| I20 | `why_so_expensive` | UTM.lean |
| I21 | `one_measure_of_information` | UTM.lean |
| I22 | `does_stating_solve` | UTM.lean |
| I23 | `does_stating_solve` | UTM.lean |
| I24 | `does_stating_solve` | UTM.lean |
| I25 | `does_stating_solve` | UTM.lean |
| I26 | `does_stating_solve` | UTM.lean |

### Open Questions (OQ1-OQ9)

| Event | Primary Thread |
|-------|---------------|
| OQ1 | `can_a_machine_think` |
| OQ2 | `asking_about_nothing` |
| OQ3 | `why_so_expensive` |
| OQ4 | `universe_from_numbers` |
| OQ5 | `parts_reveal_whole` |
| OQ6 | `one_measure_of_information` |
| OQ7 | `why_so_expensive` |
| OQ8 | `parts_reveal_whole` |
| OQ9 | `what_makes_proof_valid` |

---

## Parallelization Strategy

The build splits into 4 independent sub-agents plus 1 assembler:

### Agent 1: Letter Excerpts (`@letter-indexer`)
**Input:** All files in `content/SSG_History/` and `content/SSG_History/JvM_Letters/`
**Task:** For each of the 9 narrative threads, extract 1-3 short excerpt markers (< 15 words each, for fair-use lookup — just enough to locate the passage) from the relevant letters. The thread descriptions above name the primary letters and give the flavor of what to look for. Output: `18.313x/_build/letter_excerpts.jsonl`
**Schema per line:**
```json
{"thread": "can_a_machine_think", "file": "content/SSG_History/JvM_Letters/Godel_Letter_to_Von_Neumann.md", "author": "Gödel", "date": "1956-03-20", "excerpt_marker": "mental work of the mathematician could be completely replaced by a machine"}
```

### Agent 2: Lean Code References (`@lean-indexer`)
**Input:** All Lean files in proof chain (see file inventory below)
**Task:** For each of the 9 narrative threads, identify the key theorem/def names listed in the thread description. Verify each symbol exists by grepping the file. Get approximate line numbers. Write a 1-line comment that a non-specialist could understand — connect the symbol to the human question. Output: `18.313x/_build/lean_refs.jsonl`
**Schema per line:**
```json
{"thread": "can_a_machine_think", "file": "Lean/EGPT/InformationTheory/Complexity/PPNP.lean", "symbol": "walk_complexity_le_nSquared", "line": 127, "comment": "The walk cost is ≤ n². Gödel guessed KN² in his 1956 letter. The bound is the same."}
```

### Agent 3: Historical Context (`@context-writer`)
**Input:** All historical documents, the thread descriptions above
**Task:** For each of the 9 narrative threads, write the "historical context" paragraph that will appear in the cross-reference. This is the bridge between the human question, the historical letters, and the code. 2-4 sentences. Should be evocative and precise — a developer reading this should feel the weight of the history and see exactly how it connects to the theorem they're about to look at. Output: `18.313x/_build/historical_context.jsonl`
**Schema per line:**
```json
{"thread": "can_a_machine_think", "context": "Gödel wrote to a dying von Neumann on March 20, 1956: can a machine running in polynomial time replace mathematical reasoning? He conjectured φ(N) ≤ KN². Von Neumann died before he could answer. 70 years later, walk_complexity_le_nSquared proves the walk cost is bounded by |cnf| × k ≤ n². The bound Gödel guessed is the bound the code proves."}
```

### Agent 4: Event-Thread Mapping Validator (`@mapping-validator`)
**Input:** `debate_log.jsonl`, the mapping tables above
**Task:** For each of the 82 events, verify the thread assignment makes sense by reading the event text and cross-checking against the thread descriptions. Flag any that seem misassigned. Output: `18.313x/_build/mapping_validation.jsonl`

### Assembler: Cross-Reference Builder (`@xref-assembler`)
**Runs after Agents 1-4 complete.**
1. Join the data: for each of the 82 events, attach thread(s), letter excerpts, lean refs, and historical context
2. Write `18.313x/cross_reference.jsonl` (one line per event, full schema)
3. Generate `18.313x/CROSS_REFERENCE.md` organized by thread:
   - Thread name (the question)
   - Historical context paragraph
   - Letter references (file, author, date, excerpt marker)
   - Key Lean symbols (file, symbol, line, comment)
   - Table of debate events belonging to this thread
4. Verify completeness and file/symbol existence

---

## File Inventory for Agents

### Historical Letters (Agent 1 reads these)
```
content/SSG_History/JvM_Letters/Letter1_Nov20_1930.md          — JvM discovers 2nd incompleteness
content/SSG_History/JvM_Letters/Letter2_Nov29_1930.md          — JvM defers to Gödel
content/SSG_History/JvM_Letters/Letter3_Jan12_1931.md          — THE letter: "I absolutely disagree"
content/SSG_History/JvM_Letters/Letter4_Feb14_1933.md          — Later correspondence
content/SSG_History/JvM_Letters/Godel_Letter_to_Von_Neumann.md — 1956 proto-P-vs-NP letter
content/SSG_History/JvM_Letters/JvM_vs_Godel_EGPT_History.md   — Narrative connecting letters to EGPT
content/SSG_History/JvM_Letters/IntroComments_02_Logic_and_Foundations.md — Editorial on the dispute
content/SSG_History/The_Mathematician_JvM.md                    — JvM on math & natural science
content/SSG_History/The_Barrier_of_Meaning_Rota.md              — Rota on Ulam, AI, meaning
content/SSG_History/Ulam_Rota_Discuss_Von_Neumann.md            — Ulam & Rota reminisce about JvM
content/SSG_History/Einstein_Field_Theory.md                    — Einstein's discrete physics vision
```

### Lean Proof Chain Files (Agent 2 reads these)
```
Lean/EGPT/InformationTheory/Bridge.lean                                — ParticlePath, PathCompress_AllTrue
Lean/EGPT/InformationTheory/EntropyNumber/Basic.lean                   — ParticlePath ↔ ℕ bijection
Lean/EGPT/InformationTheory/EntropyNumber/RotaEntropy.lean             — Modernized RET capstone
Lean/EGPT/InformationTheory/Complexity/CNF.lean                        — CNF formulas, CanonicalCNF
Lean/EGPT/InformationTheory/Complexity/Core.lean                       — PathToConstraint, polynomial defs
Lean/EGPT/InformationTheory/Complexity/Tableau.lean                    — SatisfyingTableau, walkCNFPaths
Lean/EGPT/InformationTheory/Bridge.lean                                — Bridge between complexity and info
Lean/EGPT/InformationTheory/Complexity/PPNP.lean                       — P, NP, P_eq_NP
Lean/EGPT/InformationTheory/Complexity/Decomposition.lean              — AssignmentFreeSAT, CNFSharesFactor
Lean/EGPT/InformationTheory/Complexity/UTM.lean                        — NDM walks, circuit SAT, entropy walk
Lean/EGPT/InformationTheory/Complexity/PPNP.lean                       — P, NP, P_eq_NP (constructive)
Lean/EGPT/InformationTheory/Entropy/Axioms.lean                        — RECT/IRECT, Rota axiom structures
Lean/EGPT/InformationTheory/Entropy/Concrete.lean                      — 7 Rota axioms proven for Shannon
Lean/EGPT/InformationTheory/Entropy/Uniqueness.lean                    — Rota Entropy Theorem
```

### Debate State Files (All agents may reference)
```
18.313x/debate_log.jsonl      — 82 events (source of truth)
18.313x/DEBATE_STATE.md       — Compiled state
18.313x/01_QA.md - 13_QA.md   — Original 13-exchange history
```
