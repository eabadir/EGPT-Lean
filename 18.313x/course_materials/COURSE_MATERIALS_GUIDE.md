# 18.313x: Course Materials Guide

All materials live in the EGPT repository. This guide organizes them by type for instructor and student reference.

---

## Historical Readings

Primary sources — the actual letters, essays, and interviews that form the connective tissue of the course.

| Document | Location | Sessions | Description |
|----------|----------|----------|-------------|
| Gödel → von Neumann (1956) | `content/SSG_History/JvM_Letters/Godel_Letter_to_Von_Neumann.md` | 1, 9 | The proto-P-vs-NP letter: "Can a machine decide provability in N² steps?" |
| JvM → Gödel, Nov 20, 1930 | `content/SSG_History/JvM_Letters/Letter1_Nov20_1930.md` | 3 | Von Neumann's independent discovery of the 2nd incompleteness theorem |
| JvM → Gödel, Jan 12, 1931 | `content/SSG_History/JvM_Letters/Letter3_Jan12_1931.md` | 3, 8, 9 | "I absolutely disagree with your view on the formalizability of intuitionism" |
| JvM vs Gödel — Full Narrative | `content/SSG_History/JvM_Letters/JvM_vs_Godel_EGPT_History.md` | 1, 4, 10 | Complete narrative connecting the letters to EGPT |
| The Mathematician (JvM) | `content/SSG_History/The_Mathematician_JvM.md` | 0, 10 | Von Neumann on the nature of mathematics and natural science |
| Ulam & Rota Discuss von Neumann | `content/SSG_History/Ulam_Rota_Discuss_Von_Neumann.md` | 0, 3, 4, 5 | The interview: "merely a diagonal method," JvM's vision |
| The Barrier of Meaning (Rota) | `content/SSG_History/The_Barrier_of_Meaning_Rota.md` | 3, 5, 8 | Ulam on meaning, keys, passengers, and the word "as" |
| Einstein on Field Theory | `content/SSG_History/Einstein_Field_Theory.md` | 4 | "Nothing remains of my entire castle in the air, *and all of modern physics*" |
| Von Neumann's Precision Loss | `content/Notes/Precision Loss.md` | 0, 10 | "425 operations at 5% error = 1 billion degradation" |

---

## Lean 4 Proof Chain

Formal proofs — the code the student never reads but causes to exist. Organized by the session where each symbol first appears.

### Entropy (Sessions 3, 5)

| Symbol | File | Description |
|--------|------|-------------|
| `IsEntropyCondAddSigma` | `Lean/EGPT/InformationTheory/Entropy/Axioms.lean` | THE bedrock axiom: H(joint) = H(prior) + Σ prior(i) × H(conditional_i) |
| `h_canonical_is_cond_add_sigma` | `Lean/EGPT/InformationTheory/Entropy/Concrete.lean` | Conditional additivity proven for Shannon entropy |
| `RET_All_Entropy_Is_Scaled_Shannon_Entropy` | `Lean/EGPT/InformationTheory/Entropy/Uniqueness.lean` | Rota's capstone: all entropy is scaled Shannon |
| `IsEntropyZeroInvariance` | `Lean/EGPT/InformationTheory/Entropy/Axioms.lean` | Adding a zero-probability event changes nothing |
| `IsEntropyZeroOnEmptyDomain` | `Lean/EGPT/InformationTheory/Entropy/Axioms.lean` | H(∅) = 0 |

### Number Theory (Session 4)

| Symbol | File | Description |
|--------|------|-------------|
| `equivParticlePathToNat` | `Lean/EGPT/InformationTheory/EntropyNumber/Basic.lean` | ParticlePath ↔ ℕ bijection |
| `PathCompress_AllTrue` | `Lean/EGPT/InformationTheory/EntropyNumber/Basic.lean` | Maximal compression: one unique ParticlePath per length |

### Complexity — Chain 1 (Session 1)

| Symbol | File | Description |
|--------|------|-------------|
| `P_eq_NP` | `Lean/EGPT/InformationTheory/Complexity/PPNP.lean` | The `rfl` proof: `Set.ext + Iff.rfl` |
| `canonical_n_squared_bound` | `Lean/EGPT/InformationTheory/Complexity/PPNP.lean` | The polynomial is n² |
| `walkComplexity_upper_bound` | `Lean/EGPT/InformationTheory/Complexity/Tableau.lean` | Walk cost ≤ |cnf| × k |
| `walk_complexity_le_nSquared` | `Lean/EGPT/InformationTheory/Complexity/PPNP.lean` | ≤ n² |

### Decomposition (Sessions 5, 6, 7)

| Symbol | File | Description |
|--------|------|-------------|
| `evalLiteral_true_iff_literalSharesFactor` | `Lean/EGPT/InformationTheory/Complexity/Decomposition.lean` | Literal eval = prime divisibility |
| `evalCNF_true_iff_cnfSharesFactor` | `Lean/EGPT/InformationTheory/Complexity/Decomposition.lean` | Boolean ↔ prime bridge |
| `cnfSharesFactor_iff_zero_conditional_cnf_entropy` | `Lean/EGPT/InformationTheory/Complexity/Decomposition.lean` | Prime ↔ entropy bridge |
| `conditional_entropy_gcd_characterization` | `Lean/EGPT/InformationTheory/Complexity/Decomposition.lean` | GCD ↔ zero entropy |
| `unsat_detected_by_prime_structure` | `Lean/EGPT/InformationTheory/Complexity/Decomposition.lean` | UNSAT via primes |

### Constructive Proof Components (Sessions 6, 7, 8, 9)

| Symbol | File | Description |
|--------|------|-------------|
| `consistency_is_local` | `Lean/EGPT/InformationTheory/Complexity/PPNP.lean` | Local checks determine global truth |
| `canonical_entropy_bounded_by_log` | `Lean/EGPT/InformationTheory/Complexity/PPNP.lean` | H ≤ H(uniform) for all distributions |
| `walk_empty_domain_implies_zero_entropy` | `Lean/EGPT/InformationTheory/Complexity/PPNP.lean` | Walk finds empty → entropy zero |
| `walk_construction_iff_bounded_certificate` | `Lean/EGPT/InformationTheory/Complexity/PPNP.lean` | Walk = certificate |
| `three_equivalent_sat_formulations` | `Lean/EGPT/InformationTheory/Complexity/PPNP.lean` | Three-layer equivalence |

### UTM / Circuit (Sessions 2, 8, 10)

| Symbol | File | Description |
|--------|------|-------------|
| `cnf_for_specific_assignment` | `Lean/EGPT/InformationTheory/Complexity/UTM.lean` | Constructs CNF from state vectors |
| `constrainedSystem_equiv_SAT` | `Lean/EGPT/InformationTheory/Complexity/UTM.lean` | Circuit constraints = SAT |
| `breadthStep` | `Lean/EGPT/InformationTheory/Complexity/UTM.lean` | One step through the maze |
| `ndmCircuitEval_eq_evalCNF` | `Lean/EGPT/InformationTheory/Complexity/UTM.lean` | THE capstone: circuit = evalCNF |
| `ndmAddressWalk` | `Lean/EGPT/InformationTheory/Complexity/UTM.lean` | Endpoint-free walk over literal addresses |
| `literalAddress` | `Lean/EGPT/InformationTheory/Complexity/UTM.lean` | Maps literals to 2k addresses |
| `time_eq_information_eq_complexity` | `Lean/EGPT/InformationTheory/Complexity/UTM.lean` | RECT: time = information |
| `ndmWalkComplexity_polynomial` | `Lean/EGPT/InformationTheory/Complexity/UTM.lean` | NDM walk is polynomial |
| `deterministicBreadth_cost_le_nSquared` | `Lean/EGPT/InformationTheory/Complexity/UTM.lean` | n² bound |

### Student's Destination (Session 9)

| Symbol | File | Description |
|--------|------|-------------|
| `P` | `MyConstructiveProof.lean` | (the student's definition) |
| `NP` | `MyConstructiveProof.lean` | (the student's definition) |
| `P_eq_NP` | `MyConstructiveProof.lean` | (the student's proof) |

---

## JavaScript / Simulations

Interactive demonstrations and the working integer-only math library.

| Resource | Location | Sessions | Description |
|----------|----------|----------|-------------|
| GPU Heatdeath Simulation | `www/GPUHeatDeath.html` | 0, 10 | Interactive precision erosion: CPU → iPhone → GPU → supercomputer |
| Circuit SAT Experiment | `egpt_circuit_sat/index.html` | 2, 10 | Half-adder via particle transport: 80 runs, 20 seeds, zero failures |
| EGPTMath Library | `EGPTMath/EGPTMath.js` | 10 | Integer-only vector algebra engine (~6800 lines, 157 tests) |
| EGPTNumber | `EGPTMath/EGPTNumber.js` | 4 | PPF number representation: lossless Shannon coding |
| Pedagogical FAT | `EGPTMath/FAT/EGPTFAT.js` | 10 | Integer-only FFT/QFT (Cooley-Tukey, no floats) |

---

## Debate Materials

The AI debate that serves as the instructor's guide.

| Resource | Location | Description |
|----------|----------|-------------|
| Debate Log | `18.313x/debate_log.jsonl` | 82 events across 21 exchanges — machine-readable |
| Debate State | `18.313x/DEBATE_STATE.md` | 27 consensus points, 14 concessions, 7 failed approaches |
| Q&A Transcripts | `18.313x/01_QA.md` through `13_QA.md` | 13 exchanges from the founding conversation |
| Cross-Reference | `18.313x/cross_reference.jsonl` | Agent memory: events mapped to sessions, letters, Lean symbols |

---

## Proof Documentation

Navigation aids for understanding the proof chain.

| Resource | Location | Description |
|----------|----------|-------------|
| P=NP Proof Walkthrough | `Lean/EGPT/InformationTheory/Complexity/WHY_P_EQUALS_NP.md` | Detailed proof walkthrough |
| Proof Dependency Graph | `docs/PROOF_GRAPH.md` | Mermaid diagrams of theorem DAG |
| Proof Graph (JSON) | `docs/proof_graph.json` | Machine-readable dependency graph |
| Proof Dependencies | `Lean/PROOF_DEPENDENCIES.md` | Full theorem inventory |
| EGPTMath Developer Guide | `EGPTMath/EGPTMath_Developer_Guide.md` | How unlimited precision works in information space |
| FRAQTL White Paper | `content/pyFRAQTL/FRAQTL_WhitePaper.md` | FRAQTL factorization algorithm |
