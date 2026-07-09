# 18.313x: Syllabus

> 11 sessions. 11 questions anyone can ask. One constructive proof of P = NP — built by you.

---

## Session 0: "What Does Water Boiling at 100° Have to Do with Pennies on a Carpet?"

Rota's Day 1. You drop 100 pennies on a carpet. You boil water. What do these have in common? Both are about counting — and the mathematics of counting is the mathematics of information. Boltzmann, Gibbs, and Shannon all measured the same thing. Rota proved they had to. This session is where you lean forward and realize that probability, physics, and computation are the same subject wearing different hats.

---

## Session 1: "Can a Machine Replace a Mathematician?"

Gödel, writing to a dying von Neumann in 1956, asks the question that would become P vs. NP — twenty years before anyone named it. Can a machine find a proof in N² steps, or must it take 2^N? EGPT says the walk cost is bounded by n². Gödel guessed KN². The bound is the same. Von Neumann died before he could answer. You will.

---

## Session 2: "How Does This Stuff Get Over There?"

A Boolean circuit is a maze. An electron crossing it is a particle following wires. Shannon proved in 1937 that circuits ARE logic — the same man who then proved information has a unique measure. This session builds physical intuition: run the circuit SAT simulation, watch particles find satisfying assignments by diffusion, and ask the question that changes everything — if the electron just follows the wires, where is the exponential work?

---

## Session 3: "Can You Formalize Intuition?"

The fight that started in 1931 between von Neumann and Gödel — and still isn't over. Rota's conditional additivity axiom (`IsEntropyCondAddSigma`) says: if you know the whole, the parts always add up. This is the OPPOSITE of Gödel's incompleteness. Conditional additivity is the bedrock "1+1=2 always." Incompleteness says the gaps prove the system is broken. Conditional additivity says the gaps are just unanswered questions. This distinction is the foundation of the entire course.

---

## Session 4: "Is the Universe Built from Numbers?"

Einstein on his deathbed: "nothing remains of my entire castle in the air, *and all of modern physics*." Von Neumann, dying, reached for a stochastic computer. Ulam proposed deriving physics — distance, mass, time — from a random walk. A particle flipping coins IS a number IS a computation. `ParticlePath = List Bool = ℕ`. The hierarchy that builds all of mathematics from coin flips.

---

## Session 5: "Is There Only One Way to Measure Information?"

Rota's 30-year theorem: log is the UNIQUE information measure. All entropy — Boltzmann's, Shannon's, von Neumann's — is scaled Shannon entropy. This is the bridge: physics IS information theory, computation IS physics, and the logarithm connects them. There is no other bridge. The chain rule that processes a CNF clause-by-clause IS the same chain rule that decomposes entropy. This is the technical heart.

---

## Session 6: "Does Every Part Reveal the Whole?"

You're assembling a jigsaw puzzle. If every piece fits its neighbors, must the whole picture be correct? In EGPT's prime encoding, yes. The Fundamental Theorem of Arithmetic guarantees unique decomposition. Checking a literal is checking whether a prime divides a composite — that's GCD, and GCD is polynomial. If checking each piece is cheap, why would checking the whole puzzle be expensive?

---

## Session 7: "Can You Ask About Something That Doesn't Exist?"

You search an empty room for your keys. How much did you learn? Zero — the room already told you the answer. In information theory, zero-probability events contribute zero information. UNSAT instances are zero-probability events in information space. The Cantor diagonal creates syntactic novelty but not semantic novelty. This is the philosophical crux: is absence evidence of incompleteness, or just an unanswered question with answer zero?

---

## Session 8: "Does Stating a Problem Solve It?"

The address is the map. If every house has exactly one address, writing the address IS finding the house. This is where everything clicks: Session 2's circuit intuition meets Sessions 4-7's machinery. Defining a CNF creates an address space. Walking it IS solving it. `ndmCircuitEval_eq_evalCNF`: the circuit IS evalCNF in address space. The problem statement IS the solution — not metaphorically, but provably.

---

## Session 9: "What Makes a Proof Valid?"

Two people watch the same magic trick. One says impossible, the other says you don't understand the method. They agree on every fact. They disagree on definitions. This is where it ended in 1931 and in 2026: von Neumann said "name one construction that can't be formalized." The AI skeptic said "the code is clean, the types are standard, I have no line to cite." By now the student has built their own constructive proof. Their proof IS their answer to this question.

---

## Session 10: "Why Does This Cost So Much?"

Von Neumann disavowed his own architecture on his deathbed. He wanted integer arithmetic at 2-3 digits, not floating point at 64 bits. We ignored him and built a trillion-dollar industry on the design he said was wrong. The exponential blowup was always an artifact of the representation. FLOPs are the wrong unit. IOPs — integer operations, exact arithmetic — are what he was reaching for. The student who built the constructive proof now understands what it means: we're boiling rivers because we're solving the wrong problem with the wrong tools.

---

## Session Map

| Session | Thread Key | Question | Historical Anchor |
|---------|-----------|----------|-------------------|
| 0 | `pennies_and_boiling_water` | What does water boiling have to do with pennies on a carpet? | Rota's 18.313 Day 1 |
| 1 | `can_a_machine_think` | Can a machine replace a mathematician? | Gödel → JvM, 1956 |
| 2 | `how_does_stuff_get_there` | How does this stuff get over there? | Shannon's thesis, 1937 |
| 3 | `can_you_formalize_intuition` | Can you formalize intuition? | JvM → Gödel, Jan 12 1931 |
| 4 | `universe_from_numbers` | Is the universe built from numbers? | Einstein 1954, JvM 1957, Ulam's random walk |
| 5 | `one_measure_of_information` | Is there only one way to measure information? | Rota's 30-year manuscript |
| 6 | `parts_reveal_whole` | Does every part reveal the whole? | Fundamental Theorem of Arithmetic |
| 7 | `asking_about_nothing` | Can you ask about something that doesn't exist? | Cantor, Gödel, zero-probability |
| 8 | `does_stating_solve` | Does stating a problem solve it? | Ulam & Rota in Santa Fe |
| 9 | `what_makes_proof_valid` | What makes a proof valid? | JvM & Gödel, 1931 = 2026 |
| 10 | `why_so_expensive` | Why does this cost so much? | JvM's dying words |

Session 0 is the overture. Sessions 1-9 build the constructive proof. Session 10 is why it matters.

The student who completes the course has:
- Read the actual historical letters
- Understood 11 ideas deeply enough to connect them
- Built a constructive proof of P = NP by playing Stan — connecting dots, with agents writing the code
- Understood why P = NP without reading a line of Lean syntax
- Understood why we're boiling rivers and how to stop
- A debate log that IS their term paper
