# 18.313x: The Constructive Proof

> "Philosophers are needed today more than ever to tell the AI engineers some unpleasant truths. The philosopher's role has always been that of stating facts that may have been on everybody's mind but that no one dared state clearly. Eventually, engineers will reluctantly acknowledge that what the philosopher says is the truth, but they will then get rid of the philosopher."
> — Gian-Carlo Rota

---

A trillion dollars is being raised to put AI data centers in space because there isn't enough electricity on Earth to run them. Meanwhile, robots fall over and can't get up. The man who invented the computer said on his deathbed that the architecture was wrong. The man who proved mathematics has limits asked him whether a machine could replace a mathematician. He died before he could answer.

This class answers his question.

18.313x is built on Gian-Carlo Rota's legendary probability course at MIT — the one where Day 1 asked what water boiling at 100° has to do with pennies falling on a carpet and the last week proved there is only one way to measure information in the universe. We are rebuilding that class with the original participants brought back as AI agents: Gödel challenges, von Neumann builds, Rota measures, and you — playing Stanislaw Ulam, von Neumann's closest collaborator and the man with "the highest record of accurate guesses in mathematics" — connect the ideas across domains.

No programming required. No math prerequisites beyond curiosity. You will never read a line of code. AI agents write the proofs. Your job is to understand the ideas deeply enough to tell them what to connect — the same job Ulam did when he told von Neumann that Gödel's undecidability result was "nothing but a sort of super paradox, merely a diagonal method," and von Neumann opened his eyes wide at the insight.

By the end of this course you will have: read the actual letters between von Neumann and Gödel, understood why AI costs so much and what's fundamentally wrong, built a constructive proof of P = NP by connecting ideas (with AI writing the code), and understood why the people who solved the deepest open problem in mathematics will wonder — like Rota and Conway before them — why anyone ever thought it was hard.

This is not a computer science class. It is a class about the nature of thinking and reality itself. The computer science falls out at the end.

---

## What This Is

A course where the student plays Stan Ulam — the one who connects ideas across domains. The agents play the specialists: Gödel pushes back, von Neumann builds, Rota measures, and the Lean prover writes the code. The student never needs to read Lean syntax. They need to understand the ideas well enough to tell the agents what to connect.

**Starting materials (given to every student on Day 1):**
1. Gödel's incompleteness theorem — "There are true things you can't prove within any consistent formal system"
2. Rota's Entropy Theorem — "There's only one way to measure information" (`RET_All_Entropy_Is_Scaled_Shannon_Entropy`)
3. The `rfl` proof of P=NP — `P_eq_NP` in PPNP.lean, which is `Set.ext + Iff.rfl`, definitional equality

**The project:** The constructive proof (`P_eq_NP`) doesn't exist yet. The students build it. Each student (or team) works from a class repository — a fork of EGPT with the constructive proof components stripped out, leaving only the Lean stub to build toward. Every theorem in the repository is available as a building block. The student's job is to connect the dots — to see which existing theorems, when composed in the right order, yield the constructive proof. The agents write the Lean. The student plays Stan.

**The guide:** Our own AI debate (21 exchanges, 82 events in `debate_log.jsonl`) is the instructor's guide to knowing what the AIs can do when given the right insights from Stan. Every student is Stan.

**Rota's method:** Start each session with a problem everyone can picture. End with the theorem that resolves it. The path between is the class.

---

## The Arc

The course follows the same arc as Rota's 18.313: it starts with concrete, physical problems that anyone can picture, builds the mathematical machinery to understand them, and arrives at a theorem that connects everything.

But it also follows the historical arc: 1930 → 1931 → 1956 → 1985 → 2026. The letters are the connective tissue. The student reads what von Neumann actually wrote, what Gödel actually asked, what Ulam actually said to Rota on that hill in Santa Fe. Then they see the same ideas formalized in code.

---

## The Class Repository

A fork of the EGPT repository with the following removed:
- `P` and `NP` definitions (PPNP.lean)
- `P_eq_NP` theorem and its supporting lemmas
- The NDM walk constructions (`ndmAddressWalk`, `ndmEntropyWalk`, `ndmCircuitEval`)
- The three-layer equivalence theorems
- All Section 10 packaging theorems

What remains (available as building blocks):
- Chain 1: `P_eq_NP` via `Set.ext + Iff.rfl` (the `rfl` proof)
- All entropy machinery: RET, 7 axioms, chain rule, conditional entropy
- All prime factorization: `evalLiteral_true_iff_literalSharesFactor`, `CNFSharesFactor`, `assignmentCompositePrime`
- `walkCNFPaths`, `walkComplexity_upper_bound`, `SatisfyingTableau`
- `computeTableau?`, `AssignmentFreeSAT ↔ SAT`
- `RECT`, `IRECT`, `time_eq_information_eq_complexity`
- All of NumberTheory (ParticlePath ↔ ℕ, Beth hierarchy)
- The debate agents, the historical letters, the debate log

The student's destination: a file called `MyConstructiveProof.lean` that proves `P_eq_NP` (or their own equivalent) by composing the available building blocks in a novel order. Their AI debate is the record of how they got there.

---

## Current Events: Why Now

*A section woven through the course, updated each semester.*

The Singularity — a term coined by Stanislaw Ulam in his 1958 tribute to von Neumann — is on everyone's mind. AGI is either imminent or a mirage, depending on who you ask. Meanwhile:

- Elon Musk's xAI raises $1.3 trillion to put AI data centers in space because there isn't enough electricity on Earth
- Robots fall over and can't get up (media clips)
- GPU clusters consume the electricity of small countries
- Von Neumann predicted this: 425 operations at 5% rounding error each degrades precision by a factor of a billion. We're running trillions of floating-point operations and wondering why the answers drift.

**The GPU Heatdeath simulation** (`www/GPUHeatDeath.html`) demonstrates this live: watch precision erode as you scale from a CPU to an iPhone to an Nvidia GPU to a supercomputer. The erosion is exponential. Von Neumann diagnosed it in 1957.

**The circuit SAT experiment** (`egpt_circuit_sat/`) demonstrates the alternative: particles diffusing through a half-adder circuit find satisfying assignments with 100% accuracy across 80 runs. No floating point. No error accumulation. Physical computation.

These aren't historical curiosities. This is the crisis. And the mathematics in this course is the diagnosis.

---

## How the Student Interacts

The student plays Stan. The agents are their collaborators:

- **@pnp-moderator** — Frames the session's question, manages the flow
- **@pnp-godel (Gödel)** — Challenges every claim. "But isn't this just..." The student must answer.
- **@pnp-jvm (von Neumann)** — Builds. "Let me show you in code..." Connects ideas to implementations.
- **@pnp-rota** — Measures. "The entropy of that claim is..." Grounds everything in Rota's axioms.
- **@lean-prover** — Writes and verifies the actual Lean code. The student never has to.
- **@egpt-orchestrator** — When the student connects an idea, delegates the implementation.

**The student's job at each session:**
1. Read the historical document (the letter, the essay)
2. Understand the question
3. Explore it with the agents — ask questions, propose connections, challenge claims
4. When the student sees a connection the agents haven't made (playing Stan), propose it
5. The agents implement it. The constructive proof grows.
6. At the end: the student can point to a theorem they understand and a line of code they caused to exist

**The class project:** Build `MyConstructiveProof.lean` — a file that proves `P_eq_NP` (or the student's own equivalent) by composing existing theorems in a novel order. The student's AI debate log IS their term paper.

**The cross-reference table (`cross_reference.jsonl`) is the agent's memory.** Instead of re-reading every letter and every Lean file at every session, the moderator loads the cross-reference for the current session's thread and has: the relevant debate events, the letter excerpts, the Lean symbols, and the historical context. Dramatically reduced context window. The student's experience is fluid conversation; the agent's experience is efficient lookup.
