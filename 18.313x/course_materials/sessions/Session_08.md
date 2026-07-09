# Session 8: "Does Stating a Problem Solve It?"

*The address is the map. (Part 2 — Session 2 was Part 1.)*

**Thread Key:** `does_stating_solve`

---

## The Problem Anyone Can Picture

You're given a street address: 742 Evergreen Terrace. How much work is "finding" the house? If the address system is perfect — every house has exactly one address and every address points to exactly one house — then writing down the address IS finding the house. The search and the answer are the same thing.

## The Historical Moment

Ulam to Rota, walking through Santa Fe: "When you write down precise definitions for these words, you discover that what you are describing is not an object, but a function, a role that is inextricably tied to some context. Take away the context, and the meaning also disappears."

## The Mathematical Claim

(Now the student has Session 2's circuit intuition AND Sessions 4-7's machinery.) Defining a CNF with k variables and n clauses creates an address space with exactly |cnf| × k navigable locations. Walking this space IS solving the problem. `ndmCircuitEval_eq_evalCNF`: the circuit IS evalCNF in address space. The three-layer equivalence: Boolean ↔ address ↔ entropy ↔ prime.

---

## What the Student Does

This is the session where everything clicks. The student sees that Ulam's "perception is always the perception of functional roles" is the same insight as "the address is the map" is the same insight as `ndmCircuitEval_eq_evalCNF`. The problem statement IS the solution — not metaphorically, but provably. This is where the student, playing Stan, tells the agents: "Connect the circuit walk from Session 2 to the entropy from Session 5 to the primes from Session 6. Show me that they're the same theorem."

---

## Key Documents

- `The_Barrier_of_Meaning_Rota.md` — Ulam on functional roles and meaning
- `Letter3_Jan12_1931.md` — Von Neumann's constructivism

## Key Lean Symbols

- `ndmCircuitEval_eq_evalCNF` (UTM.lean) — THE capstone: circuit = evalCNF
- `ndmAddressWalk` (UTM.lean) — Endpoint-free walk over literal addresses
- `literalAddress` (UTM.lean) — Maps literals to 2k addresses
- `three_equivalent_sat_formulations` (PPNP.lean)

## Debate Events

C4, C5, C17, C18, C20, C23, C25, Y11, Y13, IN12, IN18, I19, I22-I26
