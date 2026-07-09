# Session 6: "Does Every Part Reveal the Whole?"

*Prime factorization and why local consistency implies global consistency.*

**Thread Key:** `parts_reveal_whole`

---

## The Problem Anyone Can Picture

You're assembling a jigsaw puzzle. If every piece fits perfectly with its neighbors, does the whole puzzle have to be correct? Or could the pieces all fit locally but the big picture be wrong?

## The Mathematical Claim

In EGPT's prime encoding, the Fundamental Theorem of Arithmetic guarantees unique decomposition. Each literal's truth value is a single prime divisibility test. If every literal is locally consistent, the whole CNF must be satisfiable. The contrapositive: if any literal is inconsistent, you detect it without examining the whole.

---

## What the Student Does

Understand `assignmentCompositePrime` — an assignment becomes a product of primes. Understanding `evalLiteral_true_iff_literalSharesFactor` — checking a literal is checking whether a prime divides the composite. This is GCD, and GCD is polynomial (Euclid's algorithm). Ask: "If checking each piece is cheap, why would checking the whole puzzle be expensive?"

---

## Key Lean Symbols

- `evalLiteral_true_iff_literalSharesFactor` (Decomposition.lean) — Literal eval = prime divisibility
- `consistency_is_local` (PPNP.lean) — Local checks determine global truth
- `evalCNF_true_iff_cnfSharesFactor` (Decomposition.lean) — Boolean ↔ prime bridge
- `cnfSharesFactor_iff_zero_conditional_cnf_entropy` (Decomposition.lean) — Prime ↔ entropy bridge

## Debate Events

C4, C5, C13, C16, C23, C24, Y7, Y13, IN3, IN4, IN5, IN9, IN18, F3, I7, I15-I18, OQ5, OQ8
