# Session 7: "Can You Ask About Something That Doesn't Exist?"

*Zero-probability events, Cantor's diagonal, and why absence has a cost of zero.*

**Thread Key:** `asking_about_nothing`

---

## The Problem Anyone Can Picture

You ask me to find your keys in a room. I search every drawer, every pocket, every surface. They're not there. How much did I learn by searching? Did the search teach me anything, or did I just confirm what the room already told me — that the keys aren't in it?

## The Mathematical Claim

In information theory, zero-probability events contribute zero information. `IsEntropyZeroInvariance`: appending an outcome with probability zero doesn't change the entropy. You can't extract information from what isn't there. UNSAT instances are zero-probability events in information space. The walk reaches an empty domain, and the entropy is zero. The Cantor diagonal — and Gödel's incompleteness proof, which uses the same trick — creates something that "should" exist but doesn't. EGPT says: you're asking about a zero-probability event. The answer is nothing.

---

## What the Student Does

This is the philosophical crux. Understand that the Cantor diagonal creates SYNTACTIC novelty (a new string) but not necessarily SEMANTIC novelty (new information). In maximally compressed space, flipping a digit doesn't create a new prime atom. Ask the skeptic: "Is this really the flaw in Cantor's argument, or am I missing something?"

---

## Key Lean Symbols

- `IsEntropyZeroInvariance` (Entropy/Common.lean) — Adding a zero-probability event changes nothing
- `IsEntropyZeroOnEmptyDomain` (Entropy/Common.lean) — H(∅) = 0
- `walk_empty_domain_implies_zero_entropy` (PPNP.lean) — Walk finds empty → entropy zero
- `unsat_detected_by_prime_structure` (Decomposition.lean) — UNSAT via primes

## Debate Events

C7, C24, Y3, IN1, IN2, IN16, I2, I3, OQ2
