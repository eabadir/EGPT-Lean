# Session 1: "Can a Machine Replace a Mathematician?"

*The question that launched everything.*

**Thread Key:** `can_a_machine_think`

---

## The Problem Anyone Can Picture

You're a mathematician. You think about a problem for years. One day, you see the answer. Could a machine have found it faster? Is there a shortcut to insight?

## The Historical Moment

Gödel, March 20, 1956, writing to a dying von Neumann. He opens with "the greatest sorrow" and then asks the question he'd been holding for years: if a formula has length N, can a machine decide its provability in N² steps? Or does it take 2^N? "If the answer were affirmative, it would mean that the mental work of the mathematician concerning yes-or-no questions could be completely replaced by a machine."

Von Neumann died before he could answer.

## The Mathematical Claim

EGPT says yes. The walk cost is bounded by |cnf| × k ≤ n². Gödel guessed KN². The bound is the same.

---

## What the Student Does

Read Gödel's letter. Understand what he's really asking — not about SAT solvers, but about whether thought has a polynomial shortcut. Then look at `walkComplexity_upper_bound`: walk cost ≤ |cnf| × k. Ask the skeptic agent: "Why isn't this the answer Gödel was looking for?"

---

## Key Letters

- `Godel_Letter_to_Von_Neumann.md` (1956) — the question
- `JvM_vs_Godel_EGPT_History.md` — the full narrative

## Key Lean Symbols

- `walkComplexity_upper_bound` (TableauFromCNF.lean) — Walk cost ≤ |cnf| × k
- `walk_complexity_le_nSquared` (PPNP.lean) — ≤ n²
- `canonical_n_squared_bound` (PPNP.lean) — The polynomial is n²
- `P_eq_NP` (PPNP.lean) — The theorem Gödel was asking about

## Debate Events

C2, C12, C13, Y1, Y5, F2, F5, I5, I6, IN3, IN7, IN13, OQ1
