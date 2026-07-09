# Session 10: "Why Does This Cost So Much?"

*The practical question. Von Neumann's dying words. The reason this matters now.*

**Thread Key:** `why_so_expensive`

---

## The Problem Anyone Can Picture

We're boiling rivers to cool data centers. We're spending more on electricity for AI than some countries consume. Is this inevitable? Or are we doing something fundamentally wrong?

## The Historical Moment

Von Neumann, dying, disavowed his own architecture. He wanted "a radically divergent system of notation" — a stochastic computer at 2-3 decimal digits, "a lower level of arithmetical precision but a higher level of logical reliability: a deterioration in arithmetics has been traded for an improvement in logics." We ignored this and built a trillion-dollar industry on his first design. Every computer ever built is a von Neumann machine running on the architecture he said was wrong.

## The Mathematical Claim

The exponential blowup in computation comes from representing problems in the wrong space. 2^k assignments in Boolean space compress to k × |cnf| walk steps in address space. Shannon compression: 2^t_i paths → t_i+1 addresses. The exponential was always an artifact of the representation. FLOPs are the wrong unit. IOPs — integer operations, exact arithmetic, no error accumulation — are what von Neumann was reaching for.

---

## What the Student Does

This is the synthesis. Everything from Sessions 0-9 converges: Rota's uniqueness theorem says there's one way to measure information. The walk operates in address space, not solution space. The cost is polynomial, not exponential. Von Neumann's stochastic computer doesn't need to boil rivers. EGPTMath (157 tests, zero floating-point operations) is the proof of concept.

The student who built their own constructive proof now understands what it means: not just P = NP in the abstract, but that the trillion-dollar floating-point industry is solving the wrong problem with the wrong tools. Ask: "If this is right, what changes?"

---

## Key Documents

- `JvM_vs_Godel_EGPT_History.md` — "a radically divergent system of notation"
- `The_Mathematician_JvM.md` — Mathematics and science
- `content/Notes/Precision Loss.md` — "425 operations at 5% error = 1 billion degradation"

## Simulations

- `www/GPUHeatDeath.html` — Precision erosion visualization
- `egpt_circuit_sat/index.html` — The alternative: physical computation

## Key Lean Symbols

- `walkComplexity_upper_bound` (TableauFromCNF.lean) — Walk cost ≤ |cnf| × k
- `ndmWalkComplexity_polynomial` (UTM.lean) — NDM walk is polynomial
- `deterministicBreadth_cost_le_nSquared` (UTM.lean) — n² bound

## Debate Events

C2, C18, C20, Y10, Y11, F1, F6, IN9, IN10, IN14, I19, I20, OQ3, OQ7
