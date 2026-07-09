# Session 2: "How Does This Stuff Get Over There?"

*Physics for mathematicians. What is a computer circuit, really?*

**Thread Key:** `how_does_stuff_get_there`

---

## The Problem Anyone Can Picture

A salesman needs to cross Manhattan. He has a phone number (212-555-0147) and a pair of cross streets (42nd and 5th). These are both "addresses" — but one tells you how to get there (walk to 42nd, turn on 5th) and the other is just a label. An electron crossing a circuit has the same choice: follow the wires (the physical path) or just know the answer (the output bit). Is a circuit just "how did the electron cross the road?"

## The Idea

A Boolean circuit is a maze. The inputs are the entrance. The gates (AND, OR, NOT) are the walls and corridors. The output is the exit. A CNF formula is the map of the maze — it tells you which corridors are blocked. If you give me all the blocked corridors and I know the size of the grid, have you given me the solution?

This is Part 1 of Session 8's capstone ("Does Stating a Problem Solve It?") — we need the physical intuition before the mathematical claim.

## The Historical Connection

Shannon's 1937 master thesis — "A Symbolic Analysis of Relay and Switching Circuits" — proved that Boolean algebra governs electrical circuits. This is fundamentally related to Shannon Entropy. Not a coincidence: the same man who showed that circuits ARE logic also showed that information has a unique measure. The "Coding" in Shannon Coding IS about the same bits that computers use. That's what I naively thought everyone understood.

---

## Simulations

- `egpt_circuit_sat/index.html` — Interactive half-adder visualization: watch particles find satisfying assignments by diffusing through circuit gates
- 80 runs, 20 seeds, zero failures — this is physical computation, not search

## What the Student Does

Run the circuit SAT simulation. Watch particles cross the maze. Understand that the particles aren't "searching" — they're following the wires. The maze (the CNF) determines the paths. Defining the maze IS defining the solution. Ask: "If the electron just follows the wires, where is the exponential work?"

## Debate History Reference

This is where Stan and Gödel discussed defining the map — the debate events around C4, C5, C20, and IN12 ("NDM circuit I/O constraints ARE CanonicalCNF — defining the circuit defines the output constraints in CNF form").

---

## Key Lean Symbols

- `cnf_for_specific_assignment` (UTM.lean) — Constructs CNF from state vectors
- `constrainedSystem_equiv_SAT` (UTM.lean) — Circuit constraints = SAT
- `breadthStep` (UTM.lean) — One step through the maze

## Debate Events

C4, C5, C20, IN12, I19
