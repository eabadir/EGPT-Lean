# EGPT Lean Library

This directory contains the formal Lean 4 proofs for Electronic Graph Paper Theory (EGPT). The proofs construct number theory from first principles in an information space and derive P = NP as a consequence.

For the full narrative and motivation behind EGPT, see [EGPT_STORY.md](../../EGPT_STORY.md) at the repo root.

---

## Module Overview

### Core Definitions
- **[Core.lean](Core.lean)** — `ParticlePath` (the fundamental type: `{ L : List Bool // PathCompress_AllTrue L }`), `ComputerTape`, path operations
- **[Basic.lean](Basic.lean)** — Helper lemmas for logarithms, casts, Archimedean properties
- **[Constraints.lean](Constraints.lean)** — CNF formulas (`Literal_EGPT`, `Clause_EGPT`, `CanonicalCNF`), `encodeCNF`, encoding size bounds

### Number Theory (`NumberTheory/`)
- **[Core.lean](NumberTheory/Core.lean)** — The `ParticlePath ≃ ℕ` bijection (`toNat`, `fromNat`, `equivParticlePathToNat`), native arithmetic, `EGPT_Polynomial`
- **[Analysis.lean](NumberTheory/Analysis.lean)** — Analytical properties of the number system
- **[Filter.lean](NumberTheory/Filter.lean)** — Rejection filters, probability distributions

### Complexity — The P=NP Proof (`Complexity/`)
- **[Core.lean](Complexity/Core.lean)** — `PathToConstraint` (the address IS the path), polynomial definitions
- **[TableauFromCNF.lean](Complexity/TableauFromCNF.lean)** — `SatisfyingTableau`, `constructSatisfyingTableau`, `tableauComplexity_upper_bound` (cost ≤ clauses × variables)
- **[SetRFL.lean](Complexity/SetRFL.lean)** — `P`, `NP`, **`P_eq_NP`** (the theorem), `EGPT_CookLevin_Theorem`

For a detailed walkthrough of the proof: [PeqNP_Proof_README.md](PeqNP_Proof_README.md)

### Entropy — Rota's Entropy Theorem (`Entropy/`)
An independent formalization, NOT used in the P=NP proof chain:
- **[Common.lean](Entropy/Common.lean)** — Rota's 5 axioms of entropy (`HasRotaEntropyProperties`)
- **[H.lean](Entropy/H.lean)** — Entropy function definitions
- **[RET.lean](Entropy/RET.lean)** — `RotaUniformTheorem_formula_with_C_constant` — all valid entropy = C × log(n)

### Physics — Physical Models (`Physics/`)
Motivation and semantics, NOT imported by the proof chain:
- `Common.lean`, `BoseEinstein.lean`, `PhotonicCA.lean`, `PhysicsDist.lean`, `UniformSystems.lean`

---

## The Proof Chain at a Glance

```
Core.lean (ParticlePath)
    ↓
NumberTheory/Core.lean (ParticlePath ≃ ℕ bijection)
    ↓
Constraints.lean (CNF as addresses)
    ↓
Complexity/Core.lean (PathToConstraint: address = path)
    ↓
Complexity/TableauFromCNF.lean (SatisfyingTableau, polynomial bound)
    ↓
Complexity/SetRFL.lean (P = NP via Iff.rfl)
```

These 6 files are **sorry-free** and **axiom-free**. The proof completes with `Iff.rfl` because `P` and `NP` are syntactically identical definitions.

---

## Building

```bash
lake build    # from the Lean/ directory
```

Requires Lean 4 v4.21.0-rc3 and will download mathlib4 on first build.
