# Extraction prototype

A working demonstration of the Zulip handoff's thesis: **one surgical
replacement for `Classical.choice` + a small per-constant realizer
table extracts classical Mathlib theorems to bit-exact C without
rewriting the theorems.**

Nine theorems, twelve-realizer walker, one `#extract_to_c` command.
All emitted C programs compile against [`libegpt_num`](../../../../Unkamon/FRAQTL/fat/crates/egpt_num/),
run to `true`, exit 0, and pass `make diff` byte-equivalence.

---

## Read in this order

1. **[AUDIT.md](AUDIT.md)** — what the audit of the EntropyReal tower
   found on 2026-04-24. The `#print axioms` baseline, the
   divergences from the original handoff, and the session decisions
   that shaped the prototype.
2. **[PLAN.md](PLAN.md)** — the Phase 0–Phase 1 passes (A–H),
   completion scoreboard, and open questions. Pass-level history.
3. **[ARCHITECTURE.md](ARCHITECTURE.md)** — how the walker works,
   where realizers live, the runtime ABI, and extension procedures
   for adding a new function or connective.
4. **[RISKS.md](RISKS.md)** — honest limitations: approximation
   soundness, bounded search, walker gaps, and what a correctness
   meta-theorem would still need to prove.
5. **This file** — index + quick start.

---

## The nine target theorems

All in [ExtractionCommand.lean](ExtractionCommand.lean),
extracted via `#extract_to_c <name>`, output under
[prototype/Extraction_<name>/](prototype/).

| # | Name | Statement | Shape exercised |
|---|---|---|---|
| 1 | `exp_one_gt_two` | `(2 : ℝ) < Real.exp 1` | LT + OfNat + Real.exp |
| 2 | `exp_one_lt_three` | `Real.exp 1 < (3 : ℝ)` | operand reordering |
| 3 | `one_lt_sqrt_two` | `(1 : ℝ) < Real.sqrt 2` | + Real.sqrt |
| 4 | `two_lt_one_plus_sqrt_two` | `(2 : ℝ) < 1 + Real.sqrt 2` | + HAdd, nested |
| 5 | `classical_choice_mul_zero_lt_one` | `Classical.choice ℝ ⟨37⟩ * 0 < 1` | **+ Classical.choice** |
| 6 | `exists_sq_eq_four` | `∃ x : ℝ, x * x = 4` | **+ Exists + Eq + bvar** |
| 7 | `exp_one_between_two_and_three` | `2 < Real.exp 1 ∧ Real.exp 1 < 3` | **+ And** |
| 8 | `exp_one_lt_three_or_huge` | `Real.exp 1 < 3 ∨ 100 < Real.exp 1` | **+ Or** |
| 9 | `forall_fin_three_val_lt_three` | `∀ x : Fin 3, x.val < 3` | **+ ∀ + forallE + Fin.val** |

Eight have axiom closure `{propext, Classical.choice, Quot.sound}`.
#9 depends on no axioms (constructive).

---

## Quick start

```bash
# 1. Runtime (FRAQTL; one time):
cd ~/Code/Unkamon/FRAQTL/fat
cargo build --release -p egpt_num

# 2. Extraction library build (cached oleans if available):
cd ~/Code/EGPT-research/Lean/EGPT
lake exe cache get
lake build InformationTheory.EntropyNumber.ContinuumHypothesis

# 3. Run the extractor (writes prototype/Extraction_<name>/extracted.c for each target):
lake env lean extraction/ExtractionCommand.lean

# 4. Compile + byte-equivalence gate for all nine targets:
cd extraction/prototype
make diff
# expected: 9 × "✓ <name> byte-equivalent"
```

---

## Branch / commit layout

| Repo | Branch | Purpose |
|---|---|---|
| `EGPT-research` | `feat/extraction-prototype` | Lean-side walker + target theorems + docs |
| `FRAQTL` | `feat/egpt-num-cffi` | `egpt_num` C ABI runtime (cdylib + header) |

Commit history on `feat/extraction-prototype`:

```
0497796 Pass H — Or + ∀-over-Fin (structural claim at 100%)
2729fb7 Pass G — conjunction
81f749d Pass F — existentials + Eq + binder
7bd735b Pass E — uniform Classical.choice realizer
26ef0e0 Pass D — binary-operator realizers
29872a0 Pass C — Real.sqrt
4a69761 Pass B — decomposing Expr walker
54165e2 Pass A — template walker (retired)
c5c7fe8 Audit + plan docs (Phase 0)
```

Phase 0 `egpt_num` FFI runtime lands on FRAQTL as `f4ba38b`.

---

## What this demonstrates — and what it doesn't

### Demonstrates

- A Lean `#extract_to_c` meta-command that walks a theorem type and
  emits C.
- A 12-entry realizer registry covering LT, Eq, And, Or, Exists,
  ∀-over-Fin, HAdd/HSub/HMul, OfNat, Real.exp, Real.sqrt,
  Classical.choice, with Fin.val pass-through and bvar 0 handling.
- Nine structurally distinct Mathlib classical theorems flowing
  through the **same** command to bit-exact C.
- A uniform `Classical.choice` realizer keyed by type that
  preserves Mathlib provability conditions.

### Doesn't (yet) demonstrate — see [RISKS.md](RISKS.md)

- Precision-safe extraction for tight inequalities / equalities on
  transcendentals.
- Nested binders.
- `∀` over infinite / opaque domains.
- A formal composition correctness meta-theorem.
- Integration with Lean's own extraction pipeline
  (`@[extern]` / LCNF).

---

## Reproducibility canary

If `make diff` fails after any change in this tree, the ten-realizer
walker has regressed. The diagnostic sequence:

1. `lake env lean extraction/ExtractionCommand.lean` — do all nine
   `#extract_to_c` commands succeed? If not, the Lean-side walker
   has a bug.
2. `cd extraction/prototype && make` — do all nine binaries build?
   If not, the runtime ABI or header drifted.
3. `./Extraction_<name>/extracted_bin` — does each individual
   binary print `true`? If one prints `false`, the realizer for
   some constant in that theorem's closure is producing a wrong
   value.
4. `diff expected_output.txt stdout` — byte differences here
   usually mean preamble / formatting drift.
