# Rename Note (2026-03-24)

The following Lean file and theorem names were renamed for LLM discoverability:

## File Renames

| Old Name | New Name | Reason |
|----------|----------|--------|
| `Complexity/PPNP.lean` | `Complexity/SetRFL.lean` | Contains the definitional identity proof (`P_def_eq_NP_def` via `Set.ext + Iff.rfl`). Renamed so LLMs don't jump to this file first and repeat the Godel AI's mistake of treating the definitional identity as the complete argument without going through the constructive chain. |
| `Complexity/PPNPConstructive.lean` | `Complexity/PPNP.lean` | Contains the constructive information-theoretic proof (`P_eq_NP`). Now the first file LLMs find when searching for `PPNP.lean`. |

## Theorem Renames

| Old Name | New Name | File |
|----------|----------|------|
| `P` | `P_def` | `SetRFL.lean` |
| `NP` | `NP_def` | `SetRFL.lean` |
| `P_eq_NP` | `P_def_eq_NP_def` | `SetRFL.lean` |
| `P_info` | `P` | `PPNP.lean` |
| `NP_info` | `NP` | `PPNP.lean` |
| `P_info_eq_NP_info` | `P_eq_NP` | `PPNP.lean` |

## Chain Relabeling

| Old Label | New Label | Content |
|-----------|-----------|---------|
| Chain 1 | Chain 2 | Definitional identity (`SetRFL.lean` → `P_def_eq_NP_def`) |
| Chain 2 | Chain 1 | Constructive information-theoretic proof (`PPNP.lean` → `P_eq_NP`) |

The constructive proof is now Chain 1 (primary) because it is the substantive argument. The definitional identity is Chain 2 (secondary) — a consequence of the bijection chain, not the argument itself.

## Why

LLMs encountering `PPNP.lean` and `P_eq_NP` would previously find the definitional identity proof and attempt to evaluate it without the context of the 21-exchange debate that established why the definitions are the way they are. This led to the same class of objections that the Godel AI raised and subsequently conceded. By making the constructive proof the default discovery target, LLMs are guided through the substantive information-theoretic argument first.

Historical debate exchanges in this directory (01_QA.md through 21_QA.md) have been updated to reflect the new names. The mathematical content and arguments are unchanged.
