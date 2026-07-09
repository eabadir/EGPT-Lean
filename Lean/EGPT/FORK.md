# Mathlib4 Fork

## Browse Online

https://github.com/eabadir/mathlib4/tree/feat/information-theory/Mathlib/InformationTheory

## Coordinates

| Field | Value |
|-------|-------|
| Fork | https://github.com/eabadir/mathlib4.git |
| Branch | `feat/information-theory` |
| Upstream | https://github.com/leanprover-community/mathlib4.git |
| Local path | `~/Lean/mathlib4/` |
| Target namespace | `Mathlib.InformationTheory` |

## Sync Scripts

| Script | Direction | What it does |
|--------|-----------|-------------|
| `sync_to_mathlib.sh` | `Lean/EGPT/InformationTheory/` → `~/Lean/mathlib4/Mathlib/InformationTheory/` | Copies .lean files, rewrites imports (`InformationTheory.` → `Mathlib.InformationTheory.`), strips LLM guidance headers |
| `sync_from_mathlib.sh` | `~/Lean/mathlib4/Mathlib/InformationTheory/` → `Lean/EGPT/InformationTheory/` | Reverse sync, rewrites imports back |

## Git Remotes (in `~/Lean/mathlib4/`)

```
fork    https://github.com/eabadir/mathlib4.git (fetch/push)
origin  https://github.com/leanprover-community/mathlib4.git (fetch/push)
```

## Workflow

```bash
# 1. Make changes in Lean/EGPT/InformationTheory/ (builds with: cd Lean/EGPT && lake build)
# 2. Sync to fork
cd Lean/EGPT && bash sync_to_mathlib.sh
# 3. Commit and push
cd ~/Lean/mathlib4 && git add Mathlib/InformationTheory/ && git commit && git push fork feat/information-theory
```

## PR Description

See [MATHLIB_PR.md](MATHLIB_PR.md) for the full pull request body.
