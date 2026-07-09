---
name: debate-explorer
description: "Explore the P=NP debate record, proof chains, and consensus points. Use to study before challenging."
argument-hint: "[topic: 'chains', 'consensus', 'concessions', 'deleted', 'entropy', or a search term]"
user-invocable: true
allowed-tools: Read Grep Glob
model: sonnet
effort: medium
---

# Debate Explorer

Help Georg study the debate record and proof files to find potential attack angles.

## Topics

Based on `$ARGUMENTS`:

**"chains"** or **"proof"**: Read and summarize `Lean/PROOF_CHAINS.md`. Show the three chains, their capstones, and the file dependency graph.

**"consensus"** or **"points"**: Read `18.313x/DEBATE_STATE.md` and list all consensus points (C1-C45) in a scannable format. Highlight which ones block common objection patterns.

**"concessions"**: Show all 16 concessions (Y1-Y16) — what the skeptic yielded and when. These are potential weak points where the skeptic gave ground.

**"deleted"** or **"audit"**: Read the C43–C45 consensus points in `18.313x/DEBATE_STATE.md` — they record which code was deleted and why.

**"entropy"** or **"rota"**: Show the entropy chain (Axioms.lean, Concrete.lean, Uniqueness.lean) and how it connects to the complexity chain via Decomposition.lean.

**"failed"**: Show failed approaches (F5, F6, F8, F9) — things that were tried and didn't work. These are dead ends Georg should avoid.

**"open"**: Show remaining open questions (OQ2, OQ4, OQ8) — secondary/tertiary items that might be attack angles.

**Search term**: Grep the debate state, proof files, and exchange JSONs for the term. Show relevant context.

## Key Entry Points

| If Georg wants to... | Read this first |
|----------------------|----------------|
| Understand what's proven | `Lean/PROOF_CHAINS.md` |
| See where the skeptic conceded | `18.313x/DEBATE_STATE.md` → Concessions table |
| Find potential weak points | Open Frontier in DEBATE_STATE.md |
| Understand the definitions | `Lean/EGPT/InformationTheory/Complexity/WHY_P_EQUALS_NP.md` |
| See the actual Lean code | `Lean/EGPT/InformationTheory/Complexity/PPNP.lean` (start here) |

## Coaching Tips

When presenting information, point out potential attack angles:
- "This consensus point (C_N) rests on [theorem]. You could check if [theorem] actually proves what they claim."
- "The skeptic conceded Y_N at exchange E_M. The basis was [X]. You could check if [X] still holds."
- "This open question (OQ_N) was deprioritized but never fully resolved."

But always be honest — if an angle is genuinely closed, say so.
