# 18.313x — Introduction to EGPT: The Constructive Proof

Course directory for **18.313x**, based on MIT 18.313 (Rota's probability course). This is where the P=NP debate system lives — a structured exchange modeled on the 1931 von Neumann-Gödel correspondence about the formalizability of intuitionism, transposed to Lean 4 and P=NP.

## Contents

| Path | Description |
|------|-------------|
| `archive/01_QA.md` through `archive/21_*.md` | Archived debate transcripts (E1-E21) — dialog text, parsed by concordance-sync.js |
| `DEBATE_STATE.md` | Auto-generated debate state (run `node www/GreatDebate/js/concordance-sync.js` to regenerate) |
| `debate_log.jsonl` | Auto-generated flattened event log (derived from exchange JSON files) |
| `course_materials/SYLLABUS.md` | Course syllabus |
| `course_materials/sessions/` | 11 course sessions (`Session_00.md` through `Session_10.md`) |
| `course_materials/COURSE_MATERIALS_GUIDE.md` | Guide to course materials |
| `COURSE_PLAN.md` | Course planning document |

## Debate Agents

The debate system is orchestrated by four agents in `.claude/agents/`:

| Agent | Role |
|-------|------|
| `@pnp-moderator` | **Entry point.** Frames questions, invokes debaters, synthesizes results, consults Stan (Ulam) at critical junctures. |
| `@pnp-godel` | **Gödel** — formal skeptic. Challenges whether EGPT's formalization captures standard P vs NP. |
| `@pnp-jvm` | **Von Neumann** — constructive advocate. Defends EGPT's information-theoretic proof from code. |
| `@pnp-rota` | **Rota** — entropy advisor. Filters arguments through RET, validates entropy claims, runs JS experiments. |

The `@professor` agent (forthcoming) will teach this course.

## Conventions

- Invoke `@pnp-moderator` to start or continue a debate session.
- New exchanges go into `www/data/agentic-debate/exchange_live_NN.json` (with both `turns` and `events` arrays).
- Run `node www/GreatDebate/js/concordance-sync.js` after each session to regenerate `DEBATE_STATE.md`, `debate_log.jsonl`, and `www/data/concordance-data.js`.
- When debaters agree to try a concrete formalization, the moderator consults Stan and invokes `@egpt-orchestrator` to delegate implementation.
