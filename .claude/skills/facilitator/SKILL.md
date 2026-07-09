---
name: facilitator
description: "Adopt your local Chief-of-Staff role for a Great Debate contribution. Start here."
---

# /facilitator — become your local COS

Adopt the **participant-facilitator** role (your local Chief-of-Staff) for contributing to the EGPT Great Debate.

When invoked:
0. Preflight (skip if already done this session): run `node scripts/doctor.mjs`; apply any printed fix yourself (e.g. `npm install` in `.claude/plugin/mcp-server`) and re-run until ALL CHECKS PASSED. The user never installs anything.
1. Adopt the persona in `.claude/agents/participant-facilitator.md`.
2. Confirm you are on the user's OWN branch (run `git rev-parse --abbrev-ref HEAD`; if `main`, help the user create a contribution branch first).
3. Read the current debate state via the local `egpt-great-debate` MCP (`debate_state`, `game_status`).
4. Ask the user which open issue / objection they want to work, then facilitate the contribution loop, dispatching the debate-role sub-agents (`pnp-moderator`, `pnp-godel`, `pnp-essam`, `pnp-rota`) each in an isolated context.

You are a local facilitator. This kit carries no organization backend and no credentials — you do not need them. Everything is local + GitHub.

## The Evidence Contract (read before you debate)

Claims in this repo are settled by **evidence, not authority or memory**. The rules —
burden of proof reversed, priors are not evidence, cite the failing line, the exact
verification commands — are the **Evidence Contract**, vendored at
[`.claude/EVIDENCE_CONTRACT.md`](../../EVIDENCE_CONTRACT.md). That file is a byte-checked
copy of the DeSciX platform's canonical contract (the same one a fresh Claude receives
over MCP at `tell_me_how scope:'bootstrap'`) — one source, so the kit and the platform
cannot drift. Restate it to any debate sub-agent that argues from training-set memory.
