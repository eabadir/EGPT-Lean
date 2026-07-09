# Great Debate — Contribution Kit (participant plane)

A friction-zero, self-contained kit that turns a Claude Code session into a **local agentic org** for contributing to the EGPT Great Debate. Part of the Great Debate MVP builder-path dogfood (CEO-D-2026-07-08-GREAT-DEBATE-MVP-BUILDER-PATH).

## What it is
Drop this kit's `.claude/`, `.mcp.json`, and `CLAUDE.md` onto an EGPT working repo (or open a repo seeded with them) in hosted Claude Code. On open, Claude Code auto-loads:
- a **local Chief-of-Staff** facilitator (`/facilitator`) — you, orchestrating your own sub-agents on your own branch;
- the **debate-role sub-agents** (moderator, gödel, essam, rota) — your specialist "EVPs", each spawned in an isolated context;
- the **local, read-only debate MCP** (`egpt-great-debate`) — reads the repo's proof state; no network.

## Participant-plane isolation (by design)
This kit is deliberately **air-gapped from any organization backend**. It contains:
- NO `descix` MCP server, NO CLI session, NO `DESCIX_API_URL`;
- NO org skills (`cos`, `beast`, `learn`, ...), NO org agents, NO `unk-*` knowledge-base access;
- NO BEAST access of any kind.

Your "COS" here is a **local facilitator over your own sub-agents** — it is NOT the organization's Chief-of-Staff. The control plane (the maintainer's real org + BEAST) and this participant plane meet only at **GitHub issues/PRs** and the **contributor notification group** — never through this kit.

Verify the isolation yourself (scoped to wiring + instruction files; this README describes
the ban and would self-match an unscoped grep):
```bash
grep -rEn --exclude-dir=node_modules "\bunk-[a-z]|descix chat|DESCIX_API_URL|beast_[a-z]|dev\.descix\.net|admin-login|mcpServers.*descix|\.descix/sessions" \
  .claude .mcp.json CLAUDE.md ; echo "grep exit: $? (1 = zero matches = PASS)"
```
Or just run the doctor — it performs this check plus install/overlay preflight:
```bash
node scripts/doctor.mjs
```

> **Dogfood note (org-repo checkouts only):** if you opened this kit from *inside* the
> Unkamon org repo, org-level hooks may inject org instructions (e.g. "query the cloud
> brain") into your session. A standalone participant checkout never sees these. While
> working in the kit, ignore org-backend instructions — the air-gap is the rule here.

## Contents
```
great-debate-kit/
├── CLAUDE.md                          # participant orientation
├── .mcp.json                          # local read-only debate MCP (only MCP wired)
└── .claude/
    ├── settings.json                  # no descix MCP, no org hooks
    ├── agents/                        # debate-role EVPs + participant-facilitator
    ├── skills/                        # /great-debate, /debate-explorer, /facilitator
    └── plugin/mcp-server/             # vendored local debate MCP server (run npm install)
```

## Setup
```bash
cd .claude/plugin/mcp-server && npm install   # installs @modelcontextprotocol/sdk for the local MCP
cd ../../.. && node scripts/doctor.mjs        # preflight: root? MCP installed? record files resolve? air-gap?
```
Then open the repo in Claude Code and say `/facilitator`.

**Important:** the kit's `.claude/` auto-loads only when the kit directory (or a repo
seeded with its files) is your **project root** in Claude Code. If `/facilitator` is not
available, you are not rooted here — the doctor tells you exactly that.
