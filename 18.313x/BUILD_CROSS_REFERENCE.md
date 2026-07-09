# Cross-Reference Build Prompt

Paste this into Claude Code to build the cross-reference table. It will parallelize into 4 sub-agents + 1 assembler.

---

## Prompt

```
Read 18.313x/CROSS_REFERENCE_PLAN.md — this is the full build plan for a cross-reference table linking the P=NP debate events to historical letters, Lean code, and philosophical context.

The plan defines 9 narrative threads — each is a universally compelling human question ("Can a machine replace a mathematician?", "Does stating a problem solve it?", etc.) that connects historical letters to specific Lean theorems. Every one of the 82 debate events maps to a thread.

Execute the plan in parallel:

1. Create the _build directory: mkdir -p 18.313x/_build

2. Launch 4 parallel sub-agents:

**Agent 1 — Letter Excerpts:** Read all files listed under "Historical Letters" in the plan. For each of the 9 narrative threads, find 1-3 short excerpt markers (< 15 words each, just enough to locate the passage — NOT full quotes) from the relevant letters. The plan names the primary letters for each thread and gives the flavor. Write output to 18.313x/_build/letter_excerpts.jsonl, one JSON line per excerpt: {"thread": "...", "file": "...", "author": "...", "date": "...", "excerpt_marker": "..."}. If a thread has no direct letter reference (Thread 5 "asking_about_nothing"), write {"thread": "...", "file": null, "note": "Insight emerged from the debate itself, not a specific letter"}.

**Agent 2 — Lean Code References:** Read the Lean files listed in the plan. For each of the 9 threads, verify the key symbols listed in the thread description exist (grep for each symbol in its file), get the line number, and write a 1-line comment a non-specialist could understand — connect the symbol to the human question, not just describe what it does. Write output to 18.313x/_build/lean_refs.jsonl, one JSON line per ref: {"thread": "...", "file": "...", "symbol": "...", "line": N, "comment": "..."}. Example good comment: "The walk cost is ≤ n². Gödel guessed KN² in 1956. The bound is the same." Example bad comment: "Upper bound on walk complexity."

**Agent 3 — Historical Context:** Read the historical documents and the thread descriptions. For each of the 9 threads, write a 2-4 sentence historical context paragraph that a developer would find compelling. This bridges the human question → the historical moment → the code. It should be evocative and precise — the developer should feel the weight of the history and see exactly how it connects to the theorem they're about to look at. Write output to 18.313x/_build/historical_context.jsonl, one JSON line per thread: {"thread": "...", "context": "..."}.

**Agent 4 — Mapping Validator:** Read 18.313x/debate_log.jsonl and the "Event-to-Thread Mapping" tables in the plan. For each of the 82 events, verify the thread assignment makes sense. Flag any that seem misassigned. Write output to 18.313x/_build/mapping_validation.jsonl, one JSON line per event: {"event_id": "...", "assigned_thread": "...", "valid": true/false, "suggested_thread": "...", "reason": "..."}.

3. After all 4 agents complete, run the assembler:

**Assembler:** Read all 4 _build/*.jsonl files plus 18.313x/debate_log.jsonl plus the mapping tables from the plan. For each of the 82 debate events:
- Look up its primary and secondary thread(s) from the mapping tables (corrected by Agent 4 if needed)
- Attach letter excerpts for those threads (from Agent 1)
- Attach Lean refs for those threads (from Agent 2)
- Attach historical context for the primary thread (from Agent 3)
- Write the joined record to 18.313x/cross_reference.jsonl

Then generate 18.313x/CROSS_REFERENCE.md — a human-readable document organized by thread. For each thread:
- The question (thread name) as a section header
- Historical context paragraph (from Agent 3)
- Letter references with excerpt markers
- Key Lean symbols with non-specialist comments
- Table of debate events belonging to this thread (id, type, text, exchange)

The document should read like a guide for a developer who just cloned the repo and wants to understand why this code exists and what questions it answers. Each thread section should feel like opening a door.

Finally verify: every event_id from debate_log.jsonl appears in cross_reference.jsonl. Every thread has at least one event. Every letter file path exists. Every Lean symbol can be grep'd in its file.

Report any gaps or issues found during verification.
```
