# 18.313x Task Board

> Coordination layer between Cowork (strategy) and local Claude Code agents (implementation).

## Protocol

1. **Cowork writes briefs** → `briefs/NNN_description.md`
2. **Local agent reads brief** → implements or responds in `briefs/NNN_response.md`
3. **Both append to** `task_log.jsonl` with status updates
4. **This file** is the human-readable dashboard — regenerated from the log

---

## Active Tasks

| ID | Title | Status | Brief | Assigned To |
|----|-------|--------|-------|-------------|
| T002 | Design and implement TTS tagging system | assigned | [002](briefs/002_tts_tagging_system.md) | local agent |

## Completed Tasks

| ID | Title | Brief | Key Finding |
|----|-------|-------|-------------|
| T001 | Review TTS tool architecture | [001](briefs/001_tts_tool_review.md) | SSML upgrade path enables sub-sentence tag positioning via Google TTS timepoints. [Response](briefs/001_response.md) |

---

## Pipeline (upcoming briefs to be written by Cowork)

| ID | Title | Depends On | Notes |
|----|-------|------------|-------|
| T003 | Transcribe Session 0 audio + tag mapping | T002 | Transcribe the 37-min m4a, map segments to cross-reference events |
| T004 | Interactive lecture player (browser) | T002 | Reads tagged control.json, syncs audio with slides/demos/letters |
| T005 | @professor agent definition (Session 0 MVP) | T003, T004 | The agent that wraps everything |
| T006 | Build cross-reference table | T002 | cross_reference.jsonl from debate_log.jsonl — enables tag enrichment |
| T007 | Student fork + onboarding flow | T005 | Class repo fork, student profile creation, first @professor invocation |

---

## How to Use

**From Cowork (strategy side):**
- Reads repo state, brainstorms with Stan, writes briefs
- Briefs contain: Context, Task, Files to Read, Success Criteria, Constraints

**From local Claude Code (implementation side):**
- Reads brief, implements, writes response if needed
- Appends to `task_log.jsonl`: `{"id":"T002","status":"done","notes":"...","from":"local","date":"..."}`

**From Stan (human):**
- Reviews both sides, redirects as needed
- Can edit this board directly to reprioritize
