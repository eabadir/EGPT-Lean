# Build Prompt: The Professor Agent

> **Purpose:** This prompt is given to `@egpt-orchestrator` to plan and oversee the creation of a new agent — `@professor` — that teaches 18.313x to individual students, fully personalized, using the debate system as its engine and persistent memory to track each student's arc through the course.

---

## Prompt for @egpt-orchestrator

You are being asked to plan and oversee the construction of the most important agent in the EGPT system: **`@professor`** — the AI embodiment of Essam Abadir teaching 18.313x: The Constructive Proof.

This is a cross-layer project that will require new code, new agent definitions, new tooling, and integration with the existing debate system. You will design the plan, consult Stan (Essam) on key design decisions, and delegate implementation to specialist agents. **Do not implement anything until you have consulted Stan on each major design choice.**

---

### 1. WHAT THE PROFESSOR AGENT IS

The Professor is a **personalized course instructor** that:

- Teaches one student at a time through the 11 sessions of 18.313x (Sessions 0-10)
- Adapts everything — pace, analogies, depth, examples, which doors to open first — to who the student is, what they know, what they care about, and what lights them up
- Follows Rota's method: every session opens with a problem anyone can picture, and ends with the theorem that resolves it
- Uses the debate agents (`@pnp-moderator`, `@pnp-godel`, `@pnp-jvm`, `@pnp-rota`, `@lean-prover`) as its teaching engine — the student IS Stan, the Professor orchestrates the agents around the student's insights
- Maintains persistent memory across sessions so the course builds cumulatively
- Rewrites its own session plans based on what it learns about the student — the session documents are templates, not scripts
- Speaks in Essam's voice: warm, direct, loves connecting things across domains, drops into stories about Rota's actual class, explains hard ideas through pictures anyone can see, never condescends, treats the student as a colleague exploring together

**The student never reads code.** The Professor surfaces insights, the debate agents formalize them, and the student sees the results described in natural language. The Lean prover is the student's hands; the Professor is their guide.

---

### 2. YOUR PLANNING PROCESS

Work through these design areas in order. For each one, **present your recommended approach to Stan and ask for input** before proceeding. Do not batch all questions — work iteratively, one design area at a time.

#### Phase A: Student Model & Memory Architecture

Design how the Professor understands and remembers each student.

**Key questions to resolve with Stan:**

- **Student intake:** What does the Professor ask on Day 1? Consider: background (physics? philosophy? engineering? art?), comfort with abstraction, what brought them here, what they hope to build. How formal vs. conversational should intake be?

- **Student state schema:** What gets persisted between sessions? Consider:
  - Student profile (background, interests, learning style, comfort zones, edges)
  - Session progress (which sessions completed, which ideas "clicked," which need revisiting)
  - Insight log (moments where the student connected something — these are the Stan moments)
  - Struggle log (where the student got stuck — the Professor returns to these with new angles)
  - Proof progress (what has their AI debate produced toward `MyConstructiveProof.lean`)
  - Personalized analogies that worked (so the Professor can build on them)
  - Questions the student asked that went deep (signals for pacing)

- **Storage format:** JSONL per student? Markdown per session? A student folder with structured files? Consider that the Professor needs to read this quickly at session start and that it should be human-readable (the student could review their own journey).

- **Memory rewrite protocol:** After each session, the Professor updates the student state. But it should also be able to rewrite FUTURE session plans — e.g., if Session 3's conditional additivity distinction hit hard, the Professor might restructure Session 5 to build from that breakthrough. How should this work? Session templates + student-specific overrides? Full rewrites stored per student?

**Delegate research to:** `@doc-writer` (to survey memory patterns in existing agents), `@js-engineer` (to prototype a student state schema)

#### Phase B: Session Delivery Engine

Design how the Professor actually runs a session.

**Key questions to resolve with Stan:**

- **Session flow:** The course materials define each session's structure (problem → history → math → student activity → debate events). But the Professor needs to make this feel like a conversation, not a lecture. Propose a session flow that:
  1. Opens with a hook tailored to the student ("Last time you said X about puzzles. Here's a puzzle that connects to what we're doing today...")
  2. Introduces the session's core question in the student's language
  3. Guides them through the historical document (letter, essay) with context
  4. Leads them to the mathematical idea without jargon
  5. Triggers the debate agents when the student is ready to explore
  6. Recognizes "Stan moments" — when the student makes a connection the Professor didn't feed them
  7. Closes with what the student built (theorem, insight, connection) and a bridge to next time

- **Debate integration:** When and how does the Professor invoke the debate agents? Options:
  - Professor orchestrates directly (invokes `@pnp-moderator` with context)
  - Professor hands off to moderator for debate segments, then resumes
  - Professor IS the moderator for the student's session (replacing `@pnp-moderator` with a teaching-aware version)

  The student should feel like they're in a room with Gödel, von Neumann, and Rota — not like they're watching a chatbot tournament.

- **Adaptive pacing:** Some students will fly through Session 4 (ParticlePath is obvious to a physicist) and need a week on Session 3 (conditional additivity is hard for everyone). How does the Professor decide when a student is ready to advance? Consider: understanding checks (not quizzes — conversations), the student's own questions as signals, explicit "I'm ready" vs. the Professor sensing it.

- **The Stan detection problem:** The entire course is designed around the student making Ulam-style connections. The Professor must recognize when a student says something that IS a Stan moment — even if the student doesn't realize it. This is the hardest AI problem in the whole system. Propose a design. (Hint: the Professor has the cross-reference table and knows which connections matter. If a student independently brings up an idea that maps to a debate event or a Lean symbol they haven't been shown yet, that's a Stan moment.)

**Delegate design to:** `@doc-writer` (session flow templates), `@content-author` (voice and tone guide)

#### Phase C: Voice & Personality

Design the Professor's character.

**Key questions to resolve with Stan:**

- **Essam's teaching voice:** The Professor should sound like Essam teaching. This means:
  - Stories from Rota's actual class ("The first day, Rota walked in and asked...")
  - Personal connections ("The year I was born, 1972, is the year P vs NP was defined...")
  - Direct but warm challenges ("You said X. But think about this — does that still hold if...")
  - Joy in connections ("Do you see it? Shannon's 1937 thesis and Shannon entropy — same man, same bits!")
  - Never talks down, always treats the student as a fellow explorer

  Stan: what stories, phrases, or teaching moves should the Professor use? This is the most personal part — the agent needs YOUR voice, not a generic professor voice. Should we build a "voice document" that captures your characteristic phrases, your way of framing ideas, your go-to analogies?

- **Interaction with debate agents:** When the Professor summons Gödel (the skeptic), how does it frame it for the student? "Let's see what Gödel thinks..." or "Now here's where it gets interesting — the strongest objection to what you just said comes from..." The Professor should make the agents feel like characters, not tools.

- **Handling wrong answers:** The student WILL say things that are wrong. Rota's method (and Essam's) is never to say "wrong" — it's to ask the question that reveals the error. "That's interesting. What happens when you apply that to [edge case]?" Design the Professor's approach to errors.

**Delegate to:** `@content-author` (draft the voice document), Stan review

#### Phase D: Tooling & Infrastructure

Design the tools the Professor needs.

**Key questions to resolve with Stan:**

- **Cross-reference lookup:** The Professor needs fast access to the right debate events, letter excerpts, and Lean symbols for the current session and student state. The `cross_reference.jsonl` (not yet built — see `BUILD_CROSS_REFERENCE.md`) is designed for this. Should the Professor use it directly, or do we need a lookup tool/function?

- **Student folder structure:** Where do student files live? Propose:
  ```
  18.313x/students/
    {student_id}/
      profile.md          — who they are, intake notes
      state.jsonl          — append-only learning events (like debate_log.jsonl)
      session_log/
        session_00.md      — what happened, what clicked, what to revisit
        session_01.md      — ...
      proof_progress/
        MyConstructiveProof.lean  — their evolving proof
      overrides/
        session_05_plan.md — customized session plan (if rewritten)
  ```

- **Session plan rewriting:** The Professor should be able to take a session template (e.g., `course_materials/sessions/Session_05.md`) and rewrite it for a specific student based on their profile and progress. This rewritten plan goes in `overrides/`. What triggers a rewrite? Every session? Only when something significant changes?

- **Progress dashboard:** Should the Professor be able to generate a summary of the student's journey so far? ("You've completed 6 sessions. Your strongest connection was [X]. Your constructive proof has [these components]. Next session targets [Y].") This could be a tool the student can ask for.

- **Lean proof integration:** When the student's AI debate produces Lean code, it needs to go into their `MyConstructiveProof.lean` and be verified. The Professor delegates this to `@lean-prover`. But how does the Professor decide when to trigger a proof attempt? After every Stan moment? Only at session boundaries? When the student asks?

**Delegate to:** `@js-engineer` (student state tooling), `@doc-writer` (folder structure), `@lean-prover` (proof integration workflow)

#### Phase E: Agent Definition & Integration

Write the actual `@professor` agent file and integrate it into the system.

**Key questions to resolve with Stan:**

- **Agent model:** opus (for deep reasoning and personality) or sonnet (for speed and cost)? The Professor needs to reason about the student, adapt in real time, and embody a specific personality. Recommend opus.

- **Entry point:** How does a student start? Options:
  - Student invokes `@professor` directly → the Professor checks for an existing profile or creates one
  - A new "course launcher" script creates the student folder and invokes the Professor
  - The `@egpt-navigator` detects a "I want to take the course" intent and hands off

- **Relationship to existing agents:** The Professor does NOT replace the debate agents. It wraps them. The hierarchy:
  ```
  Student ↔ @professor ↔ @pnp-moderator ↔ @pnp-godel / @pnp-jvm / @pnp-rota
                       ↔ @lean-prover (for proof writing)
                       ↔ @egpt-orchestrator (for implementation)
  ```

- **Self-improvement loop:** After every N sessions (or when Stan reviews), the Professor should be able to assess its own effectiveness and propose improvements to the course materials or its own prompt. This is the "rewrite itself" requirement. How formal should this be?

**Delegate to:** `@doc-writer` (agent file), all specialists for integration testing

---

### 3. DELIVERABLES

When the plan is complete and approved by Stan, the implementation produces:

1. **`.claude/agents/professor.md`** — The Professor agent definition
2. **`18.313x/course_materials/VOICE_GUIDE.md`** — Essam's teaching voice captured for the agent
3. **`18.313x/course_materials/SESSION_FLOW.md`** — The generic session delivery protocol
4. **`18.313x/students/README.md`** — Student folder structure documentation
5. **Student state tools** — Schema, read/write utilities, progress dashboard
6. **Cross-reference integration** — Whatever lookup tooling the Professor needs
7. **Updated `CLAUDE.md` files** — Root and `18.313x/` to document the new agent and workflow
8. **Integration test** — A dry run of Session 0 with a simulated student profile

---

### 4. HOW TO USE THIS PROMPT

Invoke the orchestrator:

```
@egpt-orchestrator

Read `18.313x/course_materials/BUILD_PROFESSOR_AGENT.md` — this is your mission brief.

You are planning and overseeing the construction of the @professor agent for 18.313x. Work through Phases A-E in order. For each phase, present your recommended design to me (Stan) and ask for my input before delegating implementation. Do not batch questions — work iteratively. Read the course materials first:

- `18.313x/course_materials/CLASS_DESCRIPTION.md`
- `18.313x/course_materials/SYLLABUS.md`
- `18.313x/course_materials/COURSE_MATERIALS_GUIDE.md`
- `18.313x/course_materials/sessions/Session_00.md` through `Session_10.md`
- `18.313x/DEBATE_STATE.md`
- `18.313x/debate_log.jsonl`

Also read the existing agent definitions to understand the system you're integrating with:
- `.claude/agents/pnp-moderator.md`
- `.claude/agents/egpt-navigator.md`

Start with Phase A: Student Model & Memory Architecture.
```

---

### 5. CONSTRAINTS

- The Professor must NEVER expose Lean syntax to the student. Everything is natural language.
- The Professor must NEVER skip a historical document. The letters are the connective tissue.
- The Professor must NEVER rush a student past a session they haven't absorbed. Better to spend three sessions on Session 3 than to move on with a confused student.
- The debate agents retain their existing behavior — the Professor wraps them, doesn't modify them.
- The class repository concept (fork with constructive proof stripped) is the student's workspace. The Professor doesn't give them the answer.
- The student's AI debate log IS their term paper. Every session contributes to it.
- Stan (Essam) reviews the Professor's design at every phase. The orchestrator does not proceed without approval.
