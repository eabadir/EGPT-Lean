# Brief T001: Review TTS Tool and Explain Its Architecture

**From:** Cowork (strategy session with Stan)
**To:** Local Claude Code agent
**Date:** 2026-03-16
**Priority:** High — this is the foundation for the lecture delivery system

---

## Context

We are building an AI professor agent (`@professor`) for the 18.313x course (P=NP constructive proof). The professor will deliver interactive, personalized lectures to students. A key component is audio lectures recorded by Essam's AI TAs, delivered via a podcast/RSS feed, with time-synced interactive content in the browser.

The TTS tool at `/Users/essam/Documents/Code/DeSciXV2/Apps/SSG/TTS/app.js` is central to this workflow. It is used to produce the lecture audio drafts. We need to understand it thoroughly before we can:

1. Add cross-reference data tags to the audio content (linking lecture moments to debate events, Lean symbols, historical letters)
2. Make it an ongoing production tool for generating tagged lecture audio
3. Build the interactive browser-based lecture player that syncs with these tags

## Task

**Read and explain the TTS tool comprehensively.** Produce a response brief (`briefs/001_response.md`) that covers:

### A. Architecture Overview
- What does `app.js` do? What is the full application structure?
- What TTS engine/API does it use?
- What input format does it expect? (Plain text? SSML? Markdown? Something custom?)
- What output does it produce? (Audio format, metadata, timestamps?)
- Does it already produce any timing/alignment data (word-level timestamps, segment markers)?

### B. Current Capabilities
- What configuration options exist?
- Does it support multiple voices? Voice styles? Prosody control?
- What's the workflow: text in → ? → audio out?
- Are there any existing tag or marker systems in the input format?
- Does it batch process or work interactively?

### C. Related Files
- What other files are in the `/Users/essam/Documents/Code/DeSciXV2/Apps/SSG/TTS/` directory?
- Are there config files, templates, or example inputs?
- What dependencies does it have? (package.json, APIs, credentials)
- Is there any connection to the EGPT repo already?

### D. Integration Points
- Where would cross-reference tags naturally fit in the input pipeline?
- Does the TTS API provide word-level or sentence-level timing that we could use for sync?
- What would need to change to support output like:
  ```json
  {"time": 145.2, "text": "Rota spent 30 years...", "cross_ref": "C3", "session": 0}
  {"time": 312.8, "text": "walkComplexity_upper_bound", "lean_symbol": true}
  ```

### E. Recommendations
- How hard would it be to add a tagging system to the input format?
- What's the path from "draft audio" to "tagged, time-synced lecture asset"?
- Any limitations we should know about (rate limits, cost per minute, quality constraints)?

## Files to Read

- `/Users/essam/Documents/Code/DeSciXV2/Apps/SSG/TTS/app.js` (primary)
- Everything else in that `TTS/` directory (package.json, configs, examples, etc.)
- Scan `/Users/essam/Documents/Code/DeSciXV2/Apps/SSG/` for related context (what is SSG? What else is in the DeSciX app suite?)

## Success Criteria

- A `briefs/001_response.md` file in this repo that gives Cowork enough information to design the tagged lecture system without needing to read the TTS code directly
- Specific enough that we can write the next brief (T002: "Add cross-reference tagging to TTS tool") based on your findings

## Constraints

- **Read only.** Do not modify the TTS tool yet. We need to understand before we change.
- Report what IS there, not what you think should be there. We'll design changes in the next brief.
- If you can't access the file path, report that — Stan may need to grant access or share the file.

---

## Response Format

Write your response to: `18.313x/tasks/briefs/001_response.md`

Then append to `18.313x/tasks/task_log.jsonl`:
```jsonl
{"id":"T001","status":"done","notes":"Response written to briefs/001_response.md","from":"local","date":"2026-03-16"}
```
