# Brief T002: Design and Implement TTS Tagging System

**From:** Cowork (strategy session with Stan)
**To:** Local Claude Code agent (via @egpt-orchestrator)
**Date:** 2026-03-16
**Priority:** High — enables the entire lecture delivery pipeline
**Depends on:** T001 (complete)

---

## Context

From T001 we learned:

1. The TTS tool (`DeSciXV2/Apps/SSG/TTS/app.js`) is a full-stack Express.js app using **Google Cloud TTS** (plain text → MP3) with a segment-based `control.json` manifest
2. **No SSML support currently** — but switching from `{ text }` to `{ ssml }` input is a one-line change in the TTS call
3. **Google TTS returns `timepoints`** when SSML `<mark>` tags are used with `enable_time_pointing: SSML_MARK` — giving us exact timestamps for tag positions in the audio
4. The parser (`parseTranscriptSegments`) is centralized — one place to add tag extraction
5. `control.json` is the natural insertion point for tag metadata
6. Word-level timestamps are available from the STT (Speech-to-Text) transcription side but are currently discarded
7. Lecture audio already exists: `SSG/18.313x/Session0/18.313_Intro_Session.m4a` (~37 min)

**Strategic decision from Cowork session:** This tool becomes an ongoing production tool for the 18.313x course. Every lecture draft gets tagged with cross-references to the EGPT repo — debate events, Lean symbols, historical letters, session thread keys. The tagged `control.json` becomes the data source for the interactive browser-based lecture player.

---

## Task

Implement the tagging system in three parts. **Do Part 1 first, get it working, then Part 2, then Part 3.** Report back after each part.

### Part 1: SSML Upgrade + Mark-Based Timing

**Goal:** Switch the TTS synthesis to SSML mode and capture `<mark>` timepoints.

**Changes to `app.js`:**

1. **Modify the synthesis call** (look for where `@google-cloud/text-to-speech` `synthesizeSpeech` is called):
   - Change `input: { text: segmentText }` to `input: { ssml: ssmlText }`
   - Add `enableTimePointing: ['SSML_MARK']` to the `audioConfig`
   - Capture `timepoints` from the response alongside the `audioContent`

2. **SSML wrapper function** — new function `textToSSML(text)`:
   - Wraps plain text in `<speak>...</speak>` tags
   - Passes through any existing `<mark name="..."/>` tags in the text
   - Escapes SSML special characters (`&`, `<`, `>`, `"`, `'`) in non-tag content
   - This means plain text input still works (just gets wrapped) and tagged text also works

3. **Store timepoints in control.json** — extend the segment schema:
   ```json
   {
     "number": 42,
     "label": "Professor",
     "text": "Rota spent thirty years building the entropy framework...",
     "filename": "0042-Professor-abc123.mp3",
     "url": "https://...",
     "startTime": "00:14:22,000",
     "endTime": "00:14:35,200",
     "preplaypause": 0.5,
     "timepoints": [
       {"markName": "ref:C3", "timeSeconds": 2.1},
       {"markName": "lean:RET_All_Entropy_Is_Scaled_Shannon_Entropy", "timeSeconds": 5.8}
     ]
   }
   ```

**Test:** Synthesize a segment with one `<mark name="test"/>` in the middle. Verify the response includes a timepoint. Verify the audio sounds correct (marks are silent).

### Part 2: Author-Friendly Tag Notation + Parser

**Goal:** Authors write readable inline tags in transcripts. The parser extracts them to SSML marks.

**Tag notation format:**
```
Speaker 1: Rota spent thirty years {{C3}} building the entropy framework.
He proved that all entropy is scaled Shannon entropy {{lean:RET_All_Entropy_Is_Scaled_Shannon_Entropy}}.
As Gödel wrote in 1956 {{letter:Godel_Letter_to_Von_Neumann}} to a dying von Neumann...
```

**Tag types:**
| Syntax | Meaning | Maps to |
|--------|---------|---------|
| `{{C3}}` | Debate event reference | `<mark name="debate:C3"/>` |
| `{{Y5}}` | Debate concession | `<mark name="debate:Y5"/>` |
| `{{IN12}}` | Debate insight | `<mark name="debate:IN12"/>` |
| `{{lean:symbol_name}}` | Lean theorem/def | `<mark name="lean:symbol_name"/>` |
| `{{letter:filename}}` | Historical document | `<mark name="letter:filename"/>` |
| `{{sim:demo_path}}` | Simulation/demo | `<mark name="sim:demo_path"/>` |
| `{{note:free_text}}` | Instructor note | `<mark name="note:free_text"/>` |

**Changes to `app.js`:**

1. **Extend `parseTranscriptSegments`:**
   - Regex to find `{{...}}` tags in segment text
   - Strip them from the display text (what the student reads)
   - Store them as a `tags` array on the segment object
   - When building SSML for synthesis, insert `<mark name="..."/>` at each tag position

2. **Extend `control.json` segment schema** — add alongside timepoints:
   ```json
   "tags": [
     {"type": "debate", "id": "C3", "position": 31, "label": "Rota's entropy principle"},
     {"type": "lean", "id": "RET_All_Entropy_Is_Scaled_Shannon_Entropy", "file": "Entropy/RET.lean"},
     {"type": "letter", "id": "Godel_Letter_to_Von_Neumann", "path": "content/SSG_History/JvM_Letters/Godel_Letter_to_Von_Neumann.md"}
   ]
   ```
   The `position` is the character offset in the clean (tag-stripped) text.

3. **After synthesis**, merge the tag metadata with the timepoints from Google TTS:
   ```json
   "tags": [
     {"type": "debate", "id": "C3", "timeSeconds": 2.1, "position": 31, "label": "Rota's entropy principle"}
   ]
   ```
   Now every tag has both a text position AND an audio timestamp.

**Test:** Write a 3-segment tagged transcript. Synthesize. Verify `control.json` has tags with timepoints. Verify stripping works (TTS speaks clean text, not the tag markers).

### Part 3: Tag Enrichment from EGPT Cross-Reference

**Goal:** Auto-populate tag labels and metadata from the EGPT repo's cross-reference data.

This part is **DEFERRED** until we build the cross-reference table (`cross_reference.jsonl`). For now, design the enrichment hook:

1. **Add a config field** in project settings: `crossReferenceSource` — path or URL to a JSONL file
2. **Add an enrichment function** `enrichTags(tags, crossRefData)` that:
   - Looks up `C3` in the cross-reference and adds `label`, `session`, `thread_key`
   - Looks up `lean:RET_All_Entropy_Is_Scaled_Shannon_Entropy` and adds `file`, `description`
   - Looks up `letter:Godel_Letter_to_Von_Neumann` and adds `path`, `excerpt`, `date`
3. **Stub it** — the function exists but returns tags unchanged until the cross-reference is available

**Do not implement the cross-reference lookup yet.** Just create the hook with a TODO comment pointing to `18.313x/tasks/briefs/` for the future brief.

---

## Files to Modify

| File | Changes |
|------|---------|
| `DeSciXV2/Apps/SSG/TTS/app.js` | SSML synthesis, tag parser, control.json schema, enrichment hook |
| `DeSciXV2/Apps/SSG/TTS/public/js/ui/srtTable.js` | (Optional) Tag display in segment table |
| `DeSciXV2/Apps/SSG/TTS/public/js/ui/playback.js` | (Optional) Tag event emission during playback |

## Files to Read First

- `DeSciXV2/Apps/SSG/TTS/app.js` (you already did in T001)
- `18.313x/tasks/briefs/001_response.md` (your own T001 findings)
- `18.313x/course_materials/COURSE_MATERIALS_GUIDE.md` (tag types map to these categories)
- `18.313x/debate_log.jsonl` (to see debate event ID format: C1-C27, Y1-Y14, IN1-IN20, etc.)

## Success Criteria

- [ ] Part 1: A segment with `<mark>` tags synthesizes correctly, timepoints appear in control.json
- [ ] Part 2: Author writes `{{C3}}` in transcript, TTS speaks clean text, control.json has tag with timepoint
- [ ] Part 3: `enrichTags()` stub exists and is called, returns tags passthrough
- [ ] Backward compatible: existing transcripts without tags still work identically
- [ ] No regressions in existing synthesis, playback, or editing workflows

## Constraints

- **Backward compatibility is mandatory.** Existing projects with plain text transcripts must work unchanged.
- **Keep the tag notation simple.** Authors (Essam and AI TAs) will write these by hand. `{{C3}}` is faster than `{{debate_event:C3:label="entropy principle"}}`.
- **Don't touch Google credentials or deployment config.** This is app logic only.
- **Test locally before deploying.** The GAE deployment can come later.

---

## Response Format

Write progress to `briefs/002_response.md` after each part.

Append to `18.313x/tasks/task_log.jsonl`:
```jsonl
{"id":"T002","status":"in_progress","notes":"Part 1 complete: SSML synthesis with timepoints working","from":"local","date":"2026-03-16"}
{"id":"T002","status":"in_progress","notes":"Part 2 complete: Tag notation parser and enriched control.json","from":"local","date":"2026-03-16"}
{"id":"T002","status":"done","notes":"All 3 parts complete. Tagged synthesis pipeline working.","from":"local","date":"2026-03-16"}
```
