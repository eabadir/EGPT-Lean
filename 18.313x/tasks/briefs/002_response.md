# T002 Response: TTS Tagging System Implementation

**From:** Local Claude Code agent
**Date:** 2026-03-16
**Status:** Complete (all 3 parts)

---

## Phase 0: SSG-Studio Repo Created

Forked the TTS tool from `DeSciXV2/Apps/SSG/TTS/` into a standalone repo:
- **Location:** `/Users/essam/Documents/Code/PnPproofs/SSG-Studio/`
- **Initial commit:** `6d67df4` — rebranded to `ssg-studio`, added .gitignore, example SRT
- Session 0 audio (68MB m4a) is gitignored but present locally
- GitHub remote creation deferred (`gh` CLI not installed)

## Part 1: SSML Upgrade + Mark-Based Timing — DONE

**Commit:** `70855a3`

### Changes to `app.js`

Added 4 new helper functions before the voice sample caching section:

1. **`parseAuthorTags(text)`** — Regex parser for `{{tag}}` notation. Returns `{cleanText, tags}`. Infers type from prefix (`lean:`, `letter:`, `sim:`, `note:`) or bare debate ID patterns (`C3`, `Y5`, `IN12`, `OQ1`, `F2`, `I5`).

2. **`escapeSsml(text)`** — Escapes `&<>"'` for SSML safety.

3. **`buildTaggedSsml(cleanText, tags)`** — Inserts `<mark name="type:id"/>` at tag positions, wraps in `<speak>`, escapes non-mark text. If no tags, produces plain `<speak>escapedText</speak>`.

4. **`mergeTimepointsWithTags(timepoints, tags)`** — Joins Google TTS timepoints with parsed tags by mark name.

### Modified synthesis endpoints

Both `/synthesize` (~line 740) and `/synthesize-range` (~line 940):
- Parse tags from segment text before synthesis
- Build SSML via `buildTaggedSsml()`
- Set `enableTimePointing: ['SSML_MARK']` when tags are present
- Capture `response.timepoints` and merge with tags
- Store `tags` and `timepoints` arrays on segment data in control.json

### Backward compatibility

- `parseAuthorTags` returns unchanged text when no `{{tags}}` found
- `buildTaggedSsml` with empty tags array produces `<speak>escapedText</speak>` — valid SSML wrapping of plain text
- Existing segments in control.json without `tags`/`timepoints` fields load fine (fields are optional)

## Part 2: Author-Friendly Tag Notation + Parser — DONE

Included in Part 1 implementation. The `parseAuthorTags()` function handles:

| Notation | Parsed Type | Parsed ID |
|----------|------------|-----------|
| `{{C3}}` | `debate` | `C3` |
| `{{Y5}}` | `debate` | `Y5` |
| `{{IN12}}` | `debate` | `IN12` |
| `{{lean:P_eq_NP}}` | `lean` | `P_eq_NP` |
| `{{letter:Godel_1956}}` | `letter` | `Godel_1956` |
| `{{sim:circuit_sat}}` | `sim` | `circuit_sat` |
| `{{note:key point}}` | `note` | `key point` |
| `{{anything_else}}` | `custom` | `anything_else` |

### Frontend: Tags column in segment table

- **New file:** `public/js/ui/tags.js` — client-side tag parser (mirrors server), badge renderer with color coding (debate=blue, lean=green, letter=amber, sim=purple)
- **Modified:** `public/js/ui/srtTable.js` — imports `renderTagsColumn`, adds Tags column after Text
- **Modified:** `public/index.html` — added `<th>Tags</th>` to table header, updated colspan

## Part 3: Tag Enrichment Hook (Stub) — DONE

Added `enrichTags(tags, crossRefData)` function — currently a passthrough that returns tags unchanged. Has TODO comment pointing to T006 (cross-reference table) for future implementation.

---

## What's Next

The SSML + tag infrastructure is in place. To verify end-to-end:

1. `cd /Users/essam/Documents/Code/PnPproofs/SSG-Studio && npm install && npm start`
2. Open `http://localhost:3000`
3. Create a project, add a transcript with `{{C3}}` tags
4. Synthesize → check that control.json has `tags` and `timepoints` arrays
5. Segment table should show colored tag badges

The remaining pipeline phases (NotebookLM import, MCP chat, video export) are tracked in the implementation plan at `.claude/plans/parallel-forging-hellman.md`.
