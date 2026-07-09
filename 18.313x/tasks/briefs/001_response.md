# T001 Response: TTS Tool Architecture Review

**From:** Local Claude Code agent
**Date:** 2026-03-16
**Status:** Complete

---

## A. Architecture Overview

### What is it?

The TTS tool is a **full-stack web application** — an Express.js (v5) server (`app.js`, ~920 lines) with a browser-based editor UI (`public/`). It is titled "AI Conversation Editor" in the browser. It runs on Google App Engine (Node.js 22, `app.yaml` service name: `descix-tts`) with manual scaling (1 instance).

### Core Data Flow

```
                   ┌─────────────────────┐
                   │  Browser UI (SPA)   │
                   │  index.html + JS    │
                   └──────┬──────────────┘
                          │ REST API
                   ┌──────▼──────────────┐
                   │  Express Server     │
                   │  app.js             │
                   └──────┬──────────────┘
                          │
              ┌───────────┼───────────────┐
              ▼           ▼               ▼
     Google Cloud    Google Cloud     Google Cloud
     Speech-to-Text  Text-to-Speech   Storage (GCS)
     (transcribe)    (synthesize)     (all persistence)
```

### TTS Engine

**Google Cloud Text-to-Speech API** (`@google-cloud/text-to-speech` v6). Every synthesis call hits the API directly — plain text input (NOT SSML), `en-US` language code, MP3 output. No SSML, no prosody markup, no speech marks.

### Input Format

The tool accepts two transcript formats:
1. **Plain text** — speaker-labeled lines: `Speaker 1: Hello, welcome to the course.`
2. **SRT** — standard subtitle format with timestamps and optional speaker prefixes

The parser (`parseTranscriptSegments`) splits input into segments by speaker label. Speaker labels must match entries in a `speakerVoiceMap` to be recognized.

### Output

- **Audio:** Individual MP3 files per segment, stored in GCS at `TTS_App/projects/{projectId}/synth/{nnnn}-{label}-{hash}.mp3`
- **Control file:** `control.json` — a JSON manifest of all segments with metadata:

```json
{
  "segments": [
    {
      "number": 1,
      "label": "Girl 1",
      "filename": "001-Girl_1-1745155725843.mp3",
      "url": "https://storage.googleapis.com/descix-assets-public/TTS_uploads/...",
      "startTime": "00:00:00,000",
      "endTime": "00:00:01,410",
      "preplaypause": 0
    }
  ]
}
```

- **Timing data:** SRT timestamps are preserved if the input was SRT. `preplaypause` is calculated as the gap between the previous segment's end and the current segment's start (capped at 10 seconds). **No word-level timing** is produced — timing is segment-level only.

### GCS Storage Layout

```
descix-assets-public/
  TTS_App/
    projects/
      {projectId}.json          # Project metadata
      {projectId}/
        uploads/                # Original audio files
        transcripts/            # .txt and .srt files
        synth/
          control.json          # Segment manifest
          0001-Speaker_1-abc123.mp3
          0002-Speaker_2-def456.mp3
          ...
    voice_samples/              # Shared voice test cache (not project-specific)
```

---

## B. Current Capabilities

### Voice System

- Lists all `en-US` voices from the Google TTS API (`/voices` endpoint)
- Multiple voices supported via a **speaker-voice map**: each speaker label (e.g., "Girl 1", "Man 1") is assigned a Google TTS voice name (e.g., `en-US-Neural2-F`)
- Voice test/preview with caching in GCS (MD5 hash of voice+text)
- **No prosody control** — no SSML, no pitch/rate/volume adjustments. Just plain text → MP3

### Workflow

1. **Create project** (or select existing)
2. **Upload audio** → stored in GCS
3. **Transcribe** (optional) → Google Speech-to-Text with speaker diarization (1-10 speakers), word-level timestamps, auto-punctuation. Produces plain text transcript with `Speaker N:` prefixes
4. **Edit transcript** — two editor modes:
   - **Raw text editor** — edit the full transcript as text
   - **Segment table** — edit individual segments (number, start/end time, speaker, text) in a table UI
5. **Assign voices** — map each speaker label to a Google TTS voice
6. **Synthesize** — generate MP3 per segment, produce `control.json`
7. **Playback** — sequential segment-by-segment playback with `preplaypause` gaps

### Range Synthesis

Two synthesis endpoints:
- `/synthesize` — re-synthesizes from stored transcript, supports start/end segment range, handles partial regeneration (merges with existing control.json)
- `/synthesize-range` — takes explicit segment payloads from the frontend (number, label, text), synthesizes directly. Used for regenerating individual edited segments

### Batch vs Interactive

The tool is **interactive** — a web UI for editing and iterating. No CLI batch mode. But the API endpoints could be called programmatically.

### Existing Tag/Marker System

**None.** There is no concept of tags, annotations, cross-references, or metadata beyond the segment-level fields (`number`, `label`, `voice`, `startTime`, `endTime`, `preplaypause`, `filename`, `url`). The `control.json` schema is the closest thing to a structured manifest, but it has no extension points for arbitrary metadata.

---

## C. Related Files

### TTS Directory (`DeSciXV2/Apps/SSG/TTS/`)

| File | Purpose |
|------|---------|
| `app.js` | Express server — all backend logic (~920 lines) |
| `package.json` | Dependencies: `@google-cloud/speech`, `@google-cloud/text-to-speech`, `@google-cloud/storage`, `express@5`, `busboy`, `googleapis` |
| `app.yaml` | GAE config: Node 22, manual scaling 1 instance, service `descix-tts` |
| `dev-overrides.json` | DeSciX service key (ECDSA keypair, slot 1052, NFT type, community: descix) |
| `.gcloudignore` | Standard GAE ignore file |
| `public/index.html` | SPA shell — two-column layout (audio + playback left, editor + settings right) |
| `public/js/main.js` | State machine (~98KB) — the core frontend orchestrator |
| `public/js/api.js` | Fetch wrappers for all backend endpoints |
| `public/js/config.js` | Constants (bucket name, debounce timing) |
| `public/js/state.js` | Centralized `appState` object (playlist is source of truth) |
| `public/js/handlers.js` | DOM event listeners → action dispatcher |
| `public/js/utils.js` | Utilities (13KB) |
| `public/js/ui/audio.js` | Audio player UI |
| `public/js/ui/playback.js` | Segment playlist player (16KB) |
| `public/js/ui/speakers.js` | Speaker-voice mapping UI |
| `public/js/ui/srtTable.js` | Segment table editor (11KB) |
| `public/js/ui/synthesis.js` | Synthesis control UI |
| `public/js/ui/transcriptRaw.js` | Raw text editor UI |
| `public/js/ui/project.js` | Project selector UI |
| `public/js/ui/common.js` | Shared UI helpers |
| `public/css/style.css` | Styles |
| `public/debugcontrol.json` | Example control.json (7 segments from "Deep dive" project — "Girl 1" and "Man 1" speakers) |

### SSG Parent Directory (`DeSciXV2/Apps/SSG/`)

| Path | Purpose |
|------|---------|
| `Episode1/SSG EP1.srt` | SRT file for "SSG Podcast" Episode 1 — a deep-dive conversation about EGPT with "Woman 1" and "Man 1" speakers. This is a real production artifact. |
| `18.313x/Session0/18.313_Intro_Session.m4a` | **The actual intro lecture audio** (~71MB m4a). This is the first 18.313x lecture, already produced. |
| `TTS/` | The TTS tool itself |

### Key Observations

- **No connection to the EGPT repo yet.** The TTS tool is a standalone DeSciX app with no imports, references, or links to the P=NP proof, Lean files, or debate system.
- The `dev-overrides.json` contains a DeSciX service key (ECDSA, slot 1052) — this is the DeSciX community membership/authorization system, not Google credentials. Google auth is handled via ADC (Application Default Credentials).
- The existing `18.313_Intro_Session.m4a` in `SSG/18.313x/Session0/` proves the tool has already been used to produce course audio.

---

## D. Integration Points

### Where cross-reference tags would fit

**The `control.json` schema is the natural insertion point.** Each segment already has structured fields. Adding cross-reference metadata would extend the segment schema:

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
  "tags": [
    {"type": "debate_ref", "id": "C3", "session": 0, "label": "Rota's entropy principle"},
    {"type": "lean_symbol", "id": "walkComplexity_upper_bound", "file": "PPNP.lean"},
    {"type": "letter_ref", "id": "godel_to_vonneumann_1931"}
  ]
}
```

### Timing Capabilities

- **Segment-level timing:** Available when SRT input is used. Start/end times in `HH:MM:SS,mmm` format.
- **Word-level timing:** The Speech-to-Text transcription endpoint (`/transcribe-gcs`) requests `enableWordTimeOffsets: true` from the Google API — **word-level timestamps are available from the STT side** but are currently discarded after constructing the plain text transcript. They are not stored or forwarded.
- **No timing from TTS:** The Google TTS API as currently configured returns only MP3 audio. Google TTS does support `timepoints` (sentence-level) when SSML `<mark>` tags are used, but this is not enabled.

### What would need to change for tagged output

1. **Input pipeline:** A tag notation system in the transcript text (e.g., inline markers like `[ref:C3]` or `[lean:walkComplexity_upper_bound]`) that the parser strips before sending to TTS but preserves in control.json
2. **`control.json` schema:** Add a `tags` array (or similar) to each segment object
3. **`parseTranscriptSegments`:** Extend to extract tag markers from text
4. **Frontend UI:** The segment table already has columns (#, Start, End, Speaker, Text, Actions) — a Tags column or tag editor would need to be added
5. **Playback:** The frontend playback system would need to emit tag events at the right timestamps for the browser lecture player to consume

### API-level integration is straightforward

The REST API is clean and well-structured. A new lecture production pipeline could:
1. POST tagged transcript to `/upload-transcript`
2. POST to `/synthesize-range` with segments
3. GET `/control/{projectId}` to retrieve the tagged manifest
4. Feed the manifest to an interactive lecture player

---

## E. Recommendations

### How hard to add tagging?

**Medium difficulty.** The architecture is well-suited for extension:
- `control.json` is already a structured manifest — adding fields is trivial
- The parser is centralized (`parseTranscriptSegments`) — one place to add tag extraction
- The segment table UI already supports per-segment editing
- The backend API is RESTful and stateless

The hardest part is **designing the tag format for the input transcript** — it needs to be human-readable (authors write the tags in the text) and machine-parseable (the parser extracts them cleanly before TTS synthesis).

### Path from "draft audio" to "tagged, time-synced lecture asset"

```
1. Author writes tagged transcript
   "Rota spent 30 years [ref:C3] building the entropy framework [lean:RET_bijection]..."

2. Parser extracts tags, strips them from TTS input, preserves in control.json

3. TTS synthesizes clean audio (tags are invisible to TTS engine)

4. control.json contains both audio URLs and tag positions
   (segment-level initially; word-level possible with SSML <mark> tags)

5. Lecture player reads control.json, plays audio, fires tag events at timestamps

6. Browser UI shows cross-references, Lean symbol links, letter images on cue
```

### Limitations to know

| Limitation | Impact | Mitigation |
|------------|--------|------------|
| **No word-level timing from TTS** | Tags can only be positioned at segment boundaries, not mid-sentence | Use SSML `<mark>` tags + `enable_time_pointing: SSML_MARK` in audioConfig to get sentence-level marks. Or post-process with forced alignment. |
| **Google TTS pricing** | Standard voices: $4/1M chars; WaveNet: $16/1M chars; Neural2: ~$16/1M chars | A 1-hour lecture ≈ 9,000 words ≈ 45,000 chars ≈ $0.18-$0.72 per full synthesis. Re-synthesis of edited segments is cheap. |
| **No SSML support currently** | Plain text only — no prosody control, no emphasis, no pauses beyond preplaypause gaps | Adding SSML support is straightforward (change `input: { text }` to `input: { ssml }` in the TTS call). This would also enable `<mark>` tags for timing. |
| **en-US only** | Language code is hardcoded | Parameterize `languageCode` in project settings |
| **Single GAE instance** | Manual scaling at 1 instance, no auto-scaling | Fine for authoring tool; would need scaling for student-facing use |
| **No authentication** | The Express app has no auth middleware | Only matters if exposed publicly; currently appears to be an internal authoring tool |
| **Frontend is a monolith** | `main.js` is ~98KB — a single state machine file | Not blocking for tag integration, but worth noting for maintenance |

### Key Insight for T002

The **SSML upgrade path** is the most important finding. If we switch from `{ text }` to `{ ssml }` input and use SSML `<mark name="ref:C3"/>` tags, Google TTS will return `timepoints` in the response — giving us the exact timestamps where each tag occurs in the audio. This eliminates the need for post-processing alignment and gives us sub-sentence tag positioning for free.

This means the tag system design (T002) should account for SSML as the internal representation, even if authors write in a simpler inline notation.
