# Design: Frequency Agreement Problem

**Date:** 2026-03-30
**Status:** Pedagogical exercise for reference implementation

---

## Grading Criteria

This is a pedagogical exercise for a computer science class. The
exercise is graded on:

1. **How faithfully the algorithm implements the deterministic
   sorted-list walk** as specified in this document. The walk must
   be a merge operation on pre-sorted lists. No heuristics. No
   scoring. No backtracking. No choice points.

2. **How clearly the implementation proves its bounds.** The bound
   accounting must be explicit: count every list entry visited,
   every lookup performed, every List C entry created. The total
   must be demonstrably O(n) for the walk (plus O(n log n) for the
   sort), where n = total number of (measurement, frequency) entries.

The exercise is **NOT** graded on:

- Whether the algorithm is optimal or even good
- Whether it outperforms other approaches on any benchmark
- Whether it uses clever data structures or optimizations
- Whether it handles edge cases that don't arise in the test data

The point of the exercise is to implement a **deterministic,
exhaustive, bounded walk** and demonstrate that its cost is
countable and polynomial. Nothing more.

---

## The Problem

A physics lab measures spectral emissions from two different
instruments. Each instrument records composite frequencies — signals
that are mixtures of pure fundamental frequencies. The fundamental
frequencies are prime numbers (Hz): 2, 3, 5, 7, 11, 13, ...

**Instrument A** records emission spectra as a list of measurements.
Each measurement is a composite frequency (a product of primes) with
a signed coefficient indicating whether the component is in phase
(positive) or anti-phase (negative).

**Instrument B** records the same phenomena but from a different
angle, producing a different set of composite measurements.

**The question:** Can the two datasets be brought into complete
agreement? That is: does there exist an assignment of each
fundamental frequency to either in-phase (+) or anti-phase (−) such
that every measurement from both instruments is accounted for?

---

## Data Format

### Measurements

Each measurement is a "constraint" — a list of signed fundamental
frequencies that were observed together in one spectral line.

```
Measurement: [ +p₂, -p₃, +p₇ ]
```

This means: in this spectral line, frequency 2 was in-phase,
frequency 3 was anti-phase, and frequency 7 was in-phase.

A measurement is "accounted for" if at least one of its signed
frequencies matches the global assignment. For example, if the
global assignment says p₂ = in-phase, then this measurement is
accounted for (via +p₂).

### The dataset

A dataset is a list of measurements. The dataset is "in agreement"
if every measurement is accounted for by some global assignment.

```
Dataset:
  measurement 0: [ +p₂, +p₃ ]
  measurement 1: [ -p₂, +p₃ ]
  measurement 2: [ -p₃ ]
```

Global assignment: p₂ = anything, p₃ = in-phase.
- Measurement 0: +p₃ matches → accounted for ✓
- Measurement 1: +p₃ matches → accounted for ✓
- Measurement 2: -p₃ does not match (p₃ is in-phase) → NOT accounted for ✗

Different assignment: p₂ = in-phase, p₃ = anti-phase.
- Measurement 0: +p₂ matches → accounted for ✓
- Measurement 1: -p₂ does not match, +p₃ does not match → NOT ✗

No single global assignment accounts for all three measurements.
This dataset has NO agreement.

---

## The Algorithm: Cross-Reference Walk

### Step 0: Compute signed composite values

Each measurement's **signed composite** is the product of its signed
frequency components. The sign of the composite encodes the overall
polarity parity of the measurement.

Using actual prime values (p₂ = 3, p₃ = 5, p₇ = 17):

```
measurement [ +3, +5 ]       → composite = (+3) × (+5) = +15
measurement [ -3, +5 ]       → composite = (-3) × (+5) = -15
measurement [ -5 ]            → composite = -5
measurement [ +3, -5, +17 ]  → composite = (+3) × (-5) × (+17) = -255
```

The signed composite IS the measurement's address in signed number
space. Two measurements with the same absolute composite but
different signs have different polarity structures.

### Step 1: Sort by signed composite value

**Sort all measurements by their signed composite value.** This is
the key step that makes the walk monotonic. Measurements with
smaller absolute composites (fewer/smaller prime factors, more
constrained) are processed first.

The sorted order ensures:
- Simpler measurements (fewer constraints) are resolved first
- Their resolutions cascade into more complex measurements
- The walk proceeds monotonically through increasing composites

Example (sorted by signed composite):
```
composite -255:  measurement 3: [ +3, -5, +17 ]
composite -15:   measurement 1: [ -3, +5 ]
composite -5:    measurement 2: [ -5 ]
composite +15:   measurement 0: [ +3, +5 ]
```

### Step 2: Build the two lists from sorted measurements

**List A (sorted by signed composite, then by signed frequency):**
```
| composite | measurement_id | signed_frequency |
|-----------|----------------|-----------------|
| -255      | 3              | -5              |
| -255      | 3              | +3              |
| -255      | 3              | +17             |
| -15       | 1              | -3              |
| -15       | 1              | +5              |
| -5        | 2              | -5              |
| +15       | 0              | +3              |
| +15       | 0              | +5              |
```

**List B (frequency-indexed, the cross-reference):**
```
| abs_freq | sign | measurement_id | composite |
|----------|------|----------------|-----------|
| 3        | +    | 0              | +15       |
| 3        | +    | 3              | -255      |
| 3        | -    | 1              | -15       |
| 5        | +    | 0              | +15       |
| 5        | +    | 1              | -15       |
| 5        | -    | 2              | -5        |
| 5        | -    | 3              | -255      |
| 17       | +    | 3              | -255      |
```

List B is the cross-reference index: for each frequency, which
measurements reference it and with what sign.

### Step 3: Walk — Build the agreement set

**Agreement set** (List C): starts empty. Will contain one entry per
accounted-for measurement. Grows monotonically.

**Committed frequencies:** tracks which frequencies have been assigned
a sign (in-phase or anti-phase). Grows monotonically. Never changed
or undone.

**The walk proceeds through List A in composite order.**

**Critical: when a frequency is knocked out of a measurement, that
measurement's signed composite is divided by the knocked-out signed
frequency, and the measurement is re-inserted into List A at the
position corresponding to its new (smaller) composite.** This
maintains the sorted invariant and ensures the measurement is
re-processed at the correct time with its reduced composite.

**The walk:**

```
1. Take the first record from List A (smallest composite):
   (measurement_j, signed_freq_f, composite_c).

2. If measurement_j is already in List C (accounted for): skip,
   move to next record.

3. Look up f in List B: find every measurement that contains f
   with matching sign. For each match:
   - Add it to List C (accounted for).
   - Commit f to the indicated sign.

4. When f is committed, look up f with the OPPOSITE sign in
   List B. Every measurement containing f with opposite sign
   just lost one option:
   - Divide that measurement's signed composite by the signed
     frequency that was knocked out. The composite shrinks.
   - Re-insert the measurement into List A at the position
     corresponding to its new, smaller composite.
   - If the measurement now has exactly one uncommitted frequency,
     it is FORCED — the cascade will process it when the walk
     reaches its new composite position.
   - If the measurement now has zero uncommitted frequencies and
     is NOT in List C: DISAGREEMENT. Stop.

5. Move to the next record in List A (which may now include
   re-inserted measurements with updated composites).

6. Continue until:
   - All measurements appear in List C: AGREEMENT FOUND.
   - A measurement has zero uncommitted frequencies and is not
     in List C: DISAGREEMENT. Stop.
```

There is no "choice point." There is no scoring. There is no
backtracking. The composite sort order determines processing order.
When a frequency is knocked out, the affected measurement's
composite shrinks and the measurement is re-inserted at the correct
(earlier) position. The walk is monotonic — it always processes the
smallest remaining composite next. Each commitment is permanent.

### Step 4: Output

If agreement is found: the committed frequency assignments form the
global agreement. List C is the evidence — one entry per measurement
showing which frequency accounts for it.

If disagreement: report which measurement(s) cannot be accounted for.

### Bound

List A has n entries (one per literal in the input). List B has n
entries.

| Operation | Count | Cost | Total |
|-----------|-------|------|-------|
| Initial sort | 1 | O(n log n) | O(n log n) |
| Walk List A entries | ≤ n | O(1) per | O(n) |
| List B lookups (match + opposite) | ≤ 2n | O(1) per | O(n) |
| List C entries created | ≤ m | O(1) per | O(m) |
| Re-insertions (composite update) | ≤ n | O(log n) per | O(n log n) |

Each (measurement, frequency) pair triggers at most one re-insertion
(when the frequency is knocked out of that measurement). There are
n such pairs total. Each re-insertion into a sorted structure costs
O(log n).

**Total: O(n log n).**

The walk itself is O(n). The sort and re-insertions cost O(n log n).
With a priority queue (min-heap on composite), re-insertions are
O(log n) each, giving O(n log n) total.

---

## Example Walkthrough

### Dataset (agreement exists)

```
measurement 0: [ +p₂, +p₃ ]       — either p₂=+ or p₃=+ accounts for it
measurement 1: [ -p₂, +p₅ ]       — either p₂=- or p₅=+ accounts for it
measurement 2: [ -p₅ ]             — only p₅=- accounts for it (forced!)
measurement 3: [ +p₂, -p₃, +p₇ ]  — any of three frequencies
```

**Pass 1:**
- Measurement 2 is forced: only `-p₅`. Commit p₅ = anti-phase.
- List B lookup for p₅=-: measurement 2. Add measurement 2 to List C.
- List B lookup for p₅=+: measurement 1. Measurement 1 just lost
  its `+p₅` option. Check remaining: `-p₂` is uncommitted. Only one
  option left → measurement 1 is now forced.

**Pass 2:**
- Measurement 1 is forced: only `-p₂`. Commit p₂ = anti-phase.
- List B lookup for p₂=-: measurement 1. Add measurement 1 to List C.
- List B lookup for p₂=+: measurements 0 and 3. They just lost
  their `+p₂` option.
  - Measurement 0: remaining uncommitted = `+p₃`. Forced!
  - Measurement 3: remaining uncommitted = `-p₃, +p₇`. Two options,
    not forced.

**Pass 3:**
- Measurement 0 is forced: only `+p₃`. Commit p₃ = in-phase.
- List B lookup for p₃=+: measurement 0. Add measurement 0 to List C.
- List B lookup for p₃=-: measurement 3. Measurement 3 just lost
  `-p₃`. Remaining: `+p₇`. Forced!

**Pass 4:**
- Measurement 3 is forced: only `+p₇`. Commit p₇ = in-phase.
- Add measurement 3 to List C.

**Result:** All 4 measurements in List C. **AGREEMENT FOUND.**
Assignment: p₂=-, p₃=+, p₅=-, p₇=+.

### Dataset (no agreement)

```
measurement 0: [ +p₂ ]    — forces p₂=+
measurement 1: [ -p₂ ]    — forces p₂=-
```

**Pass 1:** Measurement 0 forced: commit p₂=+. Measurement 1 now
has no uncommitted frequencies and is not accounted for (p₂=+ but
measurement 1 needs p₂=-). **DISAGREEMENT.**

---

## Properties

1. **Exhaustive:** Every measurement is checked. The walk scans
   List A completely. No measurement is skipped.

2. **Index-driven:** List B provides O(1) lookup for the
   consequences of each commitment. No scanning the full dataset
   to find affected measurements.

3. **Monotonic:** Once a frequency is committed, it stays committed.
   Once a measurement is in List C, it stays. The agreement set
   only grows.

4. **Cascade:** Committing one frequency can force others via the
   cross-reference. The cascade continues until stable.

5. **Cost:** Each entry in List A is visited at most once during
   propagation. Each List B lookup processes at most |measurements|
   entries. Total: O(|List A| × |List B|) = O((m × k)²) where m
   is the number of measurements and k is the max frequencies per
   measurement. With sorting: O(m × k × log(m × k)) for setup,
   O(m × k) for the walk.

---

## Implementation Notes for JavaScript Reference

All files are relative to `www/FrequencyAgreement/`.

- `solver_v2.js` — the deterministic sorted-list walk implementation
- `runner_v2.js` — Node.js CLI runner for all test datasets
- `index.html` — web front-end (to be updated after solver_v2 works)
- `HANDOFF_JS_Implementation.md` — implementation handoff document

Test datasets at `../../Lean/PR/InformationTheory/Complexity/test_data/`:
- `frequencies.json` — 6 small datasets
- `freq_*.json` — 6 larger datasets

Data structures:
- Each measurement's composite value = product of |signed_components|.
  This is computed first and used as the sort key.
- List A: array of `{ composite, measurementId, signedFreq }`,
  **sorted by composite value** (primary key), then by signedFreq
  within each composite group. The composite sort makes the walk
  monotonic — smaller composites (simpler measurements) first.
- List B: `Map<absFreq, { pos: Set<measurementId>, neg: Set<measurementId> }>`
- List C: array of `{ measurementId, signedFreq }` — the agreement
  set, grows monotonically. New entries appended and walked.
- Committed: `Map<absFreq, boolean>` — true = in-phase, false =
  anti-phase. Grows monotonically, never changed.
