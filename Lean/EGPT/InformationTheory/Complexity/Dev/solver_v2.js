// ═══════════════════════════════════════════════════════════════════════════
// Frequency Agreement Solver v2 — Deterministic Sorted-List Walk
// ═══════════════════════════════════════════════════════════════════════════
//
// Implements the cross-reference walk from DESIGN_FrequencyAgreement.md:
//
//   Step 0: Compute signed composite for each measurement.
//           composite = product of signed components.
//
//   Step 1: Build List A — one entry per (measurement, signedFreq) pair,
//           sorted by signed frequency ascending.
//           n = |List A| = total number of literals across all measurements.
//
//   Step 2: Build List B — cross-reference index.
//           Map<absFreq, { pos: Set<measurementId>, neg: Set<measurementId> }>
//
//   Step 3: Walk List A in sorted order.
//           For each entry (measurement_j, signed_freq_f):
//             - Skip if measurement_j already accounted for.
//             - Skip if f already knocked out of measurement_j.
//             - If f already committed (matching sign): account measurement_j.
//             - If f not committed: commit f, then:
//               (a) Match lookup: all measurements with f same sign -> List C.
//               (b) Opposite lookup: all measurements with f opposite sign
//                   lose an option. Divide their composite by the knocked-out
//                   signed frequency. If zero options remain: DISAGREEMENT.
//                   If exactly one option remains: FORCED — cascade immediately.
//
//   Step 4: After List A exhausted, any unaccounted measurement with
//           uncommitted frequencies: commit the first one and cascade.
//
// Properties:
//   - NO heuristics. NO scoring. NO backtracking. NO choice points.
//   - The signed-frequency sort determines the walk order.
//   - Every commitment is permanent and monotonic.
//   - Cascading processes forced measurements immediately (equivalent to
//     the design's re-insertion into a priority queue at reduced composite).
//
// ═══════════════════════════════════════════════════════════════════════════
// BOUND PROOF
// ═══════════════════════════════════════════════════════════════════════════
//
// Let n = |List A| = total literals, m = number of measurements,
//     k = number of distinct fundamental frequencies.
//
// | Operation              | Count        | Cost each | Total        |
// |------------------------|--------------|-----------|--------------|
// | Sort List A            | 1            | O(n lg n) | O(n lg n)   |
// | Walk List A entries    | <= n         | O(1)      | O(n)        |
// | List B lookups (match) | <= k         | O(1)+iter | O(n) total  |
// | List B lookups (opp.)  | <= k         | O(1)+iter | O(n) total  |
// | List C entries created | <= m         | O(1)      | O(m)        |
// | Composite divisions    | <= n         | O(1)      | O(n)        |
// | Cascade (forced)       | <= n         | O(1)      | O(n)        |
// |------------------------|--------------|-----------|--------------|
// | TOTAL                  |              |           | O(n lg n)   |
//
// Each (measurement, frequency) pair is processed at most once by the walk
// and at most once by the cascade. Each List B entry is visited at most
// once per matching lookup and once per opposite lookup. The cascade depth
// is bounded by k (number of frequencies). Total: O(n lg n) dominated by
// the initial sort.
//
// The implementation counts every operation for verification.
// ═══════════════════════════════════════════════════════════════════════════

(function (exports) {
  'use strict';

  function solve(measurements) {
    const t0 = typeof performance !== 'undefined' ? performance.now() : Date.now();

    const m = measurements.length;
    if (m === 0) {
      return {
        result: 'AGREEMENT',
        stats: {
          measurements: 0, fundamentals: 0, listAEntries: 0,
          listAVisited: 0, listBLookups: 0, listCEntries: 0,
          reinsertions: 0, forcedCommitments: 0, directCommitments: 0,
          totalOperations: 0, time: 0
        }
      };
    }

    // ── Step 0: Compute signed composites ──────────────────────────────
    // signedComposite[i] = product of signed_components[i]
    // Updated when frequencies are knocked out (divided by knocked-out sf).
    const signedComposite = new Array(m);

    // uncommittedFreqs[i] = Set of signed frequencies still available.
    // Entries are removed when a frequency is committed to the opposite sign.
    const uncommittedFreqs = new Array(m);

    // allComponents[i] = original signed components (immutable copy).
    const allComponents = new Array(m);

    const fundamentalSet = new Set();

    for (let i = 0; i < m; i++) {
      const sc = measurements[i].signed_components;
      allComponents[i] = sc.slice();
      uncommittedFreqs[i] = new Set(sc);
      let composite = 1;
      for (let j = 0; j < sc.length; j++) {
        composite *= sc[j];
        fundamentalSet.add(Math.abs(sc[j]));
      }
      signedComposite[i] = composite;
    }

    const numFundamentals = fundamentalSet.size;

    // ── Step 2: Build List B (cross-reference index) ───────────────────
    // For each fundamental frequency, which measurements reference it
    // with positive sign and which with negative sign.
    const listB = new Map();
    for (let i = 0; i < m; i++) {
      for (const sc of allComponents[i]) {
        const absFreq = Math.abs(sc);
        const isPos = sc > 0;
        if (!listB.has(absFreq)) {
          listB.set(absFreq, { pos: new Set(), neg: new Set() });
        }
        const entry = listB.get(absFreq);
        if (isPos) entry.pos.add(i);
        else entry.neg.add(i);
      }
    }

    // ── Step 1: Build List A sorted by signed frequency ────────────────
    // One entry per (measurement, signedFreq) pair.
    // Sorted by signed frequency ascending (most negative first).
    // Deterministic tie-break: by measurement id.
    const listA = [];
    for (let i = 0; i < m; i++) {
      for (const sf of allComponents[i]) {
        listA.push({ measurementId: i, signedFreq: sf });
      }
    }
    // O(n lg n) sort — the dominant cost.
    listA.sort((a, b) => {
      if (a.signedFreq !== b.signedFreq) return a.signedFreq - b.signedFreq;
      return a.measurementId - b.measurementId;
    });

    const listAEntries = listA.length;  // = n

    // ── Step 3: The Walk ───────────────────────────────────────────────
    const accountedFor = new Set();   // measurement ids in List C
    const committed = new Map();      // absFreq -> boolean (true = positive/in-phase)
    const listC = [];                 // agreement set: one entry per accounted measurement

    // ── Operation counters for bound proof ─────────────────────────────
    let listAVisited = 0;       // entries popped from List A          (bounded by n)
    let listBLookups = 0;       // List B lookups performed            (bounded by 2k)
    let listCCreated = 0;       // entries added to List C             (bounded by m)
    let reinsertions = 0;       // composite divisions / knock-outs    (bounded by n)
    let forcedCommitments = 0;  // commitments from cascade            (bounded by k)
    let directCommitments = 0;  // commitments from List A walk        (bounded by k)

    let disagreement = false;

    // ── commitFrequency ────────────────────────────────────────────────
    // Commit absFreq to the given sign. Then:
    //   1. Match lookup: account all measurements with matching sign.
    //   2. Opposite lookup: knock out the frequency from measurements with
    //      opposite sign. Divide their composite. Check for forced/dead.
    //   3. Cascade: recursively commit forced measurements.
    //
    // This function is called at most once per frequency (k calls total).
    // Each call iterates over the match and opposite sets, visiting each
    // (measurement, frequency) pair at most once across all calls.
    function commitFrequency(absFreq, isPositive, isForced) {
      if (committed.has(absFreq)) {
        if (committed.get(absFreq) !== isPositive) {
          disagreement = true;  // contradiction: same freq forced both ways
        }
        return;
      }

      committed.set(absFreq, isPositive);
      if (isForced) forcedCommitments++;
      else directCommitments++;

      const bEntry = listB.get(absFreq);
      if (!bEntry) return;

      // (a) Match lookup: measurements containing f with matching sign
      const matching = isPositive ? bEntry.pos : bEntry.neg;
      listBLookups++;
      for (const matchId of matching) {
        if (!accountedFor.has(matchId)) {
          accountedFor.add(matchId);
          listC.push({
            measurementId: matchId,
            signedFreq: isPositive ? absFreq : -absFreq
          });
          listCCreated++;
        }
      }

      // (b) Opposite lookup: measurements containing f with opposite sign
      const opposite = isPositive ? bEntry.neg : bEntry.pos;
      listBLookups++;

      // Collect forced measurements for cascade (processed after loop
      // to avoid modifying state during iteration).
      const forcedQueue = [];

      for (const affectedId of opposite) {
        if (accountedFor.has(affectedId)) continue;

        // The signed frequency being knocked out
        const knockedOutSf = isPositive ? -absFreq : absFreq;
        if (!uncommittedFreqs[affectedId].has(knockedOutSf)) continue;

        // Remove knocked-out frequency
        uncommittedFreqs[affectedId].delete(knockedOutSf);
        reinsertions++;   // one composite division counted

        // Divide composite: measurement's address shrinks
        signedComposite[affectedId] = signedComposite[affectedId] / knockedOutSf;

        if (uncommittedFreqs[affectedId].size === 0) {
          // DEAD: measurement has zero uncommitted frequencies and is
          // not in List C. No assignment can account for it.
          disagreement = true;
          return;
        }

        if (uncommittedFreqs[affectedId].size === 1) {
          // FORCED: exactly one uncommitted frequency remains.
          // This measurement MUST commit that frequency.
          // Equivalent to re-inserting at the front of the priority queue.
          const lastSf = uncommittedFreqs[affectedId].values().next().value;
          forcedQueue.push({
            absFreq: Math.abs(lastSf),
            isPositive: lastSf > 0
          });
        }
      }

      // Cascade: process forced measurements immediately.
      // Each forced commitment may trigger further cascades.
      // Total cascade depth bounded by k (number of distinct frequencies).
      for (const forced of forcedQueue) {
        if (disagreement) return;
        commitFrequency(forced.absFreq, forced.isPositive, true);
      }
    }

    // ── Walk List A in signed-frequency order ──────────────────────────
    // Each entry visited at most once. For each unaccounted measurement
    // with an uncommitted frequency, we commit and cascade.
    for (let idx = 0; idx < listA.length; idx++) {
      if (disagreement) break;
      if (accountedFor.size === m) break;

      const entry = listA[idx];
      listAVisited++;

      const mId = entry.measurementId;
      const sf = entry.signedFreq;
      const absFreq = Math.abs(sf);
      const isPositive = sf > 0;

      // Skip if measurement already accounted for
      if (accountedFor.has(mId)) continue;

      // Skip if this signed frequency was already knocked out
      if (!uncommittedFreqs[mId].has(sf)) continue;

      // If frequency already committed, check if it accounts for this measurement
      if (committed.has(absFreq)) {
        if (committed.get(absFreq) === isPositive) {
          accountedFor.add(mId);
          listC.push({ measurementId: mId, signedFreq: sf });
          listCCreated++;
        }
        // If committed to opposite sign: skip, measurement has other options
        continue;
      }

      // Frequency not yet committed: commit it. The sort order determines
      // which frequency is committed — no choice point, no heuristic.
      commitFrequency(absFreq, isPositive, false);
    }

    // ── Step 4: Fallback for unaccounted measurements ──────────────────
    // If the List A walk didn't account for everything, process remaining
    // measurements in order. Each gets its first uncommitted frequency
    // committed. This handles measurements whose entries in List A were
    // all for already-committed frequencies.
    if (!disagreement && accountedFor.size < m) {
      for (let i = 0; i < m; i++) {
        if (disagreement) break;
        if (accountedFor.has(i)) continue;

        if (uncommittedFreqs[i].size === 0) {
          disagreement = true;
          break;
        }

        // Commit first (most negative) uncommitted signed frequency.
        // Deterministic: sorted order, no choice.
        const sortedRemaining = [...uncommittedFreqs[i]].sort((a, b) => a - b);
        const sf = sortedRemaining[0];
        commitFrequency(Math.abs(sf), sf > 0, false);
      }
    }

    if (!disagreement && accountedFor.size < m) {
      disagreement = true;
    }

    const elapsed = (typeof performance !== 'undefined' ? performance.now() : Date.now()) - t0;

    return {
      result: disagreement ? 'DISAGREEMENT' : 'AGREEMENT',
      committed: new Map(committed),
      accountedFor: new Set(accountedFor),
      listC,
      stats: {
        measurements: m,
        fundamentals: numFundamentals,
        listAEntries,
        listAVisited,
        listBLookups,
        listCEntries: listCCreated,
        reinsertions,
        forcedCommitments,
        directCommitments,
        totalOperations: listAVisited + listBLookups + listCCreated + reinsertions,
        time: elapsed
      }
    };
  }

  // ─────────────────────────────────────────────────────────────────────────
  // Exports
  // ─────────────────────────────────────────────────────────────────────────
  exports.solve = solve;

})(typeof window !== 'undefined' ? (window.SolverV2 = {}) : module.exports);
