#!/usr/bin/env node
// ═══════════════════════════════════════════════════════════════════════════
// Runner v2 — Node.js CLI for solver_v2.js
// ═══════════════════════════════════════════════════════════════════════════
// Loads all 12 test datasets and runs the deterministic sorted-list walk
// on each, reporting operation counts for bound verification.
// ═══════════════════════════════════════════════════════════════════════════

'use strict';

const fs = require('fs');
const path = require('path');
const { solve } = require('./solver_v2.js');

// ─────────────────────────────────────────────────────────────────────────
// Relaxed JSON parser (handles +N notation in frequencies.json)
// ─────────────────────────────────────────────────────────────────────────
function parseRelaxedJSON(filePath) {
  let text = fs.readFileSync(filePath, 'utf-8');
  text = text.replace(/(?<=[\[,]\s*)\+(?=\d)/g, '');
  return JSON.parse(text);
}

// ─────────────────────────────────────────────────────────────────────────
// Locate test data directory
// ─────────────────────────────────────────────────────────────────────────
const dataDir = path.resolve(__dirname, '../../Lean/PR/InformationTheory/Complexity/test_data');

if (!fs.existsSync(dataDir)) {
  console.error('Test data directory not found: ' + dataDir);
  process.exit(1);
}

// ─────────────────────────────────────────────────────────────────────────
// Load datasets
// ─────────────────────────────────────────────────────────────────────────
const datasets = [];

// 1. frequencies.json — 6 sub-datasets
const freqPath = path.join(dataDir, 'frequencies.json');
if (fs.existsSync(freqPath)) {
  const data = parseRelaxedJSON(freqPath);
  if (data.datasets) {
    for (const [name, ds] of Object.entries(data.datasets)) {
      datasets.push({ name, measurements: ds.measurements });
    }
  }
}

// 2. freq_*.json — 6 larger datasets
const files = fs.readdirSync(dataDir).filter(f => f.startsWith('freq_') && f.endsWith('.json')).sort();
for (const file of files) {
  const filePath = path.join(dataDir, file);
  const data = JSON.parse(fs.readFileSync(filePath, 'utf-8'));
  // Derive dataset name from label or filename
  const name = data.label || file.replace(/^freq_/, '').replace(/\.json$/, '');
  datasets.push({ name, measurements: data.measurements });
}

// ─────────────────────────────────────────────────────────────────────────
// Expected results for validation
// ─────────────────────────────────────────────────────────────────────────
const expected = {
  'agreement_simple': 'AGREEMENT',
  'disagreement_simple': 'DISAGREEMENT',
  'agreement_chain': 'AGREEMENT',
  'agreement_medium': 'AGREEMENT',
  'disagreement_medium': 'DISAGREEMENT',
  'agreement_counterexample': 'AGREEMENT',
  'spectral_64ch_80m': 'AGREEMENT',
  'spectral_128ch_144m': 'AGREEMENT',
  'spectral_20ch_91m_random': 'DISAGREEMENT',
  'spectral_100ch_2130m_quintet': 'DISAGREEMENT',
  'spectral_75ch_6675m_dense': 'DISAGREEMENT',
  'spectral_75ch_6675m_unknown': 'DISAGREEMENT'
};

// ─────────────────────────────────────────────────────────────────────────
// Run solver on each dataset
// ─────────────────────────────────────────────────────────────────────────
console.log('═══════════════════════════════════════════════════════════════');
console.log('  Frequency Agreement Solver v2 — Deterministic Sorted-List Walk');
console.log('═══════════════════════════════════════════════════════════════');
console.log();

let allCorrect = true;

for (const { name, measurements } of datasets) {
  const result = solve(measurements);
  const s = result.stats;
  const expectedResult = expected[name];
  const correct = expectedResult ? result.result === expectedResult : null;

  if (correct === false) allCorrect = false;

  const tag = correct === true ? ' [OK]' : correct === false ? ' [MISMATCH]' : '';

  console.log('Dataset: ' + name + tag);
  console.log('  Measurements: ' + s.measurements + ' | Fundamentals: ' + s.fundamentals);
  console.log('  List A entries: ' + s.listAEntries);
  console.log('  Result: ' + result.result);
  console.log('  List A entries visited: ' + s.listAVisited);
  console.log('  List B lookups: ' + s.listBLookups);
  console.log('  List C entries created: ' + s.listCEntries);
  console.log('  Re-insertions: ' + s.reinsertions);
  console.log('  Forced commitments: ' + s.forcedCommitments);
  console.log('  Direct commitments: ' + s.directCommitments);
  console.log('  Total operations: ' + s.totalOperations);
  console.log('  Time: ' + s.time.toFixed(2) + 'ms');
  if (correct === false) {
    console.log('  *** EXPECTED: ' + expectedResult + ' ***');
  }
  console.log();
}

// ─────────────────────────────────────────────────────────────────────────
// Summary
// ─────────────────────────────────────────────────────────────────────────
console.log('═══════════════════════════════════════════════════════════════');
if (allCorrect) {
  console.log('  All datasets match expected results.');
} else {
  console.log('  WARNING: Some datasets did not match expected results.');
}
console.log('═══════════════════════════════════════════════════════════════');
