#!/usr/bin/env bash
# sync_from_mathlib.sh — Sync mathlib4 fork → Lean/EGPT/InformationTheory
#
# Usage: cd EGPT/Lean/EGPT && bash sync_from_mathlib.sh
#
# What it does:
#   1. Copies managed .lean files from the mathlib4 fork to InformationTheory/
#   2. Rewrites internal imports: Mathlib.InformationTheory.X → InformationTheory.X
#   3. Reports what changed

set -euo pipefail

SRC="$HOME/Lean/mathlib4/Mathlib/InformationTheory"
DST="$(cd "$(dirname "$0")" && pwd)/InformationTheory"

if [ ! -d "$SRC" ]; then
  echo "ERROR: Source not found: $SRC"
  exit 1
fi

if [ ! -d "$DST" ]; then
  echo "ERROR: Destination not found: $DST"
  exit 1
fi

echo "=== Syncing mathlib4 → Lean/EGPT/InformationTheory ==="
echo "Source: $SRC"
echo "Target: $DST"

# Subsystems we manage
SUBSYSTEMS="Complexity Entropy EntropyNumber Physics"

for sub in $SUBSYSTEMS; do
  if [ -d "$SRC/$sub" ]; then
    mkdir -p "$DST/$sub"
    for f in "$SRC/$sub"/*.lean; do
      [ -f "$f" ] || continue
      base=$(basename "$f")
      # Copy and rewrite internal imports
      sed 's/^import Mathlib\.InformationTheory\./import InformationTheory./g' "$f" > "$DST/$sub/$base"
      echo "  $sub/$base"
    done
  fi
done

echo ""
echo "=== Done. Verify with: cd EGPT/Lean/EGPT && lake build ==="
