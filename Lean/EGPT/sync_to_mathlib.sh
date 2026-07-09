#!/usr/bin/env bash
# sync_to_mathlib.sh — Sync Lean/EGPT/InformationTheory → mathlib4 fork
#
# Usage: cd EGPT/Lean/EGPT && bash sync_to_mathlib.sh
#
# What it does:
#   1. Copies all .lean files from InformationTheory/ to the mathlib4 fork
#   2. Rewrites internal imports: InformationTheory.X → Mathlib.InformationTheory.X
#   3. Reports what changed
#
# The reverse (mathlib4 → local) is: bash sync_from_mathlib.sh

set -euo pipefail

SRC="$(cd "$(dirname "$0")" && pwd)/InformationTheory"
DST="$HOME/Lean/mathlib4/Mathlib/InformationTheory"

if [ ! -d "$SRC" ]; then
  echo "ERROR: Source not found: $SRC"
  exit 1
fi

if [ ! -d "$DST" ]; then
  echo "ERROR: Destination not found: $DST"
  exit 1
fi

echo "=== Syncing Lean/EGPT/InformationTheory → mathlib4 ==="
echo "Source: $SRC"
echo "Target: $DST"

# Subsystems we manage (not all of InformationTheory — skip mathlib-native dirs)
SUBSYSTEMS="Complexity Entropy EntropyNumber Physics"

# sync_lean_file: copy a .lean file, rewrite imports, strip LLM guidance headers
sync_lean_file() {
  local src_file="$1"
  local dst_file="$2"
  sed \
    -e 's/^import InformationTheory\./import Mathlib.InformationTheory./g' \
    -e '/@\[debate_context\]/d' \
    -e '/^through @pnp-moderator/d' \
    -e '/^Debate record: 18\.313x\/DEBATE_STATE\.md/d' \
    -e '/^Proof walkthrough: Lean\/PR\/InformationTheory/d' \
    "$src_file" | perl -0777 -pe 's/(-\/)\n{3,}/\1\n\n/g' > "$dst_file"
}

# Sync root-level .lean files (Basic.lean, Bridge.lean)
for f in "$SRC"/*.lean; do
  [ -f "$f" ] || continue
  base=$(basename "$f")
  sync_lean_file "$f" "$DST/$base"
  echo "  $base"
done

# Sync subsystem directories (including nested subdirs like CNF/)
for sub in $SUBSYSTEMS; do
  if [ -d "$SRC/$sub" ]; then
    find "$SRC/$sub" -name '*.lean' -type f | while read -r f; do
      rel="${f#$SRC/$sub/}"
      mkdir -p "$DST/$sub/$(dirname "$rel")"
      sync_lean_file "$f" "$DST/$sub/$rel"
      echo "  $sub/$rel"
    done
  fi
done

echo ""
echo "=== Done. Verify with: cd ~/Lean/mathlib4 && lake build Mathlib.InformationTheory ==="
