#!/usr/bin/env bash
#
# Full Comparator verdict (build and export both roots in the sandbox, compare
# statements, check permitted axioms, replay in the kernel), invoked as the
# pinned Comparator README prescribes:
#
#   systemd-run --user --property=RestrictAddressFamilies=~AF_UNIX ... \
#     -- bash -c 'lake env comparator config.json'
#
# Prerequisites: `lake build` at the repository root (the candidate's .lake is
# read-only inside the sandbox), `lake build comparator lean4export` there,
# and a landrun binary. The trusted statement is comparator/Challenge.lean.
#
# Usage:  bash comparator/run.sh [evidence-dir]
# Environment:
#   COMPARATOR_LANDRUN  landrun binary (default: landrun in PATH)
#   LEAN4EXPORT         lean4export binary (default: the root package build)

set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/.." && pwd)"
CONFIG="$HERE/config.json"
EVIDENCE_DIR="${1:-$HERE/evidence}"
COMPARATOR="$REPO/.lake/packages/Comparator/.lake/build/bin/comparator"
LANDRUN="${COMPARATOR_LANDRUN:-$(command -v landrun || true)}"
LEAN4EXPORT="${LEAN4EXPORT:-$REPO/.lake/packages/lean4export/.lake/build/bin/lean4export}"
[[ -x "$LANDRUN" ]] || { echo "landrun not found: set COMPARATOR_LANDRUN" >&2; exit 2; }
[[ -x "$COMPARATOR" ]] || { echo "build it first: lake build comparator lean4export" >&2; exit 2; }
mkdir -p "$EVIDENCE_DIR"
LOG="$EVIDENCE_DIR/comparator.log"

{
  printf 'run: %s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf 'challenge: %s\n' "$(cd "$HERE" && find Challenge.lean Challenge -name '*.lean' | sort | xargs sha256sum | sha256sum | cut -d' ' -f1)"
  printf 'candidate HEAD: %s\n' "$(git -C "$REPO" rev-parse HEAD)"
  printf 'comparator: %s\n' "$(sha256sum "$COMPARATOR" | cut -d' ' -f1)"
  printf 'landrun: %s\n' "$("$LANDRUN" --version 2>&1 | head -1)"
} | tee "$LOG"

set +e
systemd-run --user --wait --pipe --quiet \
  --property=RestrictAddressFamilies=~AF_UNIX \
  -E PATH="$PATH" -E HOME="$HOME" \
  -E COMPARATOR_LANDRUN="$LANDRUN" -E COMPARATOR_LEAN4EXPORT="$LEAN4EXPORT" \
  -E GIT_ALLOW_PROTOCOL=file \
  --working-directory "$HERE" \
  -- bash -c "lake env '$COMPARATOR' '$CONFIG'" 2>&1 | tee -a "$LOG"
status=${PIPESTATUS[0]}
set -e
printf 'comparator exit: %s\n' "$status" | tee -a "$LOG"
exit "$status"
