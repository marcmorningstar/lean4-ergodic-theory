#!/usr/bin/env bash
# new-agent-worktree.sh — provision a collision-free agent worktree.
#
# The `setup.json` corruption that bites when several agents build concurrently in
# ONE worktree is a race on `<worktree>/.lake/build/ir/*.setup.json`. That file holds
# only the LOCAL libs' artifacts (Oseledets + AxiomAudit); Mathlib's 5GB of oleans live
# under `.lake/packages/mathlib/.lake/build` and are read-only at build time. So we split:
#   * `.lake/packages` -> SYMLINK to the shared, immutable cache (never copied; zero rebuild).
#   * `.lake/build`     -> PRIVATE per worktree (copied, ~263M, seconds).
# With one agent per worktree the `setup.json` race becomes structurally impossible.
#
# No leancheck daemon is provisioned: agents self-verify via `lake build <Module>`, so the
# agent's own build is the sole lake process in its tree (zero intra-worktree contention too).
#
# Usage: new-agent-worktree.sh <new-branch> [base-ref] [worktree-path]
#   Prints the absolute worktree path as the LAST line of stdout (all logs go to stderr).
#   Env: MAIN_REPO (default /workspaces/lean4-oseledets) — the shared source of .lake.
set -euo pipefail

MAIN_REPO="${MAIN_REPO:-/workspaces/lean4-oseledets}"
BRANCH="${1:?usage: new-agent-worktree.sh <new-branch> [base-ref] [worktree-path]}"
BASE="${2:-HEAD}"
SLUG="$(printf '%s' "$BRANCH" | tr '/ :@' '----')"
WT="${3:-/home/vscode/agtwt-$SLUG}"

if [ -e "$WT" ]; then echo "ERROR: worktree path already exists: $WT" >&2; exit 1; fi
if [ ! -d "$MAIN_REPO/.lake/packages" ]; then
  echo "ERROR: $MAIN_REPO/.lake/packages missing — build the main repo first." >&2; exit 1
fi

echo ">> git worktree add -b $BRANCH $WT $BASE" >&2
git -C "$MAIN_REPO" worktree add -b "$BRANCH" "$WT" "$BASE" >&2

mkdir -p "$WT/.lake"
# Shared immutable Mathlib cache: SYMLINK (never copy the 5GB).
ln -sfn "$MAIN_REPO/.lake/packages" "$WT/.lake/packages"
echo ">> symlinked .lake/packages -> $MAIN_REPO/.lake/packages" >&2

# Private build dir: reflink if the FS supports CoW, else a plain copy (~263M).
rm -rf "$WT/.lake/build" 2>/dev/null || true
if cp -a --reflink=always "$MAIN_REPO/.lake/build" "$WT/.lake/build" 2>/dev/null; then
  echo ">> reflinked .lake/build (CoW)" >&2
else
  cp -a "$MAIN_REPO/.lake/build" "$WT/.lake/build"
  echo ">> copied .lake/build (no reflink on this FS)" >&2
fi

echo ">> worktree ready: $WT" >&2
echo "$WT"
