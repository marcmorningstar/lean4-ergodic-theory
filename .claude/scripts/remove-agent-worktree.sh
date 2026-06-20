#!/usr/bin/env bash
# remove-agent-worktree.sh — tear down an agent worktree created by new-agent-worktree.sh.
# The .lake/packages symlink and the private .lake/build copy are removed with the tree;
# the shared cache they pointed at is untouched. The branch is left in place (merge/delete
# it from the main repo as you see fit).
#
# Usage: remove-agent-worktree.sh <worktree-path>
#   Env: MAIN_REPO (default /workspaces/lean4-oseledets).
set -euo pipefail

MAIN_REPO="${MAIN_REPO:-/workspaces/lean4-oseledets}"
WT="${1:?usage: remove-agent-worktree.sh <worktree-path>}"

# Drop the symlink first so `git worktree remove` never recurses into the 5GB shared cache.
rm -f "$WT/.lake/packages" 2>/dev/null || true
git -C "$MAIN_REPO" worktree remove --force "$WT"
echo ">> removed worktree: $WT" >&2
