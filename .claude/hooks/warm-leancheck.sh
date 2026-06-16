#!/usr/bin/env bash
# SessionStart hook: warm the shared `leancheck` REPL daemon in the BACKGROUND so the PostToolUse
# warm check is instant from the first edit. Idempotent (skips if the daemon socket already exists)
# and non-blocking (detaches with nohup and returns immediately, well within any hook timeout — the
# detached warm-up is NOT subject to the hook timeout).
SOCK="/tmp/leancheck-oseledets.sock"
LOG="${LEANCHECK_HOOK_LOG:-/tmp/leancheck-hook.log}"
PROJ="${CLAUDE_PROJECT_DIR:-$PWD}"
echo "$(date +%H:%M:%S) [sessionstart pid=$$] warm trigger; socket present: $([ -e "$SOCK" ] && echo yes || echo no)" >> "$LOG" 2>/dev/null
if [ ! -e "$SOCK" ]; then
  LEANCHECK_KEY=oseledets LEANCHECK_ROOT="$PROJ" \
    nohup python3 "$PROJ/.claude/leancheck/leancheck.py" --warm >> "$LOG" 2>&1 &
fi
exit 0
