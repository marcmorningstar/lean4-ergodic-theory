#!/usr/bin/env bash
# PreToolUse(Bash) hook: forbid git for SUBAGENTS (workflow/Task workers).
# The main orchestrator session may use git; subagents must report problems
# to the orchestrator instead of touching version control. A prior run lost
# work when a worker ran `git reset`, wiping other workers' edits.
# Detection: subagent tool calls carry a transcript_path under ".../subagents/...".
python3 -c '
import sys, json, re
try:
    d = json.load(sys.stdin)
except Exception:
    sys.exit(0)  # unparseable -> fail open (keeps orchestrator git working)
cmd = (d.get("tool_input") or {}).get("command", "") or ""
tp  = d.get("transcript_path", "") or ""
if not re.search(r"(^|[\s;&|()])git(\s|$)", cmd):
    sys.exit(0)               # not a git command
if "/subagents/" in tp:       # this is a worker
    sys.stderr.write(
        "BLOCKED by orchestrator policy: subagents may NOT run any git command "
        "(no add/commit/reset/checkout/restore/stash/clean/rm/push/etc.). Do not use "
        "version control at all. Just edit `.lean` files and read the automatic leancheck "
        "report appended to each edit (no need to run lake/lean). If you hit a problem you "
        "cannot resolve, describe it in your final answer so the orchestrator can handle it.\n"
    )
    sys.exit(2)               # exit 2 = block the tool call, feed stderr to the agent
sys.exit(0)
'
