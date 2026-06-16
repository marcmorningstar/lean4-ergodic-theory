#!/usr/bin/env bash
# Unconditional git block — wired into worker SUBAGENT frontmatter (lean-worker,
# mathematician). This hook only runs while that worker subagent is active, so it
# blocks ALL git for workers without needing to detect the caller. Workers must
# report problems to the orchestrator instead of touching version control.
python3 -c '
import sys, json, re
try:
    d = json.load(sys.stdin)
except Exception:
    sys.exit(0)
cmd = (d.get("tool_input") or {}).get("command", "") or ""
if re.search(r"(^|[\s;&|()])git(\s|$)", cmd):
    sys.stderr.write(
        "BLOCKED: this worker subagent may not run any git command. Do not use version "
        "control. Just edit `.lean` files and read the automatic leancheck report appended to "
        "each edit (no need to run lake/lean). If you hit a problem you cannot resolve, describe "
        "it in your final answer so the orchestrator can handle it.\n"
    )
    sys.exit(2)
sys.exit(0)
'
