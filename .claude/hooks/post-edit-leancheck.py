#!/usr/bin/env python3
"""PostToolUse hook: after an agent Edits/Writes a Lean file under Oseledets/, run the warm
`leancheck` and hand the diagnostics straight back as additionalContext — so the agent gets
its compile/error report "for free" on the tool result, with no extra tool call.

Also records the touched module in a per-session list that the SubagentStop cold-gate reads.
Non-blocking: it only ever adds context (never blocks the edit)."""
import sys, os, json, subprocess

def main():
    try:
        d = json.load(sys.stdin)
    except Exception:
        return 0
    if d.get("tool_name") not in ("Edit", "Write", "MultiEdit"):
        return 0
    ti = d.get("tool_input") or {}
    path = ti.get("file_path") or ti.get("path") or ""
    if not (path.endswith(".lean") and os.sep + "Oseledets" + os.sep in path):
        return 0

    proj = os.environ.get("CLAUDE_PROJECT_DIR", os.getcwd())
    leancheck = os.path.join(proj, ".claude", "leancheck", "leancheck.py")
    session = d.get("session_id", "default")
    # Use a stable per-repo daemon key (NOT the session id) so that this hook and the
    # worker's own active `leancheck <file>` calls share the same warm REPL: the hook
    # then doubles as a warmer for the agent's active checks. (The passive report below
    # is best-effort; PostToolUse additionalContext does not reliably reach subagent loops,
    # so workers are told to run the check themselves — see .claude/agents/lean-worker.md.)
    env = dict(os.environ, LEANCHECK_KEY="oseledets", LEANCHECK_ROOT=proj)

    # record the touched module for the Stop cold-gate
    try:
        mod = os.path.relpath(os.path.abspath(path), proj)[:-5].replace(os.sep, ".")
        touch = f"/tmp/leancheck-touched-{session}.txt"
        seen = set(open(touch).read().split()) if os.path.exists(touch) else set()
        seen.add(mod)
        open(touch, "w").write("\n".join(sorted(seen)))
    except Exception:
        pass

    try:
        r = subprocess.run([sys.executable, leancheck, path], env=env,
                           capture_output=True, text=True, timeout=300)
        report = (r.stdout or "").strip()
    except Exception as e:
        report = f"leancheck unavailable ({e}); rely on the cold build."
    if not report:
        return 0
    print(json.dumps({"hookSpecificOutput": {
        "hookEventName": "PostToolUse",
        "additionalContext": "leancheck (warm) — " + os.path.basename(path) + ":\n" + report}}))
    return 0

if __name__ == "__main__":
    sys.exit(main() or 0)
