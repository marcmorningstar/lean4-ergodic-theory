#!/usr/bin/env python3
"""SubagentStop / Stop hook: before an agent is allowed to finish, run the AUTHORITATIVE
cold `lake build` of every Lean module it touched this session. If any fails, block the stop
and hand the cold errors back so the agent must keep working. If all pass (or nothing was
touched), allow the stop — so the orchestrator is only notified when the work is *really*
verified and the agent cannot "forget" the cold gate.

Loop guard: blocks at most MAX_TRIES times per session; after that it allows the stop but
prepends a loud UNVERIFIED banner to the reason so the failure is surfaced, never hung."""
import sys, os, json, subprocess

MAX_TRIES = 6

def main():
    try:
        d = json.load(sys.stdin)
    except Exception:
        return 0
    session = d.get("session_id", "default")
    proj = os.environ.get("CLAUDE_PROJECT_DIR", os.getcwd())
    leancheck = os.path.join(proj, ".claude", "leancheck", "leancheck.py")
    touch = f"/tmp/leancheck-touched-{session}.txt"
    if not os.path.exists(touch):
        return 0                                   # nothing edited -> nothing to gate
    modules = [m for m in open(touch).read().split() if m]
    if not modules:
        return 0

    env = dict(os.environ, LEANCHECK_ROOT=proj)
    failures = []
    for mod in modules:
        r = subprocess.run([sys.executable, leancheck, "--cold", mod], env=env,
                           capture_output=True, text=True)
        if r.returncode != 0:
            failures.append(f"### {mod}\n{(r.stdout or '').strip()}")

    if not failures:
        return 0                                   # verified clean -> allow stop

    triesf = f"/tmp/leancheck-tries-{session}.txt"
    tries = int(open(triesf).read()) if os.path.exists(triesf) else 0
    tries += 1
    open(triesf, "w").write(str(tries))
    body = "\n\n".join(failures)
    if tries <= MAX_TRIES:
        reason = ("Cold `lake build` of your edited module(s) FAILED — you cannot finish yet. "
                  "Fix these and continue:\n\n" + body)
        print(json.dumps({"decision": "block", "reason": reason}))
        return 0
    # gave up: allow stop but make the unverified state impossible to miss
    print(json.dumps({"decision": "block", "reason":
        f"UNVERIFIED after {MAX_TRIES} cold-build attempts — report this as a FAILED/open node "
        f"in your final message (do NOT claim success):\n\n" + body}), file=sys.stderr)
    return 0                                        # exit 0 -> stop allowed this time

if __name__ == "__main__":
    sys.exit(main() or 0)
