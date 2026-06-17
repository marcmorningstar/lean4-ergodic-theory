#!/usr/bin/env python3
"""SubagentStop / Stop hook: before an agent is allowed to finish, run the AUTHORITATIVE
cold `lake build` of every Lean module it touched this session. If any fails, block the stop
and hand the cold errors back so the agent must keep working. If all pass (or nothing was
touched), allow the stop — so the orchestrator is only notified when the work is *really*
verified and the agent cannot "forget" the cold gate.

Loop guard: blocks at most MAX_TRIES times per session; after that it allows the stop but
prepends a loud UNVERIFIED banner so the failure is surfaced, never hung.

Appends one line per invocation to the /tmp debug log. `--selftest` runs offline unit tests."""
import sys, os, json, subprocess, time

MAX_TRIES = 6
DEBUG = os.environ.get("LEANCHECK_HOOK_LOG", "/tmp/leancheck-hook.log")

# ---------------------------------------------------------------- pure logic (unit-tested)

def read_modules(touch):
    """The touched-module list for the cold gate (deduped tokens), or [] if none."""
    if not os.path.exists(touch):
        return []
    return [m for m in open(touch).read().split() if m]

def module_to_path(mod, proj):
    """Module name -> its `.lean` source path, e.g. `Oseledets.Lyapunov.Foo` ->
    `<proj>/Oseledets/Lyapunov/Foo.lean`."""
    return os.path.join(proj, mod.replace(".", os.sep) + ".lean")

def filter_present(modules, proj):
    """Split the touched modules into (present, skipped) by whether their source still exists.
    A throwaway probe module that was edited (so it landed in the touched-list) and then deleted
    leaves a PHANTOM entry: `lake build` of it fails with 'no source' and would wrongly block the
    stop, which previously forced agents to leave probe files lying around. We skip such entries
    (and log them) so a deleted module never blocks the gate; a real module is still always built."""
    present, skipped = [], []
    for m in modules:
        (present if os.path.exists(module_to_path(m, proj)) else skipped).append(m)
    return present, skipped

def block_reason(failures, tries, max_tries):
    """Decision: return (reason_text_or_None, allow_stop). `failures` are per-module error blocks."""
    if not failures:
        return (None, True)
    body = "\n\n".join(failures)
    if tries <= max_tries:
        return ("Cold `lake build` of your edited module(s) FAILED — you cannot finish yet. "
                "Fix these and continue:\n\n" + body, False)
    return (f"UNVERIFIED after {max_tries} cold-build attempts — report this as a FAILED/open node "
            f"in your final message (do NOT claim success):\n\n" + body, True)

# ---------------------------------------------------------------- side effects

def dbg(msg):
    try:
        with open(DEBUG, "a", encoding="utf-8") as f:
            f.write(f"{time.strftime('%H:%M:%S')} [stop-gate pid={os.getpid()}] {msg}\n")
    except Exception:
        pass

def main():
    try:
        d = json.load(sys.stdin)
    except Exception:
        return 0
    session = d.get("session_id", "default")
    proj = os.environ.get("CLAUDE_PROJECT_DIR", os.getcwd())
    leancheck = os.path.join(proj, ".claude", "leancheck", "leancheck.py")
    modules = read_modules(f"/tmp/leancheck-touched-{session}.txt")
    modules, skipped = filter_present(modules, proj)
    if skipped:                                    # deleted throwaway/probe modules -> never gate on them
        dbg(f"skipped {len(skipped)} touched module(s) with no source: {' '.join(skipped)}")
    if not modules:
        return 0                                   # nothing (still) present to gate

    env = dict(os.environ, LEANCHECK_ROOT=proj)
    failures = []
    for mod in modules:
        r = subprocess.run([sys.executable, leancheck, "--cold", mod], env=env,
                           capture_output=True, text=True)
        if r.returncode != 0:
            failures.append(f"### {mod}\n{(r.stdout or '').strip()}")
    dbg(f"cold-gate: {len(modules)} module(s), {len(failures)} failed")
    if not failures:
        return 0                                   # verified clean -> allow stop

    triesf = f"/tmp/leancheck-tries-{session}.txt"
    tries = (int(open(triesf).read()) if os.path.exists(triesf) else 0) + 1
    open(triesf, "w").write(str(tries))
    reason, allow = block_reason(failures, tries, MAX_TRIES)
    if not allow:
        print(json.dumps({"decision": "block", "reason": reason}))
        dbg(f"BLOCK stop (try {tries})")
    else:
        # exit 0 with the banner on stderr -> stop allowed, but the failure is loudly surfaced
        print(json.dumps({"decision": "block", "reason": reason}), file=sys.stderr)
        dbg(f"gave up after {tries} tries -> allow stop with UNVERIFIED banner")
    return 0

# ---------------------------------------------------------------- offline self-test

def selftest():
    import tempfile
    f = tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False)
    f.write("Oseledets.A\nOseledets.B\n\n"); f.close()
    assert read_modules(f.name) == ["Oseledets.A", "Oseledets.B"], read_modules(f.name)
    os.remove(f.name)
    assert read_modules("/no/such/file") == []
    # filter_present: a deleted/probe module (no source) is skipped; a real one is kept and gated
    proj = tempfile.mkdtemp()
    os.makedirs(os.path.join(proj, "Oseledets", "Lyapunov"))
    open(os.path.join(proj, "Oseledets", "Lyapunov", "Real.lean"), "w").close()
    present, skipped = filter_present(["Oseledets.Lyapunov.Real", "Oseledets.Lyapunov.Ghost"], proj)
    assert present == ["Oseledets.Lyapunov.Real"], present
    assert skipped == ["Oseledets.Lyapunov.Ghost"], skipped
    assert filter_present([], proj) == ([], [])
    assert block_reason([], 1, 6) == (None, True)
    reason, allow = block_reason(["### M\nerr"], 1, 6)
    assert allow is False and "FAILED" in reason and "err" in reason, reason
    reason, allow = block_reason(["### M\nerr"], 7, 6)
    assert allow is True and "UNVERIFIED" in reason, reason
    print("stop-coldbuild selftest OK")
    return 0

if __name__ == "__main__":
    if "--selftest" in sys.argv:
        sys.exit(selftest())
    sys.exit(main() or 0)
