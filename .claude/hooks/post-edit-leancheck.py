#!/usr/bin/env python3
"""PostToolUse hook: after an Edit/Write/MultiEdit of a Lean file under `Oseledets/`, deliver warm
`leancheck` diagnostics to the agent automatically, as `additionalContext` — the agent does NOT run
anything.

NON-BLOCKING by design (so the hook can never exceed its timeout and have its stdout discarded):
  * if the warm REPL daemon is already up  -> run the fast check and return the report;
  * if it is not up                        -> kick off a DETACHED background warm-up and return
                                              immediately with a short "warming" note; the real
                                              diagnostics then arrive automatically on the next edit.

Also records the touched module for the Stop cold-gate, and appends one line per invocation to a
/tmp debug log (`LEANCHECK_HOOK_LOG`, default /tmp/leancheck-hook.log) for observability/verification.

`--selftest` runs offline unit tests of the pure decision logic (no Lean, no daemon)."""
import sys, os, json, subprocess, time

KEY = os.environ.get("LEANCHECK_KEY", "oseledets")
SOCK = os.path.join(os.environ.get("LEANCHECK_SOCKDIR", "/tmp"), f"leancheck-{KEY}.sock")
DEBUG = os.environ.get("LEANCHECK_HOOK_LOG", "/tmp/leancheck-hook.log")

# ---------------------------------------------------------------- pure logic (unit-tested)

def is_target(tool, path):
    """True iff this tool call is an edit of a Lean source file under an `Oseledets/` directory."""
    return (tool in ("Edit", "Write", "MultiEdit")
            and isinstance(path, str) and path.endswith(".lean")
            and os.sep + "Oseledets" + os.sep in path)

def warming_context(basename):
    return (f"leancheck: warming the Lean REPL in the background (~1-2 min); warm diagnostics for "
            f"{basename} will appear automatically on your next edit. The cold `lake build` Stop "
            f"gate remains the authoritative check.")

def report_context(basename, report):
    """Compose the additionalContext for a completed warm check (or a fallback if empty)."""
    if not report:
        return (f"leancheck: no diagnostics returned for {basename} (daemon may be restarting); "
                f"rely on the cold build.")
    return "leancheck (warm) — " + basename + ":\n" + report

def hook_output(ctx):
    """The PostToolUse JSON envelope that injects `ctx` into the agent's context."""
    return {"hookSpecificOutput": {"hookEventName": "PostToolUse", "additionalContext": ctx}}

# ---------------------------------------------------------------- side effects

def dbg(msg):
    try:
        with open(DEBUG, "a", encoding="utf-8") as f:
            f.write(f"{time.strftime('%H:%M:%S')} [post-edit pid={os.getpid()}] {msg}\n")
    except Exception:
        pass

def emit(ctx):
    print(json.dumps(hook_output(ctx)))

def record_touch(rel, session, proj):
    try:
        mod = rel[:-5].replace(os.sep, ".")
        touch = f"/tmp/leancheck-touched-{session}.txt"
        seen = set(open(touch).read().split()) if os.path.exists(touch) else set()
        seen.add(mod)
        open(touch, "w").write("\n".join(sorted(seen)))
    except Exception as e:
        dbg(f"touch-list error: {e}")

def main():
    t0 = time.time()
    try:
        d = json.load(sys.stdin)
    except Exception as e:
        dbg(f"no stdin json: {e}")
        return 0
    tool = d.get("tool_name")
    ti = d.get("tool_input") or {}
    path = ti.get("file_path") or ti.get("path") or ""
    if not is_target(tool, path):
        return 0

    proj = os.environ.get("CLAUDE_PROJECT_DIR", os.getcwd())
    leancheck = os.path.join(proj, ".claude", "leancheck", "leancheck.py")
    session = d.get("session_id", "default")
    env = dict(os.environ, LEANCHECK_KEY=KEY, LEANCHECK_ROOT=proj)
    rel = os.path.relpath(os.path.abspath(path), proj)
    base = os.path.basename(path)
    record_touch(rel, session, proj)

    if not os.path.exists(SOCK):
        # Daemon cold: spawn a DETACHED background warm-up and return now (non-blocking).
        try:
            subprocess.Popen([sys.executable, leancheck, "--warm"], env=env,
                             stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                             start_new_session=True, cwd=proj)
            dbg(f"{rel}: COLD -> spawned background warm; returned in {time.time()-t0:.2f}s")
        except Exception as e:
            dbg(f"{rel}: COLD, warm-spawn failed: {e}")
        emit(warming_context(base))
        return 0

    # Daemon warm: run the fast check (bounded timeout as a safety net).
    try:
        r = subprocess.run([sys.executable, leancheck, path], env=env,
                           capture_output=True, text=True, timeout=60)
        report = (r.stdout or "").strip()
        dbg(f"{rel}: WARM check exit={r.returncode} bytes={len(report)} in {time.time()-t0:.2f}s")
    except Exception as e:
        dbg(f"{rel}: WARM check error: {e}")
        report = ""
    emit(report_context(base, report))
    return 0

# ---------------------------------------------------------------- offline self-test

def selftest():
    assert is_target("Edit", "/r/Oseledets/A.lean")
    assert is_target("Write", "/r/Oseledets/Continuous/A.lean")
    assert is_target("MultiEdit", "/r/x/Oseledets/y/A.lean")
    assert not is_target("Edit", "/r/Other/A.lean"), "must require an Oseledets/ dir"
    assert not is_target("Edit", "/r/Oseledets/A.txt"), "must require .lean"
    assert not is_target("Read", "/r/Oseledets/A.lean"), "only edit tools"
    assert not is_target("Edit", ""), "empty path"
    w = warming_context("A.lean")
    assert "warming" in w and "A.lean" in w
    r = report_context("A.lean", "Oseledets/A.lean:3:5: error: boom")
    assert "error: boom" in r and r.startswith("leancheck (warm)")
    assert "no diagnostics" in report_context("A.lean", "")
    env = hook_output(w)
    assert env["hookSpecificOutput"]["hookEventName"] == "PostToolUse"
    assert env["hookSpecificOutput"]["additionalContext"] == w
    json.loads(json.dumps(env))  # serialisable
    print("post-edit-leancheck selftest OK")
    return 0

if __name__ == "__main__":
    if "--selftest" in sys.argv:
        sys.exit(selftest())
    sys.exit(main() or 0)
