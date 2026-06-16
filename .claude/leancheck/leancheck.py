#!/usr/bin/env python3
"""leancheck — warm Lean diagnostics via the real language server (`lake serve`), with a cold
`lake build` gate. The agent never sees JSON or the LSP protocol: it edits a `.lean` file and
either gets diagnostics for free (PostToolUse hook) or runs `leancheck <file>`.

The engine is `leanclient` (the maintained client `lean-lsp-mcp` is built on), driving one
persistent `lake serve`. `lake serve` owns import resolution, incremental within-file elaboration,
the diagnostics-finalization handshake, stale-import auto-rebuild, and process lifecycle, so this
file is thin plumbing.

WORKTREE-SAFE: the daemon socket key is derived from the (realpath'd) project root, so each
worktree/checkout gets its OWN `lake serve` bound to its own root; workers within one tree share it.
A per-root `flock` makes the daemon a singleton: only one `lake serve` per root can ever bind, so
racing callers never spawn (and orphan) a second multi-GB server.

MATHLIB GUARD: if Mathlib's oleans are absent (so a build/serve would recompile Mathlib from source
— HOURS), every entry point ABORTS with a loud warning instead of silently starting the rebuild,
unless `LEANCHECK_ALLOW_MATHLIB_REBUILD=1`.

Modes
-----
  leancheck <file.lean>        warm diagnostics (NON-BLOCKING; a cold file warms in the background)
  leancheck --cold <file|mod>  authoritative `lake build` of the module (the QA gate)
  leancheck --warm [file]      start the daemon (with a file, also start warming it)
  leancheck --stop             stop the daemon (kills `lake serve` + its `lean --server` child)
  leancheck --check-mathlib    report whether Mathlib is built (exit 1 + warning if not)
  leancheck --daemon           (internal) the long-lived server host
  leancheck --selftest         offline unit tests of the pure logic

Config (env): LEANCHECK_ROOT [cwd], LEANCHECK_KEY [derived from root], LEANCHECK_SOCKDIR [/tmp],
              LEANCHECK_MAXFILES [8], LEANCHECK_WARM_MAX [240], LEANCHECK_RECHECK_MAX [55],
              LEANCHECK_HOOK_LOG [/tmp/leancheck-hook.log], LEANCHECK_ALLOW_MATHLIB_REBUILD [unset].

Cross-file note: `lake serve` resolves imports from `.olean`, so a file's check reflects its OWN
current source but sees dependencies as last built — a changed dependency must be rebuilt to be
visible. Each warm re-check re-syncs the file's CURRENT on-disk content into the server (didChange)
before reading diagnostics, so a re-check never returns stale results for the edited file. The cold
`lake build` + guarded AxiomAudit remain the source of truth.
"""
import sys, os, json, socket, subprocess, time, argparse, re, threading, hashlib

ROOT = os.path.realpath(os.environ.get("LEANCHECK_ROOT", os.getcwd()))
KEY = os.environ.get("LEANCHECK_KEY") or ("oseledets-" + hashlib.sha1(ROOT.encode()).hexdigest()[:8])
SOCK = os.path.join(os.environ.get("LEANCHECK_SOCKDIR", "/tmp"), f"leancheck-{KEY}.sock")
LOCKFILE = SOCK + ".lock"                       # flock target: makes the daemon a per-root singleton
PIDFILE = SOCK + ".pid"                          # records daemon + lake-serve pids for orphan reaping
MAXFILES = int(os.environ.get("LEANCHECK_MAXFILES", "8"))
WARM_MAX = float(os.environ.get("LEANCHECK_WARM_MAX", "240"))      # first-open ceiling (background)
RECHECK_MAX = float(os.environ.get("LEANCHECK_RECHECK_MAX", "55")) # bounded under the 80s hook budget
ALLOW_REBUILD = os.environ.get("LEANCHECK_ALLOW_MATHLIB_REBUILD") == "1"

# ---------------------------------------------------------------- Mathlib-rebuild guard

def mathlib_built(root):
    """True iff Mathlib's oleans are present, i.e. a `lake build`/`lake serve` will NOT recompile
    Mathlib from source (a multi-hour operation). Detects the missing-cache case: a fresh checkout,
    or a worktree without the prebuilt `.lake` cache (or its symlink)."""
    base = os.path.join(root, ".lake", "packages", "mathlib", ".lake", "build", "lib")
    for cand in ("lean/Mathlib/Init.olean", "Mathlib/Init.olean"):   # pinned-toolchain layout first
        if os.path.exists(os.path.join(base, cand)):
            return True
    if os.path.isdir(base):                                          # fallback: any Mathlib olean
        for _dp, _dn, fs in os.walk(base):
            if any(f.endswith(".olean") for f in fs):
                return True
    return False

MATHLIB_WARNING = (
    "================ ⚠️  SERIOUS WARNING: MATHLIB IS NOT BUILT ================\n"
    "Mathlib's compiled oleans are missing under .lake/packages/mathlib, so a `lake build` or\n"
    "`lake serve` here would COMPILE MATHLIB FROM SOURCE — HOURS of CPU, not a quick check.\n"
    "  * On a brand-new checkout this is expected: fetch the prebuilt cache first.\n"
    "  * In a WORKTREE it usually means the prebuilt `.lake` cache (or its symlink) is missing.\n"
    "leancheck ABORTED rather than silently start a multi-hour rebuild. Decide explicitly:\n"
    "  - cancel, fix the cache/symlink, and retry; OR\n"
    "  - accept the from-scratch rebuild by re-running with  LEANCHECK_ALLOW_MATHLIB_REBUILD=1\n"
    "==================================================================================")

def mathlib_guard():
    """Warning text if a from-scratch Mathlib rebuild is imminent and not opted into, else None."""
    if ALLOW_REBUILD or mathlib_built(ROOT):
        return None
    return MATHLIB_WARNING

# ---------------------------------------------------------------- pure logic (unit-tested)

SEVERITY = {1: "error", 2: "warning", 3: "info", 4: "hint"}

def format_diagnostics(relpath, diagnostics):
    """LSP diagnostics (list of {range,severity,message}) -> (compiler-style text, n_errors).
    LSP positions are 0-based; we emit 1-based line:col. Messages are first-line-only."""
    out, n_err = [], 0
    for d in diagnostics or []:
        start = (d.get("range") or {}).get("start") or {}
        line = start.get("line", 0) + 1
        col = start.get("character", 0) + 1
        sev = SEVERITY.get(d.get("severity", 1), "info")
        msg = (d.get("message", "") or "").strip().split("\n", 1)[0]
        if sev == "error":
            n_err += 1
        out.append(f"{relpath}:{line}:{col}: {sev}: {msg}")
    if not out:
        out.append("✓ no errors")
    return "\n".join(out), n_err

# ---------------------------------------------------------------- the language-server daemon

class Engine:
    """Owns one persistent `lake serve` (via leanclient) and warms cold files in the background so a
    check never blocks: the first open elaborates a file; until then a check returns "warming";
    afterwards re-checks re-sync the file from disk (didChange) and read fresh diagnostics fast.

    No global server lock: leanclient is internally thread-safe (its diagnostics wait releases the
    file lock on a condition variable while a dedicated reader thread updates state), so concurrent
    checks of different files interleave. A small lock guards only the warming/ready bookkeeping."""
    def __init__(self):
        from leanclient import LeanLSPClient            # imported lazily: only the daemon needs it
        self.client = LeanLSPClient(ROOT, initial_build=False, prevent_cache_get=True,
                                    max_opened_files=MAXFILES)
        self.slock = threading.Lock()                   # guards the warming/ready sets + lock table
        self.ready = set()
        self.warming = set()
        self.closing = False
        self.locks = {}                                 # per-file locks (created lazily under slock)

    def lakeserve_pid(self):
        try:
            return self.client.process.pid
        except Exception:
            return None

    def _filelock(self, rel):
        """A per-file lock so two concurrent rechecks of the SAME file can't interleave leanclient's
        read-disk / compute-change / apply-change sync — which would apply a change whose end-range
        was computed from a now-stale line count and garble the server's view of the file. Distinct
        files keep distinct locks, so they still elaborate concurrently (no head-of-line block)."""
        with self.slock:
            lk = self.locks.get(rel)
            if lk is None:
                lk = self.locks[rel] = threading.Lock()
            return lk

    def _warm(self, rel):
        try:
            with self._filelock(rel):
                self.client.open_files([rel])           # first open: load import closure + elaborate
                self.client.get_diagnostics(rel, inactivity_timeout=15.0, max_timeout=WARM_MAX)
        except Exception:
            pass
        with self.slock:
            self.warming.discard(rel); self.ready.add(rel)

    def check(self, rel):
        if self.closing:
            return "leancheck: daemon shutting down; rely on the cold build."
        with self.slock:
            if rel in self.warming:
                return f"leancheck: still warming {os.path.basename(rel)}; diagnostics shortly."
            first = rel not in self.ready
            if first:
                self.warming.add(rel)
        if first:
            threading.Thread(target=self._warm, args=(rel,), daemon=True).start()
            return (f"leancheck: warming {os.path.basename(rel)} in the Lean server (first open "
                    f"of a file takes a moment); diagnostics appear on your next edit. The cold "
                    f"`lake build` Stop gate remains authoritative.")
        # Ready: re-sync the file's CURRENT on-disk content into the server (didChange if changed),
        # then read fresh diagnostics. Without this re-sync an already-open file returns the
        # diagnostics from its first open — i.e. stale results that ignore the agent's later edits.
        try:
            with self._filelock(rel):
                self.client.open_files([rel])
                res = self.client.get_diagnostics(rel, inactivity_timeout=8.0, max_timeout=RECHECK_MAX)
        except Exception as e:
            return f"leancheck: recheck error for {os.path.basename(rel)}: {e}; rely on the cold build."
        text, _ = format_diagnostics(rel, getattr(res, "diagnostics", []))
        if getattr(res, "timed_out", False):
            text += (f"\n(leancheck: diagnostics wait timed out at {RECHECK_MAX:.0f}s — report may be "
                     f"incomplete; the cold `lake build` is authoritative)")
        return text

    def close(self):
        self.closing = True
        try:
            self.client.close()                         # leanclient kills lake serve + lean --server
        except Exception:
            pass

# ---------------------------------------------------------------- process / liveness helpers

def _unix_sock():
    return socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)

def _daemon_alive():
    """Liveness by an ACTUAL connection, not mere socket-file existence: a socket left by a
    crashed/SIGKILLed daemon exists on disk but refuses connections (stale-socket safe)."""
    if not os.path.exists(SOCK):
        return False
    try:
        c = _unix_sock(); c.settimeout(2.0); c.connect(SOCK); c.close()
        return True
    except OSError:
        return False

def _proc_ctime(pid):
    """Process create-time (epoch secs) for `pid`, or None — a PID-reuse-safe identity stamp."""
    if not pid:
        return None
    try:
        import psutil
        return psutil.Process(pid).create_time()
    except Exception:
        return None

def _reap_orphan_lakeserve():
    """Called right after winning the singleton lock — which proves any daemon recorded in PIDFILE
    is already dead. Kill its orphaned `lake serve` (and children) if still alive, covering a
    SIGKILLed/OOM-killed/crashed predecessor that could not run its own cleanup. Identity is matched
    by the recorded create-time, NOT argv: the project path here contains the substring "lean", so a
    cmdline check would match almost any recycled pid — create-time is the reliable PID-reuse guard."""
    try:
        with open(PIDFILE) as f:
            rec = json.load(f)
    except Exception:
        return
    spid = rec.get("serve")
    if not spid:
        return
    try:
        import psutil
        p = psutil.Process(spid)
        sct = rec.get("serve_ctime")
        if sct is not None:
            same = abs(p.create_time() - sct) < 1.0            # exact process, not a recycled pid
        else:                                                   # legacy pidfile: fall back to argv[0]
            argv = p.cmdline()
            same = bool(argv) and os.path.basename(argv[0]) in ("lake", "lean")
        if same:
            for c in p.children(recursive=True):
                try: c.kill()
                except Exception: pass
            p.kill()
    except Exception:
        pass

_LOCKF = None   # the held-open flock fd; kept alive for the daemon's whole lifetime

def daemon():
    import atexit, signal, fcntl
    global _LOCKF
    # Singleton: only one daemon per project root may proceed. A loser exits at the lock — BEFORE
    # constructing an Engine or touching the socket — so it can never delete a live daemon's socket
    # or orphan a second lake serve (the TOCTOU double-spawn that leaked multi-GB servers).
    _LOCKF = open(LOCKFILE, "w")
    try:
        fcntl.flock(_LOCKF, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        os._exit(0)
    _reap_orphan_lakeserve()                    # winning the lock => predecessor is dead; reap its server
    eng = Engine()                              # starts lake serve (the first FILE open is the slow part)

    def _cleanup(*_):
        eng.close()
        for p in (SOCK, PIDFILE):
            try: os.remove(p)
            except OSError: pass

    atexit.register(_cleanup)
    for s in (signal.SIGTERM, signal.SIGINT):
        signal.signal(s, lambda *_: (_cleanup(), os._exit(0)))
    if os.path.exists(SOCK):
        os.remove(SOCK)
    srv = _unix_sock(); srv.bind(SOCK); srv.listen(64)
    try:
        spid = eng.lakeserve_pid()
        with open(PIDFILE, "w") as f:
            json.dump({"daemon": os.getpid(), "serve": spid, "serve_ctime": _proc_ctime(spid)}, f)
    except Exception:
        pass
    # One thread per connection: a slow check (warm/recheck) never stalls the accept loop or other
    # in-flight checks (the single-threaded inline loop was the head-of-line block).
    while True:
        try:
            conn, _ = srv.accept()
        except OSError:
            continue
        threading.Thread(target=_serve_conn, args=(conn, eng), daemon=True).start()

def _serve_conn(conn, eng):
    try:
        req = json.loads(_recv_all(conn) or "{}")
        f = req.get("file")
        if f in (None, "", "__ping__"):                 # liveness probe (bare connect / ping)
            try: conn.sendall(b"pong")
            except OSError: pass
            return
        if f == "__stop__":
            try: conn.sendall(b"stopping")
            except OSError: pass
            conn.close()
            eng.close()
            for p in (SOCK, PIDFILE):
                try: os.remove(p)
                except OSError: pass
            os._exit(0)
        rel = os.path.relpath(os.path.abspath(f), ROOT)
        conn.sendall(eng.check(rel).encode())
    except Exception as e:
        try: conn.sendall(f"leancheck daemon error: {e}".encode())
        except OSError: pass
    finally:
        try: conn.close()
        except OSError: pass

# ---------------------------------------------------------------- client / CLI

def _recv_all(conn):
    chunks = []
    while True:
        b = conn.recv(65536)
        if not b:
            break
        chunks.append(b)
    return b"".join(chunks).decode()

def ensure_daemon():
    if _daemon_alive():
        return
    # Do NOT unlink the socket from here: only the flock-winning daemon may remove a stale socket
    # (it does so before bind, while holding the lock), so a client can never race-unlink a LIVE
    # daemon's socket — which would wedge the channel and leak its lake serve.
    g = mathlib_guard()
    if g:
        raise SystemExit(g)                   # backstop: never start lake serve on an unbuilt tree
    subprocess.Popen([sys.executable, os.path.abspath(__file__), "--daemon"],
                     stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                     start_new_session=True, cwd=ROOT)
    for _ in range(900):                      # readiness = a real successful connection (~90s budget)
        if _daemon_alive():
            return
        time.sleep(0.1)
    raise SystemExit("leancheck: daemon did not come up")

def warm_check(path):
    g = mathlib_guard()
    if g:
        print(g); return 1
    ensure_daemon()
    out = "leancheck: daemon unreachable; rely on the cold build."
    for attempt in (1, 2):                    # one respawn retry if the daemon died/staled mid-call
        try:
            c = _unix_sock(); c.settimeout(120.0); c.connect(SOCK)
            c.sendall(json.dumps({"file": os.path.abspath(path)}).encode()); c.shutdown(socket.SHUT_WR)
            out = _recv_all(c); c.close()
            break
        except OSError:
            # Daemon unreachable: let ensure_daemon probe and respawn only if it is truly dead.
            # Never unlink the socket from the client side (could race-kill a live daemon's socket).
            if attempt == 1:
                ensure_daemon()
    print(out)
    return 1 if re.search(r": error:", out or "") else 0

def stop_daemon():
    import signal
    if os.path.exists(SOCK):
        try:
            c = _unix_sock(); c.settimeout(10.0); c.connect(SOCK)
            c.sendall(b'{"file":"__stop__"}'); _recv_all(c); c.close()
        except OSError:
            pass
    elif os.path.exists(PIDFILE):             # socket gone but the daemon may still live: signal it
        try:
            with open(PIDFILE) as f:
                rec = json.load(f)
            dpid = rec.get("daemon")
            if dpid:
                os.kill(dpid, signal.SIGTERM)
        except Exception:
            pass
    for p in (SOCK, PIDFILE):
        if os.path.exists(p):
            try: os.remove(p)
            except OSError: pass
    return 0

def module_of(target):
    if not target.endswith(".lean"):
        return target
    return os.path.relpath(os.path.abspath(target), ROOT)[:-5].replace("/", ".")

def cold_check(target):
    g = mathlib_guard()
    if g:
        print(g); return 1
    r = subprocess.run(["lake", "build", module_of(target)], cwd=ROOT, capture_output=True, text=True)
    diags = [l for l in (r.stdout + r.stderr).split("\n") if re.search(r"error:|warning:", l)]
    print("\n".join(diags) if diags else "✓ cold build clean")
    return r.returncode

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("target", nargs="?")
    ap.add_argument("--cold", action="store_true")
    ap.add_argument("--warm", action="store_true")
    ap.add_argument("--stop", action="store_true")
    ap.add_argument("--daemon", action="store_true")
    ap.add_argument("--check-mathlib", action="store_true")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest:
        return selftest()
    if a.check_mathlib:
        if mathlib_built(ROOT):
            print("✓ Mathlib oleans present (a build/serve will NOT recompile Mathlib)"); return 0
        print(MATHLIB_WARNING); return 1
    if a.daemon:
        return daemon()
    if a.stop:
        return stop_daemon()
    if a.warm:
        g = mathlib_guard()
        if g:
            print(g); return 1
        ensure_daemon()
        if a.target:
            return warm_check(a.target)
        print("warm"); return 0
    if not a.target:
        ap.error("need a file/module (or a mode flag)")
    return cold_check(a.target) if a.cold else warm_check(a.target)

# ---------------------------------------------------------------- offline self-test

def selftest():
    import tempfile
    diags = [
        {"range": {"start": {"line": 158, "character": 0}}, "severity": 1,
         "message": "Not a definitional equality\n  detail"},
        {"range": {"start": {"line": 3, "character": 7}}, "severity": 2,
         "message": "declaration uses 'sorry'"},
    ]
    text, nerr = format_diagnostics("Oseledets/Continuous/Flow.lean", diags)
    assert nerr == 1, nerr
    assert "Flow.lean:159:1: error: Not a definitional equality" in text, text
    assert "detail" not in text, "first-line-only"
    assert "Flow.lean:4:8: warning: declaration uses 'sorry'" in text, text
    clean, n0 = format_diagnostics("T.lean", [])
    assert n0 == 0 and clean == "✓ no errors", clean
    # Mathlib guard: an empty dir reads as not-built (would rebuild) -> warning fires
    d = tempfile.mkdtemp()
    assert mathlib_built(d) is False, "empty tree must read as not-built"
    # Per-root key derivation is deterministic and path-sensitive (worktree-safe)
    k = lambda p: "oseledets-" + hashlib.sha1(p.encode()).hexdigest()[:8]
    assert k("/repo/a") != k("/repo/b"), "different roots must yield different daemon keys"
    assert k("/repo/a") == k("/repo/a"), "same root must yield the same key"
    # Daemon-control files are derived from the socket path (singleton lock + orphan-reap pidfile)
    assert LOCKFILE == SOCK + ".lock" and PIDFILE == SOCK + ".pid", (LOCKFILE, PIDFILE)
    print("leancheck selftest OK")
    return 0

if __name__ == "__main__":
    sys.exit(main() or 0)
