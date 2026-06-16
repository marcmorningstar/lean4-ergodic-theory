#!/usr/bin/env python3
"""leancheck — warm Lean diagnostics via the real language server (`lake serve`), with a cold
`lake build` gate. The agent never sees JSON or the LSP protocol: it edits a `.lean` file and
either gets diagnostics for free (PostToolUse hook) or runs `leancheck <file>`.

The engine is `leanclient` (the maintained client `lean-lsp-mcp` is built on), driving one
persistent `lake serve`. `lake serve` is the canonical Lean tooling — it owns import resolution,
incremental within-file elaboration, the diagnostics-finalization handshake
(`waitForDiagnostics` + `$/lean/fileProgress`), and process lifecycle — so this file is just thin
plumbing, not a re-implementation.

Modes
-----
  leancheck <file.lean>        warm diagnostics (NON-BLOCKING: a cold file warms in the background
                               and reports "warming"; once warm, re-checks are ~instant)
  leancheck --cold <file|mod>  authoritative `lake build` of the module (the QA gate)
  leancheck --warm [file]      start the daemon (with a file, also start warming it)
  leancheck --stop             stop the daemon (kills `lake serve` + its `lean --server` child)
  leancheck --daemon           (internal) the long-lived server host
  leancheck --selftest         offline unit tests of the pure formatting logic

Output: compiler-style `path:line:col: severity: message`, or `✓ no errors`, or a "warming" note.
Exit code 0 unless an `error:` diagnostic is present.

Config (env): LEANCHECK_ROOT [cwd], LEANCHECK_KEY [oseledets], LEANCHECK_MAXFILES [8],
              LEANCHECK_HOOK_LOG [/tmp/leancheck-hook.log].

Cross-file note: `lake serve` resolves imports from compiled `.olean`, so a file's check reflects
its OWN current source but sees dependencies as last built — a changed dependency must be rebuilt
(`lake build`) to be visible. The cold `lake build` + guarded AxiomAudit remain the source of truth.
"""
import sys, os, json, socket, subprocess, time, argparse, re, threading

ROOT = os.environ.get("LEANCHECK_ROOT", os.getcwd())
KEY = os.environ.get("LEANCHECK_KEY", "oseledets")
SOCK = os.path.join(os.environ.get("LEANCHECK_SOCKDIR", "/tmp"), f"leancheck-{KEY}.sock")
MAXFILES = int(os.environ.get("LEANCHECK_MAXFILES", "8"))

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
    """Owns one persistent `lake serve` (via leanclient) and warms cold files in the background so
    a check never blocks: a file's first open elaborates it (~tens of seconds for a Mathlib-heavy
    file) on a worker thread; until then a check returns "warming"; afterwards re-checks are fast."""
    def __init__(self):
        from leanclient import LeanLSPClient            # imported lazily: only the daemon needs it
        self.client = LeanLSPClient(ROOT, initial_build=False, prevent_cache_get=True,
                                    max_opened_files=MAXFILES)
        self.clock = threading.Lock()                   # serialize all server access (one lake serve)
        self.slock = threading.Lock()                   # guards the state sets below
        self.ready = set()                              # rel paths elaborated at least once
        self.warming = set()                            # rel paths currently elaborating

    def _warm(self, rel):
        try:
            with self.clock:
                self.client.get_diagnostics(rel)        # elaborate + cache (the slow first open)
        except Exception:
            pass
        with self.slock:
            self.warming.discard(rel); self.ready.add(rel)

    def check(self, rel):
        """Return compiler-style diagnostics text for `rel` (relative to ROOT)."""
        with self.slock:
            if rel not in self.ready:
                if rel in self.warming:
                    return f"leancheck: still warming {os.path.basename(rel)}; diagnostics shortly."
                self.warming.add(rel)
                threading.Thread(target=self._warm, args=(rel,), daemon=True).start()
                return (f"leancheck: warming {os.path.basename(rel)} in the Lean server "
                        f"(first open of a file takes a moment); diagnostics appear on your next "
                        f"edit. The cold `lake build` Stop gate remains authoritative.")
        with self.clock:                                # ready: re-reads disk, re-elaborates, ~fast
            res = self.client.get_diagnostics(rel)
        text, _ = format_diagnostics(rel, getattr(res, "diagnostics", []))
        return text

    def close(self):
        try:
            self.client.close()                         # leanclient recursively kills lean --server
        except Exception:
            pass

def daemon():
    import atexit, signal
    eng = Engine()
    atexit.register(eng.close)
    for s in (signal.SIGTERM, signal.SIGINT):
        signal.signal(s, lambda *_: (eng.close(), os._exit(0)))
    if os.path.exists(SOCK):
        os.remove(SOCK)
    srv = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM); srv.bind(SOCK); srv.listen(8)
    atexit.register(lambda: os.path.exists(SOCK) and os.remove(SOCK))
    while True:
        conn, _ = srv.accept()
        try:
            req = json.loads(_recv_all(conn) or "{}")
            if req.get("file") == "__stop__":
                conn.sendall(b"stopping"); conn.close()
                eng.close()
                if os.path.exists(SOCK):
                    os.remove(SOCK)
                os._exit(0)
            rel = os.path.relpath(os.path.abspath(req["file"]), ROOT)
            conn.sendall(eng.check(rel).encode())
        except Exception as e:
            conn.sendall(f"leancheck daemon error: {e}".encode())
        finally:
            conn.close()

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
    if os.path.exists(SOCK):
        return
    subprocess.Popen([sys.executable, os.path.abspath(__file__), "--daemon"],
                     stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                     start_new_session=True, cwd=ROOT)
    for _ in range(600):                     # wait up to ~60s for the server to boot + bind
        if os.path.exists(SOCK):
            time.sleep(0.2); return
        time.sleep(0.1)
    raise SystemExit("leancheck: daemon did not come up")

def warm_check(path):
    ensure_daemon()
    c = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM); c.connect(SOCK)
    c.sendall(json.dumps({"file": os.path.abspath(path)}).encode()); c.shutdown(socket.SHUT_WR)
    out = _recv_all(c); c.close()
    print(out)
    return 1 if re.search(r": error:", out) else 0

def module_of(target):
    if not target.endswith(".lean"):
        return target
    return os.path.relpath(os.path.abspath(target), ROOT)[:-5].replace("/", ".")

def cold_check(target):
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
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest:
        return selftest()
    if a.daemon:
        return daemon()
    if a.stop:
        if os.path.exists(SOCK):
            try:
                c = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM); c.connect(SOCK)
                c.sendall(b'{"file":"__stop__"}'); c.close()
            except Exception:
                pass
            os.remove(SOCK)
        return 0
    if a.warm:
        ensure_daemon()
        if a.target:
            return warm_check(a.target)
        print("warm"); return 0
    if not a.target:
        ap.error("need a file/module (or a mode flag)")
    return cold_check(a.target) if a.cold else warm_check(a.target)

# ---------------------------------------------------------------- offline self-test

def selftest():
    # error + warning, 0-based -> 1-based, first-line-only
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
    print("leancheck selftest OK")
    return 0

if __name__ == "__main__":
    sys.exit(main() or 0)
