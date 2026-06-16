#!/usr/bin/env python3
"""leancheck — a warm-REPL / cold Lean checker that speaks plain compiler diagnostics.

The agent never sees JSON or the REPL protocol: it edits a `.lean` file and either
gets the diagnostics for free (via the PostToolUse hook) or runs `leancheck <file>`.

Modes
-----
  leancheck <file.lean>        warm check via a persistent REPL daemon (~ms once that file's
                               import-set has been built)
  leancheck --cold <file|mod>  authoritative `lake build` of the module (the QA gate)
  leancheck --warm [file]      start the daemon; with a file, also pre-build that file's env
  leancheck --stop             kill the daemon
  leancheck --daemon           (internal) the long-lived REPL host
  leancheck --selftest         offline unit tests of the pure logic (no Lean needed)

Output (warm and cold): compiler-style lines
  Oseledets/Foo.lean:84:67: error: <first line of message>
  ✓ no errors            (on success)
  sorries: N             (footer, when relevant)
Exit code: 0 iff no `error:` diagnostics.

Config (env, with defaults)
  LEANCHECK_ROOT     repo root to run `lake` in            [cwd]
  LEANCHECK_REPL     path to the `repl` binary             [autodetect]
  LEANCHECK_KEY      daemon socket key                     [oseledets]
  LEANCHECK_SETOPTS  ';'-separated set_options to prepend  [the mathlibStandardSet set]
  LEANCHECK_MAXENVS  max cached per-import-set envs        [4]

Design notes
  * A file is checked against an environment built from THAT FILE'S OWN `import` lines (never the
    file itself). So a file ALREADY wired into the build does NOT collide with itself ("… has
    already been declared") — which is the whole point: editing an existing module works. Envs are
    cached per import-set, so the edit loop on one file is ~instant after the first (~30-45 s) build.
    Memory is bounded: once more than LEANCHECK_MAXENVS distinct import-sets are seen, the REPL is
    restarted (cached envs rebuild lazily on demand).
  * Warm is an ITERATION accelerator only. `--cold` (lake build) is the source of truth; the cold
    `lake build` + guarded AxiomAudit remain the authoritative gate.
"""
import sys, os, json, socket, subprocess, time, argparse, re, atexit

ROOT = os.environ.get("LEANCHECK_ROOT", os.getcwd())
KEY = os.environ.get("LEANCHECK_KEY", "oseledets")
SOCK = os.path.join(os.environ.get("LEANCHECK_SOCKDIR", "/tmp"), f"leancheck-{KEY}.sock")
DEFAULT_SETOPTS = ("autoImplicit false;linter.mathlibStandardSet true;"
                   "linter.unusedSectionVars true;linter.unusedVariables true;"
                   "linter.style.longFile 1500")
SETOPTS = [f"set_option {o.strip()}" for o in
           os.environ.get("LEANCHECK_SETOPTS", DEFAULT_SETOPTS).split(";") if o.strip()]
MAXENVS = int(os.environ.get("LEANCHECK_MAXENVS", "4"))

# ---------------------------------------------------------------- pure logic (tested)

def build_submission(path):
    """Return (submission_text, kept_linenos, imports). `import` lines are pulled out (they build
    the env, not the body); set_options are prepended to the body for linter parity; kept_linenos[i]
    is the original 1-based file line of the i-th body line, so REPL positions map back exactly."""
    lines = open(path, encoding="utf-8").read().split("\n")
    body, kept, imports = [], [], []
    for n, ln in enumerate(lines, start=1):
        if re.match(r"\s*import\s", ln):
            imports.append(ln.strip())
            continue
        body.append(ln); kept.append(n)
    sub = "\n".join(SETOPTS + body)
    return sub, kept, imports

def map_line(p, kept):
    """Map a 1-based submission line `p` back to the original file line (None for the prepended
    set_option region)."""
    head = len(SETOPTS)
    if p <= head:
        return None
    idx = p - head - 1
    return kept[idx] if 0 <= idx < len(kept) else None

def format_response(resp, relpath, kept):
    """REPL JSON response -> (text, n_errors). Compiler-style, compact. Non-error messages with no
    body line (the prepended set_option/prelude region) are dropped to avoid spurious noise."""
    out, n_err, n_sorry = [], 0, 0
    for m in resp.get("messages", []):
        sev = m.get("severity", "info")
        pos = m.get("pos") or {}
        line = map_line(pos.get("line", 0), kept)
        col = pos.get("column", 0)
        data = (m.get("data") or "").strip().split("\n", 1)[0]
        if line is None and sev != "error":
            continue
        loc = f"{relpath}:{line}:{col}" if line else f"{relpath}:<prelude>"
        if sev == "error":
            n_err += 1
        out.append(f"{loc}: {sev}: {data}")
    for s in resp.get("sorries", []):
        pos = s.get("pos") or {}
        line = map_line(pos.get("line", 0), kept)
        n_sorry += 1
        out.append(f"{relpath}:{line}:{pos.get('column',0)}: warning: uses 'sorry'")
    if n_err == 0 and not out:
        out.append("✓ no errors")
    if n_sorry:
        out.append(f"sorries: {n_sorry}")
    return "\n".join(out), n_err

# ---------------------------------------------------------------- REPL driver (daemon)

def find_repl():
    if os.environ.get("LEANCHECK_REPL"):
        return os.environ["LEANCHECK_REPL"]
    for c in (".lake/packages/REPL/.lake/build/bin/repl",
              "/tmp/lean-repl/.lake/build/bin/repl",
              os.path.expanduser("~/lean-repl/.lake/build/bin/repl")):
        p = c if os.path.isabs(c) else os.path.join(ROOT, c)
        if os.path.exists(p):
            return p
    raise SystemExit("leancheck: repl binary not found; set LEANCHECK_REPL")

class Repl:
    """Hosts a `repl` process and caches one Lean environment per distinct import-set, so each file
    is checked against its own dependencies (never itself)."""
    def __init__(self):
        self._spawn()
    def _spawn(self):
        self.p = subprocess.Popen(["lake", "env", find_repl()], cwd=ROOT,
                                  stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  stderr=subprocess.DEVNULL, text=True, bufsize=1)
        self.envs = {}            # import_key (tuple of import lines) -> REPL env id
    def _send(self, obj):
        self.p.stdin.write(json.dumps(obj) + "\n\n"); self.p.stdin.flush()
    def _recv(self):
        buf = []
        for line in self.p.stdout:           # REPL emits one JSON object then a blank line
            if line.strip() == "" and buf:
                break
            buf.append(line)
        return json.loads("".join(buf)) if buf else {}
    def env_for(self, imports):
        """Return (env_id, import_error_response): the cached/just-built env for this import-set,
        or (None, resp) if importing the dependencies itself errored."""
        key = tuple(imports)
        if key in self.envs:
            return self.envs[key], None
        if len(self.envs) >= MAXENVS:            # bound memory: drop all envs by restarting
            try:
                self.p.kill()
            except Exception:
                pass
            self._spawn()
        self._send({"cmd": "\n".join(imports) if imports else "set_option autoImplicit false"})
        resp = self._recv()
        env_id = resp.get("env")
        if env_id is None:
            return None, resp
        self.envs[key] = env_id
        return env_id, None
    def check(self, body, imports):
        env_id, err = self.env_for(imports)
        if err is not None:
            return err
        self._send({"cmd": body, "env": env_id}); return self._recv()

def daemon():
    repl = Repl()
    if os.path.exists(SOCK):
        os.remove(SOCK)
    srv = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM); srv.bind(SOCK); srv.listen(8)
    atexit.register(lambda: os.path.exists(SOCK) and os.remove(SOCK))
    while True:
        conn, _ = srv.accept()
        try:
            req = json.loads(_recv_all(conn) or "{}")
            path = req["file"]
            rel = os.path.relpath(path, ROOT)
            sub, kept, imports = build_submission(path)
            text, _ = format_response(repl.check(sub, imports), rel, kept)
            conn.sendall(text.encode())
        except Exception as e:
            conn.sendall(f"leancheck daemon error: {e}".encode())
        finally:
            conn.close()

def _recv_all(conn):
    chunks = []
    while True:
        b = conn.recv(65536)
        if not b:
            break
        chunks.append(b)
    return b"".join(chunks).decode()

# ---------------------------------------------------------------- client / CLI

def ensure_daemon():
    if os.path.exists(SOCK):
        return
    subprocess.Popen([sys.executable, os.path.abspath(__file__), "--daemon"],
                     stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                     start_new_session=True, cwd=ROOT)
    for _ in range(2000):                    # wait up to ~200s for the daemon to bind the socket
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
    rel = os.path.relpath(os.path.abspath(target), ROOT)
    return rel[:-5].replace("/", ".")

def cold_check(target):
    mod = module_of(target)
    r = subprocess.run(["lake", "build", mod], cwd=ROOT, capture_output=True, text=True)
    diags = [l for l in (r.stdout + r.stderr).split("\n")
             if re.search(r"error:|warning:", l)]
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
            os.remove(SOCK)
        return 0
    if a.warm:
        ensure_daemon()
        if a.target:                         # pre-build this file's env so its first check is instant
            return warm_check(a.target)
        print("warm"); return 0
    if not a.target:
        ap.error("need a file/module (or a mode flag)")
    return cold_check(a.target) if a.cold else warm_check(a.target)

# ---------------------------------------------------------------- offline self-test

def selftest():
    import tempfile
    global SETOPTS
    SETOPTS = ["set_option autoImplicit false", "set_option linter.mathlibStandardSet true"]
    src = "import Mathlib\nimport Oseledets\n\ntheorem foo : 1 = 1 := rfl\n"
    f = tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False)
    f.write(src); f.close()
    sub, kept, imports = build_submission(f.name)
    assert "import" not in sub, "imports not stripped from body"
    assert imports == ["import Mathlib", "import Oseledets"], imports
    assert sub.startswith("set_option autoImplicit false"), "setopts not prepended"
    # original file: lines 1,2 are imports; body kept lines = [3 (blank), 4 (theorem), 5 (blank)].
    # submission lines: 1,2 = setopts ; 3 = orig 3 ; 4 = orig 4 ...
    assert map_line(4, kept) == 4, f"line map wrong: {map_line(4, kept)}"
    assert map_line(3, kept) == 3
    assert map_line(1, kept) is None, "setopt region should map to None"
    resp = {"messages": [{"severity": "error", "pos": {"line": 4, "column": 20},
                          "data": "type mismatch\n  extra"}], "sorries": []}
    text, nerr = format_response(resp, "T.lean", kept)
    assert nerr == 1 and "T.lean:4:20: error: type mismatch" in text, text
    assert "extra" not in text, "message should be first-line-only"
    # a non-error message in the prepended/prelude region (line maps to None) is dropped
    prelude = {"messages": [{"severity": "warning", "pos": {"line": 1, "column": 0},
                             "data": "The default value of the `longFile` linter is 1500."}]}
    tp, ep = format_response(prelude, "T.lean", kept)
    assert ep == 0 and tp.startswith("✓ no errors"), tp
    resp2 = {"messages": [], "sorries": [{"pos": {"line": 4, "column": 0}}]}
    t2, n2 = format_response(resp2, "T.lean", kept)
    assert n2 == 0 and "uses 'sorry'" in t2 and "sorries: 1" in t2, t2
    resp3 = {"messages": [], "sorries": []}
    t3, n3 = format_response(resp3, "T.lean", kept)
    assert t3.startswith("✓ no errors"), t3
    os.remove(f.name)
    print("selftest OK")
    return 0

if __name__ == "__main__":
    sys.exit(main() or 0)
