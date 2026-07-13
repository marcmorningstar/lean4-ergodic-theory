#!/usr/bin/env python3
"""contextpack — pack a hand-picked file list into one review-ready context.

Given a small manifest (YAML or JSON) that names a few files and gives a one-line
summary of each, this builds a single self-contained blob:

    1. a TABLE OF CONTENTS (the manifest, rendered) at the very top, then
    2. every listed file's full contents, each under a small header.

The result is meant to drop straight into a one-turn LLM call so a review agent
can answer from the material — no tool-calling, no filesystem navigation, no
worrying about what's on disk. Because the file list is hand-picked, you stay in
control of what lands in the context window; `contextpack tokens` tells you how
close you are to the limit before you spend a request.

Subcommands
-----------
  build   Assemble the context and print it (or write it with -o). No API needed.
  tokens  Assemble, then count tokens — exact via the Anthropic API, or a fast
          offline estimate with --offline — and check it against a budget.
  ask     Assemble, then send it to Claude as a one-turn question and stream the
          answer. Two transports (see --transport): the Anthropic API (needs the
          `anthropic` package + ANTHROPIC_API_KEY) or the claude-agent-sdk, which
          drives the local `claude` CLI under a Claude Code subscription (no API
          key). 'auto' picks the API when a key is set, else the SDK.

Manifest format (YAML shown; JSON with the same keys works too)
---------------------------------------------------------------
    title: Emulation theory — seal vs. rate review     # optional
    model: claude-opus-4-8                             # optional; --model overrides it
    system: |                                          # optional review-agent system prompt
      You are reviewing a physics/consciousness theory. Answer only from the
      supplied files and cite file names.
    files:
      - path: knowledge/Consciousness/Consciousness Framework.md
        summary: Entry point — axiom, derived theorems, Lean proof index.
      - path: autonomous-dynamics-limits/AutonomousDynamics/Semiconjugacy/PeriodicOrbitNovelty.lean
        summary: Flow positive-core theorem (no_flow_section_of_novel_periodic_point).
      - "README.md"                                     # bare string = path, no summary

Paths are resolved relative to the manifest's own directory by default
(override with --root). Missing files are reported and abort the run — a review
over a silently-incomplete context is worse than no review.

Examples
--------
    .claude/scripts/contextpack.py build review.yaml -o context.txt
    .claude/scripts/contextpack.py tokens review.yaml --by-file
    .claude/scripts/contextpack.py ask review.yaml -q "Is the seal/rate distinction kept clean?"
    echo "List every place novelty is conflated with forgetting." | .claude/scripts/contextpack.py ask review.yaml
"""

import argparse
import json
import os
import sys
import textwrap
from dataclasses import dataclass, field

# A conservative offline heuristic: English prose is ~4 chars/token, code and
# markup are denser. 3.5 slightly over-counts, which is the safe direction for a
# budget guard. Use `tokens` (without --offline) for the exact count.
CHARS_PER_TOKEN = 3.5
DEFAULT_MODEL = "claude-opus-4-8"
DEFAULT_LIMIT = 900_000  # headroom under the 1M window for the question + reply

DEFAULT_SYSTEM = (
    "You are a meticulous reviewer. You are given a self-contained context: a "
    "table of contents followed by the full text of every listed file. Answer "
    "the question using only this material. Cite the specific file name(s) you "
    "rely on, quote exact lines when precision matters, and state plainly when "
    "the context does not contain enough to answer."
)


def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)


# --------------------------------------------------------------------------- #
# Manifest loading and normalization
# --------------------------------------------------------------------------- #

@dataclass
class Entry:
    path: str
    summary: str = ""
    title: str = ""  # optional display label; the path is still shown


def load_manifest(path):
    try:
        with open(path, "r", encoding="utf-8") as f:
            raw = f.read()
    except OSError as exc:
        raise SystemExit(f"Could not read manifest {path!r}: {exc}")

    ext = os.path.splitext(path)[1].lower()
    if ext == ".json":
        return _load_json(raw, path)

    # Treat everything else as YAML (the common case), falling back to JSON in
    # case a JSON document happens to carry a .yaml name.
    try:
        import yaml
    except ImportError:
        try:
            return json.loads(raw)
        except json.JSONDecodeError:
            raise SystemExit(
                "This manifest looks like YAML but PyYAML is not installed.\n"
                "Install it (pip install pyyaml) or use a .json manifest."
            )
    try:
        return yaml.safe_load(raw)
    except yaml.YAMLError as exc:
        raise SystemExit(f"Could not parse YAML manifest {path!r}: {exc}")


def _load_json(raw, path):
    try:
        return json.loads(raw)
    except json.JSONDecodeError as exc:
        raise SystemExit(f"Could not parse JSON manifest {path!r}: {exc}")


def normalize(manifest, manifest_path, root=None):
    if not isinstance(manifest, dict):
        raise SystemExit("Manifest must be a mapping with a 'files' key.")
    files = manifest.get("files")
    if not files:
        raise SystemExit("Manifest has no non-empty 'files' list.")

    base = root or os.path.dirname(os.path.abspath(manifest_path)) or "."
    entries = []
    for item in files:
        if isinstance(item, str):
            entries.append(Entry(path=item))
        elif isinstance(item, dict):
            path = item.get("path")
            if not path:
                raise SystemExit(f"File entry is missing 'path': {item!r}")
            entries.append(
                Entry(
                    path=path,
                    summary=(item.get("summary") or "").strip(),
                    title=(item.get("title") or "").strip(),
                )
            )
        else:
            raise SystemExit(f"Unrecognized file entry (want str or mapping): {item!r}")
    return base, entries


def resolve(base, path):
    if os.path.isabs(path):
        return path
    return os.path.normpath(os.path.join(base, path))


def read_files(base, entries):
    missing = []
    contents = {}
    for entry in entries:
        full = resolve(base, entry.path)
        if not os.path.isfile(full):
            missing.append(entry.path)
            continue
        with open(full, "r", encoding="utf-8", errors="replace") as f:
            contents[entry.path] = f.read()
    if missing:
        raise SystemExit(
            "These manifest files were not found (relative to {}):\n  {}".format(
                base, "\n  ".join(missing)
            )
        )
    return contents


# --------------------------------------------------------------------------- #
# Context assembly
# --------------------------------------------------------------------------- #

RULE = "=" * 78
THIN = "-" * 78


def build_context(manifest, entries, contents):
    title = (manifest.get("title") or "Untitled context pack").strip()
    n = len(entries)
    out = [RULE, f"CONTEXT PACK — {title}", RULE, ""]
    out.append(
        "This context contains {n} file(s). The TABLE OF CONTENTS below lists each\n"
        "file with a short summary; the full FILE CONTENTS follow, one section per\n"
        "file, each delimited by its own header. Answer using only the material in\n"
        "this context.".format(n=n)
    )
    out.append("")

    out += [THIN, "TABLE OF CONTENTS", THIN]
    for i, entry in enumerate(entries, 1):
        label = entry.title or entry.path
        out.append(f"{i:>3}. {label}")
        if entry.title:
            out.append(f"     path: {entry.path}")
        for line in textwrap.wrap(entry.summary, width=70):
            out.append(f"     {line}")
    out.append("")

    out += [THIN, "FILE CONTENTS", THIN]
    for i, entry in enumerate(entries, 1):
        out.append("")
        out.append(f"########## FILE {i}/{n}: {entry.path} ##########")
        if entry.summary:
            out.append(f"# summary: {entry.summary}")
        out.append("")
        out.append(contents[entry.path].rstrip("\n"))
        out.append("")
        out.append(f"########## END FILE {i}/{n}: {entry.path} ##########")
    out.append("")
    return "\n".join(out)


def estimate_tokens(text):
    return int(len(text) / CHARS_PER_TOKEN)


def warn_budget(tokens, limit, exact):
    kind = "" if exact else " (estimated)"
    if limit and tokens > limit:
        eprint(f"WARNING: context is ~{tokens:,} tokens{kind}, OVER the {limit:,} budget.")
    elif limit:
        pct = 100 * tokens / limit
        eprint(f"Context is ~{tokens:,} tokens{kind} ({pct:.0f}% of the {limit:,} budget).")
    else:
        eprint(f"Context is ~{tokens:,} tokens{kind}.")


# --------------------------------------------------------------------------- #
# Anthropic client (lazy — only imported for API-backed commands)
# --------------------------------------------------------------------------- #

def make_client():
    try:
        import anthropic
    except ImportError:
        raise SystemExit(
            "The `anthropic` package is required for this command.\n"
            "Install it with: pip install anthropic"
        )
    return anthropic.Anthropic()


def count_tokens_api(text, model):
    client = make_client()
    resp = client.messages.count_tokens(
        model=model,
        messages=[{"role": "user", "content": text}],
    )
    return resp.input_tokens


# --------------------------------------------------------------------------- #
# Subcommands
# --------------------------------------------------------------------------- #

def _assemble(args):
    manifest = load_manifest(args.manifest)
    base, entries = normalize(manifest, args.manifest, args.root)
    contents = read_files(base, entries)
    context = build_context(manifest, entries, contents)
    return manifest, entries, contents, context


def cmd_build(args):
    _, _, _, context = _assemble(args)
    if args.output:
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(context)
        eprint(
            f"Wrote {len(context):,} chars (~{estimate_tokens(context):,} tokens est.) "
            f"to {args.output}"
        )
    else:
        sys.stdout.write(context)
    warn_budget(estimate_tokens(context), args.limit, exact=False)


def cmd_tokens(args):
    manifest, entries, contents, context = _assemble(args)
    if args.by_file:
        eprint("Per-file estimate (chars-based):")
        for i, entry in enumerate(entries, 1):
            eprint(f"{i:>3}. ~{estimate_tokens(contents[entry.path]):>8,}  {entry.path}")
        eprint(THIN)
    if args.offline:
        tokens, exact = estimate_tokens(context), False
    else:
        model = args.model or (manifest.get("model") or "").strip() or DEFAULT_MODEL
        tokens, exact = count_tokens_api(context, model), True
    print(tokens)  # machine-readable count on stdout
    warn_budget(tokens, args.limit, exact=exact)


def cmd_ask(args):
    manifest, _, _, context = _assemble(args)

    question = args.question
    if not question and not sys.stdin.isatty():
        question = sys.stdin.read().strip()
    if not question:
        raise SystemExit("Provide a question with -q/--question (or pipe it on stdin).")

    system = args.system or (manifest.get("system") or "").strip() or DEFAULT_SYSTEM
    # Precedence: CLI --model  >  manifest `model:`  >  DEFAULT_MODEL.
    args.model = args.model or (manifest.get("model") or "").strip() or DEFAULT_MODEL

    est = estimate_tokens(context)
    if args.limit and est > args.limit:
        eprint(f"WARNING: context ~{est:,} tokens (est.) exceeds the {args.limit:,} budget.")

    transport = _pick_transport(args.transport)
    eprint(f"[transport] {transport}  [model] {args.model}")
    if transport == "sdk":
        _ask_sdk(args, system, context, question)
    else:
        _ask_anthropic(args, system, context, question)


def _pick_transport(choice):
    """Resolve 'auto' to a concrete transport.

    Prefer the Anthropic API when it is actually usable (package importable AND an
    ANTHROPIC_API_KEY is set); otherwise fall back to the claude-agent-sdk, which
    drives the local `claude` CLI under a Claude Code subscription.
    """
    if choice != "auto":
        return choice
    import importlib.util

    def importable(mod):
        return importlib.util.find_spec(mod) is not None

    if os.environ.get("ANTHROPIC_API_KEY") and importable("anthropic"):
        return "anthropic"
    if importable("claude_agent_sdk"):
        return "sdk"
    return "anthropic"  # nothing else available — let make_client() raise clearly


def _save_answer(args, text):
    """Persist the full answer to --output, if given (in addition to stdout)."""
    out = getattr(args, "output", None)
    if not out:
        return
    with open(out, "w", encoding="utf-8") as f:
        f.write(text.rstrip() + "\n")
    eprint(f"[saved] answer written to {out}")


def _ask_anthropic(args, system, context, question):
    client = make_client()

    # Context first (cache_control makes repeated questions within ~5 min cheap),
    # question last — the "shared prefix, varying suffix" caching pattern.
    user_content = [
        {"type": "text", "text": context, "cache_control": {"type": "ephemeral"}},
        {"type": "text", "text": f"----------\nQUESTION:\n{question}"},
    ]
    kwargs = dict(
        model=args.model,
        max_tokens=args.max_tokens,
        system=system,
        messages=[{"role": "user", "content": user_content}],
    )
    if not args.no_thinking:
        display = "summarized" if args.show_thinking else "omitted"
        kwargs["thinking"] = {"type": "adaptive", "display": display}
        kwargs["output_config"] = {"effort": args.effort}

    parts = []
    with client.messages.stream(**kwargs) as stream:
        for event in stream:
            if event.type == "content_block_start":
                if event.content_block.type == "thinking" and args.show_thinking:
                    eprint("[thinking]")
            elif event.type == "content_block_delta":
                delta = event.delta
                if delta.type == "text_delta":
                    sys.stdout.write(delta.text)
                    sys.stdout.flush()
                    parts.append(delta.text)
                elif delta.type == "thinking_delta" and args.show_thinking:
                    eprint(delta.thinking, end="")
        final = stream.get_final_message()
    print()
    _save_answer(args, "".join(parts))

    usage = final.usage
    eprint(
        "[usage] input={:,} cache_read={:,} cache_write={:,} output={:,}".format(
            usage.input_tokens,
            getattr(usage, "cache_read_input_tokens", 0) or 0,
            getattr(usage, "cache_creation_input_tokens", 0) or 0,
            usage.output_tokens,
        )
    )
    if final.stop_reason == "max_tokens":
        eprint("[note] hit max_tokens — answer may be truncated; raise --max-tokens.")


def _ask_sdk(args, system, context, question):
    """One-turn ask via claude-agent-sdk — drives the local `claude` CLI under a
    Claude Code subscription (no ANTHROPIC_API_KEY needed). Mirrors the Anthropic
    path: same system prompt, same `context + QUESTION` user message, single turn,
    no tools, and project settings NOT loaded (a clean read of only the packed
    files).

    Note: --max-tokens / --no-thinking / --show-thinking are Anthropic-path only;
    on this transport the CLI manages reply length, and reasoning depth follows
    --effort. Run it with a Python that has claude-agent-sdk installed.
    """
    try:
        import anyio
        from claude_agent_sdk import (
            query,
            ClaudeAgentOptions,
            AssistantMessage,
            TextBlock,
            ResultMessage,
        )
    except ImportError:
        raise SystemExit(
            "The `claude-agent-sdk` package (plus `anyio`) is required for the SDK "
            "transport.\n  pip install claude-agent-sdk\n"
            "It drives the local `claude` CLI under your Claude Code subscription "
            "(no ANTHROPIC_API_KEY needed)."
        )

    prompt = f"{context}\n----------\nQUESTION:\n{question}"
    options = ClaudeAgentOptions(
        system_prompt=system,
        model=args.model or None,
        effort=args.effort,
        max_turns=1,
        allowed_tools=[],           # pure one-turn read — no tool use
        permission_mode="bypassPermissions",
        setting_sources=[],         # do NOT load project CLAUDE.md / settings
        skills=None,
    )

    parts = []

    async def _run():
        result = None
        async for msg in query(prompt=prompt, options=options):
            if isinstance(msg, AssistantMessage):
                for block in msg.content:
                    if isinstance(block, TextBlock):
                        sys.stdout.write(block.text)
                        sys.stdout.flush()
                        parts.append(block.text)
            elif isinstance(msg, ResultMessage):
                result = msg
        print()
        return result

    result = anyio.run(_run)
    _save_answer(args, "".join(parts))
    if result is not None:
        bits = []
        usage = getattr(result, "usage", None)
        if usage is not None:
            bits.append(f"usage={usage}")
        cost = getattr(result, "total_cost_usd", None)
        if cost is not None:
            bits.append(f"cost_usd={cost}")
        if bits:
            eprint("[usage] " + "  ".join(bits))


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #

def build_parser():
    parser = argparse.ArgumentParser(
        prog="contextpack",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    sub = parser.add_subparsers(dest="cmd", required=True)

    def add_common(sp):
        sp.add_argument("manifest", help="Path to the YAML/JSON file-list manifest.")
        sp.add_argument(
            "--root",
            help="Base dir for resolving relative paths "
            "(default: the manifest's own directory).",
        )

    b = sub.add_parser("build", help="Assemble and emit the packed context.")
    add_common(b)
    b.add_argument("-o", "--output", help="Write context here instead of stdout.")
    b.add_argument("--limit", type=int, default=DEFAULT_LIMIT,
                   help=f"Token budget for the warning line (default {DEFAULT_LIMIT}).")
    b.set_defaults(func=cmd_build)

    t = sub.add_parser("tokens", help="Count the packed context's tokens.")
    add_common(t)
    t.add_argument("--model", default=None,
                   help=f"Model to count against (default: manifest `model:` or {DEFAULT_MODEL}).")
    t.add_argument("--limit", type=int, default=DEFAULT_LIMIT)
    t.add_argument("--offline", action="store_true",
                   help="Fast char-based estimate instead of the API.")
    t.add_argument("--by-file", action="store_true",
                   help="Also print a per-file estimate on stderr.")
    t.set_defaults(func=cmd_tokens)

    a = sub.add_parser("ask", help="Send the packed context to Claude as one turn.")
    add_common(a)
    a.add_argument("-q", "--question", help="The question (or pipe it on stdin).")
    a.add_argument("--system", help="Override the review-agent system prompt.")
    a.add_argument("-o", "--output",
                   help="Also write the full answer here (streams to stdout regardless). "
                        "Convention: <manifest-stem>.answer.md next to the manifest.")
    a.add_argument("--model", default=None,
                   help=f"Model id (default: manifest `model:` or {DEFAULT_MODEL}); overrides the manifest.")
    a.add_argument("--transport", choices=["auto", "anthropic", "sdk"], default="auto",
                   help="Reach the model via the Anthropic API ('anthropic', needs "
                        "ANTHROPIC_API_KEY) or claude-agent-sdk ('sdk', uses your "
                        "Claude Code subscription). 'auto' (default): API when a key "
                        "is set, else the SDK.")
    a.add_argument("--max-tokens", type=int, default=8000,
                   help="Reply cap for the anthropic transport (default 8000).")
    a.add_argument("--effort", default="high",
                   choices=["low", "medium", "high", "xhigh", "max"])
    a.add_argument("--no-thinking", action="store_true", help="Disable adaptive thinking.")
    a.add_argument("--show-thinking", action="store_true",
                   help="Stream a summary of the model's reasoning to stderr.")
    a.add_argument("--limit", type=int, default=DEFAULT_LIMIT)
    a.set_defaults(func=cmd_ask)

    return parser


def main(argv=None):
    try:
        args = build_parser().parse_args(argv)
        args.func(args)
    except BrokenPipeError:
        # A downstream consumer (e.g. `| head`) closed the pipe. Redirect stdout
        # to devnull so Python's flush-on-exit doesn't re-raise, then exit quietly.
        try:
            devnull = os.open(os.devnull, os.O_WRONLY)
            os.dup2(devnull, sys.stdout.fileno())
        except OSError:
            pass
        sys.exit(0)
    except KeyboardInterrupt:
        eprint("\nInterrupted.")
        sys.exit(130)


if __name__ == "__main__":
    main()
