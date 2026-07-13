---
name: contextpack
description: Pack a hand-picked set of workspace files into one self-contained context and run a one-turn Claude review over it, using .claude/scripts/contextpack.py. Use when the user wants an outside review, audit, consistency check, or focused question answered over a specific slice of the repo — you select the most relevant files, write a YAML manifest with a one-line summary of each, check the token budget, then trigger the online execution (the `ask` subcommand). The tool builds a table-of-contents-then-full-contents blob so the review agent answers purely from the supplied material — no tool-calling, no filesystem navigation.
allowed-tools: Bash, Read, Write, Edit, Glob, Grep
---

# contextpack

`.claude/scripts/contextpack.py` packs a **hand-picked** file list into a single
self-contained context — a table of contents (each file + a one-line summary)
followed by every file's full contents under its own header — and can send that
blob to Claude as a **one-turn** review question. The review agent answers only
from the supplied material.

This skill is the workflow around that tool: **you pick the files, author the
YAML manifest, check the budget, and trigger the online execution.** The whole
value is that the file list is curated — so be deliberate about what goes in.

The tool's own docstring and `--help` are the source of truth for the manifest
schema and flags; a working manifest lives at
`.claude/scripts/contextpack.example.yaml`. Read those before authoring.

## When to invoke

Use this skill when the user wants a focused answer or review over a **specific
slice** of the repo, e.g.:

- "Get an outside review of whether the blueprint's MET statement matches the Lean theorem."
- "Have a fresh agent check the multifractal chapter for gaps between the prose and the proof."
- "Ask: do the Lean Oseledets hypotheses match the standard statement of the theorem?"

Do **not** use it when:

- The task needs to *search* the repo or *edit* files — that's normal agent work,
  not a packed one-turn read.
- The relevant material is one file the current agent can just read directly.
- The review needs multi-turn back-and-forth — contextpack is one-shot.

## Workflow

1. **Pin down the question.** If the user gave a task ("review X") but not a
   crisp question, phrase the exact one-turn question the review agent will
   answer. It goes in `-q`; make it specific.

2. **Select the files — hand-pick, stay lean.** Find the files that actually
   bear on the question (Glob/Grep/Read to locate and skim, not to dump). Prefer
   the few load-bearing sources over broad coverage; the point of the manifest is
   curation. Order them logically (entry point / principle first, supporting
   detail after).

3. **Write a one-line summary per file.** The summary is what the review agent
   sees in the table of contents before the full text — make each one say what
   the file contributes to *this* question, not a generic description.

4. **Author the manifest.** Write a YAML file (schema in the tool docstring /
   `.claude/scripts/contextpack.example.yaml`):

   ```yaml
   title: <what this review is about>
   system: |
     <optional: the review agent's standing instructions — what to check,
     what to flag, "answer only from the files and cite them">
   files:
     - path: blueprint/src/chapters/met.tex
       summary: <what this file contributes to the question>
     - path: Oseledets/MultiplicativeErgodic.lean
       summary: ...
   ```

   Put the manifest in the **session scratchpad** for a one-off, or a durable
   path if the user wants to keep/reuse it. Use **repo-relative paths** in
   `files:` and run with `--root <repo root>` (see Path resolution below).

5. **Check the budget before spending a request.** The list is hand-picked, but
   verify it fits:

   ```bash
   .claude/scripts/contextpack.py tokens <manifest> --root <repo-root> --by-file --offline
   ```

   `--offline` is a fast estimate (drop it for an exact count via the API). If
   it's over budget — or one file dominates — trim or excerpt before running.

6. **Trigger the online execution.** Run the `ask` subcommand — this is the
   API call:

   ```bash
   .claude/scripts/contextpack.py ask <manifest> --root <repo-root> \
       -q "<the specific review question>"
   ```

   It streams the answer to stdout and prints token usage on stderr. Defaults:
   `claude-opus-4-8`, adaptive thinking, `--effort high`. Add `--show-thinking`
   to see reasoning, `--max-tokens N` for longer answers, `--model` to switch.

   **Transport** (`--transport auto|anthropic|sdk`, default `auto`): the review
   call reaches the model two ways — the **Anthropic API** (`anthropic` package +
   `ANTHROPIC_API_KEY`) or the **claude-agent-sdk**, which drives the local
   `claude` CLI under a Claude Code subscription (no API key). `auto` uses the API
   when a key is set, else the SDK. For the SDK path, run the script with a Python
   that has `claude-agent-sdk` installed (`--show-thinking` / `--max-tokens` are
   Anthropic-only there; reasoning depth follows `--effort`).

7. **Relay the answer.** Report the review agent's answer to the user. Note the
   manifest path so they can re-run or tweak it (repeated `ask` calls within a
   few minutes hit the prompt cache — cheap follow-ups). By default the answer
   only streams to stdout; pass `-o <manifest-stem>.answer.md` (next to the
   manifest) to also persist it to a file.

## Path resolution (the one gotcha)

Manifest paths resolve relative to the **manifest's own directory** by default.
When the manifest lives in the scratchpad but lists repo files, that breaks.
Two clean fixes — use one consistently:

- **Repo-relative paths + `--root <repo root absolute path>`** (recommended).
  The `files:` entries are `Oseledets/...`, `blueprint/...`, etc., and `--root`
  points at the repo root so they resolve regardless of where the manifest sits.
- **Absolute paths in `files:`** — then `--root` is irrelevant.

Missing files abort the run with a clear list — fix the paths and re-run rather
than reviewing an incomplete context.

## If the Anthropic API isn't reachable from here

The `anthropic` transport (and an exact `tokens` count) needs the `anthropic`
package plus `ANTHROPIC_API_KEY` or an `ant auth login` profile. When those are
absent but you're in a Claude Code environment, use the **SDK transport** instead
— it runs on the subscription, no API key:

```bash
# one-time: a venv with the SDK (system pip is often PEP 668-locked)
python3 -m venv cpvenv && ./cpvenv/bin/pip install claude-agent-sdk pyyaml
# then run ask through that Python, forcing the SDK transport
./cpvenv/bin/python .claude/scripts/contextpack.py ask <manifest> --root <repo-root> \
    --transport sdk -q "<the specific review question>"
```

If neither transport is reachable, still do steps 1–5, then `build` the context
to a file and hand it off with the exact `ask` command for the user to run:

```bash
.claude/scripts/contextpack.py build <manifest> --root <repo-root> -o <out.txt>
```

## Quick reference

```bash
# assemble only (no API)
.claude/scripts/contextpack.py build  <manifest> --root <repo-root> -o context.txt
# budget check
.claude/scripts/contextpack.py tokens <manifest> --root <repo-root> --by-file [--offline]
# online execution (one-turn review) — transport auto-selected
.claude/scripts/contextpack.py ask    <manifest> --root <repo-root> -q "<question>"
# ...force the subscription (SDK) transport, via a Python that has the SDK
./cpvenv/bin/python .claude/scripts/contextpack.py ask <manifest> --root <repo-root> \
    --transport sdk -q "<question>"
```

Manifest schema and all flags: `.claude/scripts/contextpack.py --help` and the module
docstring; example: `.claude/scripts/contextpack.example.yaml`.
