#!/usr/bin/env bash
# Offline unit tests for the leancheck warm-feedback harness — no Lean toolchain, no daemon, no
# network required. Run from anywhere: `.claude/leancheck/run-tests.sh`.
set -euo pipefail
cd "$(dirname "$0")/../.."   # -> repo root
echo "== leancheck.py     (import-strip, exact line remap, response->diagnostics, sorry/clean) =="
python3 .claude/leancheck/leancheck.py --selftest
echo "== post-edit hook   (Oseledets/.lean target detection, warm/cold context, JSON envelope) =="
python3 .claude/hooks/post-edit-leancheck.py --selftest
echo "== stop-coldbuild   (touched-module parsing, block-vs-allow decision + UNVERIFIED banner) =="
python3 .claude/hooks/stop-coldbuild.py --selftest
echo "ALL HARNESS SELFTESTS PASSED"
