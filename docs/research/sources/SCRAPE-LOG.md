# Source scrape log

These PDF URLs returned empty from the self-hosted firecrawl (no PDF text extraction).
The mathematics from them is captured in ../digests/ (from HTML sources + search snippets + standard knowledge).
To re-fetch later, try firecrawl:firecrawl-parse on a downloaded PDF, or WebFetch.

## 2026-06-05 — Kingman via the maximal-inequality / Katznelson–Weiss route (M4)

Scraped three authoritative, COMPLETE proofs of Kingman's subadditive ergodic theorem
via the maximal-inequality / truncation route (NOT Steele's greedy covering). All three
extracted successfully (single long lines — no newlines from the PDF, but full text):

- `kingman-katznelson-weiss-1982-original.md` — Katznelson & Weiss, *A simple proof of
  some ergodic theorems*, Israel J. Math. 42(4), 1982, 291–296. THE canonical
  maximal-inequality/truncation proof of Kingman (and Birkhoff). OCR garbled but
  structurally complete: stopping-time `n(x)`, truncation `f_M`, the bound-`n(x)`-by-`N`
  trick, and the two-sided `∫f♭ = L = ∫f♯` squeeze.
- `kingman-avila-bochi-subadditive.md` — Avila & Bochi, *On the subadditive ergodic
  theorem* (2009), cmat.edu.uy/~lessa/tesis/Avila.pdf. The CLEANEST modern exposition.
  States the plan explicitly: `∫f♭ ≥ L ≥ ∫f♯` with `f♭ = liminf fₙ/n`, `f♯ = limsup fₙ/n`,
  `L = infₙ (1/n)∫fₙ`. Lemma 1 (easy/Fatou direction `∫f♭ = L`) is the heart; the hard
  direction `∫f♯ ≤ L` is DEDUCED from Lemma 1 applied to an ADDITIVE cocycle (the
  Birkhoff sum of `-f_k` under `T^k`) — no subadditive maximal inequality needed.
  Truncation `f⁽ᶜ⁾ = f ∨ (-Cn)` handles `L = -∞`.
- `kingman-katznelson-weiss-lalley.md` — Lalley, Kingman lecture notes (U. Chicago),
  galton.uchicago.edu/~lalley/Courses/Graz/Kingman.pdf. Ergodic-case statement; upper
  estimate by Birkhoff (the iterate-`Tᵐ`-not-ergodic subtlety), lower estimate by the
  stopping-time/covering count. Good cross-check on the squeeze and the `γ` infimum.

Plus already-on-disk: `kingman-karlsson-maximal-proof.md` (Karlsson, *A proof of the
subadditive ergodic theorem*, 2014, unige.ch) — Riesz/Derriennic maximal-inequality
route. Gives Derriennic's Lemma 3.4 + Prop 3.5 (`∫_B a(n,·) ≤ β·μ(B)` for
`B = {liminf aₙ/n < β}`), the WLOG-nonpositive reduction `vₙ = aₙ - Sₙa₁`, and the
additive-cocycle base case feeding the squeeze. Closest in spirit to the repo's M1.

## Empty (removed):
- amit-oseledets-seminar-notes.md
- filip-2017-notes-MET.md
- karlsson-margulis-1999-nonpositive-curvature.md
- kelliher-ucr-geometry-lecturenotes.md
- macpherson-bristol-oseledets.md
- psu-zhu-oseledets-notes.md
- steele-1989-kingman-proof.md
- viana-impa-lle-furstenberg-kesten.md
- viana-lectures-lyapunov-exponents.md
- zhu-uchicago-reu2023-met.md
