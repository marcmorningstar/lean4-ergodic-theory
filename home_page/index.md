---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

# layout: home
usemathjax: true
---

This site hosts the [blueprint]({{ site.url }}/blueprint/) (web, PDF, and dependency graph) of a
**Lean 4 + Mathlib formalization of the Oseledets multiplicative ergodic theorem (MET)**.

Three headline theorems are formalized, sorry-free:

* `ErgodicTheory.oseledets_filtration` — the one-sided MET (filtration form);
* `ErgodicTheory.oseledets_splitting` — the two-sided splitting;
* `ErgodicTheory.oseledets_flow` — the continuous-flow MET.

together with a layer of companion results (the Lyapunov spectrum, exponent sums,
the trace–determinant identity, exterior/wedge growth, the inverse spectrum,
restriction to invariant subbundles, the non-ergodic spectrum, regularity of the
exponents, and singular one-sided bounds).

Useful links:

* [Blueprint]({{ site.url }}/blueprint/)
* [Blueprint as pdf]({{ site.url }}/blueprint.pdf)
* [Dependency graph]({{ site.url }}/blueprint/dep_graph_document.html)
* [GitHub repository](https://github.com/marcmorningstar/lean4-ergodic-theory)
* [Zulip chat for Lean](https://leanprover.zulipchat.com/)
