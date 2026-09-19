---
usemathjax: true
---

A Lean 4 / Mathlib formalization of the deterministic core of
*Delocalization of non-mean-field random matrices in dimensions $d \ge 3$*,
[arXiv:2507.20274](https://arxiv.org/abs/2507.20274).

* [Blueprint](https://jyin80.github.io/Lean-Band3d_arXiv-2507.20274/blueprint/) — statements, proofs and their Lean counterparts
* [Dependency graph](https://jyin80.github.io/Lean-Band3d_arXiv-2507.20274/blueprint/dep_graph_document.html) — green nodes are formalized
* [Blueprint as pdf](https://jyin80.github.io/Lean-Band3d_arXiv-2507.20274/blueprint.pdf)
* [API documentation](https://jyin80.github.io/Lean-Band3d_arXiv-2507.20274/docs/)
* [Repository](https://github.com/JYin80/Lean-Band3d_arXiv-2507.20274)

Sister projects:
[Lean-RBM1d](https://jyin80.github.io/Lean-RBM1d_arxiv-2501.01718/) ($d=1$) and
[Lean-RBM2d](https://jyin80.github.io/Lean-RBM2d_arxiv-2503.07606/) ($d=2$).

## Scope

Mathlib has no Itô calculus for matrix-valued Brownian motion, no matrix SDEs and no
Dyson Brownian motion, so the loop hierarchy of Sections 3–7 cannot presently be
formalized. What can be — and what this project targets — is the deterministic
backbone: the propagator $\Theta^{(B)}_t = (1 - t\, M^{(\sigma_1,\sigma_2)} S^{(B)})^{-1}$
on $\mathbb Z_L^d$, the evolution-kernel and $\mathcal K$-loop estimates of Appendix A,
and the scaling-order bookkeeping of Appendix B.

## The axiom boundary

This project departs from its two sister projects in one structural way, and it is
worth stating plainly on the front page.

The $d=2$ paper proves its propagator estimates from scratch in its Section 8, so in
`Lean-RBM2d` those estimates are theorems. The $d \ge 3$ paper does not: properties
5–8 of its propagator lemma are attributed to earlier work (`[yang2024Del]` Lemma 3.1
and (E.19), `[DYYY25]` Lemma 2.14), with the details omitted, and the three graph
expansion lemmas of Appendix B are likewise quoted from `[yang2024Del]` B.9–B.11.

Following this repository's rule that the paper under formalization is the only source,
those results are **axioms** here, each stated verbatim in `RBM3D/Propagator/Interface.lean`
and `RBM3D/Graph/Expansions.lean`. The resulting axiom list is not an embarrassment to
be minimized; it is a precise, machine-checkable record of what this paper borrows from
its predecessors. Everything the paper does prove is proved here.

## Status

The first batch of files is drafted but not yet compiled; see `docs/TASKS.md`.
Once it is green, everything outside the two interface files is kept `sorry`-free and
the axiom set of every result is audited to be exactly `propext`, `Classical.choice`,
`Quot.sound`, plus the named interface axioms it legitimately uses.
