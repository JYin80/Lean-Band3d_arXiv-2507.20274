/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/

/-!
# RBM3D

A Lean 4 / Mathlib formalization of the deterministic core of
*Delocalization of non-mean-field random matrices in dimensions `d ≥ 3`*
(arXiv:2507.20274).

See `docs/STATUS.md` for what is formalized, `docs/PLAN.md` for the roadmap,
`docs/TASKS.md` for the work queue, `docs/paper-deltas.md` for the places where a
Lean statement departs from the paper, and `blueprint/` for the dependency graph.

## File layout

* `RBM3D.Defs.Lattice`       — the torus `Z_L^d` and its periodic `ℓ¹` distance `|x|`
* `RBM3D.Defs.Params`        — `ℓ_t` of `(eq:ellt)` and `B_{t,K}` of `(eq_B_param)`
* `RBM3D.Defs.Block`         — the block variance matrix `S^(B)(g)` of `(eq:variancematrix)`
* `RBM3D.Propagator.Basic`   — `M^(σ₁,σ₂)`, `Θ_t` and `Θ̊_t` of `def_Theta`
* `RBM3D.Propagator.Props14` — properties 1–4 of `lem_propTH`
* `RBM3D.Propagator.Interface` — properties 5–8 of `lem_propTH`, as axioms
* `RBM3D.Graph.Defs`         — scaling size and scaling order of `def scalingBA`
* `RBM3D.Graph.Expansions`   — the three expansion lemmas of Appendix B, as axioms
* `RBM3D.Graph.ScalingOrder` — the bookkeeping proved on top of them
* `RBM3D.Graph.Model`        — the case split of `lem_scalingorder`, exhaustive by construction
* `RBM3D.Test.Axioms`        — the axiom audit

## Two structural differences from the sister projects

**`d` is a parameter.**  `RBM1D` fixes `d = 1` and `RBM2D` fixes `d = 2` (with the
index type `ZMod L × ZMod L`).  Here the lattice is `RBM.Zd d L := Fin d → ZMod L`
and the hypothesis `3 ≤ d` is introduced only where it is actually used.  In the
paper that is exactly two places: the borderline lattice sum `(eq:latticesum_d3)`,
where `d = 3` costs a `log L`, and the `(r+1)^(-(d-2)/2)` decay of `T_t`.

**The propagator decay estimates are axioms, not theorems.**  The `d = 2` paper
proves them from scratch in its Section 8.  This paper does not: properties 5–8 of
`lem_propTH` are attributed to `[yang2024Del]` Lemma 3.1 and (E.19) and to
`[DYYY25]` Lemma 2.14, with the details omitted, and Appendix B quotes its three
expansion lemmas from `[yang2024Del]` B.9–B.11.  Under this repository's rule that
the paper being formalized is the only source, they are stated here as named
axioms.  The audit in `RBM3D.Test.Axioms` pins that list down, so no result can
come to depend on a borrowed fact without it showing up.
-/
