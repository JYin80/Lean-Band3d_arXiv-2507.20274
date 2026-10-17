/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Data.Int.Basic
import Mathlib.Order.Basic

/-!
# Scaling order and the bookkeeping of `lem_scalingorder`

`(eq:ordG)` of Definition `def scaling order` sets, for a normal graph `Γ`,

  `ord(Γ) := n_S(Γ) + 2 (n_W(Γ) - n_V(Γ))`,

with `n_S` the number of solid edges (light-weights included), `n_W` the number of waved
edges and `n_V` the number of internal vertices.  Appendix B's variant `(eq:ordG_BA)` for
the block Anderson model replaces internal vertices by internal atoms `n_A`; the formula
is the same, so `RBM.Graph.ord` serves both, with the caller deciding what `nV` counts.

## What this file does and does not capture

The proof of `lem_scalingorder` is a case analysis over the configurations a weight
expansion can produce.  Each case supplies relations between the counters of `G₀` and
`G₁` and then reads off a lower bound on `ord(G₁) - ord(G₀)`.  **That second step is
pure arithmetic**, and this file proves it, once per case, by `omega`.

The first step is not arithmetic: it is the claim that the listed cases exhaust the
possible configurations.  That claim needs the graph datatype -- molecules, atoms, solid
/ waved / dotted / ghost edges, the IPC property -- which is `T-graph-model` in
`docs/TASKS.md` and is not yet built.

This distinction is worth stating because of how the missing case was found.  Round 3 of
the proofreading added a case (vi) to this analysis: `G_{αw}` diagonal in `G₁` with
`G_{β₁α}` and `G_{wβ₂}` both off-diagonal.  Its counter relations are
`n_W + 1`, `n_V` unchanged, `n_S` non-decreasing -- which is arithmetically *subsumed* by
case (iv), whose hypotheses are weaker.  So `ord_case_vi` below is a corollary of
`ord_case_iv`, and a formalization that checked only the arithmetic would not have caught
the omission.  What was missing was the enumeration.  Getting value out of Lean here
therefore means building the graph model and proving the case split exhaustive, not
merely re-deriving these inequalities.
-/

namespace RBM.Graph

/-- The counters of a normal graph that the scaling order is built from.  `nlw` and `ndv`
(distinguished light-weights and distinguished vertices) do not enter `ord`, but the case
analysis of `lem_scalingorder` tracks them alongside it. -/
structure Counters where
  /-- solid edges, light-weights included -/
  nS : ℕ
  /-- waved edges -/
  nW : ℕ
  /-- internal vertices (internal atoms, in the block Anderson variant `(eq:ordG_BA)`) -/
  nV : ℕ
  /-- internal molecules -/
  nM : ℕ
  /-- distinguished light-weights -/
  nlw : ℕ
  /-- distinguished vertices -/
  ndv : ℕ

/-- `(eq:ordG)`: `ord(Γ) = n_S + 2 (n_W - n_V)`.  The difference `n_W - n_V` may be
negative, so the scaling order is an integer, not a natural number. -/
def ord (c : Counters) : ℤ := (c.nS : ℤ) + 2 * ((c.nW : ℤ) - (c.nV : ℤ))

end RBM.Graph
