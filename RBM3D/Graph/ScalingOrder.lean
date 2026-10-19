/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Data.Int.Basic
import Mathlib.Order.Basic

/-!
# Scaling order of a normal graph

`(eq:ordG)` (7.19) of Definition 7.10 (`def scaling order`) sets, for a normal graph `Γ`,

  `ord(Γ) := n_S(Γ) + 2 (n_W(Γ) - n_V(Γ))`,

with `n_S` the number of solid edges (light-weights included), `n_W` the number of waved
edges and `n_V` the number of internal vertices.  Appendix B's variant `(eq:ordG_BA)` (B.17)
for the block Anderson model replaces internal vertices by internal atoms `n_A`; the formula
is the same, so `RBM.Graph.ord` serves both, with the caller deciding what `nV` counts.

## Contents

* `RBM.Graph.Counters` : the counters of a normal graph from which the scaling order is
  built (solid, waved and distinguished edges, internal vertices and molecules);
* `RBM.Graph.ord` : the scaling order, an integer-valued function of the counters.

The scaling order is tracked along the local expansions of Section 7.1 in the proof of
Lemma 7.17 (`lem:localregular`), Appendix B.2 (`sec:pflocalregular`).
-/

namespace RBM.Graph

/-- The counters of a normal graph that the scaling order is built from.  `nlw` and `ndv`
(distinguished light-weights and distinguished vertices) do not enter `ord`, but the local
expansions track them alongside it. -/
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
