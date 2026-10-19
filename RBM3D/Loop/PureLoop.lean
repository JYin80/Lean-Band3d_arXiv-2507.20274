/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Loop.TreeRep
import RBM3D.Kernel.SumDecay

/-!
# A lattice sum for `lem_pureloop`

`lem_pureloop` (`res_pureKes`): when all the charges agree, `σ_1 = σ_2 = … = σ_n`, there are
`c_n, C_n > 0` with

  `|K^(n)_{t,σ,a}| ≤ C_n W^{-d(n-1)} exp(-c_n max_{i,j} |a_i - a_j|)`.

The paper derives this from the `M`-loop tree representation `(eq:tree_rep2)`, in which
every term consists of `M`-edges and *short* unlabeled edges, together with the strong
decay `(prop:ThfadC_short)` -- which holds precisely because the charges are equal.

## What is here

* `sum_exp_decay_centre` : `Σ_b e^{-c|x-b|} ≤ C(c,d)`, uniformly in `L` and in the centre `x`.
  It is the lattice sum for the star tree `Σ_b Π_i Θ(a_i, b)` (the canonical partition with no
  diagonals) of a pure loop, whose factors all decay exponentially: half of the total decay
  `Σ_i |a_i - b|` pays for the triangle inequality between any two labels, the other half for the
  sum over the centre `b`.
-/

namespace RBM.Loop

open Finset Real

variable {d L : ℕ} [NeZero L] {W : ℕ} {g : ℝ}

/-- `Σ_b e^{-c|x-b|} ≤ C(c,d)`, uniformly in `L` and in the centre `x`. -/
theorem sum_exp_decay_centre (k : ℕ) {c : ℝ} (hc : 0 < c) (x : Zd (k + 2) L) :
    ∑ b : Zd (k + 2) L, Real.exp (-(c * (zdistD (k + 2) L (x - b) : ℝ))) ≤ expC k c := by
  rw [sum_shift (k + 2) x (fun r : ℕ => Real.exp (-(c * (r : ℝ))))]
  exact sum_radial_exp_decay_le k hc

end RBM.Loop
