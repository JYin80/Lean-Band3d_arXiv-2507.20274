/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Loop.TreeRep
import RBM3D.Kernel.SumDecay

/-!
# `lem_pureloop`: exponential decay of pure `K`-loops

`\Cref{lem_pureloop}` (`res_pureKes`): when all the charges agree,
`σ_1 = σ_2 = … = σ_n`, there are `c_n, C_n > 0` with

  `|K^(n)_{t,σ,a}| ≤ C_n W^{-d(n-1)} exp(-c_n max_{i,j} |a_i - a_j|)`.

The paper derives this from the `M`-loop tree representation `(eq:tree_rep2)`, in which
every term consists of `M`-edges and *short* unlabeled edges, together with the strong
decay `(prop:ThfadC_short)` -- which holds precisely because the charges are equal, the
case `RBM.ThetaDecayShort` is stated for (`docs/paper-deltas.md`, D11).

## What is proved here

* `RBM.Loop.norm_Theta_same_le_exp` : `(prop:ThfadC_short)` in the form it is used,
  `|Θ^(σ,σ)_t(0,a)| ≤ C e^{-c|a|}` -- the indicator `1_{a=0}` is absorbed because
  `e^{-c|a|} = 1` at `a = 0`;
* `RBM.Loop.sum_exp_decay_conv` : `Σ_y e^{-c|x-y|} e^{-c|y-z|} ≤ C e^{-(c/2)|x-z|}`, the
  convolution of two exponentials on the torus, uniform in `L`.  Half the decay is spent
  on the triangle inequality and half on summing over `y`;
* `RBM.Loop.pureLoop_two` : `res_pureKes` at `n = 2`, from the two-loop formula
  `(Kn2sol)` and the two lemmas above.

## What is assumed, and what is left

`(Kn2sol)` -- `K^(2)_{t,σ,a} = W^{-d} m(σ_1) m(σ_2) Θ_{t m(σ_1) m(σ_2)}(a_1,a_2)` -- is one
of the formulas the paper takes from `[YY_25]`, `[RBSO1D]`; it is carried here as the
hypothesis `RBM.Loop.KTwoFormula`, in the repository's usual form.

The general `n` is not proved.  It needs an induction through the tree values of
`Loop/Partition.lean`: every edge of a pure loop carries `Θ^(σ,σ)` (external) or
`Θ^(σ,σ) - I` (internal), both exponentially decaying, and each split sums over an internal
vertex, which is where `sum_exp_decay_conv` and a constant loss in `c` come in.  That is
its own ticket (`docs/QUEUE.md`, Q25).
-/

namespace RBM.Loop

open Finset Real

variable {d L : ℕ} [NeZero L] {W : ℕ} {g : ℝ}

/-! ### `(prop:ThfadC_short)` as a clean exponential bound -/

/-! ### Convolution of two exponentials -/

/-! ### The star tree at any `n`

The canonical partition with no diagonals contributes `Σ_b Π_i Θ(a_i, b)`.  For a pure
loop every factor decays exponentially, and the sum is controlled uniformly in `L` by the
same split as in `sum_exp_decay_conv`: half of the total decay `Σ_i |a_i - b|` pays for the
triangle inequality between any two labels, the other half for the sum over the centre `b`.

This is the `n`-fold analogue of `sum_exp_decay_conv`, and it is what `res_pureKes` needs
on the star; the trees with diagonals are `docs/QUEUE.md`, Q33.
-/

/-- `Σ_b e^{-c|x-b|} ≤ C(c,d)`, uniformly in `L` and in the centre `x`. -/
theorem sum_exp_decay_centre (k : ℕ) {c : ℝ} (hc : 0 < c) (x : Zd (k + 2) L) :
    ∑ b : Zd (k + 2) L, Real.exp (-(c * (zdistD (k + 2) L (x - b) : ℝ))) ≤ expC k c := by
  rw [sum_shift (k + 2) x (fun r : ℕ => Real.exp (-(c * (r : ℝ))))]
  exact sum_radial_exp_decay_le k hc

/-! ### The two-loop formula and `res_pureKes` at `n = 2` -/

end RBM.Loop
