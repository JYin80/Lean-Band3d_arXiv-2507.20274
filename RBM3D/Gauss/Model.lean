/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Propagator.Props4
import RBM3D.Gauss.SteinMatrix
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The Gaussian band matrix, as a measure on its independent entries

`(bandcw0)` and `(eq:variancematrix)`: `H = (H_xy : x, y ∈ Z_L^d)` is a complex Hermitian
Gaussian matrix whose entries are independent up to `H_xy = conj H_yx`, with

  `H_xy ~ N_ℝ(0, S_xy) 1_{x=y} + N_ℂ(0, S_xy) 1_{x≠y}`,  `S_xy = W^{-d} S^(B)_{ab}`

for `x ∈ [a]`, `y ∈ [b]`.  A vertex is therefore a block label together with a position
inside the block, which is `RBM.Gauss.Vtx d L W = Z_L^d × Fin (W^d)`, and the variance
depends only on the two block labels.

## The independent coordinates

Hermitian symmetry means the independent real coordinates are indexed by *ordered* pairs
`(x, y)` with a `Bool` selecting real or imaginary part, of which only those with
`vkey x ≤ vkey y` are read: `vkey` is an injection of the (finite) vertex set into `ℕ`,
used only to decide which of `H_xy`, `H_yx` carries the coordinates.  The variance of one
coordinate is `S_xx` on the diagonal (a single real Gaussian) and `S_xy/2` off it (two
independent reals), so that `E|H_xy|² = S_xy` in both cases.

## Fixed parameters, not a sequence

`RBM1D/Gauss/Model.lean` bundles `W(N)`, `L(N)` into a structure and builds **one** space
for the whole sequence, because its asymptotic statements quantify over `N` inside a single
probability space.  Here the model is built for fixed `d, L, W, g`, in the style of the rest
of this project: everything is parameterized, nothing is a sequence.  The coordinate set is
then finite, so the measure is `MeasureTheory.Measure.pi` rather than `Measure.infinitePi`,
and the box-uniqueness lemma available for the resampling step (`docs/QUEUE.md`, Q43b) is
`Measure.pi_eq`.

## Main definitions

* `RBM.Gauss.Vtx`, `RBM.Gauss.svar` : vertices and `(eq:variancematrix)`
* `RBM.Gauss.Coord`, `RBM.Gauss.Omega`, `RBM.Gauss.gvar`, `RBM.Gauss.P` : the independent
  coordinates and their law
* `RBM.Gauss.Hmat` : the matrix itself, and `RBM.Gauss.Hmat_isHermitian`
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable (d L W : ℕ) (g : ℝ)

/-! ### Vertices and the variance profile -/

/-- A vertex of the fine lattice: the block it lies in, and its position inside that block.
The paper writes `x ∈ [a]`; here `x.1 = a`. -/
abbrev Vtx : Type := Zd d L × Fin (W ^ d)

/-- **`(eq:variancematrix)`**: `S_xy = W^{-d} S^(B)_{ab}` for `x ∈ [a]`, `y ∈ [b]`. -/
noncomputable def svar (x y : Vtx d L W) : ℝ := ((W : ℝ) ^ d)⁻¹ * SBR d L g x.1 y.1

theorem svar_nonneg (x y : Vtx d L W) : 0 ≤ svar d L W g x y := by
  refine mul_nonneg (by positivity) ?_
  simpa [SBR] using sbKernelR_nonneg d L g (x.1 - y.1)

variable [NeZero L]

theorem svar_comm (x y : Vtx d L W) : svar d L W g x y = svar d L W g y x := by
  simp only [svar, SBR, Matrix.of_apply]
  rw [show y.1 - x.1 = -(x.1 - y.1) by ring, sbKernelR_neg]

/-! ### The independent coordinates -/

/-! ### The matrix -/

/-! ### Resampling one coordinate leaves the law invariant

This is the one place where independence is used.  Replacing the `c`-th coordinate by an
independent sample of its own law does not change `P`:

  `(P ⊗ γ_c).map (upd c) = P`.

Both sides are probability measures on a finite product, so it is enough to compare them on
measurable boxes (`MeasureTheory.Measure.pi_eq`); the preimage of a box under `upd c` is
again a box, with `univ` in the `c`-th slot. -/

end RBM.Gauss
