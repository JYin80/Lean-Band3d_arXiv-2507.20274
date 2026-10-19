/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Propagator.Props4
import RBM3D.Gauss.SteinMatrix
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The variance profile of the fine band matrix

`(bandcw0)` and `(eq:variancematrix)`: `H = (H_xy : x, y ∈ Z_L^d)` is a complex Hermitian
Gaussian matrix whose entries are independent up to `H_xy = conj H_yx`, with

  `H_xy ~ N_ℝ(0, S_xy) 1_{x=y} + N_ℂ(0, S_xy) 1_{x≠y}`,  `S_xy = W^{-d} S^(B)_{ab}`

for `x ∈ [a]`, `y ∈ [b]`.  A vertex is therefore a block label together with a position
inside the block, which is `RBM.Gauss.Vtx d L W = Z_L^d × Fin (W^d)`, and the variance
depends only on the two block labels.  This file contains the vertex type, the variance
`RBM.Gauss.svar` of `(eq:variancematrix)`, and its non-negativity and symmetry; the measure on
the independent coordinates is built in `RBM3D.Gauss.FineModel`.

The model is built for fixed `d, L, W, g`: everything is parameterized, nothing is a
sequence.  (The one-dimensional formalization RBM1D bundles `W(N)`, `L(N)` into a structure
and builds one space for the whole sequence.)
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

end RBM.Gauss
