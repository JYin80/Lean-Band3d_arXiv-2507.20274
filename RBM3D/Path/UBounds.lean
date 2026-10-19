/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Path.Kernel
import RBM3D.Propagator.Deriv
import RBM3D.Loop.GLoop

/-!
# The generator of the evolution `𝒰`

The per-slot generator `thetaGenMat` of the evolution `𝒰` (Definition 3.3 `DefTHUST`, (3.12)
`def_Ustz`), as in RBM2D `UBounds`:

* `thetaGenMat d L g ξ u`: the generator `ξ S^{(B)} Θ^{(B)}_{uξ}` of `𝒰`, the `w`-derivative of
  `ukerMat`.

`d` and `g` enter only through `Theta d L g` and `SB d L g`; the lattice is `Zd d L` and the
coupling `g` is an explicit
real parameter (for the model, `g = sz.lam n`).
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Path

open Matrix RBM RBM.Gauss

section Hierarchy

variable (d L : ℕ) [NeZero L] (g : ℝ)

/-- The per-slot generator `ξ S^{(B)} Θ^{(B)}_{uξ}` of `𝒰` (the `w`-derivative of `ukerMat`;
Definition 3.3 `DefTHUST`). -/
def thetaGenMat (ξ : ℂ) (u : ℝ) : Matrix (Zd d L) (Zd d L) ℂ :=
  ξ • (SB d L g * Theta d L g ((u : ℂ) * ξ))

end Hierarchy

end RBM.Path

end
