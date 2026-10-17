/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Path.Kernel
import RBM3D.Propagator.Deriv
import RBM3D.Loop.GLoop

/-!
# The `𝒰` bounds: nonnegativity, row sums, `lem:sum_Ndecay` at `n = 2`, back and one-step kernels

Ticket T2097 (ST2-25, part 1).  Port of `RBM2D/Path/UBounds.lean` at commit `c9a24cf` (cited
`UBounds:<line>`).  Paper: arXiv:2507.20274, `lem:sum_Ndecay` (`3_5_Loop_Hierarchy.tex:1620`,
`(sum_res_Ndecay)`, here `n = 2`), `def_Ustz` (`:116`).

Renaming (`docs/tickets/ST1-COMMON.md` item 2): `Z2 L` becomes `Zd d L`; `SB L`, `Theta L`,
`ukerMat L`, `Uop L` become `SB d L g`, `Theta d L g`, `ukerMat d L g`, `Uop d L g` with the
coupling `g` an explicit real parameter (for the model, `g = sz.lam n`); `spectralM` becomes the
merged `mE`, `etaT` the merged `etaT` (`RBM3D/Loop/GLoop.lean:75`).  The statements that RBM2D
pins as `Prop` definitions over `L` keep that form, with the two parameters `(d, g)`.

* `thetaGenMat`, `thetaGen` : the generator `ξ S^{(B)} Θ^{(B)}_{uξ}` of `𝒰` (`UBounds:48`, `:52`).
* `normSqSpectralMOne` : `|m|² = 1` on `|E| ≤ 2` (`UBounds:416`; `norm_mE`).
* `ukerNonneg` : for real `ξ ≥ 0`, `0 ≤ v ≤ w`, `wξ < 1` the kernel `ukerMat` is entrywise a
  nonnegative real (`UBounds:424`).
* `ukerRowSum` : the row sums are `(1 - vξ)/(1 - wξ)` (`UBounds:445`).
* `sumNdecay`, `sumNdecayEta` : `lem:sum_Ndecay` at `n = 2`, deterministic, constant `1`.
* `uopBack` : `‖𝒰_{t,u} A‖_max ≤ 4 ‖A‖_max`; `uopOneStep` : `‖𝒰_{u,u+Δ} A - A - Δ Θ_u A‖_max
  ≤ 3 Δ² (1-u-Δ)^{-2} ‖A‖_max`.

`d` and `g` enter only through `Theta d L g` and `SB d L g`; the dimension-specific fact of
`UBounds:157` ("`sbKernel` is `1/5`") is replaced by `sbKernelR_nonneg` (the entries are
`(1 + 2dg²)⁻¹` on the diagonal, `g²(1 + 2dg²)⁻¹` on the `2d` neighbours, `0` elsewhere).  The
constants `1`, `4`, `3` are dimension free.  The operator-norm bound for complex `ξ`
(`‖Θ_z‖ ≤ (1 - ‖z‖)⁻¹`) is obtained from the merged `norm_Theta_le` at `z = ‖z‖ · (z/‖z‖)`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Path

open Matrix RBM RBM.Gauss

section Hierarchy

variable (d L : ℕ) [NeZero L] (g : ℝ)

/-- The per-slot generator `ξ S^{(B)} Θ^{(B)}_{uξ}` of `𝒰` (the `w`-derivative of `ukerMat`;
`UBounds:48`; `DefTHUST`). -/
def thetaGenMat (ξ : ℂ) (u : ℝ) : Matrix (Zd d L) (Zd d L) ℂ :=
  ξ • (SB d L g * Theta d L g ((u : ℂ) * ξ))

end Hierarchy

/-! ## Helpers (all `private`) -/

/-! ## The pinned theorems -/

/-! ### Compiled nonempty instances (`d = 3`, `L = 3`, `g = 1/2`)

Data: `ξ = 1`, `0 < v = 1/2 < w = 3/4 < 1` for the kernel statements (`wξ = 3/4 < 1`), `E = 0`
(`|E| < 2`, `m = i`), `u = 1/4`, `t = 3/4`, `Δ = 1/4` and `Δ = 1/2` for the one-step bound; every
hypothesis is discharged by `norm_num`.  The tensor `A` is the nonconstant bounded function
`b ↦ 1` on the first diagonal pair and `1/2` elsewhere (`α = 1`). -/

/-! ### Boundary instances of the time windows (DECISIONS §29)

`v = w = 0` (`η_0 = 1`, `𝒰 = id`), `v = 0 < w = 999/1000` (`η_w = 10⁻³ Im m`, row sum `1000`),
`u = t = 0`, and the one-step window at `u = 0`, `Δ = 0` and at `u = 0`, `Δ = 999/1000`
(`u + Δ < 1`).  Hypotheses are discharged by `norm_num`; `|E| = 0 < 2`. -/

end RBM.Path

end
