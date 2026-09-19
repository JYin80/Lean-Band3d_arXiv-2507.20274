/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.Real.Sqrt
import RBM3D.Defs.Lattice

/-!
# The control parameters `ℓ_t` and `B_{t,K}`

`(eq:ellt)`     `ℓ_t   := min (max (g |1-t|^{-1/2}) 1) L`
`(eq_B_param)`  `B_{t,K} := (g² + |1-t|)^{-1} (K+1)^{-(d-2)} + (L^d |1-t|)^{-1}`

`ℓ_t` is the effective range of the propagator and `B_{t,K}` its decay profile; both
appear in essentially every estimate in the paper.

Two deviations from the paper's notation, both recorded in `docs/paper-deltas.md`:

* `|1-t|^{-1/2}` is written `1 / Real.sqrt |1 - t|`, avoiding `rpow`.  At `t = 1` this
  is `1 / 0 = 0` in Lean, so `ellT` is `1` there rather than undefined; every use site
  in the paper has `t < 1`.
* the exponent `d - 2` is natural subtraction.  For `d ≥ 2` it agrees with the paper,
  and `3 ≤ d` is the standing hypothesis of the paper anyway.
-/

namespace RBM

open Real

/-- `ℓ_t` of `(eq:ellt)`: the effective range of the propagator. -/
noncomputable def ellT (L : ℕ) (g t : ℝ) : ℝ :=
  min (max (g / Real.sqrt |1 - t|) 1) L

/-- `B_{t,K}` of `(eq_B_param)`: the decay profile of the propagator. -/
noncomputable def Bparam (d L : ℕ) (g t : ℝ) (K : ℕ) : ℝ :=
  (g ^ 2 + |1 - t|)⁻¹ * (((K : ℝ) + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * |1 - t|)⁻¹

theorem one_le_ellT {L : ℕ} {g t : ℝ} (hL : 1 ≤ (L : ℝ)) : 1 ≤ ellT L g t :=
  le_min (le_max_right _ _) hL

theorem ellT_le_L {L : ℕ} {g t : ℝ} : ellT L g t ≤ (L : ℝ) := min_le_right _ _

theorem ellT_pos {L : ℕ} {g t : ℝ} (hL : 1 ≤ (L : ℝ)) : 0 < ellT L g t :=
  lt_of_lt_of_le zero_lt_one (one_le_ellT hL)

end RBM
