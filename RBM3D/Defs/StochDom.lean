/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Defs.Domination
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Two power estimates for `N^{-D}`

Elementary inequalities for powers of `N`, used in the estimates by stochastic domination `≺`
(1.13) `stoch_domination` and by high-probability events (an event holds w.h.p. if its
probability is at least `1 - N^{-D}` for every `D > 0` and `N` large) in
*Delocalization of non-mean-field random matrices in dimensions `d ≥ 3`* (arXiv:2507.20274):

* `eventually_two_mul_rpow_le`: `2 N^{-(D+1)} ≤ N^{-D}` for `N ≥ 2`;
* `rpow_mul_rpow_neg_add`: `N^C N^{-(D+C)} = N^{-D}` for `N ≥ 1`.

The definitions of `≺` and of w.h.p. at the scale `N = (W L)^d` are in `Defs/StochDomAt`;
the deterministic `≺` is in `Defs/Domination`.
-/
namespace RBM

open Filter MeasureTheory

section Arith

/-- `2 N^{-(D+1)} ≤ N^{-D}` for `N ≥ 2`. -/
theorem eventually_two_mul_rpow_le (D : ℝ) :
    ∀ᶠ N : ℕ in atTop, 2 * (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) := by
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  rw [neg_add, Real.rpow_add hN0, Real.rpow_neg_one]
  have h := Real.rpow_nonneg hN0.le (-D)
  calc 2 * ((N : ℝ) ^ (-D) * (N : ℝ)⁻¹) = (N : ℝ) ^ (-D) * (2 / N) := by ring
    _ ≤ (N : ℝ) ^ (-D) * 1 := by
        gcongr; rw [div_le_one hN0]; exact hN2
    _ = _ := mul_one _

/-- `N^C N^{-(D+C)} = N^{-D}`. -/
theorem rpow_mul_rpow_neg_add {N : ℕ} (hN : 1 ≤ N) (C D : ℝ) :
    (N : ℝ) ^ C * (N : ℝ) ^ (-(D + C)) = (N : ℝ) ^ (-D) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← Real.rpow_add hN0]; congr 1; ring

end Arith

end RBM
