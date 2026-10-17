/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Defs.Domination
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Stochastic domination `≺` and high-probability events

`(stoch_domination)` of *Delocalization of non-mean-field random matrices in dimensions
`d ≥ 3`* (arXiv:2507.20274), together with the `w.h.p.` conventions of the same notation
paragraph:

* `ξ ≺ ζ`, uniformly in `u ∈ U^{(N)}`: for every `τ > 0` and `D > 0`,
  `P(∪_u {ξ^{(N)}(u) > N^τ ζ^{(N)}(u)}) ≤ N^{-D}` for `N ≥ N₀(τ, D)`.  **The union over `u`
  sits inside the probability**, as in the paper.
* for a complex or matrix-valued family, `A = O_≺(ζ)` means `‖A‖ ≺ ζ`.
* `Ξ` holds **w.h.p.** if `P(Ξ) ≥ 1 - N^{-D}` eventually, for every `D > 0`; `Ω'` holds
  w.h.p. **in** `Ξ` if `P(Ξ \ Ω') ≤ N^{-D}`.

The deterministic convention of the same paragraph is `RBM.DetDom`
(`RBM3D/Defs/Domination.lean`); `StochDom.of_unifDetDom` connects the two.

**Convention (a design choice for the whole stochastic layer).**  The probability space
`(Ω, P)` is fixed and the dependence on `N` is carried by the random variables: a family is
`ξ : ∀ N, U N → Ω → ℝ`, with `U N` the (possibly `N`-dependent) parameter set.  The paper's
`N`-dependent spaces are recovered by taking a product space.  This is the same choice the
sister project `RBM1D` makes, and this file is its `Defs/StochDom.lean` with the docstrings
re-pointed at this paper; the mathematics is dimension-independent.

## Main results

* `StochDom.refl`, `trans`, `add`, `mul`, `const_mul_left`, `const_mul_right`: the closure
  properties; `StochDom.of_unifDetDom`: deterministic domination implies stochastic.
* `StochDom.of_forall_le`: **the union bound** -- a bound for each `u` separately, uniform
  in `u`, gives the uniform statement when `#U(N) ≤ N^C`.
* `HighProb.inter`, `HighProb.biInter`: finitely many, resp. polynomially many, w.h.p.
  events hold simultaneously w.h.p.; `StochDom.highProb`: `ξ ≤ N^τ ζ` holds w.h.p.
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
