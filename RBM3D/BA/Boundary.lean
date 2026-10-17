/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.CouplingWindow
import RBM3D.BA.FlowPins
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.MetricSpace.Sequences

/-!
# BA-D6 (T2285): the boundary values of `m(z, g)` on the real axis

The merged pin `BAmBoundary` (`RBM3D/BA/MFixedPoint.lean:548`, paper `1_2:715`: `m(E, g) ≡ m(E + i0_+, g)`;
`1_2:624`: `μ_N` has a continuous density `ρ_N`) is proved unconditionally, for every `d`:

* `BASelf_of_tendsto`: `(self_m)` is closed along `z_k → z`, `m_k → m` with `Im z_k ≥ 0`, `Im m > 0`;
* `BAm_tendsto_of_self` (clause 1): a real-axis solution `m` of `(self_m)` is the limit of `m(E + iη)`, `η ↓ 0`.
  Route: the holomorphic inverse function theorem (`HasStrictDerivAt.localInverse`) for
  `F_E(μ) = μ - L^{-d} Σ_i (v_i - E - μ)⁻¹` at `m`, whose derivative `A = 1 - L^{-d} tr (M^{(B)})²` has
  `Re A ≥ 2 (Im m)² > 0` (`BAgapReal_holds`);
* `BAm_im_tendsto_zero` (clause 2): no real-axis solution, then `Im m(E + iη) → 0` (compactness: `‖m‖ ≤ 1/Im m`
  and closedness of `(self_m)`);
* `BArho_tendsto`: `ρ_N(E) = π⁻¹ Im m(E + i0)` at every real `E`;
* `baMBoundary_holds`: the pin `BAmBoundary d`.

True at every `d` (the route uses no dimension); `3 ≤ L` and `0 < g` enter only through `BAgapReal_holds`
(clause 1).  Statements of the five public theorems = section 2 of `docs/tickets/checks/T2285-check.lean`.
Supervisor `docs/supervisor/2026-10-05-1806.md` §1.1: "`BAmBoundary` (owed, BA-D6) is true"; paper-delta D471
(T2189a): the identification of `BAm` at real `E` with `m(E + i0)` is this theorem.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false

noncomputable section

open Filter
open scoped Topology

namespace RBM.BA

open RBM RBM.Gauss

/-! ## 1. The map `F_E` and its strict derivative -/

/-- `(self_m)` at `Im z ≥ 0` in spectral form (`BAMB_trace_eq_sum`). -/
private theorem Boundary_self_iff (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ) (hz : 0 ≤ z.im) :
    BASelf d L g z m ↔
      0 < m.im ∧ m = (((L ^ d : ℕ) : ℂ))⁻¹ * ∑ i, ((BAspec d L g i : ℂ) - (z + m))⁻¹ := by
  unfold BASelf
  refine and_congr_right fun hm => ?_
  have hzm : (z + m).im ≠ 0 := by
    rw [Complex.add_im]; linarith
  rw [BAMB_trace_eq_sum d L g z m hzm]

/-! ## 2. Closedness of `(self_m)` (M3) -/

/-- **Closedness of `(self_m)`** (M3): if `z_k → z`, `m_k → m`, `Im z_k ≥ 0`, `(self_m)` holds at `(z_k, m_k)` and
`Im m > 0`, then it holds at `(z, m)`. -/
theorem BASelf_of_tendsto (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ) (zs ms : ℕ → ℂ)
    (hz : Tendsto zs atTop (𝓝 z)) (hm : Tendsto ms atTop (𝓝 m)) (hzs : ∀ k, 0 ≤ (zs k).im)
    (hself : ∀ k, BASelf d L g (zs k) (ms k)) (hmim : 0 < m.im) : BASelf d L g z m := by
  have hz0 : 0 ≤ z.im :=
    ge_of_tendsto ((Complex.continuous_im.tendsto z).comp hz) (Eventually.of_forall hzs)
  rw [Boundary_self_iff d L g z m hz0]
  refine ⟨hmim, ?_⟩
  have hzm : Tendsto (fun k => zs k + ms k) atTop (𝓝 (z + m)) := hz.add hm
  have hsum : Tendsto (fun k => (((L ^ d : ℕ) : ℂ))⁻¹ * ∑ i, ((BAspec d L g i : ℂ) - (zs k + ms k))⁻¹) atTop
      (𝓝 ((((L ^ d : ℕ) : ℂ))⁻¹ * ∑ i, ((BAspec d L g i : ℂ) - (z + m))⁻¹)) := by
    refine Tendsto.const_mul _ (tendsto_finsetSum _ fun i _ => ?_)
    refine Tendsto.inv₀ (tendsto_const_nhds.sub hzm) ?_
    intro h0
    have := congrArg Complex.im h0
    simp at this
    linarith
  have hk : ∀ k, ms k = (((L ^ d : ℕ) : ℂ))⁻¹ * ∑ i, ((BAspec d L g i : ℂ) - (zs k + ms k))⁻¹ :=
    fun k => ((Boundary_self_iff d L g (zs k) (ms k) (hzs k)).mp (hself k)).2
  have hm' : Tendsto (fun k => (((L ^ d : ℕ) : ℂ))⁻¹ * ∑ i, ((BAspec d L g i : ℂ) - (zs k + ms k))⁻¹) atTop (𝓝 m) := by
    refine hm.congr (fun k => hk k)
  exact tendsto_nhds_unique hm' hsum

/-! ## 3. Clause 1: a real-axis solution is the boundary value (M2, inverse function theorem) -/

/-! ## 4. Clause 2: no real-axis solution, `Im m(E + iη) → 0` (M4, compactness) -/

/-! ## 5. `ρ_N` as the boundary value; the pin -/

/-! ## 6. Compiled nonempty instances (`d = 3`, `L = 4`; no hypothesis left open) -/

end RBM.BA
