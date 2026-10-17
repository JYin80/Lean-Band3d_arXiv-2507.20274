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
# Closedness of the self-consistent equation `(self_m)` along real-axis limits

The paper identifies `m(E, g)` with the boundary value `m(E + i0_+, g)` (Definition 2.8, `def_flow`) and uses that `μ_N` has a
continuous density `ρ_N` (Section 2.2, after (2.31) `eq:Psi3D`).  The two facts rest on the self-consistent equation
`(self_m)` (Eq. (2.32)) of the block Anderson model, `m = L^{-d} Σ_i (v_i - z - m)⁻¹` with `Im m > 0`, whose spectral form
holds for `Im z ≥ 0` (`BAMB_trace_eq_sum`).

* `BASelf_of_tendsto`: `(self_m)` is closed along `z_k → z`, `m_k → m` with `Im z_k ≥ 0`, `Im m > 0`.  The statement holds at
  every `d`; no dimension enters the argument.
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

/-! ## 1. The spectral form of `(self_m)` -/

/-- `(self_m)` at `Im z ≥ 0` in spectral form (`BAMB_trace_eq_sum`). -/
private theorem Boundary_self_iff (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ) (hz : 0 ≤ z.im) :
    BASelf d L g z m ↔
      0 < m.im ∧ m = (((L ^ d : ℕ) : ℂ))⁻¹ * ∑ i, ((BAspec d L g i : ℂ) - (z + m))⁻¹ := by
  unfold BASelf
  refine and_congr_right fun hm => ?_
  have hzm : (z + m).im ≠ 0 := by
    rw [Complex.add_im]; linarith
  rw [BAMB_trace_eq_sum d L g z m hzm]

/-! ## 2. Closedness of `(self_m)` -/

/-- **Closedness of `(self_m)`**: if `z_k → z`, `m_k → m`, `Im z_k ≥ 0`, `(self_m)` holds at `(z_k, m_k)` and
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

end RBM.BA
