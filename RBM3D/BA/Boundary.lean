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

/-- `F_E(μ) = μ - L^{-d} Σ_i (v_i - (E + μ))⁻¹`, `v = BAspec d L g` (`(self_m)` as an equation for `μ = m + iη`). -/
private def Boundary_F (d L : ℕ) [NeZero L] (g E : ℝ) (μ : ℂ) : ℂ :=
  μ - (((L ^ d : ℕ) : ℂ))⁻¹ * ∑ i, ((BAspec d L g i : ℂ) - ((E : ℂ) + μ))⁻¹

/-- `(self_m)` at `Im z ≥ 0` in spectral form (`BAMB_trace_eq_sum`). -/
private theorem Boundary_self_iff (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ) (hz : 0 ≤ z.im) :
    BASelf d L g z m ↔
      0 < m.im ∧ m = (((L ^ d : ℕ) : ℂ))⁻¹ * ∑ i, ((BAspec d L g i : ℂ) - (z + m))⁻¹ := by
  unfold BASelf
  refine and_congr_right fun hm => ?_
  have hzm : (z + m).im ≠ 0 := by
    rw [Complex.add_im]; linarith
  rw [BAMB_trace_eq_sum d L g z m hzm]

/-- (M0): `BASelf (E + iη) m ↔ 0 < Im m ∧ F_E(m + iη) = iη`, `η ≥ 0`. -/
private theorem Boundary_self_iff_F (d L : ℕ) [NeZero L] (g E η : ℝ) (hη : 0 ≤ η) (m : ℂ) :
    BASelf d L g ((E : ℂ) + (η : ℂ) * Complex.I) m ↔
      0 < m.im ∧ Boundary_F d L g E (m + (η : ℂ) * Complex.I) = (η : ℂ) * Complex.I := by
  have hz : 0 ≤ ((E : ℂ) + (η : ℂ) * Complex.I).im := by simpa using hη
  rw [Boundary_self_iff d L g _ m hz]
  refine and_congr_right fun hm => ?_
  unfold Boundary_F
  have hsum : ∑ i, ((BAspec d L g i : ℂ) - ((E : ℂ) + (η : ℂ) * Complex.I + m))⁻¹ =
      ∑ i, ((BAspec d L g i : ℂ) - ((E : ℂ) + (m + (η : ℂ) * Complex.I)))⁻¹ := by
    refine Finset.sum_congr rfl fun i _ => ?_
    ring_nf
  rw [hsum]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-- (M1): the strict derivative of `F_E` at `μ`, `Im μ ≠ 0`:  `1 - L^{-d} Σ_i ((v_i - (E + μ))⁻¹)²`. -/
private theorem Boundary_F_hasStrictDerivAt (d L : ℕ) [NeZero L] (g E : ℝ) (μ : ℂ) (hμ : μ.im ≠ 0) :
    HasStrictDerivAt (Boundary_F d L g E)
      (1 - (((L ^ d : ℕ) : ℂ))⁻¹ * ∑ i, (((BAspec d L g i : ℂ) - ((E : ℂ) + μ))⁻¹) ^ 2) μ := by
  have hw : ∀ i, (BAspec d L g i : ℂ) - ((E : ℂ) + μ) ≠ 0 := by
    intro i h
    have := congrArg Complex.im h
    simp at this
    exact hμ (by linarith)
  have hterm : ∀ i ∈ (Finset.univ : Finset (Zd d L)),
      HasStrictDerivAt (fun y : ℂ => ((BAspec d L g i : ℂ) - ((E : ℂ) + y))⁻¹)
        ((((BAspec d L g i : ℂ) - ((E : ℂ) + μ))⁻¹) ^ 2) μ := by
    intro i _
    have h1 : HasStrictDerivAt (fun y : ℂ => (BAspec d L g i : ℂ) - ((E : ℂ) + y)) (-1) μ := by
      have := ((hasStrictDerivAt_id μ).const_add (E : ℂ)).const_sub (BAspec d L g i : ℂ)
      simpa using this
    have h2 := (hasStrictDerivAt_inv (hw i)).comp μ h1
    have h3 : ((((BAspec d L g i : ℂ) - ((E : ℂ) + μ))⁻¹) ^ 2) =
        -((((BAspec d L g i : ℂ) - ((E : ℂ) + μ)) ^ 2)⁻¹) * -1 := by
      rw [inv_pow]; ring
    rw [h3]
    exact h2
  have hsum := HasStrictDerivAt.fun_sum (u := (Finset.univ : Finset (Zd d L))) hterm
  have hF := (hasStrictDerivAt_id μ).sub (hsum.const_mul ((((L ^ d : ℕ) : ℂ))⁻¹))
  exact hF

/-- (M1): the gap gives `A ≠ 0` at a real-axis solution (uses `3 ≤ L`, `0 < g` through `BAgapReal_holds`). -/
private theorem Boundary_gap_ne_zero (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) (hg : 0 < g) (E : ℝ) (m : ℂ)
    (hm : BASelf d L g (E : ℂ) m) :
    (1 - (((L ^ d : ℕ) : ℂ))⁻¹ * ∑ i, (((BAspec d L g i : ℂ) - ((E : ℂ) + m))⁻¹) ^ 2) ≠ 0 := by
  have hzm : ((E : ℂ) + m).im ≠ 0 := by simpa using hm.1.ne'
  have hgap := BAgapReal_holds d L hL g hg E m hm
  rw [BAMB_trace_sq_eq_sum d L g (E : ℂ) m hzm] at hgap
  intro h0
  rw [h0] at hgap
  have : 0 < m.im ^ 2 := by have := hm.1; positivity
  simp at hgap
  linarith

/-- (M4): `‖m‖ ≤ 1 / Im m` for a solution of `(self_m)` at `Im z ≥ 0`. -/
private theorem Boundary_norm_le_inv_im (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ) (hz : 0 ≤ z.im)
    (h : BASelf d L g z m) : ‖m‖ ≤ m.im⁻¹ := by
  obtain ⟨hb, hmeq⟩ := h
  have hzm : (z + m).im ≠ 0 := by rw [Complex.add_im]; linarith
  have hNpos : (0 : ℝ) < ((L ^ d : ℕ) : ℝ) := by
    have : 0 < L ^ d := pow_pos (NeZero.pos L) d
    exact_mod_cast this
  have hcard : (Finset.univ : Finset (Zd d L)).card = L ^ d := by rw [Finset.card_univ, BAcard_Zd]
  have hv : ∀ i : Zd d L, ‖((BAspec d L g i : ℂ) - (z + m))⁻¹‖ ≤ m.im⁻¹ := by
    intro i
    rw [norm_inv]
    refine inv_anti₀ hb ?_
    have h1 : |((BAspec d L g i : ℂ) - (z + m)).im| ≤ ‖(BAspec d L g i : ℂ) - (z + m)‖ :=
      Complex.abs_im_le_norm _
    have h2 : ((BAspec d L g i : ℂ) - (z + m)).im = -(z.im + m.im) := by simp
    rw [h2, abs_neg, abs_of_nonneg (by linarith)] at h1
    linarith
  have h1 : m = (((L ^ d : ℕ) : ℂ))⁻¹ * ∑ i, ((BAspec d L g i : ℂ) - (z + m))⁻¹ := by
    rw [← BAMB_trace_eq_sum d L g z m hzm]; exact hmeq
  calc ‖m‖ = ‖(((L ^ d : ℕ) : ℂ))⁻¹ * ∑ i, ((BAspec d L g i : ℂ) - (z + m))⁻¹‖ := congrArg norm h1
    _ = ((L ^ d : ℕ) : ℝ)⁻¹ * ‖∑ i, ((BAspec d L g i : ℂ) - (z + m))⁻¹‖ := by
        rw [norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ ((L ^ d : ℕ) : ℝ)⁻¹ * ∑ i : Zd d L, ‖((BAspec d L g i : ℂ) - (z + m))⁻¹‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ ((L ^ d : ℕ) : ℝ)⁻¹ * ∑ i : Zd d L, m.im⁻¹ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hv i) (by positivity)
    _ = m.im⁻¹ := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        field_simp

/-- `BAm` is `0` when `(self_m)` has no solution (the `dite` default). -/
private theorem Boundary_BAm_of_none (d L : ℕ) [NeZero L] (g : ℝ) (z : ℂ) (h : ¬ ∃ m : ℂ, BASelf d L g z m) :
    BAm d L g z = 0 := by
  unfold BAm
  simp [h]

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

/-- **Clause 1 of `BAmBoundary`** (M2): a real-axis solution `m` of `(self_m)` is the limit of `m(E + iη)` as `η ↓ 0`.
Route: the inverse function theorem for `F_E` at `m`. -/
theorem BAm_tendsto_of_self (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) (hg : 0 < g) (E : ℝ) (m : ℂ)
    (hm : BASelf d L g (E : ℂ) m) :
    Tendsto (fun η : ℝ => BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 m) := by
  set A : ℂ := 1 - (((L ^ d : ℕ) : ℂ))⁻¹ * ∑ i, (((BAspec d L g i : ℂ) - ((E : ℂ) + m))⁻¹) ^ 2 with hA
  have hmim : 0 < m.im := hm.1
  have hF : HasStrictDerivAt (Boundary_F d L g E) A m :=
    Boundary_F_hasStrictDerivAt d L g E m hmim.ne'
  have hA0 : A ≠ 0 := Boundary_gap_ne_zero d L hL g hg E m hm
  -- `F_E(m) = 0`
  have hFm : Boundary_F d L g E m = 0 := by
    have := (Boundary_self_iff_F d L g E 0 le_rfl m).mp (by simpa using hm)
    simpa using this.2
  set G : ℂ → ℂ := HasStrictDerivAt.localInverse (Boundary_F d L g E) A m hF hA0 with hG
  have hGinv : ∀ᶠ y in 𝓝 (0 : ℂ), Boundary_F d L g E (G y) = y := by
    have := hF.eventually_right_inverse hA0
    rwa [hFm] at this
  have hGleft : ∀ᶠ x in 𝓝 m, G (Boundary_F d L g E x) = x := hF.eventually_left_inverse hA0
  have hG0 : G 0 = m := by
    have := hGleft.self_of_nhds
    rwa [hFm] at this
  have hGcont : ContinuousAt G 0 := by
    have := (hF.to_localInverse hA0).hasDerivAt.continuousAt
    rwa [hFm] at this
  -- `y = η i → 0`
  have hy : Tendsto (fun η : ℝ => (η : ℂ) * Complex.I) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    have h1 : Tendsto (fun η : ℝ => (η : ℂ) * Complex.I) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
      have : Continuous (fun η : ℝ => (η : ℂ) * Complex.I) := by fun_prop
      simpa using this.tendsto 0
    exact h1.mono_left nhdsWithin_le_nhds
  have hmη : Tendsto (fun η : ℝ => G ((η : ℂ) * Complex.I) - (η : ℂ) * Complex.I) (𝓝[>] (0 : ℝ)) (𝓝 m) := by
    have h1 : Tendsto (fun η : ℝ => G ((η : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 (G 0)) :=
      hGcont.tendsto.comp hy
    have := h1.sub hy
    rw [hG0, sub_zero] at this
    exact this
  have hev1 : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), Boundary_F d L g E (G ((η : ℂ) * Complex.I)) = (η : ℂ) * Complex.I :=
    hy.eventually hGinv
  have hev2 : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), 0 < (G ((η : ℂ) * Complex.I) - (η : ℂ) * Complex.I).im :=
    (Complex.continuous_im.tendsto m |>.comp hmη).eventually (lt_mem_nhds hmim)
  have hev3 : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), 0 < η := self_mem_nhdsWithin
  refine hmη.congr' ?_
  filter_upwards [hev1, hev2, hev3] with η h1 h2 h3
  have hself : BASelf d L g ((E : ℂ) + (η : ℂ) * Complex.I) (G ((η : ℂ) * Complex.I) - (η : ℂ) * Complex.I) := by
    rw [Boundary_self_iff_F d L g E η h3.le]
    refine ⟨h2, ?_⟩
    rw [sub_add_cancel]
    exact h1
  have hz : 0 < ((E : ℂ) + (η : ℂ) * Complex.I).im := by simpa using h3
  exact BASelf_unique d L g _ _ _ hz.le hself (BAm_self d L g _ hz)

/-! ## 4. Clause 2: no real-axis solution, `Im m(E + iη) → 0` (M4, compactness) -/

/-- **Clause 2 of `BAmBoundary`** (M4): if `(self_m)` has no solution at the real energy `E`, then
`Im m(E + iη) → 0` as `η ↓ 0`.  Compactness (`‖m‖ ≤ 1 / Im m`) and closedness of `(self_m)`. -/
theorem BAm_im_tendsto_zero (d L : ℕ) [NeZero L] (g E : ℝ) (hnone : ¬ ∃ m : ℂ, BASelf d L g (E : ℂ) m) :
    Tendsto (fun η : ℝ => (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun η => lt_of_lt_of_le ha BAm_im_nonneg, fun ε hε => ?_⟩
  by_contra hcon
  have hfreq : ∃ᶠ η : ℝ in 𝓝[>] (0 : ℝ), ε ≤ (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im := by
    have := Filter.not_eventually.mp hcon
    refine this.mono fun η h => ?_
    exact not_lt.mp h
  have hfreq2 : ∃ᶠ η : ℝ in 𝓝[>] (0 : ℝ), 0 < η ∧ ε ≤ (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im := by
    have h3 : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), 0 < η := self_mem_nhdsWithin
    exact (hfreq.and_eventually h3).mono fun η h => ⟨h.2, h.1⟩
  obtain ⟨x, hx, hxp⟩ := Filter.frequently_iff_seq_forall.mp hfreq2
  have hx0 : Tendsto x atTop (𝓝 (0 : ℝ)) := (tendsto_nhdsWithin_iff.mp hx).1
  set ms : ℕ → ℂ := fun n => BAm d L g ((E : ℂ) + (x n : ℂ) * Complex.I) with hms
  have hzim : ∀ n, 0 < ((E : ℂ) + (x n : ℂ) * Complex.I).im := fun n => by simpa using (hxp n).1
  have hself : ∀ n, BASelf d L g ((E : ℂ) + (x n : ℂ) * Complex.I) (ms n) :=
    fun n => BAm_self d L g _ (hzim n)
  have hbd : ∀ n, ms n ∈ Metric.closedBall (0 : ℂ) ε⁻¹ := by
    intro n
    rw [mem_closedBall_zero_iff]
    have h1 := Boundary_norm_le_inv_im d L g _ _ (hzim n).le (hself n)
    exact h1.trans (inv_anti₀ hε (hxp n).2)
  obtain ⟨m, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (Metric.isBounded_closedBall) hbd
  have hmim : 0 < m.im := by
    have h1 : ε ≤ m.im :=
      ge_of_tendsto ((Complex.continuous_im.tendsto m).comp hlim) (Eventually.of_forall fun n => (hxp (φ n)).2)
    linarith
  have hzs : Tendsto (fun n => (E : ℂ) + (x (φ n) : ℂ) * Complex.I) atTop (𝓝 (E : ℂ)) := by
    have h1 : Continuous (fun η : ℝ => (E : ℂ) + (η : ℂ) * Complex.I) := by fun_prop
    have := (h1.tendsto 0).comp (hx0.comp hφ.tendsto_atTop)
    simpa [Function.comp_def] using this
  exact hnone ⟨m, BASelf_of_tendsto d L g (E : ℂ) m _ _ hzs hlim (fun n => (hzim (φ n)).le)
    (fun n => hself (φ n)) hmim⟩

/-! ## 5. `ρ_N` as the boundary value; the pin -/

/-- **`ρ_N(E) = π⁻¹ Im m(E + i0)` at every real `E`** (`1_2:624`, `1_2:715`; the consumer form of `UNDensBARow'`). -/
theorem BArho_tendsto (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) (hg : 0 < g) (E : ℝ) :
    Tendsto (fun η : ℝ => (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im / Real.pi) (𝓝[>] (0 : ℝ))
      (𝓝 (BArho d L g E)) := by
  by_cases hex : ∃ m : ℂ, BASelf d L g (E : ℂ) m
  · obtain ⟨m, hm⟩ := hex
    have h1 := BAm_tendsto_of_self d L hL g hg E m hm
    have h2 : Tendsto (fun η : ℝ => (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im) (𝓝[>] (0 : ℝ)) (𝓝 m.im) :=
      (Complex.continuous_im.tendsto m).comp h1
    have h3 := h2.div_const Real.pi
    have : BArho d L g E = m.im / Real.pi := by
      unfold BArho
      rw [BAm_real_eq_of_self d L g E m hm]
    rwa [this]
  · have h1 := BAm_im_tendsto_zero d L g E hex
    have h3 := h1.div_const Real.pi
    have : BArho d L g E = 0 := by
      unfold BArho
      rw [Boundary_BAm_of_none d L g (E : ℂ) hex]
      simp
    rw [this]
    simpa using h3

/-- **`BAmBoundary`, proved** at every `d` (clause 1: `BAm_tendsto_of_self`; clause 2: `BAm_im_tendsto_zero`). -/
theorem baMBoundary_holds (d : ℕ) : BAmBoundary d := by
  intro L hL g hg E
  have : NeZero L := ⟨by omega⟩
  exact ⟨fun m hm => BAm_tendsto_of_self d L hL g hg E m hm, fun hnone => BAm_im_tendsto_zero d L g E hnone⟩


/-! ## 6. Compiled nonempty instances (`d = 3`, `L = 4`; no hypothesis left open) -/

namespace BoundaryInst

open RBM.BA.CouplingWindowInst

/-- (I1) the pin at `d = 3`. -/
example : BAmBoundary 3 := baMBoundary_holds 3

/-- (I2) clause 1 at the merged flow point `(g, E, m) = (g0P, EP, m0P)` (`flowP_data.2.2`, `g0P_pos`). -/
example : Tendsto (fun η : ℝ => BAm 3 4 g0P ((EP : ℂ) + (η : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 m0P) :=
  BAm_tendsto_of_self 3 4 (by norm_num) g0P g0P_pos EP m0P flowP_data.2.2

/-- The gap point `(g, E) = (10, 63)`: `2 + 2·3·|10| = 62 < 63`, so `(self_m)` has no solution. -/
private theorem Boundary_none_10_63 : ¬ ∃ m : ℂ, BASelf 3 4 10 ((63 : ℝ) : ℂ) m := by
  rintro ⟨m, hm⟩
  exact baSelf_none_of_gt 3 4 10 63 (by norm_num) m hm

/-- (I3) clause 2 at the gap point `(g, E) = (10, 63)`. -/
example : Tendsto (fun η : ℝ => (BAm 3 4 10 (((63 : ℝ) : ℂ) + (η : ℂ) * Complex.I)).im) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  BAm_im_tendsto_zero 3 4 10 63 Boundary_none_10_63

/-- (I4) `ρ_N(E) = π⁻¹ Im m(E + i0)` at the flow point and at the gap point. -/
example : Tendsto (fun η : ℝ => (BAm 3 4 g0P ((EP : ℂ) + (η : ℂ) * Complex.I)).im / Real.pi) (𝓝[>] (0 : ℝ))
    (𝓝 (BArho 3 4 g0P EP)) :=
  BArho_tendsto 3 4 (by norm_num) g0P g0P_pos EP

example : Tendsto (fun η : ℝ => (BAm 3 4 10 (((63 : ℝ) : ℂ) + (η : ℂ) * Complex.I)).im / Real.pi) (𝓝[>] (0 : ℝ))
    (𝓝 (BArho 3 4 10 63)) :=
  BArho_tendsto 3 4 (by norm_num) 10 (by norm_num) 63

/-- (I5) closedness along the constant sequences at `(EP, m0P)`. -/
example : BASelf 3 4 g0P (EP : ℂ) m0P :=
  BASelf_of_tendsto 3 4 g0P (EP : ℂ) m0P (fun _ => (EP : ℂ)) (fun _ => m0P) tendsto_const_nhds tendsto_const_nhds
    (fun _ => by simp) (fun _ => flowP_data.2.2) flowP_data.2.2.1

end BoundaryInst

end RBM.BA
