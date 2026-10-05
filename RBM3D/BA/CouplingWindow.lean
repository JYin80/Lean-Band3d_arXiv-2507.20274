/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/

import RBM3D.BA.MFixedPoint
import Mathlib.Topology.MetricSpace.Contracting

/-!
# BA-D8 (T2205 portmap): the deterministic coupling window of the block Anderson flow

Port of the compiled T2205 probe (`RBM3D/Probe/T2205Pins.lean` at `96e4087`, sections 2, 2.1-2.3, 3.2 and the
one-point instances 7.2).  Namespace `RBM.BA`; the one-point instances are in `RBM.BA.CouplingWindowInst`.
Paper: `paper/tex/7_8_light_weight.tex` (`7_8:1796-1808`, `zztE_BA`).

* the stability gap `BAgapReal`: `Re (1 - L^{-d} tr M^2) ≥ 2 (Im m)^2` (spectral form `BAMB_trace_sq_eq_sum`);
* the inverse of `zztE_BA`, `BAzztE_inv` (`BAzztE_inv_core`, `BAzztE_inv_holds`);
* the window `BAmWindow` with `c₁ = min(1/2, κ⁹/(64 d Λ))` and `C = 2d/κ⁴` (one Newton-Kantorovich step `BAwindow_step`, its
  iteration `BAwindow_iter`, `BAwindow_floor`); these constants are not in the paper (D537 = T2205c);
* the window premise `BAWinBulk` (written out with the merged `BAt0`, `BAm`, `BAflowE`, because `BAflowT0`, `BAflowEs`, `BAflowLam0`
  are T2197's names) and `BAWinBulk_of_dom` (the chain domain `BAdom κ` gives the window in the `κ/2`-bulk; D538).

Consumers: BA-S3, BA-V2a/b, BA-V3, BA-M1.  Nothing is registered.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal ComplexInnerProductSpace Topology Kronecker

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.BA

/-! ## 2. The deterministic pins of the coupling window (target 2)

`BAgapReal`, `BAmWindow`, `BAzztE_inv` are the check-file texts (`docs/tickets/checks/T2205-check.lean` section 2) verbatim.
Proved here: `BAgapReal` (from `BAMB_trace_eq_sum`-style spectral form of `M²` and the imaginary part of `(self_m)`),
`BAzztE_inv` (algebra), and `BAWinBulk_of_dom` from `BAmWindow` (section 3).  `BAmWindow` itself: section 2.4. -/

section DetPins

variable (d : ℕ)

/-- **The stability gap on the real axis.**  For a real-axis solution `m` of `(self_m)` at `(g, E)`:
`Re (1 - L^{-d} tr (M^{(B)})²) ≥ 2 (Im m)²`.  (With `w_i = g λ_i - E - m`: `⟨|w|^{-2}⟩ = 1` by `BAward_avg`,
`Re (1 - ⟨w^{-2}⟩) = 2 (Im m)² ⟨|w|^{-4}⟩ ≥ 2 (Im m)²` by Cauchy-Schwarz.)  Not in `MFixedPoint`; proved below
(`BAgapReal_holds`; BA-D8 ports the proof). -/
def BAgapReal : Prop :=
  ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → ∀ (E : ℝ) (m : ℂ),
    haveI : NeZero L := ⟨Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hL)⟩
    BASelf d L g (E : ℂ) m →
      2 * m.im ^ 2 ≤
        (1 - (((L ^ d : ℕ) : ℂ))⁻¹ * (BAMB d L g (E : ℂ) m * BAMB d L g (E : ℂ) m).trace).re

/-- **`m(E, ·)` on the coupling window** (supervisor 1806 §1.5 (b)).  For `g ≤ Λ` and `E` in the κ-bulk at `g`
(`BAReal`), every `g' ∈ [√(1 - c₁) g, g]` has a real-axis solution `m(E, g')` with `Im m(E, g') ≥ κ/2`, and
`|m(E, g') - m(E, g)| ≤ C (g - g')`; `c₁ ∈ (0, 1/2]` and `C` depend on `(d, Λ, κ)` only
(`∂_g m = -L^{-d} tr (M²Ψ) / (1 - L^{-d} tr M²)`, `|L^{-d} tr (M²Ψ)| ≤ 2d`, gap `BAgapReal`). -/
def BAmWindow (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 2 ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hL)⟩
        BAReal d L g κ E m → ∀ g' : ℝ, Real.sqrt (1 - c₁) * g ≤ g' → g' ≤ g →
          BAReal d L g' (κ / 2) E (BAm d L g' (E : ℂ)) ∧ ‖BAm d L g' (E : ℂ) - m‖ ≤ C * (g - g')

/-- **The inverse of `zztE_BA`** (used by supervisor 1806 §1.4): flow data `(τ, E, √τ g)` with a real-axis solution
`m₀` come from the spectral parameter `z' = z_τ(E, √τ g)/√τ` at coupling `g`, with `m(z', g) = √τ m₀`. -/
def BAzztE_inv : Prop :=
  ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → ∀ (τ E : ℝ) (m₀ : ℂ),
    haveI : NeZero L := ⟨Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hL)⟩
    0 < τ → τ < 1 → BASelf d L (Real.sqrt τ * g) (E : ℂ) m₀ →
      BAm d L g (ztOf m₀ E τ / (Real.sqrt τ : ℂ)) = (Real.sqrt τ : ℂ) * m₀ ∧
        BAt0 (ztOf m₀ E τ / (Real.sqrt τ : ℂ)) ((Real.sqrt τ : ℂ) * m₀) = τ ∧
          BAflowE (ztOf m₀ E τ / (Real.sqrt τ : ℂ)) ((Real.sqrt τ : ℂ) * m₀) = E

end DetPins

/-! ### 2.1 `BAgapReal` (proved) -/

/-- Spectral decomposition of `(g Ψ - w)⁻¹` for a Hermitian `Ψ` (copy of the private `MFixedPoint_inv_spectral`,
`RBM3D/BA/MFixedPoint.lean:614`; kept private: `MFixedPoint.lean` is not changed, DECISIONS §57 (1)). -/
private theorem T2205_inv_spectral {n : Type*} [Fintype n] [DecidableEq n]
    {Ψ : Matrix n n ℂ} (hΨ : Ψ.IsHermitian) (g : ℝ) {w : ℂ}
    (hw : ∀ l, ((g * hΨ.eigenvalues l : ℝ) : ℂ) ≠ w) :
    Ring.inverse ((g : ℂ) • Ψ - w • (1 : Matrix n n ℂ)) =
      (hΨ.eigenvectorUnitary : Matrix n n ℂ)
        * diagonal (fun l => (((g * hΨ.eigenvalues l : ℝ) : ℂ) - w)⁻¹)
        * star (hΨ.eigenvectorUnitary : Matrix n n ℂ) := by
  set U : Matrix n n ℂ := (hΨ.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : Ψ = U * diagonal (fun l => (hΨ.eigenvalues l : ℂ)) * star U := by
    conv_lhs => rw [hΨ.spectral_theorem]
    rfl
  have hdiag : diagonal (fun l => ((g * hΨ.eigenvalues l : ℝ) : ℂ) - w)
      = (g : ℂ) • diagonal (fun l => (hΨ.eigenvalues l : ℂ)) - w • (1 : Matrix n n ℂ) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  have hsub : (g : ℂ) • Ψ - w • (1 : Matrix n n ℂ)
      = U * diagonal (fun l => ((g * hΨ.eigenvalues l : ℝ) : ℂ) - w) * star U := by
    have h2 : U * (w • (1 : Matrix n n ℂ)) * star U = w • (1 : Matrix n n ℂ) := by
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUU']
    rw [hdiag, Matrix.mul_sub, Matrix.sub_mul, h2, Matrix.mul_smul, Matrix.smul_mul, ← hspec]
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  apply Matrix.inv_eq_right_inv
  rw [hsub]
  calc U * diagonal (fun l => ((g * hΨ.eigenvalues l : ℝ) : ℂ) - w) * star U
        * (U * diagonal (fun l => (((g * hΨ.eigenvalues l : ℝ) : ℂ) - w)⁻¹) * star U)
      = U * (diagonal (fun l => ((g * hΨ.eigenvalues l : ℝ) : ℂ) - w) * (star U * U)
          * diagonal (fun l => (((g * hΨ.eigenvalues l : ℝ) : ℂ) - w)⁻¹)) * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * 1 * star U := by
        have hd : (fun l => (((g * hΨ.eigenvalues l : ℝ) : ℂ) - w)
              * (((g * hΨ.eigenvalues l : ℝ) : ℂ) - w)⁻¹) = fun _ => (1 : ℂ) :=
          funext fun l => mul_inv_cancel₀ (sub_ne_zero.mpr (hw l))
        rw [hUU, mul_one, diagonal_mul_diagonal, hd, diagonal_one]
    _ = 1 := by rw [mul_one, hUU']

/-- **Spectral form of `M²`** (the public version BA-D8 needs): `tr (M^{(B)})² = Σ_i (v_i - z - m)⁻²`. -/
theorem BAMB_trace_sq_eq_sum (d L : ℕ) [NeZero L] : ∀ (g : ℝ) (z m : ℂ), (z + m).im ≠ 0 →
    (BAMB d L g z m * BAMB d L g z m).trace = ∑ i, (((BAspec d L g i : ℂ) - (z + m))⁻¹) ^ 2 := by
  intro g z m hzm
  have hw : ∀ l, ((g * (PsiB_isHermitian d L).eigenvalues l : ℝ) : ℂ) ≠ z + m := by
    intro l h
    have := congrArg Complex.im h
    simp at this
    exact hzm this.symm
  unfold BAMB Mres
  rw [T2205_inv_spectral (PsiB_isHermitian d L) g hw]
  set U : Matrix (Zd d L) (Zd d L) ℂ := ((PsiB_isHermitian d L).eigenvectorUnitary : Matrix (Zd d L) (Zd d L) ℂ) with hU
  set D := diagonal (fun l => (((g * (PsiB_isHermitian d L).eigenvalues l : ℝ) : ℂ) - (z + m))⁻¹) with hD
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  calc (U * D * star U * (U * D * star U)).trace = (U * (D * (star U * U) * D) * star U).trace := by
        simp only [Matrix.mul_assoc]
    _ = (U * (D * D) * star U).trace := by rw [hUU, Matrix.mul_one]
    _ = (U * ((D * D) * star U)).trace := by rw [Matrix.mul_assoc]
    _ = (((D * D) * star U) * U).trace := by rw [Matrix.trace_mul_comm]
    _ = (D * D * (star U * U)).trace := by rw [Matrix.mul_assoc]
    _ = (D * D).trace := by rw [hUU, Matrix.mul_one]
    _ = _ := by
        rw [hD, diagonal_mul_diagonal, Matrix.trace_diagonal]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [sq]
        rfl

/-- **`BAgapReal`, proved**: the stability gap on the real axis.  With `v_i = (g λ_i - E - m)⁻¹`, `ρ_i = |v_i|²`:
`Im v_i = (Im m) ρ_i`, `Re v_i² = ρ_i - 2 (Im m)² ρ_i²`, `L^{-d} Σ ρ_i = 1` (the imaginary part of `(self_m)`), so
`Re (1 - L^{-d} tr M²) = 2 (Im m)² L^{-d} Σ ρ_i² ≥ 2 (Im m)²` (`Σ (ρ_i - 1)² ≥ 0`). -/
theorem BAgapReal_holds (d : ℕ) : BAgapReal d := by
  intro L hL g hg E m
  have : NeZero L := ⟨by omega⟩
  intro hself
  obtain ⟨hb, hmeq⟩ := hself
  have hzm : ((E : ℂ) + m).im ≠ 0 := by simp; exact hb.ne'
  set N : ℝ := ((L ^ d : ℕ) : ℝ) with hN
  have hNpos : 0 < N := by
    have : 0 < L ^ d := pow_pos (NeZero.pos L) d
    rw [hN]; exact_mod_cast this
  have hc : (((L ^ d : ℕ) : ℂ))⁻¹ = ((N⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv, hN, Complex.ofReal_natCast]
  have hcard : (Finset.univ : Finset (Zd d L)).card = L ^ d := by
    rw [Finset.card_univ, BAcard_Zd]
  set v : Zd d L → ℂ := fun i => ((BAspec d L g i : ℂ) - ((E : ℂ) + m))⁻¹ with hv
  have h1 : (BAMB d L g (E : ℂ) m).trace = ∑ i, v i := BAMB_trace_eq_sum d L g (E : ℂ) m hzm
  have h2 : (BAMB d L g (E : ℂ) m * BAMB d L g (E : ℂ) m).trace = ∑ i, (v i) ^ 2 :=
    BAMB_trace_sq_eq_sum d L g (E : ℂ) m hzm
  set ρ : Zd d L → ℝ := fun i => Complex.normSq (v i) with hρ
  have hρpos : ∀ i, 0 < ρ i := by
    intro i
    simp only [hρ, hv]
    refine Complex.normSq_pos.mpr (inv_ne_zero fun h0 => ?_)
    have := congrArg Complex.im h0
    simp at this
    exact hb.ne' (by linarith)
  have hvim : ∀ i, (v i).im = m.im * ρ i := by
    intro i
    simp only [hρ, hv, Complex.inv_im, Complex.normSq_inv]
    have : ((BAspec d L g i : ℂ) - ((E : ℂ) + m)).im = -m.im := by simp
    rw [this]
    ring
  have hvsq : ∀ i, ((v i) ^ 2).re = ρ i - 2 * (m.im * ρ i) ^ 2 := by
    intro i
    have h3 : ((v i) ^ 2).re = (v i).re * (v i).re - (v i).im * (v i).im := by rw [sq, Complex.mul_re]
    have h4 : ρ i = (v i).re * (v i).re + (v i).im * (v i).im := by
      simp only [hρ, Complex.normSq_apply]
    rw [h3, ← hvim i]
    nlinarith [h4]
  -- the imaginary part of (self_m): Σ ρ_i = N
  have hsum : ∑ i, ρ i = N := by
    have him : m.im = N⁻¹ * ∑ i, m.im * ρ i := by
      have := congrArg Complex.im hmeq
      rw [h1, hc, Complex.im_ofReal_mul, Complex.im_sum] at this
      refine this.trans ?_
      congr 1
      exact Finset.sum_congr rfl fun i _ => hvim i
    rw [← Finset.mul_sum] at him
    have : m.im * (∑ i, ρ i) = m.im * N := by
      calc m.im * (∑ i, ρ i) = N * (N⁻¹ * (m.im * ∑ i, ρ i)) := by field_simp
        _ = N * m.im := by rw [← him]
        _ = m.im * N := by ring
    exact mul_left_cancel₀ hb.ne' this
  -- Σ ρ² ≥ N
  have hsq : N ≤ ∑ i, ρ i ^ 2 := by
    have h5 : 0 ≤ ∑ i, (ρ i - 1) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have h6 : ∑ i, (ρ i - 1) ^ 2 = ∑ i, ρ i ^ 2 - 2 * ∑ i, ρ i + N := by
      simp only [sub_sq, one_pow, mul_one, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum,
        Finset.sum_const, hcard, nsmul_eq_mul, hN]
    linarith
  -- the real part
  rw [h2, hc, Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul, Complex.re_sum]
  have h7 : ∑ i, ((v i) ^ 2).re = N - 2 * m.im ^ 2 * ∑ i, ρ i ^ 2 := by
    calc ∑ i, ((v i) ^ 2).re = ∑ i, (ρ i - 2 * m.im ^ 2 * ρ i ^ 2) :=
          Finset.sum_congr rfl fun i _ => by rw [hvsq i]; ring
      _ = ∑ i, ρ i - 2 * m.im ^ 2 * ∑ i, ρ i ^ 2 := by rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = _ := by rw [hsum]
  rw [h7]
  have h8 : 1 - N⁻¹ * (N - 2 * m.im ^ 2 * ∑ i, ρ i ^ 2) = 2 * m.im ^ 2 * (N⁻¹ * ∑ i, ρ i ^ 2) := by
    field_simp
    ring
  rw [h8]
  have h9 : 1 ≤ N⁻¹ * ∑ i, ρ i ^ 2 := by
    rw [le_inv_mul_iff₀ hNpos]; linarith
  nlinarith [sq_nonneg m.im]


/-! ### 2.2 `BAzztE_inv` (proved) -/

/-- **`BAzztE_inv`, proved** (the core: neither `3 ≤ L` nor `0 < g` is used). -/
theorem BAzztE_inv_core (d L : ℕ) [NeZero L] (g τ E : ℝ) (m₀ : ℂ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hself : BASelf d L (Real.sqrt τ * g) (E : ℂ) m₀) :
    BAm d L g (ztOf m₀ E τ / (Real.sqrt τ : ℂ)) = (Real.sqrt τ : ℂ) * m₀ ∧
      BAt0 (ztOf m₀ E τ / (Real.sqrt τ : ℂ)) ((Real.sqrt τ : ℂ) * m₀) = τ ∧
        BAflowE (ztOf m₀ E τ / (Real.sqrt τ : ℂ)) ((Real.sqrt τ : ℂ) * m₀) = E := by
  obtain ⟨hb, hmeq⟩ := hself
  set s := Real.sqrt τ with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr hτ0
  have hss : s * s = τ := Real.mul_self_sqrt hτ0.le
  have hsc : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hspos.ne'
  have hssC : (s : ℂ) * (s : ℂ) = (τ : ℂ) := by
    rw [← Complex.ofReal_mul, hss]
  set z' : ℂ := ztOf m₀ E τ / (s : ℂ) with hz'
  have hz're : z'.re = (E + (1 - τ) * m₀.re) / s := by
    simp [hz', ztOf, Complex.div_ofReal_re]
  have hz'im : z'.im = (1 - τ) * m₀.im / s := by
    simp [hz', ztOf, Complex.div_ofReal_im]
  have hz'pos : 0 < z'.im := by
    rw [hz'im]
    have : 0 < 1 - τ := by linarith
    positivity
  have hkey : z' + (s : ℂ) * m₀ = ((E : ℂ) + m₀) / (s : ℂ) := by
    simp only [hz', ztOf]
    field_simp
    linear_combination m₀ * hssC
  -- the matrix identity
  set A₀ : Matrix (Zd d L) (Zd d L) ℂ := (((s * g : ℝ) : ℂ)) • PsiB d L - ((E : ℂ) + m₀) • (1 : Matrix (Zd d L) (Zd d L) ℂ) with hA₀
  have hne : ((E : ℂ) + m₀).im ≠ 0 := by simp; exact hb.ne'
  have hA₀det : IsUnit A₀.det := by
    have := isUnit_sub_smul_of_isHermitian (BAPsi_isHermitian d L (s * g)) hne
    rw [Matrix.isUnit_iff_isUnit_det] at this
    exact this
  have hmat : (g : ℂ) • PsiB d L - (z' + (s : ℂ) * m₀) • (1 : Matrix (Zd d L) (Zd d L) ℂ) = ((s : ℂ)⁻¹) • A₀ := by
    rw [hkey, hA₀, smul_sub, smul_smul, smul_smul, Complex.ofReal_mul]
    congr 1
    · congr 1; field_simp
    · congr 1; field_simp
  have hMB : BAMB d L g z' ((s : ℂ) * m₀) = (s : ℂ) • BAMB d L (s * g) (E : ℂ) m₀ := by
    unfold BAMB Mres
    rw [hmat, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse]
    have hinv : Invertible ((s : ℂ)⁻¹) := invertibleOfNonzero (inv_ne_zero hsc)
    rw [Matrix.inv_smul A₀ ((s : ℂ)⁻¹) hA₀det, invOf_eq_inv, inv_inv]
  have hSelf : BASelf d L g z' ((s : ℂ) * m₀) := by
    refine ⟨?_, ?_⟩
    · simp only [Complex.im_ofReal_mul]; exact mul_pos hspos hb
    · rw [hMB, Matrix.trace_smul, smul_eq_mul]
      calc (s : ℂ) * m₀ = (s : ℂ) * ((((L ^ d : ℕ) : ℂ))⁻¹ * (BAMB d L (s * g) (E : ℂ) m₀).trace) := by rw [← hmeq]
        _ = _ := by ring
  have hBAm : BAm d L g z' = (s : ℂ) * m₀ :=
    BASelf_unique d L g z' _ _ hz'pos.le (BAm_spec ⟨_, hSelf⟩) hSelf
  have ht0 : BAt0 z' ((s : ℂ) * m₀) = τ := by
    unfold BAt0
    rw [Complex.im_ofReal_mul, hz'im]
    have h1ms : 0 < 1 - τ := by linarith
    field_simp
    nlinarith [hss]
  refine ⟨hBAm, ht0, ?_⟩
  unfold BAflowE
  rw [ht0, ← hs, hz're, Complex.re_ofReal_mul]
  field_simp
  have hs2 : s ^ 2 = τ := by rw [sq]; exact hss
  linear_combination (-(E + (1 - τ) * m₀.re)) * hs2

/-- **`BAzztE_inv`, proved** (the check-file statement). -/
theorem BAzztE_inv_holds (d : ℕ) : BAzztE_inv d := by
  intro L hL g _ τ E m₀
  have : NeZero L := ⟨by omega⟩
  intro hτ0 hτ1 hself
  exact BAzztE_inv_core d L g τ E m₀ hτ0 hτ1 hself


/-! ### 2.3 `BAmWindow` (proved): a one-step Newton-Kantorovich contraction at the coupling `g` of the solution

The route of the dispatcher's F-d without the implicit function theorem: at `(g, E, m)` with `Im m = b ≥ κ`, the map
`T(μ) = μ - F_{g'}(μ)/A`, `F_{g'}(μ) = μ - L^{-d} Σ_i (g' λ_i - E - μ)⁻¹`, `A = 1 - L^{-d} Σ_i (g λ_i - E - m)⁻²` (so `Re A ≥ 2 b²`:
`BAgapReal`), contracts the closed ball `B(m, r)`, `r = 2 d (g - g') / κ⁴`, into itself when `g - g' ≤ κ⁹/(64 d)`; its fixed point is
`m(E, g')` (`BASelf_unique`), `Im ≥ b - r ≥ κ/2`, `|m(E,g') - m| ≤ r`.  Constants `c₁ = min(1/2, κ⁹/(64 d Λ))`, `C = 2d/κ⁴`. -/

section Window

/-- `0 ≤ Im m(z, g)` (the junk value is `0`). -/
theorem BAm_im_nonneg {d L : ℕ} [NeZero L] {g : ℝ} {z : ℂ} : 0 ≤ (BAm d L g z).im := by
  unfold BAm
  split_ifs with h
  · exact h.choose_spec.1.le
  · simp

/-- **`Im m ≤ 1`** for every solution of `(self_m)` with `Im z ≥ 0` (`|m| ≤ L^{-d} Σ |v_i|` and `|v_i| ≤ 1/Im(z + m)`, so
`Im m · (Im z + Im m) ≤ |m| (Im z + Im m) ≤ 1`). -/
theorem BAself_im_le_one {d L : ℕ} [NeZero L] {g : ℝ} {z m : ℂ} (hz : 0 ≤ z.im) (h : BASelf d L g z m) : m.im ≤ 1 := by
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
    have h1 : |((BAspec d L g i : ℂ) - (z + m)).im| ≤ ‖(BAspec d L g i : ℂ) - (z + m)‖ := Complex.abs_im_le_norm _
    have h2 : ((BAspec d L g i : ℂ) - (z + m)).im = -(z.im + m.im) := by simp
    rw [h2, abs_neg, abs_of_nonneg (by linarith)] at h1
    linarith
  have hnorm : ‖m‖ ≤ m.im⁻¹ := by
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
  have h2 : m.im ≤ ‖m‖ := Complex.im_le_norm m
  have h3 : m.im ≤ m.im⁻¹ := h2.trans hnorm
  rw [le_inv_comm₀ hb (by positivity)] at h3
  have : m.im * m.im ≤ 1 := by
    have := mul_le_mul_of_nonneg_left h3 hb.le
    rwa [mul_inv_cancel₀ hb.ne'] at this
  nlinarith


/-- `|λ_i| ≤ 2d` for the eigenvalues of the adjacency matrix of `Z_L^d` (`L ≥ 3`): the largest entry of an eigenvector, and the `2d`
neighbours (`card_adj`). -/
private theorem abs_eigenvalue_le (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (i : Zd d L) :
    |(PsiB_isHermitian d L).eigenvalues i| ≤ 2 * d := by
  set hΨ := PsiB_isHermitian d L with hΨdef
  set v : Zd d L → ℂ := ⇑(hΨ.eigenvectorBasis i) with hv
  have hmul : (PsiB d L) *ᵥ v = ((hΨ.eigenvalues i : ℝ) : ℂ) • v := by
    have := hΨ.mulVec_eigenvectorBasis i
    rw [this]
    ext j
    simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul, hv]
  -- a coordinate of maximal modulus
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image (Finset.univ : Finset (Zd d L)) (fun j => ‖v j‖) ⟨i, Finset.mem_univ _⟩
  have hnorm1 : ‖hΨ.eigenvectorBasis i‖ = 1 := OrthonormalBasis.norm_eq_one _ _
  have hpos : 0 < ‖v j₀‖ := by
    by_contra hneg
    have hzero : ∀ j, v j = 0 := fun j => norm_eq_zero.mp (le_antisymm ((hj₀ j (Finset.mem_univ _)).trans (not_lt.mp hneg)) (norm_nonneg _))
    have : hΨ.eigenvectorBasis i = 0 := by
      ext j
      exact hzero j
    rw [this] at hnorm1
    simp at hnorm1
  have hentry : ((hΨ.eigenvalues i : ℝ) : ℂ) * v j₀ = ∑ k, PsiB d L j₀ k * v k := by
    have := congrFun hmul j₀
    simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, Complex.real_smul] using this.symm
  have hsum : ‖∑ k, PsiB d L j₀ k * v k‖ ≤ 2 * d * ‖v j₀‖ := by
    calc ‖∑ k, PsiB d L j₀ k * v k‖ ≤ ∑ k, ‖PsiB d L j₀ k * v k‖ := norm_sum_le _ _
      _ ≤ ∑ k, (if Adj d L j₀ k then ‖v j₀‖ else 0) := by
          refine Finset.sum_le_sum fun k _ => ?_
          by_cases hk : Adj d L j₀ k
          · simp only [hk, ite_true, PsiB, Matrix.of_apply, norm_mul, norm_one, one_mul]
            exact hj₀ k (Finset.mem_univ _)
          · simp [hk, PsiB]
      _ = 2 * d * ‖v j₀‖ := by
          rw [← Finset.sum_filter, Finset.sum_const, card_adj d L hL j₀, nsmul_eq_mul]
          push_cast; ring
  have : |(hΨ.eigenvalues i : ℝ)| * ‖v j₀‖ ≤ 2 * d * ‖v j₀‖ := by
    calc |(hΨ.eigenvalues i : ℝ)| * ‖v j₀‖ = ‖((hΨ.eigenvalues i : ℝ) : ℂ) * v j₀‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ = ‖∑ k, PsiB d L j₀ k * v k‖ := by rw [hentry]
      _ ≤ 2 * d * ‖v j₀‖ := hsum
  exact le_of_mul_le_mul_right this hpos

/-- `(self_m)` at a real energy as a fixed-point equation on the spectrum. -/
private theorem BASelf_iff_fixed (d L : ℕ) [NeZero L] (g E : ℝ) (μ : ℂ) :
    BASelf d L g (E : ℂ) μ ↔ 0 < μ.im ∧
      μ = ((L ^ d : ℕ) : ℂ)⁻¹ * ∑ i, (((g * (PsiB_isHermitian d L).eigenvalues i : ℝ) : ℂ) - (E : ℂ) - μ)⁻¹ := by
  rw [BASelf_iff_freeConv d L g (E : ℂ) μ (by simp), BAcard_Zd]
  simp [BAspec]

/-- The scalar estimate of the contraction: `‖a⁻¹ a'⁻¹ - b⁻¹ b⁻¹‖ ≤ 2 θ P³` when the inverses are bounded by `P` and `a, a'` are within `θ` of `b`. -/
private theorem inv_mul_inv_sub_le {P θ : ℝ} (hP : 0 ≤ P) {a a' b : ℂ} (hPa : ‖a⁻¹‖ ≤ P) (hPa' : ‖a'⁻¹‖ ≤ P) (hPb : ‖b⁻¹‖ ≤ P)
    (ha : a ≠ 0) (ha' : a' ≠ 0) (hb : b ≠ 0) (hθ : ‖a - b‖ ≤ θ) (hθ' : ‖a' - b‖ ≤ θ) :
    ‖a⁻¹ * a'⁻¹ - b⁻¹ * b⁻¹‖ ≤ 2 * θ * P ^ 3 := by
  have h1 : a⁻¹ - b⁻¹ = (b - a) * (a⁻¹ * b⁻¹) := by field_simp
  have h1' : a'⁻¹ - b⁻¹ = (b - a') * (a'⁻¹ * b⁻¹) := by field_simp
  have n1 : ‖a⁻¹ - b⁻¹‖ ≤ θ * P ^ 2 := by
    rw [h1, norm_mul, norm_mul, norm_sub_rev]
    calc ‖a - b‖ * (‖a⁻¹‖ * ‖b⁻¹‖) ≤ θ * (P * P) :=
          mul_le_mul hθ (mul_le_mul hPa hPb (norm_nonneg _) hP) (by positivity) ((norm_nonneg _).trans hθ)
      _ = θ * P ^ 2 := by ring
  have n1' : ‖a'⁻¹ - b⁻¹‖ ≤ θ * P ^ 2 := by
    rw [h1', norm_mul, norm_mul, norm_sub_rev]
    calc ‖a' - b‖ * (‖a'⁻¹‖ * ‖b⁻¹‖) ≤ θ * (P * P) :=
          mul_le_mul hθ' (mul_le_mul hPa' hPb (norm_nonneg _) hP) (by positivity) ((norm_nonneg _).trans hθ')
      _ = θ * P ^ 2 := by ring
  have hθ0 : 0 ≤ θ := (norm_nonneg _).trans hθ
  have e : a⁻¹ * a'⁻¹ - b⁻¹ * b⁻¹ = (a⁻¹ - b⁻¹) * a'⁻¹ + b⁻¹ * (a'⁻¹ - b⁻¹) := by ring
  rw [e]
  calc ‖(a⁻¹ - b⁻¹) * a'⁻¹ + b⁻¹ * (a'⁻¹ - b⁻¹)‖ ≤ ‖(a⁻¹ - b⁻¹) * a'⁻¹‖ + ‖b⁻¹ * (a'⁻¹ - b⁻¹)‖ := norm_add_le _ _
    _ ≤ θ * P ^ 2 * P + P * (θ * P ^ 2) := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul n1 hPa' (norm_nonneg _) (by positivity))
          (mul_le_mul hPb n1' (norm_nonneg _) hP)
    _ = 2 * θ * P ^ 3 := by ring

/-- `‖w⁻¹‖ ≤ β⁻¹` when `|Im w| ≥ β > 0`. -/
private theorem norm_inv_le_of_abs_im {w : ℂ} {β : ℝ} (hβ : 0 < β) (h : β ≤ |w.im|) : ‖w⁻¹‖ ≤ β⁻¹ := by
  rw [norm_inv]
  exact inv_anti₀ hβ (h.trans (Complex.abs_im_le_norm w))

/-- **The window, one step** (the core of `BAmWindow`): from a real-axis solution `m` at `(g, E)` with `Im m ≥ κ` to a real-axis solution
`m'` at `(g', E)`, `g - g' ≤ κ⁹/(64 d)`, with `|m' - m| ≤ 2 d (g - g')/κ⁴` and `Im m' ≥ κ/2`. -/
theorem BAwindow_step (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (hd : 1 ≤ d) {g g' E κ : ℝ} (hκ : 0 < κ) (hg : 0 < g)
    {m : ℂ} (hm : BASelf d L g (E : ℂ) m) (hκm : κ ≤ m.im) (hg' : g' ≤ g) (hδ : g - g' ≤ κ ^ 9 / (64 * d)) :
    ∃ m' : ℂ, BASelf d L g' (E : ℂ) m' ∧ ‖m' - m‖ ≤ 2 * d * (g - g') / κ ^ 4 ∧ κ / 2 ≤ m'.im := by
  classical
  set lam : Zd d L → ℝ := fun i => (PsiB_isHermitian d L).eigenvalues i with hlam
  have hlamb : ∀ i, |lam i| ≤ 2 * d := fun i => abs_eigenvalue_le d L hL i
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hNpos : (0 : ℝ) < ((L ^ d : ℕ) : ℝ) := by
    have : 0 < L ^ d := pow_pos (NeZero.pos L) d
    exact_mod_cast this
  set Nc : ℂ := ((L ^ d : ℕ) : ℂ) with hNc
  have hNc0 : Nc ≠ 0 := by rw [hNc]; exact_mod_cast hNpos.ne'
  have hcard : (Finset.univ : Finset (Zd d L)).card = L ^ d := by rw [Finset.card_univ, BAcard_Zd]
  -- the data
  set W : ℝ → ℂ → Zd d L → ℂ := fun h μ i => ((h * lam i : ℝ) : ℂ) - (E : ℂ) - μ with hW
  set Φ : ℝ → ℂ → ℂ := fun h μ => Nc⁻¹ * ∑ i, (W h μ i)⁻¹ with hΦ
  have hfix : m = Φ g m := ((BASelf_iff_fixed d L g E m).mp hm).2
  have hb : 0 < m.im := hm.1
  set b := m.im with hbdef
  have hb1 : b ≤ 1 := BAself_im_le_one (z := (E : ℂ)) (by simp) hm
  have hκ1 : κ ≤ 1 := hκm.trans hb1
  -- the gap `A = 1 - L^{-d} Σ w_i⁻²`, `Re A ≥ 2 b²`
  set S₀ : ℂ := Nc⁻¹ * ∑ i, ((W g m i)⁻¹) ^ 2 with hS₀
  set A : ℂ := 1 - S₀ with hA
  have hAre : 2 * b ^ 2 ≤ A.re := by
    have hzm : ((E : ℂ) + m).im ≠ 0 := by simp; exact hb.ne'
    have h1 := BAgapReal_holds d L hL g hg E m hm
    rw [BAMB_trace_sq_eq_sum d L g (E : ℂ) m hzm] at h1
    have e : ∑ i, (((BAspec d L g i : ℂ) - ((E : ℂ) + m))⁻¹) ^ 2 = ∑ i, ((W g m i)⁻¹) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have hWi : W g m i = (BAspec d L g i : ℂ) - ((E : ℂ) + m) := by
        simp only [hW, hlam, BAspec]; ring
      rw [hWi]
    rw [e] at h1
    exact h1
  have hAnorm : 2 * b ^ 2 ≤ ‖A‖ := hAre.trans (Complex.re_le_norm A)
  have hA0 : A ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hAnorm)
  -- the radius
  set δ := g - g' with hδdef
  have hδ0 : 0 ≤ δ := by linarith
  set r : ℝ := 2 * d * δ / κ ^ 4 with hr
  have hκ4 : 0 < κ ^ 4 := by positivity
  have hrnn : 0 ≤ r := by positivity
  have hr5 : r ≤ κ ^ 5 / 32 := by
    rw [hr, div_le_div_iff₀ hκ4 (by norm_num)]
    have : δ ≤ κ ^ 9 / (64 * d) := hδ
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith [pow_pos hκ 4]
  have hrb : r ≤ b / 2 := by
    have : κ ^ 5 ≤ κ := by
      calc κ ^ 5 ≤ κ ^ 1 := pow_le_pow_of_le_one hκ.le hκ1 (by norm_num)
        _ = κ := pow_one κ
    linarith
  have h2dδ : 2 * d * δ ≤ r := by
    rw [hr, le_div_iff₀ hκ4]
    have : κ ^ 4 ≤ 1 := pow_le_one₀ hκ.le hκ1
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hdpos.le) hδ0]
  set θ : ℝ := 2 * d * δ + r with hθ
  have hθ5 : θ ≤ b ^ 5 / 16 := by
    have : κ ^ 5 ≤ b ^ 5 := pow_le_pow_left₀ hκ.le hκm 5
    linarith
  -- the ball `B = closedBall m r`
  have hball_im : ∀ μ ∈ Metric.closedBall m r, b / 2 ≤ μ.im := by
    intro μ hμ
    have h1 : ‖μ - m‖ ≤ r := by simpa [dist_eq_norm] using hμ
    have h2 : |(μ - m).im| ≤ ‖μ - m‖ := Complex.abs_im_le_norm (μ - m)
    have := (abs_le.mp (h2.trans h1)).1
    rw [Complex.sub_im] at this
    linarith
  have hinv : ∀ (h : ℝ) (μ : ℂ) (β : ℝ), 0 < β → β ≤ μ.im → ∀ i, ‖(W h μ i)⁻¹‖ ≤ β⁻¹ := by
    intro h μ β hβ hμ i
    have him : (W h μ i).im = -μ.im := by simp [hW]
    have : β ≤ |(W h μ i).im| := by rw [him, abs_neg, abs_of_pos (by linarith)]; exact hμ
    exact norm_inv_le_of_abs_im hβ this
  have hWne : ∀ (h : ℝ) (μ : ℂ), 0 < μ.im → ∀ i, W h μ i ≠ 0 := by
    intro h μ hμ i hz
    have : (W h μ i).im = -μ.im := by simp [hW]
    rw [hz] at this; simp at this; linarith
  have hinv2 : ∀ (h : ℝ) (μ : ℂ), b / 2 ≤ μ.im → ∀ i, ‖(W h μ i)⁻¹‖ ≤ 2 / b := by
    intro h μ hμ i
    have := hinv h μ (b / 2) (by positivity) hμ i
    rwa [inv_div] at this
  -- the Newton map
  set T : ℂ → ℂ := fun μ => μ - (μ - Φ g' μ) / A with hT
  have hdiff : ∀ μ μ' : ℂ, 0 < μ.im → 0 < μ'.im →
      T μ - T μ' = (μ - μ') * ((Nc⁻¹ * ∑ i, (W g' μ i)⁻¹ * (W g' μ' i)⁻¹) - S₀) / A := by
    intro μ μ' hμ hμ'
    have hterm : ∀ i, (W g' μ i)⁻¹ - (W g' μ' i)⁻¹ = (μ - μ') * ((W g' μ i)⁻¹ * (W g' μ' i)⁻¹) := by
      intro i
      have h1 := hWne g' μ hμ i
      have h2 := hWne g' μ' hμ' i
      simp only [hW] at h1 h2 ⊢
      field_simp
      ring
    have hΦd : Φ g' μ - Φ g' μ' = (μ - μ') * (Nc⁻¹ * ∑ i, (W g' μ i)⁻¹ * (W g' μ' i)⁻¹) := by
      simp only [hΦ]
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      simp_rw [hterm]
      rw [← Finset.mul_sum]; ring
    have hkey : (μ - Φ g' μ) - (μ' - Φ g' μ') = (μ - μ') - (μ - μ') * (Nc⁻¹ * ∑ i, (W g' μ i)⁻¹ * (W g' μ' i)⁻¹) := by
      rw [← hΦd]; ring
    have e : T μ - T μ' = (μ - μ') - ((μ - Φ g' μ) - (μ' - Φ g' μ')) / A := by simp only [hT]; ring
    rw [e, hkey]
    field_simp
    rw [hA]; ring
  have hS : ∀ μ μ' : ℂ, μ ∈ Metric.closedBall m r → μ' ∈ Metric.closedBall m r →
      ‖(Nc⁻¹ * ∑ i, (W g' μ i)⁻¹ * (W g' μ' i)⁻¹) - S₀‖ ≤ 2 * θ * (2 / b) ^ 3 := by
    intro μ μ' hμ hμ'
    have hμi := hball_im μ hμ
    have hμ'i := hball_im μ' hμ'
    have hμ1 : ‖μ - m‖ ≤ r := by simpa [dist_eq_norm] using hμ
    have hμ'1 : ‖μ' - m‖ ≤ r := by simpa [dist_eq_norm] using hμ'
    have e : (Nc⁻¹ * ∑ i, (W g' μ i)⁻¹ * (W g' μ' i)⁻¹) - S₀ =
        Nc⁻¹ * ∑ i, ((W g' μ i)⁻¹ * (W g' μ' i)⁻¹ - (W g m i)⁻¹ * (W g m i)⁻¹) := by
      simp only [hS₀, sq]; rw [← mul_sub, ← Finset.sum_sub_distrib]
    have hdist : ∀ (μ₁ : ℂ), ‖μ₁ - m‖ ≤ r → ∀ i, ‖W g' μ₁ i - W g m i‖ ≤ θ := by
      intro μ₁ hμ₁ i
      have : W g' μ₁ i - W g m i = (((g' - g) * lam i : ℝ) : ℂ) - (μ₁ - m) := by
        simp only [hW]; push_cast; ring
      rw [this]
      calc ‖(((g' - g) * lam i : ℝ) : ℂ) - (μ₁ - m)‖ ≤ ‖(((g' - g) * lam i : ℝ) : ℂ)‖ + ‖μ₁ - m‖ := norm_sub_le _ _
        _ ≤ δ * (2 * d) + r := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_sub_comm, abs_of_nonneg hδ0]
            exact add_le_add (mul_le_mul_of_nonneg_left (hlamb i) hδ0) hμ₁
        _ = θ := by rw [hθ]; ring
    have hterm : ∀ i, ‖(W g' μ i)⁻¹ * (W g' μ' i)⁻¹ - (W g m i)⁻¹ * (W g m i)⁻¹‖ ≤ 2 * θ * (2 / b) ^ 3 := by
      intro i
      exact inv_mul_inv_sub_le (by positivity) (hinv2 g' μ hμi i) (hinv2 g' μ' hμ'i i)
        (hinv2 g m (by linarith) i) (hWne g' μ (by linarith) i) (hWne g' μ' (by linarith) i) (hWne g m hb i)
        (hdist μ hμ1 i) (hdist μ' hμ'1 i)
    rw [e, norm_mul, norm_inv, Complex.norm_natCast]
    calc ((L ^ d : ℕ) : ℝ)⁻¹ * ‖∑ i, ((W g' μ i)⁻¹ * (W g' μ' i)⁻¹ - (W g m i)⁻¹ * (W g m i)⁻¹)‖
        ≤ ((L ^ d : ℕ) : ℝ)⁻¹ * ∑ i : Zd d L, ‖(W g' μ i)⁻¹ * (W g' μ' i)⁻¹ - (W g m i)⁻¹ * (W g m i)⁻¹‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ ((L ^ d : ℕ) : ℝ)⁻¹ * ∑ i : Zd d L, (2 * θ * (2 / b) ^ 3) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hterm i) (by positivity)
      _ = 2 * θ * (2 / b) ^ 3 := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
          field_simp
  -- the contraction constant
  have hconst : 2 * θ * (2 / b) ^ 3 ≤ b ^ 2 := by
    have : 2 * θ * (2 / b) ^ 3 = 16 * θ / b ^ 3 := by field_simp; ring
    rw [this, div_le_iff₀ (by positivity)]
    nlinarith [hθ5]
  have hcontr : ∀ μ ∈ Metric.closedBall m r, ∀ μ' ∈ Metric.closedBall m r, ‖T μ - T μ'‖ ≤ (1 / 2) * ‖μ - μ'‖ := by
    intro μ hμ μ' hμ'
    have hμi := hball_im μ hμ
    have hμ'i := hball_im μ' hμ'
    rw [hdiff μ μ' (by linarith) (by linarith), norm_div, norm_mul]
    have hS' := hS μ μ' hμ hμ'
    have hAp : 0 < ‖A‖ := norm_pos_iff.mpr hA0
    rw [div_le_iff₀ hAp]
    calc ‖μ - μ'‖ * ‖(Nc⁻¹ * ∑ i, (W g' μ i)⁻¹ * (W g' μ' i)⁻¹) - S₀‖ ≤ ‖μ - μ'‖ * b ^ 2 :=
          mul_le_mul_of_nonneg_left (hS'.trans hconst) (norm_nonneg _)
      _ ≤ ‖μ - μ'‖ * (‖A‖ / 2) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      _ = 1 / 2 * ‖μ - μ'‖ * ‖A‖ := by ring
  -- the center moves by at most `r / 2`
  have hTm : ‖T m - m‖ ≤ r / 2 := by
    have e1 : T m - m = -(m - Φ g' m) / A := by simp only [hT]; ring
    have e2 : m - Φ g' m = Nc⁻¹ * ∑ i, ((W g m i)⁻¹ - (W g' m i)⁻¹) := by
      have e2a : m - Φ g' m = Φ g m - Φ g' m := by rw [← hfix]
      rw [e2a]
      simp only [hΦ]
      rw [← mul_sub, ← Finset.sum_sub_distrib]
    have hterm : ∀ i, ‖(W g m i)⁻¹ - (W g' m i)⁻¹‖ ≤ 2 * d * δ / b ^ 2 := by
      intro i
      have h1 := hWne g m hb i
      have h2 := hWne g' m hb i
      have e : (W g m i)⁻¹ - (W g' m i)⁻¹ = (W g' m i - W g m i) * ((W g m i)⁻¹ * (W g' m i)⁻¹) := by
        field_simp
      have e' : W g' m i - W g m i = (((g' - g) * lam i : ℝ) : ℂ) := by simp only [hW]; push_cast; ring
      rw [e, e', norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_sub_comm, abs_of_nonneg hδ0]
      have i1 := hinv g m b hb le_rfl i
      have i2 := hinv g' m b hb le_rfl i
      calc δ * |lam i| * (‖(W g m i)⁻¹‖ * ‖(W g' m i)⁻¹‖) ≤ δ * (2 * d) * (b⁻¹ * b⁻¹) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hlamb i) hδ0) (mul_le_mul i1 i2 (norm_nonneg _) (by positivity))
              (by positivity) (by positivity)
        _ = 2 * d * δ / b ^ 2 := by field_simp
    have hnorm : ‖m - Φ g' m‖ ≤ 2 * d * δ / b ^ 2 := by
      rw [e2, norm_mul, norm_inv, Complex.norm_natCast]
      calc ((L ^ d : ℕ) : ℝ)⁻¹ * ‖∑ i, ((W g m i)⁻¹ - (W g' m i)⁻¹)‖
          ≤ ((L ^ d : ℕ) : ℝ)⁻¹ * ∑ i : Zd d L, ‖(W g m i)⁻¹ - (W g' m i)⁻¹‖ :=
            mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
        _ ≤ ((L ^ d : ℕ) : ℝ)⁻¹ * ∑ i : Zd d L, (2 * d * δ / b ^ 2) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hterm i) (by positivity)
        _ = 2 * d * δ / b ^ 2 := by
            rw [Finset.sum_const, hcard, nsmul_eq_mul]
            field_simp
    have hAp : 0 < ‖A‖ := norm_pos_iff.mpr hA0
    rw [e1, norm_div, norm_neg, div_le_iff₀ hAp]
    have hb4 : κ ^ 4 ≤ b ^ 4 := pow_le_pow_left₀ hκ.le hκm 4
    have hr2 : r / 2 = d * δ / κ ^ 4 := by rw [hr]; ring
    have h3 : 2 * d * δ / b ^ 2 ≤ (r / 2) * (2 * b ^ 2) := by
      rw [hr2, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hκ4]
      have : 0 ≤ (d : ℝ) * δ := mul_nonneg hdpos.le hδ0
      nlinarith [pow_pos hb 2, pow_pos hκ 4, mul_nonneg this (pow_pos hb 4).le]
    calc ‖m - Φ g' m‖ ≤ 2 * d * δ / b ^ 2 := hnorm
      _ ≤ (r / 2) * (2 * b ^ 2) := h3
      _ ≤ (r / 2) * ‖A‖ := mul_le_mul_of_nonneg_left hAnorm (by positivity)
  -- the ball is invariant
  have hmaps : Set.MapsTo T (Metric.closedBall m r) (Metric.closedBall m r) := by
    intro μ hμ
    have hμ1 : ‖μ - m‖ ≤ r := by simpa [dist_eq_norm] using hμ
    have := hcontr μ hμ m (Metric.mem_closedBall_self hrnn)
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖T μ - m‖ ≤ ‖T μ - T m‖ + ‖T m - m‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (1 / 2) * ‖μ - m‖ + r / 2 := add_le_add this hTm
      _ ≤ (1 / 2) * r + r / 2 := by gcongr
      _ = r := by ring
  have hLip : ContractingWith (1 / 2 : NNReal) (hmaps.restrict T (Metric.closedBall m r) (Metric.closedBall m r)) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    have := hcontr x.1 x.2 y.1 y.2
    rw [Subtype.dist_eq]
    show dist (T x.1) (T y.1) ≤ ((1 / 2 : NNReal) : ℝ) * dist x.1 y.1
    rw [dist_eq_norm, dist_eq_norm]
    simpa using this
  obtain ⟨y, hy, hfy, -, -⟩ := ContractingWith.exists_fixedPoint' Metric.isClosed_closedBall.isComplete hmaps hLip
    (Metric.mem_closedBall_self hrnn) (edist_ne_top _ _)
  have hyim : b / 2 ≤ y.im := hball_im y hy
  have hy1 : ‖y - m‖ ≤ r := by simpa [dist_eq_norm] using hy
  -- the fixed point solves `(self_m)` at `g'`
  have hyfix : y = Φ g' y := by
    have h1 : T y = y := hfy
    simp only [hT] at h1
    have h2 : (y - Φ g' y) / A = 0 := by linear_combination -h1
    rw [div_eq_zero_iff] at h2
    rcases h2 with h2 | h2
    · linear_combination h2
    · exact absurd h2 hA0
  refine ⟨y, (BASelf_iff_fixed d L g' E y).mpr ⟨by linarith, hyfix⟩, hy1, ?_⟩
  have : m.im - y.im ≤ ‖y - m‖ := by
    have := Complex.abs_im_le_norm (y - m)
    rw [Complex.sub_im] at this
    have := (abs_le.mp this).1
    linarith
  linarith


/-- **`BAmWindow`, proved** (the coupling window; `c₁ = min(1/2, κ⁹/(64 d Λ))`, `C = 2d/κ⁴`): `BAwindow_step` at every `g' ∈ [√(1 - c₁) g, g]`
(`g - g' ≤ (1 - √(1 - c₁)) g ≤ c₁ Λ ≤ κ⁹/(64 d)`), and the fixed point is `BAm d L g' E` by `BAm_real_eq_of_self`. -/
theorem BAmWindow_holds (d : ℕ) (Λ κ : ℝ) : BAmWindow d Λ κ := by
  intro hd hΛ hκ
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  refine ⟨min (1 / 2) (κ ^ 9 / (64 * d * Λ)), lt_min (by norm_num) (by positivity), min_le_left _ _, 2 * d / κ ^ 4,
    by positivity, ?_⟩
  intro L hL g hg hgΛ E m hreal g' hlo hhi
  have : NeZero L := ⟨by omega⟩
  obtain ⟨hself, hκm⟩ := hreal
  set c₁ : ℝ := min (1 / 2) (κ ^ 9 / (64 * d * Λ)) with hc₁
  have hc₁0 : 0 ≤ c₁ := (lt_min (by norm_num) (by positivity)).le
  have hc₁1 : c₁ ≤ 1 / 2 := min_le_left _ _
  have hδ : g - g' ≤ κ ^ 9 / (64 * d) := by
    have h3 : 1 - Real.sqrt (1 - c₁) ≤ c₁ := by
      have : 1 - c₁ ≤ Real.sqrt (1 - c₁) := Real.le_sqrt_of_sq_le (by nlinarith)
      linarith
    have h4 : (1 - Real.sqrt (1 - c₁)) * g ≤ c₁ * Λ := mul_le_mul h3 hgΛ hg.le hc₁0
    have h5 : c₁ * Λ ≤ κ ^ 9 / (64 * d) := by
      have := min_le_right (1 / 2 : ℝ) (κ ^ 9 / (64 * d * Λ))
      calc c₁ * Λ ≤ (κ ^ 9 / (64 * d * Λ)) * Λ := mul_le_mul_of_nonneg_right this hΛ.le
        _ = κ ^ 9 / (64 * d) := by field_simp
    linarith
  obtain ⟨m', hm', hdist, hκ'⟩ := BAwindow_step d L hL hd1 hκ hg hself hκm hhi hδ
  have hBAm : BAm d L g' (E : ℂ) = m' := BAm_real_eq_of_self d L g' E m' hm'
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hBAm]; exact hm'
  · rw [hBAm]; exact hκ'
  · rw [hBAm]
    calc ‖m' - m‖ ≤ 2 * d * (g - g') / κ ^ 4 := hdist
      _ = 2 * d / κ ^ 4 * (g - g') := by ring

/-- **The window, iterated at a fixed floor.**  `BAwindow_step` at the floor `κf` (step `κf⁹/(64 d)`, loss `2 d δ/κf⁴` per step, `N` steps):
from a real-axis solution `m` at `(g, E)` with `κf + 2 d (g - g')/κf⁴ ≤ Im m`, every `0 < g' ≤ g` with `g - g' ≤ N κf⁹/(64 d)` has a
real-axis solution `m'` with `Im m' ≥ κf` and `‖m' - m‖ ≤ 2 d (g - g')/κf⁴`.  (The one step of `BAmWindow_holds` uses `N = 1`; the sharper
window constants of the instances of section 7 use this.) -/
theorem BAwindow_iter (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (hd : 1 ≤ d) {E κf : ℝ} (hκf : 0 < κf) :
    ∀ (N : ℕ) {g g' : ℝ}, 0 < g' → g' ≤ g → g - g' ≤ N * (κf ^ 9 / (64 * d)) →
      ∀ {m : ℂ}, BASelf d L g (E : ℂ) m → κf + 2 * d * (g - g') / κf ^ 4 ≤ m.im →
        ∃ m' : ℂ, BASelf d L g' (E : ℂ) m' ∧ ‖m' - m‖ ≤ 2 * d * (g - g') / κf ^ 4 ∧ κf ≤ m'.im := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  intro N
  induction N with
  | zero =>
    intro g g' hg' hle hdist m hm him
    have hgg : g' = g := by
      have : g - g' ≤ 0 := by simpa using hdist
      linarith
    subst hgg
    refine ⟨m, hm, by simp, ?_⟩
    have : 0 ≤ 2 * d * (g' - g') / κf ^ 4 := by simp
    linarith
  | succ N ih =>
    intro g g' hg' hle hdist m hm him
    have hδpos : 0 < κf ^ 9 / (64 * d) := by positivity
    have hgpos : 0 < g := lt_of_lt_of_le hg' hle
    have hnn : 0 ≤ 2 * d * (g - g') / κf ^ 4 :=
      div_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hle)) (by positivity)
    have hg₁g : max g' (g - κf ^ 9 / (64 * d)) ≤ g := max_le hle (by linarith)
    have hg'g₁ : g' ≤ max g' (g - κf ^ 9 / (64 * d)) := le_max_left _ _
    have hg₁pos : 0 < max g' (g - κf ^ 9 / (64 * d)) := lt_of_lt_of_le hg' hg'g₁
    have hstep : g - max g' (g - κf ^ 9 / (64 * d)) ≤ κf ^ 9 / (64 * d) := by
      have : g - κf ^ 9 / (64 * d) ≤ max g' (g - κf ^ 9 / (64 * d)) := le_max_right _ _
      linarith
    have hκfm : κf ≤ m.im := by linarith
    obtain ⟨m₁, hm₁, hd₁, -⟩ := BAwindow_step d L hL hd hκf hgpos hm hκfm hg₁g hstep
    have him₁ : κf + 2 * d * (max g' (g - κf ^ 9 / (64 * d)) - g') / κf ^ 4 ≤ m₁.im := by
      have h1 : |m₁.im - m.im| ≤ ‖m₁ - m‖ := by
        have := Complex.abs_im_le_norm (m₁ - m)
        simpa using this
      have h2 := (abs_le.mp h1).1
      have e : 2 * d * (g - g') / κf ^ 4 = 2 * d * (g - max g' (g - κf ^ 9 / (64 * d))) / κf ^ 4 +
          2 * d * (max g' (g - κf ^ 9 / (64 * d)) - g') / κf ^ 4 := by ring
      linarith
    have hdist₁ : max g' (g - κf ^ 9 / (64 * d)) - g' ≤ N * (κf ^ 9 / (64 * d)) := by
      rcases le_total g' (g - κf ^ 9 / (64 * d)) with h | h
      · rw [max_eq_right h]
        push_cast at hdist
        linarith
      · rw [max_eq_left h]
        have : 0 ≤ (N : ℝ) * (κf ^ 9 / (64 * d)) := by positivity
        linarith
    obtain ⟨m', hm', hd', him'⟩ := ih hg' hg'g₁ hdist₁ hm₁ him₁
    refine ⟨m', hm', ?_, him'⟩
    calc ‖m' - m‖ ≤ ‖m' - m₁‖ + ‖m₁ - m‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * d * (max g' (g - κf ^ 9 / (64 * d)) - g') / κf ^ 4 +
          2 * d * (g - max g' (g - κf ^ 9 / (64 * d))) / κf ^ 4 := add_le_add hd' hd₁
      _ = 2 * d * (g - g') / κf ^ 4 := by ring

/-- **The window at a floor `κf`, for `BAm`.**  `m(E, g')` is the real-axis solution at `g'`, with `Im ≥ κf` and the Lipschitz bound,
whenever the loss budget `κf + 2 d (g - g')/κf⁴ ≤ κ ≤ Im m` holds (`0 < g' ≤ g`). -/
theorem BAwindow_floor (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (hd : 1 ≤ d) {g g' E κ κf : ℝ} (hκf : 0 < κf)
    (hg' : 0 < g') (hle : g' ≤ g) {m : ℂ} (hm : BASelf d L g (E : ℂ) m) (hκm : κ ≤ m.im)
    (hbudget : κf + 2 * d * (g - g') / κf ^ 4 ≤ κ) :
    κf ≤ (BAm d L g' (E : ℂ)).im ∧ ‖BAm d L g' (E : ℂ) - m‖ ≤ 2 * d * (g - g') / κf ^ 4 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hδpos : 0 < κf ^ 9 / (64 * d) := by positivity
  obtain ⟨N, hN⟩ := exists_nat_ge ((g - g') / (κf ^ 9 / (64 * d)))
  have hdist : g - g' ≤ N * (κf ^ 9 / (64 * d)) := by
    rwa [div_le_iff₀ hδpos] at hN
  obtain ⟨m', hm', hd', him'⟩ := BAwindow_iter d L hL hd hκf N hg' hle hdist hm (by linarith)
  have hBAm : BAm d L g' (E : ℂ) = m' := BAm_real_eq_of_self d L g' E m' hm'
  rw [hBAm]
  exact ⟨him', hd'⟩

end Window

section Family

variable {d : ℕ}

/-- The window `[√(1 - c₁) g₀, g₀]` lies in the κ-bulk at the energy `E` (structural premise of the family pins). -/
def BAWinBulk (sz : Sizes d) (z : ℕ → ℂ) (c₁ κ : ℝ) : Prop :=
  ∀ (n : ℕ) (g' : ℝ),
    Real.sqrt (1 - c₁) * (Real.sqrt (BAt0 (z n) (BAm d (sz.L n) (sz.lam n) (z n))) * sz.lam n) ≤ g' →
    g' ≤ Real.sqrt (BAt0 (z n) (BAm d (sz.L n) (sz.lam n) (z n))) * sz.lam n →
    κ ≤ (BAm d (sz.L n) g' (BAflowE (z n) (BAm d (sz.L n) (sz.lam n) (z n)) : ℂ)).im


/-- From the chain domain and `BAmWindow`: the window is in the `κ/2`-bulk (`c₁` after `κ, Λ`, before the sequence). -/
def BAWinBulk_of_dom_stmt (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ Λ : ℝ, 0 < κ → 0 < Λ →
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 2 ∧
      ∀ (ε : ℝ) (sz : Sizes d) (z : ℕ → ℂ), (∀ n, 0 < sz.lam n ∧ sz.lam n ≤ Λ) →
        (∀ n, BAdom d (sz.L n) (sz.size n) (sz.lam n) κ ε (z n)) → BAWinBulk sz z c₁ (κ / 2)

/-! ### 3.2 `BAWinBulk_of_dom` (proved from `BAmWindow`) -/

/-- *Proved from `BAmWindow`.* The chain domain `BAdom κ` gives the window in the `κ/2`-bulk: `BAdom_real` (merged) puts
`(g₀, E, m₀)` in `BAReal d L g₀ κ`, and `BAmWindow` (hypothesis `hw`, discharged by `BAmWindow_holds` in `BAWinBulk_of_dom_holds`) moves `g₀` down to `g'`. -/
theorem BAWinBulk_of_dom (d : ℕ) (hw : ∀ Λ κ : ℝ, BAmWindow d Λ κ) : BAWinBulk_of_dom_stmt d := by
  intro hd κ Λ hκ hΛ
  obtain ⟨c₁, hc₁, hc₁', C, hC, H⟩ := hw Λ κ hd hΛ hκ
  refine ⟨c₁, hc₁, hc₁', fun ε sz z hlam hdom => ?_⟩
  intro n g' hlo hhi
  obtain ⟨hlam0, hlamΛ⟩ := hlam n
  obtain ⟨hκm, hz1, hz2⟩ := hdom n
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hzpos : 0 < (z n).im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN _) hz1
  have hm := BAm_self d (sz.L n) (sz.lam n) (z n) hzpos
  have hreal := BAdom_real hzpos hm hκm
  have hmpos : 0 < (BAm d (sz.L n) (sz.lam n) (z n)).im := lt_of_lt_of_le hκ hκm
  have ht0 := BAt0_pos hzpos hmpos
  have hg0pos : 0 < Real.sqrt (BAt0 (z n) (BAm d (sz.L n) (sz.lam n) (z n))) * sz.lam n :=
    mul_pos (Real.sqrt_pos.mpr ht0) hlam0
  have hg0le := BAg0_le hlam0.le hzpos hmpos
  exact (H (sz.L n) (sz.three_le_L n) _ hg0pos (hg0le.trans hlamΛ) _ _ hreal g' hlo hhi).1.2

/-- **`BAWinBulk_of_dom`, unconditional** (`BAmWindow_holds`). -/
theorem BAWinBulk_of_dom_holds (d : ℕ) : BAWinBulk_of_dom_stmt d := BAWinBulk_of_dom d (BAmWindow_holds d)

end Family

namespace CouplingWindowInst

/-! ### 7.2 The one-point sequence `(L, g) = (4, 10)` (interior gaps; the construction of the flow point of T2189) -/

section OnePoint

open RBM.BA.MFixedPointInst

/-- The one-point sizes `L ≡ 4`, `W ≡ 2`, `lam ≡ 10` (`N = 512`). -/
def szP : Sizes 3 where
  L := fun _ => 4
  W := fun _ => 2
  lam := fun _ => 10
  three_le_L := fun _ => by norm_num
  W_pos := fun _ => by norm_num

/-- The merged subordination point `z_S(4, 10)`, constant. -/
def zP : ℕ → ℂ := fun _ => zS 4 10

/-- `t₀`, `E`, `m₀`, `g₀` of the flow of `z_S(4, 10)` (`(eq:t0E0_BA)`; the same construction as the flow point `P` of T2189, which is
`Nonempty.some` and so opaque; here the data are explicit). -/
def t0P : ℝ := BAt0 (zS 4 10) (mS 4 10)
def EP : ℝ := BAflowE (zS 4 10) (mS 4 10)
def m0P : ℂ := mS 4 10 / (Real.sqrt t0P : ℂ)
def g0P : ℝ := Real.sqrt t0P * 10

theorem BAm_zP : BAm 3 4 10 (zS 4 10) = mS 4 10 :=
  BASelf_unique 3 4 10 (zS 4 10) _ _ (zS_im_pos 4 10).le (BAm_self 3 4 10 (zS 4 10) (zS_im_pos 4 10)) (selfS 4 10)

theorem flowP_data : 0 < t0P ∧ t0P < 1 ∧ BASelf 3 4 g0P (EP : ℂ) m0P :=
  let h := BAzztE_data 3 4 10 (zS_im_pos 4 10) (selfS 4 10)
  ⟨h.1, h.2.1, h.2.2.1⟩


theorem g0P_pos : 0 < g0P := mul_pos (Real.sqrt_pos.mpr flowP_data.1) (by norm_num)

theorem g0P_le : g0P ≤ 10 := BAg0_le (by norm_num) (zS_im_pos 4 10) (selfS 4 10).1

theorem flowP_real : BAReal 3 4 g0P (mS 4 10).im EP m0P := by
  have h := BAdom_real (d := 3) (L := 4) (g := 10) (z := zS 4 10) (κ := (mS 4 10).im) (zS_im_pos 4 10)
    (BAm_self 3 4 10 (zS 4 10) (zS_im_pos 4 10)) (by rw [BAm_zP])
  rw [BAm_zP] at h
  exact h

/-- **The window at the flow point of `(L, g) = (4, 10)`** (`BAmWindow_holds`; no hypothesis): the chain pins' window premise
`BAWinBulk` holds for the one-point sequence `L ≡ 4`, `lam ≡ 10`, `z ≡ z_S(4, 10)` (flow data `(g₀, E) = (g0P, EP)`), with some
`c₁ > 0` (the proof's `c₁ = min(1/2, κ⁹/(64 d Λ))`, `κ = Im m_S(4, 10)`), and `Im m ≥ κ/2` on the window. -/
example :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 2 ∧ BAWinBulk szP zP c₁ ((mS 4 10).im / 2) := by
  obtain ⟨c₁, h0, h1, C, hC, H⟩ := BAmWindow_holds 3 10 (mS 4 10).im (by norm_num) (by norm_num) (selfS 4 10).1
  refine ⟨c₁, h0, h1, fun n g' hlo hhi => ?_⟩
  have e : BAm 3 (szP.L n) (szP.lam n) (zP n) = mS 4 10 := BAm_zP
  rw [e] at hlo hhi ⊢
  exact (H 4 (by norm_num) g0P g0P_pos g0P_le EP m0P flowP_real g' hlo hhi).1.2

/-- `BAzztE_inv` at these data: the inverse of `zztE_BA` returns `m(z', 10) = √t₀ m₀`, horizon `t₀`, energy `E`. -/
example : BAm 3 4 10 (ztOf m0P EP t0P / (Real.sqrt t0P : ℂ)) = (Real.sqrt t0P : ℂ) * m0P ∧
    BAt0 (ztOf m0P EP t0P / (Real.sqrt t0P : ℂ)) ((Real.sqrt t0P : ℂ) * m0P) = t0P ∧
      BAflowE (ztOf m0P EP t0P / (Real.sqrt t0P : ℂ)) ((Real.sqrt t0P : ℂ) * m0P) = EP :=
  BAzztE_inv_holds 3 4 (by norm_num) 10 (by norm_num) t0P EP m0P flowP_data.1 flowP_data.2.1 flowP_data.2.2

/-- `BAgapReal` at the real-axis data of the flow point: `Re (1 - 4^{-3} tr M²) ≥ 2 (Im m₀)²` at `L = 4`, `g₀ = g0P`. -/
example : 2 * m0P.im ^ 2 ≤
    (1 - (((4 ^ 3 : ℕ) : ℂ))⁻¹ * (BAMB 3 4 g0P (EP : ℂ) m0P * BAMB 3 4 g0P (EP : ℂ) m0P).trace).re :=
  BAgapReal_holds 3 4 (by norm_num) g0P g0P_pos EP m0P flowP_data.2.2

/-- The spectral form of `M²` at the same data. -/
example : (BAMB 3 4 g0P (EP : ℂ) m0P * BAMB 3 4 g0P (EP : ℂ) m0P).trace =
    ∑ i, (((BAspec 3 4 g0P i : ℂ) - ((EP : ℂ) + m0P))⁻¹) ^ 2 :=
  BAMB_trace_sq_eq_sum 3 4 g0P (EP : ℂ) m0P (by
    have := flowP_data.2.2.1
    simp only [Complex.add_im, Complex.ofReal_im, zero_add]
    exact this.ne')

end OnePoint


end CouplingWindowInst

end RBM.BA

end
