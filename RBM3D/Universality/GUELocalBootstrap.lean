/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.Step1RegularityGUE
import RBM3D.Green.LDE
import RBM3D.Green.EntryCore
import RBM3D.Induction.ConArgDet
import RBM3D.Induction.Split
import RBM3D.Gauss.FlowCalculus

/-!
# `RBM3D.Universality.GUELocalBootstrap` (UN-09): the GUE local law from the Schur tail

Port of `RBM2D/Universality/GUELocalBootstrap.lean` at commit `c9a24cf` (1042 lines; read-only) to
`Sizes d`, `Ω d L W`, `N = (W L)^d` (ticket T2244; design UN-D1 = T2162, portmap row UN-09).

Target: the merged owed pin `UNGUELocal` (`RBM3D/Universality/Pins.lean`), the weak averaged bulk
local law `|m_N(z) - m_sc(z)| ≤ N^τ (N Im z)^{-1/2}` of the `N × N` GUE, `N = (W L)^d`, on
`|Re z| ≤ 2 - κ`, `N^{-1+τ} ≤ Im z ≤ 10` (internal to the project; not in the paper).  It is
proved here from the new owed pin `UNGUESchurTail` (the probabilistic input, proved by UN-10
`GUELocalSchur`): `un_gueLocal_of_tail : UNGUESchurTail → UNGUELocal`.  The bootstrap is
deterministic per sample point (`gue_local_det`); `d` enters only through `Idx d`, `Ω d`, `gueP d`,
`Xmat d`, and the scale `N`.

Contents.
* Facts on `msc` (`norm_msc_add_z_gt_one`, ..., `sqrt_le_norm_two_msc_add_z`, `sc_stability`).
* The self-consistent equation: `schurErr`, `sc_residual`, `norm_green_diag_le_two`, `sc_one_step`,
  and the a priori bounds `norm_msc_sub_le`, `norm_stieltjesN_le`, `norm_stieltjesN_sub_le`.
* The chain along a vertical line (`chain_bound`, gap `cGap κ = √(κ (4 - κ))`).
* The budget `schurBud`, `budSimp`, the grid `glPts` (mesh `N⁻⁴`, at most `N^9` points),
  the power bookkeeping (`budSimp_le`, `jump_le`, `interp_le`), the smallness conditions `GlSmall`
  (a conjunction `N55 ∧ h1 ∧ h2 ∧ h3`, the fields of the RBM2D `structure` in the same order), their
  validity for large `N` (`glSmall_eventually`), and the deterministic law `gue_local_det`.
* The pin `UNGUESchurTail` (owed, UN-10), `glPts_mem`, `glPts_card`, `un_gueLocal_of_tail`.
* Instances (namespace `GUELocalBootstrapInst`): `d = 3`, `sz0`, `κ = 1`, `τ = 1/10`.

Changes against RBM2D: `stieltjesN` is `Gres`-based here, so a private bridge
`Gres H z true = green H z` (template `RBM3D/Universality/InjSum.lean:76`) rewrites it to the
`green`-trace form; `RBM2D` `norm_green_le` is `norm_Gsig_le_inv_eta` through the bridge.
The smallness constants of `GlSmall` hold from `N ≈ 10^72.1` at `κ = 1`, `τ = 1/10`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace RBM.Univ

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal Matrix.Norms.L2Operator

section GUELocalBootstrap

/-! ### The `Gres` bridge -/

/-- The merged `Gres H z true` (a `Ring.inverse`) is `RBM.green H z = (H - z)⁻¹`
(template `RBM3D/Universality/InjSum.lean:76`, private there). -/
private theorem GUELocalBootstrap_Gres_true {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (z : ℂ) : RBM.Gauss.Gres H z true = green H z := by
  simp only [green, RBM.Gauss.Gres, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]

/-- `m_N(z) = N⁻¹ tr (H - z)⁻¹` in the `green` form of RBM2D. -/
private theorem GUELocalBootstrap_stieltjesN_eq {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (z : ℂ) :
    stieltjesN H z = (Fintype.card n : ℂ)⁻¹ * (green H z).trace := by
  unfold stieltjesN
  rw [GUELocalBootstrap_Gres_true]

/-- `‖(H - z)⁻¹‖ ≤ 1/Im z` for Hermitian `H` and `Im z > 0` (RBM2D `RBM.Gauss.norm_green_le`, rebuilt
from the merged `norm_Gsig_le_inv_eta` through the bridge). -/
private theorem GUELocalBootstrap_norm_green_le {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) : ‖green H z‖ ≤ (z.im)⁻¹ := by
  rw [← GUELocalBootstrap_Gres_true]
  exact RBM.Gauss.norm_Gsig_le_inv_eta hH hz (le_abs_self _) true

/-! ### Facts on `msc` -/

private theorem GUELocalBootstrap_msc_norm_mul {z : ℂ} : ‖msc z‖ * ‖msc z + z‖ = 1 := by
  have h1 : msc z * (msc z + z) = -1 := msc_mul z
  have := congrArg norm h1
  simpa [norm_mul] using this

theorem norm_msc_add_z_gt_one {z : ℂ} (hz : 0 < z.im) : 1 < ‖msc z + z‖ := by
  have hn := (GUELocalBootstrap_msc_norm_mul (z := z))
  have hlt := norm_msc_lt_one hz
  have hpos : 0 < ‖msc z‖ := by
    rw [norm_pos_iff]
    intro h0
    rw [h0] at hn
    simp at hn
  by_contra hcon
  push Not at hcon
  have : ‖msc z‖ * ‖msc z + z‖ < 1 := by
    calc ‖msc z‖ * ‖msc z + z‖ ≤ ‖msc z‖ * 1 := mul_le_mul_of_nonneg_left hcon hpos.le
      _ < 1 := by linarith
  linarith

theorem im_le_norm_msc_add_z {z : ℂ} (hz : 0 < z.im) : z.im ≤ ‖msc z + z‖ := by
  have h2 : z.im ≤ (msc z + z).im := by
    rw [Complex.add_im]; linarith [msc_im_pos hz]
  exact h2.trans (Complex.im_le_norm _)

theorem norm_msc_le_inv_im {z : ℂ} (hz : 0 < z.im) : ‖msc z‖ ≤ (z.im)⁻¹ := by
  have hn := (GUELocalBootstrap_msc_norm_mul (z := z))
  have him := im_le_norm_msc_add_z hz
  have h3 : ‖msc z‖ * z.im ≤ 1 := by
    calc ‖msc z‖ * z.im ≤ ‖msc z‖ * ‖msc z + z‖ := mul_le_mul_of_nonneg_left him (norm_nonneg _)
      _ = 1 := hn
  rw [← one_div, le_div_iff₀ hz]
  exact h3

/-- `(2 m + z)² = z² - 4` for `m = msc z`. -/
theorem msc_disc_sq (z : ℂ) : (2 * msc z + z) ^ 2 = z ^ 2 - 4 := by
  have h := msc_mul z
  linear_combination 4 * h

/-- **The bulk gap of the semicircle square root**: `√(κ (4 - κ)) ≤ |2 m_sc(z) + z|` for
`|Re z| ≤ 2 - κ`. -/
theorem sqrt_le_norm_two_msc_add_z {z : ℂ} {κ : ℝ} (hκ : 0 < κ) (hx : |z.re| ≤ 2 - κ) :
    Real.sqrt (κ * (4 - κ)) ≤ ‖2 * msc z + z‖ := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg z.re]
  have h1 : (2 - z.re) ≤ ‖z - 2‖ := by
    have : |(z - 2).re| ≤ ‖z - 2‖ := Complex.abs_re_le_norm _
    have h2 : (z - 2).re = z.re - 2 := by simp
    rw [h2] at this
    have : 2 - z.re ≤ |z.re - 2| := by rw [abs_sub_comm]; exact le_abs_self _
    linarith [Complex.abs_re_le_norm (z - 2), (show (z - 2).re = z.re - 2 by simp)]
  have h2 : (2 + z.re) ≤ ‖z + 2‖ := by
    have h3 : |(z + 2).re| ≤ ‖z + 2‖ := Complex.abs_re_le_norm _
    have h4 : (z + 2).re = z.re + 2 := by simp
    rw [h4] at h3
    linarith [le_abs_self (z.re + 2)]
  have hxu : z.re ≤ 2 - κ := by linarith [le_abs_self z.re]
  have hxl : -(2 - κ) ≤ z.re := by linarith [neg_abs_le z.re]
  have hprod : κ * (4 - κ) ≤ ‖z - 2‖ * ‖z + 2‖ := by
    have e1 : 0 ≤ 2 - z.re := by linarith
    have e2 : 0 ≤ 2 + z.re := by linarith
    calc κ * (4 - κ) ≤ (2 - z.re) * (2 + z.re) := by nlinarith
      _ ≤ ‖z - 2‖ * ‖z + 2‖ := mul_le_mul h1 h2 e2 (norm_nonneg _)
  have hsq : ‖2 * msc z + z‖ ^ 2 = ‖z - 2‖ * ‖z + 2‖ := by
    rw [← norm_pow, msc_disc_sq, show z ^ 2 - 4 = (z - 2) * (z + 2) by ring, norm_mul]
  apply Real.sqrt_le_iff.2
  exact ⟨norm_nonneg _, by rw [hsq]; exact hprod⟩


theorem im_le_norm_two_msc_add_z {z : ℂ} (hz : 0 < z.im) : z.im ≤ ‖2 * msc z + z‖ := by
  have h2 : z.im ≤ (2 * msc z + z).im := by
    rw [Complex.add_im, Complex.mul_im]
    simp only [Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero]
    linarith [msc_im_pos hz]
  exact h2.trans (Complex.im_le_norm _)

/-! ### The self-consistent equation: stability -/

/-- **Stability of the self-consistent equation**: `m (z + m) + 1 = (m - a)(m + z + a)`, `a = m_sc(z)`;
if `|m - a| ≤ c/2` and `c ≤ |2a + z|` then `|m - a| ≤ 2 |m (z + m) + 1| / c`. -/
theorem sc_stability {m z : ℂ} {c Λ : ℝ} (hc : 0 < c) (hcz : c ≤ ‖2 * msc z + z‖)
    (hres : ‖m * (z + m) + 1‖ ≤ Λ) (hnear : ‖m - msc z‖ ≤ c / 2) :
    ‖m - msc z‖ ≤ 2 * Λ / c := by
  set a := msc z with ha
  have hfac : m * (z + m) + 1 = (m - a) * (m + z + a) := by
    have h := msc_mul z
    rw [← ha] at h
    linear_combination h
  have h2 : c / 2 ≤ ‖m + z + a‖ := by
    have e : 2 * a + z = (m + z + a) - (m - a) := by ring
    have h3 : ‖2 * a + z‖ ≤ ‖m + z + a‖ + ‖m - a‖ := by
      rw [e]; exact norm_sub_le _ _
    linarith
  have h4 : ‖m - a‖ * (c / 2) ≤ Λ := by
    calc ‖m - a‖ * (c / 2) ≤ ‖m - a‖ * ‖m + z + a‖ :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = ‖m * (z + m) + 1‖ := by rw [hfac, norm_mul]
      _ ≤ Λ := hres
  rw [le_div_iff₀ hc]
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Schur error `Υ_i(z) = (G_ii)⁻¹ + z + m_N(z)`: `G_ii = (-(z + m_N) + Υ_i)⁻¹`. -/
def schurErr (H : Matrix ι ι ℂ) (z : ℂ) (i : ι) : ℂ :=
  (green H z i i)⁻¹ + z + stieltjesN H z

/-- **The residual of the self-consistent equation is the average of `Υ_i G_ii`** (exact). -/
theorem sc_residual [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    stieltjesN H z * (z + stieltjesN H z) + 1
      = (Fintype.card ι : ℂ)⁻¹ * ∑ i, schurErr H z i * green H z i i := by
  have hN : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hG : ∀ i, green H z i i ≠ 0 := RBM.Green.green_diag_ne_zero hH hz
  have key : ∀ i, schurErr H z i * green H z i i = 1 + (z + stieltjesN H z) * green H z i i := by
    intro i
    unfold schurErr
    field_simp [hG i]
    ring
  simp_rw [key, Finset.sum_add_distrib, ← Finset.mul_sum]
  have htr : ∑ i, green H z i i = (green H z).trace := rfl
  rw [htr, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  simp only [GUELocalBootstrap_stieltjesN_eq]
  field_simp
  ring

/-- `|G_ii| ≤ 2` once `|Υ_i| ≤ 1/4` and `|m_N - m_sc| ≤ 1/4`. -/
theorem norm_green_diag_le_two {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im)
    (i : ι) (hΥ : ‖schurErr H z i‖ ≤ 1 / 4) (hm : ‖stieltjesN H z - msc z‖ ≤ 1 / 4) :
    ‖green H z i i‖ ≤ 2 := by
  have hG : green H z i i ≠ 0 := RBM.Green.green_diag_ne_zero hH hz.ne' i
  set m := stieltjesN H z with hm_def
  have h1 : (green H z i i)⁻¹ = schurErr H z i - (z + m) := by
    unfold schurErr; ring
  have h2 : 3 / 4 ≤ ‖z + m‖ := by
    have e : z + m = (msc z + z) + (m - msc z) := by ring
    have h3 : ‖msc z + z‖ - ‖m - msc z‖ ≤ ‖z + m‖ := by
      rw [e]
      have := norm_sub_norm_le (msc z + z) (-(m - msc z))
      rw [sub_neg_eq_add, norm_neg] at this
      exact this
    linarith [norm_msc_add_z_gt_one hz]
  have h3 : 1 / 2 ≤ ‖(green H z i i)⁻¹‖ := by
    rw [h1]
    have := norm_sub_norm_le (z + m) (schurErr H z i)
    rw [norm_sub_rev] at this
    linarith
  have hpos : 0 < ‖(green H z i i)⁻¹‖ := by linarith
  rw [norm_inv] at h3 hpos
  have : ‖green H z i i‖ ≤ 2 := by
    have hGn : 0 < ‖green H z i i‖ := by simpa using hG
    rw [← inv_inv ‖green H z i i‖]
    calc (‖green H z i i‖)⁻¹⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := by
          apply inv_anti₀ (by norm_num) h3
      _ = 2 := by norm_num
  exact this

/-- **One step of the bootstrap.**  At a point `z` of the window, if `|Υ_i| ≤ υ ≤ 1/4` for all `i`
and `|m_N - m_sc| ≤ min (c/2) (1/4)`, with `c ≤ |2 m_sc + z|`, then `|m_N - m_sc| ≤ 4 υ / c`. -/
theorem sc_one_step [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im)
    {c υ : ℝ} (hc : 0 < c) (hcz : c ≤ ‖2 * msc z + z‖) (hυ : υ ≤ 1 / 4)
    (hΥ : ∀ i, ‖schurErr H z i‖ ≤ υ) (hnear : ‖stieltjesN H z - msc z‖ ≤ min (c / 2) (1 / 4)) :
    ‖stieltjesN H z - msc z‖ ≤ 4 * υ / c := by
  have hG2 : ∀ i, ‖green H z i i‖ ≤ 2 := fun i =>
    norm_green_diag_le_two hH hz i ((hΥ i).trans hυ) (hnear.trans (min_le_right _ _))
  have hres : ‖stieltjesN H z * (z + stieltjesN H z) + 1‖ ≤ 2 * υ := by
    rw [sc_residual hH hz.ne']
    have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (Fintype.card ι : ℝ)⁻¹ * ‖∑ i, schurErr H z i * green H z i i‖
        ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖schurErr H z i * green H z i i‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, (2 * υ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul]
          have h0 : 0 ≤ υ := (norm_nonneg _).trans (hΥ i)
          calc ‖schurErr H z i‖ * ‖green H z i i‖ ≤ υ * 2 :=
                mul_le_mul (hΥ i) (hG2 i) (norm_nonneg _) h0
            _ = 2 * υ := by ring
      _ = 2 * υ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp
  have := sc_stability hc hcz hres (hnear.trans (min_le_left _ _))
  calc ‖stieltjesN H z - msc z‖ ≤ 2 * (2 * υ) / c := this
    _ = 4 * υ / c := by ring


/-! ### A priori bounds and Lipschitz continuity in `z` -/

theorem norm_msc_sub_le {z z' : ℂ} (hz : 0 < z.im) (hz' : 0 < z'.im) :
    ‖msc z - msc z'‖ ≤ ‖z - z'‖ / (z.im * z'.im) := by
  set a := msc z with ha
  set a' := msc z' with ha'
  have hquad : (a' - a) * (a + a' + z') = -((z' - z) * a) := by
    have h := msc_mul z'
    have h2 := msc_mul z
    rw [← ha'] at h
    rw [← ha] at h2
    linear_combination h - h2
  have hden : z'.im ≤ ‖a + a' + z'‖ := by
    have : z'.im ≤ (a + a' + z').im := by
      simp only [Complex.add_im]
      linarith [msc_im_pos hz, msc_im_pos hz']
    exact this.trans (Complex.im_le_norm _)
  have hnum : ‖a' - a‖ * ‖a + a' + z'‖ = ‖z' - z‖ * ‖a‖ := by
    rw [← norm_mul, hquad, norm_neg, norm_mul]
  have ha1 : ‖a‖ ≤ (z.im)⁻¹ := norm_msc_le_inv_im hz
  have h3 : ‖a' - a‖ * z'.im ≤ ‖z' - z‖ * (z.im)⁻¹ := by
    calc ‖a' - a‖ * z'.im ≤ ‖a' - a‖ * ‖a + a' + z'‖ :=
          mul_le_mul_of_nonneg_left hden (norm_nonneg _)
      _ = ‖z' - z‖ * ‖a‖ := hnum
      _ ≤ ‖z' - z‖ * (z.im)⁻¹ := mul_le_mul_of_nonneg_left ha1 (norm_nonneg _)
  have h4 : ‖a' - a‖ ≤ ‖z' - z‖ / (z.im * z'.im) := by
    rw [le_div_iff₀ (mul_pos hz hz')]
    calc ‖a' - a‖ * (z.im * z'.im) = (‖a' - a‖ * z'.im) * z.im := by ring
      _ ≤ (‖z' - z‖ * (z.im)⁻¹) * z.im := mul_le_mul_of_nonneg_right h3 hz.le
      _ = ‖z' - z‖ := by field_simp
  rw [norm_sub_rev a a', norm_sub_rev z z']
  exact h4

/-- `|m_N(z)| ≤ 1/Im z`. -/
theorem norm_stieltjesN_le [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) : ‖stieltjesN H z‖ ≤ (z.im)⁻¹ := by
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hG : ‖green H z‖ ≤ (z.im)⁻¹ := GUELocalBootstrap_norm_green_le hH hz
  simp only [GUELocalBootstrap_stieltjesN_eq]
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have htr : ‖(green H z).trace‖ ≤ Fintype.card ι * (z.im)⁻¹ := by
    calc ‖(green H z).trace‖ ≤ ∑ i, ‖green H z i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, (z.im)⁻¹ :=
          Finset.sum_le_sum fun i _ => (RBM.Ind.norm_apply_le_l2_opNorm _ i i).trans hG
      _ = Fintype.card ι * (z.im)⁻¹ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc (Fintype.card ι : ℝ)⁻¹ * ‖(green H z).trace‖
      ≤ (Fintype.card ι : ℝ)⁻¹ * (Fintype.card ι * (z.im)⁻¹) :=
        mul_le_mul_of_nonneg_left htr (by positivity)
    _ = (z.im)⁻¹ := by field_simp

/-- **Lipschitz continuity of `m_N`**: `|m_N(z) - m_N(z')| ≤ |z - z'| / (Im z Im z')`. -/
theorem norm_stieltjesN_sub_le [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z z' : ℂ}
    (hz : 0 < z.im) (hz' : 0 < z'.im) :
    ‖stieltjesN H z - stieltjesN H z'‖ ≤ ‖z - z'‖ / (z.im * z'.im) := by
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hG : ‖green H z‖ ≤ (z.im)⁻¹ := GUELocalBootstrap_norm_green_le hH hz
  have hG' : ‖green H z'‖ ≤ (z'.im)⁻¹ := GUELocalBootstrap_norm_green_le hH hz'
  have hprod : ‖green H z * green H z'‖ ≤ (z.im)⁻¹ * (z'.im)⁻¹ :=
    (norm_mul_le _ _).trans (mul_le_mul hG hG' (norm_nonneg _) (by positivity))
  have htr : ‖(green H z * green H z').trace‖ ≤ Fintype.card ι * ((z.im)⁻¹ * (z'.im)⁻¹) := by
    calc ‖(green H z * green H z').trace‖ ≤ ∑ i, ‖(green H z * green H z') i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, ((z.im)⁻¹ * (z'.im)⁻¹) :=
          Finset.sum_le_sum fun i _ => (RBM.Ind.norm_apply_le_l2_opNorm _ i i).trans hprod
      _ = Fintype.card ι * ((z.im)⁻¹ * (z'.im)⁻¹) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have e : stieltjesN H z - stieltjesN H z'
      = (Fintype.card ι : ℂ)⁻¹ * ((z - z') * (green H z * green H z').trace) := by
    simp only [GUELocalBootstrap_stieltjesN_eq]
    rw [← mul_sub, ← Matrix.trace_sub,
      RBM.green_sub_green (RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero hH hz.ne')
        (RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero hH hz'.ne'), Matrix.trace_smul, smul_eq_mul]
  rw [e, norm_mul, norm_inv, Complex.norm_natCast, norm_mul]
  calc (Fintype.card ι : ℝ)⁻¹ * (‖z - z'‖ * ‖(green H z * green H z').trace‖)
      ≤ (Fintype.card ι : ℝ)⁻¹ * (‖z - z'‖ * (Fintype.card ι * ((z.im)⁻¹ * (z'.im)⁻¹))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htr (norm_nonneg _)) (by positivity)
    _ = ‖z - z'‖ / (z.im * z'.im) := by field_simp


/-! ### The chain along a vertical line `Re z = x` -/

/-- The window constant `c_κ = √(κ(4 - κ))`. -/
def cGap (κ : ℝ) : ℝ := Real.sqrt (κ * (4 - κ))

theorem cGap_pos {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) : 0 < cGap κ :=
  Real.sqrt_pos.2 (mul_pos hκ (by linarith))

theorem cGap_le_two {κ : ℝ} : cGap κ ≤ 2 := by
  unfold cGap
  rw [Real.sqrt_le_left (by norm_num)]
  nlinarith [sq_nonneg (κ - 2)]

/-- The chain: along `z_k = x + i η_k`, `η_k = 10 - k h`, if the Schur errors are below the budgets
`υ_k` (whenever `Im m_N ≤ 2`), the budgets are below `1/4` and the step condition
`4 υ_k / c + 2h / (η_k η_{k+1}) ≤ min (c/2) (1/4)` holds, then `|m_N - m_sc| ≤ 4 υ_k / c` at every
`z_k`.  The start `η_0 = 10` has the a priori bound `|m_N - m_sc| ≤ 1/5`. -/
theorem chain_bound [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {κ : ℝ} (hκ : 0 < κ)
    (hκ2 : κ ≤ 2) {x : ℝ} (hx : |x| ≤ 2 - κ) {h : ℝ} (hh : 0 < h) {K : ℕ} {η : ℕ → ℝ}
    (hη : ∀ k, η k = 10 - k * h) (hηpos : ∀ k ≤ K, 0 < η k) {υ : ℕ → ℝ}
    (hυ : ∀ k ≤ K, υ k ≤ 1 / 4)
    (hΥ : ∀ k ≤ K, ∀ i, (stieltjesN H ⟨x, η k⟩).im ≤ 2 → ‖schurErr H ⟨x, η k⟩ i‖ ≤ υ k)
    (hstep : ∀ k, k + 1 ≤ K →
      4 * υ k / cGap κ + 2 * h / (η k * η (k + 1)) ≤ min (cGap κ / 2) (1 / 4)) :
    ∀ k ≤ K, ‖stieltjesN H ⟨x, η k⟩ - msc ⟨x, η k⟩‖ ≤ 4 * υ k / cGap κ := by
  have hc := cGap_pos hκ hκ2
  have hc2 := cGap_le_two (κ := κ)
  intro k
  induction k with
  | zero =>
    intro _
    have hη0 : η 0 = 10 := by rw [hη]; simp
    have hz0 : (0 : ℝ) < (⟨x, η 0⟩ : ℂ).im := by
      change (0 : ℝ) < η 0
      rw [hη0]; norm_num
    have hz0' : ((⟨x, η 0⟩ : ℂ).im) = 10 := by change η 0 = 10; exact hη0
    have hm1 : ‖stieltjesN H ⟨x, η 0⟩‖ ≤ 1 / 10 := by
      have := norm_stieltjesN_le hH hz0
      rwa [hz0', show ((10 : ℝ))⁻¹ = 1 / 10 by norm_num] at this
    have ha1 : ‖msc ⟨x, η 0⟩‖ ≤ 1 / 10 := by
      have := norm_msc_le_inv_im hz0
      rwa [hz0', show ((10 : ℝ))⁻¹ = 1 / 10 by norm_num] at this
    have hnear : ‖stieltjesN H ⟨x, η 0⟩ - msc ⟨x, η 0⟩‖ ≤ min (10 / 2) (1 / 4) := by
      refine le_min ?_ ?_
      · linarith [norm_sub_le (stieltjesN H ⟨x, η 0⟩) (msc ⟨x, η 0⟩)]
      · linarith [norm_sub_le (stieltjesN H ⟨x, η 0⟩) (msc ⟨x, η 0⟩)]
    have hΥ0 := hΥ 0 (Nat.zero_le K)
    have hmim : (stieltjesN H ⟨x, η 0⟩).im ≤ 2 :=
      (Complex.im_le_norm _).trans (by linarith)
    have hcz : (10 : ℝ) ≤ ‖2 * msc ⟨x, η 0⟩ + ⟨x, η 0⟩‖ := by
      have := im_le_norm_two_msc_add_z hz0
      rwa [hz0'] at this
    have h1 := sc_one_step hH hz0 (by norm_num : (0 : ℝ) < 10) hcz (hυ 0 (Nat.zero_le K))
      (fun i => hΥ0 i hmim) hnear
    calc ‖stieltjesN H ⟨x, η 0⟩ - msc ⟨x, η 0⟩‖ ≤ 4 * υ 0 / 10 := h1
      _ ≤ 4 * υ 0 / cGap κ := by
          have hυ0 : 0 ≤ υ 0 := (norm_nonneg _).trans (hΥ0 (Classical.arbitrary ι) hmim)
          exact div_le_div_of_nonneg_left (by positivity) hc (by linarith)
  | succ k ih =>
    intro hk
    have hkK : k ≤ K := Nat.le_of_succ_le hk
    have ihk := ih hkK
    set zk : ℂ := ⟨x, η k⟩ with hzk
    set zk1 : ℂ := ⟨x, η (k + 1)⟩ with hzk1
    have hηk : 0 < η k := hηpos k hkK
    have hηk1 : 0 < η (k + 1) := hηpos (k + 1) hk
    have hz : 0 < zk.im := hηk
    have hz1 : 0 < zk1.im := hηk1
    have hdist : ‖zk - zk1‖ = h := by
      have : zk - zk1 = ((η k - η (k + 1) : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [hzk, hzk1]
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        hη, hη]
      push_cast
      rw [show (10 : ℝ) - k * h - (10 - (k + 1) * h) = h by ring, abs_of_pos hh]
    have hjump : ‖stieltjesN H zk - stieltjesN H zk1‖ ≤ h / (η k * η (k + 1)) := by
      have := norm_stieltjesN_sub_le hH hz hz1
      rwa [hdist] at this
    have hjump' : ‖msc zk - msc zk1‖ ≤ h / (η k * η (k + 1)) := by
      have := norm_msc_sub_le hz hz1
      rwa [hdist] at this
    have hnear : ‖stieltjesN H zk1 - msc zk1‖ ≤ min (cGap κ / 2) (1 / 4) := by
      have e : stieltjesN H zk1 - msc zk1 = (stieltjesN H zk - msc zk)
          - ((stieltjesN H zk - stieltjesN H zk1) - (msc zk - msc zk1)) := by ring
      have h1 : ‖stieltjesN H zk1 - msc zk1‖ ≤ ‖stieltjesN H zk - msc zk‖
          + ‖(stieltjesN H zk - stieltjesN H zk1) - (msc zk - msc zk1)‖ := by
        rw [e]; exact norm_sub_le _ _
      have h2 : ‖(stieltjesN H zk - stieltjesN H zk1) - (msc zk - msc zk1)‖
          ≤ ‖stieltjesN H zk - stieltjesN H zk1‖ + ‖msc zk - msc zk1‖ := norm_sub_le _ _
      have h3 := hstep k hk
      have h4 : 2 * h / (η k * η (k + 1)) = h / (η k * η (k + 1)) + h / (η k * η (k + 1)) := by
        ring
      linarith
    have hmim : (stieltjesN H zk1).im ≤ 2 := by
      have h5 : ‖stieltjesN H zk1‖ ≤ ‖msc zk1‖ + ‖stieltjesN H zk1 - msc zk1‖ := by
        calc ‖stieltjesN H zk1‖ = ‖msc zk1 + (stieltjesN H zk1 - msc zk1)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      have h6 := norm_msc_lt_one hz1
      have h7 := hnear.trans (min_le_right _ _)
      exact (Complex.im_le_norm _).trans (by linarith)
    have hcz : cGap κ ≤ ‖2 * msc zk1 + zk1‖ := sqrt_le_norm_two_msc_add_z hκ hx
    exact sc_one_step hH hz1 hc hcz (hυ (k + 1) hk) (fun i => hΥ (k + 1) hk i hmim) hnear


/-! ### The Schur-error budget and the grid -/

/-- The budget of the Schur error at `z`: `N^ε (N^{-1/2} + (2/(N Im z))^{1/2} + (N Im z)⁻¹)`.  The
middle term is `(Im m_N/(N η))^{1/2}` with `Im m_N ≤ 2` inserted. -/
def schurBud (N ε : ℝ) (z : ℂ) : ℝ :=
  N ^ ε * (1 / Real.sqrt N + Real.sqrt (2 / (N * z.im)) + 1 / (N * z.im))

/-- The simplified budget `6 N^ε / √(N η)`. -/
def budSimp (N ε η : ℝ) : ℝ := 6 * N ^ ε / Real.sqrt (N * η)

theorem schurBud_le {N ε : ℝ} (hN : 1 ≤ N) {z : ℂ} (hη1 : 1 ≤ N * z.im)
    (hη10 : z.im ≤ 10) : schurBud N ε z ≤ budSimp N ε z.im := by
  have hNpos : 0 < N := by linarith
  have hη0 : 0 < z.im := by
    by_contra h; push Not at h
    nlinarith
  have hNη : 0 < N * z.im := by positivity
  set A := Real.sqrt (N * z.im) with hA
  have hApos : 0 < A := Real.sqrt_pos.2 hNη
  have hA1 : 1 ≤ A := by rw [hA]; exact Real.one_le_sqrt.2 hη1
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have h1 : 1 / Real.sqrt N ≤ 3.2 / A := by
    have h10 : A ≤ 3.2 * Real.sqrt N := by
      rw [hA]
      calc Real.sqrt (N * z.im) ≤ Real.sqrt (N * 10) :=
            Real.sqrt_le_sqrt (by nlinarith)
        _ = Real.sqrt N * Real.sqrt 10 := by rw [Real.sqrt_mul hNpos.le]
        _ ≤ Real.sqrt N * 3.2 := by
            apply mul_le_mul_of_nonneg_left _ hsqN.le
            rw [Real.sqrt_le_left (by norm_num)]; norm_num
        _ = 3.2 * Real.sqrt N := by ring
    rw [div_le_div_iff₀ hsqN hApos]
    nlinarith
  have h2 : Real.sqrt (2 / (N * z.im)) ≤ 1.5 / A := by
    rw [Real.sqrt_div (by norm_num)]
    apply div_le_div_of_nonneg_right _ hApos.le
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h3 : 1 / (N * z.im) ≤ 1 / A := by
    apply one_div_le_one_div_of_le hApos
    calc A ≤ A * A := by nlinarith
      _ = N * z.im := by rw [hA, Real.mul_self_sqrt hNη.le]
  have hNε : 0 ≤ N ^ ε := Real.rpow_nonneg hNpos.le _
  unfold schurBud budSimp
  rw [← hA]
  calc N ^ ε * (1 / Real.sqrt N + Real.sqrt (2 / (N * z.im)) + 1 / (N * z.im))
      ≤ N ^ ε * (3.2 / A + 1.5 / A + 1 / A) := by
        apply mul_le_mul_of_nonneg_left _ hNε
        linarith
    _ = N ^ ε * (5.7 / A) := by ring
    _ ≤ N ^ ε * (6 / A) := by
        apply mul_le_mul_of_nonneg_left _ hNε
        apply div_le_div_of_nonneg_right _ hApos.le; norm_num
    _ = 6 * N ^ ε / A := by ring


/-! ### The grid of the window -/

/-- The mesh of the grid. -/
def glMesh (N : ℝ) : ℝ := (N ^ 4)⁻¹

/-- Number of steps in the real direction. -/
def glJ (N κ : ℝ) : ℕ := ⌊2 * (2 - κ) / glMesh N⌋₊

/-- Number of steps in the imaginary direction. -/
def glK (N τ : ℝ) : ℕ := ⌊(10 - N ^ (-1 + τ)) / glMesh N⌋₊

def glE (N κ : ℝ) (j : ℕ) : ℝ := -(2 - κ) + j * glMesh N

def glEta (N : ℝ) (k : ℕ) : ℝ := 10 - k * glMesh N

/-- The grid points `E_j + i η_k` of the window `|Re z| ≤ 2 - κ`, `N^{-1+τ} ≤ Im z ≤ 10`. -/
def glPts (N κ τ : ℝ) : Finset ℂ :=
  ((Finset.range (glJ N κ + 1)) ×ˢ (Finset.range (glK N τ + 1))).image
    (fun p => (⟨glE N κ p.1, glEta N p.2⟩ : ℂ))

theorem glMesh_pos {N : ℝ} (hN : 0 < N) : 0 < glMesh N := by unfold glMesh; positivity

theorem glE_le {N κ : ℝ} (hN : 0 < N) (hκ2 : κ ≤ 2) {j : ℕ} (hj : j ≤ glJ N κ) :
    -(2 - κ) ≤ glE N κ j ∧ glE N κ j ≤ 2 - κ := by
  have hh := glMesh_pos hN
  unfold glE
  refine ⟨by have : 0 ≤ (j : ℝ) * glMesh N := by positivity
             linarith, ?_⟩
  have h1 : (j : ℝ) ≤ 2 * (2 - κ) / glMesh N :=
    (Nat.cast_le.2 hj).trans (Nat.floor_le (by apply div_nonneg <;> [linarith; exact hh.le]))
  rw [le_div_iff₀ hh] at h1
  linarith

theorem glEta_mem {N τ : ℝ} (hN : 0 < N) (hτ : N ^ (-1 + τ) ≤ 10) {k : ℕ}
    (hk : k ≤ glK N τ) : N ^ (-1 + τ) ≤ glEta N k ∧ glEta N k ≤ 10 := by
  have hh := glMesh_pos hN
  unfold glEta
  refine ⟨?_, by have : 0 ≤ (k : ℝ) * glMesh N := by positivity
                 linarith⟩
  have h1 : (k : ℝ) ≤ (10 - N ^ (-1 + τ)) / glMesh N :=
    (Nat.cast_le.2 hk).trans (Nat.floor_le (by apply div_nonneg <;> [linarith; exact hh.le]))
  rw [le_div_iff₀ hh] at h1
  linarith

/-- Every point of the window is within `h` (both coordinates) of a grid point, with the grid
point above it: `η ≤ η_k ≤ η + h`. -/
theorem exists_glPt {N κ τ : ℝ} (hN : 0 < N)
    {z : ℂ} (hx : |z.re| ≤ 2 - κ) (hη1 : N ^ (-1 + τ) ≤ z.im) (hη2 : z.im ≤ 10) :
    ∃ j k : ℕ, j ≤ glJ N κ ∧ k ≤ glK N τ ∧ 0 ≤ z.re - glE N κ j ∧
      z.re - glE N κ j ≤ glMesh N ∧ 0 ≤ glEta N k - z.im ∧ glEta N k - z.im ≤ glMesh N := by
  have hh := glMesh_pos hN
  have hxl : -(2 - κ) ≤ z.re := by linarith [neg_abs_le z.re]
  have hxu : z.re ≤ 2 - κ := by linarith [le_abs_self z.re]
  set j : ℕ := ⌊(z.re + (2 - κ)) / glMesh N⌋₊ with hj
  set k : ℕ := ⌊(10 - z.im) / glMesh N⌋₊ with hk
  have hj0 : (0 : ℝ) ≤ (z.re + (2 - κ)) / glMesh N := div_nonneg (by linarith) hh.le
  have hk0 : (0 : ℝ) ≤ (10 - z.im) / glMesh N := div_nonneg (by linarith) hh.le
  have hj1 : (j : ℝ) ≤ (z.re + (2 - κ)) / glMesh N := Nat.floor_le hj0
  have hj2 : (z.re + (2 - κ)) / glMesh N < j + 1 := Nat.lt_floor_add_one _
  have hk1 : (k : ℝ) ≤ (10 - z.im) / glMesh N := Nat.floor_le hk0
  have hk2 : (10 - z.im) / glMesh N < k + 1 := Nat.lt_floor_add_one _
  rw [le_div_iff₀ hh] at hj1 hk1
  rw [div_lt_iff₀ hh] at hj2 hk2
  refine ⟨j, k, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Nat.le_floor
    rw [le_div_iff₀ hh]
    linarith
  · apply Nat.le_floor
    rw [le_div_iff₀ hh]
    linarith
  · unfold glE; linarith
  · unfold glE; linarith
  · unfold glEta; linarith
  · unfold glEta; linarith


/-! ### Power bookkeeping -/

private theorem inv_le_rpow_neg_one_add {N τ : ℝ} (hN : 1 ≤ N) (hτ : 0 ≤ τ) : N⁻¹ ≤ N ^ (-1 + τ) := by
  have h := Real.rpow_le_rpow_of_exponent_le hN (show (-1 : ℝ) ≤ -1 + τ by linarith)
  rwa [Real.rpow_neg_one] at h

private theorem mul_rpow_neg_one_add {N τ : ℝ} (hN : 0 < N) : N * N ^ (-1 + τ) = N ^ τ := by
  have h := Real.rpow_add hN 1 (-1 + τ)
  rw [Real.rpow_one] at h
  rw [← h]
  congr 1; ring

private theorem sqrt_rpow_eq {N τ : ℝ} (hN : 0 < N) : Real.sqrt (N ^ τ) = N ^ (τ / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN.le]
  congr 1; ring

private theorem one_le_rpow {N τ : ℝ} (hN : 1 ≤ N) (hτ : 0 ≤ τ) : 1 ≤ N ^ τ :=
  Real.one_le_rpow hN hτ

/-- For `η ≥ N^{-1+τ}`: `N η ≥ N^τ`. -/
private theorem rpow_le_mul_of_ge {N τ η : ℝ} (hN : 0 < N) (hη : N ^ (-1 + τ) ≤ η) : N ^ τ ≤ N * η := by
  rw [← mul_rpow_neg_one_add (τ := τ) hN]
  exact mul_le_mul_of_nonneg_left hη hN.le

/-- `budSimp ≤ 6 N^{-τ/4}` in the window. -/
theorem budSimp_le {N τ η : ℝ} (hN : 1 ≤ N) (hη : N ^ (-1 + τ) ≤ η) :
    budSimp N (τ / 4) η ≤ 6 * N ^ (-(τ / 4)) := by
  have hN0 : 0 < N := by linarith
  have h1 := rpow_le_mul_of_ge hN0 hη
  have h2 : N ^ (τ / 2) ≤ Real.sqrt (N * η) := by
    rw [← sqrt_rpow_eq hN0]
    exact Real.sqrt_le_sqrt h1
  have h3 : 0 < N ^ (τ / 2) := Real.rpow_pos_of_pos hN0 _
  unfold budSimp
  calc 6 * N ^ (τ / 4) / Real.sqrt (N * η) ≤ 6 * N ^ (τ / 4) / N ^ (τ / 2) :=
        div_le_div_of_nonneg_left (by positivity) h3 h2
    _ = 6 * N ^ (-(τ / 4)) := by
        rw [mul_div_assoc, ← Real.rpow_sub hN0]
        congr 2; ring

/-- The step of the mesh: `2h/(η η') ≤ 2 N^{-τ/4}` for `η, η' ≥ N^{-1+τ}`. -/
theorem jump_le {N τ η η' : ℝ} (hN : 1 ≤ N) (hτ : 0 < τ) (hτ8 : τ ≤ 8) (hη : N ^ (-1 + τ) ≤ η)
    (hη' : N ^ (-1 + τ) ≤ η') : 2 * glMesh N / (η * η') ≤ 2 * N ^ (-(τ / 4)) := by
  have hN0 : 0 < N := by linarith
  have hlow : N⁻¹ ≤ η := (inv_le_rpow_neg_one_add hN hτ.le).trans hη
  have hlow' : N⁻¹ ≤ η' := (inv_le_rpow_neg_one_add hN hτ.le).trans hη'
  have hinv : 0 < N⁻¹ := by positivity
  have hprod : N⁻¹ * N⁻¹ ≤ η * η' := mul_le_mul hlow hlow' hinv.le (hinv.le.trans hlow)
  have hs : N⁻¹ ^ 2 ≤ N ^ (-(τ / 4)) := by
    have : N⁻¹ ^ 2 ≤ N ^ (-(τ / 4)) := by
      have h1 : N⁻¹ ^ 2 = N ^ ((-2 : ℝ)) := by
        rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hN0.le]; norm_num
      rw [h1]
      exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    exact this
  have hpos : 0 < N⁻¹ * N⁻¹ := by positivity
  unfold glMesh
  rw [div_le_iff₀ (lt_of_lt_of_le hpos hprod)]
  have h4 : (N ^ 4)⁻¹ = N⁻¹ ^ 4 := by rw [inv_pow]
  have h5 : 2 * (N ^ 4)⁻¹ ≤ 2 * N ^ (-(τ / 4)) * (N⁻¹ * N⁻¹) := by
    rw [h4]
    have : N⁻¹ ^ 4 = N⁻¹ ^ 2 * (N⁻¹ * N⁻¹) := by ring
    rw [this]
    nlinarith [hpos, hs]
  calc 2 * (N ^ 4)⁻¹ ≤ 2 * N ^ (-(τ / 4)) * (N⁻¹ * N⁻¹) := h5
    _ ≤ 2 * N ^ (-(τ / 4)) * (η * η') :=
        mul_le_mul_of_nonneg_left hprod (by positivity)

/-- The interpolation error: `4h/η² ≤ 13/√(N η)` in the window. -/
theorem interp_le {N τ η : ℝ} (hN : 1 ≤ N) (hτ : 0 < τ) (hη : N ^ (-1 + τ) ≤ η) (hη10 : η ≤ 10) :
    4 * glMesh N / (η * η) ≤ 13 / Real.sqrt (N * η) := by
  have hN0 : 0 < N := by linarith
  have hlow : N⁻¹ ≤ η := (inv_le_rpow_neg_one_add hN hτ.le).trans hη
  have hinv : 0 < N⁻¹ := by positivity
  have hη0 : 0 < η := lt_of_lt_of_le hinv hlow
  have hNη : 0 < N * η := by positivity
  have hsq : Real.sqrt (N * η) ≤ 3.2 * N := by
    calc Real.sqrt (N * η) ≤ Real.sqrt (N * 10) := Real.sqrt_le_sqrt (by nlinarith)
      _ = Real.sqrt N * Real.sqrt 10 := by rw [Real.sqrt_mul hN0.le]
      _ ≤ N * 3.2 := by
          have hs10 : Real.sqrt 10 ≤ 3.2 := by
            rw [Real.sqrt_le_left (by norm_num)]; norm_num
          have hsN : Real.sqrt N ≤ N := by
            calc Real.sqrt N ≤ Real.sqrt (N * N) := Real.sqrt_le_sqrt (by nlinarith)
              _ = N := Real.sqrt_mul_self hN0.le
          exact mul_le_mul hsN hs10 (Real.sqrt_nonneg _) hN0.le
      _ = 3.2 * N := by ring
  have hSpos : 0 < Real.sqrt (N * η) := Real.sqrt_pos.2 hNη
  rw [div_le_div_iff₀ (mul_pos hη0 hη0) hSpos]
  unfold glMesh
  have h1 : 4 * (N ^ 4)⁻¹ * Real.sqrt (N * η) ≤ 4 * (N ^ 4)⁻¹ * (3.2 * N) :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have h2 : N⁻¹ * N⁻¹ ≤ η * η := mul_le_mul hlow hlow hinv.le hη0.le
  have h3 : 13 * (N⁻¹ * N⁻¹) ≤ 13 * (η * η) := by linarith
  have h4 : 4 * (N ^ 4)⁻¹ * (3.2 * N) ≤ 13 * (N⁻¹ * N⁻¹) := by
    have e : 4 * (N ^ 4)⁻¹ * (3.2 * N) = 12.8 * N⁻¹ ^ 3 := by
      field_simp
      ring
    rw [e]
    have : N⁻¹ ^ 3 ≤ N⁻¹ ^ 2 := pow_le_pow_of_le_one hinv.le (inv_le_one_of_one_le₀ hN) (by norm_num)
    nlinarith [this, show N⁻¹ * N⁻¹ = N⁻¹ ^ 2 by ring]
  linarith


private theorem rpow_neg_one_add_le_one {N τ : ℝ} (hN : 1 ≤ N) (hτ : τ ≤ 1) : N ^ (-1 + τ) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)

/-- The grid has at most `N^9` points (`N ≥ 55`). -/
theorem card_glPts_le {N κ τ : ℝ} (hN : 55 ≤ N) (hκ : 0 < κ) (hκ2 : κ ≤ 2) (hτ : τ ≤ 1) :
    ((glPts N κ τ).card : ℝ) ≤ N ^ 9 := by
  have hN0 : 0 < N := by linarith
  have hh := glMesh_pos hN0
  have hcard : (glPts N κ τ).card ≤ (glJ N κ + 1) * (glK N τ + 1) := by
    unfold glPts
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_product, Finset.card_range, Finset.card_range]
  have hN4 : (1 : ℝ) ≤ N ^ 4 := one_le_pow₀ (by linarith)
  have hinv : N ^ 4 * glMesh N = 1 := by
    unfold glMesh; field_simp
  have hJ : (glJ N κ : ℝ) ≤ 4 * N ^ 4 := by
    have h1 : (glJ N κ : ℝ) ≤ 2 * (2 - κ) / glMesh N :=
      Nat.floor_le (div_nonneg (by linarith) hh.le)
    have h2 : 2 * (2 - κ) / glMesh N ≤ 4 * N ^ 4 := by
      rw [div_le_iff₀ hh]
      nlinarith [pow_pos hN0 4]
    exact h1.trans h2
  have hK : (glK N τ : ℝ) ≤ 10 * N ^ 4 := by
    have h0 : 0 ≤ N ^ (-1 + τ) := Real.rpow_nonneg hN0.le _
    have h1 : (glK N τ : ℝ) ≤ (10 - N ^ (-1 + τ)) / glMesh N :=
      Nat.floor_le (div_nonneg (by linarith [rpow_neg_one_add_le_one (by linarith : 1 ≤ N) hτ]) hh.le)
    have h2 : (10 - N ^ (-1 + τ)) / glMesh N ≤ 10 * N ^ 4 := by
      rw [div_le_iff₀ hh]
      nlinarith [pow_pos hN0 4]
    exact h1.trans h2
  have hprod : ((glJ N κ + 1 : ℕ) : ℝ) * ((glK N τ + 1 : ℕ) : ℝ) ≤ N ^ 9 := by
    push_cast
    have e : (4 * N ^ 4 + 1) * (10 * N ^ 4 + 1) = 40 * N ^ 8 + 14 * N ^ 4 + 1 := by ring
    have h8 : N ^ 8 ≤ N ^ 9 / 55 := by
      rw [le_div_iff₀ (by norm_num)]
      have : N ^ 9 = N * N ^ 8 := by ring
      rw [this]
      nlinarith [pow_pos hN0 8]
    have h4 : N ^ 4 ≤ N ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h1 : (1 : ℝ) ≤ N ^ 8 := one_le_pow₀ (by linarith)
    calc ((glJ N κ : ℝ) + 1) * ((glK N τ : ℝ) + 1) ≤ (4 * N ^ 4 + 1) * (10 * N ^ 4 + 1) :=
          mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      _ = 40 * N ^ 8 + 14 * N ^ 4 + 1 := e
      _ ≤ 55 * N ^ 8 := by nlinarith
      _ ≤ N ^ 9 := by nlinarith
  calc ((glPts N κ τ).card : ℝ) ≤ (((glJ N κ + 1) * (glK N τ + 1) : ℕ) : ℝ) :=
        Nat.cast_le.2 hcard
    _ = ((glJ N κ + 1 : ℕ) : ℝ) * ((glK N τ + 1 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ N ^ 9 := hprod


/-- Smallness conditions (all true for `N` large, `s = N^{-τ/4}`): a conjunction `N55 ∧ h1 ∧ h2 ∧ h3`
(the four fields of the RBM2D `structure GlSmall` `:729`, in the same order; here a `def` on `Prop`). -/
def GlSmall (N κ τ : ℝ) : Prop :=
  55 ≤ N ∧ 6 * N ^ (-(τ / 4)) ≤ 1 / 4 ∧
    24 * N ^ (-(τ / 4)) / cGap κ + 2 * N ^ (-(τ / 4)) ≤ min (cGap κ / 2) (1 / 4) ∧
    24 * N ^ (τ / 4) / cGap κ + 13 ≤ N ^ τ

theorem budSimp_mono {N ε a b : ℝ} (hN : 0 < N) (ha : 0 < a) (hab : a ≤ b) :
    budSimp N ε b ≤ budSimp N ε a := by
  unfold budSimp
  apply div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.2 (by positivity))
  exact Real.sqrt_le_sqrt (by nlinarith)

/-- **The deterministic core of the GUE local law.**  On the event that the Schur errors are
within their budgets on the grid, `|m_N - m_sc| ≤ N^τ / √(N Im z)` on the whole window. -/
theorem gue_local_det [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {κ τ N : ℝ}
    (hκ : 0 < κ) (hκ2 : κ ≤ 2) (hτ : 0 < τ) (hτ2 : τ ≤ 1 / 2) (hs : GlSmall N κ τ)
    (hΓ : ∀ z ∈ glPts N κ τ, ∀ i, (stieltjesN H z).im ≤ 2 →
      ‖schurErr H z i‖ ≤ schurBud N (τ / 4) z) :
    ∀ z : ℂ, |z.re| ≤ 2 - κ → N ^ (-1 + τ) ≤ z.im → z.im ≤ 10 →
      ‖stieltjesN H z - msc z‖ ≤ N ^ τ / Real.sqrt (N * z.im) := by
  intro z hx hη1 hη2
  have hN1 : 1 ≤ N := by linarith [hs.1]
  have hN0 : 0 < N := by linarith
  have hc := cGap_pos hκ hκ2
  have hpowpos : 0 < N ^ (-1 + τ) := Real.rpow_pos_of_pos hN0 _
  have hτ10 : N ^ (-1 + τ) ≤ 10 := hη1.trans hη2
  have hη0 : 0 < z.im := lt_of_lt_of_le hpowpos hη1
  obtain ⟨j, k, hj, hk, hx0, hx1, hy0, hy1⟩ := exists_glPt hN0 hx hη1 hη2
  have hxj := glE_le hN0 hκ2 hj
  have hxabs : |glE N κ j| ≤ 2 - κ := abs_le.2 ⟨hxj.1, hxj.2⟩
  have hηmem : ∀ k' ≤ glK N τ, N ^ (-1 + τ) ≤ glEta N k' ∧ glEta N k' ≤ 10 :=
    fun k' hk' => glEta_mem hN0 hτ10 hk'
  have hone : ∀ k' ≤ glK N τ, 1 ≤ N * glEta N k' := fun k' hk' =>
    (one_le_rpow hN1 hτ.le).trans (rpow_le_mul_of_ge hN0 (hηmem k' hk').1)
  have hchain := chain_bound (H := H) hH hκ hκ2 hxabs (glMesh_pos hN0) (K := glK N τ)
    (η := glEta N) (fun k' => rfl)
    (fun k' hk' => lt_of_lt_of_le hpowpos (hηmem k' hk').1)
    (υ := fun k' => budSimp N (τ / 4) (glEta N k'))
    (fun k' hk' => (budSimp_le hN1 (hηmem k' hk').1).trans hs.2.1)
    (fun k' hk' i hmim => by
      have hmem : (⟨glE N κ j, glEta N k'⟩ : ℂ) ∈ glPts N κ τ :=
        Finset.mem_image.2 ⟨(j, k'), Finset.mem_product.2
          ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hj), Finset.mem_range.2 (Nat.lt_succ_of_le hk')⟩,
          rfl⟩
      exact (hΓ _ hmem i hmim).trans
        (schurBud_le hN1 (hone k' hk') (hηmem k' hk').2))
    (fun k' hk' => by
      have hb1 := budSimp_le hN1 (hηmem k' (Nat.le_of_succ_le hk')).1
      have hb2 := jump_le hN1 hτ (by linarith) (hηmem k' (Nat.le_of_succ_le hk')).1
        (hηmem (k' + 1) hk').1
      have hb3 : 4 * budSimp N (τ / 4) (glEta N k') / cGap κ
          ≤ 24 * N ^ (-(τ / 4)) / cGap κ := by
        apply div_le_div_of_nonneg_right _ hc.le
        linarith
      linarith [hs.2.2.1])
  have hg := hchain k hk
  -- the grid point and the target point
  set zg : ℂ := ⟨glE N κ j, glEta N k⟩ with hzg
  have hzgim : zg.im = glEta N k := rfl
  have hηk := hηmem k hk
  have hzg0 : 0 < zg.im := lt_of_lt_of_le hpowpos hηk.1
  have hdist : ‖z - zg‖ ≤ 2 * glMesh N := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (z - zg)
    have e1 : (z - zg).re = z.re - glE N κ j := by simp [hzg]
    have e2 : (z - zg).im = z.im - glEta N k := by simp [hzg]
    rw [e1, e2] at h1
    rw [abs_of_nonneg hx0, abs_of_nonpos (by linarith)] at h1
    linarith
  have hLm := norm_stieltjesN_sub_le hH hη0 hzg0
  have hLa := norm_msc_sub_le hη0 hzg0
  have hden : 0 < z.im * zg.im := mul_pos hη0 hzg0
  have hLm' : ‖stieltjesN H z - stieltjesN H zg‖ ≤ 2 * glMesh N / (z.im * zg.im) :=
    hLm.trans (div_le_div_of_nonneg_right hdist hden.le)
  have hLa' : ‖msc z - msc zg‖ ≤ 2 * glMesh N / (z.im * zg.im) :=
    hLa.trans (div_le_div_of_nonneg_right hdist hden.le)
  have hsplit : ‖stieltjesN H z - msc z‖ ≤ ‖stieltjesN H zg - msc zg‖
      + ‖stieltjesN H z - stieltjesN H zg‖ + ‖msc z - msc zg‖ := by
    have e : stieltjesN H z - msc z = (stieltjesN H zg - msc zg)
        + (stieltjesN H z - stieltjesN H zg) - (msc z - msc zg) := by ring
    rw [e]
    calc ‖(stieltjesN H zg - msc zg) + (stieltjesN H z - stieltjesN H zg) - (msc z - msc zg)‖
        ≤ ‖(stieltjesN H zg - msc zg) + (stieltjesN H z - stieltjesN H zg)‖ + ‖msc z - msc zg‖ :=
          norm_sub_le _ _
      _ ≤ ‖stieltjesN H zg - msc zg‖ + ‖stieltjesN H z - stieltjesN H zg‖ + ‖msc z - msc zg‖ := by
          gcongr; exact norm_add_le _ _
  -- the interpolation error and the grid value, against `N^τ / √(N η)`
  have hint : 4 * glMesh N / (z.im * z.im) ≤ 13 / Real.sqrt (N * z.im) :=
    interp_le hN1 hτ hη1 hη2
  have hint2 : 2 * glMesh N / (z.im * zg.im) + 2 * glMesh N / (z.im * zg.im)
      ≤ 4 * glMesh N / (z.im * z.im) := by
    have : 2 * glMesh N / (z.im * zg.im) ≤ 2 * glMesh N / (z.im * z.im) :=
      div_le_div_of_nonneg_left (by have := glMesh_pos hN0; positivity) (mul_pos hη0 hη0)
        (mul_le_mul_of_nonneg_left (by linarith) hη0.le)
    have e : 4 * glMesh N / (z.im * z.im) = 2 * glMesh N / (z.im * z.im) + 2 * glMesh N / (z.im * z.im) := by
      ring
    rw [e]; linarith
  have hS : 0 < Real.sqrt (N * z.im) := Real.sqrt_pos.2 (by positivity)
  have hmono := budSimp_mono (ε := τ / 4) hN0 hη0
    (by linarith : z.im ≤ glEta N k)
  have hbud : 4 * budSimp N (τ / 4) z.im / cGap κ
      = 24 * N ^ (τ / 4) / cGap κ / Real.sqrt (N * z.im) := by
    unfold budSimp
    field_simp
    ring
  have hgrid : 4 * budSimp N (τ / 4) (glEta N k) / cGap κ
      ≤ 24 * N ^ (τ / 4) / cGap κ / Real.sqrt (N * z.im) := by
    rw [← hbud]
    exact div_le_div_of_nonneg_right (by linarith) hc.le
  calc ‖stieltjesN H z - msc z‖
      ≤ ‖stieltjesN H zg - msc zg‖ + ‖stieltjesN H z - stieltjesN H zg‖ + ‖msc z - msc zg‖ :=
        hsplit
    _ ≤ 24 * N ^ (τ / 4) / cGap κ / Real.sqrt (N * z.im)
          + (2 * glMesh N / (z.im * zg.im) + 2 * glMesh N / (z.im * zg.im)) := by
        linarith
    _ ≤ 24 * N ^ (τ / 4) / cGap κ / Real.sqrt (N * z.im) + 13 / Real.sqrt (N * z.im) := by
        linarith
    _ = (24 * N ^ (τ / 4) / cGap κ + 13) / Real.sqrt (N * z.im) := by ring
    _ ≤ N ^ τ / Real.sqrt (N * z.im) := div_le_div_of_nonneg_right hs.2.2.2 hS.le


/-- The smallness conditions hold for `N` large. -/
theorem glSmall_eventually {κ τ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) (hτ : 0 < τ) {N : ℕ → ℝ}
    (hN : Tendsto N atTop atTop) : ∀ᶠ n in atTop, GlSmall (N n) κ τ := by
  have hc := cGap_pos hκ hκ2
  set c := cGap κ with hcdef
  have hr : 0 < min (c / 2) (1 / 4) := lt_min (by positivity) (by norm_num)
  have hs0 : Tendsto (fun n => N n ^ (-(τ / 4))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by positivity : 0 < τ / 4)).comp hN
  have e1 : ∀ᶠ n in atTop, 6 * N n ^ (-(τ / 4)) ≤ 1 / 4 := by
    have := (hs0.const_mul 6).eventually (gt_mem_nhds (by norm_num : (6 : ℝ) * 0 < 1 / 4))
    exact this.mono fun n hn => hn.le
  have e2 : ∀ᶠ n in atTop, 24 * N n ^ (-(τ / 4)) / c + 2 * N n ^ (-(τ / 4)) ≤ min (c / 2) (1 / 4) := by
    have hf : Tendsto (fun n => 24 * N n ^ (-(τ / 4)) / c + 2 * N n ^ (-(τ / 4))) atTop (𝓝 0) := by
      have := ((hs0.const_mul 24).div_const c).add (hs0.const_mul 2)
      simpa using this
    exact (hf.eventually (gt_mem_nhds hr)).mono fun n hn => hn.le
  have e3 : ∀ᶠ n in atTop, 24 / c + 13 ≤ N n ^ (3 * τ / 4) := by
    have : Tendsto (fun n => N n ^ (3 * τ / 4)) atTop atTop :=
      (tendsto_rpow_atTop (by positivity : 0 < 3 * τ / 4)).comp hN
    exact this.eventually_ge_atTop _
  filter_upwards [hN.eventually_ge_atTop 55, e1, e2, e3] with n h55 h1 h2 h3
  refine ⟨h55, h1, h2, ?_⟩
  have hN0 : 0 < N n := by linarith
  have hp : 1 ≤ N n ^ (τ / 4) := one_le_rpow (by linarith) (by positivity)
  have hsplit : N n ^ τ = N n ^ (τ / 4) * N n ^ (3 * τ / 4) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  rw [hsplit]
  calc 24 * N n ^ (τ / 4) / c + 13 ≤ N n ^ (τ / 4) * (24 / c + 13) := by
        have : 24 * N n ^ (τ / 4) / c = N n ^ (τ / 4) * (24 / c) := by ring
        rw [this]; nlinarith [div_pos (by norm_num : (0 : ℝ) < 24) hc]
    _ ≤ N n ^ (τ / 4) * N n ^ (3 * τ / 4) :=
        mul_le_mul_of_nonneg_left h3 (by linarith)



/-! ### The pin `UNGUESchurTail` and the assembly of `UNGUELocal` -/

section Assembly

private theorem GUELocalBootstrap_one_le_size {d : ℕ} (sz : Sizes d) (n : ℕ) : (1 : ℝ) ≤ Nsz sz n := by
  have h : 0 < sz.size n := by
    have := sz.three_le_L n
    have := sz.W_pos n
    simp only [Sizes.size]
    positivity
  exact_mod_cast h

/-- **Pin `UNGUESchurTail` (the probabilistic input of the GUE local law)**: for the `N × N` GUE,
`N = (W L)^d`, and every deterministic set `Γ_n` of at most `N^q` points of the window `|Re z| ≤ 2 - κ`,
`N^{-1+τ} ≤ Im z ≤ 10`, with probability `≥ 1 - N^{-D}` simultaneously for all `z ∈ Γ_n` and all rows `i`:
the Schur error `Υ_i(z) = G_ii⁻¹ + z + m_N(z)` of the self-consistent equation is at most
`N^ε (N^{-1/2} + (2/(N Im z))^{1/2} + (N Im z)⁻¹)` whenever `Im m_N(z) ≤ 2`.
Registry class: **owed** (T2244, UN-09; proved by UN-10 `GUELocalSchur`).  Dimension-free (only `N`).
Route (RBM2D `GUELocalBootstrap.lean:897-907`, row L1): Schur complement `G_ii⁻¹ = h_ii - z - h^* G^{(i)} h`,
the diagonal Gaussian tail `|h_ii| ≺ N^{-1/2}`, the quadratic Gaussian chaos (Hanson–Wright), the Ward
identity `∑_{kl}|G^{(i)}_{kl}|² = Im tr G^{(i)}/η`, `|tr G - tr G^{(i)}| ≤ 1/η`, and a union bound over
`Γ_n × rows`.  RBM2D `GUELocalBootstrap.lean:908` (`GUESchurTail`). -/
def UNGUESchurTail : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ sz : Sizes d, Tendsto (fun n => sz.size n) atTop atTop →
  ∀ κ τ ε D : ℝ, 0 < κ → 0 < τ → 0 < ε → 0 < D → ∀ q : ℕ, ∀ Γ : ℕ → Finset ℂ,
    (∀ n, ∀ z ∈ Γ n, |z.re| ≤ 2 - κ ∧ Nsz sz n ^ (-1 + τ) ≤ z.im ∧ z.im ≤ 10) →
    (∀ᶠ n in atTop, (((Γ n).card : ℕ) : ℝ) ≤ Nsz sz n ^ q) →
    ∀ᶠ n in atTop, gueP d (sz.L n) (sz.W n)
        {ω | ∃ z ∈ Γ n, ∃ i : Idx d (sz.L n) (sz.W n),
          (stieltjesN (Xmat d (sz.L n) (sz.W n) ω) z).im ≤ 2 ∧
            schurBud (Nsz sz n) ε z < ‖schurErr (Xmat d (sz.L n) (sz.W n) ω) z i‖} ≤
      ENNReal.ofReal (Nsz sz n ^ (-D))

/-- The grid of the window lies in the window (every `n`). -/
theorem glPts_mem {d : ℕ} (sz : Sizes d) {κ τ : ℝ} (hκ2 : κ ≤ 2) (hτ1 : τ ≤ 1) (n : ℕ) :
    ∀ z ∈ glPts (Nsz sz n) κ τ,
      |z.re| ≤ 2 - κ ∧ Nsz sz n ^ (-1 + τ) ≤ z.im ∧ z.im ≤ 10 := by
  intro z hz
  have hN1 := GUELocalBootstrap_one_le_size sz n
  have hN0 : 0 < Nsz sz n := by linarith
  have hτ10 : Nsz sz n ^ (-1 + τ) ≤ 10 :=
    (rpow_neg_one_add_le_one hN1 hτ1).trans (by norm_num)
  obtain ⟨⟨j, k⟩, hjk, rfl⟩ := Finset.mem_image.1 hz
  obtain ⟨hj, hk⟩ := Finset.mem_product.1 hjk
  have hj' : j ≤ glJ (Nsz sz n) κ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have hk' : k ≤ glK (Nsz sz n) τ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  have h1 := glE_le hN0 hκ2 hj'
  have h2 := glEta_mem hN0 hτ10 hk'
  exact ⟨abs_le.2 ⟨h1.1, h1.2⟩, h2.1, h2.2⟩

/-- The grid has at most `N^9` points, eventually. -/
theorem glPts_card {d : ℕ} (sz : Sizes d) (hd : Tendsto (fun n => sz.size n) atTop atTop) {κ τ : ℝ}
    (hκ : 0 < κ) (hκ2 : κ ≤ 2) (hτ1 : τ ≤ 1) :
    ∀ᶠ n in atTop, (((glPts (Nsz sz n) κ τ).card : ℕ) : ℝ) ≤ Nsz sz n ^ 9 :=
  ((tendsto_natCast_atTop_atTop.comp hd).eventually_ge_atTop 55).mono fun _ hn =>
    card_glPts_le hn hκ hκ2 hτ1

/-- **The GUE local law from the Schur tail** (deterministic bootstrap; RBM2D `GUELocal_of_tail`,
`GUELocalBootstrap.lean:944`): the merged owed pin `UNGUELocal` from the new owed pin `UNGUESchurTail`. -/
theorem un_gueLocal_of_tail (h : UNGUESchurTail) : UNGUELocal := by
  intro d hd sz hsz κ τ D hκ hτ hD
  set κ' : ℝ := min κ 2 with hκ'def
  set τ' : ℝ := min τ (1 / 2) with hτ'def
  have hκ' : 0 < κ' := lt_min hκ (by norm_num)
  have hκ2 : κ' ≤ 2 := min_le_right _ _
  have hτ' : 0 < τ' := lt_min hτ (by norm_num)
  have hτ2 : τ' ≤ 1 / 2 := min_le_right _ _
  have hNr : Tendsto (fun n => Nsz sz n) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsz
  have hT := h d hd sz hsz κ' τ' (τ' / 4) D hκ' hτ' (by positivity) hD 9
    (fun n => glPts (Nsz sz n) κ' τ') (glPts_mem sz hκ2 (by linarith))
    (glPts_card sz hsz hκ' hκ2 (by linarith))
  have hsm := glSmall_eventually hκ' hκ2 hτ' hNr
  filter_upwards [hT, hsm] with n hTn hsmn
  refine le_trans (measure_mono ?_) hTn
  intro ω hω
  obtain ⟨z, hx, hη1, hη2, hbad⟩ := hω
  by_contra hnot
  have hΓ : ∀ w ∈ glPts (Nsz sz n) κ' τ', ∀ i,
      (stieltjesN (Xmat d (sz.L n) (sz.W n) ω) w).im ≤ 2 →
        ‖schurErr (Xmat d (sz.L n) (sz.W n) ω) w i‖ ≤ schurBud (Nsz sz n) (τ' / 4) w := by
    intro w hw i hi
    by_contra hlt
    push Not at hlt
    exact hnot ⟨w, hw, i, hi, hlt⟩
  have hN1 := GUELocalBootstrap_one_le_size sz n
  have : Nonempty (Idx d (sz.L n) (sz.W n)) := by
    rw [← Fintype.card_pos_iff, Sizes.card_Idx]
    exact_mod_cast lt_of_lt_of_le one_pos (by exact_mod_cast hN1)
  have hdet := gue_local_det (Xmat_isHermitian d (sz.L n) (sz.W n) ω) hκ' hκ2 hτ' hτ2 hsmn hΓ z
    (hx.trans (by linarith [min_le_left κ 2, show κ' = min κ 2 from rfl]))
    (le_trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [min_le_left τ (1 / 2)])) hη1) hη2
  have hpow : Nsz sz n ^ τ' ≤ Nsz sz n ^ τ :=
    Real.rpow_le_rpow_of_exponent_le hN1 (min_le_left _ _)
  have hS : 0 ≤ Real.sqrt (Nsz sz n * z.im) := Real.sqrt_nonneg _
  have : Nsz sz n ^ τ / Real.sqrt (Nsz sz n * z.im)
      < ‖stieltjesN (Xmat d (sz.L n) (sz.W n) ω) z - msc z‖ := hbad
  have h2 : Nsz sz n ^ τ' / Real.sqrt (Nsz sz n * z.im)
      ≤ Nsz sz n ^ τ / Real.sqrt (Nsz sz n * z.im) :=
    div_le_div_of_nonneg_right hpow hS
  linarith

end Assembly

end GUELocalBootstrap

/-! ## Compiled nonempty instances (target 5; DECISIONS §56)

Data: `d = 3`, `sz0` (`L n = 4 (n + 1)`, `W n = (2 (n + 1))^5`, `N_0 = 2097152`,
`N_n = 2097152 (n + 1)^18`), `κ = 1`, `τ = 1/10`, `ε = τ/4 = 1/40`, `D = 2`, `q = 9`.  The pin
`UNGUESchurTail` stays a hypothesis (UN-10 proves it); every deterministic hypothesis is discharged.
The smallness `GlSmall` holds eventually (`inst_glSmall`) and at the concrete `N = 10^80`
(`inst_glSmall_witness`); the conclusions are eventual in `n`. -/

namespace GUELocalBootstrapInst

open RBM.Gauss.SizesInst

/-- **Instance of the pin `UNGUESchurTail`** at `sz0`: `κ = 1`, `τ = 1/10`, `ε = 1/40`, `D = 2`, `q = 9`,
with the grid `Γ_n = glPts N 1 (1/10)` of the window (membership by `glPts_mem`, cardinality by
`glPts_card`). -/
theorem inst_schurTail (h : UNGUESchurTail) :
    ∀ᶠ n in atTop, gueP 3 (sz0.L n) (sz0.W n)
      {ω | ∃ z ∈ glPts (Nsz sz0 n) 1 (1 / 10), ∃ i : Idx 3 (sz0.L n) (sz0.W n),
        (stieltjesN (Xmat 3 (sz0.L n) (sz0.W n) ω) z).im ≤ 2 ∧
          schurBud (Nsz sz0 n) (1 / 40) z <
            ‖schurErr (Xmat 3 (sz0.L n) (sz0.W n) ω) z i‖} ≤
      ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) :=
  h 3 le_rfl sz0 Step1RegularityGUEInst.inst_sz0_size_tendsto 1 (1 / 10) (1 / 40) 2 one_pos
    (by norm_num) (by norm_num) (by norm_num) 9 (fun n => glPts (Nsz sz0 n) 1 (1 / 10))
    (glPts_mem sz0 (by norm_num) (by norm_num))
    (glPts_card sz0 Step1RegularityGUEInst.inst_sz0_size_tendsto one_pos (by norm_num) (by norm_num))

/-- The scale at `n = 0` of `sz0` is `N = 2097152 = card (Idx 3 4 32)` (`card_Idx_sz0`). -/
theorem inst_Nsz_zero : Nsz sz0 0 = 2097152 := by
  have h := sz0_values.2.2.1
  simp only [Nsz, h]
  norm_num

/-- The grid at `n = 0` of `sz0` (`N = 2097152`) is nonempty (the pin is not vacuous). -/
theorem inst_grid_nonempty : (glPts (2097152 : ℝ) 1 (1 / 10)).Nonempty :=
  ⟨⟨glE 2097152 1 0, glEta 2097152 0⟩, Finset.mem_image.2 ⟨(0, 0), by simp, rfl⟩⟩

/-- The grid of the instance at `n = 0` is `glPts (Nsz sz0 0) 1 (1/10)`, nonempty. -/
theorem inst_grid_nonempty_sz0 : (glPts (Nsz sz0 0) 1 (1 / 10)).Nonempty := by
  rw [inst_Nsz_zero]; exact inst_grid_nonempty

/-- The smallness conditions of the bootstrap hold eventually along `sz0`. -/
theorem inst_glSmall : ∀ᶠ n in atTop, GlSmall (Nsz sz0 n) 1 (1 / 10) :=
  glSmall_eventually one_pos (by norm_num) (by norm_num)
    (tendsto_natCast_atTop_atTop.comp Step1RegularityGUEInst.inst_sz0_size_tendsto)

/-- **`un_gueLocal_of_tail` at the instance**: `sz0`, `κ = 1`, `τ = 1/10`, `D = 2`. -/
theorem inst_gueLocal (h : UNGUESchurTail) :
    ∀ᶠ n in atTop, gueP 3 (sz0.L n) (sz0.W n)
      {ω | ∃ z : ℂ, |z.re| ≤ 2 - 1 ∧ Nsz sz0 n ^ (-1 + 1 / 10 : ℝ) ≤ z.im ∧ z.im ≤ 10 ∧
          Nsz sz0 n ^ (1 / 10 : ℝ) / Real.sqrt (Nsz sz0 n * z.im) <
            ‖stieltjesN (Xmat 3 (sz0.L n) (sz0.W n) ω) z - msc z‖} ≤
      ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) :=
  un_gueLocal_of_tail h 3 le_rfl sz0 Step1RegularityGUEInst.inst_sz0_size_tendsto 1 (1 / 10) 2
    one_pos (by norm_num) (by norm_num)

/-- **Deterministic nonvacuity of `gue_local_det`**: `GlSmall` holds at the concrete `N = 10^80`,
`κ = 1`, `τ = 1/10` (`N^{τ/4} = 100`, `cGap 1 = √3 ≥ 1.7`: h1 `0.06 ≤ 0.25`, h2 `≤ 0.17 ≤ 0.25`,
h3 `≤ 1425 ≤ 10^8`). -/
theorem inst_glSmall_witness : GlSmall ((10 : ℝ) ^ (80 : ℕ)) 1 (1 / 10) := by
  have e1 : ((10 : ℝ) ^ (80 : ℕ)) ^ (-((1 / 10 : ℝ) / 4)) = 1 / 100 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      show ((80 : ℕ) : ℝ) * (-((1 / 10 : ℝ) / 4)) = -(2 : ℝ) by norm_num,
      Real.rpow_neg (by norm_num)]
    norm_num
  have e2 : ((10 : ℝ) ^ (80 : ℕ)) ^ ((1 / 10 : ℝ) / 4) = 100 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      show ((80 : ℕ) : ℝ) * ((1 / 10 : ℝ) / 4) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have e3 : ((10 : ℝ) ^ (80 : ℕ)) ^ (1 / 10 : ℝ) = 10 ^ 8 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      show ((80 : ℕ) : ℝ) * (1 / 10 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hc : (1.7 : ℝ) ≤ cGap 1 := by
    unfold cGap
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hc0 : (0 : ℝ) < cGap 1 := by linarith
  have hdiv : 24 * (1 / 100 : ℝ) / cGap 1 ≤ 24 * (1 / 100 : ℝ) / 1.7 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
  have hdiv3 : 24 * (100 : ℝ) / cGap 1 ≤ 24 * (100 : ℝ) / 1.7 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · rw [e1]; norm_num
  · rw [e1]
    have hA : 24 * (1 / 100 : ℝ) / 1.7 + 2 * (1 / 100) ≤ 1 / 4 := by norm_num
    exact le_min (by linarith) (by linarith)
  · rw [e2, e3]
    have hB : 24 * (100 : ℝ) / 1.7 + 13 ≤ 10 ^ 8 := by norm_num
    linarith

/-! ### Concrete applications of the other targets (nondegenerate data; `N = 10^80`, `z = i`, `H = 0` on `Unit`) -/

example : 1 < ‖msc Complex.I + Complex.I‖ := norm_msc_add_z_gt_one (by simp)

example : Complex.I.im ≤ ‖msc Complex.I + Complex.I‖ := im_le_norm_msc_add_z (by simp)

example : ‖msc Complex.I‖ ≤ (Complex.I.im)⁻¹ := norm_msc_le_inv_im (by simp)

example : (2 * msc Complex.I + Complex.I) ^ 2 = Complex.I ^ 2 - 4 := msc_disc_sq Complex.I

example : Real.sqrt (1 * (4 - 1)) ≤ ‖2 * msc 0 + 0‖ :=
  sqrt_le_norm_two_msc_add_z one_pos (by norm_num)

example : Complex.I.im ≤ ‖2 * msc Complex.I + Complex.I‖ := im_le_norm_two_msc_add_z (by simp)

example : ‖msc Complex.I - msc (2 * Complex.I)‖ ≤ ‖Complex.I - 2 * Complex.I‖ / (Complex.I.im * (2 * Complex.I).im) :=
  norm_msc_sub_le (by simp) (by simp)

example : ‖stieltjesN (0 : Matrix Unit Unit ℂ) Complex.I‖ ≤ (Complex.I.im)⁻¹ :=
  norm_stieltjesN_le Matrix.isHermitian_zero (by simp)

example : ‖stieltjesN (0 : Matrix Unit Unit ℂ) Complex.I - stieltjesN (0 : Matrix Unit Unit ℂ) (2 * Complex.I)‖ ≤
    ‖Complex.I - 2 * Complex.I‖ / (Complex.I.im * (2 * Complex.I).im) :=
  norm_stieltjesN_sub_le Matrix.isHermitian_zero (by simp) (by simp)

example : stieltjesN (0 : Matrix Unit Unit ℂ) Complex.I * (Complex.I + stieltjesN (0 : Matrix Unit Unit ℂ) Complex.I) + 1 =
    (Fintype.card Unit : ℂ)⁻¹ * ∑ i, schurErr (0 : Matrix Unit Unit ℂ) Complex.I i * green (0 : Matrix Unit Unit ℂ) Complex.I i i :=
  sc_residual Matrix.isHermitian_zero (by simp)

example : schurBud 2 (1 / 40) ⟨0, 10⟩ ≤ budSimp 2 (1 / 40) 10 :=
  schurBud_le (by norm_num) (by change (1 : ℝ) ≤ 2 * 10; norm_num) (by change (10 : ℝ) ≤ 10; norm_num)

example : 4 * glMesh ((10 : ℝ) ^ (80 : ℕ)) / (10 * 10) ≤ 13 / Real.sqrt ((10 : ℝ) ^ (80 : ℕ) * 10) :=
  interp_le (τ := 1 / 10) (by norm_num) (by norm_num) (by
    have : ((10 : ℝ) ^ (80 : ℕ)) ^ (-1 + 1 / 10 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    linarith) le_rfl

example : ((glPts ((10 : ℝ) ^ (80 : ℕ)) 1 (1 / 10)).card : ℝ) ≤ ((10 : ℝ) ^ (80 : ℕ)) ^ 9 :=
  card_glPts_le (by norm_num) one_pos (by norm_num) (by norm_num)

private theorem GUELocalBootstrap_green_zero_unit {z : ℂ} (hz : z ≠ 0) (i j : Unit) :
    green (0 : Matrix Unit Unit ℂ) z i j = -z⁻¹ := by
  have h : ((-z⁻¹) • (1 : Matrix Unit Unit ℂ)) * ((0 : Matrix Unit Unit ℂ) - z • 1) = 1 := by
    rw [zero_sub, Matrix.mul_neg, Matrix.smul_mul, Matrix.one_mul, smul_smul]
    rw [show -z⁻¹ * z = -1 by field_simp, neg_one_smul, neg_neg]
  unfold green
  rw [Matrix.inv_eq_left_inv h]
  simp

private theorem GUELocalBootstrap_stieltjesN_zero_unit {z : ℂ} (hz : z ≠ 0) :
    stieltjesN (0 : Matrix Unit Unit ℂ) z = -z⁻¹ := by
  unfold stieltjesN
  rw [show RBM.Gauss.Gres (0 : Matrix Unit Unit ℂ) z true = green 0 z by
    simp only [green, RBM.Gauss.Gres, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]]
  simp [Matrix.trace, GUELocalBootstrap_green_zero_unit hz]

private theorem GUELocalBootstrap_schurErr_zero_unit {z : ℂ} (hz : z ≠ 0) (i : Unit) :
    schurErr (0 : Matrix Unit Unit ℂ) z i = -z⁻¹ := by
  unfold schurErr
  rw [GUELocalBootstrap_green_zero_unit hz, GUELocalBootstrap_stieltjesN_zero_unit hz]
  rw [inv_neg, inv_inv]; ring

private theorem GUELocalBootstrap_norm_schurErr_zero_unit {η : ℝ} (hη : 0 < η) (i : Unit) :
    ‖schurErr (0 : Matrix Unit Unit ℂ) ⟨0, η⟩ i‖ = 1 / η := by
  have hz : (⟨0, η⟩ : ℂ) = (η : ℂ) * Complex.I := Complex.ext (by simp) (by simp)
  have hz0 : (⟨0, η⟩ : ℂ) ≠ 0 := by
    intro h0; have := congrArg Complex.im h0; simp at this; linarith
  rw [GUELocalBootstrap_schurErr_zero_unit hz0, norm_neg, norm_inv, hz, norm_mul,
    Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη, one_div]

/-- `sc_stability` at `z = i`, `m = m_sc(i) + 1/2`, `c = 1 = Im i`. -/
example : ‖(msc Complex.I + 1 / 2) - msc Complex.I‖ ≤
    2 * ‖(msc Complex.I + 1 / 2) * (Complex.I + (msc Complex.I + 1 / 2)) + 1‖ / 1 :=
  sc_stability one_pos (by simpa using im_le_norm_two_msc_add_z (z := Complex.I) (by simp)) le_rfl
    (by norm_num)

private theorem GUELocalBootstrap_near_zero_unit :
    ‖stieltjesN (0 : Matrix Unit Unit ℂ) ⟨0, 10⟩ - msc ⟨0, 10⟩‖ ≤ 1 / 5 := by
  have h1 := norm_stieltjesN_le (H := (0 : Matrix Unit Unit ℂ)) Matrix.isHermitian_zero
    (z := ⟨0, 10⟩) (by norm_num)
  have h2 := norm_msc_le_inv_im (z := ⟨0, 10⟩) (by norm_num)
  have h3 := norm_sub_le (stieltjesN (0 : Matrix Unit Unit ℂ) ⟨0, 10⟩) (msc ⟨0, 10⟩)
  simp only at h1 h2
  linarith [show (10 : ℝ)⁻¹ = 1 / 10 by norm_num]

/-- `norm_green_diag_le_two` at `H = 0` on `Unit`, `z = 10 i`: `Υ = m_N = -z⁻¹`, `|Υ| = 1/10`. -/
example : ‖green (0 : Matrix Unit Unit ℂ) ⟨0, 10⟩ () ()‖ ≤ 2 :=
  norm_green_diag_le_two Matrix.isHermitian_zero (by norm_num) ()
    (by rw [GUELocalBootstrap_norm_schurErr_zero_unit (by norm_num)]; norm_num)
    (GUELocalBootstrap_near_zero_unit.trans (by norm_num))

/-- `sc_one_step` at `H = 0` on `Unit`, `z = 10 i`, `c = 10 = Im z`, `υ = 1/10`. -/
example : ‖stieltjesN (0 : Matrix Unit Unit ℂ) ⟨0, 10⟩ - msc ⟨0, 10⟩‖ ≤ 4 * (1 / 10) / 10 :=
  sc_one_step Matrix.isHermitian_zero (by norm_num) (by norm_num)
    (im_le_norm_two_msc_add_z (z := ⟨0, 10⟩) (by norm_num)) (by norm_num)
    (fun i => by rw [GUELocalBootstrap_norm_schurErr_zero_unit (by norm_num)])
    (GUELocalBootstrap_near_zero_unit.trans (by norm_num))

private theorem GUELocalBootstrap_cGap_two : cGap 2 = 2 := by
  unfold cGap
  rw [show (2 : ℝ) * (4 - 2) = 2 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- `chain_bound` at `H = 0` on `Unit`, `x = 0`, `κ = 2` (`cGap 2 = 2`), `h = 1`, `K = 1`,
`η k = 10 - k`, `υ k = 1/(10 - k)`; step `k = 0`: `4 (1/10)/2 + 2/90 ≤ 1/4`. -/
example : ∀ k : ℕ, k ≤ 1 →
    ‖stieltjesN (0 : Matrix Unit Unit ℂ) ⟨0, 10 - (k : ℝ) * 1⟩ - msc ⟨0, 10 - (k : ℝ) * 1⟩‖ ≤
      4 * (1 / (10 - (k : ℝ) * 1)) / cGap 2 := by
  have hk1 : ∀ k : ℕ, k ≤ 1 → (k : ℝ) ≤ 1 := fun k hk => by exact_mod_cast hk
  refine chain_bound (H := (0 : Matrix Unit Unit ℂ)) Matrix.isHermitian_zero (κ := 2) (by norm_num)
    le_rfl (x := 0) (by norm_num) (h := 1) one_pos (K := 1) (η := fun k => 10 - k * 1)
    (fun _ => rfl) (fun k hk => by have := hk1 k hk; linarith)
    (υ := fun k => 1 / (10 - k * 1)) (fun k hk => ?_) (fun k hk i _ => ?_) (fun k hk => ?_)
  · have := hk1 k hk
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  · have := hk1 k hk
    rw [GUELocalBootstrap_norm_schurErr_zero_unit (by linarith)]
  · obtain rfl : k = 0 := by omega
    simp only [GUELocalBootstrap_cGap_two]
    norm_num

/-- `exists_glPt` at `N = 2097152`, `κ = 1`, `τ = 1/10`, `z = i`. -/
example : ∃ j k : ℕ, j ≤ glJ (2097152 : ℝ) 1 ∧ k ≤ glK (2097152 : ℝ) (1 / 10) ∧
    0 ≤ Complex.I.re - glE 2097152 1 j ∧ Complex.I.re - glE 2097152 1 j ≤ glMesh 2097152 ∧
    0 ≤ glEta 2097152 k - Complex.I.im ∧ glEta 2097152 k - Complex.I.im ≤ glMesh 2097152 :=
  exists_glPt (by norm_num) (by simp)
    (by rw [Complex.I_im]; exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num))
    (by rw [Complex.I_im]; norm_num)

/-- **`gue_local_det` at the matched scale** `N = Nsz sz0 n = card (Idx 3 (sz0.L n) (sz0.W n))`,
`H = Xmat 3 (sz0.L n) (sz0.W n) ω`, `κ = 1`, `τ = 1/10`: from the pin `UNGUESchurTail` (kept as a
hypothesis, UN-10), eventually in `n` there is a sample point `ω` off the event of `inst_schurTail`
(measure `≤ N^{-2} < 1`), at which `hΓ` holds; `GlSmall` from `inst_glSmall`. -/
example (h : UNGUESchurTail) :
    ∀ᶠ n in atTop, ∃ ω : Ω 3 (sz0.L n) (sz0.W n), ∀ z : ℂ, |z.re| ≤ 2 - 1 →
      Nsz sz0 n ^ (-1 + 1 / 10 : ℝ) ≤ z.im → z.im ≤ 10 →
      ‖stieltjesN (Xmat 3 (sz0.L n) (sz0.W n) ω) z - msc z‖ ≤
        Nsz sz0 n ^ (1 / 10 : ℝ) / Real.sqrt (Nsz sz0 n * z.im) := by
  filter_upwards [inst_schurTail h, inst_glSmall] with n hT hs
  have hN : (1 : ℝ) < Nsz sz0 n := by linarith [hs.1]
  have hlt : ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) < 1 :=
    ENNReal.ofReal_lt_one.2 (Real.rpow_lt_one_of_one_lt_of_neg hN (by norm_num))
  have key : ∀ S : Set (Ω 3 (sz0.L n) (sz0.W n)),
      gueP 3 (sz0.L n) (sz0.W n) S ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) → ∃ ω, ω ∉ S :=
    fun S hS => (Set.ne_univ_iff_exists_notMem S).1 fun hU => by
      rw [hU, measure_univ] at hS
      exact lt_irrefl _ (hS.trans_lt hlt)
  obtain ⟨ω, hω⟩ := key _ hT
  refine ⟨ω, ?_⟩
  have : Nonempty (Idx 3 (sz0.L n) (sz0.W n)) := ⟨0⟩
  refine gue_local_det (Xmat_isHermitian 3 _ _ ω) one_pos (by norm_num) (by norm_num) (by norm_num)
    hs ?_
  intro z hz i hi
  by_contra hlt'
  refine hω ?_
  rw [Set.mem_ofPred_eq]
  rw [show (1 / 10 : ℝ) / 4 = 1 / 40 by norm_num] at hlt'
  exact ⟨z, hz, i, hi, not_le.1 hlt'⟩

end GUELocalBootstrapInst

end RBM.Univ
