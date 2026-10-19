/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.Step1Boot
import RBM3D.Induction.Continuity
import RBM3D.Induction.Step1Setup

/-!
# The block Anderson analogue of `Induction/Step1Setup` and of the net layer of `Induction/Continuity`

Paper: Step 1 of the proof of Theorem 8.2 (`lem:main_ind_BA`), which is the same as in [RBSO1D, Section 7.1] (Truong-Yang-Yin, arXiv:2503.11382); Lemma 8.4
(`lem_GbEXP_BA`); `(def_G0)` (2.33) and `M` in Lemma 8.3 (`lem:propM`); band source: Step 1 of the proof of Theorem 2.24 (`lem:main_ind`).
Namespace `RBM.BA`.  Used by `BA/Step1Prime`.

The private helpers are copies of the band lemmas of `Induction/Step1Setup` (`S1Std`, `s1_gexRHS_le`, `s1_wl_det`),
`Induction/Continuity` (`cont_entry_diff`, `contWord`, `cont_word_norm`, `cont_word_diff`, `cont_loopFine_eq`, `cont_loopAbs_diff`,
`cont_one_add_pow_le`, `cont_LP_zeta_ratio`, `cont_LP_low`, `cont_WL_low`, `cont_LP_eventually`, `cont_eta_inv_le`, `cont_LP_close`,
`cont_WL_close`, `gopbound`, `step1NetLift`) and `Induction/Step1` (`s1x_continuousOn`).

* section 1: `baS1Std` (the band standing hypotheses at the dummy energy `E ≡ 0`);
* section 2: `baG_continuousOn`;
* section 3: the resolvent moduli along the block Anderson flow and `baGopbound`;
* section 4: `baNetLift`;
* section 5: private facts.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The standing hypotheses `S1Std` along a block Anderson window (dummy energy) -/

section Std

/-- `Im m(z, g) ≤ 1` for `Im z ≥ 0` (`BAself_norm_le_one` when `(self_m)` has a solution, `m = 0` otherwise). -/
private theorem BASetup_BAm_im_le_one (d L : ℕ) [NeZero L] (g : ℝ) (z : ℂ) (hz : 0 ≤ z.im) :
    (BAm d L g z).im ≤ 1 := by
  by_cases h : ∃ m, BASelf d L g z m
  · have hs := BAm_spec h
    exact (Complex.im_le_norm _).trans (BAself_norm_le_one d L g z _ hz hs)
  · have h0 : BAm d L g z = 0 := by
      unfold BAm
      simp [h]
    rw [h0]
    simp

/-- `baS1Std`: the band standing hypotheses `S1Std` (`Induction/Step1Setup`) at the dummy
energy `E ≡ 0` and the bulk constant `min κ 1` hold along a block Anderson window `0 ≤ s ≤ t ≤ t₀(z)`.  The only
energy field of `S1Std` is `hE : |E n| ≤ 2 - κ'`, which reads `0 ≤ 2 - min κ 1` at `E ≡ 0`; no scale fact
(`s1_F3`-`s1_F8`, `s1_B_pos`, `s1_hsize`, `s1_Wd_le_Bctl`, ...) reads it.  `τ = ε/2`:
`1 - t ≥ 1 - t₀ = Im z/(Im m + Im z) ≥ Im z/2 ≥ N^{-1+ε}/2 ≥ N^{-1+ε/2}` eventually (`Im m ≤ |m| ≤ 1`,
`BAm_spec`, `BAself_norm_le_one`). -/
theorem baS1Std (d : ℕ) :
    ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
      ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 1 / 100 →
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
          ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
            STConStInd sz 𝔠d s t →
            RBM.Ind.S1Std sz (min κ 1) 𝔠 𝔡 (ε / 2) 𝔠d (fun _ => 0) s t := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠d h𝔠d h𝔠d' 𝔠 sz z hflow s t hs0 hst htT hC
  have hA := hflow.1
  have hN0 : ∀ n, (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.one_le_size n
  have hT1 : ∀ n, BAflowT0 sz z n < 1 := fun n => (BAflow_T0_bounds hκ hflow n).2.2.2
  have ht1 : ∀ n, t n < 1 := fun n => lt_of_le_of_lt (htT n) (hT1 n)
  refine ⟨lt_min hκ one_pos, fun n => ?_, hA.1, hA.2.1, half_pos hε, h𝔠d, h𝔠d', hs0, hst, ht1,
    hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2, hC, ?_⟩
  · simp only [abs_zero]
    have := min_le_right κ 1
    linarith
  · have hN := sz.tendsto_size hA.2.2.1
    filter_upwards [hN.eventually (eventually_le_rpow 2 (half_pos hε))] with n hn
    obtain ⟨-, hz1, hz2⟩ := hflow.2 n
    obtain ⟨hzpos, hmpos, -, -⟩ := BAflow_T0_bounds hκ hflow n
    have hm1 := BASetup_BAm_im_le_one d (sz.L n) (sz.lam n) (z n) hzpos.le
    set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
    have hNpos : 0 < N := hN0 n
    have hsplit : N ^ (-1 + ε) = N ^ (-1 + ε / 2) * N ^ (ε / 2) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    have hpos : 0 ≤ N ^ (-1 + ε / 2) := Real.rpow_nonneg hNpos.le _
    have h5 : N ^ (-1 + ε / 2) * 2 ≤ N ^ (-1 + ε) := by
      rw [hsplit]
      exact mul_le_mul_of_nonneg_left hn hpos
    set m : ℝ := (BAm d (sz.L n) (sz.lam n) (z n)).im with hmdef
    set zi : ℝ := (z n).im with hzidef
    have hT : BAflowT0 sz z n = m / (m + zi) := rfl
    have hden : 0 < m + zi := by linarith
    have h1t : zi / 2 ≤ 1 - BAflowT0 sz z n := by
      rw [hT, show 1 - m / (m + zi) = zi / (m + zi) by field_simp; ring, le_div_iff₀ hden]
      nlinarith
    change N ^ (-1 + ε / 2) ≤ 1 - t n
    linarith [htT n]

end Std

/-! ## 2. Time continuity of `v ↦ (G_v - M)_{xy}` -/

section Cont

variable {d : ℕ}

/-- The flow matrix `H_u = g₀ Ψ + √u X` is Hermitian (`g₀` real). -/
private theorem BASetup_herm (sz : Sizes d) (lam0 : ℕ → ℝ) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) :
    (sz.seqHflowBA lam0 n u ω).IsHermitian := by
  unfold Sizes.seqHflowBA
  refine IsHermitian.add ?_ (Sizes.seqHflow_isHermitian (sz.withLam 0) n u ω)
  unfold IsHermitian
  rw [conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
    show star (lam0 n : ℂ) = (lam0 n : ℂ) from Complex.conj_ofReal _]

/-- `u ↦ H_u(ω)` is continuous (entrywise `g₀ Ψ_{ij} + √u X_{ij}`). -/
private theorem BASetup_continuous_H (sz : Sizes d) (lam0 : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ) :
    Continuous fun v : ℝ => sz.seqHflowBA lam0 n v ω := by
  refine continuous_matrix fun i j => ?_
  unfold Sizes.seqHflowBA
  simp only [Matrix.add_apply, Matrix.of_apply]
  exact continuous_const.add (Sizes.continuous_seqHflow_entry_time (sz.withLam 0) n ω i j)

/-- `baG_continuousOn`: `v ↦ (G_v - M)_{xy}` of the block Anderson carrier is continuous on
`[a, b]`, `b < 1`, for every sample (the band `s1x_continuousOn`, `Induction/Step1`: `continuous_green_of_isHermitian_moving`
for the clamped path `z(min(v, b))`; `Im z_v = (1 - v) Im m > 0`, `H_v = g₀ Ψ + √v X` Hermitian). -/
theorem baG_continuousOn (d : ℕ) :
    ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ), 0 < (BAmF sz lam0 E n).im →
      ∀ a b : ℝ, b < 1 → ∀ (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)),
        ContinuousOn (fun v : ℝ => (baFM sz lam0 E).GM n v ω x y) (Set.Icc a b) := by
  intro sz lam0 E n hm a b hb ω x y
  set z : ℝ → ℂ := fun v => ztOf (BAmF sz lam0 E n) (E n) (min v b) with hz
  have hzc : Continuous z := by
    simp only [hz, ztOf]
    exact continuous_const.add ((continuous_const.sub
      (Complex.continuous_ofReal.comp (continuous_id.min continuous_const))).mul continuous_const)
  have hzi : ∀ v, (z v).im ≠ 0 := by
    intro v
    simp only [hz, ztOf_im, etaOf]
    have : 0 < 1 - min v b := by
      have := min_le_right v b
      linarith
    exact (mul_pos this hm).ne'
  have hcont := continuous_green_of_isHermitian_moving (BASetup_continuous_H sz lam0 n ω)
    (fun v => BASetup_herm sz lam0 n v ω) hzc hzi
  have hfun : Continuous fun v : ℝ =>
      Gres (sz.seqHflowBA lam0 n v ω) (z v) true x y - BAMfine sz lam0 E n x y :=
    (hcont.matrix_elem x y).sub continuous_const
  refine hfun.continuousOn.congr fun v hv => ?_
  change BAGt sz lam0 E n v ω x y - BAMfine sz lam0 E n x y = _
  simp only [BAGt, hz, min_eq_left hv.2]

end Cont

/-! ## 3. The resolvent moduli along the block Anderson flow and `baGopbound` -/

section Moduli

open scoped Matrix.Norms.L2Operator

open RBM.Ind RBM.Ind.ContinuityNet

variable {d : ℕ}

/-- The entry modulus of the resolvent (the band `cont_entry_diff`, `Induction/Continuity`, for two arbitrary
Hermitian matrices with `H - H' = c X`): `‖X‖ ≤ Xb`, `|c| ≤ √Δ`, `Δ ≤ 1`, `η ≤ |Im z|, |Im z'|`, `η⁻¹ ≤ Q`,
`‖z - z'‖ ≤ Δ` give `‖(G(H, z) - G(H', z'))_{ij}‖ ≤ Q² (Xb + 1) √Δ`. -/
private theorem BASetup_entry_diff {ι : Type*} [Fintype ι] [DecidableEq ι] {H H' X : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian) {c : ℝ} (hd : H - H' = (c : ℂ) • X) {Xb Δ : ℝ}
    (hX : ‖X‖ ≤ Xb) (hc : |c| ≤ Real.sqrt Δ) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1) {z z' : ℂ} {η Q : ℝ}
    (hη : 0 < η) (hQ : η⁻¹ ≤ Q) (hz : η ≤ |z.im|) (hz' : η ≤ |z'.im|) (hzz : ‖z - z'‖ ≤ Δ)
    (i j : ι) :
    ‖Gres H z true i j - Gres H' z' true i j‖ ≤ Q * Q * (Xb + 1) * Real.sqrt Δ := by
  have hG := cont_green_flow_diff hH hH' hd hX hc hΔ0 hΔ1 hη hQ hz hz' hzz
  have hent := norm_matrix_entry_le_opNorm (green H z - green H' z') i j
  have h3 : (green H z - green H' z') i j = Gres H z true i j - Gres H' z' true i j := by
    rw [cont_Gres_true_eq_green, cont_Gres_true_eq_green]
    rfl
  rw [h3] at hent
  exact hent.trans hG

/-- `H_u - H_{u'} = (√u - √u') X` for the block Anderson flow: the deterministic part `g₀ Ψ` cancels. -/
private theorem BASetup_H_sub (sz : Sizes d) (lam0 : ℕ → ℝ) (n : ℕ) (u u' : ℝ) (ω : sz.SeqΩ) :
    sz.seqHflowBA lam0 n u ω - sz.seqHflowBA lam0 n u' ω =
      ((Real.sqrt u - Real.sqrt u' : ℝ) : ℂ) • sz.seqXmat n ω := by
  ext i j
  have h1 : ∀ v : ℝ, sz.seqHflowBA lam0 n v ω i j =
      (lam0 n : ℂ) * PsiI d (sz.L n) (sz.W n) i j + (Real.sqrt v : ℂ) * sz.seqXmat n ω i j := fun v => rfl
  rw [Matrix.sub_apply, h1, h1, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- `‖z_u - z_{u'}‖ ≤ |u - u'|` for `z_u = E + (1 - u) m`, `|m| ≤ 1`. -/
private theorem BASetup_zdiff (m : ℂ) (E u u' : ℝ) (hm : ‖m‖ ≤ 1) :
    ‖ztOf m E u - ztOf m E u'‖ ≤ |u - u'| := by
  have h : ztOf m E u - ztOf m E u' = ((u' - u : ℝ) : ℂ) * m := by
    unfold ztOf
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  exact mul_le_of_le_one_right (abs_nonneg _) hm

/-- `η_t ≤ |Im z_u|` for `u ≤ t < 1` and `Im m ≥ 0` (`Im z_u = (1 - u) Im m`; the band `cont_eta_le_abs_im`,
`Induction/ContinuityNet`). -/
private theorem BASetup_eta_le (m : ℂ) (E : ℝ) {t u : ℝ} (hm : 0 ≤ m.im) (ht : t < 1) (hut : u ≤ t) :
    etaOf m t ≤ |(ztOf m E u).im| := by
  rw [ztOf_im, etaOf, etaOf, abs_of_nonneg (mul_nonneg (by linarith) hm)]
  exact mul_le_mul_of_nonneg_right (by linarith) hm

/-- `baGopbound`: the time-Lipschitz bound of `BAGt` w.h.p. under the block Anderson law (the block
Anderson form of `GopboundPin`, `Induction/ContinuityNet`; the band `gopbound`, `Induction/Continuity`).
`C' = 2C + 10`.  On the good event `‖X‖ ≤ 2N²` (`contGood (sz.withLam 0)`), `H_u - H_{u'} = (√u - √u') X`, `z_u - z_{u'}
= (u' - u) m`, `‖G_u‖ ≤ ((1 - u) Im m)⁻¹ ≤ N/κ` for `u ≤ 1 - N⁻¹`, so
`‖G_u - G_{u'}‖_{max} ≤ (N/κ)² (2N² + 1) |u-u'|^{1/2} ≤ 3 κ⁻² N⁴ N^{-C'/2} = 3 κ⁻² N^{-1} N^{-C} ≤ N^{-C}` once `N ≥ 3 κ⁻²`. -/
theorem baGopbound (d : ℕ) :
    ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (κ : ℝ), 0 < κ → (∀ n, κ ≤ (BAmF sz lam0 E n).im) →
      (∀ n, ‖BAmF sz lam0 E n‖ ≤ 1) → sz.SizeTendsto →
      ∀ C > (0 : ℝ), ∃ C' > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
        Sizes.seqP (sz.withLam 0) {ω | ∃ u u' : ℝ, 0 ≤ u ∧ 0 ≤ u' ∧
            u ≤ 1 - ((sz.size n : ℕ) : ℝ)⁻¹ ∧ u' ≤ 1 - ((sz.size n : ℕ) : ℝ)⁻¹ ∧
            |u - u'| ≤ ((sz.size n : ℕ) : ℝ) ^ (-C') ∧
            ∃ x y : Idx d (sz.L n) (sz.W n),
              ((sz.size n : ℕ) : ℝ) ^ (-C) < ‖BAGt sz lam0 E n u ω x y - BAGt sz lam0 E n u' ω x y‖} ≤
          ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
  intro sz lam0 E κ hκ hmκ hm1 hsize C hC
  refine ⟨2 * C + 10, by linarith, fun D hD => ?_⟩
  have hcast : Tendsto (fun n : ℕ => ((sz.size n : ℕ) : ℝ)) atTop atTop := hsize
  filter_upwards [hcast.eventually_ge_atTop (max 3 (3 * (κ⁻¹) ^ 2)),
    hcast.eventually (cont_eventually_tail D)] with n hn htail
  have h3 : (3 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := (le_max_left _ _).trans hn
  have hK3 : 3 * (κ⁻¹) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) := (le_max_right _ _).trans hn
  refine le_trans (measure_mono ?_)
    ((cont_good_compl (sz.withLam 0) n).trans (ENNReal.ofReal_le_ofReal htail))
  rintro ω ⟨u, u', hu0, hu'0, hut, hu't, hΔ, i, j, hbad⟩
  by_contra hng
  have hmem : ω ∈ contGood (sz.withLam 0) n := not_not.1 hng
  have hgood : ∀ c : CoordF d (sz.L n) (sz.W n), |ω ⟨n, c⟩| ≤ ((sz.size n : ℕ) : ℝ) := fun c => hmem c
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hNi : 0 < N⁻¹ := inv_pos.2 hN0
  have hNi1 : N⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN1
  have hK0 : 0 < κ⁻¹ := inv_pos.2 hκ
  have hΔ1 : |u - u'| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hm0 : 0 ≤ (BAmF sz lam0 E n).im := (hκ.trans_le (hmκ n)).le
  set η : ℝ := κ * N⁻¹ with hηdef
  have hη : 0 < η := by positivity
  have hQ : η⁻¹ ≤ N * κ⁻¹ := by
    rw [hηdef, mul_inv, inv_inv, mul_comm]
  have hz : ∀ v : ℝ, 0 ≤ v → v ≤ 1 - N⁻¹ → η ≤ |(ztOf (BAmF sz lam0 E n) (E n) v).im| := by
    intro v hv0 hv1
    rw [ztOf_im, etaOf, abs_of_nonneg (mul_nonneg (by linarith) hm0), hηdef]
    calc κ * N⁻¹ ≤ (BAmF sz lam0 E n).im * (1 - v) :=
          mul_le_mul (hmκ n) (by linarith) hNi.le hm0
      _ = (1 - v) * (BAmF sz lam0 E n).im := mul_comm _ _
  have hcardI : (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) = N := by
    rw [sz.card_Idx n]
  have hX : ‖sz.seqXmat n ω‖ ≤ 2 * N ^ 2 := by
    have h := cont_norm_Xmat_le (sz.slice n ω) hgood
    rw [hcardI] at h
    change ‖Xmat d (sz.L n) (sz.W n) (sz.slice n ω)‖ ≤ _ at h
    change ‖Xmat d (sz.L n) (sz.W n) (sz.slice n ω)‖ ≤ _
    linarith
  have key := BASetup_entry_diff (BASetup_herm sz lam0 n u ω) (BASetup_herm sz lam0 n u' ω)
    (BASetup_H_sub sz lam0 n u u' ω) hX (cont_abs_sqrt_sub_sqrt_le hu0 hu'0) (abs_nonneg _) hΔ1
    hη hQ (hz u hu0 hut) (hz u' hu'0 hu't) (BASetup_zdiff _ _ u u' (hm1 n)) i j
  have hsq : Real.sqrt |u - u'| ≤ N ^ (-(2 * C + 10) / 2) := cont_sqrt_abs_le hN0.le hΔ
  have hQ2 : (N * κ⁻¹) * (N * κ⁻¹) * (2 * N ^ 2 + 1) ≤ (3 * (κ⁻¹) ^ 2) * N ^ 4 := by
    have : N ^ 2 ≤ N ^ 4 := pow_le_pow_right₀ hN1 (by norm_num)
    have h2 : (N * κ⁻¹) * (N * κ⁻¹) * (2 * N ^ 2 + 1) = (κ⁻¹) ^ 2 * (2 * N ^ 4 + N ^ 2) := by ring
    rw [h2]
    nlinarith [sq_nonneg κ⁻¹, mul_nonneg (sq_nonneg κ⁻¹) (sub_nonneg.2 this)]
  have hexp : (3 * (κ⁻¹) ^ 2) * N ^ 4 * N ^ (-(2 * C + 10) / 2) ≤ N ^ (-C) := by
    have e1 : N ^ 4 * N ^ (-(2 * C + 10) / 2) = N ^ (-C) * N⁻¹ := by
      rw [cont_pow_mul_rpow hN0 4 _, ← Real.rpow_neg_one, ← Real.rpow_add hN0]
      congr 1
      push_cast
      ring
    have hp : 0 ≤ N ^ (-C) := Real.rpow_nonneg hN0.le _
    calc (3 * (κ⁻¹) ^ 2) * N ^ 4 * N ^ (-(2 * C + 10) / 2)
        = (3 * (κ⁻¹) ^ 2) * (N ^ 4 * N ^ (-(2 * C + 10) / 2)) := by ring
      _ = ((3 * (κ⁻¹) ^ 2) * N⁻¹) * N ^ (-C) := by rw [e1]; ring
      _ ≤ 1 * N ^ (-C) := by
          refine mul_le_mul_of_nonneg_right ?_ hp
          rw [← div_eq_mul_inv, div_le_one hN0]
          exact hK3
      _ = N ^ (-C) := one_mul _
  have hfin : ‖BAGt sz lam0 E n u ω i j - BAGt sz lam0 E n u' ω i j‖ ≤ N ^ (-C) :=
    key.trans ((mul_le_mul (hQ2.trans' le_rfl) hsq (Real.sqrt_nonneg _) (by positivity)).trans hexp)
  exact absurd hbad (not_lt.2 hfin)

end Moduli

/-! ## 4. The net lift of the two Step 1 families of the block Anderson carrier

The band `Step1NetLift`/`step1NetLift` (`Induction/Continuity`) at `baFM sz lam0 E`, law `seqP (sz.withLam 0)`;
the bulk premise `|E| ≤ 2 - κ` is replaced by `κ ≤ Im m`, `|m| ≤ 1`, and the energy-bound helpers `cont_bulk`,
`cont_eta_le_abs_im`, `cont_norm_spectralZ_sub`, `cont_eta_inv_le` by `BASetup_eta_le`, `BASetup_zdiff`,
`BASetup_eta_inv_le`.  The private scalar helpers of `Induction/Continuity` are copied with the prefix `BASetup_`. -/

section Words

open scoped Matrix.Norms.L2Operator

open RBM.Ind RBM.Ind.ContinuityNet

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The resolvent word `∏ᵢ G(σᵢ) E_{aᵢ}` over a list of `(σᵢ, aᵢ)` (`contWord`, `Induction/Continuity`). -/
private noncomputable def BASetup_word (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (l : List (Bool × Zd d L)) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1

omit [NeZero W] in
/-- `contWord_cons` of `Induction/Continuity`. -/
private theorem BASetup_word_cons (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (p : Bool × Zd d L) (l : List (Bool × Zd d L)) :
    BASetup_word H z (p :: l) = Gres H z p.1 * Eblk d L W p.2 * BASetup_word H z l := rfl

/-- `cont_word_norm` of `Induction/Continuity`. -/
private theorem BASetup_word_norm (hW : 1 ≤ W) {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    {z : ℂ} {Q : ℝ} (hQ : ∀ σ, ‖Gres H z σ‖ ≤ Q) (l : List (Bool × Zd d L)) :
    ‖BASetup_word H z l‖ ≤ Q ^ l.length := by
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hQ true)
  induction l with
  | nil => simp [BASetup_word]
  | cons p l ih =>
    have hEa := cont_norm_Eblk_le_one (d := d) (L := L) hW p.2
    rw [BASetup_word_cons, List.length_cons, pow_succ]
    calc ‖Gres H z p.1 * Eblk d L W p.2 * BASetup_word H z l‖
        ≤ ‖Gres H z p.1‖ * ‖Eblk d L W p.2‖ * ‖BASetup_word H z l‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ Q * 1 * Q ^ l.length :=
          mul_le_mul (mul_le_mul (hQ _) hEa (norm_nonneg _) hQ0) ih (norm_nonneg _) (by positivity)
      _ = Q ^ l.length * Q := by ring

/-- The `k`-fold telescoping of a resolvent word (`cont_word_diff`, `Induction/Continuity`). -/
private theorem BASetup_word_diff (hW : 1 ≤ W)
    {H H' : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z z' : ℂ} {Q S : ℝ} (hQ1 : 1 ≤ Q)
    (hQ : ∀ σ, ‖Gres H z σ‖ ≤ Q) (hQ' : ∀ σ, ‖Gres H' z' σ‖ ≤ Q)
    (hS : ∀ σ, ‖Gres H z σ - Gres H' z' σ‖ ≤ S) (l : List (Bool × Zd d L)) :
    ‖BASetup_word H z l - BASetup_word H' z' l‖ ≤ (l.length : ℝ) * Q ^ l.length * S := by
  have hQ0 : 0 ≤ Q := by linarith
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS true)
  induction l with
  | nil => simp [BASetup_word]
  | cons p l ih =>
    have hEa := cont_norm_Eblk_le_one (d := d) (L := L) hW p.2
    rw [BASetup_word_cons, BASetup_word_cons]
    have key : Gres H z p.1 * Eblk d L W p.2 * BASetup_word H z l -
        Gres H' z' p.1 * Eblk d L W p.2 * BASetup_word H' z' l =
        (Gres H z p.1 - Gres H' z' p.1) * Eblk d L W p.2 * BASetup_word H z l +
          Gres H' z' p.1 * Eblk d L W p.2 * (BASetup_word H z l - BASetup_word H' z' l) := by
      noncomm_ring
    rw [key]
    have hP := BASetup_word_norm hW hQ l
    have t1 : ‖(Gres H z p.1 - Gres H' z' p.1) * Eblk d L W p.2 * BASetup_word H z l‖ ≤
        S * 1 * Q ^ l.length := by
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul (hS _) hEa (norm_nonneg _) hS0)) hP
        (norm_nonneg _) (by positivity)
    have t2 : ‖Gres H' z' p.1 * Eblk d L W p.2 * (BASetup_word H z l - BASetup_word H' z' l)‖ ≤
        Q * 1 * ((l.length : ℝ) * Q ^ l.length * S) := by
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul (hQ' _) hEa (norm_nonneg _) hQ0)) ih
        (norm_nonneg _) (by positivity)
    have hpos : 0 ≤ S * Q ^ l.length * (Q - 1) :=
      mul_nonneg (mul_nonneg hS0 (pow_nonneg hQ0 _)) (sub_nonneg.2 hQ1)
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ S * 1 * Q ^ l.length + Q * 1 * ((l.length : ℝ) * Q ^ l.length * S) := add_le_add t1 t2
      _ ≤ (((p :: l).length : ℕ) : ℝ) * Q ^ (p :: l).length * S := by
        rw [List.length_cons, pow_succ]
        push_cast
        nlinarith [hpos]

/-- The loop `loopFine` is the trace of the word of the block matrix (`cont_loopFine_eq`, `Induction/Continuity`). -/
private theorem BASetup_loopFine_eq (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    loopFine d L W H z σ a =
      Matrix.trace (BASetup_word (blockMat d L W H) z ((List.ofFn σ).zip (List.ofFn a))) := by
  unfold loopFine
  rw [loopM_eq_loopL]
  rfl

/-- The modulus of a loop of length `k` for two Hermitian matrices with `H - H' = c X` (the band `cont_loopAbs_diff`,
`Induction/Continuity`, with `Hflow`, `zt E u` replaced by the flow matrices `H`, `H'` and spectral parameters `z`, `z'`;
the trace is bounded by `card(Vtx) · ‖·‖`). -/
private theorem BASetup_loopAbs_diff (hW : 1 ≤ W) {H H' X : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian) {c : ℝ} (hd : H - H' = (c : ℂ) • X)
    {z z' : ℂ} {η Q Xb Δ : ℝ} (hη : 0 < η) (hQ1 : 1 ≤ Q) (hQ : η⁻¹ ≤ Q) (hz : η ≤ |z.im|)
    (hz' : η ≤ |z'.im|) (hzz : ‖z - z'‖ ≤ Δ) (hc : |c| ≤ Real.sqrt Δ) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1)
    (hXb : ‖blockMat d L W X‖ ≤ Xb) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    |‖loopFine d L W H z σ a‖ - ‖loopFine d L W H' z' σ a‖| ≤
      (Fintype.card (Vtx d L W) : ℝ) *
        ((k : ℝ) * Q ^ k * (Q * Q * (Xb + 1) * Real.sqrt Δ)) := by
  have hHu : (blockMat d L W H).IsHermitian := hH.submatrix _
  have hHu' : (blockMat d L W H').IsHermitian := hH'.submatrix _
  have hdb : blockMat d L W H - blockMat d L W H' = (c : ℂ) • blockMat d L W X := by
    rw [← cont_blockMat_sub, hd, cont_blockMat_smul]
  have hgt := cont_green_flow_diff hHu hHu' hdb hXb hc hΔ0 hΔ1 hη hQ hz hz' hzz
  have hgf : ‖green (blockMat d L W H) ((starRingEnd ℂ) z) -
      green (blockMat d L W H') ((starRingEnd ℂ) z')‖ ≤ Q * Q * (Xb + 1) * Real.sqrt Δ := by
    refine cont_green_flow_diff hHu hHu' hdb hXb hc hΔ0 hΔ1 hη hQ ?_ ?_ ?_
    · rw [Complex.conj_im, abs_neg]; exact hz
    · rw [Complex.conj_im, abs_neg]; exact hz'
    · rw [← map_sub, Complex.norm_conj]; exact hzz
  have hS : ∀ σ : Bool, ‖Gres (blockMat d L W H) z σ - Gres (blockMat d L W H') z' σ‖ ≤
      Q * Q * (Xb + 1) * Real.sqrt Δ := by
    intro σ
    cases σ
    · rw [cont_Gres_false_eq_green, cont_Gres_false_eq_green]; exact hgf
    · rw [cont_Gres_true_eq_green, cont_Gres_true_eq_green]; exact hgt
  have hGu : ∀ σ : Bool, ‖Gres (blockMat d L W H) z σ‖ ≤ Q := fun σ =>
    (norm_Gsig_le_inv_eta hHu hη hz σ).trans hQ
  have hGu' : ∀ σ : Bool, ‖Gres (blockMat d L W H') z' σ‖ ≤ Q := fun σ =>
    (norm_Gsig_le_inv_eta hHu' hη hz' σ).trans hQ
  have hw := BASetup_word_diff hW hQ1 hGu hGu' hS ((List.ofFn σ).zip (List.ofFn a))
  have hlen : ((List.ofFn σ).zip (List.ofFn a)).length = k := by simp
  rw [hlen] at hw
  rw [BASetup_loopFine_eq, BASetup_loopFine_eq]
  refine (abs_norm_sub_norm_le _ _).trans ?_
  rw [← Matrix.trace_sub]
  refine (norm_matrix_trace_le_card_mul _).trans ?_
  exact mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)

end Words

section Scalars

open RBM.Ind RBM.Ind.ContinuityNet

/-- `(1 + x)^m ≤ 1 + 2 m x` when `m x ≤ 1/2` (`cont_one_add_pow_le`, `Induction/Continuity`). -/
private theorem BASetup_one_add_pow_le {x : ℝ} (hx : 0 ≤ x) (m : ℕ) (hm : (m : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ m ≤ 1 + 2 * m * x := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hm ⊢
    have hm' : (m : ℝ) * x ≤ 1 / 2 := by nlinarith
    have h1 := ih hm'
    calc (1 + x) ^ (m + 1) = (1 + x) ^ m * (1 + x) := pow_succ _ _
      _ ≤ (1 + 2 * m * x) * (1 + x) := mul_le_mul_of_nonneg_right h1 (by linarith)
      _ ≤ 1 + 2 * ((m : ℝ) + 1) * x := by
          nlinarith [mul_nonneg hx (by linarith : (0 : ℝ) ≤ 1 - 2 * (m : ℝ) * x)]

/-- The control of `STStep1Loop` moves by at most a factor `2` under a small time change
(`cont_LP_zeta_ratio`, `Induction/Continuity`). -/
private theorem BASetup_LP_zeta_ratio {s t u u' x B : ℝ} (k : ℕ) (hB : 0 ≤ B) (hsu : s ≤ u)
    (hut : u ≤ t) (hu't : u' ≤ t) (ht : t < 1) (hx0 : 0 ≤ x)
    (hx : (1 - t)⁻¹ * |u - u'| ≤ x) (hk : ((k - 1 : ℕ) : ℝ) * x ≤ 1 / 2) :
    ((1 - s) / (1 - u')) ^ (k - 1) * B ^ (k - 1) ≤
      2 * (((1 - s) / (1 - u)) ^ (k - 1) * B ^ (k - 1)) := by
  have hu1 : u < 1 := lt_of_le_of_lt hut ht
  have hu'1 : u' < 1 := lt_of_le_of_lt hu't ht
  have hxu : 0 < 1 - u := by linarith
  have hxu' : 0 < 1 - u' := by linarith
  have hxs : 0 ≤ 1 - s := by linarith
  have hr0 : 0 ≤ (1 - s) / (1 - u) := div_nonneg hxs hxu.le
  have hr0' : 0 ≤ (1 - s) / (1 - u') := div_nonneg hxs hxu'.le
  have h1 := cont_inv_add_one_sub_ratio (γ := 0) le_rfl ht hu't hut
  rw [zero_add, zero_add, abs_sub_comm] at h1
  have hratio : (1 - s) / (1 - u') ≤ (1 + x) * ((1 - s) / (1 - u)) := by
    have h2 : (1 - u')⁻¹ ≤ (1 + x) * (1 - u)⁻¹ :=
      h1.trans (mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hxu.le))
    calc (1 - s) / (1 - u') = (1 - s) * (1 - u')⁻¹ := div_eq_mul_inv _ _
      _ ≤ (1 - s) * ((1 + x) * (1 - u)⁻¹) := mul_le_mul_of_nonneg_left h2 hxs
      _ = (1 + x) * ((1 - s) / (1 - u)) := by rw [div_eq_mul_inv]; ring
  have hA : ((1 - s) / (1 - u')) ^ (k - 1) ≤
      (1 + x) ^ (k - 1) * ((1 - s) / (1 - u)) ^ (k - 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hr0' hratio _
  have hpow : (1 + x) ^ (k - 1) ≤ 2 := by
    have := BASetup_one_add_pow_le hx0 (k - 1) hk
    nlinarith
  have hζ0 : 0 ≤ ((1 - s) / (1 - u)) ^ (k - 1) * B ^ (k - 1) := by positivity
  calc ((1 - s) / (1 - u')) ^ (k - 1) * B ^ (k - 1)
      ≤ ((1 + x) ^ (k - 1) * ((1 - s) / (1 - u)) ^ (k - 1)) * B ^ (k - 1) :=
        mul_le_mul_of_nonneg_right hA (by positivity)
    _ = (1 + x) ^ (k - 1) * (((1 - s) / (1 - u)) ^ (k - 1) * B ^ (k - 1)) := by ring
    _ ≤ 2 * (((1 - s) / (1 - u)) ^ (k - 1) * B ^ (k - 1)) :=
        mul_le_mul_of_nonneg_right hpow hζ0

/-- `ε ≤ ζ` for `STStep1Loop` (`cont_LP_low`, `Induction/Continuity`): `(1-s)/(1-u) ≥ 1` and `Bctl n s ≥ N⁻¹`. -/
private theorem BASetup_LP_low {d : ℕ} (sz : Sizes d) (n k : ℕ) {s u : ℝ} (hs0 : 0 ≤ s)
    (hsu : s ≤ u) (hu : u < 1) :
    ((((sz.size n : ℕ) : ℝ))⁻¹) ^ k ≤
      ((1 - s) / (1 - u)) ^ (k - 1) * (sz.Bctl n s) ^ (k - 1) := by
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hs1 : s < 1 := lt_of_le_of_lt hsu hu
  have hB := cont_inv_size_le_Bctl sz n hs0 hs1
  have hB0 : 0 ≤ ((sz.size n : ℕ) : ℝ)⁻¹ := inv_nonneg.2 (by linarith)
  have hr : 1 ≤ (1 - s) / (1 - u) := (one_le_div (by linarith)).2 (by linarith)
  have h1 : 1 ≤ ((1 - s) / (1 - u)) ^ (k - 1) := one_le_pow₀ hr
  have h2 : (((sz.size n : ℕ) : ℝ)⁻¹) ^ (k - 1) ≤ (sz.Bctl n s) ^ (k - 1) :=
    pow_le_pow_left₀ hB0 hB _
  have h3 : ((((sz.size n : ℕ) : ℝ))⁻¹) ^ k ≤ ((((sz.size n : ℕ) : ℝ))⁻¹) ^ (k - 1) :=
    pow_le_pow_of_le_one hB0 (inv_le_one_of_one_le₀ hN1) (Nat.sub_le k 1)
  calc ((((sz.size n : ℕ) : ℝ))⁻¹) ^ k ≤ ((((sz.size n : ℕ) : ℝ))⁻¹) ^ (k - 1) := h3
    _ ≤ (sz.Bctl n s) ^ (k - 1) := h2
    _ = 1 * (sz.Bctl n s) ^ (k - 1) := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 (pow_nonneg (hB0.trans hB) _)

/-- `ε ≤ ζ` for `STStep1Weak` (`cont_WL_low`, `Induction/Continuity`). -/
private theorem BASetup_WL_low {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu : u < 1) :
    ((((sz.size n : ℕ) : ℝ))⁻¹) ^ ((1 : ℝ) / 4) ≤ (sz.Bctl n u) ^ ((1 : ℝ) / 4) :=
  Real.rpow_le_rpow (inv_nonneg.2 (Nat.cast_nonneg _)) (cont_inv_size_le_Bctl sz n hu0 hu)
    (by norm_num)

/-- The eventual numerical facts for a fixed loop length `k`, in `N` (exponent `A = 6k + 16`;
`cont_LP_eventually`, `Induction/Continuity`). -/
private theorem BASetup_LP_eventually (k : ℕ) :
    ∀ᶠ N : ℝ in atTop, 1 ≤ N ∧ 6 * (k : ℝ) ≤ N ∧ (2 : ℝ) ^ k ≤ N ∧
      N * N ^ (-(6 * (k : ℝ) + 16)) ≤ N⁻¹ ∧
      N * ((k : ℝ) * (N ^ 2) ^ k * (3 * N ^ 6 * N ^ (-(6 * (k : ℝ) + 16) / 2))) ≤ (N⁻¹) ^ k := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (6 * (k : ℝ)),
    eventually_ge_atTop ((2 : ℝ) ^ k)] with N h1 h2 h3
  have hN0 : 0 < N := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hinv : N ^ (-1 : ℝ) = N⁻¹ := Real.rpow_neg_one N
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · have e : N * N ^ (-(6 * (k : ℝ) + 16)) = N ^ (1 + -(6 * (k : ℝ) + 16)) := by
      rw [Real.rpow_add hN0, Real.rpow_one]
    rw [e, ← hinv]
    exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  · have e : N ^ (-(6 * (k : ℝ) + 16) / 2) = (N ^ (3 * k + 8))⁻¹ := by
      rw [show -(6 * (k : ℝ) + 16) / 2 = -((3 * k + 8 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_neg hN0.le, Real.rpow_natCast]
    have hpos : 0 < N ^ (3 * k + 8) := pow_pos hN0 _
    have hk1 : 0 < N ^ k := pow_pos hN0 k
    have e2 : N * ((k : ℝ) * (N ^ 2) ^ k * (3 * N ^ 6 * (N ^ (3 * k + 8))⁻¹)) =
        (3 * k * N ^ (2 * k + 7)) / N ^ (3 * k + 8) := by
      field_simp
      ring
    rw [e, e2, inv_pow, ← one_div, div_le_div_iff₀ hpos hk1]
    have h5 : 3 * (k : ℝ) ≤ N := by linarith
    calc 3 * (k : ℝ) * N ^ (2 * k + 7) * N ^ k = 3 * (k : ℝ) * N ^ (3 * k + 7) := by ring
      _ ≤ N * N ^ (3 * k + 7) := mul_le_mul_of_nonneg_right h5 (pow_nonneg hN0.le _)
      _ = 1 * N ^ (3 * k + 8) := by ring

/-- `(η_t)⁻¹ ≤ N²` from `(1 - t)⁻¹ ≤ N`, `Im m ≥ κ` and `1/κ ≤ N` (`cont_eta_inv_le`, `Induction/Continuity`, with
`c₁ ≤ Im m(E)` replaced by `κ ≤ Im m`). -/
private theorem BASetup_eta_inv_le {m : ℂ} {t N κ : ℝ} (hN0 : 0 < N) (hκ : 0 < κ) (hκm : κ ≤ m.im)
    (hNc : 1 / κ ≤ N) (hN1 : (1 - t)⁻¹ ≤ N) : (etaOf m t)⁻¹ ≤ N ^ 2 := by
  have hm : 0 < m.im := lt_of_lt_of_le hκ hκm
  have h1 : (etaOf m t)⁻¹ = (1 - t)⁻¹ * (m.im)⁻¹ := by
    unfold etaOf
    rw [mul_inv]
  have h2 : (m.im)⁻¹ ≤ N := by
    refine le_trans ?_ hNc
    rw [one_div]
    exact inv_anti₀ hκ hκm
  rw [h1, sq]
  exact mul_le_mul hN1 h2 (inv_nonneg.2 hm.le) hN0.le

end Scalars

section Close

open scoped Matrix.Norms.L2Operator

open RBM.Ind RBM.Ind.ContinuityNet

variable {d : ℕ}

/-- `‖X‖ ≤ 2N²` on the good event, for the Gaussian matrix `X` of `sz.withLam 0` at size `n`. -/
private theorem BASetup_X_norm (sz : Sizes d) (n : ℕ) (ω : sz.SeqΩ) {N : ℝ}
    (hN : N = ((sz.size n : ℕ) : ℝ)) (hgood : ∀ c : CoordF d (sz.L n) (sz.W n), |sz.slice n ω c| ≤ N) :
    ‖sz.seqXmat n ω‖ ≤ 2 * N ^ 2 := by
  have hcardI : (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) = N := by
    rw [sz.card_Idx n, hN]
  have h := cont_norm_Xmat_le (sz.slice n ω) hgood
  rw [hcardI] at h
  change ‖Xmat d (sz.L n) (sz.W n) (sz.slice n ω)‖ ≤ _ at h
  change ‖Xmat d (sz.L n) (sz.W n) (sz.slice n ω)‖ ≤ _
  linarith

/-- The two conclusions of `hclose` for the loop family of `STStep1Loop` at one index `n`, deterministic:
`‖𝓛_u‖ ≤ ‖𝓛_{u'}‖ + N^{-k}` and `ζ_{u'} ≤ 2 ζ_u` (the band `cont_LP_close`, `Induction/Continuity`; `H_u = g₀ Ψ + √u X`,
`z_u = E + (1 - u) m`, `(η_t)⁻¹ ≤ N²` from `κ ≤ Im m`, `1/κ ≤ N`). -/
private theorem BASetup_LP_close (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ)
    {N s t u u' κ B : ℝ} {k : ℕ} (hN : N = ((sz.size n : ℕ) : ℝ))
    (hB : 0 ≤ B) (hs0 : 0 ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (hsu' : s ≤ u')
    (hu't : u' ≤ t) (ht : t < 1) (hκ : 0 < κ) (hmκ : κ ≤ (BAmF sz lam0 E n).im)
    (hm1 : ‖BAmF sz lam0 E n‖ ≤ 1) (hNc : 1 / κ ≤ N) (hN1 : (1 - t)⁻¹ ≤ N)
    (hgood : ∀ c : CoordF d (sz.L n) (sz.W n), |sz.slice n ω c| ≤ N)
    (hy : |u - u'| ≤ N ^ (-(6 * (k : ℝ) + 16)))
    (g1 : 1 ≤ N) (g2 : 6 * (k : ℝ) ≤ N)
    (gA : N * N ^ (-(6 * (k : ℝ) + 16)) ≤ N⁻¹)
    (gC : N * ((k : ℝ) * (N ^ 2) ^ k * (3 * N ^ 6 * N ^ (-(6 * (k : ℝ) + 16) / 2))) ≤ (N⁻¹) ^ k)
    (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    ‖(baFM sz lam0 E).L n u σ a ω‖ ≤ ‖(baFM sz lam0 E).L n u' σ a ω‖ + (N⁻¹) ^ k ∧
      ((1 - s) / (1 - u')) ^ (k - 1) * B ^ (k - 1) ≤
        2 * (((1 - s) / (1 - u)) ^ (k - 1) * B ^ (k - 1)) := by
  have hN0 : 0 < N := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu'0 : 0 ≤ u' := hs0.trans hsu'
  have hΔ1 : |u - u'| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hsq : Real.sqrt |u - u'| ≤ N ^ (-(6 * (k : ℝ) + 16) / 2) := cont_sqrt_abs_le hN0.le hy
  have hm0 : 0 ≤ (BAmF sz lam0 E n).im := (hκ.trans_le hmκ).le
  have hQ : (etaOf (BAmF sz lam0 E n) t)⁻¹ ≤ N ^ 2 := BASetup_eta_inv_le hN0 hκ hmκ hNc hN1
  have hη : 0 < etaOf (BAmF sz lam0 E n) t := by
    unfold etaOf
    exact mul_pos h1t (hκ.trans_le hmκ)
  have hQ1 : 1 ≤ N ^ 2 := one_le_pow₀ g1
  have hcardB : (Fintype.card (Vtx d (sz.L n) (sz.W n)) : ℝ) = N := by
    rw [card_BlockIndex, hN]
    change _ = (((sz.W n * sz.L n) ^ d : ℕ) : ℝ)
    rw [mul_comm]
  have hXb : ‖blockMat d (sz.L n) (sz.W n) (sz.seqXmat n ω)‖ ≤ 2 * N ^ 2 := by
    have h := cont_norm_blockMat_Xmat_le (sz.slice n ω) hgood
    rw [hcardB] at h
    change ‖blockMat d (sz.L n) (sz.W n) (Xmat d (sz.L n) (sz.W n) (sz.slice n ω))‖ ≤ _ at h
    change ‖blockMat d (sz.L n) (sz.W n) (Xmat d (sz.L n) (sz.W n) (sz.slice n ω))‖ ≤ _
    linarith
  have hloop := BASetup_loopAbs_diff (sz.W_pos n) (BASetup_herm sz lam0 n u ω)
    (BASetup_herm sz lam0 n u' ω) (BASetup_H_sub sz lam0 n u u' ω) hη hQ1 hQ
    (BASetup_eta_le _ (E n) hm0 ht hut) (BASetup_eta_le _ (E n) hm0 ht hu't)
    (BASetup_zdiff _ _ u u' hm1) (cont_abs_sqrt_sub_sqrt_le hu0 hu'0) (abs_nonneg _) hΔ1 hXb σ a
  rw [hcardB] at hloop
  refine ⟨?_, ?_⟩
  · have hS : N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1) * Real.sqrt |u - u'| ≤
        3 * N ^ 6 * N ^ (-(6 * (k : ℝ) + 16) / 2) := by
      have e1 : N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1) ≤ 3 * N ^ 6 := by
        have : N ^ 4 ≤ N ^ 6 := pow_le_pow_right₀ g1 (by norm_num)
        nlinarith
      exact mul_le_mul e1 hsq (Real.sqrt_nonneg _) (by positivity)
    have hbound : |‖loopFine d (sz.L n) (sz.W n) (sz.seqHflowBA lam0 n u ω)
          (ztOf (BAmF sz lam0 E n) (E n) u) σ a‖ -
        ‖loopFine d (sz.L n) (sz.W n) (sz.seqHflowBA lam0 n u' ω)
          (ztOf (BAmF sz lam0 E n) (E n) u') σ a‖| ≤
        N * ((k : ℝ) * (N ^ 2) ^ k * (3 * N ^ 6 * N ^ (-(6 * (k : ℝ) + 16) / 2))) :=
      hloop.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hS (by positivity)) hN0.le)
    have := (abs_le.1 (hbound.trans gC)).2
    change ‖loopFine d (sz.L n) (sz.W n) (sz.seqHflowBA lam0 n u ω)
          (ztOf (BAmF sz lam0 E n) (E n) u) σ a‖ ≤
        ‖loopFine d (sz.L n) (sz.W n) (sz.seqHflowBA lam0 n u' ω)
          (ztOf (BAmF sz lam0 E n) (E n) u') σ a‖ + _
    linarith
  · have hx0 : 0 ≤ N⁻¹ := inv_nonneg.2 hN0.le
    have hx1 : (1 - t)⁻¹ * |u - u'| ≤ N⁻¹ :=
      (mul_le_mul hN1 hy (abs_nonneg _) hN0.le).trans gA
    have h3k : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
    have hk : ((k - 1 : ℕ) : ℝ) * N⁻¹ ≤ 1 / 2 := by
      calc ((k - 1 : ℕ) : ℝ) * N⁻¹ ≤ k * N⁻¹ := mul_le_mul_of_nonneg_right h3k hx0
        _ ≤ (N / 6) * N⁻¹ := mul_le_mul_of_nonneg_right (by linarith) hx0
        _ = 1 / 6 := by field_simp
        _ ≤ 1 / 2 := by norm_num
    exact BASetup_LP_zeta_ratio k hB hsu hut hu't ht hx0 hx1 hk

/-- The two conclusions of `hclose` for the weak-law family of `STStep1Weak` at one index `n`, deterministic:
`‖(G_u - M)_{xy}‖ ≤ ‖(G_{u'} - M)_{xy}‖ + N^{-1/4}` and `Bctl(u')^{1/4} ≤ 2 Bctl(u)^{1/4}` (the band `cont_WL_close`,
`Induction/Continuity`; `M` is time independent, so `(G - M)` differences are `G` differences). -/
private theorem BASetup_WL_close (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ)
    {N t u u' A κ : ℝ} (hN : N = ((sz.size n : ℕ) : ℝ))
    (hu0 : 0 ≤ u) (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t) (ht : t < 1)
    (hκ : 0 < κ) (hmκ : κ ≤ (BAmF sz lam0 E n).im) (hm1 : ‖BAmF sz lam0 E n‖ ≤ 1)
    (hNc : 1 / κ ≤ N) (hN1 : (1 - t)⁻¹ ≤ N)
    (hgood : ∀ c : CoordF d (sz.L n) (sz.W n), |sz.slice n ω c| ≤ N)
    (hy : |u - u'| ≤ N ^ (-A)) (g2 : N * N ^ (-A) ≤ 1 / 10)
    (g3 : 3 * N ^ 6 * N ^ (-A / 2) ≤ (N⁻¹) ^ ((1 : ℝ) / 4)) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖(baFM sz lam0 E).GM n u ω x y‖ ≤ ‖(baFM sz lam0 E).GM n u' ω x y‖ + (N⁻¹) ^ ((1 : ℝ) / 4) ∧
      (sz.Bctl n u') ^ ((1 : ℝ) / 4) ≤ 2 * (sz.Bctl n u) ^ ((1 : ℝ) / 4) := by
  have hNge : (1 : ℝ) ≤ N := by
    rw [hN]
    exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hΔ1 : |u - u'| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hsq : Real.sqrt |u - u'| ≤ N ^ (-A / 2) := cont_sqrt_abs_le hN0.le hy
  have hm0 : 0 ≤ (BAmF sz lam0 E n).im := (hκ.trans_le hmκ).le
  have hQ : (etaOf (BAmF sz lam0 E n) t)⁻¹ ≤ N ^ 2 := BASetup_eta_inv_le hN0 hκ hmκ hNc hN1
  have hη : 0 < etaOf (BAmF sz lam0 E n) t := by
    unfold etaOf
    exact mul_pos h1t (hκ.trans_le hmκ)
  have hX := BASetup_X_norm sz n ω hN hgood
  have hent := BASetup_entry_diff (BASetup_herm sz lam0 n u ω) (BASetup_herm sz lam0 n u' ω)
    (BASetup_H_sub sz lam0 n u u' ω) hX (cont_abs_sqrt_sub_sqrt_le hu0 hu'0) (abs_nonneg _) hΔ1 hη hQ
    (BASetup_eta_le _ (E n) hm0 ht hut) (BASetup_eta_le _ (E n) hm0 ht hu't)
    (BASetup_zdiff _ _ u u' hm1) x y
  have hs0' : 0 ≤ Real.sqrt |u - u'| := Real.sqrt_nonneg _
  have hN4 : N ^ 4 ≤ N ^ 6 := pow_le_pow_right₀ hNge (by norm_num)
  have hbound : ‖Gres (sz.seqHflowBA lam0 n u ω) (ztOf (BAmF sz lam0 E n) (E n) u) true x y -
        Gres (sz.seqHflowBA lam0 n u' ω) (ztOf (BAmF sz lam0 E n) (E n) u') true x y‖ ≤
      (N⁻¹) ^ ((1 : ℝ) / 4) := by
    refine hent.trans ?_
    have e1 : N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1) * Real.sqrt |u - u'| =
        (2 * N ^ 6 + N ^ 4) * Real.sqrt |u - u'| := by ring
    rw [e1]
    calc (2 * N ^ 6 + N ^ 4) * Real.sqrt |u - u'| ≤ 3 * N ^ 6 * Real.sqrt |u - u'| :=
          mul_le_mul_of_nonneg_right (by linarith) hs0'
      _ ≤ 3 * N ^ 6 * N ^ (-A / 2) := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ (N⁻¹) ^ ((1 : ℝ) / 4) := g3
  refine ⟨?_, ?_⟩
  · have hdiff : (baFM sz lam0 E).GM n u ω x y - (baFM sz lam0 E).GM n u' ω x y =
        Gres (sz.seqHflowBA lam0 n u ω) (ztOf (BAmF sz lam0 E n) (E n) u) true x y -
          Gres (sz.seqHflowBA lam0 n u' ω) (ztOf (BAmF sz lam0 E n) (E n) u') true x y := by
      change BAGt sz lam0 E n u ω x y - BAMfine sz lam0 E n x y -
        (BAGt sz lam0 E n u' ω x y - BAMfine sz lam0 E n x y) = _
      rw [sub_sub_sub_cancel_right]
      rfl
    have habs := abs_norm_sub_norm_le ((baFM sz lam0 E).GM n u ω x y) ((baFM sz lam0 E).GM n u' ω x y)
    rw [hdiff] at habs
    have := (abs_le.1 (habs.trans hbound)).2
    linarith
  · have hu1 : u < 1 := lt_of_le_of_lt hut ht
    have hu'1 : u' < 1 := lt_of_le_of_lt hu't ht
    have hBu : 0 ≤ sz.Bctl n u :=
      (inv_nonneg.2 (Nat.cast_nonneg _)).trans (cont_inv_size_le_Bctl sz n hu0 hu1)
    have hBu' : 0 ≤ sz.Bctl n u' :=
      (inv_nonneg.2 (Nat.cast_nonneg _)).trans (cont_inv_size_le_Bctl sz n hu'0 hu'1)
    have hx : (1 - t)⁻¹ * |u' - u| ≤ 1 / 10 := by
      rw [abs_sub_comm]
      exact (mul_le_mul hN1 hy (abs_nonneg _) hN0.le).trans g2
    have hr := cont_Bctl_ratio sz n ht hu't hut
    have hMratio : sz.Bctl n u' ≤ (11 / 10) * sz.Bctl n u :=
      hr.trans (mul_le_mul_of_nonneg_right (by linarith) hBu)
    have h2 : (sz.Bctl n u') ^ ((1 : ℝ) / 4) ≤ ((11 / 10) * sz.Bctl n u) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow hBu' hMratio (by norm_num)
    rw [Real.mul_rpow (by norm_num) hBu] at h2
    have h3 : ((11 / 10 : ℝ)) ^ ((1 : ℝ) / 4) ≤ 2 := by
      calc ((11 / 10 : ℝ)) ^ ((1 : ℝ) / 4) ≤ (11 / 10 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ ≤ 2 := by rw [Real.rpow_one]; norm_num
    calc (sz.Bctl n u') ^ ((1 : ℝ) / 4)
        ≤ (11 / 10 : ℝ) ^ ((1 : ℝ) / 4) * (sz.Bctl n u) ^ ((1 : ℝ) / 4) := h2
      _ ≤ 2 * (sz.Bctl n u) ^ ((1 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hBu _)

end Close

section NetLift

open RBM.Ind RBM.Ind.ContinuityNet

variable {d : ℕ}

/-- `baNetLift`: the two halves of the band `Step1NetLift`/`step1NetLift` (`Induction/Continuity`)
for `baFM sz lam0 E` at the law `seqP (sz.withLam 0)`: the per-time domination (`PerTimeDomAt`) gives `STStep1LoopgL`,
`STStep1WeakgL`.  Both halves apply `cont_core` (`ContinuityNet`) on `TimeIcc s t n × V n` with the good event
`contGood (sz.withLam 0)` and the net of mesh `N^{-A-1}`; loops: `V n = (σ, a)`, `A = 6k + 16`, `#V ≤ N^{k+1}`,
`ε = N^{-k}`; weak law: `V n = Idx × Idx`, `A = 40`, `#V = N²`, `ε = N^{-1/4}`.  The bulk premise `|E| ≤ 2 - κ` of the band
is replaced by `κ ≤ Im m`, `|m| ≤ 1`. -/
theorem baNetLift (d : ℕ) :
    ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (κ τ : ℝ) (s t : ℕ → ℝ), 0 < κ →
      (∀ n, κ ≤ (BAmF sz lam0 E n).im) → (∀ n, ‖BAmF sz lam0 E n‖ ≤ 1) → 0 < τ →
      (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → sz.SizeTendsto → sz.RangeCond τ t →
      ((∀ k : ℕ, 1 ≤ k →
          PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size
            (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
            (fun n p ω => ‖(baFM sz lam0 E).L n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
            (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))) →
        STStep1LoopgL (baFM sz lam0 E) (Sizes.seqP (sz.withLam 0)) s t) ∧
      (PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size
          (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
          (fun n p ω => ‖(baFM sz lam0 E).GM n (p.1 : ℝ) ω p.2.1 p.2.2‖)
          (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (1 / 4 : ℝ)) →
        STStep1WeakgL (baFM sz lam0 E) (Sizes.seqP (sz.withLam 0)) s t) := by
  intro sz lam0 E κ τ s t hκ hmκ hm1 hτ hs0 hst ht1 hsize hRange
  have hlen : ∀ n, t n - s n ≤ 1 := fun n => by linarith [hs0 n, ht1 n]
  have hcast : Tendsto (fun n : ℕ => ((sz.size n : ℕ) : ℝ)) atTop atTop := hsize
  have hsizeN : Tendsto sz.size atTop atTop := tendsto_natCast_atTop_iff.mp hcast
  have hgoodP : HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size (contGood (sz.withLam 0)) :=
    cont_highProbAt_good (sz.withLam 0) hsizeN
  have ev1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hcast.eventually_ge_atTop 1
  have evc : ∀ᶠ n : ℕ in atTop, 1 / κ ≤ ((sz.size n : ℕ) : ℝ) :=
    hcast.eventually_ge_atTop _
  have evR : ∀ᶠ n : ℕ in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
    filter_upwards [hRange, ev1] with n hn h1
    have hx0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have hpos : 0 < ((sz.size n : ℕ) : ℝ) ^ (-1 + τ) := Real.rpow_pos_of_pos hx0 _
    have h2 := inv_anti₀ hpos hn
    rw [← Real.rpow_neg hx0.le] at h2
    refine h2.trans ?_
    calc ((sz.size n : ℕ) : ℝ) ^ (-(-1 + τ)) ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
      _ = _ := Real.rpow_one _
  have hBnn : ∀ n, 0 ≤ sz.Bctl n (s n) := fun n =>
    (inv_nonneg.2 (Nat.cast_nonneg _)).trans
      (cont_inv_size_le_Bctl sz n (hs0 n) (lt_of_le_of_lt (hst n) (ht1 n)))
  refine ⟨fun hPT => ?_, fun hPT => ?_⟩
  · -- the loop family
    intro k hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hA0 : 0 ≤ 6 * (k : ℝ) + 16 := by linarith
    have hcard : ∀ᶠ n : ℕ in atTop,
        (Fintype.card ((Fin k → Bool) × (Fin k → Zd d (sz.L n))) : ℝ) ≤
          ((sz.size n : ℕ) : ℝ) ^ ((k : ℝ) + 1) := by
      filter_upwards [hcast.eventually (BASetup_LP_eventually k)] with n hev
      obtain ⟨g1, _, g3, -⟩ := hev
      have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
      have e : ((sz.size n : ℕ) : ℝ) ^ ((k : ℝ) + 1) =
          ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) := by
        rw [Real.rpow_add hN0, Real.rpow_natCast, Real.rpow_one]
      have hcardZ : Fintype.card (Zd d (sz.L n)) = sz.L n ^ d := by
        simp [Zd, ZMod.card]
      have hcardV : (Fintype.card ((Fin k → Bool) × (Fin k → Zd d (sz.L n))) : ℝ) =
          (2 : ℝ) ^ k * (((sz.L n : ℕ) : ℝ) ^ d) ^ k := by
        rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, hcardZ]
        push_cast
        ring
      have hW1 : (1 : ℝ) ≤ (sz.W n : ℝ) := by exact_mod_cast sz.W_pos n
      have hL0 : (0 : ℝ) ≤ (sz.L n : ℝ) := Nat.cast_nonneg _
      have hLW : (sz.L n : ℝ) ≤ (sz.W n : ℝ) * (sz.L n : ℝ) := le_mul_of_one_le_left hL0 hW1
      have eN : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℝ) * (sz.L n : ℝ)) ^ d := by
        simp [Sizes.size]
      have hLN : (sz.L n : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
        rw [eN]
        exact pow_le_pow_left₀ hL0 hLW d
      rw [e, hcardV]
      calc (2 : ℝ) ^ k * ((sz.L n : ℝ) ^ d) ^ k
          ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ k :=
            mul_le_mul g3 (pow_le_pow_left₀ (by positivity) hLN k) (by positivity) hN0.le
        _ = ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) := by ring
    refine cont_core (V := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n))) hsizeN hst hlen
      (A := 6 * (k : ℝ) + 16) (Cv := (k : ℝ) + 1) hA0 (by linarith) hcard (hPT k hk)
      hgoodP
      (ε := fun n => (((sz.size n : ℕ) : ℝ)⁻¹) ^ k)
      (fun n => pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _) ?_ ?_
    · -- `hlow`
      refine Eventually.of_forall fun n p ω => ?_
      obtain ⟨u, σ, a⟩ := p
      exact BASetup_LP_low sz n k (hs0 n) u.2.1 (lt_of_le_of_lt u.2.2 (ht1 n))
    · -- `hclose`
      filter_upwards [hcast.eventually (BASetup_LP_eventually k), evc, evR] with n hev hc hR
      obtain ⟨g1, g2, _, gA, gC⟩ := hev
      intro ω hω u u' hΔ v
      obtain ⟨σ, a⟩ := v
      exact BASetup_LP_close sz lam0 E n ω
        (N := ((sz.size n : ℕ) : ℝ)) (s := s n) (t := t n) (u := u) (u' := u')
        (B := sz.Bctl n (s n)) (κ := κ) rfl (hBnn n) (hs0 n) u.2.1 u.2.2 u'.2.1 u'.2.2
        (ht1 n) hκ (hmκ n) (hm1 n) hc hR (fun c => hω c) hΔ g1 g2 gA gC σ a
  · -- the weak law
    have evg2 : ∀ᶠ n : ℕ in atTop,
        ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-(40 : ℝ)) ≤ 1 / 10 := by
      filter_upwards [cont_gap hsizeN 1 (κ := 1 / 10) (p := 1 - 40) (q := 0) (by norm_num)
        (by norm_num), ev1] with n hn h1
      have hx0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
      have : ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-(40 : ℝ)) =
          ((sz.size n : ℕ) : ℝ) ^ (1 - 40 : ℝ) := by
        rw [show (1 - 40 : ℝ) = 1 + -40 by ring, Real.rpow_add hx0, Real.rpow_one]
      rw [this]
      rw [Real.rpow_zero] at hn
      linarith
    have evg3 : ∀ᶠ n : ℕ in atTop,
        3 * ((sz.size n : ℕ) : ℝ) ^ 6 * ((sz.size n : ℕ) : ℝ) ^ (-(40 : ℝ) / 2) ≤
          (((sz.size n : ℕ) : ℝ)⁻¹) ^ ((1 : ℝ) / 4) := by
      filter_upwards [cont_gap hsizeN 3 (κ := 1) (p := 6 - 40 / 2) (q := -(1 / 4)) one_pos
        (by norm_num), ev1] with n hn h1
      have hx0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
      have e1 : 3 * ((sz.size n : ℕ) : ℝ) ^ 6 * ((sz.size n : ℕ) : ℝ) ^ (-(40 : ℝ) / 2) =
          3 * ((sz.size n : ℕ) : ℝ) ^ (6 - 40 / 2 : ℝ) := by
        rw [mul_assoc, cont_pow_mul_rpow hx0]
        congr 2
        push_cast
        ring
      have e2 : (((sz.size n : ℕ) : ℝ)⁻¹) ^ ((1 : ℝ) / 4) =
          ((sz.size n : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) := by
        rw [Real.inv_rpow hx0.le, Real.rpow_neg hx0.le]
      rw [e1, e2]
      linarith
    have hcard : ∀ n : ℕ,
        (Fintype.card (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) : ℝ) ≤
          ((sz.size n : ℕ) : ℝ) ^ (2 : ℝ) := by
      intro n
      rw [Fintype.card_prod, Nat.cast_mul, Real.rpow_two, sz.card_Idx n]
      ring_nf
      exact le_rfl
    refine cont_core (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) hsizeN
      hst hlen (A := 40) (Cv := 2) (by norm_num) (by norm_num) (Eventually.of_forall hcard) hPT
      hgoodP
      (ε := fun n => (((sz.size n : ℕ) : ℝ)⁻¹) ^ ((1 : ℝ) / 4))
      (fun n => Real.rpow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _) ?_ ?_
    · -- `hlow`
      refine Eventually.of_forall fun n p ω => ?_
      obtain ⟨u, i, j⟩ := p
      exact BASetup_WL_low sz n ((hs0 n).trans u.2.1) (lt_of_le_of_lt u.2.2 (ht1 n))
    · -- `hclose`
      filter_upwards [evc, evR, evg2, evg3] with n hc hR g2 g3
      intro ω hω u u' hΔ v
      obtain ⟨i, j⟩ := v
      exact BASetup_WL_close sz lam0 E n ω (N := ((sz.size n : ℕ) : ℝ)) (t := t n) (u := u)
        (u' := u') (A := 40) (κ := κ) rfl ((hs0 n).trans u.2.1) u.2.2
        ((hs0 n).trans u'.2.1) u'.2.2 (ht1 n) hκ (hmκ n) (hm1 n) hc hR (fun c => hω c) hΔ g2 g3 i j

end NetLift

/-! ## 5. Private facts -/

section InstHelpers

variable {d : ℕ}

/-- At `t = 0` the flow is `H_0 = g₀ Ψ` and `z_0 = E + m`, so `G_0 = M` (a copy of `Boot_GM_zero`,
`BA/Step1Boot`). -/
private theorem BASetup_GM_zero (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ)
    (x y : Idx d (sz.L n) (sz.W n)) : (baFM sz lam0 E).GM n 0 ω x y = 0 := by
  have hH : sz.seqHflowBA lam0 n 0 ω = ((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) := by
    ext i j
    have h : (sz.withLam 0).seqHflow n 0 ω i j = 0 := by
      have h0 : (sz.withLam 0).seqHflow n 0 ω = 0 := by simp [Sizes.seqHflow]
      rw [h0]
      rfl
    simp [Sizes.seqHflowBA, h]
  change BAGt sz lam0 E n 0 ω x y - BAMfine sz lam0 E n x y = 0
  unfold BAGt BAMfine Mres
  rw [hH]
  have hz : ztOf (BAmF sz lam0 E n) (E n) 0 = (E n : ℂ) + BAmF sz lam0 E n := by simp [ztOf]
  rw [hz]
  simp [Gres]

/-- `|m| ≤ 1` for `m = m(E, g₀)` when `Im m > 0` (`(self_m)` has a solution, `BAm_spec`; `BAself_norm_le_one` at the real
point `z = E`). -/
private theorem BASetup_norm_BAmF_le_one (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)
    (h : 0 < (BAmF sz lam0 E n).im) : ‖BAmF sz lam0 E n‖ ≤ 1 := by
  have hex : ∃ m, BASelf d (sz.L n) (lam0 n) (E n : ℂ) m := by
    by_contra hne
    have h0 : BAmF sz lam0 E n = 0 := by
      unfold BAmF BAm
      simp [hne]
    rw [h0] at h
    simp at h
  exact BAself_norm_le_one d (sz.L n) (lam0 n) (E n : ℂ) _ (by simp) (BAm_spec hex)

end InstHelpers

end RBM.BA
