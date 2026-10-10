/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Main.BUniv

/-!
# `BUniv` from the fewest leaves (UN-52b, ticket T2371)

`bUniv_holds` is `bUniv_of_leaves` (`Main/BUniv.lean`) with the two band rows `UNDensBandRow`,
`UNTrLocalBandRow` proved here (`unDensBandRow`, `unTrLocalBandRow`) and `UNGUELocal` replaced
by `UNGUESchurTail` through `un_gueLocal_of_tail` (paper-delta candidate T2371a: a reduction of
a Lean pin, not a paper statement).  Every leaf of `un_bUniv_of_rows'`
(`Universality/PinsDens.lean:233`), its status and, for a hypothesis of `bUniv_holds`, its producer:

* proved on `main`: `UNInfty1Row'` (`un_infty1Row'`), `UNUnivMainRow` (`univMainRow`), `UNClaimRow`
  (`unClaimRow`), `UNEMCTE2Row` (`unEMCTE2Row`), `UNJakUywRow` (`jakUywRow`), `UNGreenCorrAll`
  (`greenCorrAll`);
* `UNOURow`: proved, `unOURow := ouRow_of_pins g1Row g2bRow` (`Main/BUniv.lean`); the row is itself
  an implication from the three consumed inputs `UNMLOut`, `UNLocAvgBand`, `UNQueBand` below;
* `UNDensBandRow`: proved here, `unDensBandRow` (deterministic, `κ' = min κ 1`, `δ = κ'/2`);
* `UNTrLocalBandRow`: proved here, `unTrLocalBandRow` (from its own premise `UNLocAvgBand`, by
  averaging over the blocks);
* `UNNormBandRow`: hypothesis, owed pin; producer T2372 (UN-10a, `Universality/NormBand.lean`,
  `unNormBandRow`);
* `UNL32`: hypothesis, borrowed (LSY Thm 2.2, DECISIONS §5);
* `UNMLOut d` (`∀ d`): hypothesis, consumed input; producer ST-6 (no merged theorem);
* `UNLocAvgBand`: hypothesis, consumed MA input (`locSC_to_UNLocAvgBand`, `Endpoints.lean:519`);
* `UNQueBand`: hypothesis, consumed MA input (`QUE_to_UNQueBand`, `Endpoints.lean:530`);
* `UNGUELocal`: not a hypothesis, `un_gueLocal_of_tail` from `UNGUESchurTail`;
* `UNGUESchurTail`: hypothesis, owed pin; producer T2373 (UN-10b, `Universality/GUELocalSchur.lean`,
  `gueSchurTail`, `gueLocal`).

The two `example`s at the end instantiate `bUniv_holds` at the data of `RBM3D/Endpoints.lean`
(`Inst`): `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`), `d = 3`, `(𝔠, 𝔡) = (1/6, 1/10)`, `k = 1`,
`κ = 1/10`, `𝒪 = bump`, at `E = 0` and at the edge `E = 19/10 = 2 - κ`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Endpoints

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
open scoped NNReal ENNReal

/-! ## 1. Leaf `UNDensBandRow`: the density regularity of the semicircle at every bulk energy -/

section DensBand

/-- The real and imaginary parts of `m (m + z) = -1` (`msc_mul`): `1 = b² + b η - a² - a x`. -/
private theorem BUniv_msc_re_im (z : ℂ) :
    1 = (msc z).im ^ 2 + (msc z).im * z.im - (msc z).re ^ 2 - (msc z).re * z.re := by
  have h := congrArg Complex.re (msc_mul z)
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.one_re] at h
  linarith

/-- `Im msc z ≥ (1 - x²/4)/11` for `0 < Im z ≤ 10` (the proof of `un_msc_im_ge`, `Pins.lean:1378`, at a
general real part: `1 = b² + bη - a² - ax ≤ 11 b + x²/4`). -/
private theorem BUniv_msc_im_ge {z : ℂ} (hz : 0 < z.im) (hz10 : z.im ≤ 10) :
    (1 - z.re ^ 2 / 4) / 11 ≤ (msc z).im := by
  have e1 := BUniv_msc_re_im z
  have hb : 0 < (msc z).im := msc_im_pos hz
  have hb1 : (msc z).im < 1 := (Complex.im_le_norm _).trans_lt (norm_msc_lt_one hz)
  set a := (msc z).re
  set b := (msc z).im
  have e2 : -a ^ 2 - a * z.re ≤ z.re ^ 2 / 4 := by nlinarith [sq_nonneg (a + z.re / 2)]
  have e3 : b ^ 2 + b * z.im ≤ 11 * b := by
    nlinarith [mul_pos hb (sub_pos.2 hb1), mul_nonneg hb.le (sub_nonneg.2 hz10)]
  linarith

/-- Lipschitz dependence of `msc` where `Im msc ≥ c`: the proof of `un_msc_lip` (`Pins.lean:1396`) with `c`
in place of `9/100`; `(m₁ - m₂)(1 - m₁m₂) = (z₁ - z₂) m₁ m₂`, `Re(1 - m₁m₂) ≥ Im m₁ Im m₂ ≥ c²`. -/
private theorem BUniv_msc_lip {c : ℝ} (hc : 0 < c) {z₁ z₂ : ℂ} (h1 : 0 < z₁.im) (h2 : 0 < z₂.im)
    (hb1 : c ≤ (msc z₁).im) (hb2 : c ≤ (msc z₂).im) :
    ‖msc z₁ - msc z₂‖ ≤ 1 / c ^ 2 * ‖z₁ - z₂‖ := by
  set m₁ := msc z₁
  set m₂ := msc z₂
  have e1 : m₁ ^ 2 + z₁ * m₁ + 1 = 0 := by have := msc_mul z₁; linear_combination this
  have e2 : m₂ ^ 2 + z₂ * m₂ + 1 = 0 := by have := msc_mul z₂; linear_combination this
  have key : (m₁ - m₂) * (1 - m₁ * m₂) = (z₁ - z₂) * (m₁ * m₂) := by
    linear_combination (-m₂) * e1 + m₁ * e2
  have hn1 : ‖m₁‖ < 1 := norm_msc_lt_one h1
  have hn2 : ‖m₂‖ < 1 := norm_msc_lt_one h2
  have ha1 : |m₁.re| ≤ 1 := (Complex.abs_re_le_norm m₁).trans hn1.le
  have ha2 : |m₂.re| ≤ 1 := (Complex.abs_re_le_norm m₂).trans hn2.le
  have hre : c ^ 2 ≤ (1 - m₁ * m₂).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re]
    have h3 : m₁.re * m₂.re ≤ 1 := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      calc |m₁.re| * |m₂.re| ≤ 1 * 1 := mul_le_mul ha1 ha2 (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    nlinarith [mul_le_mul hb1 hb2 hc.le (by linarith)]
  have hnorm : c ^ 2 ≤ ‖1 - m₁ * m₂‖ := hre.trans (Complex.re_le_norm _)
  have hprod : ‖m₁ - m₂‖ * ‖1 - m₁ * m₂‖ = ‖z₁ - z₂‖ * (‖m₁‖ * ‖m₂‖) := by
    rw [← norm_mul, key, norm_mul, norm_mul]
  have hle : ‖z₁ - z₂‖ * (‖m₁‖ * ‖m₂‖) ≤ ‖z₁ - z₂‖ := by
    have : ‖m₁‖ * ‖m₂‖ ≤ 1 := by
      calc ‖m₁‖ * ‖m₂‖ ≤ 1 * 1 := mul_le_mul hn1.le hn2.le (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    calc ‖z₁ - z₂‖ * (‖m₁‖ * ‖m₂‖) ≤ ‖z₁ - z₂‖ * 1 := mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = ‖z₁ - z₂‖ := mul_one _
  have h4 : ‖m₁ - m₂‖ * c ^ 2 ≤ ‖z₁ - z₂‖ := by
    calc ‖m₁ - m₂‖ * c ^ 2 ≤ ‖m₁ - m₂‖ * ‖1 - m₁ * m₂‖ :=
          mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ = ‖z₁ - z₂‖ * (‖m₁‖ * ‖m₂‖) := hprod
      _ ≤ ‖z₁ - z₂‖ := hle
  rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)]
  linarith

/-- **Leaf `UNDensBandRow` (deterministic), proved.** For `|E| ≤ 2 - κ`, `κ' = min κ 1`, `δ = κ'/2 ≤ κ/2`:
`c = 7κ'/176 ≤ Im msc ≤ C = 1` on the box `|x - E| ≤ δ`, `0 < η ≤ 10` (from `1 - x²/4 ≥ 7κ'/16`), the
Lipschitz constant `Lp = 1/c²`, and the limit `Im msc(E + iη)/π → √(4 - E²)/(2π) = ρ_sc(E)`
(`FreeConvStability.msc_tendsto_mE`).  RBM2D has no counterpart (`Step1RegularityB` proves it inline). -/
theorem unDensBandRow : UNDensBandRow := by
  intro κ hκ E hE
  have hκ'0 : 0 < min κ 1 := lt_min hκ one_pos
  have hκ'κ : min κ 1 ≤ κ := min_le_left _ _
  have hκ'1 : min κ 1 ≤ 1 := min_le_right _ _
  set κ' : ℝ := min κ 1
  set c : ℝ := 7 * κ' / 176 with hc
  have hc0 : 0 < c := by positivity
  have hE2 : |E| < 2 := by linarith
  have hlow : ∀ z : ℂ, |z.re - E| ≤ κ' / 2 → 0 < z.im → z.im ≤ 10 → c ≤ (msc z).im := by
    intro z hz hz1 hz2
    have hx := abs_le.1 hz
    have hE' := abs_le.1 hE
    have hxa : |z.re| ≤ 2 - κ' / 2 :=
      abs_le.2 ⟨by linarith [hx.1, hE'.1], by linarith [hx.2, hE'.2]⟩
    have hx2 : z.re ^ 2 ≤ (2 - κ' / 2) ^ 2 := by
      have := sq_le_sq' (abs_le.1 hxa).1 (abs_le.1 hxa).2
      exact this
    have hk2 : κ' ^ 2 ≤ κ' := by nlinarith
    have := BUniv_msc_im_ge hz1 hz2
    nlinarith
  refine ⟨κ' / 2, by linarith, by positivity, c, 1, 1 / c ^ 2, hc0, one_pos, by positivity,
    Eventually.of_forall fun n => ⟨?_, ?_, ?_⟩⟩
  · intro x η hx hη hη10
    exact ⟨hlow ⟨x, η⟩ hx hη hη10, (Complex.im_le_norm _).trans (norm_msc_lt_one hη).le⟩
  · intro x y η hx hy hη hη10
    have hl := BUniv_msc_lip hc0 (z₁ := ⟨x, η⟩) (z₂ := ⟨y, η⟩) hη hη (hlow ⟨x, η⟩ hx hη hη10)
      (hlow ⟨y, η⟩ hy hη hη10)
    have hnz : ‖(⟨x, η⟩ : ℂ) - ⟨y, η⟩‖ = |x - y| := by
      have : ((⟨x, η⟩ : ℂ) - ⟨y, η⟩) = ((x - y : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [this, Complex.norm_real, Real.norm_eq_abs]
    calc |(msc ⟨x, η⟩).im - (msc ⟨y, η⟩).im| = |((msc ⟨x, η⟩) - (msc ⟨y, η⟩)).im| := by simp
      _ ≤ ‖msc ⟨x, η⟩ - msc ⟨y, η⟩‖ := Complex.abs_im_le_norm _
      _ ≤ 1 / c ^ 2 * ‖(⟨x, η⟩ : ℂ) - ⟨y, η⟩‖ := hl
      _ = 1 / c ^ 2 * |x - y| := by rw [hnz]
  · have h1 : Tendsto (fun η : ℝ => (msc ⟨E, η⟩).im / Real.pi) (𝓝[>] 0)
        (𝓝 ((mE E).im / Real.pi)) :=
      ((Complex.continuous_im.tendsto _).comp (FreeConvStability.msc_tendsto_mE hE2)).div_const _
    have h2 : (mE E).im / Real.pi = rhoSC E := by
      rw [mE_im, rhoSC, div_div]
    rwa [h2] at h1

end DensBand

/-! ## 2. Leaf `UNTrLocalBandRow`: the tracial local law from the block-averaged local law -/

section TrLocal

private theorem BUniv_card_zd (d L : ℕ) [NeZero L] : Fintype.card (Zd d L) = L ^ d := by
  simp [Zd, ZMod.card]

/-- If every block average of `G_xx` is within `B` of `m`, so is the normalised trace. -/
private theorem BUniv_trace_le (d L W : ℕ) [NeZero L] [NeZero W] (G : Matrix (Idx d L W) (Idx d L W) ℂ)
    (m : ℂ) {B : ℝ}
    (h : ∀ a : Zd d L, ‖((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, G x x - m‖ ≤ B) :
    ‖(Fintype.card (Idx d L W) : ℂ)⁻¹ * G.trace - m‖ ≤ B := by
  have hW : (W : ℂ) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W))
  have hL : (L : ℂ) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne L))
  have hLr : (0 : ℝ) < (L : ℝ) ^ d := pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))) d
  have hcard : (Fintype.card (Idx d L W) : ℂ) = (W : ℂ) ^ d * (L : ℂ) ^ d := by
    rw [RBM.Gauss.card_Idx]; push_cast; ring
  have htr : G.trace = ∑ a : Zd d L, ∑ x ∈ Iblk d L W a, G x x := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Iblk]
    exact (Finset.sum_fiberwise Finset.univ (fun x => (split d L W x).1) (fun x => G x x)).symm
  have heq : (Fintype.card (Idx d L W) : ℂ)⁻¹ * G.trace - m =
      ((L : ℂ) ^ d)⁻¹ * ∑ a : Zd d L, (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, G x x - m) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← htr, Finset.sum_const, Finset.card_univ,
      BUniv_card_zd d L, hcard, nsmul_eq_mul]
    push_cast
    field_simp
  rw [heq, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  calc ((L : ℝ) ^ d)⁻¹ * ‖∑ a : Zd d L, (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, G x x - m)‖
      ≤ ((L : ℝ) ^ d)⁻¹ * ∑ a : Zd d L, B := by
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => h a))
          (inv_nonneg.2 hLr.le)
    _ = B := by
        rw [Finset.sum_const, Finset.card_univ, BUniv_card_zd d L, nsmul_eq_mul]
        push_cast
        field_simp

/-- **Leaf `UNTrLocalBandRow`, proved from `UNLocAvgBand`.** `|Re z - E| ≤ δ ≤ κ/2` and `|E| ≤ 2 - κ` give
`z ∈ 𝐃_{κ/2,ε}`; `N⁻¹ tr G - m = L^{-d} ∑_a (W^{-d} ∑_{x∈[a]} G_xx - m)` (`BUniv_trace_le`), so a trace deviation
above `W^τ B` forces a block deviation above `W^τ B`: the event is inside the `UNLocAvgBand` event at
`(κ/2, ε, τ, D)`. -/
theorem unTrLocalBandRow : UNTrLocalBandRow := by
  intro hLoc d hd 𝔠 𝔡 sz hA κ hκ E hE δ hδ hδκ ε τ D hε hτ hD
  filter_upwards [hLoc d hd 𝔠 𝔡 sz hA (κ / 2) ε τ D (half_pos hκ) hε hτ hD] with n hn
  change Sizes.seqP sz _ ≤ _
  refine le_trans (measure_mono ?_) hn
  rintro ω ⟨z, hz1, hz2, hz3, hz4⟩
  have hx := abs_le.1 hz1
  have hE' := abs_le.1 hE
  refine ⟨z, ⟨abs_le.2 ⟨by linarith [hx.1, hE'.1], by linarith [hx.2, hE'.2]⟩, hz2, hz3⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  have hle := BUniv_trace_le d (sz.L n) (sz.W n) (Gres (Sizes.seqXmat sz n ω) z true) (msc z) hcon
  exact absurd hle (not_le.2 hz4)

end TrLocal

/-- **`BUniv` (bulk universality, Thm 2.4, `(eq:universality)`) from the fewest leaves.**
`bUniv_of_leaves` with the proved band rows `unDensBandRow`, `unTrLocalBandRow` and `UNGUELocal` from
`UNGUESchurTail`; the leaves that remain hypotheses (table in the module docstring) are the owed
`UNNormBandRow` (producer T2372) and `UNGUESchurTail` (producer T2373), the borrowed `UNL32`, and the
consumed inputs `UNMLOut` (ST-6), `UNLocAvgBand`, `UNQueBand` (MA).
RBM2D `bUniv_holds` (`Main/BUnivHolds.lean`). -/
theorem bUniv_holds :
    UNNormBandRow → UNL32 → (∀ d : ℕ, UNMLOut d) → UNLocAvgBand → UNQueBand → UNGUESchurTail →
      UNBUniv :=
  fun hN h32 hML hLoc hQ hT =>
    bUniv_of_leaves unDensBandRow unTrLocalBandRow hN h32 hML hLoc hQ (un_gueLocal_of_tail hT)

namespace Inst

open RBM.Gauss.SizesInst RBM.Univ.UNInst

/-- **`bUniv_holds` at the merged instance data** `sz0`, `d = 3`, `(𝔠, 𝔡) = (1/6, 1/10)`, `k = 1`, `κ = 1/10`,
`E = 0`, `𝒪 = bump`: every deterministic hypothesis is discharged, only the leaves stay hypotheses. -/
example (hN : UNNormBandRow) (h32 : UNL32) (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand)
    (hT : UNGUESchurTail) :
    Tendsto (fun n =>
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0 (Sizes.seqXmat_isHermitian sz0 n ω).eigenvalues ∂(Sizes.seqP sz0)) -
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0 (Xmat_isHermitian 3 (sz0.L n) (sz0.W n) ω).eigenvalues
        ∂(gueP 3 (sz0.L n) (sz0.W n)))) atTop (𝓝 0) :=
  bUniv_holds hN h32 hML hLoc hQ hT 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible 1 le_rfl (1 / 10)
    (by norm_num) 0 (by norm_num) bump bump_testFun

/-- The same at the edge energy `E = 19/10 = 2 - κ` of the allowed window. -/
example (hN : UNNormBandRow) (h32 : UNL32) (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand)
    (hT : UNGUESchurTail) :
    Tendsto (fun n =>
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) (19 / 10) (Sizes.seqXmat_isHermitian sz0 n ω).eigenvalues
        ∂(Sizes.seqP sz0)) -
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) (19 / 10) (Xmat_isHermitian 3 (sz0.L n) (sz0.W n) ω).eigenvalues
        ∂(gueP 3 (sz0.L n) (sz0.W n)))) atTop (𝓝 0) :=
  bUniv_holds hN h32 hML hLoc hQ hT 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible 1 le_rfl (1 / 10)
    (by norm_num) (19 / 10) (by norm_num) bump bump_testFun

end Inst

end RBM.Endpoints
