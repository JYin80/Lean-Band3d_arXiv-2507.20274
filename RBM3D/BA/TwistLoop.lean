/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.TwistStep2
import RBM3D.BA.TwistFold2
import RBM3D.BA.TwistKer2
import RBM3D.BA.TwistKer
import RBM3D.BA.EMn2BA
import RBM3D.BA.EKPins
import RBM3D.BA.KBase
import RBM3D.BA.Step1Setup
import RBM3D.Induction.ContinuityNet

/-!
# The net and the bootstrap in `Ξ` for the twisted 2-loop estimate

One induction step for the twisted 2-loop estimate (8.4) (`eq:TL2_BA`), `‖L̃ - K̃‖ ≺ B^{3/2}`, at the block Anderson model:
`BATwistLoopStep d R` says that (8.4) at the time sequence `s`, together with `twSteps` on `[s,t]`, gives (8.4) at every time sequence `τ ∈ [s,t]`.

* `baTwistLoopStep_of_fixed`: `BATwistStepFixed d R` gives `BATwistLoopStep d R` for every `d` and `R` (no regime is used).
  `BATwistStepFixed` is the per-time bound `‖Z_τ‖ ≺ B_τ^{3/2} (1 + B_τ^{1/6} Ξ)` from the uniform bound `‖Z_v‖ ≺ Ξ B_v^{3/2}` on `[s,t]`, `Z = L̃ - K̃`.
  Proof outline: round 0 is the a priori level `Ξ₀ = 2 (2/κ)² N⁴` (`TwistStep_zcrude`); the passage from the per-time bound at
  `τ ∈ [s,t]` to the bound uniform in `u ∈ [s,t]` is `cont_core` with the good event of `baGopbound`, a time-Lipschitz bound of `L̃`
  (entries of `G`) and of `K̃` (the resolvent identity of `Θ`); the level is iterated as `Ξ_{j+1} = 1 + N^{-c/6} Ξ_j` with `c`
  from `baEMn2ExpFacts`, and after `J` rounds `Ξ_J ≤ J + 1`.
* `baTwistLoopStep_caseI`, `baTwistLoopStep_caseII`: `baTwistLoopStep_of_fixed` at `baTwistStepFixed_caseI` and `baTwistStepFixed_caseII`.

Every statement is for every `d` (the hypothesis `3 ≤ d` enters through `BATwFrame`).  Private helpers carry the stem `TwistLoop_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.show false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open MeasureTheory Filter
open scoped Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

open private TwistKer_twLoopX_le from RBM3D.BA.TwistKer
open private TwistKer2_norm_sigma TwistKer2_M_le_one TwistKer2_norm_winv from RBM3D.BA.TwistKer2
open private BAKBase_sub from RBM3D.BA.KBase

/-! ## 1. Calculus of `≺` -/

/-- `ξ ≺ ζ'` and `ζ' ≤ c ζ` eventually give `ξ ≺ ζ` (`c ≤ N^{τ/2}` eventually). -/
private theorem TwistLoop_prec_of_le_const {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U : ℕ → Type*}
    {ξ ζ ζ' : ∀ l, U l → Ω → ℝ} {c : ℝ} (hsize : Tendsto size atTop atTop) (hζ : ∀ l u ω, 0 ≤ ζ l u ω)
    (hle : ∀ᶠ l in atTop, ∀ u ω, ζ' l u ω ≤ c * ζ l u ω) (h : StochDomAt P size ξ ζ') : StochDomAt P size ξ ζ := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [hle, hsize.eventually (eventually_le_rpow c (half_pos hτ))] with l hl hcN
  rintro ω ⟨u, hu⟩
  refine ⟨u, lt_of_le_of_lt ?_ hu⟩
  have hpos : 0 ≤ (size l : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc (size l : ℝ) ^ (τ / 2) * ζ' l u ω ≤ (size l : ℝ) ^ (τ / 2) * (c * ζ l u ω) :=
        mul_le_mul_of_nonneg_left (hl u ω) hpos
    _ ≤ (size l : ℝ) ^ (τ / 2) * ((size l : ℝ) ^ (τ / 2) * ζ l u ω) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcN (hζ l u ω)) hpos
    _ = (size l : ℝ) ^ τ * ζ l u ω := by rw [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half (size l) hτ]

/-! ## 2. Deterministic facts at the carrier -/

section Carrier

variable {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} {sz : Sizes d} {z : ℕ → ℂ}

/-- `1 - T₀ ≥ N⁻¹` as soon as `N^ε ≥ 2` (`1 - T₀ ≥ Im z/2 ≥ N^{-1+ε}/2`, `EMn2BA_one_sub_T0`). -/
private theorem TwistLoop_win (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ)
    (h2 : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ ε) : ((sz.size n : ℕ) : ℝ)⁻¹ ≤ 1 - BAflowT0 sz z n := by
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hT := EMn2BA_one_sub_T0 hκ sz hflow n
  have hNim : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ (z n).im := (hflow.2 n).2.1
  have e : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) = ((sz.size n : ℕ) : ℝ)⁻¹ * ((sz.size n : ℕ) : ℝ) ^ ε := by
    rw [Real.rpow_add hN0, Real.rpow_neg_one]
  have hi : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ)⁻¹ := inv_nonneg.2 hN0.le
  have := mul_le_mul_of_nonneg_left h2 hi
  rw [e] at hNim
  linarith

/-- `(1 - u)⁻¹ ≤ N` on `[0, T₀]` once `N^ε ≥ 2`. -/
private theorem TwistLoop_inv_one_sub_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ)
    (h2 : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ ε) {u : ℝ} (huT : u ≤ BAflowT0 sz z n) :
    (1 - u)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hw := TwistLoop_win hκ hflow n h2
  have h1 : ((sz.size n : ℕ) : ℝ)⁻¹ ≤ 1 - u := by linarith
  have := inv_anti₀ (inv_pos.2 hN0) h1
  rwa [inv_inv] at this

/-- Entries of `G_u` are at most `η_u⁻¹` (`TwistKer_entry_le`). -/
private theorem TwistLoop_G_entry (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u)
    (huT : u ≤ BAflowT0 sz z n) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖(baFMz sz z).G n u ω x y‖ ≤ ((baFMz sz z).eta n u)⁻¹ := by
  have hm := EMn2BA_mF_data sz hflow n
  have hT := EMn2BA_T0_lt_one hκ sz hflow n
  have hη : 0 < (baFMz sz z).eta n u :=
    mul_pos (by linarith) (by linarith [hm.1] : 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im)
  have hzim : (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) u).im = (baFMz sz z).eta n u :=
    ztOf_im _ _ _
  have hz : 0 < (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) u).im := by rw [hzim]; exact hη
  have h := TwistKer_entry_le (EMn2BA_seqHflowBA_herm sz (BAflowLam0 sz z) n u ω) hz true x y
  rw [hzim] at h
  exact h

/-- `η_u⁻¹ ≤ N/κ` on `[0, T₀]` once `N^ε ≥ 2`. -/
private theorem TwistLoop_eta_inv_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ)
    (h2 : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ ε) {u : ℝ} (huT : u ≤ BAflowT0 sz z n) :
    ((baFMz sz z).eta n u)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) * κ⁻¹ := by
  have hm := (EMn2BA_mF_data sz hflow n).1
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hw := TwistLoop_win hκ hflow n h2
  have h1 : ((sz.size n : ℕ) : ℝ)⁻¹ ≤ 1 - u := by linarith
  have h3 : ((sz.size n : ℕ) : ℝ)⁻¹ * κ ≤ (baFMz sz z).eta n u :=
    mul_le_mul h1 hm hκ.le ((inv_pos.2 hN0).le.trans h1)
  have hpos : 0 < ((sz.size n : ℕ) : ℝ)⁻¹ * κ := mul_pos (inv_pos.2 hN0) hκ
  calc ((baFMz sz z).eta n u)⁻¹ ≤ (((sz.size n : ℕ) : ℝ)⁻¹ * κ)⁻¹ := inv_anti₀ hpos h3
    _ = ((sz.size n : ℕ) : ℝ) * κ⁻¹ := by rw [mul_inv, inv_inv]

end Carrier

/-! ### `L̃` moves by at most `2 Q δ` when the entries of `G` move by `δ` -/

section LoopDiff

variable {d : ℕ} {sz : Sizes d}

private theorem TwistLoop_loopX_sub (n : ℕ) (X₁ X₂ X₁' X₂' : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (a c₁ c₂ : Zd d (sz.L n)) :
    twLoopX n X₁ X₂ a c₁ c₂ - twLoopX n X₁' X₂' a c₁ c₂ =
      twLoopX n X₁ (fun x y => X₂ x y - X₂' x y) a c₁ c₂ + twLoopX n (fun x y => X₁ x y - X₁' x y) X₂' a c₁ c₂ := by
  unfold twLoopX
  rw [← mul_sub, ← mul_add, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

private theorem TwistLoop_twChg_norm_le {ι : Type*} (G : ι → ι → ℂ) (σ : Bool) {Q : ℝ} (hQ : ∀ x y, ‖G x y‖ ≤ Q) (x y : ι) :
    ‖twChg G σ x y‖ ≤ Q := by
  unfold twChg
  split_ifs
  · exact hQ x y
  · rw [Complex.norm_conj]; exact hQ y x

private theorem TwistLoop_twChg_sub_le {ι : Type*} (G G' : ι → ι → ℂ) (σ : Bool) {δ : ℝ}
    (hδ : ∀ x y, ‖G x y - G' x y‖ ≤ δ) (x y : ι) : ‖twChg G σ x y - twChg G' σ x y‖ ≤ δ := by
  unfold twChg
  split_ifs
  · exact hδ x y
  · rw [← map_sub, Complex.norm_conj]; exact hδ y x

/-- **`L̃` is Lipschitz in `G`**: entries of `G_u`, `G_{u'}` at most `Q`, entries of the difference at most `δ`, then
`‖L̃_u - L̃_{u'}‖ ≤ 2 Q δ` (the average of `W^{2d}` products, `twLoopX` is bilinear). -/
private theorem TwistLoop_L2_diff (C : FlowFM sz) (n : ℕ) (u u' : ℝ) (ω : sz.SeqΩ) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n))
    {Q δ : ℝ} (hQ : ∀ x y, ‖C.G n u ω x y‖ ≤ Q) (hQ' : ∀ x y, ‖C.G n u' ω x y‖ ≤ Q)
    (hδ : ∀ x y, ‖C.G n u ω x y - C.G n u' ω x y‖ ≤ δ) :
    ‖twL2' C n u ω σ a c₁ c₂ - twL2' C n u' ω σ a c₁ c₂‖ ≤ 2 * (Q * δ) := by
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hQ (Classical.arbitrary _) (Classical.arbitrary _))
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ (Classical.arbitrary _) (Classical.arbitrary _))
  unfold twL2'
  rw [TwistLoop_loopX_sub]
  refine (norm_add_le _ _).trans ?_
  have h1 := TwistKer_twLoopX_le (sz := sz) n (twChg (C.G n u ω) (σ 0)) (fun x y => twChg (C.G n u ω) (σ 1) x y - twChg (C.G n u' ω) (σ 1) x y)
    a c₁ c₂ (m := δ * Q) (fun x _ w _ => by
      rw [norm_mul]
      exact mul_le_mul (TwistLoop_twChg_sub_le _ _ _ hδ _ _) (TwistLoop_twChg_norm_le _ _ hQ _ _) (norm_nonneg _) hδ0)
  have h2 := TwistKer_twLoopX_le (sz := sz) n (fun x y => twChg (C.G n u ω) (σ 0) x y - twChg (C.G n u' ω) (σ 0) x y) (twChg (C.G n u' ω) (σ 1))
    a c₁ c₂ (m := Q * δ) (fun x _ w _ => by
      rw [norm_mul]
      exact mul_le_mul (TwistLoop_twChg_norm_le _ _ hQ' _ _) (TwistLoop_twChg_sub_le _ _ _ hδ _ _) (norm_nonneg _) hQ0)
  linarith [mul_comm δ Q]

end LoopDiff

/-! ### `K̃` moves by at most `|u - u'| (1-u)⁻¹ (1-u')⁻¹` -/

section KDiff

open scoped Matrix.Norms.Operator

variable {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} {sz : Sizes d} {z : ℕ → ℂ}

/-- **`K̃` is Lipschitz in time**: `Θ_u - Θ_{u'} = (u - u') Θ_u M^{(σσ')} Θ_{u'}` (`BAKBase_sub`), `‖Θ_v‖_{∞→∞} ≤ (1-v)⁻¹`
(`EKPins_norm_Theta_le`), `‖M^{(σσ')}‖ ≤ 1` (`EKPins_norm_Q_le`), `|M| ≤ 1`, `W^{-d} ≤ 1`. -/
private theorem TwistLoop_K_diff (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {u u' : ℝ} (hu0 : 0 ≤ u)
    (huT : u ≤ BAflowT0 sz z n) (hu'0 : 0 ≤ u') (hu'T : u' ≤ BAflowT0 sz z n) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) :
    ‖twK (baFMz sz z) n u σ a c₁ c₂ - twK (baFMz sz z) n u' σ a c₁ c₂‖ ≤ |u - u'| * ((1 - u)⁻¹ * (1 - u')⁻¹) := by
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hT := EMn2BA_T0_lt_one hκ sz hflow n
  have hu1 : u < 1 := huT.trans_lt hT
  have hu'1 : u' < 1 := hu'T.trans_lt hT
  set Q := BAMss d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 0) (σ 1)
    with hQdef
  have hQ : ‖Q‖ ≤ 1 := EKPins_norm_Q_le hr (σ 0) (σ 1)
  have hΘu : ‖PropThetaQ Q u‖ ≤ (1 - u)⁻¹ := EKPins_norm_Theta_le hr hu0 hu1 (σ 0) (σ 1)
  have hΘu' : ‖PropThetaQ Q u'‖ ≤ (1 - u')⁻¹ := EKPins_norm_Theta_le hr hu'0 hu'1 (σ 0) (σ 1)
  have hsub := BAKBase_sub hQ (abs_lt.2 ⟨by linarith, hu1⟩ : |u| < 1) (abs_lt.2 ⟨by linarith, hu'1⟩ : |u'| < 1)
  have hdiff : ‖PropThetaQ Q u - PropThetaQ Q u'‖ ≤ |u - u'| * ((1 - u)⁻¹ * (1 - u')⁻¹) := by
    rw [hsub, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc ‖PropThetaQ Q u * Q * PropThetaQ Q u'‖ ≤ ‖PropThetaQ Q u * Q‖ * ‖PropThetaQ Q u'‖ := norm_mul_le _ _
      _ ≤ (‖PropThetaQ Q u‖ * ‖Q‖) * ‖PropThetaQ Q u'‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ ((1 - u)⁻¹ * 1) * (1 - u')⁻¹ :=
          mul_le_mul (mul_le_mul hΘu hQ (norm_nonneg _) (inv_nonneg.2 (by linarith))) hΘu' (norm_nonneg _) (by positivity)
      _ = (1 - u)⁻¹ * (1 - u')⁻¹ := by rw [mul_one]
  have hmB := EMn2BA_mF_data sz hflow n
  rw [twK_ba z n (by linarith [hmB.1]) u σ a c₁ c₂, twK_ba z n (by linarith [hmB.1]) u' σ a c₁ c₂, ← mul_sub, norm_mul,
    TwistKer2_norm_winv n, ← Finset.sum_sub_distrib]
  have hW1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 := by
    have : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    exact inv_le_one_of_one_le₀ (one_le_pow₀ this)
  have hrow := sum_norm_row_le (PropThetaQ Q u - PropThetaQ Q u') a
  have hsum : ‖∑ a', (BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) u (σ 0) (σ 1) a a' *
      BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 0) c₂ a' *
      BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 1) a' c₁ -
      BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) u' (σ 0) (σ 1) a a' *
      BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 0) c₂ a' *
      BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 1) a' c₁)‖ ≤
      ‖PropThetaQ Q u - PropThetaQ Q u'‖ := by
    refine (norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum fun a' _ => ?_) hrow)
    rw [← sub_mul, ← sub_mul, norm_mul, norm_mul]
    have h0 := TwistKer2_M_le_one hr (σ 0) c₂ a'
    have h1 := TwistKer2_M_le_one hr (σ 1) a' c₁
    have e : BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) u (σ 0) (σ 1) a a' -
        BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) u' (σ 0) (σ 1) a a' =
        (PropThetaQ Q u - PropThetaQ Q u') a a' := rfl
    rw [e]
    calc ‖(PropThetaQ Q u - PropThetaQ Q u') a a'‖ * ‖BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 0) c₂ a'‖ *
          ‖BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 1) a' c₁‖
        ≤ ‖(PropThetaQ Q u - PropThetaQ Q u') a a'‖ * 1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h0 (norm_nonneg _)) h1 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * _ ≤ 1 * ‖PropThetaQ Q u - PropThetaQ Q u'‖ :=
        mul_le_mul hW1 (hsum.trans le_rfl) (norm_nonneg _) zero_le_one
    _ ≤ _ := by rw [one_mul]; exact hdiff

end KDiff

/-! ### The closeness `ξ_u ≤ ξ_{u'} + N^{-3/2}` of `Z = L̃ - K̃` -/

section Close

variable {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} {sz : Sizes d} {z : ℕ → ℂ}

/-- The arithmetic of the net: with `N ≥ 4`, `N ≥ 8/κ`, `δ ≤ N^{-6}`, `Δ ≤ N^{-A}`, `A ≥ 22`:
`2 (N/κ) δ + Δ N² ≤ N^{-3/2}`. -/
private theorem TwistLoop_arith {N κ δ Δ A : ℝ} (hκ : 0 < κ) (hN4 : 4 ≤ N) (hNκ : 8 * κ⁻¹ ≤ N)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ N ^ (-(6 : ℝ))) (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ N ^ (-A)) (hA : 22 ≤ A) :
    2 * ((N * κ⁻¹) * δ) + Δ * (N * N) ≤ N ^ (-(3 / 2 : ℝ)) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have e2 : N ^ (-(2 : ℝ)) ≤ N ^ (-(3 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have e2' : N ^ (-(2 : ℝ)) = (N ^ 2)⁻¹ := by rw [Real.rpow_neg hN0.le]; norm_cast
  have e6 : N ^ (-(6 : ℝ)) = (N ^ 6)⁻¹ := by rw [Real.rpow_neg hN0.le]; norm_cast
  have hA' : N ^ (-A) ≤ N ^ (-(22 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have e22 : N ^ (-(22 : ℝ)) = (N ^ 22)⁻¹ := by rw [Real.rpow_neg hN0.le]; norm_cast
  rw [e6] at hδ
  rw [e22] at hA'
  set M : ℝ := N⁻¹ with hM
  have hM0 : 0 < M := inv_pos.2 hN0
  have hNM : N * M = 1 := mul_inv_cancel₀ hN0.ne'
  have hM4 : M ≤ 1 / 4 := by
    rw [hM]; calc N⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hN4
      _ = 1 / 4 := by norm_num
  have hinv : ∀ k : ℕ, (N ^ k)⁻¹ = M ^ k := fun k => by rw [hM]; exact (inv_pow N k).symm
  rw [hinv] at hδ hA'
  have hΔ' : Δ ≤ M ^ 22 := hΔ.trans hA'
  have hκN : κ⁻¹ ≤ N / 8 := by linarith
  have s1 : 2 * ((N * κ⁻¹) * δ) ≤ M ^ 4 / 4 := by
    calc 2 * ((N * κ⁻¹) * δ) ≤ 2 * ((N * (N / 8)) * M ^ 6) := by
          gcongr
      _ = (N * M) ^ 2 * M ^ 4 / 4 := by ring
      _ = M ^ 4 / 4 := by rw [hNM]; ring
  have s2 : Δ * (N * N) ≤ M ^ 20 := by
    calc Δ * (N * N) ≤ M ^ 22 * (N * N) := by gcongr
      _ = (N * M) ^ 2 * M ^ 20 := by ring
      _ = M ^ 20 := by rw [hNM]; ring
  have hMM : M ^ 2 ≤ N ^ (-(3 / 2 : ℝ)) := by
    refine le_trans (le_of_eq ?_) (e2'.symm ▸ e2 : (N ^ 2)⁻¹ ≤ N ^ (-(3 / 2 : ℝ)))
    rw [hinv]
  have h4 : M ^ 4 ≤ M ^ 2 / 16 := by
    have : M ^ 4 = M ^ 2 * M ^ 2 := by ring
    rw [this]
    have h2 : M ^ 2 ≤ 1 / 16 := by nlinarith
    nlinarith [sq_nonneg M]
  have h20 : M ^ 20 ≤ M ^ 2 / 16 := by
    have h18 : M ^ 18 ≤ 1 / 16 := by
      calc M ^ 18 ≤ M ^ 2 := pow_le_pow_of_le_one hM0.le (by linarith) (by norm_num)
        _ ≤ 1 / 16 := by nlinarith
    calc M ^ 20 = M ^ 2 * M ^ 18 := by ring
      _ ≤ M ^ 2 * (1 / 16) := by gcongr
      _ = M ^ 2 / 16 := by ring
  linarith [sq_nonneg M]

/-- **The closeness of `Z`**: for `u, u' ∈ [0, T₀]` with `N^ε ≥ 2`, if the entries of `G_u - G_{u'}` are at most `δ`, then
`‖Z_u‖ ≤ ‖Z_{u'}‖ + 2 (N/κ) δ + |u - u'| N²`. -/
private theorem TwistLoop_Z_close (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) (h2 : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ ε)
    {u u' : ℝ} (hu0 : 0 ≤ u) (huT : u ≤ BAflowT0 sz z n) (hu'0 : 0 ≤ u') (hu'T : u' ≤ BAflowT0 sz z n) (ω : sz.SeqΩ)
    {δ : ℝ} (hδ : ∀ x y, ‖(baFMz sz z).G n u ω x y - (baFMz sz z).G n u' ω x y‖ ≤ δ)
    (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) :
    ‖twL2' (baFMz sz z) n u ω σ a c₁ c₂ - twK (baFMz sz z) n u σ a c₁ c₂‖ ≤
      ‖twL2' (baFMz sz z) n u' ω σ a c₁ c₂ - twK (baFMz sz z) n u' σ a c₁ c₂‖ +
        (2 * ((((sz.size n : ℕ) : ℝ) * κ⁻¹) * δ) + |u - u'| * (((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ))) := by
  have hQ := TwistLoop_eta_inv_le hκ hflow n h2 huT
  have hQ' := TwistLoop_eta_inv_le hκ hflow n h2 hu'T
  have hL := TwistLoop_L2_diff (baFMz sz z) n u u' ω σ a c₁ c₂ (Q := ((sz.size n : ℕ) : ℝ) * κ⁻¹) (δ := δ)
    (fun x y => (TwistLoop_G_entry hκ hflow n hu0 huT ω x y).trans hQ)
    (fun x y => (TwistLoop_G_entry hκ hflow n hu'0 hu'T ω x y).trans hQ') hδ
  have hK := TwistLoop_K_diff hκ hflow n hu0 huT hu'0 hu'T σ a c₁ c₂
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hi := TwistLoop_inv_one_sub_le hκ hflow n h2 huT
  have hi' := TwistLoop_inv_one_sub_le hκ hflow n h2 hu'T
  have hT := EMn2BA_T0_lt_one hκ sz hflow n
  have hpos : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 (by linarith)
  have hK' : |u - u'| * ((1 - u)⁻¹ * (1 - u')⁻¹) ≤ |u - u'| * (((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hi hi' (inv_nonneg.2 (by linarith)) (by linarith)) (abs_nonneg _)
  have e : twL2' (baFMz sz z) n u ω σ a c₁ c₂ - twK (baFMz sz z) n u σ a c₁ c₂ =
      (twL2' (baFMz sz z) n u' ω σ a c₁ c₂ - twK (baFMz sz z) n u' σ a c₁ c₂) +
        (twL2' (baFMz sz z) n u ω σ a c₁ c₂ - twL2' (baFMz sz z) n u' ω σ a c₁ c₂) -
        (twK (baFMz sz z) n u σ a c₁ c₂ - twK (baFMz sz z) n u' σ a c₁ c₂) := by ring
  rw [e]
  calc _ ≤ ‖(twL2' (baFMz sz z) n u' ω σ a c₁ c₂ - twK (baFMz sz z) n u' σ a c₁ c₂) +
        (twL2' (baFMz sz z) n u ω σ a c₁ c₂ - twL2' (baFMz sz z) n u' ω σ a c₁ c₂)‖ +
        ‖twK (baFMz sz z) n u σ a c₁ c₂ - twK (baFMz sz z) n u' σ a c₁ c₂‖ := norm_sub_le _ _
    _ ≤ (‖twL2' (baFMz sz z) n u' ω σ a c₁ c₂ - twK (baFMz sz z) n u' σ a c₁ c₂‖ +
        ‖twL2' (baFMz sz z) n u ω σ a c₁ c₂ - twL2' (baFMz sz z) n u' ω σ a c₁ c₂‖) +
        ‖twK (baFMz sz z) n u σ a c₁ c₂ - twK (baFMz sz z) n u' σ a c₁ c₂‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ _ := by linarith

end Close

/-- `N Δ ≤ 1/4` for `Δ ≤ N^{-A}`, `A ≥ 22`, `N ≥ 4`. -/
private theorem TwistLoop_small {N Δ A : ℝ} (hN4 : 4 ≤ N) (hΔ : Δ ≤ N ^ (-A)) (hA : 22 ≤ A) : N * Δ ≤ 1 / 4 := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hA' : N ^ (-A) ≤ N ^ (-(22 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have e22 : N ^ (-(22 : ℝ)) = (N ^ 22)⁻¹ := by rw [Real.rpow_neg hN0.le]; norm_cast
  rw [e22] at hA'
  have h1 : N * Δ ≤ N * (N ^ 22)⁻¹ := mul_le_mul_of_nonneg_left (hΔ.trans hA') hN0.le
  have h2 : N * (N ^ 22)⁻¹ = (N ^ 21)⁻¹ := by
    field_simp
  have h3 : (N ^ 21)⁻¹ ≤ (4 : ℝ)⁻¹ := by
    refine inv_anti₀ (by norm_num) ?_
    calc (4 : ℝ) = 4 ^ 1 := by norm_num
      _ ≤ N ^ 1 := pow_le_pow_left₀ (by norm_num) hN4 1
      _ ≤ N ^ 21 := pow_le_pow_right₀ hN1 (by norm_num)
  rw [h2] at h1
  have : (4 : ℝ)⁻¹ = 1 / 4 := by norm_num
  linarith

/-- The control `Bctl^{3/2}` moves by at most a factor `2` under a time change `x ≤ 1/4`. -/
private theorem TwistLoop_zeta_ratio {B B' x : ℝ} (hB' : 0 ≤ B') (hx0 : 0 ≤ x) (hx : x ≤ 1 / 4) (hr : B' ≤ (1 + x) * B) (hB : 0 ≤ B) :
    B' ^ (3 / 2 : ℝ) ≤ 2 * B ^ (3 / 2 : ℝ) := by
  have h1 : B' ^ (3 / 2 : ℝ) ≤ ((1 + x) * B) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow hB' hr (by norm_num)
  rw [Real.mul_rpow (by linarith) hB] at h1
  have h2 : (1 + x) ^ (3 / 2 : ℝ) ≤ 2 := by
    calc (1 + x) ^ (3 / 2 : ℝ) ≤ (1 + x) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = (1 + x) ^ 2 := by rw [Real.rpow_two]
      _ ≤ 2 := by nlinarith
  have h3 : 0 ≤ B ^ (3 / 2 : ℝ) := Real.rpow_nonneg hB _
  nlinarith

/-- The uniform-in-time statement of the bootstrap at the deterministic level `Ξ` (the hypothesis of `BATwistStepFixed`). -/
private def TwistLoop_Unif {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (Ξ : ℕ → ℝ) : Prop :=
  PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
    (fun n p ω => ‖twL2' (baFMz sz z) n (p.1 : ℝ) ω p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 - twK (baFMz sz z) n (p.1 : ℝ) p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2‖)
    (fun n p _ => Ξ n * sz.Bctl n (p.1 : ℝ) ^ (3 / 2 : ℝ))

/-- The per-time statement at the level `Ξ` (the hypothesis of `cont_core`). -/
private def TwistLoop_Pt {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (Ξ : ℕ → ℝ) : Prop :=
  PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size
    (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
    (fun n p ω => ‖twL2' (baFMz sz z) n (p.1 : ℝ) ω p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 - twK (baFMz sz z) n (p.1 : ℝ) p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2‖)
    (fun n p _ => Ξ n * sz.Bctl n (p.1 : ℝ) ^ (3 / 2 : ℝ))

section Net

open RBM.Ind RBM.Ind.ContinuityNet

variable {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} {sz : Sizes d} {z : ℕ → ℂ}

/-- **The net**: the per-time statement at the level `Ξ ≥ 1` gives the uniform one (`cont_core` with the good event of
`baGopbound` at `C = 6`, the mesh `N^{-(C' + 22)}`, `#V ≤ N⁴`, `ε_n = N^{-3/2}`, `B ≥ N⁻¹`). -/
private theorem TwistLoop_net (hκ : 0 < κ) (hε : 0 < ε) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ BAflowT0 sz z n) {Ξ : ℕ → ℝ} (hΞ : ∀ n, 1 ≤ Ξ n)
    (hpt : TwistLoop_Pt sz z s t Ξ) : TwistLoop_Unif sz z s t Ξ := by
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hsize := tendsto_size sz hsz
  have hcast : Tendsto (fun n : ℕ => ((sz.size n : ℕ) : ℝ)) atTop atTop := hsz
  have hT := fun n => EMn2BA_T0_lt_one hκ sz hflow n
  have hlen : ∀ n, t n - s n ≤ 1 := fun n => by linarith [hs n, htT n, hT n]
  have hm : ∀ n, κ ≤ (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := fun n => (EMn2BA_mF_data sz hflow n).1
  have hm1 : ∀ n, ‖BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n‖ ≤ 1 := fun n => by
    have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
    exact BAm_norm_le_one d (sz.L n) _ ((BAflowEs sz z n : ℝ) : ℂ) _ (by simp) hr.1
  obtain ⟨C', hC', hGop⟩ := baGopbound d sz (BAflowLam0 sz z) (BAflowEs sz z) κ hκ hm hm1 hsz 6 (by norm_num)
  set bad : ℕ → Set sz.SeqΩ := fun n => {ω | ∃ u u' : ℝ, 0 ≤ u ∧ 0 ≤ u' ∧ u ≤ 1 - ((sz.size n : ℕ) : ℝ)⁻¹ ∧
      u' ≤ 1 - ((sz.size n : ℕ) : ℝ)⁻¹ ∧ |u - u'| ≤ ((sz.size n : ℕ) : ℝ) ^ (-C') ∧
      ∃ x y : Idx d (sz.L n) (sz.W n), ((sz.size n : ℕ) : ℝ) ^ (-(6 : ℝ)) <
        ‖BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n u ω x y - BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n u' ω x y‖} with hbad
  have hgood : HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size (fun n => (bad n)ᶜ) := by
    intro D hD
    filter_upwards [hGop D hD] with n hn
    refine le_trans (le_of_eq ?_) hn
    congr 1
    exact compl_compl _
  have hcard : ∀ᶠ n : ℕ in atTop, (Fintype.card ((Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) : ℝ) ≤
      ((sz.size n : ℕ) : ℝ) ^ (4 : ℝ) := by
    filter_upwards [hcast.eventually_ge_atTop 4] with n h4
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have hcardZ : Fintype.card (Zd d (sz.L n)) = sz.L n ^ d := by simp [Zd, ZMod.card]
    have hW1 : (1 : ℝ) ≤ (sz.W n : ℝ) := by exact_mod_cast sz.W_pos n
    have hL0 : (0 : ℝ) ≤ (sz.L n : ℝ) := Nat.cast_nonneg _
    have hLW : (sz.L n : ℝ) ≤ (sz.W n : ℝ) * (sz.L n : ℝ) := le_mul_of_one_le_left hL0 hW1
    have eN : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℝ) * (sz.L n : ℝ)) ^ d := by simp [Sizes.size]
    have hLN : (sz.L n : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
      rw [eN]; exact pow_le_pow_left₀ hL0 hLW d
    have hc : (Fintype.card ((Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) : ℝ) =
        4 * (((sz.L n : ℕ) : ℝ) ^ d) ^ 3 := by
      rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, hcardZ]
      push_cast
      ring
    have e4 : ((sz.size n : ℕ) : ℝ) ^ (4 : ℝ) = ((sz.size n : ℕ) : ℝ) ^ 4 := by norm_cast
    rw [hc, e4]
    calc 4 * (((sz.L n : ℕ) : ℝ) ^ d) ^ 3 ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ 3 :=
          mul_le_mul h4 (pow_le_pow_left₀ (by positivity) hLN 3) (by positivity) hN0.le
      _ = ((sz.size n : ℕ) : ℝ) ^ 4 := by ring
  have hlow : ∀ᶠ n : ℕ in atTop, ∀ (p : TimeIcc s t n × ((Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))) (ω : sz.SeqΩ),
      ((sz.size n : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) ≤ Ξ n * sz.Bctl n (p.1 : ℝ) ^ (3 / 2 : ℝ) := by
    refine Eventually.of_forall fun n p ω => ?_
    have hp1 : (p.1 : ℝ) < 1 := (p.1.2.2.trans (htT n)).trans_lt (hT n)
    have hB := cont_inv_size_le_Bctl sz n ((hs n).trans p.1.2.1) hp1
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by
      have := sz.one_le_size n
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
    have e : ((sz.size n : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) = (((sz.size n : ℕ) : ℝ)⁻¹) ^ (3 / 2 : ℝ) := by
      rw [Real.inv_rpow hN0.le, Real.rpow_neg hN0.le]
    rw [e]
    calc (((sz.size n : ℕ) : ℝ)⁻¹) ^ (3 / 2 : ℝ) ≤ sz.Bctl n (p.1 : ℝ) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow (inv_nonneg.2 hN0.le) hB (by norm_num)
      _ = 1 * sz.Bctl n (p.1 : ℝ) ^ (3 / 2 : ℝ) := (one_mul _).symm
      _ ≤ Ξ n * sz.Bctl n (p.1 : ℝ) ^ (3 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (hΞ n) (Real.rpow_nonneg (le_trans (inv_nonneg.2 hN0.le) hB) _)
  have hclose : ∀ᶠ n : ℕ in atTop, ∀ ω ∈ (fun n => (bad n)ᶜ) n, ∀ u u' : TimeIcc s t n,
      |(u : ℝ) - (u' : ℝ)| ≤ ((sz.size n : ℕ) : ℝ) ^ (-(C' + 22)) →
      ∀ v : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n),
        ‖twL2' (baFMz sz z) n (u : ℝ) ω v.1 v.2.1 v.2.2.1 v.2.2.2 - twK (baFMz sz z) n (u : ℝ) v.1 v.2.1 v.2.2.1 v.2.2.2‖ ≤
          ‖twL2' (baFMz sz z) n (u' : ℝ) ω v.1 v.2.1 v.2.2.1 v.2.2.2 - twK (baFMz sz z) n (u' : ℝ) v.1 v.2.1 v.2.2.1 v.2.2.2‖ +
            ((sz.size n : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) ∧
        Ξ n * sz.Bctl n (u' : ℝ) ^ (3 / 2 : ℝ) ≤ 2 * (Ξ n * sz.Bctl n (u : ℝ) ^ (3 / 2 : ℝ)) := by
    filter_upwards [hcast.eventually_ge_atTop 4, hcast.eventually_ge_atTop (8 * κ⁻¹),
      hsize.eventually (eventually_le_rpow 2 hε)] with n h4 h8 h2
    intro ω hω u u' hΔ v
    obtain ⟨σ, a, c₁, c₂⟩ := v
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
    have hΔ' : |(u : ℝ) - (u' : ℝ)| ≤ ((sz.size n : ℕ) : ℝ) ^ (-C') :=
      hΔ.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
    have hw := TwistLoop_win hκ hflow n h2
    have hwin : ∀ w : TimeIcc s t n, (w : ℝ) ≤ 1 - ((sz.size n : ℕ) : ℝ)⁻¹ := fun w => by
      linarith [w.2.2, htT n]
    have hu0 : 0 ≤ (u : ℝ) := (hs n).trans u.2.1
    have hu'0 : 0 ≤ (u' : ℝ) := (hs n).trans u'.2.1
    have huT : (u : ℝ) ≤ BAflowT0 sz z n := u.2.2.trans (htT n)
    have hu'T : (u' : ℝ) ≤ BAflowT0 sz z n := u'.2.2.trans (htT n)
    have hδ : ∀ x y, ‖(baFMz sz z).G n (u : ℝ) ω x y - (baFMz sz z).G n (u' : ℝ) ω x y‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (-(6 : ℝ)) := by
      intro x y
      by_contra hlt
      push Not at hlt
      refine hω ?_
      exact ⟨(u : ℝ), (u' : ℝ), hu0, hu'0, hwin u, hwin u', hΔ', x, y, hlt⟩
    refine ⟨?_, ?_⟩
    · have hZ := TwistLoop_Z_close hκ hflow n h2 hu0 huT hu'0 hu'T ω hδ σ a c₁ c₂
      have hA := TwistLoop_arith (N := ((sz.size n : ℕ) : ℝ)) (κ := κ) (δ := ((sz.size n : ℕ) : ℝ) ^ (-(6 : ℝ)))
        (Δ := |(u : ℝ) - (u' : ℝ)|) (A := C' + 22) hκ h4 h8 (Real.rpow_nonneg (by linarith) _) le_rfl (abs_nonneg _) hΔ
        (by linarith)
      exact hZ.trans (by linarith)
    · have hT1 : t n < 1 := (htT n).trans_lt (hT n)
      have hr := cont_Bctl_ratio sz n hT1 u'.2.2 u.2.2
      have hpi : (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := TwistLoop_inv_one_sub_le hκ hflow n h2 (htT n)
      have hx : (1 - t n)⁻¹ * |(u' : ℝ) - (u : ℝ)| ≤ 1 / 4 := by
        have hsm := TwistLoop_small (Δ := |(u' : ℝ) - (u : ℝ)|) h4 (by rw [abs_sub_comm]; exact hΔ) (by linarith)
        exact (mul_le_mul_of_nonneg_right hpi (abs_nonneg _)).trans hsm
      have hx0 : 0 ≤ (1 - t n)⁻¹ * |(u' : ℝ) - (u : ℝ)| :=
        mul_nonneg (inv_nonneg.2 (by linarith)) (abs_nonneg _)
      have hB' : 0 ≤ sz.Bctl n (u' : ℝ) := (inv_nonneg.2 (by linarith)).trans
        (cont_inv_size_le_Bctl sz n hu'0 (u'.2.2.trans_lt hT1))
      have hB : 0 ≤ sz.Bctl n (u : ℝ) := (inv_nonneg.2 (by linarith)).trans
        (cont_inv_size_le_Bctl sz n hu0 (u.2.2.trans_lt hT1))
      have := TwistLoop_zeta_ratio hB' hx0 hx hr hB
      have hΞ0 : 0 ≤ Ξ n := by linarith [hΞ n]
      calc Ξ n * sz.Bctl n (u' : ℝ) ^ (3 / 2 : ℝ) ≤ Ξ n * (2 * sz.Bctl n (u : ℝ) ^ (3 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left this hΞ0
        _ = 2 * (Ξ n * sz.Bctl n (u : ℝ) ^ (3 / 2 : ℝ)) := by ring
  exact cont_core (V := fun n => (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) hsize
    (fun n => (hst n).le) hlen (A := C' + 22) (Cv := 4) (by linarith) (by norm_num) hcard hpt hgood
    (ε := fun n => ((sz.size n : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) hlow hclose

end Net

/-! ## 3. The iteration of the level -/

section Boot

variable {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} {sz : Sizes d} {z : ℕ → ℂ}

/-- The statement `BATwistStepFixed` at the carrier `baFMz sz z`: the per-`τ` bound from the uniform bootstrap bound at the level `Ξ`. -/
private def TwistLoop_Step {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) : Prop :=
  ∀ Ξ : ℕ → ℝ, (∀ n, 1 ≤ Ξ n) → TwistLoop_Unif sz z s t Ξ → ∀ τ : ℕ → ℝ, (∀ n, s n ≤ τ n) → (∀ n, τ n ≤ t n) →
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p ω => ‖twL2' (baFMz sz z) n (τ n) ω p.1 p.2.1 p.2.2.1 p.2.2.2 - twK (baFMz sz z) n (τ n) p.1 p.2.1 p.2.2.1 p.2.2.2‖)
      (fun n _ _ => sz.Bctl n (τ n) ^ (3 / 2 : ℝ) * (1 + sz.Bctl n (τ n) ^ (1 / 6 : ℝ) * Ξ n))

/-- The level `Ξ_j`: `Ξ₀ = X₀`, `Ξ_{j+1} = 1 + b Ξ_j`. -/
private def TwistLoop_Xi (X0 b : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => X0
  | j + 1 => fun n => 1 + b n * TwistLoop_Xi X0 b j n

/-- `Ξ_j ≤ j + b^j X₀` for `0 ≤ b ≤ 1`. -/
private theorem TwistLoop_Xi_le (X0 b : ℕ → ℝ) (hb0 : ∀ n, 0 ≤ b n) (hb1 : ∀ n, b n ≤ 1) (hX0 : ∀ n, 0 ≤ X0 n) (n : ℕ) :
    ∀ j : ℕ, TwistLoop_Xi X0 b j n ≤ j + b n ^ j * X0 n := by
  intro j
  induction j with
  | zero => simp [TwistLoop_Xi]
  | succ j ih =>
    simp only [TwistLoop_Xi]
    have h1 : b n * TwistLoop_Xi X0 b j n ≤ b n * (j + b n ^ j * X0 n) := mul_le_mul_of_nonneg_left ih (hb0 n)
    have h2 : b n * (j : ℝ) ≤ j := by nlinarith [hb0 n, hb1 n, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have e : b n * ((j : ℝ) + b n ^ j * X0 n) = b n * j + b n ^ (j + 1) * X0 n := by ring
    push_cast
    linarith

/-- The a priori round: `Ξ₀ = 2 (2/κ)² N⁴` (`TwistStep_zcrude`). -/
private theorem TwistLoop_unif_zero (hκ : 0 < κ) (hε : 0 < ε) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n)
    (htT : ∀ n, t n ≤ BAflowT0 sz z n) :
    TwistLoop_Unif sz z s t (fun n => 2 * (2 / κ) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ 4) := by
  refine (sz.withLam 0).ST_prec_of_le_ev (fun n p ω => ?_) (Filter.Eventually.of_forall fun n p ω => ?_)
  · have hp1 : (p.1 : ℝ) < 1 := (p.1.2.2.trans (htT n)).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
    have := (st_Bctl_pos sz (n := n) hp1).le
    positivity
  · exact TwistStep_zcrude hκ hε hflow n ((hs n).trans p.1.2.1) (p.1.2.2.trans (htT n)) ω p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2

/-- **One round**: the level `Ξ` gives the level `1 + b Ξ` (`b ≥ Bctl^{1/6}` on `[0, T₀]`, eventually): per `τ` by `BATwistStepFixed`,
per time by the sections (`perTimeDomAt_iff_forall_section`), uniform by the net. -/
private theorem TwistLoop_round (hκ : 0 < κ) (hε : 0 < ε) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ BAflowT0 sz z n) (hF : TwistLoop_Step sz z s t) {b : ℕ → ℝ} (hb0 : ∀ n, 0 ≤ b n)
    (hb : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ BAflowT0 sz z n → sz.Bctl n u ^ (1 / 6 : ℝ) ≤ b n)
    {Ξ : ℕ → ℝ} (hΞ : ∀ n, 1 ≤ Ξ n) (hU : TwistLoop_Unif sz z s t Ξ) :
    TwistLoop_Unif sz z s t (fun n => 1 + b n * Ξ n) := by
  have hsize := tendsto_size sz hflow.1.2.2.1
  have hΞ' : ∀ n, 1 ≤ 1 + b n * Ξ n := fun n => by
    have := mul_nonneg (hb0 n) (by linarith [hΞ n] : 0 ≤ Ξ n)
    linarith
  refine TwistLoop_net hκ hε hflow hs hst htT hΞ' ?_
  unfold TwistLoop_Pt
  rw [perTimeDomAt_iff_forall_section _ _ (fun n => ⟨⟨⟨s n, le_rfl, (hst n).le⟩, fun _ => true, 0, 0, 0⟩⟩)]
  intro p
  have h1 := hF Ξ hΞ hU (fun n => ((p n).1 : ℝ)) (fun n => (p n).1.2.1) (fun n => (p n).1.2.2)
  have h2 := StochDomAt.precomp_param (V := fun _ => Unit) h1 (fun n (_ : Unit) => (p n).2)
  refine TwistLoop_prec_of_le_const (c := 1) hsize (fun n u ω => ?_) ?_ h2
  · have hp1 : ((p n).1 : ℝ) < 1 := ((p n).1.2.2.trans (htT n)).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
    have h0 := (st_Bctl_pos sz (n := n) hp1).le
    have hbΞ := mul_nonneg (hb0 n) (by linarith [hΞ n] : 0 ≤ Ξ n)
    positivity
  · filter_upwards [hb] with n hbn
    intro u ω
    have hp1 : ((p n).1 : ℝ) < 1 := ((p n).1.2.2.trans (htT n)).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
    have h0 := (st_Bctl_pos sz (n := n) hp1).le
    have hbn' := hbn ((p n).1 : ℝ) ((hs n).trans (p n).1.2.1) ((p n).1.2.2.trans (htT n))
    have hΞ0 : 0 ≤ Ξ n := by linarith [hΞ n]
    have h3 : 0 ≤ sz.Bctl n ((p n).1 : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg h0 _
    have h4 : sz.Bctl n ((p n).1 : ℝ) ^ (1 / 6 : ℝ) * Ξ n ≤ b n * Ξ n := mul_le_mul_of_nonneg_right hbn' hΞ0
    show sz.Bctl n ((p n).1 : ℝ) ^ (3 / 2 : ℝ) * (1 + sz.Bctl n ((p n).1 : ℝ) ^ (1 / 6 : ℝ) * Ξ n) ≤
      1 * ((1 + b n * Ξ n) * sz.Bctl n ((p n).1 : ℝ) ^ (3 / 2 : ℝ))
    nlinarith

/-- All the levels `Ξ_j` satisfy the uniform bootstrap bound. -/
private theorem TwistLoop_levels (hκ : 0 < κ) (hε : 0 < ε) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ BAflowT0 sz z n) (hF : TwistLoop_Step sz z s t) {b : ℕ → ℝ} (hb0 : ∀ n, 0 ≤ b n)
    (hb : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ BAflowT0 sz z n → sz.Bctl n u ^ (1 / 6 : ℝ) ≤ b n)
    {X0 : ℕ → ℝ} (hX0 : ∀ n, 1 ≤ X0 n) (hU0 : TwistLoop_Unif sz z s t X0) (j : ℕ) :
    (∀ n, 1 ≤ TwistLoop_Xi X0 b j n) ∧ TwistLoop_Unif sz z s t (TwistLoop_Xi X0 b j) := by
  induction j with
  | zero => exact ⟨hX0, hU0⟩
  | succ j ih =>
    refine ⟨fun n => ?_, TwistLoop_round hκ hε hflow hs hst htT hF hb0 hb ih.1 ih.2⟩
    have := mul_nonneg (hb0 n) (by linarith [ih.1 n] : 0 ≤ TwistLoop_Xi X0 b j n)
    show 1 ≤ 1 + b n * TwistLoop_Xi X0 b j n
    linarith

/-- **The bootstrap**: from the per-`τ` step, (8.4) at every `τ ∈ [s,t]` (round 0 at `Ξ₀ = 2 (2/κ)² N⁴`; `Bctl ≤ N^{-c}` on `[0,T₀]`,
`baEMn2ExpFacts`; `J = ⌈30/c⌉` rounds give `Ξ_J ≤ J + 1`; one more round and the constant `J + 2` is absorbed). -/
private theorem TwistLoop_core (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ BAflowT0 sz z n) (hF : TwistLoop_Step sz z s t)
    (τ : ℕ → ℝ) (hsτ : ∀ n, s n ≤ τ n) (hτt : ∀ n, τ n ≤ t n) :
    BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) τ := by
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hsize := tendsto_size sz hsz
  have hcast : Tendsto (fun n : ℕ => ((sz.size n : ℕ) : ℝ)) atTop atTop := hsz
  obtain ⟨-, -, cB, c, hcB, hc, hev⟩ := (baEMn2ExpFacts d).2 κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow
  have hN1 : ∀ n, (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.one_le_size n
  set b : ℕ → ℝ := fun n => ((sz.size n : ℕ) : ℝ) ^ (-(c / 6)) with hbdef
  have hb0 : ∀ n, 0 ≤ b n := fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hb1 : ∀ n, b n ≤ 1 := fun n => Real.rpow_le_one_of_one_le_of_nonpos (hN1 n) (by linarith)
  have hb : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ BAflowT0 sz z n → sz.Bctl n u ^ (1 / 6 : ℝ) ≤ b n := by
    filter_upwards [hev] with n hn u hu0 huT
    have hBu := (hn u hu0 huT).2
    have hu1 : u < 1 := huT.trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
    have hB0 : 0 ≤ sz.Bctl n u := (st_Bctl_pos sz hu1).le
    calc sz.Bctl n u ^ (1 / 6 : ℝ) ≤ (((sz.size n : ℕ) : ℝ) ^ (-c)) ^ (1 / 6 : ℝ) := Real.rpow_le_rpow hB0 hBu (by norm_num)
      _ = ((sz.size n : ℕ) : ℝ) ^ (-(c / 6)) := by
          rw [← Real.rpow_mul (Nat.cast_nonneg _)]
          congr 1
          ring
  set X0 : ℕ → ℝ := fun n => 2 * (2 / κ) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ 4 with hX0def
  have hκ1 : κ ≤ 1 := by
    have := EMn2BA_mF_data sz hflow 0
    linarith [this.1, this.2]
  have hk1 : (1 : ℝ) ≤ 2 / κ := by rw [le_div_iff₀ hκ]; linarith
  have hX0 : ∀ n, 1 ≤ X0 n := fun n => by
    have h4N : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ 4 := one_le_pow₀ (hN1 n)
    have h2k : (1 : ℝ) ≤ (2 / κ) ^ 2 := one_le_pow₀ hk1
    simp only [hX0def]
    nlinarith
  have hlev := TwistLoop_levels hκ hε hflow hs hst htT hF hb0 hb hX0 (TwistLoop_unif_zero hκ hε hflow hs htT)
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, 5 ≤ (J : ℝ) * (c / 6) := by
    refine ⟨⌈30 / c⌉₊, ?_⟩
    have h1 := Nat.le_ceil (30 / c)
    rw [div_le_iff₀ hc] at h1
    nlinarith
  have hXJ : ∀ᶠ n in atTop, TwistLoop_Xi X0 b J n ≤ (J : ℝ) + 1 := by
    filter_upwards [hcast.eventually_ge_atTop (2 * (2 / κ) ^ 2)] with n hn
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith [hN1 n]
    have h1 := TwistLoop_Xi_le X0 b hb0 hb1 (fun n => by linarith [hX0 n]) n J
    have hbJ : b n ^ J ≤ ((sz.size n : ℕ) : ℝ) ^ (-(5 : ℝ)) := by
      calc b n ^ J = ((sz.size n : ℕ) : ℝ) ^ (-(c / 6) * (J : ℝ)) := by
            simp only [hbdef]
            rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
        _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-(5 : ℝ)) := Real.rpow_le_rpow_of_exponent_le (hN1 n) (by linarith)
    have e5 : ((sz.size n : ℕ) : ℝ) ^ (-(5 : ℝ)) = (((sz.size n : ℕ) : ℝ) ^ 5)⁻¹ := by
      rw [Real.rpow_neg hN0.le]; norm_cast
    rw [e5] at hbJ
    have h2 : b n ^ J * X0 n ≤ 1 := by
      calc b n ^ J * X0 n ≤ (((sz.size n : ℕ) : ℝ) ^ 5)⁻¹ * (2 * (2 / κ) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ 4) :=
            mul_le_mul hbJ le_rfl (by linarith [hX0 n]) (by positivity)
        _ = (2 * (2 / κ) ^ 2) / ((sz.size n : ℕ) : ℝ) := by field_simp
        _ ≤ 1 := by rw [div_le_one hN0]; exact hn
    linarith
  have hStep := hF (TwistLoop_Xi X0 b J) (hlev J).1 (hlev J).2 τ hsτ hτt
  unfold BATwistLoopLaw PrecL
  refine TwistLoop_prec_of_le_const (c := (J : ℝ) + 2) hsize (fun n u ω => ?_) ?_ hStep
  · have hτ1 : τ n < 1 := ((hτt n).trans (htT n)).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
    exact Real.rpow_nonneg (st_Bctl_pos sz hτ1).le _
  · filter_upwards [hXJ, hb] with n hX hbn
    intro u ω
    have hτ1 : τ n < 1 := ((hτt n).trans (htT n)).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
    have hB0 : 0 ≤ sz.Bctl n (τ n) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (st_Bctl_pos sz hτ1).le _
    have hbn' := hbn (τ n) ((hs n).trans (hsτ n)) ((hτt n).trans (htT n))
    have hXn := (hlev J).1 n
    have hq : sz.Bctl n (τ n) ^ (1 / 6 : ℝ) * TwistLoop_Xi X0 b J n ≤ (J : ℝ) + 1 :=
      calc _ ≤ 1 * TwistLoop_Xi X0 b J n :=
            mul_le_mul_of_nonneg_right (hbn'.trans (hb1 n)) (by linarith)
        _ ≤ _ := by linarith
    nlinarith

end Boot

/-! ## 4. `BATwistLoopStep` from `BATwistStepFixed` -/

/-- `BATwistStepFixed d R` gives `BATwistLoopStep d R`, for every `d` and every regime `R` (the net and the bootstrap use no regime).
The constant `𝔠d` of the conclusion is the one of `h` at the same `(κ, ε, 𝔡, Cd)`. -/
theorem baTwistLoopStep_of_fixed (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h : BATwistStepFixed d R) :
    BATwistLoopStep d R := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h𝔠d, h𝔠d1, hfix⟩ := h hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨𝔠d, h𝔠d, h𝔠d1, fun 𝔠 sz z hflow s t hs hst htT hR hST hsteps hTL2 τ hsτ hτt => ?_⟩
  exact TwistLoop_core hκ hε h𝔡 hflow hs hst htT
    (fun Ξ hΞ hU τ' h1 h2 => hfix 𝔠 sz z hflow s t hs hst htT hR hST hsteps hTL2 Ξ hΞ hU τ' h1 h2) τ hsτ hτt

/-- The regime `STCaseI`: `BATwistLoopStep d STCaseI`. -/
theorem baTwistLoopStep_caseI (d : ℕ) : BATwistLoopStep d STCaseI :=
  baTwistLoopStep_of_fixed d STCaseI (baTwistStepFixed_caseI d)

/-- The regime `STCaseII`: `BATwistLoopStep d STCaseII`. -/
theorem baTwistLoopStep_caseII (d : ℕ) : BATwistLoopStep d STCaseII :=
  baTwistLoopStep_of_fixed d STCaseII (baTwistStepFixed_caseII d)

end RBM.BA

end
