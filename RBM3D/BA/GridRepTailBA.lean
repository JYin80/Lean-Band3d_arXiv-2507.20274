/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.GridRepTailGen2
import RBM3D.BA.GridMartBA
import RBM3D.BA.TwistKer
import RBM3D.BA.TwistGridWTail
import RBM3D.BA.TwistGridWTail2
import RBM3D.BA.TwistGridTail2
import RBM3D.BA.TwistGridRem2
import RBM3D.BA.GreenSchur
import RBM3D.BA.EMn2BA

/-!
# The two-slot BA tail and the full loop-length-2 grid statement

Paper: Lemma 3.6 (`lem:DIfREP`), (3.18) `alu9_STime`; at BA Section 8 ("remain valid").  The generic parts are
`Chain/GridRepTailGen`, `GridRepTailGen2`.

* §1 the kernel and window classes at BA; §2 the `Q`-layer of the two-slot gradient `Q₁ = G₀ E_{b₀} G₁ E_{b₁} G₀`,
  `Q₂ = G₁ E_{b₁} G₀ E_{b₀} G₁` (entries, crude bound, shift in `u`); §3 the cross-label quadratic variation (`STeeMg` of two
  different labels, the `Φ₂` form) and `linTrVar ≤ 2 Re Σ κ κ̄ STeeMg`; §4 the `Z`/`Y` increments and the BA discharge of
  `GridRepTailGen_Inc`; §5 `gridRepTailGen_hyp_BA` and `baGridWTail2_holds`.
* §6 the three list identities at `baStep2Mat`; §7 the assembly `baGridRepNAt2_of_bridge` (clause 1 by
  the residual at every `n`) and `baGridRepNAt2_holds`.

Every statement is for every `d`.  The names of the private helpers begin with GridRepTailBA_.
The private helpers of `BA/GridMartBA`, `BA/TwistKer`, `BA/TwistGridWTail` are used through `open private`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private GridMartBA_Q1 GridMartBA_Q2 GridMartBA_Phi GridMartBA_Phi_add_le GridMartBA_chain GridMartBA_twDerM_eq
  GridMartBA_Q1_conjTranspose GridMartBA_Q2_conjTranspose GridMartBA_Hpath_herm GridMartBA_twL2M_diag from RBM3D.BA.GridMartBA
open private TwistKer_fE TwistKer_trace_sandwich TwistKer_loopFine_eq from RBM3D.BA.TwistKer
open private TwistGridWTail_card_blk TwistGridWTail_norm_sum_sum_le TwistGridWTail_tri TwistGridWTail_wd_sq
  TwistGridWTail_norm_sum_wS_mul_le TwistGridWTail_linTrVar_le TwistGridWTail_chg_eq_Gres TwistGridWTail_linTr_neg_I_smul
  TwistGridWTail_sum4_swap from RBM3D.BA.TwistGridWTail

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Matrix

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The kernel class `GridRepTailGen_Ker`, the spectral height and the window at BA -/

/-- BA discharge of `GridRepTailGen_Ker` (the semigroup property `BAuKerSemigroup_holds` through `Step2Kern_uKer_BA`; the other fields from the `twU` lemmas of
the twisted layer through `twU_eq_uKer` at `![σ, σ']`); the hypotheses are `BAReal` at `n` (`BAflow_real`) and `0 < κ`. -/
theorem gridRepTailGen_ker_BA {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) {κ : ℝ} (hκ : 0 < κ)
    (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) :
    GridRepTailGen_Ker (baStep2Mat sz lam0 E).toFlowFM n := by
  have hIm : (((E n : ℝ) : ℂ) + BAmF sz lam0 E n).im ≠ 0 := by simpa using (lt_of_lt_of_le hκ hr.2).ne'
  have hu : ∀ (σ σ' : Bool) (v w : ℝ),
      Step2Gen_uKer (baStep2Mat sz lam0 E).toFlowFM n σ σ' v w = twU sz lam0 E n ![σ, σ'] v w := fun σ σ' v w =>
    (twU_eq_uKer sz lam0 E n hIm ![σ, σ'] v w).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ σ' u v w hv0 hv1 hw0 hw1
    have h := BAuKerSemigroup_holds d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n) hr σ σ' u v w hv0 hv1 hw0 hw1
    simp only [← Step2Kern_uKer_BA sz lam0 E n hIm] at h
    exact h
  · intro σ σ' v w hv hvw hw a
    rw [hu]
    exact TwistGridWTail_sum_norm_twU_le sz lam0 E n hr ![σ, σ'] hv hvw hw a
  · intro σ σ' s t ht0 ht1 a
    simp only [hu]
    have h := TwistGridWTail_norm_twU_sub_one_le sz lam0 E n hr ![σ, σ'] s ht0 ht1
    have h2 := sum_norm_row_le (twU sz lam0 E n ![σ, σ'] s t - 1) a
    simp only [Matrix.sub_apply] at h2
    exact h2.trans h
  · intro σ σ' v w hw0 hw1 a b
    have h := TwistGridWTail_twU_conj sz lam0 E n hr ![σ, σ'] v hw0 hw1 a b
    have e : (fun i => !(![σ, σ'] : Fin 2 → Bool) i) = ![!σ, !σ'] := by
      funext i; fin_cases i <;> rfl
    rw [e] at h
    simp only [hu]
    exact h

/-- The spectral height at BA along the flow: `η_u ≥ 1/(16 N)` for `u ≤ t_n ≤ t₀` (as in `TwistGridWTail2`);
the only size condition is `N^ε ≥ 1/(8κ)`. -/
theorem gridRepTailBA_eta {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) {z : ℕ → ℂ} (hz : BAFlow sz κ ε 𝔠 𝔡 z)
    (t : ℕ → ℝ) (n : ℕ) (htT : t n ≤ BAflowT0 sz z n) (hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ))
    (hεn : 1 / (8 * κ) ≤ ((sz.size n : ℕ) : ℝ) ^ ε) :
    ∀ u : ℝ, u ≤ t n → 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) u := by
  have h1 : ∀ u : ℝ, u ≤ t n → (z n).im / 2 ≤ 1 - u := fun u hu => (EMn2BA_one_sub_T0 hκ sz hz n).trans (by linarith)
  have h8 : (((sz.size n : ℕ) : ℝ))⁻¹ * (1 / (8 * κ)) ≤ (z n).im := by
    refine (mul_le_mul_of_nonneg_left hεn (inv_nonneg.2 hN0.le)).trans ?_
    rw [← Real.rpow_neg_one, ← Real.rpow_add hN0]; exact (hz.2 n).2.1
  intro u hu
  have h6 : 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ (z n).im / 2 * κ :=
    calc 1 / (16 * ((sz.size n : ℕ) : ℝ)) = (((sz.size n : ℕ) : ℝ))⁻¹ * (1 / (8 * κ)) / 2 * κ := by field_simp; norm_num
      _ ≤ (z n).im / 2 * κ := by gcongr
  unfold etaOf
  exact h6.trans (mul_le_mul (h1 u hu) (EMn2BA_mF_data sz hz n).1 hκ.le (by linarith [EMn2BA_zim_pos sz hz n, h1 u hu]))

/-- BA discharge of `GridRepTailGen_Window` (`hη`, `hR16` of the twisted layer): `t_n < 1` and `(1 - u)⁻¹ ≤ 16 N` for `u ≤ t_n`. -/
theorem gridRepTailGen_window_BA {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) {z : ℕ → ℂ} (hz : BAFlow sz κ ε 𝔠 𝔡 z)
    (t : ℕ → ℝ) (n : ℕ) (htT : t n ≤ BAflowT0 sz z n) (hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ))
    (hεn : 1 / (8 * κ) ≤ ((sz.size n : ℕ) : ℝ) ^ ε) :
    GridRepTailGen_Window (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) t n := by
  have hη := gridRepTailBA_eta hκ sz hz t n htT hN0 hεn
  refine ⟨htT.trans_lt (EMn2BA_T0_lt_one hκ sz hz n), fun u _ hu => ?_⟩
  have h1 : (z n).im / 2 ≤ 1 - u := (EMn2BA_one_sub_T0 hκ sz hz n).trans (by linarith)
  have h2 : etaOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) u ≤ 1 - u := by
    have := (EMn2BA_mF_data sz hz n).2
    have h1u : 0 < 1 - u := by linarith [EMn2BA_zim_pos sz hz n]
    unfold etaOf; nlinarith
  calc (1 - u)⁻¹ ≤ (1 / (16 * ((sz.size n : ℕ) : ℝ)))⁻¹ := inv_anti₀ (by positivity) ((hη u hu).trans h2)
    _ = 16 * ((sz.size n : ℕ) : ℝ) := TwistGridWTail2_inv_eta hN0

/-! ## 2. The `Q`-layer of the two-slot gradient: entries, crude bound, shift in `u`, the form `Φ₂` -/

section QLayer

open scoped Matrix.Norms.L2Operator

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)

/-- The fine matrices of one size index. -/
abbrev GridRepTailBA_Mat {d : ℕ} (sz : Sizes d) (n : ℕ) :=
  Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ

/-- Entries of the charged resolvent `G(τ)(H, z)` are at most `η⁻¹` (`‖G‖ ≤ η⁻¹`). -/
theorem gridRepTailBA_norm_G_le {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ}
    {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) (τ : Bool) (x y : ι) : ‖Gres H z τ x y‖ ≤ η⁻¹ := by
  have h := TwistGridWTail_norm_chg_le hH hη hz τ x y
  rwa [TwistGridWTail_chg_eq_Gres hH z τ x y] at h

/-- Entries of the charged resolvents at two spectral parameters differ by at most `|z' − z| η⁻²`. -/
theorem gridRepTailBA_norm_G_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    {z z' : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) (hz' : η ≤ |z'.im|) (τ : Bool) (x y : ι) :
    ‖Gres H z' τ x y - Gres H z τ x y‖ ≤ ‖z' - z‖ * η⁻¹ ^ 2 := by
  have h := TwistGridWTail_chg_sub_le hH hη hz hz' τ x y
  rwa [TwistGridWTail_chg_eq_Gres hH z' τ x y, TwistGridWTail_chg_eq_Gres hH z τ x y] at h

/-- A chain `(A E_b B E_c C)_{yx}` of three entry arrays bounded by `R` is at most `R³` (`W^{-2d}` against `W^{2d}` terms). -/
theorem gridRepTailBA_chain_le {A B C : GridRepTailBA_Mat sz n} {R : ℝ} (hA : ∀ x y, ‖A x y‖ ≤ R)
    (hB : ∀ x y, ‖B x y‖ ≤ R) (hC : ∀ x y, ‖C x y‖ ≤ R) (b c : Zd d (sz.L n)) (y x : Idx d (sz.L n) (sz.W n)) :
    ‖(A * TwistKer_fE n b * B * TwistKer_fE n c * C) y x‖ ≤ R ^ 3 := by
  rw [GridMartBA_chain, norm_mul]
  have hS : ‖∑ z ∈ twBlk n b, ∑ w ∈ twBlk n c, A y z * B z w * C w x‖ ≤
      ((twBlk n b).card : ℝ) * ((twBlk n c).card : ℝ) * R ^ 3 :=
    TwistGridWTail_norm_sum_sum_le _ _ _ fun z _ w _ => by
      rw [norm_mul, norm_mul]
      have hR0 : 0 ≤ R := (norm_nonneg _).trans (hA y z)
      calc ‖A y z‖ * ‖B z w‖ * ‖C w x‖ ≤ R * R * R :=
            mul_le_mul (mul_le_mul (hA _ _) (hB _ _) (norm_nonneg _) hR0) (hC _ _) (norm_nonneg _) (mul_nonneg hR0 hR0)
        _ = R ^ 3 := by ring
  rw [TwistGridWTail_card_blk, TwistGridWTail_card_blk] at hS
  have hwd := TwistGridWTail_wd_sq (sz := sz) (d := d) n
  calc ‖((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2‖ * ‖∑ z ∈ twBlk n b, ∑ w ∈ twBlk n c, A y z * B z w * C w x‖ ≤
        ‖((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2‖ * (((sz.W n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ d * R ^ 3) :=
        mul_le_mul_of_nonneg_left hS (norm_nonneg _)
    _ = R ^ 3 := by
        have : ‖((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2‖ * (((sz.W n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ d) * R ^ 3 = R ^ 3 := by
          rw [hwd, one_mul]
        linarith [this]

/-- The difference of two chains: entries of `A, B, C, A', B', C'` at most `R` and `δ`-close give `3 R² δ`. -/
theorem gridRepTailBA_chain_sub_le {A B C A' B' C' : GridRepTailBA_Mat sz n} {R δ : ℝ} (hR : 0 ≤ R)
    (hA : ∀ x y, ‖A x y‖ ≤ R) (hB : ∀ x y, ‖B x y‖ ≤ R) (hC : ∀ x y, ‖C x y‖ ≤ R) (hA' : ∀ x y, ‖A' x y‖ ≤ R)
    (hB' : ∀ x y, ‖B' x y‖ ≤ R) (hC' : ∀ x y, ‖C' x y‖ ≤ R) (dA : ∀ x y, ‖A x y - A' x y‖ ≤ δ)
    (dB : ∀ x y, ‖B x y - B' x y‖ ≤ δ) (dC : ∀ x y, ‖C x y - C' x y‖ ≤ δ) (b c : Zd d (sz.L n))
    (y x : Idx d (sz.L n) (sz.W n)) :
    ‖(A * TwistKer_fE n b * B * TwistKer_fE n c * C) y x - (A' * TwistKer_fE n b * B' * TwistKer_fE n c * C') y x‖ ≤
      3 * R ^ 2 * δ := by
  rw [GridMartBA_chain, GridMartBA_chain, ← mul_sub, norm_mul]
  have hS : ‖∑ z ∈ twBlk n b, ∑ w ∈ twBlk n c, A y z * B z w * C w x -
      ∑ z ∈ twBlk n b, ∑ w ∈ twBlk n c, A' y z * B' z w * C' w x‖ ≤
      ((twBlk n b).card : ℝ) * ((twBlk n c).card : ℝ) * (3 * R ^ 2 * δ) := by
    rw [← Finset.sum_sub_distrib]
    simp only [← Finset.sum_sub_distrib]
    exact TwistGridWTail_norm_sum_sum_le _ _ _ fun z _ w _ =>
      TwistGridWTail_tri hR (hA _ _) (hB _ _) (hC _ _) (hA' _ _) (hB' _ _) (hC' _ _) (dA _ _) (dB _ _) (dC _ _)
  rw [TwistGridWTail_card_blk, TwistGridWTail_card_blk] at hS
  have hwd := TwistGridWTail_wd_sq (sz := sz) (d := d) n
  calc ‖((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2‖ * ‖∑ z ∈ twBlk n b, ∑ w ∈ twBlk n c, A y z * B z w * C w x -
        ∑ z ∈ twBlk n b, ∑ w ∈ twBlk n c, A' y z * B' z w * C' w x‖ ≤
        ‖((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2‖ * (((sz.W n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ d * (3 * R ^ 2 * δ)) :=
        mul_le_mul_of_nonneg_left hS (norm_nonneg _)
    _ = 3 * R ^ 2 * δ := by
        have : ‖((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2‖ * (((sz.W n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ d) * (3 * R ^ 2 * δ) =
            3 * R ^ 2 * δ := by rw [hwd, one_mul]
        linarith [this]

/-- Entries of the first slot `Q₁ = G₀ E_{b₀} G₁ E_{b₁} G₀` are at most `η⁻³`, `η ≤ η_u`. -/
theorem gridRepTailBA_Q1_le (u : ℝ) {H : GridRepTailBA_Mat sz n} (hH : H.IsHermitian) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ etaOf (BAmF sz lam0 E n) u) (σ : Fin 2 → Bool) (b c : Zd d (sz.L n)) (y x : Idx d (sz.L n) (sz.W n)) :
    ‖GridMartBA_Q1 sz lam0 E n u H σ b c y x‖ ≤ η⁻¹ ^ 3 := by
  have hz := TwistGridWTail_abs_im (E n) u hη0 hη
  unfold GridMartBA_Q1
  exact gridRepTailBA_chain_le sz n (fun x y => gridRepTailBA_norm_G_le hH hη0 hz _ x y)
    (fun x y => gridRepTailBA_norm_G_le hH hη0 hz _ x y) (fun x y => gridRepTailBA_norm_G_le hH hη0 hz _ x y) b c y x

/-- Entries of the second slot `Q₂ = G₁ E_{b₁} G₀ E_{b₀} G₁` are at most `η⁻³`. -/
theorem gridRepTailBA_Q2_le (u : ℝ) {H : GridRepTailBA_Mat sz n} (hH : H.IsHermitian) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ etaOf (BAmF sz lam0 E n) u) (σ : Fin 2 → Bool) (b c : Zd d (sz.L n)) (y x : Idx d (sz.L n) (sz.W n)) :
    ‖GridMartBA_Q2 sz lam0 E n u H σ b c y x‖ ≤ η⁻¹ ^ 3 := by
  have hz := TwistGridWTail_abs_im (E n) u hη0 hη
  unfold GridMartBA_Q2
  exact gridRepTailBA_chain_le sz n (fun x y => gridRepTailBA_norm_G_le hH hη0 hz _ x y)
    (fun x y => gridRepTailBA_norm_G_le hH hη0 hz _ x y) (fun x y => gridRepTailBA_norm_G_le hH hη0 hz _ x y) c b y x

/-- The shift of the first slot in `u`: `|Q₁(u') − Q₁(u)|_{yx} ≤ 3 η⁻⁴ |z_{u'} − z_u|`. -/
theorem gridRepTailBA_Q1_sub_le (u u' : ℝ) {H : GridRepTailBA_Mat sz n} (hH : H.IsHermitian) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ etaOf (BAmF sz lam0 E n) u) (hη' : η ≤ etaOf (BAmF sz lam0 E n) u') (σ : Fin 2 → Bool)
    (b c : Zd d (sz.L n)) (y x : Idx d (sz.L n) (sz.W n)) :
    ‖GridMartBA_Q1 sz lam0 E n u' H σ b c y x - GridMartBA_Q1 sz lam0 E n u H σ b c y x‖ ≤
      3 * η⁻¹ ^ 4 * ‖ztOf (BAmF sz lam0 E n) (E n) u' - ztOf (BAmF sz lam0 E n) (E n) u‖ := by
  have hz := TwistGridWTail_abs_im (E n) u hη0 hη
  have hz' := TwistGridWTail_abs_im (E n) u' hη0 hη'
  have hR0 : 0 ≤ η⁻¹ := inv_nonneg.2 hη0.le
  unfold GridMartBA_Q1
  have h := gridRepTailBA_chain_sub_le sz n (R := η⁻¹) (δ := ‖ztOf (BAmF sz lam0 E n) (E n) u' - ztOf (BAmF sz lam0 E n) (E n) u‖ * η⁻¹ ^ 2)
    (A := Gres H (ztOf (BAmF sz lam0 E n) (E n) u') (σ 0)) (B := Gres H (ztOf (BAmF sz lam0 E n) (E n) u') (σ 1))
    (C := Gres H (ztOf (BAmF sz lam0 E n) (E n) u') (σ 0)) (A' := Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 0))
    (B' := Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 1)) (C' := Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 0))
    hR0 (fun x y => gridRepTailBA_norm_G_le hH hη0 hz' _ x y) (fun x y => gridRepTailBA_norm_G_le hH hη0 hz' _ x y)
    (fun x y => gridRepTailBA_norm_G_le hH hη0 hz' _ x y) (fun x y => gridRepTailBA_norm_G_le hH hη0 hz _ x y)
    (fun x y => gridRepTailBA_norm_G_le hH hη0 hz _ x y) (fun x y => gridRepTailBA_norm_G_le hH hη0 hz _ x y)
    (fun x y => gridRepTailBA_norm_G_sub_le hH hη0 hz hz' _ x y) (fun x y => gridRepTailBA_norm_G_sub_le hH hη0 hz hz' _ x y)
    (fun x y => gridRepTailBA_norm_G_sub_le hH hη0 hz hz' _ x y) b c y x
  refine h.trans (le_of_eq ?_)
  ring

/-- The shift of the second slot in `u`. -/
theorem gridRepTailBA_Q2_sub_le (u u' : ℝ) {H : GridRepTailBA_Mat sz n} (hH : H.IsHermitian) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ etaOf (BAmF sz lam0 E n) u) (hη' : η ≤ etaOf (BAmF sz lam0 E n) u') (σ : Fin 2 → Bool)
    (b c : Zd d (sz.L n)) (y x : Idx d (sz.L n) (sz.W n)) :
    ‖GridMartBA_Q2 sz lam0 E n u' H σ b c y x - GridMartBA_Q2 sz lam0 E n u H σ b c y x‖ ≤
      3 * η⁻¹ ^ 4 * ‖ztOf (BAmF sz lam0 E n) (E n) u' - ztOf (BAmF sz lam0 E n) (E n) u‖ := by
  have hz := TwistGridWTail_abs_im (E n) u hη0 hη
  have hz' := TwistGridWTail_abs_im (E n) u' hη0 hη'
  have hR0 : 0 ≤ η⁻¹ := inv_nonneg.2 hη0.le
  unfold GridMartBA_Q2
  have h := gridRepTailBA_chain_sub_le sz n (R := η⁻¹) (δ := ‖ztOf (BAmF sz lam0 E n) (E n) u' - ztOf (BAmF sz lam0 E n) (E n) u‖ * η⁻¹ ^ 2)
    (A := Gres H (ztOf (BAmF sz lam0 E n) (E n) u') (σ 1)) (B := Gres H (ztOf (BAmF sz lam0 E n) (E n) u') (σ 0))
    (C := Gres H (ztOf (BAmF sz lam0 E n) (E n) u') (σ 1)) (A' := Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 1))
    (B' := Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 0)) (C' := Gres H (ztOf (BAmF sz lam0 E n) (E n) u) (σ 1))
    hR0 (fun x y => gridRepTailBA_norm_G_le hH hη0 hz' _ x y) (fun x y => gridRepTailBA_norm_G_le hH hη0 hz' _ x y)
    (fun x y => gridRepTailBA_norm_G_le hH hη0 hz' _ x y) (fun x y => gridRepTailBA_norm_G_le hH hη0 hz _ x y)
    (fun x y => gridRepTailBA_norm_G_le hH hη0 hz _ x y) (fun x y => gridRepTailBA_norm_G_le hH hη0 hz _ x y)
    (fun x y => gridRepTailBA_norm_G_sub_le hH hη0 hz hz' _ x y) (fun x y => gridRepTailBA_norm_G_sub_le hH hη0 hz hz' _ x y)
    (fun x y => gridRepTailBA_norm_G_sub_le hH hη0 hz hz' _ x y) c b y x
  refine h.trans (le_of_eq ?_)
  ring

/-- **The sesquilinear form `Φ₂(R, R') = Σ_{xy} W^{-d} S_{[x][y]} R_{xy} conj R'_{xy}`** (`S = 1` at the carrier `baFM`);
`Φ₂(R, R) = Φ(R)` of `GridMartBA`, and `STeeMg` at `baStep2Mat` is `Φ₂(Q₁, Q₁') + Φ₂(Q₂, Q₂')` (§3). -/
def GridRepTailBA_Phi2 (R R' : GridRepTailBA_Mat sz n) : ℂ :=
  ∑ x, ∑ y, TwistGridWTail_wS (sz := sz) lam0 E n x y * (R x y * starRingEnd ℂ (R' x y))

/-- `‖Φ₂(R, R')‖ ≤ N B B'` for entries bounded by `B`, `B'`. -/
theorem gridRepTailBA_Phi2_norm_le {R R' : GridRepTailBA_Mat sz n} {B B' : ℝ} (hR : ∀ x y, ‖R x y‖ ≤ B)
    (hR' : ∀ x y, ‖R' x y‖ ≤ B') (hB : 0 ≤ B) :
    ‖GridRepTailBA_Phi2 sz lam0 E n R R'‖ ≤ ((sz.size n : ℕ) : ℝ) * (B * B') := by
  unfold GridRepTailBA_Phi2
  refine TwistGridWTail_norm_sum_wS_mul_le lam0 E n fun x y => ?_
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hR x y) (hR' x y) (norm_nonneg _) hB

/-- `‖Φ₂(R, R') − Φ₂(S, S')‖ ≤ N · 2 B δ` for entries bounded by `B` and `δ`-close. -/
theorem gridRepTailBA_Phi2_sub_le {R R' S S' : GridRepTailBA_Mat sz n} {B δ : ℝ} (hR : ∀ x y, ‖R x y‖ ≤ B)
    (hR' : ∀ x y, ‖R' x y‖ ≤ B) (hS : ∀ x y, ‖S x y‖ ≤ B) (hS' : ∀ x y, ‖S' x y‖ ≤ B) (hB : 0 ≤ B)
    (d1 : ∀ x y, ‖R x y - S x y‖ ≤ δ) (d2 : ∀ x y, ‖R' x y - S' x y‖ ≤ δ) :
    ‖GridRepTailBA_Phi2 sz lam0 E n R R' - GridRepTailBA_Phi2 sz lam0 E n S S'‖ ≤ ((sz.size n : ℕ) : ℝ) * (2 * B * δ) := by
  unfold GridRepTailBA_Phi2
  rw [← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  refine TwistGridWTail_norm_sum_wS_mul_le lam0 E n fun x y => ?_
  have e : ∀ (f f' e e' : ℂ), f * (starRingEnd ℂ) f' - e * (starRingEnd ℂ) e' =
      (f - e) * (starRingEnd ℂ) f' + e * (starRingEnd ℂ) (f' - e') := fun f f' e e' => by rw [map_sub]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (d1 x y)
  have h1 : ‖R x y - S x y‖ * ‖R' x y‖ ≤ δ * B := mul_le_mul (d1 x y) (hR' x y) (norm_nonneg _) hδ
  have h2 : ‖S x y‖ * ‖R' x y - S' x y‖ ≤ B * δ := mul_le_mul (hS x y) (d2 x y) (norm_nonneg _) hB
  nlinarith

end QLayer

/-! ## 3. The cross-label quadratic variation: `STeeMg` of two different labels is `Φ₂(Q₁, Q₁') + Φ₂(Q₂, Q₂')`, and
`linTrVar (Σ_b κ_b ∇Φ_b) ≤ 2 Re Σ κ_b κ̄_{b'} STeeMg(b, b')` -/

section CrossQV

open scoped Matrix.Norms.L2Operator

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)

/-- The weight `W^{-d} S^{(B)}_{[x][y]}` at the carrier `baFM` (`S^{(B)} = 1`): `W^{-d} 1[[x] = [y]]`. -/
theorem gridRepTailBA_wS_eq (x y : Idx d (sz.L n) (sz.W n)) :
    TwistGridWTail_wS (sz := sz) lam0 E n x y =
      if (split d (sz.L n) (sz.W n) x).1 = (split d (sz.L n) (sz.W n) y).1 then (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ else 0 := by
  unfold TwistGridWTail_wS
  have h : (baFM sz lam0 E).S n (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1 =
      if (split d (sz.L n) (sz.W n) x).1 = (split d (sz.L n) (sz.W n) y).1 then 1 else 0 := by
    change (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) _ _ = _
    rw [Matrix.one_apply]
  rw [h]
  split_ifs <;> simp

theorem gridRepTailBA_wS_symm (x y : Idx d (sz.L n) (sz.W n)) :
    TwistGridWTail_wS (sz := sz) lam0 E n x y = TwistGridWTail_wS (sz := sz) lam0 E n y x := by
  rw [gridRepTailBA_wS_eq, gridRepTailBA_wS_eq]
  by_cases h : (split d (sz.L n) (sz.W n) x).1 = (split d (sz.L n) (sz.W n) y).1
  · simp [h]
  · have h' : ¬ (split d (sz.L n) (sz.W n) y).1 = (split d (sz.L n) (sz.W n) x).1 := fun h2 => h h2.symm
    simp [h, h']

/-- `LM` at `baStep2Mat` is `LIM` of the list (`loopM_eq_loopL`). -/
theorem gridRepTailBA_LIM_KLloopOf (u : ℝ) (H : GridRepTailBA_Mat sz n) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) :
    (baStep2Mat sz lam0 E).LIM n u H (KLloopOf d (sz.L n) σ a) = (baStep2Mat sz lam0 E).LM n u H σ a := by
  change loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) H) _ _ = loopFine d (sz.L n) (sz.W n) H _ σ a
  rw [loopFine, loopM_eq_loopL]
  rfl

theorem gridRepTailBA_STeeLoop_one (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)) (b b' : Zd d (sz.L n)) :
    STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') 1 b b' =
      KLloopOf d (sz.L n) ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a 0, a 1, b', a' 1, a' 0, b] := by
  simp [STeeLoop, KLloopOf, List.ofFn_succ]

theorem gridRepTailBA_STeeLoop_two (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)) (b b' : Zd d (sz.L n)) :
    STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') 2 b b' =
      KLloopOf d (sz.L n) ![σ 1, σ 0, σ 1, !(σ 1), !(σ 0), !(σ 1)] ![a 1, a 0, b', a' 0, a' 1, b] := by
  simp [STeeLoop, KLloopOf, List.ofFn_succ]

/-- The 6-loop of the first cut, two different labels: `𝓛_{(σ₀σ₁σ₀σ̄₀σ̄₁σ̄₀),(b₀,b₁,c',b'₁,b'₀,c)} = Tr(Q₁^b E_{c'} (Q₁^{b'})^* E_c)`. -/
theorem gridRepTailBA_loop6_one (u : ℝ) {H : GridRepTailBA_Mat sz n} (hH : H.IsHermitian) (σ : Fin 2 → Bool)
    (b b' : Fin 2 → Zd d (sz.L n)) (c c' : Zd d (sz.L n)) :
    (baStep2Mat sz lam0 E).LM n u H ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![b 0, b 1, c', b' 1, b' 0, c] =
      Matrix.trace (GridMartBA_Q1 sz lam0 E n u H σ (b 0) (b 1) * TwistKer_fE n c' *
        (GridMartBA_Q1 sz lam0 E n u H σ (b' 0) (b' 1))ᴴ * TwistKer_fE n c) := by
  rw [GridMartBA_Q1_conjTranspose sz lam0 E n u hH]
  change loopFine d (sz.L n) (sz.W n) H (ztOf (BAmF sz lam0 E n) (E n) u) _ _ = _
  rw [TwistKer_loopFine_eq]
  simp only [GridMartBA_Q1, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.mul_assoc]

/-- The 6-loop of the second cut: `Tr(Q₂^b E_{c'} (Q₂^{b'})^* E_c)`. -/
theorem gridRepTailBA_loop6_two (u : ℝ) {H : GridRepTailBA_Mat sz n} (hH : H.IsHermitian) (σ : Fin 2 → Bool)
    (b b' : Fin 2 → Zd d (sz.L n)) (c c' : Zd d (sz.L n)) :
    (baStep2Mat sz lam0 E).LM n u H ![σ 1, σ 0, σ 1, !(σ 1), !(σ 0), !(σ 1)] ![b 1, b 0, c', b' 0, b' 1, c] =
      Matrix.trace (GridMartBA_Q2 sz lam0 E n u H σ (b 0) (b 1) * TwistKer_fE n c' *
        (GridMartBA_Q2 sz lam0 E n u H σ (b' 0) (b' 1))ᴴ * TwistKer_fE n c) := by
  rw [GridMartBA_Q2_conjTranspose sz lam0 E n u hH]
  change loopFine d (sz.L n) (sz.W n) H (ztOf (BAmF sz lam0 E n) (E n) u) _ _ = _
  rw [TwistKer_loopFine_eq]
  simp only [GridMartBA_Q2, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.mul_assoc]

/-- `Σ_c Σ_{i,j ∈ [c]} F_{ij} = Σ_{ij} 1[[i] = [j]] F_{ij}`. -/
theorem gridRepTailBA_sum_blocks (F : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) :
    ∑ c : Zd d (sz.L n), ∑ i ∈ twBlk n c, ∑ j ∈ twBlk n c, F i j =
      ∑ i, ∑ j, if (split d (sz.L n) (sz.W n) i).1 = (split d (sz.L n) (sz.W n) j).1 then F i j else 0 := by
  simp only [twBlk, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : (split d (sz.L n) (sz.W n) i).1 = (split d (sz.L n) (sz.W n) j).1
  · simp [hij]
  · have : ¬ (split d (sz.L n) (sz.W n) j).1 = (split d (sz.L n) (sz.W n) i).1 := fun h => hij h.symm
    simp [hij, this]

/-- `W^d Σ_c Tr(R E_c R'^* E_c) = Φ₂(R, R')` (the sesquilinear form of the private `GridMartBA_sum_trace`). -/
theorem gridRepTailBA_sum_trace2 (R R' : GridRepTailBA_Mat sz n) :
    (((sz.W n : ℕ) : ℂ) ^ d) * ∑ c, Matrix.trace (R * TwistKer_fE n c * R'ᴴ * TwistKer_fE n c) =
      GridRepTailBA_Phi2 sz lam0 E n R R' := by
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (sz.W_pos n).ne')
  simp only [TwistKer_trace_sandwich]
  have h1 : ∀ i j : Idx d (sz.L n) (sz.W n), R i j * R'ᴴ j i = R i j * starRingEnd ℂ (R' i j) := fun i j => by
    rw [Matrix.conjTranspose_apply, Complex.star_def]
  simp only [h1]
  rw [← Finset.mul_sum, gridRepTailBA_sum_blocks sz n (fun i j => R i j * starRingEnd ℂ (R' i j))]
  unfold GridRepTailBA_Phi2
  simp only [gridRepTailBA_wS_eq]
  rw [← mul_assoc, show (((sz.W n : ℕ) : ℂ) ^ d) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ by
    field_simp]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- **`STeeMg` at `baStep2Mat` for two different labels** (Hermitian `H`): `Φ₂(Q₁^b, Q₁^{b'}) + Φ₂(Q₂^b, Q₂^{b'})`; the cross-label
form of the private `GridMartBA_STEEk` (`b = b'`). -/
theorem gridRepTailBA_STeeMg_eq (u : ℝ) {H : GridRepTailBA_Mat sz n} (hH : H.IsHermitian) (σ : Fin 2 → Bool)
    (b b' : Fin 2 → Zd d (sz.L n)) :
    STeeMg (baStep2Mat sz lam0 E) n u H σ b b' =
      GridRepTailBA_Phi2 sz lam0 E n (GridMartBA_Q1 sz lam0 E n u H σ (b 0) (b 1))
          (GridMartBA_Q1 sz lam0 E n u H σ (b' 0) (b' 1)) +
        GridRepTailBA_Phi2 sz lam0 E n (GridMartBA_Q2 sz lam0 E n u H σ (b 0) (b 1))
          (GridMartBA_Q2 sz lam0 E n u H σ (b' 0) (b' 1)) := by
  have hS : ∀ x y : Zd d (sz.L n), (baStep2Mat sz lam0 E).S n x y = if x = y then 1 else 0 := fun x y => by
    change (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) x y = _
    rw [Matrix.one_apply]
  unfold STeeMg
  have e1 : Finset.Icc 1 2 = {1, 2} := by decide
  rw [e1, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2), mul_add]
  simp only [gridRepTailBA_STeeLoop_one, gridRepTailBA_STeeLoop_two, hS, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, STLIMg, gridRepTailBA_LIM_KLloopOf]
  congr 1
  · rw [← gridRepTailBA_sum_trace2]
    congr 1
    exact Finset.sum_congr rfl fun c _ => gridRepTailBA_loop6_one sz lam0 E n u hH σ b b' c c
  · rw [← gridRepTailBA_sum_trace2]
    congr 1
    exact Finset.sum_congr rfl fun c _ => gridRepTailBA_loop6_two sz lam0 E n u hH σ b b' c c

/-- **Crude bound of the quadratic variation at BA**: `|STeeMg_u(H)(b, b')| ≤ 2 N η⁻⁶` for Hermitian `H`, `η ≤ η_u`. -/
theorem gridRepTailBA_STeeMg_norm_le (u : ℝ) {H : GridRepTailBA_Mat sz n} (hH : H.IsHermitian) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ etaOf (BAmF sz lam0 E n) u) (σ : Fin 2 → Bool) (b b' : Fin 2 → Zd d (sz.L n)) :
    ‖STeeMg (baStep2Mat sz lam0 E) n u H σ b b'‖ ≤ 2 * ((sz.size n : ℕ) : ℝ) * η⁻¹ ^ 6 := by
  rw [gridRepTailBA_STeeMg_eq sz lam0 E n u hH]
  have hB : 0 ≤ η⁻¹ ^ 3 := by positivity
  have h1 := gridRepTailBA_Phi2_norm_le sz lam0 E n (R := GridMartBA_Q1 sz lam0 E n u H σ (b 0) (b 1))
    (R' := GridMartBA_Q1 sz lam0 E n u H σ (b' 0) (b' 1)) (fun x y => gridRepTailBA_Q1_le sz lam0 E n u hH hη0 hη σ _ _ x y)
    (fun x y => gridRepTailBA_Q1_le sz lam0 E n u hH hη0 hη σ _ _ x y) hB
  have h2 := gridRepTailBA_Phi2_norm_le sz lam0 E n (R := GridMartBA_Q2 sz lam0 E n u H σ (b 0) (b 1))
    (R' := GridMartBA_Q2 sz lam0 E n u H σ (b' 0) (b' 1)) (fun x y => gridRepTailBA_Q2_le sz lam0 E n u hH hη0 hη σ _ _ x y)
    (fun x y => gridRepTailBA_Q2_le sz lam0 E n u hH hη0 hη σ _ _ x y) hB
  refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
  ring

/-- **The shift of the quadratic variation in `u` at BA**: for Hermitian `H` and `η ≤ η_u, η_{u'}`,
`|STeeMg_{u'}(H) − STeeMg_u(H)| ≤ 12 N η⁻⁷ |z_{u'} − z_u|`. -/
theorem gridRepTailBA_STeeMg_sub_le (u u' : ℝ) {H : GridRepTailBA_Mat sz n} (hH : H.IsHermitian) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ etaOf (BAmF sz lam0 E n) u) (hη' : η ≤ etaOf (BAmF sz lam0 E n) u') (σ : Fin 2 → Bool)
    (b b' : Fin 2 → Zd d (sz.L n)) :
    ‖STeeMg (baStep2Mat sz lam0 E) n u' H σ b b' - STeeMg (baStep2Mat sz lam0 E) n u H σ b b'‖ ≤
      ((sz.size n : ℕ) : ℝ) * (12 * η⁻¹ ^ 7 * ‖ztOf (BAmF sz lam0 E n) (E n) u' - ztOf (BAmF sz lam0 E n) (E n) u‖) := by
  rw [gridRepTailBA_STeeMg_eq sz lam0 E n u hH, gridRepTailBA_STeeMg_eq sz lam0 E n u' hH]
  set Δz := ‖ztOf (BAmF sz lam0 E n) (E n) u' - ztOf (BAmF sz lam0 E n) (E n) u‖ with hΔz
  have hB : 0 ≤ η⁻¹ ^ 3 := by positivity
  have h1 := gridRepTailBA_Phi2_sub_le sz lam0 E n (δ := 3 * η⁻¹ ^ 4 * Δz)
    (R := GridMartBA_Q1 sz lam0 E n u' H σ (b 0) (b 1)) (R' := GridMartBA_Q1 sz lam0 E n u' H σ (b' 0) (b' 1))
    (S := GridMartBA_Q1 sz lam0 E n u H σ (b 0) (b 1)) (S' := GridMartBA_Q1 sz lam0 E n u H σ (b' 0) (b' 1))
    (fun x y => gridRepTailBA_Q1_le sz lam0 E n u' hH hη0 hη' σ _ _ x y) (fun x y => gridRepTailBA_Q1_le sz lam0 E n u' hH hη0 hη' σ _ _ x y)
    (fun x y => gridRepTailBA_Q1_le sz lam0 E n u hH hη0 hη σ _ _ x y) (fun x y => gridRepTailBA_Q1_le sz lam0 E n u hH hη0 hη σ _ _ x y) hB
    (fun x y => gridRepTailBA_Q1_sub_le sz lam0 E n u u' hH hη0 hη hη' σ _ _ x y)
    (fun x y => gridRepTailBA_Q1_sub_le sz lam0 E n u u' hH hη0 hη hη' σ _ _ x y)
  have h2 := gridRepTailBA_Phi2_sub_le sz lam0 E n (δ := 3 * η⁻¹ ^ 4 * Δz)
    (R := GridMartBA_Q2 sz lam0 E n u' H σ (b 0) (b 1)) (R' := GridMartBA_Q2 sz lam0 E n u' H σ (b' 0) (b' 1))
    (S := GridMartBA_Q2 sz lam0 E n u H σ (b 0) (b 1)) (S' := GridMartBA_Q2 sz lam0 E n u H σ (b' 0) (b' 1))
    (fun x y => gridRepTailBA_Q2_le sz lam0 E n u' hH hη0 hη' σ _ _ x y) (fun x y => gridRepTailBA_Q2_le sz lam0 E n u' hH hη0 hη' σ _ _ x y)
    (fun x y => gridRepTailBA_Q2_le sz lam0 E n u hH hη0 hη σ _ _ x y) (fun x y => gridRepTailBA_Q2_le sz lam0 E n u hH hη0 hη σ _ _ x y) hB
    (fun x y => gridRepTailBA_Q2_sub_le sz lam0 E n u u' hH hη0 hη hη' σ _ _ x y)
    (fun x y => gridRepTailBA_Q2_sub_le sz lam0 E n u u' hH hη0 hη hη' σ _ _ x y)
  rw [add_sub_add_comm]
  refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
  ring

/-- `Φ₂(R, R) = Φ(R)` of `GridMartBA`. -/
theorem gridRepTailBA_Phi2_self (R : GridRepTailBA_Mat sz n) :
    GridRepTailBA_Phi2 sz lam0 E n R R = ((GridMartBA_Phi sz n R : ℝ) : ℂ) := by
  unfold GridRepTailBA_Phi2 GridMartBA_Phi
  simp only [gridRepTailBA_wS_eq]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [Complex.mul_conj']
    push_cast
    ring
  · simp

/-- `Φ₂` of a weighted sum: `Φ₂(Σ κ_b Q_b, Σ κ_b Q_b) = Σ_{b,b'} κ_b κ̄_{b'} Φ₂(Q_b, Q_{b'})`. -/
theorem gridRepTailBA_Phi2_sum {ι : Type*} [Fintype ι] (Q : ι → GridRepTailBA_Mat sz n) (κ : ι → ℂ) :
    GridRepTailBA_Phi2 sz lam0 E n (∑ b, κ b • Q b) (∑ b, κ b • Q b) =
      ∑ b, ∑ b', κ b * starRingEnd ℂ (κ b') * GridRepTailBA_Phi2 sz lam0 E n (Q b) (Q b') := by
  have hpt : ∀ x y : Idx d (sz.L n) (sz.W n), TwistGridWTail_wS (sz := sz) lam0 E n x y *
      ((∑ b, κ b • Q b) x y * starRingEnd ℂ ((∑ b, κ b • Q b) x y)) =
      ∑ b, ∑ b', κ b * starRingEnd ℂ (κ b') *
        (TwistGridWTail_wS (sz := sz) lam0 E n x y * (Q b x y * starRingEnd ℂ (Q b' x y))) := by
    intro x y
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum]
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b' _ => ?_
    simp only [map_mul]
    ring
  unfold GridRepTailBA_Phi2
  simp only [hpt]
  rw [TwistGridWTail_sum4_swap]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  simp only [Finset.mul_sum]

/-- **The label family of the two-slot tail**: `Φ_b(M) = 𝓛_{u,σ,(b₀,b₁)}(g₀Ψ + M)`, TL's twisted observable at `c₁ = c₂ = b₁`
(`GridMartBA_twL2M_diag`: `L̃_{σ,(b₀;b₁,b₁)} = 𝓛^{(2)}_{σ,(b₀,b₁)}`), so TL's Hermitian-test-function and second-derivative lemmas apply. -/
def GridRepTailBA_Phi (u : ℝ) (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)) : GridRepTailBA_Mat sz n → ℂ :=
  TwistGridWTail_Phi sz lam0 E n u σ (b 1) (b 1) (b 0)

/-- `Φ_b(M) = 𝓛_{u,σ,b}(g₀Ψ + M)` (the loop of `baStep2Mat`) for Hermitian `M`. -/
theorem gridRepTailBA_Phi_eq (u : ℝ) (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)) {M : GridRepTailBA_Mat sz n}
    (hM : M.IsHermitian) :
    GridRepTailBA_Phi sz lam0 E n u σ b M = (baStep2Mat sz lam0 E).LM n u (TwistGridWTail_Hm sz lam0 n M) σ b := by
  have h := GridMartBA_twL2M_diag sz lam0 E n u (TwistGridWTail_Hm_herm sz lam0 n hM) σ (b 0) (b 1)
  have hb : (![b 0, b 1] : Fin 2 → Zd d (sz.L n)) = b := by funext i; fin_cases i <;> rfl
  rw [hb] at h
  exact h

/-- **The cross-label variance of the gradient at a fixed matrix**: for the weights `κ`, `linTrVar` of `Σ_b κ_b ∇Φ_b(M)` and of `(-I)` times it
are at most `2 Re Σ_{b,b'} κ_b conj(κ_{b'}) STeeMg_u(g₀Ψ + M)(b, b')` (the two slots `Q₁ + Q₂` of the gradient; Cauchy-Schwarz over the
two cuts, `|Q₁ + Q₂|² ≤ 2|Q₁|² + 2|Q₂|²`, the factor `2 = m`; equality fails, as in the band case). -/
theorem gridRepTailBA_linTrVar_le_QV (u : ℝ) (σ : Fin 2 → Bool) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ etaOf (BAmF sz lam0 E n) u) (κ : (Fin 2 → Zd d (sz.L n)) → ℂ) {M : GridRepTailBA_Mat sz n}
    (hM : M.IsHermitian) :
    linTrVar (sz := sz.withLam 0) n (∑ b, κ b • gradMat (GridRepTailBA_Phi sz lam0 E n u σ b) M) ≤
      2 * (∑ b, ∑ b', κ b * starRingEnd ℂ (κ b') *
        STeeMg (baStep2Mat sz lam0 E) n u (TwistGridWTail_Hm sz lam0 n M) σ b b').re ∧
    linTrVar (sz := sz.withLam 0) n ((-Complex.I) • ∑ b, κ b • gradMat (GridRepTailBA_Phi sz lam0 E n u σ b) M) ≤
      2 * (∑ b, ∑ b', κ b * starRingEnd ℂ (κ b') *
        STeeMg (baStep2Mat sz lam0 E) n u (TwistGridWTail_Hm sz lam0 n M) σ b b').re := by
  have hHm : (TwistGridWTail_Hm sz lam0 n M).IsHermitian := TwistGridWTail_Hm_herm sz lam0 n hM
  set Hm := TwistGridWTail_Hm sz lam0 n M with hHmdef
  set Q1 : (Fin 2 → Zd d (sz.L n)) → GridRepTailBA_Mat sz n := fun b => GridMartBA_Q1 sz lam0 E n u Hm σ (b 0) (b 1) with hQ1
  set Q2 : (Fin 2 → Zd d (sz.L n)) → GridRepTailBA_Mat sz n := fun b => GridMartBA_Q2 sz lam0 E n u Hm σ (b 0) (b 1) with hQ2
  set R1 : GridRepTailBA_Mat sz n := ∑ b, κ b • Q1 b with hR1
  set R2 : GridRepTailBA_Mat sz n := ∑ b, κ b • Q2 b with hR2
  set f : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ := fun p q => -(R1 + R2) q p with hf
  set D : CoordF d (sz.L n) (sz.W n) → ℂ := fun c => ∑ b, κ b *
    fderiv ℝ (GridRepTailBA_Phi sz lam0 E n u σ b) M (coordinateMatrix d (sz.L n) (sz.W n) c) with hD
  have hDtr : ∀ c, Matrix.trace ((∑ b, κ b • gradMat (GridRepTailBA_Phi sz lam0 E n u σ b) M) *
      coordinateMatrix d (sz.L n) (sz.W n) c) = D c := by
    intro c
    rw [Matrix.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← fderiv_eq_trace_gradMat M (coordinateMatrix_isHermitian _ _ _ c)]
  obtain ⟨h1, h2⟩ := TwistGridWTail_linTrVar_le n (sz.withLam 0) _ D hDtr
  have hDf : ∀ c, D c = ∑ p, ∑ q, f p q * coordinateMatrix d (sz.L n) (sz.W n) c p q := by
    intro c
    have hb : ∀ b : Fin 2 → Zd d (sz.L n), fderiv ℝ (GridRepTailBA_Phi sz lam0 E n u σ b) M
        (coordinateMatrix d (sz.L n) (sz.W n) c) = ∑ p, ∑ q, (-(Q1 b + Q2 b) q p) *
          coordinateMatrix d (sz.L n) (sz.W n) c p q := fun b => by
      unfold GridRepTailBA_Phi
      rw [TwistGridWTail_fderiv_eq sz lam0 E n u σ (b 1) (b 1) (b 0) hη0 hη hM (coordinateMatrix_isHermitian _ _ _ c)]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      rw [GridMartBA_twDerM_eq sz lam0 E n u hHm σ (b 0) (b 1) p q]
    have hpt : ∀ p q : Idx d (sz.L n) (sz.W n), f p q * coordinateMatrix d (sz.L n) (sz.W n) c p q =
        ∑ b, κ b * ((-(Q1 b + Q2 b) q p) * coordinateMatrix d (sz.L n) (sz.W n) c p q) := by
      intro p q
      have e : (R1 + R2) q p = ∑ b, κ b * (Q1 b + Q2 b) q p := by
        simp only [hR1, hR2, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_add,
          Finset.sum_add_distrib]
      rw [hf]
      simp only [e]
      rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    simp only [hD, hb, hpt, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
  have hS : ∑ c : CoordF d (sz.L n) (sz.W n), (gvarF d (sz.L n) (sz.W n) ((sz.withLam 0).lam n) c : ℝ) * ‖D c‖ ^ 2 =
      (GridRepTailBA_Phi2 sz lam0 E n (R1 + R2) (R1 + R2)).re := by
    simp only [hDf]
    rw [TwistGridWTail_coord_sum_eq sz lam0 E n f]
    congr 1
    unfold GridRepTailBA_Phi2
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [gridRepTailBA_wS_symm sz lam0 E n k l]
    simp only [hf, map_neg, neg_mul_neg]
  have hΦ : (GridRepTailBA_Phi2 sz lam0 E n (R1 + R2) (R1 + R2)).re ≤
      2 * (∑ b, ∑ b', κ b * starRingEnd ℂ (κ b') * STeeMg (baStep2Mat sz lam0 E) n u Hm σ b b').re := by
    rw [gridRepTailBA_Phi2_self, Complex.ofReal_re]
    have hsum : ∑ b, ∑ b', κ b * starRingEnd ℂ (κ b') * STeeMg (baStep2Mat sz lam0 E) n u Hm σ b b' =
        GridRepTailBA_Phi2 sz lam0 E n R1 R1 + GridRepTailBA_Phi2 sz lam0 E n R2 R2 := by
      rw [hR1, hR2, gridRepTailBA_Phi2_sum, gridRepTailBA_Phi2_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [gridRepTailBA_STeeMg_eq sz lam0 E n u hHm σ b b']
      simp only [hQ1, hQ2]
      ring
    rw [hsum, gridRepTailBA_Phi2_self, gridRepTailBA_Phi2_self, ← Complex.ofReal_add, Complex.ofReal_re]
    have := GridMartBA_Phi_add_le sz n R1 R2
    linarith
  exact ⟨h1.trans (le_of_eq hS |>.trans hΦ), h2.trans (le_of_eq hS |>.trans hΦ)⟩

end CrossQV

/-! ## 4. The `Z` / `Y` increments and the BA discharge of `GridRepTailGen_Inc` -/

section Inc

open RBM.Ind
open scoped Matrix.Norms.L2Operator

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

/-- The label family of step `j`: `Φ_b` at the spectral time `u_{j+1}` (the family of `stepDecompCN`). -/
def GridRepTailBA_fam (σ : Fin 2 → Bool) (j : ℕ) :
    (Fin 2 → Zd d (sz.L n)) → GridRepTailBA_Mat sz n → ℂ :=
  fun b => GridRepTailBA_Phi sz lam0 E n (gridTime s t K n (j + 1)) σ b

/-- `stepZCN = √Δ tr (AbCN · X_{j+1})`: the complex linear term is the trace pairing (`linTr = Re tr`, `linTr ((-I) •) = Im tr`). -/
theorem gridRepTailBA_stepZCN_eq_trace (szz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*} [Fintype ι]
    (Φ : ι → GridRepTailBA_Mat szz n → ℂ) (U : ι → ι → ℂ) (b₀ : ι) (ω : PathΩ szz) :
    stepZCN szz s t K n j Φ U b₀ ω =
      (Real.sqrt (gridStep s t K n) : ℂ) * Matrix.trace (AbCN szz s t K n j Φ U b₀ ω * Sizes.seqXmat szz n (ω (j + 1))) := by
  unfold stepZCN stepZCN_re stepZCN_im
  rw [TwistGridWTail_linTr_neg_I_smul n szz]
  apply Complex.ext <;> simp [linTr]

/-- **Linearity of `stepZCN` in the weights**: `stepZCN κ = Σ_b κ_b stepZCN δ_b`. -/
theorem gridRepTailBA_stepZCN_sum (szz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Φ : ι → GridRepTailBA_Mat szz n → ℂ) (κ : ι → ℂ) (b₀ : ι) (ω : PathΩ szz) :
    stepZCN szz s t K n j Φ (fun _ a => κ a) b₀ ω =
      ∑ b, κ b * stepZCN szz s t K n j Φ (fun _ a => if a = b then 1 else 0) b₀ ω := by
  simp only [gridRepTailBA_stepZCN_eq_trace]
  unfold AbCN
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Matrix.sum_mul, Matrix.trace_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  ring

/-- The first-chaos increment of the label `b` at step `j` (the `Z` of the class `GridRepTailGen_Inc`): `stepZCN` with the weight `δ_b`,
i.e. `√Δ tr (∇Φ_b(H_j) X_{j+1})`. -/
def GridRepTailBA_Z (σ : Fin 2 → Bool) (j : ℕ) (ω : PathΩ sz) (b : Fin 2 → Zd d (sz.L n)) : ℂ :=
  stepZCN (sz.withLam 0) s t K n j (GridRepTailBA_fam sz lam0 E s t K n σ j) (fun _ a => if a = b then 1 else 0) (fun _ => 0) ω

/-- `Σ_b κ_b Z_b` is `stepZCN` of the weights `κ`. -/
theorem gridRepTailBA_sum_Z (σ : Fin 2 → Bool) (j : ℕ) (ω : PathΩ sz) (κ : (Fin 2 → Zd d (sz.L n)) → ℂ) :
    ∑ b, κ b * GridRepTailBA_Z sz lam0 E s t K n σ j ω b =
      stepZCN (sz.withLam 0) s t K n j (GridRepTailBA_fam sz lam0 E s t K n σ j) (fun _ a => κ a) (fun _ => 0) ω :=
  (gridRepTailBA_stepZCN_sum (sz.withLam 0) s t K n j (GridRepTailBA_fam sz lam0 E s t K n σ j) κ (fun _ => 0) ω).symm

/-- The label observables are Hermitian test functions, with the second-derivative constant `6 η⁻⁴` (the lemmas `TwistGridWTail_hermTestFun`
and `TwistGridWTail_Phi_second` of the twisted layer at `c₁ = c₂ = b₁`). -/
theorem gridRepTailBA_hermTestFun (u : ℝ) (σ : Fin 2 → Bool) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ etaOf (BAmF sz lam0 E n) u)
    (b : Fin 2 → Zd d (sz.L n)) :
    HermTestFun (sz.withLam 0) n (GridRepTailBA_Phi sz lam0 E n u σ b) :=
  TwistGridWTail_hermTestFun sz lam0 E n u σ (b 1) (b 1) (b 0) hη0 hη

theorem gridRepTailBA_C2 (u : ℝ) (σ : Fin 2 → Bool) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ etaOf (BAmF sz lam0 E n) u)
    (b : Fin 2 → Zd d (sz.L n)) (M y : GridRepTailBA_Mat sz n) (hM : M.IsHermitian) (hy : y.IsHermitian) :
    ‖fderiv ℝ (fderiv ℝ (GridRepTailBA_Phi sz lam0 E n u σ b)) M y y‖ ≤ (6 * η⁻¹ ^ 4) * ‖y‖ ^ 2 :=
  TwistGridWTail_Phi_second sz lam0 E n u σ (b 1) (b 1) (b 0) hη0 hη hM hy

/-- `AbCN` of the weights `κ` is `filt j`-measurable (from `stepDecompCN`). -/
theorem gridRepTailBA_AbCN_measurable (σ : Fin 2 → Bool) (j : ℕ) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ etaOf (BAmF sz lam0 E n) (gridTime s t K n (j + 1))) (hΔ : 0 ≤ gridStep s t K n)
    (κ : (Fin 2 → Zd d (sz.L n)) → ℂ) (b₀ : Fin 2 → Zd d (sz.L n)) :
    Measurable[filt sz j] (fun ω => AbCN (sz.withLam 0) s t K n j (GridRepTailBA_fam sz lam0 E s t K n σ j) (fun _ a => κ a) b₀ ω) := by
  have hΦ := fun b => gridRepTailBA_hermTestFun sz lam0 E n _ σ hη0 hη b
  have hC₂ := fun b M y hM hy => gridRepTailBA_C2 sz lam0 E n _ σ hη0 hη b M y hM hy
  have hIntRe := integrable_stepZCN_re_of_hermTestFun (sz.withLam 0) s t K n j (Φ := GridRepTailBA_fam sz lam0 E s t K n σ j)
    hΦ hC₂ hΔ (fun _ a => κ a) b₀
  have hIntIm := integrable_stepZCN_im_of_hermTestFun (sz.withLam 0) s t K n j (Φ := GridRepTailBA_fam sz lam0 E s t K n σ j)
    hΦ hC₂ hΔ (fun _ a => κ a) b₀
  obtain ⟨-, hAm, -, -⟩ := stepDecompCN (sz.withLam 0) s t K n j hΦ hC₂ hΔ (fun _ a => κ a) b₀ hIntRe hIntIm
  exact hAm

/-- `Re Σ_{bb'} κ_b κ̄_{b'} T_{bb'} ≤ (Σ|κ|)² M` when `|T_{bb'}| ≤ M`. -/
theorem gridRepTailBA_quad_le {ι : Type*} [Fintype ι] (κ : ι → ℂ) (T : ι → ι → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hT : ∀ b b', ‖T b b'‖ ≤ M) :
    (∑ b, ∑ b', κ b * starRingEnd ℂ (κ b') * T b b').re ≤ (∑ b, ‖κ b‖) ^ 2 * M := by
  calc (∑ b, ∑ b', κ b * starRingEnd ℂ (κ b') * T b b').re ≤ ‖∑ b, ∑ b', κ b * starRingEnd ℂ (κ b') * T b b'‖ :=
        Complex.re_le_norm _
    _ ≤ ∑ b, ∑ b', ‖κ b * starRingEnd ℂ (κ b') * T b b'‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => norm_sum_le _ _)
    _ ≤ ∑ b, ∑ b', ‖κ b‖ * ‖κ b'‖ * M := Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun b' _ => by
        rw [norm_mul, norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_left (hT b b') (by positivity)
    _ = (∑ b, ‖κ b‖) ^ 2 * M := by
        rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_mul]

/-- `STeeMg` is measurable in the matrix argument (`walk_measurable_loopL`, `walk_measurable_blockMat`). -/
theorem gridRepTailBA_measurable_STeeMg (u : ℝ) (σ : Fin 2 → Bool) (b b' : Fin 2 → Zd d (sz.L n)) :
    Measurable (fun M : GridRepTailBA_Mat sz n => STeeMg (baStep2Mat sz lam0 E) n u M σ b b') := by
  unfold STeeMg
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun c _ =>
    Finset.measurable_sum _ fun c' _ => measurable_const.mul ?_)
  exact (walk_measurable_loopL d (sz.L n) (sz.W n) (ztOf (BAmF sz lam0 E n) (E n) u) _).comp
    (walk_measurable_blockMat d (sz.L n) (sz.W n))

/-- **The martingale increment as a `stepXiCN`** (the analogue of `TwistGridWTail_xi_ae`): `Σ_b κ_b ξ_{j+1}(b)` is a.e.
`stepXiCN` of the family `GridRepTailBA_fam` with the kernel `(·, a) ↦ κ_a` (linearity of the conditional expectation; the deterministic `𝒦`
cancels), and `filt (j+1)`-measurable. -/
theorem gridRepTailBA_xi_ae (σ : Fin 2 → Bool) (j : ℕ) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ etaOf (BAmF sz lam0 E n) (gridTime s t K n (j + 1))) (κ : (Fin 2 → Zd d (sz.L n)) → ℂ) :
    (fun ω : PathΩ (sz.withLam 0) => ∑ b, κ b * martIncNg (baStep2Mat sz lam0 E) s t K n j σ ω b) =ᵐ[pathP (sz.withLam 0)]
      stepXiCN (sz.withLam 0) s t K n j (GridRepTailBA_fam sz lam0 E s t K n σ j) (fun _ a => κ a) (fun _ => 0) ∧
    Measurable[filt (sz.withLam 0) (j + 1)]
      (fun ω : PathΩ (sz.withLam 0) => ∑ b, κ b * martIncNg (baStep2Mat sz lam0 E) s t K n j σ ω b) := by
  set szz : Sizes d := sz.withLam 0 with hszz
  set u := gridTime s t K n (j + 1) with hu
  set Ξ : (Fin 2 → Zd d (sz.L n)) → PathΩ szz → ℂ := fun b ω =>
    GridRepTailBA_fam sz lam0 E s t K n σ j b (pathH szz s t K n (j + 1) ω) with hΞ
  set Kc : (Fin 2 → Zd d (sz.L n)) → ℂ := fun b => (baStep2Mat sz lam0 E).K n u σ b with hKc
  have hΞm : ∀ b, Measurable[filt szz (j + 1)] (Ξ b) := fun b =>
    (TwistGridWTail_Phi_measurable sz lam0 E n u σ (b 1) (b 1) (b 0)).comp (pathH_measurable_filt szz s t K n (j + 1))
  have hΞint : ∀ b, Integrable (Ξ b) (pathP szz) := by
    intro b
    have hm : Measurable (Ξ b) := (hΞm b).mono ((filt szz).le (j + 1)) le_rfl
    exact (memLp_top_of_bound hm.aestronglyMeasurable (η⁻¹ ^ 2) (Eventually.of_forall fun ω =>
      TwistGridWTail_Phi_norm_le sz lam0 E n _ σ (b 1) (b 1) (b 0) (pathH_isHermitian szz s t K n (j + 1) ω) hη0 hη)).integrable le_top
  have hAv : ∀ ω b, AvecNg (baStep2Mat sz lam0 E) s t K n (j + 1) σ ω b = Ξ b ω - Kc b := by
    intro ω b
    have h := gridRepTailBA_Phi_eq sz lam0 E n u σ b (pathH_isHermitian szz s t K n (j + 1) ω)
    change (baStep2Mat sz lam0 E).LM n u (TwistGridWTail_Hm sz lam0 n (pathH szz s t K n (j + 1) ω)) σ b -
      (baStep2Mat sz lam0 E).K n u σ b = Ξ b ω - Kc b
    rw [← h]
    rfl
  have hmart : ∀ ω b, martIncNg (baStep2Mat sz lam0 E) s t K n j σ ω b =
      (Ξ b ω - Kc b) - (pathP szz)[fun ω' => Ξ b ω' - Kc b | filt szz j] ω := by
    intro ω b
    unfold martIncNg
    have h1 : (fun ω' => AvecNg (baStep2Mat sz lam0 E) s t K n (j + 1) σ ω' b) = fun ω' => Ξ b ω' - Kc b :=
      funext fun ω' => hAv ω' b
    rw [h1, hAv ω b]
    rfl
  have hce : ∀ b, (pathP szz)[fun ω' => Ξ b ω' - Kc b | filt szz j] =ᵐ[pathP szz]
      fun ω => (pathP szz)[Ξ b | filt szz j] ω - Kc b := by
    intro b
    have h := condExp_sub (hΞint b) (integrable_const (Kc b)) (filt szz j)
    have hc : (pathP szz)[fun _ : PathΩ szz => Kc b | filt szz j] = fun _ => Kc b := condExp_const ((filt szz).le j) _
    filter_upwards [h] with ω hω
    simp only [Pi.sub_apply] at hω ⊢
    rw [show (fun ω' => Ξ b ω' - Kc b) = Ξ b - fun _ => Kc b from rfl, hω, hc]
  have hlin : (pathP szz)[fun ω' => ∑ a, κ a * Ξ a ω' | filt szz j] =ᵐ[pathP szz]
      fun ω => ∑ a, κ a * (pathP szz)[Ξ a | filt szz j] ω := by
    have h1 := condExp_finsetSum (μ := pathP szz) (s := Finset.univ) (f := fun a ω' => κ a * Ξ a ω')
      (fun a _ => (hΞint a).const_mul (κ a)) (filt szz j)
    have h2 : ∀ a, (pathP szz)[fun ω' => κ a * Ξ a ω' | filt szz j] =ᵐ[pathP szz]
        fun ω => κ a * (pathP szz)[Ξ a | filt szz j] ω := fun a => condExp_smul (κ a) (Ξ a) (filt szz j)
    have h3 : ∀ᵐ ω ∂(pathP szz), ∀ a, (pathP szz)[fun ω' => κ a * Ξ a ω' | filt szz j] ω =
        κ a * (pathP szz)[Ξ a | filt szz j] ω := ae_all_iff.2 h2
    filter_upwards [h1, h3] with ω hω1 hω2
    have : (fun ω' => ∑ a, κ a * Ξ a ω') = ∑ a, fun ω' => κ a * Ξ a ω' := by funext ω'; simp [Finset.sum_apply]
    rw [this, hω1]
    simp only [Finset.sum_apply, hω2]
  have hce' : ∀ᵐ ω ∂(pathP szz), ∀ b, (pathP szz)[fun ω' => Ξ b ω' - Kc b | filt szz j] ω =
      (pathP szz)[Ξ b | filt szz j] ω - Kc b := ae_all_iff.2 hce
  refine ⟨?_, ?_⟩
  · filter_upwards [hlin, hce'] with ω h1 h2
    have hL : ∑ b, κ b * martIncNg (baStep2Mat sz lam0 E) s t K n j σ ω b =
        ∑ b, κ b * (Ξ b ω - (pathP szz)[Ξ b | filt szz j] ω) :=
      Finset.sum_congr rfl fun b _ => by rw [hmart ω b, h2 b]; ring
    rw [hL]
    change _ = (∑ a, κ a * Ξ a ω) - (pathP szz)[fun ω' => ∑ a, κ a * Ξ a ω' | filt szz j] ω
    rw [h1, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  · have hfun : (fun ω : PathΩ szz => ∑ b, κ b * martIncNg (baStep2Mat sz lam0 E) s t K n j σ ω b) =
        fun ω : PathΩ szz => ∑ b, κ b * ((Ξ b ω - Kc b) - (pathP szz)[fun ω' => Ξ b ω' - Kc b | filt szz j] ω) :=
      funext fun ω => Finset.sum_congr rfl fun b _ => by rw [hmart ω b]
    rw [hfun]
    refine Finset.measurable_sum _ fun b _ => measurable_const.mul ?_
    exact ((hΞm b).sub measurable_const).sub ((stronglyMeasurable_condExp.measurable).mono ((filt szz).mono (Nat.le_succ j)) le_rfl)

/-- The constants of `TwistGridWTail_Y_fields` imply those of the class (`4 (S C₂/2)² · 768 N⁸ ≤ 2000 (S · 6 N (16 N)⁴)² N⁸`). -/
theorem gridRepTailBA_Yconst_le (S Δ N : ℝ) (hS : 0 ≤ S) (hN : 1 ≤ N) :
    4 * (S * (6 * (1 / (16 * N))⁻¹ ^ 4 / 2)) ^ 2 * Δ ^ 2 * (768 * N ^ 8) ≤
      Δ ^ 2 * (2000 * (S * (6 * N * (16 * N) ^ 4)) ^ 2 * N ^ 8) := by
  have h : (1 / (16 * N))⁻¹ = 16 * N := by rw [one_div, inv_inv]
  rw [h]
  set A : ℝ := S * (16 * N) ^ 4 with hA
  have hA0 : 0 ≤ A := by positivity
  have e1 : 4 * (S * (6 * (16 * N) ^ 4 / 2)) ^ 2 * Δ ^ 2 * (768 * N ^ 8) = 27648 * (A ^ 2 * Δ ^ 2 * N ^ 8) := by
    rw [hA]; ring
  have e2 : Δ ^ 2 * (2000 * (S * (6 * N * (16 * N) ^ 4)) ^ 2 * N ^ 8) = 72000 * N ^ 2 * (A ^ 2 * Δ ^ 2 * N ^ 8) := by
    rw [hA]; ring
  rw [e1, e2]
  have hX : 0 ≤ A ^ 2 * Δ ^ 2 * N ^ 8 := by positivity
  have hN2 : 1 ≤ N ^ 2 := one_le_pow₀ hN
  nlinarith [mul_nonneg (sub_nonneg.2 hN2) hX]

/-- **The `Z` fields at BA** (class `GridRepTailGen_Zfields`): TL's `ι`-generic conditional mgf at `ι = Fin 2 → Zd`, the variance proxy
`2 Re Σ κ κ̄ STeeMg` of the cross-label identity (`gridRepTailBA_linTrVar_le_QV`) and the crude bound of `STeeMg`. -/
theorem gridRepTailBA_zfields (hs0 : 0 ≤ s n) (hst : s n ≤ t n)
    (hη : ∀ u : ℝ, u ≤ t n → 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaOf (BAmF sz lam0 E n) u) :
    GridRepTailGen_Zfields (baStep2Mat sz lam0 E) s t K n
      (fun j σ ω b => GridRepTailBA_Z sz lam0 E s t K n σ j ω b) := by
  intro j hj σ κ r
  have hK0 : K n ≠ 0 := by omega
  have hu0 := TwistGridWTail_gridTime_nonneg (K := K) hs0 hst (j + 1)
  have hut := TwistGridWTail_gridTime_le hst hK0 hj
  set u := gridTime s t K n (j + 1) with hu
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  have hη0 : 0 < 1 / (16 * N) := by positivity
  have hηu := hη u hut
  have hΔ := ST_gridStep_nonneg s t K n hst
  have hΦ := fun b => gridRepTailBA_hermTestFun sz lam0 E n u σ hη0 hηu b
  have hC₂ := fun b M y hM hy => gridRepTailBA_C2 sz lam0 E n u σ hη0 hηu b M y hM hy
  set S : ℝ := ∑ b, ‖κ b‖ with hS
  set Mee : ℝ := 2 * N * (1 / (16 * N))⁻¹ ^ 6 with hMee
  have hMee0 : 0 ≤ Mee := by positivity
  set v : PathΩ (sz.withLam 0) → ℝ := fun ω => 2 * (∑ b, ∑ b', κ b * starRingEnd ℂ (κ b') *
    STeeMg (baStep2Mat sz lam0 E) n u ((baStep2Mat sz lam0 E).Hpath s t K n j ω) σ b b').re with hv
  have hvle : ∀ ω, v ω ≤ 2 * (S ^ 2 * Mee) := by
    intro ω
    have hH := GridMartBA_Hpath_herm sz lam0 E n s t K j ω
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact gridRepTailBA_quad_le κ _ hMee0 fun b b' => gridRepTailBA_STeeMg_norm_le sz lam0 E n u hH hη0 hηu σ b b'
  have hRe : ∀ ω, linTrVar (sz := sz.withLam 0) n (AbCN (sz.withLam 0) s t K n j (GridRepTailBA_fam sz lam0 E s t K n σ j)
      (fun _ a => κ a) (fun _ => 0) ω) ≤ v ω := fun ω =>
    (gridRepTailBA_linTrVar_le_QV sz lam0 E n u σ hη0 hηu κ (pathH_isHermitian (sz.withLam 0) s t K n j ω)).1
  have hIm : ∀ ω, linTrVar (sz := sz.withLam 0) n ((-Complex.I) • AbCN (sz.withLam 0) s t K n j (GridRepTailBA_fam sz lam0 E s t K n σ j)
      (fun _ a => κ a) (fun _ => 0) ω) ≤ v ω := fun ω =>
    (gridRepTailBA_linTrVar_le_QV sz lam0 E n u σ hη0 hηu κ (pathH_isHermitian (sz.withLam 0) s t K n j ω)).2
  have hvb : ∀ ω, gridStep s t K n * v ω ≤ gridStep s t K n * (2 * (S ^ 2 * Mee)) := fun ω =>
    mul_le_mul_of_nonneg_left (hvle ω) hΔ
  obtain ⟨hi1, hi2, hc1, hc2⟩ := TwistGridWTail_condMGF_generic (sz := sz.withLam 0) s t K n j
    (Φ := GridRepTailBA_fam sz lam0 E s t K n σ j) hΦ hC₂ hΔ (fun _ a => κ a) (fun _ => 0)
    (c0 := gridStep s t K n * (2 * (S ^ 2 * Mee))) (by positivity) v hRe hIm hvb r
  have hAm := gridRepTailBA_AbCN_measurable sz lam0 E s t K n σ j hη0 hηu hΔ κ (fun _ => 0)
  have hZm := TwistGridWTail_measurable_stepZCN (sz := sz.withLam 0) s t K n j (GridRepTailBA_fam sz lam0 E s t K n σ j)
    (fun _ a => κ a) (fun _ => 0) hAm
  have hre : ∀ ω : PathΩ sz, (stepZCN (sz.withLam 0) s t K n j (GridRepTailBA_fam sz lam0 E s t K n σ j) (fun _ a => κ a) (fun _ => 0) ω).re =
      stepZCN_re (sz.withLam 0) s t K n j (GridRepTailBA_fam sz lam0 E s t K n σ j) (fun _ a => κ a) (fun _ => 0) ω := fun ω => by
    simp [stepZCN]
  have him : ∀ ω : PathΩ sz, (stepZCN (sz.withLam 0) s t K n j (GridRepTailBA_fam sz lam0 E s t K n σ j) (fun _ a => κ a) (fun _ => 0) ω).im =
      stepZCN_im (sz.withLam 0) s t K n j (GridRepTailBA_fam sz lam0 E s t K n σ j) (fun _ a => κ a) (fun _ => 0) ω := fun ω => by
    simp [stepZCN]
  simp only [gridRepTailBA_sum_Z, hre, him]
  exact ⟨hZm, hi1, hi2, hc1, hc2⟩

/-- **The `Y` fields at BA** (class `GridRepTailGen_Yfields`, `Y = martIncNg − Z`): TL's `TwistGridWTail_Y_fields` with `C₂ = 6 η⁻⁴`; its
constant `4 (S C₂/2)² · 768 N⁸` is at most the class's `2000 (S · 6 N (16 N)⁴)² N⁸`. -/
theorem gridRepTailBA_yfields (hs0 : 0 ≤ s n) (hst : s n ≤ t n)
    (hη : ∀ u : ℝ, u ≤ t n → 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaOf (BAmF sz lam0 E n) u) :
    GridRepTailGen_Yfields (baStep2Mat sz lam0 E) s t K n
      (fun j σ ω b => martIncNg (baStep2Mat sz lam0 E) s t K n j σ ω b - GridRepTailBA_Z sz lam0 E s t K n σ j ω b) := by
  intro j hj σ κ
  have hK0 : K n ≠ 0 := by omega
  have hu0 := TwistGridWTail_gridTime_nonneg (K := K) hs0 hst (j + 1)
  have hut := TwistGridWTail_gridTime_le hst hK0 hj
  set u := gridTime s t K n (j + 1) with hu
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  have hη0 : 0 < 1 / (16 * N) := by positivity
  have hηu := hη u hut
  have hΔ := ST_gridStep_nonneg s t K n hst
  have hΦ := fun b => gridRepTailBA_hermTestFun sz lam0 E n u σ hη0 hηu b
  have hC₂ := fun b M y hM hy => gridRepTailBA_C2 sz lam0 E n u σ hη0 hηu b M y hM hy
  obtain ⟨hxi, hxim⟩ := gridRepTailBA_xi_ae sz lam0 E s t K n σ j hη0 hηu κ
  have hY := TwistGridWTail_Y_fields (sz := sz.withLam 0) s t K n j (Φ := GridRepTailBA_fam sz lam0 E s t K n σ j) hΦ hC₂ hΔ κ
    (fun _ => 0) (fun ω => ∑ b, κ b * martIncNg (baStep2Mat sz lam0 E) s t K n j σ ω b) hxi hxim
  have hpt : ∀ ω : PathΩ sz, ∑ b, κ b * (martIncNg (baStep2Mat sz lam0 E) s t K n j σ ω b - GridRepTailBA_Z sz lam0 E s t K n σ j ω b) =
      (∑ b, κ b * martIncNg (baStep2Mat sz lam0 E) s t K n j σ ω b) -
        stepZCN (sz.withLam 0) s t K n j (GridRepTailBA_fam sz lam0 E s t K n σ j) (fun _ a => κ a) (fun _ => 0) ω := by
    intro ω
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [gridRepTailBA_sum_Z]
  simp only [hpt]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hY
  have hS0 : 0 ≤ ∑ b, ‖κ b‖ := Finset.sum_nonneg fun b _ => norm_nonneg _
  have hc := gridRepTailBA_Yconst_le (∑ b, ‖κ b‖) (gridStep s t K n) N hS0 hN1
  exact ⟨h1, h2, h3, h4, h5, h6.trans hc, h7.trans hc⟩

/-- **The BA discharge of `GridRepTailGen_Inc`**: `Z = GridRepTailBA_Z`, `Y = martIncNg − Z`; the crude bound `gridRepTailBA_STeeMg_norm_le` at
`η = 1/(16 N)`; the shift bound `gridRepTailBA_STeeMg_sub_le` with `|z_{u'} − z_u| = (u' − u) |m| ≤ u' − u`.  Hypotheses: `|m_F| ≤ 1`, `s ≤ t` and
`η_u ≥ 1/(16 N)` for `u ≤ t_n` (the window, `gridRepTailBA_eta`). -/
theorem gridRepTailGen_inc_BA (hm : ‖BAmF sz lam0 E n‖ ≤ 1) (hs0 : 0 ≤ s n) (hst : s n ≤ t n)
    (hη : ∀ u : ℝ, u ≤ t n → 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaOf (BAmF sz lam0 E n) u) :
    GridRepTailGen_Inc (baStep2Mat sz lam0 E) s t K n := by
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hη0 : 0 < 1 / (16 * ((sz.size n : ℕ) : ℝ)) := by positivity
  have hinv : (1 / (16 * ((sz.size n : ℕ) : ℝ)))⁻¹ = 16 * ((sz.size n : ℕ) : ℝ) := by rw [one_div, inv_inv]
  refine ⟨(inferInstance : IsProbabilityMeasure (pathP (sz.withLam 0))),
    fun j => ⟨measurable_const.add (pathH_measurable_filt (sz.withLam 0) s t K n j),
      fun ω => GridMartBA_Hpath_herm sz lam0 E n s t K j ω⟩,
    fun u σ b b' => gridRepTailBA_measurable_STeeMg sz lam0 E n u σ b b',
    ⟨fun j σ ω b => GridRepTailBA_Z sz lam0 E s t K n σ j ω b,
      fun j σ ω b => martIncNg (baStep2Mat sz lam0 E) s t K n j σ ω b - GridRepTailBA_Z sz lam0 E s t K n σ j ω b,
      fun j σ => Eventually.of_forall fun ω b => by ring,
      gridRepTailBA_zfields sz lam0 E s t K n hs0 hst hη, gridRepTailBA_yfields sz lam0 E s t K n hs0 hst hη⟩, ?_, ?_⟩
  · intro u hu0 hut H hH σ a a'
    have h := gridRepTailBA_STeeMg_norm_le sz lam0 E n u hH hη0 (hη u hut) σ a a'
    rw [hinv] at h
    exact h
  · intro u u' hu0 huu' hu't H hH σ a a'
    have h := gridRepTailBA_STeeMg_sub_le sz lam0 E n u u' hH hη0 (hη u (huu'.trans hu't)) (hη u' hu't) σ a a'
    rw [hinv] at h
    have hz : ‖ztOf (BAmF sz lam0 E n) (E n) u' - ztOf (BAmF sz lam0 E n) (E n) u‖ ≤ u' - u := by
      have e : ztOf (BAmF sz lam0 E n) (E n) u' - ztOf (BAmF sz lam0 E n) (E n) u = (((u - u' : ℝ)) : ℂ) * BAmF sz lam0 E n := by
        unfold ztOf; push_cast; ring
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      calc -(u - u') * ‖BAmF sz lam0 E n‖ ≤ -(u - u') * 1 :=
            mul_le_mul_of_nonneg_left hm (by linarith)
        _ = u' - u := by ring
    refine h.trans ?_
    set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
    calc N * (12 * (16 * N) ^ 7 * ‖ztOf (BAmF sz lam0 E n) (E n) u' - ztOf (BAmF sz lam0 E n) (E n) u‖) ≤
          N * (12 * (16 * N) ^ 7 * (u' - u)) := by gcongr
      _ = 12 * 16 ^ 7 * N ^ 8 * (u' - u) := by ring

end Inc

/-! ## 5. `gridRepTailGen_hyp_BA` and `baGridWTail2_holds` -/

/-- **`GridRepTailGen_Hyp` at BA** (non-vacuity of the classes): along every `BAFlow` datum, `SizeTendsto`
from the flow, and for the `n` with `N_n^ε ≥ 1/(8κ)` (eventually): `Ker` (`BAflow_real`), the window and, for every grid `K`, `Inc`. -/
theorem gridRepTailGen_hyp_BA (d : ℕ) :
    GridRepTailGen_Hyp d BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0 := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT
  have hsize : sz.SizeTendsto := hz.1.2.2.1
  refine ⟨hsize, ?_⟩
  have hev : ∀ᶠ n in atTop, 1 / (8 * κ) ≤ ((sz.size n : ℕ) : ℝ) ^ ε :=
    ((tendsto_rpow_atTop hε).comp hsize).eventually_ge_atTop _
  filter_upwards [hev] with n hn
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hz n
  have hmn : ‖BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n‖ ≤ 1 :=
    BAm_norm_le_one d (sz.L n) _ ((BAflowEs sz z n : ℝ) : ℂ) _ (by simp) hr.1
  exact ⟨gridRepTailGen_ker_BA sz _ _ n hκ hr, gridRepTailGen_window_BA hκ sz hz t n (htT n) hN0 hn,
    fun K _ => gridRepTailGen_inc_BA sz _ _ s t K n hmn (hs n) (hst n) (gridRepTailBA_eta hκ sz hz t n (htT n) hN0 hn)⟩

/-- **`baGridWTail2_holds`**: clause 4 of `STGridRepNAtgL d 2` at the BA carrier along `BAFlow` (the `Ũ`-weighted two-slot tail
`STGridWTail2gL`), for every `d`; `CK = 3 D + 40`. -/
theorem baGridWTail2_holds (d : ℕ) :
    STGridWTail2gL d BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0 :=
  stGridWTail2gL_of (gridRepTailGen_hyp_BA d)

/-! ## 6. The loop-length-2 list identities at `baStep2Mat`

The analogues of `STgA_eq_STgAN`, `STgDrift_eq_STgDriftN`, `STEEM_eq_STeeM` (`Induction/Step2Iterate.lean`), generic over a carrier
whose `LM` is `LIM ∘ KLloopOf` (`GridRepTailBA_F1`) and whose `K` is `KI ∘ KLloopOf` (`GridRepTailBA_F2`); both hold by definition at `baStep2Mat`
(`gridRepTailBA_LIM_KLloopOf`). -/

section ListIds

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)

/-- `LM = LIM ∘ KLloopOf`. -/
def GridRepTailBA_F1 : Prop :=
  ∀ (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)), Cm.LM n u H σ a = Cm.LIM n u H (KLloopOf d (sz.L n) σ a)

/-- `K = KI ∘ KLloopOf`. -/
def GridRepTailBA_F2 : Prop :=
  ∀ (n : ℕ) (u : ℝ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
    Cm.toFlowFM.K n u σ a = Cm.KI n u (KLloopOf d (sz.L n) σ a)

theorem gridRepTailBA_LM_eq (h1 : GridRepTailBA_F1 Cm) (n : ℕ) (u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) : Cm.LM n u H σ a = Cm.LIM n u H (KLloopOf d (sz.L n) σ a) := h1 n u H σ a

theorem gridRepTailBA_STLKMg_eq (h1 : GridRepTailBA_F1 Cm) (h2 : GridRepTailBA_F2 Cm) (n : ℕ) (u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) :
    STLKMg Cm n u H σ a = STLKIMg Cm n u H (KLloopOf d (sz.L n) σ a) := by
  unfold STLKMg STLKIMg STLMg STLIMg
  rw [h1, h2]

theorem gridRepTailBA_STavgMg_eq (h1 : GridRepTailBA_F1 Cm) (n : ℕ) (u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Bool) (x : Zd d (sz.L n)) :
    STavgMg Cm n u H σ x = STavgErrMg Cm n u H σ x := by
  unfold STavgMg STavgErrMg STLMg STLIMg
  rw [h1]
  have : KLloopOf d (sz.L n) (fun _ : Fin 1 => σ) (fun _ => x) = ⟨[σ], [x]⟩ := by
    simp [KLloopOf, List.ofFn_succ]
  rw [this]

/-- `STgAg = STgANg`. -/
theorem gridRepTailBA_STgAg_eq (h1 : GridRepTailBA_F1 Cm) (h2 : GridRepTailBA_F2 Cm) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) :
    STgAg Cm s t K n σ a k ω = STgANg Cm s t K n σ a k ω :=
  gridRepTailBA_STLKMg_eq Cm h1 h2 _ _ _ σ a

/-- `STgDriftg = STgDriftNg` at `m = 2` (`Icc 3 2 = ∅`; `KLloopOf_cutL`, `KLloopOf_cutR`, `KLloopOf_cutGlue1`, `KLloopOf_cutGlue2`; `STthetaOpg` is `Step2Gen_ThetaN` at `m = 2`). -/
theorem gridRepTailBA_STgDriftg_eq (h1 : GridRepTailBA_F1 Cm) (h2 : GridRepTailBA_F2 Cm) (s t : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) :
    STgDriftg Cm s t K n σ a k ω = STgDriftNg Cm s t K n σ a k ω := by
  unfold STgDriftg STgDriftNg
  have h3 : Finset.Icc 3 2 = (∅ : Finset ℕ) := by decide
  rw [h3, Finset.sum_empty, add_zero]
  have hf : STLKMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) σ =
      fun a' => STLKIMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) (KLloopOf d (sz.L n) σ a') :=
    funext fun a' => gridRepTailBA_STLKMg_eq Cm h1 h2 _ _ _ σ a'
  rw [hf]
  have hθ : STthetaOpg Cm n (gridTime s t K n k) σ
      (fun a' => STLKIMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) (KLloopOf d (sz.L n) σ a')) a =
      Step2Gen_ThetaN Cm.toFlowFM n σ (gridTime s t K n k)
        (fun a' => STLKIMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) (KLloopOf d (sz.L n) σ a')) a := rfl
  rw [hθ]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl ?_) ?_
  · unfold STELKLKMg STelklkMg
    rw [KLloopOf_length2]
    have e1 : Finset.Icc 1 2 = {1, 2} := by decide
    have e2 : Finset.Ioc 1 2 = {2} := by decide
    have e3 : Finset.Ioc 2 2 = ∅ := by decide
    rw [e1, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2), e2, e3]
    simp only [Finset.sum_singleton, Finset.sum_empty, add_zero, KLloopOf_cutL, KLloopOf_cutR,
      gridRepTailBA_STLKMg_eq Cm h1 h2]
  · unfold STEGtMg STegtMg
    rw [KLloopOf_length2]
    have e1 : Finset.Icc 1 2 = {1, 2} := by decide
    rw [e1, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]
    simp only [Finset.sum_add_distrib, KLloopOf_cutGlue1, KLloopOf_cutGlue2, gridRepTailBA_STavgMg_eq Cm h1, STLMg, STLIMg,
      gridRepTailBA_LM_eq Cm h1]
    rfl

/-- `STEEMg = STeeMg σ a a` at `m = 2`. -/
theorem gridRepTailBA_STEEMg_eq (h1 : GridRepTailBA_F1 Cm) (n : ℕ) (u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STEEMg Cm n u H σ a = STeeMg Cm n u H σ a a := by
  unfold STEEMg STEEkMg STeeMg
  have e1 : Finset.Icc 1 2 = {1, 2} := by decide
  rw [e1, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2), mul_add]
  simp only [STeeLoop_one, STeeLoop_two, STLIMg, STLMg, gridRepTailBA_LM_eq Cm h1]
  simp

end ListIds

/-- `GridRepTailBA_F1` holds at `baStep2Mat` (`loopM_eq_loopL`). -/
theorem gridRepTailBA_F1_ba {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) : GridRepTailBA_F1 (baStep2Mat sz lam0 E) := by
  intro n u H k σ a
  exact (gridRepTailBA_LIM_KLloopOf sz lam0 E n u H σ a).symm

/-- `GridRepTailBA_F2` holds at `baStep2Mat` (`baFM.K = BAKloop = KI ∘ KLloopOf`). -/
theorem gridRepTailBA_F2_ba {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) : GridRepTailBA_F2 (baStep2Mat sz lam0 E) :=
  fun n u k σ a => rfl

/-- **`STgAg = STgANg` at `baStep2Mat`**, every `d`, `sz`, `lam0`, `E`. -/
theorem baStep2_STgAg_eq {d : ℕ} (sz : Sizes d) (lam0 E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) :
    STgAg (baStep2Mat sz lam0 E) s t K n σ a k ω = STgANg (baStep2Mat sz lam0 E) s t K n σ a k ω :=
  gridRepTailBA_STgAg_eq _ (gridRepTailBA_F1_ba sz lam0 E) (gridRepTailBA_F2_ba sz lam0 E) s t K n σ a k ω

/-- **`STgDriftg = STgDriftNg` at `baStep2Mat`**. -/
theorem baStep2_STgDriftg_eq {d : ℕ} (sz : Sizes d) (lam0 E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) :
    STgDriftg (baStep2Mat sz lam0 E) s t K n σ a k ω = STgDriftNg (baStep2Mat sz lam0 E) s t K n σ a k ω :=
  gridRepTailBA_STgDriftg_eq _ (gridRepTailBA_F1_ba sz lam0 E) (gridRepTailBA_F2_ba sz lam0 E) s t K n σ a k ω

/-- **`STEEMg = STeeMg σ a a` at `baStep2Mat`**. -/
theorem baStep2_STEEMg_eq {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STEEMg (baStep2Mat sz lam0 E) n u H σ a = STeeMg (baStep2Mat sz lam0 E) n u H σ a a :=
  gridRepTailBA_STEEMg_eq _ (gridRepTailBA_F1_ba sz lam0 E) n u H σ a

/-! ## 7. The assembly `baGridRepNAt2_of_bridge` and `baGridRepNAt2_holds`

Clause 1 holds at every `n` for `Mart_k = Σ_{j<k} ξ_{j+1}` and `Rem_k` the residual `A_k − A_0 − Δ Σ Drift − Mart_k` (the
`baTwistGrid_decomp` pattern, `BA/TwistGrid2.lean`).  Eventually in `n` (the three identities (H1), (H2), (H3′) of `BAGridBridge` along the grid): `Mart = twMart`,
`Rem = twRem` at `(σ, a 0, a 1, a 1)`, so clauses 2 and 3 are `baTwistGridRem_holds` and `baTwistGridTail_holds` (the latter at `ε'/2`,
`‖twEEk‖ ≤ 2 ‖STeeMg σ a a‖`, `N^{ε'/2} ≥ 2`), clause 4 is `baGridWTail2_holds`; `CK` is the maximum of the three. -/

section Assembly

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

/-- The canonical martingale `Mart_k = Σ_{j<k} ξ_{j+1}` (`martIncNg`, `Chain/GridDuhamelGen.lean`) at the label `i = (σ, a)`. -/
def GridRepTailBA_Mart (i : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) (k : ℕ) (ω : PathΩ sz) : ℂ :=
  ∑ j ∈ Finset.range k, martIncNg (baStep2Mat sz lam0 E) s t K n j i.1 ω i.2

/-- The residual `Rem_k = A_k − A_0 − Δ Σ_{j<k} Drift_j − Mart_k` (a ring identity: clause 1 at every `n`). -/
def GridRepTailBA_Rem (i : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) (k : ℕ) (ω : PathΩ sz) : ℂ :=
  STgANg (baStep2Mat sz lam0 E) s t K n i.1 i.2 k ω - STgANg (baStep2Mat sz lam0 E) s t K n i.1 i.2 0 ω -
    ((gridStep s t K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k, STgDriftNg (baStep2Mat sz lam0 E) s t K n i.1 i.2 j ω -
      GridRepTailBA_Mart sz lam0 E s t K n i k ω

/-- Under (H1) at `j + 1` (as functions of `ω'`): `martIncNg` is the twisted `twMartInc` at `(σ, a 1, a 1)(a 0)`. -/
theorem gridRepTailBA_inc_eq (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (j : ℕ) (ω : PathΩ sz)
    (hA : ∀ ω', twAk sz lam0 E s t K n σ (a 1) (a 1) (j + 1) ω' (a 0) =
      STgAg (baStep2Mat sz lam0 E) s t K n σ a (j + 1) ω') :
    martIncNg (baStep2Mat sz lam0 E) s t K n j σ ω a = twMartInc sz lam0 E s t K n σ (a 1) (a 1) j ω (a 0) := by
  unfold martIncNg twMartInc
  have hf : (fun ω' => AvecNg (baStep2Mat sz lam0 E) s t K n (j + 1) σ ω' a) =
      fun ω' => twAk sz lam0 E s t K n σ (a 1) (a 1) (j + 1) ω' (a 0) := funext fun ω' => (hA ω').symm
  rw [hf, hA ω]
  rfl

/-- `Σ_{j<k} martIncNg = twMart` at `(σ, a 0, a 1, a 1)` under (H1) for `j + 1 ≤ k`. -/
theorem gridRepTailBA_mart_eq (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz)
    (hA : ∀ j, j + 1 ≤ k → ∀ ω', twAk sz lam0 E s t K n σ (a 1) (a 1) (j + 1) ω' (a 0) =
      STgAg (baStep2Mat sz lam0 E) s t K n σ a (j + 1) ω') :
    GridRepTailBA_Mart sz lam0 E s t K n (σ, a) k ω = twMart sz lam0 E s t K n σ (a 0) (a 1) (a 1) k ω := by
  unfold twMart GridRepTailBA_Mart
  exact Finset.sum_congr rfl fun j hj => gridRepTailBA_inc_eq sz lam0 E s t K n σ a j ω (hA j (Finset.mem_range.1 hj))

/-- The residual is the twisted `twRem` at `(σ, a 0, a 1, a 1)` under (H1) (`j ≤ k`), (H2) (`j < k`) and the identities `STgAg = STgANg`, `STgDriftg = STgDriftNg`. -/
theorem gridRepTailBA_rem_eq (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz)
    (hA : ∀ j, j ≤ k → ∀ ω', twAk sz lam0 E s t K n σ (a 1) (a 1) j ω' (a 0) = STgAg (baStep2Mat sz lam0 E) s t K n σ a j ω')
    (hD : ∀ j, j < k → twDriftk sz lam0 E s t K n σ (a 0) (a 1) (a 1) j ω = STgDriftg (baStep2Mat sz lam0 E) s t K n σ a j ω) :
    GridRepTailBA_Rem sz lam0 E s t K n (σ, a) k ω = twRem sz lam0 E s t K n σ (a 0) (a 1) (a 1) k ω := by
  have hdec := baTwistGrid_decomp sz lam0 E s t K n σ (a 0) (a 1) (a 1) k ω
  unfold GridRepTailBA_Rem
  rw [gridRepTailBA_mart_eq sz lam0 E s t K n σ a k ω (fun j hj => hA (j + 1) hj)]
  simp only []
  rw [← baStep2_STgAg_eq sz lam0 E s t K n σ a k ω, ← baStep2_STgAg_eq sz lam0 E s t K n σ a 0 ω,
    ← hA k le_rfl ω, ← hA 0 (Nat.zero_le _) ω]
  have hs : ∑ j ∈ Finset.range k, STgDriftNg (baStep2Mat sz lam0 E) s t K n σ a j ω =
      ∑ j ∈ Finset.range k, twDriftk sz lam0 E s t K n σ (a 0) (a 1) (a 1) j ω :=
    Finset.sum_congr rfl fun j hj => ((hD j (Finset.mem_range.1 hj)).trans (baStep2_STgDriftg_eq sz lam0 E s t K n σ a j ω)).symm
  rw [hs]
  linear_combination hdec

/-- The (H3′) shift of clause 3: `A (T + Y)^{1/2} ≤ A² (X + Y)^{1/2}` for `T ≤ 2 X`, `A ≥ 2`. -/
theorem gridRepTailBA_shift_ineq {T X Y A : ℝ} (hY : 0 ≤ Y) (hT0 : 0 ≤ T) (hT : T ≤ 2 * X) (hA : 2 ≤ A) :
    A * (T + Y) ^ (1 / 2 : ℝ) ≤ (A * A) * (X + Y) ^ (1 / 2 : ℝ) := by
  have hX : 0 ≤ X := by linarith
  have h1 : (T + Y) ^ (1 / 2 : ℝ) ≤ (2 * (X + Y)) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  have h2 : (2 * (X + Y)) ^ (1 / 2 : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) * (X + Y) ^ (1 / 2 : ℝ) :=
    Real.mul_rpow (by norm_num) (by linarith)
  have h3 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 :=
    calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have h4 : 0 ≤ (X + Y) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  calc A * (T + Y) ^ (1 / 2 : ℝ) ≤ A * ((2 : ℝ) ^ (1 / 2 : ℝ) * (X + Y) ^ (1 / 2 : ℝ)) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by linarith)
    _ ≤ A * (A * (X + Y) ^ (1 / 2 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (h3.trans hA) h4) (by linarith)
    _ = (A * A) * (X + Y) ^ (1 / 2 : ℝ) := by ring

/-- **`baGridRepNAt2_of_bridge`** (for every `d`): the bridge (`BAGridBridge` with the conjunct (H3′), a hypothesis of exact type, inline) and the explicit parts
`baTwistGridRem_holds`, `baTwistGridTail_holds` of the twisted layer give the full
loop-length-2 grid statement `STGridRepNAtgL d 2` at the BA carrier along `BAFlow`, with the canonical `Mart`, `Rem`, clause 4 being
`baGridWTail2_holds`; `CK` is the maximum of the three constants. -/
theorem baGridRepNAt2_of_bridge (d : ℕ)
    (hB :
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
        ∀ᶠ n : ℕ in atTop, ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ∀ k ≤ K n, ∀ ω : PathΩ sz,
          twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ (a 1) (a 1) k ω (a 0) =
              STgAg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s t K n σ a k ω ∧
            twDriftk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ (a 0) (a 1) (a 1) k ω =
              STgDriftg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s t K n σ a k ω ∧
            ‖twEEk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ (a 0) (a 1) (a 1) k ω‖ ≤
              2 * ‖STEEMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (gridTime s t K n k)
                ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Hpath s t K n k ω) σ a‖) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      STGridRepNAtgL d 2 C₀ BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0 := by
  obtain ⟨C₀, hC₀, hRem⟩ := baTwistGridRem_holds d
  have hTail := baTwistGridTail_holds d
  have hW := baGridWTail2_holds d
  refine ⟨C₀, hC₀, ?_⟩
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT D hD
  obtain ⟨CKr, hCKr, hr⟩ := hRem κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT
  obtain ⟨CKt, hCKt, ht⟩ := hTail κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT D hD
  obtain ⟨CKw, hCKw, hw⟩ := hW κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT D hD
  refine ⟨max CKr (max CKt CKw), le_max_of_le_left hCKr, fun K hK0 hKN => ?_⟩
  have hmono : ∀ C : ℝ, C ≤ max CKr (max CKt CKw) → ∀ n : ℕ,
      ((sz.size n : ℕ) : ℝ) ^ (max CKr (max CKt CKw)) ≤ K n → ((sz.size n : ℕ) : ℝ) ^ C ≤ K n :=
    fun C hC n hn => (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast sz.one_le_size n) hC).trans hn
  have hKr : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CKr ≤ K n := hKN.mono fun n hn => hmono _ (le_max_left _ _) n hn
  have hKt : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CKt ≤ K n :=
    hKN.mono fun n hn => hmono _ ((le_max_left _ _).trans (le_max_right _ _)) n hn
  have hKw : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CKw ≤ K n :=
    hKN.mono fun n hn => hmono _ ((le_max_right _ _).trans (le_max_right _ _)) n hn
  obtain ⟨-, hrem⟩ := hr K hK0 hKr
  have hbr := hB κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT K hK0
  have hsize : sz.SizeTendsto := hz.1.2.2.1
  refine ⟨fun n i k ω => GridRepTailBA_Mart sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i k ω,
    fun n i k ω => GridRepTailBA_Rem sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i k ω, ?_, ?_, ?_, ?_⟩
  · -- clause 1: the residual identity at every `n`
    intro n i
    exact Eventually.of_forall fun ω k _ => by unfold GridRepTailBA_Rem; ring
  · -- clause 2: `Rem = twRem` ((H1), (H2) and the two list identities); the remainder bound of the twisted layer
    filter_upwards [hbr, hrem] with n hb hrn
    intro i
    filter_upwards [hrn (i.1, i.2 0, i.2 1, i.2 1)] with ω hω k hk
    have h := hω k hk
    have e := gridRepTailBA_rem_eq sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2 k ω
      (fun j hj ω' => (hb i.1 i.2 j (hj.trans hk) ω').1)
      (fun j hj => (hb i.1 i.2 j (hj.le.trans hk) ω).2.1)
    exact e ▸ h
  · -- clause 3: `Mart = twMart`, `‖twEEk‖ ≤ 2 ‖STeeMg σ a a‖` (H3′), the tail of the twisted layer at `ε'/2`
    intro ε' hε'
    have hA2 := ((tendsto_rpow_atTop (half_pos hε')).comp hsize).eventually_ge_atTop 2
    filter_upwards [ht K hK0 hKt (ε' / 2) (half_pos hε'), hbr, hA2] with n htn hb hAn
    intro i
    refine le_trans (measure_mono ?_) (htn (i.1, i.2 0, i.2 1, i.2 1))
    intro ω hω
    obtain ⟨k, hk, hlt⟩ := hω
    refine ⟨k, hk, ?_⟩
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    have hmart := gridRepTailBA_mart_eq sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2 k ω
      (fun j hj ω' => (hb i.1 i.2 (j + 1) (hj.trans hk) ω').1)
    have hee : ∀ j ∈ Finset.range k, ‖twEEk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 (i.2 0) (i.2 1) (i.2 1) j ω‖ ≤
        2 * ‖STeeMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (gridTime s t K n j)
          ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Hpath s t K n j ω) i.1 i.2 i.2‖ := fun j hj => by
      have h := (hb i.1 i.2 j ((Finset.mem_range.1 hj).le.trans hk) ω).2.2
      rwa [baStep2_STEEMg_eq] at h
    have hT : ∑ j ∈ Finset.range k, gridStep s t K n * ‖twEEk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 (i.2 0) (i.2 1) (i.2 1) j ω‖ ≤
        2 * ∑ j ∈ Finset.range k, gridStep s t K n * ‖STeeMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (gridTime s t K n j)
          ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Hpath s t K n j ω) i.1 i.2 i.2‖ := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      have hΔ : 0 ≤ gridStep s t K n := ST_gridStep_nonneg s t K n (hst n)
      calc _ ≤ gridStep s t K n * (2 * ‖STeeMg _ n (gridTime s t K n j) _ i.1 i.2 i.2‖) := mul_le_mul_of_nonneg_left (hee j hj) hΔ
        _ = _ := by ring
    have hT0 : 0 ≤ ∑ j ∈ Finset.range k, gridStep s t K n * ‖twEEk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 (i.2 0) (i.2 1) (i.2 1) j ω‖ :=
      Finset.sum_nonneg fun j _ => mul_nonneg (ST_gridStep_nonneg s t K n (hst n)) (norm_nonneg _)
    have hY : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hN0.le _
    have hineq := gridRepTailBA_shift_ineq (A := ((sz.size n : ℕ) : ℝ) ^ (ε' / 2)) hY hT0 hT hAn
    have hAA : (((sz.size n : ℕ) : ℝ) ^ (ε' / 2)) * (((sz.size n : ℕ) : ℝ) ^ (ε' / 2)) = ((sz.size n : ℕ) : ℝ) ^ ε' := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    rw [hAA] at hineq
    have hmart' : ‖GridRepTailBA_Mart sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i k ω‖ =
        ‖twMart sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 (i.2 0) (i.2 1) (i.2 1) k ω‖ := by
      rw [← hmart]
    exact lt_of_le_of_lt hineq (hmart' ▸ hlt)
  · -- clause 4: `baGridWTail2_holds`
    exact hw K hK0 hKw

/-- **`baGridRepNAt2_holds`** (for every `d`): the full loop-length-2 grid statement at the BA
carrier along `BAFlow`, from `baGridBridge_holds` (its type is the inline hypothesis of `baGridRepNAt2_of_bridge`, `BAGridBridge d`). -/
theorem baGridRepNAt2_holds (d : ℕ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      STGridRepNAtgL d 2 C₀ BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0 :=
  baGridRepNAt2_of_bridge d (baGridBridge_holds d)

end Assembly

end RBM.BA


end
