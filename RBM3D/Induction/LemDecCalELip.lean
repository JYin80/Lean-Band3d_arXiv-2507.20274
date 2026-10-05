/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step5Pins
import RBM3D.Path.NetLift2
import RBM3D.Propagator.Deriv
import RBM3D.Propagator.Props4

/-!
# `lem_dec_calE` uniformly in `u`: Hölder-1/2 in `u`, relative continuity, the realized control
`J♯` and the generic lift `PrecPT → Prec` (S5-09a, ticket T2198)

The deterministic and generic half of route (d) of DECISIONS §64 for `STLemDecCalEConcl`
(`Induction/Step5Pins.lean:161-186`).  No RBM2D counterpart (RBM2D stops at the deterministic
`lemDecCalE_*`); the proofs are copies of the merged private helpers of `Path/NetLift2.lean`
(cited `NetLift2:line`) and one application of the merged `ContinuityNet.cont_core`.

* (L1) `LemDecCalELip_LK2`, `_ELKLK`, `_EGt`, `_ee`: on the good event `contGood` and for
  `u, u' ∈ [s_n, t_n]`, the four functionals `STLK2`, `STELKLK`, `STEGt`, `STee` are Hölder-1/2 in
  `u` with constant `N^C`.  The loop-level helpers (`LemDecCalELip_STLI_sub`, `_STLI_norm`,
  `_Lloop_sub`, `_Lloop_norm`, `_STKloop_two_sub`, `_STKloop_two_norm`) are public: S5-13 needs them
  for `STEEk`.
* (L2) `LemDecCalELip_relcont`: relative continuity of `(1-u)⁻¹`, `(W^d|1-u|)⁻¹`, its `1/2` power,
  `STtailTD`, `STtailTD²`.
* `LemDecCalELip_Jsharp` and `LemDecCalELip_Jsharp_basic`, `LemDecCalELip_Jsharp_rel`: the realized
  control `J♯ = max (1, max_{σ,a} STLK2 / STtailTD)` and its relative continuity.
* (G) `LemDecCalELip_lift`: `PrecPT(ξ ≺ R₀ + J^m R)` + Lipschitz + floors gives `Prec`.
-/

noncomputable section

namespace RBM.Gauss.Sizes

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Loop RBM.Path RBM.Gauss
  RBM.Ind.ContinuityNet
open scoped NNReal ENNReal

set_option linter.style.longLine false

/-! ## 1. Loops in the `L²` operator norm: the modulus and the size of a loop of any length -/

section Flow

open scoped Matrix.Norms.L2Operator

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The resolvent word `∏ᵢ G(σᵢ) E_{aᵢ}` over a list (the `foldr` of `loopL`); copy of the private
`nl2Word`, `NetLift2:52`. -/
private def lemDecCalELip_word (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (l : List (Bool × Zd d L)) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1

omit [NeZero W] in
/-- The word of a cons; copy of `nl2Word_cons`, `NetLift2:58`. -/
private theorem lemDecCalELip_word_cons (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (p : Bool × Zd d L) (l : List (Bool × Zd d L)) :
    lemDecCalELip_word H z (p :: l) = Gres H z p.1 * Eblk d L W p.2 * lemDecCalELip_word H z l :=
  rfl

/-- The word is bounded by `Q^length`; copy of `nl2_word_norm`, `NetLift2:64`. -/
private theorem lemDecCalELip_word_norm (hW : 1 ≤ W) {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    {z : ℂ} {Q : ℝ} (hQ : ∀ σ, ‖Gres H z σ‖ ≤ Q) (l : List (Bool × Zd d L)) :
    ‖lemDecCalELip_word H z l‖ ≤ Q ^ l.length := by
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hQ true)
  induction l with
  | nil => simp [lemDecCalELip_word]
  | cons p l ih =>
    have hEa := cont_norm_Eblk_le_one (d := d) (L := L) hW p.2
    rw [lemDecCalELip_word_cons, List.length_cons, pow_succ]
    calc ‖Gres H z p.1 * Eblk d L W p.2 * lemDecCalELip_word H z l‖
        ≤ ‖Gres H z p.1‖ * ‖Eblk d L W p.2‖ * ‖lemDecCalELip_word H z l‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ Q * 1 * Q ^ l.length :=
          mul_le_mul (mul_le_mul (hQ _) hEa (norm_nonneg _) hQ0) ih (norm_nonneg _) (by positivity)
      _ = Q ^ l.length * Q := by ring

/-- The `k`-fold telescoping of a resolvent word; copy of `nl2_word_diff`, `NetLift2:83`. -/
private theorem lemDecCalELip_word_diff (hW : 1 ≤ W)
    {H H' : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z z' : ℂ} {Q S : ℝ} (hQ1 : 1 ≤ Q)
    (hQ : ∀ σ, ‖Gres H z σ‖ ≤ Q) (hQ' : ∀ σ, ‖Gres H' z' σ‖ ≤ Q)
    (hS : ∀ σ, ‖Gres H z σ - Gres H' z' σ‖ ≤ S) (l : List (Bool × Zd d L)) :
    ‖lemDecCalELip_word H z l - lemDecCalELip_word H' z' l‖ ≤ (l.length : ℝ) * Q ^ l.length * S := by
  have hQ0 : 0 ≤ Q := by linarith
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS true)
  induction l with
  | nil => simp [lemDecCalELip_word]
  | cons p l ih =>
    have hEa := cont_norm_Eblk_le_one (d := d) (L := L) hW p.2
    rw [lemDecCalELip_word_cons, lemDecCalELip_word_cons]
    have key : Gres H z p.1 * Eblk d L W p.2 * lemDecCalELip_word H z l -
        Gres H' z' p.1 * Eblk d L W p.2 * lemDecCalELip_word H' z' l =
        (Gres H z p.1 - Gres H' z' p.1) * Eblk d L W p.2 * lemDecCalELip_word H z l +
          Gres H' z' p.1 * Eblk d L W p.2 *
            (lemDecCalELip_word H z l - lemDecCalELip_word H' z' l) := by
      noncomm_ring
    rw [key]
    have hP := lemDecCalELip_word_norm hW hQ l
    have t1 : ‖(Gres H z p.1 - Gres H' z' p.1) * Eblk d L W p.2 * lemDecCalELip_word H z l‖ ≤
        S * 1 * Q ^ l.length := by
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul (hS _) hEa (norm_nonneg _) hS0)) hP
        (norm_nonneg _) (by positivity)
    have t2 : ‖Gres H' z' p.1 * Eblk d L W p.2 *
        (lemDecCalELip_word H z l - lemDecCalELip_word H' z' l)‖ ≤
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

/-- The resolvent bound `‖G_u(σ)‖ ≤ Q` along the flow, from `(η_t)⁻¹ ≤ Q`. -/
private theorem lemDecCalELip_G_le (ω : Ω d L W) {E t u Q : ℝ} (hE : |E| < 2) (ht : t < 1)
    (hut : u ≤ t) (hQ : (etaT E t)⁻¹ ≤ Q) (σ : Bool) :
    ‖Gres (blockMat d L W (Hflow d L W u ω)) (zt E u) σ‖ ≤ Q := by
  have hη : 0 < etaT E t := etaT_pos hE ht
  have hHu : (blockMat d L W (Hflow d L W u ω)).IsHermitian :=
    (Hflow_isHermitian d L W u ω).submatrix _
  exact (norm_Gsig_le_inv_eta hHu hη (cont_eta_le_abs_im hE ht hut) σ).trans hQ

/-- The size of a loop along the flow: `‖tr word‖ ≤ #Vtx · Q^length`. -/
private theorem lemDecCalELip_word_trace_norm (hW : 1 ≤ W) (ω : Ω d L W) {E t u Q : ℝ}
    (hE : |E| < 2) (ht : t < 1) (hut : u ≤ t) (hQ : (etaT E t)⁻¹ ≤ Q)
    (l : List (Bool × Zd d L)) :
    ‖Matrix.trace (lemDecCalELip_word (blockMat d L W (Hflow d L W u ω)) (zt E u) l)‖ ≤
      (Fintype.card (Vtx d L W) : ℝ) * Q ^ l.length :=
  (norm_matrix_trace_le_card_mul _).trans
    (mul_le_mul_of_nonneg_left
      (lemDecCalELip_word_norm hW (fun σ => lemDecCalELip_G_le ω hE ht hut hQ σ) l)
      (Nat.cast_nonneg _))

/-- The modulus of a loop of any length along the flow, on `‖X‖ ≤ Xb`; copy of `nl2_loop_sub`
(`NetLift2:136`), stated for the trace of the word of an arbitrary list (the list loops `STLI`,
`STeeLoop`) instead of `Fin k`-indexed `loopFine`. -/
private theorem lemDecCalELip_word_trace_sub (hW : 1 ≤ W) (ω : Ω d L W) {E t u u' Q Xb : ℝ}
    (hE : |E| < 2) (ht : t < 1) (hu0 : 0 ≤ u) (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t)
    (hΔ : |u - u'| ≤ 1) (hQ1 : 1 ≤ Q) (hQ : (etaT E t)⁻¹ ≤ Q)
    (hXb : ‖blockMat d L W (Xmat d L W ω)‖ ≤ Xb) (l : List (Bool × Zd d L)) :
    ‖Matrix.trace (lemDecCalELip_word (blockMat d L W (Hflow d L W u ω)) (zt E u) l) -
        Matrix.trace (lemDecCalELip_word (blockMat d L W (Hflow d L W u' ω)) (zt E u') l)‖ ≤
      (Fintype.card (Vtx d L W) : ℝ) *
        ((l.length : ℝ) * Q ^ l.length * (Q * Q * (Xb + 1) * Real.sqrt |u - u'|)) := by
  have hη : 0 < etaT E t := etaT_pos hE ht
  have hHu : (blockMat d L W (Hflow d L W u ω)).IsHermitian :=
    (Hflow_isHermitian d L W u ω).submatrix _
  have hHu' : (blockMat d L W (Hflow d L W u' ω)).IsHermitian :=
    (Hflow_isHermitian d L W u' ω).submatrix _
  have hzu := cont_eta_le_abs_im hE ht hut
  have hzu' := cont_eta_le_abs_im hE ht hu't
  have hzz : ‖zt E u - zt E u'‖ ≤ |u - u'| :=
    (cont_norm_spectralZ_sub hE.le u u').le
  have hd : blockMat d L W (Hflow d L W u ω) - blockMat d L W (Hflow d L W u' ω) =
      ((Real.sqrt u - Real.sqrt u' : ℝ) : ℂ) • blockMat d L W (Xmat d L W ω) := by
    rw [← cont_blockMat_sub, Hflow_sub, cont_blockMat_smul]
  have hgt := cont_green_flow_diff hHu hHu' hd hXb (cont_abs_sqrt_sub_sqrt_le hu0 hu'0)
    (abs_nonneg _) hΔ hη hQ hzu hzu' hzz
  have hgf : ‖green (blockMat d L W (Hflow d L W u ω)) ((starRingEnd ℂ) (zt E u)) -
      green (blockMat d L W (Hflow d L W u' ω)) ((starRingEnd ℂ) (zt E u'))‖ ≤
      Q * Q * (Xb + 1) * Real.sqrt |u - u'| := by
    refine cont_green_flow_diff hHu hHu' hd hXb (cont_abs_sqrt_sub_sqrt_le hu0 hu'0)
      (abs_nonneg _) hΔ hη hQ ?_ ?_ ?_
    · rw [Complex.conj_im, abs_neg]; exact hzu
    · rw [Complex.conj_im, abs_neg]; exact hzu'
    · rw [← map_sub, Complex.norm_conj]; exact hzz
  have hS : ∀ σ : Bool, ‖Gres (blockMat d L W (Hflow d L W u ω)) (zt E u) σ -
      Gres (blockMat d L W (Hflow d L W u' ω)) (zt E u') σ‖ ≤
      Q * Q * (Xb + 1) * Real.sqrt |u - u'| := by
    intro σ
    cases σ
    · rw [cont_Gres_false_eq_green, cont_Gres_false_eq_green]; exact hgf
    · rw [cont_Gres_true_eq_green, cont_Gres_true_eq_green]; exact hgt
  have hw := lemDecCalELip_word_diff hW hQ1 (fun σ => lemDecCalELip_G_le ω hE ht hut hQ σ)
    (fun σ => lemDecCalELip_G_le ω hE ht hu't hQ σ) hS l
  rw [← Matrix.trace_sub]
  refine (norm_matrix_trace_le_card_mul _).trans ?_
  exact mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)

end Flow

section LoopsSz

open scoped Matrix.Norms.L2Operator

variable {d : ℕ} (sz : Sizes d)

/-- `#Vtx = N`. -/
private theorem lemDecCalELip_card_Vtx (n : ℕ) {N : ℝ} (hN : N = ((sz.size n : ℕ) : ℝ)) :
    (Fintype.card (Vtx d (sz.L n) (sz.W n)) : ℝ) = N := by
  have hN' : N = (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) := hN
  rw [card_BlockIndex, hN', mul_comm]

/-- On the good event, `‖blockMat X‖ ≤ 2N²` (`cont_norm_blockMat_Xmat_le`, `#Vtx = N`). -/
private theorem lemDecCalELip_Xb (n : ℕ) (ω : sz.SeqΩ) {N : ℝ} (hN : N = ((sz.size n : ℕ) : ℝ))
    (hgood : ∀ c : CoordF d (sz.L n) (sz.W n), |sz.slice n ω c| ≤ N) :
    ‖blockMat d (sz.L n) (sz.W n) (Xmat d (sz.L n) (sz.W n) (sz.slice n ω))‖ ≤ 2 * N ^ 2 := by
  have h := cont_norm_blockMat_Xmat_le (sz.slice n ω) hgood
  rw [lemDecCalELip_card_Vtx sz n hN] at h
  linarith

/-- **The size of a loop of any length** (`STLI`, every list loop) on `contGood`: `‖𝓛_I‖ ≤ N^{2k+1}`,
`k = |I|` the length of the zipped lists. -/
theorem LemDecCalELip_STLI_norm (n : ℕ) (E : ℝ) {t u N : ℝ} (ω : sz.SeqΩ)
    (hN : N = ((sz.size n : ℕ) : ℝ)) (hE : |E| < 2) (ht : t < 1) (hut : u ≤ t)
    (hQ : (etaT E t)⁻¹ ≤ N ^ 2) (I : LoopIdx (Zd d (sz.L n))) :
    ‖STLI sz n E u ω I‖ ≤ N ^ (2 * (I.σ.zip I.a).length + 1) := by
  have h := lemDecCalELip_word_trace_norm (sz.W_pos n) (sz.slice n ω) hE ht hut hQ
    (I.σ.zip I.a)
  rw [lemDecCalELip_card_Vtx sz n hN] at h
  refine h.trans (le_of_eq ?_)
  rw [← pow_mul]
  ring

/-- **The modulus of a loop of any length** (`STLI`, every list loop) on `contGood`:
`‖𝓛_I(u) - 𝓛_I(u')‖ ≤ 3 k N^{2k+7} √|u-u'|`, `k = |I|`; (`nl2_loop_sub`, `NetLift2:136`, with
`Q = N²`, `Xb = 2N²`). -/
theorem LemDecCalELip_STLI_sub (n : ℕ) (E : ℝ) {t u u' N : ℝ} (ω : sz.SeqΩ)
    (hN : N = ((sz.size n : ℕ) : ℝ)) (hN1 : 1 ≤ N) (hE : |E| < 2) (ht : t < 1) (hu0 : 0 ≤ u)
    (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t) (hQ : (etaT E t)⁻¹ ≤ N ^ 2)
    (hgood : ∀ c : CoordF d (sz.L n) (sz.W n), |sz.slice n ω c| ≤ N)
    (I : LoopIdx (Zd d (sz.L n))) :
    ‖STLI sz n E u ω I - STLI sz n E u' ω I‖ ≤
      3 * ((I.σ.zip I.a).length : ℝ) * N ^ (2 * (I.σ.zip I.a).length + 7) *
        Real.sqrt |u - u'| := by
  have hΔ1 : |u - u'| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hQ1 : 1 ≤ N ^ 2 := one_le_pow₀ hN1
  have hXb := lemDecCalELip_Xb sz n ω hN hgood
  have h := lemDecCalELip_word_trace_sub (sz.W_pos n) (sz.slice n ω) hE ht hu0 hut hu'0 hu't hΔ1 hQ1
    hQ hXb (I.σ.zip I.a)
  rw [lemDecCalELip_card_Vtx sz n hN] at h
  refine h.trans ?_
  set k : ℕ := (I.σ.zip I.a).length with hk
  have hs0 : 0 ≤ Real.sqrt |u - u'| := Real.sqrt_nonneg _
  have hN0 : 0 ≤ N := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have e1 : N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1) ≤ 3 * N ^ 6 := by
    have : N ^ 4 ≤ N ^ 6 := pow_le_pow_right₀ hN1 (by norm_num)
    nlinarith
  have e3 : (N ^ 2) ^ k * N ^ 7 = N ^ (2 * k + 7) := by rw [← pow_mul, ← pow_add]
  calc N * ((k : ℝ) * (N ^ 2) ^ k * (N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1) * Real.sqrt |u - u'|))
      = (k : ℝ) * (N * (N ^ 2) ^ k * (N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1))) * Real.sqrt |u - u'| := by
        ring
    _ ≤ (k : ℝ) * (N * (N ^ 2) ^ k * (3 * N ^ 6)) * Real.sqrt |u - u'| := by
        gcongr
    _ = 3 * (k : ℝ) * ((N ^ 2) ^ k * N ^ 7) * Real.sqrt |u - u'| := by ring
    _ = 3 * (k : ℝ) * N ^ (2 * k + 7) * Real.sqrt |u - u'| := by rw [e3]

/-- `𝓛^{(k)}` (`Lloop`) is `𝓛_I` (`STLI`) of the loop index `loopOf σ a` (`loopM_eq_loopL`). -/
theorem LemDecCalELip_Lloop_eq_STLI (n : ℕ) (E u : ℝ) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    Lloop sz n E u σ a ω = STLI sz n E u ω (loopOf σ a) := by
  unfold Lloop STLI loopFine
  exact loopM_eq_loopL (d := d) (L := sz.L n) (W := sz.W n) _ _ σ a

private theorem lemDecCalELip_len_loopOf (n : ℕ) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) :
    ((loopOf σ a).σ.zip (loopOf σ a).a).length = k := by
  simp [loopOf]

/-- **The size of `𝓛^{(k)}`** on `contGood`: `‖𝓛^{(k)}_{u,σ,a}‖ ≤ N^{2k+1}`. -/
theorem LemDecCalELip_Lloop_norm (n : ℕ) (E : ℝ) {t u N : ℝ} (ω : sz.SeqΩ)
    (hN : N = ((sz.size n : ℕ) : ℝ)) (hE : |E| < 2) (ht : t < 1) (hut : u ≤ t)
    (hQ : (etaT E t)⁻¹ ≤ N ^ 2) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    ‖Lloop sz n E u σ a ω‖ ≤ N ^ (2 * k + 1) := by
  have h := LemDecCalELip_STLI_norm sz n E ω hN hE ht hut hQ (loopOf σ a)
  rw [lemDecCalELip_len_loopOf] at h
  rwa [LemDecCalELip_Lloop_eq_STLI]

/-- **The modulus of `𝓛^{(k)}`** on `contGood`: `‖𝓛^{(k)}_u - 𝓛^{(k)}_{u'}‖ ≤ 3 k N^{2k+7} √|u-u'|`. -/
theorem LemDecCalELip_Lloop_sub (n : ℕ) (E : ℝ) {t u u' N : ℝ} (ω : sz.SeqΩ)
    (hN : N = ((sz.size n : ℕ) : ℝ)) (hN1 : 1 ≤ N) (hE : |E| < 2) (ht : t < 1) (hu0 : 0 ≤ u)
    (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t) (hQ : (etaT E t)⁻¹ ≤ N ^ 2)
    (hgood : ∀ c : CoordF d (sz.L n) (sz.W n), |sz.slice n ω c| ≤ N) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) :
    ‖Lloop sz n E u σ a ω - Lloop sz n E u' σ a ω‖ ≤
      3 * (k : ℝ) * N ^ (2 * k + 7) * Real.sqrt |u - u'| := by
  have h := LemDecCalELip_STLI_sub sz n E ω hN hN1 hE ht hu0 hut hu'0 hu't hQ hgood (loopOf σ a)
  rw [lemDecCalELip_len_loopOf] at h
  rwa [LemDecCalELip_Lloop_eq_STLI, LemDecCalELip_Lloop_eq_STLI]

end LoopsSz


/-! ## 2. The two-loop `𝒦^{(2)}` in the `ℓ^∞ → ℓ^∞` operator norm -/

section Kloop

open scoped Matrix.Norms.Operator

variable {d : ℕ} (sz : Sizes d)

/-- A matrix entry is at most the `ℓ^∞ → ℓ^∞` operator norm. -/
private theorem lemDecCalELip_entry_le {L : ℕ} [NeZero L] (M : Matrix (Zd d L) (Zd d L) ℂ)
    (a b : Zd d L) : ‖M a b‖ ≤ ‖M‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h1 : ‖M a b‖₊ ≤ ∑ j, ‖M a j‖₊ :=
    Finset.single_le_sum (f := fun j => ‖M a j‖₊) (fun _ _ => _root_.zero_le) (Finset.mem_univ b)
  have h2 : (∑ j, ‖M a j‖₊) ≤ Finset.univ.sup fun i => ∑ j, ‖M i j‖₊ :=
    Finset.le_sup (f := fun i => ∑ j, ‖M i j‖₊) (Finset.mem_univ a)
  exact_mod_cast h1.trans h2

/-- `𝒦^{(2)}_{u,σ,a} = W^{-d} μ Θ_{uμ}(a₀, a₁)`, `μ = m(σ₀) m(σ₁)` (`KLK_two`); copy of the private
`lemDecCalE_STKloop_two`, `Path/LemDecCalE.lean:1276`. -/
private theorem lemDecCalELip_STKloop_two_eq (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) :
    STKloop sz n E u σ a =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (mSigma E (σ 0) * mSigma E (σ 1)) *
        Theta d (sz.L n) (sz.lam n) ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) (a 0) (a 1) := by
  unfold STKloop
  have h : KLloopOf d (sz.L n) σ a = ⟨[σ 0, σ 1], [a 0, a 1]⟩ := by
    simp [KLloopOf, List.ofFn_succ]
  rw [h]
  exact KLK_two d (sz.L n) (sz.lam n) (sz.W n) E u (σ 0) (σ 1) (a 0) (a 1)

private theorem lemDecCalELip_Wd_inv_le (n : ℕ) : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast sz.W_pos n))

/-- **The size of `𝒦^{(2)}`**: `‖𝒦^{(2)}_{u,σ,a}‖ ≤ (1-t)⁻¹ ≤ N` (`KLK_two`, `norm_Theta_le`,
`‖m(σ₀) m(σ₁)‖ = 1`), for `0 ≤ u ≤ t < 1`, `|E| ≤ 2`. -/
theorem LemDecCalELip_STKloop_two_norm (n : ℕ) {E t u N : ℝ} (hE : |E| ≤ 2) (ht : t < 1)
    (hu0 : 0 ≤ u) (hut : u ≤ t) (htN : (1 - t)⁻¹ ≤ N) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) : ‖STKloop sz n E u σ a‖ ≤ N := by
  have hμ : ‖mSigma E (σ 0) * mSigma E (σ 1)‖ = 1 := by
    rw [norm_mul, norm_mSigma hE, norm_mSigma hE, one_mul]
  have hu1 : u < 1 := lt_of_le_of_lt hut ht
  have h1t : 0 < 1 - t := by linarith
  have hΘ : ‖Theta d (sz.L n) (sz.lam n) ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1)))‖ ≤ N :=
    (norm_Theta_le (sz.three_le_L n) hu0 hu1 hμ).trans
      ((inv_anti₀ h1t (by linarith)).trans htN)
  have hWd : ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_pow, Complex.norm_natCast]
    exact lemDecCalELip_Wd_inv_le sz n
  rw [lemDecCalELip_STKloop_two_eq, norm_mul, norm_mul, hμ, mul_one]
  have hent := (lemDecCalELip_entry_le
    (Theta d (sz.L n) (sz.lam n) ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1)))) (a 0) (a 1)).trans hΘ
  calc ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹‖ *
        ‖Theta d (sz.L n) (sz.lam n) ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) (a 0) (a 1)‖
      ≤ 1 * N := mul_le_mul hWd hent (norm_nonneg _) zero_le_one
    _ = N := one_mul N

/-- **The modulus of `𝒦^{(2)}`**: `‖𝒦^{(2)}_{u} - 𝒦^{(2)}_{u'}‖ ≤ N² √|u-u'|`
(`Θ_ζ - Θ_ξ = (ζ-ξ) Θ_ζ S Θ_ξ`, `Theta_sub_Theta`; `‖S‖ = 1`, `norm_SB`; `‖Θ‖ ≤ (1-t)⁻¹ ≤ N`;
`|u-u'| ≤ √|u-u'|`), for `0 ≤ u, u' ≤ t < 1`, `|E| ≤ 2`, `(1-t)⁻¹ ≤ N`. -/
theorem LemDecCalELip_STKloop_two_sub (n : ℕ) {E t u u' N : ℝ} (hE : |E| ≤ 2) (ht : t < 1)
    (hu0 : 0 ≤ u) (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t) (htN : (1 - t)⁻¹ ≤ N)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ‖STKloop sz n E u σ a - STKloop sz n E u' σ a‖ ≤ N ^ 2 * Real.sqrt |u - u'| := by
  set μ : ℂ := mSigma E (σ 0) * mSigma E (σ 1) with hμdef
  have hμ : ‖μ‖ = 1 := by
    rw [hμdef, norm_mul, norm_mSigma hE, norm_mSigma hE, one_mul]
  have hu1 : u < 1 := lt_of_le_of_lt hut ht
  have hu'1 : u' < 1 := lt_of_le_of_lt hu't ht
  have h1t : 0 < 1 - t := by linarith
  have hS := norm_SB d (sz.L n) (sz.lam n) (sz.three_le_L n)
  have hζ : ‖(u : ℂ) * μ‖ < 1 := norm_t_mul_lt_one hu0 hu1 hμ
  have hξ : ‖(u' : ℂ) * μ‖ < 1 := norm_t_mul_lt_one hu'0 hu'1 hμ
  have hΘu : ‖Theta d (sz.L n) (sz.lam n) ((u : ℂ) * μ)‖ ≤ N :=
    (norm_Theta_le (sz.three_le_L n) hu0 hu1 hμ).trans ((inv_anti₀ h1t (by linarith)).trans htN)
  have hΘu' : ‖Theta d (sz.L n) (sz.lam n) ((u' : ℂ) * μ)‖ ≤ N :=
    (norm_Theta_le (sz.three_le_L n) hu'0 hu'1 hμ).trans ((inv_anti₀ h1t (by linarith)).trans htN)
  have hN0 : 0 ≤ N := (norm_nonneg _).trans hΘu
  have hdiff := Theta_sub_Theta d (sz.L n) (sz.lam n) hS hξ hζ
  have hprod : ‖Theta d (sz.L n) (sz.lam n) ((u : ℂ) * μ) * SB d (sz.L n) (sz.lam n) *
      Theta d (sz.L n) (sz.lam n) ((u' : ℂ) * μ)‖ ≤ N * 1 * N := by
    refine (norm_mul_le _ _).trans ?_
    refine mul_le_mul ((norm_mul_le _ _).trans ?_) hΘu' (norm_nonneg _) (by positivity)
    rw [hS]
    exact mul_le_mul hΘu le_rfl (by positivity) hN0
  have hent : ‖(Theta d (sz.L n) (sz.lam n) ((u : ℂ) * μ) - Theta d (sz.L n) (sz.lam n) ((u' : ℂ) * μ))
      (a 0) (a 1)‖ ≤ |u - u'| * (N * 1 * N) := by
    rw [hdiff, Matrix.smul_apply, smul_eq_mul, norm_mul]
    have hzz : ‖(u : ℂ) * μ - (u' : ℂ) * μ‖ = |u - u'| := by
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, hμ, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
    rw [hzz]
    refine mul_le_mul le_rfl ((lemDecCalELip_entry_le _ _ _).trans hprod) (norm_nonneg _)
      (abs_nonneg _)
  have hWd : ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_pow, Complex.norm_natCast]
    exact lemDecCalELip_Wd_inv_le sz n
  have hΔs : |u - u'| ≤ Real.sqrt |u - u'| := by
    have hΔ1 : |u - u'| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    calc |u - u'| = Real.sqrt |u - u'| * Real.sqrt |u - u'| := (Real.mul_self_sqrt (abs_nonneg _)).symm
      _ ≤ Real.sqrt |u - u'| * 1 := by
          gcongr
          rw [Real.sqrt_le_one]; exact hΔ1
      _ = Real.sqrt |u - u'| := mul_one _
  have hsub : STKloop sz n E u σ a - STKloop sz n E u' σ a =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * μ *
        (Theta d (sz.L n) (sz.lam n) ((u : ℂ) * μ) -
          Theta d (sz.L n) (sz.lam n) ((u' : ℂ) * μ)) (a 0) (a 1) := by
    rw [lemDecCalELip_STKloop_two_eq, lemDecCalELip_STKloop_two_eq, Matrix.sub_apply]
    ring
  rw [hsub, norm_mul, norm_mul, hμ, mul_one]
  calc ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹‖ * ‖(Theta d (sz.L n) (sz.lam n) ((u : ℂ) * μ) -
          Theta d (sz.L n) (sz.lam n) ((u' : ℂ) * μ)) (a 0) (a 1)‖
      ≤ 1 * (|u - u'| * (N * 1 * N)) := mul_le_mul hWd hent (norm_nonneg _) zero_le_one
    _ ≤ Real.sqrt |u - u'| * (N * 1 * N) := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_right hΔs (by positivity)
    _ = N ^ 2 * Real.sqrt |u - u'| := by ring

end Kloop


/-! ## 3. The four functionals: deterministic Hölder-1/2 bounds on the good event -/

section Functionals

variable {d : ℕ} (sz : Sizes d)

/-- `W^d · #Z_L^d = N`. -/
private theorem lemDecCalELip_Wd_card (n : ℕ) {N : ℝ} (hN : N = ((sz.size n : ℕ) : ℝ)) :
    ((sz.W n : ℕ) : ℝ) ^ d * (Fintype.card (Zd d (sz.L n)) : ℝ) = N := by
  rw [card_Zd, hN]
  simp [Sizes.size, mul_pow]

/-- The bilinear sum `Σ_{x,y} A_x S_{xy} B_y` is Lipschitz: the product rule and `Σ_y |S_{xy}| = 1`
(`sum_norm_SB_row`). -/
private theorem lemDecCalELip_bilin {L : ℕ} [NeZero L] (g : ℝ) (hL : 3 ≤ L)
    (A A' B B' : Zd d L → ℂ) {δA δB αA βB : ℝ} (hδA : 0 ≤ δA) (_hδB : 0 ≤ δB) (hαA : 0 ≤ αA)
    (_hβB : 0 ≤ βB) (hA : ∀ x, ‖A x - A' x‖ ≤ δA) (hB : ∀ y, ‖B y‖ ≤ βB)
    (hA' : ∀ x, ‖A' x‖ ≤ αA) (hBd : ∀ y, ‖B y - B' y‖ ≤ δB) :
    ‖∑ x, ∑ y, A x * SB d L g x y * B y - ∑ x, ∑ y, A' x * SB d L g x y * B' y‖ ≤
      (Fintype.card (Zd d L) : ℝ) * (δA * βB + αA * δB) := by
  have hterm : ∀ x y, ‖A x * SB d L g x y * B y - A' x * SB d L g x y * B' y‖ ≤
      ‖SB d L g x y‖ * (δA * βB + αA * δB) := by
    intro x y
    have e : A x * SB d L g x y * B y - A' x * SB d L g x y * B' y =
        (A x - A' x) * SB d L g x y * B y + A' x * SB d L g x y * (B y - B' y) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(A x - A' x) * SB d L g x y * B y‖ ≤ δA * ‖SB d L g x y‖ * βB := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul (hA x) le_rfl (norm_nonneg _) hδA) (hB y) (norm_nonneg _)
        (by positivity)
    have h2 : ‖A' x * SB d L g x y * (B y - B' y)‖ ≤ αA * ‖SB d L g x y‖ * δB := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul (hA' x) le_rfl (norm_nonneg _) hαA) (hBd y) (norm_nonneg _)
        (by positivity)
    nlinarith [h1, h2]
  simp only [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hrow : ∀ x, ∑ y, ‖A x * SB d L g x y * B y - A' x * SB d L g x y * B' y‖ ≤
      δA * βB + αA * δB := by
    intro x
    calc ∑ y, ‖A x * SB d L g x y * B y - A' x * SB d L g x y * B' y‖
        ≤ ∑ y, ‖SB d L g x y‖ * (δA * βB + αA * δB) := Finset.sum_le_sum fun y _ => hterm x y
      _ = δA * βB + αA * δB := by rw [← Finset.sum_mul, sum_norm_SB_row d L g hL, one_mul]
  calc ∑ x, ‖∑ y, (A x * SB d L g x y * B y - A' x * SB d L g x y * B' y)‖
      ≤ ∑ x, (δA * βB + αA * δB) := Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans (hrow x)
    _ = (Fintype.card (Zd d L) : ℝ) * (δA * βB + αA * δB) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

section Det

open scoped Matrix.Norms.L2Operator

variable (n : ℕ) (E : ℝ) {t u u' N : ℝ} (ω : sz.SeqΩ)
  (hN : N = ((sz.size n : ℕ) : ℝ)) (hN1 : 1 ≤ N) (hE : |E| < 2) (ht : t < 1) (hu0 : 0 ≤ u)
  (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t) (hQ : (etaT E t)⁻¹ ≤ N ^ 2)
  (hgood : ∀ c : CoordF d (sz.L n) (sz.W n), |sz.slice n ω c| ≤ N) (htN : (1 - t)⁻¹ ≤ N)

include hN hN1 hE ht hu0 hut hu'0 hu't hQ hgood htN

/-- `(𝓛 - 𝒦)^{(2)}` is Hölder-1/2: `‖(𝓛-𝒦)_u - (𝓛-𝒦)_{u'}‖ ≤ 7 N^{11} √|u-u'|`. -/
theorem LemDecCalELip_LK_sub (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ‖(Lloop sz n E u σ a ω - STKloop sz n E u σ a) -
        (Lloop sz n E u' σ a ω - STKloop sz n E u' σ a)‖ ≤
      7 * N ^ 11 * Real.sqrt |u - u'| := by
  have hL := LemDecCalELip_Lloop_sub sz n E ω hN hN1 hE ht hu0 hut hu'0 hu't hQ hgood σ a
  have hK := LemDecCalELip_STKloop_two_sub sz n hE.le ht hu0 hut hu'0 hu't htN σ a
  have hs0 : 0 ≤ Real.sqrt |u - u'| := Real.sqrt_nonneg _
  have e : (Lloop sz n E u σ a ω - STKloop sz n E u σ a) -
        (Lloop sz n E u' σ a ω - STKloop sz n E u' σ a) =
      (Lloop sz n E u σ a ω - Lloop sz n E u' σ a ω) -
        (STKloop sz n E u σ a - STKloop sz n E u' σ a) := by ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have h2 : N ^ 2 ≤ N ^ 11 := pow_le_pow_right₀ hN1 (by norm_num)
  have hL' : 3 * ((2 : ℕ) : ℝ) * N ^ (2 * 2 + 7) * Real.sqrt |u - u'| =
      6 * N ^ 11 * Real.sqrt |u - u'| := by norm_num
  rw [hL'] at hL
  nlinarith [mul_le_mul_of_nonneg_right h2 hs0]

/-- **2a (deterministic)**: `|STLK2_u - STLK2_{u'}| ≤ 7 N^{11} √|u-u'|`. -/
theorem LemDecCalELip_LK2_sub (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    |STLK2 sz n E u σ a ω - STLK2 sz n E u' σ a ω| ≤ 7 * N ^ 11 * Real.sqrt |u - u'| :=
  (abs_norm_sub_norm_le _ _).trans (LemDecCalELip_LK_sub sz n E ω hN hN1 hE ht hu0 hut hu'0 hu't hQ
    hgood htN σ a)

omit hu'0 hu't hgood in
/-- `‖(𝓛 - 𝒦)^{(2)}_u‖ ≤ 2 N⁵`. -/
theorem LemDecCalELip_LK_norm (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ‖Lloop sz n E u σ a ω - STKloop sz n E u σ a‖ ≤ 2 * N ^ 5 := by
  have hL := LemDecCalELip_Lloop_norm sz n E ω hN hE ht hut hQ σ a
  have hK := LemDecCalELip_STKloop_two_norm sz n hE.le ht hu0 hut htN σ a
  have h1 : N ≤ N ^ 5 := by simpa using pow_le_pow_right₀ hN1 (show 1 ≤ 5 by norm_num)
  have hL' : N ^ (2 * 2 + 1) = N ^ 5 := by norm_num
  rw [hL'] at hL
  exact (norm_sub_le _ _).trans (by linarith)


/-- **2b (deterministic)**: `‖ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(2)}_u - ℰ^{…}_{u'}‖ ≤ 28 N^{17} √|u-u'|`
(`W^d Σ_{x,y} |A_x||S_{xy}||B_y|`, `Σ_y |S_{xy}| = 1`, `W^d #Z_L^d = N`). -/
theorem LemDecCalELip_ELKLK_sub (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ‖STELKLK sz n E u σ a ω - STELKLK sz n E u' σ a ω‖ ≤ 28 * N ^ 17 * Real.sqrt |u - u'| := by
  have eq : ∀ v : ℝ, STELKLK sz n E v σ a ω = (((sz.W n : ℕ) : ℂ) ^ d) * ∑ x, ∑ y,
      (Lloop sz n E v σ ![x, a 1] ω - STKloop sz n E v σ ![x, a 1]) * SB d (sz.L n) (sz.lam n) x y *
        (Lloop sz n E v σ ![a 0, y] ω - STKloop sz n E v σ ![a 0, y]) := fun v => rfl
  have hs0 : 0 ≤ Real.sqrt |u - u'| := Real.sqrt_nonneg _
  have hN0 : 0 ≤ N := by linarith
  have hbil := lemDecCalELip_bilin (d := d) (L := sz.L n) (sz.lam n) (sz.three_le_L n)
    (fun x => Lloop sz n E u σ ![x, a 1] ω - STKloop sz n E u σ ![x, a 1])
    (fun x => Lloop sz n E u' σ ![x, a 1] ω - STKloop sz n E u' σ ![x, a 1])
    (fun y => Lloop sz n E u σ ![a 0, y] ω - STKloop sz n E u σ ![a 0, y])
    (fun y => Lloop sz n E u' σ ![a 0, y] ω - STKloop sz n E u' σ ![a 0, y])
    (δA := 7 * N ^ 11 * Real.sqrt |u - u'|) (δB := 7 * N ^ 11 * Real.sqrt |u - u'|)
    (αA := 2 * N ^ 5) (βB := 2 * N ^ 5) (by positivity) (by positivity) (by positivity)
    (by positivity)
    (fun x => LemDecCalELip_LK_sub sz n E ω hN hN1 hE ht hu0 hut hu'0 hu't hQ hgood htN σ _)
    (fun y => LemDecCalELip_LK_norm sz n E ω hN hN1 hE ht hu0 hut hQ htN σ _)
    (fun x => LemDecCalELip_LK_norm sz n E ω hN hN1 hE ht hu'0 hu't hQ htN σ _)
    (fun y => LemDecCalELip_LK_sub sz n E ω hN hN1 hE ht hu0 hut hu'0 hu't hQ hgood htN σ _)
  rw [eq u, eq u', ← mul_sub, norm_mul, norm_pow, Complex.norm_natCast]
  have hWd : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  calc ((sz.W n : ℕ) : ℝ) ^ d * ‖∑ x, ∑ y, (Lloop sz n E u σ ![x, a 1] ω - STKloop sz n E u σ ![x, a 1]) *
          SB d (sz.L n) (sz.lam n) x y * (Lloop sz n E u σ ![a 0, y] ω - STKloop sz n E u σ ![a 0, y]) -
        ∑ x, ∑ y, (Lloop sz n E u' σ ![x, a 1] ω - STKloop sz n E u' σ ![x, a 1]) *
          SB d (sz.L n) (sz.lam n) x y * (Lloop sz n E u' σ ![a 0, y] ω - STKloop sz n E u' σ ![a 0, y])‖
      ≤ ((sz.W n : ℕ) : ℝ) ^ d * ((Fintype.card (Zd d (sz.L n)) : ℝ) *
          (7 * N ^ 11 * Real.sqrt |u - u'| * (2 * N ^ 5) + 2 * N ^ 5 * (7 * N ^ 11 * Real.sqrt |u - u'|))) :=
        mul_le_mul_of_nonneg_left hbil hWd
    _ = N * (28 * N ^ 16 * Real.sqrt |u - u'|) := by
        rw [← mul_assoc, lemDecCalELip_Wd_card sz n hN]; ring
    _ = 28 * N ^ 17 * Real.sqrt |u - u'| := by ring

omit htN in
/-- The one-loop `⟨G̃_u(τ) E_x⟩ = 𝓛^{(1)}_{u,τ,x} - m(τ)` moves by `3 N⁹ √|u-u'|`. -/
private theorem lemDecCalELip_avg_sub (τ : Bool) (x : Zd d (sz.L n)) :
    ‖(Lloop sz n E u (fun _ : Fin 1 => τ) (fun _ => x) ω - STmsig E τ) -
        (Lloop sz n E u' (fun _ : Fin 1 => τ) (fun _ => x) ω - STmsig E τ)‖ ≤
      3 * N ^ 9 * Real.sqrt |u - u'| := by
  have h := LemDecCalELip_Lloop_sub sz n E ω hN hN1 hE ht hu0 hut hu'0 hu't hQ hgood
    (fun _ : Fin 1 => τ) (fun _ => x)
  rw [sub_sub_sub_cancel_right]
  refine h.trans (le_of_eq ?_)
  norm_num

omit hu0 hu'0 hu't hgood htN in
/-- `‖⟨G̃_u(τ) E_x⟩‖ ≤ 2 N³`. -/
private theorem lemDecCalELip_avg_norm (τ : Bool) (x : Zd d (sz.L n)) :
    ‖Lloop sz n E u (fun _ : Fin 1 => τ) (fun _ => x) ω - STmsig E τ‖ ≤ 2 * N ^ 3 := by
  have h := LemDecCalELip_Lloop_norm sz n E ω hN hE ht hut hQ (fun _ : Fin 1 => τ) (fun _ => x)
  have hm : ‖STmsig E τ‖ = 1 := norm_mSigma hE.le τ
  have h1 : (1 : ℝ) ≤ N ^ 3 := one_le_pow₀ hN1
  have h3 : N ^ (2 * 1 + 1) = N ^ 3 := by norm_num
  rw [h3] at h
  exact (norm_sub_le _ _).trans (by linarith)

omit htN in
/-- **2c (deterministic)**: `‖ℰ^{G̃,(2)}_u - ℰ^{G̃,(2)}_{u'}‖ ≤ 42 N^{17} √|u-u'|`
(`W^d Σ_{x,y} ⟨G̃E_x⟩ S_{xy} 𝓛^{(3)}`, two terms; the one-loop moves by `3N⁹√`, has size `2N³`,
the three-loop moves by `9N¹³√`, has size `N⁷`). -/
theorem LemDecCalELip_EGt_sub (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ‖STEGt sz n E u σ a ω - STEGt sz n E u' σ a ω‖ ≤ 42 * N ^ 17 * Real.sqrt |u - u'| := by
  have eq : ∀ v : ℝ, STEGt sz n E v σ a ω = (((sz.W n : ℕ) : ℂ) ^ d) * (
      (∑ x, ∑ y, (Lloop sz n E v (fun _ : Fin 1 => σ 0) (fun _ => x) ω - STmsig E (σ 0)) *
          SB d (sz.L n) (sz.lam n) x y * Lloop sz n E v ![σ 0, σ 0, σ 1] ![y, a 0, a 1] ω) +
      (∑ x, ∑ y, (Lloop sz n E v (fun _ : Fin 1 => σ 1) (fun _ => x) ω - STmsig E (σ 1)) *
          SB d (sz.L n) (sz.lam n) x y * Lloop sz n E v ![σ 0, σ 1, σ 1] ![a 0, y, a 1] ω)) := by
    intro v
    unfold STEGt STEGtM
    simp only [STavgM, STLM_seqHflow, Finset.sum_add_distrib]
  have hs0 : 0 ≤ Real.sqrt |u - u'| := Real.sqrt_nonneg _
  have hN0 : 0 ≤ N := by linarith
  have key : ∀ (τ : Bool) (τ3 : Fin 3 → Bool) (b3 : Zd d (sz.L n) → Fin 3 → Zd d (sz.L n)),
      ‖(∑ x, ∑ y, (Lloop sz n E u (fun _ : Fin 1 => τ) (fun _ => x) ω - STmsig E τ) *
            SB d (sz.L n) (sz.lam n) x y * Lloop sz n E u τ3 (b3 y) ω) -
        (∑ x, ∑ y, (Lloop sz n E u' (fun _ : Fin 1 => τ) (fun _ => x) ω - STmsig E τ) *
            SB d (sz.L n) (sz.lam n) x y * Lloop sz n E u' τ3 (b3 y) ω)‖ ≤
        (Fintype.card (Zd d (sz.L n)) : ℝ) * (21 * N ^ 16 * Real.sqrt |u - u'|) := by
    intro τ τ3 b3
    have h3n : ∀ (v : ℝ), 0 ≤ v → v ≤ t → ∀ y, ‖Lloop sz n E v τ3 (b3 y) ω‖ ≤ N ^ 7 := by
      intro v hv0 hvt y
      have h := LemDecCalELip_Lloop_norm sz n E ω hN hE ht hvt hQ τ3 (b3 y)
      have h3 : N ^ (2 * 3 + 1) = N ^ 7 := by norm_num
      rwa [h3] at h
    have h3s : ∀ y, ‖Lloop sz n E u τ3 (b3 y) ω - Lloop sz n E u' τ3 (b3 y) ω‖ ≤
        9 * N ^ 13 * Real.sqrt |u - u'| := by
      intro y
      refine (LemDecCalELip_Lloop_sub sz n E ω hN hN1 hE ht hu0 hut hu'0 hu't hQ hgood τ3
        (b3 y)).trans (le_of_eq ?_)
      norm_num
    have hb := lemDecCalELip_bilin (d := d) (L := sz.L n) (sz.lam n) (sz.three_le_L n)
      (fun x => Lloop sz n E u (fun _ : Fin 1 => τ) (fun _ => x) ω - STmsig E τ)
      (fun x => Lloop sz n E u' (fun _ : Fin 1 => τ) (fun _ => x) ω - STmsig E τ)
      (fun y => Lloop sz n E u τ3 (b3 y) ω) (fun y => Lloop sz n E u' τ3 (b3 y) ω)
      (δA := 3 * N ^ 9 * Real.sqrt |u - u'|) (δB := 9 * N ^ 13 * Real.sqrt |u - u'|)
      (αA := 2 * N ^ 3) (βB := N ^ 7) (by positivity) (by positivity) (by positivity)
      (by positivity) (fun x => lemDecCalELip_avg_sub sz n E ω hN hN1 hE ht hu0 hut hu'0 hu't hQ
        hgood τ x)
      (fun y => h3n u hu0 hut y)
      (fun x => lemDecCalELip_avg_norm sz n E ω hN hN1 hE ht hu't hQ τ x)
      h3s
    refine hb.trans (le_of_eq ?_)
    ring
  have k1 := key (σ 0) ![σ 0, σ 0, σ 1] (fun y => ![y, a 0, a 1])
  have k2 := key (σ 1) ![σ 0, σ 1, σ 1] (fun y => ![a 0, y, a 1])
  rw [eq u, eq u', ← mul_sub, norm_mul, norm_pow, Complex.norm_natCast]
  have hWd : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hsplit : ∀ P1 P2 P1' P2' : ℂ, (P1 + P2) - (P1' + P2') = (P1 - P1') + (P2 - P2') :=
    fun _ _ _ _ => by ring
  rw [hsplit]
  refine (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add k1 k2)) hWd).trans
    (le_of_eq ?_)
  calc ((sz.W n : ℕ) : ℝ) ^ d * ((Fintype.card (Zd d (sz.L n)) : ℝ) * (21 * N ^ 16 * Real.sqrt |u - u'|) +
        (Fintype.card (Zd d (sz.L n)) : ℝ) * (21 * N ^ 16 * Real.sqrt |u - u'|))
      = (((sz.W n : ℕ) : ℝ) ^ d * (Fintype.card (Zd d (sz.L n)) : ℝ)) *
          (42 * N ^ 16 * Real.sqrt |u - u'|) := by ring
    _ = 42 * N ^ 17 * Real.sqrt |u - u'| := by rw [lemDecCalELip_Wd_card sz n hN]; ring

omit hN hN1 hE ht hu0 hut hu'0 hu't hQ hgood htN in
/-- The cut loop `STeeLoop` of `m = 2` and `k ∈ {1, 2}` has `6` edges. -/
private theorem lemDecCalELip_STeeLoop_len {α : Type*} (σ : Fin 2 → Bool) (a a' : Fin 2 → α)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 2) (b b' : α) :
    ((STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b').σ.zip
      (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b').a).length = 6 := by
  have hk' : k = 1 ∨ k = 2 := by
    simp only [Finset.mem_Icc] at hk
    omega
  rcases hk' with rfl | rfl <;> simp [STeeLoop, List.ofFn_succ]

omit htN in
/-- **2d (deterministic)**: `‖(ℰ⊗ℰ)^{M,(2)}_u - (ℰ⊗ℰ)^{M,(2)}_{u'}‖ ≤ 36 N^{20} √|u-u'|`
(`W^d Σ_{k=1,2} Σ_{b,b'} |S_{bb'}| |𝓛^{(6)}_u - 𝓛^{(6)}_{u'}|`, the `6`-loop `STeeLoop` moves by
`18 N^{19} √`, `Σ_{b'} |S_{bb'}| = 1`, `W^d L^d = N`). -/
theorem LemDecCalELip_ee_sub (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)) :
    ‖STee sz n E u ω σ a a' - STee sz n E u' ω σ a a'‖ ≤ 36 * N ^ 20 * Real.sqrt |u - u'| := by
  have hs0 : 0 ≤ Real.sqrt |u - u'| := Real.sqrt_nonneg _
  have hN0 : 0 ≤ N := by linarith
  unfold STee
  rw [← mul_sub, norm_mul, norm_pow, Complex.norm_natCast]
  have hWd : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hterm : ∀ k ∈ Finset.Icc 1 2, ∀ b b' : Zd d (sz.L n),
      ‖SB d (sz.L n) (sz.lam n) b b' *
          STLI sz n E u ω (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b') -
        SB d (sz.L n) (sz.lam n) b b' *
          STLI sz n E u' ω (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b')‖ ≤
      ‖SB d (sz.L n) (sz.lam n) b b'‖ * (18 * N ^ 19 * Real.sqrt |u - u'|) := by
    intro k hk b b'
    rw [← mul_sub, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h := LemDecCalELip_STLI_sub sz n E ω hN hN1 hE ht hu0 hut hu'0 hu't hQ hgood
      (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b')
    rw [lemDecCalELip_STeeLoop_len σ a a' hk b b'] at h
    refine h.trans (le_of_eq ?_)
    norm_num
  have hb : ∀ k ∈ Finset.Icc 1 2, ∀ b : Zd d (sz.L n),
      ‖∑ b', (SB d (sz.L n) (sz.lam n) b b' *
          STLI sz n E u ω (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b') -
        SB d (sz.L n) (sz.lam n) b b' *
          STLI sz n E u' ω (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b'))‖ ≤
      18 * N ^ 19 * Real.sqrt |u - u'| := by
    intro k hk b
    refine (norm_sum_le _ _).trans ?_
    calc ∑ b', ‖SB d (sz.L n) (sz.lam n) b b' *
          STLI sz n E u ω (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b') -
        SB d (sz.L n) (sz.lam n) b b' *
          STLI sz n E u' ω (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b')‖
        ≤ ∑ b', ‖SB d (sz.L n) (sz.lam n) b b'‖ * (18 * N ^ 19 * Real.sqrt |u - u'|) :=
          Finset.sum_le_sum fun b' _ => hterm k hk b b'
      _ = 18 * N ^ 19 * Real.sqrt |u - u'| := by
          rw [← Finset.sum_mul, sum_norm_SB_row d (sz.L n) (sz.lam n) (sz.three_le_L n), one_mul]
  have hk : ∀ k ∈ Finset.Icc 1 2,
      ‖∑ b, ∑ b', (SB d (sz.L n) (sz.lam n) b b' *
          STLI sz n E u ω (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b') -
        SB d (sz.L n) (sz.lam n) b b' *
          STLI sz n E u' ω (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b'))‖ ≤
      (Fintype.card (Zd d (sz.L n)) : ℝ) * (18 * N ^ 19 * Real.sqrt |u - u'|) := by
    intro k hk
    refine (norm_sum_le _ _).trans ?_
    calc ∑ b, ‖∑ b', (SB d (sz.L n) (sz.lam n) b b' *
          STLI sz n E u ω (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b') -
        SB d (sz.L n) (sz.lam n) b b' *
          STLI sz n E u' ω (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b'))‖
        ≤ ∑ _b : Zd d (sz.L n), 18 * N ^ 19 * Real.sqrt |u - u'| :=
          Finset.sum_le_sum fun b _ => hb k hk b
      _ = (Fintype.card (Zd d (sz.L n)) : ℝ) * (18 * N ^ 19 * Real.sqrt |u - u'|) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [← Finset.sum_sub_distrib]
  have htot : ‖∑ k ∈ Finset.Icc 1 2, ∑ b, ∑ b', (SB d (sz.L n) (sz.lam n) b b' *
          STLI sz n E u ω (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b') -
        SB d (sz.L n) (sz.lam n) b b' *
          STLI sz n E u' ω (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b'))‖ ≤
      2 * ((Fintype.card (Zd d (sz.L n)) : ℝ) * (18 * N ^ 19 * Real.sqrt |u - u'|)) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ Finset.Icc 1 2, ‖∑ b, ∑ b', (SB d (sz.L n) (sz.lam n) b b' *
          STLI sz n E u ω (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b') -
        SB d (sz.L n) (sz.lam n) b b' *
          STLI sz n E u' ω (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b'))‖
        ≤ ∑ _k ∈ Finset.Icc 1 2, (Fintype.card (Zd d (sz.L n)) : ℝ) *
            (18 * N ^ 19 * Real.sqrt |u - u'|) := Finset.sum_le_sum fun k hk' => hk k hk'
      _ = 2 * ((Fintype.card (Zd d (sz.L n)) : ℝ) * (18 * N ^ 19 * Real.sqrt |u - u'|)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp
  refine (mul_le_mul_of_nonneg_left htot hWd).trans (le_of_eq ?_)
  calc ((sz.W n : ℕ) : ℝ) ^ d * (2 * ((Fintype.card (Zd d (sz.L n)) : ℝ) *
        (18 * N ^ 19 * Real.sqrt |u - u'|)))
      = (((sz.W n : ℕ) : ℝ) ^ d * (Fintype.card (Zd d (sz.L n)) : ℝ)) *
          (36 * N ^ 19 * Real.sqrt |u - u'|) := by ring
    _ = 36 * N ^ 20 * Real.sqrt |u - u'| := by rw [lemDecCalELip_Wd_card sz n hN]; ring

end Det

end Functionals


/-! ## 4. (L1): the four functionals are Hölder-1/2 in `u` on `contGood` -/

section L1

variable {d : ℕ}

/-- `(η_t)⁻¹ ≤ N²` from `(1 - t)⁻¹ ≤ N`, `Im m ≥ c₁` and `1/c₁ ≤ N` (copy of the private
`nl2_eta_inv_le`, `NetLift2:203`). -/
private theorem lemDecCalELip_eta_inv_le {E t N c₁ : ℝ} (hE : |E| < 2) (hN0 : 0 < N)
    (hc₁ : 0 < c₁) (hc₁m : c₁ ≤ (mE E).im) (hNc : 1 / c₁ ≤ N) (hN1 : (1 - t)⁻¹ ≤ N) :
    (etaT E t)⁻¹ ≤ N ^ 2 := by
  have hm : 0 < (mE E).im := mE_im_pos hE
  have h1 : (etaT E t)⁻¹ = (1 - t)⁻¹ * ((mE E).im)⁻¹ := by
    unfold etaT; rw [mul_inv]
  have h2 : ((mE E).im)⁻¹ ≤ N := by
    refine le_trans ?_ hNc
    rw [one_div]; exact inv_anti₀ hc₁ hc₁m
  rw [h1, sq]
  exact mul_le_mul hN1 h2 (inv_nonneg.2 hm.le) hN0.le

/-- **The eventual numerical facts of (L1)**, public for S5-13 (`STEEk`): `M ≤ N`, `1 ≤ N`, `|E_n| < 2`,
`(η_t)⁻¹ ≤ N²`, `(1 - t)⁻¹ ≤ N` (`cont_bulk` for `c₁ = √(2κ)/2`, `1/c₁ ≤ N` from `SizeTendsto`);
these are the hypotheses `hN1`, `hE`, `hQ` of the loop-level helpers `LemDecCalELip_STLI_sub`,
`_STLI_norm`, `_Lloop_sub`, `_Lloop_norm`, `_STKloop_two_sub`, `_STKloop_two_norm`. -/
theorem LemDecCalELip_env (sz : Sizes d) (E t : ℕ → ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hE : ∀ n, |E n| ≤ 2 - κ) (hsize : sz.SizeTendsto)
    (hN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) (M : ℝ) :
    ∀ᶠ n in atTop, M ≤ ((sz.size n : ℕ) : ℝ) ∧ 1 ≤ ((sz.size n : ℕ) : ℝ) ∧ |E n| < 2 ∧
      (etaT (E n) (t n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ 2 ∧ (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
  set c₁ : ℝ := Real.sqrt (2 * κ) / 2 with hc₁def
  have hc₁ : 0 < c₁ := by
    rw [hc₁def]
    have := Real.sqrt_pos.2 (by linarith : 0 < 2 * κ)
    linarith
  have hbulk : ∀ n, |E n| < 2 ∧ c₁ ≤ (mE (E n)).im := fun n => cont_bulk hκ (hE n)
  filter_upwards [hsize.eventually_ge_atTop (max M (max 1 (1 / c₁))), hN] with n h1 h2
  have hM : M ≤ ((sz.size n : ℕ) : ℝ) := (le_max_left _ _).trans h1
  have h1N : 1 ≤ ((sz.size n : ℕ) : ℝ) := ((le_max_left _ _).trans (le_max_right _ _)).trans h1
  have hc : 1 / c₁ ≤ ((sz.size n : ℕ) : ℝ) := ((le_max_right _ _).trans (le_max_right _ _)).trans h1
  exact ⟨hM, h1N, (hbulk n).1,
    lemDecCalELip_eta_inv_le (hbulk n).1 (by linarith) hc₁ (hbulk n).2 hc h2, h2⟩

/-- `c · N^e · x ≤ N^{e+1} · x` for `c ≤ N`, `x ≥ 0`: the constant is absorbed in the exponent. -/
private theorem lemDecCalELip_absorb {N c x : ℝ} {e : ℕ} (hc : c ≤ N) (hN0 : 0 ≤ N) (hx : 0 ≤ x) :
    c * N ^ e * x ≤ N ^ (((e + 1 : ℕ)) : ℝ) * x := by
  rw [Real.rpow_natCast, pow_succ]
  have h : 0 ≤ N ^ e := pow_nonneg hN0 e
  calc c * N ^ e * x = (N ^ e * c) * x := by ring
    _ ≤ (N ^ e * N) * x := by gcongr

/-- **2a (L1)**: `STLK2` is Hölder-1/2 in `u ∈ [s_n, t_n]` on `contGood`, constant `N^{12}`. -/
theorem LemDecCalELip_LK2 (sz : Sizes d) (E s t : ℕ → ℝ) (κ : ℝ) (_hd : 3 ≤ d)
    (hsize : sz.SizeTendsto) (hκ : 0 < κ) (hE : ∀ n, |E n| ≤ 2 - κ) (hs : ∀ n, 0 ≤ s n)
    (ht : ∀ n, t n < 1) (htN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz n,
      ∀ (u u' : TimeIcc s t n) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        |STLK2 sz n (E n) (u : ℝ) σ a ω - STLK2 sz n (E n) (u' : ℝ) σ a ω| ≤
          ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)| := by
  refine ⟨((12 : ℕ) : ℝ), Nat.cast_nonneg _, ?_⟩
  filter_upwards [LemDecCalELip_env sz E t κ hκ hE hsize htN 7] with n hn ω hω u u' σ a
  obtain ⟨h7, h1, hE2, hQ, hN1⟩ := hn
  have h := LemDecCalELip_LK2_sub sz n (E n) ω (N := ((sz.size n : ℕ) : ℝ)) rfl h1 hE2 (ht n)
    ((hs n).trans u.2.1) u.2.2 ((hs n).trans u'.2.1) u'.2.2 hQ (fun c => hω c) hN1 σ a
  exact h.trans (lemDecCalELip_absorb (e := 11) h7 (by linarith) (Real.sqrt_nonneg _))

/-- **2b (L1)**: `STELKLK` is Hölder-1/2 in `u` on `contGood`, constant `N^{18}`. -/
theorem LemDecCalELip_ELKLK (sz : Sizes d) (E s t : ℕ → ℝ) (κ : ℝ) (_hd : 3 ≤ d)
    (hsize : sz.SizeTendsto) (hκ : 0 < κ) (hE : ∀ n, |E n| ≤ 2 - κ) (hs : ∀ n, 0 ≤ s n)
    (ht : ∀ n, t n < 1) (htN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz n,
      ∀ (u u' : TimeIcc s t n) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STELKLK sz n (E n) (u : ℝ) σ a ω - STELKLK sz n (E n) (u' : ℝ) σ a ω‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)| := by
  refine ⟨((17 + 1 : ℕ) : ℝ), Nat.cast_nonneg _, ?_⟩
  filter_upwards [LemDecCalELip_env sz E t κ hκ hE hsize htN 28] with n hn ω hω u u' σ a
  obtain ⟨h7, h1, hE2, hQ, hN1⟩ := hn
  have h := LemDecCalELip_ELKLK_sub sz n (E n) ω (N := ((sz.size n : ℕ) : ℝ)) rfl h1 hE2 (ht n)
    ((hs n).trans u.2.1) u.2.2 ((hs n).trans u'.2.1) u'.2.2 hQ (fun c => hω c) hN1 σ a
  exact h.trans (lemDecCalELip_absorb (e := 17) h7 (by linarith) (Real.sqrt_nonneg _))

/-- **2c (L1)**: `STEGt` is Hölder-1/2 in `u` on `contGood`, constant `N^{18}`. -/
theorem LemDecCalELip_EGt (sz : Sizes d) (E s t : ℕ → ℝ) (κ : ℝ) (_hd : 3 ≤ d)
    (hsize : sz.SizeTendsto) (hκ : 0 < κ) (hE : ∀ n, |E n| ≤ 2 - κ) (hs : ∀ n, 0 ≤ s n)
    (ht : ∀ n, t n < 1) (htN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz n,
      ∀ (u u' : TimeIcc s t n) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STEGt sz n (E n) (u : ℝ) σ a ω - STEGt sz n (E n) (u' : ℝ) σ a ω‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)| := by
  refine ⟨((17 + 1 : ℕ) : ℝ), Nat.cast_nonneg _, ?_⟩
  filter_upwards [LemDecCalELip_env sz E t κ hκ hE hsize htN 42] with n hn ω hω u u' σ a
  obtain ⟨h7, h1, hE2, hQ, hN1⟩ := hn
  have h := LemDecCalELip_EGt_sub sz n (E n) ω (N := ((sz.size n : ℕ) : ℝ)) rfl h1 hE2 (ht n)
    ((hs n).trans u.2.1) u.2.2 ((hs n).trans u'.2.1) u'.2.2 hQ (fun c => hω c) σ a
  exact h.trans (lemDecCalELip_absorb (e := 17) h7 (by linarith) (Real.sqrt_nonneg _))

/-- **2d (L1)**: `STee` (`m = 2`, every `a'`) is Hölder-1/2 in `u` on `contGood`, constant `N^{21}`. -/
theorem LemDecCalELip_ee (sz : Sizes d) (E s t : ℕ → ℝ) (κ : ℝ) (_hd : 3 ≤ d)
    (hsize : sz.SizeTendsto) (hκ : 0 < κ) (hE : ∀ n, |E n| ≤ 2 - κ) (hs : ∀ n, 0 ≤ s n)
    (ht : ∀ n, t n < 1) (htN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz n,
      ∀ (u u' : TimeIcc s t n) (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)),
        ‖STee sz n (E n) (u : ℝ) ω σ a a' - STee sz n (E n) (u' : ℝ) ω σ a a'‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)| := by
  refine ⟨((20 + 1 : ℕ) : ℝ), Nat.cast_nonneg _, ?_⟩
  filter_upwards [LemDecCalELip_env sz E t κ hκ hE hsize htN 36] with n hn ω hω u u' σ a a'
  obtain ⟨h7, h1, hE2, hQ, hN1⟩ := hn
  have h := LemDecCalELip_ee_sub sz n (E n) ω (N := ((sz.size n : ℕ) : ℝ)) rfl h1 hE2 (ht n)
    ((hs n).trans u.2.1) u.2.2 ((hs n).trans u'.2.1) u'.2.2 hQ (fun c => hω c) σ a a'
  exact h.trans (lemDecCalELip_absorb (e := 20) h7 (by linarith) (Real.sqrt_nonneg _))

end L1


/-! ## 5. (L2): relative continuity of the deterministic factors -/

section L2

variable {d : ℕ}

/-- **(L2) relative continuity of the deterministic factors of `STLemDecCalEConcl`**
(`Step5Pins.lean:164-186`): for `u, u' ≤ t < 1`, `ρ = 1 + (1-t)⁻¹ |u-u'|`: `(1-u')⁻¹ ≤ ρ (1-u)⁻¹`, the
same for `(W^d|1-u|)⁻¹`, `ρ` for its `1/2` power, `ρ²` for `STtailTD`, `ρ⁴` for `STtailTD²`
(`cont_inv_add_one_sub_ratio` at `γ = 0`).  Deterministic, every `n, D, a`. -/
theorem LemDecCalELip_relcont (sz : Sizes d) (n : ℕ) (t u u' D : ℝ) (a : Fin 2 → Zd d (sz.L n))
    (ht : t < 1) (hut : u ≤ t) (hu't : u' ≤ t) :
    (1 - u')⁻¹ ≤ (1 + (1 - t)⁻¹ * |u - u'|) * (1 - u)⁻¹ ∧
    (((sz.W n : ℕ) : ℝ) ^ d * |1 - u'|)⁻¹ ≤
      (1 + (1 - t)⁻¹ * |u - u'|) * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ∧
    (((sz.W n : ℕ) : ℝ) ^ d * |1 - u'|)⁻¹ ^ (1 / 2 : ℝ) ≤
      (1 + (1 - t)⁻¹ * |u - u'|) * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) ∧
    STtailTD sz n u' D a ≤ (1 + (1 - t)⁻¹ * |u - u'|) ^ 2 * STtailTD sz n u D a ∧
    STtailTD sz n u' D a ^ 2 ≤ (1 + (1 - t)⁻¹ * |u - u'|) ^ 4 * STtailTD sz n u D a ^ 2 := by
  have h1t : 0 < 1 - t := by linarith
  have hu1 : 0 < 1 - u := by linarith
  have hu'1 : 0 < 1 - u' := by linarith
  set ρ : ℝ := 1 + (1 - t)⁻¹ * |u - u'| with hρdef
  have hρ1 : 1 ≤ ρ := by
    have : 0 ≤ (1 - t)⁻¹ * |u - u'| := mul_nonneg (inv_nonneg.2 h1t.le) (abs_nonneg _)
    linarith
  have hρ0 : 0 ≤ ρ := by linarith
  have e1 : (1 - u')⁻¹ ≤ ρ * (1 - u)⁻¹ := by
    have h := cont_inv_add_one_sub_ratio (γ := 0) le_rfl ht hu't hut
    rw [zero_add, zero_add, abs_sub_comm] at h
    exact h
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
  have e2 : (((sz.W n : ℕ) : ℝ) ^ d * |1 - u'|)⁻¹ ≤ ρ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ := by
    rw [abs_of_pos hu1, abs_of_pos hu'1, mul_inv, mul_inv]
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 - u')⁻¹ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (ρ * (1 - u)⁻¹) :=
          mul_le_mul_of_nonneg_left e1 (inv_nonneg.2 hWd.le)
      _ = ρ * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 - u)⁻¹) := by ring
  have hy0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ := inv_nonneg.2 (by positivity)
  have hy'0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d * |1 - u'|)⁻¹ := inv_nonneg.2 (by positivity)
  have e3 : (((sz.W n : ℕ) : ℝ) ^ d * |1 - u'|)⁻¹ ^ (1 / 2 : ℝ) ≤
      ρ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) := by
    calc (((sz.W n : ℕ) : ℝ) ^ d * |1 - u'|)⁻¹ ^ (1 / 2 : ℝ)
        ≤ (ρ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hy'0 e2 (by norm_num)
      _ = ρ ^ (1 / 2 : ℝ) * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) :=
          Real.mul_rpow hρ0 hy0
      _ ≤ ρ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hy0 _)
          calc ρ ^ (1 / 2 : ℝ) ≤ ρ ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hρ1 (by norm_num)
            _ = ρ := Real.rpow_one ρ
  have e4 : STtailTD sz n u' D a ≤ ρ ^ 2 * STtailTD sz n u D a := by
    unfold STtailTD tailTD
    set e : ℝ := Real.exp (-Real.sqrt ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) with he
    have he0 : 0 ≤ e := (Real.exp_pos _).le
    have hr0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW.le _
    have h2 : (((sz.W n : ℕ) : ℝ) ^ d * |1 - u'|)⁻¹ ^ 2 ≤
        ρ ^ 2 * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ 2 := by
      calc (((sz.W n : ℕ) : ℝ) ^ d * |1 - u'|)⁻¹ ^ 2
          ≤ (ρ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹) ^ 2 := pow_le_pow_left₀ hy'0 e2 2
        _ = ρ ^ 2 * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ 2 := by ring
    have hρ2 : 1 ≤ ρ ^ 2 := one_le_pow₀ hρ1
    calc (((sz.W n : ℕ) : ℝ) ^ d * |1 - u'|)⁻¹ ^ 2 * e + ((sz.W n : ℕ) : ℝ) ^ (-D)
        ≤ ρ ^ 2 * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ 2 * e +
          ρ ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D) :=
          add_le_add (mul_le_mul_of_nonneg_right h2 he0) (by nlinarith)
      _ = ρ ^ 2 * ((((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ 2 * e + ((sz.W n : ℕ) : ℝ) ^ (-D)) := by
          ring
  have hT0 : 0 ≤ STtailTD sz n u' D a := tailTD_nonneg hW.le
  refine ⟨e1, e2, e3, e4, ?_⟩
  calc STtailTD sz n u' D a ^ 2 ≤ (ρ ^ 2 * STtailTD sz n u D a) ^ 2 := pow_le_pow_left₀ hT0 e4 2
    _ = ρ ^ 4 * STtailTD sz n u D a ^ 2 := by ring

end L2

/-! ## 6. The realized control `J♯` -/

section Jsharp

variable {d : ℕ}

/-- **The realized control** `J♯(n,u,ω) := max(1, max_{σ ∈ {±}², a} |(𝓛-𝒦)^{(2)}_{u,σ,a}| /
T_{u,D}(|a₁-a₂|))` at the single time `u` (supervisor 1.3; `sup'` written as in the merged
`STJhatM`, `Induction/Step2Defs.lean:81-86`). -/
noncomputable def LemDecCalELip_Jsharp {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (D : ℝ) (n : ℕ) (u : ℝ)
    (ω : sz.SeqΩ) : ℝ :=
  max 1 (Finset.univ.sup' ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
    (fun p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) =>
      STLK2 sz n (E n) u p.1 p.2 ω / STtailTD sz n u D p.2))

/-- `STtailTD > 0` (`W^{-D} > 0`). -/
theorem LemDecCalELip_tail_pos (sz : Sizes d) (n : ℕ) (u D : ℝ) (a : Fin 2 → Zd d (sz.L n)) :
    0 < STtailTD sz n u D a := by
  unfold STtailTD tailTD
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  exact add_pos_of_nonneg_of_pos (by positivity) (Real.rpow_pos_of_pos hW _)

/-- **Target 1**: the three defining properties of `J♯` (deterministic, every `n, u, ω`):
`1 ≤ J♯`; `STLK2 ≤ J♯ · STtailTD` for every `σ, a`; `J♯ ≤ X` for every `X ≥ 1` dominating all the
ratios. -/
theorem LemDecCalELip_Jsharp_basic {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (D : ℝ) (n : ℕ) (u : ℝ)
    (ω : sz.SeqΩ) :
    1 ≤ LemDecCalELip_Jsharp sz E D n u ω ∧
    (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      STLK2 sz n (E n) u σ a ω ≤ LemDecCalELip_Jsharp sz E D n u ω * STtailTD sz n u D a) ∧
    ∀ X : ℝ, 1 ≤ X →
      (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        STLK2 sz n (E n) u σ a ω ≤ X * STtailTD sz n u D a) →
      LemDecCalELip_Jsharp sz E D n u ω ≤ X := by
  refine ⟨le_max_left _ _, ?_, ?_⟩
  · intro σ a
    have hT := LemDecCalELip_tail_pos sz n u D a
    have h : STLK2 sz n (E n) u σ a ω / STtailTD sz n u D a ≤ LemDecCalELip_Jsharp sz E D n u ω :=
      (Finset.le_sup' (fun p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) =>
        STLK2 sz n (E n) u p.1 p.2 ω / STtailTD sz n u D p.2) (Finset.mem_univ (σ, a))).trans
        (le_max_right _ _)
    exact (div_le_iff₀ hT).1 h
  · intro X hX hall
    refine max_le hX (Finset.sup'_le _ _ fun p _ => ?_)
    exact (div_le_iff₀ (LemDecCalELip_tail_pos sz n u D p.2)).2 (hall p.1 p.2)

/-- The real-number inequality chain of `LemDecCalELip_Jsharp_rel` (the chain of the preflight):
`S' ≤ S + 7N^{11}x`, `S ≤ J T`, `T ≤ ρ² T'`, `1 ≤ N^D T'`, `J ≥ 1`, `ρ ≤ 1 + N x` give
`S' ≤ (1 + N^{15} N^D x) J T'`. -/
private theorem lemDecCalELip_Jrel_alg {N x ρ ND S S' T T' J : ℝ} (hN7 : 7 ≤ N) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) (hρ1 : 1 ≤ ρ) (hρ : ρ ≤ 1 + N * x) (hND : 1 ≤ ND) (hT : T ≤ ρ ^ 2 * T')
    (hT' : 0 < T') (hlow : 1 ≤ ND * T') (hJ : 1 ≤ J) (hS : S ≤ J * T)
    (hS' : S' ≤ S + 7 * N ^ 11 * x) : S' ≤ (1 + N ^ 15 * ND * x) * J * T' := by
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hN2 : N ^ 2 ≤ N ^ 11 := pow_le_pow_right₀ hN1 (by norm_num)
  have hN11 : 0 ≤ N ^ 11 := pow_nonneg hN0 11
  set P : ℝ := N ^ 11 * ND * x with hP
  have hP0 : 0 ≤ P := by positivity
  have hρ2 : ρ ^ 2 ≤ 1 + 3 * N ^ 2 * x := by
    have h1 : ρ ^ 2 ≤ (1 + N * x) ^ 2 := pow_le_pow_left₀ (by linarith) hρ 2
    have h2 : N * x ≤ N ^ 2 * x := by nlinarith
    have h3 : N ^ 2 * x ^ 2 ≤ N ^ 2 * x := by nlinarith [sq_nonneg N]
    nlinarith
  have hρP : ρ ^ 2 ≤ 1 + 3 * P := by
    refine hρ2.trans ?_
    have : N ^ 2 * x ≤ P := by
      rw [hP]
      calc N ^ 2 * x ≤ N ^ 11 * x := mul_le_mul_of_nonneg_right hN2 hx0
        _ ≤ N ^ 11 * ND * x := by
          refine mul_le_mul_of_nonneg_right ?_ hx0
          nlinarith
    nlinarith
  have h2 : 7 * N ^ 11 * x ≤ 7 * P * T' * J := by
    have h1 : N ^ 11 * x ≤ N ^ 11 * x * (ND * T') := by
      have : 0 ≤ N ^ 11 * x := by positivity
      nlinarith
    have h2 : N ^ 11 * x * (ND * T') = P * T' := by rw [hP]; ring
    have h3 : P * T' ≤ P * T' * J := by
      have : 0 ≤ P * T' := by positivity
      nlinarith
    nlinarith
  have h4 : J * T ≤ J * (ρ ^ 2 * T') := mul_le_mul_of_nonneg_left hT hJ0
  have h5 : J * (ρ ^ 2 * T') ≤ J * ((1 + 3 * P) * T') :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hρP hT'.le) hJ0
  have hN4 : (10 : ℝ) ≤ N ^ 4 := by
    have : (7 : ℝ) ^ 4 ≤ N ^ 4 := pow_le_pow_left₀ (by norm_num) hN7 4
    norm_num at this
    linarith
  have h6 : (1 + 10 * P) ≤ 1 + N ^ 15 * ND * x := by
    have : N ^ 15 * ND * x = N ^ 4 * P := by rw [hP]; ring
    rw [this]
    nlinarith
  have h7 : 0 ≤ J * T' := by positivity
  calc S' ≤ S + 7 * N ^ 11 * x := hS'
    _ ≤ J * T + 7 * P * T' * J := add_le_add hS h2
    _ ≤ J * ((1 + 3 * P) * T') + 7 * P * T' * J := add_le_add (h4.trans h5) le_rfl
    _ = (1 + 10 * P) * J * T' := by ring
    _ ≤ (1 + N ^ 15 * ND * x) * J * T' := by
        have : 0 ≤ J * T' := h7
        nlinarith

/-- `W ≤ N` for `d ≥ 1`: `W ≤ W L ≤ (W L)^d`. -/
private theorem lemDecCalELip_W_le_size (sz : Sizes d) (n : ℕ) (hd : 1 ≤ d) :
    ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  have hL : 1 ≤ sz.L n := by have := sz.three_le_L n; omega
  have h1 : sz.W n ≤ sz.W n * sz.L n := Nat.le_mul_of_pos_right _ hL
  have h2 : sz.W n * sz.L n ≤ (sz.W n * sz.L n) ^ d := Nat.le_self_pow (by omega) _
  exact_mod_cast h1.trans h2

/-- **Target 4**: relative continuity of `J♯` in `u` on `contGood` (supervisor 1.3): 2a, (L2) for
`STtailTD`, `STtailTD ≥ W^{-D} ≥ N^{-D}`, `J♯ ≥ 1`, `ρ ≤ 1 + N √|u-u'|`; constant `N^{15+D}`. -/
theorem LemDecCalELip_Jsharp_rel (sz : Sizes d) (E s t : ℕ → ℝ) (κ D : ℝ) (hd : 3 ≤ d)
    (hsize : sz.SizeTendsto) (hκ : 0 < κ) (hD : 0 < D) (hE : ∀ n, |E n| ≤ 2 - κ)
    (hs : ∀ n, 0 ≤ s n) (ht : ∀ n, t n < 1)
    (htN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz n,
      ∀ u u' : TimeIcc s t n,
        LemDecCalELip_Jsharp sz E D n (u' : ℝ) ω ≤
          (1 + ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)|) *
            LemDecCalELip_Jsharp sz E D n (u : ℝ) ω := by
  refine ⟨((15 : ℕ) : ℝ) + D, by positivity, ?_⟩
  filter_upwards [LemDecCalELip_env sz E t κ hκ hE hsize htN 7] with n hn ω hω u u'
  obtain ⟨h7, h1, hE2, hQ, hN1⟩ := hn
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  have hu0 : 0 ≤ (u : ℝ) := (hs n).trans u.2.1
  have hu'0 : 0 ≤ (u' : ℝ) := (hs n).trans u'.2.1
  have hΔ0 : 0 ≤ |(u : ℝ) - u'| := abs_nonneg _
  have hΔ1 : |(u : ℝ) - u'| ≤ 1 := abs_le.2 ⟨by linarith [u.2.2, u'.2.2, ht n], by linarith [u.2.2, u'.2.2, ht n]⟩
  have hx0 : 0 ≤ Real.sqrt |(u : ℝ) - u'| := Real.sqrt_nonneg _
  have hx1 : Real.sqrt |(u : ℝ) - u'| ≤ 1 := by rw [Real.sqrt_le_one]; exact hΔ1
  have hΔx : |(u : ℝ) - u'| ≤ Real.sqrt |(u : ℝ) - u'| := by
    calc |(u : ℝ) - u'| = Real.sqrt |(u : ℝ) - u'| * Real.sqrt |(u : ℝ) - u'| :=
          (Real.mul_self_sqrt hΔ0).symm
      _ ≤ Real.sqrt |(u : ℝ) - u'| * 1 := by gcongr
      _ = Real.sqrt |(u : ℝ) - u'| := mul_one _
  have h1t : 0 < 1 - t n := by linarith [ht n]
  set ρ : ℝ := 1 + (1 - t n)⁻¹ * |(u : ℝ) - u'| with hρdef
  have hρ1 : 1 ≤ ρ := by
    have : 0 ≤ (1 - t n)⁻¹ * |(u : ℝ) - u'| := mul_nonneg (inv_nonneg.2 h1t.le) hΔ0
    linarith
  have hρ : ρ ≤ 1 + N * Real.sqrt |(u : ℝ) - u'| := by
    have : (1 - t n)⁻¹ * |(u : ℝ) - u'| ≤ N * Real.sqrt |(u : ℝ) - u'| :=
      mul_le_mul hN1 hΔx hΔ0 hN0.le
    linarith
  have hND : 1 ≤ N ^ D := Real.one_le_rpow h1 hD.le
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWN : ((sz.W n : ℕ) : ℝ) ≤ N := lemDecCalELip_W_le_size sz n (by omega)
  have hNC : N ^ (((15 : ℕ) : ℝ) + D) = N ^ 15 * N ^ D := by
    rw [Real.rpow_add hN0, Real.rpow_natCast]
  -- the pointwise inequality
  have hall : ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      STLK2 sz n (E n) (u' : ℝ) σ a ω ≤
        ((1 + N ^ (((15 : ℕ) : ℝ) + D) * Real.sqrt |(u : ℝ) - u'|) *
          LemDecCalELip_Jsharp sz E D n (u : ℝ) ω) * STtailTD sz n (u' : ℝ) D a := by
    intro σ a
    have hb := LemDecCalELip_Jsharp_basic sz E D n (u : ℝ) ω
    have hS' := LemDecCalELip_LK2_sub sz n (E n) ω (N := N) hNdef h1 hE2 (ht n) hu0 u.2.2 hu'0
      u'.2.2 hQ (fun c => hω c) hN1 σ a
    have hrel := (LemDecCalELip_relcont sz n (t n) (u' : ℝ) (u : ℝ) D a (ht n) u'.2.2 u.2.2).2.2.2.1
    rw [abs_sub_comm (u' : ℝ) (u : ℝ)] at hrel
    have hT'0 := LemDecCalELip_tail_pos sz n (u' : ℝ) D a
    have hlow : 1 ≤ N ^ D * STtailTD sz n (u' : ℝ) D a := by
      have h2 : ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ STtailTD sz n (u' : ℝ) D a := by
        unfold STtailTD tailTD
        have : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d * |1 - (u' : ℝ)|)⁻¹ ^ 2 *
            Real.exp (-Real.sqrt ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) :=
          mul_nonneg (by positivity) (Real.exp_pos _).le
        linarith
      have h3 : N ^ (-D) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) :=
        Real.rpow_le_rpow_of_nonpos hW0 hWN (by linarith)
      rw [Real.rpow_neg hN0.le] at h3
      have h4 : (N ^ D)⁻¹ ≤ STtailTD sz n (u' : ℝ) D a := h3.trans h2
      have hNDpos : 0 < N ^ D := Real.rpow_pos_of_pos hN0 D
      calc (1 : ℝ) = N ^ D * (N ^ D)⁻¹ := (mul_inv_cancel₀ hNDpos.ne').symm
        _ ≤ N ^ D * STtailTD sz n (u' : ℝ) D a := mul_le_mul_of_nonneg_left h4 hNDpos.le
    have hS'' : STLK2 sz n (E n) (u' : ℝ) σ a ω ≤
        STLK2 sz n (E n) (u : ℝ) σ a ω + 7 * N ^ 11 * Real.sqrt |(u : ℝ) - u'| := by
      have := (abs_le.1 hS').1
      linarith
    rw [hNC]
    have key := lemDecCalELip_Jrel_alg (N := N) (x := Real.sqrt |(u : ℝ) - u'|) (ρ := ρ)
      (ND := N ^ D) h7 hx0 hx1 hρ1 hρ hND hrel hT'0 hlow hb.1 (hb.2.1 σ a) hS''
    exact key
  have hX1 : 1 ≤ (1 + N ^ (((15 : ℕ) : ℝ) + D) * Real.sqrt |(u : ℝ) - u'|) *
      LemDecCalELip_Jsharp sz E D n (u : ℝ) ω := by
    have hb := (LemDecCalELip_Jsharp_basic sz E D n (u : ℝ) ω).1
    have : 1 ≤ 1 + N ^ (((15 : ℕ) : ℝ) + D) * Real.sqrt |(u : ℝ) - u'| := by
      have : 0 ≤ N ^ (((15 : ℕ) : ℝ) + D) * Real.sqrt |(u : ℝ) - u'| :=
        mul_nonneg (Real.rpow_nonneg hN0.le _) hx0
      linarith
    nlinarith
  exact (LemDecCalELip_Jsharp_basic sz E D n (u' : ℝ) ω).2.2 _ hX1 hall

end Jsharp


/-! ## 7. (G): the generic lift `PrecPT → Prec` through `cont_core` -/

section Lift

variable {d : ℕ}

/-- `(1 + δ)^{m+1} ≤ 2` for `0 ≤ δ ≤ N⁻¹`, `N ≥ 2(m+1)` (`1 + δ ≤ e^δ`, `e^y ≤ 1/(1-y) ≤ 2` for
`y = (m+1) δ ≤ 1/2`). -/
private theorem lemDecCalELip_bpow {δ m N : ℝ} (hm : 0 ≤ m) (hδ0 : 0 ≤ δ) (hδ : δ ≤ N⁻¹)
    (hN : 2 * (m + 1) ≤ N) : (1 + δ) ^ (m + 1) ≤ 2 := by
  have hN0 : 0 < N := by linarith
  have h1 : 1 + δ ≤ Real.exp δ := by linarith [Real.add_one_le_exp δ]
  have h2 : (1 + δ) ^ (m + 1) ≤ Real.exp δ ^ (m + 1) :=
    Real.rpow_le_rpow (by linarith) h1 (by linarith)
  rw [← Real.exp_mul] at h2
  have hy0 : 0 ≤ δ * (m + 1) := mul_nonneg hδ0 (by linarith)
  have hy : δ * (m + 1) ≤ 1 / 2 := by
    calc δ * (m + 1) ≤ N⁻¹ * (m + 1) := mul_le_mul_of_nonneg_right hδ (by linarith)
      _ = (m + 1) / N := by rw [inv_mul_eq_div]
      _ ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hN0 (by norm_num)]
        linarith
  have h3 := Real.exp_bound_div_one_sub_of_interval hy0 (by linarith)
  refine h2.trans (h3.trans ?_)
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- The `ζ`-closeness of (G): a common factor `b = 1 + δ` with `b^{m+1} ≤ 2` gives
`R₀' + J'^m R' ≤ 2 (R₀ + J^m R)`. -/
private theorem lemDecCalELip_zeta {J J' R R' R₀ R₀' b m : ℝ} (hm : 0 ≤ m) (hb1 : 1 ≤ b)
    (hb2 : b ^ (m + 1) ≤ 2) (hJ : 1 ≤ J) (hJ'0 : 0 ≤ J') (hJ' : J' ≤ b * J) (hR : 0 ≤ R)
    (hR'0 : 0 ≤ R') (hR' : R' ≤ b * R) (hR₀ : 0 ≤ R₀) (hR₀' : R₀' ≤ b * R₀) :
    R₀' + J' ^ m * R' ≤ 2 * (R₀ + J ^ m * R) := by
  have hb0 : 0 < b := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hbm : 0 ≤ b ^ m := Real.rpow_nonneg hb0.le _
  have hJm : 0 ≤ J ^ m := Real.rpow_nonneg hJ0 _
  have h1 : J' ^ m ≤ b ^ m * J ^ m := by
    calc J' ^ m ≤ (b * J) ^ m := Real.rpow_le_rpow hJ'0 hJ' hm
      _ = b ^ m * J ^ m := Real.mul_rpow hb0.le hJ0
  have hbb : b ^ (m + 1) = b ^ m * b := by rw [Real.rpow_add hb0, Real.rpow_one]
  have h2 : J' ^ m * R' ≤ b ^ (m + 1) * (J ^ m * R) := by
    calc J' ^ m * R' ≤ (b ^ m * J ^ m) * (b * R) :=
          mul_le_mul h1 hR' hR'0 (mul_nonneg hbm hJm)
      _ = b ^ (m + 1) * (J ^ m * R) := by rw [hbb]; ring
  have hb_le : b ≤ b ^ (m + 1) := by
    calc b = b ^ (1 : ℝ) := (Real.rpow_one b).symm
      _ ≤ b ^ (m + 1) := Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
  have h3 : R₀' ≤ b ^ (m + 1) * R₀ :=
    hR₀'.trans (mul_le_mul_of_nonneg_right hb_le hR₀)
  have hz : 0 ≤ R₀ + J ^ m * R := add_nonneg hR₀ (mul_nonneg hJm hR)
  calc R₀' + J' ^ m * R' ≤ b ^ (m + 1) * R₀ + b ^ (m + 1) * (J ^ m * R) := add_le_add h3 h2
    _ = b ^ (m + 1) * (R₀ + J ^ m * R) := by ring
    _ ≤ 2 * (R₀ + J ^ m * R) := mul_le_mul_of_nonneg_right hb2 hz

/-- **Target 5 (G)**: `PrecPT(ξ ≺ R₀ + J^m R)` + Hölder-1/2 of `ξ` and relative continuity of `J`
on `contGood` + relative continuity of the deterministic `R₀, R` + floors (`J ≥ 1`, `R₀ ≥ 0`,
`R ≥ N^{-CR}`) ⇒ `Prec(ξ ≺ R₀ + J^m R)`, by the merged `cont_core` with `P = seqP sz`,
`Ξ = contGood`, `ε = N^{-CR}` and the mesh `A = 2(|C| + |CR|) + 2` (`δ = N^C N^{-A/2} ≤
N^{-|CR|-1}`). -/
theorem LemDecCalELip_lift {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (V : ℕ → Type)
    [∀ n, Fintype (V n)]
    (ξ : ∀ n, TimeIcc s t n × V n → sz.SeqΩ → ℝ) (J : ℕ → ℝ → sz.SeqΩ → ℝ)
    (R₀ R : ∀ n, TimeIcc s t n × V n → ℝ) (m Cv C CR : ℝ) :
    sz.SizeTendsto → (∀ n, s n ≤ t n) → (∀ n, t n - s n ≤ 1) → 0 ≤ m →
    (∀ᶠ n in atTop, (Fintype.card (V n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ Cv) →
    (∀ n u ω, 1 ≤ J n u ω) → (∀ n p, 0 ≤ R₀ n p) →
    (∀ᶠ n in atTop, ∀ p, ((sz.size n : ℕ) : ℝ) ^ (-CR) ≤ R n p) →
    (∀ᶠ n in atTop, ∀ (u u' : TimeIcc s t n) (v : V n),
      R₀ n (u', v) ≤ (1 + ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)|) * R₀ n (u, v) ∧
      R n (u', v) ≤ (1 + ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)|) * R n (u, v)) →
    (∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz n, ∀ u u' : TimeIcc s t n,
      (∀ v : V n, |ξ n (u, v) ω - ξ n (u', v) ω| ≤
        ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)|) ∧
      J n (u' : ℝ) ω ≤ (1 + ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)|) * J n (u : ℝ) ω) →
    PrecPT sz (U := fun n => TimeIcc s t n × V n) ξ
      (fun n p ω => R₀ n p + J n (p.1 : ℝ) ω ^ m * R n p) →
    Prec sz (U := fun n => TimeIcc s t n × V n) ξ
      (fun n p ω => R₀ n p + J n (p.1 : ℝ) ω ^ m * R n p) := by
  intro hsize hst hlen hm hcard hJ hR₀ hRlow hrel hxi hPT
  have hsizeN : Tendsto sz.size atTop atTop := sz.tendsto_size hsize
  have hA : (0 : ℝ) ≤ 2 * (|C| + |CR|) + 2 := by positivity
  refine cont_core (V := V) (P := sz.seqP) (size := sz.size) hsizeN hst hlen
    (A := 2 * (|C| + |CR|) + 2) (Cv := max Cv 0) hA (le_max_right _ _) ?_ hPT
    (cont_highProbAt_good sz hsizeN) (ε := fun n => ((sz.size n : ℕ) : ℝ) ^ (-CR))
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) ?_ ?_
  · -- `hcard`
    filter_upwards [hcard, hsize.eventually_ge_atTop 1] with n h h1
    exact h.trans (Real.rpow_le_rpow_of_exponent_le h1 (le_max_left _ _))
  · -- `hlow`
    filter_upwards [hRlow] with n hn p ω
    have hJm : 1 ≤ J n (p.1 : ℝ) ω ^ m := Real.one_le_rpow (hJ n _ ω) hm
    have hR0 : 0 ≤ R n p := (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans (hn p)
    have : R n p ≤ J n (p.1 : ℝ) ω ^ m * R n p := le_mul_of_one_le_left hR0 hJm
    have := hR₀ n p
    change ((sz.size n : ℕ) : ℝ) ^ (-CR) ≤ R₀ n p + J n (p.1 : ℝ) ω ^ m * R n p
    linarith [hn p]
  · -- `hclose`
    filter_upwards [hrel, hxi, hRlow, hsize.eventually_ge_atTop (max 1 (2 * (m + 1)))] with n hr hx hRl hN
    intro ω hω u u' hΔ v
    set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
    have h1 : 1 ≤ N := (le_max_left _ _).trans hN
    have h2 : 2 * (m + 1) ≤ N := (le_max_right _ _).trans hN
    have hN0 : 0 < N := by linarith
    obtain ⟨hξ, hJ'⟩ := hx ω hω u u'
    obtain ⟨hRa, hRb⟩ := hr u u' v
    have hsq : Real.sqrt |(u : ℝ) - (u' : ℝ)| ≤ N ^ (-(2 * (|C| + |CR|) + 2) / 2) :=
      cont_sqrt_abs_le hN0.le hΔ
    -- `δ = N^C N^{-A/2} ≤ N^{-|CR|-1}`
    set δ : ℝ := N ^ C * N ^ (-(2 * (|C| + |CR|) + 2) / 2) with hδdef
    have hNCx : N ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)| ≤ δ :=
      mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hN0.le _)
    have hδ0 : 0 ≤ δ := by positivity
    have hδe : δ = N ^ (C + -(2 * (|C| + |CR|) + 2) / 2) := by
      rw [hδdef, Real.rpow_add hN0]
    have hδ1 : δ ≤ N ^ (-|CR| - 1) := by
      rw [hδe]
      refine Real.rpow_le_rpow_of_exponent_le h1 ?_
      have := le_abs_self C
      have := abs_nonneg C
      linarith
    have hδε : δ ≤ N ^ (-CR) := by
      refine hδ1.trans (Real.rpow_le_rpow_of_exponent_le h1 ?_)
      have := le_abs_self CR
      linarith
    have hδN : δ ≤ N⁻¹ := by
      refine hδ1.trans ?_
      rw [← Real.rpow_neg_one]
      refine Real.rpow_le_rpow_of_exponent_le h1 ?_
      have := abs_nonneg CR
      linarith
    have hξv := (abs_le.1 ((hξ v).trans (hNCx.trans hδε)))
    refine ⟨?_, ?_⟩
    · show ξ n (u, v) ω ≤ ξ n (u', v) ω + N ^ (-CR)
      have := hξv.1
      have := hξv.2
      linarith
    · have hb2 := lemDecCalELip_bpow hm hδ0 hδN h2
      have hb1 : 1 ≤ 1 + δ := by linarith
      have hJu : 1 ≤ J n (u : ℝ) ω := hJ n _ ω
      have hJu' : 0 ≤ J n (u' : ℝ) ω := by linarith [hJ n (u' : ℝ) ω]
      have hRu : 0 ≤ R n (u, v) := (Real.rpow_nonneg hN0.le _).trans (hRl _)
      have hRu' : 0 ≤ R n (u', v) := (Real.rpow_nonneg hN0.le _).trans (hRl _)
      have hRo := hR₀ n (u, v)
      have mono : ∀ y : ℝ, 0 ≤ y → (1 + N ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)|) * y ≤ (1 + δ) * y :=
        fun y hy => mul_le_mul_of_nonneg_right (by linarith) hy
      exact lemDecCalELip_zeta hm hb1 hb2 hJu hJu' (hJ'.trans (mono _ (by linarith))) hRu hRu'
        (hRb.trans (mono _ hRu)) hRo (hRa.trans (mono _ hRo))

end Lift


/-! ## 8. Compiled nonempty instances at `d = 3`

The size data are the merged preflight sequence `RBM.Gauss.SizesInst.sz0` (`L_n = 4(n+1)`,
`W_n = (2(n+1))^5`, `N_n = (W_n L_n)^3`; `N_0 = 2097152`), `SizeTendsto` by `sz0_tendsto`, `E ≡ 1/2`,
`κ = 1` (`|E| = 1/2 ≤ 1`), `s ≡ 0`, `t ≡ 1/16` (`sInst`, `tInst`).  Every deterministic hypothesis
is discharged; for (L1) and target 4 the premise `(1 - t_n)⁻¹ = 16/15 ≤ N_n` holds for every `n`. -/

section Instances

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst

/-- `(1 - 1/16)⁻¹ = 16/15 ≤ N_n` for every `n` (`N_n ≥ 4`). -/
private theorem lemDecCalELip_inst_tN (n : ℕ) :
    (1 - tInst n)⁻¹ ≤ ((sz0.size n : ℕ) : ℝ) := by
  have h1 : 4 * (n + 1) ≤ (2 * (n + 1)) ^ 5 * (4 * (n + 1)) :=
    Nat.le_mul_of_pos_left _ (by positivity)
  have h2 : (2 * (n + 1)) ^ 5 * (4 * (n + 1)) ≤ ((2 * (n + 1)) ^ 5 * (4 * (n + 1))) ^ 3 :=
    Nat.le_self_pow (by norm_num) _
  have h3 : 4 ≤ sz0.size n := by
    change 4 ≤ ((2 * (n + 1)) ^ 5 * (4 * (n + 1))) ^ 3
    omega
  have h4 : (4 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) := by exact_mod_cast h3
  have h5 : (1 - tInst n)⁻¹ = 16 / 15 := by
    simp only [tInst]; norm_num
  rw [h5]
  linarith

/-- **(a)** 2a at `sz0`, `E ≡ 1/2`, `κ = 1`, `s ≡ 0`, `t ≡ 1/16`: every premise discharged. -/
example : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz0 n,
    ∀ (u u' : TimeIcc sInst tInst n) (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L n)),
      |STLK2 sz0 n (1 / 2) (u : ℝ) σ a ω - STLK2 sz0 n (1 / 2) (u' : ℝ) σ a ω| ≤
        ((sz0.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)| :=
  LemDecCalELip_LK2 sz0 (fun _ => 1 / 2) sInst tInst 1 (by norm_num) sz0_tendsto one_pos
    (fun _ => by norm_num) (fun _ => le_rfl) (fun _ => by norm_num [tInst])
    (Eventually.of_forall lemDecCalELip_inst_tN)

/-- **(a)** 2b at the same data. -/
example : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz0 n,
    ∀ (u u' : TimeIcc sInst tInst n) (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L n)),
      ‖STELKLK sz0 n (1 / 2) (u : ℝ) σ a ω - STELKLK sz0 n (1 / 2) (u' : ℝ) σ a ω‖ ≤
        ((sz0.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)| :=
  LemDecCalELip_ELKLK sz0 (fun _ => 1 / 2) sInst tInst 1 (by norm_num) sz0_tendsto one_pos
    (fun _ => by norm_num) (fun _ => le_rfl) (fun _ => by norm_num [tInst])
    (Eventually.of_forall lemDecCalELip_inst_tN)

/-- **(a)** 2c at the same data. -/
example : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz0 n,
    ∀ (u u' : TimeIcc sInst tInst n) (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L n)),
      ‖STEGt sz0 n (1 / 2) (u : ℝ) σ a ω - STEGt sz0 n (1 / 2) (u' : ℝ) σ a ω‖ ≤
        ((sz0.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)| :=
  LemDecCalELip_EGt sz0 (fun _ => 1 / 2) sInst tInst 1 (by norm_num) sz0_tendsto one_pos
    (fun _ => by norm_num) (fun _ => le_rfl) (fun _ => by norm_num [tInst])
    (Eventually.of_forall lemDecCalELip_inst_tN)

/-- **(a)** 2d at the same data (`m = 2`, every `a'`). -/
example : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz0 n,
    ∀ (u u' : TimeIcc sInst tInst n) (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd 3 (sz0.L n)),
      ‖STee sz0 n (1 / 2) (u : ℝ) ω σ a a' - STee sz0 n (1 / 2) (u' : ℝ) ω σ a a'‖ ≤
        ((sz0.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)| :=
  LemDecCalELip_ee sz0 (fun _ => 1 / 2) sInst tInst 1 (by norm_num) sz0_tendsto one_pos
    (fun _ => by norm_num) (fun _ => le_rfl) (fun _ => by norm_num [tInst])
    (Eventually.of_forall lemDecCalELip_inst_tN)

/-- **(b)** target 3 at `sz0`, `n = 1`, `t = 1/16`, `u = 0`, `u' = 1/16`, `D = 42`, `a ≡ 0`: all five
inequalities with `ρ = 1 + (15/16)⁻¹ · 1/16 = 16/15 > 1`. -/
example := LemDecCalELip_relcont sz0 1 (1 / 16) 0 (1 / 16) 42 (fun _ => 0) (by norm_num)
  (by norm_num) le_rfl

/-- **(c)** target 1 at `sz0` (`n = 1`, `u = 0`, `D = 42`, the zero sample): `1 ≤ J♯` and the two
other properties. -/
example := LemDecCalELip_Jsharp_basic sz0 (fun _ => 1 / 2) 42 1 0 (fun _ => 0)

/-- Target 4 at the same data as (a), `D = 42`. -/
example : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz0 n,
    ∀ u u' : TimeIcc sInst tInst n,
      LemDecCalELip_Jsharp sz0 (fun _ => 1 / 2) 42 n (u' : ℝ) ω ≤
        (1 + ((sz0.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)|) *
          LemDecCalELip_Jsharp sz0 (fun _ => 1 / 2) 42 n (u : ℝ) ω :=
  LemDecCalELip_Jsharp_rel sz0 (fun _ => 1 / 2) sInst tInst 1 42 (by norm_num) sz0_tendsto one_pos
    (by norm_num) (fun _ => by norm_num) (fun _ => le_rfl) (fun _ => by norm_num [tInst])
    (Eventually.of_forall lemDecCalELip_inst_tN)

/-- **(d)** target 5 at `sz0`, `V = fun _ => Unit`, `ξ ≡ 0`, `J ≡ 1`, `R₀ ≡ 0`, `R ≡ 1`, `m = 2`,
`Cv = C = CR = 0`, `s ≡ 0`, `t ≡ 1/16`: every premise discharged (`PrecPT` by `precPT_of_le`). -/
example : Prec sz0 (U := fun n => TimeIcc sInst tInst n × Unit)
    (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => 0 + (1 : ℝ) ^ (2 : ℝ) * 1) :=
  LemDecCalELip_lift sz0 sInst tInst (fun _ => Unit) (fun _ _ _ => (0 : ℝ))
    (fun _ _ _ => (1 : ℝ)) (fun _ _ => (0 : ℝ)) (fun _ _ => (1 : ℝ)) 2 0 0 0 sz0_tendsto
    (fun _ => by norm_num [sInst, tInst]) (fun _ => by norm_num [sInst, tInst]) (by norm_num)
    (Eventually.of_forall fun n => by simp)
    (fun _ _ _ => le_rfl) (fun _ _ => le_rfl)
    (Eventually.of_forall fun n p => by simp)
    (Eventually.of_forall fun n u u' v => ⟨by simp, by simp⟩)
    (Eventually.of_forall fun n ω _ u u' => ⟨fun v => by simp, by simp⟩)
    (precPT_of_le sz0 (fun n p ω => by norm_num) (fun n p ω => by norm_num))

end Instances

end RBM.Gauss.Sizes
