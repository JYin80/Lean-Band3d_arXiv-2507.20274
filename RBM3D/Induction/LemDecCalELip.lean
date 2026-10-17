/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step5Pins
import RBM3D.Path.NetLift2
import RBM3D.Propagator.Deriv
import RBM3D.Propagator.Props4
import RBM3D.Chain.Step5Gen
import RBM3D.Chain.Step34Gen
import RBM3D.Chain.StepDecompGen
import RBM3D.Chain.NQGood1Gen
import RBM3D.Chain.Step2EventsGen

/-!
# Hölder-1/2 continuity in `u`, relative continuity and the realized bound `J♯`

The deterministic and generic part of the proof of `STLemDecCalEConcl` (Lemma 5.2 `lem_dec_calE`,
`STLemDecCalEConcl` in `Induction/Step5Pins.lean`).  The loop-level estimates follow the helper lemmas of
`Path/NetLift2.lean`, and the lift uses `ContinuityNet.cont_core`.

* Loops in the `L²` operator norm: the modulus of a loop of any length along the flow
  (`LemDecCalELip_STLI_sub`, `LemDecCalELip_Lloop_sub`), and over a flow carrier `Cm : Step2Mat sz`
  (`LemDecCalELipG_FlowMod`: a Hermitian model matrix `Hm`, entrywise Hölder-1/2 with `N^c` on a
  high-probability event; `LemDecCalELip_loopL_subg`, `_Lloop_subg`, `_Lloop_normg`).
* The two-loop `𝒦^{(2)}` in the `ℓ^∞ → ℓ^∞` operator norm: size and Hölder-1/2 modulus
  (`LemDecCalELip_STKloop_two_norm`, `_lip`, `_sub`).
* The functionals `STLK2`, `STELKLK`, `STEGt`, `STee` are Hölder-1/2 in `u ∈ [s_n, t_n]` on the good event
  `contGood`, with constant `N^C`, over a carrier (`LemDecCalELip_LK_subg`, `_EGt_subg`) and for the
  band model (`LemDecCalELip_LK_sub`, `_LK2_sub`, `LemDecCalELip_LK2`); the eventual numerical facts
  `LemDecCalELip_env`, `_envg`, `lemDecCalELipG_loops`, `lemDecCalELipG_Kn`.
* `LemDecCalELip_relcont`: relative continuity of `(1-u)⁻¹`, `(W^d|1-u|)⁻¹`, its `1/2` power,
  `STtailTD`, `STtailTD²`.
* `LemDecCalELip_Jsharp`, `_Jsharp_basic`, `_Jsharp_rel`: the realized bound
  `J♯ = max (1, max_{σ,a} STLK2 / STtailTD)`, its defining properties and its relative continuity.
* `LemDecCalELip_lift`: `PrecPT(ξ ≺ R₀ + J^m R)` + Lipschitz + floors gives `Prec`.
-/

noncomputable section

namespace RBM.Gauss.Sizes

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Loop RBM.Path RBM.Gauss
  RBM.Ind.ContinuityNet RBM.BA
open scoped NNReal ENNReal

set_option linter.style.longLine false

/-! ## 1. Loops in the `L²` operator norm: the modulus and the size of a loop of any length -/

section Flow

open scoped Matrix.Norms.L2Operator

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The resolvent word `∏ᵢ G(σᵢ) E_{aᵢ}` over a list (the `foldr` of `loopL`). -/
private def lemDecCalELip_word (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (l : List (Bool × Zd d L)) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1

omit [NeZero W] in
/-- The word of a cons. -/
private theorem lemDecCalELip_word_cons (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (p : Bool × Zd d L) (l : List (Bool × Zd d L)) :
    lemDecCalELip_word H z (p :: l) = Gres H z p.1 * Eblk d L W p.2 * lemDecCalELip_word H z l :=
  rfl

/-- The word is bounded by `Q^length`. -/
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

/-- The `k`-fold telescoping of a resolvent word. -/
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

/-- The modulus of a loop of any length along the flow, on `‖X‖ ≤ Xb`, stated for the trace of the word
of an arbitrary list (the list loops `STLI`, `STeeLoop`) instead of `Fin k`-indexed `loopFine`. -/
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

/-- **The modulus of a loop of any length** (`STLI`, every list loop) on `contGood`:
`‖𝓛_I(u) - 𝓛_I(u')‖ ≤ 3 k N^{2k+7} √|u-u'|`, `k = |I|`, with `Q = N²`, `Xb = 2N²`. -/
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

section CarrierG

open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

/-- **The flow modulus**: a model matrix `Hm` reading the loops and `G - M` of the carrier, Hermitian and
entrywise Hölder-1/2 in the time with `N^c` on a high-probability event.  Band: `Hm = seqHflow sz`,
`G = contGood sz`, `c = 1` (`lemDecCalELipG_flowMod_band`). -/
def LemDecCalELipG_FlowMod {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) (c : ℝ) : Prop :=
  ∃ (Hm : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (G : ℕ → Set sz.SeqΩ),
    (∀ (n : ℕ) (u : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) ω, Cm.LM n u (Hm n u ω) σ a = Cm.L n u σ a ω) ∧
    (∀ (n : ℕ) (u : ℝ) ω x y, Cm.GMM n u (Hm n u ω) x y = Cm.GM n u ω x y) ∧
    HighProbAt μ sz.size G ∧
    ∀ n, ∀ ω ∈ G n, ∀ u u' : ℝ, 0 ≤ u → u ≤ 1 → 0 ≤ u' → u' ≤ 1 → (Hm n u ω).IsHermitian ∧
      ∀ x y, ‖Hm n u ω x y - Hm n u' ω x y‖ ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ c * Real.sqrt |u - u'|

/-- The first, third and fourth conjuncts of the flow modulus (the clause on `GMM` is dropped). -/
theorem lemDecCalELipG_flowMod_base {sz : Sizes d} {Cm : Step2Mat sz} {μ : Measure sz.SeqΩ} {c : ℝ}
    (h : LemDecCalELipG_FlowMod Cm μ c) :
    ∃ (Hm : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (G : ℕ → Set sz.SeqΩ),
      (∀ (n : ℕ) (u : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) ω, Cm.LM n u (Hm n u ω) σ a = Cm.L n u σ a ω) ∧
      HighProbAt μ sz.size G ∧
      ∀ n, ∀ ω ∈ G n, ∀ u u' : ℝ, 0 ≤ u → u ≤ 1 → 0 ≤ u' → u' ≤ 1 → (Hm n u ω).IsHermitian ∧
        ∀ x y, ‖Hm n u ω x y - Hm n u' ω x y‖ ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ c * Real.sqrt |u - u'| := by
  obtain ⟨Hm, G, h1, -, h3, h4⟩ := h
  exact ⟨Hm, G, h1, h3, h4⟩

/-- The last conjunct of the flow modulus for a flow matrix `Hf` on an event `G`. -/
def LemDecCalELipG_Mod {sz : Sizes d} (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (G : ℕ → Set sz.SeqΩ) (c : ℝ) : Prop :=
  ∀ n, ∀ ω ∈ G n, ∀ u u' : ℝ, 0 ≤ u → u ≤ 1 → 0 ≤ u' → u' ≤ 1 → (Hf n u ω).IsHermitian ∧
    ∀ x y, ‖Hf n u ω x y - Hf n u' ω x y‖ ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ c * Real.sqrt |u - u'|

/-- The entries of `H_u - H_{u'}` on the good event: `≤ 2 N √|u-u'|` (`cont_norm_Xentry_le`). -/
theorem lemDecCalELipG_seqHflow_entry_sub (sz : Sizes d) (n : ℕ) {ω : sz.SeqΩ}
    (hω : ∀ c : CoordF d (sz.L n) (sz.W n), |sz.slice n ω c| ≤ ((sz.size n : ℕ) : ℝ)) {u u' : ℝ} (hu0 : 0 ≤ u) (hu'0 : 0 ≤ u')
    (x y : Idx d (sz.L n) (sz.W n)) :
    ‖sz.seqHflow n u ω x y - sz.seqHflow n u' ω x y‖ ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * Real.sqrt |u - u'| := by
  have h1 := Hflow_sub_apply d (sz.L n) (sz.W n) u u' (sz.slice n ω) x y
  have h2 := cont_norm_Xentry_le (sz.slice n ω) (B := ((sz.size n : ℕ) : ℝ)) hω x y
  change ‖(Hflow d (sz.L n) (sz.W n) u (sz.slice n ω) - Hflow d (sz.L n) (sz.W n) u' (sz.slice n ω)) x y‖ ≤ _
  rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.rpow_one]
  calc _ ≤ Real.sqrt |u - u'| * (2 * ((sz.size n : ℕ) : ℝ)) :=
        mul_le_mul (cont_abs_sqrt_sub_sqrt_le hu0 hu'0) h2 (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- **The flow modulus at the band** (`c = 1`, `M = N`): `Hm = seqHflow sz` is Hermitian and moves by
`2 N √|u-u'|` entrywise on `contGood sz`. -/
theorem lemDecCalELipG_mod_band (sz : Sizes d) : LemDecCalELipG_Mod (fun n u => sz.seqHflow n u) (contGood sz) 1 :=
  fun n ω hω u _ hu0 _ hu'0 _ => ⟨Sizes.seqHflow_isHermitian sz n u ω, fun x y =>
    lemDecCalELipG_seqHflow_entry_sub sz n hω hu0 hu'0 x y⟩

/-- **The flow modulus at the band**: `Hm = seqHflow sz`, `G = contGood sz`, `c = 1`
(`cont_highProbAt_good`), at every energy sequence. -/
theorem lemDecCalELipG_flowMod_band (sz : Sizes d) (hs : Tendsto sz.size atTop atTop) (E : ℕ → ℝ) :
    LemDecCalELipG_FlowMod (bandStep2Mat sz E) sz.seqP 1 :=
  ⟨fun n u => sz.seqHflow n u, contGood sz, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, cont_highProbAt_good sz hs,
    lemDecCalELipG_mod_band sz⟩

end CarrierG

section LoopsG

open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

/-- **The modulus of a list loop over a carrier** (the band case is `LemDecCalELip_STLI_sub`): for Hermitian
`Hm` with entrywise modulus `2 N^c √|u-u'|`, `‖𝓛_I(u) - 𝓛_I(u')‖ ≤ 3 k N^{2k+6} N^c √|u-u'|`, `k = |I|`
(`cont_green_flow_diff` at `X = (H_u - H_{u'})/√|u-u'|`). -/
theorem LemDecCalELip_loopL_subg {sz : Sizes d} {Cm : Step2Mat sz} {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E)
    {Hm : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hm : ‖Cm.m n‖ ≤ 1) {t u u' N : ℝ} (ω : sz.SeqΩ) (hN : N = ((sz.size n : ℕ) : ℝ)) (hN1 : 1 ≤ N)
    (ht : t < 1) (hu0 : 0 ≤ u) (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t) (hQ : (Cm.eta n t)⁻¹ ≤ N ^ 2)
    (hherm : ∀ v : ℝ, 0 ≤ v → v ≤ t → (Hm n v ω).IsHermitian)
    (hmod : ∀ x y, ‖Hm n u ω x y - Hm n u' ω x y‖ ≤ 2 * N ^ c * Real.sqrt |u - u'|) (I : LoopIdx (Zd d (sz.L n))) :
    ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (Hm n u ω)) (ztOf (Cm.m n) (E n) u) I -
        loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (Hm n u' ω)) (ztOf (Cm.m n) (E n) u') I‖ ≤
      3 * ((I.σ.zip I.a).length : ℝ) * N ^ (2 * (I.σ.zip I.a).length + 6) * N ^ c * Real.sqrt |u - u'| := by
  have hη := NQGood1Gen_eta_pos hL n ht
  have hN0 : 0 ≤ N := by linarith
  have hNc : 1 ≤ N ^ c := Real.one_le_rpow hN1 hc
  have hQ1 : 1 ≤ N ^ 2 := one_le_pow₀ hN1
  have hΔ1 : |u - u'| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hzv : ∀ v, v ≤ t → Cm.eta n t ≤ |(ztOf (Cm.m n) (E n) v).im| := fun v hv => by
    rw [NQGood1Gen_abs_zt_im hL n (lt_of_le_of_lt hv ht)]; exact NQGood1Gen_eta_anti hL n hv
  have hHu := (hherm u hu0 hut).submatrix (splitEquiv d (sz.L n) (sz.W n)).symm
  have hHu' := (hherm u' hu'0 hu't).submatrix (splitEquiv d (sz.L n) (sz.W n)).symm
  have hG : ∀ v, 0 ≤ v → v ≤ t → ∀ σ, ‖Gres (blockMat d (sz.L n) (sz.W n) (Hm n v ω)) (ztOf (Cm.m n) (E n) v) σ‖ ≤ N ^ 2 :=
    fun v hv0 hv σ => (norm_Gsig_le_inv_eta ((hherm v hv0 hv).submatrix _) hη (hzv v hv) σ).trans hQ
  have hzz : ‖ztOf (Cm.m n) (E n) u - ztOf (Cm.m n) (E n) u'‖ ≤ |u - u'| := NQGood1Gen_norm_zt_sub (E := E) hm u' u
  change ‖Matrix.trace (lemDecCalELip_word (blockMat d (sz.L n) (sz.W n) (Hm n u ω)) (ztOf (Cm.m n) (E n) u) (I.σ.zip I.a)) -
    Matrix.trace (lemDecCalELip_word (blockMat d (sz.L n) (sz.W n) (Hm n u' ω)) (ztOf (Cm.m n) (E n) u') (I.σ.zip I.a))‖ ≤ _
  rcases eq_or_ne u u' with rfl | hne
  · simp only [sub_self, norm_zero]; positivity
  set s := Real.sqrt |u - u'| with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (abs_pos.2 (sub_ne_zero.2 hne))
  set X : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ :=
    ((s⁻¹ : ℝ) : ℂ) • (blockMat d (sz.L n) (sz.W n) (Hm n u ω) - blockMat d (sz.L n) (sz.W n) (Hm n u' ω)) with hX
  have hd : blockMat d (sz.L n) (sz.W n) (Hm n u ω) - blockMat d (sz.L n) (sz.W n) (Hm n u' ω) = (s : ℂ) • X := by
    rw [hX, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hs0.ne', Complex.ofReal_one, one_smul]
  have hent : ∀ p q, ‖X p q‖ ≤ 2 * N ^ c := fun p q => by
    rw [hX, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs0)]
    calc s⁻¹ * ‖Hm n u ω ((splitEquiv d (sz.L n) (sz.W n)).symm p) ((splitEquiv d (sz.L n) (sz.W n)).symm q) -
          Hm n u' ω ((splitEquiv d (sz.L n) (sz.W n)).symm p) ((splitEquiv d (sz.L n) (sz.W n)).symm q)‖ ≤ s⁻¹ * (2 * N ^ c * s) :=
        mul_le_mul_of_nonneg_left (hmod _ _) (inv_nonneg.2 hs0.le)
      _ = 2 * N ^ c := by field_simp
  have hXb : ‖X‖ ≤ N * (2 * N ^ c) := by
    have := cont_norm_le_card_mul X (B := 2 * N ^ c) (by positivity) hent
    rwa [lemDecCalELip_card_Vtx sz n hN] at this
  have hgt := cont_green_flow_diff hHu hHu' hd hXb (c := s) (by rw [abs_of_pos hs0]) (abs_nonneg _) hΔ1 hη hQ (hzv u hut) (hzv u' hu't) hzz
  have hgf := cont_green_flow_diff hHu hHu' hd hXb (c := s) (by rw [abs_of_pos hs0]) (abs_nonneg _) hΔ1 hη hQ
    (z := (starRingEnd ℂ) (ztOf (Cm.m n) (E n) u)) (z' := (starRingEnd ℂ) (ztOf (Cm.m n) (E n) u'))
    (by rw [Complex.conj_im, abs_neg]; exact hzv u hut) (by rw [Complex.conj_im, abs_neg]; exact hzv u' hu't)
    (by rw [← map_sub, Complex.norm_conj]; exact hzz)
  have hS : ∀ τ : Bool, ‖Gres (blockMat d (sz.L n) (sz.W n) (Hm n u ω)) (ztOf (Cm.m n) (E n) u) τ -
      Gres (blockMat d (sz.L n) (sz.W n) (Hm n u' ω)) (ztOf (Cm.m n) (E n) u') τ‖ ≤ N ^ 2 * N ^ 2 * (N * (2 * N ^ c) + 1) * s := by
    intro τ; cases τ
    · rw [cont_Gres_false_eq_green, cont_Gres_false_eq_green]; exact hgf
    · rw [cont_Gres_true_eq_green, cont_Gres_true_eq_green]; exact hgt
  have hw := lemDecCalELip_word_diff (sz.W_pos n) hQ1 (hG u hu0 hut) (hG u' hu'0 hu't) hS (I.σ.zip I.a)
  rw [← Matrix.trace_sub]
  refine (norm_matrix_trace_le_card_mul _).trans ?_
  rw [lemDecCalELip_card_Vtx sz n hN]
  refine (mul_le_mul_of_nonneg_left hw hN0).trans ?_
  have e1 : N ^ 2 * N ^ 2 * (N * (2 * N ^ c) + 1) ≤ 3 * N ^ 5 * N ^ c := by
    have : 1 ≤ N * N ^ c := one_le_mul_of_one_le_of_one_le hN1 hNc
    nlinarith [pow_pos (by linarith : (0 : ℝ) < N) 4]
  calc N * (((I.σ.zip I.a).length : ℝ) * (N ^ 2) ^ (I.σ.zip I.a).length * (N ^ 2 * N ^ 2 * (N * (2 * N ^ c) + 1) * s))
      ≤ N * (((I.σ.zip I.a).length : ℝ) * (N ^ 2) ^ (I.σ.zip I.a).length * (3 * N ^ 5 * N ^ c * s)) := by gcongr
    _ = 3 * ((I.σ.zip I.a).length : ℝ) * N ^ (2 * (I.σ.zip I.a).length + 6) * N ^ c * s := by rw [pow_add, pow_mul]; ring


/-- **The modulus of `𝓛^{(k)}` over a carrier** (the band case is `LemDecCalELip_Lloop_sub`):
`3 k N^{2k+6} N^c √|u-u'|`, the exponent `2k+7` at `c = 1`. -/
theorem LemDecCalELip_Lloop_subg {sz : Sizes d} {Cm : Step2Mat sz} {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E)
    {Hm : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hLM : ∀ (n : ℕ) (u : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) ω, Cm.LM n u (Hm n u ω) σ a = Cm.L n u σ a ω)
    {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hm : ‖Cm.m n‖ ≤ 1) {t u u' N : ℝ} (ω : sz.SeqΩ) (hN : N = ((sz.size n : ℕ) : ℝ)) (hN1 : 1 ≤ N)
    (ht : t < 1) (hu0 : 0 ≤ u) (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t) (hQ : (Cm.eta n t)⁻¹ ≤ N ^ 2)
    (hherm : ∀ v : ℝ, 0 ≤ v → v ≤ t → (Hm n v ω).IsHermitian)
    (hmod : ∀ x y, ‖Hm n u ω x y - Hm n u' ω x y‖ ≤ 2 * N ^ c * Real.sqrt |u - u'|)
    {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    ‖Cm.L n u σ a ω - Cm.L n u' σ a ω‖ ≤ 3 * (k : ℝ) * N ^ (2 * k + 6) * N ^ c * Real.sqrt |u - u'| := by
  have h := LemDecCalELip_loopL_subg hL hc hm ω hN hN1 ht hu0 hut hu'0 hu't hQ hherm hmod (loopOf σ a)
  rw [lemDecCalELip_len_loopOf] at h
  have hloop : ∀ v, Cm.L n v σ a ω = loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (Hm n v ω))
      (ztOf (Cm.m n) (E n) v) (loopOf σ a) := fun v => by
    rw [← hLM, (hL n).2.1 v (Hm n v ω) k σ a]
    exact loopM_eq_loopL d (sz.L n) (sz.W n) _ _ σ a
  rw [hloop u, hloop u']
  exact h

/-- **The size of `𝓛^{(k)}` over a carrier**, `k ≥ 1`: `‖𝓛^{(k)}_u‖ ≤ (η_u)⁻ᵏ ≤ N^{2k} ≤ N^{2k+1}`
(`norm_loopFine_crudeNg`). -/
theorem LemDecCalELip_Lloop_normg {sz : Sizes d} {Cm : Step2Mat sz} {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E)
    {Hm : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hLM : ∀ (n : ℕ) (u : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) ω, Cm.LM n u (Hm n u ω) σ a = Cm.L n u σ a ω)
    {n : ℕ} {t u N : ℝ} (ω : sz.SeqΩ) (hN1 : 1 ≤ N) (ht : t < 1) (hut : u ≤ t) (hQ : (Cm.eta n t)⁻¹ ≤ N ^ 2)
    (hherm : (Hm n u ω).IsHermitian) {k : ℕ} (hk : 1 ≤ k) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    ‖Cm.L n u σ a ω‖ ≤ N ^ (2 * k + 1) := by
  rw [← hLM]
  refine (norm_loopFine_crudeNg hL hherm (hut.trans_lt ht) hk σ a).trans ?_
  have hη := NQGood1Gen_eta_pos hL n ht
  calc (Cm.eta n u)⁻¹ ^ k ≤ (N ^ 2) ^ k :=
        pow_le_pow_left₀ (inv_nonneg.2 (lt_of_lt_of_le hη (NQGood1Gen_eta_anti hL n hut)).le)
          ((inv_anti₀ hη (NQGood1Gen_eta_anti hL n hut)).trans hQ) k
    _ = N ^ (2 * k) := (pow_mul N 2 k).symm
    _ ≤ N ^ (2 * k + 1) := pow_le_pow_right₀ hN1 (Nat.le_succ _)

end LoopsG


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

/-- `𝒦^{(2)}_{u,σ,a} = W^{-d} μ Θ_{uμ}(a₀, a₁)`, `μ = m(σ₀) m(σ₁)` (`KLK_two`). -/
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

open scoped Matrix.Norms.Operator in
/-- **The Lipschitz modulus of `𝒦^{(2)}`**: `‖𝒦^{(2)}_{u} - 𝒦^{(2)}_{u'}‖ ≤ N² |u-u'|`
(`Θ_ζ - Θ_ξ = (ζ-ξ) Θ_ζ S Θ_ξ`, `Theta_sub_Theta`; `‖S‖ = 1`, `norm_SB`; `‖Θ‖ ≤ (1-t)⁻¹ ≤ N`), for
`0 ≤ u, u' ≤ t < 1`, `|E| ≤ 2`, `(1-t)⁻¹ ≤ N`. -/
theorem LemDecCalELip_STKloop_two_lip (n : ℕ) {E t u u' N : ℝ} (hE : |E| ≤ 2) (ht : t < 1)
    (hu0 : 0 ≤ u) (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t) (htN : (1 - t)⁻¹ ≤ N)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ‖STKloop sz n E u σ a - STKloop sz n E u' σ a‖ ≤ N ^ 2 * |u - u'| := by
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
    _ = N ^ 2 * |u - u'| := by ring

/-- **The modulus of `𝒦^{(2)}`**: `‖𝒦^{(2)}_{u} - 𝒦^{(2)}_{u'}‖ ≤ N² √|u-u'|` (`LemDecCalELip_STKloop_two_lip` and
`|u-u'| ≤ √|u-u'|`), for `0 ≤ u, u' ≤ t < 1`, `|E| ≤ 2`, `(1-t)⁻¹ ≤ N`. -/
theorem LemDecCalELip_STKloop_two_sub (n : ℕ) {E t u u' N : ℝ} (hE : |E| ≤ 2) (ht : t < 1)
    (hu0 : 0 ≤ u) (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t) (htN : (1 - t)⁻¹ ≤ N)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ‖STKloop sz n E u σ a - STKloop sz n E u' σ a‖ ≤ N ^ 2 * Real.sqrt |u - u'| := by
  have hN0 : 0 ≤ N := le_trans (inv_nonneg.2 (by linarith)) htN
  refine (LemDecCalELip_STKloop_two_lip sz n hE ht hu0 hut hu'0 hu't htN σ a).trans
    (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have h1 : |u - u'| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  calc |u - u'| = Real.sqrt |u - u'| * Real.sqrt |u - u'| := (Real.mul_self_sqrt (abs_nonneg _)).symm
    _ ≤ Real.sqrt |u - u'| * 1 := mul_le_mul_of_nonneg_left (Real.sqrt_le_one.2 h1) (Real.sqrt_nonneg _)
    _ = _ := mul_one _

end Kloop


/-! ## 3. The four functionals: deterministic Hölder-1/2 bounds on the good event -/

section Functionals

variable {d : ℕ} (sz : Sizes d)

/-- `W^d · #Z_L^d = N`. -/
private theorem lemDecCalELip_Wd_card (n : ℕ) {N : ℝ} (hN : N = ((sz.size n : ℕ) : ℝ)) :
    ((sz.W n : ℕ) : ℝ) ^ d * (Fintype.card (Zd d (sz.L n)) : ℝ) = N := by
  rw [card_Zd, hN]
  simp [Sizes.size, mul_pow]

/-- The bilinear sum `Σ_{x,y} A_x S_{xy} B_y` is Lipschitz for a kernel `S` with row sums `≤ 1`: the product rule (the band kernel is
`SB d L g` with `Σ_y |S_{xy}| = 1`, `sum_norm_SB_row`; the carrier kernel is `C.S n`, premise `∀ a, Σ_b ‖S a b‖ ≤ 1`). -/
private theorem lemDecCalELip_bilin {L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℂ) (hS : ∀ x, ∑ y, ‖S x y‖ ≤ 1)
    (A A' B B' : Zd d L → ℂ) {δA δB αA βB : ℝ} (hδA : 0 ≤ δA) (hδB : 0 ≤ δB) (hαA : 0 ≤ αA)
    (hβB : 0 ≤ βB) (hA : ∀ x, ‖A x - A' x‖ ≤ δA) (hB : ∀ y, ‖B y‖ ≤ βB)
    (hA' : ∀ x, ‖A' x‖ ≤ αA) (hBd : ∀ y, ‖B y - B' y‖ ≤ δB) :
    ‖∑ x, ∑ y, A x * S x y * B y - ∑ x, ∑ y, A' x * S x y * B' y‖ ≤
      (Fintype.card (Zd d L) : ℝ) * (δA * βB + αA * δB) := by
  have hK0 : 0 ≤ δA * βB + αA * δB := by positivity
  have hterm : ∀ x y, ‖A x * S x y * B y - A' x * S x y * B' y‖ ≤
      ‖S x y‖ * (δA * βB + αA * δB) := by
    intro x y
    have e : A x * S x y * B y - A' x * S x y * B' y =
        (A x - A' x) * S x y * B y + A' x * S x y * (B y - B' y) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(A x - A' x) * S x y * B y‖ ≤ δA * ‖S x y‖ * βB := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul (hA x) le_rfl (norm_nonneg _) hδA) (hB y) (norm_nonneg _)
        (by positivity)
    have h2 : ‖A' x * S x y * (B y - B' y)‖ ≤ αA * ‖S x y‖ * δB := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul (hA' x) le_rfl (norm_nonneg _) hαA) (hBd y) (norm_nonneg _)
        (by positivity)
    nlinarith [h1, h2]
  simp only [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hrow : ∀ x, ∑ y, ‖A x * S x y * B y - A' x * S x y * B' y‖ ≤ δA * βB + αA * δB := by
    intro x
    calc ∑ y, ‖A x * S x y * B y - A' x * S x y * B' y‖
        ≤ ∑ y, ‖S x y‖ * (δA * βB + αA * δB) := Finset.sum_le_sum fun y _ => hterm x y
      _ = (∑ y, ‖S x y‖) * (δA * βB + αA * δB) := by rw [Finset.sum_mul]
      _ ≤ 1 * (δA * βB + αA * δB) := mul_le_mul_of_nonneg_right (hS x) hK0
      _ = δA * βB + αA * δB := one_mul _
  calc ∑ x, ‖∑ y, (A x * S x y * B y - A' x * S x y * B' y)‖
      ≤ ∑ x, (δA * βB + αA * δB) := Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans (hrow x)
    _ = (Fintype.card (Zd d L) : ℝ) * (δA * βB + αA * δB) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Functionals

/-! ### 3g. The functionals over a carrier `C : FlowFM sz`

The deterministic Hölder-1/2 bounds read the carrier through four inputs: the size `N^{2k+1}` and the modulus
`3 k N^{2k+6} M √|u-u'|` of the loops `C.L`, the size `N` and the modulus `N^6 √|u-u'|` of `C.K` at `k = 2`, the
row sums `Σ_b ‖C.S a b‖ ≤ 1` and `‖C.m‖ ≤ 1`; `M = N` at the band (the flow modulus with `c = 1`) and `M = N^c`
in general. -/

section FunctionalsG

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) {t u u' N M : ℝ} (ω : sz.SeqΩ)

/-- `(𝓛 - 𝒦)^{(2)}` is Hölder-1/2 over a carrier: `7 N^{10} M √|u-u'|` (band case `LemDecCalELip_LK_sub`,
`M = N`). -/
theorem LemDecCalELip_LK_subg (hN1 : 1 ≤ N) (hM1 : 1 ≤ M)
    (hLs : ∀ {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖C.L n u σ a ω - C.L n u' σ a ω‖ ≤ 3 * (k : ℝ) * N ^ (2 * k + 6) * M * Real.sqrt |u - u'|)
    (hKs : ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖C.K n u σ a - C.K n u' σ a‖ ≤ N ^ 6 * Real.sqrt |u - u'|)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ‖(C.L n u σ a ω - C.K n u σ a) - (C.L n u' σ a ω - C.K n u' σ a)‖ ≤ 7 * N ^ 10 * M * Real.sqrt |u - u'| := by
  have hL := hLs σ a
  have hK := hKs σ a
  have hs0 : 0 ≤ Real.sqrt |u - u'| := Real.sqrt_nonneg _
  have e : (C.L n u σ a ω - C.K n u σ a) - (C.L n u' σ a ω - C.K n u' σ a) =
      (C.L n u σ a ω - C.L n u' σ a ω) - (C.K n u σ a - C.K n u' σ a) := by ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have h2 : N ^ 6 ≤ N ^ 10 * M := by
    calc N ^ 6 ≤ N ^ 10 := pow_le_pow_right₀ hN1 (by norm_num)
      _ = N ^ 10 * 1 := (mul_one _).symm
      _ ≤ N ^ 10 * M := mul_le_mul_of_nonneg_left hM1 (by positivity)
  have hL' : 3 * ((2 : ℕ) : ℝ) * N ^ (2 * 2 + 6) * M * Real.sqrt |u - u'| = 6 * N ^ 10 * M * Real.sqrt |u - u'| := by
    norm_num
  rw [hL'] at hL
  nlinarith [mul_le_mul_of_nonneg_right h2 hs0]

/-- The one-loop `⟨G̃_u(τ) E_x⟩ = 𝓛^{(1)}_{u,τ,x} - m(τ)` moves by `3 N⁸ M √|u-u'|` over a carrier (band: `3 N⁹ √`, `M = N`). -/
private theorem lemDecCalELip_avg_sub
    (hLs : ∀ {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖C.L n u σ a ω - C.L n u' σ a ω‖ ≤ 3 * (k : ℝ) * N ^ (2 * k + 6) * M * Real.sqrt |u - u'|)
    (τ : Bool) (x : Zd d (sz.L n)) :
    ‖(C.L n u (fun _ : Fin 1 => τ) (fun _ => x) ω - (if τ then C.m n else (starRingEnd ℂ) (C.m n))) -
        (C.L n u' (fun _ : Fin 1 => τ) (fun _ => x) ω - (if τ then C.m n else (starRingEnd ℂ) (C.m n)))‖ ≤
      3 * N ^ 8 * M * Real.sqrt |u - u'| := by
  rw [sub_sub_sub_cancel_right]
  exact (hLs (fun _ : Fin 1 => τ) (fun _ => x)).trans (le_of_eq (by norm_num))

/-- `‖⟨G̃_v(τ) E_x⟩‖ ≤ 2 N³` over a carrier, from `‖m‖ ≤ 1` and the loop size `N^{2k+1}` at `k = 1` (band: `‖m(τ)‖ = 1`). -/
private theorem lemDecCalELip_avg_norm (hN1 : 1 ≤ N) (hm : ‖C.m n‖ ≤ 1)
    (hLn : ∀ {k : ℕ}, 1 ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)), ‖C.L n u σ a ω‖ ≤ N ^ (2 * k + 1))
    (τ : Bool) (x : Zd d (sz.L n)) :
    ‖C.L n u (fun _ : Fin 1 => τ) (fun _ => x) ω - (if τ then C.m n else (starRingEnd ℂ) (C.m n))‖ ≤ 2 * N ^ 3 := by
  have h := hLn (k := 1) le_rfl (fun _ : Fin 1 => τ) (fun _ => x)
  have hmτ : ‖(if τ then C.m n else (starRingEnd ℂ) (C.m n))‖ ≤ 1 := by cases τ <;> simp [hm]
  have h1 : (1 : ℝ) ≤ N ^ 3 := one_le_pow₀ hN1
  have h3 : N ^ (2 * 1 + 1) = N ^ 3 := by norm_num
  rw [h3] at h
  exact (norm_sub_le _ _).trans (by linarith)

/-- `‖ℰ^{G̃,(2)}_u - ℰ^{G̃,(2)}_{u'}‖ ≤ 42 N^{16} M √|u-u'|` over a carrier (band case `M = N`): the one-loop
`⟨G̃E_x⟩ = 𝓛^{(1)} - m(τ)` moves by `3 N⁸ M √` and has size `2 N³`, the three-loop moves by `9 N^{12} M √` and has size `N⁷`. -/
theorem LemDecCalELip_EGt_subg (hN : N = ((sz.size n : ℕ) : ℝ)) (hN1 : 1 ≤ N) (hM1 : 1 ≤ M) (hu0 : 0 ≤ u) (hut : u ≤ t)
    (hu'0 : 0 ≤ u') (hu't : u' ≤ t) (hm : ‖C.m n‖ ≤ 1) (hS : ∀ a, ∑ b, ‖C.S n a b‖ ≤ 1)
    (hLn : ∀ v : ℝ, 0 ≤ v → v ≤ t → ∀ {k : ℕ}, 1 ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)), ‖C.L n v σ a ω‖ ≤ N ^ (2 * k + 1))
    (hLs : ∀ {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖C.L n u σ a ω - C.L n u' σ a ω‖ ≤ 3 * (k : ℝ) * N ^ (2 * k + 6) * M * Real.sqrt |u - u'|)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ‖STEGtg C n u σ a ω - STEGtg C n u' σ a ω‖ ≤ 42 * N ^ 16 * M * Real.sqrt |u - u'| := by
  have hs0 : 0 ≤ Real.sqrt |u - u'| := Real.sqrt_nonneg _
  have hN0 : 0 ≤ N := by linarith
  have hM0 : 0 ≤ M := by linarith
  have key : ∀ (τ : Bool) (τ3 : Fin 3 → Bool) (b3 : Zd d (sz.L n) → Fin 3 → Zd d (sz.L n)),
      ‖(∑ x, ∑ y, (C.L n u (fun _ : Fin 1 => τ) (fun _ => x) ω - (if τ then C.m n else (starRingEnd ℂ) (C.m n))) *
            C.S n x y * C.L n u τ3 (b3 y) ω) -
        (∑ x, ∑ y, (C.L n u' (fun _ : Fin 1 => τ) (fun _ => x) ω - (if τ then C.m n else (starRingEnd ℂ) (C.m n))) *
            C.S n x y * C.L n u' τ3 (b3 y) ω)‖ ≤
        (Fintype.card (Zd d (sz.L n)) : ℝ) * (21 * N ^ 15 * M * Real.sqrt |u - u'|) := by
    intro τ τ3 b3
    have h3n : ∀ y, ‖C.L n u τ3 (b3 y) ω‖ ≤ N ^ 7 := fun y => by
      have h := hLn u hu0 hut (k := 3) (by norm_num) τ3 (b3 y)
      have h3 : N ^ (2 * 3 + 1) = N ^ 7 := by norm_num
      rwa [h3] at h
    have h3s : ∀ y, ‖C.L n u τ3 (b3 y) ω - C.L n u' τ3 (b3 y) ω‖ ≤ 9 * N ^ 12 * M * Real.sqrt |u - u'| := fun y =>
      (hLs τ3 (b3 y)).trans (le_of_eq (by norm_num))
    have hb := lemDecCalELip_bilin (d := d) (L := sz.L n) (C.S n) hS
      (fun x => C.L n u (fun _ : Fin 1 => τ) (fun _ => x) ω - (if τ then C.m n else (starRingEnd ℂ) (C.m n)))
      (fun x => C.L n u' (fun _ : Fin 1 => τ) (fun _ => x) ω - (if τ then C.m n else (starRingEnd ℂ) (C.m n)))
      (fun y => C.L n u τ3 (b3 y) ω) (fun y => C.L n u' τ3 (b3 y) ω)
      (δA := 3 * N ^ 8 * M * Real.sqrt |u - u'|) (δB := 9 * N ^ 12 * M * Real.sqrt |u - u'|)
      (αA := 2 * N ^ 3) (βB := N ^ 7) (by positivity) (by positivity) (by positivity)
      (by positivity) (fun x => lemDecCalELip_avg_sub C n ω hLs τ x) h3n
      (fun x => lemDecCalELip_avg_norm C n ω hN1 hm (hLn u' hu'0 hu't) τ x) h3s
    refine hb.trans (le_of_eq ?_)
    ring
  have k1 := key (σ 0) ![σ 0, σ 0, σ 1] (fun y => ![y, a 0, a 1])
  have k2 := key (σ 1) ![σ 0, σ 1, σ 1] (fun y => ![a 0, y, a 1])
  have eq : ∀ v : ℝ, STEGtg C n v σ a ω = (((sz.W n : ℕ) : ℂ) ^ d) * (
      (∑ x, ∑ y, (C.L n v (fun _ : Fin 1 => σ 0) (fun _ => x) ω - (if σ 0 then C.m n else (starRingEnd ℂ) (C.m n))) *
          C.S n x y * C.L n v ![σ 0, σ 0, σ 1] ![y, a 0, a 1] ω) +
      (∑ x, ∑ y, (C.L n v (fun _ : Fin 1 => σ 1) (fun _ => x) ω - (if σ 1 then C.m n else (starRingEnd ℂ) (C.m n))) *
          C.S n x y * C.L n v ![σ 0, σ 1, σ 1] ![a 0, y, a 1] ω)) := by
    intro v
    unfold STEGtg
    simp only [Finset.sum_add_distrib]
  rw [eq u, eq u', ← mul_sub, norm_mul, norm_pow, Complex.norm_natCast]
  have hWd : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hsplit : ∀ P1 P2 P1' P2' : ℂ, (P1 + P2) - (P1' + P2') = (P1 - P1') + (P2 - P2') :=
    fun _ _ _ _ => by ring
  rw [hsplit]
  refine (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add k1 k2)) hWd).trans
    (le_of_eq ?_)
  calc ((sz.W n : ℕ) : ℝ) ^ d * ((Fintype.card (Zd d (sz.L n)) : ℝ) * (21 * N ^ 15 * M * Real.sqrt |u - u'|) +
        (Fintype.card (Zd d (sz.L n)) : ℝ) * (21 * N ^ 15 * M * Real.sqrt |u - u'|))
      = (((sz.W n : ℕ) : ℝ) ^ d * (Fintype.card (Zd d (sz.L n)) : ℝ)) *
          (42 * N ^ 15 * M * Real.sqrt |u - u'|) := by ring
    _ = 42 * N ^ 16 * M * Real.sqrt |u - u'| := by rw [lemDecCalELip_Wd_card sz n hN]; ring


end FunctionalsG


/-! ### 3b. The band functionals as corollaries of the carrier ones

The band carrier is `bandFM sz (fun _ => E)` (the band functionals are definitionally those of the carrier), the flow modulus holds at `c = 1`
(`M = N`), the kernel rows sum to `1` (`sum_norm_SB_row`), `‖m(E)‖ = 1` (`norm_mE`), and the four inputs of the
carrier lemmas are the band loop and `𝒦^{(2)}` lemmas of sections 1 and 2. -/

section FunctionalsBand

variable {d : ℕ} (sz : Sizes d)

/-- Band input: the modulus `3 k N^{2k+6} N √|u-u'|` of the loops (exponent `2k+7` of `LemDecCalELip_Lloop_sub`). -/
private theorem lemDecCalELip_bandIn_Ls (n : ℕ) (E : ℝ) {t u u' N : ℝ} (ω : sz.SeqΩ) (hN : N = ((sz.size n : ℕ) : ℝ)) (hN1 : 1 ≤ N)
    (hE : |E| < 2) (ht : t < 1) (hu0 : 0 ≤ u) (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t) (hQ : (etaT E t)⁻¹ ≤ N ^ 2)
    (hgood : ∀ c : CoordF d (sz.L n) (sz.W n), |sz.slice n ω c| ≤ N) :
    ∀ {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖(bandFM sz fun _ => E).L n u σ a ω - (bandFM sz fun _ => E).L n u' σ a ω‖ ≤
        3 * (k : ℝ) * N ^ (2 * k + 6) * N * Real.sqrt |u - u'| := fun σ a =>
  (LemDecCalELip_Lloop_sub sz n E ω hN hN1 hE ht hu0 hut hu'0 hu't hQ hgood σ a).trans (le_of_eq (by ring))

/-- Band input: the modulus `N^6 √|u-u'|` of `𝒦^{(2)}` (the Hölder form of section 2 is below `N^6 √`). -/
private theorem lemDecCalELip_bandIn_Ks (n : ℕ) (E : ℝ) {t u u' N : ℝ} (hN1 : 1 ≤ N) (hE : |E| < 2) (ht : t < 1) (hu0 : 0 ≤ u)
    (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t) (htN : (1 - t)⁻¹ ≤ N) :
    ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      ‖(bandFM sz fun _ => E).K n u σ a - (bandFM sz fun _ => E).K n u' σ a‖ ≤ N ^ 6 * Real.sqrt |u - u'| := fun σ a =>
  (LemDecCalELip_STKloop_two_sub sz n hE.le ht hu0 hut hu'0 hu't htN σ a).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hN1 (by norm_num)) (Real.sqrt_nonneg _))

section Det

open scoped Matrix.Norms.L2Operator

variable (n : ℕ) (E : ℝ) {t u u' N : ℝ} (ω : sz.SeqΩ)
  (hN : N = ((sz.size n : ℕ) : ℝ)) (hN1 : 1 ≤ N) (hE : |E| < 2) (ht : t < 1) (hu0 : 0 ≤ u)
  (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t) (hQ : (etaT E t)⁻¹ ≤ N ^ 2)
  (hgood : ∀ c : CoordF d (sz.L n) (sz.W n), |sz.slice n ω c| ≤ N) (htN : (1 - t)⁻¹ ≤ N)

include hN hN1 hE ht hu0 hut hu'0 hu't hQ hgood htN

/-- `(𝓛 - 𝒦)^{(2)}` is Hölder-1/2: `‖(𝓛-𝒦)_u - (𝓛-𝒦)_{u'}‖ ≤ 7 N^{11} √|u-u'|` (`LemDecCalELip_LK_subg`, `M = N`). -/
theorem LemDecCalELip_LK_sub (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ‖(Lloop sz n E u σ a ω - STKloop sz n E u σ a) -
        (Lloop sz n E u' σ a ω - STKloop sz n E u' σ a)‖ ≤
      7 * N ^ 11 * Real.sqrt |u - u'| :=
  (LemDecCalELip_LK_subg (bandFM sz fun _ => E) n ω hN1 hN1
    (lemDecCalELip_bandIn_Ls sz n E ω hN hN1 hE ht hu0 hut hu'0 hu't hQ hgood)
    (lemDecCalELip_bandIn_Ks sz n E hN1 hE ht hu0 hut hu'0 hu't htN) σ a).trans (le_of_eq (by ring))

/-- **Deterministic bound for `STLK2`**: `|STLK2_u - STLK2_{u'}| ≤ 7 N^{11} √|u-u'|`. -/
theorem LemDecCalELip_LK2_sub (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    |STLK2 sz n E u σ a ω - STLK2 sz n E u' σ a ω| ≤ 7 * N ^ 11 * Real.sqrt |u - u'| :=
  (abs_norm_sub_norm_le _ _).trans (LemDecCalELip_LK_sub sz n E ω hN hN1 hE ht hu0 hut hu'0 hu't hQ
    hgood htN σ a)

end Det

end FunctionalsBand


/-! ## 4. The four functionals are Hölder-1/2 in `u` on `contGood` -/

section L1

variable {d : ℕ}

/-- `(η_t)⁻¹ ≤ N²` from `(1 - t)⁻¹ ≤ N`, `Im m ≥ c₁` and `1/c₁ ≤ N`. -/
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

/-- **The eventual numerical facts of the Hölder-1/2 bound**: `M ≤ N`, `1 ≤ N`, `|E_n| < 2`,
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

/-- **`STLK2` is Hölder-1/2** in `u ∈ [s_n, t_n]` on `contGood`, constant `N^{12}`. -/
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

end L1

section L1G

variable {d : ℕ} {sz : Sizes d}

/-- **The eventual numerical facts over a carrier**: `M ≤ N`, `1 ≤ N`, `(η_t)⁻¹ ≤ N²`, `(1 - t)⁻¹ ≤ N` (band
case `LemDecCalELip_env`; the premise `|E| < 2` is replaced by `κ ≤ Im m` and `η_t = (1 - t) Im m`). -/
theorem LemDecCalELip_envg {Cm : Step2Mat sz} {t : ℕ → ℝ} {κ : ℝ} (hκ : 0 < κ) (hIm : ∀ n, κ ≤ (Cm.m n).im)
    (hη : ∀ n (u : ℝ), Cm.eta n u = (1 - u) * (Cm.m n).im) (hsize : sz.SizeTendsto)
    (hN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) (M : ℝ) :
    ∀ᶠ n in atTop, M ≤ ((sz.size n : ℕ) : ℝ) ∧ 1 ≤ ((sz.size n : ℕ) : ℝ) ∧
      (Cm.eta n (t n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ 2 ∧ (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
  filter_upwards [hsize.eventually_ge_atTop (max M (max 1 (1 / κ))), hN] with n h1 h2
  have h1N : 1 ≤ ((sz.size n : ℕ) : ℝ) := ((le_max_left _ _).trans (le_max_right _ _)).trans h1
  have hc : 1 / κ ≤ ((sz.size n : ℕ) : ℝ) := ((le_max_right _ _).trans (le_max_right _ _)).trans h1
  have hm0 : 0 < (Cm.m n).im := lt_of_lt_of_le hκ (hIm n)
  refine ⟨(le_max_left _ _).trans h1, h1N, ?_, h2⟩
  rw [hη, mul_inv, sq]
  exact mul_le_mul h2 ((one_div κ ▸ inv_anti₀ hκ (hIm n)).trans hc) (inv_nonneg.2 hm0.le) (by linarith)

/-- `k N^e N^c x ≤ N^{(e+1)+c} x` for `k ≤ N`, `x ≥ 0`: the constant is absorbed in the exponent. -/
private theorem lemDecCalELipG_absorb {N k x c : ℝ} {e : ℕ} (hk : k ≤ N) (hN1 : 1 ≤ N) (hx : 0 ≤ x) :
    k * N ^ e * N ^ c * x ≤ N ^ (((e + 1 : ℕ) : ℝ) + c) * x := by
  have hN0 : 0 < N := by linarith
  rw [Real.rpow_add hN0, Real.rpow_natCast]
  calc k * N ^ e * N ^ c * x = (N ^ e * N ^ c * k) * x := by ring
    _ ≤ (N ^ e * N ^ c * N) * x := by gcongr
    _ = N ^ (e + 1) * N ^ c * x := by ring

/-- **The loop facts of the flow modulus on its good event** (packaged forms of `LemDecCalELip_Lloop_subg`, `LemDecCalELip_Lloop_normg`): for
`t < 1` and `(η_t)⁻¹ ≤ N²` eventually, on `G` and for all `u, u' ∈ [0,t_n]`, every `𝓛^{(k)}` moves by
`≤ 3 k N^{2k+6} N^c √|u-u'|` and has size `≤ N^{2k+1}`, `k ≥ 1`. -/
theorem lemDecCalELipG_loops {Cm : Step2Mat sz} {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E)
    {Hm : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {G : ℕ → Set sz.SeqΩ} {c : ℝ}
    (hLM : ∀ (n : ℕ) (u : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) ω, Cm.LM n u (Hm n u ω) σ a = Cm.L n u σ a ω)
    (hc : 0 ≤ c) (hmod : LemDecCalELipG_Mod Hm G c) (hm : ∀ n, ‖Cm.m n‖ ≤ 1)
    {t : ℕ → ℝ} (ht : ∀ n, t n < 1) (hQ : ∀ᶠ n in atTop, (Cm.eta n (t n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ 2) :
    ∀ᶠ n in atTop, ∀ ω ∈ G n,
      (∀ u u' : ℝ, 0 ≤ u → u ≤ t n → 0 ≤ u' → u' ≤ t n → ∀ {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
        ‖Cm.L n u σ a ω - Cm.L n u' σ a ω‖ ≤
          3 * (k : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (2 * k + 6) * ((sz.size n : ℕ) : ℝ) ^ c * Real.sqrt |u - u'|) ∧
      ∀ u : ℝ, 0 ≤ u → u ≤ t n → ∀ {k : ℕ}, 1 ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
        ‖Cm.L n u σ a ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * k + 1) := by
  filter_upwards [hQ] with n hQn ω hω
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have h1 : ∀ v, v ≤ t n → v ≤ 1 := fun v hv => (hv.trans (ht n).le)
  refine ⟨fun u u' hu0 hut hu'0 hu't k σ a => ?_, fun u hu0 hut k hk σ a => ?_⟩
  · exact LemDecCalELip_Lloop_subg hL hLM hc (hm n) ω rfl hN1 (ht n) hu0 hut hu'0 hu't hQn
      (fun v hv0 hvt => (hmod n ω hω v v hv0 (h1 v hvt) hv0 (h1 v hvt)).1)
      (fun x y => (hmod n ω hω u u' hu0 (h1 u hut) hu'0 (h1 u' hu't)).2 x y) σ a
  · exact LemDecCalELip_Lloop_normg hL hLM ω hN1 (ht n) hut hQn ((hmod n ω hω u u hu0 (h1 u hut) hu0 (h1 u hut)).1) hk σ a

/-- **The size of `𝒦^{(2)}` from its decay** (the class `Step2IterGen_K2`: `‖𝒦^{(2)}_u‖ ≤ C_K W^{-d} 𝒯̃^L_{u,D}`,
with `D = 1`) and the size data `c_B W^{-d} ≤ W^{-d} B_{u,0} ≤ N^{-c}` (`STBdatagL`):
`STprof ≤ (1 + c_B⁻¹) W^{-d} B_{u,0} ≤ 1 + c_B⁻¹`, so `‖𝒦^{(2)}_u‖ ≤ C_K (1 + c_B⁻¹) ≤ N` eventually. -/
theorem lemDecCalELipG_Kn {C : FlowFM sz} {t : ℕ → ℝ} {CK cB c : ℝ} (hCK : 0 ≤ CK) (hcB : 0 < cB) (hc : 0 < c) (hsize : sz.SizeTendsto)
    (hdec : ∀ᶠ n in atTop, ∀ (u D : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), 0 ≤ u → u ≤ t n → 0 ≤ D →
      ‖C.K n u σ a‖ ≤ CK * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1))
    (hBd : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
      cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c)) :
    ∀ᶠ n in atTop, ∀ v : ℝ, 0 ≤ v → v ≤ t n → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖C.K n v σ a‖ ≤ ((sz.size n : ℕ) : ℝ) := by
  filter_upwards [hdec, hBd, hsize.eventually_ge_atTop (CK * (1 + cB⁻¹)), hsize.eventually_ge_atTop 1] with n hd hB hN hN1 v hv0 hvt σ a
  have hP := ST_prof_le_Bctl sz n (u := v) (D := 1) (ℓ := ((sz.L n : ℕ) : ℝ)) hcB (Nat.cast_nonneg _) one_pos (hB v hv0 hvt).1 (a 0) (a 1)
  have hb1 : sz.Bctl n v ≤ 1 := (hB v hv0 hvt).2.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith))
  calc ‖C.K n v σ a‖ ≤ CK * STprof sz n v 1 ((sz.L n : ℕ) : ℝ) (a 0) (a 1) := hd v 1 σ a hv0 hvt zero_le_one
    _ ≤ CK * ((1 + cB⁻¹) * 1) := mul_le_mul_of_nonneg_left (hP.trans (mul_le_mul_of_nonneg_left hb1 (by positivity))) hCK
    _ ≤ _ := by rw [mul_one]; exact hN

end L1G


/-! ## 5. Relative continuity of the deterministic factors -/

section L2

variable {d : ℕ}

/-- **Relative continuity of the deterministic factors of `STLemDecCalEConcl`**: for `u, u' ≤ t < 1`,
`ρ = 1 + (1-t)⁻¹ |u-u'|`: `(1-u')⁻¹ ≤ ρ (1-u)⁻¹`, the same for `(W^d|1-u|)⁻¹`, `ρ` for its `1/2` power,
`ρ²` for `STtailTD`, `ρ⁴` for `STtailTD²` (`cont_inv_add_one_sub_ratio` at `γ = 0`).  Deterministic,
every `n, D, a`. -/
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

/-! ## 6. The realized bound `J♯` -/

section Jsharp

variable {d : ℕ}

/-- **The realized bound** `J♯(n,u,ω) := max(1, max_{σ ∈ {±}², a} |(𝓛-𝒦)^{(2)}_{u,σ,a}| /
T_{u,D}(|a₁-a₂|))` at the single time `u` (`sup'` written as in `STJhatM`). -/
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

/-- **The defining properties of `J♯`** (deterministic, every `n, u, ω`):
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

/-- The real-number inequality chain of `LemDecCalELip_Jsharp_rel`:
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

/-- **Relative continuity of `J♯`** in `u` on `contGood`: Hölder-1/2 of `STLK2`, relative continuity of
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


/-! ## 7. The generic lift `PrecPT → Prec` through `cont_core` -/

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

/-- The `ζ`-closeness: a common factor `b = 1 + δ` with `b^{m+1} ≤ 2` gives
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

/-- **The lift `PrecPT → Prec`**: `PrecPT(ξ ≺ R₀ + J^m R)` + Hölder-1/2 of `ξ` and relative continuity of `J`
on `contGood` + relative continuity of the deterministic `R₀, R` + floors (`J ≥ 1`, `R₀ ≥ 0`,
`R ≥ N^{-CR}`) ⇒ `Prec(ξ ≺ R₀ + J^m R)`, by `cont_core` with `P = seqP sz`,
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

end RBM.Gauss.Sizes
