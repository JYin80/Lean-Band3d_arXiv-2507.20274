/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step2Defs
import RBM3D.Induction.Continuity
import RBM3D.Propagator.Deriv
import RBM3D.Propagator.Props4
import RBM3D.Loop.KLTree

/-!
# The net lift of Step 2, part 1: the decay family `STStep2DecayPT → STStep2Decay`
(ST2-18, ticket T2074)

Port of the first part of `RBM2D/Path/NetLift.lean` at commit `c9a24cf` (cited `NetLift:line`),
onto the merged MD layer, the merged ST-1 net lift (`RBM3D/Induction/ContinuityNet.lean`, T2047,
`cont_core`, `contGood`, `cont_highProbAt_good`, `cont_green_flow_diff`, the scalar facts about
`Bctl`; and `RBM3D/Induction/Continuity.lean`, T2062) and the vocabulary of Step 2
(`RBM3D/Induction/Step2Defs.lean`, T2066).

**Cut line.**  Part 1 (this file) is `NetLift:1-1242` (the abstract net lift, the good event, the
resolvent and flow moduli, the propagator modulus, the `𝓛 - 𝒦` modulus, the scalar estimates, the
ratio of the controls, `netLift_T1_close`, `netLift_bulk`), the pin `Step2NetLift` (`:1334`), the
assembly `netLift_gap`, `netLift_pow_mul_rpow` (`:1362`, `:1376`) and the proof `step2NetLift`
(`:1387-1511`, `end MainT1`).  Part 2 (ST2-19) is `Step2LocalUnif` (`:1343`), `Step2LocalNetLift`
(`:1351`), `netLift_T2_low`, `netLift_T2_close` (`:1244-1324`) and `step2LocalNetLift`
(`:1518-1595`).  The abstract net lift, the good event, the Green-function moduli
(`NetLift:73-588`) are not copied: they are the merged `ContinuityNet` (T2047).

**What is proved of the pin `STNetLift2`.**  `STNetLift2` has the three hypotheses
`STStep2LocalPT ∧ STStep2AvgPT ∧ STStep2DecayPT` and the three conclusions
`STStep2Local ∧ STStep2Avg ∧ STStep2Decay`.  `stNetLift2_part1` is the third conjunct: it takes
`STStep2DecayPT` alone, with the quantifiers and the premises of `STNetLift2`, and concludes
`STStep2Decay`.  `STStep2Avg` has no counterpart in RBM2D `Path/NetLift.lean`; with
`STStep2Local` it is ST2-19.

Renaming (`docs/tickets/ST1-COMMON.md` item 2): `d : Sizes` becomes `sz : Sizes d`, `Z2 L` becomes
`Zd d L`, `Idx L W` becomes `Idx d L W`, `(W L)^2` becomes `(W L)^d = sz.size n`, `spectralM`,
`spectralZ` become `mE`, `zt`, `Gsig` is `Gres`, `BlockIndex` is `Vtx`, `zdist2` becomes
`zdistInf`.  The `d = 2` controls `scaleM⁻²·(η_s/η_u)^4·e^{-√(|a-b|/ℓ_u)}` become
`((1-s)/(1-u))^{C_d}·Bctl_u^{1/5}·STWB_{u,|a-b|}·e^{-√(|a-b|/ℓ_u)}`; the ratio of two values of the
control under a time change is `nl_zeta_ratio` (replaces `netLift_scaleM_ratio`,
`netLift_zeta_ratio`, `netLift_ellT_diff`, `netLift_exp_ell_diff`).  The index set of the loops is
`(σ, a) ∈ {±}² × (Z_L^d)²` (all four sign patterns: `Cv = 3`, where RBM2D had `σ = (-,+)` and
`Cv = 2`), and `𝒦^{(2)} = W^{-d} m₁ m₂ Θ_{u m₁ m₂}(a₁, a₂)` has `‖u m₁ m₂‖ = u`
(`KLK_two`).  `Bandwidth` and `CondStInd` of RBM2D's `Step2NetLift` are not used by its proof
and are dropped; `(eq:WO)` is a hypothesis (the control moves by a factor at most `2` only if
`ĝ ≤ 𝔡⁻¹`).

Every public declaration is `Step2NetLift`, `step2NetLift` (namespace `RBM.Ind`) and
`stNetLift2_part1` (namespace `RBM.Gauss.Sizes`); the helpers are `private`.
-/

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path
  RBM.Loop RBM.Ind.ContinuityNet
open scoped NNReal ENNReal

set_option linter.style.longLine false

/-! ## 1. The modulus of a loop of length `k` in the time -/

section Flow

open scoped Matrix.Norms.L2Operator

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The resolvent word `∏ᵢ G(σᵢ) E_{aᵢ}` over a list of `(σᵢ, aᵢ)` (the `foldr` of `loopL`); copy of
the private `contWord`, `Continuity.lean:89`. -/
private noncomputable def nlWord (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (l : List (Bool × Zd d L)) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1

omit [NeZero W] in
/-- The word of a cons. -/
private theorem nlWord_cons (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (p : Bool × Zd d L) (l : List (Bool × Zd d L)) :
    nlWord H z (p :: l) = Gres H z p.1 * Eblk d L W p.2 * nlWord H z l := rfl

/-- The word is bounded by `Q^length` (`Continuity.lean`, private `cont_word_norm`, copied: a
private declaration cannot be imported). -/
private theorem nl_word_norm (hW : 1 ≤ W) {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    {z : ℂ} {Q : ℝ} (hQ : ∀ σ, ‖Gres H z σ‖ ≤ Q) (l : List (Bool × Zd d L)) :
    ‖nlWord H z l‖ ≤ Q ^ l.length := by
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hQ true)
  induction l with
  | nil => simp [nlWord]
  | cons p l ih =>
    have hEa := cont_norm_Eblk_le_one (d := d) (L := L) hW p.2
    rw [nlWord_cons, List.length_cons, pow_succ]
    calc ‖Gres H z p.1 * Eblk d L W p.2 * nlWord H z l‖
        ≤ ‖Gres H z p.1‖ * ‖Eblk d L W p.2‖ * ‖nlWord H z l‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ Q * 1 * Q ^ l.length :=
          mul_le_mul (mul_le_mul (hQ _) hEa (norm_nonneg _) hQ0) ih (norm_nonneg _) (by positivity)
      _ = Q ^ l.length * Q := by ring

/-- The `k`-fold telescoping of a resolvent word: port of RBM1D `norm_gchain_sub_le`
(`Gauss/Step1Hyp.lean:517` at `86573b9`) to the block matrices of `d ≥ 3` (copy of the private
`cont_word_diff`, `Continuity.lean:119`). -/
private theorem nl_word_diff (hW : 1 ≤ W)
    {H H' : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z z' : ℂ} {Q S : ℝ} (hQ1 : 1 ≤ Q)
    (hQ : ∀ σ, ‖Gres H z σ‖ ≤ Q) (hQ' : ∀ σ, ‖Gres H' z' σ‖ ≤ Q)
    (hS : ∀ σ, ‖Gres H z σ - Gres H' z' σ‖ ≤ S) (l : List (Bool × Zd d L)) :
    ‖nlWord H z l - nlWord H' z' l‖ ≤ (l.length : ℝ) * Q ^ l.length * S := by
  have hQ0 : 0 ≤ Q := by linarith
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS true)
  induction l with
  | nil => simp [nlWord]
  | cons p l ih =>
    have hEa := cont_norm_Eblk_le_one (d := d) (L := L) hW p.2
    rw [nlWord_cons, nlWord_cons]
    have key : Gres H z p.1 * Eblk d L W p.2 * nlWord H z l -
        Gres H' z' p.1 * Eblk d L W p.2 * nlWord H' z' l =
        (Gres H z p.1 - Gres H' z' p.1) * Eblk d L W p.2 * nlWord H z l +
          Gres H' z' p.1 * Eblk d L W p.2 * (nlWord H z l - nlWord H' z' l) := by
      noncomm_ring
    rw [key]
    have hP := nl_word_norm hW hQ l
    have t1 : ‖(Gres H z p.1 - Gres H' z' p.1) * Eblk d L W p.2 * nlWord H z l‖ ≤
        S * 1 * Q ^ l.length := by
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul (hS _) hEa (norm_nonneg _) hS0)) hP
        (norm_nonneg _) (by positivity)
    have t2 : ‖Gres H' z' p.1 * Eblk d L W p.2 * (nlWord H z l - nlWord H' z' l)‖ ≤
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

/-- The loop `loopFine` is the trace of the `nlWord` of the block matrix. -/
private theorem nl_loopFine_eq (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    loopFine d L W H z σ a =
      Matrix.trace (nlWord (blockMat d L W H) z ((List.ofFn σ).zip (List.ofFn a))) := by
  unfold loopFine
  rw [loopM_eq_loopL]
  rfl

/-- The modulus of a loop of length `k` along the flow, on `‖X‖ ≤ Xb` (`Gopboundu` and the net
argument of 5-6:16; RBM1D `norm_gloop_sub_le`, `Gauss/Step1Hyp.lean:571` at `86573b9`, for the
block matrices of `d ≥ 3`; the trace is bounded by `card(Vtx) · ‖·‖`).
Copy of the private `cont_loopAbs_diff` (`Continuity.lean:166`, T2062), stated for the norm of the
difference (`NetLift:661` `netLift_gloop_diff` for `k = 2`) instead of the difference of the norms;
`Continuity.lean` does not export it. -/
private theorem nl_loop_sub (hW : 1 ≤ W) (ω : Ω d L W) {E t u u' Q Xb : ℝ} (hE : |E| < 2)
    (ht : t < 1) (hu0 : 0 ≤ u) (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t)
    (hΔ : |u - u'| ≤ 1) (hQ1 : 1 ≤ Q) (hQ : (etaT E t)⁻¹ ≤ Q)
    (hXb : ‖blockMat d L W (Xmat d L W ω)‖ ≤ Xb) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d L) :
    ‖loopFine d L W (Hflow d L W u ω) (zt E u) σ a -
        loopFine d L W (Hflow d L W u' ω) (zt E u') σ a‖ ≤
      (Fintype.card (Vtx d L W) : ℝ) *
        ((k : ℝ) * Q ^ k * (Q * Q * (Xb + 1) * Real.sqrt |u - u'|)) := by
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
  have hGu : ∀ σ : Bool, ‖Gres (blockMat d L W (Hflow d L W u ω)) (zt E u) σ‖ ≤ Q := fun σ =>
    (norm_Gsig_le_inv_eta hHu hη hzu σ).trans hQ
  have hGu' : ∀ σ : Bool, ‖Gres (blockMat d L W (Hflow d L W u' ω)) (zt E u') σ‖ ≤ Q := fun σ =>
    (norm_Gsig_le_inv_eta hHu' hη hzu' σ).trans hQ
  have hw := nl_word_diff hW hQ1 hGu hGu' hS ((List.ofFn σ).zip (List.ofFn a))
  have hlen : ((List.ofFn σ).zip (List.ofFn a)).length = k := by simp
  rw [hlen] at hw
  rw [nl_loopFine_eq, nl_loopFine_eq]
  rw [← Matrix.trace_sub]
  refine (norm_matrix_trace_le_card_mul _).trans ?_
  exact mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)

end Flow

/-- `(η_t)⁻¹ ≤ N²` from `(1 - t)⁻¹ ≤ N`, `Im m ≥ c₁` and `1/c₁ ≤ N` (copy of the private
`cont_eta_inv_le`, `Continuity.lean:346`). -/
private theorem nl_eta_inv_le {E t N c₁ : ℝ} (hE : |E| < 2) (hN0 : 0 < N) (hc₁ : 0 < c₁)
    (hc₁m : c₁ ≤ (mE E).im) (hNc : 1 / c₁ ≤ N) (hN1 : (1 - t)⁻¹ ≤ N) :
    (etaT E t)⁻¹ ≤ N ^ 2 := by
  have hm : 0 < (mE E).im := mE_im_pos hE
  have h1 : (etaT E t)⁻¹ = (1 - t)⁻¹ * ((mE E).im)⁻¹ := by
    unfold etaT; rw [mul_inv]
  have h2 : ((mE E).im)⁻¹ ≤ N := by
    refine le_trans ?_ hNc
    rw [one_div]; exact inv_anti₀ hc₁ hc₁m
  rw [h1, sq]
  exact mul_le_mul hN1 h2 (inv_nonneg.2 hm.le) hN0.le

/-! ## 2. The modulus of `𝒦^{(2)}` in the time -/

section KMod

open scoped Matrix.Norms.Operator

variable {d L : ℕ} [NeZero L]

/-- An entry is at most the `ℓ^∞` operator norm (`Prop5Short.lean`, private `P5s_entry_le_norm`). -/
private theorem nl_entry_le_norm {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ)
    (x y : n) : ‖M x y‖ ≤ ‖M‖ :=
  le_trans (Finset.single_le_sum (f := fun j => ‖M x j‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ y)) (RBM.sum_norm_row_le M x)

/-- The propagator is Lipschitz in the time, entrywise, at the charge `u m` with `‖m‖ = 1`:
`|Θ_{u m}(a,b) - Θ_{u' m}(a,b)| ≤ |u - u'| (1-u)⁻¹ (1-u')⁻¹`.  `NetLift:595` (`netLift_Theta_diff`),
from `Theta_sub_Theta`, `norm_SB`, `norm_Theta_le` (the `ℓ^∞` operator norm `(1-u)⁻¹`). -/
private theorem nl_Theta_diff (hL : 3 ≤ L) (g : ℝ) {m : ℂ} (hm : ‖m‖ = 1) {u u' : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hu'0 : 0 ≤ u') (hu'1 : u' < 1) (a b : Zd d L) :
    ‖Theta d L g ((u : ℂ) * m) a b - Theta d L g ((u' : ℂ) * m) a b‖ ≤
      |u - u'| * ((1 - u)⁻¹ * (1 - u')⁻¹) := by
  have hS := norm_SB d L g hL
  have hn : ∀ v : ℝ, 0 ≤ v → ‖(v : ℂ) * m‖ = v := fun v hv => by
    rw [norm_mul, hm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv]
  have hζ : ‖(u : ℂ) * m‖ < 1 := by rw [hn u hu0]; exact hu1
  have hξ : ‖(u' : ℂ) * m‖ < 1 := by rw [hn u' hu'0]; exact hu'1
  have h1 := nl_entry_le_norm (Theta d L g ((u : ℂ) * m) - Theta d L g ((u' : ℂ) * m)) a b
  rw [Matrix.sub_apply] at h1
  refine h1.trans ?_
  rw [Theta_sub_Theta d L g hS hξ hζ, norm_smul]
  have hdiff : ‖(u : ℂ) * m - (u' : ℂ) * m‖ = |u - u'| := by
    rw [← sub_mul, norm_mul, hm, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
  rw [hdiff]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc ‖Theta d L g ((u : ℂ) * m) * SB d L g * Theta d L g ((u' : ℂ) * m)‖
      ≤ ‖Theta d L g ((u : ℂ) * m) * SB d L g‖ * ‖Theta d L g ((u' : ℂ) * m)‖ := norm_mul_le _ _
    _ ≤ ‖Theta d L g ((u : ℂ) * m)‖ * ‖SB d L g‖ * ‖Theta d L g ((u' : ℂ) * m)‖ := by
        gcongr
        exact norm_mul_le _ _
    _ ≤ (1 - u)⁻¹ * 1 * (1 - u')⁻¹ := by
        rw [hS]
        gcongr
        · exact norm_Theta_le hL hu0 hu1 hm
        · exact norm_Theta_le hL hu'0 hu'1 hm
    _ = (1 - u)⁻¹ * (1 - u')⁻¹ := by ring

omit [NeZero L] in
/-- `𝒦^{(2)}` of a loop index of length `2`. -/
private theorem nl_KLloopOf_two (σ : Fin 2 → Bool) (a : Fin 2 → Zd d L) :
    KLloopOf d L σ a = ⟨[σ 0, σ 1], [a 0, a 1]⟩ := by
  simp [KLloopOf, List.ofFn_succ]

/-- **The modulus of `𝒦^{(2)}`**: `|𝒦^{(2)}_{u,σ,a} - 𝒦^{(2)}_{u',σ,a}| ≤ (1-t)⁻² |u - u'|` for
`u, u' ∈ [0, t]`, `t < 1`, `|E| ≤ 2`, `W ≥ 1`.  `KLK_two`: `𝒦^{(2)} = W^{-d} m₁ m₂ Θ_{u m₁ m₂}(a₁,a₂)`
with `‖m₁ m₂‖ = 1`.  `NetLift:707` (`netLift_Kpm_diff`), all four sign patterns. -/
private theorem nl_K_diff (hL : 3 ≤ L) {W : ℕ} (hW : 1 ≤ W) (g : ℝ) {E t u u' : ℝ} (hE : |E| ≤ 2)
    (ht : t < 1) (hu0 : 0 ≤ u) (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d L) :
    ‖KLK d L g W E u (KLloopOf d L σ a) - KLK d L g W E u' (KLloopOf d L σ a)‖ ≤
      (1 - t)⁻¹ * (1 - t)⁻¹ * |u - u'| := by
  have h1t : 0 < 1 - t := by linarith
  have hm : ‖mSigma E (σ 0) * mSigma E (σ 1)‖ = 1 := by
    rw [norm_mul, norm_mSigma hE, norm_mSigma hE, mul_one]
  rw [nl_KLloopOf_two, KLK_two, KLK_two, ← mul_sub, norm_mul]
  have hW1 : ‖((W : ℂ) ^ d)⁻¹ * (mSigma E (σ 0) * mSigma E (σ 1))‖ ≤ 1 := by
    rw [norm_mul, hm, mul_one, norm_inv, norm_pow, Complex.norm_natCast]
    have : (1 : ℝ) ≤ (W : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hW)
    exact inv_le_one_of_one_le₀ this
  have hd := nl_Theta_diff hL g hm hu0 (by linarith) hu'0 (by linarith) (a 0) (a 1)
  have hinv : (1 - u)⁻¹ ≤ (1 - t)⁻¹ := inv_anti₀ h1t (by linarith)
  have hinv' : (1 - u')⁻¹ ≤ (1 - t)⁻¹ := inv_anti₀ h1t (by linarith)
  calc ‖((W : ℂ) ^ d)⁻¹ * (mSigma E (σ 0) * mSigma E (σ 1))‖ *
        ‖Theta d L g ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) (a 0) (a 1) -
          Theta d L g ((u' : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) (a 0) (a 1)‖
      ≤ 1 * (|u - u'| * ((1 - u)⁻¹ * (1 - u')⁻¹)) :=
        mul_le_mul hW1 hd (norm_nonneg _) zero_le_one
    _ ≤ 1 * (|u - u'| * ((1 - t)⁻¹ * (1 - t)⁻¹)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul hinv hinv' (inv_nonneg.2 (by linarith)) (inv_nonneg.2 h1t.le))
          (abs_nonneg _)) zero_le_one
    _ = (1 - t)⁻¹ * (1 - t)⁻¹ * |u - u'| := by ring

end KMod

/-! ## 3. The slow variation of the control of `STStep2Decay` -/

section Scalars

/-- `|(1-u)^{-1/2} - (1-u')^{-1/2}| ≤ (1-t)⁻¹ |u-u'|^{1/2}` for `u, u' ≤ t < 1`.
`NetLift:884` (`netLift_one_div_sqrt_diff`). -/
private theorem nl_one_div_sqrt_diff {t u u' : ℝ} (ht : t < 1) (hut : u ≤ t) (hu't : u' ≤ t) :
    |1 / Real.sqrt (1 - u) - 1 / Real.sqrt (1 - u')| ≤ (1 - t)⁻¹ * Real.sqrt |u - u'| := by
  have h1t : 0 < 1 - t := by linarith
  have hx : 0 < 1 - u := by linarith
  have hx' : 0 < 1 - u' := by linarith
  have ha0 : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.2 hx
  have hb0 : 0 < Real.sqrt (1 - u') := Real.sqrt_pos.2 hx'
  have hab : 1 - t ≤ Real.sqrt (1 - u) * Real.sqrt (1 - u') := by
    have hta : Real.sqrt (1 - t) ≤ Real.sqrt (1 - u) := Real.sqrt_le_sqrt (by linarith)
    have htb : Real.sqrt (1 - t) ≤ Real.sqrt (1 - u') := Real.sqrt_le_sqrt (by linarith)
    calc 1 - t = Real.sqrt (1 - t) * Real.sqrt (1 - t) := (Real.mul_self_sqrt h1t.le).symm
      _ ≤ _ := mul_le_mul hta htb (Real.sqrt_nonneg _) ha0.le
  have heq : 1 / Real.sqrt (1 - u) - 1 / Real.sqrt (1 - u') =
      (Real.sqrt (1 - u') - Real.sqrt (1 - u)) / (Real.sqrt (1 - u) * Real.sqrt (1 - u')) := by
    field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos ha0 hb0)]
  have hba : |Real.sqrt (1 - u') - Real.sqrt (1 - u)| ≤ Real.sqrt |u - u'| := by
    have h := cont_abs_sqrt_sub_sqrt_le hx'.le hx.le
    have h2 : |(1 - u') - (1 - u)| = |u - u'| := by
      rw [show (1 - u') - (1 - u) = -(u' - u) by ring, abs_neg, abs_sub_comm]
    rwa [h2] at h
  calc |Real.sqrt (1 - u') - Real.sqrt (1 - u)| / (Real.sqrt (1 - u) * Real.sqrt (1 - u'))
      ≤ Real.sqrt |u - u'| / (1 - t) := by gcongr
    _ = (1 - t)⁻¹ * Real.sqrt |u - u'| := by rw [div_eq_inv_mul]

/-- The range `ℓ_u` is Hölder-`1/2` in `u`: `|ℓ_u - ℓ_{u'}| ≤ ĝ (1-t)⁻¹ |u-u'|^{1/2}` (`ĝ ≥ 0`).
`NetLift:909` (`netLift_ellT_diff`); new: `ellT` carries the coupling `ĝ`. -/
private theorem nl_ellT_diff {L : ℕ} {g t u u' : ℝ} (hg : 0 ≤ g) (ht : t < 1) (hut : u ≤ t)
    (hu't : u' ≤ t) :
    |ellT L g u - ellT L g u'| ≤ g * ((1 - t)⁻¹ * Real.sqrt |u - u'|) := by
  have hx : 0 < 1 - u := by linarith
  have hx' : 0 < 1 - u' := by linarith
  unfold ellT
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero]
  refine max_le ?_ (by have := Real.sqrt_nonneg |u - u'|; positivity)
  refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero]
  refine max_le ?_ (by have := Real.sqrt_nonneg |u - u'|; positivity)
  rw [abs_of_pos hx, abs_of_pos hx']
  have e : g / Real.sqrt (1 - u) - g / Real.sqrt (1 - u') =
      g * (1 / Real.sqrt (1 - u) - 1 / Real.sqrt (1 - u')) := by ring
  rw [e, abs_mul, abs_of_nonneg hg]
  exact mul_le_mul_of_nonneg_left (nl_one_div_sqrt_diff ht hut hu't) hg

/-- `e^{-√(z/ℓ_{u'})} ≤ e^{δ} e^{-√(z/ℓ_u)}` with `δ = √(z ĝ (1-t)⁻¹ |u-u'|^{1/2})`
(`ℓ ≥ 1`, `z ≥ 0`).  `NetLift:916` (`netLift_exp_ell_diff`), multiplicative form. -/
private theorem nl_exp_ell {L : ℕ} (hL : 1 ≤ L) {g t u u' z : ℝ} (hg : 0 ≤ g) (ht : t < 1)
    (hut : u ≤ t) (hu't : u' ≤ t) (hz : 0 ≤ z) :
    Real.exp (-(z / ellT L g u') ^ (1 / 2 : ℝ)) ≤
      Real.exp (Real.sqrt (z * (g * ((1 - t)⁻¹ * Real.sqrt |u - u'|)))) *
        Real.exp (-(z / ellT L g u) ^ (1 / 2 : ℝ)) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hℓ : 1 ≤ ellT L g u := one_le_ellT hL1
  have hℓ' : 1 ≤ ellT L g u' := one_le_ellT hL1
  have h2 := cont_abs_sqrt_sub_sqrt_le (div_nonneg hz (by linarith : (0 : ℝ) ≤ ellT L g u))
    (div_nonneg hz (by linarith : (0 : ℝ) ≤ ellT L g u'))
  have h3 : |z / ellT L g u - z / ellT L g u'| ≤ z * |ellT L g u - ellT L g u'| := by
    have hpos : 0 < ellT L g u * ellT L g u' := by nlinarith
    have heq : z / ellT L g u - z / ellT L g u' =
        z * (ellT L g u' - ellT L g u) / (ellT L g u * ellT L g u') := by
      field_simp
    rw [heq, abs_div, abs_of_pos hpos, abs_mul, abs_of_nonneg hz, abs_sub_comm (ellT L g u')]
    refine div_le_self (by positivity) (by nlinarith)
  have h4 : z * |ellT L g u - ellT L g u'| ≤ z * (g * ((1 - t)⁻¹ * Real.sqrt |u - u'|)) :=
    mul_le_mul_of_nonneg_left (nl_ellT_diff hg ht hut hu't) hz
  have h5 := h2.trans (Real.sqrt_le_sqrt (h3.trans h4))
  rw [← Real.exp_add, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  refine Real.exp_le_exp.2 ?_
  have := (abs_le.1 h5).2
  linarith

/-- The ratio of `W^{-d} B_{u,K}` at two times, for every block distance `K`:
`STWB_{u,K} ≤ (1 + (1-t)⁻¹ |u-u'|) STWB_{u',K}` (`u, u' ≤ t < 1`); the two terms of `B` are ratios
of the type `cont_inv_add_one_sub_ratio` (as `cont_Bctl_ratio` for `K = 0`). -/
private theorem nl_STWB_ratio {d : ℕ} (sz : Sizes d) (n K : ℕ) {t u u' : ℝ} (ht : t < 1)
    (hut : u ≤ t) (hu't : u' ≤ t) :
    STWB sz n u K ≤ (1 + (1 - t)⁻¹ * |u - u'|) * STWB sz n u' K := by
  have hu : u < 1 := by linarith
  have hu' : u' < 1 := by linarith
  unfold STWB Bparam
  rw [abs_of_pos (by linarith : 0 < 1 - u), abs_of_pos (by linarith : 0 < 1 - u')]
  have hA := cont_inv_add_one_sub_ratio (γ := sz.lam n ^ 2) (sq_nonneg _) ht hut hu't
  have hB := cont_inv_add_one_sub_ratio (γ := 0) le_rfl ht hut hu't
  have hLi : (0 : ℝ) ≤ (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  have hWi : (0 : ℝ) ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  have hc : (0 : ℝ) ≤ ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
  have hBe : ∀ v : ℝ, (((sz.L n : ℕ) : ℝ) ^ d * (1 - v))⁻¹ =
      (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * (0 + (1 - v))⁻¹ := by
    intro v; rw [zero_add, mul_inv]
  rw [hBe u, hBe u']
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ * ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ +
        (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * (0 + (1 - u))⁻¹)
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
        (((1 + (1 - t)⁻¹ * |u - u'|) * (sz.lam n ^ 2 + (1 - u'))⁻¹) *
            ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ +
          (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * ((1 + (1 - t)⁻¹ * |u - u'|) * (0 + (1 - u'))⁻¹)) := by
        gcongr
    _ = (1 + (1 - t)⁻¹ * |u - u'|) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
        ((sz.lam n ^ 2 + (1 - u'))⁻¹ * ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ +
          (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * (0 + (1 - u'))⁻¹)) := by
        ring

/-- `(1-s)/(1-u') ≤ (1 + x) (1-s)/(1-u)` for `u, u' ≤ t < 1`, `s ≤ 1`, `(1-t)⁻¹ |u-u'| ≤ x`. -/
private theorem nl_R_le {s t u u' x : ℝ} (hs : s ≤ 1) (ht : t < 1) (hut : u ≤ t) (hu't : u' ≤ t)
    (hx : (1 - t)⁻¹ * |u - u'| ≤ x) : (1 - s) / (1 - u') ≤ (1 + x) * ((1 - s) / (1 - u)) := by
  have hxu : 0 < 1 - u := by linarith
  have hxs : 0 ≤ 1 - s := by linarith
  have h1 := cont_inv_add_one_sub_ratio (γ := 0) le_rfl ht hu't hut
  rw [zero_add, zero_add, abs_sub_comm] at h1
  have h2 : (1 - u')⁻¹ ≤ (1 + x) * (1 - u)⁻¹ :=
    h1.trans (mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hxu.le))
  calc (1 - s) / (1 - u') = (1 - s) * (1 - u')⁻¹ := div_eq_mul_inv _ _
    _ ≤ (1 - s) * ((1 + x) * (1 - u)⁻¹) := mul_le_mul_of_nonneg_left h2 hxs
    _ = (1 + x) * ((1 - s) / (1 - u)) := by rw [div_eq_mul_inv]; ring

/-- A real power moves by at most `c^{|p|}` when the base moves by a factor `c ≥ 1` (both
directions): `R' ≤ c R`, `R ≤ c R'` give `R'^p ≤ c^{|p|} R^p`, for either sign of `p`. -/
private theorem nl_rpow_ratio {R R' c : ℝ} (p : ℝ) (hR : 0 < R) (hR' : 0 < R') (hc : 1 ≤ c)
    (h1 : R' ≤ c * R) (h2 : R ≤ c * R') : R' ^ p ≤ c ^ |p| * R ^ p := by
  have hc0 : 0 ≤ c := by linarith
  rcases le_or_gt 0 p with hp | hp
  · rw [abs_of_nonneg hp, ← Real.mul_rpow hc0 hR.le]
    exact Real.rpow_le_rpow hR'.le h1 hp
  · rw [abs_of_neg hp]
    have h3 : R'⁻¹ ≤ c * R⁻¹ := cont_inv_le_const_mul_inv hR hR' h2
    have e1 : R' ^ p = (R'⁻¹) ^ (-p) := by
      rw [Real.inv_rpow hR'.le, Real.rpow_neg hR'.le, inv_inv]
    have e2 : R ^ p = (R⁻¹) ^ (-p) := by
      rw [Real.inv_rpow hR.le, Real.rpow_neg hR.le, inv_inv]
    rw [e1, e2, ← Real.mul_rpow hc0 (inv_nonneg.2 hR.le)]
    exact Real.rpow_le_rpow (inv_nonneg.2 hR'.le) h3 (by linarith)

/-- `exp (1/2) ≤ 2`. -/
private theorem nl_exp_half_le : Real.exp (1 / 2) ≤ 2 := by
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h3 := Real.exp_pos (1 / 2)
  nlinarith

/-- The product of the four factors of the control is at most `2` once `(|C_d| + 2) x + δ ≤ 1/2`:
`(1+x)^{|C_d|} (1+x)^{1/5} (1+x) e^{δ} ≤ exp ((|C_d| + 6/5) x + δ) ≤ exp (1/2) ≤ 2`. -/
private theorem nl_c_le {x δ : ℝ} (Cd : ℝ) (hx : 0 ≤ x)
    (h : (|Cd| + 2) * x + δ ≤ 1 / 2) :
    (1 + x) ^ |Cd| * ((1 + x) ^ (1 / 5 : ℝ) * ((1 + x) * Real.exp δ)) ≤ 2 := by
  have hx1 : (0 : ℝ) ≤ 1 + x := by linarith
  have he : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hp : ∀ p : ℝ, 0 ≤ p → (1 + x) ^ p ≤ Real.exp (x * p) := fun p hp => by
    rw [Real.exp_mul]; exact Real.rpow_le_rpow hx1 he hp
  have h1 := hp |Cd| (abs_nonneg _)
  have h2 := hp (1 / 5) (by norm_num)
  have h0 : (0 : ℝ) ≤ Real.exp δ := (Real.exp_pos _).le
  calc (1 + x) ^ |Cd| * ((1 + x) ^ (1 / 5 : ℝ) * ((1 + x) * Real.exp δ))
      ≤ Real.exp (x * |Cd|) * (Real.exp (x * (1 / 5)) * (Real.exp x * Real.exp δ)) := by
        refine mul_le_mul h1 (mul_le_mul h2 (mul_le_mul he le_rfl h0 (Real.exp_pos _).le)
          (by positivity) (Real.exp_pos _).le) (by positivity) (Real.exp_pos _).le
    _ = Real.exp (x * |Cd| + (x * (1 / 5) + (x + δ))) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_add]
    _ ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 (by nlinarith [abs_nonneg Cd])
    _ ≤ 2 := nl_exp_half_le

/-- **The control of `STStep2Decay` moves by at most a factor `2` under a small time change**
(the Step 2 counterpart of `NetLift:974` `netLift_zeta_ratio`).  The control is
`ζ_u = R_u^{C_d} b_u^{1/5} w_u e_u + W^{-D}` with `R_u = (1-s)/(1-u)`, `b_u = Bctl_u`,
`w_u = STWB_{u,K}`, `e_u = exp(-√(K/ℓ_u))`; each of the first four is within a factor `1 + x`
(`e` within `e^δ`) of its value at `u'`, and `c = (1+x)^{|C_d|} (1+x)^{1/5} (1+x) e^δ ≤ 2`.
The additive term `W^{-D}` is not multiplied: `ζ_{u'} ≤ 2 F_u + W^{-D} ≤ 2 ζ_u`. -/
private theorem nl_zeta_ratio {Cd x δ R R' b b' w w' e e' wd : ℝ} (hx : 0 ≤ x) (hR : 0 < R)
    (hR' : 0 < R') (hRR : R' ≤ (1 + x) * R) (hRR' : R ≤ (1 + x) * R') (hb : 0 ≤ b) (hb'0 : 0 ≤ b')
    (hb' : b' ≤ (1 + x) * b) (hw0 : 0 ≤ w) (hw'0 : 0 ≤ w') (hw' : w' ≤ (1 + x) * w) (he0 : 0 ≤ e)
    (he'0 : 0 ≤ e') (he' : e' ≤ Real.exp δ * e) (hwd : 0 ≤ wd)
    (hc : (1 + x) ^ |Cd| * ((1 + x) ^ (1 / 5 : ℝ) * ((1 + x) * Real.exp δ)) ≤ 2) :
    R' ^ Cd * b' ^ (1 / 5 : ℝ) * w' * e' + wd ≤ 2 * (R ^ Cd * b ^ (1 / 5 : ℝ) * w * e + wd) := by
  have hx1 : (0 : ℝ) ≤ 1 + x := by linarith
  have hR1 : R' ^ Cd ≤ (1 + x) ^ |Cd| * R ^ Cd := nl_rpow_ratio Cd hR hR' (by linarith) hRR hRR'
  have hb1 : b' ^ (1 / 5 : ℝ) ≤ (1 + x) ^ (1 / 5 : ℝ) * b ^ (1 / 5 : ℝ) := by
    rw [← Real.mul_rpow hx1 hb]; exact Real.rpow_le_rpow hb'0 hb' (by norm_num)
  have hRp0 : 0 ≤ R ^ Cd := Real.rpow_nonneg hR.le _
  have hRp'0 : 0 ≤ R' ^ Cd := Real.rpow_nonneg hR'.le _
  have hb0 : 0 ≤ b ^ (1 / 5 : ℝ) := Real.rpow_nonneg hb _
  have hb'p0 : 0 ≤ b' ^ (1 / 5 : ℝ) := Real.rpow_nonneg hb'0 _
  have hF0 : 0 ≤ R ^ Cd * b ^ (1 / 5 : ℝ) * w * e := by positivity
  have hE0 : 0 ≤ Real.exp δ := (Real.exp_pos _).le
  have hpow0 : 0 ≤ (1 + x) ^ |Cd| := Real.rpow_nonneg hx1 _
  have hpow0' : 0 ≤ (1 + x) ^ (1 / 5 : ℝ) := Real.rpow_nonneg hx1 _
  have hmain : R' ^ Cd * b' ^ (1 / 5 : ℝ) * w' * e' ≤
      ((1 + x) ^ |Cd| * ((1 + x) ^ (1 / 5 : ℝ) * ((1 + x) * Real.exp δ))) *
        (R ^ Cd * b ^ (1 / 5 : ℝ) * w * e) := by
    calc R' ^ Cd * b' ^ (1 / 5 : ℝ) * w' * e'
        ≤ ((1 + x) ^ |Cd| * R ^ Cd) * ((1 + x) ^ (1 / 5 : ℝ) * b ^ (1 / 5 : ℝ)) *
            ((1 + x) * w) * (Real.exp δ * e) := by
          refine mul_le_mul (mul_le_mul (mul_le_mul hR1 hb1 hb'p0 (by positivity)) hw' hw'0
            (by positivity)) he' he'0 (by positivity)
      _ = _ := by ring
  calc R' ^ Cd * b' ^ (1 / 5 : ℝ) * w' * e' + wd
      ≤ 2 * (R ^ Cd * b ^ (1 / 5 : ℝ) * w * e) + wd := by
        have := mul_le_mul_of_nonneg_right hc hF0
        linarith
    _ ≤ 2 * (R ^ Cd * b ^ (1 / 5 : ℝ) * w * e + wd) := by linarith

end Scalars

/-! ## 4. The two conclusions of `hclose` at one index `n` -/

section Close

open scoped Matrix.Norms.L2Operator

private theorem nl_STWB_nonneg {d : ℕ} (sz : Sizes d) (n K : ℕ) (u : ℝ) : 0 ≤ STWB sz n u K := by
  unfold STWB Bparam
  positivity

/-- The two conclusions of `hclose` for the family of `STStep2Decay`, at one index `n`,
deterministic: `‖𝓛_u - 𝒦_u‖ ≤ ‖𝓛_{u'} - 𝒦_{u'}‖ + N^{-D}` and `ζ_{u'} ≤ 2 ζ_u`.
`NetLift:1111` (`netLift_T1_close`).  `N = (W L)^d`; the smallness hypotheses `gx`, `gδ`, `g3` are
the eventual numerical facts of `step2NetLift` (`NetLift:1395-1447`). -/
private theorem nl_close {d : ℕ} (sz : Sizes d) (n : ℕ) (ω : sz.SeqΩ) (Cd : ℝ)
    {N E s t u u' D A c₁ Dg : ℝ} (hN : N = ((sz.size n : ℕ) : ℝ)) (hd : 1 ≤ d)
    (hE : |E| < 2) (hs0 : 0 ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (hsu' : s ≤ u') (hu't : u' ≤ t)
    (ht : t < 1) (hc₁ : 0 < c₁) (hc₁m : c₁ ≤ (mE E).im) (hNc : 1 / c₁ ≤ N)
    (hN1 : (1 - t)⁻¹ ≤ N) (hgood : ∀ c : CoordF d (sz.L n) (sz.W n), |sz.slice n ω c| ≤ N)
    (hy : |u - u'| ≤ N ^ (-A)) (hg0 : 0 ≤ sz.lam n) (hgD : sz.lam n ≤ Dg)
    (gx : (|Cd| + 2) * (N * N ^ (-A)) ≤ 1 / 4) (gδ : Real.sqrt (Dg * N ^ (2 - A / 2)) ≤ 1 / 4)
    (g3 : 6 * N ^ (11 - A / 2) + N ^ (2 - A) ≤ N ^ (-D)) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) :
    ‖Lloop sz n E u σ a ω - STKloop sz n E u σ a‖ ≤
        ‖Lloop sz n E u' σ a ω - STKloop sz n E u' σ a‖ + N ^ (-D) ∧
      ((1 - s) / (1 - u')) ^ Cd * (sz.Bctl n u') ^ (1 / 5 : ℝ) *
          STWB sz n u' (zdistInf d (sz.L n) (a 0 - a 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) u') ^ (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-D) ≤
        2 * (((1 - s) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
          STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-D)) := by
  have hN' : N = (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) := hN
  have hNge : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu'0 : 0 ≤ u' := hs0.trans hsu'
  have hu1 : u < 1 := by linarith
  have hu'1 : u' < 1 := by linarith
  have hs1 : s < 1 := by linarith
  have hΔ1 : |u - u'| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hsq : Real.sqrt |u - u'| ≤ N ^ (-A / 2) := cont_sqrt_abs_le hN0.le hy
  have hQ : (etaT E t)⁻¹ ≤ N ^ 2 := nl_eta_inv_le hE hN0 hc₁ hc₁m hNc hN1
  have hQ1 : 1 ≤ N ^ 2 := one_le_pow₀ hNge
  have hcardB : (Fintype.card (Vtx d (sz.L n) (sz.W n)) : ℝ) = N := by
    rw [card_BlockIndex, hN', mul_comm]
  have hXb : ‖blockMat d (sz.L n) (sz.W n) (Xmat d (sz.L n) (sz.W n) (sz.slice n ω))‖ ≤
      2 * N ^ 2 := by
    have h := cont_norm_blockMat_Xmat_le (sz.slice n ω) hgood
    rw [hcardB] at h
    linarith
  refine ⟨?_, ?_⟩
  · -- the additive modulus of `𝓛 - 𝒦`
    have hloop : ‖Lloop sz n E u σ a ω - Lloop sz n E u' σ a ω‖ ≤
        (Fintype.card (Vtx d (sz.L n) (sz.W n)) : ℝ) *
          (((2 : ℕ) : ℝ) * (N ^ 2) ^ 2 *
            (N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1) * Real.sqrt |u - u'|)) :=
      nl_loop_sub (sz.W_pos n) (sz.slice n ω) hE ht hu0 hut hu'0 hu't hΔ1 hQ1 hQ hXb σ a
    rw [hcardB] at hloop
    have hS : N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1) * Real.sqrt |u - u'| ≤
        3 * N ^ 6 * N ^ (-A / 2) := by
      have e1 : N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1) ≤ 3 * N ^ 6 := by
        have : N ^ 4 ≤ N ^ 6 := pow_le_pow_right₀ hNge (by norm_num)
        nlinarith
      exact mul_le_mul e1 hsq (Real.sqrt_nonneg _) (by positivity)
    have hL2 : ‖Lloop sz n E u σ a ω - Lloop sz n E u' σ a ω‖ ≤ 6 * N ^ (11 - A / 2) := by
      refine hloop.trans ?_
      have e : N * (((2 : ℕ) : ℝ) * (N ^ 2) ^ 2 * (3 * N ^ 6 * N ^ (-A / 2))) =
          6 * N ^ (11 - A / 2) := by
        rw [show (11 - A / 2) = ((11 : ℕ) : ℝ) + (-A / 2) by push_cast; ring,
          ← cont_pow_mul_rpow hN0]
        ring
      rw [← e]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS (by positivity)) hN0.le
    have hK : ‖STKloop sz n E u σ a - STKloop sz n E u' σ a‖ ≤ N ^ (2 - A) := by
      have h := nl_K_diff (sz.three_le_L n) (sz.W_pos n) (sz.lam n) hE.le ht hu0 hut hu'0 hu't σ a
      refine h.trans ?_
      have e : N ^ (2 - A) = N * N * N ^ (-A) := by
        rw [show (2 - A) = ((2 : ℕ) : ℝ) + (-A) by push_cast; ring, ← cont_pow_mul_rpow hN0]
        ring
      rw [e]
      exact mul_le_mul (mul_le_mul hN1 hN1 (inv_nonneg.2 h1t.le) hN0.le) hy (abs_nonneg _)
        (by positivity)
    have hsplit : Lloop sz n E u σ a ω - STKloop sz n E u σ a =
        (Lloop sz n E u' σ a ω - STKloop sz n E u' σ a) +
          (Lloop sz n E u σ a ω - Lloop sz n E u' σ a ω) -
          (STKloop sz n E u σ a - STKloop sz n E u' σ a) := by ring
    rw [hsplit]
    refine (norm_sub_le _ _).trans ?_
    have := norm_add_le (Lloop sz n E u' σ a ω - STKloop sz n E u' σ a)
      (Lloop sz n E u σ a ω - Lloop sz n E u' σ a ω)
    linarith
  · -- the control
    set zd : ℕ := zdistInf d (sz.L n) (a 0 - a 1) with hzd
    have hz0 : (0 : ℝ) ≤ (zd : ℝ) := Nat.cast_nonneg _
    have hW1 : (1 : ℝ) ≤ (sz.W n : ℝ) := by exact_mod_cast sz.W_pos n
    have hL1 : (1 : ℝ) ≤ (sz.L n : ℝ) := by
      have := sz.three_le_L n
      exact_mod_cast (by omega : 1 ≤ sz.L n)
    have hzL : (zd : ℝ) ≤ (sz.L n : ℝ) := by
      have : zd ≤ sz.L n := Finset.sup_le fun i _ => zdist_le_L _
      exact_mod_cast this
    have hLN : (sz.L n : ℝ) ≤ N := by
      have hWL1 : (1 : ℝ) ≤ (sz.W n : ℝ) * (sz.L n : ℝ) := one_le_mul_of_one_le_of_one_le hW1 hL1
      have e : N = ((sz.W n : ℝ) * (sz.L n : ℝ)) ^ d := by rw [hN]; simp [Sizes.size]
      rw [e]
      exact (le_mul_of_one_le_left (by positivity) hW1).trans (le_self_pow₀ hWL1 (by omega : d ≠ 0))
    have hzN : (zd : ℝ) ≤ N := hzL.trans hLN
    have hDg0 : 0 ≤ Dg := hg0.trans hgD
    set x : ℝ := N * N ^ (-A) with hxdef
    have hx0 : 0 ≤ x := by positivity
    have hx : (1 - t)⁻¹ * |u - u'| ≤ x := mul_le_mul hN1 hy (abs_nonneg _) hN0.le
    have hx' : (1 - t)⁻¹ * |u' - u| ≤ x := by rw [abs_sub_comm]; exact hx
    have hRR := nl_R_le hs1.le ht hut hu't hx
    have hRR' := nl_R_le hs1.le ht hu't hut hx'
    have hRpos : 0 < (1 - s) / (1 - u) := div_pos (by linarith) (by linarith)
    have hRpos' : 0 < (1 - s) / (1 - u') := div_pos (by linarith) (by linarith)
    have hBu : 0 ≤ sz.Bctl n u :=
      (inv_nonneg.2 (Nat.cast_nonneg _)).trans (cont_inv_size_le_Bctl sz n hu0 hu1)
    have hBu' : 0 ≤ sz.Bctl n u' :=
      (inv_nonneg.2 (Nat.cast_nonneg _)).trans (cont_inv_size_le_Bctl sz n hu'0 hu'1)
    have hb' : sz.Bctl n u' ≤ (1 + x) * sz.Bctl n u :=
      (cont_Bctl_ratio sz n ht hu't hut).trans
        (mul_le_mul_of_nonneg_right (by linarith) hBu)
    have hw' : STWB sz n u' zd ≤ (1 + x) * STWB sz n u zd :=
      (nl_STWB_ratio sz n zd ht hu't hut).trans
        (mul_le_mul_of_nonneg_right (by linarith) (nl_STWB_nonneg sz n zd u))
    -- the exponential factor
    have hexp := nl_exp_ell (L := sz.L n) (by have := sz.three_le_L n; omega) (g := sz.lam n) (t := t) (u := u) (u' := u')
      (z := (zd : ℝ)) hg0 ht hut hu't hz0
    have hδ_in : (zd : ℝ) * (sz.lam n * ((1 - t)⁻¹ * Real.sqrt |u - u'|)) ≤
        Dg * N ^ (2 - A / 2) := by
      have e : N ^ (2 - A / 2) = N * (N * N ^ (-A / 2)) := by
        rw [show (2 - A / 2) = 1 + (1 + (-A / 2)) by ring, Real.rpow_add hN0, Real.rpow_add hN0,
          Real.rpow_one]
      have h1 : (zd : ℝ) * (sz.lam n * ((1 - t)⁻¹ * Real.sqrt |u - u'|)) ≤
          N * (Dg * (N * N ^ (-A / 2))) :=
        mul_le_mul hzN (mul_le_mul hgD (mul_le_mul hN1 hsq (Real.sqrt_nonneg _) hN0.le)
          (by positivity) hDg0) (by positivity) hN0.le
      rw [e]
      linarith
    have hδ : Real.sqrt ((zd : ℝ) * (sz.lam n * ((1 - t)⁻¹ * Real.sqrt |u - u'|))) ≤ 1 / 4 :=
      (Real.sqrt_le_sqrt hδ_in).trans gδ
    have hc := nl_c_le (x := x) (δ := Real.sqrt ((zd : ℝ) * (sz.lam n * ((1 - t)⁻¹ *
      Real.sqrt |u - u'|)))) Cd hx0 (by linarith)
    have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    exact nl_zeta_ratio hx0 hRpos hRpos' hRR hRR' hBu hBu' hb' (nl_STWB_nonneg sz n zd u)
      (nl_STWB_nonneg sz n zd u') hw' (Real.exp_pos _).le (Real.exp_pos _).le hexp hW0 hc

end Close

/-! ## 5. The pinned statements and their proofs -/

section Main

variable {d : ℕ}

/-- `N → ∞` forces `d ≥ 1` (for `d = 0` the scale `N = (W L)^0` is constant). -/
private theorem nl_one_le_d (sz : Sizes d) (h : sz.SizeTendsto) : 1 ≤ d := by
  by_contra hd
  have hd0 : d = 0 := by omega
  subst hd0
  have h1 : ∀ n, ((sz.size n : ℕ) : ℝ) = 1 := fun n => by simp [Sizes.size]
  obtain ⟨n, hn⟩ := (h.eventually_ge_atTop 2).exists
  rw [h1 n] at hn
  norm_num at hn

/-- **The net lift of the decay family of Step 2**: the per-time statement `STStep2DecayPT`
(`(Eq:Gdecay_w)` per time) gives the `u`-uniform one `STStep2Decay`, with the premises `0 < κ`,
`|E n| ≤ 2 - κ`, `0 < τ`, `0 ≤ s ≤ t < 1`, `N → ∞`, `(eq:WO)` and the application range
`RangeCond τ t` (`1 - t ≥ N^{-1+τ}`).  `NetLift:1334` (`Step2NetLift`); the differences with RBM2D's
statement are: `d : Sizes` is `sz : Sizes d`, `Step2DecayPT/Unif` are `STStep2DecayPT/Decay`
(with the constant `C_d`), the arguments `c`, `Bandwidth d c`, `CondStInd d E s t`, which the proof
does not use, are dropped (paper-delta candidate `T2074a`), and `sz.WO 𝔡` is added (paper-delta
candidate `T2074b`): at `d ≥ 3` the control carries `ℓ_u`, which depends on `ĝ` through
`ĝ (1-u)^{-1/2}`, and `ĝ ≤ 𝔡⁻¹` makes it Hölder in `u` with a controlled constant. -/
def Step2NetLift (sz : Sizes d) (E : ℕ → ℝ) (κ τ 𝔡 : ℝ) (s t : ℕ → ℝ) (Cd : ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → 0 < τ → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) →
    (∀ n, t n < 1) → sz.SizeTendsto → sz.WO 𝔡 → sz.RangeCond τ t →
    STStep2DecayPT sz Cd E s t → STStep2Decay sz Cd E s t

/-- **The net lift of `(Eq:Gdecay_w)`**: `STStep2DecayPT → STStep2Decay`.  `NetLift:1387`
(`step2NetLift`).  `cont_core` (`ContinuityNet`) on `TimeIcc s t n × V n` with the good event
`contGood` and the net of mesh `N^{-A-1}`; `V n = {±}² × (Z_L^d)²`, `A = 4 D + 40`,
`#V ≤ 4 N² ≤ N³`, `ε = N^{-D}`. -/
theorem step2NetLift (sz : Sizes d) : ∀ E κ τ 𝔡 s t Cd, Step2NetLift sz E κ τ 𝔡 s t Cd := by
  intro E κ τ 𝔡 s t Cd hκ hE hτ hs0 hst ht1 hsize hWO hRange hPT D hD
  set c₁ : ℝ := Real.sqrt (2 * κ) / 2 with hc₁def
  have hc₁ : 0 < c₁ := by
    rw [hc₁def]
    have := Real.sqrt_pos.2 (by linarith : 0 < 2 * κ)
    linarith
  have hbulk : ∀ n, |E n| < 2 ∧ c₁ ≤ (mE (E n)).im := fun n => cont_bulk hκ (hE n)
  have hlen : ∀ n, t n - s n ≤ 1 := fun n => by linarith [hs0 n, ht1 n]
  have hd1 : 1 ≤ d := nl_one_le_d sz hsize
  set A : ℝ := 4 * D + 40 with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; linarith
  have hcast : Tendsto (fun n : ℕ => ((sz.size n : ℕ) : ℝ)) atTop atTop := hsize
  have hsizeN : Tendsto sz.size atTop atTop := tendsto_natCast_atTop_iff.mp hcast
  -- eventual facts about `N = size n`
  have ev1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hcast.eventually_ge_atTop 1
  have ev4 : ∀ᶠ n : ℕ in atTop, (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hcast.eventually_ge_atTop 4
  have evc : ∀ᶠ n : ℕ in atTop, 1 / c₁ ≤ ((sz.size n : ℕ) : ℝ) :=
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
  have evW : ∀ᶠ n : ℕ in atTop, 0 ≤ sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hWO] with n hn
    have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    exact ⟨(Real.rpow_pos_of_pos hW _).le.trans hn.1, hn.2⟩
  have evgx : ∀ᶠ n : ℕ in atTop, (|Cd| + 2) * (((sz.size n : ℕ) : ℝ) *
      ((sz.size n : ℕ) : ℝ) ^ (-A)) ≤ 1 / 4 := by
    filter_upwards [cont_gap hsizeN (|Cd| + 2) (κ := 1 / 4) (p := 1 - A) (q := 0) (by norm_num)
      (by rw [hAdef]; linarith), ev1] with n hn h1
    have hx0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have : ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-A) =
        ((sz.size n : ℕ) : ℝ) ^ (1 - A) := by
      rw [show (1 - A) = 1 + -A by ring, Real.rpow_add hx0, Real.rpow_one]
    rw [this]
    rw [Real.rpow_zero] at hn
    linarith
  have evgδ : ∀ᶠ n : ℕ in atTop, Real.sqrt (𝔡⁻¹ * ((sz.size n : ℕ) : ℝ) ^ (2 - A / 2)) ≤ 1 / 4 := by
    filter_upwards [cont_gap hsizeN 𝔡⁻¹ (κ := 1 / 16) (p := 2 - A / 2) (q := 0) (by norm_num)
      (by rw [hAdef]; linarith)] with n hn
    rw [Real.rpow_zero] at hn
    exact Real.sqrt_le_iff.2 ⟨by norm_num, by linarith⟩
  have evg3 : ∀ᶠ n : ℕ in atTop,
      6 * ((sz.size n : ℕ) : ℝ) ^ (11 - A / 2) + ((sz.size n : ℕ) : ℝ) ^ (2 - A) ≤
        ((sz.size n : ℕ) : ℝ) ^ (-D) := by
    filter_upwards [cont_gap hsizeN 6 (κ := 1 / 2) (p := 11 - A / 2) (q := -D) (by norm_num)
      (by rw [hAdef]; linarith),
      cont_gap hsizeN 1 (κ := 1 / 2) (p := 2 - A) (q := -D) (by norm_num)
      (by rw [hAdef]; linarith)] with n h1 h2
    linarith
  -- the cardinality of the index sets
  have hcard : ∀ᶠ n : ℕ in atTop,
      (Fintype.card ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) : ℝ) ≤
        ((sz.size n : ℕ) : ℝ) ^ (((3 : ℕ) : ℝ)) := by
    filter_upwards [ev4] with n h4
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have hcardZ : Fintype.card (Zd d (sz.L n)) = sz.L n ^ d := by
      simp [Zd, ZMod.card]
    have hcardV : (Fintype.card ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) : ℝ) =
        4 * (((sz.L n : ℝ)) ^ d) ^ 2 := by
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
      rw [eN]; exact pow_le_pow_left₀ hL0 hLW d
    rw [hcardV, Real.rpow_natCast]
    calc 4 * ((sz.L n : ℝ) ^ d) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ 2 :=
          mul_le_mul h4 (pow_le_pow_left₀ (by positivity) hLN 2) (by positivity) hN0.le
      _ = ((sz.size n : ℕ) : ℝ) ^ 3 := by ring
  refine cont_core (V := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) hsizeN hst hlen
    (A := A) (Cv := ((3 : ℕ) : ℝ)) hA0 (Nat.cast_nonneg _) hcard (hPT D hD)
    (cont_highProbAt_good sz hsizeN)
    (ε := fun n => ((sz.size n : ℕ) : ℝ) ^ (-D))
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) ?_ ?_
  · -- `hlow`
    refine Eventually.of_forall fun n p ω => ?_
    obtain ⟨u, σ, a⟩ := p
    change ((sz.size n : ℕ) : ℝ) ^ (-D) ≤
      ((1 - s n) / (1 - (u : ℝ))) ^ Cd * (sz.Bctl n (u : ℝ)) ^ (1 / 5 : ℝ) *
          STWB sz n (u : ℝ) (zdistInf d (sz.L n) (a 0 - a 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) (u : ℝ)) ^ (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-D)
    have hu1 : (u : ℝ) < 1 := lt_of_le_of_lt u.2.2 (ht1 n)
    have hW1 : (1 : ℝ) ≤ (sz.W n : ℝ) := by exact_mod_cast sz.W_pos n
    have hL1 : (1 : ℝ) ≤ (sz.L n : ℝ) := by
      have := sz.three_le_L n
      exact_mod_cast (by omega : 1 ≤ sz.L n)
    have hWL1 : (1 : ℝ) ≤ (sz.W n : ℝ) * (sz.L n : ℝ) := one_le_mul_of_one_le_of_one_le hW1 hL1
    have eN : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℝ) * (sz.L n : ℝ)) ^ d := by
      simp [Sizes.size]
    have hWN : (sz.W n : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
      rw [eN]
      exact (le_mul_of_one_le_right (by positivity) hL1).trans
        (le_self_pow₀ hWL1 (by omega : d ≠ 0))
    have hwN : ((sz.size n : ℕ) : ℝ) ^ (-D) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hWN (by linarith)
    have hR0 : 0 ≤ (1 - s n) / (1 - (u : ℝ)) :=
      div_nonneg (by linarith [u.2.1, u.2.2, ht1 n]) (by linarith)
    have hB0 : 0 ≤ sz.Bctl n (u : ℝ) :=
      (inv_nonneg.2 (Nat.cast_nonneg _)).trans
        (cont_inv_size_le_Bctl sz n ((hs0 n).trans u.2.1) hu1)
    have h0 : 0 ≤ ((1 - s n) / (1 - (u : ℝ))) ^ Cd * (sz.Bctl n (u : ℝ)) ^ (1 / 5 : ℝ) *
          STWB sz n (u : ℝ) (zdistInf d (sz.L n) (a 0 - a 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) (u : ℝ)) ^ (1 / 2 : ℝ)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hR0 _) (Real.rpow_nonneg hB0 _))
        (nl_STWB_nonneg sz n _ _)) (Real.exp_pos _).le
    linarith
  · -- `hclose`
    filter_upwards [evc, evR, evW, evgx, evgδ, evg3] with n hc hR hW gx gδ g3
    intro ω hω u u' hΔ v
    obtain ⟨σ, a⟩ := v
    exact nl_close sz n ω Cd (N := ((sz.size n : ℕ) : ℝ)) (E := E n) (s := s n) (t := t n)
      (u := u) (u' := u') (D := D) (A := A) (c₁ := c₁) (Dg := 𝔡⁻¹) rfl hd1 (hbulk n).1 (hs0 n)
      u.2.1 u.2.2 u'.2.1 u'.2.2 (ht1 n) hc₁ (hbulk n).2 hc hR (fun c => hω c) hΔ hW.1 hW.2
      gx gδ g3 σ a

end Main

end RBM.Ind

namespace RBM.Gauss.Sizes

open RBM.Ind

set_option linter.style.longLine false

/-- **The net lift of Step 2, part 1 (the decay family; ST2-18)**: the third conjunct of the pin
`STNetLift2` (`Induction/Step2Defs.lean`), with its quantifiers and premises (`κ, ε, 𝔡`, `𝔠`, `sz`,
`z`, `STFlow`, `0 ≤ s ≤ t ≤ lemT z`, `C_d`) and the third per-time hypothesis alone:
`STStep2DecayPT → STStep2Decay`.  The other two conjuncts (`STStep2Local`, `STStep2Avg`) are ST2-19.
Proof: `STFlow` with `t ≤ lemT z` gives the premises of `step2NetLift`
(`Green.v3_premises_of_stFlow`: `|E_n| < 2 - κ/2`, `t_n < 1`, `1 - t_n ≥ N^{-1+ε/2}`, `N → ∞` and
`(eq:WO)` from `Admissible`), at `κ/2`, `τ = ε/2`. -/
theorem stNetLift2_part1 (d : ℕ) :
    ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
          ∀ Cd : ℝ, STStep2DecayPT sz Cd (STflowE z) s t → STStep2Decay sz Cd (STflowE z) s t := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s t hs0 hst ht Cd hPT
  obtain ⟨hA, hE, hlt, hR⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow ht
  exact step2NetLift sz (STflowE z) (κ / 2) (ε / 2) 𝔡 s t Cd (half_pos hκ)
    (fun n => (hE n).le) (half_pos hε) hs0 hst hlt hA.2.2.1 hA.2.2.2.2 hR hPT

end RBM.Gauss.Sizes

namespace RBM.Ind

set_option linter.style.longLine false

/-! ## 6. Compiled nonempty instances at `d = 3`

The size data are the merged preflight sequence `RBM.Gauss.SizesInst.sz0` (`L_n = 4(n+1)`,
`W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6} → 0`, `N_n = (W_n L_n)^3`; `n = 0`: `L = 4`, `W = 32`,
`N = 2097152`), admissible at `𝔠 = 1/6`, `𝔡 = 1/10`; the flow points `z_n = 1/2 + i N_n^{-4/5}`
(`κ = ε = 1/10`, `E_n = lemE z_n`, `|E_n| ≤ 1/2`), `s ≡ 0`, `t ≡ 1/16 ≤ t₀ = lemT z_n`
(`RBM3D/Induction/Defs.lean`, section 3).  Every deterministic hypothesis is discharged; what stays
a hypothesis is the per-time statement `STStep2DecayPT` itself (the stochastic input of ST2-04),
at an arbitrary constant `C_d`. -/

section Instances

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst

/-- `Step2NetLift` at the flow of the instance (`κ = τ = (1/10)/2`, `𝔡 = 1/10`, `s ≡ 0`,
`t ≡ 1/16`): `step2NetLift` applies for every `C_d`. -/
example (Cd : ℝ) : Step2NetLift sz0 (STflowE z0) ((1 / 10) / 2) ((1 / 10) / 2) (1 / 10) sInst tInst Cd :=
  step2NetLift sz0 _ _ _ _ _ _ _

/-- `step2NetLift`, fully applied: every hypothesis (`0 < κ`, `|E_n| ≤ 2 - κ`, `0 < τ`,
`0 ≤ s ≤ t < 1`, `N → ∞`, `(eq:WO)`, `RangeCond`) is discharged; the per-time family
`STStep2DecayPT` stays the hypothesis of the implication. -/
example (Cd : ℝ) (hD : STStep2DecayPT sz0 Cd (STflowE z0) sInst tInst) :
    STStep2Decay sz0 Cd (STflowE z0) sInst tInst :=
  step2NetLift sz0 (STflowE z0) ((1 / 10) / 2) ((1 / 10) / 2) (1 / 10) sInst tInst Cd
    (by norm_num) (fun n => (RBM.Green.Instance.premises.2.1 n).le) (by norm_num) (fun _ => le_rfl)
    (fun n => by simp only [sInst, tInst]; norm_num) RBM.Green.Instance.premises.2.2.2.1
    sz0_tendsto flow_z0.1.2.2.2.2 RBM.Green.Instance.premises.2.2.2.2 hD

/-- `stNetLift2_part1` at `d = 3`: `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `sz0`, `z0`, `STFlow`
(`flow_z0`), `0 ≤ s ≤ t ≤ lemT z_n` (`sixteenth_le_lemT`). -/
example (Cd : ℝ) (hD : STStep2DecayPT sz0 Cd (STflowE z0) sInst tInst) :
    STStep2Decay sz0 Cd (STflowE z0) sInst tInst :=
  stNetLift2_part1 3 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 sInst tInst (fun _ => le_rfl)
    (fun n => by simp only [sInst, tInst]; norm_num) (fun n => sixteenth_le_lemT n) Cd hD

end Instances

end RBM.Ind
