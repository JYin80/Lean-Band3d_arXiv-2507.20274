/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.ContinuityNet
import RBM3D.Induction.Defs
import RBM3D.Green.Pins

/-!
# Continuity of the Green function in time, part 2: `gopbound`, the net lift `step1NetLift` and
the pin `STNetLift` (ST-1, ticket S1-34 = T2062)

Port of the second part (lines 765-1464) of `RBM2D/Induction/Continuity.lean` at commit `c9a24cf`
(cited `Continuity:line`), onto the merged MD layer and the merged ST-1 files.  The first part
(lines 1-764: `GopboundPin`, `cont_core`, the good event, the resolvent and flow moduli, the
scalar facts about `Bctl`) is `RBM3D/Induction/ContinuityNet.lean` (T2047), imported and not
copied.

* `gopbound` (`Continuity:1269`): the pin `GopboundPin sz κ E`, any `d`.
* `Step1NetLift`, `step1NetLift` (`Continuity:1261`, `:1331`): the net lift of the two Step 1
  families, per time to uniform in `u ∈ [s,t]`: `STStep1LoopPT → STStep1Loop` and
  `STStep1WeakPT → STStep1Weak`.
* `stNetLift_holds : STNetLift d` (the merged pin of `RBM3D/Induction/Defs.lean`): `step1NetLift`
  together with the diagonal step (`perTime_of_sections`): the hypothesis of `STNetLift` is `≺`
  at every time *sequence* `u` with the union over `(σ, a)` inside `P`, which gives the per-time
  statement over `TimeIcc s t n × (σ, a)`; and `STFlow` with `t ≤ lemT z` gives the premises of
  `step1NetLift` (`Green.v3_premises_of_stFlow`: `|E_n| < 2 - κ/2`, `t_n < 1`,
  `1 - t_n ≥ N^{-1+ε/2}`).

Renaming (`docs/tickets/ST1-COMMON.md` item 2): `d : Sizes` becomes `sz : Sizes d`, `Z2 L` becomes
`Zd d L`, `Idx L W` becomes `Idx d L W`, `(W L)^2` becomes `(W L)^d = sz.size n`, `Gsig` is `Gres`,
`BlockIndex` is `Vtx`, `spectralM`, `spectralZ` are `mE`, `zt`, `loopAbs` is `‖loopFine …‖`
(`Lloop`), `llErrMat` is the entry of `STGM`.  The `d = 2` controls `scaleM`, `ellT` do not exist
at `d ≥ 3`: the controls are `((1-s)/(1-u))^{k-1} (W^{-d} B_{s,0})^{k-1}` (`STStep1Loop`) and
`(W^{-d} B_{u,0})^{1/4}` (`STStep1Weak`); the lemmas that use them are `cont_LP_zeta_ratio`,
`cont_LP_low`, `cont_WL_low`, `cont_WL_close` below (on top of `ContinuityNet.cont_Bctl_ratio`,
`cont_inv_size_le_Bctl`, `cont_inv_add_one_sub_ratio`).

`Bandwidth` and `CondStInd` of RBM2D's `Step1NetLift` are unused by its proof (RBM2D paper-delta
candidate `T2070b`) and are dropped; `RangeCond` is the merged `Sizes.RangeCond`.  Section 5 holds
the compiled instances at the merged size data `sz0` (`d = 3`).
-/

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path
  RBM.Ind.ContinuityNet
open scoped NNReal ENNReal

set_option linter.style.longLine false

/-! ## 1. Deterministic estimates along the flow -/

section Flow

open scoped Matrix.Norms.L2Operator

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The entry modulus of the resolvent along the flow (`Gopboundu`, 5-6:13–16): if
`‖X‖ ≤ Xb`, `u, u' ≤ t < 1`, `|u - u'| ≤ 1` and `(η_t)⁻¹ ≤ Q`, then
`‖G_u - G_{u'}‖_max ≤ Q² (Xb + 1) |u - u'|^{1/2}`.  `Continuity:776` (`cont_entry_diff`). -/
private theorem cont_entry_diff (ω : Ω d L W) {E t u u' Q Xb : ℝ} (hE : |E| < 2) (ht : t < 1)
    (hu0 : 0 ≤ u) (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t) (hΔ : |u - u'| ≤ 1)
    (hQ : (etaT E t)⁻¹ ≤ Q) (hX : ‖Xmat d L W ω‖ ≤ Xb) (i j : Idx d L W) :
    ‖(Hflow d L W u ω - zt E u • (1 : Matrix (Idx d L W) (Idx d L W) ℂ))⁻¹ i j -
        (Hflow d L W u' ω - zt E u' • (1 : Matrix (Idx d L W) (Idx d L W) ℂ))⁻¹ i j‖ ≤
      Q * Q * (Xb + 1) * Real.sqrt |u - u'| := by
  have hη : 0 < etaT E t := etaT_pos hE ht
  have hG := cont_green_flow_diff (Hflow_isHermitian d L W u ω) (Hflow_isHermitian d L W u' ω)
    (Hflow_sub d L W u u' ω) hX (cont_abs_sqrt_sub_sqrt_le hu0 hu'0) (abs_nonneg _) hΔ hη hQ
    (cont_eta_le_abs_im hE ht hut) (cont_eta_le_abs_im hE ht hu't)
    (cont_norm_spectralZ_sub hE.le u u').le
  have hent := norm_matrix_entry_le_opNorm
    (green (Hflow d L W u ω) (zt E u) - green (Hflow d L W u' ω) (zt E u')) i j
  have h3 : (green (Hflow d L W u ω) (zt E u) -
        green (Hflow d L W u' ω) (zt E u')) i j =
      (Hflow d L W u ω - zt E u • (1 : Matrix (Idx d L W) (Idx d L W) ℂ))⁻¹ i j -
        (Hflow d L W u' ω - zt E u' • (1 : Matrix (Idx d L W) (Idx d L W) ℂ))⁻¹ i j := by
    simp [green, Matrix.sub_apply]
  rw [h3] at hent
  exact hent.trans hG

/-- The resolvent word `∏ᵢ G(σᵢ) E_{aᵢ}` over a list of `(σᵢ, aᵢ)` (the `foldr` of `loopL`).
`Continuity:809` (`contWord`). -/
private noncomputable def contWord (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (l : List (Bool × Zd d L)) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1

omit [NeZero W] in
/-- `Continuity:814` (`contWord_cons`). -/
private theorem contWord_cons (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (p : Bool × Zd d L) (l : List (Bool × Zd d L)) :
    contWord H z (p :: l) = Gres H z p.1 * Eblk d L W p.2 * contWord H z l := rfl

/-- `Continuity:818` (`cont_word_norm`). -/
private theorem cont_word_norm (hW : 1 ≤ W) {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    {z : ℂ} {Q : ℝ} (hQ : ∀ σ, ‖Gres H z σ‖ ≤ Q) (l : List (Bool × Zd d L)) :
    ‖contWord H z l‖ ≤ Q ^ l.length := by
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hQ true)
  induction l with
  | nil => simp [contWord]
  | cons p l ih =>
    have hEa := cont_norm_Eblk_le_one (d := d) (L := L) hW p.2
    rw [contWord_cons, List.length_cons, pow_succ]
    calc ‖Gres H z p.1 * Eblk d L W p.2 * contWord H z l‖
        ≤ ‖Gres H z p.1‖ * ‖Eblk d L W p.2‖ * ‖contWord H z l‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ Q * 1 * Q ^ l.length :=
          mul_le_mul (mul_le_mul (hQ _) hEa (norm_nonneg _) hQ0) ih (norm_nonneg _) (by positivity)
      _ = Q ^ l.length * Q := by ring

/-- The `k`-fold telescoping of a resolvent word: port of RBM1D `norm_gchain_sub_le`
(`Gauss/Step1Hyp.lean:517` at `86573b9`) to the block matrices of `d ≥ 3`.
`Continuity:836` (`cont_word_diff`). -/
private theorem cont_word_diff (hW : 1 ≤ W)
    {H H' : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z z' : ℂ} {Q S : ℝ} (hQ1 : 1 ≤ Q)
    (hQ : ∀ σ, ‖Gres H z σ‖ ≤ Q) (hQ' : ∀ σ, ‖Gres H' z' σ‖ ≤ Q)
    (hS : ∀ σ, ‖Gres H z σ - Gres H' z' σ‖ ≤ S) (l : List (Bool × Zd d L)) :
    ‖contWord H z l - contWord H' z' l‖ ≤ (l.length : ℝ) * Q ^ l.length * S := by
  have hQ0 : 0 ≤ Q := by linarith
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS true)
  induction l with
  | nil => simp [contWord]
  | cons p l ih =>
    have hEa := cont_norm_Eblk_le_one (d := d) (L := L) hW p.2
    rw [contWord_cons, contWord_cons]
    have key : Gres H z p.1 * Eblk d L W p.2 * contWord H z l -
        Gres H' z' p.1 * Eblk d L W p.2 * contWord H' z' l =
        (Gres H z p.1 - Gres H' z' p.1) * Eblk d L W p.2 * contWord H z l +
          Gres H' z' p.1 * Eblk d L W p.2 * (contWord H z l - contWord H' z' l) := by
      noncomm_ring
    rw [key]
    have hP := cont_word_norm hW hQ l
    have t1 : ‖(Gres H z p.1 - Gres H' z' p.1) * Eblk d L W p.2 * contWord H z l‖ ≤
        S * 1 * Q ^ l.length := by
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul (hS _) hEa (norm_nonneg _) hS0)) hP
        (norm_nonneg _) (by positivity)
    have t2 : ‖Gres H' z' p.1 * Eblk d L W p.2 * (contWord H z l - contWord H' z' l)‖ ≤
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

/-- The loop `loopFine` is the trace of the `contWord` of the block matrix. -/
private theorem cont_loopFine_eq (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    loopFine d L W H z σ a =
      Matrix.trace (contWord (blockMat d L W H) z ((List.ofFn σ).zip (List.ofFn a))) := by
  unfold loopFine
  rw [loopM_eq_loopL]
  rfl

/-- The modulus of a loop of length `k` along the flow, on `‖X‖ ≤ Xb` (`Gopboundu` and the net
argument of 5-6:16; RBM1D `norm_gloop_sub_le`, `Gauss/Step1Hyp.lean:571` at `86573b9`, for the
block matrices of `d ≥ 3`; the trace is bounded by `card(Vtx) · ‖·‖`).
`Continuity:877` (`cont_loopAbs_diff`), `loopAbs` is `‖loopFine …‖`. -/
private theorem cont_loopAbs_diff (hW : 1 ≤ W) (ω : Ω d L W) {E t u u' Q Xb : ℝ} (hE : |E| < 2)
    (ht : t < 1) (hu0 : 0 ≤ u) (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t)
    (hΔ : |u - u'| ≤ 1) (hQ1 : 1 ≤ Q) (hQ : (etaT E t)⁻¹ ≤ Q)
    (hXb : ‖blockMat d L W (Xmat d L W ω)‖ ≤ Xb) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d L) :
    |‖loopFine d L W (Hflow d L W u ω) (zt E u) σ a‖ -
        ‖loopFine d L W (Hflow d L W u' ω) (zt E u') σ a‖| ≤
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
  have hw := cont_word_diff hW hQ1 hGu hGu' hS ((List.ofFn σ).zip (List.ofFn a))
  have hlen : ((List.ofFn σ).zip (List.ofFn a)).length = k := by simp
  rw [hlen] at hw
  rw [cont_loopFine_eq, cont_loopFine_eq]
  refine (abs_norm_sub_norm_le _ _).trans ?_
  rw [← Matrix.trace_sub]
  refine (norm_matrix_trace_le_card_mul _).trans ?_
  exact mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)

end Flow

/-! ## 2. The control ratios and the closeness statements for the two families -/

section Close

open scoped Matrix.Norms.L2Operator

/-- `(1 + x)^m ≤ 1 + 2 m x` when `m x ≤ 1/2`.  `Continuity:956` (`cont_one_add_pow_le`). -/
private theorem cont_one_add_pow_le {x : ℝ} (hx : 0 ≤ x) (m : ℕ) (hm : (m : ℝ) * x ≤ 1 / 2) :
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

/-- **The control of `STStep1Loop` moves by at most a factor `2` under a small time change.**
`ζ_u = ((1-s)/(1-u))^{k-1} B^{k-1}` with `B = W^{-d} B_{s,0}` independent of `u`;
`(1-s)/(1-u') ≤ (1 + x) (1-s)/(1-u)` for `(1-t)⁻¹ |u-u'| ≤ x`, so `ζ_{u'} ≤ (1 + x)^{k-1} ζ_u`.
New at `d ≥ 3` (replaces `Continuity:973` `cont_LP_zeta_ratio`, whose control was
`(ℓ_u/ℓ_s)^{2(k-1)} M_u^{-(k-1)}`); the ratio of `(1-u)⁻¹` is `cont_inv_add_one_sub_ratio`. -/
private theorem cont_LP_zeta_ratio {s t u u' x B : ℝ} (k : ℕ) (hB : 0 ≤ B) (hsu : s ≤ u)
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
    have := cont_one_add_pow_le hx0 (k - 1) hk
    nlinarith
  have hζ0 : 0 ≤ ((1 - s) / (1 - u)) ^ (k - 1) * B ^ (k - 1) := by positivity
  calc ((1 - s) / (1 - u')) ^ (k - 1) * B ^ (k - 1)
      ≤ ((1 + x) ^ (k - 1) * ((1 - s) / (1 - u)) ^ (k - 1)) * B ^ (k - 1) :=
        mul_le_mul_of_nonneg_right hA (by positivity)
    _ = (1 + x) ^ (k - 1) * (((1 - s) / (1 - u)) ^ (k - 1) * B ^ (k - 1)) := by ring
    _ ≤ 2 * (((1 - s) / (1 - u)) ^ (k - 1) * B ^ (k - 1)) :=
        mul_le_mul_of_nonneg_right hpow hζ0

/-- `ε ≤ ζ` for `STStep1Loop`: `(1-s)/(1-u) ≥ 1` and `Bctl n s ≥ N⁻¹` give `N^{-k} ≤ ζ_u`.
New at `d ≥ 3` (replaces `Continuity:1130` `cont_LP_low`, which used `ℓ_u ≥ ℓ_s`, `M_u ≤ N`). -/
private theorem cont_LP_low {d : ℕ} (sz : Sizes d) (n k : ℕ) {s u : ℝ} (hs0 : 0 ≤ s)
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

/-- `ε ≤ ζ` for `STStep1Weak`: `Bctl n u ≥ N⁻¹` gives `N^{-1/4} ≤ Bctl(u)^{1/4}`.  New at `d ≥ 3`
(replaces `Continuity:1057` `cont_WL_low`, `M_u ≤ N`). -/
private theorem cont_WL_low {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu : u < 1) :
    ((((sz.size n : ℕ) : ℝ))⁻¹) ^ ((1 : ℝ) / 4) ≤ (sz.Bctl n u) ^ ((1 : ℝ) / 4) :=
  Real.rpow_le_rpow (inv_nonneg.2 (Nat.cast_nonneg _)) (cont_inv_size_le_Bctl sz n hu0 hu)
    (by norm_num)

/-- The eventual numerical facts for a fixed loop length `k`, in `N` (exponent `A = 6k + 16`);
`Continuity:1153` (`cont_LP_eventually`) without `gB`, which was needed only for the `ℓ` factor of
the `d = 2` control. -/
private theorem cont_LP_eventually (k : ℕ) :
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

/-- `(η_t)⁻¹ ≤ N²` from `(1 - t)⁻¹ ≤ N`, `Im m ≥ c₁` and `1/c₁ ≤ N`.  `Continuity:1044`
(`cont_eta_inv_le`). -/
private theorem cont_eta_inv_le {E t N c₁ : ℝ} (hE : |E| < 2) (hN0 : 0 < N) (hc₁ : 0 < c₁)
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

section LPClose

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The two conclusions of `hclose` for the loop family of `STStep1Loop`, at one index `n`,
deterministic: `‖𝓛_u‖ ≤ ‖𝓛_{u'}‖ + N^{-k}` and `ζ_{u'} ≤ 2 ζ_u`.  `Continuity:1188`
(`cont_LP_close`), the `ζ` ratio being `cont_LP_zeta_ratio`. -/
private theorem cont_LP_close (hW : 1 ≤ W) (ω : Ω d L W)
    {N E s t u u' c₁ B : ℝ} {k : ℕ} (hN : N = (((W * L) ^ d : ℕ) : ℝ))
    (hE : |E| < 2) (hB : 0 ≤ B) (hs0 : 0 ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (hsu' : s ≤ u')
    (hu't : u' ≤ t) (ht : t < 1) (hc₁ : 0 < c₁) (hc₁m : c₁ ≤ (mE E).im) (hNc : 1 / c₁ ≤ N)
    (hN1 : (1 - t)⁻¹ ≤ N) (hgood : ∀ c : CoordF d L W, |ω c| ≤ N)
    (hy : |u - u'| ≤ N ^ (-(6 * (k : ℝ) + 16)))
    (g1 : 1 ≤ N) (g2 : 6 * (k : ℝ) ≤ N)
    (gA : N * N ^ (-(6 * (k : ℝ) + 16)) ≤ N⁻¹)
    (gC : N * ((k : ℝ) * (N ^ 2) ^ k * (3 * N ^ 6 * N ^ (-(6 * (k : ℝ) + 16) / 2))) ≤ (N⁻¹) ^ k)
    (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    ‖loopFine d L W (Hflow d L W u ω) (zt E u) σ a‖ ≤
        ‖loopFine d L W (Hflow d L W u' ω) (zt E u') σ a‖ + (N⁻¹) ^ k ∧
      ((1 - s) / (1 - u')) ^ (k - 1) * B ^ (k - 1) ≤
        2 * (((1 - s) / (1 - u)) ^ (k - 1) * B ^ (k - 1)) := by
  have hN0 : 0 < N := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu'0 : 0 ≤ u' := hs0.trans hsu'
  have hΔ1 : |u - u'| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hsq : Real.sqrt |u - u'| ≤ N ^ (-(6 * (k : ℝ) + 16) / 2) := cont_sqrt_abs_le hN0.le hy
  have hQ : (etaT E t)⁻¹ ≤ N ^ 2 := cont_eta_inv_le hE hN0 hc₁ hc₁m hNc hN1
  have hQ1 : 1 ≤ N ^ 2 := one_le_pow₀ g1
  have hcardB : (Fintype.card (Vtx d L W) : ℝ) = N := by
    rw [card_BlockIndex, hN, mul_comm]
  have hXb : ‖blockMat d L W (Xmat d L W ω)‖ ≤ 2 * N ^ 2 := by
    have h := cont_norm_blockMat_Xmat_le ω hgood
    rw [hcardB] at h
    linarith
  have hloop := cont_loopAbs_diff hW ω hE ht hu0 hut hu'0 hu't hΔ1 hQ1 hQ hXb σ a
  rw [hcardB] at hloop
  refine ⟨?_, ?_⟩
  · have hS : N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1) * Real.sqrt |u - u'| ≤
        3 * N ^ 6 * N ^ (-(6 * (k : ℝ) + 16) / 2) := by
      have e1 : N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1) ≤ 3 * N ^ 6 := by
        have : N ^ 4 ≤ N ^ 6 := pow_le_pow_right₀ g1 (by norm_num)
        nlinarith
      exact mul_le_mul e1 hsq (Real.sqrt_nonneg _) (by positivity)
    have hbound : |‖loopFine d L W (Hflow d L W u ω) (zt E u) σ a‖ -
        ‖loopFine d L W (Hflow d L W u' ω) (zt E u') σ a‖| ≤
        N * ((k : ℝ) * (N ^ 2) ^ k * (3 * N ^ 6 * N ^ (-(6 * (k : ℝ) + 16) / 2))) :=
      hloop.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hS (by positivity)) hN0.le)
    have := (abs_le.1 (hbound.trans gC)).2
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
    exact cont_LP_zeta_ratio k hB hsu hut hu't ht hx0 hx1 hk

end LPClose

/-- `STGM` is the `(x, y)` entry of the resolvent of the flow, minus `m(E)` on the diagonal. -/
private theorem cont_STGM_eq {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (ω : sz.SeqΩ)
    (x y : Idx d (sz.L n) (sz.W n)) :
    STGM sz n E u ω x y =
      (Hflow d (sz.L n) (sz.W n) u (sz.slice n ω) -
          zt E u • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))⁻¹ x y -
        (if x = y then mE E else 0) := by
  unfold STGM Gt
  rw [cont_Gres_true_eq_green]
  rfl

/-- The two conclusions of `hclose` for the weak-law family of `STStep1Weak`, at one index `n`,
deterministic: `‖G_u - M‖_{xy} ≤ ‖G_{u'} - M‖_{xy} + N^{-1/4}` and
`Bctl(u')^{1/4} ≤ 2 Bctl(u)^{1/4}`.  `Continuity:1065` (`cont_WL_close`), with `llErrMat` read as
the entry of `STGM`; the ratio of the controls is `ContinuityNet.cont_Bctl_ratio`
(`1 + N |u-u'| ≤ 11/10`, `(11/10)^{1/4} ≤ 2`). -/
private theorem cont_WL_close {d : ℕ} (sz : Sizes d) (n : ℕ) (ω : sz.SeqΩ)
    {N E t u u' A c₁ : ℝ} (hN : N = ((sz.size n : ℕ) : ℝ)) (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t) (ht : t < 1)
    (hc₁ : 0 < c₁) (hc₁m : c₁ ≤ (mE E).im) (hNc : 1 / c₁ ≤ N) (hN1 : (1 - t)⁻¹ ≤ N)
    (hgood : ∀ c : CoordF d (sz.L n) (sz.W n), |sz.slice n ω c| ≤ N)
    (hy : |u - u'| ≤ N ^ (-A)) (g2 : N * N ^ (-A) ≤ 1 / 10)
    (g3 : 3 * N ^ 6 * N ^ (-A / 2) ≤ (N⁻¹) ^ ((1 : ℝ) / 4)) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖STGM sz n E u ω x y‖ ≤ ‖STGM sz n E u' ω x y‖ + (N⁻¹) ^ ((1 : ℝ) / 4) ∧
      (sz.Bctl n u') ^ ((1 : ℝ) / 4) ≤ 2 * (sz.Bctl n u) ^ ((1 : ℝ) / 4) := by
  have hNge : (1 : ℝ) ≤ N := by
    rw [hN]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hΔ1 : |u - u'| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hsq : Real.sqrt |u - u'| ≤ N ^ (-A / 2) := cont_sqrt_abs_le hN0.le hy
  have hQ : (etaT E t)⁻¹ ≤ N ^ 2 := cont_eta_inv_le hE hN0 hc₁ hc₁m hNc hN1
  have hcardI : (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) = N := by
    rw [sz.card_Idx n, hN]
  have hX : ‖Xmat d (sz.L n) (sz.W n) (sz.slice n ω)‖ ≤ 2 * N ^ 2 := by
    have h := cont_norm_Xmat_le (sz.slice n ω) hgood
    rw [hcardI] at h
    linarith
  have hent := cont_entry_diff (sz.slice n ω) (Q := N ^ 2) (Xb := 2 * N ^ 2) hE ht hu0 hut hu'0
    hu't hΔ1 hQ hX x y
  have hs0' : 0 ≤ Real.sqrt |u - u'| := Real.sqrt_nonneg _
  have hN4 : N ^ 4 ≤ N ^ 6 := pow_le_pow_right₀ hNge (by norm_num)
  have hbound : ‖(Hflow d (sz.L n) (sz.W n) u (sz.slice n ω) -
          zt E u • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))⁻¹ x y -
        (Hflow d (sz.L n) (sz.W n) u' (sz.slice n ω) -
          zt E u' • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))⁻¹ x y‖ ≤
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
  · have hdiff : STGM sz n E u ω x y - STGM sz n E u' ω x y =
        (Hflow d (sz.L n) (sz.W n) u (sz.slice n ω) -
          zt E u • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))⁻¹ x y -
        (Hflow d (sz.L n) (sz.W n) u' (sz.slice n ω) -
          zt E u' • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))⁻¹ x y := by
      rw [cont_STGM_eq, cont_STGM_eq, sub_sub_sub_cancel_right]
    have habs := abs_norm_sub_norm_le (STGM sz n E u ω x y) (STGM sz n E u' ω x y)
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

/-! ## 3. The pinned statements and their proofs -/

section Main

open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

/-- **Continuity of the Green function in time** (`Gopboundu`, 5-6:13–16 of the `d = 2` paper; no
statement in the `d ≥ 3` paper, paper-delta T2015e): the pin `GopboundPin` of `ContinuityNet`, for
every `d` (the proof uses `d` only through `card Idx = N = (W L)^d`).  `C' = 2 C + 14`: on the good
event `‖X‖ ≤ 2 N²`, `‖G_u - G_{u'}‖_max ≤ 3 N⁶ |u-u'|^{1/2} ≤ 3 N⁶ N^{-C'/2} = 3 N^{-1} N^{-C} ≤
N^{-C}`.  `Continuity:1269` (`gopbound`). -/
theorem gopbound (sz : Sizes d) (κ : ℝ) (E : ℕ → ℝ) : GopboundPin sz κ E := by
  intro hκ hE hsize C hC
  refine ⟨2 * C + 14, by linarith, fun D hD => ?_⟩
  set c₁ : ℝ := Real.sqrt (2 * κ) / 2 with hc₁def
  have hc₁ : 0 < c₁ := by
    rw [hc₁def]
    have := Real.sqrt_pos.2 (by linarith : 0 < 2 * κ)
    linarith
  have hbulk : ∀ n, |E n| < 2 ∧ c₁ ≤ (mE (E n)).im := fun n => cont_bulk hκ (hE n)
  have hcast : Tendsto (fun n : ℕ => ((sz.size n : ℕ) : ℝ)) atTop atTop := hsize
  filter_upwards [hcast.eventually_ge_atTop (max 3 (1 / c₁)),
    hcast.eventually (cont_eventually_tail D)] with n hn htail
  have h3 : (3 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := (le_max_left _ _).trans hn
  have hc : 1 / c₁ ≤ ((sz.size n : ℕ) : ℝ) := (le_max_right _ _).trans hn
  refine le_trans (measure_mono ?_) ((cont_good_compl sz n).trans (ENNReal.ofReal_le_ofReal htail))
  rintro ω ⟨u, u', hu0, hu'0, hut, hu't, hΔ, i, j, hbad⟩
  by_contra hng
  have hgood : ∀ c : CoordF d (sz.L n) (sz.W n), |ω ⟨n, c⟩| ≤ ((sz.size n : ℕ) : ℝ) := by
    simpa [contGood] using hng
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  have ht1 : 1 - N⁻¹ < 1 := by have := inv_pos.2 hN0; linarith
  have hΔ1 : |u - u'| ≤ 1 := abs_le.2 ⟨by linarith [inv_pos.2 hN0], by linarith [inv_pos.2 hN0]⟩
  have hN1 : (1 - (1 - N⁻¹))⁻¹ ≤ N := by
    rw [sub_sub_cancel, inv_inv]
  have hQ : (etaT (E n) (1 - N⁻¹))⁻¹ ≤ N ^ 2 :=
    cont_eta_inv_le (hbulk n).1 hN0 hc₁ (hbulk n).2 hc hN1
  have hcardI : (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) = N := by
    rw [sz.card_Idx n]
  have hX : ‖Xmat d (sz.L n) (sz.W n) (sz.slice n ω)‖ ≤ 2 * N ^ 2 := by
    have h := cont_norm_Xmat_le (sz.slice n ω) hgood
    rw [hcardI] at h
    linarith
  have key := cont_entry_diff (sz.slice n ω) (Q := N ^ 2) (Xb := 2 * N ^ 2) (hbulk n).1 ht1
    hu0 hut hu'0 hu't hΔ1 hQ hX i j
  have hsq : Real.sqrt |u - u'| ≤ N ^ (-(2 * C + 14) / 2) := cont_sqrt_abs_le hN0.le hΔ
  have hN6 : N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1) ≤ 3 * N ^ 6 := by
    have hN1' : (1 : ℝ) ≤ N := by linarith
    have : N ^ 4 ≤ N ^ 6 := pow_le_pow_right₀ hN1' (by norm_num)
    nlinarith
  have hexp : 3 * N ^ 6 * N ^ (-(2 * C + 14) / 2) ≤ N ^ (-C) := by
    have e1 : N ^ 6 * N ^ (-(2 * C + 14) / 2) = N ^ (-C) * N⁻¹ := by
      rw [cont_pow_mul_rpow hN0 6 _, ← Real.rpow_neg_one, ← Real.rpow_add hN0]
      congr 1
      push_cast
      ring
    have hp : 0 ≤ N ^ (-C) := Real.rpow_nonneg hN0.le _
    calc 3 * N ^ 6 * N ^ (-(2 * C + 14) / 2) = 3 * (N ^ 6 * N ^ (-(2 * C + 14) / 2)) := by ring
      _ = (3 * N⁻¹) * N ^ (-C) := by rw [e1]; ring
      _ ≤ 1 * N ^ (-C) := by
          refine mul_le_mul_of_nonneg_right ?_ hp
          rw [← div_eq_mul_inv, div_le_one hN0]
          exact h3
      _ = N ^ (-C) := one_mul _
  have hfin : ‖(sz.seqHflow n u ω - zt (E n) u • 1)⁻¹ i j -
      (sz.seqHflow n u' ω - zt (E n) u' • 1)⁻¹ i j‖ ≤ N ^ (-C) :=
    key.trans ((mul_le_mul hN6 hsq (Real.sqrt_nonneg _) (by positivity)).trans hexp)
  exact absurd hbad (not_lt.2 hfin)

/-- **The net lift of the Step 1 families** (the net argument after `Gopboundu`, 5-6:16): the
per-time statements `STStep1LoopPT`, `STStep1WeakPT` (`lRB1`, `Gtmwc`) give the `u`-uniform ones
`STStep1Loop`, `STStep1Weak`, with the premises `0 < κ`, `|E n| ≤ 2 - κ`, `0 < τ`,
`0 ≤ s ≤ t < 1`, `N → ∞` and the application range `RangeCond τ t` (`1 - t ≥ N^{-1+τ}`).
`Continuity:1261` (`Step1NetLift`); the differences with RBM2D's statement are `d : Sizes` is
`sz : Sizes d`, `Step1LoopPT/Unif`, `Step1WeakLawPT/Unif` are `STStep1LoopPT/Loop`,
`STStep1WeakPT/Weak`, and the arguments `c`, `Bandwidth d c`, `CondStInd d E s t`, which the proof
does not use (paper-delta candidate `T2062a`, RBM2D `T2070b`), are dropped. -/
def Step1NetLift (sz : Sizes d) (E : ℕ → ℝ) (κ τ : ℝ) (s t : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → 0 < τ → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) →
    (∀ n, t n < 1) → sz.SizeTendsto → sz.RangeCond τ t →
    (STStep1LoopPT sz E s t → STStep1Loop sz E s t) ∧
      (STStep1WeakPT sz E s t → STStep1Weak sz E s t)

/-- **The net lift of the Step 1 families**: `STStep1LoopPT → STStep1Loop` and
`STStep1WeakPT → STStep1Weak`.  `Continuity:1331` (`step1NetLift`).  Both halves apply `cont_core`
(`ContinuityNet`) on `TimeIcc s t n × V n` with the good event `contGood` and the net of mesh
`N^{-A-1}`; loops: `V n = (σ, a)`, `A = 6k + 16`, `#V ≤ N^{k+1}`, `ε = N^{-k}`; weak law:
`V n = Idx × Idx`, `A = 40`, `#V = N²`, `ε = N^{-1/4}`. -/
theorem step1NetLift (sz : Sizes d) : ∀ E κ τ s t, Step1NetLift sz E κ τ s t := by
  intro E κ τ s t hκ hE hτ hs0 hst ht1 hsize hRange
  set c₁ : ℝ := Real.sqrt (2 * κ) / 2 with hc₁def
  have hc₁ : 0 < c₁ := by
    rw [hc₁def]
    have := Real.sqrt_pos.2 (by linarith : 0 < 2 * κ)
    linarith
  have hbulk : ∀ n, |E n| < 2 ∧ c₁ ≤ (mE (E n)).im := fun n => cont_bulk hκ (hE n)
  have hlen : ∀ n, t n - s n ≤ 1 := fun n => by linarith [hs0 n, ht1 n]
  have hcast : Tendsto (fun n : ℕ => ((sz.size n : ℕ) : ℝ)) atTop atTop := hsize
  have hsizeN : Tendsto sz.size atTop atTop := tendsto_natCast_atTop_iff.mp hcast
  have ev1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hcast.eventually_ge_atTop 1
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
      filter_upwards [hcast.eventually (cont_LP_eventually k)] with n hev
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
        rw [eN]; exact pow_le_pow_left₀ hL0 hLW d
      rw [e, hcardV]
      calc (2 : ℝ) ^ k * ((sz.L n : ℝ) ^ d) ^ k
          ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ k :=
            mul_le_mul g3 (pow_le_pow_left₀ (by positivity) hLN k) (by positivity) hN0.le
        _ = ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) := by ring
    refine cont_core (V := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n))) hsizeN hst hlen
      (A := 6 * (k : ℝ) + 16) (Cv := (k : ℝ) + 1) hA0 (by linarith) hcard (hPT k hk)
      (cont_highProbAt_good sz hsizeN)
      (ε := fun n => (((sz.size n : ℕ) : ℝ)⁻¹) ^ k)
      (fun n => pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _) ?_ ?_
    · -- `hlow`
      refine Eventually.of_forall fun n p ω => ?_
      obtain ⟨u, σ, a⟩ := p
      exact cont_LP_low sz n k (hs0 n) u.2.1 (lt_of_le_of_lt u.2.2 (ht1 n))
    · -- `hclose`
      filter_upwards [hcast.eventually (cont_LP_eventually k), evc, evR] with n hev hc hR
      obtain ⟨g1, g2, _, gA, gC⟩ := hev
      intro ω hω u u' hΔ v
      obtain ⟨σ, a⟩ := v
      exact cont_LP_close (sz.W_pos n) (sz.slice n ω)
        (N := ((sz.size n : ℕ) : ℝ)) (E := E n) (s := s n) (t := t n) (u := u) (u' := u')
        (B := sz.Bctl n (s n)) rfl (hbulk n).1 (hBnn n) (hs0 n) u.2.1 u.2.2 u'.2.1 u'.2.2
        (ht1 n) hc₁ (hbulk n).2 hc hR (fun c => hω c) hΔ g1 g2 gA gC σ a
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
        push_cast; ring
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
      ring_nf; exact le_rfl
    refine cont_core (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) hsizeN
      hst hlen (A := 40) (Cv := 2) (by norm_num) (by norm_num) (Eventually.of_forall hcard) hPT
      (cont_highProbAt_good sz hsizeN)
      (ε := fun n => (((sz.size n : ℕ) : ℝ)⁻¹) ^ ((1 : ℝ) / 4))
      (fun n => Real.rpow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _) ?_ ?_
    · -- `hlow`
      refine Eventually.of_forall fun n p ω => ?_
      obtain ⟨u, i, j⟩ := p
      exact cont_WL_low sz n ((hs0 n).trans u.2.1) (lt_of_le_of_lt u.2.2 (ht1 n))
    · -- `hclose`
      filter_upwards [evc, evR, evg2, evg3] with n hc hR g2 g3
      intro ω hω u u' hΔ v
      obtain ⟨i, j⟩ := v
      exact cont_WL_close sz n ω (N := ((sz.size n : ℕ) : ℝ)) (E := E n) (t := t n) (u := u)
        (u' := u') (A := 40) (c₁ := c₁) rfl (hbulk n).1 ((hs0 n).trans u.2.1) u.2.2
        ((hs0 n).trans u'.2.1) u'.2.2 (ht1 n) hc₁ (hbulk n).2 hc hR (fun c => hω c) hΔ g2 g3 i j

end Main

/-! ## 4. The diagonal step and the pin `STNetLift` -/

section Diagonal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The diagonal step**: `≺` along every time *section* `u_n ∈ [s_n, t_n]`, the union over the
rest of the index `V n` inside `P`, gives the per-time statement over `TimeIcc s t n × V n`
(union over `(u, v)` outside `P`).  A bad `(u_n, v_n)` at infinitely many `n` is a bad section; the
single event `{N^τ ζ(u_n, v_n) < ξ(u_n, v_n)}` is contained in the union over `v` at `u_n`.  No
exponent is involved.  New (no RBM2D counterpart: RBM2D's net lift takes the per-time statement
over `TimeIcc × V` as its hypothesis); via `perTimeDomAt_iff_forall_section`. -/
private theorem perTime_of_sections (P : Measure Ω) (size : ℕ → ℕ) {s t : ℕ → ℝ}
    (hst : ∀ n, s n ≤ t n) {V : ℕ → Type*} (hV : ∀ n, Nonempty (V n))
    (ξ ζ : ∀ n, TimeIcc s t n × V n → Ω → ℝ)
    (h : ∀ u : ∀ n, TimeIcc s t n,
      StochDomAt P size (fun n (v : V n) ω => ξ n (u n, v) ω)
        (fun n (v : V n) ω => ζ n (u n, v) ω)) :
    PerTimeDomAt P size ξ ζ := by
  refine (perTimeDomAt_iff_forall_section P size
    (fun n => ⟨(⟨s n, le_refl _, hst n⟩, Classical.choice (hV n))⟩) ξ ζ).2 ?_
  intro w
  exact (h (fun n => (w n).1)).precomp_param (V := fun _ => Unit) (fun n _ => (w n).2)

end Diagonal

end RBM.Ind

namespace RBM.Gauss.Sizes

open RBM.Ind

/-- **The net lift of Step 1 (`STNetLift`)** for every `d`: if the loop bound `(lRB1)` holds at
every time sequence `u ∈ [s,t]` (the union over `(σ, a)` inside `P`), it holds uniformly in
`u ∈ [s,t]`.  Proof: the diagonal step (`perTime_of_sections`) turns the hypothesis into
`STStep1LoopPT`; `STFlow` and `t ≤ lemT z` give the premises of `step1NetLift`
(`Green.v3_premises_of_stFlow`: `|E_n| < 2 - κ/2`, `t_n < 1`, `1 - t_n ≥ N^{-1+ε/2}`,
`N → ∞` from `Admissible`), at `κ/2`, `τ = ε/2`.  Neither `Bandwidth` nor `(eq:WO)` nor
`(con_st_ind)` is used.  The merged pin of `RBM3D/Induction/Defs.lean`; its owed registry line
(`RBM3D/Test/Axioms.lean`, `STNetLift`) is discharged by this theorem (DECISIONS §22, S1-34). -/
theorem stNetLift_holds (d : ℕ) : STNetLift d := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s t hs0 hst ht hu
  obtain ⟨hA, hE, hlt, hR⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow ht
  have hPT : STStep1LoopPT sz (STflowE z) s t := by
    intro k hk
    refine perTime_of_sections sz.seqP sz.size hst
      (fun n => ⟨(fun _ => true, fun _ => 0)⟩) _ _ ?_
    intro u
    exact hu (fun n => (u n : ℝ)) (fun n => (u n).2.1) (fun n => (u n).2.2) k hk
  exact (step1NetLift sz (STflowE z) (κ / 2) (ε / 2) s t (half_pos hκ) (fun n => (hE n).le)
    (half_pos hε) hs0 hst hlt hA.2.2.1 hR).1 hPT

end RBM.Gauss.Sizes

/-! ## 5. Compiled nonempty instances at `d = 3`

The size data are the merged preflight sequence `RBM.Gauss.SizesInst.sz0` (`L_n = 4(n+1)`,
`W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6} → 0`, `N_n = (W_n L_n)^3`; `n = 0`: `L = 4`, `W = 32`,
`N = 2097152`), admissible at `𝔠 = 1/6`, `𝔡 = 1/10`; the flow points `z_n = 1/2 + i N_n^{-4/5}`
(`κ = ε = 1/10`, `E_n = lemE z_n`, `|E_n| ≤ 1/2`), `s ≡ 0`, `t ≡ 1/16 ≤ t₀ = lemT z_n`
(`RBM3D/Induction/Defs.lean`, section 3).  Every deterministic hypothesis is discharged; what stays
a hypothesis is the stochastic premise of the theorem itself (`≺` of the loops at every time
sequence, resp. per time). -/

namespace RBM.Ind

section Instances

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst

/-- `gopbound` at `sz0`, `κ = 1/10`, `E ≡ 1/2`: `0 < κ`, `|E n| = 1/2 ≤ 2 - κ`, `N → ∞`
(`sz0_tendsto`) are discharged; the output is the existence of `C'` for every `C > 0`. -/
example (C : ℝ) (hC : 0 < C) :=
  gopbound sz0 (1 / 10) (fun _ => (1 / 2 : ℝ)) (by norm_num) (fun _ => by norm_num) sz0_tendsto C hC

/-- `Step1NetLift` at the flow of the instance (`κ = (1/10)/2`, `τ = (1/10)/2`, `s ≡ 0`,
`t ≡ 1/16`): `step1NetLift` applies; the two per-time statements stay hypotheses of the two
implications. -/
example : Step1NetLift sz0 (STflowE z0) ((1 / 10) / 2) ((1 / 10) / 2) sInst tInst :=
  step1NetLift sz0 _ _ _ _ _

/-- `step1NetLift`, both halves, at the flow of the instance: every hypothesis of the net lift
(`0 < κ`, `|E_n| ≤ 2 - κ`, `0 < τ`, `0 ≤ s ≤ t < 1`, `N → ∞`, `RangeCond`) is discharged; the
per-time loop family `STStep1LoopPT` (resp. `STStep1WeakPT`) stays the hypothesis of the
implication. -/
example :
    (STStep1LoopPT sz0 (STflowE z0) sInst tInst → STStep1Loop sz0 (STflowE z0) sInst tInst) ∧
      (STStep1WeakPT sz0 (STflowE z0) sInst tInst → STStep1Weak sz0 (STflowE z0) sInst tInst) :=
  step1NetLift sz0 (STflowE z0) ((1 / 10) / 2) ((1 / 10) / 2) sInst tInst (by norm_num)
    (fun n => (RBM.Green.Instance.premises.2.1 n).le) (by norm_num) (fun _ => le_rfl)
    (fun n => by simp only [sInst, tInst]; norm_num) RBM.Green.Instance.premises.2.2.2.1
    sz0_tendsto RBM.Green.Instance.premises.2.2.2.2

/-- `stNetLift_holds` at `d = 3`, through the merged instance `inst_netLift` (which takes the pin
as its hypothesis): the pin is now discharged, the loop bound at every time sequence in `[0, 1/16]`
(`hu`) stays a hypothesis. -/
example
    (hu : ∀ u : ℕ → ℝ, (∀ n, sInst n ≤ u n) → (∀ n, u n ≤ tInst n) →
      ∀ k : ℕ, 1 ≤ k →
        Prec sz0 (U := fun n => (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
          (fun n p ω => ‖Lloop sz0 n (STflowE z0 n) (u n) p.1 p.2 ω‖)
          (fun n _ _ => ((1 - sInst n) / (1 - u n)) ^ (k - 1) * (sz0.Bctl n (sInst n)) ^ (k - 1))) :
    STStep1Loop sz0 (STflowE z0) sInst tInst :=
  inst_netLift (stNetLift_holds 3) hu

/-- `stNetLift_holds` applied directly: `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `sz0`, `z0`, `STFlow`
(`flow_z0`), `0 ≤ s ≤ t ≤ lemT z_n` (`sixteenth_le_lemT`). -/
example
    (hu : ∀ u : ℕ → ℝ, (∀ n, sInst n ≤ u n) → (∀ n, u n ≤ tInst n) →
      ∀ k : ℕ, 1 ≤ k →
        Prec sz0 (U := fun n => (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
          (fun n p ω => ‖Lloop sz0 n (STflowE z0 n) (u n) p.1 p.2 ω‖)
          (fun n _ _ => ((1 - sInst n) / (1 - u n)) ^ (k - 1) * (sz0.Bctl n (sInst n)) ^ (k - 1))) :
    STStep1Loop sz0 (STflowE z0) sInst tInst :=
  stNetLift_holds 3 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 sInst tInst (fun _ => le_rfl)
    (fun n => by simp only [sInst, tInst]; norm_num) (fun n => sixteenth_le_lemT n) hu

end Instances

end RBM.Ind
