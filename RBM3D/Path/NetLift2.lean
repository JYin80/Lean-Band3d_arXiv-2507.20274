/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Path.NetLift1

/-!
# The net lift of Step 2, part 2: `STStep2LocalPT → STStep2Local`, `STStep2AvgPT → STStep2Avg`
and the pin `STNetLift2` (ST2-19, ticket T2082)

Port of the second part of `RBM2D/Path/NetLift.lean` at commit `c9a24cf` (cited `NetLift:line`),
the part T2074 left (`RBM3D/Path/NetLift1.lean`, cut at `NetLift:1511`): `Step2LocalUnif` (`:1343`,
the merged pin `STStep2Local`, not redefined), `Step2LocalNetLift` (`:1351`), `netLift_llErr_diff`
(`:622`), `netLift_T2_low` (`:1244`), `netLift_T2_close` (`:1251`) and `step2LocalNetLift`
(`:1518-1595`).  `STStep2Avg` has no RBM2D counterpart (new at `d ≥ 3`).  The abstract net lift is
the merged `ContinuityNet.cont_core`; `NetLift1` exports only `Step2NetLift`, `step2NetLift` and
`stNetLift2_part1`, so the helpers it keeps `private` that are needed here are recopied as
`private` (`nl2_*`, copies of `nl_*`, and `nl2_STGM_eq`, `nl2_entry_diff` of `Continuity.lean`).

Renaming (`docs/tickets/ST1-COMMON.md` item 2): `d : Sizes` is `sz : Sizes d`, `Idx L W` is
`Idx d L W`, `(W L)^2` is `sz.size n = (W L)^d`, `llErrMat` is the entry of `STGM`,
`spectralM`, `spectralZ` are `mE`, `zt`.  The `d = 2` control `M_u^{-1/2}` on `|G - M|` becomes
`STWB_{u,|x-y|}` on `|G - M|²` (`ε = N^{-1}`, `ξ = ‖·‖²`); `Bandwidth`, `CondStInd` of RBM2D's
`Step2LocalNetLift` are not used by the proof and are dropped (as `T2074a`).

Public declarations: `Step2LocalNetLift`, `step2LocalNetLift`, `Step2AvgNetLift`,
`step2AvgNetLift` (namespace `RBM.Ind`) and `stNetLift2_holds` (namespace `RBM.Gauss.Sizes`);
the helpers are `private`.
-/

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path
  RBM.Loop RBM.Ind.ContinuityNet
open scoped NNReal ENNReal

set_option linter.style.longLine false

/-! ## 1. The modulus of a loop of length `k` in the time (copy of `NetLift1` section 1) -/

section Flow

open scoped Matrix.Norms.L2Operator

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The resolvent word `∏ᵢ G(σᵢ) E_{aᵢ}` over a list of `(σᵢ, aᵢ)` (the `foldr` of `loopL`); copy of
the private `contWord`, `Continuity.lean:89`. -/
private noncomputable def nl2Word (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (l : List (Bool × Zd d L)) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1

omit [NeZero W] in
/-- The word of a cons. -/
private theorem nl2Word_cons (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (p : Bool × Zd d L) (l : List (Bool × Zd d L)) :
    nl2Word H z (p :: l) = Gres H z p.1 * Eblk d L W p.2 * nl2Word H z l := rfl

/-- The word is bounded by `Q^length` (`Continuity.lean`, private `cont_word_norm`, copied: a
private declaration cannot be imported). -/
private theorem nl2_word_norm (hW : 1 ≤ W) {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    {z : ℂ} {Q : ℝ} (hQ : ∀ σ, ‖Gres H z σ‖ ≤ Q) (l : List (Bool × Zd d L)) :
    ‖nl2Word H z l‖ ≤ Q ^ l.length := by
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hQ true)
  induction l with
  | nil => simp [nl2Word]
  | cons p l ih =>
    have hEa := cont_norm_Eblk_le_one (d := d) (L := L) hW p.2
    rw [nl2Word_cons, List.length_cons, pow_succ]
    calc ‖Gres H z p.1 * Eblk d L W p.2 * nl2Word H z l‖
        ≤ ‖Gres H z p.1‖ * ‖Eblk d L W p.2‖ * ‖nl2Word H z l‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ Q * 1 * Q ^ l.length :=
          mul_le_mul (mul_le_mul (hQ _) hEa (norm_nonneg _) hQ0) ih (norm_nonneg _) (by positivity)
      _ = Q ^ l.length * Q := by ring

/-- The `k`-fold telescoping of a resolvent word: port of RBM1D `norm_gchain_sub_le`
(`Gauss/Step1Hyp.lean:517` at `86573b9`) to the block matrices of `d ≥ 3` (copy of the private
`cont_word_diff`, `Continuity.lean:119`). -/
private theorem nl2_word_diff (hW : 1 ≤ W)
    {H H' : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z z' : ℂ} {Q S : ℝ} (hQ1 : 1 ≤ Q)
    (hQ : ∀ σ, ‖Gres H z σ‖ ≤ Q) (hQ' : ∀ σ, ‖Gres H' z' σ‖ ≤ Q)
    (hS : ∀ σ, ‖Gres H z σ - Gres H' z' σ‖ ≤ S) (l : List (Bool × Zd d L)) :
    ‖nl2Word H z l - nl2Word H' z' l‖ ≤ (l.length : ℝ) * Q ^ l.length * S := by
  have hQ0 : 0 ≤ Q := by linarith
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS true)
  induction l with
  | nil => simp [nl2Word]
  | cons p l ih =>
    have hEa := cont_norm_Eblk_le_one (d := d) (L := L) hW p.2
    rw [nl2Word_cons, nl2Word_cons]
    have key : Gres H z p.1 * Eblk d L W p.2 * nl2Word H z l -
        Gres H' z' p.1 * Eblk d L W p.2 * nl2Word H' z' l =
        (Gres H z p.1 - Gres H' z' p.1) * Eblk d L W p.2 * nl2Word H z l +
          Gres H' z' p.1 * Eblk d L W p.2 * (nl2Word H z l - nl2Word H' z' l) := by
      noncomm_ring
    rw [key]
    have hP := nl2_word_norm hW hQ l
    have t1 : ‖(Gres H z p.1 - Gres H' z' p.1) * Eblk d L W p.2 * nl2Word H z l‖ ≤
        S * 1 * Q ^ l.length := by
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul (hS _) hEa (norm_nonneg _) hS0)) hP
        (norm_nonneg _) (by positivity)
    have t2 : ‖Gres H' z' p.1 * Eblk d L W p.2 * (nl2Word H z l - nl2Word H' z' l)‖ ≤
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

/-- The loop `loopFine` is the trace of the `nl2Word` of the block matrix. -/
private theorem nl2_loopFine_eq (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    loopFine d L W H z σ a =
      Matrix.trace (nl2Word (blockMat d L W H) z ((List.ofFn σ).zip (List.ofFn a))) := by
  unfold loopFine
  rw [loopM_eq_loopL]
  rfl

/-- The modulus of a loop of length `k` along the flow, on `‖X‖ ≤ Xb` (`Gopboundu` and the net
argument of 5-6:16; RBM1D `norm_gloop_sub_le`, `Gauss/Step1Hyp.lean:571` at `86573b9`, for the
block matrices of `d ≥ 3`; the trace is bounded by `card(Vtx) · ‖·‖`).
Copy of the private `cont_loopAbs_diff` (`Continuity.lean:166`, T2062), stated for the norm of the
difference (`NetLift:661` `netLift_gloop_diff` for `k = 2`) instead of the difference of the norms;
`Continuity.lean` does not export it. -/
private theorem nl2_loop_sub (hW : 1 ≤ W) (ω : Ω d L W) {E t u u' Q Xb : ℝ} (hE : |E| < 2)
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
  have hw := nl2_word_diff hW hQ1 hGu hGu' hS ((List.ofFn σ).zip (List.ofFn a))
  have hlen : ((List.ofFn σ).zip (List.ofFn a)).length = k := by simp
  rw [hlen] at hw
  rw [nl2_loopFine_eq, nl2_loopFine_eq]
  rw [← Matrix.trace_sub]
  refine (norm_matrix_trace_le_card_mul _).trans ?_
  exact mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)

end Flow


/-! ## 2. Deterministic facts: the entry modulus, `STGM`, the controls `STWB` and `Bctl` -/

section Close

open scoped Matrix.Norms.L2Operator

/-- `0 ≤ STWB` (copy of the private `nl_STWB_nonneg`, `NetLift1`). -/
private theorem nl2_STWB_nonneg {d : ℕ} (sz : Sizes d) (n K : ℕ) (u : ℝ) :
    0 ≤ STWB sz n u K := by
  unfold STWB Bparam
  positivity

/-- `(η_t)⁻¹ ≤ N²` from `(1 - t)⁻¹ ≤ N`, `Im m ≥ c₁` and `1/c₁ ≤ N` (copy of the private
`nl_eta_inv_le`, `NetLift1`). -/
private theorem nl2_eta_inv_le {E t N c₁ : ℝ} (hE : |E| < 2) (hN0 : 0 < N) (hc₁ : 0 < c₁)
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

/-- The ratio of `STWB_{u,K}` at two times (copy of the private `nl_STWB_ratio`, `NetLift1`):
`STWB_{u,K} ≤ (1 + (1-t)⁻¹ |u-u'|) STWB_{u',K}` for `u, u' ≤ t < 1`, every `K`. -/
private theorem nl2_STWB_ratio {d : ℕ} (sz : Sizes d) (n K : ℕ) {t u u' : ℝ} (ht : t < 1)
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

/-- **The floor of the control** (RBM2D `netLift_T2_low`, `NetLift:1244`, `M_u^{-1/2} ≥ N^{-1/2}`):
`N^{-1} ≤ STWB_{u,K}` for `0 ≤ u < 1` and every block distance `K`.  The zero-mode term
`W^{-d} (L^d (1-u))⁻¹ ≥ (W L)^{-d}` of `B_{u,K}` does not depend on `K`; the other term is `≥ 0`
(`cont_inv_size_le_Bctl` is `K = 0`). -/
private theorem nl2_STWB_low {d : ℕ} (sz : Sizes d) (n K : ℕ) {u : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u < 1) : ((sz.size n : ℕ) : ℝ)⁻¹ ≤ STWB sz n u K := by
  unfold STWB Bparam
  have hx : 0 < 1 - u := by linarith
  rw [abs_of_pos hx]
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := pow_pos hL d
  have hsize : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp [Sizes.size, mul_pow]
  have h1 : (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ :=
    inv_anti₀ (by positivity) (by nlinarith)
  have h2 : (0 : ℝ) ≤ (sz.lam n ^ 2 + (1 - u))⁻¹ * ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by
    have : 0 < sz.lam n ^ 2 + (1 - u) := by positivity
    positivity
  rw [hsize, mul_inv]
  exact mul_le_mul_of_nonneg_left (h1.trans (le_add_of_nonneg_left h2)) (inv_nonneg.2 hWd.le)

/-- `STGM` is the `(x, y)` entry of the resolvent of the flow, minus `m(E)` on the diagonal
(copy of the private `cont_STGM_eq`, `Continuity.lean:423`). -/
private theorem nl2_STGM_eq {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (ω : sz.SeqΩ)
    (x y : Idx d (sz.L n) (sz.W n)) :
    STGM sz n E u ω x y =
      (Hflow d (sz.L n) (sz.W n) u (sz.slice n ω) -
          zt E u • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))⁻¹ x y -
        (if x = y then mE E else 0) := by
  unfold STGM Gt
  rw [cont_Gres_true_eq_green]
  rfl

section Entry

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The entry modulus of the resolvent along the flow: if `‖X‖ ≤ Xb`, `u, u' ≤ t < 1`,
`|u - u'| ≤ 1` and `(η_t)⁻¹ ≤ Q`, then `‖G_u - G_{u'}‖_max ≤ Q² (Xb + 1) |u-u'|^{1/2}`.  `NetLift:622`
(`netLift_llErr_diff`), for the entry of the resolvent (`llErrMat` is the entry of `STGM`); copy
of the private `cont_entry_diff` (`Continuity.lean:66`). -/
private theorem nl2_entry_diff (ω : Ω d L W) {E t u u' Q Xb : ℝ} (hE : |E| < 2) (ht : t < 1)
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

/-- An entry of the resolvent along the flow is at most `Q`: `‖G_{u,xy}‖ ≤ ‖G_u‖ ≤ (η_t)⁻¹ ≤ Q`. -/
private theorem nl2_entry_le (ω : Ω d L W) {E t u Q : ℝ} (hE : |E| < 2) (ht : t < 1)
    (hut : u ≤ t) (hQ : (etaT E t)⁻¹ ≤ Q) (i j : Idx d L W) :
    ‖(Hflow d L W u ω - zt E u • (1 : Matrix (Idx d L W) (Idx d L W) ℂ))⁻¹ i j‖ ≤ Q := by
  have hη : 0 < etaT E t := etaT_pos hE ht
  have hgr := cont_norm_green_le (Hflow_isHermitian d L W u ω) hη (cont_eta_le_abs_im hE ht hut)
  have hent := norm_matrix_entry_le_opNorm (green (Hflow d L W u ω) (zt E u)) i j
  have e : green (Hflow d L W u ω) (zt E u) i j =
      (Hflow d L W u ω - zt E u • (1 : Matrix (Idx d L W) (Idx d L W) ℂ))⁻¹ i j := by
    simp [green]
  rw [e] at hent
  exact hent.trans (hgr.trans hQ)

end Entry

end Close

/-! ## 3. The two closeness conclusions of `hclose`, at one index `n` -/

section Closeness

open scoped Matrix.Norms.L2Operator

/-- The two conclusions of `hclose` for the family of `STStep2Local`, at one index `n`,
deterministic: `‖G_u - M‖²_{xy} ≤ ‖G_{u'} - M‖²_{xy} + N^{-1}` and `STWB_{u',K} ≤ 2 STWB_{u,K}`.
`NetLift:1251` (`netLift_T2_close`): RBM2D has `ξ = |llErr|` against `M_u^{-1/2}`; here
`ξ = ‖STGM‖²`, so the closeness of the squares costs the factor `2 ‖b‖ + δ ≤ 5 N²`
(`‖b‖ ≤ ‖G_{u',xy}‖ + ‖m‖ ≤ N² + 1`, `δ = 3 N⁶ N^{-A/2} ≤ 1`).  The ratio of the controls
is `nl2_STWB_ratio` with `1 + x ≤ 11/10 ≤ 2`, for every `K`. -/
private theorem nl2_loc_close {d : ℕ} (sz : Sizes d) (n : ℕ) (ω : sz.SeqΩ)
    {N E t u u' A c₁ : ℝ} (hN : N = ((sz.size n : ℕ) : ℝ)) (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t) (ht : t < 1)
    (hc₁ : 0 < c₁) (hc₁m : c₁ ≤ (mE E).im) (hNc : 1 / c₁ ≤ N) (hN1 : (1 - t)⁻¹ ≤ N)
    (hgood : ∀ c : CoordF d (sz.L n) (sz.W n), |sz.slice n ω c| ≤ N)
    (hy : |u - u'| ≤ N ^ (-A)) (g2 : N * N ^ (-A) ≤ 1 / 10)
    (g3 : 15 * N ^ 9 * N ^ (-A / 2) ≤ N⁻¹) (K : ℕ) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖STGM sz n E u ω x y‖ ^ 2 ≤ ‖STGM sz n E u' ω x y‖ ^ 2 + N⁻¹ ∧
      STWB sz n u' K ≤ 2 * STWB sz n u K := by
  have hNge : (1 : ℝ) ≤ N := by
    rw [hN]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hΔ1 : |u - u'| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hsq : Real.sqrt |u - u'| ≤ N ^ (-A / 2) := cont_sqrt_abs_le hN0.le hy
  have hQ : (etaT E t)⁻¹ ≤ N ^ 2 := nl2_eta_inv_le hE hN0 hc₁ hc₁m hNc hN1
  have hcardI : (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) = N := by
    rw [sz.card_Idx n, hN]
  have hX : ‖Xmat d (sz.L n) (sz.W n) (sz.slice n ω)‖ ≤ 2 * N ^ 2 := by
    have h := cont_norm_Xmat_le (sz.slice n ω) hgood
    rw [hcardI] at h
    linarith
  have hent := nl2_entry_diff (sz.slice n ω) (Q := N ^ 2) (Xb := 2 * N ^ 2) hE ht hu0 hut hu'0
    hu't hΔ1 hQ hX x y
  have hs0' : 0 ≤ Real.sqrt |u - u'| := Real.sqrt_nonneg _
  have hN4 : N ^ 4 ≤ N ^ 6 := pow_le_pow_right₀ hNge (by norm_num)
  have hR0 : 0 ≤ N ^ (-A / 2) := Real.rpow_nonneg hN0.le _
  -- `δ = 3 N⁶ N^{-A/2}`
  set δ : ℝ := 3 * N ^ 6 * N ^ (-A / 2) with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  have hbound : ‖(Hflow d (sz.L n) (sz.W n) u (sz.slice n ω) -
          zt E u • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))⁻¹ x y -
        (Hflow d (sz.L n) (sz.W n) u' (sz.slice n ω) -
          zt E u' • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))⁻¹ x y‖ ≤
      δ := by
    refine hent.trans ?_
    have e1 : N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1) * Real.sqrt |u - u'| =
        (2 * N ^ 6 + N ^ 4) * Real.sqrt |u - u'| := by ring
    rw [e1]
    calc (2 * N ^ 6 + N ^ 4) * Real.sqrt |u - u'| ≤ 3 * N ^ 6 * Real.sqrt |u - u'| :=
          mul_le_mul_of_nonneg_right (by linarith) hs0'
      _ ≤ 3 * N ^ 6 * N ^ (-A / 2) := mul_le_mul_of_nonneg_left hsq (by positivity)
  have hN9 : N ^ 8 ≤ N ^ 9 := pow_le_pow_right₀ hNge (by norm_num)
  have hN69 : N ^ 6 ≤ N ^ 9 := pow_le_pow_right₀ hNge (by norm_num)
  -- `δ ≤ 1` and `5 N² δ ≤ N⁻¹`
  have hδ5 : 5 * N ^ 2 * δ ≤ N⁻¹ := by
    have e : 5 * N ^ 2 * δ = 15 * N ^ 8 * N ^ (-A / 2) := by rw [hδdef]; ring
    rw [e]
    refine le_trans ?_ g3
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN9 (by norm_num)) hR0
  have hδ1 : δ ≤ 1 := by
    have h1 : δ ≤ 5 * N ^ 2 * δ := by
      have : (1 : ℝ) ≤ 5 * N ^ 2 := by nlinarith
      nlinarith
    have h2 : N⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hNge
    linarith
  refine ⟨?_, ?_⟩
  · have hdiff : STGM sz n E u ω x y - STGM sz n E u' ω x y =
        (Hflow d (sz.L n) (sz.W n) u (sz.slice n ω) -
          zt E u • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))⁻¹ x y -
        (Hflow d (sz.L n) (sz.W n) u' (sz.slice n ω) -
          zt E u' • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ))⁻¹ x y := by
      rw [nl2_STGM_eq, nl2_STGM_eq, sub_sub_sub_cancel_right]
    have habs := abs_norm_sub_norm_le (STGM sz n E u ω x y) (STGM sz n E u' ω x y)
    rw [hdiff] at habs
    have hab : ‖STGM sz n E u ω x y‖ ≤ ‖STGM sz n E u' ω x y‖ + δ := by
      have := (abs_le.1 (habs.trans hbound)).2
      linarith
    -- `‖b‖ ≤ N² + 1`
    have hb : ‖STGM sz n E u' ω x y‖ ≤ N ^ 2 + 1 := by
      rw [nl2_STGM_eq]
      refine (norm_sub_le _ _).trans ?_
      refine add_le_add (nl2_entry_le (sz.slice n ω) hE ht hu't hQ x y) ?_
      split_ifs
      · exact (norm_mE hE.le).le
      · simp
    have ha0 : 0 ≤ ‖STGM sz n E u ω x y‖ := norm_nonneg _
    have hb0 : 0 ≤ ‖STGM sz n E u' ω x y‖ := norm_nonneg _
    calc ‖STGM sz n E u ω x y‖ ^ 2 ≤ (‖STGM sz n E u' ω x y‖ + δ) ^ 2 :=
          pow_le_pow_left₀ ha0 hab 2
      _ = ‖STGM sz n E u' ω x y‖ ^ 2 + δ * (2 * ‖STGM sz n E u' ω x y‖ + δ) := by ring
      _ ≤ ‖STGM sz n E u' ω x y‖ ^ 2 + δ * (5 * N ^ 2) := by
          refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hδ0)
          nlinarith
      _ ≤ ‖STGM sz n E u' ω x y‖ ^ 2 + N⁻¹ := by
          have : δ * (5 * N ^ 2) = 5 * N ^ 2 * δ := by ring
          rw [this]
          exact add_le_add le_rfl hδ5
  · have hu1 : u < 1 := lt_of_le_of_lt hut ht
    have hu'1 : u' < 1 := lt_of_le_of_lt hu't ht
    have hx : (1 - t)⁻¹ * |u' - u| ≤ 1 / 10 := by
      rw [abs_sub_comm]
      exact (mul_le_mul hN1 hy (abs_nonneg _) hN0.le).trans g2
    have hr := nl2_STWB_ratio sz n K ht hu't hut
    exact hr.trans (mul_le_mul_of_nonneg_right (by linarith) (nl2_STWB_nonneg sz n K u))

/-- The two conclusions of `hclose` for the family of `STStep2Avg`, at one index `n`,
deterministic: `‖𝓛^{(1)}_u - m‖ ≤ ‖𝓛^{(1)}_{u'} - m‖ + N^{-1}` and `Bctl(u') ≤ 2 Bctl(u)`.  New
at `d ≥ 3` (no RBM2D counterpart): the triangle inequality (`m(E)` does not depend on `u`) and
the loop modulus `nl2_loop_sub` at `k = 1`; the ratio is `cont_Bctl_ratio`. -/
private theorem nl2_avg_close {d : ℕ} (sz : Sizes d) (n : ℕ) (ω : sz.SeqΩ)
    {N E t u u' A c₁ : ℝ} (hN : N = ((sz.size n : ℕ) : ℝ)) (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t) (ht : t < 1)
    (hc₁ : 0 < c₁) (hc₁m : c₁ ≤ (mE E).im) (hNc : 1 / c₁ ≤ N) (hN1 : (1 - t)⁻¹ ≤ N)
    (hgood : ∀ c : CoordF d (sz.L n) (sz.W n), |sz.slice n ω c| ≤ N)
    (hy : |u - u'| ≤ N ^ (-A)) (g2 : N * N ^ (-A) ≤ 1 / 10)
    (g3 : 15 * N ^ 9 * N ^ (-A / 2) ≤ N⁻¹) (a : Zd d (sz.L n)) :
    ‖Lloop sz n E u (fun _ : Fin 1 => true) (fun _ => a) ω - mE E‖ ≤
        ‖Lloop sz n E u' (fun _ : Fin 1 => true) (fun _ => a) ω - mE E‖ + N⁻¹ ∧
      sz.Bctl n u' ≤ 2 * sz.Bctl n u := by
  have hNge : (1 : ℝ) ≤ N := by
    rw [hN]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hΔ1 : |u - u'| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hsq : Real.sqrt |u - u'| ≤ N ^ (-A / 2) := cont_sqrt_abs_le hN0.le hy
  have hQ : (etaT E t)⁻¹ ≤ N ^ 2 := nl2_eta_inv_le hE hN0 hc₁ hc₁m hNc hN1
  have hQ1 : 1 ≤ N ^ 2 := one_le_pow₀ hNge
  have hcardB : (Fintype.card (Vtx d (sz.L n) (sz.W n)) : ℝ) = N := by
    have hN' : N = (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) := hN
    rw [card_BlockIndex, hN', mul_comm]
  have hXb : ‖blockMat d (sz.L n) (sz.W n) (Xmat d (sz.L n) (sz.W n) (sz.slice n ω))‖ ≤
      2 * N ^ 2 := by
    have h := cont_norm_blockMat_Xmat_le (sz.slice n ω) hgood
    rw [hcardB] at h
    linarith
  refine ⟨?_, ?_⟩
  · have hloop : ‖Lloop sz n E u (fun _ : Fin 1 => true) (fun _ => a) ω -
        Lloop sz n E u' (fun _ : Fin 1 => true) (fun _ => a) ω‖ ≤
        (Fintype.card (Vtx d (sz.L n) (sz.W n)) : ℝ) *
          (((1 : ℕ) : ℝ) * (N ^ 2) ^ 1 *
            (N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1) * Real.sqrt |u - u'|)) :=
      nl2_loop_sub (sz.W_pos n) (sz.slice n ω) hE ht hu0 hut hu'0 hu't hΔ1 hQ1 hQ hXb
        (fun _ : Fin 1 => true) (fun _ => a)
    rw [hcardB] at hloop
    have hS : N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1) * Real.sqrt |u - u'| ≤
        3 * N ^ 6 * N ^ (-A / 2) := by
      have e1 : N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1) ≤ 3 * N ^ 6 := by
        have : N ^ 4 ≤ N ^ 6 := pow_le_pow_right₀ hNge (by norm_num)
        nlinarith
      exact mul_le_mul e1 hsq (Real.sqrt_nonneg _) (by positivity)
    have hdiff : ‖Lloop sz n E u (fun _ : Fin 1 => true) (fun _ => a) ω -
        Lloop sz n E u' (fun _ : Fin 1 => true) (fun _ => a) ω‖ ≤ N⁻¹ := by
      refine hloop.trans ?_
      refine le_trans ?_ g3
      have e : N * (((1 : ℕ) : ℝ) * (N ^ 2) ^ 1 * (3 * N ^ 6 * N ^ (-A / 2))) =
          3 * N ^ 9 * N ^ (-A / 2) := by push_cast; ring
      have hR0 : 0 ≤ N ^ (-A / 2) := Real.rpow_nonneg hN0.le _
      have hN69 : N ^ 9 ≤ N ^ 9 := le_rfl
      calc N * (((1 : ℕ) : ℝ) * (N ^ 2) ^ 1 *
            (N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1) * Real.sqrt |u - u'|))
          ≤ N * (((1 : ℕ) : ℝ) * (N ^ 2) ^ 1 * (3 * N ^ 6 * N ^ (-A / 2))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS (by positivity)) hN0.le
        _ = 3 * N ^ 9 * N ^ (-A / 2) := e
        _ ≤ 15 * N ^ 9 * N ^ (-A / 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
              hR0
    have hsplit : Lloop sz n E u (fun _ : Fin 1 => true) (fun _ => a) ω - mE E =
        (Lloop sz n E u' (fun _ : Fin 1 => true) (fun _ => a) ω - mE E) +
          (Lloop sz n E u (fun _ : Fin 1 => true) (fun _ => a) ω -
            Lloop sz n E u' (fun _ : Fin 1 => true) (fun _ => a) ω) := by ring
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add le_rfl hdiff)
  · have hu1 : u < 1 := lt_of_le_of_lt hut ht
    have hu'1 : u' < 1 := lt_of_le_of_lt hu't ht
    have hBu : 0 ≤ sz.Bctl n u :=
      (inv_nonneg.2 (Nat.cast_nonneg _)).trans (cont_inv_size_le_Bctl sz n hu0 hu1)
    have hx : (1 - t)⁻¹ * |u' - u| ≤ 1 / 10 := by
      rw [abs_sub_comm]
      exact (mul_le_mul hN1 hy (abs_nonneg _) hN0.le).trans g2
    have hr := cont_Bctl_ratio sz n ht hu't hut
    exact hr.trans (mul_le_mul_of_nonneg_right (by linarith) hBu)

end Closeness

/-! ## 4. The pinned statements and their proofs -/

section Main

variable {d : ℕ}

/-- **The net lift of `(Gt_bound_flow)`**: the per-time statement `STStep2LocalPT` gives the
`u`-uniform one `STStep2Local` (RBM2D `Step2Local*`: `Step2LocalPT → Step2LocalUnif`), with the
premises `0 < κ`, `|E n| ≤ 2 - κ`, `0 < τ`, `0 ≤ s ≤ t < 1`, `N → ∞` and the application range
`RangeCond τ t` (`1 - t ≥ N^{-1+τ}`).  `NetLift:1351` (`Step2LocalNetLift`); `Step2LocalUnif`
(`:1343`) is the merged pin `STStep2Local`; the arguments `c`, `Bandwidth d c`, `CondStInd d E s t`,
which the proof does not use, are dropped (paper-delta candidate `T2082a`; as `T2074a`). -/
def Step2LocalNetLift (sz : Sizes d) (E : ℕ → ℝ) (κ τ : ℝ) (s t : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → 0 < τ → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) →
    (∀ n, t n < 1) → sz.SizeTendsto → sz.RangeCond τ t →
    STStep2LocalPT sz E s t → STStep2Local sz E s t

/-- **The net lift of `(Gt_avgbound_flow)`**: `STStep2AvgPT → STStep2Avg` under the premises of
`Step2LocalNetLift`.  New at `d ≥ 3`: RBM2D has no counterpart (paper-delta candidate `T2082b`). -/
def Step2AvgNetLift (sz : Sizes d) (E : ℕ → ℝ) (κ τ : ℝ) (s t : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → 0 < τ → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) →
    (∀ n, t n < 1) → sz.SizeTendsto → sz.RangeCond τ t →
    STStep2AvgPT sz E s t → STStep2Avg sz E s t

/-- The eventual numerical facts of the two lifts, at the common modulus `A = 40`:
`N N^{-A} ≤ 1/10` and `15 N⁹ N^{-A/2} ≤ N⁻¹` (`δ = 3 N⁶ N^{-A/2}`, the loop of length `1` and the
square of an entry cost `15 N⁹ N^{-A/2}` at most). -/
private theorem nl2_eventual {size : ℕ → ℕ} (hsize : Tendsto size atTop atTop) :
    ∀ᶠ n : ℕ in atTop, ((size n : ℕ) : ℝ) * ((size n : ℕ) : ℝ) ^ (-(40 : ℝ)) ≤ 1 / 10 ∧
      15 * ((size n : ℕ) : ℝ) ^ 9 * ((size n : ℕ) : ℝ) ^ (-(40 : ℝ) / 2) ≤
        (((size n : ℕ) : ℝ))⁻¹ := by
  filter_upwards [cont_gap hsize 1 (κ := 1 / 10) (p := 1 - 40) (q := 0) (by norm_num)
    (by norm_num), cont_gap hsize 15 (κ := 1) (p := 9 - 40 / 2) (q := -1) one_pos
    (by norm_num), hsize.eventually (eventually_ge_atTop 1)] with n h1 h2 h3
  have hx0 : (0 : ℝ) < ((size n : ℕ) : ℝ) := by exact_mod_cast h3
  refine ⟨?_, ?_⟩
  · have : ((size n : ℕ) : ℝ) * ((size n : ℕ) : ℝ) ^ (-(40 : ℝ)) =
        ((size n : ℕ) : ℝ) ^ (1 - 40 : ℝ) := by
      rw [show (1 - 40 : ℝ) = 1 + -40 by ring, Real.rpow_add hx0, Real.rpow_one]
    rw [this]
    rw [Real.rpow_zero] at h1
    linarith
  · have e1 : 15 * ((size n : ℕ) : ℝ) ^ 9 * ((size n : ℕ) : ℝ) ^ (-(40 : ℝ) / 2) =
        15 * ((size n : ℕ) : ℝ) ^ (9 - 40 / 2 : ℝ) := by
      rw [mul_assoc, cont_pow_mul_rpow hx0]
      congr 2
      push_cast; ring
    have e2 : (((size n : ℕ) : ℝ))⁻¹ = ((size n : ℕ) : ℝ) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one]
    rw [e1, e2]
    linarith

/-- The `d ≥ 3` premises shared by the two lifts: `c₁`, the bulk, the eventual `(1-t)⁻¹ ≤ N`. -/
private theorem nl2_evR (sz : Sizes d) {τ : ℝ} {t : ℕ → ℝ}
    (hRange : sz.RangeCond τ t) (hτ : 0 < τ)
    (hcast : Tendsto (fun n : ℕ => ((sz.size n : ℕ) : ℝ)) atTop atTop) :
    ∀ᶠ n : ℕ in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
  have ev1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hcast.eventually_ge_atTop 1
  filter_upwards [hRange, ev1] with n hn h1
  have hx0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hpos : 0 < ((sz.size n : ℕ) : ℝ) ^ (-1 + τ) := Real.rpow_pos_of_pos hx0 _
  have h2 := inv_anti₀ hpos hn
  rw [← Real.rpow_neg hx0.le] at h2
  refine h2.trans ?_
  calc ((sz.size n : ℕ) : ℝ) ^ (-(-1 + τ)) ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    _ = _ := Real.rpow_one _

/-- **The net lift of `(Gt_bound_flow)`**: `STStep2LocalPT → STStep2Local`.  `NetLift:1518`
(`step2LocalNetLift`).  `cont_core` (`ContinuityNet`) on `TimeIcc s t n × V n` with the good event
`contGood` and the net of mesh `N^{-A-1}`; `V n = Idx × Idx`, `A = 40`, `#V = N²`, `ε = N^{-1}`,
`ξ = ‖G_u - M‖²_{xy}`, `ζ = STWB_{u,|[x]-[y]|}`. -/
theorem step2LocalNetLift (sz : Sizes d) : ∀ E κ τ s t, Step2LocalNetLift sz E κ τ s t := by
  intro E κ τ s t hκ hE hτ hs0 hst ht1 hsize hRange hPT
  set c₁ : ℝ := Real.sqrt (2 * κ) / 2 with hc₁def
  have hc₁ : 0 < c₁ := by
    rw [hc₁def]
    have := Real.sqrt_pos.2 (by linarith : 0 < 2 * κ)
    linarith
  have hbulk : ∀ n, |E n| < 2 ∧ c₁ ≤ (mE (E n)).im := fun n => cont_bulk hκ (hE n)
  have hlen : ∀ n, t n - s n ≤ 1 := fun n => by linarith [hs0 n, ht1 n]
  have hcast : Tendsto (fun n : ℕ => ((sz.size n : ℕ) : ℝ)) atTop atTop := hsize
  have hsizeN : Tendsto sz.size atTop atTop := tendsto_natCast_atTop_iff.mp hcast
  have evc : ∀ᶠ n : ℕ in atTop, 1 / c₁ ≤ ((sz.size n : ℕ) : ℝ) :=
    hcast.eventually_ge_atTop _
  have evR := nl2_evR sz hRange hτ hcast
  have hcard : ∀ n : ℕ,
      (Fintype.card (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) : ℝ) ≤
        ((sz.size n : ℕ) : ℝ) ^ (2 : ℝ) := by
    intro n
    rw [Fintype.card_prod, Nat.cast_mul, Real.rpow_two, sz.card_Idx n]
    ring_nf; exact le_rfl
  refine cont_core (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) hsizeN
    hst hlen (A := 40) (Cv := 2) (by norm_num) (by norm_num) (Eventually.of_forall hcard) hPT
    (cont_highProbAt_good sz hsizeN)
    (ε := fun n => (((sz.size n : ℕ) : ℝ))⁻¹)
    (fun n => inv_nonneg.2 (Nat.cast_nonneg _)) ?_ ?_
  · -- `hlow`
    refine Eventually.of_forall fun n p ω => ?_
    obtain ⟨u, i, j⟩ := p
    exact nl2_STWB_low sz n _ ((hs0 n).trans u.2.1) (lt_of_le_of_lt u.2.2 (ht1 n))
  · -- `hclose`
    filter_upwards [evc, evR, nl2_eventual hsizeN] with n hc hR hg
    intro ω hω u u' hΔ v
    obtain ⟨i, j⟩ := v
    exact nl2_loc_close sz n ω (N := ((sz.size n : ℕ) : ℝ)) (E := E n) (t := t n) (u := u)
      (u' := u') (A := 40) (c₁ := c₁) rfl (hbulk n).1 ((hs0 n).trans u.2.1) u.2.2
      ((hs0 n).trans u'.2.1) u'.2.2 (ht1 n) hc₁ (hbulk n).2 hc hR (fun c => hω c) hΔ hg.1 hg.2
      _ i j

/-- **The net lift of `(Gt_avgbound_flow)`**: `STStep2AvgPT → STStep2Avg`.  New at `d ≥ 3`.
`cont_core` on `TimeIcc s t n × Zd d (L n)`, `A = 40`, `#V = L^d ≤ N`, `ε = N^{-1}`,
`ξ = ‖𝓛^{(1)}_{u,+,a} - m(E)‖`, `ζ = Bctl(u)`. -/
theorem step2AvgNetLift (sz : Sizes d) : ∀ E κ τ s t, Step2AvgNetLift sz E κ τ s t := by
  intro E κ τ s t hκ hE hτ hs0 hst ht1 hsize hRange hPT
  set c₁ : ℝ := Real.sqrt (2 * κ) / 2 with hc₁def
  have hc₁ : 0 < c₁ := by
    rw [hc₁def]
    have := Real.sqrt_pos.2 (by linarith : 0 < 2 * κ)
    linarith
  have hbulk : ∀ n, |E n| < 2 ∧ c₁ ≤ (mE (E n)).im := fun n => cont_bulk hκ (hE n)
  have hlen : ∀ n, t n - s n ≤ 1 := fun n => by linarith [hs0 n, ht1 n]
  have hcast : Tendsto (fun n : ℕ => ((sz.size n : ℕ) : ℝ)) atTop atTop := hsize
  have hsizeN : Tendsto sz.size atTop atTop := tendsto_natCast_atTop_iff.mp hcast
  have evc : ∀ᶠ n : ℕ in atTop, 1 / c₁ ≤ ((sz.size n : ℕ) : ℝ) :=
    hcast.eventually_ge_atTop _
  have evR := nl2_evR sz hRange hτ hcast
  have hcard : ∀ n : ℕ, (Fintype.card (Zd d (sz.L n)) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) := by
    intro n
    have hcardZ : Fintype.card (Zd d (sz.L n)) = sz.L n ^ d := by
      simp [Zd, ZMod.card]
    have hW1 : (1 : ℝ) ≤ (sz.W n : ℝ) := by exact_mod_cast sz.W_pos n
    have hL0 : (0 : ℝ) ≤ (sz.L n : ℝ) := Nat.cast_nonneg _
    have hLW : (sz.L n : ℝ) ≤ (sz.W n : ℝ) * (sz.L n : ℝ) := le_mul_of_one_le_left hL0 hW1
    have eN : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℝ) * (sz.L n : ℝ)) ^ d := by
      simp [Sizes.size]
    have hLN : (sz.L n : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
      rw [eN]; exact pow_le_pow_left₀ hL0 hLW d
    rw [hcardZ, Real.rpow_one]
    exact_mod_cast hLN
  refine cont_core (V := fun n => Zd d (sz.L n)) hsizeN hst hlen
    (A := 40) (Cv := 1) (by norm_num) (by norm_num) (Eventually.of_forall hcard) hPT
    (cont_highProbAt_good sz hsizeN)
    (ε := fun n => (((sz.size n : ℕ) : ℝ))⁻¹)
    (fun n => inv_nonneg.2 (Nat.cast_nonneg _)) ?_ ?_
  · -- `hlow`
    refine Eventually.of_forall fun n p ω => ?_
    obtain ⟨u, a⟩ := p
    exact cont_inv_size_le_Bctl sz n ((hs0 n).trans u.2.1) (lt_of_le_of_lt u.2.2 (ht1 n))
  · -- `hclose`
    filter_upwards [evc, evR, nl2_eventual hsizeN] with n hc hR hg
    intro ω hω u u' hΔ a
    exact nl2_avg_close sz n ω (N := ((sz.size n : ℕ) : ℝ)) (E := E n) (t := t n) (u := u)
      (u' := u') (A := 40) (c₁ := c₁) rfl (hbulk n).1 ((hs0 n).trans u.2.1) u.2.2
      ((hs0 n).trans u'.2.1) u'.2.2 (ht1 n) hc₁ (hbulk n).2 hc hR (fun c => hω c) hΔ hg.1 hg.2 a

end Main

end RBM.Ind

namespace RBM.Gauss.Sizes

open RBM.Ind

set_option linter.style.longLine false

/-- **The net lift of Step 2 (the pin `STNetLift2`)** for every `d`: the per-time statements
`STStep2LocalPT ∧ STStep2AvgPT ∧ STStep2DecayPT` give the `u`-uniform `STStep2Local ∧ STStep2Avg ∧
STStep2Decay`, for every `C_d`.  The three conjuncts are independent: `step2LocalNetLift`,
`step2AvgNetLift` (this file) and `stNetLift2_part1` (`NetLift1`, T2074).  `STFlow` with
`t ≤ lemT z` gives the premises of the lifts (`Green.v3_premises_of_stFlow`: `|E_n| < 2 - κ/2`,
`t_n < 1`, `1 - t_n ≥ N^{-1+ε/2}`, `N → ∞`), at `κ/2`, `τ = ε/2`.  The merged pin of
`Induction/Step2Defs.lean:581`; its owed registry line (`RBM3D/Test/Axioms.lean`) is discharged
by this theorem. -/
theorem stNetLift2_holds (d : ℕ) : STNetLift2 d := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s t hs0 hst ht Cd hL hA hD
  obtain ⟨hA', hE, hlt, hR⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow ht
  exact ⟨step2LocalNetLift sz (STflowE z) (κ / 2) (ε / 2) s t (half_pos hκ)
      (fun n => (hE n).le) (half_pos hε) hs0 hst hlt hA'.2.2.1 hR hL,
    step2AvgNetLift sz (STflowE z) (κ / 2) (ε / 2) s t (half_pos hκ)
      (fun n => (hE n).le) (half_pos hε) hs0 hst hlt hA'.2.2.1 hR hA,
    stNetLift2_part1 d κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s t hs0 hst ht Cd hD⟩

end RBM.Gauss.Sizes

namespace RBM.Ind

set_option linter.style.longLine false

/-! ## 5. Compiled nonempty instances at `d = 3`

The size data are the merged preflight sequence `RBM.Gauss.SizesInst.sz0` (`L_n = 4(n+1)`,
`W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6} → 0`, `N_n = (W_n L_n)^3`; `n = 0`: `L = 4`, `W = 32`,
`N = 2097152`), admissible at `𝔠 = 1/6`, `𝔡 = 1/10`; the flow points `z_n = 1/2 + i N_n^{-4/5}`
(`κ = ε = 1/10`, `E_n = lemE z_n`, `|E_n| ≤ 1/2`), `s ≡ 0`, `t ≡ 1/16 ≤ t₀ = lemT z_n`
(`RBM3D/Induction/Defs.lean`, section 3).  Every deterministic hypothesis is discharged; what stays
a hypothesis is the per-time statement itself (`STStep2LocalPT`, `STStep2AvgPT`, `STStep2DecayPT`:
the stochastic inputs of the Step 2 chain, ST2-04). -/

section Instances

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst

/-- `Step2LocalNetLift` at the flow of the instance (`κ = τ = (1/10)/2`, `s ≡ 0`, `t ≡ 1/16`). -/
example : Step2LocalNetLift sz0 (STflowE z0) ((1 / 10) / 2) ((1 / 10) / 2) sInst tInst :=
  step2LocalNetLift sz0 _ _ _ _ _

/-- `step2LocalNetLift`, fully applied: every hypothesis (`0 < κ`, `|E_n| ≤ 2 - κ`, `0 < τ`,
`0 ≤ s ≤ t < 1`, `N → ∞`, `RangeCond`) is discharged; `STStep2LocalPT` stays the hypothesis of the
implication. -/
example (hL : STStep2LocalPT sz0 (STflowE z0) sInst tInst) :
    STStep2Local sz0 (STflowE z0) sInst tInst :=
  step2LocalNetLift sz0 (STflowE z0) ((1 / 10) / 2) ((1 / 10) / 2) sInst tInst
    (by norm_num) (fun n => (RBM.Green.Instance.premises.2.1 n).le) (by norm_num) (fun _ => le_rfl)
    (fun n => by simp only [sInst, tInst]; norm_num) RBM.Green.Instance.premises.2.2.2.1
    sz0_tendsto RBM.Green.Instance.premises.2.2.2.2 hL

/-- `Step2AvgNetLift` at the flow of the instance. -/
example : Step2AvgNetLift sz0 (STflowE z0) ((1 / 10) / 2) ((1 / 10) / 2) sInst tInst :=
  step2AvgNetLift sz0 _ _ _ _ _

/-- `step2AvgNetLift`, fully applied: `STStep2AvgPT` stays the hypothesis of the implication. -/
example (hA : STStep2AvgPT sz0 (STflowE z0) sInst tInst) :
    STStep2Avg sz0 (STflowE z0) sInst tInst :=
  step2AvgNetLift sz0 (STflowE z0) ((1 / 10) / 2) ((1 / 10) / 2) sInst tInst
    (by norm_num) (fun n => (RBM.Green.Instance.premises.2.1 n).le) (by norm_num) (fun _ => le_rfl)
    (fun n => by simp only [sInst, tInst]; norm_num) RBM.Green.Instance.premises.2.2.2.1
    sz0_tendsto RBM.Green.Instance.premises.2.2.2.2 hA

/-- `stNetLift2_holds` at `d = 3`: `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `sz0`, `z0`, `STFlow`
(`flow_z0`), `0 ≤ s ≤ t ≤ lemT z_n` (`sixteenth_le_lemT`); the three per-time statements stay
hypotheses, at an arbitrary constant `C_d`. -/
example (Cd : ℝ) (hL : STStep2LocalPT sz0 (STflowE z0) sInst tInst)
    (hA : STStep2AvgPT sz0 (STflowE z0) sInst tInst)
    (hD : STStep2DecayPT sz0 Cd (STflowE z0) sInst tInst) :
    STStep2Local sz0 (STflowE z0) sInst tInst ∧ STStep2Avg sz0 (STflowE z0) sInst tInst ∧
      STStep2Decay sz0 Cd (STflowE z0) sInst tInst :=
  stNetLift2_holds 3 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 sInst tInst (fun _ => le_rfl)
    (fun n => by simp only [sInst, tInst]; norm_num) (fun n => sixteenth_le_lemT n) Cd hL hA hD

end Instances

end RBM.Ind
