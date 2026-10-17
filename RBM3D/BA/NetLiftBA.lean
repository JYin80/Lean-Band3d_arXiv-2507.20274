/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step2Gen
import RBM3D.BA.TwistLoop
import RBM3D.BA.Step1Setup
import RBM3D.BA.EMn2BA
import RBM3D.BA.KInduct
import RBM3D.BA.EKPins
import RBM3D.BA.KBase
import RBM3D.BA.GreenSchur
import RBM3D.Path.NetLift1
import RBM3D.Path.NetLift2
import RBM3D.Induction.ContinuityNet

/-!
# Sub-stage T, producer P2 (T2461): the net lift of Step 2 at the block Anderson carrier

Ticket `docs/tickets/T2461.md`; DECISIONS §268; U-D report `docs/reports/T2452-design.md` D3 (ii).
Paper: arXiv:2507.20274, `1_2:1400` (the estimates of each step of Step 2 hold uniformly in
`u ∈ [s,t]` by a standard `N^{-C}`-net and perturbation argument); at BA `7_8:1993-1994`.

* **Target 1** `baNetLift2_holds`: the generic pin `STNetLift2gL` at the block Anderson law
  `seqP (sz.withLam 0)`, setting `BAFlow`, carrier `baFMz` and horizon `BAflowT0`, for every `d`.
  BA-direct: per family, `cont_core` (`ContinuityNet`) on `TimeIcc s t n × V n` with the good event
  `contGood (sz.withLam 0)`, as `baNetLift` (`Step1Setup`); the moduli are the resolvent moduli
  of `Step1Setup` and the one new BA modulus, the time Lipschitz bound of `𝒦^{(2)}`
  (`baKsol_two`, every charge pair).
* **Target 2** `baFlow_premises`: `t_n < 1` and `RangeCond (ε/2) t` from `BAFlow` and
  `t ≤ BAflowT0`.
* Compiled nonempty instances at `d = 3` (section 7).

Private helpers carry the stem `NetLiftBA_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false

open MeasureTheory Filter
open scoped Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Ind RBM.Ind.ContinuityNet

open private BASetup_entry_diff BASetup_H_sub BASetup_zdiff BASetup_eta_le BASetup_eta_inv_le BASetup_herm
  BASetup_X_norm BASetup_word_diff BASetup_loopFine_eq BASetup_GM_zero BASetup_norm_BAmF_le_one
  from RBM3D.BA.Step1Setup
open private BAKBase_sub from RBM3D.BA.KBase
open private TwistKer2_norm_winv from RBM3D.BA.TwistKer2
open private nl2_STWB_nonneg nl2_STWB_ratio nl2_STWB_low nl2_eventual nl2_evR from RBM3D.Path.NetLift2
open private nl_zeta_ratio nl_c_le nl_exp_ell nl_R_le nl_one_le_d nl_STWB_ratio from RBM3D.Path.NetLift1

/-! ## 1. Target 2: the BA premises of the flow -/

/-- **Target 2** (`T2461_BAFlowPremises`; the probe `T2452_ba_premises`, `t/T2452:RBM3D/Probe/T2452Pins.lean:177-195`): the BA reading
of the band premises lemma (`Green/Pins.lean:1049`) without its spectral conjunct: `t_n < 1` and `RangeCond (ε/2) t` from `BAFlow` and
`t ≤ BAflowT0` (`1 - t₀ ≥ Im z/2 ≥ N^{-1+ε}/2`, `EMn2BA_one_sub_T0`, and `N^{ε/2} ≥ 2` eventually). -/
theorem baFlow_premises (d : ℕ) :
    ∀ (κ ε 𝔠 𝔡 : ℝ), 0 < κ → 0 < ε → ∀ (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, t n ≤ BAflowT0 sz z n) → (∀ n, t n < 1) ∧ sz.RangeCond (ε / 2) t := by
  intro κ ε 𝔠 𝔡 hκ hε sz z hflow t htT
  refine ⟨fun n => lt_of_le_of_lt (htT n) (EMn2BA_T0_lt_one hκ sz hflow n), ?_⟩
  have hN := sz.tendsto_size hflow.1.2.2.1
  filter_upwards [hN.eventually (eventually_le_rpow 2 (half_pos hε))] with n hn
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hsplit : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) =
      ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2) * ((sz.size n : ℕ) : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hpos : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2) := Real.rpow_nonneg hN0.le _
  have h5 : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2) * 2 ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) := by
    rw [hsplit]; exact mul_le_mul_of_nonneg_left hn hpos
  have h6 : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ (z n).im := (hflow.2 n).2.1
  have h7 := EMn2BA_one_sub_T0 hκ sz hflow n
  change ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2) ≤ 1 - t n
  linarith [htT n]

/-! ## 2. The new BA modulus: `𝒦^{(2)}` is Lipschitz in time, every charge pair -/

section KDiff

open scoped Matrix.Norms.Operator

variable {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} {sz : Sizes d} {z : ℕ → ℂ}

/-- **`𝒦^{(2)}` moves by at most `|u - u'| (1-u)⁻¹ (1-u')⁻¹`** for every charge pair `σ ∈ {±}²` (same-charge included) and
every `a ∈ (Z_L^d)²`: `𝒦^{(2)}_{u,σ,a} = W^{-d} (Θ_u^{(σ₀σ₁)} M^{(σ₀σ₁)})(a₀, a₁)` (`baKsol_two`, `0 < g₀`, `BAReal` by
`BAflow_real`), `Θ_u - Θ_{u'} = (u - u') Θ_u M Θ_{u'}` (`BAKBase_sub`), `‖Θ_v‖_{∞→∞} ≤ (1-v)⁻¹` (`EKPins_norm_Theta_le`),
`‖M^{(σ₀σ₁)}‖_{∞→∞} ≤ 1` (`EKPins_norm_Q_le`), `W^{-d} ≤ 1`.  Pattern `TwistLoop_K_diff` (`TwistLoop.lean:208`). -/
private theorem NetLiftBA_K_diff (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) (hg : 0 < BAflowLam0 sz z n)
    {u u' : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hu'0 : 0 ≤ u') (hu'1 : u' < 1) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) :
    ‖(baFMz sz z).K n u σ a - (baFMz sz z).K n u' σ a‖ ≤ |u - u'| * ((1 - u)⁻¹ * (1 - u')⁻¹) := by
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  set Q := BAMss d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ)
    (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 0) (σ 1) with hQdef
  have hQ : ‖Q‖ ≤ 1 := EKPins_norm_Q_le hr (σ 0) (σ 1)
  have hΘu : ‖PropThetaQ Q u‖ ≤ (1 - u)⁻¹ := EKPins_norm_Theta_le hr hu0 hu1 (σ 0) (σ 1)
  have hΘu' : ‖PropThetaQ Q u'‖ ≤ (1 - u')⁻¹ := EKPins_norm_Theta_le hr hu'0 hu'1 (σ 0) (σ 1)
  have hsub := BAKBase_sub hQ (abs_lt.2 ⟨by linarith, hu1⟩ : |u| < 1) (abs_lt.2 ⟨by linarith, hu'1⟩ : |u'| < 1)
  have hK : ∀ v : ℝ, 0 ≤ v → v < 1 → (baFMz sz z).K n v σ a =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (PropThetaQ Q v * Q) (a 0) (a 1) := fun v hv0 hv1 =>
    baKsol_two d hκ hg (sz.three_le_L n) (sz.W n) hr ⟨hv0, hv1⟩ σ a
  have hmat : (PropThetaQ Q u * Q) - (PropThetaQ Q u' * Q) =
      ((u - u' : ℝ) : ℂ) • (PropThetaQ Q u * Q * PropThetaQ Q u' * Q) := by
    rw [← sub_mul, hsub, smul_mul_assoc]
  have hnorm : ‖(PropThetaQ Q u * Q) - (PropThetaQ Q u' * Q)‖ ≤ |u - u'| * ((1 - u)⁻¹ * (1 - u')⁻¹) := by
    rw [hmat, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have h1 : ‖PropThetaQ Q u * Q * PropThetaQ Q u' * Q‖ ≤ ‖PropThetaQ Q u‖ * ‖Q‖ * ‖PropThetaQ Q u'‖ * ‖Q‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))) (norm_nonneg _))
    refine h1.trans ?_
    have hi : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 (by linarith)
    have hi' : 0 ≤ (1 - u')⁻¹ := inv_nonneg.2 (by linarith)
    calc ‖PropThetaQ Q u‖ * ‖Q‖ * ‖PropThetaQ Q u'‖ * ‖Q‖ ≤ (1 - u)⁻¹ * 1 * (1 - u')⁻¹ * 1 :=
          mul_le_mul (mul_le_mul (mul_le_mul hΘu hQ (norm_nonneg _) hi) hΘu' (norm_nonneg _)
            (by positivity)) hQ (norm_nonneg _) (by positivity)
      _ = (1 - u)⁻¹ * (1 - u')⁻¹ := by ring
  rw [hK u hu0 hu1, hK u' hu'0 hu'1, ← mul_sub, norm_mul, TwistKer2_norm_winv n, ← Matrix.sub_apply]
  have hW1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 := by
    have : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    exact inv_le_one_of_one_le₀ (one_le_pow₀ this)
  have hent : ‖((PropThetaQ Q u * Q) - (PropThetaQ Q u' * Q)) (a 0) (a 1)‖ ≤
      ‖(PropThetaQ Q u * Q) - (PropThetaQ Q u' * Q)‖ :=
    (Finset.single_le_sum (f := fun b => ‖((PropThetaQ Q u * Q) - (PropThetaQ Q u' * Q)) (a 0) b‖)
      (fun b _ => norm_nonneg _) (Finset.mem_univ (a 1))).trans (sum_norm_row_le _ (a 0))
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ‖((PropThetaQ Q u * Q) - (PropThetaQ Q u' * Q)) (a 0) (a 1)‖
      ≤ 1 * ‖(PropThetaQ Q u * Q) - (PropThetaQ Q u' * Q)‖ :=
        mul_le_mul hW1 hent (norm_nonneg _) zero_le_one
    _ ≤ _ := by rw [one_mul]; exact hnorm

end KDiff

/-! ## 3. The resolvent and loop moduli along the block Anderson flow at an arbitrary carrier `baFM sz lam0 E`

The band moduli (`NetLift1-2`) carry the band energy and its spectral data; here the bulk data are
`κ ≤ Im m`, `‖m‖ ≤ 1`, `(1 - t)⁻¹ ≤ N` (as `Step1Setup`'s `BASetup_*_close`), and `M = BAMfine` (time independent). -/

section Moduli

open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

/-- **The modulus of a loop of length `k` in the norm of the difference** (`BASetup_loopAbs_diff`, `Step1Setup.lean:519`, without its
last step `abs_norm_sub_norm_le`): for two Hermitian matrices with `H - H' = c X`,
`‖loopFine H z σ a - loopFine H' z' σ a‖ ≤ #Vtx · k Q^k (Q² (Xb + 1) √Δ)`. -/
private theorem NetLiftBA_loop_sub {L W : ℕ} [NeZero L] [NeZero W] (hW : 1 ≤ W)
    {H H' X : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian) {c : ℝ} (hd : H - H' = (c : ℂ) • X)
    {z z' : ℂ} {η Q Xb Δ : ℝ} (hη : 0 < η) (hQ1 : 1 ≤ Q) (hQ : η⁻¹ ≤ Q) (hz : η ≤ |z.im|)
    (hz' : η ≤ |z'.im|) (hzz : ‖z - z'‖ ≤ Δ) (hc : |c| ≤ Real.sqrt Δ) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1)
    (hXb : ‖blockMat d L W X‖ ≤ Xb) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    ‖loopFine d L W H z σ a - loopFine d L W H' z' σ a‖ ≤
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
  rw [BASetup_loopFine_eq, BASetup_loopFine_eq, ← Matrix.trace_sub]
  refine (norm_matrix_trace_le_card_mul _).trans ?_
  exact mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)

/-- `‖G_v(x,y)‖ ≤ N²` for `0 ≤ v ≤ t < 1` (an entry is at most the resolvent norm, `norm_Gsig_le_inv_eta`, `‖G‖ ≤ (η_t)⁻¹ ≤ N²`). -/
private theorem NetLiftBA_G_le (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ) {N t v κ : ℝ}
    (hN : N = ((sz.size n : ℕ) : ℝ)) (hv0 : 0 ≤ v) (hvt : v ≤ t) (ht : t < 1) (hκ : 0 < κ)
    (hmκ : κ ≤ (BAmF sz lam0 E n).im) (hNc : 1 / κ ≤ N) (hN1 : (1 - t)⁻¹ ≤ N)
    (x y : Idx d (sz.L n) (sz.W n)) : ‖(baFM sz lam0 E).G n v ω x y‖ ≤ N ^ 2 := by
  have hNge : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  have hm0 : 0 ≤ (BAmF sz lam0 E n).im := (hκ.trans_le hmκ).le
  have hQ : (etaOf (BAmF sz lam0 E n) t)⁻¹ ≤ N ^ 2 := BASetup_eta_inv_le hN0 hκ hmκ hNc hN1
  have hη : 0 < etaOf (BAmF sz lam0 E n) t := by
    unfold etaOf
    exact mul_pos (by linarith) (hκ.trans_le hmκ)
  have h := (RBM.Ind.norm_apply_le_l2_opNorm _ x y).trans
    (RBM.Gauss.norm_Gsig_le_inv_eta (BASetup_herm sz lam0 n v ω) hη
      (BASetup_eta_le _ (E n) hm0 ht hvt) true)
  exact h.trans hQ

/-- **The entry modulus** `‖(G_u - G_{u'})_{xy}‖ ≤ 3 N⁶ N^{-A/2}` on the good event for `|u - u'| ≤ N^{-A}`, `u, u' ≤ t < 1`
(`BASetup_entry_diff`, `Q = N²`, `Xb = 2N²`; the middle of `BASetup_WL_close`, `Step1Setup.lean:787`). -/
private theorem NetLiftBA_G_diff (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ)
    {N t u u' A κ : ℝ} (hN : N = ((sz.size n : ℕ) : ℝ))
    (hu0 : 0 ≤ u) (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t) (ht : t < 1)
    (hκ : 0 < κ) (hmκ : κ ≤ (BAmF sz lam0 E n).im) (hm1 : ‖BAmF sz lam0 E n‖ ≤ 1)
    (hNc : 1 / κ ≤ N) (hN1 : (1 - t)⁻¹ ≤ N)
    (hgood : ∀ c : CoordF d (sz.L n) (sz.W n), |sz.slice n ω c| ≤ N)
    (hy : |u - u'| ≤ N ^ (-A)) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖(baFM sz lam0 E).G n u ω x y - (baFM sz lam0 E).G n u' ω x y‖ ≤ 3 * N ^ 6 * N ^ (-A / 2) := by
  have hNge : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
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
  refine hent.trans ?_
  have e1 : N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1) * Real.sqrt |u - u'| =
      (2 * N ^ 6 + N ^ 4) * Real.sqrt |u - u'| := by ring
  rw [e1]
  calc (2 * N ^ 6 + N ^ 4) * Real.sqrt |u - u'| ≤ 3 * N ^ 6 * Real.sqrt |u - u'| :=
        mul_le_mul_of_nonneg_right (by linarith) hs0'
    _ ≤ 3 * N ^ 6 * N ^ (-A / 2) := mul_le_mul_of_nonneg_left hsq (by positivity)

/-- **The loop modulus** `‖𝓛^{(k)}_u - 𝓛^{(k)}_{u'}‖ ≤ N · k (N²)^k · 3 N⁶ N^{-A/2}` on the good event for
`|u - u'| ≤ N^{-A}`, `u, u' ≤ t < 1` (`NetLiftBA_loop_sub`; the first half of `BASetup_LP_close`, `Step1Setup.lean:712`). -/
private theorem NetLiftBA_L_diff (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ)
    {N t u u' A κ : ℝ} {k : ℕ} (hN : N = ((sz.size n : ℕ) : ℝ))
    (hu0 : 0 ≤ u) (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t) (ht : t < 1)
    (hκ : 0 < κ) (hmκ : κ ≤ (BAmF sz lam0 E n).im) (hm1 : ‖BAmF sz lam0 E n‖ ≤ 1)
    (hNc : 1 / κ ≤ N) (hN1 : (1 - t)⁻¹ ≤ N)
    (hgood : ∀ c : CoordF d (sz.L n) (sz.W n), |sz.slice n ω c| ≤ N)
    (hy : |u - u'| ≤ N ^ (-A)) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    ‖(baFM sz lam0 E).L n u σ a ω - (baFM sz lam0 E).L n u' σ a ω‖ ≤
      N * ((k : ℝ) * (N ^ 2) ^ k * (3 * N ^ 6 * N ^ (-A / 2))) := by
  have hNge : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hΔ1 : |u - u'| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hsq : Real.sqrt |u - u'| ≤ N ^ (-A / 2) := cont_sqrt_abs_le hN0.le hy
  have hm0 : 0 ≤ (BAmF sz lam0 E n).im := (hκ.trans_le hmκ).le
  have hQ : (etaOf (BAmF sz lam0 E n) t)⁻¹ ≤ N ^ 2 := BASetup_eta_inv_le hN0 hκ hmκ hNc hN1
  have hη : 0 < etaOf (BAmF sz lam0 E n) t := by
    unfold etaOf
    exact mul_pos h1t (hκ.trans_le hmκ)
  have hQ1 : 1 ≤ N ^ 2 := one_le_pow₀ hNge
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
  have hloop := NetLiftBA_loop_sub (sz.W_pos n) (BASetup_herm sz lam0 n u ω)
    (BASetup_herm sz lam0 n u' ω) (BASetup_H_sub sz lam0 n u u' ω) hη hQ1 hQ
    (BASetup_eta_le _ (E n) hm0 ht hut) (BASetup_eta_le _ (E n) hm0 ht hu't)
    (BASetup_zdiff _ _ u u' hm1) (cont_abs_sqrt_sub_sqrt_le hu0 hu'0) (abs_nonneg _) hΔ1 hXb σ a
  rw [hcardB] at hloop
  have hS : N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1) * Real.sqrt |u - u'| ≤
      3 * N ^ 6 * N ^ (-A / 2) := by
    have e1 : N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1) ≤ 3 * N ^ 6 := by
      have : N ^ 4 ≤ N ^ 6 := pow_le_pow_right₀ hNge (by norm_num)
      nlinarith
    exact mul_le_mul e1 hsq (Real.sqrt_nonneg _) (by positivity)
  exact hloop.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hS (by positivity)) hN0.le)

/-- **The two conclusions of `hclose` for the local family** at one index `n`, deterministic:
`‖G_u - M‖²_{xy} ≤ ‖G_{u'} - M‖²_{xy} + N⁻¹` and `STWB_{u',K} ≤ 2 STWB_{u,K}` (the band local close lemma, `NetLift2.lean:339`; the
bound on `‖G_{u'} - M‖_{xy} ≤ 2N²` replaces `N² + 1`: `M = G_0`, `‖G_0‖ ≤ N²`). -/
private theorem NetLiftBA_loc_close (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ)
    {N t u u' A κ : ℝ} (hN : N = ((sz.size n : ℕ) : ℝ))
    (hu0 : 0 ≤ u) (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t) (ht : t < 1)
    (hκ : 0 < κ) (hmκ : κ ≤ (BAmF sz lam0 E n).im) (hm1 : ‖BAmF sz lam0 E n‖ ≤ 1)
    (hNc : 1 / κ ≤ N) (hN1 : (1 - t)⁻¹ ≤ N)
    (hgood : ∀ c : CoordF d (sz.L n) (sz.W n), |sz.slice n ω c| ≤ N)
    (hy : |u - u'| ≤ N ^ (-A)) (g2 : N * N ^ (-A) ≤ 1 / 10)
    (g3 : 15 * N ^ 9 * N ^ (-A / 2) ≤ N⁻¹) (K : ℕ) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖(baFM sz lam0 E).GM n u ω x y‖ ^ 2 ≤ ‖(baFM sz lam0 E).GM n u' ω x y‖ ^ 2 + N⁻¹ ∧
      STWB sz n u' K ≤ 2 * STWB sz n u K := by
  have hNge : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  have hR0 : 0 ≤ N ^ (-A / 2) := Real.rpow_nonneg hN0.le _
  have hN9 : N ^ 8 ≤ N ^ 9 := pow_le_pow_right₀ hNge (by norm_num)
  set δ : ℝ := 3 * N ^ 6 * N ^ (-A / 2) with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  have hbound := NetLiftBA_G_diff sz lam0 E n ω hN hu0 hut hu'0 hu't ht hκ hmκ hm1 hNc hN1 hgood hy x y
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
  · have hdiff : (baFM sz lam0 E).GM n u ω x y - (baFM sz lam0 E).GM n u' ω x y =
        (baFM sz lam0 E).G n u ω x y - (baFM sz lam0 E).G n u' ω x y := by
      change (baFM sz lam0 E).G n u ω x y - (baFM sz lam0 E).M n x y -
        ((baFM sz lam0 E).G n u' ω x y - (baFM sz lam0 E).M n x y) = _
      rw [sub_sub_sub_cancel_right]
    have habs := abs_norm_sub_norm_le ((baFM sz lam0 E).GM n u ω x y) ((baFM sz lam0 E).GM n u' ω x y)
    rw [hdiff] at habs
    have hab : ‖(baFM sz lam0 E).GM n u ω x y‖ ≤ ‖(baFM sz lam0 E).GM n u' ω x y‖ + δ := by
      have := (abs_le.1 (habs.trans hbound)).2
      linarith
    -- `‖b‖ ≤ 2 N²`: `M = G_0`
    have hMG : (baFM sz lam0 E).M n x y = (baFM sz lam0 E).G n 0 ω x y := by
      have h0 := BASetup_GM_zero sz lam0 E n ω x y
      change (baFM sz lam0 E).G n 0 ω x y - (baFM sz lam0 E).M n x y = 0 at h0
      exact (sub_eq_zero.1 h0).symm
    have hb : ‖(baFM sz lam0 E).GM n u' ω x y‖ ≤ 2 * N ^ 2 := by
      change ‖(baFM sz lam0 E).G n u' ω x y - (baFM sz lam0 E).M n x y‖ ≤ _
      refine (norm_sub_le _ _).trans ?_
      rw [hMG]
      have h1 := NetLiftBA_G_le sz lam0 E n ω hN hu'0 hu't ht hκ hmκ hNc hN1 x y
      have h2 := NetLiftBA_G_le sz lam0 E n ω hN le_rfl (hu'0.trans hu't) ht hκ hmκ hNc hN1 x y
      linarith
    have ha0 : 0 ≤ ‖(baFM sz lam0 E).GM n u ω x y‖ := norm_nonneg _
    have hb0 : 0 ≤ ‖(baFM sz lam0 E).GM n u' ω x y‖ := norm_nonneg _
    have hN2 : (1 : ℝ) ≤ N ^ 2 := one_le_pow₀ hNge
    calc ‖(baFM sz lam0 E).GM n u ω x y‖ ^ 2 ≤ (‖(baFM sz lam0 E).GM n u' ω x y‖ + δ) ^ 2 :=
          pow_le_pow_left₀ ha0 hab 2
      _ = ‖(baFM sz lam0 E).GM n u' ω x y‖ ^ 2 + δ * (2 * ‖(baFM sz lam0 E).GM n u' ω x y‖ + δ) := by ring
      _ ≤ ‖(baFM sz lam0 E).GM n u' ω x y‖ ^ 2 + δ * (5 * N ^ 2) := by
          refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hδ0)
          nlinarith
      _ ≤ ‖(baFM sz lam0 E).GM n u' ω x y‖ ^ 2 + N⁻¹ := by
          have : δ * (5 * N ^ 2) = 5 * N ^ 2 * δ := by ring
          rw [this]
          exact add_le_add le_rfl hδ5
  · have hx : (1 - t)⁻¹ * |u' - u| ≤ 1 / 10 := by
      rw [abs_sub_comm]
      exact (mul_le_mul hN1 hy (abs_nonneg _) hN0.le).trans g2
    have hr := nl2_STWB_ratio sz n K ht hu't hut
    exact hr.trans (mul_le_mul_of_nonneg_right (by linarith) (nl2_STWB_nonneg sz n K u))

/-- **The two conclusions of `hclose` for the average family** at one index `n`, deterministic:
`‖𝓛^{(1)}_u - m‖ ≤ ‖𝓛^{(1)}_{u'} - m‖ + N⁻¹` and `Bctl(u') ≤ 2 Bctl(u)` (the band average close lemma, `NetLift2.lean:439`; `m = BAmF`
does not depend on `u`). -/
private theorem NetLiftBA_avg_close (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ)
    {N t u u' A κ : ℝ} (hN : N = ((sz.size n : ℕ) : ℝ))
    (hu0 : 0 ≤ u) (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t) (ht : t < 1)
    (hκ : 0 < κ) (hmκ : κ ≤ (BAmF sz lam0 E n).im) (hm1 : ‖BAmF sz lam0 E n‖ ≤ 1)
    (hNc : 1 / κ ≤ N) (hN1 : (1 - t)⁻¹ ≤ N)
    (hgood : ∀ c : CoordF d (sz.L n) (sz.W n), |sz.slice n ω c| ≤ N)
    (hy : |u - u'| ≤ N ^ (-A)) (g2 : N * N ^ (-A) ≤ 1 / 10)
    (g3 : 15 * N ^ 9 * N ^ (-A / 2) ≤ N⁻¹) (a : Zd d (sz.L n)) :
    ‖(baFM sz lam0 E).L n u (fun _ : Fin 1 => true) (fun _ => a) ω - (baFM sz lam0 E).m n‖ ≤
        ‖(baFM sz lam0 E).L n u' (fun _ : Fin 1 => true) (fun _ => a) ω - (baFM sz lam0 E).m n‖ + N⁻¹ ∧
      sz.Bctl n u' ≤ 2 * sz.Bctl n u := by
  have hNge : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  refine ⟨?_, ?_⟩
  · have hloop := NetLiftBA_L_diff sz lam0 E n ω hN hu0 hut hu'0 hu't ht hκ hmκ hm1 hNc hN1 hgood hy
      (fun _ : Fin 1 => true) (fun _ => a)
    have hdiff : ‖(baFM sz lam0 E).L n u (fun _ : Fin 1 => true) (fun _ => a) ω -
        (baFM sz lam0 E).L n u' (fun _ : Fin 1 => true) (fun _ => a) ω‖ ≤ N⁻¹ := by
      refine hloop.trans (le_trans ?_ g3)
      have e : N * (((1 : ℕ) : ℝ) * (N ^ 2) ^ 1 * (3 * N ^ 6 * N ^ (-A / 2))) =
          3 * N ^ 9 * N ^ (-A / 2) := by push_cast; ring
      have hR0 : 0 ≤ N ^ (-A / 2) := Real.rpow_nonneg hN0.le _
      refine le_of_eq_of_le (by simpa using e) ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) (by positivity)) hR0
    have hsplit : (baFM sz lam0 E).L n u (fun _ : Fin 1 => true) (fun _ => a) ω - (baFM sz lam0 E).m n =
        ((baFM sz lam0 E).L n u' (fun _ : Fin 1 => true) (fun _ => a) ω - (baFM sz lam0 E).m n) +
          ((baFM sz lam0 E).L n u (fun _ : Fin 1 => true) (fun _ => a) ω -
            (baFM sz lam0 E).L n u' (fun _ : Fin 1 => true) (fun _ => a) ω) := by ring
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add le_rfl hdiff)
  · have hu1 : u < 1 := lt_of_le_of_lt hut ht
    have hBu : 0 ≤ sz.Bctl n u :=
      (inv_nonneg.2 (Nat.cast_nonneg _)).trans (cont_inv_size_le_Bctl sz n hu0 hu1)
    have hx : (1 - t)⁻¹ * |u' - u| ≤ 1 / 10 := by
      rw [abs_sub_comm]
      exact (mul_le_mul hN1 hy (abs_nonneg _) hN0.le).trans g2
    have hr := cont_Bctl_ratio sz n ht hu't hut
    exact hr.trans (mul_le_mul_of_nonneg_right (by linarith) hBu)

/-- **The control of `STStep2Decay` moves by at most a factor `2` under a small time change** (the second half of the band decay close
lemma, `NetLift1.lean:533`): it involves `sz` only, not the carrier. -/
private theorem NetLiftBA_ctrl_ratio (sz : Sizes d) (n : ℕ) (Cd : ℝ)
    {N s t u u' D A Dg : ℝ} (hN : N = ((sz.size n : ℕ) : ℝ)) (hd : 1 ≤ d)
    (hs0 : 0 ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (hsu' : s ≤ u') (hu't : u' ≤ t)
    (ht : t < 1) (hN1 : (1 - t)⁻¹ ≤ N)
    (hy : |u - u'| ≤ N ^ (-A)) (hg0 : 0 ≤ sz.lam n) (hgD : sz.lam n ≤ Dg)
    (gx : (|Cd| + 2) * (N * N ^ (-A)) ≤ 1 / 4) (gδ : Real.sqrt (Dg * N ^ (2 - A / 2)) ≤ 1 / 4)
    (a : Fin 2 → Zd d (sz.L n)) :
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
  have hsq : Real.sqrt |u - u'| ≤ N ^ (-A / 2) := cont_sqrt_abs_le hN0.le hy
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
      (mul_le_mul_of_nonneg_right (by linarith) (nl2_STWB_nonneg sz n zd u))
  have hexp := nl_exp_ell (L := sz.L n) (by have := sz.three_le_L n; omega) (g := sz.lam n) (t := t)
    (u := u) (u' := u') (z := (zd : ℝ)) hg0 ht hut hu't hz0
  have hδ_in : (zd : ℝ) * (sz.lam n * ((1 - t)⁻¹ * Real.sqrt |u - u'|)) ≤ Dg * N ^ (2 - A / 2) := by
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
  exact nl_zeta_ratio hx0 hRpos hRpos' hRR hRR' hBu hBu' hb' (nl2_STWB_nonneg sz n zd u)
    (nl2_STWB_nonneg sz n zd u') hw' (Real.exp_pos _).le (Real.exp_pos _).le hexp hW0 hc

/-- **The two conclusions of `hclose` for the decay family** at one index `n`, deterministic:
`‖𝓛^{(2)}_u - 𝒦^{(2)}_u‖ ≤ ‖𝓛^{(2)}_{u'} - 𝒦^{(2)}_{u'}‖ + N^{-D}` and `ζ_{u'} ≤ 2 ζ_u` (the band decay close lemma, `NetLift1.lean:533`).
The loop moduli is `NetLiftBA_L_diff` (`k = 2`), the `𝒦^{(2)}` modulus is `NetLiftBA_K_diff` (needs `0 < g₀_n`), the control is
`NetLiftBA_ctrl_ratio` (uses `sz.lam n ≤ Dg`, never `g₀`). -/
private theorem NetLiftBA_decay_close {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (sz : Sizes d) (hκ : 0 < κ)
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) (hg : 0 < BAflowLam0 sz z n) (ω : sz.SeqΩ) (Cd : ℝ)
    {N s t u u' D A Dg : ℝ} (hN : N = ((sz.size n : ℕ) : ℝ)) (hd : 1 ≤ d)
    (hs0 : 0 ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (hsu' : s ≤ u') (hu't : u' ≤ t)
    (ht : t < 1) (hNc : 1 / κ ≤ N) (hN1 : (1 - t)⁻¹ ≤ N)
    (hgood : ∀ c : CoordF d (sz.L n) (sz.W n), |sz.slice n ω c| ≤ N)
    (hy : |u - u'| ≤ N ^ (-A)) (hg0 : 0 ≤ sz.lam n) (hgD : sz.lam n ≤ Dg)
    (gx : (|Cd| + 2) * (N * N ^ (-A)) ≤ 1 / 4) (gδ : Real.sqrt (Dg * N ^ (2 - A / 2)) ≤ 1 / 4)
    (g3 : 6 * N ^ (11 - A / 2) + N ^ (2 - A) ≤ N ^ (-D)) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) :
    ‖(baFMz sz z).L n u σ a ω - (baFMz sz z).K n u σ a‖ ≤
        ‖(baFMz sz z).L n u' σ a ω - (baFMz sz z).K n u' σ a‖ + N ^ (-D) ∧
      ((1 - s) / (1 - u')) ^ Cd * (sz.Bctl n u') ^ (1 / 5 : ℝ) *
          STWB sz n u' (zdistInf d (sz.L n) (a 0 - a 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) u') ^ (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-D) ≤
        2 * (((1 - s) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
          STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-D)) := by
  refine ⟨?_, NetLiftBA_ctrl_ratio sz n Cd hN hd hs0 hsu hut hsu' hu't ht hN1 hy hg0 hgD gx gδ a⟩
  have hNge : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu'0 : 0 ≤ u' := hs0.trans hsu'
  have hu1 : u < 1 := by linarith
  have hu'1 : u' < 1 := by linarith
  have hm := EMn2BA_mF_data sz hflow n
  have hmκ : κ ≤ (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := hm.1
  have hm1 : ‖BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n‖ ≤ 1 :=
    BASetup_norm_BAmF_le_one sz _ _ n (hκ.trans_le hmκ)
  have hloop := NetLiftBA_L_diff sz (BAflowLam0 sz z) (BAflowEs sz z) n ω hN hu0 hut hu'0 hu't ht hκ hmκ
    hm1 hNc hN1 hgood hy σ a
  have hL2 : ‖(baFMz sz z).L n u σ a ω - (baFMz sz z).L n u' σ a ω‖ ≤ 6 * N ^ (11 - A / 2) := by
    refine hloop.trans ?_
    have e : N * (((2 : ℕ) : ℝ) * (N ^ 2) ^ 2 * (3 * N ^ 6 * N ^ (-A / 2))) = 6 * N ^ (11 - A / 2) := by
      rw [show (11 - A / 2) = ((11 : ℕ) : ℝ) + (-A / 2) by push_cast; ring, ← cont_pow_mul_rpow hN0]
      push_cast
      ring
    exact le_of_eq e
  have hK : ‖(baFMz sz z).K n u σ a - (baFMz sz z).K n u' σ a‖ ≤ N ^ (2 - A) := by
    refine (NetLiftBA_K_diff hκ hflow n hg hu0 hu1 hu'0 hu'1 σ a).trans ?_
    have e : N ^ (2 - A) = N * N * N ^ (-A) := by
      rw [show (2 - A) = ((2 : ℕ) : ℝ) + (-A) by push_cast; ring, ← cont_pow_mul_rpow hN0]
      ring
    have hiu : (1 - u)⁻¹ ≤ N := (inv_anti₀ h1t (by linarith)).trans hN1
    have hiu' : (1 - u')⁻¹ ≤ N := (inv_anti₀ h1t (by linarith)).trans hN1
    rw [e, mul_comm (N * N)]
    exact mul_le_mul hy (mul_le_mul hiu hiu' (inv_nonneg.2 (by linarith)) hN0.le) (by positivity)
      (by positivity)
  have hsplit : (baFMz sz z).L n u σ a ω - (baFMz sz z).K n u σ a =
      ((baFMz sz z).L n u' σ a ω - (baFMz sz z).K n u' σ a) +
        ((baFMz sz z).L n u σ a ω - (baFMz sz z).L n u' σ a ω) -
        ((baFMz sz z).K n u σ a - (baFMz sz z).K n u' σ a) := by ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  have := norm_add_le ((baFMz sz z).L n u' σ a ω - (baFMz sz z).K n u' σ a)
    ((baFMz sz z).L n u σ a ω - (baFMz sz z).L n u' σ a ω)
  linarith

end Moduli

/-! ## 4. The three per-family lifts: `cont_core` on `TimeIcc s t n × V n` with the good event `contGood (sz.withLam 0)`

The block Anderson twin of `step2LocalNetLift`, `step2AvgNetLift` (`NetLift2.lean:586, 627`) and `step2NetLift` (`NetLift1.lean:706`), at
the carrier `baFMz`, the law `seqP (sz.withLam 0)`, with the template `baNetLift` (`Step1Setup.lean:877`).  Premises: `BAFlow`
(`κ ≤ Im m`, `‖m‖ ≤ 1`, `N → ∞`, `(eq:WO)`), `t_n < 1` and `RangeCond τ t` (target 2).  No spectral parameter. -/

section Lifts

variable {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}

/-- The bulk data at the flow parameters: `κ ≤ Im m_F`, `‖m_F‖ ≤ 1`. -/
private theorem NetLiftBA_bulk {sz : Sizes d} (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
    κ ≤ (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im ∧
      ‖BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n‖ ≤ 1 := by
  have hm := EMn2BA_mF_data sz hflow n
  exact ⟨hm.1, BASetup_norm_BAmF_le_one sz _ _ n (hκ.trans_le hm.1)⟩

/-- **The lift of the local family**: `STStep2LocalPTgL → STStep2LocalgL` at `baFMz`, `seqP (sz.withLam 0)`.  `V n = Idx × Idx`,
`A = 40`, `#V = N²`, `ε = N⁻¹`, `ξ = ‖G_u - M‖²_{xy}`, `ζ = STWB_{u,|[x]-[y]|}`. -/
private theorem NetLiftBA_local (sz : Sizes d) (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {τ : ℝ} (hτ : 0 < τ)
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hRange : sz.RangeCond τ t) :
    STStep2LocalPTgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t →
      STStep2LocalgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t := by
  intro hPT
  have hsize : sz.SizeTendsto := hflow.1.2.2.1
  have hlen : ∀ n, t n - s n ≤ 1 := fun n => by linarith [hs0 n, ht1 n]
  have hcast : Tendsto (fun n : ℕ => ((sz.size n : ℕ) : ℝ)) atTop atTop := hsize
  have hsizeN : Tendsto sz.size atTop atTop := tendsto_natCast_atTop_iff.mp hcast
  have evc : ∀ᶠ n : ℕ in atTop, 1 / κ ≤ ((sz.size n : ℕ) : ℝ) := hcast.eventually_ge_atTop _
  have evR := nl2_evR sz hRange hτ hcast
  have hcard : ∀ n : ℕ,
      (Fintype.card (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) : ℝ) ≤
        ((sz.size n : ℕ) : ℝ) ^ (2 : ℝ) := by
    intro n
    rw [Fintype.card_prod, Nat.cast_mul, Real.rpow_two, sz.card_Idx n]
    ring_nf; exact le_rfl
  refine cont_core (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) hsizeN
    hst hlen (A := 40) (Cv := 2) (by norm_num) (by norm_num) (Eventually.of_forall hcard) hPT
    (cont_highProbAt_good (sz.withLam 0) hsizeN)
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
    obtain ⟨hmκ, hm1⟩ := NetLiftBA_bulk hκ hflow n
    exact NetLiftBA_loc_close sz (BAflowLam0 sz z) (BAflowEs sz z) n ω (N := ((sz.size n : ℕ) : ℝ))
      (t := t n) (u := u) (u' := u') (A := 40) (κ := κ) rfl ((hs0 n).trans u.2.1) u.2.2
      ((hs0 n).trans u'.2.1) u'.2.2 (ht1 n) hκ hmκ hm1 hc hR (fun c => hω c) hΔ hg.1 hg.2 _ i j

/-- **The lift of the average family**: `STStep2AvgPTgL → STStep2AvggL` at `baFMz`.  `V n = Zd`, `A = 40`, `#V = L^d ≤ N`, `ε = N⁻¹`,
`ξ = ‖𝓛^{(1)}_{u,+,a} - m‖`, `ζ = Bctl(u)`. -/
private theorem NetLiftBA_avg (sz : Sizes d) (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {τ : ℝ} (hτ : 0 < τ)
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hRange : sz.RangeCond τ t) :
    STStep2AvgPTgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t →
      STStep2AvggL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t := by
  intro hPT
  have hsize : sz.SizeTendsto := hflow.1.2.2.1
  have hlen : ∀ n, t n - s n ≤ 1 := fun n => by linarith [hs0 n, ht1 n]
  have hcast : Tendsto (fun n : ℕ => ((sz.size n : ℕ) : ℝ)) atTop atTop := hsize
  have hsizeN : Tendsto sz.size atTop atTop := tendsto_natCast_atTop_iff.mp hcast
  have evc : ∀ᶠ n : ℕ in atTop, 1 / κ ≤ ((sz.size n : ℕ) : ℝ) := hcast.eventually_ge_atTop _
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
    (cont_highProbAt_good (sz.withLam 0) hsizeN)
    (ε := fun n => (((sz.size n : ℕ) : ℝ))⁻¹)
    (fun n => inv_nonneg.2 (Nat.cast_nonneg _)) ?_ ?_
  · -- `hlow`
    refine Eventually.of_forall fun n p ω => ?_
    obtain ⟨u, a⟩ := p
    exact cont_inv_size_le_Bctl sz n ((hs0 n).trans u.2.1) (lt_of_le_of_lt u.2.2 (ht1 n))
  · -- `hclose`
    filter_upwards [evc, evR, nl2_eventual hsizeN] with n hc hR hg
    intro ω hω u u' hΔ a
    obtain ⟨hmκ, hm1⟩ := NetLiftBA_bulk hκ hflow n
    exact NetLiftBA_avg_close sz (BAflowLam0 sz z) (BAflowEs sz z) n ω (N := ((sz.size n : ℕ) : ℝ))
      (t := t n) (u := u) (u' := u') (A := 40) (κ := κ) rfl ((hs0 n).trans u.2.1) u.2.2
      ((hs0 n).trans u'.2.1) u'.2.2 (ht1 n) hκ hmκ hm1 hc hR (fun c => hω c) hΔ hg.1 hg.2 a

/-- **The lift of the decay family**: `STStep2DecayPTgL → STStep2DecaygL` at `baFMz`, for every `C_d`.  `V n = {±}² × (Z_L^d)²`,
`A = 4 D + 40`, `#V ≤ 4 N² ≤ N³`, `ε = N^{-D}`; the loop modulus is `NetLiftBA_L_diff`, the `𝒦^{(2)}` modulus `NetLiftBA_K_diff` (eventually
`0 < g₀_n`, `BAflow_lam0_window`), the control ratio uses `0 ≤ sz.lam n ≤ 𝔡⁻¹` (`WO`). -/
private theorem NetLiftBA_decay (sz : Sizes d) (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {τ : ℝ} (hτ : 0 < τ)
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hRange : sz.RangeCond τ t)
    (Cd : ℝ) :
    STStep2DecayPTgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) Cd s t →
      STStep2DecaygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) Cd s t := by
  intro hPT D hD
  have hsize : sz.SizeTendsto := hflow.1.2.2.1
  have hWO : sz.WO 𝔡 := hflow.1.2.2.2.2
  have hlen : ∀ n, t n - s n ≤ 1 := fun n => by linarith [hs0 n, ht1 n]
  have hd1 : 1 ≤ d := nl_one_le_d sz hsize
  set A : ℝ := 4 * D + 40 with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; linarith
  have hcast : Tendsto (fun n : ℕ => ((sz.size n : ℕ) : ℝ)) atTop atTop := hsize
  have hsizeN : Tendsto sz.size atTop atTop := tendsto_natCast_atTop_iff.mp hcast
  have ev1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hcast.eventually_ge_atTop 1
  have ev4 : ∀ᶠ n : ℕ in atTop, (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hcast.eventually_ge_atTop 4
  have evc : ∀ᶠ n : ℕ in atTop, 1 / κ ≤ ((sz.size n : ℕ) : ℝ) := hcast.eventually_ge_atTop _
  have evR := nl2_evR sz hRange hτ hcast
  have evg0 : ∀ᶠ n : ℕ in atTop, 0 < BAflowLam0 sz z n :=
    (BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow).mono fun n hn => hn.1
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
    (cont_highProbAt_good (sz.withLam 0) hsizeN)
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
        (nl2_STWB_nonneg sz n _ _)) (Real.exp_pos _).le
    linarith
  · -- `hclose`
    filter_upwards [evc, evR, evW, evgx, evgδ, evg3, evg0] with n hc hR hW gx gδ g3 hg
    intro ω hω u u' hΔ v
    obtain ⟨σ, a⟩ := v
    exact NetLiftBA_decay_close sz hκ hflow n hg ω Cd (N := ((sz.size n : ℕ) : ℝ)) (s := s n)
      (t := t n) (u := u) (u' := u') (D := D) (A := A) (Dg := 𝔡⁻¹) rfl hd1 (hs0 n)
      u.2.1 u.2.2 u'.2.1 u'.2.2 (ht1 n) hc hR (fun c => hω c) hΔ hW.1 hW.2 gx gδ g3 σ a

end Lifts

/-! ## 5. Target 1: the pin `STNetLift2gL` at the block Anderson carrier -/

/-- **Target 1** (`T2461_NetLift2BA`; U-D D6 `docs/reports/T2452-design.md:193`): the net lift of Step 2 at the block Anderson reading, the
pin `STNetLift2gL` (`Chain/Step2Gen.lean:602`) at the law `seqP (sz.withLam 0)`, the setting `BAFlow`, the carrier `baFMz` and the horizon
`BAflowT0` (the arguments of `BAStep2`, `FlowPins.lean:432`), for every `d` and every `C_d`: the per-time statements
`STStep2LocalPTgL ∧ STStep2AvgPTgL ∧ STStep2DecayPTgL` give the uniform-in-`u ∈ [s,t]` ones.  BA-direct: per family `cont_core` with the good
event `contGood (sz.withLam 0)` (`NetLiftBA_local`, `NetLiftBA_avg`, `NetLiftBA_decay`); the premises `t_n < 1`, `RangeCond (ε/2) t` are
`baFlow_premises`.  No spectral premise, no dimension guard, no smallness of `g`. -/
theorem baNetLift2_holds (d : ℕ) :
    STNetLift2gL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s t hs0 hst htT Cd hL hA hD
  obtain ⟨ht1, hR⟩ := baFlow_premises d κ ε 𝔠 𝔡 hκ hε sz z hflow t htT
  exact ⟨NetLiftBA_local sz hκ hflow (half_pos hε) hs0 hst ht1 hR hL,
    NetLiftBA_avg sz hκ hflow (half_pos hε) hs0 hst ht1 hR hA,
    NetLiftBA_decay sz hκ hflow (half_pos hε) hs0 hst ht1 hR Cd hD⟩

/-! ## 6. Compiled nonempty instances at `d = 3`

The size data are the merged preflight sequence `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `g_n = (2(n+1))^{-6} → 0`,
`N_n = (W_n L_n)^3`; `n = 0`: `L = 4`, `W = 32`, `N = 2097152`), the spectral parameters `zSeq` with
`BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` (`flow_sz0`), `κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`, and the horizon
`t₀_n ≥ 2/3` (`t0_sz0`).  Instance (a): `s ≡ 1/2`, `t ≡ 2/3 ≤ t₀`; instance (b): `s ≡ 0`, `t ≡ 1/2 < t₀` (`half_lt_t0`),
the start of the Step-2 chain.  Every deterministic hypothesis is discharged (`0 < κ`, `0 < ε`, `0 < 𝔡`, `BAFlow`,
`0 ≤ s ≤ t ≤ t₀`); what stays a hypothesis is the three per-time statements `STStep2LocalPTgL`, `STStep2AvgPTgL`,
`STStep2DecayPTgL` themselves (the stochastic inputs of Step 2, at an arbitrary constant `C_d`). -/

end RBM.BA

end
