/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.MAPins
import RBM3D.BA.MainIndTermBA
import RBM3D.BA.RandomLayerBGBA
import RBM3D.BA.GreenSchur
import RBM3D.BA.EMn2BA
import RBM3D.BA.Ward
import RBM3D.Main.FixedZ
import RBM3D.Main.ZTransfer
import RBM3D.Main.ZNet

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Univ RBM.Endpoints

open private FlowPins_eig_le from RBM3D.BA.FlowPins

/-!
# M/N M1, row a, file 2 (T2514a): locSC at BA from `UNMLOutBA d`, the bridge to `UNLocAvgBA` (`BA/MALocal`)

Ticket T2514 (dispatcher V4, DECISIONS §337; supervisor `2026-10-15-0643` Q3, Q4 (a), MNO-C3; design `docs/reports/T2449-design.md` §2, §3.3).
Paper: `MR:locSC` for `BA` (`1_2:653`), `(G_bound)`, `(G_bound_ave)` (`1_2:388-393`), the net argument (`1_2:1226-1228`).  Law
`Sizes.seqP (sz.withLam 0)`, matrix `sz.seqHBA`, ρ-bulk `BAbulk` (DECISIONS §51), carrier `baFMz`; the pin texts are those of `BA/MAPins`.

* §1 two spectral facts of `(self_m)`, new: the ρ-bulk lies in `|x| ≤ 2 + 2 d |g|` (`MALocal_bulk_abs_le`) and `Im m(i) ≥ (2 + 2 d |g|)^{-2}`
  (`MALocal_im_I_ge`).
* §2 A1 the transfer along a BA flow: `G(z) - M(z) = √t₀ (G_{t₀} - M)` entrywise, the block average, `𝒦^{(1)} = m_F`, and the constants
  `W^{-d} B_{t₀,k} ≤ 2 𝓑_{Im z, Wk}` (`Gt_BA`, `BAzztE_data`, `STWB_compare`).
* §3 A2 `baLocSCFixed_of_ML`: the fixed-`z` forms from conjuncts 1 and 5 of `UNMLOutBA d`; the sections lemma runs over the chain domain
  `BAdom κ_f ε` (`κ_f = min κ' c`, `κ' = (π κ)^5 / 2048`), nonempty at every `n` by the uniform margin at `z = i`, because the end domain
  `BAendDom κ ε` may be empty at some `n`.
* §4 A3 `baMANetLoc`: a finite net of representatives of mesh `N^{-7}` (one point per occupied cell: the end domain is not a rectangle,
  so the grid of `zNet_exists` does not apply), at most `(4R + 2) N^{14}` points with `R = 2 + 2 d 𝔡⁻¹`; the cover lemmas at `(τ/2, D + 15)`
  with the margin `κ' ≤ Im m` on the end domain; the carrier-free cores `znet_loc1_core`, `znet_loc2_core`, `znet_geom`, `znet_floor`, `znet_avg1` of
  `Main/ZNet` are reached by `open private`.
* §5 A4-A8: `baEnd_locSCL`, `baEnd_locSCL_three` (at the merged `unMLOutBA_three`), `unLocAvgBAAt_of_locSCL`, `UNLocAvgBA_of_BAEnd_locSCL`,
  `unLocAvgBAAt_of_ML`.  `d > 3` enters only through `UNMLOutBA d` (Jun decision B, DECISIONS §316).
* §6 A9 compiled nonempty instances at `d = 3` on `S0`, `sz0`, `zSeq`, `flow_sz0`.

No public definition; every helper is `private` or prefixed `MALocal_`.
-/

/-! ## 1. Two spectral facts of `(self_m)` -/


/-- The spectral form of the imaginary part of `(self_m)`: `Im m = L^{-d} Σ_i (Im m + Im z) / ‖v_i - (z + m)‖²`. -/
private theorem MALocal_im_eq (d L : ℕ) [NeZero L] (g : ℝ) {z m : ℂ} (hz : 0 ≤ z.im) (h : BASelf d L g z m) :
    m.im = (((L ^ d : ℕ) : ℝ))⁻¹ * ∑ i : Zd d L, (m.im + z.im) / ‖(BAspec d L g i : ℂ) - (z + m)‖ ^ 2 := by
  obtain ⟨hmpos, hmeq⟩ := h
  have hw : (z + m).im ≠ 0 := by
    rw [Complex.add_im]; linarith
  have htr := BAMB_trace_eq_sum d L g z m hw
  have hc : (((L ^ d : ℕ) : ℂ))⁻¹ = ((((L ^ d : ℕ) : ℝ))⁻¹ : ℝ) := by
    rw [Complex.ofReal_inv, Complex.ofReal_natCast]
  have h1 := congrArg Complex.im hmeq
  rw [hc, Complex.im_ofReal_mul, htr, Complex.im_sum] at h1
  refine h1.trans ?_
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.inv_im, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.add_im, neg_neg]
  ring


/-- `|v_i| ≤ 2 d |g|` for the scaled spectrum `BAspec = g · eig Ψ^{(B)}` (`FlowPins_eig_le`). -/
private theorem MALocal_spec_le (d L : ℕ) [NeZero L] (g : ℝ) (i : Zd d L) : |BAspec d L g i| ≤ 2 * d * |g| := by
  unfold BAspec
  rw [abs_mul]
  have := FlowPins_eig_le d L i
  nlinarith [abs_nonneg g, abs_nonneg ((PsiB_isHermitian d L).eigenvalues i)]

private theorem MALocal_card_pos (d L : ℕ) [NeZero L] : (0 : ℝ) < ((L ^ d : ℕ) : ℝ) := by
  have : 0 < L ^ d := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) d
  exact_mod_cast this

/-- **The ρ-bulk lies in `|x| ≤ 2 + 2 d |g|`** (new, no merged lemma): at a real energy `x` (`Im z = 0`) and `Im m > 0`, `(self_m)` gives
`1 = L^{-d} Σ_i ‖v_i - (x + m)‖⁻²`, while `‖v_i - (x + m)‖ ≥ |x| - |v_i| - |m| > 1` for `|x| > 2 + 2 d |g|`
(`|v_i| ≤ 2 d |g|`, `|m| ≤ 1`). -/
theorem MALocal_bulk_abs_le (d L : ℕ) [NeZero L] (g κ x : ℝ) (hκ : 0 < κ) (hb : BAbulk d L g κ x) :
    |x| ≤ 2 + 2 * d * |g| := by
  obtain ⟨m, hm, hmκ⟩ := (BAbulk_iff_exists d L g κ x hκ).mp hb
  have hmpos : 0 < m.im := hm.1
  have him := MALocal_im_eq d L g (z := (x : ℂ)) (by simp) hm
  have hm1 := BAm_norm_le_one d L g (x : ℂ) m (by simp) hm
  by_contra hnot
  push Not at hnot
  have hlt : ∀ i : Zd d L, (m.im + (x : ℂ).im) / ‖(BAspec d L g i : ℂ) - ((x : ℂ) + m)‖ ^ 2 < m.im := by
    intro i
    have hv := MALocal_spec_le d L g i
    have hre : |m.re| ≤ 1 := (Complex.abs_re_le_norm m).trans hm1
    have h1 : 1 < |BAspec d L g i - x - m.re| := by
      have := abs_sub_abs_le_abs_sub x (BAspec d L g i - m.re)
      have h2 : |BAspec d L g i - m.re| ≤ |BAspec d L g i| + |m.re| := abs_sub _ _
      have h3 : |x - (BAspec d L g i - m.re)| = |BAspec d L g i - x - m.re| := by
        rw [← abs_neg]; congr 1; ring
      linarith
    have h2 : |BAspec d L g i - x - m.re| ≤ ‖(BAspec d L g i : ℂ) - ((x : ℂ) + m)‖ := by
      refine le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re]
      congr 1; ring
    have h3 : 1 < ‖(BAspec d L g i : ℂ) - ((x : ℂ) + m)‖ ^ 2 := by nlinarith
    simp only [Complex.ofReal_im, add_zero]
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  have hN := MALocal_card_pos d L
  have hne : (Finset.univ : Finset (Zd d L)).Nonempty := Finset.univ_nonempty
  have hsum : ∑ i : Zd d L, (m.im + (x : ℂ).im) / ‖(BAspec d L g i : ℂ) - ((x : ℂ) + m)‖ ^ 2 <
      ∑ _i : Zd d L, m.im := Finset.sum_lt_sum_of_nonempty hne fun i _ => hlt i
  rw [Finset.sum_const, Finset.card_univ, BAcard_Zd, nsmul_eq_mul] at hsum
  have := mul_lt_mul_of_pos_left hsum (inv_pos.2 hN)
  rw [← him, ← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul] at this
  exact lt_irrefl _ this

/-- **`Im m(i) ≥ (2 + 2 d |g|)^{-2}`** at `z = i`, every size (new): `Im m = L^{-d} Σ_i (Im m + 1) ‖v_i - (i + m)‖⁻²` and
`‖v_i - (i + m)‖ ≤ |v_i| + 1 + |m| ≤ 2 + 2 d |g|`. -/
theorem MALocal_im_I_ge (d L : ℕ) [NeZero L] (g : ℝ) :
    1 / (2 + 2 * d * |g|) ^ 2 ≤ (BAm d L g Complex.I).im := by
  have hm := BAm_self d L g Complex.I (by simp)
  set m := BAm d L g Complex.I with hmdef
  have hmpos : 0 < m.im := hm.1
  have him := MALocal_im_eq d L g (z := Complex.I) (by simp) hm
  have hm1 := BAm_norm_le_one d L g Complex.I m (by simp) hm
  have hR : 0 < 2 + 2 * d * |g| := by positivity
  have hle : ∀ i : Zd d L, (m.im + Complex.I.im) / (2 + 2 * d * |g|) ^ 2 ≤
      (m.im + Complex.I.im) / ‖(BAspec d L g i : ℂ) - (Complex.I + m)‖ ^ 2 := by
    intro i
    have hv := MALocal_spec_le d L g i
    have h1 : ‖(BAspec d L g i : ℂ) - (Complex.I + m)‖ ≤ 2 + 2 * d * |g| := by
      calc ‖(BAspec d L g i : ℂ) - (Complex.I + m)‖ ≤ ‖(BAspec d L g i : ℂ)‖ + ‖Complex.I + m‖ := norm_sub_le _ _
        _ ≤ |BAspec d L g i| + (1 + 1) := by
            rw [Complex.norm_real, Real.norm_eq_abs]
            have := norm_add_le Complex.I m
            rw [Complex.norm_I] at this
            linarith
        _ ≤ 2 + 2 * d * |g| := by linarith
    have hpos : 0 < ‖(BAspec d L g i : ℂ) - (Complex.I + m)‖ := by
      refine norm_pos_iff.2 fun h0 => ?_
      have := congrArg Complex.im h0
      simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.I_im, Complex.zero_im] at this
      linarith
    refine div_le_div_of_nonneg_left (by simp; linarith) (by positivity) ?_
    exact pow_le_pow_left₀ hpos.le h1 2
  have hN := MALocal_card_pos d L
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Zd d L))) => hle i
  rw [Finset.sum_const, Finset.card_univ, BAcard_Zd, nsmul_eq_mul] at hsum
  have h2 := mul_le_mul_of_nonneg_left hsum (inv_pos.2 hN).le
  rw [← him, ← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul] at h2
  refine le_trans ?_ h2
  simp only [Complex.I_im]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith


/-! ## 2. A1: the transfer `G(z) = √t₀ G_{t₀}`, `M(z) = √t₀ M_{t₀}` along a BA flow -/

section Transfer

variable {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {zs : ℕ → ℂ}

/-- The flow data at one size index, in the form the transfer needs: `Im z > 0`, `Im m_F > 0` and `m_F = m(z)/√t₀`. -/
private theorem MALocal_mF (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 zs) (n : ℕ) :
    BAmF sz (BAflowLam0 sz zs) (BAflowEs sz zs) n =
      BAm d (sz.L n) (sz.lam n) (zs n) / (Real.sqrt (BAflowT0 sz zs n) : ℂ) :=
  BAm_real_eq_of_self d (sz.L n) _ _ _
    (BAzztE_data d (sz.L n) (sz.lam n) (EMn2BA_zim_pos sz h n) (BAm_self d (sz.L n) (sz.lam n) (zs n) (EMn2BA_zim_pos sz h n))).2.2.1

/-- **A1 (entries)**: `G(z)_{xy} - M(z)_{xy} = √t₀ (G_{t₀} - M)_{xy}` pathwise, `t₀ = BAflowT0`, `z = z_n` (`Gt_BA`, `BAzztE_data`,
`BAMres_fine_apply`). -/
theorem MALocal_G_sub_M (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 zs) (n : ℕ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) :
    BAGz sz n (zs n) ω x y - BAMz sz n (zs n) x y =
      (Real.sqrt (BAflowT0 sz zs n) : ℂ) * (baFMz sz zs).GM n (BAflowT0 sz zs n) ω x y := by
  have hz := EMn2BA_zim_pos sz h n
  have hm := EMn2BA_mim_pos hκ sz h n
  have hself := BAm_self d (sz.L n) (sz.lam n) (zs n) hz
  obtain ⟨ht0, -, hselfF, hzt, hMB⟩ := BAzztE_data d (sz.L n) (sz.lam n) hz hself
  have hmF := MALocal_mF hκ h n
  have hG := Gt_BA sz (BAflowLam0 sz zs) n (m0 := BAmF sz (BAflowLam0 sz zs) (BAflowEs sz zs) n)
    (E := BAflowEs sz zs n) (t0 := BAflowT0 sz zs n) hz ht0 rfl (by rw [hmF]; exact hzt) ω
  have hGxy : BAGz sz n (zs n) ω x y = (Real.sqrt (BAflowT0 sz zs n) : ℂ) *
      (baFMz sz zs).G n (BAflowT0 sz zs n) ω x y := by
    have := congrFun (congrFun hG x) y
    rw [Matrix.smul_apply, smul_eq_mul] at this
    exact this.symm
  have hw1 : ((zs n) + BAm d (sz.L n) (sz.lam n) (zs n)).im ≠ 0 := by
    rw [Complex.add_im]; linarith
  have hw2 : (((BAflowEs sz zs n : ℝ) : ℂ) + BAmF sz (BAflowLam0 sz zs) (BAflowEs sz zs) n).im ≠ 0 := by
    rw [hmF, Complex.add_im, Complex.ofReal_im, zero_add]
    exact hselfF.1.ne'
  have hMz := BAMres_fine_apply d (sz.L n) (sz.W n) (sz.lam n) (zs n) (BAm d (sz.L n) (sz.lam n) (zs n)) hw1 x y
  have hMf := BAMres_fine_apply d (sz.L n) (sz.W n) (BAflowLam0 sz zs n) ((BAflowEs sz zs n : ℝ) : ℂ)
    (BAmF sz (BAflowLam0 sz zs) (BAflowEs sz zs) n) hw2 x y
  have hMBe : ∀ a b : Zd d (sz.L n), BAMB d (sz.L n) (sz.lam n) (zs n) (BAm d (sz.L n) (sz.lam n) (zs n)) a b =
      (Real.sqrt (BAflowT0 sz zs n) : ℂ) *
        BAMB d (sz.L n) (BAflowLam0 sz zs n) ((BAflowEs sz zs n : ℝ) : ℂ)
          (BAmF sz (BAflowLam0 sz zs) (BAflowEs sz zs) n) a b := by
    intro a b
    rw [hmF]
    have := congrFun (congrFun hMB a) b
    rw [Matrix.smul_apply, smul_eq_mul] at this
    exact this.symm
  have hMxy : BAMz sz n (zs n) x y = (Real.sqrt (BAflowT0 sz zs n) : ℂ) * BAMfine sz (BAflowLam0 sz zs) (BAflowEs sz zs) n x y := by
    change Mres _ _ _ x y = _ * Mres _ _ _ x y
    rw [hMz, hMf]
    split_ifs
    · exact hMBe _ _
    · simp
  rw [hGxy, hMxy, ← mul_sub]
  rfl

/-- `𝓛^{(1)}` of a flow matrix is the block average of the diagonal of its resolvent (the proof of `zAve`, `ZTransfer.lean:368`). -/
private theorem MALocal_loop_one {L W : ℕ} [NeZero L] [NeZero W] (H : Matrix (Idx d L W) (Idx d L W) ℂ) (ζ : ℂ) (a : Zd d L) :
    loopFine d L W H ζ (fun _ : Fin 1 => true) (fun _ => a) =
      (((W : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, Gres H ζ true x x := by
  unfold loopFine loopM
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  rw [Gres_blockMat', trace_two]

/-- `𝒦^{(1)} = m_F` of the BA carrier (the third clause of `IsKLoopS` of `BAKsol`; `baKcac_isKLoopS` under `BAReal`). -/
private theorem MALocal_K_one (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 zs) (n : ℕ) (a : Zd d (sz.L n)) :
    (baFMz sz zs).K n (BAflowT0 sz zs n) (fun _ : Fin 1 => true) (fun _ => a) =
      BAmF sz (BAflowLam0 sz zs) (BAflowEs sz zs) n := by
  have hr := BAflow_real κ ε 𝔠 𝔡 sz zs h n
  have hz := EMn2BA_zim_pos sz h n
  have hm := EMn2BA_mim_pos hκ sz h n
  have ht0 := BAt0_pos hz hm
  have ht1 := BAt0_lt_one hz hm
  have hex : ∃ K : ℝ → LoopIdx (Zd d (sz.L n)) → ℂ, IsKLoopS d (sz.L n) (sz.W n) (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ)
      (PropSpin (BAmF sz (BAflowLam0 sz zs) (BAflowEs sz zs) n))
      (BAMLoop d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz zs n) ((BAflowEs sz zs n : ℝ) : ℂ)
        (BAmF sz (BAflowLam0 sz zs) (BAflowEs sz zs) n)))) (Set.Ico (0 : ℝ) 1) K := ⟨_, baKcac_isKLoopS hr⟩
  have hK := hex.choose_spec.2.2 (BAflowT0 sz zs n) ⟨ht0.le, ht1⟩ true a
  change BAKsol d (sz.L n) (sz.W n) _ _ _ (KLloopOf d (sz.L n) (fun _ : Fin 1 => true) (fun _ => a)) = _
  have e : KLloopOf d (sz.L n) (fun _ : Fin 1 => true) (fun _ => a) = ⟨[true], [a]⟩ := by simp [KLloopOf]
  unfold BAKsol
  simp only [hex, ↓reduceDIte]
  rw [e, hK]
  simp [PropSpin]

/-- **A1 (block average)**: `W^{-d} Σ_{x ∈ [a]} G(z)_{xx} - m(z) = √t₀ (𝓛^{(1)}_{t₀,+,a} - 𝒦^{(1)}_{t₀,+,a})`. -/
theorem MALocal_avg_sub_m (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 zs) (n : ℕ) (ω : sz.SeqΩ) (a : Zd d (sz.L n)) :
    (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, BAGz sz n (zs n) ω x x -
        BAm d (sz.L n) (sz.lam n) (zs n) =
      (Real.sqrt (BAflowT0 sz zs n) : ℂ) *
        ((baFMz sz zs).L n (BAflowT0 sz zs n) (fun _ : Fin 1 => true) (fun _ => a) ω -
          (baFMz sz zs).K n (BAflowT0 sz zs n) (fun _ : Fin 1 => true) (fun _ => a)) := by
  have hz := EMn2BA_zim_pos sz h n
  have hm := EMn2BA_mim_pos hκ sz h n
  have hself := BAm_self d (sz.L n) (sz.lam n) (zs n) hz
  obtain ⟨ht0, -, hselfF, hzt, -⟩ := BAzztE_data d (sz.L n) (sz.lam n) hz hself
  have hmF := MALocal_mF hκ h n
  have hG := Gt_BA sz (BAflowLam0 sz zs) n (m0 := BAmF sz (BAflowLam0 sz zs) (BAflowEs sz zs) n)
    (E := BAflowEs sz zs n) (t0 := BAflowT0 sz zs n) hz ht0 rfl (by rw [hmF]; exact hzt) ω
  have hs0 : (Real.sqrt (BAflowT0 sz zs n) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 ht0).ne'
  have hGxx : ∀ x : Idx d (sz.L n) (sz.W n), BAGz sz n (zs n) ω x x = (Real.sqrt (BAflowT0 sz zs n) : ℂ) *
      Gres (sz.seqHflowBA (BAflowLam0 sz zs) n (BAflowT0 sz zs n) ω)
        (ztOf (BAmF sz (BAflowLam0 sz zs) (BAflowEs sz zs) n) (BAflowEs sz zs n) (BAflowT0 sz zs n)) true x x := by
    intro x
    have := congrFun (congrFun hG x) x
    rw [Matrix.smul_apply, smul_eq_mul] at this
    exact this.symm
  have hL : (baFMz sz zs).L n (BAflowT0 sz zs n) (fun _ : Fin 1 => true) (fun _ => a) ω =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a,
        Gres (sz.seqHflowBA (BAflowLam0 sz zs) n (BAflowT0 sz zs n) ω)
          (ztOf (BAmF sz (BAflowLam0 sz zs) (BAflowEs sz zs) n) (BAflowEs sz zs n) (BAflowT0 sz zs n)) true x x :=
    MALocal_loop_one _ _ a
  have hsum : ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, BAGz sz n (zs n) ω x x =
      (Real.sqrt (BAflowT0 sz zs n) : ℂ) * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a,
        Gres (sz.seqHflowBA (BAflowLam0 sz zs) n (BAflowT0 sz zs n) ω)
          (ztOf (BAmF sz (BAflowLam0 sz zs) (BAflowEs sz zs) n) (BAflowEs sz zs n) (BAflowT0 sz zs n)) true x x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => hGxx x
  have hmF' : (Real.sqrt (BAflowT0 sz zs n) : ℂ) * BAmF sz (BAflowLam0 sz zs) (BAflowEs sz zs) n =
      BAm d (sz.L n) (sz.lam n) (zs n) := by
    rw [hmF]; field_simp
  rw [hL, MALocal_K_one hκ h n a, hsum]
  linear_combination hmF'

/-- **A1 (the `B`-constants, `(eq:BtBt)`)**: `W^{-d} B_{t₀,k} ≤ 2 𝓑_{Im z, Wk}` at `t₀ = BAflowT0`: `1 - t₀ = Im z / (Im m + Im z)` lies in
`[Im z / 2, Im z / Im m]` (`Im m ≤ 1`, `Im z ≤ 1`), and `STWB_compare` (`ZTransfer.lean:174`) with `C = (Im m)⁻¹`. -/
theorem MALocal_STWB_le (hd : 3 ≤ d) (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 zs) (n : ℕ) (k : ℕ) :
    sz.STWB n (BAflowT0 sz zs n) k ≤ 2 * calB sz n (zs n).im (((sz.W n : ℕ) : ℝ) * (k : ℝ)) := by
  have hz := EMn2BA_zim_pos sz h n
  have hm := EMn2BA_mim_pos hκ sz h n
  have hm1 := EMn2BA_mim_le_one sz h n
  have hu0 : 0 < 1 - BAflowT0 sz zs n := by linarith [EMn2BA_T0_lt_one hκ sz h n]
  have hhalf := EMn2BA_one_sub_T0 hκ sz h n
  have hform : 1 - BAflowT0 sz zs n = (zs n).im / ((BAm d (sz.L n) (sz.lam n) (zs n)).im + (zs n).im) := by
    unfold BAflowT0 BAt0
    field_simp
    ring
  have huC : 1 - BAflowT0 sz zs n ≤ ((BAm d (sz.L n) (sz.lam n) (zs n)).im)⁻¹ * (zs n).im := by
    rw [hform, div_le_iff₀ (by linarith)]
    have : (1 : ℝ) ≤ ((BAm d (sz.L n) (sz.lam n) (zs n)).im)⁻¹ * ((BAm d (sz.L n) (sz.lam n) (zs n)).im +
        (zs n).im) := by
      rw [← div_eq_inv_mul, le_div_iff₀ hm]; linarith
    calc (zs n).im = (zs n).im * 1 := (mul_one _).symm
      _ ≤ (zs n).im * (((BAm d (sz.L n) (sz.lam n) (zs n)).im)⁻¹ * ((BAm d (sz.L n) (sz.lam n) (zs n)).im +
          (zs n).im)) := mul_le_mul_of_nonneg_left this hz.le
      _ = _ := by ring
  have hC1 : (1 : ℝ) ≤ ((BAm d (sz.L n) (sz.lam n) (zs n)).im)⁻¹ := by
    rw [one_le_inv₀ hm]; exact hm1
  obtain ⟨h1, -⟩ := STWB_compare sz n hz hu0 (by linarith) hC1 huC k
  rw [calB_blk_eq_STWB sz n (by omega) hz k]
  have e : 1 - (1 - BAflowT0 sz zs n) = BAflowT0 sz zs n := by ring
  rw [e] at h1
  exact h1

/-- The same at `k = 0`: `Bctl n t₀ ≤ 2 𝓑_{Im z, 0}`. -/
theorem MALocal_Bctl_le (hd : 3 ≤ d) (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 zs) (n : ℕ) :
    sz.Bctl n (BAflowT0 sz zs n) ≤ 2 * calB sz n (zs n).im 0 := by
  have h1 := MALocal_STWB_le hd hκ h n 0
  simp only [Nat.cast_zero, mul_zero] at h1
  exact h1

end Transfer

/-! ## 3. A2: the fixed-`z` statements from `UNMLOutBA d` -/

section Fixed

variable {d : ℕ}

/-- **A uniform margin at `z = i`** (new): along an admissible sequence `Im m_n(i) ≥ c > 0` for every `n`, with `c` independent of `n`
(`Im m(i) ≥ (2 + 2 d |λ_n|)^{-2}` and `|λ_n| ≤ 𝔡⁻¹ + Σ_{k < n₀} |λ_k|` for all `n`, `λ_n ≤ 𝔡⁻¹` eventually).  It makes the chain domain
`BAdom κ_f ε` nonempty at every `n`, which the sections lemma needs; the end domain `BAendDom κ ε` may be empty at some `n`. -/
private theorem MALocal_kappa_floor {sz : Sizes d} {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) :
    ∃ c : ℝ, 0 < c ∧ ∀ n, c ≤ (BAm d (sz.L n) (sz.lam n) Complex.I).im := by
  obtain ⟨-, h𝔡, -, -, hWO⟩ := hA
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hWO
  set G : ℝ := 𝔡⁻¹ + ∑ k ∈ Finset.range n₀, |sz.lam k| with hGdef
  have hG0 : 0 ≤ G := by
    have : 0 ≤ ∑ k ∈ Finset.range n₀, |sz.lam k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have : 0 ≤ 𝔡⁻¹ := inv_nonneg.2 h𝔡.le
    linarith
  have hG : ∀ n, |sz.lam n| ≤ G := by
    intro n
    by_cases hn : n < n₀
    · have := Finset.single_le_sum (f := fun k => |sz.lam k|) (fun _ _ => abs_nonneg _) (Finset.mem_range.2 hn)
      have h0 : 0 ≤ 𝔡⁻¹ := inv_nonneg.2 h𝔡.le
      linarith
    · obtain ⟨h1, h2⟩ := hn₀ n (not_lt.1 hn)
      have hW : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hl : 0 ≤ sz.lam n := le_trans hW h1
      have : 0 ≤ ∑ k ∈ Finset.range n₀, |sz.lam k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      rw [abs_of_nonneg hl]
      linarith
  refine ⟨1 / (2 + 2 * d * G) ^ 2, by positivity, fun n => le_trans ?_ (MALocal_im_I_ge d (sz.L n) (sz.lam n))⟩
  refine one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) ?_ 2)
  have := hG n
  have h2 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith [mul_le_mul_of_nonneg_left this h2]

/-- A point of the end domain has `Im z > 0` (`N ≥ 1`). -/
private theorem MALocal_endDom_im_pos {sz : Sizes d} {κ ε : ℝ} {n : ℕ} {z : ℂ} (hz : BAendDom sz κ ε n z) : 0 < z.im := by
  have hN : (0 : ℝ) < Nsz sz n := by exact_mod_cast Nat.pos_of_ne_zero (by have := sz.one_le_size n; omega)
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos hN _) hz.2.1

/-- The end domain is inside the chain domain at the margin `κ' = (π κ)^5 / 2048` (`ba_dom_of_bulk`, `BA/RandomLayerBGBA.lean:69`). -/
private theorem MALocal_endDom_dom {sz : Sizes d} {κ ε : ℝ} (hκ : 0 < κ) {n : ℕ} {z : ℂ} (hz : BAendDom sz κ ε n z) :
    (Real.pi * κ) ^ 5 / 2048 ≤ (BAm d (sz.L n) (sz.lam n) z).im :=
  ba_dom_of_bulk d (sz.L n) (sz.lam n) κ hκ hz.1 (MALocal_endDom_im_pos hz) hz.2.2

private theorem MALocal_rpow_sq {W : ℝ} (hW : 0 < W) (τ : ℝ) : (W ^ (τ / 2)) ^ 2 = W ^ τ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le]
  congr 1; push_cast; ring

/-- **A2, `baLocSCFixed_of_ML`** (twin of `locSCFixed_of_ML`, `Main/FixedZ.lean:100`): the fixed-`z` forms of `(G_bound)`, `(G_bound_ave)`
from conjuncts 1 and 5 of `UNMLOutBA d` at `t = BAflowT0`: the sections lemma over the chain domain `BAdom κ_f ε` (`κ_f = min κ' c`),
the transfer `MALocal_G_sub_M`, `MALocal_avg_sub_m`, the constants `MALocal_STWB_le`, the form bridge `explicit_of_stochDomAt` at `τ/2` and
`2 ≤ W^{τ/2}` eventually. -/
theorem baLocSCFixed_of_ML (d : ℕ) (hML : UNMLOutBA d) : BAlocSCFixed d := by
  intro hd 𝔠 𝔡 sz hA κ ε τ D hκ hε hτ hD
  have hA' := hA
  obtain ⟨h𝔠, h𝔡, hsz, hbw, hWO⟩ := hA'
  by_cases hε1 : ε ≤ 1
  swap
  · filter_upwards [hsz.eventually_gt_atTop 1] with n hn z hz
    exfalso
    have h1 := Real.one_lt_rpow hn (by linarith [not_le.1 hε1] : 0 < -1 + ε)
    have h2 := hz.2.1
    have h3 := hz.2.2
    exact absurd (lt_of_lt_of_le h1 (h2.trans h3)) (lt_irrefl _)
  obtain ⟨c₁, hc₁, hc₁I⟩ := MALocal_kappa_floor hA
  have hκ' : 0 < (Real.pi * κ) ^ 5 / 2048 := by positivity
  set κf : ℝ := min ((Real.pi * κ) ^ 5 / 2048) c₁ with hκfdef
  have hκf : 0 < κf := lt_min hκ' hc₁
  have hne : ∀ n, Nonempty {z : ℂ // BAdom d (sz.L n) (sz.size n) (sz.lam n) κf ε z} := fun n =>
    ⟨⟨Complex.I, (min_le_right _ _).trans (hc₁I n), by
      simp only [Complex.I_im]
      have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
      exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith), by simp⟩⟩
  have hW2 : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (half_pos hτ)).comp (RBM.Green.tendsto_W sz h𝔠 hsz hbw)).eventually_ge_atTop 2
  refine (eventually_forall_of_sections hne (Q := fun n z =>
      Sizes.seqP (sz.withLam 0) {ω | BAlocBad1z sz τ n z.1 ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
      Sizes.seqP (sz.withLam 0) {ω | BAlocBad2z sz τ n z.1 ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))) ?_).mono
    fun n hn z hz => hn ⟨z, ⟨(min_le_left _ _).trans (MALocal_endDom_dom hκ hz), hz.2.1, hz.2.2⟩⟩
  intro s
  set zs : ℕ → ℂ := fun n => (s n).1 with hzs
  have hflow : BAFlow sz κf ε 𝔠 𝔡 zs := ⟨hA, fun n => (s n).2⟩
  have hT0 := fun n => BAflow_T0_bounds hκf hflow n
  obtain ⟨hLK, -, -, -, hLoc⟩ := hML hd κf ε 𝔡 𝔠 hκf hε h𝔡 sz zs hflow (fun n => BAflowT0 sz zs n)
    (fun n => (hT0 n).2.2.1.le) (fun n => le_rfl)
  have hτ2 : 0 < τ / 2 := half_pos hτ
  have hζ1 : ∀ (n : ℕ) (u : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (ω : sz.SeqΩ),
      0 ≤ sz.STWB n (BAflowT0 sz zs n) (zdistInf d (sz.L n) (STblk sz n u.1 - STblk sz n u.2)) :=
    fun n u ω => STWB_nonneg sz n _ _
  have hζ2 : ∀ (n : ℕ) (u : (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n))) (ω : sz.SeqΩ),
      0 ≤ (sz.Bctl n (BAflowT0 sz zs n)) ^ 1 := fun n u ω => pow_nonneg (Bctl_nonneg sz n _) 1
  have hE1 := explicit_of_stochDomAt sz (Sizes.seqP (sz.withLam 0)) h𝔠 hζ1 hbw hLoc hτ2 hD
  have hE2 := explicit_of_stochDomAt sz (Sizes.seqP (sz.withLam 0)) h𝔠 hζ2 hbw (hLK 1 le_rfl) hτ2 hD
  filter_upwards [hE1, hE2, hW2] with n hn1 hn2 hn3
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWτ := MALocal_rpow_sq hWpos τ
  have hWh : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg hWpos.le _
  have hz := (hT0 n).1
  have ht0 := (hT0 n).2.2.1
  have ht1 := (hT0 n).2.2.2
  have hsq : ‖(Real.sqrt (BAflowT0 sz zs n) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_one.2 ht1.le
  refine ⟨le_trans (measure_mono ?_) hn1, le_trans (measure_mono ?_) hn2⟩
  · rintro ω ⟨x, y, hxy⟩
    refine ⟨(x, y), ?_⟩
    simp only
    set k := zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) with hk
    have hb1 := MALocal_STWB_le hd hκf hflow n k
    have hcB : 0 ≤ calB sz n (zs n).im (((sz.W n : ℕ) : ℝ) * (k : ℝ)) :=
      calB_nonneg sz n hz (by positivity)
    have hxy' : ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n (zs n).im (((sz.W n : ℕ) : ℝ) * (k : ℝ)) <
        ‖BAGz sz n (zs n) ω x y - BAMz sz n (zs n) x y‖ ^ 2 := hxy
    rw [MALocal_G_sub_M hκf hflow n ω x y, norm_mul, mul_pow] at hxy'
    have hle : ‖(Real.sqrt (BAflowT0 sz zs n) : ℂ)‖ ^ 2 * ‖(baFMz sz zs).GM n (BAflowT0 sz zs n) ω x y‖ ^ 2 ≤
        ‖(baFMz sz zs).GM n (BAflowT0 sz zs n) ω x y‖ ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) hsq)
    calc ((sz.W n : ℕ) : ℝ) ^ (τ / 2) * sz.STWB n (BAflowT0 sz zs n) k
        ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) * (2 * calB sz n (zs n).im (((sz.W n : ℕ) : ℝ) * (k : ℝ))) :=
          mul_le_mul_of_nonneg_left hb1 hWh
      _ = (((sz.W n : ℕ) : ℝ) ^ (τ / 2) * 2) * calB sz n (zs n).im (((sz.W n : ℕ) : ℝ) * (k : ℝ)) := by ring
      _ ≤ (((sz.W n : ℕ) : ℝ) ^ (τ / 2) * ((sz.W n : ℕ) : ℝ) ^ (τ / 2)) *
            calB sz n (zs n).im (((sz.W n : ℕ) : ℝ) * (k : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn3 hWh) hcB
      _ = ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n (zs n).im (((sz.W n : ℕ) : ℝ) * (k : ℝ)) := by rw [← sq, hWτ]
      _ < _ := hxy'
      _ ≤ _ := hle
  · rintro ω ⟨a, ha⟩
    refine ⟨(fun _ => true, fun _ => a), ?_⟩
    simp only
    have hb1 := MALocal_Bctl_le hd hκf hflow n
    have hcB : 0 ≤ calB sz n (zs n).im 0 := calB_nonneg sz n hz le_rfl
    have ha' : ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n (zs n).im 0 <
        ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, BAGz sz n (zs n) ω x x -
          BAm d (sz.L n) (sz.lam n) (zs n)‖ := ha
    rw [MALocal_avg_sub_m hκf hflow n ω a, norm_mul] at ha'
    have hle : ‖(Real.sqrt (BAflowT0 sz zs n) : ℂ)‖ *
        ‖(baFMz sz zs).L n (BAflowT0 sz zs n) (fun _ : Fin 1 => true) (fun _ => a) ω -
          (baFMz sz zs).K n (BAflowT0 sz zs n) (fun _ : Fin 1 => true) (fun _ => a)‖ ≤
        ‖(baFMz sz zs).L n (BAflowT0 sz zs n) (fun _ : Fin 1 => true) (fun _ => a) ω -
          (baFMz sz zs).K n (BAflowT0 sz zs n) (fun _ : Fin 1 => true) (fun _ => a)‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hsq
    calc ((sz.W n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n (BAflowT0 sz zs n)) ^ 1
        = ((sz.W n : ℕ) : ℝ) ^ (τ / 2) * sz.Bctl n (BAflowT0 sz zs n) := by rw [pow_one]
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) * (2 * calB sz n (zs n).im 0) := mul_le_mul_of_nonneg_left hb1 hWh
      _ = (((sz.W n : ℕ) : ℝ) ^ (τ / 2) * 2) * calB sz n (zs n).im 0 := by ring
      _ ≤ (((sz.W n : ℕ) : ℝ) ^ (τ / 2) * ((sz.W n : ℕ) : ℝ) ^ (τ / 2)) * calB sz n (zs n).im 0 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn3 hWh) hcB
      _ = ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n (zs n).im 0 := by rw [← sq, hWτ]
      _ < _ := ha'
      _ ≤ _ := hle

end Fixed

/-! ## 4. A3: the `N^{-7}`-net over the end domain and the union bound -/

section Net

variable {d : ℕ}

open private znet_geom znet_floor znet_avg1 znet_loc1_core znet_loc2_core znet_rpow_neg7 from RBM3D.Main.ZNet

/-- `⌊x/h⌋₊ = ⌊y/h⌋₊` forces `|x - y| ≤ h` (`x, y ≥ 0`). -/
private theorem MALocal_floor_close {x y h : ℝ} (hh : 0 < h) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : ⌊x / h⌋₊ = ⌊y / h⌋₊) : |x - y| ≤ h := by
  have h1 := Nat.floor_le (div_nonneg hx hh.le)
  have h2 := Nat.lt_floor_add_one (x / h)
  have h3 := Nat.floor_le (div_nonneg hy hh.le)
  have h4 := Nat.lt_floor_add_one (y / h)
  rw [hxy] at h1 h2
  have h5 : |x / h - y / h| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  rw [← sub_div, abs_div, abs_of_pos hh, div_le_one hh] at h5
  exact h5

/-- **A finite net of representatives** (carrier-free): a set `P` of points with `|Re z| ≤ R`, `0 ≤ Im z ≤ 1` has, for every mesh `h > 0`,
a finite subset `S ⊆ P` with at most `(2R/h + 1)(1/h + 1)` points such that every `z ∈ P` has a point of `S` within `h` in both
coordinates (one representative per occupied cell `⌊(Re z + R)/h⌋₊ × ⌊Im z/h⌋₊`). -/
private theorem MALocal_net_exists {P : ℂ → Prop} {R h : ℝ} (hR : 0 ≤ R) (hh : 0 < h)
    (hP : ∀ z, P z → |z.re| ≤ R ∧ 0 ≤ z.im ∧ z.im ≤ 1) :
    ∃ S : Finset ℂ, (S.card : ℝ) ≤ (2 * R / h + 1) * (1 / h + 1) ∧ (∀ w ∈ S, P w) ∧
      ∀ z, P z → ∃ w ∈ S, |z.re - w.re| ≤ h ∧ |z.im - w.im| ≤ h := by
  classical
  set cell : ℂ → ℕ × ℕ := fun z => (⌊(z.re + R) / h⌋₊, ⌊z.im / h⌋₊) with hcell
  set K1 : ℕ := ⌊2 * R / h⌋₊ with hK1
  set K2 : ℕ := ⌊1 / h⌋₊ with hK2
  set T : Finset (ℕ × ℕ) := Finset.range (K1 + 1) ×ˢ Finset.range (K2 + 1) with hT
  set G : Finset (ℕ × ℕ) := T.filter (fun c => ∃ z, P z ∧ cell z = c) with hG
  set rep : ℕ × ℕ → ℂ := fun c => if hc : ∃ z, P z ∧ cell z = c then hc.choose else 0 with hrep
  have hrepP : ∀ c ∈ G, P (rep c) ∧ cell (rep c) = c := by
    intro c hc
    have hex := (Finset.mem_filter.1 hc).2
    simp only [hrep, hex, ↓reduceDIte]
    exact hex.choose_spec
  refine ⟨G.image rep, ?_, ?_, ?_⟩
  · calc ((G.image rep).card : ℝ) ≤ (G.card : ℝ) := by exact_mod_cast Finset.card_image_le
      _ ≤ (T.card : ℝ) := by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      _ = ((K1 : ℝ) + 1) * ((K2 : ℝ) + 1) := by simp [hT, Finset.card_product]
      _ ≤ (2 * R / h + 1) * (1 / h + 1) := by
          have h1 : (K1 : ℝ) ≤ 2 * R / h := Nat.floor_le (by positivity)
          have h2 : (K2 : ℝ) ≤ 1 / h := Nat.floor_le (by positivity)
          have h3 : (0 : ℝ) ≤ (K1 : ℝ) + 1 := by positivity
          exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  · intro w hw
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hw
    exact (hrepP c hc).1
  · intro z hz
    obtain ⟨hre, hz0, hz1⟩ := hP z hz
    have hre' := abs_le.1 hre
    have hcT : cell z ∈ T := by
      refine Finset.mem_product.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le ?_), Finset.mem_range.2 (Nat.lt_succ_of_le ?_)⟩
      · exact Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hh.le)
      · exact Nat.floor_le_floor (div_le_div_of_nonneg_right hz1 hh.le)
    have hcG : cell z ∈ G := Finset.mem_filter.2 ⟨hcT, z, hz, rfl⟩
    obtain ⟨hwP, hwc⟩ := hrepP _ hcG
    refine ⟨rep (cell z), Finset.mem_image_of_mem _ hcG, ?_, ?_⟩
    · have hw0 : 0 ≤ (rep (cell z)).re + R := by
        have := abs_le.1 ((hP _ hwP).1); linarith
      have := MALocal_floor_close hh (by linarith : 0 ≤ z.re + R) hw0 (congrArg Prod.fst hwc.symm)
      rw [show z.re - (rep (cell z)).re = (z.re + R) - ((rep (cell z)).re + R) by ring]
      exact this
    · exact MALocal_floor_close hh hz0 (hP _ hwP).2.1 (congrArg Prod.snd hwc.symm)

open scoped Matrix.Norms.L2Operator in
/-- **Resolvent entries are `η⁻²`-Lipschitz in the spectral parameter** on `Im ≥ η`, for any Hermitian `H` (`cont_green_diff` at `H = H'`;
the entry is bounded by the operator norm).  The BA twin of `Gn_entry_lip` (`ZNet.lean:334`); it serves `G(z)` (`H = seqHBA`) and `M(z)`
(`H = λΨ`, spectral parameter `z + m(z)`). -/
private theorem MALocal_Gres_lip {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {q q' : ℂ}
    {η : ℝ} (hη : 0 < η) (hq : η ≤ q.im) (hq' : η ≤ q'.im) (x y : ι) :
    ‖Gres H q true x y - Gres H q' true x y‖ ≤ η⁻¹ * η⁻¹ * ‖q - q'‖ := by
  have h1 := RBM.Ind.ContinuityNet.cont_green_diff hH hH hη (le_trans hq (le_abs_self _)) (le_trans hq' (le_abs_self _))
  rw [sub_self, norm_zero, zero_add] at h1
  have h2 := norm_matrix_entry_le_opNorm (green H q - green H q') x y
  rw [Matrix.sub_apply] at h2
  rw [RBM.Ind.ContinuityNet.cont_Gres_true_eq_green, RBM.Ind.ContinuityNet.cont_Gres_true_eq_green]
  exact h2.trans h1

/-- The geometry of an end-domain point `z` and a net point `w` within `N^{-7}` of it (`znet_geom`, `ZNet.lean:564`, at the band
domain predicate of `ZNet` with the margin `2 - max |Re z| |Re w|`, which holds for both points). -/
private theorem MALocal_geom (sz : Sizes d) (n : ℕ) {κ ε : ℝ} (hε : 0 < ε) (h32 : 32 ≤ Nsz sz n) {z w : ℂ}
    (hz : BAendDom sz κ ε n z) (hw : BAendDom sz κ ε n w) (hre : |z.re - w.re| ≤ Nsz sz n ^ (-7 : ℝ))
    (him : |z.im - w.im| ≤ Nsz sz n ^ (-7 : ℝ)) :
    (Nsz sz n)⁻¹ ≤ z.im ∧ (Nsz sz n)⁻¹ ≤ w.im ∧ |w.im - z.im| ≤ z.im / 2 ∧ ‖z - w‖ ≤ 2 * ((Nsz sz n)⁻¹) ^ 7 :=
  znet_geom sz n (κ := 2 - max |z.re| |w.re|) hε h32
    ⟨by linarith [le_max_left |z.re| |w.re|], hz.2.1, hz.2.2⟩
    ⟨by linarith [le_max_right |z.re| |w.re|], hw.2.1, hw.2.2⟩ hre him

/-- The three Lipschitz moduli of the cover at the margin `κ'` (`κ' ≤ Im m` at both points, `‖z - w‖ ≤ 2 u⁷`, `Cκ ≤ N`,
`Cκ = κ'⁻² (1 + κ'⁻²)`): the resolvent entries `G(z)_{xy}` and `M(z)_{xy}` move by `≤ 2 u⁵` and `m(z)` by `≤ 2 u⁵`, `u = N⁻¹`. -/
private theorem MALocal_moduli (sz : Sizes d) (n : ℕ) {κ' : ℝ} (hκ' : 0 < κ') {z w : ℂ} (hz0 : 0 < z.im) (hw0 : 0 < w.im)
    (hmz : κ' ≤ (BAm d (sz.L n) (sz.lam n) z).im) (hmw : κ' ≤ (BAm d (sz.L n) (sz.lam n) w).im)
    {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (hCN : κ'⁻¹ * κ'⁻¹ * (1 + κ'⁻¹ * κ'⁻¹) ≤ u⁻¹) (hζ : ‖z - w‖ ≤ 2 * u ^ 7)
    (hzu : u ≤ z.im) (hwu : u ≤ w.im) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖BAGz sz n z ω x y - BAGz sz n w ω x y‖ ≤ 2 * u ^ 5 ∧ ‖BAMz sz n z x y - BAMz sz n w x y‖ ≤ 2 * u ^ 5 ∧
      ‖BAm d (sz.L n) (sz.lam n) z - BAm d (sz.L n) (sz.lam n) w‖ ≤ 2 * u ^ 5 := by
  have hu2 : 0 < u ^ 2 := by positivity
  have hCu : κ'⁻¹ * κ'⁻¹ * (1 + κ'⁻¹ * κ'⁻¹) * u ^ 2 ≤ 1 := by
    calc κ'⁻¹ * κ'⁻¹ * (1 + κ'⁻¹ * κ'⁻¹) * u ^ 2 ≤ u⁻¹ * u ^ 2 := mul_le_mul_of_nonneg_right hCN hu2.le
      _ = u := by field_simp
      _ ≤ 1 := hu1
  have hk2 : κ'⁻¹ * κ'⁻¹ ≤ κ'⁻¹ * κ'⁻¹ * (1 + κ'⁻¹ * κ'⁻¹) :=
    le_mul_of_one_le_right (by positivity) (by nlinarith [mul_self_nonneg κ'⁻¹])
  have hdm : ‖BAm d (sz.L n) (sz.lam n) z - BAm d (sz.L n) (sz.lam n) w‖ ≤ ‖z - w‖ / κ' ^ 2 :=
    BAm_sub_le_of_im d (sz.L n) (sz.lam n) κ' z w hκ' hz0 hw0 hmz hmw
  refine ⟨?_, ?_, ?_⟩
  · refine (MALocal_Gres_lip (Sizes.seqHBA_isHermitian sz n ω) hu hzu hwu x y).trans ?_
    calc u⁻¹ * u⁻¹ * ‖z - w‖ ≤ u⁻¹ * u⁻¹ * (2 * u ^ 7) := mul_le_mul_of_nonneg_left hζ (by positivity)
      _ = 2 * u ^ 5 := by field_simp
  · have hqz : κ' ≤ (z + BAm d (sz.L n) (sz.lam n) z).im := by
      rw [Complex.add_im]; linarith
    have hqw : κ' ≤ (w + BAm d (sz.L n) (sz.lam n) w).im := by
      rw [Complex.add_im]; linarith
    have hH : ((sz.lam n : ℂ) • PsiI d (sz.L n) (sz.W n)).IsHermitian := (UNModelC.ba sz).mean_herm n
    have h1 := MALocal_Gres_lip hH hκ' hqz hqw x y
    have h2 : ‖(z + BAm d (sz.L n) (sz.lam n) z) - (w + BAm d (sz.L n) (sz.lam n) w)‖ ≤
        ‖z - w‖ + ‖z - w‖ / κ' ^ 2 := by
      calc _ = ‖(z - w) + (BAm d (sz.L n) (sz.lam n) z - BAm d (sz.L n) (sz.lam n) w)‖ := by congr 1; ring
        _ ≤ ‖z - w‖ + ‖BAm d (sz.L n) (sz.lam n) z - BAm d (sz.L n) (sz.lam n) w‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    change ‖Gres _ _ true x y - Gres _ _ true x y‖ ≤ _
    refine h1.trans ?_
    calc κ'⁻¹ * κ'⁻¹ * ‖(z + BAm d (sz.L n) (sz.lam n) z) - (w + BAm d (sz.L n) (sz.lam n) w)‖
        ≤ κ'⁻¹ * κ'⁻¹ * (‖z - w‖ + ‖z - w‖ / κ' ^ 2) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = κ'⁻¹ * κ'⁻¹ * (1 + κ'⁻¹ * κ'⁻¹) * ‖z - w‖ := by field_simp
      _ ≤ κ'⁻¹ * κ'⁻¹ * (1 + κ'⁻¹ * κ'⁻¹) * (2 * u ^ 7) :=
          mul_le_mul_of_nonneg_left hζ (by positivity)
      _ = 2 * u ^ 5 * (κ'⁻¹ * κ'⁻¹ * (1 + κ'⁻¹ * κ'⁻¹) * u ^ 2) := by ring
      _ ≤ 2 * u ^ 5 * 1 := mul_le_mul_of_nonneg_left hCu (by positivity)
      _ = 2 * u ^ 5 := mul_one _
  · refine hdm.trans ?_
    calc ‖z - w‖ / κ' ^ 2 ≤ 2 * u ^ 7 / κ' ^ 2 := div_le_div_of_nonneg_right hζ (by positivity)
      _ = 2 * u ^ 5 * (κ'⁻¹ * κ'⁻¹ * u ^ 2) := by field_simp
      _ ≤ 2 * u ^ 5 * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact le_trans (mul_le_mul_of_nonneg_right hk2 hu2.le) hCu
      _ = 2 * u ^ 5 := mul_one _

/-- **Cover lemma for `(G_bound)` at BA** (twin of `locBad1_net`, `ZNet.lean:781`): every `ω` in the bad event at `τ` over the end domain lies in
the per-point bad event at `τ/2` of a net point (`32 ≤ N`, `5 ≤ W^{τ/2}`, `κ'⁻² (1 + κ'⁻²) ≤ N`, `κ' ≤ Im m` on the end domain);
deterministic, for every `ω`. -/
private theorem MALocal_locBad1_net (sz : Sizes d) (n : ℕ) (hd : 3 ≤ d) {κ ε τ κ' : ℝ} (hκ' : 0 < κ') (hε : 0 < ε)
    (h32 : 32 ≤ Nsz sz n) (hCN : κ'⁻¹ * κ'⁻¹ * (1 + κ'⁻¹ * κ'⁻¹) ≤ Nsz sz n)
    (hdom : ∀ z : ℂ, BAendDom sz κ ε n z → κ' ≤ (BAm d (sz.L n) (sz.lam n) z).im)
    (h5 : 5 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2)) (S : Finset ℂ) (hS : ∀ w ∈ S, BAendDom sz κ ε n w)
    (hcov : ∀ z : ℂ, BAendDom sz κ ε n z → ∃ w ∈ S,
      |z.re - w.re| ≤ Nsz sz n ^ (-7 : ℝ) ∧ |z.im - w.im| ≤ Nsz sz n ^ (-7 : ℝ))
    (ω : sz.SeqΩ) (hω : ∃ z : ℂ, BAendDom sz κ ε n z ∧ BAlocBad1z sz τ n z ω) :
    ∃ w ∈ S, BAlocBad1z sz (τ / 2) n w ω := by
  obtain ⟨z, hz, x, y, hxy⟩ := hω
  obtain ⟨w, hwS, hre, him⟩ := hcov z hz
  refine ⟨w, hwS, ?_⟩
  by_contra hnb
  unfold BAlocBad1z at hnb
  push Not at hnb
  have hnb' := hnb x y
  have hw := hS w hwS
  obtain ⟨hzu, hwu, hshift, hζ⟩ := MALocal_geom sz n hε h32 hz hw hre him
  have hu0 : 0 < (Nsz sz n)⁻¹ := inv_pos.2 (by linarith)
  have hu32 : (Nsz sz n)⁻¹ ≤ 1 / 32 := by
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 32) h32
    simpa using this
  have hz0 : 0 < z.im := lt_of_lt_of_le hu0 hzu
  have hw0 : 0 < w.im := lt_of_lt_of_le hu0 hwu
  have hK : 0 ≤ distB sz n (STblk sz n x) (STblk sz n y) := by unfold distB; positivity
  have hfloor := znet_floor sz n (by omega) hz0 hz.2.2 hK
  have hshiftB := calB_shift_le sz n hz0 hK hshift
  obtain ⟨hGd, hMd, -⟩ := MALocal_moduli sz n hκ' hz0 hw0 (hdom z hz) (hdom w hw) hu0 (by linarith) (by rwa [inv_inv])
    hζ hzu hwu ω x y
  have hX : ‖BAGz sz n z ω x y - BAMz sz n z x y‖ ≤
      ‖BAGz sz n w ω x y - BAMz sz n w x y‖ + 4 * ((Nsz sz n)⁻¹) ^ 5 := by
    have hsplit : BAGz sz n z ω x y - BAMz sz n z x y =
        (BAGz sz n w ω x y - BAMz sz n w x y) +
          ((BAGz sz n z ω x y - BAGz sz n w ω x y) - (BAMz sz n z x y - BAMz sz n w x y)) := by ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have := norm_sub_le (BAGz sz n z ω x y - BAGz sz n w ω x y) (BAMz sz n z x y - BAMz sz n w x y)
    linarith
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hsq := MALocal_rpow_sq hW τ
  have := znet_loc1_core (s := ((sz.W n : ℕ) : ℝ) ^ (τ / 2))
    (Bz := calB sz n z.im (distB sz n (STblk sz n x) (STblk sz n y)))
    (Bw := calB sz n w.im (distB sz n (STblk sz n x) (STblk sz n y))) (u := (Nsz sz n)⁻¹)
    (X := ‖BAGz sz n z ω x y - BAMz sz n z x y‖) (Y := ‖BAGz sz n w ω x y - BAMz sz n w x y‖)
    (e := 4 * ((Nsz sz n)⁻¹) ^ 5) h5 hshiftB hfloor hu0 hu32 (by positivity) le_rfl (norm_nonneg _)
    (norm_nonneg _) hnb' hX
  rw [hsq] at this
  exact absurd hxy (not_lt.2 this)

/-- **Cover lemma for `(G_bound_ave)` at BA** (twin of `locBad2_net`, `ZNet.lean:831`). -/
private theorem MALocal_locBad2_net (sz : Sizes d) (n : ℕ) (hd : 3 ≤ d) {κ ε τ κ' : ℝ} (hκ' : 0 < κ') (hε : 0 < ε)
    (h32 : 32 ≤ Nsz sz n) (hCN : κ'⁻¹ * κ'⁻¹ * (1 + κ'⁻¹ * κ'⁻¹) ≤ Nsz sz n)
    (hdom : ∀ z : ℂ, BAendDom sz κ ε n z → κ' ≤ (BAm d (sz.L n) (sz.lam n) z).im)
    (h5 : 5 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2)) (S : Finset ℂ) (hS : ∀ w ∈ S, BAendDom sz κ ε n w)
    (hcov : ∀ z : ℂ, BAendDom sz κ ε n z → ∃ w ∈ S,
      |z.re - w.re| ≤ Nsz sz n ^ (-7 : ℝ) ∧ |z.im - w.im| ≤ Nsz sz n ^ (-7 : ℝ))
    (ω : sz.SeqΩ) (hω : ∃ z : ℂ, BAendDom sz κ ε n z ∧ BAlocBad2z sz τ n z ω) :
    ∃ w ∈ S, BAlocBad2z sz (τ / 2) n w ω := by
  obtain ⟨z, hz, a, ha⟩ := hω
  obtain ⟨w, hwS, hre, him⟩ := hcov z hz
  refine ⟨w, hwS, ?_⟩
  by_contra hnb
  unfold BAlocBad2z at hnb
  push Not at hnb
  have hnb' := hnb a
  have hw := hS w hwS
  obtain ⟨hzu, hwu, hshift, hζ⟩ := MALocal_geom sz n hε h32 hz hw hre him
  have hu0 : 0 < (Nsz sz n)⁻¹ := inv_pos.2 (by linarith)
  have hu32 : (Nsz sz n)⁻¹ ≤ 1 / 32 := by
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 32) h32
    simpa using this
  have hz0 : 0 < z.im := lt_of_lt_of_le hu0 hzu
  have hw0 : 0 < w.im := lt_of_lt_of_le hu0 hwu
  have hfloor := znet_floor sz n (by omega) hz0 hz.2.2 (le_refl (0 : ℝ))
  have hshiftB := calB_shift_le sz n hz0 (le_refl (0 : ℝ)) hshift
  have hmoduli := fun x y => MALocal_moduli sz n hκ' hz0 hw0 (hdom z hz) (hdom w hw) hu0 (by linarith)
    (by rwa [inv_inv]) hζ hzu hwu ω x y
  have hAd := znet_avg1 sz n a (fun x => BAGz sz n z ω x x) (fun x => BAGz sz n w ω x x)
    (c := 2 * ((Nsz sz n)⁻¹) ^ 5) (fun x => (hmoduli x x).1)
  have hMd := (hmoduli (Classical.arbitrary _) (Classical.arbitrary _)).2.2
  have hsplit : (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, BAGz sz n z ω x x -
        BAm d (sz.L n) (sz.lam n) z =
      ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, BAGz sz n w ω x x -
        BAm d (sz.L n) (sz.lam n) w) +
        (((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, BAGz sz n z ω x x -
          (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, BAGz sz n w ω x x) -
            (BAm d (sz.L n) (sz.lam n) z - BAm d (sz.L n) (sz.lam n) w)) := by ring
  have hX : ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, BAGz sz n z ω x x -
        BAm d (sz.L n) (sz.lam n) z‖ ≤
      ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, BAGz sz n w ω x x -
        BAm d (sz.L n) (sz.lam n) w‖ + 4 * ((Nsz sz n)⁻¹) ^ 5 := by
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have := norm_sub_le ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, BAGz sz n z ω x x -
          (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, BAGz sz n w ω x x)
        (BAm d (sz.L n) (sz.lam n) z - BAm d (sz.L n) (sz.lam n) w)
    linarith
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hsq := MALocal_rpow_sq hW τ
  have := znet_loc2_core (s := ((sz.W n : ℕ) : ℝ) ^ (τ / 2)) (Bz := calB sz n z.im 0) (Bw := calB sz n w.im 0)
    (u := (Nsz sz n)⁻¹)
    (X := ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, BAGz sz n z ω x x -
      BAm d (sz.L n) (sz.lam n) z‖)
    (Y := ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, BAGz sz n w ω x x -
      BAm d (sz.L n) (sz.lam n) w‖)
    (e := 4 * ((Nsz sz n)⁻¹) ^ 5) h5 hshiftB hfloor hu0 hu32 (by positivity) le_rfl hnb' hX
  rw [hsq] at this
  exact absurd ha (not_lt.2 this)

/-- **The count** (twin of `net_count`, `ZNet.lean:101`, with the constant `25` replaced by `C ≤ N`): at most `C N^{14}` net points of
probability `N^{-(D+15)}` each have total mass `≤ N^{-D}`. -/
private theorem MALocal_net_count {N D C : ℝ} (c : ℕ) (hC : 1 ≤ C) (hN : C ≤ N) (hc : (c : ℝ) ≤ C * N ^ (14 : ℕ)) :
    (c : ℝ≥0∞) * ENNReal.ofReal (N ^ (-(D + 15))) ≤ ENNReal.ofReal (N ^ (-D)) := by
  have hN0 : 0 < N := by linarith
  have hexp : N ^ (14 : ℕ) * N ^ (-(D + 15)) = N ^ (-D) * N⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hN0,
      show ((14 : ℕ) : ℝ) + -(D + 15) = -D + (-1) by push_cast; ring, Real.rpow_add hN0, Real.rpow_neg_one]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have h1 : (c : ℝ) * N ^ (-(D + 15)) ≤ C * N ^ (14 : ℕ) * N ^ (-(D + 15)) :=
    mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hN0.le _)
  have h2 : C * N ^ (14 : ℕ) * N ^ (-(D + 15)) = C * (N ^ (-D) * N⁻¹) := by rw [mul_assoc, hexp]
  have h3 : C * N⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hN0]; exact hN
  have h4 : 0 ≤ N ^ (-D) := Real.rpow_nonneg hN0.le _
  nlinarith

/-- The cardinality of the net: `(2R/h + 1)(1/h + 1) ≤ (4R + 2) N^{14}` for `h = N^{-7}`, `N ≥ 1`, `R ≥ 0`. -/
private theorem MALocal_card_le {N R : ℝ} (hN : 1 ≤ N) (hR : 0 ≤ R) :
    (2 * R / N ^ (-7 : ℝ) + 1) * (1 / N ^ (-7 : ℝ) + 1) ≤ (4 * R + 2) * N ^ (14 : ℕ) := by
  have hN0 : 0 < N := by linarith
  have hinv : 1 / N ^ (-7 : ℝ) = N ^ (7 : ℕ) := by rw [one_div, znet_rpow_neg7 hN0]
  have h7 : (1 : ℝ) ≤ N ^ (7 : ℕ) := one_le_pow₀ hN
  rw [div_eq_mul_one_div, hinv]
  have h14 : N ^ (14 : ℕ) = N ^ (7 : ℕ) * N ^ (7 : ℕ) := by rw [← pow_add]
  rw [h14]
  nlinarith [mul_nonneg hR (sub_nonneg.2 h7), mul_nonneg (mul_nonneg hR (sub_nonneg.2 h7)) (sub_nonneg.2 h7),
    mul_nonneg hR (by positivity : (0 : ℝ) ≤ N ^ (7 : ℕ))]

/-- The thresholds of the net argument along an admissible sequence: `32 ≤ N`, `5 ≤ W^{τ/2}`, any fixed `C ≤ N` (`N → ∞`, `W → ∞`,
`Main_DEL_COND`), and `0 ≤ λ_n ≤ 𝔡⁻¹` (`(eq:WO)`). -/
private theorem MALocal_thresholds {𝔠 𝔡 : ℝ} (sz : Sizes d) (hA : sz.Admissible 𝔠 𝔡) {τ : ℝ} (hτ : 0 < τ) (C : ℝ) :
    ∀ᶠ n in atTop, 32 ≤ Nsz sz n ∧ C ≤ Nsz sz n ∧ 5 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) ∧ 0 ≤ sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
  have hN : ∀ᶠ n in atTop, max 32 C ≤ Nsz sz n := hA.2.2.1.eventually_ge_atTop (max 32 C)
  have hW : ∀ᶠ n in atTop, (5 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (τ / 2) := by
    have h := RBM.Green.tendsto_W sz hA.1 hA.2.2.1 hA.2.2.2.1
    exact ((tendsto_rpow_atTop (by positivity : 0 < τ / 2)).comp h).eventually_ge_atTop 5
  filter_upwards [hN, hW, hA.2.2.2.2] with n h1 h2 h3
  exact ⟨le_trans (le_max_left _ _) h1, le_trans (le_max_right _ _) h1, h2,
    le_trans (Real.rpow_nonneg (Nat.cast_nonneg _) _) h3.1, h3.2⟩

/-- **A3, `baMANetLoc`** (twin of `netLoc`, `ZNet.lean:999`): `BAEnd_locSCL` from its fixed-`z` form by the finite net of representatives
`MALocal_net_exists` (mesh `N^{-7}`, real range `2 + 2 d 𝔡⁻¹` of the ρ-bulk by `MALocal_bulk_abs_le`), the cover lemmas at `(τ/2, D + 15)`,
the union bound and the count `(4R + 2) N^{14} N^{-(D+15)} ≤ N^{-D}` (`N ≥ 4R + 2`). -/
theorem baMANetLoc (d : ℕ) : BAMANetLoc d := by
  intro hFix hd 𝔠 𝔡 sz hA κ ε τ D hκ hε hτ hD
  have hF := hFix hd 𝔠 𝔡 sz hA κ ε (τ / 2) (D + 15) hκ hε (by positivity) (by positivity)
  have h𝔡 : 0 < 𝔡 := hA.2.1
  set R : ℝ := 2 + 2 * d * 𝔡⁻¹ with hRdef
  have hR0 : 0 ≤ R := by positivity
  set κ' : ℝ := (Real.pi * κ) ^ 5 / 2048 with hκ'def
  have hκ' : 0 < κ' := by positivity
  filter_upwards [hF, MALocal_thresholds sz hA hτ (max (κ'⁻¹ * κ'⁻¹ * (1 + κ'⁻¹ * κ'⁻¹)) (4 * R + 2))] with n hn hth
  obtain ⟨h32, hCN, h5, hl0, hl1⟩ := hth
  have hCN1 := le_trans (le_max_left _ _) hCN
  have hCN2 := le_trans (le_max_right _ _) hCN
  have hN1 : (1 : ℝ) ≤ Nsz sz n := by linarith
  have hh0 : 0 < Nsz sz n ^ (-7 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hdom : ∀ z : ℂ, BAendDom sz κ ε n z → κ' ≤ (BAm d (sz.L n) (sz.lam n) z).im := fun z hz =>
    MALocal_endDom_dom hκ hz
  have hP : ∀ z, BAendDom sz κ ε n z → |z.re| ≤ R ∧ 0 ≤ z.im ∧ z.im ≤ 1 := by
    intro z hz
    refine ⟨?_, (MALocal_endDom_im_pos hz).le, hz.2.2⟩
    have h1 := MALocal_bulk_abs_le d (sz.L n) (sz.lam n) κ z.re hκ hz.1
    rw [abs_of_nonneg hl0] at h1
    have h2 : 2 * (d : ℝ) * sz.lam n ≤ 2 * (d : ℝ) * 𝔡⁻¹ := mul_le_mul_of_nonneg_left hl1 (by positivity)
    linarith
  obtain ⟨S, hcard, hS, hcov⟩ := MALocal_net_exists (P := BAendDom sz κ ε n) hR0 hh0 hP
  have hcard' : (S.card : ℝ) ≤ (4 * R + 2) * Nsz sz n ^ (14 : ℕ) := hcard.trans (MALocal_card_le hN1 hR0)
  have hnc := MALocal_net_count (D := D) S.card (by linarith) hCN2 hcard'
  refine ⟨?_, ?_⟩
  · refine le_trans (net_union_le (Sizes.seqP (sz.withLam 0)) S {ω | ∃ z : ℂ, BAendDom sz κ ε n z ∧ BAlocBad1z sz τ n z ω}
      (fun w => {ω | BAlocBad1z sz (τ / 2) n w ω}) (ENNReal.ofReal (Nsz sz n ^ (-(D + 15)))) ?_ ?_) hnc
    · intro ω hω
      obtain ⟨w, hw, hbad⟩ := MALocal_locBad1_net sz n hd hκ' hε h32 hCN1 hdom h5 S hS hcov ω hω
      exact Set.mem_biUnion hw hbad
    · intro w hw
      exact (hn w (hS w hw)).1
  · refine le_trans (net_union_le (Sizes.seqP (sz.withLam 0)) S {ω | ∃ z : ℂ, BAendDom sz κ ε n z ∧ BAlocBad2z sz τ n z ω}
      (fun w => {ω | BAlocBad2z sz (τ / 2) n w ω}) (ENNReal.ofReal (Nsz sz n ^ (-(D + 15)))) ?_ ?_) hnc
    · intro ω hω
      obtain ⟨w, hw, hbad⟩ := MALocal_locBad2_net sz n hd hκ' hε h32 hCN1 hdom h5 S hS hcov ω hω
      exact Set.mem_biUnion hw hbad
    · intro w hw
      exact (hn w (hS w hw)).2

end Net

/-! ## 5. A4-A8: locSC at BA and the bridge to `UNLocAvgBA`, per `d` -/

section Main

/-- **A4, `baEnd_locSCL`**: `BAEnd_locSCL d` from `UNMLOutBA d` (A3 ∘ A2; `MR:locSC`, `1_2:653`; `(G_bound)`, `(G_bound_ave)`). -/
theorem baEnd_locSCL (d : ℕ) (hML : UNMLOutBA d) : BAEnd_locSCL d :=
  baMANetLoc d (baLocSCFixed_of_ML d hML)

/-- **A6, `unLocAvgBAAt_of_locSCL`** (per-`d` core of the bridge; the band `locSC_to_UNLocAvgBand`, `Endpoints.lean:519`): the second half
of `BAEnd_locSCL d` is `UNLocAvgBAAt d`; the only rewriting is `𝓑_{η,0} = Bctl n (1 - η)` (`calB_zero_eq_Bctl`, `Im z > 0`). -/
theorem unLocAvgBAAt_of_locSCL (d : ℕ) (hd : 3 ≤ d) (h : BAEnd_locSCL d) : UNLocAvgBAAt d := by
  intro 𝔠 𝔡 sz hA κ ε τ D hκ hε hτ hD
  filter_upwards [h hd 𝔠 𝔡 sz hA κ ε τ D hκ hε hτ hD] with n hn
  refine le_trans (measure_mono ?_) hn.2
  rintro ω ⟨z, hz, a, ha⟩
  refine ⟨z, ⟨hz.1, hz.2.1, hz.2.2⟩, a, ?_⟩
  rw [calB_zero_eq_Bctl sz n (by omega) (MALocal_endDom_im_pos hz)]
  exact ha

end Main

/-! ## 6. A9: compiled nonempty instances at `d = 3` -/

end RBM.BA

end
