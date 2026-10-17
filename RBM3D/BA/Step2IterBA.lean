/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step2CloseGen
import RBM3D.Chain.Step2EventsGenTw
import RBM3D.Chain.NewKLKGen
import RBM3D.BA.Step2BA
import RBM3D.BA.NewKLKBA
import RBM3D.BA.KInduct
import RBM3D.BA.EMn2BA
import RBM3D.BA.GreenSchur
import RBM3D.BA.TwistStep2
import RBM3D.BA.NetLiftBA
import RBM3D.Induction.Step2Scale

/-!
# The Step 2 iteration at the block Anderson carrier, first half (BA-T row T1-BA, ticket T2487)

Check file `docs/tickets/checks/T2487-check.lean`; T1's merged skeleton (`Chain/Step2IterGen`, `Step2IterGen2`, `OptL2Gen`,
`Step2CloseGen`).  No merged file is edited.  The carrier is `baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)` (`toFlowFM = baFMz sz z`).

* **Target 1** `baStep2Mat_Hpath_herm`: the grid walk of `baStep2Mat` is Hermitian.
* **Target 2** `baStep2_oneLoop`: `Step2IterGen_OneLoop (baFMz sz z)` under `0 < κ` and the flow (finding F2).
* **Target 3** `baStep2Mat_listLink`: `Step2IterGen_ListLink (baStep2Mat sz lam0 E)`.
* **Target 4** `baStep2_K2`: `Step2IterGen_K2` at the BA family (kernel at `g₀`, profile at `g`; the forward comparison R1).
* **Target 5** `baStep2_newKLK`: `Step2IterGen_NewKLK` at the BA family, with the constant uniform in `(sz, z)` (finding F1).
* **Target 6** `baSTBdatagL_holds`: the size data (`ST_Bdata_holds` with `1 - t₀ ≥ Im z / 2`).
* **Target 7** `baScaleExists_holds`: P3, the scale family (`stScaleExists_holds` with P6 `baFlow_premises`).

Coupling (UBA-C1; R1 = `g₀² ≤ g²`, `g² ≤ A g₀²`, `A = (κ+1)/κ`): the crossing between the kernel at `g₀` and the profile at `g` lives in the
proofs of targets 4 and 5 only.  Ports: copies of `stNewKLKAtgL'_of` (`Chain/NewKLKGen.lean:416-605`), `ST_Bdata_holds`
(`Induction/Step2Iterate.lean:1049-1173`), `stScaleExists_holds` (`Induction/Step2Scale.lean:430-567`) in this repository
(no RBM1D/RBM2D text).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.maxHeartbeats false

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal

open private NewKLKBA_conv_P NewKLKBA_tail from RBM3D.BA.NewKLKBA
open private nkl_Cs_ge_one nkl_tailT_le_tailW nkl_zdistInf_sub_comm from RBM3D.Induction.NewKLK
open private NewKLKGen_bound2 NewKLKGen_ward_LKM from RBM3D.Chain.NewKLKGen
open private st2sSeq st2sSeq_bounds st2sSeq_cap st2sSeq_clause4 st2sSeq_floor st2sSeq_mono_succ st2sSeq_tailT_mono_time
  st2s_cap_arith st2s_floor_arith from RBM3D.Induction.Step2Scale

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Targets 1-3: the Hermitian walk, the one loop, the list link -/

/-- **Target 1, `baStep2Mat_Hpath_herm`** (BAT-C1; pattern `BA/ConArg.lean:308-316`): the grid walk of the BA carrier, `lam0 • Ψ + pathH (sz.withLam 0)`,
is Hermitian, for every `lam0, E`: the input `hHerm` of `ST_step2_of_pinsg` and `stOptL2_of_pinsg`. -/
theorem baStep2Mat_Hpath_herm {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (ω : PathΩ sz) : ((baStep2Mat sz lam0 E).Hpath s t K n k ω).IsHermitian := by
  rw [baStep2Mat_Hpath]
  refine IsHermitian.add ?_ (pathH_isHermitian (sz.withLam 0) s t K n k ω)
  unfold IsHermitian
  rw [conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
    show star (lam0 n : ℂ) = (lam0 n : ℂ) from Complex.conj_ofReal _]

/-- **Target 2, `baStep2_oneLoop`** (the single BA one-loop proof; `Def_Ktza`, `1_2:988`): `Step2IterGen_OneLoop` at `baFMz sz z` under
`0 < κ` and the flow.  Conjunct 1: `baKsol_one` at `g₀_n > 0` (`BAflow_lam0_window`) with `BAReal` (`BAflow_real`); `BAKsol` is `0`
when no tree solution exists, so there is no flow-free form (finding F2).  Conjunct 2: the argument of `ST_Lloop_one_false` at
`seqHflowBA` (`EMn2BA_seqHflowBA_herm`). -/
theorem baStep2_oneLoop {d : ℕ} (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (hκ : 0 < κ)
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) : Step2IterGen_OneLoop (baFMz sz z) := by
  refine ⟨?_, fun n u a ω => ?_⟩
  · filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow] with n hn u hu0 hu1 σ a
    have h := baKsol_one d hκ hn.1 (sz.three_le_L n) (sz.W n) (BAflow_real κ ε 𝔠 𝔡 sz z hflow n)
      (t := u) ⟨hu0, hu1⟩ (fun _ : Fin 1 => σ) (fun _ => a)
    change BAKsol d (sz.L n) (sz.W n) _ _ u (KLloopOf d (sz.L n) (fun _ : Fin 1 => σ) (fun _ => a)) = _
    rw [h]
    cases σ <;> rfl
  · have hH := EMn2BA_seqHflowBA_herm sz (BAflowLam0 sz z) n u ω
    have hHb : (blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA (BAflowLam0 sz z) n u ω)).IsHermitian := by
      unfold blockMat
      exact hH.submatrix _
    change BALloop sz (BAflowLam0 sz z) (BAflowEs sz z) n u (fun _ : Fin 1 => false) (fun _ => a) ω =
      (starRingEnd ℂ) (BALloop sz (BAflowLam0 sz z) (BAflowEs sz z) n u (fun _ : Fin 1 => true) (fun _ => a) ω)
    unfold BALloop loopFine loopM
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
    have hE := ST_Eblk_herm d (sz.L n) (sz.W n) a
    rw [ST_Gres_false hHb]
    have hm : (Gres (blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA (BAflowLam0 sz z) n u ω))
        (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) u) true)ᴴ *
        Eblk d (sz.L n) (sz.W n) a =
        (Eblk d (sz.L n) (sz.W n) a *
          Gres (blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA (BAflowLam0 sz z) n u ω))
            (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) u) true)ᴴ := by
      rw [Matrix.conjTranspose_mul, hE]
    rw [hm, Matrix.trace_conjTranspose, Matrix.trace_mul_comm]
    rfl

/-- **Target 3, `baStep2Mat_listLink`** (T1b audit O3; `loopM_eq_loopL`): the class `Step2IterGen_ListLink` at the BA carrier, for every
`lam0, E`.  `𝒦_I` at `KLloopOf σ a` is `𝒦^{(k)}_{σ,a}` by definition (`baStep2Mat_KI`). -/
theorem baStep2Mat_listLink {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) : Step2IterGen_ListLink (baStep2Mat sz lam0 E) :=
  ⟨fun n u H k σ a => by
    change loopFine d (sz.L n) (sz.W n) H _ σ a = loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) H) _ _
    rw [loopFine, loopM_eq_loopL]
    rfl, fun n u k σ a => rfl⟩

/-! ## 2. Target 4: the `𝒦^{(2)}` decay at the BA family, and the forward profile comparison (R1) -/

section Compare

/-- `0 < g_n ≤ 𝔡⁻¹` eventually along a BA flow (`(eq:WO)`, `1_2:363`). -/
private theorem Step2IterBA_lam_window {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} {sz : Sizes d} {z : ℕ → ℂ} (h : BAFlow sz κ ε 𝔠 𝔡 z) :
    ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
  filter_upwards [h.1.2.2.2.2] with n hn
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hn.1, hn.2⟩

/-- `ℓ_t` is monotone in the coupling `g ≥ 0`. -/
private theorem Step2IterBA_ellT_mono {L : ℕ} {g₀ g t : ℝ} (hg : g₀ ≤ g) : ellT L g₀ t ≤ ellT L g t := by
  unfold ellT
  exact min_le_min (max_le_max (div_le_div_of_nonneg_right hg (Real.sqrt_nonneg _)) le_rfl) le_rfl

/-- `(g₀² + w)⁻¹ ≤ A (g² + w)⁻¹` from `g₀ ≤ g`, `g² ≤ A g₀²`, `A ≥ 1`, `w ≥ 0`. -/
private theorem Step2IterBA_inv_le {g₀ g w A : ℝ} (h0 : 0 ≤ g₀) (hg : g₀ ≤ g) (hA1 : 1 ≤ A) (hsq : g ^ 2 ≤ A * g₀ ^ 2)
    (hw : 0 ≤ w) : (g₀ ^ 2 + w)⁻¹ ≤ A * (g ^ 2 + w)⁻¹ := by
  rcases (add_nonneg (sq_nonneg g₀) hw).eq_or_lt with h | h
  · rw [← h, _root_.inv_zero]
    have : 0 ≤ g ^ 2 + w := by positivity
    positivity
  · have hgg : g₀ ^ 2 ≤ g ^ 2 := by nlinarith
    have h2 : 0 < g ^ 2 + w := by linarith
    rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ h h2]
    nlinarith

/-- **Forward comparison of the tail** (R1; `tail_{g₀} ≤ A tail_g`): for `0 ≤ g₀ ≤ g`, `g² ≤ A g₀²`, `1 ≤ A`, `L ≥ 1`, `r ≥ 0`.  The reverse
bound is false (T1 row 13) and is not used. -/
private theorem Step2IterBA_tailT_le {d L : ℕ} {g₀ g t A r : ℝ} (hL : 1 ≤ (L : ℝ)) (h0 : 0 ≤ g₀) (hg : g₀ ≤ g)
    (hA1 : 1 ≤ A) (hsq : g ^ 2 ≤ A * g₀ ^ 2) (hr : 0 ≤ r) : tailT d L g₀ t r ≤ A * tailT d L g t r := by
  unfold tailT BparamR
  have hw : 0 ≤ |1 - t| := abs_nonneg _
  have hc2 : 0 ≤ ((L : ℝ) ^ d * |1 - t|)⁻¹ := by positivity
  have hc1 : 0 ≤ ((r + 1) ^ (d - 2))⁻¹ := by positivity
  have hB : (g₀ ^ 2 + |1 - t|)⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * |1 - t|)⁻¹ ≤
      A * ((g ^ 2 + |1 - t|)⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * |1 - t|)⁻¹) := by
    have h1 := mul_le_mul_of_nonneg_right (Step2IterBA_inv_le h0 hg hA1 hsq hw) hc1
    have h2 : ((L : ℝ) ^ d * |1 - t|)⁻¹ ≤ A * ((L : ℝ) ^ d * |1 - t|)⁻¹ := le_mul_of_one_le_left hc2 hA1
    rw [mul_add]
    nlinarith
  have hℓ0 := ellT_pos (L := L) (g := g₀) (t := t) hL
  have hE : Real.exp (-Real.sqrt (r / ellT L g₀ t)) ≤ Real.exp (-Real.sqrt (r / ellT L g t)) := by
    refine Real.exp_le_exp.2 (neg_le_neg (Real.sqrt_le_sqrt ?_))
    exact div_le_div_of_nonneg_left hr hℓ0 (Step2IterBA_ellT_mono hg)
  have hB0 : 0 ≤ A * ((g ^ 2 + |1 - t|)⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * |1 - t|)⁻¹) := by
    have : 0 ≤ (g ^ 2 + |1 - t|)⁻¹ * ((r + 1) ^ (d - 2))⁻¹ := by positivity
    have hA0 : 0 ≤ A := by linarith
    positivity
  calc _ ≤ A * ((g ^ 2 + |1 - t|)⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * |1 - t|)⁻¹) *
        Real.exp (-Real.sqrt (r / ellT L g t)) :=
        mul_le_mul hB hE (Real.exp_pos _).le hB0
    _ = _ := by ring

/-- The forward comparison for the truncated tail `tailW`. -/
private theorem Step2IterBA_tailW_le {d L : ℕ} {g₀ g t A ℓ W D r : ℝ} (hL : 1 ≤ (L : ℝ)) (h0 : 0 ≤ g₀) (hg : g₀ ≤ g)
    (hA1 : 1 ≤ A) (hsq : g ^ 2 ≤ A * g₀ ^ 2) (hr : 0 ≤ r) (hℓ : 0 ≤ ℓ) (hW : 0 ≤ W) :
    tailW d L g₀ t ℓ W D r ≤ A * tailW d L g t ℓ W D r := by
  unfold tailW
  have hA0 : 0 ≤ A := by linarith
  have h1 := Step2IterBA_tailT_le (d := d) (t := t) hL h0 hg hA1 hsq (le_min hr hℓ)
  have h2 : W ^ (-D) ≤ A * W ^ (-D) := le_mul_of_one_le_left (Real.rpow_nonneg hW _) hA1
  exact max_le (h1.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hA0))
    (h2.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hA0))

/-- **The forward profile comparison** `STprof (sz.withLam g₀) ≤ A · STprof sz` (R1; proof-internal, target 4). -/
private theorem Step2IterBA_prof_le {d : ℕ} (sz : Sizes d) (g₀ : ℕ → ℝ) (A : ℝ) (n : ℕ) (hA1 : 1 ≤ A) (h0 : 0 ≤ g₀ n)
    (hg : g₀ n ≤ sz.lam n) (hsq : sz.lam n ^ 2 ≤ A * g₀ n ^ 2) (u D ℓ : ℝ) (hℓ : 0 ≤ ℓ) (a b : Zd d (sz.L n)) :
    STprof (sz.withLam g₀) n u D ℓ a b ≤ A * STprof sz n u D ℓ a b := by
  have hL : (1 : ℝ) ≤ (sz.L n : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hW : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold STprof
  have h := Step2IterBA_tailW_le (d := d) (L := sz.L n) (t := u) (D := D) (W := ((sz.W n : ℕ) : ℝ))
    (r := ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ)) hL h0 hg hA1 hsq (Nat.cast_nonneg _) hℓ hW
  have hc : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (g₀ n) u ℓ ((sz.W n : ℕ) : ℝ) D
        ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ)
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (A * tailW d (sz.L n) (sz.lam n) u ℓ ((sz.W n : ℕ) : ℝ) D
        ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left h hc
    _ = _ := by ring

end Compare

/-- **Target 4, `baStep2_K2`** (`(Kn2sol)`, `7_8:2090`): `Step2IterGen_K2` at the BA family.  `stK2decaygL'_ba` (`NewKLKBA:567`) at `sz.withLam g₀`,
`E ≡ E_n`, gives the bound with the profile at `g₀`; the forward comparison `STprof (sz.withLam g₀) ≤ A · STprof sz`, `A = (κ+1)/κ`
(R1, `TwistStep2_lam0_sq`), moves it to the profile at `g`.  The constant is `Q₀ A` (`Q₀` of `(d, κ, 𝔡)`). -/
theorem baStep2_K2 (d : ℕ) : Step2IterGen_K2 d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) := by
  intro hd κ ε 𝔠 𝔡 hκ h𝔡 sz z hflow s t hs ht1
  obtain ⟨Q₀, hQ₀, HQ⟩ := stK2decaygL'_ba d hd κ 𝔡 hκ h𝔡
  have hA1 : 1 ≤ (κ + 1) / κ := by rw [le_div_iff₀ hκ]; linarith
  refine ⟨Q₀ * ((κ + 1) / κ), by positivity, ?_⟩
  filter_upwards [Step2IterBA_lam_window hflow] with n hn u D σ a hsu hut hD
  have hu0 : 0 ≤ u := (hs n).trans hsu
  have hu1 : u < 1 := hut.trans_lt (ht1 n)
  have hg := baStep2Fam_lam_pos_le hκ hflow n hn.1
  have hm := (EMn2BA_mF_data sz hflow n).1
  have h := HQ (sz.withLam (BAflowLam0 sz z)) n (BAflowEs sz z n) u D hg.1 (hg.2.trans hn.2) hm hu0 hu1 hD σ a
  have hR1 := TwistStep2_lam0_sq hκ hflow n
  have hP := Step2IterBA_prof_le sz (BAflowLam0 sz z) ((κ + 1) / κ) n hA1 hg.1.le hg.2 hR1.2 u D
    ((sz.L n : ℕ) : ℝ) (Nat.cast_nonneg _) (a 0) (a 1)
  calc ‖(baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).K n u σ a‖
      ≤ Q₀ * STprof (sz.withLam (BAflowLam0 sz z)) n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) := h
    _ ≤ Q₀ * (((κ + 1) / κ) * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1)) :=
        mul_le_mul_of_nonneg_left hP hQ₀.le
    _ = _ := by ring

/-! ## 3. Target 6: the size data at the BA setting and horizon (copy of `ST_Bdata_holds`, `Induction/Step2Iterate.lean:1049-1173`) -/

set_option maxHeartbeats 800000 in
/-- **Target 6, `baSTBdatagL_holds`** (`(eq:WO)`, `1_2:363`): the size data of `ST_Bdata_holds` at `BAFlow` and the horizon `BAflowT0`:
`W^{-d} B_{u,0} ≤ (g² W^d)⁻¹ + (N(1-u))⁻¹ ≤ W^{-2𝔡} + 4 N^{-ε}` for `u ≤ t_n ≤ t₀_n`, and `B_{u,0} ≥ (𝔡^{-2} + 1)⁻¹`.  The only change
is the source of `1 - u`: `1 - u ≥ 1 - t₀ ≥ Im z/2` (`EMn2BA_one_sub_T0`; the copy uses the weaker `Im z/4`, so the constants `cB`, `c`
are those of the band) and `u < 1` from `EMn2BA_T0_lt_one`. -/
theorem baSTBdatagL_holds (d : ℕ) (hd : 0 < d) :
    STBdatagL d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) BAflowT0 := by
  intro κ ε 𝔡 hκ hε h𝔡
  refine ⟨(𝔡⁻¹ ^ 2 + 1)⁻¹, by positivity, fun 𝔠 => ?_⟩
  rcases le_or_gt 𝔠 0 with h𝔠 | h𝔠
  · exact ⟨1, one_pos, fun sz z hflow => absurd hflow.1.1 (not_lt.2 h𝔠)⟩
  refine ⟨min (2 * 𝔡 * 𝔠) ε / 2, by
    have := lt_min (mul_pos (mul_pos two_pos h𝔡) h𝔠) hε; linarith, ?_⟩
  intro sz z hflow t ht0 htT
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hband : sz.Bandwidth 𝔠 := hflow.1.2.2.2.1
  have hWO : sz.WO 𝔡 := hflow.1.2.2.2.2
  have hsize := tendsto_size sz hsz
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = min (2 * 𝔡 * 𝔠) ε / 2 := ⟨_, rfl⟩
  have hc : 0 < c := by
    rw [hcdef]; have := lt_min (mul_pos (mul_pos two_pos h𝔡) h𝔠) hε; linarith
  have hc1 : 2 * c ≤ 2 * 𝔡 * 𝔠 := by rw [hcdef]; have := min_le_left (2 * 𝔡 * 𝔠) ε; linarith
  have hc2 : 2 * c ≤ ε := by rw [hcdef]; have := min_le_right (2 * 𝔡 * 𝔠) ε; linarith
  rw [← hcdef]
  filter_upwards [hWO, hband, ST_size_pow_big sz hsize (a := c) (M := 5) hc,
    hsize.eventually (eventually_ge_atTop 1)] with n hwo hbn hN5 hN1 u hu0 hut
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have him := EMn2BA_zim_pos sz hflow n
  have hlt1 : u < 1 := lt_of_le_of_lt (hut.trans (htT n)) (EMn2BA_T0_lt_one hκ sz hflow n)
  have hlam : 0 < sz.lam n :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hwo.1
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := pow_pos hL d
  have hz0 : ((0 : ℕ) : ℝ) + 1 = 1 := by norm_num
  have hBp : Bparam d (sz.L n) (sz.lam n) u 0 =
      (sz.lam n ^ 2 + (1 - u))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by
    unfold Bparam
    rw [abs_of_pos (by linarith : (0 : ℝ) < 1 - u)]
    simp
  have hBc : sz.Bctl n u = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) u 0 := rfl
  constructor
  · -- the lower bound
    rw [hBc, hBp, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hWd.le)
    have h1 : (sz.lam n ^ 2 + (1 - u))⁻¹ ≥ (𝔡⁻¹ ^ 2 + 1)⁻¹ := by
      refine inv_anti₀ (by positivity) ?_
      have := pow_le_pow_left₀ hlam.le hwo.2 2
      linarith
    have h2 : 0 ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ :=
      inv_nonneg.mpr (mul_nonneg hLd.le (by linarith))
    linarith
  · -- the upper bound
    have hu1 : (z n).im / 4 ≤ 1 - u := by
      have h2 := EMn2BA_one_sub_T0 hκ sz hflow n
      linarith [hut.trans (htT n)]
    have hNim : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ (z n).im := (hflow.2 n).2.1
    have hsz2 : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
      unfold Sizes.size; push_cast; ring
    -- `(N(1-u))⁻¹ ≤ 4 N^{-ε}`
    have hA : (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤
        4 * ((sz.size n : ℕ) : ℝ) ^ (-ε) := by
      have h1 : (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ =
          (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ := by
        rw [hsz2]; field_simp
      rw [h1]
      have hNε : 0 < ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) := Real.rpow_pos_of_pos hN0 _
      have h2 : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 4 ≤ 1 - u := by linarith
      have h3 : ((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 4) ≤
          ((sz.size n : ℕ) : ℝ) * (1 - u) := mul_le_mul_of_nonneg_left h2 hN0.le
      have h4 : ((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 4) =
          ((sz.size n : ℕ) : ℝ) ^ ε / 4 := by
        have : ((sz.size n : ℕ) : ℝ) ^ ε = ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) := by
          conv_lhs => rw [show ε = 1 + (-1 + ε) by ring]
          rw [Real.rpow_add hN0, Real.rpow_one]
        rw [this]; ring
      rw [h4] at h3
      have h5 : 0 < ((sz.size n : ℕ) : ℝ) ^ ε / 4 := by positivity
      calc (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ ≤ (((sz.size n : ℕ) : ℝ) ^ ε / 4)⁻¹ :=
            inv_anti₀ h5 h3
        _ = 4 * ((sz.size n : ℕ) : ℝ) ^ (-ε) := by
            rw [Real.rpow_neg hN0.le]; field_simp
    -- `(W^d lam²)⁻¹ ≤ W^{-2𝔡} ≤ N^{-2𝔡𝔠}`
    have hB : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-(2 * 𝔡 * 𝔠)) := by
      have h1 := Sizes.lam_sq_mul_pow_ge sz n hwo.1
      have h2 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ =
          (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by rw [mul_comm, mul_inv]
      rw [h2]
      have hNc : 0 < ((sz.size n : ℕ) : ℝ) ^ 𝔠 := Real.rpow_pos_of_pos hN0 _
      calc (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡))⁻¹ :=
            inv_anti₀ (Real.rpow_pos_of_pos hW _) h1
        _ = ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) := (Real.rpow_neg hW.le _).symm
        _ ≤ (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (-(2 * 𝔡)) :=
            Real.rpow_le_rpow_of_nonpos hNc hbn (by linarith)
        _ = ((sz.size n : ℕ) : ℝ) ^ (-(2 * 𝔡 * 𝔠)) := by
            rw [← Real.rpow_mul hN0.le]; congr 1; ring
    rw [hBc, hBp, mul_add]
    have hfirst : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + (1 - u))⁻¹ ≤
        (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (by linarith))
        (inv_nonneg.mpr hWd.le)
    have hsecond : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ≤
        4 * ((sz.size n : ℕ) : ℝ) ^ (-ε) := by rw [mul_comm]; exact hA
    have hN2c : ((sz.size n : ℕ) : ℝ) ^ (-(2 * 𝔡 * 𝔠)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(2 * c)) :=
      Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    have hNe : ((sz.size n : ℕ) : ℝ) ^ (-ε) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(2 * c)) :=
      Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    have hsum : 5 * ((sz.size n : ℕ) : ℝ) ^ (-(2 * c)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-c) := by
      have e : ((sz.size n : ℕ) : ℝ) ^ (-(2 * c)) =
          ((sz.size n : ℕ) : ℝ) ^ (-c) * ((sz.size n : ℕ) : ℝ) ^ (-c) := by
        rw [← Real.rpow_add hN0]; congr 1; ring
      have h5 : 5 * ((sz.size n : ℕ) : ℝ) ^ (-c) ≤ 1 := by
        have hNc : 0 < ((sz.size n : ℕ) : ℝ) ^ c := Real.rpow_pos_of_pos hN0 _
        rw [Real.rpow_neg hN0.le, ← div_eq_mul_inv, div_le_one hNc]
        linarith
      have hp : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-c) := Real.rpow_nonneg hN0.le _
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_right h5 hp]
    linarith

/-! ## 4. Target 7: P3, the scale family at the BA setting (copy of `stScaleExists_holds`, `Induction/Step2Scale.lean:430-567`) -/

/-- **Target 7, P3 `baScaleExists_holds`** (`(eq:def_ell1)`, `3_5:570-577`; design T2452 `:183`, `:193`): the scale family `K^{(m)}_u` of the pin
`STScaleExistsgL` at `BAFlow` and the horizon `BAflowT0`.  The levels are `st2sSeq` (`K^{(0)} = 0`, `𝒯_u(K^{(m+1)}_u) = (W^{-d} B_{u,0})^{1/6}
𝒯_u(K^{(m)}_u)` cut at `L`); the flow premises `t_n < 1` and `RangeCond (ε/2)` are P6 `baFlow_premises` (`NetLiftBA:65`) in place of
`v3_premises_of_stFlow`, and `hflow.1` is the admissibility.  The rest is the proof of `stScaleExists_holds` (`W^{-d} B_{u,0} ≤ 2 N^{-c₀}`,
`c₀ = min(2𝔠𝔡, ε/2)`, `scaleFacts_R1`; `M(D) = 6 ⌈(2 + D)/c₀⌉`). -/
theorem baScaleExists_holds (d : ℕ) :
    STScaleExistsgL d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) BAflowT0 := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s t hs hst htz
  obtain ⟨ht1, hR⟩ := baFlow_premises d κ ε 𝔠 𝔡 hκ hε sz z hflow t htz
  obtain ⟨h𝔠, -, hsize, hBand, hWO⟩ := hflow.1
  -- `d ≥ 1`: for `d = 0` the size `N = 1` does not tend to infinity
  have hd1 : 1 ≤ d := by
    by_contra h
    have hd0 : d = 0 := by omega
    obtain ⟨n, hn⟩ := (hsize.eventually_ge_atTop 2).exists
    have h1 : ((sz.size n : ℕ) : ℝ) = 1 := by simp [Sizes.size, hd0]
    linarith
  set c₀ : ℝ := min (2 * 𝔠 * 𝔡) (ε / 2) with hc₀
  have hc₀pos : 0 < c₀ := lt_min (by positivity) (by linarith)
  have hR1 := RBM.Ind.scaleFacts_R1 sz 𝔠 𝔡 (ε / 2) t h𝔡 hBand hWO hR
  have hL : ∀ n, 1 ≤ ((sz.L n : ℕ) : ℝ) := fun n => by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hW1 : ∀ n, (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.W_pos n
  have hWdN : ∀ n, ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := fun n => by
    have h : (sz.W n) ^ d ≤ sz.size n :=
      Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by have := sz.three_le_L n; omega)) d
    exact_mod_cast h
  have hWN : ∀ n, ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := fun n => by
    have h : ((sz.W n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := by
      exact_mod_cast Nat.le_self_pow (by omega : d ≠ 0) (sz.W n)
    exact h.trans (hWdN n)
  -- eventual facts
  have hsmall : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-c₀) ≤ 1 / 2 :=
    ((tendsto_rpow_neg_atTop hc₀pos).comp hsize).eventually (Iic_mem_nhds (by norm_num))
  have hWlarge : ∀ B : ℝ, ∀ᶠ n in atTop, B ≤ ((sz.W n : ℕ) : ℝ) := by
    intro B
    have h1 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
      (tendsto_rpow_atTop h𝔠).comp hsize
    filter_upwards [hBand, h1.eventually_ge_atTop B] with n hn1 hn2 using hn2.trans hn1
  have hNlarge : ∀ B : ℝ, ∀ᶠ n in atTop, B ≤ ((sz.size n : ℕ) : ℝ) := fun B =>
    hsize.eventually_ge_atTop B
  have hlam : ∀ᶠ n in atTop, 0 ≤ sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ :=
    hWO.mono fun n hn => ⟨le_trans (Real.rpow_nonneg (Nat.cast_nonneg _) _) hn.1, hn.2⟩
  -- the controls `W^{-d} B_{u,0} ∈ (0, 1]`, `≤ 2 N^{-c₀}`, for `u ∈ [s_n, t_n]`
  have hgood : ∀ᶠ n in atTop, 0 ≤ sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ ∧ ∀ u, s n ≤ u → u ≤ t n →
      0 < sz.Bctl n u ∧ sz.Bctl n u ≤ 1 ∧
        sz.Bctl n u ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (-c₀) := by
    filter_upwards [hlam, hR1, hsmall] with n hl hb hsm
    refine ⟨hl.1, hl.2, fun u _ hut => ⟨STBctl_pos sz n (hut.trans_lt (ht1 n)), ?_, hb u hut⟩⟩
    linarith [hb u hut]
  refine ⟨fun m n u => st2sSeq d (sz.L n) (sz.lam n) u (sz.Bctl n u) m, fun n u => rfl,
    ?_, ?_, ?_, ?_⟩
  · -- `STScaleOk`
    intro m
    refine ⟨?_, ?_⟩
    · set A : ℝ := ((m : ℝ) * ((d : ℝ) + 1) / 6) ^ 2 with hAdef
      set Cc : ℝ := (𝔡⁻¹) ^ 2 + 1 with hCc
      filter_upwards [hgood, hWlarge (Real.exp (max 1 A)), hWlarge Cc] with n hg hW2 hW3 u hsu hut
      obtain ⟨hl0, hl1, hb⟩ := hg
      obtain ⟨hβ, hβ1, -⟩ := hb u hsu hut
      have hu : u < 1 := hut.trans_lt (ht1 n)
      obtain ⟨h0, hLm⟩ := st2sSeq_bounds (g := sz.lam n) (hL n) hu hβ hβ1 m
      refine ⟨h0, hLm, ?_⟩
      have hcap := st2sSeq_cap (d := d) (g := sz.lam n) (hL n) hu hβ hβ1 m
      have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith [hW1 n]
      have hlogW : max 1 A ≤ Real.log ((sz.W n : ℕ) : ℝ) :=
        (Real.le_log_iff_exp_le hWpos).2 hW2
      have hCc1 : 1 ≤ Cc := by have : 0 ≤ (𝔡⁻¹) ^ 2 := sq_nonneg _; linarith
      have hlam2 : sz.lam n ^ 2 + 1 ≤ Cc := by
        have := pow_le_pow_left₀ hl0 hl1 2; linarith
      have hlow : ((((sz.W n : ℕ) : ℝ) ^ d) * Cc)⁻¹ ≤ sz.Bctl n u := by
        have h1 := STBctl_ge sz n ((hs n).trans hsu) hu
        calc ((((sz.W n : ℕ) : ℝ) ^ d) * Cc)⁻¹ = ((((sz.W n : ℕ) : ℝ) ^ d))⁻¹ * Cc⁻¹ :=
              mul_inv _ _
          _ ≤ ((((sz.W n : ℕ) : ℝ) ^ d))⁻¹ * (sz.lam n ^ 2 + 1)⁻¹ :=
              mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hlam2) (by positivity)
          _ ≤ _ := h1
      have hcapA := st2s_cap_arith (d := d) (m := m) (hW1 n) hW3 hCc1 hβ hβ1 hlow
        (le_trans (le_max_left _ _) hlogW) (le_trans (le_max_right _ _) hlogW)
      calc st2sSeq d (sz.L n) (sz.lam n) u (sz.Bctl n u) m
          ≤ ellT (sz.L n) (sz.lam n) u * (((m : ℝ) / 6) * (-Real.log (sz.Bctl n u))) ^ 2 := hcap
        _ ≤ ellT (sz.L n) (sz.lam n) u * (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 :=
            mul_le_mul_of_nonneg_left hcapA ellT_nonneg
        _ = _ := mul_comm _ _
    · filter_upwards [hgood] with n hg u v hsu huv hvt
      obtain ⟨hl0, -, hb⟩ := hg
      have hsv : s n ≤ v := hsu.trans huv
      obtain ⟨hβu, hβu1, -⟩ := hb u hsu (huv.trans hvt)
      obtain ⟨hβv, hβv1, -⟩ := hb v hsv hvt
      exact st2sSeq_tailT_mono_time (L := sz.L n) (hL n) hl0 huv (hvt.trans_lt (ht1 n))
        hβu hβu1 hβv hβv1 (STBctl_mono sz n huv (hvt.trans_lt (ht1 n))) m
  · -- `0 ≤ K_m ≤ K_{m+1}`
    intro m
    filter_upwards [hgood] with n hg u hsu hut
    obtain ⟨-, -, hb⟩ := hg
    obtain ⟨hβ, hβ1, -⟩ := hb u hsu hut
    have hu : u < 1 := hut.trans_lt (ht1 n)
    exact ⟨(st2sSeq_bounds (g := sz.lam n) (hL n) hu hβ hβ1 m).1,
      st2sSeq_mono_succ (hL n) hu hβ hβ1 m⟩
  · -- `(kwr3juw)`
    intro m
    filter_upwards [hgood] with n hg u hsu hut
    obtain ⟨-, -, hb⟩ := hg
    obtain ⟨hβ, hβ1, -⟩ := hb u hsu hut
    exact st2sSeq_clause4 (hL n) (hut.trans_lt (ht1 n)) hβ hβ1 m
  · -- the floor
    intro D hD
    set j : ℕ := ⌈(2 + D) / c₀⌉₊ with hj
    have hjc : 2 + D ≤ c₀ * ((j : ℝ) + 1) := by
      have h1 : (2 + D) / c₀ ≤ j := Nat.le_ceil _
      rw [div_le_iff₀ hc₀pos] at h1
      nlinarith
    refine ⟨6 * j, ?_⟩
    filter_upwards [hgood, hNlarge ((2 : ℝ) ^ (j + 1))] with n hg hN u hsu hut
    obtain ⟨-, -, hb⟩ := hg
    obtain ⟨hβ, hβ1, hβ2⟩ := hb u hsu hut
    have hu : u < 1 := hut.trans_lt (ht1 n)
    rcases st2sSeq_floor (g := sz.lam n) (hL n) hu hβ hβ1 (6 * j) with h | h
    · right; exact le_of_eq h.symm
    · left
      have hq : (sz.Bctl n u ^ (1 / 6 : ℝ)) ^ (6 * j) = sz.Bctl n u ^ j := by
        have hq6 : (sz.Bctl n u ^ (1 / 6 : ℝ)) ^ 6 = sz.Bctl n u := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hβ.le]; norm_num
        rw [pow_mul, hq6]
      rw [hq] at h
      have hWd0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos (by linarith [hW1 n]) _
      have hT0 : tailT d (sz.L n) (sz.lam n) u 0 = ((sz.W n : ℕ) : ℝ) ^ d * sz.Bctl n u := by
        rw [tailT_zero]; unfold Sizes.Bctl; field_simp
      rw [hT0] at h
      refine h.trans ?_
      calc sz.Bctl n u ^ j * (((sz.W n : ℕ) : ℝ) ^ d * sz.Bctl n u)
          = ((sz.W n : ℕ) : ℝ) ^ d * sz.Bctl n u ^ (j + 1) := by ring
        _ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) :=
            st2s_floor_arith (hW1 n) (hWdN n) (hWN n) hβ.le hβ2 hD hjc hN

/-! ## 5. Target 5: `lem:newKLK` at the BA family, the constant uniform in `(sz, z)` (finding F1) -/

section NewKLK

/-- **`lem:newKLK` at one carrier and one size index, with explicit constants** (private per-carrier copy of `stNewKLKAtgL'_of`,
`Chain/NewKLKGen.lean:416-605`, `3_5:371`; finding F1): the facts F5, F7, F8, F9 of `NewKLKGenHyp` (`NewKLKGen.lean:383`) are read at the one
carrier `Cm` and the one index `n`, the `(TTT2)` bound is the hypothesis `hTT` at the profile `g = sz.lam n`; the constant is
`C = 2 K_c + 2 C_s (4 + C_K) + C_s C_T`, a function of the constants `K_c, C_K, C_T` only (`C_s = 2^{d-2} e`), so that
`Step2IterGen_NewKLK` at a family gets `C` before the sizes. -/
private theorem Step2IterBA_newKLKAtN_of {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (n : ℕ) {κ K_c C_K CT : ℝ} (hκ : 0 < κ)
    (hKc : 0 ≤ K_c) (hCK : 0 ≤ C_K) (hCT : 0 < CT) (hlam : 0 < sz.lam n) (hIm : κ ≤ (Cm.m n).im)
    (hTT : ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ x y : Zd d (sz.L n), ∑ z : Zd d (sz.L n),
      tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (x - z) : ℕ) : ℝ) *
        tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (z - y) : ℕ) : ℝ) ≤
      (CT / (1 - u)) * tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ))
    (hsupp : ∀ x y, Cm.S n x y ≠ 0 → zdistInf d (sz.L n) (x - y) ≤ 1) (hrow : ∀ x, ∑ y, ‖Cm.S n x y‖ ≤ 1)
    (hsym : ∀ x y, ‖Cm.S n x y‖ = ‖Cm.S n y x‖)
    (hconv : ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (s s' : Bool) (ℓ' D' : ℝ), 0 ≤ ℓ' → 0 ≤ D' → ∀ a a' : Zd d (sz.L n),
      ∑ b, ‖Step2Gen_thetaKer Cm.toFlowFM n s s' u a b‖ *
          tailW d (sz.L n) (sz.lam n) u ℓ' ((sz.W n : ℕ) : ℝ) D' ((zdistInf d (sz.L n) (b - a') : ℕ) : ℝ) ≤
        K_c / (1 - u) *
          tailW d (sz.L n) (sz.lam n) u ℓ' ((sz.W n : ℕ) : ℝ) D' ((zdistInf d (sz.L n) (a - a') : ℕ) : ℝ))
    (hK : ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ σ : Fin 2 → Bool,
      (∀ a₁ : Zd d (sz.L n), ∑ x, ‖Cm.K n u σ ![x, a₁]‖ ≤ C_K * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 - u)⁻¹)) ∧
      (∀ a₀ : Zd d (sz.L n), ∑ y, ‖Cm.K n u σ ![a₀, y]‖ ≤ C_K * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 - u)⁻¹)))
    (hlink : ∀ u : ℝ, 0 ≤ u → u < 1 →
      ∃ ζ : ℂ, ζ.im = (1 - u) * (Cm.m n).im ∧
        (∀ (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool)
          (a : Fin 2 → Zd d (sz.L n)), Cm.LM n u H σ a = loopFine d (sz.L n) (sz.W n) H ζ σ a) ∧
        (∀ (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (x : Idx d (sz.L n) (sz.W n)),
          Cm.GMM n u H x x = Gres H ζ true x x - Cm.m n)) :
    Step2IterGen_NewKLKAtN Cm n
      (2 * K_c + 2 * (2 ^ (d - 2) * Real.exp 1) * (4 + C_K) + (2 ^ (d - 2) * Real.exp 1) * CT) (κ / 2) := by
  have hCs := nkl_Cs_ge_one (d := d)
  set Cs : ℝ := 2 ^ (d - 2) * Real.exp 1 with hCsdef
  have hCs0 : 0 < Cs := by linarith
  intro u D ℓ hu0 hu1 hD hℓ0 hℓL H hH hGM σ a
  have hL : 3 ≤ sz.L n := sz.three_le_L n
  have hv : 0 < 1 - u := by linarith
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
  set Wr : ℝ := ((sz.W n : ℕ) : ℝ) with hWr
  set J : ℝ := STJhatMg Cm n D ℓ u H with hJ
  set g : ℝ := sz.lam n with hg
  set P : ℝ → ℝ := tailW d (sz.L n) g u ℓ Wr D with hP
  have hP0 : ∀ r, 0 < P r := fun r => tailW_pos hWpos r
  have hprof : ∀ x y : Zd d (sz.L n), STprof sz n u D ℓ x y =
      (Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) := fun x y => rfl
  have hprof0 : ∀ x y : Zd d (sz.L n), 0 < STprof sz n u D ℓ x y := fun x y => by
    rw [hprof]; have := hP0 ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ); positivity
  have hF : ∀ (σ' : Fin 2 → Bool) (a' : Fin 2 → Zd d (sz.L n)),
      ‖STLKMg Cm n u H σ' a'‖ ≤ J * STprof sz n u D ℓ (a' 0) (a' 1) := by
    intro σ' a'
    have h := Finset.le_sup' (fun p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) =>
      ‖STLKMg Cm n u H p.1 p.2‖ / STprof sz n u D ℓ (p.2 0) (p.2 1)) (Finset.mem_univ (σ', a'))
    rw [div_le_iff₀ (hprof0 _ _)] at h
    exact h
  have hJ0 : 0 ≤ J := by
    have h := hF σ (fun _ => 0)
    have h1 := norm_nonneg (STLKMg Cm n u H σ (fun _ => 0))
    have h2 := hprof0 (0 : Zd d (sz.L n)) 0
    by_contra hneg
    push Not at hneg
    nlinarith
  -- the data of `mk`
  have hTTT : ∀ x y : Zd d (sz.L n), ∑ z : Zd d (sz.L n),
      tailT d (sz.L n) g u ((zdistInf d (sz.L n) (x - z) : ℕ) : ℝ) *
        tailT d (sz.L n) g u ((zdistInf d (sz.L n) (z - y) : ℕ) : ℝ) ≤
      (CT / (1 - u)) * tailT d (sz.L n) g u ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) :=
    fun x y => hTT u hu0 hu1 x y
  have hCT' : 0 ≤ CT / (1 - u) := by positivity
  -- Bound 1
  set K : ℝ := K_c / (1 - u) with hKdef
  have hK1 : ∀ (s s' : Bool) (p q : Zd d (sz.L n)),
      ∑ b, ‖Step2Gen_thetaKer Cm.toFlowFM n s s' u p b‖ * P ((zdistInf d (sz.L n) (b - q) : ℕ) : ℝ) ≤
        K * P ((zdistInf d (sz.L n) (p - q) : ℕ) : ℝ) :=
    fun s s' p q => hconv u hu0 hu1 s s' ℓ D hℓ0 hD p q
  have hK0 : 0 ≤ K := by positivity
  have hconvJ : ∀ (s s' : Bool) (p q : Zd d (sz.L n)),
      ∑ b, ‖Step2Gen_thetaKer Cm.toFlowFM n s s' u p b‖ *
        (J * ((Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (b - q) : ℕ) : ℝ))) ≤
      K * J * ((Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (p - q) : ℕ) : ℝ)) := by
    intro s s' p q
    have h := mul_le_mul_of_nonneg_left (hK1 s s' p q)
      (mul_nonneg hJ0 (by positivity : (0 : ℝ) ≤ (Wr ^ d)⁻¹))
    calc ∑ b, ‖Step2Gen_thetaKer Cm.toFlowFM n s s' u p b‖ *
          (J * ((Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (b - q) : ℕ) : ℝ)))
        = (J * (Wr ^ d)⁻¹) * ∑ b, ‖Step2Gen_thetaKer Cm.toFlowFM n s s' u p b‖ *
            P ((zdistInf d (sz.L n) (b - q) : ℕ) : ℝ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
      _ ≤ (J * (Wr ^ d)⁻¹) * (K * P ((zdistInf d (sz.L n) (p - q) : ℕ) : ℝ)) := h
      _ = _ := by ring
  have hC2 : 2 * K = 2 * K_c / (1 - u) := by rw [hKdef]; field_simp
  have hB1 : ‖STthetaOpg Cm n u σ (STLKMg Cm n u H σ) a‖ ≤
      (2 * K_c) / (1 - u) * J * STprof sz n u D ℓ (a 0) (a 1) := by
    unfold STthetaOpg
    have hterm : ∀ i : Fin 2, ‖∑ b, Step2Gen_thetaKer Cm.toFlowFM n (σ i) (σ (finRotate 2 i)) u (a i) b *
        STLKMg Cm n u H σ (Function.update a i b)‖ ≤
        ∑ b, ‖Step2Gen_thetaKer Cm.toFlowFM n (σ i) (σ (finRotate 2 i)) u (a i) b‖ *
          (J * STprof sz n u D ℓ ((Function.update a i b) 0) ((Function.update a i b) 1)) := by
      intro i
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hF σ _) (norm_nonneg _)
    rw [Fin.sum_univ_two]
    refine (norm_add_le _ _).trans ((add_le_add (hterm 0) (hterm 1)).trans ?_)
    have e0 : ∀ b, (Function.update a 0 b) 0 = b := fun b => by simp
    have e0' : ∀ b, (Function.update a 0 b) 1 = a 1 := fun b => by simp
    have e1 : ∀ b, (Function.update a 1 b) 0 = a 0 := fun b => by simp
    have e1' : ∀ b, (Function.update a 1 b) 1 = b := fun b => by simp
    simp only [e0, e0', e1, e1', hprof]
    have t0 := hconvJ (σ 0) (σ (finRotate 2 0)) (a 0) (a 1)
    have t1 : ∑ b, ‖Step2Gen_thetaKer Cm.toFlowFM n (σ 1) (σ (finRotate 2 1)) u (a 1) b‖ * (J * ((Wr ^ d)⁻¹ *
        P ((zdistInf d (sz.L n) (a 0 - b) : ℕ) : ℝ))) ≤
        K * J * ((Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) := by
      have h := hconvJ (σ 1) (σ (finRotate 2 1)) (a 1) (a 0)
      rw [nkl_zdistInf_sub_comm (a 1) (a 0)] at h
      calc _ = ∑ b, ‖Step2Gen_thetaKer Cm.toFlowFM n (σ 1) (σ (finRotate 2 1)) u (a 1) b‖ * (J * ((Wr ^ d)⁻¹ *
              P ((zdistInf d (sz.L n) (b - a 0) : ℕ) : ℝ))) :=
            Finset.sum_congr rfl fun b _ => by rw [nkl_zdistInf_sub_comm (a 0) b]
        _ ≤ _ := h
    have hfin : K * J * ((Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) +
        K * J * ((Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) =
        2 * K_c / (1 - u) * J *
          ((Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) := by
      rw [← hC2]; ring
    linarith
  -- Bound 2
  have hWd : ‖(((sz.W n : ℕ) : ℂ) ^ d)‖ = Wr ^ d := by rw [norm_pow, Complex.norm_natCast]
  obtain ⟨ζ, hζ, hLM, hGMd⟩ := hlink u hu0 hu1
  obtain ⟨hKa, hKb⟩ := hK u hu0 hu1 σ
  obtain ⟨hSumA, hSumB⟩ := NewKLKGen_ward_LKM Cm n hκ hIm hu1 hζ hLM hGMd σ hKa hKb H hH hGM
  have hA : ∀ x : Zd d (sz.L n), ‖STLKMg Cm n u H σ ![x, a 1]‖ ≤
      J * ((Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (x - a 1) : ℕ) : ℝ)) := by
    intro x
    have h := hF σ ![x, a 1]
    simpa [hprof] using h
  have hB : ∀ y : Zd d (sz.L n), ‖STLKMg Cm n u H σ ![a 0, y]‖ ≤
      J * ((Wr ^ d)⁻¹ * P ((zdistInf d (sz.L n) (a 0 - y) : ℕ) : ℝ)) := by
    intro y
    have h := hF σ ![a 0, y]
    simpa [hprof] using h
  have key := NewKLKGen_bound2 hsupp hrow hsym (g := g) (t := u) (ℓ := ℓ) (D := D) (CT := CT / (1 - u))
    hWpos hℓ0 hJ0 (cW := (Wr ^ d)⁻¹) (by positivity) (fun x => ‖STLKMg Cm n u H σ ![x, a 1]‖)
    (fun y => ‖STLKMg Cm n u H σ ![a 0, y]‖) (fun x => norm_nonneg _) (fun y => norm_nonneg _)
    (a 0) (a 1) hA hB (hSumA (a 1)) (hSumB (a 0)) hTTT
  have hB2 : ‖STELKLKMg Cm n u H σ a‖ ≤ Wr ^ d *
      (2 * (J * (Wr ^ d)⁻¹ * Cs * P ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) *
          ((4 + C_K) * ((Wr ^ d)⁻¹ * (1 - u)⁻¹)) +
        (if 1 ≤ ℓ then (J * (Wr ^ d)⁻¹) ^ 2 * (Cs * ((CT / (1 - u)) *
          tailT d (sz.L n) g u ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ))) else 0)) := by
    unfold STELKLKMg
    rw [norm_mul, hWd]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun x _ => norm_sum_le _ _).trans ?_)
    refine le_trans (Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_) key
    rw [norm_mul, norm_mul]
  -- the constants
  have hw : 0 < Wr ^ d := by positivity
  set Q2 : ℝ := 2 * Cs * (4 + C_K) with hQ2
  set Cc : ℝ := 2 * K_c + Q2 + Cs * CT with hCc
  have hQ20 : 0 ≤ Q2 := by rw [hQ2]; positivity
  have hCc1 : 0 ≤ Cc - 2 * K_c := by
    rw [hCc]; have := mul_pos hCs0 hCT; linarith
  have hCc2 : 0 ≤ Cc - Q2 := by
    rw [hCc]; linarith [mul_nonneg hCs0.le hCT.le]
  have hCc3 : 0 ≤ Cc - Cs * CT := by
    rw [hCc]; linarith
  set Ps : ℝ := P ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) with hPs
  set Ts : ℝ := tailT d (sz.L n) g u ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) with hTs
  have hTsP : Ts ≤ Ps := nkl_tailT_le_tailW hℓ0 (Nat.cast_nonneg _)
  have hTs0 : 0 ≤ Ts := tailT_nonneg (Nat.cast_nonneg _)
  have hPs0 : 0 < Ps := hP0 _
  have hpr : STprof sz n u D ℓ (a 0) (a 1) = (Wr ^ d)⁻¹ * Ps := hprof _ _
  have hpr0 : 0 < (Wr ^ d)⁻¹ * Ps := by positivity
  have e1 : Wr ^ d * (2 * (J * (Wr ^ d)⁻¹ * Cs * Ps) * ((4 + C_K) * ((Wr ^ d)⁻¹ * (1 - u)⁻¹))) =
      Q2 / (1 - u) * J * ((Wr ^ d)⁻¹ * Ps) := by
    rw [hQ2]
    field_simp
  have e2 : Wr ^ d * ((J * (Wr ^ d)⁻¹) ^ 2 * (Cs * (CT / (1 - u) * Ts))) =
      Cs * CT / (1 - u) * J ^ 2 * ((Wr ^ d)⁻¹ * Ts) := by
    field_simp
  refine ⟨?_, ?_⟩
  · rw [hpr] at hB1 ⊢
    refine hB1.trans ?_
    have h1 : 2 * K_c / (1 - u) ≤ Cc / (1 - u) :=
      div_le_div_of_nonneg_right (by linarith) hv.le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hJ0) hpr0.le
  · rw [hpr]
    refine hB2.trans ?_
    rw [mul_add, e1]
    have hX : 0 ≤ J * ((Wr ^ d)⁻¹ * Ps) / (1 - u) := by positivity
    by_cases h1 : 1 ≤ ℓ
    · simp only [h1, ite_true, mul_one]
      rw [e2]
      have hq : (Wr ^ d)⁻¹ * Ts ≤ (Wr ^ d)⁻¹ * Ps :=
        mul_le_mul_of_nonneg_left hTsP (by positivity)
      have hq2 : Cs * CT / (1 - u) * J ^ 2 * ((Wr ^ d)⁻¹ * Ts) ≤
          Cs * CT / (1 - u) * J ^ 2 * ((Wr ^ d)⁻¹ * Ps) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
      have hdiff : Cc / (1 - u) * (J + J ^ 2) * ((Wr ^ d)⁻¹ * Ps) -
          (Q2 / (1 - u) * J * ((Wr ^ d)⁻¹ * Ps) +
            Cs * CT / (1 - u) * J ^ 2 * ((Wr ^ d)⁻¹ * Ps)) =
          (Cc - Q2) / (1 - u) * J * ((Wr ^ d)⁻¹ * Ps) +
            (Cc - Cs * CT) / (1 - u) * J ^ 2 * ((Wr ^ d)⁻¹ * Ps) := by ring
      have hn1 : 0 ≤ (Cc - Q2) / (1 - u) * J * ((Wr ^ d)⁻¹ * Ps) := by
        have := div_nonneg hCc2 hv.le; positivity
      have hn2 : 0 ≤ (Cc - Cs * CT) / (1 - u) * J ^ 2 * ((Wr ^ d)⁻¹ * Ps) := by
        have := div_nonneg hCc3 hv.le; positivity
      linarith
    · simp only [h1, ite_false, mul_zero, add_zero, mul_zero]
      have hdiff : Cc / (1 - u) * (J + J ^ 2 * 0) * ((Wr ^ d)⁻¹ * Ps) -
          Q2 / (1 - u) * J * ((Wr ^ d)⁻¹ * Ps) =
          (Cc - Q2) / (1 - u) * J * ((Wr ^ d)⁻¹ * Ps) := by ring
      have hn1 : 0 ≤ (Cc - Q2) / (1 - u) * J * ((Wr ^ d)⁻¹ * Ps) := by
        have := div_nonneg hCc2 hv.le; positivity
      linarith

/-- **Target 5, `baStep2_newKLK`** (`lem:newKLK`, `3_5:371`; BA `7_8:1994`): `Step2IterGen_NewKLK` at the BA family, with `C, δ₀` before the sizes.
Per index `n` in the window `0 < g₀_n ≤ g_n`, `0 < g_n ≤ 𝔡⁻¹` (`BAflow_lam0_window`, `(eq:WO)`) the per-carrier copy is applied at
`baStep2Mat sz g₀ E` with the constants `K_c = A K_c⁰`, `K_c⁰ = Q₀ C_T + C_s`, `A = (κ+1)/κ`, `C_K` of `baNewKLKGenHyp`.
* F5, F8, F9 come from `baNewKLKGenHyp` at `sz.withLam g₀` (`baStep2Fam (sz.withLam g₀) (fun _ => E)` and `baStep2Mat sz g₀ (fun _ => E n)` have
  the same fields at index `n`, definitionally; the datum `κ ≤ Im m_F` is `EMn2BA_mF_data`).
* F7 is re-proved at mixed coupling: the kernel `Θ_BA M^{(ss')}` at `g₀` has the tail `Q₀ 𝒯_{g₀}` (`NewKLKBA_tail`) and row sum `(1-u)⁻¹`
  (`baComp_row_le`, `BAReal` at `g₀`); the forward comparison `𝒯_{g₀} ≤ A 𝒯_g` (R1, `TwistStep2_lam0_sq`) puts the tail at the profile
  `g = sz.lam n`, where `(TTT2)` of `ekPropTInf_holds` and `NewKLKBA_conv_P` apply.  No reverse comparison is used. -/
theorem baStep2_newKLK (d : ℕ) : Step2IterGen_NewKLK d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) := by
  intro hd κ 𝔡 hκ h𝔡
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  obtain ⟨Q₀, hQ₀, HQ⟩ := NewKLKBA_tail d hd 𝔡⁻¹ κ hΛ hκ
  obtain ⟨CT, hCT, HT⟩ := ekPropTInf_holds d hd
  obtain ⟨-, C_K, -, hCK, hF5, -, -, hF8, hF9⟩ := baNewKLKGenHyp hd κ 𝔡 hκ h𝔡
  have hCs := nkl_Cs_ge_one (d := d)
  set Cs : ℝ := 2 ^ (d - 2) * Real.exp 1 with hCsdef
  have hCs0 : 0 < Cs := by linarith
  set A : ℝ := (κ + 1) / κ with hAdef
  have hA1 : 1 ≤ A := by rw [hAdef, le_div_iff₀ hκ]; linarith
  have hA0 : 0 ≤ A := by linarith
  set Kc : ℝ := A * (Q₀ * CT + Cs) with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  refine ⟨2 * Kc + 2 * Cs * (4 + C_K) + Cs * CT, κ / 2, by positivity, by positivity, ?_⟩
  intro ε 𝔠 sz z hflow
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow, Step2IterBA_lam_window hflow] with n hn1 hn2
  have hg := baStep2Fam_lam_pos_le hκ hflow n hn2.1
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hm := (EMn2BA_mF_data sz hflow n).1
  have hR1 := TwistStep2_lam0_sq hκ hflow n
  have hL : 3 ≤ sz.L n := sz.three_le_L n
  have hL1 : (1 : ℝ) ≤ (sz.L n : ℝ) := by exact_mod_cast (by omega : 1 ≤ sz.L n)
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
  refine Step2IterBA_newKLKAtN_of (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n hκ hKc0 hCK hCT hn2.1 hm
    (fun u hu0 hu1 x y => HT (sz.L n) (sz.lam n) u u hn2.1 hu0 le_rfl hu1 (le_total _ _) x y)
    (hF5 (sz.withLam (BAflowLam0 sz z)) n (BAflowEs sz z n) hn1.1 hn1.2 hm).1
    (hF5 (sz.withLam (BAflowLam0 sz z)) n (BAflowEs sz z n) hn1.1 hn1.2 hm).2.1
    (hF5 (sz.withLam (BAflowLam0 sz z)) n (BAflowEs sz z n) hn1.1 hn1.2 hm).2.2 ?_
    (fun u hu0 hu1 σ => hF8 (sz.withLam (BAflowLam0 sz z)) n (BAflowEs sz z n) u hn1.1 hn1.2 hm hu0 hu1 σ)
    (fun u hu0 hu1 => hF9 (sz.withLam (BAflowLam0 sz z)) n (BAflowEs sz z n) u hn1.1 hn1.2 hm hu0 hu1)
  -- F7 at mixed coupling
  intro u hu0 hu1 s s' ℓ' D' hℓ' hD' a a'
  have hv : 0 < 1 - u := by linarith
  have hIm' : ((((BAflowEs sz z n : ℝ)) : ℂ) + BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im ≠ 0 := by
    have : 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := lt_of_lt_of_le hκ hm
    simpa using this.ne'
  have hker : ∀ x y : Zd d (sz.L n),
      Step2Gen_thetaKer (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).toFlowFM n s s' u x y =
        (BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) u s s' *
          BAMss d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ)
            (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) s s') x y :=
    fun x y => congrFun (congrFun (Step2Kern_thetaKer_BA sz (BAflowLam0 sz z) (BAflowEs sz z) n hIm' s s' u) x) y
  have hTail : ∀ x y : Zd d (sz.L n),
      ‖(BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) u s s' *
          BAMss d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ)
            (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) s s') x y‖ ≤
        (Q₀ * A) * tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) := by
    intro x y
    have h1 := HQ (sz.L n) hL (BAflowLam0 sz z n) hn1.1 hn1.2 (BAflowEs sz z n) _ hr u hu0 hu1 s s' x y
    have h2 := Step2IterBA_tailT_le (d := d) (L := sz.L n) (t := u) (r := ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ))
      hL1 hg.1.le hg.2 hA1 hR1.2 (Nat.cast_nonneg _)
    calc _ ≤ Q₀ * tailT d (sz.L n) (BAflowLam0 sz z n) u ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) := h1
      _ ≤ Q₀ * (A * tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 hQ₀.le
      _ = _ := by ring
  have hconvP := NewKLKBA_conv_P (d := d) (L := sz.L n) (g := sz.lam n) (t := u) (ℓ := ℓ')
    (W := ((sz.W n : ℕ) : ℝ)) (D := D') hWpos hℓ'
    (X := BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) u s s' *
      BAMss d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ)
        (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) s s')
    (Q := Q₀ * A) (CT := CT / (1 - u)) (c := (1 - u)⁻¹) (by positivity) (by positivity) hTail
    (fun x => baComp_row_le hr hu0 hu1 s s' x)
    (fun x y => HT (sz.L n) (sz.lam n) u u hn2.1 hu0 le_rfl hu1 (le_total _ _) x y) a a'
  simp only [hker]
  refine hconvP.trans (mul_le_mul_of_nonneg_right ?_ (tailW_pos hWpos _).le)
  have e : Q₀ * A * (CT / (1 - u)) + Cs * (1 - u)⁻¹ = (Q₀ * A * CT + Cs) / (1 - u) := by field_simp
  rw [e]
  refine div_le_div_of_nonneg_right ?_ hv.le
  have : Cs ≤ A * Cs := le_mul_of_one_le_left hCs0.le hA1
  rw [hKc]
  nlinarith

end NewKLK

/-! ## 6. Compiled nonempty instances of targets 1-7 (`d = 3`)

The data are the merged preflight sequence `sz0` (`Defs/Sizes.lean:260`: `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `g_n = (2(n+1))^{-6}`,
`N_n = (W_n L_n)^3`), the spectral parameters `zSeq` and `flow_sz0 : BAFlow sz0 zSeq` at `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`
(`BA/FlowPins.lean:1214`), the times `s ≡ 1/10 < t ≡ 1/2 < t₀` (`half_lt_t0`).  Every deterministic hypothesis is discharged. -/

end RBM.BA
