/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.ExpAvgGen
import RBM3D.Chain.Step6KitGen
import RBM3D.Chain.Step2CloseGen
import RBM3D.BA.TwistPins
import RBM3D.BA.CltFlowBA
import RBM3D.BA.GreenCond2
import RBM3D.BA.GreenSchur
import RBM3D.BA.SEforLnBA
import RBM3D.BA.DecayLoopBA
import RBM3D.Graph.BALWOut

/-!
# Step 6 of `lem:main_ind` at the block Anderson tuple: the bridges (BA-V row V1-BA, ticket T2510 row a, file 1)

The three W1 bridges of `lem:improve_exp_aver` at the BA tuple `(fun sz => Sizes.seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`, the per-flow
reading of `(res_ELK_n=1)` (row 21), and two private glue results for file 2 (`BA/Step6PinsBA`).  No new mathematics; paper `6:12-21`.

* **Target 1** `baExpAvgGen_W1iii_of_tl1` (W1 (iii) from TL1: `t_{aq} - M^{(++)}_{aq} = M^{(B)}_{aq} twTr(q, a)`, `TwistPins_circ_term`).
* **Target 2** `baExpAvgGen_W1iv` (the public form of `CltFlowBA_MB_decay`, summed by `GreenCond2_sum_exp_le`).
* **Target 3** `baExpAvgGen_W1fam` (port of the probe `T2502c_ba_W1fam`, `t/T2502c` `Probe/T2502Pins.lean:227-262`, with target 2), `baImproveCoregL`.
* **Target 4** `baExpAvgUgL_of_tl1` (row 21, per flow, TL1 on `[s,t]`): the private twins `Step6BridgeBA_LWAvg_ev`, `Step6BridgeBA_expAvgU_of_core`
  of `LWAvgLawgL_of_STAvgUgL_at`, `stExpAvgUgL_of_core` read the carrier datum `𝒦^{(1)}_{+,a} = m` eventually in `n` (`baKsol_oneLoop`, F1).
* **Target 5** private glue `Step6BridgeBA_LW` (LW at each `u`, `baLWtermEXPTw_holds`) and `Step6BridgeBA_decay` (row 18 at the `FlowFM` labels).
Names of the file stem `Step6BridgeBA_`; no merged file is edited.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open private TwistPins_circ_term TwistPins_shift_of_mem TwistPins_split_shift TwistPins_mem_blk from RBM3D.BA.TwistPins
open private CltFlowBA_MB_decay from RBM3D.BA.CltFlowBA

open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Target 1: W1 (iii) from TL1 -/

section Iii

/-- The identity `t_{aq} - M^{(++)}_{aq} = M^{(B)}_{aq} Tr(Ǧ P_{aq})`, `Ǧ = G - M`, at the BA carrier: `M = M^{(B)} ⊗ I` (`BAMfine_eq`), `twLoopX n G M a q q`
through `TwistPins_circ_term`, `Tr(M P) = M^{(B)}_{qa}` and `M^{(++)}_{aq} = M^{(B)}_{qa} M^{(B)}_{aq}` (`Step2Kern_Mss_BA`). -/
private theorem Step6BridgeBA_iii_ident {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ)
    (hm : 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im) (a q : Zd d (sz.L n)) :
    ExpAvgGen_tM (baFMz sz z) n u ω a q - Step2Kern_Mss (baFMz sz z) n true true a q =
      ExpAvgGen_MB (baFMz sz z) n a q * twTr (baFMz sz z) n u ω q a := by
  have hW : ((sz.W n : ℕ) : ℂ) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (sz.W_pos n).ne')
  set MB : Zd d (sz.L n) → Zd d (sz.L n) → ℂ := fun a b => BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ)
    (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) a b with hMB
  have hM : ∀ w γ : Idx d (sz.L n) (sz.W n), (baFMz sz z).M n w γ =
      if (split d (sz.L n) (sz.W n) w).2 = (split d (sz.L n) (sz.W n) γ).2 then
        MB (split d (sz.L n) (sz.W n) w).1 (split d (sz.L n) (sz.W n) γ).1 else 0 :=
    fun w γ => BAMfine_eq sz _ _ n hm w γ
  have hA : ExpAvgGen_tM (baFMz sz z) n u ω a q =
      ((sz.W n : ℕ) : ℂ) ^ d * twLoopX n ((baFMz sz z).G n u ω) ((baFMz sz z).M n) a q q := by
    unfold ExpAvgGen_tM twLoopX
    have : ∀ x ∈ twBlk n a, ∑ w ∈ twBlk n q, (baFMz sz z).M n x w * (baFMz sz z).G n u ω (twShift n q w) x =
        ∑ y ∈ Iblk d (sz.L n) (sz.W n) q, (baFMz sz z).M n x y * (baFMz sz z).G n u ω y x := fun x _ =>
      Finset.sum_congr rfl fun w hw => by rw [TwistPins_shift_of_mem n hw]
    rw [Finset.sum_congr rfl this]
    have e : twBlk n a = Iblk d (sz.L n) (sz.W n) a := rfl
    rw [e]
    field_simp
  have hB := TwistPins_circ_term n ((baFMz sz z).G n u ω) ((baFMz sz z).M n) MB hM a q q
  have hC : twTrP n ((baFMz sz z).G n u ω) a q = twTr (baFMz sz z) n u ω q a + MB q a := by
    rw [twTr_eq]
    unfold twTrP
    have : ∀ w ∈ twBlk n q, (baFMz sz z).G n u ω w (twShift n a w) =
        (baFMz sz z).GM n u ω w (twShift n a w) + MB q a := by
      intro w hw
      have h1 := (TwistPins_mem_blk n).1 hw
      have h2 := TwistPins_split_shift n a w
      have h3 : (baFMz sz z).M n w (twShift n a w) = MB q a := by
        rw [hM, h2, h1]; simp
      unfold FlowFM.GM
      rw [h3]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((twBlk n q).card : ℂ) = ((sz.W n : ℕ) : ℂ) ^ d := by
      have := card_Iblk d (sz.L n) (sz.W n) q
      exact_mod_cast this
    rw [hcard]
    field_simp
  have hIm : (((BAflowEs sz z n : ℝ) : ℂ) + BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im ≠ 0 := by
    simpa using hm.ne'
  have hD : Step2Kern_Mss (baFMz sz z) n true true a q = MB q a * MB a q := by
    have := Step2Kern_Mss_BA sz (BAflowLam0 sz z) (BAflowEs sz z) n hIm true true
    rw [show baFMz sz z = baFM sz (BAflowLam0 sz z) (BAflowEs sz z) from rfl, this]
    simp [BAMss, BAMsigma, hMB]
  have hE : ExpAvgGen_MB (baFMz sz z) n a q = MB a q :=
    congrFun (congrFun (twMB_ba z n hm) a) q
  rw [hA, hB, hC, hD, hE]
  field_simp
  ring

/-- **Target 1, `baExpAvgGen_W1iii_of_tl1`** (= `T2510_W1iiiOfTL1`; bridge (iii), V1-BA): TL1 `BATwistAvgLaw` at the time sequence `u` gives W1 (iii) at `u`,
along every BA flow: `‖t_{aq} - M^{(++)}_{aq}‖ = ‖M^{(B)}_{aq}‖ ‖twTr(q, a)‖ ≺ ‖M^{(B)}_{aq}‖ W^{-d}B_{u,0}` (the transposed pair `(q, a)`: TL1 is over all
ordered pairs). -/
theorem baExpAvgGen_W1iii_of_tl1 (d : ℕ) :
    ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → ∀ u : ℕ → ℝ,
      BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u →
        ExpAvgGen_W1iii (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u := by
  intro sz κ ε 𝔠 𝔡 z hκ hflow u h
  have hsize : Tendsto sz.size atTop atTop := tendsto_size sz hflow.1.2.2.1
  have hm : ∀ n, 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := fun n =>
    lt_of_lt_of_le hκ (EMn2BA_mF_data sz hflow n).1
  have hsw := StochDomAt.precomp_param h (fun n (p : Zd d (sz.L n) × Zd d (sz.L n)) => (p.2, p.1))
  have hMB : StochDomAt (Sizes.seqP (sz.withLam 0)) sz.size (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p _ => ‖ExpAvgGen_MB (baFMz sz z) n p.1 p.2‖) (fun n p _ => ‖ExpAvgGen_MB (baFMz sz z) n p.1 p.2‖) :=
    StochDomAt.refl hsize (fun _ _ _ => norm_nonneg _)
  have hmul := StochDomAt.mul hsize (fun _ _ _ => norm_nonneg _) (fun _ _ _ => norm_nonneg _) hMB hsw
  refine StochDomAt.of_le_left (fun n p ω => le_of_eq ?_) hmul
  change ‖ExpAvgGen_tM (baFMz sz z) n (u n) ω p.1 p.2 - Step2Kern_Mss (baFMz sz z) n true true p.1 p.2‖ =
    ‖ExpAvgGen_MB (baFMz sz z) n p.1 p.2‖ * ‖twTr (baFMz sz z) n (u n) ω p.2 p.1‖
  rw [Step6BridgeBA_iii_ident sz z n (u n) ω (hm n) p.1 p.2, norm_mul]

end Iii

/-! ## 2. Targets 2, 3: W1 (iv), the family text and the per-time core -/

section Fam

/-- **Target 2, `baExpAvgGen_W1iv`** (= `T2510_W1ivBA`; bridge (iv)): the public form of the private `CltFlowBA_MB_decay`:
`‖M^{(B)}_{ab}‖ ≤ K e^{-c_M |a-b|}` summed over `b` by `GreenCond2_sum_exp_le`, on the window `0 < g₀ ≤ 𝔡⁻¹`; `CM` depends on `(d, κ, 𝔡)` only. -/
theorem baExpAvgGen_W1iv (d : ℕ) :
    3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ CM : ℝ, 0 < CM ∧
      ∀ (ε 𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ExpAvgGen_W1iv (baFMz sz z) CM := by
  intro hd κ 𝔡 hκ h𝔡
  obtain ⟨K, cM, hK, hcM, H⟩ := CltFlowBA_MB_decay hd hκ h𝔡
  have hexp : Real.exp (-cM) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  have hr : 0 < (1 + Real.exp (-cM)) / (1 - Real.exp (-cM)) :=
    div_pos (by positivity) (by linarith)
  refine ⟨K * ((1 + Real.exp (-cM)) / (1 - Real.exp (-cM))) ^ d, by positivity, ?_⟩
  intro ε 𝔠 sz z hflow
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow] with n hwin a
  have hr' := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hm : 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := lt_of_lt_of_le hκ hr'.2
  have : NeZero (sz.L n) := ⟨by have := sz.three_le_L n; omega⟩
  have hpt : ∀ q : Zd d (sz.L n), ‖ExpAvgGen_MB (baFMz sz z) n a q‖ ≤
      K * Real.exp (-cM * (zdistD d (sz.L n) (a - q) : ℝ)) := fun q => by
    have e : ExpAvgGen_MB (baFMz sz z) n a q =
        BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) a q :=
      congrFun (congrFun (twMB_ba z n hm) a) q
    rw [e]
    exact H (sz.L n) (sz.three_le_L n) (BAflowLam0 sz z n) hwin.1 hwin.2 (BAflowEs sz z n) _ hr' a q
  calc ∑ q, ‖ExpAvgGen_MB (baFMz sz z) n a q‖ ≤ ∑ q : Zd d (sz.L n), K * Real.exp (-cM * (zdistD d (sz.L n) (a - q) : ℝ)) :=
        Finset.sum_le_sum fun q _ => hpt q
    _ = K * ∑ q : Zd d (sz.L n), Real.exp (-cM * (zdistD d (sz.L n) (a - q) : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ K * ((1 + Real.exp (-cM)) / (1 - Real.exp (-cM))) ^ d :=
        mul_le_mul_of_nonneg_left (GreenCond2_sum_exp_le d (sz.L n) hcM a) hK0.le

/-- W1 (i)′ at the BA tuple (port of `T2502c_ba_W1i`, `t/T2502c` `Probe/T2502Pins.lean:227`): `S = SB d L 0`, `(H₀ - E - m) M = 1`, the block average of `M` is `m`. -/
private theorem Step6BridgeBA_W1i {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
    ExpAvgGen_W1i (baFMz sz z) (fun n => ((BAflowLam0 sz z n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (fun _ => 0)
      (BAflowEs sz z) n := by
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z h n
  have hmpos : 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := lt_of_lt_of_le hκ hr.2
  have hIm : ((BAflowEs sz z n : ℂ) + BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im ≠ 0 := by
    simpa using hmpos.ne'
  have hW : ((sz.W n : ℕ) : ℂ) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne _))
  refine ⟨(EMn2BA_SB_zero (sz.L n)).symm, ?_, fun a => ?_⟩
  · exact Ring.mul_inverse_cancel _ (RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero ((baCltRepg_holds sz z).2.1 n) hIm)
  · have hdiag := BAMB_diag_eq d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) _ hr.1 a
    have hx : ∀ x ∈ Iblk d (sz.L n) (sz.W n) a, (baFMz sz z).M n x x = (baFMz sz z).m n := fun x hx => by
      have hx1 : (split d (sz.L n) (sz.W n) x).1 = a := (Finset.mem_filter.1 hx).2
      change BAMfine sz (BAflowLam0 sz z) (BAflowEs sz z) n x x = BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n
      rw [BAMfine_eq sz _ _ n hmpos x x]
      simp [hx1, hdiag]
    rw [Finset.sum_congr rfl hx, Finset.sum_const, card_Iblk, nsmul_eq_mul]
    push_cast
    field_simp

/-- **Target 3, `baExpAvgGen_W1fam`** (= `T2510_W1famBA`; rows 9 + 14 with (iv)): the family text of `ExpAvgGen_W1fam` at the BA tuple, `H₀ = g₀ Ψ`, `g' = 0`,
`E = BAflowEs z` (`baCltRepg_holds`); `Cs` is `baEKSameRow_holds d 𝔡⁻¹ κ`, `uKer` through `Step2Kern_uKer_BA`, `CM` is target 2.  Port of the probe
`T2502c_ba_W1fam` (`t/T2502c` 0f0ad532 `Probe/T2502Pins.lean:249-262`) to the merged text, which adds `CM`. -/
theorem baExpAvgGen_W1fam (d : ℕ) :
    ExpAvgGen_W1fam d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨C, hC, H⟩ := baEKSameRow_holds d 𝔡⁻¹ κ hd (inv_pos.2 h𝔡) hκ
  obtain ⟨CM, hCM, HM⟩ := baExpAvgGen_W1iv d hd κ 𝔡 hκ h𝔡
  refine ⟨C, CM, hC, hCM, fun 𝔠 sz z h => ⟨_, fun _ => 0, BAflowEs sz z, baCltRepg_holds sz z,
    fun n => Step6BridgeBA_W1i hκ h n, ?_, HM ε 𝔠 sz z h⟩⟩
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z h] with n hn σ s t hs hst ht a
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z h n
  have hIm : ((BAflowEs sz z n : ℂ) + BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im ≠ 0 := by
    simpa using (lt_of_lt_of_le hκ hr.2).ne'
  change ∑ b, ‖Step2Gen_uKer (baFM sz (BAflowLam0 sz z) (BAflowEs sz z)) n σ σ s t a b‖ ≤ C
  rw [Step2Kern_uKer_BA sz _ _ n hIm σ σ s t]
  exact (RBM.sum_norm_row_le _ a).trans (H (sz.L n) (sz.three_le_L n) _ hn.1 hn.2 _ _ hr σ s t hs hst ht)

/-- **Target 3, `baImproveCoregL`** (= `T2510_CoreBA`): `lem:improve_exp_aver` per time at the BA tuple, `stImproveCoregL_of` with row 3 and the family text. -/
theorem baImproveCoregL (d : ℕ) :
    STImproveCoregL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) :=
  stImproveCoregL_of (baStep5CasesGen_flowFacts d) (baExpAvgGen_W1fam d)

end Fam

/-! ## 3. Target 4 (row 21): the eventual carrier datum `𝒦^{(1)} = m` (F1) -/

section Avg

/-- `𝒦^{(1)}_{+,a} = m` at the times `[0,1)`, eventually in `n`, along every BA flow (`baKsol_oneLoop`; the every-`n` form has no BA discharge, F1). -/
private theorem Step6BridgeBA_K1 {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) :
    ∀ᶠ n in atTop, ∀ (τ : ℝ) (a : Zd d (sz.L n)), 0 ≤ τ → τ < 1 →
      (baFMz sz z).K n τ (fun _ : Fin 1 => true) (fun _ => a) = (baFMz sz z).m n := by
  filter_upwards [baKsol_oneLoop d sz κ ε 𝔠 𝔡 z hκ hflow] with n hn τ a h0 h1
  simpa using hn τ h0 h1 true a

/-- Private twin of `LWAvgLawgL_of_STAvgUgL_at` (`Step6KitGen:139`) with the eventual `hK1` (shape `T2510_LWAvgEv`): the bound for the sections `u ∈ [s,t]`
transfers `‖𝓛^{(1)} - 𝒦^{(1)}‖ ≺ B` to `‖𝓛^{(1)} - m‖ ≺ B` because the two agree for all large `n`, and `≺` only sees the failure events eventually. -/
private theorem Step6BridgeBA_LWAvg_ev {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) {s t u : ℕ → ℝ}
    (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n)
    (hK1 : ∀ᶠ n in atTop, ∀ (τ : ℝ) (a : Zd d (sz.L n)), 0 ≤ τ → τ < 1 →
      C.K n τ (fun _ : Fin 1 => true) (fun _ => a) = C.m n)
    (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) (h : STAvgUgL C μ s t) : LWAvgLawgL C μ u := by
  have h1 := StochDomAt.precomp_param h
    (fun n (a : Zd d (sz.L n)) =>
      ((⟨u n, hsu n, hut n⟩ : TimeIcc s t n), ((fun _ : Fin 1 => true), (fun _ : Fin 1 => a))))
  refine StochDomAt.of_subset h1 fun τ hτ => ⟨τ, hτ, ?_⟩
  filter_upwards [hK1] with n hn ω ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have e := hn (u n) a ((hs0 n).trans (hsu n)) ((hut n).trans_lt (ht1 n))
  simpa only [e, pow_one] using ha

/-- Private twin of `stExpAvgUgL_of_core` (`ExpAvgGen:1416`) with the eventual `hK1` (through `Step6BridgeBA_LWAvg_ev`). -/
private theorem Step6BridgeBA_expAvgU_of_core {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ}
    {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop} {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz}
    {T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ} (hCore : STImproveCoregL d law Flow mk T0) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {sz : Sizes d} {z : ℕ → ℂ} (hflow : Flow sz κ ε 𝔠 𝔡 z)
    (hμ : IsProbabilityMeasure (law sz)) (hsz : sz.SizeTendsto)
    (hK1 : ∀ᶠ n in atTop, ∀ (τ : ℝ) (a : Zd d (sz.L n)), 0 ≤ τ → τ < 1 →
      (mk sz z).K n τ (fun _ : Fin 1 => true) (fun _ => a) = (mk sz z).m n)
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ T0 sz z n) (ht1 : ∀ n, t n < 1)
    (hS2 : STStep2CoregL (mk sz z) (law sz) s t) (hLKU : STLKUgL (mk sz z) (law sz) s t)
    (hiii : ∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) → ExpAvgGen_W1iii (mk sz z) (law sz) u) :
    STExpAvgUgL (mk sz z) (law sz) s t := by
  refine st6_precU_of_forall_seqg sz (law sz) hμ hsz (fun n => (hst n).le) (W := fun n => Bool × Zd d (sz.L n))
    (fun n u w => ‖(∫ ω, (mk sz z).L n u (fun _ : Fin 1 => w.1) (fun _ => w.2) ω ∂(law sz)) -
      (if w.1 then (mk sz z).m n else (starRingEnd ℂ) ((mk sz z).m n))‖) (fun n u _ => (sz.Bctl n u) ^ 2) ?_
  intro u hsu hut
  exact hCore hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u (fun n => (hs0 n).trans (hsu n)) (fun n => (hut n).trans (htT n))
    (Step6BridgeBA_LWAvg_ev (mk sz z) (law sz) hsu hut hK1 hs0 ht1 hS2.2) (STLKgL_of_STLKUgL_at (mk sz z) hsu hut hLKU) (hiii u hsu hut)

/-- **Target 4, `baExpAvgUgL_of_tl1`** (= `T2510_ExpAvgUBA`; row 21, V1L-C1): `(res_ELK_n=1)` uniformly in `u ∈ [s,t]`, per BA flow, from the per-time core
`baImproveCoregL`, W1 (iii) at every `u ∈ [s,t]` (target 1, from TL1 on `[s,t]`) and the Step 2 / Step 4 inputs on `[s,t]`.  The carrier datum `𝒦^{(1)} = m` enters
eventually (`baKsol_oneLoop`, F1); no `STImproveExpAvergL`, no global every-`n` `hK1`. -/
theorem baExpAvgUgL_of_tl1 (d : ℕ) :
    3 ≤ d → ∀ κ ε 𝔠 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        STStep2CoregL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t → STLKUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t →
        (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) → BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u) →
          STExpAvgUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t := by
  intro hd κ ε 𝔠 𝔡 hκ hε h𝔡 sz z hflow s t hs0 hst htT hS2 hLKU hTL1
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  exact Step6BridgeBA_expAvgU_of_core (baImproveCoregL d) hd hκ hε h𝔡 hflow (Sizes.isProbabilityMeasure_seqP (sz.withLam 0))
    hflow.1.2.2.1 (Step6BridgeBA_K1 hκ hflow) hs0 hst htT ht1 hS2 hLKU
    (fun u hsu hut => baExpAvgGen_W1iii_of_tl1 d sz κ ε 𝔠 𝔡 z hκ hflow u (hTL1 u hsu hut))

end Avg

/-! ## 4. Target 5: private glue for file 2 -/

section Glue

/-- **Row 7 at each `u ∈ [s,t]`** (LW, `Step6KitGen:701-706`): the seven-premise `baLWtermEXPTw_holds` (TL1, TL2 at `u` from the `Concl` slot of `BAStep6R`; the five Step 1/2
inputs at `u` by `Step6KitGen:121-151`), the conclusion of `st6_EGtHi_of_LWg`'s hypothesis.  `LWAvgLawgL` at `u` is the eventual twin. -/
private theorem Step6BridgeBA_LW (d : ℕ) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {sz : Sizes d} {z : ℕ → ℂ}
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (htT : ∀ n, t n ≤ BAflowT0 sz z n)
    (hS2 : STStep2CoregL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t)
    (hLmax : STLmaxUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t) (hLKU : STLKUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t)
    (hS5 : STGdecayWgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t 0)
    (hTL : ∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
      BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u ∧ BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u) :
    ∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
      PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
          sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - u n})
        (fun n p _ => ‖∫ ω, LWEg (baFMz sz z) n (u n) p.1.1 p.1.2 ω ∂(Sizes.seqP (sz.withLam 0))‖)
        (fun n _ _ => (1 - u n)⁻¹ * (sz.Bctl n (u n)) ^ (5 / 2 : ℝ)) := by
  intro u hsu hut
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  exact baLWtermEXPTw_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u (fun n => (hs0 n).trans (hsu n)) (fun n => (hut n).trans (htT n))
    (STLocalEntrygL_of_STLocalEntryUgL_at _ hsu hut hS2.1)
    (Step6BridgeBA_LWAvg_ev _ _ hsu hut (Step6BridgeBA_K1 hκ hflow) hs0 ht1 hS2.2)
    (STLmaxgL_of_STLmaxUgL_at _ hsu hut hLmax) (STLKgL_of_STLKUgL_at _ hsu hut hLKU)
    (STDecaygL_of_STGdecayWgL_at _ hsu hut hS5) (hTL u hsu hut).1 (hTL u hsu hut).2

/-- **Row 18 at the `FlowFM` labels** (T2506 open issue 2): the `hDec` premise of `stExpDriftDecaygL_of` at the BA tuple.  `STDecayLoopUgL` is `baDecayLoopU_of`; the E-term decays at
`STELKLKg (baFMz sz z)`, `STEGtg (baFMz sz z)` are `baEtermDecaygL` (labels `STelklkg`, `STegtg` of `baStep2Mat`, `k = 2`) through `STELKLKMg_eq_STelklkMg`,
`STEGtMg_eq_STegtMg` (with `baStep2Mat_listLink`) and `Step2EventsGen_STEGtMg_eq`. -/
private theorem Step6BridgeBA_decay (d : ℕ) :
    3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      (∀ Cd : ℝ, STGdecayWgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd →
        STDecayLoopUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t) ∧
      (STDecayLoopUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t → ∀ σ : Fin 2 → Bool,
        STEKDecaygL (sz := sz) (Sizes.seqP (sz.withLam 0)) s t
          (fun n v ω (a : Fin 2 → Zd d (sz.L n)) => STELKLKg (baFMz sz z) n (v : ℝ) σ a ω) ∧
        STEKDecaygL (sz := sz) (Sizes.seqP (sz.withLam 0)) s t
          (fun n v ω (a : Fin 2 → Zd d (sz.L n)) => STEGtg (baFMz sz z) n (v : ℝ) σ a ω)) := by
  intro hd sz κ ε 𝔠 𝔡 z hκ hε hflow s t hs0 hst htT
  refine ⟨fun Cd hG => baDecayLoopU_of d hd sz κ ε 𝔠 𝔡 z hκ hflow s t Cd hs0 htT hG, fun hU σ => ?_⟩
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  obtain ⟨h1, -, h3, -⟩ := baEtermDecaygL d hd sz κ ε 𝔠 𝔡 z hκ hflow s t hs0 hst ht1 hU 2 le_rfl σ
  have hL := baStep2Mat_listLink sz (BAflowLam0 sz z) (BAflowEs sz z)
  refine ⟨?_, ?_⟩
  · have e : (fun n (v : TimeIcc s t n) (ω : sz.SeqΩ) (a : Fin 2 → Zd d (sz.L n)) =>
        STELKLKg (baFMz sz z) n (v : ℝ) σ a ω) =
        fun n (v : TimeIcc s t n) (ω : sz.SeqΩ) (a : Fin 2 → Zd d (sz.L n)) =>
          STelklkg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (sz.seqHflowBA (BAflowLam0 sz z)) n (v : ℝ) ω
            ⟨List.ofFn σ, List.ofFn a⟩ := by
      funext n v ω a
      exact STELKLKMg_eq_STelklkMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) hL n (v : ℝ) _ σ a
    exact e ▸ h3
  · have e : (fun n (v : TimeIcc s t n) (ω : sz.SeqΩ) (a : Fin 2 → Zd d (sz.L n)) =>
        STEGtg (baFMz sz z) n (v : ℝ) σ a ω) =
        fun n (v : TimeIcc s t n) (ω : sz.SeqΩ) (a : Fin 2 → Zd d (sz.L n)) =>
          STegtg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (sz.seqHflowBA (BAflowLam0 sz z)) n (v : ℝ) ω
            ⟨List.ofFn σ, List.ofFn a⟩ := by
      funext n v ω a
      exact (Step2EventsGen_STEGtMg_eq (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))
        (fun n u k σ a ω => rfl) n (v : ℝ) σ a ω).symm.trans
        (STEGtMg_eq_STegtMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) hL n (v : ℝ) _ σ a)
    exact e ▸ h1

end Glue

/-! ## 5. Compiled nonempty instances (targets 1-4)

`d = 3`, the preflight sequence `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`), the spectral parameters `zSeq`, `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq`
(`BA/FlowPins.lean:1214`), `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, times `u ≡ 1/2` (`half_lt_t0`) and `1/2 < 3/5 ≤ 2/3 ≤ T₀` (`t0_sz0`).  Every deterministic premise is discharged
(`3 ≤ 3`, the positivity of `κ, ε, 𝔡`, the flow, `0 ≤ s < t ≤ T₀`).  What stays a hypothesis is another gate's pin: `LWAvgLawgL`, `STLmaxgL`, `STLKgL` at `u` (Steps 1/2, from which TL1 is
`baTwistAvgProd_holds`), `STStep2CoregL`, `STLKUgL` on `[s,t]`, and TL1 on `[s,t]`. -/

end RBM.BA

end
