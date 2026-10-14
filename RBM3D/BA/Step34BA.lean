/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step34RGen
import RBM3D.Chain.QtXiRoundLiftGen
import RBM3D.Chain.QtNonzeroBootGen
import RBM3D.Chain.Step2Kern
import RBM3D.BA.EKGenBA
import RBM3D.BA.KLipBA
import RBM3D.BA.SEforLnBA
import RBM3D.BA.ZeroModeBA
import RBM3D.BA.GridDriftBA
import RBM3D.BA.GridRepTailBA
import RBM3D.BA.Step5KerBA
import RBM3D.BA.B45BA
import RBM3D.BA.KDecayBA
import RBM3D.BA.NetLiftBA
import RBM3D.BA.TwistStep2
import RBM3D.BA.KBound

/-!
# Steps 3-4 of `lem:main_ind` at the block Anderson tuple (U3-BA (b), file 2; ticket T2509)

Paper: arXiv:2507.20274, Steps 3-4 `1_2:1359-1374` read at the block Anderson model (`7_8:2099-2100`: Steps 3-6 extend verbatim; `lem:main_ind_BA`
`7_8:1825`).  Composition of merged results, no new mathematics and no new public `def`; no merged file is edited.  The check is
`docs/tickets/checks/T2509-check.lean` (pins `T2509_*`).

BA tuple `(law, Flow, mkM, Hf, Es, T0)`: law `seqP (sz.withLam 0)`, flow `BAFlow`, `mkM = baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)`,
`Hf = seqHflowBA (BAflowLam0 sz z)`, `Es = BAflowEs`, `T0 = BAflowT0`, `mk = baFMz`; kernel coupling `gK = BAflowLam0`, `Aof κ = (κ+1)/κ`; the comparison R1 enters only as the slots `hR1` of the two bootstraps
(`TwistStep2_lam0_sq`, with `0 ≤ g₀ λ`).

* **Target 6** `baQtNZGen_kerNZ` (= T2507 target 7): `QtNZGen_KerNZFam` at BA, `C5` from `baEKSumDecayNonzeroA_holds` at `A = (κ+1)/κ`.
* **Target 7** `baOeqQtgL'_holds`, `baOeqQtNZgL'_holds`: `stOeqQtgL'_of`, `stOeqQtNZgL'_of` at the BA tuple, every slot a merged BA discharge.
* **Target 8** `baStep3RegIII_holds`, `baStep3RegI_holds`, `baStep3II_holds`: `STStep3RgL` at the BA tuple at the three regimes.
* **Target 9** `baStep4I_holds`, `baStep4II_holds`, `baStep4RegIII_holds`, `baStep4RegI_holds`: `STStep4RgL` at the BA tuple.
* **Target 10** compiled nonempty instances at `d = 3` (`RBM.BA.Step34BAInst`).

The generic Steps 3-4 producers are `Chain/Step34RGen`.  There is no statement at `STAny` (general Steps 3/4 are cancelled, DECISIONS §68 (9), §132 (3)).
`BAStep3R`, `BAStep4R` are not introduced (DECISIONS §331 (4)).  Private helpers carry the stem `Step34BA_`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open private EKGenBA_hIm from RBM3D.BA.EKGenBA

open private szI zI flowI szI_window szI_regIterI szII_caseII from RBM3D.BA.ZeroModeBA

open MeasureTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Target 6: `lem:sum_decay_nonzero` (T2505 D1) at BA -/

/-- **Target 6, `baQtNZGen_kerNZ`** (= `T2509_KerNZBA` = T2507 target 7 at the merged `QtNZGen_KerNZFam`): the family form of D1 at the BA tuple,
`Aof κ = (κ+1)/κ`, `gK = g₀`.  `C5` is the constant of `baEKSumDecayNonzeroA_holds d k 𝔡⁻¹ κ` at `A = (κ+1)/κ`, so it depends on `(d, k, 𝔡, κ)` only (before
`(sz, z)`); at a flow the window `0 < g₀ ≤ 𝔡⁻¹` holds eventually (`BAflow_lam0_window`), the kernel is stage E's `BAUN` (`Step2Kern_UN_BA`). -/
theorem baQtNZGen_kerNZ (d : ℕ) :
    QtNZGen_KerNZFam d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowLam0 sz z)
      (fun κ => (κ + 1) / κ) := by
  intro hd k hk κ 𝔡 hκ h𝔡
  obtain ⟨C, hC, hpin⟩ := baEKSumDecayNonzeroA_holds d k 𝔡⁻¹ κ hd hk (inv_pos.2 h𝔡) hκ ((κ + 1) / κ) (by positivity)
  refine ⟨C, hC, fun sz ε 𝔠 z hflow => ?_⟩
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow] with n hn
  intro v w hv0 hvthr hvw hw1 σ Aset hA X
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  change ‖zeroModeSet d (sz.L n) Aset (Step2Gen_UN (baFM sz (BAflowLam0 sz z) (BAflowEs sz z)) n σ v w X)‖ ≤ C * ‖X‖
  rw [Step2Kern_UN_BA sz _ _ n (EKGenBA_hIm hκ hr)]
  exact hpin (sz.L n) (sz.three_le_L n) (BAflowLam0 sz z n) hn.1 hn.2 v w hv0 hvthr hvw hw1 (BAflowEs sz z n) _ hr σ Aset hA X

/-! ## 2. Target 7: the two bootstraps at BA -/

/-- The spectral data of the carrier (`DecayGen_Spec` with `κm` from `baStep5CasesGen_flowFacts`). -/
private theorem Step34BA_hSpec (d : ℕ) :
    ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
      ∃ κm, DecayGen_Spec (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).toFlowFM κm := by
  intro sz κ ε 𝔠 𝔡 z hκ hflow
  obtain ⟨κm, hκm, hF⟩ := baStep5CasesGen_flowFacts d κ hκ
  obtain ⟨-, -, hmκ, hη⟩ := hF sz ε 𝔠 𝔡 z hflow
  exact ⟨κm, hκm, hmκ, hη⟩

/-- `‖m‖ ≤ 1` along a BA flow (`BAm_norm_le_one`, `BAflow_real`; the pattern of `baIterationsGen2_fam`). -/
private theorem Step34BA_hm (d : ℕ) :
    ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ n, ‖(baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).m n‖ ≤ 1 := by
  intro sz κ ε 𝔠 𝔡 z hκ hflow n
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  exact BAm_norm_le_one d (sz.L n) _ _ _ (by simp) hr.1

/-- **R1, the comparison of the kernel coupling `g₀` with the size-level `λ`** (UBA-C1, §273 (1)): `1 ≤ (κ+1)/κ`, `0 ≤ g₀ λ`, `g₀² ≤ λ²`, `λ² ≤ ((κ+1)/κ) g₀²`
(`TwistStep2_lam0_sq`; `g₀ = √t₀ λ`). -/
private theorem Step34BA_hR1 (d : ℕ) :
    ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
      1 ≤ (κ + 1) / κ ∧ ∀ n, 0 ≤ BAflowLam0 sz z n * sz.lam n ∧ BAflowLam0 sz z n ^ 2 ≤ sz.lam n ^ 2 ∧
        sz.lam n ^ 2 ≤ (κ + 1) / κ * BAflowLam0 sz z n ^ 2 := by
  intro sz κ ε 𝔠 𝔡 z hκ hflow
  refine ⟨(one_le_div hκ).2 (by linarith), fun n => ?_⟩
  have h := TwistStep2_lam0_sq hκ hflow n
  refine ⟨?_, h.1, h.2⟩
  have e : BAflowLam0 sz z n * sz.lam n = Real.sqrt (BAflowT0 sz z n) * (sz.lam n * sz.lam n) := by
    unfold BAflowLam0; ring
  rw [e]
  exact mul_nonneg (Real.sqrt_nonneg _) (mul_self_nonneg _)

/-- The range condition of the horizon: `∃ τ > 0, RangeCond τ T₀` at `τ = ε/2` (`baFlow_premises`, `N^{-1+ε/2} ≤ 1 - t₀`). -/
private theorem Step34BA_hT0 (d : ℕ) :
    ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → BAFlow sz κ ε 𝔠 𝔡 z →
      ∃ τ : ℝ, 0 < τ ∧ sz.RangeCond τ (BAflowT0 sz z) :=
  fun sz κ ε 𝔠 𝔡 z hκ hε hflow =>
    ⟨ε / 2, half_pos hε, (baFlow_premises d κ ε 𝔠 𝔡 hκ hε sz z hflow (BAflowT0 sz z) (fun _ => le_rfl)).2⟩

/-- **Target 7 (a), `baOeqQtgL'_holds`** (= `T2509_OeqQtBA`): `lem:STOeq_Qt`, R2*, at the BA tuple: `stOeqQtgL'_of` with every slot a merged BA discharge
(`baSEforLn_holds`, `Step2EventsGenTw_baFlow`, `Step2EventsGenTw_baLaw`, `DecayGenTw_baWardPair`, `baKcalDecay_holds`, `baEtermDecaygL`, `baStep2Mat_walkForm`,
`baStep2Mat_S`, `baStep2Mat_S_rowSum`, `gridRepTailGen_ker_BA`, `baHierDrift_classes`, `baNQGoodGen_kerNAL`, `baQProxyG_kerEK4`, `baStep5KerGen_thDecay`,
`baB45Gen_facts`, `baKloop_lip`, `baLemDecCalELipG_flowMod`); `lam' = 0`, `Ψ = g₀ Ψ_I`, `gK = g₀`, `Aof κ = (κ+1)/κ`.  For `d < 3` the pin is vacuous. -/
theorem baOeqQtgL'_holds (d : ℕ) :
    STOeqQtgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) := by
  by_cases hd : 3 ≤ d
  · exact stOeqQtgL'_of d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => BAflowT0 sz z)
      (fun sz z => sz.seqHflowBA (BAflowLam0 sz z)) (fun sz z => BAflowEs sz z) (fun _ _ => 0) (fun sz z => BAflowLam0 sz z)
      (fun sz z n => ((BAflowLam0 sz z n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (fun κ => (κ + 1) / κ)
      (baSEforLn_holds d STAny) (Step2EventsGenTw_baFlow d) (Step34BA_hSpec d)
      (fun sz κ ε 𝔠 𝔡 z hκ hflow => baStep2Mat_loopForm d sz κ ε 𝔠 𝔡 z hκ hflow)
      (fun sz κ ε 𝔠 𝔡 z _ _ => baStep2Mat_walkForm sz _ _)
      (fun sz z => Step2EventsGenTw_baLaw sz _ _) (fun sz z => baStep34_LCompat d sz _ _)
      (fun sz z => DecayGenTw_baWardPair sz _ _)
      (fun sz κ ε 𝔠 𝔡 z hκ hflow => baKcalDecay_holds d hd sz κ ε 𝔠 𝔡 z hκ hflow)
      (fun sz κ ε 𝔠 𝔡 z hκ hflow s t hs hst ht1 hU k hk σ => baEtermDecaygL d hd sz κ ε 𝔠 𝔡 z hκ hflow s t hs hst ht1 hU k hk σ)
      (Step34BA_hm d) (fun sz z n => baStep2Mat_S sz _ _ n) (fun sz z n a => baStep2Mat_S_rowSum sz _ _ n a)
      (fun sz κ ε 𝔠 𝔡 z hκ hflow n =>
        gridRepTailGen_ker_BA sz (BAflowLam0 sz z) (BAflowEs sz z) n hκ (BAflow_real κ ε 𝔠 𝔡 sz z hflow n))
      (fun sz z n w k σ a => rfl)
      (fun sz κ ε 𝔠 𝔡 z hκ hflow =>
        Eventually.of_forall fun n s' t' K' => (baHierDrift_classes sz κ ε 𝔠 𝔡 z hκ hflow).1 s' t' K' n)
      (fun sz κ ε 𝔠 𝔡 z hκ hflow => ((baHierDrift_classes sz κ ε 𝔠 𝔡 z hκ hflow).2.2.2).mono fun n h => h.1)
      (fun sz κ ε 𝔠 𝔡 z hκ hflow => ((baHierDrift_classes sz κ ε 𝔠 𝔡 z hκ hflow).2.2.2).mono fun n h => h.2.1)
      (fun sz κ ε 𝔠 𝔡 z hκ hflow => ((baHierDrift_classes sz κ ε 𝔠 𝔡 z hκ hflow).2.2.2).mono fun n h => h.2.2)
      (baNQGoodGen_kerNAL d) (Step34BA_hR1 d) (Step34BA_hT0 d) (baQProxyG_kerEK4 d)
      (fun 𝔡 h𝔡 κ hκ => baStep5KerGen_thDecay d hd κ 𝔡 hκ h𝔡) (baB45Gen_facts d) (baKloop_lip d)
      (fun κ ε 𝔡 hκ hε h𝔡 => baLemDecCalELipG_flowMod d κ ε 𝔡 hκ hε h𝔡)
  · exact fun h => absurd h hd

/-- **Target 7 (b), `baOeqQtNZgL'_holds`** (= `T2509_OeqQtNZBA`): `lem:STOeq_Qt_nonzero`, R2*, at the BA tuple: `stOeqQtNZgL'_of` with the slots of (a) except the
alternating-endpoint and `Θ`-decay classes, plus D1 `baQtNZGen_kerNZ` (target 6) and R1 in the A-form `λ² ≤ ((κ+1)/κ) g₀²`. -/
theorem baOeqQtNZgL'_holds (d : ℕ) :
    STOeqQtNZgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) := by
  by_cases hd : 3 ≤ d
  · exact stOeqQtNZgL'_of d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => BAflowT0 sz z)
      (fun sz z => sz.seqHflowBA (BAflowLam0 sz z)) (fun sz z => BAflowEs sz z) (fun _ _ => 0) (fun sz z => BAflowLam0 sz z)
      (fun sz z n => ((BAflowLam0 sz z n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (fun κ => (κ + 1) / κ)
      (baSEforLn_holds d STAny) (Step2EventsGenTw_baFlow d) (Step34BA_hSpec d)
      (fun sz κ ε 𝔠 𝔡 z hκ hflow => baStep2Mat_loopForm d sz κ ε 𝔠 𝔡 z hκ hflow)
      (fun sz κ ε 𝔠 𝔡 z _ _ => baStep2Mat_walkForm sz _ _)
      (fun sz z => Step2EventsGenTw_baLaw sz _ _) (fun sz z => baStep34_LCompat d sz _ _)
      (fun sz z => DecayGenTw_baWardPair sz _ _)
      (fun sz κ ε 𝔠 𝔡 z hκ hflow => baKcalDecay_holds d hd sz κ ε 𝔠 𝔡 z hκ hflow)
      (fun sz κ ε 𝔠 𝔡 z hκ hflow s t hs hst ht1 hU k hk σ => baEtermDecaygL d hd sz κ ε 𝔠 𝔡 z hκ hflow s t hs hst ht1 hU k hk σ)
      (Step34BA_hm d) (fun sz z n => baStep2Mat_S sz _ _ n) (fun sz z n a => baStep2Mat_S_rowSum sz _ _ n a)
      (fun sz κ ε 𝔠 𝔡 z hκ hflow n =>
        gridRepTailGen_ker_BA sz (BAflowLam0 sz z) (BAflowEs sz z) n hκ (BAflow_real κ ε 𝔠 𝔡 sz z hflow n))
      (fun sz z n w k σ a => rfl)
      (fun sz κ ε 𝔠 𝔡 z hκ hflow =>
        Eventually.of_forall fun n s' t' K' => (baHierDrift_classes sz κ ε 𝔠 𝔡 z hκ hflow).1 s' t' K' n)
      (fun sz κ ε 𝔠 𝔡 z hκ hflow => ((baHierDrift_classes sz κ ε 𝔠 𝔡 z hκ hflow).2.2.2).mono fun n h => h.1)
      (fun sz κ ε 𝔠 𝔡 z hκ hflow => ((baHierDrift_classes sz κ ε 𝔠 𝔡 z hκ hflow).2.2.2).mono fun n h => h.2.1)
      (fun sz κ ε 𝔠 𝔡 z hκ hflow => ((baHierDrift_classes sz κ ε 𝔠 𝔡 z hκ hflow).2.2.2).mono fun n h => h.2.2)
      (baB45Gen_facts d) (baQtNZGen_kerNZ d) (fun sz κ ε 𝔠 𝔡 z hκ hflow n => (TwistStep2_lam0_sq hκ hflow n).2)
      (Step34BA_hT0 d) (baKloop_lip d) (fun κ ε 𝔡 hκ hε h𝔡 => baLemDecCalELipG_flowMod d κ ε 𝔡 hκ hε h𝔡)
  · exact fun h => absurd h hd

/-! ## 3. Targets 8 and 9: Steps 3-4 at the BA tuple, per regime

The statements of `STStep3RgL`, `STStep4RgL` at `(law, Flow, mk, T0)` of the BA tuple; `mk sz z = baFMz sz z` is `(baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).toFlowFM` by
unfolding (as `baSTIterationsgL'_holds`).  The family bundle is `baIterationsGen2_fam` (T2500). -/

/-- **Target 8 (iii), `baStep3RegIII_holds`** (= `T2509_Step3BA d STReg5III`): Step 3 at regime (iii) at the BA tuple, `𝔠d = 1/100`. -/
theorem baStep3RegIII_holds (d : ℕ) :
    STStep3RgL d STReg5III (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
  stStep3RegIIIgL_of d _ _ (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))
    (fun sz z => sz.seqHflowBA (BAflowLam0 sz z)) (fun sz z => BAflowEs sz z) (fun sz z => BAflowT0 sz z)
    (baIterationsGen2_fam d)

/-- **Target 8 (i), `baStep3RegI_holds`** (= `T2509_Step3BA d STReg5I`): Step 3 at regime (i) at the BA tuple, from `baIterationsGen2_fam`, the bootstrap
`baOeqQtgL'_holds` and `baSTIterationsgL'_holds`. -/
theorem baStep3RegI_holds (d : ℕ) :
    STStep3RgL d STReg5I (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
  stStep3RegIgL_of d _ _ (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))
    (fun sz z => sz.seqHflowBA (BAflowLam0 sz z)) (fun sz z => BAflowEs sz z) (fun sz z => BAflowT0 sz z)
    (baIterationsGen2_fam d) (baOeqQtgL'_holds d) (baSTIterationsgL'_holds d)

/-- **Target 8 (ii), `baStep3II_holds`** (= `T2509_Step3BA d STCaseII`): Step 3 at case (ii) at the BA tuple, from `baIterationsGen2_fam`, the bootstrap
`baOeqQtNZgL'_holds` and `baSTIterationsIIgL'_holds`. -/
theorem baStep3II_holds (d : ℕ) :
    STStep3RgL d STCaseII (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
  stStep3IIgL_of d _ _ (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))
    (fun sz z => sz.seqHflowBA (BAflowLam0 sz z)) (fun sz z => BAflowEs sz z) (fun sz z => BAflowT0 sz z)
    (baIterationsGen2_fam d) (baOeqQtNZgL'_holds d) (baSTIterationsIIgL'_holds d)

/-- **Target 9 (i), `baStep4I_holds`** (= `T2509_Step4BA d STCaseI`): Step 4 at case (i) at the BA tuple, from `baIterationsGen2_fam` and the bootstrap
`baOeqQtgL'_holds` (`STIngRgL d STCaseI .. STXiBootgL'`). -/
theorem baStep4I_holds (d : ℕ) :
    STStep4RgL d STCaseI (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
  stStep4RgL_of_ing d STCaseI _ _ (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))
    (fun sz z => sz.seqHflowBA (BAflowLam0 sz z)) (fun sz z => BAflowEs sz z) (fun sz z => BAflowT0 sz z)
    (baIterationsGen2_fam d) (baOeqQtgL'_holds d)

/-- **Target 9 (ii), `baStep4II_holds`** (= `T2509_Step4BA d STCaseII`): Step 4 at case (ii) at the BA tuple, from `baOeqQtNZgL'_holds`. -/
theorem baStep4II_holds (d : ℕ) :
    STStep4RgL d STCaseII (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
  stStep4RgL_of_ing d STCaseII _ _ (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))
    (fun sz z => sz.seqHflowBA (BAflowLam0 sz z)) (fun sz z => BAflowEs sz z) (fun sz z => BAflowT0 sz z)
    (baIterationsGen2_fam d) (baOeqQtNZgL'_holds d)

/-- **Target 9 (iii), `baStep4RegIII_holds`** (= `T2509_Step4BA d STReg5III`): Step 4 at regime (iii), `baStep4I_holds` by `stStep34RgL_mono` along
`STReg5III ⊆ STCaseI` (`st_caseI_of_reg5III`). -/
theorem baStep4RegIII_holds (d : ℕ) :
    STStep4RgL d STReg5III (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
  (stStep34RgL_mono d STCaseI STReg5III _ _ _ _ (fun sz s t h => st_caseI_of_reg5III d sz s t h)).2 (baStep4I_holds d)

/-- **Target 9 (i), `baStep4RegI_holds`** (= `T2509_Step4BA d STReg5I`): Step 4 at regime (i), `baStep4I_holds` along `STReg5I ⊆ STCaseI` (`st_caseI_of_reg5I`). -/
theorem baStep4RegI_holds (d : ℕ) :
    STStep4RgL d STReg5I (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
  (stStep34RgL_mono d STCaseI STReg5I _ _ _ _ (fun sz s t h => st_caseI_of_reg5I d sz s t h)).2 (baStep4I_holds d)

end RBM.BA

/-! ## 4. Target 10: compiled nonempty instances at `d = 3`

Namespace `RBM.BA.Step34BAInst`.  Three merged data (`d = 3`), `(κ, ε, 𝔡)` and `𝔠` as listed, `C_d` arbitrary positive:

* **A** (regime (iii), `STCaseI`): `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`), `zSeq`, `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq`,
  `t0_sz0 : 2/3 ≤ T₀`, `s ≡ 1/2 < t ≡ 2/3` (`lam² ≤ 1/4096 ≤ 1/3 = 1 - t`); `(κ, ε, 𝔡) = (1/2, 1/10, 1/10)`, `Aof κ = 3`.
* **B** (regime (i), `STReg5I`; `sz0` has no window, `TwistStep2_no_caseII_sz0`-type: `1 - s₀ ≤ lam₀² = 1/4096` against `t₀ ≤ 25/36`): the private datum `szI` of `BA/ZeroModeBA`
  (`L ≡ 4`, `W = n + 25`, `lam ≡ 2`; read by `open private`, not copied), `flowI` at `(3/1000, 1/2, 1/9, 1/10)`, `T₀ ≥ 1/400`, `s ≡ 0 < t ≡ 1/400`.
* **C** (case (ii), `STCaseII`): `TwistStep2_szII` (`L ≡ 4`, `W = n + 25`, `lam ≡ 5`), `TwistStep2_flowII` at `(3/5000, 1/2, 1/9, 1/10)`, `T₀ ≥ 1/2000`, `s ≡ 0 < t ≡ 1/2000`.

`STKboundgL`, `STKwardgL` are discharged (`baKbound_holds`, `baKward_holds`), `(con_st_ind)` for every produced `𝔠d > 0` (`conStInd_const`, `W_n → ∞` from `Admissible`), the
regime and the window; what stays a hypothesis is another gate's pin (`STLKgL`, `STStep1LoopgL`, `STStep2ConclgL`, `STLmaxUgL` of Step 3). -/

namespace RBM.BA.Step34BAInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.BA.FlowPinsInst RBM.Gauss.Step34Inst Filter

/-- `STKboundgL`, `STKwardgL` at a BA flow (`baKbound_holds`, `baKward_holds`). -/
private theorem Step34BAInst_K {sz : Sizes 3} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) :
    STKboundgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) ∧ STKwardgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) :=
  ⟨baKbound_holds 3 (by norm_num) κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow, baKward_holds 3 (by norm_num) κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow⟩

/-- `(con_st_ind)` at constant times, every exponent `𝔠d > 0` (`conStInd_const`; `W_n → ∞` from `Admissible`). -/
private theorem Step34BAInst_con {sz : Sizes 3} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {s0 t0 : ℝ}
    (hst : s0 < t0) (ht : t0 < 1) {𝔠d : ℝ} (h : 0 < 𝔠d) : sz.STConStInd 𝔠d (fun _ => s0) (fun _ => t0) :=
  conStInd_const sz (step34Gen_W_tendsto hflow.1) hst ht h

/-- Regime (iii) at datum A: `lam_n² ≤ 1/3 = 1 - t` (`sz0_lam_L`: `lam² L³ ≤ 1/64`, `L ≥ 1`). -/
private theorem Step34BAInst_regIII : STReg5III sz0 (fun _ => 1 / 2) (fun _ => 2 / 3) := by
  intro n
  have h := sz0_lam_L n
  have hL : (1 : ℝ) ≤ (((sz0.L n) ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_pow _ _ (by have := sz0.three_le_L n; omega)
  have h0 : 0 ≤ sz0.lam n ^ 2 := sq_nonneg _
  change sz0.lam n ^ 2 ≤ 1 - 2 / 3
  nlinarith

/-- Regime (i) at datum B (`STRegIterI` of `ZeroModeBA`, as `STReg5I`). -/
private theorem Step34BAInst_regI : STReg5I szI (fun _ => 0) (fun _ => 1 / 400) :=
  fun n => ⟨szI_regIterI.1 n, szI_regIterI.2 n⟩

/-- **Target 6, instance**: `baQtNZGen_kerNZ` at `k = 3`, `(κ, 𝔡) = (1/2, 1/10)`, applied at `(sz0, zSeq)` (`flow_sz0`): some `C5 > 0` with `QtNZGen_KerNZ` at every
large index, `Aof (1/2) = 3`; at such an index the window is nonempty (`v = w = 1 - 3 g₀²/L²`: `3 g₀² ≤ 3 lam² ≤ 1 ≤ L²`, `g₀ > 0`) and the bound is applied at `σ = (+,-,+)`,
`Aset = univ`, `X ≡ 1`. -/
theorem inst_baQtNZGen_kerNZ :
    ∃ C5 : ℝ, 0 < C5 ∧ ∀ᶠ n in atTop, QtNZGen_KerNZ (baFMz sz0 zSeq) (BAflowLam0 sz0 zSeq) 3 3 C5 n := by
  obtain ⟨C5, hC5, H⟩ := baQtNZGen_kerNZ 3 (by norm_num) 3 (by norm_num) (1 / 2) (1 / 10) (by norm_num) (by norm_num)
  have e : ((1 / 2 : ℝ) + 1) / (1 / 2) = 3 := by norm_num
  have h := H sz0 (1 / 10) (1 / 6) zSeq flow_sz0
  beta_reduce at h
  rw [e] at h
  exact ⟨C5, hC5, h⟩

/-- **Target 6, the window of the instance is nonempty and the bound is applied**: at every index with `0 < g₀`, `v = w = 1 - 3 g₀²/L²` satisfy `0 ≤ v ≤ w < 1` and
`(1 - v) L² ≤ 3 g₀²`, and `QtNZGen_KerNZ` gives `‖Q^{(A)} 𝒰 X‖ ≤ C5 ‖X‖` at the point mass `X ≡ 1`, `σ = (+,-,+)`, `Aset = univ`. -/
example : ∃ C5 : ℝ, 0 < C5 ∧ ∃ n : ℕ, ∃ v w : ℝ, 0 ≤ v ∧ (1 - v) * ((sz0.L n : ℕ) : ℝ) ^ 2 ≤ 3 * BAflowLam0 sz0 zSeq n ^ 2 ∧
    v ≤ w ∧ w < 1 ∧ ‖zeroModeSet 3 (sz0.L n) Finset.univ
      (Step2Gen_UN (baFMz sz0 zSeq) n ![true, false, true] v w (fun _ => (1 : ℂ)))‖ ≤ C5 * ‖(fun _ : Fin 3 → Zd 3 (sz0.L n) => (1 : ℂ))‖ := by
  obtain ⟨C5, hC5, h⟩ := inst_baQtNZGen_kerNZ
  obtain ⟨n, hn, hnw⟩ := (h.and (BAflow_lam0_window (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq flow_sz0)).exists
  have hL : (0 : ℝ) < ((sz0.L n : ℕ) : ℝ) ^ 2 := by
    have : (0 : ℝ) < ((sz0.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz0.three_le_L n; omega : 0 < sz0.L n)
    positivity
  have hL1 : (1 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) ^ 2 := by
    have : (3 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by exact_mod_cast sz0.three_le_L n
    nlinarith
  have hg := TwistStep2_lam0_sq (by norm_num : (0 : ℝ) < 1 / 2) flow_sz0 n
  have hlam : sz0.lam n ^ 2 ≤ 1 / 64 := by
    have h1 := sz0_lam_L n
    have h2 : (1 : ℝ) ≤ (((sz0.L n) ^ 3 : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_pow _ _ (by have := sz0.three_le_L n; omega)
    have h3 : 0 ≤ sz0.lam n ^ 2 := sq_nonneg _
    nlinarith
  have hq : 0 < 3 * BAflowLam0 sz0 zSeq n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 := by
    have : 0 < BAflowLam0 sz0 zSeq n := hnw.1
    positivity
  have hq1 : 3 * BAflowLam0 sz0 zSeq n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one hL]
    nlinarith [hg.1]
  have hwin : (1 - (1 - 3 * BAflowLam0 sz0 zSeq n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2)) * ((sz0.L n : ℕ) : ℝ) ^ 2 ≤
      3 * BAflowLam0 sz0 zSeq n ^ 2 := by
    have : (1 - (1 - 3 * BAflowLam0 sz0 zSeq n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2)) * ((sz0.L n : ℕ) : ℝ) ^ 2 =
        3 * BAflowLam0 sz0 zSeq n ^ 2 := by rw [sub_sub_cancel]; exact div_mul_cancel₀ _ hL.ne'
    exact this.le
  refine ⟨C5, hC5, n, 1 - 3 * BAflowLam0 sz0 zSeq n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2,
    1 - 3 * BAflowLam0 sz0 zSeq n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2, by linarith, hwin, le_rfl, by linarith, ?_⟩
  refine hn _ _ (by linarith) hwin le_rfl (by linarith) ![true, false, true] Finset.univ (fun i _ => Finset.mem_univ i) _

/-- **Target 7 (a), instance**: `baOeqQtgL'_holds 3` at `(κ, ε, 𝔡) = (1/2, 1/10, 1/10)`, `𝔠 = 1/6`, datum A (`STCaseI`: `st_caseI_of_reg5III`). -/
theorem inst_baOeqQtgL' (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLKgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) →
        STStep2ConclgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3) Cd →
        STXiBootgL' (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3)) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := baOeqQtgL'_holds 3 (by norm_num) (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) Cd hCd
  obtain ⟨hK, hKw⟩ := Step34BAInst_K (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10) flow_sz0
  exact ⟨𝔠d, h0, h1, fun hL h2 => H (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun n => t0_sz0 n) (st_caseI_of_reg5III 3 sz0 _ _ Step34BAInst_regIII) hK hKw hL
    (Step34BAInst_con flow_sz0 (by norm_num) (by norm_num) h0) h2⟩

/-- **Target 7 (b), instance**: `baOeqQtNZgL'_holds 3` at `(κ, ε, 𝔡) = (3/5000, 1/2, 1/10)`, `𝔠 = 1/9`, datum C (`TwistStep2_szII`, `STCaseII`). -/
theorem inst_baOeqQtNZgL' (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLKgL (baFMz TwistStep2_szII TwistStep2_zII) (Sizes.seqP (TwistStep2_szII.withLam 0)) (fun _ => 0) →
        STStep2ConclgL (baFMz TwistStep2_szII TwistStep2_zII) (Sizes.seqP (TwistStep2_szII.withLam 0)) (fun _ => 0) (fun _ => 1 / 2000) Cd →
        STXiBootgL' (baFMz TwistStep2_szII TwistStep2_zII) (Sizes.seqP (TwistStep2_szII.withLam 0)) (fun _ => 0) (fun _ => 1 / 2000)) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := baOeqQtNZgL'_holds 3 (by norm_num) (3 / 5000) (1 / 2) (1 / 10) (by norm_num) (by norm_num) (by norm_num) Cd hCd
  obtain ⟨hflow, ht0⟩ := TwistStep2_flowII
  obtain ⟨hK, hKw⟩ := Step34BAInst_K (by norm_num : (0 : ℝ) < 3 / 5000) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 10) hflow
  exact ⟨𝔠d, h0, h1, fun hL h2 => H (1 / 9) TwistStep2_szII TwistStep2_zII hflow (fun _ => 0) (fun _ => 1 / 2000) (fun _ => le_rfl)
    (fun _ => by norm_num) ht0 szII_caseII hK hKw hL (Step34BAInst_con hflow (by norm_num) (by norm_num) h0) h2⟩

/-- **Target 8 (iii), instance**: `baStep3RegIII_holds 3` at datum A, `(κ, ε, 𝔡) = (1/2, 1/10, 1/10)`. -/
theorem inst_baStep3RegIII (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLKgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) →
        STStep1LoopgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3) →
        STStep2ConclgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3) Cd →
        STLmaxUgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3)) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := baStep3RegIII_holds 3 (by norm_num) (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) Cd hCd
  obtain ⟨hK, hKw⟩ := Step34BAInst_K (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10) flow_sz0
  exact ⟨𝔠d, h0, h1, fun hL h1' h2 => H (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun n => t0_sz0 n) Step34BAInst_regIII hK hKw hL
    (Step34BAInst_con flow_sz0 (by norm_num) (by norm_num) h0) h1' h2⟩

/-- **Target 8 (i), instance**: `baStep3RegI_holds 3` at datum B (`szI`), `(κ, ε, 𝔡) = (3/1000, 1/2, 1/10)`, `𝔠 = 1/9`. -/
theorem inst_baStep3RegI (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLKgL (baFMz szI zI) (Sizes.seqP (szI.withLam 0)) (fun _ => 0) →
        STStep1LoopgL (baFMz szI zI) (Sizes.seqP (szI.withLam 0)) (fun _ => 0) (fun _ => 1 / 400) →
        STStep2ConclgL (baFMz szI zI) (Sizes.seqP (szI.withLam 0)) (fun _ => 0) (fun _ => 1 / 400) Cd →
        STLmaxUgL (baFMz szI zI) (Sizes.seqP (szI.withLam 0)) (fun _ => 0) (fun _ => 1 / 400)) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := baStep3RegI_holds 3 (by norm_num) (3 / 1000) (1 / 2) (1 / 10) (by norm_num) (by norm_num) (by norm_num) Cd hCd
  obtain ⟨hK, hKw⟩ := Step34BAInst_K (by norm_num : (0 : ℝ) < 3 / 1000) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 10) flowI.1
  exact ⟨𝔠d, h0, h1, fun hL h1' h2 => H (1 / 9) szI zI flowI.1 (fun _ => 0) (fun _ => 1 / 400) (fun _ => le_rfl)
    (fun _ => by norm_num) szI_window Step34BAInst_regI hK hKw hL
    (Step34BAInst_con flowI.1 (by norm_num) (by norm_num) h0) h1' h2⟩

/-- **Target 8 (ii), instance**: `baStep3II_holds 3` at datum C (`TwistStep2_szII`), `(κ, ε, 𝔡) = (3/5000, 1/2, 1/10)`, `𝔠 = 1/9`. -/
theorem inst_baStep3II (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLKgL (baFMz TwistStep2_szII TwistStep2_zII) (Sizes.seqP (TwistStep2_szII.withLam 0)) (fun _ => 0) →
        STStep1LoopgL (baFMz TwistStep2_szII TwistStep2_zII) (Sizes.seqP (TwistStep2_szII.withLam 0)) (fun _ => 0) (fun _ => 1 / 2000) →
        STStep2ConclgL (baFMz TwistStep2_szII TwistStep2_zII) (Sizes.seqP (TwistStep2_szII.withLam 0)) (fun _ => 0) (fun _ => 1 / 2000) Cd →
        STLmaxUgL (baFMz TwistStep2_szII TwistStep2_zII) (Sizes.seqP (TwistStep2_szII.withLam 0)) (fun _ => 0) (fun _ => 1 / 2000)) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := baStep3II_holds 3 (by norm_num) (3 / 5000) (1 / 2) (1 / 10) (by norm_num) (by norm_num) (by norm_num) Cd hCd
  obtain ⟨hflow, ht0⟩ := TwistStep2_flowII
  obtain ⟨hK, hKw⟩ := Step34BAInst_K (by norm_num : (0 : ℝ) < 3 / 5000) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 10) hflow
  exact ⟨𝔠d, h0, h1, fun hL h1' h2 => H (1 / 9) TwistStep2_szII TwistStep2_zII hflow (fun _ => 0) (fun _ => 1 / 2000) (fun _ => le_rfl)
    (fun _ => by norm_num) ht0 szII_caseII hK hKw hL (Step34BAInst_con hflow (by norm_num) (by norm_num) h0) h1' h2⟩

/-- **Target 9 (i), instance**: `baStep4I_holds 3` at datum A (`STCaseI`). -/
theorem inst_baStep4I (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLKgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) →
        STStep1LoopgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3) →
        STStep2ConclgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3) Cd →
        STLmaxUgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3) →
        STLKUgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3)) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := baStep4I_holds 3 (by norm_num) (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) Cd hCd
  obtain ⟨hK, hKw⟩ := Step34BAInst_K (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10) flow_sz0
  exact ⟨𝔠d, h0, h1, fun hL h1' h2 h3 => H (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun n => t0_sz0 n) (st_caseI_of_reg5III 3 sz0 _ _ Step34BAInst_regIII) hK hKw hL
    (Step34BAInst_con flow_sz0 (by norm_num) (by norm_num) h0) h1' h2 h3⟩

/-- **Target 9 (ii), instance**: `baStep4II_holds 3` at datum C (`STCaseII`). -/
theorem inst_baStep4II (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLKgL (baFMz TwistStep2_szII TwistStep2_zII) (Sizes.seqP (TwistStep2_szII.withLam 0)) (fun _ => 0) →
        STStep1LoopgL (baFMz TwistStep2_szII TwistStep2_zII) (Sizes.seqP (TwistStep2_szII.withLam 0)) (fun _ => 0) (fun _ => 1 / 2000) →
        STStep2ConclgL (baFMz TwistStep2_szII TwistStep2_zII) (Sizes.seqP (TwistStep2_szII.withLam 0)) (fun _ => 0) (fun _ => 1 / 2000) Cd →
        STLmaxUgL (baFMz TwistStep2_szII TwistStep2_zII) (Sizes.seqP (TwistStep2_szII.withLam 0)) (fun _ => 0) (fun _ => 1 / 2000) →
        STLKUgL (baFMz TwistStep2_szII TwistStep2_zII) (Sizes.seqP (TwistStep2_szII.withLam 0)) (fun _ => 0) (fun _ => 1 / 2000)) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := baStep4II_holds 3 (by norm_num) (3 / 5000) (1 / 2) (1 / 10) (by norm_num) (by norm_num) (by norm_num) Cd hCd
  obtain ⟨hflow, ht0⟩ := TwistStep2_flowII
  obtain ⟨hK, hKw⟩ := Step34BAInst_K (by norm_num : (0 : ℝ) < 3 / 5000) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 10) hflow
  exact ⟨𝔠d, h0, h1, fun hL h1' h2 h3 => H (1 / 9) TwistStep2_szII TwistStep2_zII hflow (fun _ => 0) (fun _ => 1 / 2000) (fun _ => le_rfl)
    (fun _ => by norm_num) ht0 szII_caseII hK hKw hL (Step34BAInst_con hflow (by norm_num) (by norm_num) h0) h1' h2 h3⟩

/-- **Target 9 (iii), instance**: `baStep4RegIII_holds 3` at datum A (`STReg5III`). -/
theorem inst_baStep4RegIII (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLKgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) →
        STStep1LoopgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3) →
        STStep2ConclgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3) Cd →
        STLmaxUgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3) →
        STLKUgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3)) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := baStep4RegIII_holds 3 (by norm_num) (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) Cd hCd
  obtain ⟨hK, hKw⟩ := Step34BAInst_K (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10) flow_sz0
  exact ⟨𝔠d, h0, h1, fun hL h1' h2 h3 => H (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun n => t0_sz0 n) Step34BAInst_regIII hK hKw hL
    (Step34BAInst_con flow_sz0 (by norm_num) (by norm_num) h0) h1' h2 h3⟩

/-- **Target 9 (iv), instance**: `baStep4RegI_holds 3` at datum B (`STReg5I`). -/
theorem inst_baStep4RegI (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLKgL (baFMz szI zI) (Sizes.seqP (szI.withLam 0)) (fun _ => 0) →
        STStep1LoopgL (baFMz szI zI) (Sizes.seqP (szI.withLam 0)) (fun _ => 0) (fun _ => 1 / 400) →
        STStep2ConclgL (baFMz szI zI) (Sizes.seqP (szI.withLam 0)) (fun _ => 0) (fun _ => 1 / 400) Cd →
        STLmaxUgL (baFMz szI zI) (Sizes.seqP (szI.withLam 0)) (fun _ => 0) (fun _ => 1 / 400) →
        STLKUgL (baFMz szI zI) (Sizes.seqP (szI.withLam 0)) (fun _ => 0) (fun _ => 1 / 400)) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := baStep4RegI_holds 3 (by norm_num) (3 / 1000) (1 / 2) (1 / 10) (by norm_num) (by norm_num) (by norm_num) Cd hCd
  obtain ⟨hK, hKw⟩ := Step34BAInst_K (by norm_num : (0 : ℝ) < 3 / 1000) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 10) flowI.1
  exact ⟨𝔠d, h0, h1, fun hL h1' h2 h3 => H (1 / 9) szI zI flowI.1 (fun _ => 0) (fun _ => 1 / 400) (fun _ => le_rfl)
    (fun _ => by norm_num) szI_window Step34BAInst_regI hK hKw hL
    (Step34BAInst_con flowI.1 (by norm_num) (by norm_num) h0) h1' h2 h3⟩

end RBM.BA.Step34BAInst

end
