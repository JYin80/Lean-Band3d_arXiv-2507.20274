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
# Steps 3-4 of `lem:main_ind` at the block Anderson tuple

Paper: Steps 3-4 of the proof of Theorem 2.24 (`lem:main_ind`) (the induction hypotheses (2.89)-(2.91), `Eq:Gdecay_w`, `Eq:L-KGt-flow`), read at the block Anderson model
(Section 8: Steps 3-6 extend verbatim; Theorem 8.2 `lem:main_ind_BA`).  Composition of existing results, no new mathematics and no new public `def`.

BA tuple `(law, Flow, mkM, Hf, Es, T0)`: law `seqP (sz.withLam 0)`, flow `BAFlow`, `mkM = baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)`,
`Hf = seqHflowBA (BAflowLam0 sz z)`, `Es = BAflowEs`, `T0 = BAflowT0`, `mk = baFMz`; kernel coupling `gK = BAflowLam0`, `Aof κ = (κ+1)/κ`; the comparison of the
couplings enters only as the slots `hR1` of the two bootstraps (`TwistStep2_lam0_sq`, with `0 ≤ g₀ λ`).

* `baQtNZGen_kerNZ`: `QtNZGen_KerNZFam` at BA, with the constant from `baEKSumDecayNonzeroA_holds` at `A = (κ+1)/κ`.
* `baOeqQtgL'_holds`, `baOeqQtNZgL'_holds`: `stOeqQtgL'_of`, `stOeqQtNZgL'_of` at the BA tuple, every slot an existing BA result.
* `baStep3RegIII_holds`, `baStep3RegI_holds`, `baStep3II_holds`: `STStep3RgL` at the BA tuple at the three regimes.
* `baStep4I_holds`, `baStep4II_holds`, `baStep4RegIII_holds`, `baStep4RegI_holds`: `STStep4RgL` at the BA tuple.

The generic Steps 3-4 theorems are in `Chain/Step34RGen`.  There is no statement at `STAny`: Steps 3-4 are stated per regime.  Private helpers carry the stem `Step34BA_`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open private EKGenBA_hIm from RBM3D.BA.EKGenBA

open MeasureTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Lemma 4.17 (`lem:sum_decay_nonzero`) at BA -/

/-- `baQtNZGen_kerNZ` (`QtNZGen_KerNZFam`): the family form of Lemma 4.17 (`lem:sum_decay_nonzero`) at the BA tuple,
`Aof κ = (κ+1)/κ`, `gK = g₀`.  The constant `C5` is that of `baEKSumDecayNonzeroA_holds d k 𝔡⁻¹ κ` at `A = (κ+1)/κ`, so it depends on `(d, k, 𝔡, κ)` only (before
`(sz, z)`); at a flow the window `0 < g₀ ≤ 𝔡⁻¹` holds eventually (`BAflow_lam0_window`), the kernel is `BAUN` (`Step2Kern_UN_BA`). -/
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

/-! ## 2. The two bootstraps at BA -/

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

/-- The comparison of the kernel coupling `g₀` with the size-level `λ`: `1 ≤ (κ+1)/κ`, `0 ≤ g₀ λ`, `g₀² ≤ λ²`, `λ² ≤ ((κ+1)/κ) g₀²`
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

/-- `baOeqQtgL'_holds`: Lemma 4.10 (`lem:STOeq_Qt`) at the BA tuple: `stOeqQtgL'_of` with every slot an existing BA result
(`baSEforLn_holds`, `Step2EventsGenTw_baFlow`, `Step2EventsGenTw_baLaw`, `DecayGenTw_baWardPair`, `baKcalDecay_holds`, `baEtermDecaygL`, `baStep2Mat_walkForm`,
`baStep2Mat_S`, `baStep2Mat_S_rowSum`, `gridRepTailGen_ker_BA`, `baHierDrift_classes`, `baNQGoodGen_kerNAL`, `baQProxyG_kerEK4`, `baStep5KerGen_thDecay`,
`baB45Gen_facts`, `baKloop_lip`, `baLemDecCalELipG_flowMod`); `lam' = 0`, `Ψ = g₀ Ψ_I`, `gK = g₀`, `Aof κ = (κ+1)/κ`.  For `d < 3` the statement is vacuous. -/
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

/-- `baOeqQtNZgL'_holds`: Lemma 4.14 (`lem:STOeq_Qt_nonzero`) at the BA tuple: `stOeqQtNZgL'_of` with the slots of `baOeqQtgL'_holds` except the
alternating-endpoint and `Θ`-decay classes, plus `baQtNZGen_kerNZ` and the comparison of the couplings in the form `λ² ≤ ((κ+1)/κ) g₀²`. -/
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

/-! ## 3. Steps 3-4 at the BA tuple, per regime

The statements of `STStep3RgL`, `STStep4RgL` at `(law, Flow, mk, T0)` of the BA tuple; `mk sz z = baFMz sz z` is `(baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).toFlowFM` by
unfolding (as `baSTIterationsgL'_holds`).  The family bundle is `baIterationsGen2_fam`. -/

/-- `baStep3RegIII_holds`: Step 3 at regime (iii) at the BA tuple, `𝔠d = 1/100`. -/
theorem baStep3RegIII_holds (d : ℕ) :
    STStep3RgL d STReg5III (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
  stStep3RegIIIgL_of d _ _ (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))
    (fun sz z => sz.seqHflowBA (BAflowLam0 sz z)) (fun sz z => BAflowEs sz z) (fun sz z => BAflowT0 sz z)
    (baIterationsGen2_fam d)

/-- `baStep3RegI_holds`: Step 3 at regime (i) at the BA tuple, from `baIterationsGen2_fam`, the bootstrap
`baOeqQtgL'_holds` and `baSTIterationsgL'_holds`. -/
theorem baStep3RegI_holds (d : ℕ) :
    STStep3RgL d STReg5I (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
  stStep3RegIgL_of d _ _ (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))
    (fun sz z => sz.seqHflowBA (BAflowLam0 sz z)) (fun sz z => BAflowEs sz z) (fun sz z => BAflowT0 sz z)
    (baIterationsGen2_fam d) (baOeqQtgL'_holds d) (baSTIterationsgL'_holds d)

/-- `baStep3II_holds`: Step 3 at case (ii) at the BA tuple, from `baIterationsGen2_fam`, the bootstrap
`baOeqQtNZgL'_holds` and `baSTIterationsIIgL'_holds`. -/
theorem baStep3II_holds (d : ℕ) :
    STStep3RgL d STCaseII (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
  stStep3IIgL_of d _ _ (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))
    (fun sz z => sz.seqHflowBA (BAflowLam0 sz z)) (fun sz z => BAflowEs sz z) (fun sz z => BAflowT0 sz z)
    (baIterationsGen2_fam d) (baOeqQtNZgL'_holds d) (baSTIterationsIIgL'_holds d)

/-- `baStep4I_holds`: Step 4 at case (i) at the BA tuple, from `baIterationsGen2_fam` and the bootstrap
`baOeqQtgL'_holds` (`STIngRgL d STCaseI .. STXiBootgL'`). -/
theorem baStep4I_holds (d : ℕ) :
    STStep4RgL d STCaseI (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
  stStep4RgL_of_ing d STCaseI _ _ (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))
    (fun sz z => sz.seqHflowBA (BAflowLam0 sz z)) (fun sz z => BAflowEs sz z) (fun sz z => BAflowT0 sz z)
    (baIterationsGen2_fam d) (baOeqQtgL'_holds d)

/-- `baStep4II_holds`: Step 4 at case (ii) at the BA tuple, from `baOeqQtNZgL'_holds`. -/
theorem baStep4II_holds (d : ℕ) :
    STStep4RgL d STCaseII (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
  stStep4RgL_of_ing d STCaseII _ _ (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))
    (fun sz z => sz.seqHflowBA (BAflowLam0 sz z)) (fun sz z => BAflowEs sz z) (fun sz z => BAflowT0 sz z)
    (baIterationsGen2_fam d) (baOeqQtNZgL'_holds d)

/-- `baStep4RegIII_holds`: Step 4 at regime (iii), `baStep4I_holds` by `stStep34RgL_mono` along
`STReg5III ⊆ STCaseI` (`st_caseI_of_reg5III`). -/
theorem baStep4RegIII_holds (d : ℕ) :
    STStep4RgL d STReg5III (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
  (stStep34RgL_mono d STCaseI STReg5III _ _ _ _ (fun sz s t h => st_caseI_of_reg5III d sz s t h)).2 (baStep4I_holds d)

/-- `baStep4RegI_holds`: Step 4 at regime (i), `baStep4I_holds` along `STReg5I ⊆ STCaseI` (`st_caseI_of_reg5I`). -/
theorem baStep4RegI_holds (d : ℕ) :
    STStep4RgL d STReg5I (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
  (stStep34RgL_mono d STCaseI STReg5I _ _ _ _ (fun sz s t h => st_caseI_of_reg5I d sz s t h)).2 (baStep4I_holds d)

end RBM.BA

end
