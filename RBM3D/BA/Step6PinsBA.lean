/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.Step6BridgeBA
import RBM3D.Chain.ExpEtermsAGen
import RBM3D.Chain.ExpEtermsBGen
import RBM3D.Chain.ExpIniIGen
import RBM3D.Chain.ExpWardIGen
import RBM3D.Chain.ExpIntIIGen
import RBM3D.Chain.ExpDuhamelGen
import RBM3D.BA.EKGenBA
import RBM3D.BA.GridDriftBA
import RBM3D.BA.Step5KerBA
import RBM3D.BA.B45BA
import RBM3D.BA.Step5CasesBA

/-!
# Step 6 of `lem:main_ind` at the block Anderson tuple: the statements and the regimes

Step 6 of Theorem 2.24 (`lem:main_ind`) (Section 6, `Sec:Step6`) at the BA tuple
`(fun sz => Sizes.seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`, `gK = BAflowLam0`, `κm = κ`, `Aof κ = (κ+1)/κ`, `mkM = baStep2Mat sz g₀ (BAflowEs sz z)`,
`H₀ = g₀ Ψ`, `g' = 0`.  No new mathematics: the generic producers (`stExpLKLKHigL_of`, `stExpDriftLogL_of`, …) are read by name.

* `BAStep6R` (the one new public def): `STIngR6gL d R` at the BA tuple, with TL1, TL2 at every `u ∈ [s,t]` on the `Concl` slot.
* `baExpLKLKHigL`, `baExpDriftLogL`, `baExpDriftDecaygL`, `baExpWardIgL'`, `baExpIniIgL'`, `baExpIntIIgL`: the generic producers
  at the BA tuple.  The generic `stExpLKLKHigL_of`, `stExpDriftLogL_of`, `stExpIniIgL'_of` take `STKboundgL` unguarded in
  `d`; `SEforLnBA_Kbound` needs `3 ≤ d`, which every statement supplies (`STIngR6gL` starts `3 ≤ d →`).
* `baExpDuhamelZgL`, `baExpDuhamelQgL`: `stExpDuhamelZgL_ev`, `stExpDuhamelQgL_ev`; the semigroup law of `uKer` holds for every `d`
  (`BAuKerSemigroup_holds`, no `3 ≤ d`), so it is the body of the first conjunct of `baIniTermGen_kerFacts`, not that conjunct.
* `baStep6RegIII_of_pin`, `baStep6RegIV_of_pin`, `baStep6RegII_of_pin`: the bodies of `ST_step6_caseIII_of_pins`, `ST_step6_caseIV_of_pins`, `ST_step6_caseII_of_pins` (`Induction/Step6Kit`), with the generic cores `st6_caseIII_coreg`, `st6_caseIV_coreg`, `st6_caseII_coreg` of `Chain/Step6KitGen`, per flow at BA
  with the cores `st6_caseIII_coreg`, `st6_caseIV_coreg`, `st6_caseII_coreg`; `hegt` from the glue `Step6BridgeBA_LW`, `hAvgU` from `baExpAvgUgL_of_tl1`; the three generic statements
  `STExpIntIIIgL`, `STExpIntIVgL`, `STExpWardIIgL` are hypotheses.  The regimes (i) are in `BA/Step6BA`.

Names of the file stem `Step6PinsBA_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open private SEforLnBA_Kbound from RBM3D.BA.SEforLnBA
open private Step6BridgeBA_LW Step6BridgeBA_decay from RBM3D.BA.Step6BridgeBA
open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. `BAStep6R` -/

/-- `BAStep6R`: the statement `STIngR6gL d R` at the BA tuple
`(fun sz => Sizes.seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)` (`STStep6R`), with TL1 `BATwistAvgLaw` and TL2 `BATwistLoopLaw` at every
time sequence `u ∈ [s,t]` as the premise of the conclusion. -/
def BAStep6R (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  STIngR6gL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)
    (fun sz z s t => (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
      BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u ∧ BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u) →
      STStep6ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t)

/-! ## 2. The generic producers at the BA tuple -/

section Pins

/-- The column sums of `S = 1` along every BA flow (`baSEforLnGen_facts`). -/
private theorem Step6PinsBA_cols (d : ℕ) :
    ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ (n : ℕ) (y : Zd d (sz.L n)), ∑ x : Zd d (sz.L n), ‖(baFMz sz z).S n x y‖ ≤ 1 := by
  intro sz κ ε 𝔠 𝔡 z hκ hf n y
  obtain ⟨-, -, -, -, -, -, hcol, -⟩ := baSEforLnGen_facts d sz κ ε 𝔠 𝔡 z hκ hf
  exact hcol n y

/-- `Aof κ = (κ+1)/κ ≥ 1` for `κ > 0` (the coupling comparison: `1 ≤ (κ+1)/κ`). -/
private theorem Step6PinsBA_Aof : ∀ κm : ℝ, 0 < κm → 1 ≤ (fun κ : ℝ => (κ + 1) / κ) κm := fun κm hκm => by
  change 1 ≤ (κm + 1) / κm
  rw [le_div_iff₀ hκm]; linarith

/-- `(eq:Exp(L-K)1)` at BA (`stExpLKLKHigL_of` with `Step2EventsGenTw_baFlow`, `baIniTermGen_cltFlow`, `SEforLnBA_Kbound`, `Step6PinsBA_cols`). -/
theorem baExpLKLKHigL (d : ℕ) :
    STExpLKLKHigL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) := by
  intro hd
  exact stExpLKLKHigL_of d _ _ _ _ (fun sz => Sizes.isProbabilityMeasure_seqP (sz.withLam 0)) (Step2EventsGenTw_baFlow d)
    (baIniTermGen_cltFlow d) (fun sz κ ε 𝔠 𝔡 z hκ hf => SEforLnBA_Kbound d hd sz κ ε 𝔠 𝔡 z hκ hf) (Step6PinsBA_cols d) hd

/-- `(eq:Exp(L-K)2)`, `(eq:ExpLWn=2_smalleta)` at BA (`stExpDriftLogL_of`; the inputs of `baExpLKLKHigL` and `baKsol_oneLoop`). -/
theorem baExpDriftLogL (d : ℕ) :
    STExpDriftLogL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) := by
  intro hd
  exact stExpDriftLogL_of d _ _ _ _ (fun sz => Sizes.isProbabilityMeasure_seqP (sz.withLam 0)) (Step2EventsGenTw_baFlow d)
    (baIniTermGen_cltFlow d) (fun sz κ ε 𝔠 𝔡 z hκ hf => SEforLnBA_Kbound d hd sz κ ε 𝔠 𝔡 z hκ hf) (Step6PinsBA_cols d)
    (fun sz κ ε 𝔠 𝔡 z hκ hf => baKsol_oneLoop d sz κ ε 𝔠 𝔡 z hκ hf) hd

/-- `(deccA0)` for the expected drift at BA (`stExpDriftDecaygL_of`; as `baExpDriftLogL`, and `Step6BridgeBA_decay`). -/
theorem baExpDriftDecaygL (d : ℕ) :
    STExpDriftDecaygL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) := by
  intro hd
  exact stExpDriftDecaygL_of d _ _ _ _ (fun sz => Sizes.isProbabilityMeasure_seqP (sz.withLam 0)) (Step2EventsGenTw_baFlow d)
    (baIniTermGen_cltFlow d) (fun sz κ ε 𝔠 𝔡 z hκ hf => SEforLnBA_Kbound d hd sz κ ε 𝔠 𝔡 z hκ hf) (Step6PinsBA_cols d)
    (fun sz κ ε 𝔠 𝔡 z hκ hf => baKsol_oneLoop d sz κ ε 𝔠 𝔡 z hκ hf) (Step6BridgeBA_decay d) hd

/-- The primed Ward statement at BA (`stExpWardIgL'_of` with `baStep5CasesGen_flowFacts`, `baCltRepg_holds`, `baB45Gen_facts`, `baKsol_oneLoop`). -/
theorem baExpWardIgL' (d : ℕ) :
    STExpWardIgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) :=
  stExpWardIgL'_of (fun sz => Sizes.isProbabilityMeasure_seqP (sz.withLam 0)) (baStep5CasesGen_flowFacts d)
    (fun sz κ ε 𝔠 𝔡 z _ _ => ⟨_, fun _ => 0, BAflowEs sz z, baCltRepg_holds sz z⟩) (baB45Gen_facts d)
    (fun sz κ ε 𝔠 𝔡 z hκ hf => baKsol_oneLoop d sz κ ε 𝔠 𝔡 z hκ hf)

/-- The initial term of regime (i) at BA (`stExpIniIgL'_of` with `baStep5CasesGen_flowFacts`, `baIniTermGen_cltFlow`, `SEforLnBA_Kbound`, `baEKSumRes2NALgL_holds`, `baEKSumRes2gL_holds`,
and the coupling comparison through `baEKKer_flow` at `Aof κ = (κ+1)/κ`, `gK = g₀`). -/
theorem baExpIniIgL' (d : ℕ) :
    STExpIniIgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) := by
  intro hd
  exact stExpIniIgL'_of (Ker := @BAEKKer d) (Aof := fun κ => (κ + 1) / κ) (fun sz z => BAflowLam0 sz z)
    (fun sz => Sizes.isProbabilityMeasure_seqP (sz.withLam 0)) (baStep5CasesGen_flowFacts d) (baIniTermGen_cltFlow d)
    (fun sz κ ε 𝔠 𝔡 z hκ hf => SEforLnBA_Kbound d hd sz κ ε 𝔠 𝔡 z hκ hf) (baEKSumRes2NALgL_holds d) (baEKSumRes2gL_holds d)
    Step6PinsBA_Aof (baEKKer_flow d) hd

/-- Regime (ii) integrated estimate at BA (`stExpIntIIgL_of` with `baStep5CasesGen_flowFacts`, `baEKNonzerogL_holds` and the coupling comparison through `baEKKer_flow`). -/
theorem baExpIntIIgL (d : ℕ) :
    STExpIntIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) :=
  stExpIntIIgL_of (Ker := @BAEKKer d) (Aof := fun κ => (κ + 1) / κ) (fun sz z => BAflowLam0 sz z)
    (fun sz => Sizes.isProbabilityMeasure_seqP (sz.withLam 0)) (baStep5CasesGen_flowFacts d) (baEKNonzerogL_holds d _)
    Step6PinsBA_Aof (baEKKer_flow d)

/-- The semigroup law of `uKer` at every size index along every BA flow, for every `d` (the body of the first conjunct of `baIniTermGen_kerFacts`, `BA/Step5KerBA`;
that conjunct sits under `3 ≤ d`, the statements `STExpDuhamelZgL`, `STExpDuhamelQgL` carry no `3 ≤ d`). -/
private theorem Step6PinsBA_USemigroup {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z)
    (n : ℕ) : Step2Gen_USemigroup (baFMz sz z) n := by
  intro σ σ' u v w hv0 hv1 hw0 hw1
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hIm : ((BAflowEs sz z n : ℂ) + BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im ≠ 0 := by
    simpa using (lt_of_lt_of_le hκ hr.2).ne'
  have h := BAuKerSemigroup_holds d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n)
    (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) hr σ σ' u v w hv0 hv1 hw0 hw1
  simp only [← Step2Kern_uKer_BA sz (BAflowLam0 sz z) (BAflowEs sz z) n hIm] at h
  exact h

/-- The data `hrep` of `stExpDuhamelZgL_ev` at BA: `H₀ = g₀ Ψ`, `g' = 0`, `E = BAflowEs`, one witness (`baCltRepg_holds ∧ baStep2Mat_loopForm ∧ baStep2Mat_S`). -/
private theorem Step6PinsBA_rep (d : ℕ) :
    ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
      ∃ (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (g' E : ℕ → ℝ),
        CltRepg (baFMz sz z) (Sizes.seqP (sz.withLam 0)) H₀ g' E ∧
          StepDecompGen_LoopForm (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) E ∧
          ∀ n, (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).S n = SB d (sz.L n) (g' n) :=
  fun sz κ ε 𝔠 𝔡 z hκ hf => ⟨_, fun _ => 0, BAflowEs sz z, baCltRepg_holds sz z, baStep2Mat_loopForm d sz κ ε 𝔠 𝔡 z hκ hf,
    fun n => baStep2Mat_S sz _ _ n⟩

/-- The classes `HierDriftGen_KLoop`, `HierDriftGen_KTwo`, `HierDriftGen_KLink` eventually (`baHierDrift_classes`). -/
private theorem Step6PinsBA_cls (d : ℕ) :
    ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, HierDriftGen_KLoop (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n ∧
        HierDriftGen_KTwo (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n ∧
        HierDriftGen_KLink (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n := by
  intro sz κ ε 𝔠 𝔡 z hκ hf
  obtain ⟨-, hLink, -, hev⟩ := baHierDrift_classes sz κ ε 𝔠 𝔡 z hκ hf
  exact hev.mono fun n hn => ⟨hn.1, hn.2.1, hLink n⟩

/-- The plain and zero-mode Duhamel family at BA (`stExpDuhamelZgL_ev` with `Step6PinsBA_rep`, `Step6PinsBA_cls`, `Step6PinsBA_USemigroup`). -/
theorem baExpDuhamelZgL (d : ℕ) :
    STExpDuhamelZgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) :=
  stExpDuhamelZgL_ev _ _ _ (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => rfl) (Step6PinsBA_rep d)
    (Step6PinsBA_cls d) (fun sz κ ε 𝔠 𝔡 z hκ hf => Eventually.of_forall fun n => Step6PinsBA_USemigroup hκ hf n)

/-- The `𝒬`-Duhamel family at BA (`stExpDuhamelQgL_ev` with `Step6PinsBA_rep`, `Step6PinsBA_cls`, `Step6PinsBA_USemigroup`). -/
theorem baExpDuhamelQgL (d : ℕ) :
    STExpDuhamelQgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) :=
  stExpDuhamelQgL_ev _ _ _ (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => rfl) (Step6PinsBA_rep d)
    (Step6PinsBA_cls d) (fun sz κ ε 𝔠 𝔡 z hκ hf => Eventually.of_forall fun n => Step6PinsBA_USemigroup hκ hf n)

end Pins

/-! ## 3. The regimes (iii), (iv), (ii) from the three generic statements -/

section Regimes

/-- Step 6, regime (iii), at BA from the generic statement `STExpIntIIIgL` (`baStep6RegIII_of_pin`, the body of `ST_step6_caseIII_of_pins` of `Induction/Step6Kit`, with `st6_caseIII_coreg` of `Chain/Step6KitGen`): `STExpLKLKHigL`
(`baExpLKLKHigL`), the LW bound at every `u` (`Step6BridgeBA_LW`, TL1, TL2 from the `Concl` slot), the Duhamel family (`baExpDuhamelZgL`), the statement `STExpIntIIIgL` (a hypothesis) and
the initial term `st6_ini_sumNdecayg` with `baEKSumNdecaygL_holds` and `baEKKer_flow`; `𝔠d = min` of the two constants. -/
theorem baStep6RegIII_of_pin (d : ℕ) :
    STExpIntIIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) → BAStep6R d STReg5III := by
  intro hInt hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := baExpLKLKHigL d hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₂, hc₂, hc₂', H₂⟩ := hInt hd κ ε 𝔡 hκ hε h𝔡
  have hcpos : 0 < min c₁ c₂ := lt_min hc₁ hc₂
  refine ⟨min c₁ c₂, hcpos, (min_le_left _ _).trans hc₁', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec hExp hcon hS2 hLmax hLKU hS5 hTL
  obtain ⟨κm, hκm, hKF⟩ := baEKKer_flow d κ hκ
  obtain ⟨-, hKer', hg', -⟩ := hKF sz ε 𝔠 𝔡 z hflow
  have hadm : sz.Admissible 𝔠 𝔡 := hflow.1
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  have hHi := st6_hi_of_reg5III sz hR
  have hlk := H₁ 𝔠 sz z hflow s t hs0 hst htT hHi hLK0 hDec hExp
    (st5_conStInd_mono sz hcon ht1 hcpos (min_le_left _ _)) hS2 hLmax hLKU hS5
  have hegt := st6_EGtHi_of_LWg (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t (Sizes.isProbabilityMeasure_seqP (sz.withLam 0))
    hadm.2.2.1 (fun n => (hst n).le) hHi (Step2EventsGenTw_baRot3 sz _ _)
    (Step6BridgeBA_LW d hd hκ hε h𝔡 hflow hs0 htT hS2 hLmax hLKU hS5 hTL)
  have hduh := st6_duhEq_of_ping (baExpDuhamelZgL d) hκ hflow hs0 ht1
  have hint := H₂ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec hExp
    (st5_conStInd_mono sz hcon ht1 hcpos (min_le_right _ _)) hS2 hLmax hLKU hS5
  have hini := st6_ini_sumNdecayg (baEKSumNdecaygL_holds d) hd hκm hadm (baFMz sz z) (BAflowLam0 sz z) hKer' hg'
    (Sizes.isProbabilityMeasure_seqP (sz.withLam 0)) hs0 hst ht1 hExp
  exact st6_caseIII_coreg (baFMz sz z) (Sizes.seqP (sz.withLam 0)) hadm hs0 hst ht1 hR hlk hegt hduh hint hini

/-- Step 6, regime (iv), at BA from the generic statement `STExpIntIVgL` (`baStep6RegIV_of_pin`, the body of `ST_step6_caseIV_of_pins` of `Induction/Step6Kit`, with `st6_caseIV_coreg` of `Chain/Step6KitGen`): `STExpDriftLogL`
(`baExpDriftLogL`), whose premise `(res_ELK_n=1)` is `baExpAvgUgL_of_tl1` (TL1 on `[s,t]` from the `Concl` slot), the Duhamel family, the statement `STExpIntIVgL` and the initial term. -/
theorem baStep6RegIV_of_pin (d : ℕ) :
    STExpIntIVgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) → BAStep6R d STReg5IV := by
  intro hInt hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := baExpDriftLogL d hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₂, hc₂, hc₂', H₂⟩ := hInt hd κ ε 𝔡 hκ hε h𝔡
  have hcpos : 0 < min c₁ c₂ := lt_min hc₁ hc₂
  refine ⟨min c₁ c₂, hcpos, (min_le_left _ _).trans hc₁', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec hExp hcon hS2 hLmax hLKU hS5 hTL
  obtain ⟨κm, hκm, hKF⟩ := baEKKer_flow d κ hκ
  obtain ⟨-, hKer', hg', -⟩ := hKF sz ε 𝔠 𝔡 z hflow
  have hadm : sz.Admissible 𝔠 𝔡 := hflow.1
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  have hAvgU := baExpAvgUgL_of_tl1 d hd κ ε 𝔠 𝔡 hκ hε h𝔡 sz z hflow s t hs0 hst htT hS2 hLKU
    (fun u hsu hut => (hTL u hsu hut).1)
  have hlo := H₁ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec hExp
    (st5_conStInd_mono sz hcon ht1 hcpos (min_le_left _ _)) hS2 hLmax hLKU hS5
  have hduh := st6_duhEq_of_ping (baExpDuhamelZgL d) hκ hflow hs0 ht1
  have hint := H₂ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec hExp
    (st5_conStInd_mono sz hcon ht1 hcpos (min_le_right _ _)) hS2 hLmax hLKU hS5
  have hini := st6_ini_sumNdecayg (baEKSumNdecaygL_holds d) hd hκm hadm (baFMz sz z) (BAflowLam0 sz z) hKer' hg'
    (Sizes.isProbabilityMeasure_seqP (sz.withLam 0)) hs0 hst ht1 hExp
  exact st6_caseIV_coreg (baFMz sz z) (Sizes.seqP (sz.withLam 0)) hadm hs0 hst ht1 hR hAvgU hlo hduh hint hini

/-- Step 6, regime (ii), at BA from the generic statement `STExpWardIIgL` (`baStep6RegII_of_pin`, the body of `ST_step6_caseII_of_pins` of `Induction/Step6Kit`, with `st6_caseII_coreg` of `Chain/Step6KitGen`): `STExpLKLKHigL`, the LW bound at
every `u`, `baExpAvgUgL_of_tl1`, the Duhamel family, `STExpIntIIgL` (`baExpIntIIgL`), the Ward decomposition `STExpWardIIgL` (a hypothesis) and the two initial
terms `st6_ini_nonzerog` with `baEKNonzerogL_holds`, and the coupling comparison from `baEKKer_flow` at `Aof κ = (κ+1)/κ`. -/
theorem baStep6RegII_of_pin (d : ℕ) :
    STExpWardIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) → BAStep6R d STReg5II := by
  intro hWd hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := baExpLKLKHigL d hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₂, hc₂, hc₂', H₂⟩ := baExpIntIIgL d hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₃, hc₃, hc₃', H₃⟩ := hWd hd κ ε 𝔡 hκ hε h𝔡
  have hcpos : 0 < min c₁ (min c₂ c₃) := lt_min hc₁ (lt_min hc₂ hc₃)
  refine ⟨min c₁ (min c₂ c₃), hcpos, (min_le_left _ _).trans hc₁', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec hExp hcon hS2 hLmax hLKU hS5 hTL
  obtain ⟨κm, hκm, hKF⟩ := baEKKer_flow d κ hκ
  obtain ⟨-, hKer', hg', hR1'⟩ := hKF sz ε 𝔠 𝔡 z hflow
  have hadm : sz.Admissible 𝔠 𝔡 := hflow.1
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  have hHi := st6_hi_of_reg5II sz hR
  have hAvgU := baExpAvgUgL_of_tl1 d hd κ ε 𝔠 𝔡 hκ hε h𝔡 sz z hflow s t hs0 hst htT hS2 hLKU
    (fun u hsu hut => (hTL u hsu hut).1)
  have hlk := H₁ 𝔠 sz z hflow s t hs0 hst htT hHi hLK0 hDec hExp
    (st5_conStInd_mono sz hcon ht1 hcpos (min_le_left _ _)) hS2 hLmax hLKU hS5
  have hegt := st6_EGtHi_of_LWg (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t (Sizes.isProbabilityMeasure_seqP (sz.withLam 0))
    hadm.2.2.1 (fun n => (hst n).le) hHi (Step2EventsGenTw_baRot3 sz _ _)
    (Step6BridgeBA_LW d hd hκ hε h𝔡 hflow hs0 htT hS2 hLmax hLKU hS5 hTL)
  have hduh := st6_duhEq_of_ping (baExpDuhamelZgL d) hκ hflow hs0 ht1
  have hint := H₂ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec hExp
    (st5_conStInd_mono sz hcon ht1 hcpos ((min_le_right _ _).trans (min_le_left _ _))) hS2 hLmax hLKU hS5
  have hward := H₃ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec hExp
    (st5_conStInd_mono sz hcon ht1 hcpos ((min_le_right _ _).trans (min_le_right _ _))) hS2 hLmax hLKU hS5
  have hsg : ∀ n, 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ s n := fun n => by linarith [(hR n).2]
  exact st6_caseII_coreg (baFMz sz z) (Sizes.seqP (sz.withLam 0)) hadm hs0 hst ht1 hR hlk hegt hAvgU hduh hint hward
    (st6_ini_nonzerog (baEKNonzerogL_holds d (fun κ => (κ + 1) / κ)) hd hκm (Step6PinsBA_Aof κm hκm) hadm (baFMz sz z)
      (BAflowLam0 sz z) hKer' hg' hR1' (Sizes.isProbabilityMeasure_seqP (sz.withLam 0)) hs0 hst ht1 hsg hExp
      (Finset.univ : Finset (Fin 2)) STSigMixed (fun σ _ i _ => Finset.mem_univ i))
    (st6_ini_nonzerog (baEKNonzerogL_holds d (fun κ => (κ + 1) / κ)) hd hκm (Step6PinsBA_Aof κm hκm) hadm (baFMz sz z)
      (BAflowLam0 sz z) hKer' hg' hR1' (Sizes.isProbabilityMeasure_seqP (sz.withLam 0)) hs0 hst ht1 hsg hExp
      (∅ : Finset (Fin 2)) STSigSame (fun σ hσ i hi => absurd hi (st6_Idiff_same hσ i)))

end Regimes

end RBM.BA

end
