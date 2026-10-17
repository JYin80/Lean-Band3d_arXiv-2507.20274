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
# Step 6 of `lem:main_ind` at the block Anderson tuple: the pins and the regimes (BA-V row V1-BA, ticket T2510 row a, file 2)

Step 6 of `lem:main_ind` (arXiv:2507.20274 `1_2:1390-1396`, proof `6:3-152`) at the BA tuple
`(fun sz => Sizes.seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`, `gK = BAflowLam0`, `κm = κ`, `Aof κ = (κ+1)/κ`, `mkM = baStep2Mat sz g₀ (BAflowEs sz z)`,
`H₀ = g₀Ψ`, `g' = 0`.  No new mathematics: the merged generic producers of T2502 and T2506 are read by name.

* **Target 6** `BAStep6R` (the one new public def): `STIngR6gL d R` at the BA tuple, with TL1, TL2 at every `u ∈ [s,t]` on the `Concl` slot (V2a reads it by name).
* **Target 7** `baExpLKLKHigL`, `baExpDriftLogL`, `baExpDriftDecaygL`, `baExpWardIgL`, `baExpWardIgL'`, `baExpIniIgL'`, `baExpIntIIgL`: the merged producers
  at the BA tuple (rows 1, 2, 3, 5, 6, 9, 9', 16, 17, 18, 19, 19', 20).  The merged `stExpLKLKHigL_of`, `stExpDriftLogL_of`, `stExpIniIgL'_of` take `STKboundgL` unguarded in
  `d`; `SEforLnBA_Kbound` needs `3 ≤ d`, which every pin text supplies (`STIngR6gL` starts `3 ≤ d →`).
* **Target 8** `baExpDuhamelZgL`, `baExpDuhamelQgL` (O5): `stExpDuhamelZgL_ev`, `stExpDuhamelQgL_ev` with rows 9-13; the semigroup law of `uKer` holds for every `d`
  (`BAuKerSemigroup_holds`, no `3 ≤ d`), so it is the body of the first conjunct of `baIniTermGen_kerFacts`, not that conjunct.
* **Target 9** `baStep6RegIII_of_pin`, `baStep6RegIV_of_pin`, `baStep6RegII_of_pin`: the bodies of `ST_step6_caseIII/IV/II_of_pinsgL` (`Step6KitGen:676, 715, 746`) per flow at BA
  with the cores `st6_caseIII/IV/II_coreg`; `hegt` from the glue `Step6BridgeBA_LW`, `hAvgU` from `baExpAvgUgL_of_tl1`; the three owed generic pins
  `STExpIntIIIgL`, `STExpIntIVgL`, `STExpWardIIgL` are hypotheses of merged type.  The regimes (i) are row b.
Names of the file stem `Step6PinsBA_`; no merged file is edited.
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

/-! ## 1. Target 6: `BAStep6R` -/

/-- **Target 6, `BAStep6R`** (= `T2510_Step6BA`; the one new public def; V2a's 1b reads it by name as `S6` of `T2503_RegShape`): the pin `STIngR6gL d R` at the BA tuple
`(fun sz => Sizes.seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)` (T2502's `STStep6RgL`, `Chain/Step6Gen:115`), with TL1 `BATwistAvgLaw` and TL2 `BATwistLoopLaw` at every
time sequence `u ∈ [s,t]` as the premise of the conclusion (probe `T2503_Step6BA`, `t/T2503` 93bd54cd `Probe/T2503Pins.lean:290`). -/
def BAStep6R (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  STIngR6gL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)
    (fun sz z s t => (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
      BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u ∧ BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u) →
      STStep6ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t)

/-! ## 2. Targets 7, 8: the merged producers at the BA tuple -/

section Pins

/-- The column sums of `S = 1` along every BA flow (row 20, `baSEforLnGen_facts`). -/
private theorem Step6PinsBA_cols (d : ℕ) :
    ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ (n : ℕ) (y : Zd d (sz.L n)), ∑ x : Zd d (sz.L n), ‖(baFMz sz z).S n x y‖ ≤ 1 := by
  intro sz κ ε 𝔠 𝔡 z hκ hf n y
  obtain ⟨-, -, -, -, -, -, hcol, -⟩ := baSEforLnGen_facts d sz κ ε 𝔠 𝔡 z hκ hf
  exact hcol n y

/-- `Aof κ = (κ+1)/κ ≥ 1` for `κ > 0` (row 16 / R1: `1 ≤ (κ+1)/κ`). -/
private theorem Step6PinsBA_Aof : ∀ κm : ℝ, 0 < κm → 1 ≤ (fun κ : ℝ => (κ + 1) / κ) κm := fun κm hκm => by
  change 1 ≤ (κm + 1) / κm
  rw [le_div_iff₀ hκm]; linarith

/-- **`(eq:Exp(L-K)1)` at BA** (`stExpLKLKHigL_of`; rows 1, 2, 9', 17, 20). -/
theorem baExpLKLKHigL (d : ℕ) :
    STExpLKLKHigL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) := by
  intro hd
  exact stExpLKLKHigL_of d _ _ _ _ (fun sz => Sizes.isProbabilityMeasure_seqP (sz.withLam 0)) (Step2EventsGenTw_baFlow d)
    (baIniTermGen_cltFlow d) (fun sz κ ε 𝔠 𝔡 z hκ hf => SEforLnBA_Kbound d hd sz κ ε 𝔠 𝔡 z hκ hf) (Step6PinsBA_cols d) hd

/-- **`(eq:Exp(L-K)2)`, `(eq:ExpLWn=2_smalleta)` at BA** (`stExpDriftLogL_of`; rows 1, 2, 9', 17, 20 and 19 eventually, `baKsol_oneLoop`). -/
theorem baExpDriftLogL (d : ℕ) :
    STExpDriftLogL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) := by
  intro hd
  exact stExpDriftLogL_of d _ _ _ _ (fun sz => Sizes.isProbabilityMeasure_seqP (sz.withLam 0)) (Step2EventsGenTw_baFlow d)
    (baIniTermGen_cltFlow d) (fun sz κ ε 𝔠 𝔡 z hκ hf => SEforLnBA_Kbound d hd sz κ ε 𝔠 𝔡 z hκ hf) (Step6PinsBA_cols d)
    (fun sz κ ε 𝔠 𝔡 z hκ hf => baKsol_oneLoop d sz κ ε 𝔠 𝔡 z hκ hf) hd

/-- **`(deccA0)` for the expected drift at BA** (`stExpDriftDecaygL_of`; as `baExpDriftLogL`, and row 18 through `Step6BridgeBA_decay`). -/
theorem baExpDriftDecaygL (d : ℕ) :
    STExpDriftDecaygL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) := by
  intro hd
  exact stExpDriftDecaygL_of d _ _ _ _ (fun sz => Sizes.isProbabilityMeasure_seqP (sz.withLam 0)) (Step2EventsGenTw_baFlow d)
    (baIniTermGen_cltFlow d) (fun sz κ ε 𝔠 𝔡 z hκ hf => SEforLnBA_Kbound d hd sz κ ε 𝔠 𝔡 z hκ hf) (Step6PinsBA_cols d)
    (fun sz κ ε 𝔠 𝔡 z hκ hf => baKsol_oneLoop d sz κ ε 𝔠 𝔡 z hκ hf) (Step6BridgeBA_decay d) hd

/-- **The primed Ward pin at BA** (`stExpWardIgL'_of`; same rows as `baExpWardIgL`). -/
theorem baExpWardIgL' (d : ℕ) :
    STExpWardIgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) :=
  stExpWardIgL'_of (fun sz => Sizes.isProbabilityMeasure_seqP (sz.withLam 0)) (baStep5CasesGen_flowFacts d)
    (fun sz κ ε 𝔠 𝔡 z _ _ => ⟨_, fun _ => 0, BAflowEs sz z, baCltRepg_holds sz z⟩) (baB45Gen_facts d)
    (fun sz κ ε 𝔠 𝔡 z hκ hf => baKsol_oneLoop d sz κ ε 𝔠 𝔡 z hκ hf)

/-- **The initial term of regime (i) at BA** (`stExpIniIgL'_of`; rows 1, 3, 9', 17, 16 and R1 through `baEKKer_flow` at `Aof κ = (κ+1)/κ`, `gK = g₀`). -/
theorem baExpIniIgL' (d : ℕ) :
    STExpIniIgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) := by
  intro hd
  exact stExpIniIgL'_of (Ker := @BAEKKer d) (Aof := fun κ => (κ + 1) / κ) (fun sz z => BAflowLam0 sz z)
    (fun sz => Sizes.isProbabilityMeasure_seqP (sz.withLam 0)) (baStep5CasesGen_flowFacts d) (baIniTermGen_cltFlow d)
    (fun sz κ ε 𝔠 𝔡 z hκ hf => SEforLnBA_Kbound d hd sz κ ε 𝔠 𝔡 z hκ hf) (baEKSumRes2NALgL_holds d) (baEKSumRes2gL_holds d)
    Step6PinsBA_Aof (baEKKer_flow d) hd

/-- **Regime (ii) integrated estimate at BA** (`stExpIntIIgL_of`; rows 1, 3, 6 and R1 through `baEKKer_flow`). -/
theorem baExpIntIIgL (d : ℕ) :
    STExpIntIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) :=
  stExpIntIIgL_of (Ker := @BAEKKer d) (Aof := fun κ => (κ + 1) / κ) (fun sz z => BAflowLam0 sz z)
    (fun sz => Sizes.isProbabilityMeasure_seqP (sz.withLam 0)) (baStep5CasesGen_flowFacts d) (baEKNonzerogL_holds d _)
    Step6PinsBA_Aof (baEKKer_flow d)

/-- The semigroup law of `uKer` at every size index along every BA flow, for every `d` (the body of the first conjunct of `baIniTermGen_kerFacts`, `Step5KerBA:172-177`;
that conjunct sits under `3 ≤ d`, the pins `STExpDuhamelZgL`, `STExpDuhamelQgL` carry no `3 ≤ d`: F5). -/
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

/-- The classes `KLoop`, `KTwo`, `KLink` eventually (rows 11-12, `baHierDrift_classes`). -/
private theorem Step6PinsBA_cls (d : ℕ) :
    ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, HierDriftGen_KLoop (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n ∧
        HierDriftGen_KTwo (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n ∧
        HierDriftGen_KLink (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n := by
  intro sz κ ε 𝔠 𝔡 z hκ hf
  obtain ⟨-, hLink, -, hev⟩ := baHierDrift_classes sz κ ε 𝔠 𝔡 z hκ hf
  exact hev.mono fun n hn => ⟨hn.1, hn.2.1, hLink n⟩

/-- **The plain and zero-mode Duhamel family at BA** (O5; `stExpDuhamelZgL_ev`, rows 9-13). -/
theorem baExpDuhamelZgL (d : ℕ) :
    STExpDuhamelZgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) :=
  stExpDuhamelZgL_ev _ _ _ (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => rfl) (Step6PinsBA_rep d)
    (Step6PinsBA_cls d) (fun sz κ ε 𝔠 𝔡 z hκ hf => Eventually.of_forall fun n => Step6PinsBA_USemigroup hκ hf n)

/-- **The `𝒬`-Duhamel family at BA** (O5; `stExpDuhamelQgL_ev`, rows 9-13). -/
theorem baExpDuhamelQgL (d : ℕ) :
    STExpDuhamelQgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) :=
  stExpDuhamelQgL_ev _ _ _ (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => rfl) (Step6PinsBA_rep d)
    (Step6PinsBA_cls d) (fun sz κ ε 𝔠 𝔡 z hκ hf => Eventually.of_forall fun n => Step6PinsBA_USemigroup hκ hf n)

end Pins

/-! ## 3. Target 9: the regimes (iii), (iv), (ii) from the three owed generic pins -/

section Regimes

/-- **Step 6, regime (iii), at BA from its one owed generic pin** (`baStep6RegIII_of_pin`, the body of `ST_step6_caseIII_of_pinsgL`, `Step6KitGen:676`): `STExpLKLKHigL`
(`baExpLKLKHigL`), the LW bound at every `u` (`Step6BridgeBA_LW`, TL1, TL2 from the `Concl` slot), the Duhamel family (`baExpDuhamelZgL`), the pin `STExpIntIIIgL` (a hypothesis of
merged type) and the initial term `st6_ini_sumNdecayg` with rows 5 (`baEKSumNdecaygL_holds`) and `baEKKer_flow`; `𝔠d = min` of the two pins' constants. -/
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

/-- **Step 6, regime (iv), at BA from its one owed generic pin** (`baStep6RegIV_of_pin`, the body of `ST_step6_caseIV_of_pinsgL`, `Step6KitGen:715`): `STExpDriftLogL`
(`baExpDriftLogL`), whose premise `(res_ELK_n=1)` is `baExpAvgUgL_of_tl1` (TL1 on `[s,t]` from the `Concl` slot), the Duhamel family, the pin `STExpIntIVgL` and the initial term. -/
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

/-- **Step 6, regime (ii), at BA from its one owed generic pin** (`baStep6RegII_of_pin`, the body of `ST_step6_caseII_of_pinsgL`, `Step6KitGen:746`): `STExpLKLKHigL`, the LW bound at
every `u`, `baExpAvgUgL_of_tl1`, the Duhamel family, `STExpIntIIgL` (`baExpIntIIgL`), the Ward decomposition `STExpWardIIgL` (a hypothesis of merged type) and the two initial
terms `st6_ini_nonzerog` with row 6 (`baEKNonzerogL_holds`), R1 from `baEKKer_flow` at `Aof κ = (κ+1)/κ`. -/
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

/-! ## 4. Compiled nonempty instances (target 10)

`d = 3`.  Data for target 7 (regimes), as `STIngR6gL` reads them: the flow, `0 ≤ s < t ≤ T₀`, the regime `R sz s t`, `(con_st_ind)` at every `𝔠_d > 0`.
* `(sz0, zSeq, flow_sz0)` (`BA/FlowPins.lean:1214`), `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, `s ≡ 1/2 < t ≡ 3/5 ≤ 2/3 ≤ T₀`: regimes `STDriftHi`, `STReg5III` (`lam² ≤ 1 - t`).
* Regimes (i), (ii), (iv) are empty at `sz0` (`1 - s ≥ 1/3 > lam²`; `TwistStep2_no_caseII_sz0`), so they run at the parametrised private datum of `BA/Step5CasesBA.lean` (read by `open private`;
  `L_n ≡ L`, `lam_n ≡ lam`, `W_n = n + W₀`, `w = (5003/5000) i`, `(ε, 𝔠, 𝔡) = (1/2, 1/9, 1/10)`, `s ≡ 0`): (i) `(L, W₀, lam, κ, t) = (4, 25, 2, 3/1000, 1/400)`, (ii) `(4, 25, 5, 3/5000, 1/2000)`,
  (iv) `(3, 40, 6, 1/1000, 1/2000)`.
* The seven stochastic premises of `STIngR6gL` (`STLKgL`, `STDecaygL`, `STExp2gL` at `s`; `STStep2CoregL`, `STLmaxUgL`, `STLKUgL`, `STGdecayWgL … 0` on `[s,t]`) are other gates' pins and stay hypotheses
  (`Step6PinsBA_prem`), as do the premises that the three owed generic pins and TL1, TL2 carry. -/

end RBM.BA

end
