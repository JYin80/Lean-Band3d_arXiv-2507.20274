/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.Step6PinsBA
import RBM3D.Chain.ExpWardIIGen
import RBM3D.Chain.ExpIntEasyGen
import RBM3D.Chain.ExpIntIGen
import RBM3D.Chain.ExpIntIQGen
import RBM3D.BA.Step5CasesBA

/-!
# Step 6 of `lem:main_ind` at the block Anderson tuple: the four regimes

Step 6 of Theorem 2.24 (`lem:main_ind`) (Section 6, `Sec:Step6`) at the BA tuple
`(fun sz => Sizes.seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`, `gK = BAflowLam0`, `κm = κ`, `Aof κ = (κ+1)/κ`.  No new mathematics: the producers
`stExpWardIIgL_of`, `stExpIntIIIgL_of`, `stExpIntIVgL_of`, `stExpIntIgL'_of` are read by name at the BA discharges of the family statements, and the four regimes
`BAStep6R d R` (`BA/Step6PinsBA`) are assembled from them and the statements of `BA/Step6PinsBA`.

* `baExpWardIIgL`, `baExpIntIIIgL`, `baExpIntIVgL`: regimes (ii), (iii), (iv) at the BA tuple.
* `baExpIntIgL'`: the primed integrated statement of regime (i) at the BA tuple.
* `baStep6RegI_of_pins`: the body of `ST_step6_caseI_of_pins''` per flow at BA with `st6_caseI_coreg'` (`Chain/ExpIntIGen`), the primed statements of `BA/Step6PinsBA`, the
  per-flow average `baExpAvgUgL_of_tl1` and the LW glue `Step6BridgeBA_LW`; no `STImproveExpAver`, no every-`n` `hK1`, no `LWtermEXP`.
* `baStep6RegIII_holds`, `baStep6RegI_holds`, `baStep6RegII_holds`, `baStep6RegIV_holds`: `BAStep6R d R` for the four regimes, every `d`.

Names of the file stem `Step6BA_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open private SEforLnBA_Kbound from RBM3D.BA.SEforLnBA
open private Step6BridgeBA_LW from RBM3D.BA.Step6BridgeBA
open private Step6PinsBA_Aof from RBM3D.BA.Step6PinsBA
open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The integrated statements of regimes (ii), (iii), (iv) at the BA tuple -/

section Row11

/-- The first three conjuncts of `baEKKer_flow` (`hKer` of `stExpIntIIIgL_of`, `stExpIntIVgL_of`; the fourth conjunct is the coupling comparison, read by regime (i)). -/
private theorem Step6BA_Ker3 (d : ℕ) : ∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, 0 < κm ∧ ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    (∀ n, κm ≤ ((baFMz sz z).m n).im) ∧ @BAEKKer d sz (baFMz sz z) (BAflowLam0 sz z) κm ∧
      ∀ᶠ n in atTop, 0 < BAflowLam0 sz z n ∧ BAflowLam0 sz z n ≤ 𝔡⁻¹ := by
  intro κ hκ
  obtain ⟨κm, hκm, H⟩ := baEKKer_flow d κ hκ
  exact ⟨κm, hκm, fun sz ε 𝔠 𝔡 z hf => by
    obtain ⟨h1, h2, h3, -⟩ := H sz ε 𝔠 𝔡 z hf
    exact ⟨h1, h2, h3⟩⟩

/-- Regime (ii) Ward decomposition at BA (`stExpWardIIgL_of` with `baStep5CasesGen_flowFacts`, `baCltRepg_holds`, `baKsol_oneLoop`, `baStep5CasesGen_wardIdent`, `baB45Gen_facts`). -/
theorem baExpWardIIgL (d : ℕ) :
    STExpWardIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) :=
  stExpWardIIgL_of (fun sz => Sizes.isProbabilityMeasure_seqP (sz.withLam 0)) (baStep5CasesGen_flowFacts d)
    (fun sz κ ε 𝔠 𝔡 z _ _ => ⟨_, fun _ => 0, BAflowEs sz z, baCltRepg_holds sz z⟩)
    (fun sz κ ε 𝔠 𝔡 z hκ hf => baKsol_oneLoop d sz κ ε 𝔠 𝔡 z hκ hf) (baStep5CasesGen_wardIdent d) (baB45Gen_facts d)

/-- Regime (iii) integrated estimate at BA (`stExpIntIIIgL_of` with `baStep5CasesGen_flowFacts`, `baEKSumNdecaygL_holds` and the kernel data `baEKKer_flow`). -/
theorem baExpIntIIIgL (d : ℕ) :
    STExpIntIIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) :=
  stExpIntIIIgL_of (Ker := @BAEKKer d) (fun sz z => BAflowLam0 sz z) (fun sz => Sizes.isProbabilityMeasure_seqP (sz.withLam 0))
    (baStep5CasesGen_flowFacts d) (baEKSumNdecaygL_holds d) (Step6BA_Ker3 d)

/-- Regime (iv) integrated estimate at BA (`stExpIntIVgL_of`; the same inputs as `baExpIntIIIgL`). -/
theorem baExpIntIVgL (d : ℕ) :
    STExpIntIVgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) :=
  stExpIntIVgL_of (Ker := @BAEKKer d) (fun sz z => BAflowLam0 sz z) (fun sz => Sizes.isProbabilityMeasure_seqP (sz.withLam 0))
    (baStep5CasesGen_flowFacts d) (baEKSumNdecaygL_holds d) (Step6BA_Ker3 d)

end Row11

/-! ## 2. The primed integrated statement of regime (i) -/

/-- Regime (i) integrated estimate at BA (`stExpIntIgL'_of` with `baStep5CasesGen_flowFacts`, `baIniTermGen_cltFlow`, `SEforLnBA_Kbound` (after `hd`), `baEKSumRes2NALgL_holds`,
`baEKSumRes2gL_holds`, the coupling comparison `baEKKer_flow` at `Aof κ = (κ+1)/κ`, `baStep5KerGen_thDecay` (the binders `(κ, 𝔡)` swapped to `(𝔡, κ)`), `baB45Gen_facts` and the
`𝒬`-Duhamel family `baExpDuhamelQgL`). -/
theorem baExpIntIgL' (d : ℕ) :
    STExpIntIgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) := by
  intro hd
  exact stExpIntIgL'_of (Ker := @BAEKKer d) (Aof := fun κ => (κ + 1) / κ) (fun sz z => BAflowLam0 sz z)
    (fun sz => Sizes.isProbabilityMeasure_seqP (sz.withLam 0)) (baStep5CasesGen_flowFacts d) (baIniTermGen_cltFlow d)
    (fun sz κ ε 𝔠 𝔡 z hκ hf => SEforLnBA_Kbound d hd sz κ ε 𝔠 𝔡 z hκ hf) (baEKSumRes2NALgL_holds d) (baEKSumRes2gL_holds d)
    Step6PinsBA_Aof (baEKKer_flow d) (fun 𝔡 h𝔡 κ hκ => baStep5KerGen_thDecay d hd κ 𝔡 hκ h𝔡) (baB45Gen_facts d) (baExpDuhamelQgL d) hd

/-! ## 3. Regime (i) -/

/-- Step 6, regime (i), at BA from the primed integrated statement (`baStep6RegI_of_pins`, the body of `ST_step6_caseI_of_pins''` per flow at BA): `STExpLKLKHigL`
(`baExpLKLKHigL`), the LW bound at every `u` (`Step6BridgeBA_LW`, TL1, TL2 from the `Concl` slot), `STExpDriftDecaygL` (`baExpDriftDecaygL`), the primed Ward statement (`baExpWardIgL'`) and initial
term (`baExpIniIgL'`), the primed integrated statement `STExpIntIgL'` (a hypothesis), the Duhamel families (`baExpDuhamelZgL`, `baExpDuhamelQgL`) and the per-flow average
`baExpAvgUgL_of_tl1` (TL1 on `[s,t]`); the core is `st6_caseI_coreg'`.  `𝔠d = min` of the five constants. -/
theorem baStep6RegI_of_pins (d : ℕ) :
    STExpIntIgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) → BAStep6R d STReg5I := by
  intro hInt hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := baExpLKLKHigL d hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₂, hc₂, hc₂', H₂⟩ := baExpDriftDecaygL d hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₃, hc₃, hc₃', H₃⟩ := baExpWardIgL' d hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₄, hc₄, hc₄', H₄⟩ := baExpIniIgL' d hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₅, hc₅, hc₅', H₅⟩ := hInt hd κ ε 𝔡 hκ hε h𝔡
  have hcpos : 0 < min c₁ (min c₂ (min c₃ (min c₄ c₅))) :=
    lt_min hc₁ (lt_min hc₂ (lt_min hc₃ (lt_min hc₄ hc₅)))
  refine ⟨min c₁ (min c₂ (min c₃ (min c₄ c₅))), hcpos, (min_le_left _ _).trans hc₁', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hcon hS2 hLmax hLKU hS5 hTL
  have hadm : sz.Admissible 𝔠 𝔡 := hflow.1
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  have m : ∀ c', min c₁ (min c₂ (min c₃ (min c₄ c₅))) ≤ c' → STConStInd sz c' s t :=
    fun c' hcc => st5_conStInd_mono sz hcon ht1 hcpos hcc
  have hm1 := m c₁ (min_le_left _ _)
  have hm2 := m c₂ ((min_le_right _ _).trans (min_le_left _ _))
  have hm3 := m c₃ ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hm4 := m c₄ ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hm5 := m c₅ ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hHi := st6_hi_of_reg5I sz (by omega) hR
  have hAvgU := baExpAvgUgL_of_tl1 d hd κ ε 𝔠 𝔡 hκ hε h𝔡 sz z hflow s t hs0 hst htT hS2 hLKU
    (fun u hsu hut => (hTL u hsu hut).1)
  have hlk := H₁ 𝔠 sz z hflow s t hs0 hst htT hHi hLK0 hDec0 hExp hm1 hS2 hLmax hLKU hS5
  have hegt := st6_EGtHi_of_LWg (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t (Sizes.isProbabilityMeasure_seqP (sz.withLam 0))
    hadm.2.2.1 (fun n => (hst n).le) hHi (Step2EventsGenTw_baRot3 sz _ _)
    (Step6BridgeBA_LW d hd hκ hε h𝔡 hflow hs0 htT hS2 hLmax hLKU hS5 hTL)
  have hdec := H₂ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hm2 hS2 hLmax hLKU hS5
  have hward := H₃ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hm3 hS2 hLmax hLKU hS5
  have hini := H₄ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hm4 hS2 hLmax hLKU hS5
  have hduh := st6_duhEq_of_ping (baExpDuhamelZgL d) hκ hflow hs0 ht1
  have hint := H₅ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hm5 hS2 hLmax hLKU hS5
  exact st6_caseI_coreg' (baFMz sz z) (Sizes.seqP (sz.withLam 0)) hd h𝔡 hadm hs0 hst ht1 hR hlk hegt hdec hAvgU hward hini hduh
    (fun Cq c ϑ hϑ => st6_duhEqQ_of_ping (baExpDuhamelQgL d) hκ hflow hs0 ht1 Cq c ϑ hϑ) hint

/-! ## 4. `BAStep6R d R` for the four regimes -/

/-- Step 6 of Theorem 2.24 at BA, regime (iii) (`baStep6RegIII_of_pin` with `baExpIntIIIgL`). -/
theorem baStep6RegIII_holds (d : ℕ) : BAStep6R d STReg5III := baStep6RegIII_of_pin d (baExpIntIIIgL d)

/-- Step 6 at BA, regime (i) (`baStep6RegI_of_pins` with `baExpIntIgL'`). -/
theorem baStep6RegI_holds (d : ℕ) : BAStep6R d STReg5I := baStep6RegI_of_pins d (baExpIntIgL' d)

/-- Step 6 at BA, regime (ii) (`baStep6RegII_of_pin` with `baExpWardIIgL`). -/
theorem baStep6RegII_holds (d : ℕ) : BAStep6R d STReg5II := baStep6RegII_of_pin d (baExpWardIIgL d)

/-- Step 6 at BA, regime (iv) (`baStep6RegIV_of_pin` with `baExpIntIVgL`). -/
theorem baStep6RegIV_holds (d : ℕ) : BAStep6R d STReg5IV := baStep6RegIV_of_pin d (baExpIntIVgL d)

end RBM.BA

end
