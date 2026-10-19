/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.Step5IIIWalk2
import RBM3D.BA.SEforLnBA
import RBM3D.Chain.Step5CasesGen

/-!
# Step 5, case `1 - t ≥ λ²`, for the block Anderson model at every `d ≥ 3`

Paper: Lemma 5.4 (`lem:pf_step5`) in Subsection 5.3 (`sec:Step5_larget`), and its extension to the
block Anderson model in the proof of Steps 3-6 for Theorem 8.2 (`lem:main_ind_BA`), where the
details are omitted.  The band-model counterparts are `stPfStep5_holds` and `stStep5III_holds`.

This file assembles the stopped grid walk and its lift into Step 5 in case (iii) (`lam² ≤ 1 - t`)
over the block Anderson tuple `(fun sz => seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`, at every
`d ≥ 3`:

* `baPfStep5_of_walk`: the two statements `BAStep5IIIWalk`, `BAStep5IIIFromWalk` give `STPfStep5gL`;
* `baPfStep5_holds`: `STPfStep5gL` (Lemma 5.4 at the block Anderson tuple), from
  `baStep5IIIWalk_holds` and `baStep5IIIFromWalk_holds`;
* `baStep5III_holds_any`: `STStep5IIIgL` for every `d ≥ 3`, by `ST_step5_caseIII_of_pfgL` with
  `baStep5CasesGen_flowFacts`; `baStep5III_holds` is its `d = 3` case (one line);
* an instance of `baStep5III_holds_any` at `d = 4` (section 2).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Lemma 5.4 and Step 5, case (iii), at the block Anderson tuple -/

/-- Lemma 5.4 (`lem:pf_step5`) at the block Anderson tuple from the stopped grid walk and the lift
(`𝔠d = 1/100` from the walk; the lift at the walk's grid conclusion). -/
theorem baPfStep5_of_walk (d : ℕ) :
    BAStep5IIIWalk d → BAStep5IIIFromWalk d →
      STPfStep5gL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := by
  intro walk fromWalk hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h0, h1, H⟩ := walk hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨𝔠d, h0, h1, fun 𝔠 sz z hflow s t hs hst ht hR hKb hKw hLK hDec hDecS hcon hS1 hS2 hLmax hLKU => ?_⟩
  exact fromWalk hd κ ε 𝔠 𝔡 sz z hκ hε h𝔡 hflow s t hs hst ht hR
    (H 𝔠 sz z hflow s t hs hst ht hR hKb hKw hLK hDec hDecS hcon hS1 hS2 hLmax hLKU)

/-- Lemma 5.4 (`lem:pf_step5`) at the block Anderson tuple, at every `d`. -/
theorem baPfStep5_holds (d : ℕ) :
    STPfStep5gL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
  baPfStep5_of_walk d (baStep5IIIWalk_holds d) (baStep5IIIFromWalk_holds d)

/-- Step 5 in case (iii) (`lam² ≤ 1 - t`) at the block Anderson tuple, at every `d ≥ 3` (no premise beyond `3 ≤ d`). -/
theorem baStep5III_holds_any (d : ℕ) (hd : 3 ≤ d) :
    STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
  ST_step5_caseIII_of_pfgL d _ _ _ _ (baStep5CasesGen_flowFacts d) (baPfStep5_holds d)

/-- Step 5 in case (iii) at the block Anderson tuple at `d = 3`: the `d = 3` case of `baStep5III_holds_any`. -/
theorem baStep5III_holds :
    STStep5IIIgL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
  baStep5III_holds_any 3 le_rfl

/-! ## 2. An instance at `d = 4`

`baStep5III_holds_any 4` with its only hypothesis `3 ≤ 4` discharged. -/

/-- Step 5 in case (iii) at `d = 4`: no premise beyond `3 ≤ 4`. -/
example :
    STStep5IIIgL 4 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
  baStep5III_holds_any 4 (by norm_num)

end RBM.BA
