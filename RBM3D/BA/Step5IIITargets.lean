/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.Step5IIIWalk2
import RBM3D.BA.SEforLnBA
import RBM3D.Chain.Step5CasesGen

/-!
# U5e: the targets of BA case (iii) of Step 5

Ticket T2499.  Paper: `lem:pf_step5` (`3_5:2364-2383`) and Step 5 case `1 - t ≥ λ²` (`sec:Step5_larget`, `3_5:2284`);
BA `7_8:2101` ("we therefore omit the details", paper-delta candidate T2459a).  Band twins (not edited): `stPfStep5_holds`
(`Induction/PfStep5.lean:2457`), `stStep5III_holds` (`:2473`).  The check is `docs/tickets/checks/T2499-check.lean`.

A composition of merged results, `d = 3` at the instances (U-C5):

* 1. `baPfStep5_of_walk` (= `T2499_MainOfParts`): the two U5d texts `BAStep5IIIWalk`, `BAStep5IIIFromWalk` give `STPfStep5gL`.
* 2. `baPfStep5_holds` (= `T2499_STPfStep5BA`, U6 target 10 at BA): target 1 at `baStep5IIIWalk_holds`, `baStep5IIIFromWalk_holds`.
* 3. `baStep5III_holds` (= `T2499_STStep5IIIBA`, U6 target 9 at BA): `ST_step5_caseIII_of_pfgL` with `baStep5CasesGen_flowFacts`.
* 4. Compiled nonempty instances at `d = 3` (section 2).

Tuple: `(fun sz => seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`.  Helpers carry the stem `Step5IIITargets_`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The targets -/

/-- **Target 1** (`T2499_MainOfParts`): `lem:pf_step5` at the BA tuple from the stopped grid walk and the lift
(`𝔠d = 1/100` from the walk; the lift at the walk's grid conclusion). -/
theorem baPfStep5_of_walk :
    BAStep5IIIWalk → BAStep5IIIFromWalk →
      STPfStep5gL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := by
  intro walk fromWalk hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h0, h1, H⟩ := walk hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨𝔠d, h0, h1, fun 𝔠 sz z hflow s t hs hst ht hR hKb hKw hLK hDec hDecS hcon hS1 hS2 hLmax hLKU => ?_⟩
  exact fromWalk κ ε 𝔠 𝔡 sz z hκ hε h𝔡 hflow s t hs hst ht hR
    (H 𝔠 sz z hflow s t hs hst ht hR hKb hKw hLK hDec hDecS hcon hS1 hS2 hLmax hLKU)

/-- **Target 2** (`T2499_STPfStep5BA`; U6 target 10 at BA): `lem:pf_step5` (`3_5:2364-2383`) at the BA tuple, `d = 3`. -/
theorem baPfStep5_holds :
    STPfStep5gL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
  baPfStep5_of_walk baStep5IIIWalk_holds baStep5IIIFromWalk_holds

/-- **Target 3** (`T2499_STStep5IIIBA`; U6 target 9 at BA): Step 5 in case (iii) (`lam² ≤ 1 - t`) at the BA tuple, `d = 3`. -/
theorem baStep5III_holds :
    STStep5IIIgL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
  ST_step5_caseIII_of_pfgL 3 _ _ _ _ (baStep5CasesGen_flowFacts 3) baPfStep5_holds

/-! ## 2. Compiled nonempty instances at `d = 3` (target 4)

`sz0`, `zSeq`, `flow_sz0` with `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, `s ≡ 1/10 < t ≡ 1/2 < t₀` (`half_lt_t0`), `Cd = 1`.  The regime
(`Step5IIIGood_reg_sz0`) and `(con_st_ind)` (`s1Setup_conStInd_const`) are discharged; the nine carrier predicates of `STIngR5gL` (other gates'
pins) stay hypotheses, as in `BA/Step5IIIWalk2.lean` section 7. -/

end RBM.BA
