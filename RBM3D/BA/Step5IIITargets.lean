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

A composition of merged results, at every `d` (`baStep5III_holds_any`: `3 ≤ d`; ticket T2533, BA-D row R1):

* 1. `baPfStep5_of_walk` (= `T2499_MainOfParts`): the two U5d texts `BAStep5IIIWalk`, `BAStep5IIIFromWalk` give `STPfStep5gL`.
* 2. `baPfStep5_holds` (= `T2499_STPfStep5BA`, U6 target 10 at BA): target 1 at `baStep5IIIWalk_holds`, `baStep5IIIFromWalk_holds`.
* 3. `baStep5III_holds_any` (= `T2499_STStep5IIIBA`, U6 target 9 at BA, every `d ≥ 3`): `ST_step5_caseIII_of_pfgL` with `baStep5CasesGen_flowFacts`;
  `baStep5III_holds` is its `d = 3` instance (one line).
* 4. A compiled instance of target 3 at `d = 4` (section 2).

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
theorem baPfStep5_of_walk (d : ℕ) :
    BAStep5IIIWalk d → BAStep5IIIFromWalk d →
      STPfStep5gL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := by
  intro walk fromWalk hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h0, h1, H⟩ := walk hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨𝔠d, h0, h1, fun 𝔠 sz z hflow s t hs hst ht hR hKb hKw hLK hDec hDecS hcon hS1 hS2 hLmax hLKU => ?_⟩
  exact fromWalk hd κ ε 𝔠 𝔡 sz z hκ hε h𝔡 hflow s t hs hst ht hR
    (H 𝔠 sz z hflow s t hs hst ht hR hKb hKw hLK hDec hDecS hcon hS1 hS2 hLmax hLKU)

/-- **Target 2** (`T2499_STPfStep5BA`; U6 target 10 at BA): `lem:pf_step5` (`3_5:2364-2383`) at the BA tuple, at every `d`. -/
theorem baPfStep5_holds (d : ℕ) :
    STPfStep5gL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
  baPfStep5_of_walk d (baStep5IIIWalk_holds d) (baStep5IIIFromWalk_holds d)

/-- **Target 3** (`T2499_STStep5IIIBA`; U6 target 9 at BA): Step 5 in case (iii) (`lam² ≤ 1 - t`) at the BA tuple, at every `d ≥ 3` (no premise beyond `3 ≤ d`). -/
theorem baStep5III_holds_any (d : ℕ) (hd : 3 ≤ d) :
    STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
  ST_step5_caseIII_of_pfgL d _ _ _ _ (baStep5CasesGen_flowFacts d) (baPfStep5_holds d)

/-- Step 5 in case (iii) at the BA tuple at `d = 3`: the one-line corollary of `baStep5III_holds_any` (kept with its type; read by `MainIndFamTL`, `MainIndTermBA`, `MainIndRegBA`, `UNBUniv`). -/
theorem baStep5III_holds :
    STStep5IIIgL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
  baStep5III_holds_any 3 le_rfl

/-! ## 2. Compiled instance of the target at `d = 4`

The first dimension that the `d = 3` theorem does not cover: `baStep5III_holds_any 4` with its only hypothesis `3 ≤ 4` discharged.  The
data-level instances (`Sizes 4`, the flow) belong to the assembly row (ticket T2533, R2). -/

/-- The target at `d = 4`: no premise beyond `3 ≤ 4`. -/
example :
    STStep5IIIgL 4 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
  baStep5III_holds_any 4 (by norm_num)

end RBM.BA
