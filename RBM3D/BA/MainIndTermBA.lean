/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.MainIndRegBA
import RBM3D.BA.MainIndGlue

/-!
# The block Anderson general-`d` step

The four regime steps of `BA/MainIndRegBA` enter the regime glue
`baMainIndFamTL_of_regimes` (`BA/MainIndGlue`) in its binder order (iii), (i), (ii), (iv).
Every theorem below is a composition of existing theorems.

* `baMainIndFamTL_any`: `∀ d, STStep5IIIgL d … → BAMainIndFamTL d STAny`; the hypothesis `STStep5IIIgL d …` is regime (iii) of Step 5 in dimension `d`.
  It is supplied at `d = 3` by `baStep5III_holds` and at every `d ≥ 3` by `baStep5III_holds_any` (`BA/Step5IIITargets`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The general-`d` step at `STAny` -/

/-- `baMainIndFamTL_any`: the family step at `STAny` for every `d` under Step 5 (iii) `STStep5IIIgL d` as a hypothesis;
`BAMainIndFamTL d STAny` starts `3 ≤ d →`.  At `d = 3` the hypothesis is `baStep5III_holds`; for every `d ≥ 3` it is `baStep5III_holds_any`. -/
theorem baMainIndFamTL_any : ∀ d : ℕ,
    STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) → BAMainIndFamTL d STAny :=
  fun d h5 => baMainIndFamTL_of_regimes d (baMainIndFamTL_III d h5) (baMainIndFamTL_I d) (baMainIndFamTL_II d) (baMainIndFamTL_IV d)

end RBM.BA

end
