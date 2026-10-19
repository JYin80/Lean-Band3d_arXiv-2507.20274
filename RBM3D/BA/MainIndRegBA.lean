/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.MainIndFamTL
import RBM3D.BA.Step6BA

/-!
# The four regimes of the block Anderson main induction

`BAMainIndFamTL d R` (`BA/MainIndOutBA`) for the four regimes `R ∈ {STReg5III, STReg5I, STReg5II, STReg5IV}`: the regime theorems of `BA/MainIndFamTL` with the
Step-6 closures (`baStep6RegIII_holds` .. `baStep6RegIV_holds`, `BA/Step6BA`) as the Step-6 hypothesis, by unfolding of `BAStep6R` (`BA/Step6PinsBA`).
The bridge of the generic step is `fun _ _ _ _ h c => c h`.

* `baMainIndFamTL_III`: regime (iii) for every `d`, with Step 5 (iii) `STStep5IIIgL d …` as a hypothesis; `baStep5III_holds_any` (`BA/Step5IIITargets`) supplies it for every `d ≥ 3`.
* `baMainIndFamTL_I`, `baMainIndFamTL_II`, `baMainIndFamTL_IV`: regimes (i), (ii), (iv) for every `d`, unconditional (`baStep5I_holds`, `baStep5II_holds`, `baStep5IV_holds`, `BA/Step5CasesBA`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The four regimes -/

/-- `baMainIndFamTL_III`: `lem:main_ind_BA` in family form with TL2 in regime (iii), every `d`, with Step 5 (iii) (`STStep5IIIgL`) as the hypothesis; Step 6 is `baStep6RegIII_holds`. -/
theorem baMainIndFamTL_III : ∀ d : ℕ,
    STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) → BAMainIndFamTL d STReg5III :=
  fun d h5 => baMainIndFamTL_III_of d h5 _ (baStep6RegIII_holds d) (fun _ _ _ _ h c => c h)

/-- `baMainIndFamTL_I`: regime (i), every `d`, unconditional (`baStep5I_holds`, `baStep6RegI_holds`). -/
theorem baMainIndFamTL_I : ∀ d : ℕ, BAMainIndFamTL d STReg5I :=
  fun d => baMainIndFamTL_I_of d _ (baStep6RegI_holds d) (fun _ _ _ _ h c => c h)

/-- `baMainIndFamTL_II`: regime (ii), every `d`, unconditional (`baStep5II_holds`, `baStep6RegII_holds`). -/
theorem baMainIndFamTL_II : ∀ d : ℕ, BAMainIndFamTL d STReg5II :=
  fun d => baMainIndFamTL_II_of d _ (baStep6RegII_holds d) (fun _ _ _ _ h c => c h)

/-- `baMainIndFamTL_IV`: regime (iv), every `d`, unconditional (`baStep5IV_holds`, `baStep6RegIV_holds`). -/
theorem baMainIndFamTL_IV : ∀ d : ℕ, BAMainIndFamTL d STReg5IV :=
  fun d => baMainIndFamTL_IV_of d _ (baStep6RegIV_holds d) (fun _ _ _ _ h c => c h)

end RBM.BA

end
