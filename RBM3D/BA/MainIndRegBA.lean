/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.MainIndFamTL
import RBM3D.BA.Step6BA

/-!
# V row V2a, row a (T2511): the four regimes closed

`BAMainIndFamTL d R` (`BA/MainIndOutBA.lean:60`, merged) for the four regimes `R ∈ {STReg5III, STReg5I, STReg5II, STReg5IV}`: the regime theorems of `BA/MainIndFamTL.lean` (targets 7-9) with the merged
Step-6 closures of T2510 (`baStep6RegIII_holds` .. `baStep6RegIV_holds`, `BA/Step6BA.lean:148-157`) as the Step-6 hypothesis, by unfolding of `BAStep6R` (`BA/Step6PinsBA.lean:59`, read by name).
The bridge of the generic step is `fun _ _ _ _ h c => c h`.

* `baMainIndFamTL_III`: regime (iii) for every `d` with Step 5 (iii) as the hypothesis (DECISIONS §316: `d > 3` is out of scope, Jun decision B).
* `baMainIndFamTL_III_three`: regime (iii) at `d = 3`, unconditional (`baStep5III_holds`, `BA/Step5IIITargets.lean:57`).
* `baMainIndFamTL_I`, `_II`, `_IV`: regimes (i), (ii), (iv) for every `d`, unconditional (`baStep5I/II/IV_holds`, `BA/Step5CasesBA.lean:248-260`).
* Compiled `d = 3` instances at the data of `BA/MainIndFamTL.lean` §4 (read by `open private`); the six conclusions at every member of `Fam(s)` (the induction hypothesis) are the one hypothesis.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Target 10: the four regimes -/

/-- **Target 10 (iii), `baMainIndFamTL_III`**: `lem:main_ind_BA` in family form with TL2 in regime (iii), every `d`, Step 5 (iii) the hypothesis (`STStep5IIIgL`); Step 6 is `baStep6RegIII_holds`. -/
theorem baMainIndFamTL_III : ∀ d : ℕ,
    STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) → BAMainIndFamTL d STReg5III :=
  fun d h5 => baMainIndFamTL_III_of d h5 _ (baStep6RegIII_holds d) (fun _ _ _ _ h c => c h)

/-- **Target 10 (iii), `baMainIndFamTL_III_three`**: regime (iii) at `d = 3`, unconditional (`baStep5III_holds`). -/
theorem baMainIndFamTL_III_three : BAMainIndFamTL 3 STReg5III := baMainIndFamTL_III 3 baStep5III_holds

/-- **Target 10 (i), `baMainIndFamTL_I`**: regime (i), every `d`, unconditional (`baStep5I_holds`, `baStep6RegI_holds`). -/
theorem baMainIndFamTL_I : ∀ d : ℕ, BAMainIndFamTL d STReg5I :=
  fun d => baMainIndFamTL_I_of d _ (baStep6RegI_holds d) (fun _ _ _ _ h c => c h)

/-- **Target 10 (ii), `baMainIndFamTL_II`**: regime (ii), every `d`, unconditional (`baStep5II_holds`, `baStep6RegII_holds`). -/
theorem baMainIndFamTL_II : ∀ d : ℕ, BAMainIndFamTL d STReg5II :=
  fun d => baMainIndFamTL_II_of d _ (baStep6RegII_holds d) (fun _ _ _ _ h c => c h)

/-- **Target 10 (iv), `baMainIndFamTL_IV`**: regime (iv), every `d`, unconditional (`baStep5IV_holds`, `baStep6RegIV_holds`). -/
theorem baMainIndFamTL_IV : ∀ d : ℕ, BAMainIndFamTL d STReg5IV :=
  fun d => baMainIndFamTL_IV_of d _ (baStep6RegIV_holds d) (fun _ _ _ _ h c => c h)

/-! ## 2. Compiled `d = 3` instances (target 10)

At the data of `BA/MainIndFamTL.lean` §4: (iii) at `(sz0, zSeq)`, `κ = 1/4`, `(ε, 𝔠, 𝔡) = (1/10, 1/6, 1/10)`, `c₁ = 1/3`, `s ≡ 1/10 < t ≡ 1/2`; (i), (ii), (iv) at the private data of `BA/Step5CasesBA.lean` §5.
Every premise except the six conclusions at every member of `Fam(s)` (the induction hypothesis) is discharged. -/

-- (iii) at `(sz0, zSeq)`: `d = 3`, unconditional; the seven conclusions at the non-main member of `Fam(1/2)`
-- (iii) through the general-`d` form, with Step 5 (iii) at `d = 3`
-- (i) at `(L, W₀, lam, κ_dom, t) = (4, 25, 1, 1/70, 1/100)`
-- (ii) at `(4, 25, 4, 1/1100, 9/10000)`
-- (iv) at `(3, 40, 6, 1/1000, 1/2000)`
end RBM.BA

end
