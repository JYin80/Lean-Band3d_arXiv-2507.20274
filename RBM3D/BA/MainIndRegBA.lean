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

section Inst

open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst RBM.BA.Step1FamInst
open private MainIndOutBA_flow MainIndOutBA_win MainIndOutBA_mem from RBM3D.BA.MainIndOutBA
open private MainIndFamTL_atSz0 MainIndFamTL_atDatum from RBM3D.BA.MainIndFamTL
open private Step5CasesBA_szI Step5CasesBA_zI Step5CasesBA_szII Step5CasesBA_zII Step5CasesBA_szIV Step5CasesBA_zIV Step5CasesBA_sz
  Step5CasesBA_datI Step5CasesBA_datII Step5CasesBA_datIV Step5CasesBA_regI Step5CasesBA_regII Step5CasesBA_regIV from RBM3D.BA.Step5CasesBA
local notation "μ0" => Sizes.seqP (sz0.withLam 0)
local notation "mem0" => BAzSrc sz0 zSeq (fun _ => 2 / 3) (fun _ => 17 / 25)
local notation "Fam6" "(" C ", " μ ", " s ")" =>
  STLKgL C μ s ∧ STDecaygL C μ s ∧ STDecayStronggL C μ s ∧ STLocalMaxgL C μ s ∧ STExp2gL C μ s ∧ BATwistLoopLaw C μ s
local notation "Fam7" "(" C ", " μ ", " t ")" =>
  STLKgL C μ t ∧ STLmaxgL C μ t ∧ STDecaygL C μ t ∧ STExp2gL C μ t ∧ STLocalEntrygL C μ t ∧ STDecayStronggL C μ t ∧ BATwistLoopLaw C μ t

-- (iii) at `(sz0, zSeq)`: `d = 3`, unconditional; the seven conclusions at the non-main member of `Fam(1/2)`
example (hfam : ∀ z', BAFamZ sz0 zSeq (1 / 3) (fun _ => 1 / 10) z' → Fam6(baFMz sz0 z', μ0, fun _ => 1 / 10)) :
    Fam7(baFMz sz0 mem0, μ0, fun _ => 1 / 2) :=
  MainIndFamTL_atSz0 baMainIndFamTL_III_three (fun n => by nlinarith [sz0_lam_le n, sz0_lam_pos n]) hfam

-- (iii) through the general-`d` form, with Step 5 (iii) at `d = 3`
example (hfam : ∀ z', BAFamZ sz0 zSeq (1 / 3) (fun _ => 1 / 10) z' → Fam6(baFMz sz0 z', μ0, fun _ => 1 / 10)) :
    Fam7(baFMz sz0 mem0, μ0, fun _ => 1 / 2) :=
  MainIndFamTL_atSz0 (baMainIndFamTL_III 3 baStep5III_holds) (fun n => by nlinarith [sz0_lam_le n, sz0_lam_pos n]) hfam

-- (i) at `(L, W₀, lam, κ_dom, t) = (4, 25, 1, 1/70, 1/100)`
example : ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 2 ∧
    ((∀ z', BAFamZ Step5CasesBA_szI Step5CasesBA_zI c₁ (fun _ => 0) z' →
        Fam6(baFMz Step5CasesBA_szI z', Sizes.seqP (Step5CasesBA_szI.withLam 0), fun _ => 0)) →
      Fam7(baFMz Step5CasesBA_szI Step5CasesBA_zI, Sizes.seqP (Step5CasesBA_szI.withLam 0), fun _ => 1 / 100)) :=
  MainIndFamTL_atDatum STReg5I (baMainIndFamTL_I 3) Step5CasesBA_datI 10 (by norm_num)
    (fun n => ⟨by norm_num [Step5CasesBA_szI, Step5CasesBA_sz], by norm_num [Step5CasesBA_szI, Step5CasesBA_sz]⟩) Step5CasesBA_regI

-- (ii) at `(4, 25, 4, 1/1100, 9/10000)`
example : ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 2 ∧
    ((∀ z', BAFamZ Step5CasesBA_szII Step5CasesBA_zII c₁ (fun _ => 0) z' →
        Fam6(baFMz Step5CasesBA_szII z', Sizes.seqP (Step5CasesBA_szII.withLam 0), fun _ => 0)) →
      Fam7(baFMz Step5CasesBA_szII Step5CasesBA_zII, Sizes.seqP (Step5CasesBA_szII.withLam 0), fun _ => 9 / 10000)) :=
  MainIndFamTL_atDatum STReg5II (baMainIndFamTL_II 3) Step5CasesBA_datII 10 (by norm_num)
    (fun n => ⟨by norm_num [Step5CasesBA_szII, Step5CasesBA_sz], by norm_num [Step5CasesBA_szII, Step5CasesBA_sz]⟩) Step5CasesBA_regII

-- (iv) at `(3, 40, 6, 1/1000, 1/2000)`
example : ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 2 ∧
    ((∀ z', BAFamZ Step5CasesBA_szIV Step5CasesBA_zIV c₁ (fun _ => 0) z' →
        Fam6(baFMz Step5CasesBA_szIV z', Sizes.seqP (Step5CasesBA_szIV.withLam 0), fun _ => 0)) →
      Fam7(baFMz Step5CasesBA_szIV Step5CasesBA_zIV, Sizes.seqP (Step5CasesBA_szIV.withLam 0), fun _ => 1 / 2000)) :=
  MainIndFamTL_atDatum STReg5IV (baMainIndFamTL_IV 3) Step5CasesBA_datIV 10 (by norm_num)
    (fun n => ⟨by norm_num [Step5CasesBA_szIV, Step5CasesBA_sz], by norm_num [Step5CasesBA_szIV, Step5CasesBA_sz]⟩) Step5CasesBA_regIV

end Inst

end RBM.BA

end
