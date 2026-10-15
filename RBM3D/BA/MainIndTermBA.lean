/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.MainIndRegBA
import RBM3D.BA.MainIndGlue

/-!
# V row V2a, row b (T2511b): the BA terminal at `d = 3` and the general-`d` step

The four regime steps of `BA/MainIndRegBA.lean` (merged, T2511 row a) enter the regime glue
`baMainIndFamTL_of_regimes` (`BA/MainIndGlue.lean:288`, merged, T2512) in its binder order (iii), (i), (ii), (iv).
No new mathematics: every theorem below is a composition of merged names.

* `baMainIndFamTL_three : BAMainIndFamTL 3 STAny` (target 11): unconditional at `d = 3` (regime (iii) through `baStep5III_holds`).
* `baMLOutTL_three : BAMLOutTL 3`, `unMLOutBA_three : Univ.UNMLOutBA 3` (target 11): `baMLOutTL_of_famStep`, `unMLOutBA_of_famStep`
  (`BA/MainIndOutBA.lean:315, 326`).
* `baMainIndFamTL_any` (target 12): `∀ d, STStep5IIIgL d … → BAMainIndFamTL d STAny` (the text of `T2512_AnyD`); `d > 3` regime (iii)
  enters only as the hypothesis `STStep5IIIgL d` (DECISIONS §316, Jun decision B).
* Compiled `d = 3` instances at `(sz0, zSeq)`, `κ = 1/4`, `(ε, 𝔠, 𝔡) = (1/10, 1/6, 1/10)`, `c₁ = 1/3`; the hypothesis `hm` of the instances of
  `BA/MainIndOutBA.lean:408-426` is now discharged.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Target 11: the terminal at `d = 3` -/

/-- **Target 11, `baMainIndFamTL_three`**: `lem:main_ind_BA` in family form with TL2 at `STAny`, `d = 3`, unconditional:
`baMainIndFamTL_of_regimes` of the four closed regimes. -/
theorem baMainIndFamTL_three : BAMainIndFamTL 3 STAny :=
  baMainIndFamTL_of_regimes 3 baMainIndFamTL_III_three (baMainIndFamTL_I 3) (baMainIndFamTL_II 3) (baMainIndFamTL_IV 3)

/-- **Target 11, `baMLOutTL_three`**: `BAMLOutTL 3`, unconditional (`baMLOutTL_of_famStep`, `MainIndOutBA:315`). -/
theorem baMLOutTL_three : BAMLOutTL 3 := baMLOutTL_of_famStep 3 baMainIndFamTL_three

/-- **Target 11, `unMLOutBA_three`**: `UNMLOutBA 3`, unconditional (`unMLOutBA_of_famStep`, `MainIndOutBA:326`). -/
theorem unMLOutBA_three : Univ.UNMLOutBA 3 := unMLOutBA_of_famStep 3 baMainIndFamTL_three

/-! ## 2. Target 12: the general-`d` step at `STAny` -/

/-- **Target 12, `baMainIndFamTL_any`**: the family step at `STAny` for every `d` under Step 5 (iii) `STStep5IIIgL d` (0342 Q4; the text of
`T2512_AnyD`); `BAMainIndFamTL d STAny` starts `3 ≤ d →`. `d = 3`: `baStep5III_holds`. -/
theorem baMainIndFamTL_any : ∀ d : ℕ,
    STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) → BAMainIndFamTL d STAny :=
  fun d h5 => baMainIndFamTL_of_regimes d (baMainIndFamTL_III d h5) (baMainIndFamTL_I d) (baMainIndFamTL_II d) (baMainIndFamTL_IV d)

/-! ## 3. Compiled `d = 3` instances (targets 11, 12)

Data (`BA/MainIndOutBA.lean` §7, by `open private`): `sz0`, `zSeq`, `flow_sz0` weakened to `κ = 1/4`, `(ε, 𝔠, 𝔡) = (1/10, 1/6, 1/10)`, `c₁ = 1/3`
(`sz0_win_third`), `t ≡ 1/2 ≤ T₀` (`half_lt_t0`) and `t ≡ 0`.  The terminal outputs are hypothesis-free.  Target 12 is applied at `d = 3` with
`baStep5III_holds`: at `s ≡ 0 < t ≡ 1/2` every premise is discharged (the six conclusions at every member of `Fam(0)` are the base, `baFamMember_base`);
at `s ≡ 1/10` the six conclusions on `Fam(1/10)` (the induction hypothesis) are the one binder. -/

section Inst

open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst RBM.BA.Step1FamInst
open private MainIndOutBA_flow MainIndOutBA_win MainIndOutBA_mem from RBM3D.BA.MainIndOutBA
local notation "μ0" => Sizes.seqP (sz0.withLam 0)
local notation "mem0" => BAzSrc sz0 zSeq (fun _ => 2 / 3) (fun _ => 17 / 25)
local notation "Fam6" "(" C ", " μ ", " s ")" =>
  STLKgL C μ s ∧ STDecaygL C μ s ∧ STDecayStronggL C μ s ∧ STLocalMaxgL C μ s ∧ STExp2gL C μ s ∧ BATwistLoopLaw C μ s
local notation "Fam7" "(" C ", " μ ", " t ")" =>
  STLKgL C μ t ∧ STLmaxgL C μ t ∧ STDecaygL C μ t ∧ STExp2gL C μ t ∧ STLocalEntrygL C μ t ∧ STDecayStronggL C μ t ∧ BATwistLoopLaw C μ t

-- target 11: the three outputs as one conjunction (the pin `T2511_Terminal`)
example : BAMainIndFamTL 3 STAny ∧ BAMLOutTL 3 ∧ Univ.UNMLOutBA 3 := ⟨baMainIndFamTL_three, baMLOutTL_three, unMLOutBA_three⟩

-- target 12 at `d = 3` with Step 5 (iii) proved: it is target 11
example : BAMainIndFamTL 3 STAny := baMainIndFamTL_any 3 baStep5III_holds

-- target 11: `BAMLOutTL 3` at `t ≡ 1/2` and at `t ≡ 0` (hypothesis-free; the instances of `MainIndOutBA:408-426` without `hm`)
example := baMLOutTL_three le_rfl (1 / 4) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq
  MainIndOutBA_flow (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)
example := baMLOutTL_three le_rfl (1 / 4) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq
  MainIndOutBA_flow (fun _ => 0) (fun _ => le_rfl) (fun n => by linarith [half_lt_t0 n])

-- target 11: `UNMLOutBA 3` at `t ≡ 1/2` and at `t ≡ 0`
example := unMLOutBA_three le_rfl (1 / 4) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq
  MainIndOutBA_flow (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)
example := unMLOutBA_three le_rfl (1 / 4) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq
  MainIndOutBA_flow (fun _ => 0) (fun _ => le_rfl) (fun n => by linarith [half_lt_t0 n])

-- target 12 at `d = 3`: the plug-in on the general-`d` step with `baStep5III_holds`
example := baMLOutTL_of_famStep 3 (baMainIndFamTL_any 3 baStep5III_holds) le_rfl (1 / 4) (1 / 10) (1 / 10) (1 / 6) (by norm_num)
  (by norm_num) (by norm_num) sz0 zSeq MainIndOutBA_flow (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)

-- target 12 at `s ≡ 0 < t ≡ 1/2`, hypothesis-free: the six conclusions on `Fam(0)` are the base; the seven at the non-main member of `Fam(1/2)`
example : ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ Fam7(baFMz sz0 mem0, μ0, fun _ => 1 / 2) := by
  obtain ⟨𝔠d, h𝔠, -, H⟩ := baMainIndFamTL_any 3 baStep5III_holds le_rfl (1 / 4) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨𝔠d, h𝔠, H (1 / 6) sz0 zSeq MainIndOutBA_flow sz0_lam_pos (1 / 3) (by norm_num) (by norm_num) MainIndOutBA_win
    (fun _ => 0) (fun _ => 1 / 2) (fun _ => le_rfl) (fun n => by linarith [half_lt_t0 n]) (fun _ => by norm_num)
    (fun n => (half_lt_t0 n).le) trivial ?_ (Ind.Step1SetupInst.s1Setup_conStInd_const (by norm_num) (by norm_num) h𝔠) _
    (MainIndOutBA_mem (1 / 2) (by norm_num))⟩
  intro z' hz'
  obtain ⟨⟨b1, -, b3, b4, b5, b6⟩, tl⟩ := baFamMember_base 3 (baBaseG_holds 3) (baG0M_holds 3) le_rfl (1 / 4) (1 / 10) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq MainIndOutBA_flow sz0_lam_pos (1 / 3) (by norm_num) (by norm_num)
    MainIndOutBA_win z' hz'
  exact ⟨b1, b3, b6, STLocalMaxgL_of_STLocalEntrygL _ _ _ b5, b4, tl⟩

-- target 12 at `s ≡ 1/10 < t ≡ 1/2` (the data of T2511 row a): the six conclusions on `Fam(1/10)` (the induction hypothesis) are the one binder
example (hfam : ∀ z', BAFamZ sz0 zSeq (1 / 3) (fun _ => 1 / 10) z' → Fam6(baFMz sz0 z', μ0, fun _ => 1 / 10)) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ Fam7(baFMz sz0 mem0, μ0, fun _ => 1 / 2) := by
  obtain ⟨𝔠d, h𝔠, -, H⟩ := baMainIndFamTL_any 3 baStep5III_holds le_rfl (1 / 4) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨𝔠d, h𝔠, H (1 / 6) sz0 zSeq MainIndOutBA_flow sz0_lam_pos (1 / 3) (by norm_num) (by norm_num) MainIndOutBA_win
    (fun _ => 1 / 10) (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (by norm_num : (1 / 10 : ℝ) ≤ 1 / 2).trans (half_lt_t0 n).le)
    (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) trivial hfam
    (Ind.Step1SetupInst.s1Setup_conStInd_const (by norm_num) (by norm_num) h𝔠) _ (MainIndOutBA_mem (1 / 2) (by norm_num))⟩

end Inst

end RBM.BA

end
