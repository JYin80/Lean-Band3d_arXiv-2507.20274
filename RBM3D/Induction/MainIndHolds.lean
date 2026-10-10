/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWTermHolds
import RBM3D.Induction.MainIndOut

/-!
# ST-6 R4 (ticket T2375): `lem:main_ind` and `UNMLOut` for every `d`

The two light-weight estimates `lwterm_holds`, `lwtermExp_holds` (`Graph/LWTermHolds.lean`) close
the two owed LW pins of `stMainInd_of_LW` and `unMLOut_of_LW` (`Induction/MainIndOut.lean`); Step 2
is not re-proved.

* `stMainInd_holds : ∀ d, STMainInd d` (`lem:main_ind`, `1_2:1256-1330`);
* `unMLOut_holds : ∀ d, UNMLOut d` (the ST-6 output);
* `stStep2_holds : ∀ d, STStep2 d` (Step 2, `1_2:1340-1357`): the premise `3 ≤ d` of `STStep2 d` is
  part of its definition, so the instance of `ST_step2_of_pinsLW'` used by `stMainInd_of_LW` is
  unconditional;
* `stEtermsMid_holds`, `stStep5I_holds`, `stStep5II_holds`: the other pins that `stMainInd_of_LW`
  derives from `LWtermExp` (each starts with `3 ≤ d →`), unconditional in the same way.
-/

set_option linter.style.longLine false

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Ind

namespace RBM.Gauss.Sizes

/-- **`lem:main_ind`** (`1_2:1256-1330`) for every `d`: `stMainInd_of_LW` applied to `lwterm_holds`,
`lwtermExp_holds`. -/
theorem stMainInd_holds : ∀ d, STMainInd d := fun d =>
  stMainInd_of_LW d (lwterm_holds d) (lwtermExp_holds d)

/-- **Step 2** (`1_2:1340-1357`) for every `d`: `ST_step2_of_pinsLW'` at the merged producers (the
instance of `stMainInd_of_LW`) and `lwtermExp_holds`, `lwterm_holds` (through `STLWB_of_LWterm`). -/
theorem stStep2_holds : ∀ d, STStep2 d := fun d hd =>
  ST_step2_of_pinsLW' hd (stNewKLK_holds d) (lwtermExp_holds d) (stEMn2Exp_holds d hd) (stGridRepN_holds d hd)
    (stOptL2_of_pins hd (STLWB_of_LWterm hd (lwterm_holds d)) (stGridMart_holds d hd)) (stLocalAvgOfL2_holds hd) hd

/-- **`(S5WG+M000)`, `(S5WG+M)`** (`3_5:1961-1979`) for every `d`: `stEtermsMid_of_LWT` at `STLWT_of_LWtermExp` of `lwtermExp_holds`
(the instance used in `stMainInd_of_LW`). -/
theorem stEtermsMid_holds : ∀ d, STEtermsMid d := fun d hd =>
  stEtermsMid_of_LWT d (STLWT_of_LWtermExp hd (lwtermExp_holds d)) hd

/-- **Step 5, case (i)** (`3_5:1939`) for every `d`: `ST_step5_caseI_of_pins` at `stEtermsMid_holds` (the instance used in `stMainInd_of_LW`). -/
theorem stStep5I_holds : ∀ d, STStep5I d := fun d =>
  ST_step5_caseI_of_pins (stEtermsMid_holds d) (stDuhamelI_holds d) (stIniTermI_holds d)

/-- **Step 5, case (ii)** for every `d`: `ST_step5_caseII_of_pins` at `stEtermsMid_holds` (the instance used in `stMainInd_of_LW`). -/
theorem stStep5II_holds : ∀ d, STStep5II d := fun d =>
  ST_step5_caseII_of_pins (stEtermsMid_holds d) (stDuhamelII_holds d) (stIniTermII_holds d) (stWardII_holds d)

end RBM.Gauss.Sizes

namespace RBM.Univ

/-- **The ST-6 output** `UNMLOut` for every `d` (`unMLOut_of_LW` at `lwterm_holds`,
`lwtermExp_holds`). -/
theorem unMLOut_holds : ∀ d, UNMLOut d := fun d =>
  unMLOut_of_LW d (lwterm_holds d) (lwtermExp_holds d)

end RBM.Univ

/-! ## Compiled nonempty instances (`d = 3`, merged data `sz0`, `z0`, `flow_z0`) -/

namespace RBM.Gauss.MainIndHoldsInst

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst

/-- `unMLOut_holds` (so `stMainInd_holds`, `lwterm_holds`, `lwtermExp_holds`) at `sz0`, `z0`, `t = lemT z / 2`: the `L`-`K` bound `STLK`
with no hypothesis left (the merged instance of `unMLOut_of_LW` had `LWterm 3`, `LWtermExp 3` as hypotheses). -/
example : sz0.STLK (STflowE z0) (fun n => lemT (z0 n) / 2) :=
  (RBM.Univ.unMLOut_holds 3 (by norm_num) (1 / 10) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num)
    (by norm_num) sz0 z0 flow_z0 _ (fun n => (half_pos (lemT_pos (z0_im_pos n))).le)
    (fun n => by linarith [lemT_pos (z0_im_pos n)])).1

/-- `stMainInd_holds` at `d = 3`, `κ = ε = 𝔡 = 1/10`: the constant `𝔠_d` and the pin at the sequences. -/
example := stMainInd_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)

/-- `stStep2_holds` at `d = 3`, `κ = ε = 𝔡 = 1/10`: the constants `C_d`, `𝔠_d` (the hypotheses on the sequences are the other pins `STLK`,
`STDecay`, `STStep1Loop`, `STStep1Weak` and `STConStInd`). -/
example := stStep2_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)

/-- `stEtermsMid_holds`, `stStep5I_holds`, `stStep5II_holds` at `d = 3`, `κ = ε = 𝔡 = 1/10`, `C_d = 1`. -/
example := stEtermsMid_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 1 one_pos

example := stStep5I_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 1 one_pos

example := stStep5II_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 1 one_pos

end RBM.Gauss.MainIndHoldsInst
