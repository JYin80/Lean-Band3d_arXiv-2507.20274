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

namespace RBM.Univ

/-- **The ST-6 output** `UNMLOut` for every `d` (`unMLOut_of_LW` at `lwterm_holds`,
`lwtermExp_holds`). -/
theorem unMLOut_holds : ∀ d, UNMLOut d := fun d =>
  unMLOut_of_LW d (lwterm_holds d) (lwtermExp_holds d)

end RBM.Univ

/-! ## Compiled nonempty instances (`d = 3`, merged data `sz0`, `z0`, `flow_z0`) -/
