/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWTermHolds
import RBM3D.Induction.MainIndOut

/-!
# `UNMLOut` for every `d`

The two light-weight estimates `lwterm_holds`, `lwtermExp_holds` (`Graph/LWTermHolds.lean`) are the
hypotheses of `unMLOut_of_LW` (`Induction/MainIndOut.lean`); with them `unMLOut_holds : ∀ d, UNMLOut d`,
the loop estimates of Lemma 2.21 `ML:GLoop`, Lemma 2.22 `ML:GLoop_expec` and Lemma 2.23 `ML:GtLocal`
at every `0 ≤ t_n ≤ lemT z_n`, derived from Theorem 2.24 (`lem:main_ind`).
-/

set_option linter.style.longLine false

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Ind

namespace RBM.Univ

/-- **`UNMLOut` for every `d`** (`unMLOut_of_LW` at `lwterm_holds`, `lwtermExp_holds`). -/
theorem unMLOut_holds : ∀ d, UNMLOut d := fun d =>
  unMLOut_of_LW d (lwterm_holds d) (lwtermExp_holds d)

end RBM.Univ
