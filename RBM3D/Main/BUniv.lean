/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Endpoints
import RBM3D.Universality.PinsDens
import RBM3D.Universality.GUETranslation
import RBM3D.Universality.UnivMain
import RBM3D.Universality.EMCTE2
import RBM3D.Universality.Uyw
import RBM3D.Universality.ZeroModeProfile
import RBM3D.Universality.QUEFlow
import RBM3D.Universality.GreenCorr
import RBM3D.Universality.GUELocalBootstrap
import RBM3D.Universality.GUEPhase.RandomLayerB

/-!
# `BUniv` from the leaves of `un_bUniv_of_rows'` (UN-52b, ticket T2371)

Port of RBM2D `Main/BUniv.lean` (`bUniv_of_g1Row`) to the band model `Sizes d`, `d ≥ 3`.
`un_bUniv_of_rows'` (`Universality/PinsDens.lean:233`) with every row that is a proved theorem on
`main` plugged in:

* `un_infty1Row'`, `univMainRow`, `unClaimRow`, `unEMCTE2Row`, `jakUywRow`, `greenCorrAll`;
* `unOURow := ouRow_of_pins g1Row g2bRow` (`g1Row`: `GUEPhase/RandomLayerB`, `g2bRow`: `QUEFlow`).

The leaves that remain hypotheses of `bUniv_of_leaves` are the three band rows `UNDensBandRow`,
`UNTrLocalBandRow`, `UNNormBandRow`, the borrowed `UNL32`, the consumed inputs `UNMLOut`,
`UNLocAvgBand`, `UNQueBand`, and the GUE local law `UNGUELocal`.
-/

set_option linter.style.longLine false

namespace RBM.Endpoints

open RBM RBM.Univ

/-- `UNOURow` (the `𝐇_t` claims from the three consumed inputs) from the proved `g1Row` and `g2bRow`:
`ouRow_of_pins` (`ZeroModeProfile.lean:719`). RBM2D `ouRow_of_g1Row`. -/
theorem unOURow : UNOURow := ouRow_of_pins GUEPhase.g1Row g2bRow

/-- **`BUniv` (`UNBUniv`) from the leaves.** `un_bUniv_of_rows'` with `un_infty1Row'`, `univMainRow`,
`unClaimRow`, `unEMCTE2Row`, `jakUywRow`, `unOURow` and `greenCorrAll` plugged in. RBM2D `bUniv_of_g1Row`. -/
theorem bUniv_of_leaves :
    UNDensBandRow → UNTrLocalBandRow → UNNormBandRow →
      UNL32 → (∀ d : ℕ, UNMLOut d) → UNLocAvgBand → UNQueBand → UNGUELocal → UNBUniv :=
  fun rD rT rN h32 hML hLoc hQ hGL =>
    un_bUniv_of_rows' un_infty1Row' univMainRow unClaimRow unEMCTE2Row jakUywRow unOURow rD rT rN
      h32 hML hLoc hQ hGL greenCorrAll

end RBM.Endpoints
