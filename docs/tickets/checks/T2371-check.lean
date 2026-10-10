/-
Release check for T2371 (dispatcher V2, Sat Oct 10 04:11 UTC 2026; DECISIONS §183).  UN-52b: `Main/BUniv.lean`,
`Main/BUnivHolds.lean`, bulk universality `UNBUniv` from the proved rows (RBM2D `Main/BUniv.lean`, `Main/BUnivHolds.lean`).
Part 1: the pin of target 2 (statement shape; the 1a may only drop leaves that it proves, DECISIONS §183).
Part 2: merged names.  No proofs, no sorry.  Run: lake env lean docs/tickets/checks/T2371-check.lean
-/
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
import RBM3D.Endpoints

open RBM RBM.Univ

namespace RBM.Endpoints.T2371Check

/-- **`BUnivFromLeaves`** (target 2): `UNBUniv` from the leaves of `un_bUniv_of_rows'` (`PinsDens.lean:233`) that are not
proved theorems on `main` today. Every row that is proved is plugged in: `un_infty1Row'`, `univMainRow`, `unClaimRow`,
`unEMCTE2Row`, `jakUywRow`, `ouRow_of_pins g1Row g2bRow`, `greenCorrAll`. -/
def BUnivFromLeaves : Prop :=
  UNDensBandRow → UNTrLocalBandRow → UNNormBandRow →
    UNL32 → (∀ d : ℕ, UNMLOut d) → UNLocAvgBand → UNQueBand → UNGUELocal → UNBUniv

end RBM.Endpoints.T2371Check

/-! ## Part 2: merged names -/
#check @RBM.Univ.un_bUniv_of_rows'
#check @RBM.Univ.un_infty1Row'
#check @RBM.Univ.univMainRow
#check @RBM.Univ.unClaimRow
#check @RBM.Univ.unEMCTE2Row
#check @RBM.Univ.jakUywRow
#check @RBM.Univ.ouRow_of_pins
#check @RBM.Univ.GUEPhase.g1Row
#check @RBM.Univ.g2bRow
#check @RBM.Univ.greenCorrAll
#check @RBM.Univ.un_gueLocal_of_tail
#check @RBM.Univ.UNGUESchurTail
#check @RBM.Univ.unDensBandRow'_of_row
#check @RBM.Univ.unApriori_band_of_rows
#check @RBM.Endpoints.BUniv
