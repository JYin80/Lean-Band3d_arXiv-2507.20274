/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GreenLocal
import RBM3D.BA.GreenCond2

/-!
# `lem_GbEXP_BA`, `(GavLGEX)` at block Anderson

`BAGbEXPav d` is obtained from `greenLocal_gbEXPav_of_fa` (which uses the bound `baGbEXPii_holds` at `ε₀/2`)
applied to the averaged law of the residual, `baFAav_holds`.
The two statements `BAFAav` and `GreenLocal_FAav` are textually identical, so the bridge is `id`.
The guard `2 ≤ d` is that of `baGbEXPii_holds`.
-/

namespace RBM.BA

/-- `BAFAav d` is `GreenLocal_FAav d` (identical statements). -/
theorem baFAav_greenLocal (d : ℕ) : BAFAav d → GreenLocal_FAav d := fun h => h

/-- **Lemma 8.4 (`lem_GbEXP_BA`), the averaged bound `(GavLGEX)`** at block Anderson: the statement `BAGbEXPav`. -/
theorem baGbEXPav_holds (d : ℕ) (hd : 2 ≤ d) : BAGbEXPav d :=
  greenLocal_gbEXPav_of_fa d hd (baFAav_greenLocal d (baFAav_holds d))

end RBM.BA
