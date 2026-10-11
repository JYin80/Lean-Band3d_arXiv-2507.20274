/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GreenLocal
import RBM3D.BA.GreenCond2

/-!
# `lem_GbEXP_BA`, `(GavLGEX)` at block Anderson (BA-G6b)

`BAGbEXPav d` is the wiring of G6a (`greenLocal_gbEXPav_of_fa`, with GL2 at `ε₀/2` inside)
applied to the averaged law of the residual proved in G5b (`baFAav_holds`).
The two statements `BAFAav` and `GreenLocal_FAav` are textually identical, so the bridge is `id`.
The guard `2 ≤ d` is that of `baGbEXPii_holds`.
-/

namespace RBM.BA

/-- `BAFAav d` is `GreenLocal_FAav d` (identical statements). -/
theorem baFAav_greenLocal (d : ℕ) : BAFAav d → GreenLocal_FAav d := fun h => h

/-- **`lem_GbEXP_BA`, `(GavLGEX)`** at block Anderson (`7_8:1916-1946`), the pin `BAGbEXPav`. -/
theorem baGbEXPav_holds (d : ℕ) (hd : 2 ≤ d) : BAGbEXPav d :=
  greenLocal_gbEXPav_of_fa d hd (baFAav_greenLocal d (baFAav_holds d))

/-- Compiled nonempty instance: `d = 3`. -/
example : BAGbEXPav 3 := baGbEXPav_holds 3 (by norm_num)

end RBM.BA
