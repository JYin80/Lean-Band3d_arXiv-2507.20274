/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAExp14a2
import RBM3D.Graph.BAExp14b2B

/-!
# The light-weight expectation bound at the block Anderson data (`lem:LWterm_EXP`)

Paper: Lemma 6.2 (`lem:LWterm_EXP`), through (7.1) `eq:EGC` and (B.1) `eq:ELW_term`.  For the
block Anderson model the proof (Subappendix B.1) is the one for random band matrices with the
`GG` expansion (B.20) `GGGamma` in place of the band expansion ("analogous ... we omit the
details").

* **`baLWtermEXPTw_holds : ∀ d, BALWtermEXPTw d`**: the expected light-weight bound written out at
  the block Anderson data; its seven premises (the five Step 1/2 inputs `STLocalEntrygL`,
  `LWAvgLawgL`, `STLmaxgL`, `STLKgL`, `STDecaygL`, and the two twist laws `BATwistAvgLaw`,
  `BATwistLoopLaw`) are part of the statement `BALWtermEXPTw d`.  The proof composes
  `baLWtermEXPTw_of_S2` with `baExp14bS2_holds d` (`Graph/BAExp14b2B.lean`).
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-- **Lemma 6.2 (`lem:LWterm_EXP`) at the block Anderson data**: `BALWtermEXPTw d`
(`Graph/BAExp14a2.lean`) for every `d`; `baLWtermEXPTw_of_S2` applied to `baExp14bS2_holds`. -/
theorem baLWtermEXPTw_holds : ∀ d : ℕ, BALWtermEXPTw d :=
  fun d => baLWtermEXPTw_of_S2 d (baExp14bS2_holds d)

end RBM.BA

end
