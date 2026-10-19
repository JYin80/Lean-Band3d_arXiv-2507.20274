/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.LWGen
import RBM3D.Graph.LWTermHolds
import RBM3D.Graph.LWExpTerm6
import RBM3D.BA.FlowPins

/-!
# The block Anderson readings of the light-weight statements

`baPin P d` is the generic statement `P d` read at the block Anderson data: law `seqP (sz.withLam 0)`, setting `BAFlow`, carrier `baFMz`, horizon `BAflowT0`.
The file defines two readings:

* `BALWterm` is `baPin LWtermG`, Lemma 3.10 (`lem:LWterm`) at the block Anderson data; it is proved as `baLWterm_holds`.
* `BALWtermExp` is `baPin LWtermExpG`, Lemma 3.11 (`lem: EWGn2_N`) at the block Anderson data; it is proved as `baLWtermExp_holds`.

The file imports the band theorems `lwterm_holds`, `lwtermExp_holds` and `lwTermEXP_holds`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-- The generic statement `P d` at the block Anderson data: law `seqP (sz.withLam 0)`, setting `BAFlow`, carrier `baFMz`, horizon `BAflowT0`. -/
def baPin (P : PinFam) (d : ℕ) : Prop := P d (fun sz => Sizes.seqP (sz.withLam 0))
  (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0

/-! ## 1. The block Anderson readings -/

/-- Lemma 3.10 (`lem:LWterm`) at the block Anderson data (proved as `baLWterm_holds`). -/
abbrev BALWterm : ℕ → Prop := baPin LWtermG
/-- Lemma 3.11 (`lem: EWGn2_N`) at the block Anderson data (proved as `baLWtermExp_holds`). -/
abbrev BALWtermExp : ℕ → Prop := baPin LWtermExpG

end RBM.BA

end
