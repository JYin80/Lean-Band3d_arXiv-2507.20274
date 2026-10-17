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
# The band instances and the BA readings of the generic light-weight pins (BA-L0, ticket T2394)

Design `docs/reports/T2387-design.md` §2 (LD2), §6 (row L0); probe `t/T2387:RBM3D/Probe/T2387Pins.lean:205-244, 305-322`.
This file sits downstream of the band theorems (`lwterm_holds`, `lwtermExp_holds`, `lwTermEXP_holds`,
`STLWB_of_LWterm`, `STLWT_of_LWtermExp`), which the chain files do not import.

* `baPin P` is `P` at the block Anderson data (law `seqP (sz.withLam 0)`, setting `BAFlow`, carrier `baFMz`, horizon
  `BAflowT0`); `BAStep2 d` (`BA/FlowPins.lean:432`) is `baPin STStep2G d`.
* The BA readings `BALWterm`, `BALWtermExp` (proved: `baLWterm_holds`, `baLWtermExp_holds`, `Graph/BATermHolds.lean:706`, `Graph/BATermHoldsB.lean:865`), `BALWtermEXP` (superseded by `BALWtermEXPTw` (T2490/T2494); no producer; do not read) and `BASTLWB`, `BASTLWT` (proved for `3 ≤ d`: `baSTLWB_of` / `baSTLWT_of`, `BA/DecayLoopBA.lean:135, 140`, from `baLWterm_holds` / `baLWtermExp_holds`) are
  `Prop`-valued pins with no proof here.
* The band instances at `d = 3` are theorems (the merged band results, transported by `Iff.rfl`).
* The nonempty instances at the end apply the BA pins at the concrete data of `sz0` (`n = 0`: `L = 4`, `W = 32`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-- BA: law `seqP (sz.withLam 0)`, setting `BAFlow`, carrier `baFMz`, horizon `BAflowT0` (as `BAStep2`, `BA/FlowPins.lean:432`). -/
def baPin (P : PinFam) (d : ℕ) : Prop := P d (fun sz => Sizes.seqP (sz.withLam 0))
  (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0

/-! ## 1. The BA readings (pins; no proof) -/

/-- `lem:LWterm` at the block Anderson data (proved: `baLWterm_holds`, `Graph/BATermHolds.lean:706`). -/
abbrev BALWterm : ℕ → Prop := baPin LWtermG
/-- `lem: EWGn2_N` at the block Anderson data (proved: `baLWtermExp_holds`, `Graph/BATermHoldsB.lean:865`). -/
abbrev BALWtermExp : ℕ → Prop := baPin LWtermExpG
/-! ## 2. The generic pins at the band carrier are the merged theorems -/

/-! ## 3. Nonempty instances at `d = 3`

Data: `sz0` (`n = 0`: `L = 4`, `W = 32`, `λ = 1/64`), flow `flow_sz0` (`κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`), `t ≡ 1/2 ≤ BAflowT0`,
`ε₀ = 1/10`, `Ψ_n = W_n^{-1/2}` (window `W^{-3/2} ≤ Ψ ≤ W^{-1/10}`), `ℓ ≡ 0`, `D = 1`. -/

end RBM.BA

end
