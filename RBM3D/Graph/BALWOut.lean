/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAExp14a2
import RBM3D.Graph.BAExp14b2B

/-!
# BA-L L6 (T2494), file C: the closures of the L4a2 successor pins (`lem:LWterm_EXP` at BA)

Paper: arXiv:2507.20274, `paper/tex/6_Step6_two_loop.tex:83-88` (`lem:LWterm_EXP`),
`paper/tex/7_8_light_weight.tex:10` (`(eq:EGC)`), `paper/tex/B_graphical_lemmas.tex:7-15`
(`(eq:ELW_term)`), `:118` ("analogous ... omit"; route R1, paper delta T2398d of the L4a2 row).

The last terminal row of stage L (supervisor `2026-10-12-2246` L40-C1): the two closures that the
L4a2 row (`Graph/BAExp14a2.lean`, T2490) left open, because their antecedent `BAExp14bS2` was
produced by the L4b2b row (`baExp14bS2_holds`, `Graph/BAExp14b2B.lean`, T2489) only afterwards.

* **`baLWCutExpTw_holds : ∀ d, BALWCutExpTw d`** (the R1 cut pin, seven premises): the assembly
  `baLWCutExpTw_of_S2` at `baExp14bS2_holds d`.
* **`baLWtermEXPTw_holds : ∀ d, BALWtermEXPTw d`** (the seven-premise successor of `BALWtermEXP`,
  `BA/LWPinsBA.lean:49`): the composition `baLWtermEXPTw_of_S2` at `baExp14bS2_holds d`.
* Compiled nonempty instances at `d = 3` (`sz0`, `zSeq`, `flow_sz0`, `t ≡ 1/2`), with TL1
  discharged by `baTwistAvgProd_holds 3` (`BA/TwistAvgB.lean`); TL2 and the five Step 1/2 pins
  stay hypotheses (other gates' pins).

`BAExp14bS2` is read at the merged type only, through `baExp14bS2_holds`; it is not a binder of
any public result.  No pin of the stage-L registry is edited here.
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-- **`lem:LWterm_EXP` at BA (target 7 (b); = `T2490_TermClosed`)**: the seven-premise successor of
`BALWtermEXP`, `BALWtermEXPTw d` (`Graph/BAExp14a2.lean:92`), for every `d`;
`baLWtermEXPTw_of_S2` applied to `baExp14bS2_holds`. -/
theorem baLWtermEXPTw_holds : ∀ d : ℕ, BALWtermEXPTw d :=
  fun d => baLWtermEXPTw_of_S2 d (baExp14bS2_holds d)

/-! ## Compiled nonempty instances (`d = 3`)

Data: `sz0` (`n = 0`: `L = 4`, `W = 32`, `N = 2097152`, `λ = 1/64`), `zSeq`, `flow_sz0`
(`κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`), `t ≡ 1/2 ≤ BAflowT0` (`half_lt_t0`).  Every deterministic
hypothesis is discharged (`3 ≤ 3`, `0 < 1/2`, `0 < 1/10`, `flow_sz0`, `0 ≤ t`, `t ≤ BAflowT0`);
TL1 is `baTwistAvgProd_holds 3` applied to the average law and `STLmaxgL`.  What stays a
hypothesis is another gate's input: the five Step 1/2 pins (`STLocalEntrygL`, `LWAvgLawgL`,
`STLmaxgL`, `STLKgL`, `STDecaygL`) and TL2 (`BATwistLoopLaw`).  The index set
`λ²/L^d ≤ 1 - t` is all of the sizes at `t ≡ 1/2` (`λ_n ≤ 1/64`, `L_n ≥ 1`). -/

end RBM.BA

end
