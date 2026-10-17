/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.ZeroModeGen
import RBM3D.Chain.Step34Gen
import RBM3D.Chain.IterationsGen2
import RBM3D.Chain.QGridGen
import RBM3D.Chain.Step2Kern
import RBM3D.Chain.Step2EventsGenTw
import RBM3D.BA.SEforLnBA
import RBM3D.BA.B45BA
import RBM3D.BA.GridRepTailBA
import RBM3D.BA.TwistStep2
import RBM3D.BA.Step1Fam

/-!
# The BA side of U1: `lem: newPQ`, the zero-mode commutation, the kernel semigroup and `lem:iterations` (ticket T2500, U1-BA)

Composition of merged results; no merged file is edited.

* **Target 1** `stNewPQgL_wardCls`: `STNewPQgL` over the carrier Ward class `ZeroModeGen_WardCls`, from `zeroModeGen_newPQ` at the class
  witnesses `TL`, `TK`.
* **Target 2** `baSTNewPQgL`: the same over the class of BA carriers along a BA flow (`baZeroModeGen_wardCls`).
* **Target 3** `baZeroModeSet_UN` (with `BAUN`), `baZeroModeSet_ThetaN`: `Q^{(A)}` commutes with the kernels (`zeroModeSet_UNg`,
  `zeroModeSet_ThetaNg` at `baZeroModeGen_kerSums`; `Step2Kern_UN_BA`).
* **Target 4** `baStep2Gen_USemigroup`: first conjunct of `gridRepTailGen_ker_BA`.
* **Target 5** `baIterationsGen2_fam`: `IterationsGen2_Fam` at the BA tuple.
* **Target 6** `baSTIterationsgL'_holds`, `baSTIterationsIIgL'_holds`: `stIterationsgL'_of`, `stIterationsIIgL'_of` at target 5
  (`(baStep2Mat ..).toFlowFM` is `baFMz sz z` by unfolding).
* **Instances** at `d = 3` in `RBM.BA.ZeroModeBAInst`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.BA

open MeasureTheory ProbabilityTheory Filter RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ### 1. `lem: newPQ` over the carrier Ward class and at BA -/

/-! ### 2. The zero-mode commutation at BA -/

/-! ### 3. The kernel semigroup at BA -/

/-! ### 4. `lem:iterations` at BA -/

/-- **Target 5** (`T2500_IterFamBA`): the family bundle `IterationsGen2_Fam` at the BA tuple. -/
theorem baIterationsGen2_fam (d : ℕ) :
    IterationsGen2_Fam d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => sz.seqHflowBA (BAflowLam0 sz z))
      (fun sz z => BAflowEs sz z) (fun sz z => BAflowT0 sz z) := by
  refine ⟨Step2EventsGenTw_baFlow d, fun sz => Sizes.isProbabilityMeasure_seqP (sz.withLam 0), ?_, ?_⟩
  · intro sz κ ε 𝔠 𝔡 z hκ hflow
    refine ⟨baStep2Mat_loopForm d sz κ ε 𝔠 𝔡 z hκ hflow, fun n => ?_⟩
    have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
    exact BAm_norm_le_one d (sz.L n) _ _ _ (by simp) hr.1
  · exact fun sz z => ⟨baStep34_LCompat d sz _ _, EMn2BA_seqHflowBA_herm sz _⟩

/-- **Target 6, case (i)** (`T2500_IterationsBA`): the R2* pin `STIterationsgL'` at the BA tuple. -/
theorem baSTIterationsgL'_holds (d : ℕ) :
    STIterationsgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
  stIterationsgL'_of d _ _ (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))
    (fun sz z => sz.seqHflowBA (BAflowLam0 sz z)) (fun sz z => BAflowEs sz z) (fun sz z => BAflowT0 sz z)
    (baIterationsGen2_fam d)

/-- **Target 6, case (ii)** (`T2500_IterationsIIBA`): `STIterationsIIgL'` at the BA tuple. -/
theorem baSTIterationsIIgL'_holds (d : ℕ) :
    STIterationsIIgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
  stIterationsIIgL'_of d _ _ (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))
    (fun sz z => sz.seqHflowBA (BAflowLam0 sz z)) (fun sz z => BAflowEs sz z) (fun sz z => BAflowT0 sz z)
    (baIterationsGen2_fam d)

end RBM.BA

/-! ### 5. Compiled nonempty instances at `d = 3` (targets 1-5)

`sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`), `zSeq`, `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq`,
`m = 3`, `σ = (+,-,+)` (`STIdiff σ = {0, 1}`), `n = 0`, `τ = 1/2`, windows `s ≡ 1/10 ≤ t ≡ 1/2 < 1`, `K = 4`. -/

/-! ### 6. Compiled nonempty instances of target 6 (`d = 3`)

Case (ii) at the merged datum `TwistStep2_szII` (`L ≡ 4`, `W_n = n + 25`, `lam ≡ 5`; `TwistStep2_flowII`), `s ≡ 0 < t ≡ 1/2000`.  Case (i) at the
new private datum `szI` (`lam ≡ 2`, the `TwistStep2_szII` pattern, ported from `BA/TwistStep2.lean:1341-1435` with `g = 2`): `sz0` has no `STRegIterI`
window (`n = 0`: `1 - s₀ ≤ lam₀² = 1/4096` against `t₀ ≤ 25/36`, `t0_sz0_le`), and `TwistStep2_szII` has none either (`lam²/L² = 25/16 > 1 - t`).
`(κ, ε, 𝔠, 𝔡) = (3/1000, 1/2, 1/9, 1/10)`, `s ≡ 0 < t ≡ 1/400 ≤ T₀`, `STCaseI` (`1/4 ≤ 399/400`), `1 - s = 1 ≤ lam² = 4`.  The pin binders (`STKboundgL`,
`STLKgL`, `STStep1LoopgL`, `STStep2ConclgL`, `STXiBootgL'`) and the two induction hypotheses stay hypotheses (other gates' pins). -/

end
