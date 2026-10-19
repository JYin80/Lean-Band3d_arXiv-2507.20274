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
# The BA side of `lem:iterations`

Lemma 4.11 (`lem:iterations`) at the block Anderson tuple.  Composition of existing results.

* `baIterationsGen2_fam`: `IterationsGen2_Fam` at the BA tuple.
* `baSTIterationsgL'_holds`, `baSTIterationsIIgL'_holds`: `stIterationsgL'_of`, `stIterationsIIgL'_of` at `baIterationsGen2_fam`
  (`(baStep2Mat ..).toFlowFM` is `baFMz sz z` by unfolding).
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.BA

open MeasureTheory ProbabilityTheory Filter RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- `baIterationsGen2_fam`: the family bundle `IterationsGen2_Fam` at the BA tuple. -/
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

/-- `baSTIterationsgL'_holds`, case (i): the statement `STIterationsgL'` at the BA tuple. -/
theorem baSTIterationsgL'_holds (d : ℕ) :
    STIterationsgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
  stIterationsgL'_of d _ _ (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))
    (fun sz z => sz.seqHflowBA (BAflowLam0 sz z)) (fun sz z => BAflowEs sz z) (fun sz z => BAflowT0 sz z)
    (baIterationsGen2_fam d)

/-- `baSTIterationsIIgL'_holds`, case (ii): `STIterationsIIgL'` at the BA tuple. -/
theorem baSTIterationsIIgL'_holds (d : ℕ) :
    STIterationsIIgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
  stIterationsIIgL'_of d _ _ (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))
    (fun sz z => sz.seqHflowBA (BAflowLam0 sz z)) (fun sz z => BAflowEs sz z) (fun sz z => BAflowT0 sz z)
    (baIterationsGen2_fam d)

end RBM.BA

end
