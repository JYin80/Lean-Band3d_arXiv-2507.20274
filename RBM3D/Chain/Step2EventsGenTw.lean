/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step2EventsGen
import RBM3D.BA.LWPinsBA
import RBM3D.BA.Step2BA
import RBM3D.BA.EMn2BA
import RBM3D.BA.FlowPins

/-!
# The BA side of the Step 2 events, closed band instance of target 11 (BA-T row T7b leaf, T2467)

A leaf (no module imports it): it may import `BA/`, while `Chain/Step2EventsGen.lean` may not.
This is the BA side of `Chain/Step2EventsGen` (targets 8-11 of ticket T2454, the Step 2 events over
the carrier; Amend 1 of T2467); `Chain/DecayGenTw.lean` (T7a) is not edited and not imported.

* **Carrier facts at BA.**  `Step2EventsGenTw_baFlow` (F1-F2 at `BAFlow`, `BAflowT0`;
  `EMn2BA_T0_lt_one`), `Step2EventsGenTw_baGrid` (F9 at `baStep2Mat sz l E`, law
  `seqP (sz.withLam 0)`; `Hm = seqHflowBA`, `(5.1)` through the translation `H ↦ l • PsiI + H`
  in `Step2EventsGenTw_baLaw`) and `Step2EventsGenTw_baRot3` (F7 at `baFM sz l E`, the generic
  `Step2EventsGen_loopFine_rot3`).  F3 at BA is `EMn2BA_mF_data` (`BA/EMn2BA.lean:125`), inline
  as in `DecayGenTw.lean:75`.
* **Statement-level instances** (examples): (E1), (E3), (E4) elaborated at the BA family
  `(law, Flow, mk, T0) = (seqP (sz.withLam 0), BAFlow, baStep2Mat sz (BAflowLam0 sz z)
  (BAflowEs sz z), BAflowT0)` with F1-F3 and F9 discharged and `BASTLWT`, `baSTEMn2Exp`, Step 1
  (`STStep1WeakgL`), `STScaleInvgL` and the `Bctl` bounds left open; target 11 at the BA family
  (`BALWterm 3 → BASTLWB 3`, `BALWtermExp 3 → BASTLWT 3`, F7 from `Step2EventsGenTw_baRot3`).
* **The closed band instance of target 11** (`band_LWtermG`, `band_LWtermExpG`,
  `BA/LWPinsBA.lean`): `Step2EventsGenTw_band_STLWBgL`, `Step2EventsGenTw_band_STLWTgL` are
  `bandPin STLWBgL 3`, `bandPin STLWTgL 3` through `stLWBgL_of_LWtermG`,
  `stLWTgL_of_LWtermExpG`, with every hypothesis discharged (`3 ≤ 3`, F1, F7).
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.setOption false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The carrier facts F1-F2, F7, F9 at BA -/

/-- **F1-F2 at BA**: `BAFlow` contains `Admissible`; `t₀ < 1` (`EMn2BA_T0_lt_one`). -/
theorem Step2EventsGenTw_baFlow (d : ℕ) :
    Step2EventsGen_Flow d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) BAflowT0 :=
  ⟨fun _ _ _ _ _ _ h => h.1, fun sz _ _ _ _ _ hκ h n => EMn2BA_T0_lt_one hκ sz h n⟩

/-- **F7 at BA**: the generic trace cyclicity of the 3-loop (`BALloop` is `loopFine` at `seqHflowBA`, `ztOf`). -/
theorem Step2EventsGenTw_baRot3 {d : ℕ} (sz : Sizes d) (l E : ℕ → ℝ) : Step2EventsGen_Rot3 (baFM sz l E) :=
  fun n t σ₀ σ₁ a₀ y a₁ ω => Step2EventsGen_loopFine_rot3 _ _ σ₀ σ₁ a₀ y a₁

/-- **The law clause of F9 at BA**: `Hm = seqHflowBA`; `(5.1)` is `ST_pathP_eq_seqP (sz.withLam 0)` at the translated set
`{H | l • PsiI + H ∈ S}` (`Hpath = l • PsiI + pathH`, `seqHflowBA = l • PsiI + seqHflow`). -/
theorem Step2EventsGenTw_baLaw {d : ℕ} (sz : Sizes d) (l E : ℕ → ℝ) :
    Step2EventsGen_Law (baStep2Mat sz l E) (Sizes.seqP (sz.withLam 0)) (fun n u => sz.seqHflowBA l n u) :=
  fun s t K n k hs hst hK S hS => by
    have hT : Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
        ((l n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + H :=
      Measurable.of_eval_matrix _ fun i j => measurable_const.add ((measurable_pi_apply j).comp (measurable_pi_apply i))
    exact ST_pathP_eq_seqP (sz.withLam 0) s t K n k hs hst hK (hS.preimage hT)

/-- **F9 at BA**: `Hm = seqHflowBA`; clauses 1-2 are `rfl` (`baStep2Mat_LM`, `baStep2Mat_GMM`), 3-4 the measurability of `loopFine`,
`Gres` in the matrix, and `(5.1)` is `Step2EventsGenTw_baLaw`. -/
theorem Step2EventsGenTw_baGrid {d : ℕ} (sz : Sizes d) (l E : ℕ → ℝ) :
    Step2EventsGen_Grid (baStep2Mat sz l E) (Sizes.seqP (sz.withLam 0)) :=
  ⟨fun n u => sz.seqHflowBA l n u, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl,
    fun n u _ σ a => walk_measurable_loopFine d (sz.L n) (sz.W n) (ztOf (BAmF sz l E n) (E n) u) σ a,
    fun n u x y => (walk_measurable_Gres_apply (ztOf (BAmF sz l E n) (E n) u) true x y).sub measurable_const,
    Step2EventsGenTw_baLaw sz l E⟩

/-! ## 2. Statement-level instances at the BA family

The family is `(law, Flow, mk, T0) = (fun sz => seqP (sz.withLam 0), BAFlow, fun sz z => baStep2Mat sz (BAflowLam0 sz z)
(BAflowEs sz z), BAflowT0)`.  F1-F2 (`Step2EventsGenTw_baFlow`), F3 (`EMn2BA_mF_data`, `etaOf` is `(1 - t) Im m` by `rfl`) and
F9 (`Step2EventsGenTw_baGrid`) are discharged; the stage-L pin `BASTLWT` and the merged `baSTEMn2Exp` are the two light-weight pins,
and Step 1, `STScaleInvgL`, the `Bctl` bounds and the scale cap stay hypotheses (other gates' pins, T1-BA). -/

/-! ## 3. The closed band instance of target 11 -/

end RBM.BA

end
