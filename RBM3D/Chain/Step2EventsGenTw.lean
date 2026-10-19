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
# The Step 2 events at the block Anderson carrier

For the block Anderson carrier `baFM sz l E` and the Step 2 matrix `baStep2Mat sz l E`
(`l E : ℕ → ℝ`), this module proves the carrier hypotheses of `Chain/Step2EventsGen`:

* `Step2EventsGenTw_baFlow`: `Step2EventsGen_Flow` for `BAFlow` and `BAflowT0` (the flow is
  admissible and `t₀ < 1`; `EMn2BA_T0_lt_one`);
* `Step2EventsGenTw_baRot3`: `Step2EventsGen_Rot3`, the trace cyclicity of the 3-loop, at `baFM sz l E`;
* `Step2EventsGenTw_baLaw` and `Step2EventsGenTw_baGrid`: `Step2EventsGen_Law` and
  `Step2EventsGen_Grid` with the model matrix `seqHflowBA` and the law `seqP (sz.withLam 0)`.
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

/-! ## 1. The carrier hypotheses at the block Anderson carrier -/

/-- `BAFlow` implies `Admissible`, and `BAflowT0 < 1` (`EMn2BA_T0_lt_one`): `Step2EventsGen_Flow` for the block Anderson flow. -/
theorem Step2EventsGenTw_baFlow (d : ℕ) :
    Step2EventsGen_Flow d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) BAflowT0 :=
  ⟨fun _ _ _ _ _ _ h => h.1, fun sz _ _ _ _ _ hκ h n => EMn2BA_T0_lt_one hκ sz h n⟩

/-- The trace cyclicity `Step2EventsGen_Rot3` of the 3-loop at `baFM sz l E`: `BALloop` is `loopFine` at `seqHflowBA`, `ztOf`. -/
theorem Step2EventsGenTw_baRot3 {d : ℕ} (sz : Sizes d) (l E : ℕ → ℝ) : Step2EventsGen_Rot3 (baFM sz l E) :=
  fun n t σ₀ σ₁ a₀ y a₁ ω => Step2EventsGen_loopFine_rot3 _ _ σ₀ σ₁ a₀ y a₁

/-- The law clause `Step2EventsGen_Law` with `Hm = seqHflowBA`: the grid state has the law of the model matrix at the grid time,
by `ST_pathP_eq_seqP (sz.withLam 0)` at the translated set `{H | l • PsiI + H ∈ S}`
(`Hpath = l • PsiI + pathH`, `seqHflowBA = l • PsiI + seqHflow`). -/
theorem Step2EventsGenTw_baLaw {d : ℕ} (sz : Sizes d) (l E : ℕ → ℝ) :
    Step2EventsGen_Law (baStep2Mat sz l E) (Sizes.seqP (sz.withLam 0)) (fun n u => sz.seqHflowBA l n u) :=
  fun s t K n k hs hst hK S hS => by
    have hT : Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
        ((l n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + H :=
      Measurable.of_eval_matrix _ fun i j => measurable_const.add ((measurable_pi_apply j).comp (measurable_pi_apply i))
    exact ST_pathP_eq_seqP (sz.withLam 0) s t K n k hs hst hK (hS.preimage hT)

/-- `Step2EventsGen_Grid` at `baStep2Mat sz l E` and `seqP (sz.withLam 0)` with `Hm = seqHflowBA`: the first two clauses are `rfl`
(the fields `LM`, `GMM` of `baStep2Mat`), the next two are the measurability of `loopFine` and `Gres` in the matrix, and the law clause is
`Step2EventsGenTw_baLaw`. -/
theorem Step2EventsGenTw_baGrid {d : ℕ} (sz : Sizes d) (l E : ℕ → ℝ) :
    Step2EventsGen_Grid (baStep2Mat sz l E) (Sizes.seqP (sz.withLam 0)) :=
  ⟨fun n u => sz.seqHflowBA l n u, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl,
    fun n u _ σ a => walk_measurable_loopFine d (sz.L n) (sz.W n) (ztOf (BAmF sz l E n) (E n) u) σ a,
    fun n u x y => (walk_measurable_Gres_apply (ztOf (BAmF sz l E n) (E n) u) true x y).sub measurable_const,
    Step2EventsGenTw_baLaw sz l E⟩

end RBM.BA

end
