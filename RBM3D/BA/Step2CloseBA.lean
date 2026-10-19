/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.Step2IterBA
import RBM3D.BA.GridMartBA
import RBM3D.BA.Step1Prime
import RBM3D.BA.LWPinsBA
import RBM3D.BA.GreenOff

/-!
# The Step 2 iteration at the block Anderson carrier, second half

Continuation of `BA/Step2IterBA`.

* `baSTOptL2gL_holds`: `(eq:opt_L2)` (3.39) at BA, `stOptL2_of_pinsg` at the BA family; the light-weight input is `BALWterm`.
* `baSTLocalAvgOfL2gL_holds`: the BA reader of the Step 2 local bound, `stLocalAvgOfL2_holdsDecG` at `baStep2Data`; the Green
  input is `STGijDecgL` (a hypothesis), `(GiiGEX)` and `(GavLGEX)` are `baSTGiiGEXgL_holds`, `baSTGavLGEXgL_holds`.
* `baSTGijDecgL_holds`: the Green input at BA, from
  `baGbEXPij'_holds` (`BA/GreenOff`): the two-charge loop premise of `STGijDecgL` is restricted to `(-,+)`.
* (private) `Step2CloseBA_step2_of_pins`: the body of `ST_step2_of_pins` (`Induction/Step2Iterate`) with the one-loop input read
  under `0 < κ` and the flow.
* `baStep2_holds`: `BAStep2 d` from `BALWterm d` and `BALWtermExp d` alone (the Green input `STGijDecgL` is discharged by
  `baSTGijDecgL_holds`).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.maxHeartbeats false

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. `(eq:opt_L2)` at BA -/

/-- `baSTOptL2gL_holds`: `(eq:opt_L2)` (3.39) in the proof of Step 2 (Subsection 3.3, `subsec:step2_pf`) at the block Anderson model (Section 8): `stOptL2_of_pinsg` (`Chain/OptL2Gen`) at the BA family.  Inputs:
`Step2EventsGenTw_baFlow`; `Step2EventsGenTw_baGrid`; the third fact inline with `κm = κ` (`EMn2BA_mF_data`; as in `Chain/Step2EventsGenTw`); the
Hermitian walk `baStep2Mat_Hpath_herm`; the size data `baSTBdatagL_holds`; `STLWBgL` from `BALWterm d` through `stLWBgL_of_LWtermG` and `Step2EventsGenTw_baRot3`; `baSTEMn2Poly`;
`lem:newKLK` (`baStep2_newKLK`); the grid estimate `baGridMart_holds`. -/
theorem baSTOptL2gL_holds (d : ℕ) (hd : 3 ≤ d) (hLW : BALWterm d) :
    STOptL2gL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
  stOptL2_of_pinsg d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0 hd (Step2EventsGenTw_baFlow d)
    (fun sz z => Step2EventsGenTw_baGrid sz _ _)
    (fun κ hκ => ⟨κ, fun sz ε 𝔠 𝔡 z h => ⟨hκ, fun n => (EMn2BA_mF_data sz h n).1, fun n t => rfl⟩⟩)
    (fun sz z s t K n k ω => baStep2Mat_Hpath_herm sz _ _ s t K n k ω)
    (baSTBdatagL_holds d (by omega))
    (stLWBgL_of_LWtermG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) BAflowT0 baFMz hd
      (fun _ _ _ _ _ _ h => h.1) (fun sz z => Step2EventsGenTw_baRot3 sz _ _) hLW)
    (baSTEMn2Poly d) (baStep2_newKLK d) (baGridMart_holds d)

/-! ## 2. The Green input and the local-average reader at BA -/

/-- `baSTGijDecgL_holds` (the Green input of `baSTLocalAvgOfL2gL_holds`; `(GijGEX_BA)` of Lemma 8.4 `lem_GbEXP_BA`): `STGijDecgL` at the BA carrier from
`baGbEXPij'_holds` (`BA/GreenOff`): `c` after `(κ, ε, 𝔡)`; the two-charge loop premise of `STGijDecgL` is restricted to the charges
`(-,+)` by `StochDomAt.precomp_param`; `FlowFM.indMax` and `STindMaxg` have the same body and `GreenCore_decayRHS` unfolds, so the conclusion is
the one of `BAGbEXPij'`. -/
theorem baSTGijDecgL_holds (d : ℕ) (hd : 2 ≤ d) : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ),
    BAFlow sz κ ε 𝔠 𝔡 z → ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ BAflowT0 sz z n) →
      STGijDecgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u hu0 huT
  obtain ⟨c, hc, hmain⟩ := baGbEXPij'_holds d hd κ ε 𝔡 hκ hε h𝔡
  refine ⟨c, hc, fun ε₀ hε₀ D hD Φ Ψ hΦ hΨ1 hΨ2 hprem => ?_⟩
  have hprem' : GreenCore_loopPrem sz z u ε₀ Φ :=
    hprem.precomp_param (V := fun n => Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p => (⟨![false, true], by simp⟩, p))
  exact hmain 𝔠 sz z hflow u hu0 huT ε₀ hε₀ D hD Φ Ψ hΦ hΨ1 hΨ2 hprem'

/-- `baSTLocalAvgOfL2gL_holds` (the proof of Lemma 3.13 `lem: EMn2_N` at the block Anderson model, Section 8): the BA reader of the Step 2 local bound (with the average
bound): `stLocalAvgOfL2_holdsDecG` (`Chain/Step2CloseGen`; its local bound is `stStep2LocalPT_of_L2decayDecG`) at `baStep2Data`.
`hdat` is `baSTBdatagL_holds` (reordered `∃ cB c`), `(GiiGEX)` and `(GavLGEX)` are `baSTGiiGEXgL_holds`, `baSTGavLGEXgL_holds`, `hGij` is the Green
input `STGijDecgL` (the form `FarEntry` gives; no window-shaped Green input). -/
theorem baSTLocalAvgOfL2gL_holds (d : ℕ) (hd : 2 ≤ d)
    (hGij : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ BAflowT0 sz z n) →
        STGijDecgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u) :
    STLocalAvgOfL2gL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
  stLocalAvgOfL2_holdsDecG (by omega) (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => baStep2Data sz z) (fun _ _ _ _ _ _ h => h)
    (fun κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow => by
      obtain ⟨cB, hcB, h⟩ := baSTBdatagL_holds d (by omega) κ ε 𝔡 hκ hε h𝔡
      obtain ⟨c, hc, h'⟩ := h 𝔠
      exact ⟨cB, c, hcB, hc, h' sz z hflow⟩)
    (baSTGiiGEXgL_holds d hd) hGij (baSTGavLGEXgL_holds d hd)

/-! ## 3. The guarded skeleton (private) -/

/-- `Step2CloseBA_step2_of_pins` (private): the body of `ST_step2_of_pins` (`Induction/Step2Iterate`; Subsection 3.3 `subsec:step2_pf`) with the one-loop
input read under `0 < κ` and the flow: the proof of `ST_step2_of_pins` uses `hOne sz z` once, at its last line, where `hκ` and `hflow` are in scope; at BA the first
conjunct of `Step2IterGen_OneLoop` needs `BAReal` (`BAKsol` is `0` without a tree solution), hence the flow.  Every callee is public; nothing else is
changed. -/
private theorem Step2CloseBA_step2_of_pins (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (hFl : Step2EventsGen_Flow d Flow T0)
    (hGrid : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2EventsGen_Grid (mk sz z) (law sz))
    (hSpec : ∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      DecayGen_Spec (mk sz z).toFlowFM κm)
    (hHerm : ∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz),
      ((mk sz z).Hpath s t K n k ω).IsHermitian)
    (hOne : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      Step2IterGen_OneLoop (mk sz z).toFlowFM)
    (hBdata : STBdatagL d Flow T0)
    (hLWT : STLWTgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0)
    (hEMe : STEMn2ExpgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0)
    (hNew : Step2IterGen_NewKLK d Flow mk)
    (hMart : STGridMartgL d Flow mk T0)
    (hK2 : Step2IterGen_K2 d Flow mk)
    (hNet : STNetLift2gL d law Flow (fun sz z => (mk sz z).toFlowFM) T0)
    (hScale : STScaleExistsgL d Flow T0)
    (hOpt : STOptL2gL d law Flow (fun sz z => (mk sz z).toFlowFM) T0)
    (hClos : STLocalAvgOfL2gL d law Flow (fun sz z => (mk sz z).toFlowFM) T0) :
    STStep2G d law Flow (fun sz z => (mk sz z).toFlowFM) T0 := by
  intro hd3 κ ε 𝔡 hκ hε h𝔡
  have hd : 0 < d := by omega
  obtain ⟨C, δ₀, hC, hδ₀, hnew⟩ := hNew hd3 κ 𝔡 hκ h𝔡
  obtain ⟨κm, hκm⟩ := hSpec κ hκ
  obtain ⟨cB, hcB, hBc⟩ := hBdata κ ε 𝔡 hκ hε h𝔡
  obtain ⟨𝔠₀, h𝔠₀, hOptat⟩ := hOpt κ ε 𝔡 hκ hε h𝔡
  have hCd : 0 < 3 * C + 1 := by positivity
  obtain ⟨𝔠d, h𝔠d⟩ : ∃ 𝔠d : ℝ, 𝔠d = min (min (1 / 100) (1 / (60 * (3 * C + 1)))) 𝔠₀ :=
    ⟨_, rfl⟩
  have h𝔠dpos : 0 < 𝔠d := by
    rw [h𝔠d]; exact lt_min (lt_min (by norm_num) (by positivity)) h𝔠₀
  have h𝔠d1 : 𝔠d ≤ 1 / 100 := by
    rw [h𝔠d]; exact (min_le_left _ _).trans (min_le_left _ _)
  have h𝔠d3 : 𝔠d ≤ 𝔠₀ := by rw [h𝔠d]; exact min_le_right _ _
  have h𝔠d2 : (3 * C + 1) * 𝔠d ≤ 1 / 60 := by
    have h : 𝔠d ≤ 1 / (60 * (3 * C + 1)) := by
      rw [h𝔠d]; exact (min_le_left _ _).trans (min_le_right _ _)
    calc (3 * C + 1) * 𝔠d ≤ (3 * C + 1) * (1 / (60 * (3 * C + 1))) :=
          mul_le_mul_of_nonneg_left h hCd.le
      _ = 1 / 60 := by field_simp
  refine ⟨3 * C + 1, hCd, 𝔠d, h𝔠dpos, h𝔠d1, ?_⟩
  intro 𝔠 sz z hflow s t hs hsl hst htT hLK hDec hCon hS1L hS1W
  have hst' : ∀ n, s n ≤ t n := fun n => (hst n).le
  have hadm := hFl.1 sz κ ε 𝔠 𝔡 z hflow
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have h𝔠 : 0 < 𝔠 := hadm.1
  have hband : sz.Bandwidth 𝔠 := hadm.2.2.2.1
  have ht1 : ∀ n, t n < 1 := fun n => lt_of_le_of_lt (htT n) (hFl.2 sz κ ε 𝔠 𝔡 z hκ hflow n)
  obtain ⟨c, hc, hBc'⟩ := hBc 𝔠
  have hBd := hBc' sz z hflow t (fun n => (hs n).trans (hst' n)) htT
  -- the deterministic `𝒦^{(2)}` bound, eventually
  obtain ⟨C_K, hCK, hK2e⟩ := hK2 hd3 κ ε 𝔠 𝔡 hκ h𝔡 sz z hflow s t hs ht1
  -- the closure arithmetic `r^{C_d} b^{1/5} ≤ b^{1/6}`
  have hq := ST_hq_of_data sz hsz hs hst' ht1 hC h𝔠dpos h𝔠d2 hBd hc hCon
  -- the base of the iteration and the scale family
  have hbase0 := hOptat 𝔠d h𝔠dpos h𝔠d3 𝔠 sz z hflow s t hs hst' htT hLK hCon hS1L hS1W
  have hbase : STScaleInvgL (mk sz z).toFlowFM (law sz) s t (fun n u => 0) :=
    ST_base_invg (mk sz z).toFlowFM (law sz) hsz hst' hCK hK2e hbase0
  obtain ⟨Kseq, hAdm⟩ := hScale κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s t hs hst' htT
  have hKz : Kseq 0 = fun n u => 0 := funext fun n => funext fun u => hAdm.1 n u
  have hbase' : STScaleInvgL (mk sz z).toFlowFM (law sz) s t (Kseq 0) := by rw [hKz]; exact hbase
  -- one self-improving step at every level
  have hSelf : ∀ Kf : ℕ → ℝ → ℝ, STScaleOk sz s t Kf → STScaleInvgL (mk sz z).toFlowFM (law sz) s t Kf →
      STSelfImpgL (mk sz z).toFlowFM (law sz) (3 * C + 1) s t Kf := fun Kf hKok hinv =>
    ST_selfImproveg d law Flow mk T0 hFl hLWT hEMe hd hκ hε h𝔡 hflow (hκm sz ε 𝔠 𝔡 z hflow) (hGrid sz z)
      (hHerm sz z) hs hst' htT hC hδ₀ (hnew ε 𝔠 sz z hflow) hMart h𝔠dpos h𝔠d2 hDec hCon hS1W hcB hc hBd
      Kf hKok hinv
  have hdec := ST_decay_ptg (mk sz z).toFlowFM (law sz) hsz hst' hCK hSelf hK2e hq Kseq hAdm hbase'
  have hL2 := ST_L2_decay_ptg (mk sz z).toFlowFM (law sz) hsz hst' hs ht1 hCK h𝔠 hband hdec hK2e hq
  obtain ⟨hLocPT, hAvgPT⟩ := hClos κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s t hs hst' htT hS1W hL2
  obtain ⟨hl, ha, hd'⟩ := hNet κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s t hs hst' htT (3 * C + 1) hLocPT hAvgPT hdec
  exact ST_concl_of_step2g _ _ hl ha hd' (hOne sz κ ε 𝔠 𝔡 z hκ hflow) hs ht1

/-! ## 4. `baStep2_holds` -/

/-- `baStep2_holds` (`BAStep2 d`, i.e. `STStep2G` at `(seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`; Subsection 3.3 `subsec:step2_pf` and Section 8):
the skeleton `Step2CloseBA_step2_of_pins` at the BA family with `baStep2Mat_Hpath_herm`, `baStep2_oneLoop`, `baStep2_K2`, `baStep2_newKLK`, `baSTBdatagL_holds`, `baScaleExists_holds`, `baSTOptL2gL_holds`, `baSTLocalAvgOfL2gL_holds`, `baSTEMn2Exp`, `stLWTgL_of_LWtermExpG`, `baNetLift2_holds` and `baGridMart_holds`.
The inputs are `BALWterm d`, `BALWtermExp d` only: the Green input `STGijDecgL` is proved by `baSTGijDecgL_holds`. -/
theorem baStep2_holds (d : ℕ) (hLW : BALWterm d) (hLWE : BALWtermExp d) : BAStep2 d := by
  intro hd3
  have hd2 : 2 ≤ d := by omega
  have hmain := Step2CloseBA_step2_of_pins d (fun sz => Sizes.seqP (sz.withLam 0))
    (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0
    (Step2EventsGenTw_baFlow d) (fun sz z => Step2EventsGenTw_baGrid sz _ _)
    (fun κ hκ => ⟨κ, fun sz ε 𝔠 𝔡 z h => ⟨hκ, fun n => (EMn2BA_mF_data sz h n).1, fun n t => rfl⟩⟩)
    (fun sz z s t K n k ω => baStep2Mat_Hpath_herm sz _ _ s t K n k ω)
    (fun sz κ ε 𝔠 𝔡 z hκ hflow => baStep2_oneLoop sz κ ε 𝔠 𝔡 z hκ hflow)
    (baSTBdatagL_holds d (by omega))
    (stLWTgL_of_LWtermExpG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) BAflowT0 baFMz hd3
      (fun _ _ _ _ _ _ h => h.1) (fun sz z => Step2EventsGenTw_baRot3 sz _ _) hLWE)
    (baSTEMn2Exp d hd3) (baStep2_newKLK d) (baGridMart_holds d) (baStep2_K2 d) (baNetLift2_holds d)
    (baScaleExists_holds d) (baSTOptL2gL_holds d hd3 hLW)
    (baSTLocalAvgOfL2gL_holds d hd2 (baSTGijDecgL_holds d hd2))
  exact hmain hd3

end RBM.BA
