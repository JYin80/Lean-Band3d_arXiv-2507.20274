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
# The Step 2 iteration at the block Anderson carrier, second half (BA-T row T1-BA, ticket T2487)

Check file `docs/tickets/checks/T2487-check.lean`; continuation of `BA/Step2IterBA.lean` (targets 1-7).  No merged file is edited.

* **Target 8** `baSTOptL2gL_holds`: `(eq:opt_L2)` at BA, `stOptL2_of_pinsg` at the BA family; the light-weight input is `BALWterm` (stage L).
* **Target 9 (GMN-C1)** `baSTLocalAvgOfL2gL_holds`: the primed BA reader of the Step 2 local bound, `stLocalAvgOfL2_holdsDecG` at `baStep2Data`; the Green
  input is `STGijDecgL` (the pin's hypothesis), `(GiiGEX)`, `(GavLGEX)` are G7.
* **Target 9b** `baSTGijDecgL_holds` (ticket note (3), dispatcher answer (3), the 1a prices it at 45 lines): the Green input at BA, from the merged
  `baGbEXPij'_holds` (`BA/GreenOff.lean:1289`): the two-charge loop premise of `STGijDecgL` is restricted to `(-,+)`.
* **Target 10** (private) `Step2CloseBA_step2_of_pins`: the body of `ST_step2_of_pinsg` (`Chain/Step2IterGen2.lean:299-371`) with the one-loop input read
  under `0 < κ` and the flow (finding F2).
* **Target 11** `baStep2_holds`: `BAStep2 d` from `BALWterm d` and `BALWtermExp d` alone (the pin's third input `T2487_BAGijDec d` is discharged by
  target 9b and may be passed as an unused argument; see the instance section).
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

/-! ## 1. Target 8: `(eq:opt_L2)` at BA -/

/-- **Target 8, `baSTOptL2gL_holds`** (`3_5:466-512`, BA `7_8:1994`): `stOptL2_of_pinsg` (`Chain/OptL2Gen.lean:1109`) at the BA family.  Inputs: F1-F2
`Step2EventsGenTw_baFlow`; F9 `Step2EventsGenTw_baGrid`; F3 inline with `κm = κ` (`EMn2BA_mF_data`; pattern `Chain/Step2EventsGenTw.lean:94-109`); the
Hermitian walk (target 1); the size data (target 6); `STLWBgL` from `BALWterm d` through `stLWBgL_of_LWtermG` and `Step2EventsGenTw_baRot3`; `baSTEMn2Poly`;
`lem:newKLK` (target 5); the grid estimate `baGridMart_holds` (P1). -/
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

/-! ## 2. Target 9b and target 9: the Green input and the GMN-C1 reader at BA -/

/-- **Target 9b, `baSTGijDecgL_holds`** (the Green input of the GMN-C1 reader; `(GijGEX_BA)`, `7_8:1916-1946`): `STGijDecgL` at the BA carrier from the merged
primed pin `baGbEXPij'_holds` (`GreenOff:1289`): `c` after `(κ, ε, 𝔡)`; the two-charge loop premise of `STGijDecgL` is restricted to the charges
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

/-- **Target 9 (GMN-C1), `baSTLocalAvgOfL2gL_holds`** (`7_8:2035-2050`; `3_5:455-465`): the primed BA reader of the Step 2 local bound (with the average
bound): `stLocalAvgOfL2_holdsDecG` (`Chain/Step2CloseGen.lean:781`; its local bound is `stStep2LocalPT_of_L2decayDecG`, `:584`) at `baStep2Data`.
`hdat` is target 6 (reordered `∃ cB c`), `(GiiGEX)` and `(GavLGEX)` are G7 (`baSTGiiGEXgL_holds`, `baSTGavLGEXgL_holds`), `hGij` is the pin's Green
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

/-! ## 3. Target 10: the guarded skeleton (private; finding F2) -/

/-- **Target 10, `Step2CloseBA_step2_of_pins`** (private): the body of `ST_step2_of_pinsg` (`Chain/Step2IterGen2.lean:299-371`, `3_5:345-609`) with the one-loop
input read under `0 < κ` and the flow: the merged proof uses `hOne sz z` once, at its last line, where `hκ` and `hflow` are in scope; at BA the first
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

/-! ## 4. Target 11: `baStep2_holds` -/

/-- **Target 11, `baStep2_holds`** (the pin `BAStep2 d`, i.e. `STStep2G` at `(seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`; `3_5:345-609`, BA `7_8:1993-2099`):
the skeleton (target 10) at the BA family with targets 1, 2, 4-9, `baSTEMn2Exp`, `stLWTgL_of_LWtermExpG`, `baNetLift2_holds` (P2) and `baGridMart_holds`
(P1).  The inputs are the two stage-L pins `BALWterm d`, `BALWtermExp d` only: the Green input `STGijDecgL` of the pin `T2487_Step2Holds` is proved by
target 9b (dispatcher answer (3)). -/
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

/-! ## 5. Compiled nonempty instances of targets 8, 9, 9b, 11 (`d = 3`)

Data as in `BA/Step2IterBA.lean` §6: `sz0`, `zSeq`, `flow_sz0 : BAFlow sz0 zSeq` at `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, `s ≡ 1/10 < t ≡ 1/2 <
t₀` (`half_lt_t0`).  The stage-L inputs `BALWterm 3`, `BALWtermExp 3` (BA-L6) and the Step 1, `STLKgL`, `STDecaygL`, `STConStInd`,
`STL2decayPTgL` binders of the pins stay hypotheses; every deterministic premise is discharged. -/

section Instances

open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst

local notation "μ0" => Sizes.seqP (sz0.withLam 0)

/-- Target 9b at `sz0`, `zSeq`, `u ≡ 1/10 ≤ t₀`. -/
example : STGijDecgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) :=
  baSTGijDecgL_holds 3 (by norm_num) (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 10) (fun _ => by norm_num) (fun n => by have := half_lt_t0 n; show (1 / 10 : ℝ) ≤ BAflowT0 sz0 zSeq n; linarith)

/-- Target 8 at `sz0`, `zSeq`, `s ≡ 1/10`, `t ≡ 1/2`: the constant `𝔠₀` first, then the per-time estimate under the Step 1 binders. -/
example (hLW : BALWterm 3) : ∃ 𝔠₀ : ℝ, 0 < 𝔠₀ ∧ ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 𝔠₀ →
    STLKgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) → STConStInd sz0 𝔠d (fun _ => 1 / 10) (fun _ => 1 / 2) →
      STStep1LoopgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) →
      STStep1WeakgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) →
        PrecPTL sz0 μ0 (U := fun n => TimeIcc (fun _ => 1 / 10) (fun _ => 1 / 2) n × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
          (fun n p ω => ‖(baFMz sz0 zSeq).L n (p.1 : ℝ) p.2.1 p.2.2 ω - (baFMz sz0 zSeq).K n (p.1 : ℝ) p.2.1 p.2.2‖)
          (fun n p _ => sz0.Bctl n (p.1 : ℝ)) := by
  obtain ⟨𝔠₀, h𝔠₀, h⟩ := baSTOptL2gL_holds 3 le_rfl hLW (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨𝔠₀, h𝔠₀, fun 𝔠d h1 h2 => h 𝔠d h1 h2 (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 10) (fun _ => 1 / 2) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)⟩

/-- Target 9 at `sz0`, `zSeq`, with the Green input discharged by target 9b. -/
example : STStep1WeakgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) →
    STL2decayPTgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) →
      STStep2LocalPTgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) ∧
        STStep2AvgPTgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) :=
  baSTLocalAvgOfL2gL_holds 3 (by norm_num) (baSTGijDecgL_holds 3 (by norm_num)) (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 10) (fun _ => 1 / 2) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun n => (half_lt_t0 n).le)

/-- Target 11 at `sz0`, `zSeq`, `s ≡ 1/10 < t ≡ 1/2`: constants `C_d, 𝔠_d` first, then the conclusion bundle under the binders of `STStep2G`. -/
example (hLW : BALWterm 3) (hLWE : BALWtermExp 3) : ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
    (STLKgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) → STDecaygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) →
      STConStInd sz0 𝔠d (fun _ => 1 / 10) (fun _ => 1 / 2) →
      STStep1LoopgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) →
      STStep1WeakgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) →
        STStep2ConclgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) Cd) := by
  obtain ⟨Cd, hCd, 𝔠d, h𝔠d, h𝔠d1, h⟩ := baStep2_holds 3 hLW hLWE le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨Cd, hCd, 𝔠d, h𝔠d, h𝔠d1, h (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 10) (fun _ => 1 / 2) (fun _ => by norm_num)
    (fun n => by have := half_lt_t0 n; show (1 / 10 : ℝ) ≤ BAflowT0 sz0 zSeq n; linarith) (fun _ => by norm_num)
    (fun n => (half_lt_t0 n).le)⟩

/-- The pin `T2487_Step2Holds` (three inputs, the third being the Green input `T2487_BAGijDec d` written out) follows from `baStep2_holds`
by an unused third argument. -/
example (d : ℕ) : BALWterm d → BALWtermExp d →
    (∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ BAflowT0 sz z n) →
        STGijDecgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u) → BAStep2 d :=
  fun hL hE _ => baStep2_holds d hL hE

end Instances

end RBM.BA
