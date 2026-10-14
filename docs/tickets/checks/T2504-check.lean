/-
Release check for T2504 (dispatcher V4, 2026-10-14; DECISIONS §318).  V V3: the BA terminal of the main induction in
family form, new leaf `BA/MainIndOutBA` (supervisor 2026-10-14-0342 Q1 (i)-(v), Q2, Q5 (b), V-C1; design T2503 D3 (c)-(d),
D4 row V3; REQ-2026-10-14-0330-Vopen, V3 row and Interfaces).
Part 1: merged names (`main` 58bcd8b6), declaration lines from `git grep` at drafting.  Merged `private` names that the
target file opens (`open private`) cannot be checked here; comments list them with file:line.
Part 2: pins (prefix `T2504_`).  Binding: `T2504_BAMainIndFamTL`, a verbatim copy of `docs/tickets/checks/T2503-check.lean:163-177`
with the prefix changed (it binds V2a and V2b).  Ported (statements of the T2503 probe, compiled there from merged names):
`T2504_TL2Congr`, `T2504_MemberFlow` (copies of the T2503 check `:247-249`, `:235-243`), `T2504_MemberBase`,
`T2504_TailPassage`, `T2504_ConclShift`, `T2504_BAChainFamTL` (copy of the T2503 check `:257-264`).  New: `T2504_G0M`,
`T2504_LK0`, `T2504_BaseGInit'`, `T2504_BaseGBA`, `T2504_HorizonGBA`, `T2504_MLOutOfStep`, `T2504_UNOfMLOut`, `T2504_UNOfStep`.
Shapes: the d = 3 readings.
No `open`, no namespace: every name is fully qualified.  Statements only.
Run: lake env lean docs/tickets/checks/T2504-check.lean
-/
import RBM3D.BA.TwistChain
import RBM3D.BA.Step1Fam
import RBM3D.BA.Step1Boot
import RBM3D.BA.Step1Trivial
import RBM3D.BA.CouplingWindow
import RBM3D.BA.KBound
import RBM3D.BA.KBase
import RBM3D.BA.KTreeRep
import RBM3D.BA.GreenSchur
import RBM3D.BA.EMn2BA
import RBM3D.BA.GridGoodBA
import RBM3D.BA.CltFlowBA
import RBM3D.BA.DecayLoopBA
import RBM3D.BA.LWPinsBA
import RBM3D.BA.UNPins
import RBM3D.BA.FlowPins
import RBM3D.Induction.SizesComp
import RBM3D.Induction.MainIndBase
import RBM3D.Induction.MainIndChain
import RBM3D.Induction.MainIndOut
import RBM3D.Loop.KLTree
import RBM3D.Loop.GLoopFlow

/-! ## Part 1: merged names (`main` 58bcd8b6) -/

-- TL pins (`BA/TwistPins.lean`): TL2 `:95`, base `:164`, single-flow step `:169` (off the route), output `:178`, chain pin `:185` (unused, F2)
#check @RBM.BA.BATwistLoopLaw
#check @RBM.BA.BATwistLoopBase
#check @RBM.BA.BAMainIndTL
#check @RBM.BA.BAMLOutTL
#check @RBM.BA.BAChainTL
-- TL chain (`BA/TwistChain.lean`): base `:110`, the single-flow model `:240`; private, opened: `TwistChain_LK_mix` `:194`,
-- `TwistChain_Lmax_mix` `:200`, `TwistChain_Decay_mix` `:206`, `TwistChain_Exp2_mix` `:212`, `TwistChain_LocalEntry_mix` `:218`,
-- `TwistChain_TL2_mix` `:226`
#check @RBM.BA.baTwistLoopBase_holds
#check @RBM.BA.baChainTL_holds
-- base (`Induction/MainIndBase.lean`): `:45`, `:50`, `:54`, `:58`, `:110` (K3: its `hK` has no `0 < ε`, `0 < 𝔡`), band `:128`
#check @RBM.BA.STConclgL
#check @RBM.BA.STLK0
#check @RBM.BA.STG0M
#check @RBM.BA.STBaseG
#check @RBM.BA.stBaseG_of_init
#check @RBM.BA.stBase_band
-- chain (`Induction/MainIndChain.lean`): `:43`, `:51`, `:55`, `:58`, `:62`, `:80`, `:126`, band horizon `:180`
#check @RBM.BA.STHorizonG
#check @RBM.BA.stChainTime
#check @RBM.BA.stChainTime_zero
#check @RBM.BA.stChainTime_top
#check @RBM.BA.stChainTime_facts
#check @RBM.BA.stChainSteps
#check @RBM.BA.STLocalMaxgL_of_STLocalEntrygL
#check @RBM.BA.stHorizon_band
-- the family (`BA/Step1Trivial.lean`): `:42`, `:47`, main flow `:56` (closing condition (i))
#check @RBM.BA.BAFamZ
#check @RBM.BA.BAflow_T0_bounds
#check @RBM.BA.BAFamZ_main
-- (`BA/Step1Boot.lean`): `:133`, `:173`, `:179`, `:185`; private, opened: `Boot_GM_zero` `:358` (`G_0 = M` at every `(lam0, E)`)
#check @RBM.BA.BAFlowMember
#check @RBM.BA.BAFamZ_mono
#check @RBM.BA.BAFamZ_horizon
#check @RBM.BA.PrecL_congr
-- (`BA/Step1Fam.lean`): `:63`, `:74`, `:158`, `:172`, `:197`, congruences `:205-247`, `:273`, `:361`, `:624`
#check @RBM.BA.BAzSrc
#check @RBM.BA.BAflowT0_congr
#check @RBM.BA.BAFamZ_closed
#check @RBM.BA.BAFamZ_mono_max
#check @RBM.BA.FlowFM.EvEq
#check @RBM.BA.STLKgL_congr
#check @RBM.BA.STLmaxgL_congr
#check @RBM.BA.STDecaygL_congr
#check @RBM.BA.STDecayStronggL_congr
#check @RBM.BA.STLocalMaxgL_congr
#check @RBM.BA.STLocalEntrygL_congr
#check @RBM.BA.STExp2gL_congr
#check @RBM.BA.STKboundgL_congr
#check @RBM.BA.baFMz_eqAt
#check @RBM.BA.BAStep1
#check @RBM.BA.BAFlowMember_holds
-- window and K-bound: `BA/CouplingWindow.lean:799, 836`; `BA/KBound.lean:196, 245`
#check @RBM.BA.BAWinBulk
#check @RBM.BA.BAWinBulk_of_dom_holds
#check @RBM.BA.BAKbound
#check @RBM.BA.baKbound_holds
#check @RBM.BA.STKboundgL
-- the tail (`Induction/SizesComp.lean`): `:55`, `:93`, `:222`, `:239`, `:253`, `:536`
#check @RBM.Gauss.Sizes.comp
#check @RBM.Gauss.Sizes.comp_admissible
#check @RBM.Gauss.Sizes.reindex
#check @RBM.Gauss.Sizes.seqP_withLam_reindex_preimage
#check @RBM.Gauss.Sizes.integral_reindex
#check @RBM.Gauss.Sizes.stochDomAt_iff_comp_cover
-- carrier and flow data (`BA/FlowPins.lean`): `:259`, `:264`, `:276`, `:283`, `:298`, `:322`, `:380`, `:389`, `:393`
#check @RBM.BA.BAGt
#check @RBM.BA.BALloop
#check @RBM.BA.BAMLoop
#check @RBM.BA.BAKsol
#check @RBM.BA.BAKloop
#check @RBM.BA.baFM
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAFlow
#check @RBM.BA.baFMz
-- `𝓛_0 = 𝒦_0` inputs: `BA/GreenSchur.lean:59, 93`; `BA/KTreeRep.lean:1674`; `Loop/KLTree.lean:828, 149`; `Loop/GLoopFlow.lean:117`;
-- `BA/KBase.lean:434`; private, opened: `GridGoodBA_loopFine_init` `BA/GridGoodBA.lean:566`, `GridGoodBA_BAMLoop_one_loop` `:591`,
-- `CltFlowBA_Ksol_isKLoopS` `BA/CltFlowBA.lean:362`; not used: `GridGoodBA_KI_init` `:603`, `GridGoodBA_LM_sub_K_zero` `:967` (need `0 < g₀ n`)
#check @RBM.BA.BAflow_real
#check @RBM.BA.BAMfine_eq
#check @RBM.BA.baKcac_isKLoopS
#check @RBM.Loop.IsKLoopS
#check @RBM.Loop.KLloopOf
#check @RBM.Gauss.loopOf
#check @RBM.BA.BAMLoop_trace
-- horizon inputs (`BA/EMn2BA.lean`): `:99`, `:106`, `:111`, `:125` (its docstring `:124` gets the comment fix);
-- private, opened: `CltFlowBA_one_sub_T0` `BA/CltFlowBA.lean:543`
#check @RBM.BA.EMn2BA_mim_le_one
#check @RBM.BA.EMn2BA_T0_lt_one
#check @RBM.BA.EMn2BA_one_sub_T0
#check @RBM.BA.EMn2BA_mF_data
-- UN side: `BA/UNPins.lean:110`; route G, stays unused: `Induction/MainIndOut.lean:144`
#check @RBM.Univ.UNMLOutBA
#check @RBM.Univ.unMLOutBA_of_pins
-- F1: `BA/LWPinsBA.lean:51, 53` (comments `:50, :52`) and the producers `BA/DecayLoopBA.lean:135, 140`
#check @RBM.BA.BASTLWB
#check @RBM.BA.BASTLWT
#check @RBM.BA.baSTLWB_of
#check @RBM.BA.baSTLWT_of
-- regime-free regime `Induction/Step34Pins.lean:272`; the law `Gauss/FineModel.lean:171`; `withLam` `Defs/Sizes.lean:182`
#check @RBM.Gauss.Sizes.STAny
#check @RBM.Gauss.Sizes.isProbabilityMeasure_seqP
#check @RBM.Gauss.Sizes.withLam
-- d = 3 data: `Defs/Sizes.lean:260`; `BA/FlowPins.lean:1181, 1184, 1214, 1254`; `BA/Step1Fam.lean:748, 802, 820`
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.sz0_lam_pos
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0
#check @RBM.BA.Step1FamInst.t0_sz0_ge
#check @RBM.BA.Step1FamInst.sz0_win_third
#check @RBM.BA.Step1FamInst.inst_BAFamZ_closed

/-! ## Part 2: pins -/

/-- **Target 1 (binding; T2503 D1): the family step** `BAMainIndFamTL d R`, verbatim from the T2503 check `:163-177`.
V3 publishes it as `RBM.BA.BAMainIndFamTL` (answer (1)); V2a proves it per regime, V2b at `STAny`. -/
def T2504_BAMainIndFamTL (d : ℕ) (R : ∀ {d : ℕ}, RBM.Gauss.Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
    ∀ (𝔠 : ℝ) (sz : RBM.Gauss.Sizes d) (z : ℕ → ℂ), RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
      ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → RBM.BA.BAWinBulk sz z c₁ κ →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ RBM.BA.BAflowT0 sz z n) → (∀ n, s n < t n) →
        (∀ n, t n ≤ RBM.BA.BAflowT0 sz z n) → R sz s t →
        (∀ z' : ℕ → ℂ, RBM.BA.BAFamZ sz z c₁ s z' →
          let C := RBM.BA.baFMz sz z'; let μ := RBM.Gauss.Sizes.seqP (sz.withLam 0)
          RBM.BA.STLKgL C μ s ∧ RBM.BA.STDecaygL C μ s ∧ RBM.BA.STDecayStronggL C μ s ∧ RBM.BA.STLocalMaxgL C μ s ∧
            RBM.BA.STExp2gL C μ s ∧ RBM.BA.BATwistLoopLaw C μ s) →
        sz.STConStInd 𝔠d s t →
        ∀ z' : ℕ → ℂ, RBM.BA.BAFamZ sz z c₁ t z' →
          let C := RBM.BA.baFMz sz z'; let μ := RBM.Gauss.Sizes.seqP (sz.withLam 0)
          RBM.BA.STLKgL C μ t ∧ RBM.BA.STLmaxgL C μ t ∧ RBM.BA.STDecaygL C μ t ∧ RBM.BA.STExp2gL C μ t ∧
            RBM.BA.STLocalEntrygL C μ t ∧ RBM.BA.STDecayStronggL C μ t ∧ RBM.BA.BATwistLoopLaw C μ t

/-- **Target 2 (a)**: TL2 is tail-local (`BATwistLoopLaw_congr`; T2503 check `:247-249`, probe `:95`). -/
def T2504_TL2Congr : Prop :=
  ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d) (C C' : RBM.BA.FlowFM sz) (μ : MeasureTheory.Measure sz.SeqΩ) (τ : ℕ → ℝ),
    RBM.BA.FlowFM.EvEq C C' → (RBM.BA.BATwistLoopLaw C μ τ ↔ RBM.BA.BATwistLoopLaw C' μ τ)

/-- **Target 2 (b)**: a member of `Fam(t)` is, after the finite modification below `n₀`, a `BAFlow` at `(κ', ε')` with horizon
`≥ t` at every `n` (`baFamMember_flow`; T2503 check `:235-243`, probe `:115`). -/
def T2504_MemberFlow (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ κ' ε' : ℝ, 0 < κ' ∧ κ' ≤ κ ∧ 0 < ε' ∧ ε' ≤ ε ∧
    ∀ (𝔠 : ℝ) (sz : RBM.Gauss.Sizes d) (z : ℕ → ℂ), RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
      ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → RBM.BA.BAWinBulk sz z c₁ κ →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ RBM.BA.BAflowT0 sz z n) →
      ∀ z' : ℕ → ℂ, RBM.BA.BAFamZ sz z c₁ t z' →
        (∀ n, t n ≤ RBM.BA.BAflowT0 sz z' n) ∧
          ∃ z'' : ℕ → ℂ, RBM.BA.BAFlow sz κ' ε' 𝔠 𝔡 z'' ∧ (∀ n, t n ≤ RBM.BA.BAflowT0 sz z'' n) ∧
            RBM.BA.FlowFM.EvEq (RBM.BA.baFMz sz z'') (RBM.BA.baFMz sz z')

/-- **Target 3**: the per-member base at the zero sequence (`baFamMember_base`; probe `:142-145`, statement unchanged). -/
def T2504_MemberBase (d : ℕ) : Prop :=
  RBM.BA.STBaseG d (fun sz => RBM.Gauss.Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z)
      RBM.BA.baFMz →
    (∀ κ ε 𝔠 𝔡 (sz : RBM.Gauss.Sizes d) z, RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z → RBM.BA.STG0M (RBM.BA.baFMz sz z)) →
    3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : RBM.Gauss.Sizes d) (z : ℕ → ℂ),
      RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
      ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → RBM.BA.BAWinBulk sz z c₁ κ →
      ∀ z' : ℕ → ℂ, RBM.BA.BAFamZ sz z c₁ (fun _ => 0) z' →
        RBM.BA.STConclgL (RBM.BA.baFMz sz z') (RBM.Gauss.Sizes.seqP (sz.withLam 0)) (fun _ => 0) ∧
          RBM.BA.BATwistLoopLaw (RBM.BA.baFMz sz z') (RBM.Gauss.Sizes.seqP (sz.withLam 0)) (fun _ => 0)

/-- **Target 4**: the tail passage, route (α) (D538; `baTailPassage`; probe `:155-157`): from `WO` a tail
`sz.comp (· + n₀)` with `0 < lam`, a `BAFlow` at `κ/2` and the window at `κ/2`; `c₁` before `(ε, 𝔠, sz, z)`. -/
def T2504_TailPassage (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 →
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 2 ∧ ∀ (ε 𝔠 : ℝ) (sz : RBM.Gauss.Sizes d) (z : ℕ → ℂ), RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z →
      ∃ n₀ : ℕ, RBM.BA.BAFlow (sz.comp (· + n₀)) (κ / 2) ε 𝔠 𝔡 (fun j => z (j + n₀)) ∧
        (∀ j, 0 < (sz.comp (· + n₀)).lam j) ∧
        RBM.BA.BAWinBulk (sz.comp (· + n₀)) (fun j => z (j + n₀)) c₁ (κ / 2)

/-- **Target 5**: the seven conclusions along the tail give the seven along `sz` (`baConclShift`; probe `:177-183`;
`{d}` implicit as there). -/
def T2504_ConclShift : Prop :=
  ∀ {d : ℕ} (sz : RBM.Gauss.Sizes d) (z : ℕ → ℂ) (τ : ℕ → ℝ) (n₀ : ℕ),
    let C₁ := RBM.BA.baFMz (sz.comp (· + n₀)) (fun j => z (j + n₀))
    let μ₁ := RBM.Gauss.Sizes.seqP ((sz.comp (· + n₀)).withLam 0)
    let τ₁ : ℕ → ℝ := fun j => τ (j + n₀)
    (RBM.BA.STLKgL C₁ μ₁ τ₁ ∧ RBM.BA.STLmaxgL C₁ μ₁ τ₁ ∧ RBM.BA.STDecaygL C₁ μ₁ τ₁ ∧ RBM.BA.STExp2gL C₁ μ₁ τ₁ ∧
      RBM.BA.STLocalEntrygL C₁ μ₁ τ₁ ∧ RBM.BA.STDecayStronggL C₁ μ₁ τ₁ ∧ RBM.BA.BATwistLoopLaw C₁ μ₁ τ₁) →
    let C := RBM.BA.baFMz sz z; let μ := RBM.Gauss.Sizes.seqP (sz.withLam 0)
    RBM.BA.STLKgL C μ τ ∧ RBM.BA.STLmaxgL C μ τ ∧ RBM.BA.STDecaygL C μ τ ∧ RBM.BA.STExp2gL C μ τ ∧
      RBM.BA.STLocalEntrygL C μ τ ∧ RBM.BA.STDecayStronggL C μ τ ∧ RBM.BA.BATwistLoopLaw C μ τ

/-- **Target 6**: the family twin of `BAChainTL` (T2503 check `:257-264`; probe `:197-200`).  The target
`baChainFamTL_holds` states it with explicit hypotheses (no `BAChainFamTL` def), conclusion head `BAMLOutTL`. -/
def T2504_BAChainFamTL (d : ℕ) : Prop :=
  T2504_BAMainIndFamTL d RBM.Gauss.Sizes.STAny →
    RBM.BA.STHorizonG d (fun sz κ ε 𝔠 𝔡 z => RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => RBM.BA.BAflowT0 sz z) →
    RBM.BA.STBaseG d (fun sz => RBM.Gauss.Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z)
      RBM.BA.baFMz →
    RBM.BA.BATwistLoopBase d →
    (∀ κ ε 𝔠 𝔡 (sz : RBM.Gauss.Sizes d) z, RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z → RBM.BA.STG0M (RBM.BA.baFMz sz z)) →
    RBM.BA.BAMLOutTL d

/-- **Target 7**: `G_0 = M` at the BA carrier, uniform over `BAFlow` (`baG0M_holds`; from `Boot_GM_zero`). -/
def T2504_G0M (d : ℕ) : Prop :=
  ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : RBM.Gauss.Sizes d) (z : ℕ → ℂ), RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z → RBM.BA.STG0M (RBM.BA.baFMz sz z)

/-- **Target 8**: `𝓛_0 = 𝒦_0` at the BA carrier at every `n`, uniform over `BAFlow` (`baLK0_holds`). -/
def T2504_LK0 (d : ℕ) : Prop :=
  ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : RBM.Gauss.Sizes d) (z : ℕ → ℂ), RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z → RBM.BA.STLK0 (RBM.BA.baFMz sz z)

/-- **Target 9 (a), generic (K3, supervisor 0150 `:87-93`)**: `stBaseG_of_init` with `hK` under `0 < ε → 0 < 𝔡 →`
(`stBaseG_of_init'`; `STBaseG` supplies both, `Induction/MainIndBase.lean:58`). -/
def T2504_BaseGInit' : Prop :=
  ∀ {d : ℕ} {law : ∀ sz : RBM.Gauss.Sizes d, MeasureTheory.Measure sz.SeqΩ}
    {Flow : ∀ (sz : RBM.Gauss.Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop}
    {mk : ∀ (sz : RBM.Gauss.Sizes d) (z : ℕ → ℂ), RBM.BA.FlowFM sz},
    (∀ sz, MeasureTheory.IsProbabilityMeasure (law sz)) →
    (∀ κ ε 𝔠 𝔡 sz z, Flow sz κ ε 𝔠 𝔡 z → RBM.BA.STLK0 (mk sz z)) →
    (∀ κ ε 𝔠 𝔡 sz z, Flow sz κ ε 𝔠 𝔡 z → RBM.BA.STG0M (mk sz z)) →
    (3 ≤ d → ∀ κ ε 𝔠 𝔡 sz z, 0 < κ → 0 < ε → 0 < 𝔡 → Flow sz κ ε 𝔠 𝔡 z → RBM.BA.STKboundgL (mk sz z) (law sz)) →
    RBM.BA.STBaseG d law Flow mk

/-- **Target 9 (b)**: the base case at the BA data (`baBaseG_holds`; registry `Test/Axioms.lean:140`). -/
def T2504_BaseGBA (d : ℕ) : Prop :=
  RBM.BA.STBaseG d (fun sz => RBM.Gauss.Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z)
    RBM.BA.baFMz

/-- **Target 10**: the horizon at the BA data (`baHorizonG_holds`; `BAflowT0`, `Im m ≤ 1`; registry `:141`). -/
def T2504_HorizonGBA (d : ℕ) : Prop :=
  RBM.BA.STHorizonG d (fun sz κ ε 𝔠 𝔡 z => RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => RBM.BA.BAflowT0 sz z)

/-- **Target 11 (a)**: the terminal plug-in (`baMLOutTL_of_famStep`): only the family step stays a hypothesis. -/
def T2504_MLOutOfStep (d : ℕ) : Prop :=
  T2504_BAMainIndFamTL d RBM.Gauss.Sizes.STAny → RBM.BA.BAMLOutTL d

/-- **Target 11 (b)**: V3 is the projection (`unMLOutBA_of_BAMLOutTL`; T2449 MN2, probe `t/T2449` `:259`). -/
def T2504_UNOfMLOut (d : ℕ) : Prop :=
  RBM.BA.BAMLOutTL d → RBM.Univ.UNMLOutBA d

/-- **Target 11 (c)**: the composite (`unMLOutBA_of_famStep`). -/
def T2504_UNOfStep (d : ℕ) : Prop :=
  T2504_BAMainIndFamTL d RBM.Gauss.Sizes.STAny → RBM.Univ.UNMLOutBA d

/-! ### Shapes (not binding) -/

/-- d = 3, at V2b (answer (8)): the family step at `d = 3` gives both terminal outputs (closing condition (i)). -/
example : Prop := T2504_BAMainIndFamTL 3 RBM.Gauss.Sizes.STAny → RBM.BA.BAMLOutTL 3 ∧ RBM.Univ.UNMLOutBA 3

/-- d = 3 instance of targets 7-9: the six conclusions at the zero sequence at `zSeq`, with no hypothesis. -/
example : Prop :=
  RBM.BA.STConclgL (RBM.BA.baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq)
    (RBM.Gauss.Sizes.seqP (RBM.Gauss.Sizes.withLam RBM.Gauss.SizesInst.sz0 0)) (fun _ => 0)

/-- d = 3 instance of target 3: the non-main member of `Fam(0)` (probe data, `κ = 1/4`, `c₁ = 1/3`). -/
example : Prop :=
  RBM.BA.BAFamZ RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq (1 / 3) (fun _ => 0)
    (RBM.BA.BAzSrc RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq (fun _ => 2 / 3) (fun _ => 17 / 25))
