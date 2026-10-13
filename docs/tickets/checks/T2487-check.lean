/-
Release check for T2487 (dispatcher V3, 2026-10-13 03:12 UTC; DECISIONS §287).  BA-T T1-BA: the block Anderson instance of Step 2, the pin
`BAStep2` (`BA/FlowPins.lean:432`), read through T1's merged skeleton (T1a 6039f7ed, T1b 1e73b1b8) in the new BA leaf files
`BA/Step2IterBA.lean` (targets 1-7) and `BA/Step2CloseBA.lean` (targets 8-12).
Part 1: merged names.  Part 2: pins (prefix `T2487_`, content binding): the BA discharges of T1's carrier classes (Hermitian
walk, one loop, list link, `𝒦^{(2)}` decay, `lem:newKLK`), the size data, P3, `(eq:opt_L2)` at BA, the GMN-C1 reader at BA, and
the conclusion `BAStep2 d` under the two inputs of exact type (`BALWterm`/`BALWtermExp`; `T2487_BAGijDec`).  Then shapes (not
binding): the flow-guarded skeleton (finding F2), F7 at mixed coupling (finding F1), the forward profile comparison, R1 at BA,
the U2-BA one-loop bridge, `twSteps`, the alternative of note (3), the stage-L bridges, the instance data.  Part 3: the band and
generic names whose bodies targets 5, 6, 7, 10 copy (unchanged, not edited).
Coupling (UBA-C1; R1 = DECISIONS §273 (1)): no pin reads `withLam` except the law `seqP (sz.withLam 0)`; the crossing lives in
the proofs of targets 4-5 only (the two shapes marked proof-internal).  TN-C4: no `STGridRepNgL` below.
Merged names only.  Statements only; no proof terms, no placeholders.
Run: lake env lean docs/tickets/checks/T2487-check.lean
-/
import RBM3D.Chain.Step2CloseGen
import RBM3D.Chain.Step2EventsGenTw
import RBM3D.Chain.NewKLKGen
import RBM3D.Chain.SEforLnGen
import RBM3D.BA.Step2BA
import RBM3D.BA.NewKLKBA
import RBM3D.BA.KInduct
import RBM3D.BA.EMn2BA
import RBM3D.BA.GreenSchur
import RBM3D.BA.GreenLDE
import RBM3D.BA.GreenCore
import RBM3D.BA.GreenOff
import RBM3D.BA.TwistStep2
import RBM3D.BA.TwistPins
import RBM3D.BA.NetLiftBA
import RBM3D.BA.GridMartBA
import RBM3D.BA.Step1Prime
import RBM3D.BA.LWPinsBA
import RBM3D.BA.Step5IIIKer
import RBM3D.Induction.Step2Scale
import RBM3D.Induction.Step2Iterate

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the pin and the BA Step 2 carrier (row 0, T8-BA)
#check @RBM.BA.BAStep2
#check @RBM.BA.BAStep2_iff_STStep2G
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.BA.baFM
#check @RBM.BA.baFMz
#check @RBM.BA.baStep2Mat
#check @RBM.BA.baStep2Mat_Hpath
#check @RBM.BA.baStep2Mat_Pp
#check @RBM.BA.baStep2Mat_KI
#check @RBM.BA.baStep2Data
#check @RBM.BA.baStep2Data_toFlowFM
#check @RBM.BA.baStep2Fam
#check @RBM.BA.baStep2Fam_K
#check @RBM.BA.baStep2Fam_lam_pos_le
#check @RBM.BA.BAKsol
-- T1a (`Chain/Step2IterGen`, `Step2IterGen2`): the carrier classes, the skeleton and its callees
#check @RBM.BA.Step2IterGen_NewKLKAtN
#check @RBM.BA.Step2IterGen_NewKLK
#check @RBM.BA.Step2IterGen_K2
#check @RBM.BA.Step2IterGen_OneLoop
#check @RBM.BA.step2IterGen_newKLK_band
#check @RBM.BA.step2IterGen_K2_band
#check @RBM.BA.step2IterGen_oneLoop_band
#check @RBM.BA.ST_good_engineg
#check @RBM.BA.ST_selfImproveg
#check @RBM.BA.ST_base_invg
#check @RBM.BA.ST_decay_ptg
#check @RBM.BA.ST_L2_decay_ptg
#check @RBM.BA.ST_avgU_of_avgg
#check @RBM.BA.ST_concl_of_step2g
#check @RBM.BA.ST_step2_of_pinsg
#check @RBM.BA.stBdatagL_band
#check @RBM.BA.stScaleExistsgL_band
#check @RBM.BA.step2IterGen_step2_of_pins_band
-- T1b (`Chain/OptL2Gen`, `Step2CloseGen`): `(eq:opt_L2)`, the list link, the GMN-C1 generic reader
#check @RBM.BA.stOptL2_of_pinsg
#check @RBM.BA.Step2IterGen_ListLink
#check @RBM.BA.step2IterGen_listLink_band
#check @RBM.BA.stStep2LocalPT_of_L2decayDecG
#check @RBM.BA.stLocalAvgOfL2_holdsDecG
#check @RBM.BA.step2CloseGen_stLocalAvgOfL2_band
#check @RBM.BA.step2CloseGen_step2_of_pinsLW'
-- the Step 2 pins over a carrier (T8, T8b, T7b, X1a)
#check @RBM.BA.STStep2G
#check @RBM.BA.STStep2ConclgL
#check @RBM.BA.STLocalEntryUgL
#check @RBM.BA.STAvgUgL
#check @RBM.BA.STGdecayWgL
#check @RBM.BA.STNetLift2gL
#check @RBM.BA.STLocalAvgOfL2gL
#check @RBM.BA.STOptL2gL
#check @RBM.BA.STScaleExistsgL
#check @RBM.BA.STLWBgL
#check @RBM.BA.STLWTgL
#check @RBM.BA.STEMn2PolygL
#check @RBM.BA.STEMn2ExpgL
#check @RBM.BA.STGridMartgL
#check @RBM.BA.STBdatagL
#check @RBM.BA.STGiiGEXgL
#check @RBM.BA.STGijGEXgL
#check @RBM.BA.STGavLGEXgL
#check @RBM.BA.STGijDecgL
#check @RBM.BA.stGijDecgL_of_gex
#check @RBM.BA.STL2decayPTgL
#check @RBM.BA.STStep2DecayPTgL
#check @RBM.BA.STScaleInvgL
#check @RBM.BA.STGoodAtg
#check @RBM.BA.STStep1WeakgL
#check @RBM.BA.STStep1LoopgL
#check @RBM.BA.STLKgL
#check @RBM.BA.STDecaygL
#check @RBM.BA.STmsigg
#check @RBM.BA.Step2Gen_thetaKer
#check @RBM.BA.Step2EventsGen_Flow
#check @RBM.BA.Step2EventsGen_Grid
#check @RBM.BA.Step2EventsGen_Rot3
#check @RBM.BA.DecayGen_Spec
#check @RBM.BA.stLWBgL_of_LWtermG
#check @RBM.BA.stLWTgL_of_LWtermExpG
#check @RBM.BA.LWtermG
#check @RBM.BA.LWtermExpG
-- the carrier facts at BA (T7b leaf, `BA/EMn2BA`, `BA/GreenSchur`, `BA/GreenLDE`, `BA/TwistStep2`)
#check @RBM.BA.Step2EventsGenTw_baFlow
#check @RBM.BA.Step2EventsGenTw_baGrid
#check @RBM.BA.Step2EventsGenTw_baRot3
#check @RBM.BA.Step2EventsGenTw_toFlowFM
#check @RBM.BA.EMn2BA_mF_data
#check @RBM.BA.EMn2BA_T0_lt_one
#check @RBM.BA.EMn2BA_one_sub_T0
#check @RBM.BA.EMn2BA_seqHflowBA_herm
#check @RBM.BA.BAflow_real
#check @RBM.BA.BAflow_lam0_window
#check @RBM.BA.ba_G_data
#check @RBM.BA.TwistStep2_T0_ge
#check @RBM.BA.TwistStep2_lam0_sq
#check @RBM.BA.baStep5III_lam0_le_lam
-- the K-side BA inputs (T3-BA `BA/NewKLKBA`, `Chain/NewKLKGen`, `BA/KInduct`)
#check @RBM.BA.baKsol_one
#check @RBM.BA.stNewKLKgL'_ba
#check @RBM.BA.stK2decaygL'_ba
#check @RBM.BA.baNewKLKGenHyp
#check @RBM.BA.NewKLKGenHyp
#check @RBM.BA.STNewKLKAtgL'
#check @RBM.BA.stNewKLKAtgL'_of
#check @RBM.BA.stNewKLKgL'_of
#check @RBM.BA.STK2decaygL'
-- merged BA producers of T1's pins (P1, P2/P6, G7, EMn2-BA, stage L pins)
#check @RBM.BA.baGridMart_holds
#check @RBM.BA.baNetLift2_holds
#check @RBM.BA.baFlow_premises
#check @RBM.BA.baSTEMn2Poly
#check @RBM.BA.baSTEMn2Exp
#check @RBM.BA.baSTGiiGEXgL_holds
#check @RBM.BA.baSTGavLGEXgL_holds
#check @RBM.BA.baStep1_holds'
#check @RBM.BA.BAStep1
#check @RBM.BA.BAGbEXPij'
#check @RBM.BA.baGbEXPij'_holds
#check @RBM.BA.baPin
#check @RBM.BA.BALWterm
#check @RBM.BA.BALWtermExp
#check @RBM.BA.BASTLWB
#check @RBM.BA.BASTLWT
-- consumers (V, U2-BA)
#check @RBM.BA.twSteps
#check @RBM.BA.SEforLnGen_Facts
-- model-free and size-level vocabulary
#check @RBM.Gauss.Sizes.STprof
#check @RBM.Gauss.Sizes.STScaleAdm
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Path.PathΩ
#check @RBM.Path.pathH_isHermitian
#check @RBM.Gauss.PsiI_isHermitian
#check @RBM.Gauss.loopM_eq_loopL
#check @RBM.PropSpin
-- the instance data (`d = 3`)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0

/-! ## Part 2: pins (content binding), then shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Input (b) of the ticket** (exact type; owner U4-BA, registry `STGijDecgL`): the Green input of the GMN-C1 reader at BA, the
hypothesis `hGij` of `stLocalAvgOfL2_holdsDecG` (`Chain/Step2CloseGen.lean:781`) at the family `baStep2Data` (its projections
`toFlowFM`, `T0`, `flowOK` are `baFMz`, `BAflowT0`, `BAFlow`, definitionally). -/
def T2487_BAGijDec (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ BAflowT0 sz z n) →
      STGijDecgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u

/-- **Target 1, `baStep2Mat_Hpath_herm`**: the grid walk of the BA carrier is Hermitian (`Hpath = lam0 • Ψ + pathH (sz.withLam 0)`,
`baStep2Mat_Hpath`), for every `lam0, E`: the input `hHerm` of `ST_step2_of_pinsg` and `stOptL2_of_pinsg`. -/
def T2487_HpathHerm : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz),
    ((baStep2Mat sz lam0 E).Hpath s t K n k ω).IsHermitian

/-- **Target 2, `baStep2_oneLoop`** (the single BA one-loop proof, supervisor 0149 U2-C3): `Step2IterGen_OneLoop` at `baFMz sz z`
under `0 < κ` and the flow.  Finding F2: `BAKsol` is `0` when no tree solution exists (`BA/FlowPins.lean:283`), so the first
conjunct needs `BAReal` (`BAflow_real`) and has no flow-free form. -/
def T2487_OneLoop : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
    Step2IterGen_OneLoop (baFMz sz z)

/-- **Target 3, `baStep2Mat_listLink`**: the class `Step2IterGen_ListLink` (`Chain/Step2CloseGen.lean:65`) at the BA carrier, for
every `lam0, E` (`loopM_eq_loopL`; `baStep2Mat_KI`, definitional). -/
def T2487_ListLink : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ), Step2IterGen_ListLink (baStep2Mat sz lam0 E)

/-- **Target 4, `baStep2_K2`**: the class `Step2IterGen_K2` at the BA family (profile at `sz`, kernel at `BAflowLam0 sz z`). -/
def T2487_K2 : Prop :=
  ∀ d : ℕ, Step2IterGen_K2 d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))

/-- **Target 5, `baStep2_newKLK`**: the class `Step2IterGen_NewKLK` at the BA family; `C, δ₀` come before the sizes, so the
constant is uniform in `(sz, z)` (finding F1). -/
def T2487_NewKLK : Prop :=
  ∀ d : ℕ, Step2IterGen_NewKLK d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))

/-- **Target 6, `baSTBdatagL_holds`**: the size data at the BA setting and horizon (band `ST_Bdata_holds`,
`Induction/Step2Iterate.lean:1049`; `1 - t₀ ≥ Im z / 2`, `EMn2BA_one_sub_T0`). -/
def T2487_Bdata : Prop :=
  ∀ d : ℕ, 0 < d → STBdatagL d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) BAflowT0

/-- **Target 7, P3 `baScaleExists_holds`** (design T2452 `:183`, `:193`; band `stScaleExists_holds`, `Induction/Step2Scale.lean:430`;
the flow premises are P6 `baFlow_premises`). -/
def T2487_ScaleExists : Prop :=
  ∀ d : ℕ, STScaleExistsgL d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) BAflowT0

/-- **Target 8, `baSTOptL2gL_holds`**: `(eq:opt_L2)` at the BA reading through `stOptL2_of_pinsg`; the light-weight input is the
stage-L pin `BALWterm` (input (a)). -/
def T2487_OptL2 : Prop :=
  ∀ d : ℕ, 3 ≤ d → BALWterm d →
    STOptL2gL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0

/-- **Target 9 (GMN-C1), `baSTLocalAvgOfL2gL_holds`**: the primed BA reader of the Step 2 local bound (with the average bound),
`stLocalAvgOfL2_holdsDecG` at `baStep2Data`; Green input `STGijDecgL` (input (b)); `(GiiGEX)`, `(GavLGEX)` from G7. -/
def T2487_LocalAvgOfL2 : Prop :=
  ∀ d : ℕ, 2 ≤ d → T2487_BAGijDec d →
    STLocalAvgOfL2gL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0

/-- **Target 11, `baStep2_holds`**: Step 2 at BA, the pin `BAStep2 d`, under the inputs (a), (b) of exact type. -/
def T2487_Step2Holds : Prop :=
  ∀ d : ℕ, BALWterm d → BALWtermExp d → T2487_BAGijDec d → BAStep2 d

/-! ### Shapes (not binding) -/

/-- Shape (finding F2; target 10, private copy): `ST_step2_of_pinsg` (`Chain/Step2IterGen2.lean:299`) with the one-loop input read
under `0 < κ` and the flow (the merged proof uses `hOne` only at `:371`, under `hflow`); every other input as merged. -/
example : Prop :=
  ∀ (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ),
    Step2EventsGen_Flow d Flow T0 →
    (∀ (sz : Sizes d) (z : ℕ → ℂ), Step2EventsGen_Grid (mk sz z) (law sz)) →
    (∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      DecayGen_Spec (mk sz z).toFlowFM κm) →
    (∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz),
      ((mk sz z).Hpath s t K n k ω).IsHermitian) →
    (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      Step2IterGen_OneLoop (mk sz z).toFlowFM) →
    STBdatagL d Flow T0 →
    STLWTgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0 →
    STEMn2ExpgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0 →
    Step2IterGen_NewKLK d Flow mk →
    STGridMartgL d Flow mk T0 →
    Step2IterGen_K2 d Flow mk →
    STNetLift2gL d law Flow (fun sz z => (mk sz z).toFlowFM) T0 →
    STScaleExistsgL d Flow T0 →
    STOptL2gL d law Flow (fun sz z => (mk sz z).toFlowFM) T0 →
    STLocalAvgOfL2gL d law Flow (fun sz z => (mk sz z).toFlowFM) T0 →
    STStep2G d law Flow (fun sz z => (mk sz z).toFlowFM) T0

/-- Shape (finding F1; target 5, proof-internal): F7 of `NewKLKGenHyp` (`Chain/NewKLKGen.lean:383`) at one frozen BA carrier: the
`Θ`-kernel at the coupling `BAflowLam0 sz z` against the tail at `sz.lam`, with `K_c` uniform in `(sz, z)` (`K_c = A K_c⁰`). -/
example {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (K_c : ℝ) : Prop :=
  ∀ (n : ℕ) (u : ℝ), 0 ≤ u → u < 1 → ∀ (s s' : Bool) (ℓ' D' : ℝ), 0 ≤ ℓ' → 0 ≤ D' → ∀ a a' : Zd d (sz.L n),
    ∑ b, ‖Step2Gen_thetaKer (baFMz sz z) n s s' u a b‖ *
        tailW d (sz.L n) (sz.lam n) u ℓ' ((sz.W n : ℕ) : ℝ) D' ((zdistInf d (sz.L n) (b - a') : ℕ) : ℝ) ≤
      K_c / (1 - u) *
        tailW d (sz.L n) (sz.lam n) u ℓ' ((sz.W n : ℕ) : ℝ) D' ((zdistInf d (sz.L n) (a - a') : ℕ) : ℝ)

/-- Shape (target 4, proof-internal): the forward profile comparison from R1 (T1's 1a row 14; the reverse one is false, row 13). -/
example {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (A : ℝ) : Prop :=
  ∀ (n : ℕ) (u D ℓ : ℝ) (a b : Zd d (sz.L n)),
    STprof (sz.withLam (BAflowLam0 sz z)) n u D ℓ a b ≤ A * STprof sz n u D ℓ a b

/-- The UBA-C1 literal R1 at BA (`gK = BAflowLam0 sz z`, `A = (κ+1)/κ`; `TwistStep2_lam0_sq`); the guarded per-index form is
`baStep5III_lam0_le_lam`. -/
example {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (κ : ℝ) : Prop :=
  ∀ n, 0 ≤ BAflowLam0 sz z n * sz.lam n ∧ BAflowLam0 sz z n ^ 2 ≤ sz.lam n ^ 2 ∧
    sz.lam n ^ 2 ≤ (κ + 1) / κ * BAflowLam0 sz z n ^ 2

/-- Shape (U2-C3): U2-BA's one-loop field (the last conjunct of `SEforLnGen_Facts`, `Chain/SEforLnGen.lean:57`) at the BA carrier,
read from target 2 as its first conjunct with `STmsigg` unfolded (no second named Prop, no second proof). -/
example {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) : Prop :=
  Step2IterGen_OneLoop (baFMz sz z) →
    ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)),
      (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).K n u (fun _ : Fin 1 => σ) (fun _ => a) =
        STmsigg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n σ

/-- Shape (consumers): the first conjunct of `twSteps` (`BA/TwistPins.lean:134`) is the conclusion of `BAStep2` at a window. -/
example {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (Cd : ℝ) : Prop :=
  STStep2ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd ∧
    twSteps (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd

/-- Shape (note (3), alternative): input (b) from the merged primed Green pin (`BA/GreenCore.lean:1644`, `baGbEXPij'_holds`). -/
example (d : ℕ) : Prop := BAGbEXPij' d → T2487_BAGijDec d

/-- Shape: the stage-L bridges used in targets 8, 11 (pattern `Chain/Step2EventsGenTw.lean:144-150`, every `3 ≤ d`). -/
example (d : ℕ) : Prop := 3 ≤ d → (BALWterm d → BASTLWB d) ∧ (BALWtermExp d → BASTLWT d)

/-- Shape (target 12): the instance data (`sz0`, `zSeq`, `flow_sz0`) and the instance of target 11. -/
example : Prop :=
  BAFlow RBM.Gauss.SizesInst.sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) RBM.BA.FlowPinsInst.zSeq ∧
    Step2IterGen_OneLoop (baFMz RBM.Gauss.SizesInst.sz0 RBM.BA.FlowPinsInst.zSeq) ∧
    (BALWterm 3 → BALWtermExp 3 → T2487_BAGijDec 3 → BAStep2 3)

end RBM.BA

end

/-! ## Part 3: the bodies that targets 5, 6, 7, 10 copy (unchanged, not edited; copies under the stems) -/

#check @RBM.BA.stNewKLKAtgL'_of
#check @RBM.Gauss.Sizes.ST_Bdata_holds
#check @RBM.Gauss.Sizes.stScaleExists_holds
#check @RBM.BA.ST_step2_of_pinsg
#check @RBM.Gauss.Sizes.ST_Lloop_one_false
