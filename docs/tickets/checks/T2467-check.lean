/-
Release check for T2467 (dispatcher V3, Mon Oct 12 17:34 UTC 2026; DECISIONS §272).  ST T7b (sub-stage T, ST side; the split successor of
T2454 = T7): targets 8-11 of T2454 in the new file `Chain/Step2EventsGen.lean` (no `BA/` import); the BA side in
the new leaf `Chain/Step2EventsGenTw.lean` (Amend 1, DECISIONS §274 (3); `Chain/DecayGenTw.lean` is not edited).  The band files `Induction/Step2Events`, `Step2Core` are not edited.
Part 1: merged names.  Part 2: the pins `T2467_*`, copied from the compiled T2454 probe
(`t/T2454:RBM3D/Probe/T2454Pins.lean`, commit e949c71, Part 2 `:138-293`) with two changes only: the bundle `S2EvGen_Sect`
(`:213-218`) is unbundled into explicit premises (1a-audit round 2, O2), so `STScaleInvgL` and `STStep1WeakgL` are explicit
premises ((a‴) item 4).  Each `T2467_X` stands for the generic definition `X` that the 1b writes (renaming table in the ticket).
Content binding: the definitions (target 8 `T2467_ScaleInvgL`, target 9 event sets `T2467_Ev*`, target 10 field list
`T2467_GoodAtFields`, target 11 `T2467_BdatagL`) and the carrier facts F1-F2 `T2467_Flow`, F7 `T2467_Rot3`, F9 `T2467_Grid`.
The target statements `T2467_ST_*`, `T2467_stLW*` are binding up to these names, binder implicitness and a premise the 1a
drops (a stronger result, reported).  Every `example` is a shape (not binding).
Merged names only.  No proofs.
Run: lake env lean docs/tickets/checks/T2467-check.lean
-/
import RBM3D.Chain.Carrier
import RBM3D.Chain.Step2Gen
import RBM3D.Chain.LWGen
import RBM3D.Chain.DecayGen
import RBM3D.Chain.DecayGenTw
import RBM3D.Induction.Step2Core
import RBM3D.Induction.Step2Events
import RBM3D.Induction.Step2Iterate
import RBM3D.BA.Step2BA
import RBM3D.BA.FlowPins
import RBM3D.BA.EMn2BA
import RBM3D.BA.LWPinsBA
import RBM3D.Defs.StochDomAt

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the band objects of targets 8-11 (`Induction/Step2Events`, `Step2Core`, `Step2Iterate`)
#check @RBM.Gauss.Sizes.STScaleInv
#check @RBM.Gauss.Sizes.ST_LW_sections
#check @RBM.Gauss.Sizes.ST_event_weak
#check @RBM.Gauss.Sizes.ST_event_init
#check @RBM.Gauss.Sizes.ST_event_lw
#check @RBM.Gauss.Sizes.ST_event_mg
#check @RBM.Gauss.Sizes.ST_good_prob
#check @RBM.Gauss.Sizes.STGoodAt
#check @RBM.Gauss.Sizes.STLab
#check @RBM.Gauss.Sizes.STBdata
#check @RBM.Gauss.Sizes.ST_Bdata_holds
#check @RBM.Gauss.Sizes.STLWB_of_LWterm
#check @RBM.Gauss.Sizes.STLWT_of_LWtermExp
#check @RBM.Gauss.Sizes.LWterm
#check @RBM.Gauss.Sizes.LWtermExp
-- the T1-read helpers that get a generic form here ((a‴) item 3; 1a-audit round 2 §5) and the spectral ones
#check @RBM.Gauss.Sizes.ST_grid_whp_of_sections
#check @RBM.Gauss.Sizes.ST_grid_whp_zero
#check @RBM.Gauss.Sizes.ST_prec_mono_eventually
#check @RBM.Gauss.Sizes.ST_prec_of_le_ev
#check @RBM.Gauss.Sizes.ST_prec_sup
#check @RBM.Gauss.Sizes.ST_sections_of_PT
#check @RBM.Gauss.Sizes.ST_PT_of_sections
#check @RBM.Gauss.Sizes.ST_model_le_path
#check @RBM.Gauss.Sizes.ST_cstar_le
#check @RBM.Gauss.Sizes.ST_flow_im_pos
#check @RBM.Gauss.Sizes.ST_mE_im_ge
-- the grid transfer behind F9, the union bound, the arithmetic of the band instance of target 10
#check @RBM.Gauss.Sizes.ST_whp_grid
#check @RBM.Gauss.Sizes.ST_pathP_eq_seqP
#check @RBM.Gauss.Sizes.STLM_measurable
#check @RBM.Gauss.Sizes.STGMM_measurable
#check @RBM.Gauss.Sizes.ST_union_prob
#check @RBM.Gauss.Sizes.ST_card_lab_le
#check @RBM.Gauss.Sizes.ST_floor_sq
#check @RBM.Gauss.Sizes.ST_prof_lower_N
#check @RBM.Gauss.Sizes.ST_gridStep_nonneg
-- T1's P4 (not a target here; U-D `T2452-design.md:184`)
#check @RBM.Gauss.Sizes.ST_good_engine
-- the carrier and the generic vocabulary (row 0, T8, T8b, stage L, T7a)
#check @RBM.BA.FlowFM
#check @RBM.BA.FlowFM.GM
#check @RBM.BA.PrecL
#check @RBM.BA.Step2Mat
#check @RBM.BA.bandFM
#check @RBM.BA.bandStep2Mat
#check @RBM.BA.STLWassmExpgL
#check @RBM.BA.STStep1WeakgL
#check @RBM.BA.STDecaygL
#check @RBM.BA.STLWBgL
#check @RBM.BA.STLWTgL
#check @RBM.BA.STEMn2ExpgL
#check @RBM.BA.STScaleExistsgL
#check @RBM.BA.STEGtg
#check @RBM.BA.STEEg
#check @RBM.BA.STJhatg
#check @RBM.BA.STGMMg
#check @RBM.BA.STEGtMg
#check @RBM.BA.STEEMg
#check @RBM.BA.STJhatMg
#check @RBM.BA.STgAg
#check @RBM.BA.STgDriftg
#check @RBM.BA.bandStep2_STgA
#check @RBM.BA.bandStep2_STgDrift
#check @RBM.BA.bandStep2_STGMM
#check @RBM.BA.bandStep2_STEGtM
#check @RBM.BA.bandStep2_STEEM
#check @RBM.BA.bandStep2_STJhatM
#check @RBM.BA.LWtermG
#check @RBM.BA.LWtermExpG
#check @RBM.BA.bandPin
#check @RBM.BA.STLWB_bandPin
#check @RBM.BA.STLWT_bandPin
#check @RBM.BA.DecayGen_Spec
#check @RBM.BA.DecayGen_bandSpec
#check @RBM.BA.DecayGenTw_baWardPair
-- the BA side (leaf): carrier, law, setting, horizon, the facts the probe used, stage L readings
#check @RBM.BA.baStep2Mat
#check @RBM.BA.baFM
#check @RBM.BA.baFMz
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.BA.EMn2BA_T0_lt_one
#check @RBM.BA.EMn2BA_mF_data
#check @RBM.BA.EMn2BA_seqHflowBA_herm
#check @RBM.BA.baSTEMn2Exp
#check @RBM.BA.baPin
#check @RBM.BA.BALWterm
#check @RBM.BA.BALWtermExp
#check @RBM.BA.BASTLWB
#check @RBM.BA.BASTLWT
#check @RBM.BA.band_LWtermG
#check @RBM.BA.band_LWtermExpG
#check @RBM.BA.band_STLWBgL
#check @RBM.BA.band_STLWTgL
#check @RBM.Gauss.Sizes.seqHflowBA
#check @RBM.Gauss.walk_measurable_loopFine
#check @RBM.Gauss.walk_measurable_Gres_apply
-- measure-level and index vocabulary; the band instance data
#check @RBM.ellT
#check @RBM.Path.TimeIcc
#check @RBM.Path.gridTime
#check @RBM.Path.gridStep
#check @RBM.Path.PathΩ
#check @RBM.Gauss.HighProbAt
#check @RBM.Gauss.Sizes.STprof
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.InductionDefsInst.z0
#check @RBM.Gauss.InductionDefsInst.flow_z0
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.InductionDefsInst.tInst

/-! ## Part 2: the pins (content binding) and shapes (not binding) -/

open MeasureTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ### Definitions (content binding) -/

/-- **Target 8, `STScaleInvgL`** (probe `:144`): `Inv(Kf)`, `(eq:LW_assm_exp)` at the scale family at every time section
(band `STScaleInv`, `Step2Events.lean:159`; definitional at `bandFM`). -/
def T2467_ScaleInvgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) (Kf : ℕ → ℝ → ℝ) : Prop :=
  ∀ (tt : ∀ n, TimeIcc s t n) (D : ℝ), 0 < D → STLWassmExpgL C μ (fun n => (tt n : ℝ)) D (fun n => Kf n (tt n : ℝ))

/-- **Target 11, `STBdatagL`** (probe `:149`): the size data over a flow setting and a horizon (band `STBdata`,
`Step2Events.lean:209`, proved as `ST_Bdata_holds`, `Step2Iterate.lean:1049`; definitional at the band setting). -/
def T2467_BdatagL (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ cB : ℝ, 0 < cB ∧ ∀ 𝔠 : ℝ, ∃ c : ℝ, 0 < c ∧
    ∀ (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
      ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
        cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c)

/-- **Target 9, (E1) `STEvWeakg`** (probe `:172`): the weak law on the grid (band `ST_event_weak`, `Step2Events.lean:609`). -/
def T2467_EvWeak {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s T : ℕ → ℝ) (K : ℕ → ℕ) (δ₀ : ℝ) : Prop :=
  HighProbAt Cm.Pp sz.size (fun n => {ω | ∀ j, j ≤ K n → ∀ x y,
    ‖STGMMg Cm n (gridTime s T K n j) (Cm.Hpath s T K n j ω) x y‖ ≤ δ₀})

/-- **Target 9, (E2) `STEvInitg`** (probe `:175`): the initial value on the grid (band `ST_event_init`, `:786`). -/
def T2467_EvInit {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s T : ℕ → ℝ) (K : ℕ → ℕ) (D : ℝ) (Kf : ℕ → ℝ → ℝ)
    (a₀ : ℕ → ℝ) : Prop :=
  HighProbAt Cm.Pp sz.size (fun n => {ω | ∀ i : STLab sz n, ‖STgAg Cm s T K n i.1 i.2 0 ω‖ ≤
    a₀ n * STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1)})

/-- **Target 9, (E3) `STEvLWg`** (probe `:179`): the light-weight term on the grid (band `ST_event_lw`, `:637`); the band factor
`(mE E).im * (1 - u)` is the carrier's `eta`. -/
def T2467_EvLW {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s T : ℕ → ℝ) (K : ℕ → ℕ) (D : ℝ) (Kf : ℕ → ℝ → ℝ)
    (Λ : ℕ → ℝ) : Prop :=
  HighProbAt Cm.Pp sz.size (fun n => {ω | ∀ j, j ≤ K n → ∀ i : STLab sz n,
    ‖STEGtMg Cm n (gridTime s T K n j) (Cm.Hpath s T K n j ω) i.1 i.2‖ ≤
      Λ n / Cm.eta n (gridTime s T K n j) * (sz.Bctl n (gridTime s T K n j)) ^ (1 / 2 : ℝ) *
        STprof sz n (gridTime s T K n j) D (Kf n (gridTime s T K n j)) (i.2 0) (i.2 1)})

/-- **Target 9, (E4) `STEvMGg`** (probe `:184`): the quadratic variation on the grid with the random control `Ĵ` (band
`ST_event_mg`, `:710`; supervisor 0853 Q2: `J := Ĵ`). -/
def T2467_EvMG {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s T : ℕ → ℝ) (K : ℕ → ℕ) (D : ℝ) (Kf : ℕ → ℝ → ℝ)
    (Λ : ℕ → ℝ) : Prop :=
  HighProbAt Cm.Pp sz.size (fun n => {ω | ∀ j, j ≤ K n → ∀ i : STLab sz n,
    ‖STEEMg Cm n (gridTime s T K n j) (Cm.Hpath s T K n j ω) i.1 i.2‖ ≤
      Λ n / Cm.eta n (gridTime s T K n j) * ((sz.Bctl n (gridTime s T K n j)) ^ (1 / 2 : ℝ) +
        (STJhatMg Cm n D (Kf n (gridTime s T K n j)) (gridTime s T K n j) (Cm.Hpath s T K n j ω)) ^ 3) *
        STprof sz n (gridTime s T K n j) D (Kf n (gridTime s T K n j)) (i.2 0) (i.2 1) ^ 2})

/-- **Target 10, the fields of `STGoodAtg`** (probe `:156-170`; band `STGoodAt`, `Step2Core.lean:963`).  `STGoodAtg` is a
record, as the band's, with the fields `weak`, `init`, `lw`, `mg`, `mart`, `rem`, `ident`, whose types are, in this order, the
seven conjuncts below; `ident` reads T8b's drift `STgDriftg`, never a scalar `m m'` drift. -/
def T2467_GoodAtFields {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (D : ℝ)
    (ℓk : ℕ → ℝ) (Λ δ₀ a₀ r₀ ρ₁ : ℝ) (Mart Rem : STLab sz n → ℕ → PathΩ sz → ℂ) (ω : PathΩ sz) : Prop :=
  (∀ j, j ≤ K n → ∀ x y, ‖STGMMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) x y‖ ≤ δ₀) ∧
  (∀ i : STLab sz n, ‖STgAg Cm s t K n i.1 i.2 0 ω‖ ≤ a₀ * STprof sz n (gridTime s t K n 0) D (ℓk 0) (i.2 0) (i.2 1)) ∧
  (∀ j, j ≤ K n → ∀ i : STLab sz n, ‖STEGtMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) i.1 i.2‖ ≤
    Λ / Cm.eta n (gridTime s t K n j) * (sz.Bctl n (gridTime s t K n j)) ^ (1 / 2 : ℝ) *
      STprof sz n (gridTime s t K n j) D (ℓk j) (i.2 0) (i.2 1)) ∧
  (∀ j, j ≤ K n → ∀ i : STLab sz n, ‖STEEMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) i.1 i.2‖ ≤
    Λ / Cm.eta n (gridTime s t K n j) * ((sz.Bctl n (gridTime s t K n j)) ^ (1 / 2 : ℝ) +
      (STJhatMg Cm n D (ℓk j) (gridTime s t K n j) (Cm.Hpath s t K n j ω)) ^ 3) *
      STprof sz n (gridTime s t K n j) D (ℓk j) (i.2 0) (i.2 1) ^ 2) ∧
  (∀ i : STLab sz n, ∀ k, k ≤ K n → ‖Mart i k ω‖ ≤ Λ * (∑ j ∈ Finset.range k, gridStep s t K n *
      ‖STEEMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) i.1 i.2‖ +
      ρ₁ * STprof sz n (gridTime s t K n 0) D (ℓk 0) (i.2 0) (i.2 1) ^ 2) ^ (1 / 2 : ℝ)) ∧
  (∀ i : STLab sz n, ∀ k, k ≤ K n → ‖Rem i k ω‖ ≤ r₀ * STprof sz n (gridTime s t K n 0) D (ℓk 0) (i.2 0) (i.2 1)) ∧
  (∀ i : STLab sz n, ∀ k, k ≤ K n → STgAg Cm s t K n i.1 i.2 k ω = STgAg Cm s t K n i.1 i.2 0 ω +
    ((gridStep s t K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k, STgDriftg Cm s t K n i.1 i.2 j ω + Rem i k ω + Mart i k ω)

/-- **F9, `Step2EventsGen_Grid`** (probe `S2EvGen_Grid` `:191`; (a′) C1): a model matrix `Hm` (band `seqHflow`, BA
`seqHflowBA`) at which `LM`, `GMM` read `L`, `G - M`, both measurable in the matrix, and `(5.1)` (`Step2Core.lean:400`). -/
def T2467_Grid {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) : Prop :=
  ∃ Hm : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
    (∀ n u ω x y, Cm.GMM n u (Hm n u ω) x y = Cm.GM n u ω x y) ∧
    (∀ (n : ℕ) (u : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) ω, Cm.LM n u (Hm n u ω) σ a = Cm.L n u σ a ω) ∧
    (∀ (n : ℕ) (u : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)), Measurable fun H => Cm.LM n u H σ a) ∧
    (∀ n u x y, Measurable fun H => Cm.GMM n u H x y) ∧
    ∀ (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ), 0 ≤ s n → s n ≤ t n → K n ≠ 0 → ∀ S, MeasurableSet S →
      Cm.Pp {ω | Cm.Hpath s t K n k ω ∈ S} = μ {ω | Hm n (gridTime s t K n k) ω ∈ S}

/-- **F7, `Step2EventsGen_Rot3`** (probe `S2EvGen_Rot3` `:200`): trace cyclicity of the 3-loop (band `STB_loop_rot`,
`Step2Events.lean:1283`, private). -/
def T2467_Rot3 {d : ℕ} {sz : Sizes d} (C : FlowFM sz) : Prop :=
  ∀ (n : ℕ) (t : ℝ) (σ₀ σ₁ : Bool) (a₀ y a₁ : Zd d (sz.L n)) (ω : sz.SeqΩ),
    C.L n t ![σ₀, σ₁, σ₁] ![a₀, y, a₁] ω = C.L n t ![σ₁, σ₁, σ₀] ![y, a₁, a₀] ω

/-- **F1-F2, `Step2EventsGen_Flow`** (probe `S2EvGen_Flow` `:210`; `Step2Data.flowOK_adm`, `flowOK_T` in family shape). -/
def T2467_Flow (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  (∀ sz κ ε 𝔠 𝔡 z, Flow sz κ ε 𝔠 𝔡 z → sz.Admissible 𝔠 𝔡) ∧
    (∀ sz κ ε 𝔠 𝔡 z, 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n, T0 sz z n < 1)

/-! ### Target statements (binding up to the names above; `S2EvGen_Sect` unbundled) -/

/-- **Target 8, `ST_LW_sectionsg`** (probe `:220`; band `ST_LW_sections`, `Step2Events.lean:348`). -/
def T2467_ST_LW_sectionsg (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  T2467_Flow d Flow T0 → STLWTgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0 →
  STEMn2ExpgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0 →
  0 < d → ∀ (sz : Sizes d) (κ ε 𝔡 𝔠 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → 0 < 𝔡 → Flow sz κ ε 𝔠 𝔡 z →
  ∀ (s t : ℕ → ℝ) (cB c : ℝ) (Kf : ℕ → ℝ → ℝ),
    (∀ n, 0 ≤ s n) → (∀ n, t n ≤ T0 sz z n) → STStep1WeakgL (mk sz z).toFlowFM (law sz) s t → 0 < cB → 0 < c →
    (∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
      cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c)) →
    (∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
      0 ≤ Kf n u ∧ Kf n u ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 * ellT (sz.L n) (sz.lam n) u) →
    T2467_ScaleInvgL (mk sz z).toFlowFM (law sz) s t Kf →
    ∀ tt : ∀ n, TimeIcc s t n,
      (∀ D : ℝ, 0 < D → PrecL sz (law sz) (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
        (fun n p ω => ‖STEGtg (mk sz z).toFlowFM n (tt n : ℝ) p.1 p.2 ω‖)
        (fun n p _ => ((mk sz z).eta n (tt n : ℝ))⁻¹ * (sz.Bctl n (tt n : ℝ)) ^ (1 / 2 : ℝ) *
          STprof sz n (tt n : ℝ) D (Kf n (tt n : ℝ)) (p.2 0) (p.2 1))) ∧
      (∀ D : ℝ, 0 < D → PrecL sz (law sz) (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
        (fun n p ω => ‖STEEg (mk sz z).toFlowFM n (tt n : ℝ) p.1 p.2.1 p.2.2 ω‖)
        (fun n p ω => ((mk sz z).eta n (tt n : ℝ))⁻¹ * ((sz.Bctl n (tt n : ℝ)) ^ (1 / 2 : ℝ) +
          (STJhatg (mk sz z).toFlowFM n D (Kf n (tt n : ℝ)) (tt n : ℝ) ω) ^ 3) *
          (STprof sz n (tt n : ℝ) D (Kf n (tt n : ℝ)) (p.2.2 0) (p.2.2 1)) ^ 2))

/-- **Target 9, (E1) `ST_event_weakg`** (probe `:259`). -/
def T2467_ST_event_weakg : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ), T2467_Grid Cm μ → ∀ (s t T : ℕ → ℝ) (K : ℕ → ℕ),
    (∀ n, 0 ≤ s n) → (∀ n, s n ≤ T n) → (∀ n, T n ≤ t n) → (∀ n, K n ≠ 0) → ∀ C₁ : ℝ, 0 ≤ C₁ →
    (∀ᶠ n in atTop, ((((K n + 1) * Fintype.card (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) : ℕ)) : ℝ) ≤
      ((sz.size n : ℕ) : ℝ) ^ C₁) →
    STStep1WeakgL Cm.toFlowFM μ s t → ∀ ε₁ δ₀ : ℝ, 0 < ε₁ →
    (∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n → ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n u) ^ (1 / 4 : ℝ) ≤ δ₀) →
    T2467_EvWeak Cm s T K δ₀

/-- **Target 9, (E2) `ST_event_initg`** (probe `:265`). -/
def T2467_ST_event_initg : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ), T2467_Grid Cm μ → ∀ (s T : ℕ → ℝ) (K : ℕ → ℕ),
    (∀ n, 0 ≤ s n) → (∀ n, s n ≤ T n) → (∀ n, K n ≠ 0) → STDecaygL Cm.toFlowFM μ s → ∀ C₁ : ℝ, 0 ≤ C₁ →
    (∀ᶠ n in atTop, (Fintype.card (STLab sz n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C₁) → ∀ ε₁ : ℝ, 0 < ε₁ → ∀ Di : ℝ, 0 < Di →
    ∀ (D : ℝ) (Kf : ℕ → ℝ → ℝ) (a₀ : ℕ → ℝ),
    (∀ᶠ n in atTop, ∀ i : STLab sz n, ((sz.size n : ℕ) : ℝ) ^ ε₁ * ((sz.Bctl n (s n)) ^ (1 / 5 : ℝ) *
      STWB sz n (s n) (zdistInf d (sz.L n) (i.2 0 - i.2 1)) * Real.exp (-(((zdistInf d (sz.L n) (i.2 0 - i.2 1) : ℕ) : ℝ) /
        ellT (sz.L n) (sz.lam n) (s n)) ^ (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-Di)) ≤
      a₀ n * STprof sz n (s n) D (Kf n (s n)) (i.2 0) (i.2 1)) → T2467_EvInit Cm s T K D Kf a₀

/-- **Target 9, (E3) `ST_event_lwg`** (probe `:232`): the premises of target 8 plus F3 (`DecayGen_Spec`, merged) and F9. -/
def T2467_ST_event_lwg (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  T2467_Flow d Flow T0 → STLWTgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0 →
  STEMn2ExpgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0 →
  0 < d → ∀ (sz : Sizes d) (κ ε 𝔡 𝔠 κm : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → 0 < 𝔡 → Flow sz κ ε 𝔠 𝔡 z →
  DecayGen_Spec (mk sz z).toFlowFM κm → T2467_Grid (mk sz z) (law sz) →
  ∀ (s t T : ℕ → ℝ) (K : ℕ → ℕ) (cB c : ℝ) (Kf : ℕ → ℝ → ℝ),
    (∀ n, 0 ≤ s n) → (∀ n, t n ≤ T0 sz z n) → STStep1WeakgL (mk sz z).toFlowFM (law sz) s t → 0 < cB → 0 < c →
    (∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
      cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c)) →
    (∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
      0 ≤ Kf n u ∧ Kf n u ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 * ellT (sz.L n) (sz.lam n) u) →
    T2467_ScaleInvgL (mk sz z).toFlowFM (law sz) s t Kf →
    (∀ n, s n ≤ T n) → (∀ n, T n ≤ t n) → (∀ n, K n ≠ 0) → ∀ C₁ : ℝ, 0 ≤ C₁ →
    (∀ᶠ n in atTop, ((((K n + 1) * Fintype.card (STLab sz n) : ℕ)) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C₁) →
    ∀ ε₁ : ℝ, 0 < ε₁ → ∀ Λ : ℕ → ℝ, (∀ n, ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ Λ n) → ∀ D : ℝ, 0 < D →
      T2467_EvLW (mk sz z) s T K D Kf Λ

/-- **Target 9, (E4) `ST_event_mgg`** (probe `:241`); the `Ĵ` form stays. -/
def T2467_ST_event_mgg (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  T2467_Flow d Flow T0 → STLWTgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0 →
  STEMn2ExpgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0 →
  0 < d → ∀ (sz : Sizes d) (κ ε 𝔡 𝔠 κm : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → 0 < 𝔡 → Flow sz κ ε 𝔠 𝔡 z →
  DecayGen_Spec (mk sz z).toFlowFM κm → T2467_Grid (mk sz z) (law sz) →
  ∀ (s t T : ℕ → ℝ) (K : ℕ → ℕ) (cB c : ℝ) (Kf : ℕ → ℝ → ℝ),
    (∀ n, 0 ≤ s n) → (∀ n, t n ≤ T0 sz z n) → STStep1WeakgL (mk sz z).toFlowFM (law sz) s t → 0 < cB → 0 < c →
    (∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
      cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c)) →
    (∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
      0 ≤ Kf n u ∧ Kf n u ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 * ellT (sz.L n) (sz.lam n) u) →
    T2467_ScaleInvgL (mk sz z).toFlowFM (law sz) s t Kf →
    (∀ n, s n ≤ T n) → (∀ n, T n ≤ t n) → (∀ n, K n ≠ 0) → ∀ C₁ : ℝ, 0 ≤ C₁ →
    (∀ᶠ n in atTop, ((((K n + 1) * Fintype.card (Fin 2 × STLab sz n) : ℕ)) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C₁) →
    ∀ ε₁ : ℝ, 0 < ε₁ → ∀ Λ : ℕ → ℝ, (∀ n, 2 * ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ Λ n) → ∀ D : ℝ, 0 < D →
      T2467_EvMG (mk sz z) s T K D Kf Λ

/-- **Target 10, `ST_good_probg`** (probe `:276`; band `ST_good_prob`, `Step2Events.lean:853`): `P(¬ STGoodAtg) ≤ N^{-D'}`
from (E1)-(E4), the martingale tail (E5) and the a.e. identities; in the 1b's statement `STGoodAtg` stands where
`T2467_GoodAtFields` stands here. -/
def T2467_ST_good_probg : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (Cm : Step2Mat sz), Tendsto sz.size atTop atTop → ∀ (s T : ℕ → ℝ) (K : ℕ → ℕ) (D : ℝ)
    (Kf : ℕ → ℝ → ℝ) (δ₀ : ℝ) (Λ a₀ r₀ ρ₁ : ℕ → ℝ) (Mart Rem : ∀ n, STLab sz n → ℕ → PathΩ sz → ℂ),
    T2467_EvWeak Cm s T K δ₀ → T2467_EvInit Cm s T K D Kf a₀ → T2467_EvLW Cm s T K D Kf Λ → T2467_EvMG Cm s T K D Kf Λ →
    (∀ n, 0 ≤ gridStep s T K n) → ∀ D' Dm ε₁ : ℝ, 0 < D' → D' + 1 + 3 ≤ Dm →
    (∀ᶠ n in atTop, ∀ i : STLab sz n, Cm.Pp {ω | ∃ k, k ≤ K n ∧ ((sz.size n : ℕ) : ℝ) ^ ε₁ *
      (∑ j ∈ Finset.range k, gridStep s T K n * ‖STEEMg Cm n (gridTime s T K n j) (Cm.Hpath s T K n j ω) i.1 i.2‖ +
        ((sz.size n : ℕ) : ℝ) ^ (-Dm)) ^ (1 / 2 : ℝ) < ‖Mart n i k ω‖} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-Dm))) →
    (∀ n, ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ Λ n) →
    (∀ᶠ n in atTop, ∀ i : STLab sz n, ((sz.size n : ℕ) : ℝ) ^ (-Dm) ≤
      ρ₁ n * STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1) ^ 2) →
    (∀ n (i : STLab sz n), ∀ᵐ ω ∂Cm.Pp, ∀ k, k ≤ K n → STgAg Cm s T K n i.1 i.2 k ω = STgAg Cm s T K n i.1 i.2 0 ω +
      ((gridStep s T K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k, STgDriftg Cm s T K n i.1 i.2 j ω + Rem n i k ω + Mart n i k ω) →
    (∀ᶠ n in atTop, ∀ i : STLab sz n, ∀ᵐ ω ∂Cm.Pp, ∀ k, k ≤ K n →
      ‖Rem n i k ω‖ ≤ r₀ n * STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1)) →
    (∀ᶠ n in atTop, (Fintype.card (STLab sz n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ)) →
    ∀ᶠ n in atTop, Cm.Pp {ω | ¬ T2467_GoodAtFields Cm s T K n D (fun j => Kf n (gridTime s T K n j)) (Λ n) δ₀ (a₀ n) (r₀ n)
        (ρ₁ n) (Mart n) (Rem n) ω} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D'))

/-- **Target 11, `stLWBgL_of_LWtermG`** (probe `:250`; band `STLWB_of_LWterm`, `Step2Events.lean:1355`): F1 and F7 are the facts read. -/
def T2467_stLWBgL_of_LWtermG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (mkF : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) : Prop :=
  3 ≤ d → (∀ sz κ ε 𝔠 𝔡 z, Flow sz κ ε 𝔠 𝔡 z → sz.Admissible 𝔠 𝔡) → (∀ sz z, T2467_Rot3 (mkF sz z)) →
    LWtermG d law Flow mkF T0 → STLWBgL d law Flow mkF T0

/-- **Target 11, `stLWTgL_of_LWtermExpG`** (probe `:253`; band `STLWT_of_LWtermExp`, `Step2Events.lean:1427`). -/
def T2467_stLWTgL_of_LWtermExpG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (mkF : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) : Prop :=
  3 ≤ d → (∀ sz κ ε 𝔠 𝔡 z, Flow sz κ ε 𝔠 𝔡 z → sz.Admissible 𝔠 𝔡) → (∀ sz z, T2467_Rot3 (mkF sz z)) →
    LWtermExpG d law Flow mkF T0 → STLWTgL d law Flow mkF T0

/-! ### Shapes (not binding) -/

/-- Target 8, band reading (shape; definitional expected, probe `:146`). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (E s t : ℕ → ℝ) (Kf : ℕ → ℝ → ℝ),
  STScaleInv sz E s t Kf ↔ T2467_ScaleInvgL (bandFM sz E) (Sizes.seqP sz) s t Kf

/-- Target 11, band reading (shape; definitional expected, probe `:154`) and the BA reading that T1-BA proves (shape). -/
example : Prop := ∀ d : ℕ,
  STBdata d ↔ T2467_BdatagL d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun _ z n => lemT (z n))
example : Prop := ∀ d : ℕ, T2467_BdatagL d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) BAflowT0

/-- Target 10, the band reading of the good event (shape; a proved bridge, not definitional: the band factor
`(mE E).im * (1 - u)` against `eta = etaT = (1 - u) * (mE E).im`, and `bandStep2_STgA`, `bandStep2_STgDrift`). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (Es s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (D : ℝ) (ℓk : ℕ → ℝ)
    (Λ δ₀ a₀ r₀ ρ₁ : ℝ) (Mart Rem : STLab sz n → ℕ → PathΩ sz → ℂ) (ω : PathΩ sz),
  STGoodAt sz s t K n (Es n) D ℓk Λ δ₀ a₀ r₀ ρ₁ Mart Rem ω ↔
    T2467_GoodAtFields (bandStep2Mat sz Es) s t K n D ℓk Λ δ₀ a₀ r₀ ρ₁ Mart Rem ω

/-- F1-F2, F7, F9 at the band (shapes; proved in `Chain/Step2EventsGen`, probe `:309-316`, `:326`). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (E : ℕ → ℝ),
  T2467_Rot3 (bandFM sz E) ∧ T2467_Grid (bandStep2Mat sz E) (Sizes.seqP sz)
example : Prop := ∀ d : ℕ, T2467_Flow d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun _ z n => lemT (z n))

/-- F1-F2, F7, F9 at BA (shapes; proved in the new leaf `Chain/Step2EventsGenTw`, probe `:317-331`). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (l E : ℕ → ℝ),
  T2467_Rot3 (baFM sz l E) ∧ T2467_Grid (baStep2Mat sz l E) (Sizes.seqP (sz.withLam 0))
example : Prop := ∀ d : ℕ, T2467_Flow d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) BAflowT0

/-- Target 9, (E3) and (E4) elaborated at the BA family (shapes; probe `:390`; statement-level instances in the leaf). -/
example : Prop := T2467_ST_event_lwg 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
  (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0
example : Prop := T2467_ST_event_mgg 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
  (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0

/-- Target 11 at the band family (shape; the closed instance applies it to `band_LWtermG`, probe `:374-379`) and at the BA family
(shape: with F7 at `baFMz`, stage L's `BALWterm 3` gives `BASTLWB 3`). -/
example : Prop := T2467_stLWBgL_of_LWtermG 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
  (fun _ z n => lemT (z n)) (fun sz z => bandFM sz (STflowE z))
example : Prop := T2467_stLWTgL_of_LWtermExpG 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
  BAflowT0 baFMz

end RBM.BA

end
