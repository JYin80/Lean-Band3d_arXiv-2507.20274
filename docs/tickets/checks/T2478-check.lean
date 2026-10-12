/-
Release check for T2478 (dispatcher V3, Mon Oct 12 22:25 UTC 2026; DECISIONS §279).  ST T1 (sub-stage T): the Step 2 iteration over the carrier
(`Induction/Step2Iterate`, `OptL2a`, `OptL2b`, and P4 = the generic `ST_good_engine`, `Step2Core:997`) in the new files
`Chain/Step2IterGen.lean`, `Chain/Step2IterGen2.lean` (T1a) and `Chain/OptL2Gen.lean`, `Chain/Step2CloseGen.lean` (T1b); the
band files are not edited (outside the certificate lane).
Part 1: merged names.  Part 2: the target statements as Prop values (prefix `T2478_`): the carrier classes and the conclusions
are content binding (a class field may be added only with a named band discharge, reported in 1a (iii)); then shapes (not
binding): band discharges, the BA readings (T1-BA), the UBA-C1 literal.  Part 3 (G1): the public band names the row restates
or reads, unchanged; the auditor adds `example : <statement> := <name>` for each.
Merged names only; statements only.
Run: lake env lean docs/tickets/checks/T2478-check.lean
-/
import RBM3D.Induction.OptL2b
import RBM3D.Induction.LocalAvg2
import RBM3D.Chain.Step2EventsGenTw
import RBM3D.Chain.NewKLKGen
import RBM3D.Evolution.FarEntry
import RBM3D.Path.DifREP2
import RBM3D.BA.NewKLKBA
import RBM3D.BA.GridMartBA
import RBM3D.BA.NetLiftBA
import RBM3D.BA.GreenOff
import RBM3D.BA.KInduct

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the carrier and the Step 2 family (row 0, T8, T8b)
#check @RBM.BA.FlowFM
#check @RBM.BA.Step2Mat
#check @RBM.BA.Step2Data
#check @RBM.BA.bandFM
#check @RBM.BA.bandStep2Mat
#check @RBM.BA.bandStep2Data
#check @RBM.BA.PrecL
#check @RBM.BA.PrecPTL
#check @RBM.BA.STLKgL
#check @RBM.BA.STDecaygL
#check @RBM.BA.STStep1LoopgL
#check @RBM.BA.STStep1WeakgL
#check @RBM.BA.STStep2G
#check @RBM.BA.STStep2_iff
#check @RBM.BA.STStep2ConclgL
#check @RBM.BA.STAvgUgL
#check @RBM.BA.STStep2AvggL
#check @RBM.BA.STGdecayWgL
#check @RBM.BA.STStep2LocalPTgL
#check @RBM.BA.STStep2AvgPTgL
#check @RBM.BA.STStep2DecayPTgL
#check @RBM.BA.STL2decayPTgL
#check @RBM.BA.STNetLift2gL
#check @RBM.BA.STLocalAvgOfL2gL
#check @RBM.BA.STOptL2gL
#check @RBM.BA.STScaleExistsgL
#check @RBM.BA.STLWBgL
#check @RBM.BA.STLWTgL
#check @RBM.BA.STEMn2PolygL
#check @RBM.BA.STEMn2ExpgL
#check @RBM.BA.bandFM_STNetLift2
#check @RBM.BA.bandFM_STLocalAvgOfL2
#check @RBM.BA.bandFM_STOptL2
#check @RBM.BA.bandFM_STScaleExists
#check @RBM.BA.bandFM_STLWB
#check @RBM.BA.bandFM_STLWT
#check @RBM.BA.bandFM_STEMn2Poly
#check @RBM.BA.bandFM_STEMn2Exp
#check @RBM.BA.bandFM_STStep2DecayPT
#check @RBM.BA.bandFM_STL2decayPT
#check @RBM.BA.bandFM_STStep2LocalPT
#check @RBM.BA.STmsigg
#check @RBM.BA.STLMg
#check @RBM.BA.STLKMg
#check @RBM.BA.STJhatMg
#check @RBM.BA.STEGtMg
#check @RBM.BA.STELKLKMg
#check @RBM.BA.STthetaOpg
#check @RBM.BA.STEEMg
#check @RBM.BA.STGMMg
#check @RBM.BA.STgAg
#check @RBM.BA.STgDriftg
#check @RBM.BA.STstopIdxg
#check @RBM.BA.STGridMartAtgL
#check @RBM.BA.STGridMartgL
#check @RBM.BA.bandStep2_STGridMart
#check @RBM.BA.STLIMg
#check @RBM.BA.STLKIMg
#check @RBM.BA.STelklkMg
#check @RBM.BA.STegtMg
#check @RBM.BA.STeeMg
#check @RBM.BA.STgANg
#check @RBM.BA.STgDriftNg
#check @RBM.BA.Step2Gen_thetaKer
#check @RBM.BA.Step2Gen_ThetaN
#check @RBM.BA.Step2Gen_UN
#check @RBM.BA.STNewKLKAtgL
#check @RBM.BA.STNewKLKgL
#check @RBM.BA.STK2decaygL
#check @RBM.BA.STK2decaygL'
#check @RBM.BA.bandStep2_STNewKLK
#check @RBM.BA.bandStep2_STK2decay
#check @RBM.BA.STGiiGEXgL
#check @RBM.BA.STGijGEXgL
#check @RBM.BA.STGavLGEXgL
#check @RBM.BA.bandFM_STGijGEX
-- T3 (`Chain/NewKLKGen`): the primed energy-family pins (read only through the band and BA discharges of target 1)
#check @RBM.BA.STNewKLKAtgL'
#check @RBM.BA.STNewKLKgL'
#check @RBM.BA.stNewKLKgL_of_primed
#check @RBM.BA.stK2decaygL_of_primed
#check @RBM.BA.stK2decaygL'_band
-- T7a, T7b (`Chain/DecayGen`, `Chain/Step2EventsGen`, leaf `Step2EventsGenTw`)
#check @RBM.BA.DecayGen_Spec
#check @RBM.BA.DecayGen_bandSpec
#check @RBM.BA.Step2EventsGen_Flow
#check @RBM.BA.Step2EventsGen_Grid
#check @RBM.BA.Step2EventsGen_Rot3
#check @RBM.BA.Step2EventsGen_bandFlow
#check @RBM.BA.Step2EventsGen_bandGrid
#check @RBM.BA.Step2EventsGen_bandGoodAt
#check @RBM.BA.Step2EventsGen_sections_of_PT
#check @RBM.BA.Step2EventsGen_PT_of_sections
#check @RBM.BA.Step2EventsGen_grid_whp_of_sections
#check @RBM.BA.Step2EventsGen_grid_whp_zero
#check @RBM.BA.Step2EventsGen_model_le_path
#check @RBM.BA.Step2EventsGen_prec_mono_eventually
#check @RBM.BA.Step2EventsGen_cstar_le
#check @RBM.BA.STScaleInvgL
#check @RBM.BA.bandFM_STScaleInv
#check @RBM.BA.ST_LW_sectionsg
#check @RBM.BA.STEvWeakg
#check @RBM.BA.STEvInitg
#check @RBM.BA.STEvLWg
#check @RBM.BA.STEvMGg
#check @RBM.BA.ST_event_weakg
#check @RBM.BA.ST_event_initg
#check @RBM.BA.ST_event_lwg
#check @RBM.BA.ST_event_mgg
#check @RBM.BA.STGoodAtg
#check @RBM.BA.ST_good_probg
#check @RBM.BA.STBdatagL
#check @RBM.BA.bandFM_STBdata
#check @RBM.BA.stLWBgL_of_LWtermG
#check @RBM.BA.stLWTgL_of_LWtermExpG
#check @RBM.BA.Step2EventsGenTw_baFlow
#check @RBM.BA.Step2EventsGenTw_baGrid
#check @RBM.BA.Step2EventsGenTw_toFlowFM
-- X1a (`Chain/CltGen`, `Evolution/FarEntry`): the GMN-C1 Green input and its band source
#check @RBM.BA.STGijDecgL
#check @RBM.BA.stGijDecgL_of_gex
#check @RBM.BA.bandFM_STGijDecgL_of_three_le
-- T8 (`Induction/LocalAvg2`, carrier-generic in place): the window-form reader and the closing pin
#check @RBM.Gauss.Sizes.stStep2LocalPT_of_L2decayG
#check @RBM.Gauss.Sizes.stLocalAvgOfL2_holdsG
#check @RBM.Gauss.Sizes.stLocalAvgOfL2_holds
-- size-level and model-free band vocabulary (reused, not copied)
#check @RBM.Gauss.Sizes.STprof
#check @RBM.Gauss.Sizes.STWB
#check @RBM.Gauss.Sizes.STLab
#check @RBM.Gauss.Sizes.STScaleOk
#check @RBM.Gauss.Sizes.STScaleAdm
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.ST_hq_arith
#check @RBM.Gauss.Sizes.ST_ratio_le
#check @RBM.Gauss.Sizes.ST_hq_of_data
#check @RBM.Gauss.Sizes.ST_zdistInf_le
#check @RBM.Gauss.Sizes.ST_Gres_false
#check @RBM.tailT
#check @RBM.Bparam
#check @RBM.Path.TimeIcc
#check @RBM.Path.PathΩ
#check @RBM.Path.gridTime
#check @RBM.Path.gridStep
#check @RBM.Path.firstHit
#check @RBM.Path.pathH_isHermitian
#check @RBM.Loop.KLloopOf
#check @RBM.Gauss.loopM_eq_loopL
-- band producers that discharge the generic inputs at the band (targets 1, 6, 8, 9, 11)
#check @RBM.Gauss.Sizes.stNewKLK_holds
#check @RBM.Gauss.Sizes.stK2decay_holds
#check @RBM.Gauss.Sizes.ST_K2e_of_flow
#check @RBM.Gauss.Sizes.stEMn2Poly_holds
#check @RBM.Gauss.Sizes.stScaleExists_holds
#check @RBM.Gauss.Sizes.stNetLift2_holds
#check @RBM.Gauss.Sizes.ST_Bdata_holds
#check @RBM.Gauss.Sizes.ST_flow_im_pos
#check @RBM.Gauss.Sizes.STLWT_of_LWtermExp
#check @RBM.Ind.stGridMart_holds
#check @RBM.abs_lemE_le
#check @RBM.lemT
-- BA sources of the classes and pins (T1-BA; read here as names only)
#check @RBM.BA.baFMz
#check @RBM.BA.baStep2Mat
#check @RBM.BA.baStep2Mat_toFlowFM
#check @RBM.BA.baStep2Mat_Hpath
#check @RBM.BA.baStep2Mat_KI
#check @RBM.BA.baStep2Data
#check @RBM.BA.baStep2Data_toFlowFM
#check @RBM.BA.baStep2Fam
#check @RBM.BA.BAStep2
#check @RBM.BA.BAStep2_iff_STStep2G
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.BA.stNewKLKgL'_ba
#check @RBM.BA.stK2decaygL'_ba
#check @RBM.BA.baGridMart_holds
#check @RBM.BA.baNetLift2_holds
#check @RBM.BA.baFlow_premises
#check @RBM.BA.baSTEMn2Poly
#check @RBM.BA.baSTEMn2Exp
#check @RBM.BA.BASTLWB
#check @RBM.BA.BASTLWT
#check @RBM.BA.EMn2BA_mF_data
#check @RBM.BA.baKsol_one
#check @RBM.BA.baGbEXPij'_holds
#check @RBM.BA.BAGbEXPij'
#check @RBM.Gauss.PsiI_isHermitian

/-! ## Part 2: the target statements (content binding), then shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 1, class `Step2IterGen_NewKLKAtN`** (binding): the instance of `lem:newKLK` at one carrier and one size index, the
body of `STNewKLKAtgL'` (`Chain/NewKLKGen.lean:58`) with the energy family `mk sz (fun _ => E)` read as the carrier `Cm` and the
premises `0 < sz.lam n ≤ 𝔡⁻¹`, `κ ≤ Im m` moved to the family form below.  It replaces `STNewKLKAt` in `ST_good_engine`
(`Step2Core:1002`) and in `OptL2a_drift_matrix` (`OptL2a:98`). -/
def T2478_NewKLKAtN {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (n : ℕ) (C δ₀ : ℝ) : Prop :=
  ∀ (u D ℓ : ℝ), 0 ≤ u → u < 1 → 0 ≤ D → 0 ≤ ℓ → ℓ ≤ ((sz.L n : ℕ) : ℝ) →
    ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
      (∀ x y, ‖STGMMg Cm n u H x y‖ ≤ δ₀) →
      ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STthetaOpg Cm n u σ (STLKMg Cm n u H σ) a‖ ≤
            C / (1 - u) * STJhatMg Cm n D ℓ u H * STprof sz n u D ℓ (a 0) (a 1) ∧
        ‖STELKLKMg Cm n u H σ a‖ ≤
            C / (1 - u) * (STJhatMg Cm n D ℓ u H +
              STJhatMg Cm n D ℓ u H ^ 2 * (if 1 ≤ ℓ then 1 else 0)) *
              STprof sz n u D ℓ (a 0) (a 1)

/-- **Target 1, class `Step2IterGen_NewKLK`** (binding): the family form over `(Flow, mk)`; `C, δ₀` depend on `κ, 𝔡` only (the
skeleton chooses `C_d = 3C + 1` before the sizes, `Step2Iterate:1398-1417`). -/
def T2478_NewKLK (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧
    ∀ (ε 𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, T2478_NewKLKAtN (mk sz z) n C δ₀

/-- **Target 1, class `Step2IterGen_K2`** (binding): the deterministic `𝒦^{(2)}` bound of the skeleton (`hK2e`,
`Step2Iterate:1429-1440`), the conclusion form of `ST_K2e_of_flow` (`Step2Iterate:1800`) over the carrier. -/
def T2478_K2 (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) : Prop :=
  3 ≤ d → ∀ κ ε 𝔠 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, t n < 1) →
      ∃ C_K : ℝ, 0 < C_K ∧ ∀ᶠ n in atTop, ∀ (u D : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        s n ≤ u → u ≤ t n → 0 ≤ D →
        ‖(mk sz z).K n u σ a‖ ≤ C_K * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1)

/-- **Target 1, class `Step2IterGen_OneLoop`** (binding): the one-loop facts of `ST_avgU_of_avg` (`Step2Iterate:1261`): `𝒦^{(1)} =
m(σ)` in the window (band `ST_Kloop_one`, `:1237`, from `KLK_one`) and `𝓛^{(1)}_{-} = conj 𝓛^{(1)}_{+}` (band `ST_Lloop_one_false`,
`:1218`). -/
def T2478_OneLoop {d : ℕ} {sz : Sizes d} (C : FlowFM sz) : Prop :=
  (∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)),
      C.K n u (fun _ : Fin 1 => σ) (fun _ => a) = if σ then C.m n else (starRingEnd ℂ) (C.m n)) ∧
    ∀ (n : ℕ) (u : ℝ) (a : Zd d (sz.L n)) (ω : sz.SeqΩ),
      C.L n u (fun _ : Fin 1 => false) (fun _ => a) ω =
        (starRingEnd ℂ) (C.L n u (fun _ : Fin 1 => true) (fun _ => a) ω)

/-- **Target 2, P4 `ST_good_engineg`** (binding): `ST_good_engine` (`Step2Core:997`) over `Cm : Step2Mat sz`: the good event is
T7b's `STGoodAtg`, the `hNew` instance is target 1 at `(Cm, n)`, `Im m` is `(Cm.m n).im` with F3 (`DecayGen_Spec`: `κm ≤ Im m`,
`η = (1 - u) Im m`), the walk is `Cm.Hpath` (Hermitian along the grid, inline), the stopping index is T8b's `STstopIdxg`. -/
def T2478_GoodEngineg : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (D : ℝ) (Kf : ℕ → ℝ → ℝ)
    (κm Λ δ₀ C a₀ r₀ ρ₁ q : ℝ),
    K n ≠ 0 → 0 ≤ s n → s n ≤ t n → t n < 1 → 0 ≤ D → DecayGen_Spec Cm.toFlowFM κm → 0 ≤ sz.lam n →
    1 ≤ Λ → 0 ≤ C → 0 ≤ a₀ → 0 ≤ r₀ → 0 ≤ ρ₁ → T2478_NewKLKAtN Cm n C δ₀ →
    (∀ j, j ≤ K n → 0 ≤ Kf n (gridTime s t K n j)) →
    (∀ j, j ≤ K n → Kf n (gridTime s t K n j) ≤ ((sz.L n : ℕ) : ℝ)) →
    (∀ j k, j ≤ k → k ≤ K n →
      tailT d (sz.L n) (sz.lam n) (gridTime s t K n j) (Kf n (gridTime s t K n j)) ≤
        tailT d (sz.L n) (sz.lam n) (gridTime s t K n k) (Kf n (gridTime s t K n k))) →
    sz.Bctl n (t n) ≤ 1 → 0 ≤ q →
    a₀ ≤ q * (sz.Bctl n (s n)) ^ (1 / 5 : ℝ) → r₀ ≤ q * (sz.Bctl n (s n)) ^ (1 / 5 : ℝ) →
    ρ₁ ≤ (q * (sz.Bctl n (s n)) ^ (1 / 5 : ℝ)) ^ 2 →
    (∀ k, k ≤ K n →
      (3 + 3 * ((Cm.m n).im)⁻¹) * Λ ^ 2 *
          (1 + q + Real.log ((1 - s n) / (1 - gridTime s t K n k))) *
          ((1 - s n) / (1 - gridTime s t K n k)) ^ (3 * C) *
          (sz.Bctl n (gridTime s t K n k)) ^ (1 / 30 : ℝ) < 1) →
    ∀ (Mart Rem : STLab sz n → ℕ → PathΩ sz → ℂ) (ω : PathΩ sz),
      (∀ j, j ≤ K n → (Cm.Hpath s t K n j ω).IsHermitian) →
      STGoodAtg Cm s t K n D (fun j => Kf n (gridTime s t K n j)) Λ δ₀ a₀ r₀ ρ₁ Mart Rem ω →
      STstopIdxg Cm s t K D Kf n ω = K n ∧ ∀ k, k ≤ K n →
        STJhatMg Cm n D (Kf n (gridTime s t K n k)) (gridTime s t K n k) (Cm.Hpath s t K n k ω) ≤
          ((3 + 3 * ((Cm.m n).im)⁻¹) * Λ ^ 2 *
              (1 + q + Real.log ((1 - s n) / (1 - gridTime s t K n k))) *
              (sz.Bctl n (gridTime s t K n k)) ^ (1 / 5 : ℝ)) *
            ((1 - s n) / (1 - gridTime s t K n k)) ^ (3 * C)

/-- **Target 3, `STSelfImpgL`** (binding): `STSelfImp` (`Step2Iterate:56`) over a flow carrier and a law. -/
def T2478_SelfImpgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (Cd : ℝ) (s t : ℕ → ℝ)
    (Kf : ℕ → ℝ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    PrecPTL sz μ (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ Cd * (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) *
        STprof sz n (p.1 : ℝ) D (Kf n (p.1 : ℝ)) (p.2.2 0) (p.2.2 1))

/-- **Target 6, `ST_step2_of_pinsg`** (binding): `ST_step2_of_pins` (`Step2Iterate:1393`) over a carrier family `(law, Flow, mk, T0)`
with `mk` valued in `Step2Mat`; conclusion `STStep2G` at `fun sz z => (mk sz z).toFlowFM`.  Carrier facts: F1-F2, F9 (T7b), F3
(T7a) in family form, the Hermitian walk (inline), target 1.  Pins as in the band, with `STGridMartgL` for the loop length 2
(TN-C4: no `STGridRepNgL`), target 1 for `STNewKLK`/`STK2decay`, and `STBdatagL` for `ST_Bdata_holds`. -/
def T2478_Step2OfPinsg : Prop :=
  ∀ (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ),
    Step2EventsGen_Flow d Flow T0 →
    (∀ (sz : Sizes d) (z : ℕ → ℂ), Step2EventsGen_Grid (mk sz z) (law sz)) →
    (∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      DecayGen_Spec (mk sz z).toFlowFM κm) →
    (∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz),
      ((mk sz z).Hpath s t K n k ω).IsHermitian) →
    (∀ (sz : Sizes d) (z : ℕ → ℂ), T2478_OneLoop (mk sz z).toFlowFM) →
    STBdatagL d Flow T0 →
    STLWTgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0 →
    STEMn2ExpgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0 →
    T2478_NewKLK d Flow mk →
    STGridMartgL d Flow mk T0 →
    T2478_K2 d Flow mk →
    STNetLift2gL d law Flow (fun sz z => (mk sz z).toFlowFM) T0 →
    STScaleExistsgL d Flow T0 →
    STOptL2gL d law Flow (fun sz z => (mk sz z).toFlowFM) T0 →
    STLocalAvgOfL2gL d law Flow (fun sz z => (mk sz z).toFlowFM) T0 →
    STStep2G d law Flow (fun sz z => (mk sz z).toFlowFM) T0

/-- **Target 8, `stOptL2_of_pinsg`** (binding): `stOptL2_of_pins` (`OptL2b:195`) over the carrier family; the band proves
`lem:newKLK` (`stNewKLK_holds`) and `(eq:MG_conclusion)` (`stEMn2Poly_holds`) inside, the generic form takes target 1 and
`STEMn2PolygL`. -/
def T2478_OptL2OfPinsg : Prop :=
  ∀ (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ),
    3 ≤ d →
    Step2EventsGen_Flow d Flow T0 →
    (∀ (sz : Sizes d) (z : ℕ → ℂ), Step2EventsGen_Grid (mk sz z) (law sz)) →
    (∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      DecayGen_Spec (mk sz z).toFlowFM κm) →
    (∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz),
      ((mk sz z).Hpath s t K n k ω).IsHermitian) →
    STBdatagL d Flow T0 →
    STLWBgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0 →
    STEMn2PolygL d law Flow (fun sz z => (mk sz z).toFlowFM) T0 →
    T2478_NewKLK d Flow mk →
    STGridMartgL d Flow mk T0 →
    STOptL2gL d law Flow (fun sz z => (mk sz z).toFlowFM) T0

/-- **Target 9 (GMN-C1), `stStep2LocalPT_of_L2decayDecG`** (binding; conditional, see the ticket): `stStep2LocalPT_of_L2decayG`
(`LocalAvg2:367`) with the window input `STGijGEXgL` replaced with the `FarEntry` form `STGijDecgL` (`Chain/CltGen.lean:93`). -/
def T2478_LocalReaderDec : Prop :=
  ∀ {d : ℕ} {sz : Sizes d} (Cm : Step2Data sz) (μ : Measure sz.SeqΩ), 0 < d →
    ∀ {κ ε 𝔠 𝔡 : ℝ}, Cm.flowOK κ ε 𝔠 𝔡 → ∀ {s t : ℕ → ℝ}, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) →
    (∀ n, t n ≤ Cm.T0 n) →
    (∃ cB c : ℝ, 0 < cB ∧ 0 < c ∧ ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ Cm.T0 n) →
      ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
        cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c)) →
    (∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ Cm.T0 n) → ∀ ε₀ : ℝ, 0 < ε₀ →
      STGiiGEXgL Cm.toFlowFM μ u ε₀) →
    (∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ Cm.T0 n) → STGijDecgL Cm.toFlowFM μ u) →
    STStep1WeakgL Cm.toFlowFM μ s t → STL2decayPTgL Cm.toFlowFM μ s t →
    STStep2LocalPTgL Cm.toFlowFM μ s t

/-- **Target 9 (GMN-C1), `stLocalAvgOfL2_holdsDecG`** (binding; conditional): `stLocalAvgOfL2_holdsG` (`LocalAvg2:467`) with `hGij`
in the `STGijDecgL` form. -/
def T2478_LocalAvgOfL2Dec : Prop :=
  ∀ {d : ℕ}, 0 < d → ∀ (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Data sz),
    (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → (mk sz z).flowOK κ ε 𝔠 𝔡) →
    (∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∃ cB c : ℝ, 0 < cB ∧ 0 < c ∧ ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ (mk sz z).T0 n) →
        ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
          cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c)) →
    (∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ (mk sz z).T0 n) → ∀ ε₀ : ℝ, 0 < ε₀ →
        STGiiGEXgL (mk sz z).toFlowFM (law sz) u ε₀) →
    (∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ (mk sz z).T0 n) →
        STGijDecgL (mk sz z).toFlowFM (law sz) u) →
    (∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ (mk sz z).T0 n) → ∀ ε₀ : ℝ, 0 < ε₀ →
        STGavLGEXgL (mk sz z).toFlowFM (law sz) u ε₀) →
    STLocalAvgOfL2gL d law Flow (fun sz z => (mk sz z).toFlowFM) (fun sz z => (mk sz z).T0)

/-- **Target 10, class `Step2IterGen_ListLink`** (binding): the list-index link of section 12.2 (`Step2Iterate:1586-1700`): `LM` is
`LIM` at `KLloopOf σ a` (band `STLM_eq_STLIM`, model-free through `loopM_eq_loopL`) and `KI` at `KLloopOf σ a` is `K` (band
definitional; BA `baStep2Mat_KI`). -/
def T2478_ListLink {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) : Prop :=
  (∀ (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (k : ℕ)
      (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Cm.LM n u H σ a = Cm.LIM n u H (KLloopOf d (sz.L n) σ a)) ∧
    ∀ (n : ℕ) (u : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Cm.KI n u (KLloopOf d (sz.L n) σ a) = Cm.K n u σ a

/-! ### Shapes (not binding) -/

/-- Shape: target 1 at the band family (discharges `stNewKLK_holds`, `ST_K2e_of_flow`, `ST_Kloop_one`, `ST_Lloop_one_false`). -/
example : Prop :=
  T2478_NewKLK 3 (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandStep2Mat sz (STflowE z))
example : Prop :=
  T2478_K2 3 (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandStep2Mat sz (STflowE z))
example (sz : Sizes 3) (E : ℕ → ℝ) : Prop := T2478_OneLoop (bandFM sz E) ∧ T2478_ListLink (bandStep2Mat sz E)

/-- Shape: the band bridge of target 3 (expected definitional). -/
example {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (Cd : ℝ) (s t : ℕ → ℝ) (Kf : ℕ → ℝ → ℝ) : Prop :=
  STSelfImp sz Cd E s t Kf ↔ T2478_SelfImpgL (bandFM sz E) (Sizes.seqP sz) Cd s t Kf

/-- Shape: the band readings that the premise scan needs as concluded heads (target 6). -/
example (d : ℕ) : Prop :=
  STBdatagL d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun _ z n => lemT (z n)) ∧
    STScaleExistsgL d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun _ z n => lemT (z n))

/-- Shape: the band Green input of target 9 (`bandFM_STGijDecgL_of_three_le`, `3 ≤ d`). -/
example (sz : Sizes 3) (z : ℕ → ℂ) (t : ℕ → ℝ) : Prop :=
  STGijDecgL (bandStep2Data sz z).toFlowFM (Sizes.seqP sz) t

/-- Shape (T1-BA): target 1 at the BA family `baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)`; sources `stNewKLKgL'_ba`,
`stK2decaygL'_ba` at `sz.withLam (BAflowLam0 sz z)` with the R1 comparison below, `baKsol_one`, `loopM_eq_loopL`, `baStep2Mat_KI`. -/
example : Prop :=
  T2478_NewKLK 3 (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))
example : Prop :=
  T2478_K2 3 (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))
example (sz : Sizes 3) (z : ℕ → ℂ) : Prop :=
  T2478_OneLoop (baFMz sz z) ∧ T2478_ListLink (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))

/-- Shape (T1-BA): the conclusion of target 6 at the BA family is the pin `BAStep2` (`BA/FlowPins.lean:432`). -/
example (d : ℕ) : Prop :=
  STStep2G d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).toFlowFM) BAflowT0 ↔ BAStep2 d

/-- Shape (T1-BA): the Green input of target 9 at BA (U4-BA's implication from `BAGbEXPij'`, registry `STGijDecgL`). -/
example (sz : Sizes 3) (z : ℕ → ℂ) (t : ℕ → ℝ) : Prop :=
  STGijDecgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t

/-- The UBA-C1 literal R1 (DECISIONS §273 (1)); not triggered in this row (no generic statement reads a kernel coupling); the only
allowed text if a crossing appears, and the text T1-BA uses for the profile comparison of target 1 at BA. -/
example {d : ℕ} (sz : Sizes d) (gK : ℕ → ℝ) (A : ℝ) : Prop :=
  ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2

end RBM.BA

end

/-! ## Part 3 (G1): the band names restated or read, unchanged (`example : <statement> := <name>` in the audit) -/

#check @RBM.Gauss.Sizes.STSelfImp
#check @RBM.Gauss.Sizes.ST_next
#check @RBM.Gauss.Sizes.ST_decay_of_final
#check @RBM.Gauss.Sizes.ST_selfImprove_section
#check @RBM.Gauss.Sizes.ST_selfImprove
#check @RBM.Gauss.Sizes.ST_iterate
#check @RBM.Gauss.Sizes.ST_decay_pt
#check @RBM.Gauss.Sizes.ST_L2_cmp
#check @RBM.Gauss.Sizes.ST_L2_decay_pt
#check @RBM.Gauss.Sizes.ST_base_inv
#check @RBM.Gauss.Sizes.ST_Kloop_one
#check @RBM.Gauss.Sizes.ST_Lloop_one_false
#check @RBM.Gauss.Sizes.ST_avgU_of_avg
#check @RBM.Gauss.Sizes.ST_concl_of_step2
#check @RBM.Gauss.Sizes.ST_step2_of_pins
#check @RBM.Gauss.Sizes.ST_step2_of_pins'
#check @RBM.Gauss.Sizes.ST_step2_of_pinsN
#check @RBM.Gauss.Sizes.ST_step2_of_pinsN'
#check @RBM.Gauss.Sizes.ST_step2_of_pinsLW'
#check @RBM.Gauss.Sizes.STStep2Parts
#check @RBM.Gauss.Sizes.ST_step2_concl
#check @RBM.Gauss.Sizes.ST_gridMart_of_repN
#check @RBM.Gauss.Sizes.STLKM_eq_STLKIM
#check @RBM.Gauss.Sizes.STLM_eq_STLIM
#check @RBM.Gauss.Sizes.STgA_eq_STgAN
#check @RBM.Gauss.Sizes.STthetaOp_eq_ThetaN
#check @RBM.Gauss.Sizes.STELKLKM_eq_STelklkM
#check @RBM.Gauss.Sizes.STavgM_eq_STavgErrM
#check @RBM.Gauss.Sizes.STEGtM_eq_STegtM
#check @RBM.Gauss.Sizes.STEEM_eq_STeeM
#check @RBM.Gauss.Sizes.STgDrift_eq_STgDriftN
#check @RBM.Gauss.Sizes.OptL2aJ
#check @RBM.Gauss.Sizes.OptL2a_drift_matrix
#check @RBM.Gauss.Sizes.OptL2a_drift_grid
#check @RBM.Gauss.Sizes.OptL2a_pathwise
#check @RBM.Gauss.Sizes.stOptL2a_drift
#check @RBM.Gauss.Sizes.stOptL2a_martingale
#check @RBM.Gauss.Sizes.stOptL2a_gronwall
#check @RBM.Gauss.Sizes.stOptL2_of_pins
#check @RBM.Gauss.Sizes.STGoodAt
#check @RBM.Gauss.Sizes.ST_good_engine
