/-
Release check for T2502 = V1s1 (dispatcher V4, 2026-10-14; DECISIONS §314; supervisor 0342 Q2/Q3/O1).  BA sub-stage V, first row group:
the generic conversion of the band Step 6 layer over the carrier (band `Induction/Step6Pins`, `Step6Kit`, `ExpAvg`, `ExpDuhamel`,
`ExpHier`; 4,730 lines, 22 frozen), NEW-FILE layout (0342 Q3: certificate cone): row a `Chain/Step6Gen` + `Chain/Step6KitGen`,
row b `Chain/ExpHierGen` + `Chain/ExpDuhamelGen`, row c `Chain/ExpAvgGen`.  No band file is edited (G1 by construction).
Part 1: merged names (`main` bbb1fd30; file:line in the comments, checked by grep).  Part 2: Prop values (prefix `T2502_`).
Binding: `T2502_Exp2UgL`, `T2502_Step2CoregL`, `T2502_IngR6gL`, `T2502_Step6RgL` (row a, vocabulary and shape; V2a's gate T2503
reads these two texts for the Step-6 input of the family step), `T2502_ExpAvgAtgL`, `T2502_ImproveExpAvergL` (row a text, row c proof),
`T2502_ExpHierAtgL`, `T2502_ExpDuhamelZAtgL`, `T2502_ExpDuhamelQAtgL`, `T2502_ExpDuhamelZgL`, `T2502_ExpDuhEqgL` (row a text, row b proof),
`T2502_EGtHiConclgL`, `T2502_EGtHiOfLW` (row a).  Not binding (shapes, fixed at the 1a or at row c's gate): the band and BA readings,
the per-index bundle of row b, the two W1 drafts of row c.
Only names, statements and Prop-valued definitions; no proofs.
Run: lake env lean docs/tickets/checks/T2502-check.lean
-/
import RBM3D.Induction.ExpDuhamel
import RBM3D.Induction.ExpAvg
import RBM3D.Induction.ExpIntEasy
import RBM3D.Induction.ExpIntIQ
import RBM3D.Induction.MainIndRegimes
import RBM3D.Chain.Step5Gen
import RBM3D.Chain.LWGen
import RBM3D.Chain.HierDriftGen
import RBM3D.Chain.GridDuhamelGen
import RBM3D.Chain.CltGen
import RBM3D.Chain.Step34Gen
import RBM3D.Chain.Step2EventsGen
import RBM3D.Chain.Step2EventsGenTw
import RBM3D.Chain.Step5CasesGen
import RBM3D.Chain.IniTermIIGen
import RBM3D.Chain.StepDecompGen
import RBM3D.Evolution.XiPins
import RBM3D.BA.CltFlowBA
import RBM3D.BA.GridDriftBA
import RBM3D.BA.SEforLnBA
import RBM3D.BA.Step5KerBA
import RBM3D.BA.EKPins
import RBM3D.BA.LWPinsBA
import RBM3D.Graph.BALWOut

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- row 0 / T8 / U3s1 (`Chain/Carrier:51-203`, `Chain/Step2Gen:85-514`, `Chain/Step34Gen:58-65`): carrier, law, the Step 1-4 pins over the carrier
#check @RBM.BA.PrecL                 -- Carrier:51
#check @RBM.BA.FlowFM                -- Carrier:55
#check @RBM.BA.STLKgL                -- Carrier:80
#check @RBM.BA.STLmaxgL              -- Carrier:87
#check @RBM.BA.STDecaygL             -- Carrier:94
#check @RBM.BA.STLocalEntrygL        -- Carrier:121
#check @RBM.BA.STExp2gL              -- Carrier:127
#check @RBM.BA.STKboundgL            -- Carrier:147
#check @RBM.BA.bandFM                -- Carrier:203
#check @RBM.BA.Step2Mat              -- Step2Gen:85
#check @RBM.BA.bandStep2Mat          -- Step2Gen:136
#check @RBM.BA.Step2Gen_thetaKer     -- Step2Gen:188
#check @RBM.BA.Step2Gen_uKer         -- Step2Gen:192
#check @RBM.BA.Step2Gen_ThetaN       -- Step2Gen:197
#check @RBM.BA.Step2Gen_UN           -- Step2Gen:202
#check @RBM.BA.STEGtg                -- Step2Gen:455
#check @RBM.BA.STAvgUgL              -- Step2Gen:491
#check @RBM.BA.STLocalEntryUgL       -- Step2Gen:497
#check @RBM.BA.STGdecayWgL           -- Step2Gen:503
#check @RBM.BA.STStep2ConclgL        -- Step2Gen:514
#check @RBM.BA.STLmaxUgL             -- Step34Gen:58
#check @RBM.BA.STLKUgL               -- Step34Gen:65
-- U6 (`Chain/Step5Gen`, 1debc230): the Step-5 shape over the carrier tuple (the pattern of `STIngR6gL`) and its band bridge
#check @RBM.BA.STELKLKg              -- Step5Gen:74
#check @RBM.BA.STIngR5gL             -- Step5Gen:191
#check @RBM.BA.STStep5RgL            -- Step5Gen:214
#check @RBM.BA.STStep5IIIgL          -- Step5Gen:228
#check @RBM.BA.bandFM_STELKLK        -- Step5Gen:272
#check @RBM.BA.STIngR5_iff_gL        -- Step5Gen:376
-- L0 (`Chain/LWGen`, 3efd9dad): the LW observables and pins over the carrier (the `LWtermEXP` / `LWAvgLaw` / `LWcut` readings)
#check @RBM.BA.LWcutg                -- LWGen:39
#check @RBM.BA.LWEg                  -- LWGen:44
#check @RBM.BA.LWAvgLawgL            -- LWGen:48
#check @RBM.BA.LWtermEXPG            -- LWGen:108
#check @RBM.BA.bandPin               -- LWGen:130
#check @RBM.BA.LWtermEXP_iff         -- LWGen:144
-- T7b / U4s1a (`Chain/Step2EventsGen`, 97341078; `Chain/Step5CasesGen`, c9f69dba): flow facts, F7 rotation
#check @RBM.BA.Step2EventsGen_Flow   -- Step2EventsGen:68
#check @RBM.BA.Step2EventsGen_Rot3   -- Step2EventsGen:74
#check @RBM.BA.Step5CasesGen_FlowFacts -- Step5CasesGen:140
-- T4s1 / T5s2 (`Chain/GridDuhamelGen`, 4fad6107; `Chain/StepDecompGen`, e8fd7d27; `Chain/HierDriftGen`, eaa247c4): kernel window, loop form, hierarchy classes
#check @RBM.BA.Step2Gen_USemigroup   -- GridDuhamelGen:51
#check @RBM.BA.StepDecompGen_LoopForm -- StepDecompGen:60
#check @RBM.BA.HierDriftGen_KLoop    -- HierDriftGen:320
#check @RBM.BA.HierDriftGen_KTwo     -- HierDriftGen:326
#check @RBM.BA.HierarchyNg           -- HierDriftGen:429
#check @RBM.BA.hierarchyNg_of        -- HierDriftGen:441 (`∀ n` premises; row b restates it per index, 0849 `:72-77`)
#check @RBM.BA.HierDriftGen_UStep    -- HierDriftGen:666
#check @RBM.BA.HierDriftGen_KLink    -- HierDriftGen:677
-- X1a (`Chain/CltGen`, 62eed82c): the representation class (W2 of row b, W1 of row c)
#check @RBM.BA.CltRepg               -- CltGen:84
-- U3s1 (`Chain/Step34Gen`, 6e7d2602): the kernel pins of the initial terms, R1
#check @RBM.BA.STEKKer               -- Step34Gen:526
#check @RBM.BA.STEKSumNdecaygL       -- Step34Gen:529
#check @RBM.BA.STEKNonzerogL         -- Step34Gen:575
#check @RBM.BA.STEKBandKer           -- Step34Gen:587
#check @RBM.BA.stek_sumNdecaygL_band -- Step34Gen:617
#check @RBM.BA.stek_nonzerogL_band   -- Step34Gen:644
#check @RBM.BA.step34Gen_winK_of_cmp -- Step34Gen:683 (R1 text, DECISIONS §273 (1))
-- U4s2 (`Chain/IniTermIIGen`): the family class whose R1 conjunct and `USemigroup` the BA side reads
#check @RBM.BA.IniTermGen_KerFacts   -- IniTermIIGen:68
-- BA discharges (family table; read by V1-BA, never imported by the new files)
#check @RBM.BA.BAflowT0              -- BA/FlowPins:380
#check @RBM.BA.BAflowLam0            -- BA/FlowPins:386
#check @RBM.BA.BAFlow                -- BA/FlowPins:389
#check @RBM.BA.baFMz                 -- BA/FlowPins:393
#check @RBM.BA.Step2EventsGenTw_baFlow -- Chain/Step2EventsGenTw:53
#check @RBM.BA.Step2EventsGenTw_baRot3 -- Chain/Step2EventsGenTw:58
#check @RBM.BA.baStep2Mat_loopForm   -- BA/SEforLnBA:135 (U2-BA, 7be99aae)
#check @RBM.BA.baStep5CasesGen_flowFacts -- BA/SEforLnBA:152
#check @RBM.BA.baHierDrift_classes   -- BA/GridDriftBA:631 (T5-BA, b3ead83b)
#check @RBM.BA.baIniTermGen_kerFacts -- BA/Step5KerBA:161 (T2501 a1, 4c9a9311)
#check @RBM.BA.baCltRepg_holds       -- BA/CltFlowBA:316 (T2501 a2, db1932eb)
#check @RBM.BA.baEKSumNdecay_holds   -- BA/EKPins:218
#check @RBM.BA.baEKSameRow_holds     -- BA/EKPins:568 (W1 (ii))
#check @RBM.BA.band_LWtermEXPG       -- BA/LWPinsBA:59 (band, `d = 3`)
#check @RBM.BA.BALWtermEXPTw         -- Graph/BAExp14a2:92 (seven premises)
#check @RBM.BA.baLWtermEXPTw_holds   -- Graph/BALWOut:54
#check @RBM.BA.baLWCutExpTw_holds    -- Graph/BALWOut:48
#check @RBM.ekSameRow_holds          -- Evolution/XiPins:357 (W1 (ii), band)
#check @RBM.Gauss.deriv_integral_gloop_eq_integral_samplewiseLoopGeneratorCuts -- Gauss/LoopGenerator:312 (W2: `H₀ = 0`, `zt E`)
-- the band texts converted here (unchanged; `RBM.Gauss.Sizes`)
#check @RBM.Gauss.Sizes.STExp2U      -- Step6Pins:71
#check @RBM.Gauss.Sizes.STExp2_of_STExp2U -- Step6Pins:87
#check @RBM.Gauss.Sizes.STStep2Core  -- Step6Pins:95
#check @RBM.Gauss.Sizes.STIngR6      -- Step6Pins:111
#check @RBM.Gauss.Sizes.STStep6R     -- Step6Pins:126
#check @RBM.Gauss.Sizes.STStep6I     -- Step6Pins:131
#check @RBM.Gauss.Sizes.STStep6II    -- Step6Pins:134
#check @RBM.Gauss.Sizes.STStep6III   -- Step6Pins:137
#check @RBM.Gauss.Sizes.STStep6IV    -- Step6Pins:140
#check @RBM.Gauss.Sizes.STStep6      -- Step6Pins:145
#check @RBM.Gauss.Sizes.ST_step6R_of_any -- Step6Pins:149
#check @RBM.Gauss.Sizes.STExpAvgAt   -- Step6Pins:177
#check @RBM.Gauss.Sizes.STImproveExpAver -- Step6Pins:191
#check @RBM.Gauss.Sizes.STExpHier    -- Step6Pins:213
#check @RBM.Gauss.Sizes.STExpDuhamelZ -- Step6Pins:225
#check @RBM.Gauss.Sizes.STExpDuhamelQ -- Step6Pins:246
#check @RBM.Gauss.Sizes.STExpDuhEq   -- Step6Pins:256 (`∀ n`; the generic twin is eventual, answer (5))
#check @RBM.Gauss.Sizes.STExpDuhEqQ  -- Step6Pins:266
#check @RBM.Gauss.Sizes.STDriftHi    -- Step6Pins:286 (size level, reused)
#check @RBM.Gauss.Sizes.STExpEGtHiConcl -- Step6Pins:305
#check @RBM.Gauss.Sizes.STExpTarget  -- Step6Pins:65 (size level, reused)
#check @RBM.Gauss.Sizes.STRegSeq     -- Step6Pins:482 (size level, reused)
#check @RBM.Gauss.Sizes.STIdx2       -- Step5Pins:139 (size level, reused)
#check @RBM.Gauss.Sizes.st6_precU_of_forall_seq -- Step6Kit:115
#check @RBM.Gauss.Sizes.LWAvgLaw_of_STAvgU_at -- Step6Kit:189
#check @RBM.Gauss.Sizes.st6_EGt_eq_LWE -- Step6Kit:327
#check @RBM.Gauss.Sizes.st6_expAvgU_of_pin -- Step6Kit:557
#check @RBM.Gauss.Sizes.st6_EGtHi_of_LW -- Step6Kit:571
#check @RBM.Gauss.Sizes.st6_ini_sumNdecay -- Step6Kit:600
#check @RBM.Gauss.Sizes.st6_ini_nonzero -- Step6Kit:651
#check @RBM.Gauss.Sizes.ST_step6_caseIII_of_pins -- Step6Kit:737
#check @RBM.Gauss.Sizes.ST_step6_caseIV_of_pins -- Step6Kit:786
#check @RBM.Gauss.Sizes.ST_step6_caseII_of_pins -- Step6Kit:865
#check @RBM.Gauss.Sizes.ST_step6_caseI_of_pins -- Step6Kit:947
#check @RBM.Gauss.Sizes.STExpAvgAt_of_LWAvgLaw -- ExpAvg:799
#check @RBM.Gauss.Sizes.stImproveExpAver_holds -- ExpAvg:879
#check @RBM.Gauss.Sizes.expHier_genMat_eq_cuts -- ExpHier:331
#check @RBM.Gauss.Sizes.stExpHier_holds -- ExpHier:770
#check @RBM.Gauss.Sizes.stExpDuhamelZ_holds -- ExpDuhamel:385
#check @RBM.Gauss.Sizes.stExpDuhamelQ_holds -- ExpDuhamel:570
-- band readers downstream (not edited; they keep compiling because no band file changes)
#check @RBM.Gauss.Sizes.ST_mainIndR_I_of_steps -- MainIndRegimes:222
#check @RBM.Gauss.Sizes.stStep6IV_holds -- ExpIntEasy:626
#check @RBM.Gauss.Sizes.stStep6I_of_LW -- ExpIntIQ:1362

/-! ## Part 2: the target statements (binding as marked), then shapes (not binding) -/

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes
open MeasureTheory ProbabilityTheory Filter

/-! ### Row a, `Chain/Step6Gen`: the target of Step 6 and the shape (binding) -/

/-- **Target 2, `STExp2UgL`** (band `STExp2U`, `Step6Pins:71`): `(Eq:Gtlp_exp_flow)` uniformly in `u ∈ [s,t]` over a carrier and a law;
the uniform form of `STExp2gL` (`Carrier:127`). -/
def T2502_Exp2UgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n p _ => ‖(∫ ω, C.L n (p.1 : ℝ) p.2.1 p.2.2 ω ∂μ) - C.K n (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ 2 *
        ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n (p.1 : ℝ)))

/-- **Target 2, `STStep2CoregL`** (band `STStep2Core`, `Step6Pins:95`). -/
def T2502_Step2CoregL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  STLocalEntryUgL C μ s t ∧ STAvgUgL C μ s t

/-- **Target 2, `STIngR6gL`** (band `STIngR6`, `Step6Pins:111`) over the carrier tuple `(law, Flow, mk, T0)` of `STIngR5gL`
(`Step5Gen:191`); the premises are the band ones read over the carrier (no `STKboundgL`, `STKwardgL`: answer (6)). -/
def T2502_IngR6gL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Concl : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ T0 sz z n) →
          R sz s t → STLKgL (mk sz z) (law sz) s → STDecaygL (mk sz z) (law sz) s →
          STExp2gL (mk sz z) (law sz) s → STConStInd sz 𝔠d s t →
          T2502_Step2CoregL (mk sz z) (law sz) s t → STLmaxUgL (mk sz z) (law sz) s t →
          STLKUgL (mk sz z) (law sz) s t → STGdecayWgL (mk sz z) (law sz) s t 0 →
            Concl sz z s t

/-- **Target 2, `STStep6RgL`** (band `STStep6R`, `Step6Pins:126`); `STStep6IgL` .. `STStep6IVgL`, `STStep6gL` are it at
`STReg5I` .. `STReg5IV`, `STAny`. -/
def T2502_Step6RgL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  T2502_IngR6gL d R law Flow mk T0 (fun sz z s t => T2502_Exp2UgL (mk sz z) (law sz) s t)

/-! ### Row a text, row c proof: `lem:improve_exp_aver` (binding) -/

/-- **Target 3, `STExpAvgAtgL`** (band `STExpAvgAt`, `Step6Pins:177`): `max_a |𝔼 𝓛^{(1)}_{u,σ,a} - m_σ| ≺ (W^{-d}B_{u,0})²`, both charges. -/
def T2502_ExpAvgAtgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (u : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => Bool × Zd d (sz.L n))
    (fun n p _ => ‖(∫ ω, C.L n (u n) (fun _ : Fin 1 => p.1) (fun _ => p.2) ω ∂μ) -
      (if p.1 then C.m n else (starRingEnd ℂ) (C.m n))‖)
    (fun n _ _ => (sz.Bctl n (u n)) ^ 2)

/-- **Target 3, `STImproveExpAvergL`** (band `STImproveExpAver`, `Step6Pins:191`) over the carrier tuple; proved by row c
(`stImproveExpAvergL_of`, under the family table). -/
def T2502_ImproveExpAvergL (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ T0 sz z n) →
        LWAvgLawgL (mk sz z) (law sz) u → STLKgL (mk sz z) (law sz) u → T2502_ExpAvgAtgL (mk sz z) (law sz) u

/-! ### Row a text, row b proof: the expected hierarchy at `n = 2` and the Duhamel forms, per index (binding; UP-C4) -/

/-- **Target 3, `STExpHierAtgL`** (band `STExpHier`, `Step6Pins:213`, at one index `n`, no `|E| < 2`): with
`f_u = 𝔼 𝓛^{(2)}_u - 𝒦^{(2)}_u` and `D_u = 𝔼 ℰ^{LK×LK}_u + 𝔼 ℰ^{G̃}_u`, both continuous on `[0,1)` and `∂_u f_u = Θ^{(2)}_{u,σ} f_u + D_u`
on `(0,1)`, `Θ` the carrier generator `Step2Gen_ThetaN`. -/
def T2502_ExpHierAtgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (n : ℕ) : Prop :=
  ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
    ContinuousOn (fun u => (∫ ω, C.L n u σ a ω ∂μ) - C.K n u σ a) (Set.Ico (0 : ℝ) 1) ∧
    ContinuousOn (fun u => (∫ ω, STELKLKg C n u σ a ω ∂μ) + ∫ ω, STEGtg C n u σ a ω ∂μ) (Set.Ico (0 : ℝ) 1) ∧
    ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun v => (∫ ω, C.L n v σ a ω ∂μ) - C.K n v σ a)
      (Step2Gen_ThetaN C n σ u (fun b => (∫ ω, C.L n u σ b ω ∂μ) - C.K n u σ b) a +
        ((∫ ω, STELKLKg C n u σ a ω ∂μ) + ∫ ω, STEGtg C n u σ a ω ∂μ)) u

/-- **Target 3, `STExpDuhamelZAtgL`** (band `STExpDuhamelZ`, `Step6Pins:225`, at one index, kernel `Step2Gen_UN C`). -/
def T2502_ExpDuhamelZAtgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (n : ℕ) : Prop :=
  ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 →
    ∀ (σ : Fin 2 → Bool) (A : Finset (Fin 2)) (a : Fin 2 → Zd d (sz.L n)),
      zeroModeSet d (sz.L n) A (fun b => (∫ ω, C.L n t σ b ω ∂μ) - C.K n t σ b) a =
        zeroModeSet d (sz.L n) A
          (Step2Gen_UN C n σ s t (fun b => (∫ ω, C.L n s σ b ω ∂μ) - C.K n s σ b)) a +
        ∫ u in s..t, zeroModeSet d (sz.L n) A
          (Step2Gen_UN C n σ u t (fun b => (∫ ω, STELKLKg C n u σ b ω ∂μ) + ∫ ω, STEGtg C n u σ b ω ∂μ)) a

/-- **Target 3, `STExpDuhamelQAtgL`** (band `STExpDuhamelQ`, `Step6Pins:246`, at one index; the source is `STExpQsrc`, `:236`, read
over the carrier; the mollifier at the size coupling `sz.lam n`). -/
def T2502_ExpDuhamelQAtgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (n : ℕ) : Prop :=
  ∀ (Cq c : ℝ) (ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ), STMollifierProps (d := d) (sz.lam n) Cq c ϑ →
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      STQop (d := d) ϑ t (fun b => (∫ ω, C.L n t σ b ω ∂μ) - C.K n t σ b) a =
        Step2Gen_UN C n σ s t (STQop (d := d) ϑ s (fun b => (∫ ω, C.L n s σ b ω ∂μ) - C.K n s σ b)) a +
        ∫ u in s..t, Step2Gen_UN C n σ u t (fun b =>
          STQop (d := d) ϑ u (fun c' => (∫ ω, STELKLKg C n u σ c' ω ∂μ) + ∫ ω, STEGtg C n u σ c' ω ∂μ) b +
            (STQop (d := d) ϑ u (Step2Gen_ThetaN C n σ u (fun c' => (∫ ω, C.L n u σ c' ω ∂μ) - C.K n u σ c')) b -
              Step2Gen_ThetaN C n σ u (STQop (d := d) ϑ u (fun c' => (∫ ω, C.L n u σ c' ω ∂μ) - C.K n u σ c')) b) -
            STPsum (d := d) (fun c' => (∫ ω, C.L n u σ c' ω ∂μ) - C.K n u σ c') (b 0) * deriv (fun τ => ϑ τ b) u) a

/-- **Target 3, `STExpDuhamelZgL`**: the eventual family form (UP-C4: the hierarchy classes hold only eventually at BA);
`STExpDuhamelQgL` is the same with `T2502_ExpDuhamelQAtgL`. -/
def T2502_ExpDuhamelZgL (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) : Prop :=
  ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
    ∀ᶠ n in atTop, T2502_ExpDuhamelZAtgL (mk sz z) (law sz) n

/-- **Target 3, `STExpDuhEqgL`** (band `STExpDuhEq`, `Step6Pins:256`, which is `∀ n`): the Duhamel identities along `[s_n, t_n]`,
**eventually in `n`** (answer (5); as the band `STExpDuhEqQ`, `:266`). -/
def T2502_ExpDuhEqgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (σ : Fin 2 → Bool) (A : Finset (Fin 2)) (a : Fin 2 → Zd d (sz.L n)),
    zeroModeSet d (sz.L n) A (fun b => (∫ ω, C.L n (u : ℝ) σ b ω ∂μ) - C.K n (u : ℝ) σ b) a =
      zeroModeSet d (sz.L n) A
        (Step2Gen_UN C n σ (s n) (u : ℝ) (fun b => (∫ ω, C.L n (s n) σ b ω ∂μ) - C.K n (s n) σ b)) a +
      ∫ v in (s n)..(u : ℝ), zeroModeSet d (sz.L n) A
        (Step2Gen_UN C n σ v (u : ℝ) (fun b => (∫ ω, STELKLKg C n v σ b ω ∂μ) + ∫ ω, STEGtg C n v σ b ω ∂μ)) a

/-! ### Row a, `Chain/Step6KitGen`: the LW reading (binding) -/

/-- **Target 3, `STExpEGtHiConclgL`** (band `STExpEGtHiConcl`, `Step6Pins:305`). -/
def T2502_EGtHiConclgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := STIdx2 sz s t)
    (fun n p _ => ‖∫ ω, STEGtg C n (p.1 : ℝ) p.2.1 p.2.2 ω ∂μ‖)
    (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (5 / 2 : ℝ))

/-- **Target 6, `st6_EGtHi_of_LWg`** (band `st6_EGtHi_of_LW`, `Step6Kit:571`), per carrier: the LW bound at every time sequence
`u ∈ [s,t]` (the conclusion of `LWtermEXPG`, `LWGen:108`, at `u`; at BA the conclusion of `BALWtermEXPTw`, `BAExp14a2:92`) gives
`(eq:ExpLWn=2)` uniformly in `u`, through F7 (`STEGtg = LWEg`) and the deterministic `≺` calculus at the law `μ`. -/
def T2502_EGtHiOfLW {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  IsProbabilityMeasure μ → sz.SizeTendsto → (∀ n, s n ≤ t n) → STDriftHi sz s t → Step2EventsGen_Rot3 C →
    (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
      PrecL sz μ (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
          sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - u n})
        (fun n p _ => ‖∫ ω, LWEg C n (u n) p.1.1 p.1.2 ω ∂μ‖)
        (fun n _ _ => (1 - u n)⁻¹ * (sz.Bctl n (u n)) ^ (5 / 2 : ℝ))) →
      T2502_EGtHiConclgL C μ s t

/-! ### Shapes (not binding) -/

/-- The band reading of the Step-6 pin: `STStep6R d R` is this at the band tuple (bridge `STStep6R_iff_gL`, row a). -/
def T2502_Step6RgL_band (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  T2502_Step6RgL d R (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))

/-- The BA reading (the tuple of T2499/T2501; V1-BA's `BAStep6R` is this or its family/TL extension, decided at V2a's gate T2503). -/
def T2502_Step6RgL_BA (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  T2502_Step6RgL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)

/-- Row b, target 12: the per-index bundle of `stExpHiergL_at` (draft; the 1a fixes the list). -/
def T2502_ExpHierAtOf {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ)
    (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (g' E : ℕ → ℝ) (n : ℕ) : Prop :=
  CltRepg Cm.toFlowFM μ H₀ g' E → StepDecompGen_LoopForm Cm E → Cm.S n = SB d (sz.L n) (g' n) →
    HierDriftGen_KLoop Cm n → HierDriftGen_KTwo Cm n → HierDriftGen_KLink Cm n →
      T2502_ExpHierAtgL Cm.toFlowFM μ n

/-- Row b, target 13: Duhamel from the hierarchy and the kernel window at one index (draft). -/
def T2502_ExpDuhamelZAtOf {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (n : ℕ) : Prop :=
  Step2Gen_USemigroup C n → T2502_ExpHierAtgL C μ n → T2502_ExpDuhamelZAtgL C μ n

/-- Row c, W1 (i), draft for the gate: the carrier's `M` solves the self-consistent equation of `H₀ + √u X` along the flow
(band `M = m(E) I`, `m² + E m + 1 = 0`; BA `BASelf`/`BAMB`, `BA/MFixedPoint:190-193`). -/
def T2502_W1SelfConsDraft {d : ℕ} {sz : Sizes d} (C : FlowFM sz)
    (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (E : ℕ → ℝ) : Prop :=
  ∀ n, (H₀ n - ((E n : ℂ) + C.m n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) *
      Matrix.of (fun x y => C.M n x y) = 1

/-- Row c, W1 (ii), draft for the gate: the same-charge row bound of the carrier kernel without the `(1-t)⁻¹` loss
(band `ekSameRow_holds`, `Evolution/XiPins:357`; BA `baEKSameRow_holds`, `BA/EKPins:568`). -/
def T2502_W1SameRowDraft {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (Cs : ℝ) : Prop :=
  ∀ (n : ℕ) (σ : Bool) (s t : ℝ), 0 ≤ s → s ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
    ∑ b : Zd d (sz.L n), ‖Step2Gen_uKer C n σ σ s t a b‖ ≤ Cs

end RBM.BA
