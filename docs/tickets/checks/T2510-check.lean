/-
Release check for T2510 (dispatcher V4, 2026-10-14; DECISIONS §332;
`docs/tickets/checks/T2510-check.lean`; not compiled by the dispatcher).  V V1-BA: Step 6 of `lem:main_ind` at the BA tuple
`(fun sz => Sizes.seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`; `gK = BAflowLam0`; `κm = κ`; `Aof κ = (κ+1)/κ`.
Part 1: merged names (`main` b4147edc); private names in comments (read by `open private`).  Part 2: pins `T2510_*`, binding:
`T2510_Step6BA` (= `BAStep6R`), the row-a targets, `T2510_RowB`; `T2510_LWAvgEv` is a shape (not binding).  T2508 is not fully merged (row a 57178a34 is; T2510 row a reads none of it):
row b's T2508 inputs are pinned in `T2508-check.lean:105, 119, 129, 157-199, 202, 239` (ticket prose only).  Statements only; merged modules only.  Run: lake env lean docs/tickets/checks/T2510-check.lean
-/
import RBM3D.Chain.Step6Gen
import RBM3D.Chain.Step6KitGen
import RBM3D.Chain.ExpAvgGen
import RBM3D.Chain.ExpHierGen
import RBM3D.Chain.ExpDuhamelGen
import RBM3D.Chain.ExpEtermsAGen
import RBM3D.Chain.ExpEtermsBGen
import RBM3D.Chain.ExpIniIGen
import RBM3D.Chain.ExpWardIGen
import RBM3D.Chain.ExpIntIIGen
import RBM3D.Chain.Step2EventsGen
import RBM3D.Chain.Step2EventsGenTw
import RBM3D.Chain.Step2CloseGen
import RBM3D.BA.TwistPins
import RBM3D.BA.TwistStep2
import RBM3D.BA.TwistLoop
import RBM3D.BA.CltFlowBA
import RBM3D.BA.GreenSchur
import RBM3D.BA.GreenCond2
import RBM3D.BA.EKGenBA
import RBM3D.BA.SEforLnBA
import RBM3D.BA.KInduct
import RBM3D.BA.KBound
import RBM3D.BA.Step2BA
import RBM3D.BA.Step2IterBA
import RBM3D.BA.GridDriftBA
import RBM3D.BA.DecayLoopBA
import RBM3D.BA.B45BA
import RBM3D.BA.Step5KerBA
import RBM3D.BA.Step5CasesBA
import RBM3D.BA.EMn2BA
import RBM3D.BA.FlowPins
import RBM3D.Graph.BAExp14a2
import RBM3D.Graph.BALWOut

set_option linter.style.longLine false

/-! ## Part 1: merged names -/
#check @RBM.BA.STIngR6gL                       -- Chain/Step6Gen:100
#check @RBM.BA.STStep6RgL                      -- Step6Gen:115 (T2502's text; `BAStep6R` adds the TL slot)
#check @RBM.BA.STStep6ConclgL                  -- Step6Gen:93 (= `STExp2UgL` :72, `rfl`)
#check @RBM.BA.STExpAvgUgL                     -- Step6Gen:160 (row 21, per flow)
#check @RBM.BA.STImproveExpAvergL              -- Step6Gen:316 (global; not at BA, §319 (3) (b))
#check @RBM.BA.STExpWardIIgL                   -- Step6Gen:351 (hypothesis of row a's regime (ii); T2508 a proves)
#check @RBM.BA.STExpIntIIIgL                   -- Step6Gen:356 (hypothesis of row a's regime (iii))
#check @RBM.BA.STExpIntIVgL                    -- Step6Gen:362 (hypothesis of row a's regime (iv))
#check @RBM.BA.LWAvgLawgL_of_STAvgUgL_at       -- Step6KitGen:139 (every-`n` `hK1`: no BA discharge, F1)
#check @RBM.BA.st6_EGtHi_of_LWg                -- Step6KitGen:284 (LW at each `u`; BA: `baLWtermEXPTw_holds`)
#check @RBM.BA.st6_expAvgU_of_ping             -- Step6KitGen:338 (global `hAvg`; not at BA)
#check @RBM.BA.st6_ini_sumNdecayg              -- Step6KitGen:365 (regimes (iii), (iv); row 5)
#check @RBM.BA.st6_ini_nonzerog                -- Step6KitGen:401 (regime (ii); row 6, R1 slot)
#check @RBM.BA.st6_caseIII_coreg               -- Step6KitGen:505
#check @RBM.BA.st6_caseIV_coreg                -- Step6KitGen:520
#check @RBM.BA.st6_caseII_coreg                -- Step6KitGen:536
#check @RBM.BA.st6_caseI_coreg                 -- Step6KitGen:601 (unprimed; row b reads T2508's `st6_caseI_coreg'`)
#check @RBM.BA.ST_step6_caseIII_of_pinsgL      -- Step6KitGen:676 (body pattern of target 9; reads `LWtermEXPG`, every-`n` `hK1`)
#check @RBM.BA.ST_step6_caseIV_of_pinsgL       -- Step6KitGen:715
#check @RBM.BA.ST_step6_caseII_of_pinsgL       -- Step6KitGen:746
#check @RBM.BA.ST_step6_caseI_of_pinsgL        -- Step6KitGen:795 (body pattern of target 13)
#check @RBM.BA.ExpAvgGen_W1iii                 -- Chain/ExpAvgGen:81
#check @RBM.BA.ExpAvgGen_W1iv                  -- ExpAvgGen:87
#check @RBM.BA.ExpAvgGen_W1fam                 -- ExpAvgGen:93 (rows 9 + 14 with (iv))
#check @RBM.BA.STImproveCoregL                 -- ExpAvgGen:104 (16a text)
#check @RBM.BA.stImproveCoregL_of              -- ExpAvgGen:1365 (16a)
#check @RBM.BA.stExpAvgUgL_of_core             -- ExpAvgGen:1416 (16c; every-`n` `hK1`)
#check @RBM.BA.stExpHiergL_ev                  -- Chain/ExpHierGen:797
#check @RBM.BA.stExpHiergL_at                  -- ExpHierGen:720 (O5 instance)
#check @RBM.BA.stExpDuhamelZgL_ev              -- Chain/ExpDuhamelGen:434
#check @RBM.BA.stExpDuhamelQgL_ev              -- ExpDuhamelGen:452
#check @RBM.BA.stExpLKLKHigL_of                -- Chain/ExpEtermsAGen:516
#check @RBM.BA.stExpDriftLogL_of               -- Chain/ExpEtermsBGen:717
#check @RBM.BA.stExpDriftDecaygL_of            -- ExpEtermsBGen:831 (row 18 at the `FlowFM` labels)
#check @RBM.BA.stExpWardIgL_of                 -- Chain/ExpWardIGen:413
#check @RBM.BA.stExpWardIgL'_of                -- ExpWardIGen:438
#check @RBM.BA.stExpIniIgL'_of                 -- Chain/ExpIniIGen:787
#check @RBM.BA.stExpIntIIgL_of                 -- Chain/ExpIntIIGen:313
#check @RBM.BA.Step2EventsGen_STEGtMg_eq       -- Chain/Step2EventsGen:409
#check @RBM.BA.STEGtMg_eq_STegtMg              -- Chain/Step2CloseGen:125
#check @RBM.BA.STELKLKMg_eq_STelklkMg          -- Step2CloseGen:102
#check @RBM.BA.BATwistAvgLaw                   -- BA/TwistPins:91 (TL1)
#check @RBM.BA.BATwistLoopLaw                  -- TwistPins:95 (TL2)
#check @RBM.BA.twMB_ba                         -- TwistPins:80 (`M^{(B)}` of `baFMz`)
-- private RBM.BA.TwistPins_circ_term          -- TwistPins:440 (bridge (iii), `open private`)
#check @RBM.BA.TwistStep2_tl1                  -- BA/TwistStep2:1137 (V2a supplies TL1)
#check @RBM.BA.baTwistLoopStep_caseI           -- BA/TwistLoop:705 (V2a supplies TL2)
#check @RBM.BA.baTwistLoopStep_caseII          -- TwistLoop:709
#check @RBM.BA.BALWtermEXPTw                   -- Graph/BAExp14a2:92 (seven premises, LC-3)
#check @RBM.BA.baLWtermEXPTw_holds             -- Graph/BALWOut:54
-- private RBM.BA.CltFlowBA_MB_decay           -- BA/CltFlowBA:221 (bridge (iv), `open private`)
#check @RBM.BA.GreenCond2_sum_exp_le           -- BA/GreenCond2:1148
#check @RBM.BA.BAflow_lam0_window              -- BA/GreenSchur:72
#check @RBM.BA.baCltRepg_holds                 -- CltFlowBA:316 (rows 9, 9 + 14; `H₀ = g₀Ψ`, `g′ = 0`)
#check @RBM.BA.baIniTermGen_cltFlow            -- CltFlowBA:566 (row 9′)
#check @RBM.BA.baStep5CasesGen_flowFacts       -- BA/SEforLnBA:152 (row 3, `κm = κ`)
#check @RBM.BA.baKsol_one                      -- BA/KInduct:77 (needs `0 < g₀ₙ`: eventual only, F1)
#check @RBM.BA.baKsol_oneLoop                  -- SEforLnBA:113 (row 19, `∀ᶠ n`)
#check @RBM.BA.baStep2Mat_loopForm             -- SEforLnBA:135 (row 10)
#check @RBM.BA.baSEforLnGen_facts              -- SEforLnBA:163 (row 20; label link of row 18)
-- private RBM.BA.SEforLnBA_Kbound             -- SEforLnBA:235 (row 17, no `0 < ε`)
#check @RBM.BA.baEtermDecaygL                  -- SEforLnBA:271 (row 18)
#check @RBM.BA.baKbound_holds                  -- BA/KBound:245 (needs `0 < ε`: F3)
#check @RBM.BA.baDecayLoopU_of                 -- BA/DecayLoopBA:60 (row 18)
#check @RBM.BA.baStep2Mat                      -- BA/Step2BA:54 (`mkM`)
#check @RBM.BA.baStep2Mat_toFlowFM             -- Step2BA:75 (`hmk`, `rfl`)
#check @RBM.BA.baStep2Mat_S                    -- BA/GridDriftBA:86 (row 10, `S = SB d L 0`)
#check @RBM.BA.baHierDrift_classes             -- GridDriftBA:631 (rows 11-12, eventual; UP-F3)
#check @RBM.BA.baIniTermGen_kerFacts           -- BA/Step5KerBA:161 (row 13: conjunct 1)
#check @RBM.BA.baStep5KerGen_thDecay           -- Step5KerBA:132 (row 22; row b, binder order `κ, 𝔡`)
#check @RBM.BA.baStep5CasesGen_wardIdent       -- BA/Step5CasesBA:128 (row 23; row b)
#check @RBM.BA.baB45Gen_facts                  -- BA/B45BA:205 (row 19′)
#check @RBM.BA.Step2EventsGenTw_baFlow         -- Chain/Step2EventsGenTw:53 (row 2)
#check @RBM.BA.Step2EventsGenTw_baRot3         -- Step2EventsGenTw:58 (row 4)
#check @RBM.Gauss.Sizes.isProbabilityMeasure_seqP -- Gauss/FineModel:171 (row 1)
#check @RBM.BA.BAEKKer                         -- BA/EKGenBA:64
#check @RBM.BA.baEKKer_flow                    -- EKGenBA:70 (`hKer`: `κm = κ`, R1 at `(κm+1)/κm`; O3)
#check @RBM.BA.baEKSumNdecaygL_holds           -- EKGenBA:317 (row 5)
#check @RBM.BA.baEKSumRes2NALgL_holds          -- EKGenBA:373 (row 16)
#check @RBM.BA.baEKSumRes2gL_holds             -- EKGenBA:396 (row 16)
#check @RBM.BA.baEKNonzerogL_holds             -- EKGenBA:427 (row 6)
#check @RBM.BA.FlowPinsInst.flow_sz0           -- FlowPins:1214
#check @RBM.BA.FlowPinsInst.half_lt_t0         -- FlowPins:1254
#check @RBM.BA.TwistStep2_flowII               -- TwistStep2:1353
#check @RBM.BA.GridDriftBAInst.inst_lam0_pos   -- GridDriftBA:695 (O5: `0 < g₀`, so `H₀ ≠ 0`)

open MeasureTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## Part 2: pins (binding unless marked) -/

/-- **Target 6, `BAStep6R`** (the one new public def; V2a's 1b reads it by name as `S6` of `T2503_RegShape`, `T2503-check:271`):
T2502's `STStep6RgL` (`Step6Gen:115`) at the BA tuple, with TL1, TL2 at every `u ∈ [s,t]` on the `Concl` slot (probe
`T2503_Step6BA`, `t/T2503` 93bd54cd `Probe/T2503Pins.lean:290`, with `T2503v1_*` → `STIngR6gL`, `STStep6ConclgL`). -/
def T2510_Step6BA (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  STIngR6gL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)
    (fun sz z s t => (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
      BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u ∧ BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u) →
      STStep6ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t)

/-- **Target 1, `baExpAvgGen_W1iii_of_tl1`** (bridge (iii)): TL1 at `u` gives W1 (iii) at `u`, along every BA flow. -/
def T2510_W1iiiOfTL1 (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → ∀ u : ℕ → ℝ,
    BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u → ExpAvgGen_W1iii (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u

/-- **Target 2, `baExpAvgGen_W1iv`** (bridge (iv), the public form of the private `CltFlowBA_MB_decay`): `∃ CM` after `(κ, 𝔡)`. -/
def T2510_W1ivBA (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ CM : ℝ, 0 < CM ∧
    ∀ (ε 𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ExpAvgGen_W1iv (baFMz sz z) CM

/-- **Target 3, `baExpAvgGen_W1fam`** (rows 9 + 14 with (iv); probe `T2502c_ba_W1fam` ported to the merged text). -/
def T2510_W1famBA (d : ℕ) : Prop :=
  ExpAvgGen_W1fam d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)

/-- **Target 3, `baImproveCoregL`** (16a at BA, `stImproveCoregL_of` with row 3). -/
def T2510_CoreBA (d : ℕ) : Prop :=
  STImproveCoregL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)

/-- **Target 4, `baExpAvgUgL_of_tl1`** (row 21: 16c per flow at BA, TL1 on `[s,t]`, the eventual `hK1` inside, F1). -/
def T2510_ExpAvgUBA (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔠 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      STStep2CoregL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t → STLKUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t →
      (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) → BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u) →
        STExpAvgUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t

/-- Shape (not binding; private generic twin in file 1): `LWAvgLawgL_of_STAvgUgL_at` (`Step6KitGen:139`) with the eventual `hK1` of row 19. -/
def T2510_LWAvgEv {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) : Prop :=
  sz.SizeTendsto → ∀ s t u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) → (∀ n, 0 ≤ s n) → (∀ n, t n < 1) →
    (∀ᶠ n in atTop, ∀ (τ : ℝ) (a : Zd d (sz.L n)), 0 ≤ τ → τ < 1 → C.K n τ (fun _ : Fin 1 => true) (fun _ => a) = C.m n) →
    STAvgUgL C μ s t → LWAvgLawgL C μ u

/-- **Targets 7, 8** (the merged pins at the BA tuple from the merged producers; conjuncts in the order of the ticket's names). -/
def T2510_IngBA (d : ℕ) : Prop :=
  STExpLKLKHigL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) ∧
  STExpDriftLogL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) ∧
  STExpDriftDecaygL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) ∧
  STExpWardIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) ∧
  STExpWardIgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) ∧
  STExpIniIgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) ∧
  STExpIntIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) ∧
  STExpDuhamelZgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) ∧
  STExpDuhamelQgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)

/-- **Target 9, `baStep6RegIII_of_pin`**: regime (iii) at BA from the one T2508-proved pin (merged type). -/
def T2510_RegIIIOfPin (d : ℕ) : Prop :=
  STExpIntIIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) →
    T2510_Step6BA d STReg5III

/-- **Target 9, `baStep6RegIV_of_pin`**: regime (iv). -/
def T2510_RegIVOfPin (d : ℕ) : Prop :=
  STExpIntIVgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) →
    T2510_Step6BA d STReg5IV

/-- **Target 9, `baStep6RegII_of_pin`**: regime (ii) (the Ward decomposition is the one T2508 pin; `STExpIntIIgL` is target 7). -/
def T2510_RegIIOfPin (d : ℕ) : Prop :=
  STExpWardIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) →
    T2510_Step6BA d STReg5II

/-- **Target 14 (row b), `baStep6RegIII/I/II/IV_holds`**: `BAStep6R d R` for the four regimes, every `d`; consumer V2a's 1b.
Row b's inputs (T2508, unmerged): `stExpWardIIgL_of`, `stExpIntIIIgL_of`, `stExpIntIVgL_of` (`T2508-check:202`), `stExpIntIgL'_of`
(`:239`), `st6_caseI_coreg'` (`:129`), with the family texts `:157-199`. -/
def T2510_RowB : Prop :=
  ∀ d : ℕ, T2510_Step6BA d STReg5III ∧ T2510_Step6BA d STReg5I ∧ T2510_Step6BA d STReg5II ∧ T2510_Step6BA d STReg5IV

end RBM.BA

end
