/-
Release check for T2506 = V1s2′ (dispatcher V4, 2026-10-14; DECISIONS §323; supervisor 0843: new files, V1L-C1, V1L-C2; 0342 Q2/Q3).
BA sub-stage V, rows 6–7: generic conversion over the carrier of the band Step-6 ingredient proofs `Induction/ExpEtermsA`, `ExpIniI`,
`ExpEtermsB`, `ExpWardI`, `ExpIntII` (4,409 lines on `main` de05a3b1; cert no), NEW FILES: row a `Chain/ExpEtermsAGen` →
`Chain/ExpEtermsBGen`; row b `Chain/ExpIniIGen`, `Chain/ExpWardIGen`, `Chain/ExpIntIIGen`.  No band file is edited (G1 by construction).
Part 1: merged names relied on (`main` de05a3b1; file:line checked by grep; not compiled by the dispatcher).  Part 2: Prop values `T2506_`.
Binding: `T2506_ExpIniIConclgL'`, `T2506_ExpIniIgL'`, `T2506_ExpWardIConclgL'`, `T2506_ExpWardIgL'` (the four public defs of T2506).
Not binding (fixed at the 1a): the family rows `T2506_Fam*`, the row shapes `T2506_RowAOf`, `T2506_RowBOf`, the band reading.
V1L-C1: no text here reads `STImproveExpAvergL` or `st6_expAvgU_of_ping`; the average input is `STExpAvgUgL` on `[s,t]`.
Only imports, `#check`s and Prop-valued definitions; no proofs.  Run: lake env lean docs/tickets/checks/T2506-check.lean
-/
import RBM3D.Induction.ExpEtermsA
import RBM3D.Induction.ExpIniI
import RBM3D.Induction.ExpEtermsB
import RBM3D.Induction.ExpWardI
import RBM3D.Induction.ExpIntII
import RBM3D.Induction.ExpIntI
import RBM3D.Chain.Step6Gen
import RBM3D.Chain.Step6KitGen
import RBM3D.Chain.KDecayGen
import RBM3D.Chain.DecayGen
import RBM3D.Chain.SEforLnGen2
import RBM3D.Chain.CltFarUGen
import RBM3D.Chain.ZeroModeGen
import RBM3D.Chain.B45Gen
import RBM3D.Chain.Step2IterGen
import RBM3D.Chain.Step2Kern
import RBM3D.BA.CltFlowBA
import RBM3D.BA.SEforLnBA
import RBM3D.BA.KBound
import RBM3D.BA.DecayLoopBA
import RBM3D.BA.EKSum
import RBM3D.BA.Step5KerBA

/-! ## Part 1: merged names -/

-- the band files converted here (unchanged; `RBM.Gauss.Sizes`)
#check @RBM.Gauss.Sizes.STExpLKLKHiConcl_of_LKU  -- ExpEtermsA:594
#check @RBM.Gauss.Sizes.stExpLKLKHi_holds        -- ExpEtermsA:607 (read by Graph/LWExpTerm6:627)
#check @RBM.Gauss.Sizes.expLK_expect             -- ExpEtermsA:492 (`≺ → 𝔼`, W-a)
#check @RBM.Gauss.Sizes.expIniI_same             -- ExpIniI:646 (`(sum_res_2_NAL)`, ratio ≤ 2 at `:706`; W-b)
#check @RBM.Gauss.Sizes.expIniI_mixed            -- ExpIniI:892 (`(sum_res_2)`)
#check @RBM.Gauss.Sizes.STExpIniIConcl'          -- ExpIniI:1089
#check @RBM.Gauss.Sizes.STExpIniI'               -- ExpIniI:1102
#check @RBM.Gauss.Sizes.stExpIniI'_holds         -- ExpIniI:1106
#check @RBM.Gauss.Sizes.ST_step6_caseI_of_pins'  -- ExpIniI:1127 (global `hAvg : STImproveExpAver d`, `:1150`): band only, V1L-C1
#check @RBM.Gauss.Sizes.expDr_EGtK_prec          -- ExpEtermsB:723 (per-flow `hAvg : STExpAvgU … s t`, `:725`)
#check @RBM.Gauss.Sizes.STExpDriftLoConcl_of_LKU -- ExpEtermsB:818
#check @RBM.Gauss.Sizes.stExpDriftLo_holds       -- ExpEtermsB:901
#check @RBM.Gauss.Sizes.STExpDriftDecayConcl_of_GdecayW -- ExpEtermsB:968 (W-d)
#check @RBM.Gauss.Sizes.stExpDriftDecay_holds    -- ExpEtermsB:1049
#check @RBM.Gauss.Sizes.expWI_Psum_eq            -- ExpWardI:120 (`|E| < 2`, `mSigma`; W-c)
#check @RBM.Gauss.Sizes.STExpWardIConcl'         -- ExpWardI:321
#check @RBM.Gauss.Sizes.STExpWardI'              -- ExpWardI:339
#check @RBM.Gauss.Sizes.expWI_core               -- ExpWardI:411 (per-flow `STExpAvgU`)
#check @RBM.Gauss.Sizes.stExpWardI_holds         -- ExpWardI:441
#check @RBM.Gauss.Sizes.stExpWardI'_holds        -- ExpWardI:448
#check @RBM.Gauss.Sizes.expIntII_drift_integral_le -- ExpIntII:202 (`Ugen`; generic twin read by V1s3′)
#check @RBM.Gauss.Sizes.expIntII_kernel_unif     -- ExpIntII:393 (`(sum_res_Ndecay_nonzero)`)
#check @RBM.Gauss.Sizes.STExpIntConcl_of_kernel  -- ExpIntII:472
#check @RBM.Gauss.Sizes.stExpIntII_holds         -- ExpIntII:553 (read by Graph/LWExpTerm6:628)
-- V1L-C1 / V1L-C2
#check @RBM.Gauss.Sizes.STImproveExpAver         -- Step6Pins:191
#check @RBM.Gauss.Sizes.st6_expAvgU_of_pin       -- Step6Kit:557
#check @RBM.Gauss.Sizes.ST_step6_caseI_of_pins'' -- ExpIntI:573 (V1s3′'s consumer; `st6_expAvgU_of_pin` at `:596`)
#check @RBM.Gauss.Sizes.expAvg_Bctl_ge           -- ExpAvg:604 (size level, reused by name)
#check @RBM.Gauss.Sizes.expAvg_eta_inv_le        -- ExpAvg:631 (band flow; re-derived privately from row 9′)
-- V1s1 (`Chain/Step6Gen`, `Chain/Step6KitGen`, d3351df4)
#check @RBM.BA.STExpErrg                         -- Step6Gen:40
#check @RBM.BA.STIngR6gL                         -- Step6Gen:100
#check @RBM.BA.STExpAvgUgL                       -- Step6Gen:160 (the per-flow average)
#check @RBM.BA.STExpWardIConclgL                 -- Step6Gen:244
#check @RBM.BA.STExpIniIConclgL                  -- Step6Gen:294 (unprimed; finding T2223a)
#check @RBM.BA.STImproveExpAvergL                -- Step6Gen:316 (global; not read here)
#check @RBM.BA.STExpLKLKHigL                     -- Step6Gen:333 (row a proves)
#check @RBM.BA.STExpDriftLogL                    -- Step6Gen:337 (row a proves)
#check @RBM.BA.STExpDriftDecaygL                 -- Step6Gen:342 (row a proves)
#check @RBM.BA.STExpWardIgL                      -- Step6Gen:346 (row b proves)
#check @RBM.BA.STExpIntIIgL                      -- Step6Gen:368 (row b proves)
#check @RBM.BA.STExpIniIgL                       -- Step6Gen:382 (stays owed; superseded by the primed twin)
#check @RBM.BA.Step6Gen_ingR6_iff_congr          -- Step6Gen:505 (pattern of the primed bridges)
#check @RBM.BA.st6_expAvgU_of_ping               -- Step6KitGen:338 (global pin; not read here)
-- the merged generic layer read here
#check @RBM.BA.Step2Gen_ThetaN                   -- Step2Gen:197
#check @RBM.BA.Step2Gen_UN                       -- Step2Gen:202
#check @RBM.BA.STEGtg                            -- Step2Gen:455
#check @RBM.BA.STELKLKg                          -- Step5Gen:74
#check @RBM.BA.STEKSumRes2NALgL                  -- Step34Gen:552 (row 16)
#check @RBM.BA.STEKSumRes2gL                     -- Step34Gen:563 (row 16)
#check @RBM.BA.STEKNonzerogL                     -- Step34Gen:575 (row 6)
#check @RBM.BA.stKbound_timeIccgL                -- KDecayGen:92 (W-a)
#check @RBM.BA.stDecayLoopUgL_of_step2           -- DecayGen:583 (row 18)
#check @RBM.BA.stEtermDecaygL                    -- SEforLnGen2:865 (W-d: `Step2Mat` level)
#check @RBM.BA.IniTermGen_CltFlow                -- CltFarUGen:62 (row 9′)
#check @RBM.BA.ZeroModeGen_WardCls               -- ZeroModeGen:289 (row 19)
#check @RBM.BA.B45_ward_fing                     -- B45Gen:117 (W-c)
#check @RBM.BA.Step2IterGen_OneLoop              -- Step2IterGen:81 (first conjunct: row 19)
-- BA discharges of the family table (read by V1-BA / U3-BA; never imported by the new files)
#check @RBM.BA.baStep5CasesGen_flowFacts         -- BA/SEforLnBA:152 (row 3)
#check @RBM.BA.baIniTermGen_cltFlow              -- BA/CltFlowBA:566 (row 9′)
#check @RBM.BA.baEKSumDecayNAL_holds             -- BA/EKSum:290 (row 16, U3-BA (a))
#check @RBM.BA.baEKSumDecay2_holds               -- BA/EKSum:1772 (row 16, U3-BA (a))
#check @RBM.BA.Step2Kern_UN_BA                   -- Chain/Step2Kern:124
#check @RBM.BA.baIniTermGen_kerFacts             -- BA/Step5KerBA:161 (R1 conjunct, rows 6, 16)
#check @RBM.BA.baKbound_holds                    -- BA/KBound:245 (row 17)
#check @RBM.BA.baDecayLoopU_of                   -- BA/DecayLoopBA:60 (row 18)
#check @RBM.BA.baEtermDecaygL                    -- BA/SEforLnBA:271 (row 18, W-d)
#check @RBM.BA.baZeroModeGen_wardCls             -- BA/SEforLnBA:66 (row 19)
#check @RBM.BA.baKsol_oneLoop                    -- BA/SEforLnBA:113 (row 19)
#check @RBM.BA.baSEforLnGen_facts                -- BA/SEforLnBA:163 (row 20)

/-! ## Part 2: Prop values -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ### Binding: the primed vocabulary (row b; X1-C4: one text per pin) -/

/-- **Target 6, `STExpIniIConclgL'`** (band `STExpIniIConcl'`, `ExpIniI:1089`): `STExpIniIConclgL` (`Step6Gen:294`) with `0 < Cq → 0 < c →`. -/
def T2506_ExpIniIConclgL' {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := STIdx2P sz STSigSame s t)
    (fun n p _ => ‖Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ) (fun b => STExpErrg C μ n (s n) p.2.1.1 b) p.2.2‖)
    (fun n p _ => STExpTarget sz n (p.1 : ℝ)) ∧
  ∀ (Cq c : ℝ), 0 < Cq → 0 < c → ∀ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ,
    (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) Cq c (ϑ n)) →
    PrecL sz μ (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ)
        (STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C μ n (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => STExpTarget sz n (p.1 : ℝ))

/-- **Target 6, `STExpIniIgL'`** (band `STExpIniI'`, `ExpIniI:1102`) over the carrier tuple. -/
def T2506_ExpIniIgL' (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngR6gL d STReg5I law Flow mk T0 (fun sz z s t => T2506_ExpIniIConclgL' (mk sz z) (law sz) s t)

/-- **Target 9, `STExpWardIConclgL'`** (band `STExpWardIConcl'`, `ExpWardI:321`): `STExpWardIConclgL` (`Step6Gen:244`) with `0 < Cq → 0 < c →`. -/
def T2506_ExpWardIConclgL' {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ (Cq c : ℝ), 0 < Cq → 0 < c → ∀ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ,
    (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) Cq c (ϑ n)) →
    PrecL sz μ (U := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (fun n q _ => ‖STPsum (d := d) (fun b => STExpErrg C μ n (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) *
        ϑ n (q.1 : ℝ) q.2.2‖)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ 3) ∧
    PrecL sz μ (U := fun n => TimeIcc s t n × {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (fun n q _ =>
        ‖STQop (d := d) (ϑ n) (q.1 : ℝ) (Step2Gen_ThetaN C n q.2.1.1 (q.1 : ℝ)
            (fun c' => STExpErrg C μ n (q.1 : ℝ) q.2.1.1 c')) q.2.2 -
          Step2Gen_ThetaN C n q.2.1.1 (q.1 : ℝ)
            (STQop (d := d) (ϑ n) (q.1 : ℝ) (fun c' => STExpErrg C μ n (q.1 : ℝ) q.2.1.1 c')) q.2.2‖ +
        ‖STPsum (d := d) (fun b => STExpErrg C μ n (q.1 : ℝ) q.2.1.1 b) (q.2.2 0) *
          deriv (fun τ => ϑ n τ q.2.2) (q.1 : ℝ)‖)
      (fun n q _ => (1 - (q.1 : ℝ))⁻¹ * (sz.Bctl n (q.1 : ℝ)) ^ 3)

/-- **Target 9, `STExpWardIgL'`** (band `STExpWardI'`, `ExpWardI:339`): the average input is per flow (`STExpAvgUgL` on `[s,t]`, V1L-C1). -/
def T2506_ExpWardIgL' (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngR6gL d STReg5I law Flow mk T0 (fun sz z s t =>
    STExpAvgUgL (mk sz z) (law sz) s t → T2506_ExpWardIConclgL' (mk sz z) (law sz) s t)

/-! ### Not binding: family rows (numbers of the ticket's table) -/

/-- Rows 1–3, 9′, 17, 20 (`IniTermGen_CltFlow` carries `CltRepg`, `κ' ≤ Im m`, `N^{-1+δ} ≤ 1 - T0`: W-a). -/
def T2506_FamBase (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  (∀ sz : Sizes d, IsProbabilityMeasure (law sz)) ∧ Step2EventsGen_Flow d Flow T0 ∧ Step5CasesGen_FlowFacts d Flow mk T0 ∧
    IniTermGen_CltFlow d law Flow mk T0 ∧
    ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → STKboundgL (mk sz z) (law sz) ∧
      (∀ (n : ℕ) (x : Zd d (sz.L n)), ∑ y : Zd d (sz.L n), ‖(mk sz z).S n x y‖ ≤ 1) ∧
      ∀ (n : ℕ) (y : Zd d (sz.L n)), ∑ x : Zd d (sz.L n), ‖(mk sz z).S n x y‖ ≤ 1

/-- Row 18 (form of `baDecayLoopU_of`, `BA/DecayLoopBA:60`, and of the E-term decays; W-d: the 1a fixes the labels). -/
def T2506_FamDecay (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) →
    (∀ n, s n ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
    (∀ Cd : ℝ, STGdecayWgL (mk sz z) (law sz) s t Cd → STDecayLoopUgL (mk sz z) (law sz) s t) ∧
    (STDecayLoopUgL (mk sz z) (law sz) s t → ∀ σ : Fin 2 → Bool,
      STEKDecaygL (law sz) s t (fun n v ω a => STELKLKg (mk sz z) n (v : ℝ) σ a ω) ∧
      STEKDecaygL (law sz) s t (fun n v ω a => STEGtg (mk sz z) n (v : ℝ) σ a ω))

/-- Row 19 (W-c): the Ward class and `𝒦^{(1)}_σ = m_σ` (first conjunct of `Step2IterGen_OneLoop`), guarded (T2502 audit O1). -/
def T2506_FamWard (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) : Prop :=
  ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ZeroModeGen_WardCls sz (mk sz z) ∧
    ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)),
      (mk sz z).K n u (fun _ : Fin 1 => σ) (fun _ => a) = if σ then (mk sz z).m n else (starRingEnd ℂ) ((mk sz z).m n)

/-- Rows 6, 16 (kernel data, W-b): the class `Ker` at the coupling `gK`, the window and R1 in the A-form (`Aof κ`, as `STEKNonzerogL`). -/
def T2506_FamKerData (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (Ker : STEKKer d) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Aof : ℝ → ℝ) : Prop :=
  (∀ κ : ℝ, 0 < κ → 1 ≤ Aof κ) ∧ ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
    Ker sz (mk sz z) (gK sz z) κ ∧ (∀ᶠ n in atTop, 0 < gK sz z n ∧ gK sz z n ≤ 𝔡⁻¹) ∧
      ∀ n, 0 ≤ gK sz z n * sz.lam n ∧ gK sz z n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ Aof κ * gK sz z n ^ 2

/-! ### Not binding: the row shapes (targets 2, 4, 5; 8, 11, 13) -/

/-- Row a: the three merged pins of `Chain/Step6Gen` from the family rows. -/
def T2506_RowAOf (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  T2506_FamBase d law Flow mk T0 →
    STExpLKLKHigL d law Flow mk T0 ∧ STExpDriftLogL d law Flow mk T0 ∧
      (T2506_FamDecay d law Flow mk T0 → STExpDriftDecaygL d law Flow mk T0)

/-- Row b: the primed initial term, the Ward pins (unprimed and primed) and the regime-(ii) integrated estimate. -/
def T2506_RowBOf (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (Ker : STEKKer d)
    (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (Aof : ℝ → ℝ) : Prop :=
  T2506_FamBase d law Flow mk T0 → T2506_FamKerData d Flow mk Ker gK Aof →
    (STEKSumRes2NALgL d law Ker → STEKSumRes2gL d law Ker → T2506_ExpIniIgL' d law Flow mk T0) ∧
    (T2506_FamWard d Flow mk → STExpWardIgL d law Flow mk T0 ∧ T2506_ExpWardIgL' d law Flow mk T0) ∧
    (STEKNonzerogL d law Ker Aof → STExpIntIIgL d law Flow mk T0)

/-- The band reading of the primed initial-term pin: `STExpIniI' d` is this (bridge `STExpIniI'_iff_gL'`, row b). -/
def T2506_ExpIniIgL'_band (d : ℕ) : Prop :=
  T2506_ExpIniIgL' d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))

end RBM.BA
