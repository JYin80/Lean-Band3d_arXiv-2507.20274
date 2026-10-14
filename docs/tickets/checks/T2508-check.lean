/-
Release check for T2508 = V1s3′ (dispatcher V4, 2026-10-14; DECISIONS §330, §318 (2), §320 (3), §322 (2), §323 (2), §324, §329 (2); supervisor 0843 (new files,
V1L-C1, V1L-C2), 0342 Q2/Q3).  BA sub-stage V, rows 8–9: the band Step-6 files `Induction/ExpWardII`, `ExpIntEasy`, `ExpIntI`, `ExpIntIQ`, `QopDecay` (4,805
lines on `main` 4845a70f; cert no) over the carrier, NEW FILES: row a `Chain/ExpWardIIGen`, `ExpIntEasyGen`, `ExpIntIGen`; row b `Chain/QopDecayGen` →
`ExpIntIQGen`.  No band file is edited.  Part 1: merged names relied on (`main` 4845a70f; file:line by grep).  Part 2: Prop values `T2508_`.
Binding: `T2508_ExpIntQConclgL'`, `T2508_ExpIntIgL'` (the two public defs, twins of the band primed `STExpIntQConcl'`, `STExpIntI'`); the V1L-C1 shapes
`T2508_CaseICoreg'` (per-carrier regime-(i) core) and `T2508_Step6IAvgUgL` (the consumer's conclusion, average per flow on `[s,t]`).  Not binding (fixed at
the 1a): `T2508_Step6ICoreAvgUgL`, `T2508_Fam*`, `T2508_RowAOf`, `T2508_ConsumerPrem`, `T2508_ConsumerOf`, `T2508_QopDecayGenOf`, `T2508_RowBOf`.
V1L-C1: no text here reads `STImproveExpAvergL` or `st6_expAvgU_of_ping`.  Only imports, `#check`s and Prop-valued definitions; no proofs; not compiled by
the dispatcher.  Run: lake env lean docs/tickets/checks/T2508-check.lean
-/
import RBM3D.Induction.ExpWardII
import RBM3D.Induction.ExpIntEasy
import RBM3D.Induction.ExpIntI
import RBM3D.Induction.ExpIntIQ
import RBM3D.Induction.QopDecay
import RBM3D.Chain.Step6Gen
import RBM3D.Chain.Step6KitGen
import RBM3D.Chain.ExpAvgGen
import RBM3D.Chain.ExpDuhamelGen
import RBM3D.Chain.ExpEtermsAGen
import RBM3D.Chain.ExpEtermsBGen
import RBM3D.Chain.ExpIniIGen
import RBM3D.Chain.ExpWardIGen
import RBM3D.Chain.ExpIntIIGen
import RBM3D.Chain.Step5KerGen
import RBM3D.Chain.Step5CasesGen
import RBM3D.Chain.ZeroModeGen
import RBM3D.Chain.B45Gen
import RBM3D.Chain.Step34Gen
import RBM3D.Chain.CltFarUGen
import RBM3D.BA.Step5KerBA
import RBM3D.BA.Step5CasesBA
import RBM3D.BA.B45BA
import RBM3D.BA.CltFlowBA
import RBM3D.BA.KBound
import RBM3D.BA.EKPins
import RBM3D.BA.EKSum
import RBM3D.BA.SEforLnBA
import RBM3D.BA.TwistPins

/-! ## Part 1: merged names -/
-- the band files converted here (unchanged; `RBM.Gauss.Sizes`)
#check @RBM.Gauss.Sizes.expWII_slot0               -- ExpWardII:182 (`stWardII_identity`, `|E| < 2`; W-w)
#check @RBM.Gauss.Sizes.expWII_slot1               -- ExpWardII:223 (rotation of the 2-loop)
#check @RBM.Gauss.Sizes.STExpWardIIConcl_of_avgU   -- ExpWardII:364 (per-flow `hAvg : STExpAvgU … s t`, `:366`)
#check @RBM.Gauss.Sizes.stExpWardII_holds          -- ExpWardII:419 (read by Graph/LWExpTerm6:628)
#check @RBM.Gauss.Sizes.expIntEasy_kernel_seq      -- ExpIntEasy:355 (`stek_sumNdecay_holds`, row 5)
#check @RBM.Gauss.Sizes.stExpIntIII_holds          -- ExpIntEasy:610 (read by Graph/LWExpTerm6:632)
#check @RBM.Gauss.Sizes.stStep6IV_holds            -- ExpIntEasy:626 (global `stImproveExpAver_holds`, `:627`): band only, V1L-C1
#check @RBM.Gauss.Sizes.STExpIntQConcl'            -- ExpIntI:56
#check @RBM.Gauss.Sizes.STExpIntI'                 -- ExpIntI:71
#check @RBM.Gauss.Sizes.expIntI_kernel_unif        -- ExpIntI:253 (`(sum_res_2_NAL)`, `(sum_res_2)`, row 16)
#check @RBM.Gauss.Sizes.expIntI_same               -- ExpIntI:465 (first conjunct of `STExpIntI'`)
#check @RBM.Gauss.Sizes.ST_step6_caseI_of_pins''   -- ExpIntI:573 (global `hAvg : STImproveExpAver d`, `st6_expAvgU_of_pin` `:596`): V1L-C1
#check @RBM.Gauss.Sizes.stStep6I_of_LW             -- ExpIntIQ:1362 (read by Graph/LWExpTerm6:623): band only
#check @RBM.Gauss.Sizes.QopDecay_ThetaN_fastDecay  -- QopDecay:762 (W-q; read by QDriftB)
#check @RBM.Gauss.Sizes.QopDecay_STthetaOp_fastDecay -- QopDecay:883 (`STthetaOp`)
-- V1L-C1 / V1L-C2 (band global pin and the merged 16a–16c)
#check @RBM.Gauss.Sizes.st6_expAvgU_of_pin         -- Step6Kit:557
#check @RBM.BA.STImproveExpAvergL                  -- Step6Gen:316 (global; not read by a T2508 statement)
#check @RBM.BA.st6_expAvgU_of_ping                 -- Step6KitGen:338 (band re-derivations only)
#check @RBM.BA.stImproveCoregL_of                  -- ExpAvgGen:1365 (16a)
#check @RBM.BA.stImproveExpAvergL_of               -- ExpAvgGen:1407 (16b; band-type carriers)
#check @RBM.BA.stExpAvgUgL_of_core                 -- ExpAvgGen:1416 (16c: the per-flow average from 16a + W1 (iii) on `[s,t]`)
-- V1s1 (`Chain/Step6Gen`, `Chain/Step6KitGen`)
#check @RBM.BA.STIngR6gL                           -- Step6Gen:100
#check @RBM.BA.STExpAvgUgL                         -- Step6Gen:160 (the per-flow average)
#check @RBM.BA.STExpWardIIgL                       -- Step6Gen:351 (row a proves)
#check @RBM.BA.STExpIntIIIgL                       -- Step6Gen:356 (row a proves)
#check @RBM.BA.STExpWardII_iff_gL                  -- Step6Gen:603
#check @RBM.BA.STExpIntIII_of_gL                   -- Step6Gen:618
#check @RBM.BA.st6_caseI_coreg                     -- Step6KitGen:601 (unprimed core: `STExpIniIConclgL`, `STExpIntQConclgL` have no producer)
#check @RBM.BA.st6_caseIV_coreg                    -- Step6KitGen:520 (per-flow `hAvgU`; V1-BA's regime (iv))
-- V1s2′ (T2506, merged c9b3f490 + 4845a70f)
#check @RBM.BA.stExpIniIgL'_of                     -- ExpIniIGen:787
#check @RBM.BA.stExpWardIgL'_of                    -- ExpWardIGen:438
-- the merged generic layer read here
#check @RBM.BA.Step5KerGen_ThDecay                 -- Step5KerGen:188 (row 22; W-q)
#check @RBM.BA.Step5CasesGen_WardIdent             -- Step5CasesGen:187 (row 23; W-w)
#check @RBM.BA.B45Gen_Facts                        -- B45Gen:61 (row 19′: Ward class with rotation, `KerSums`, `thetaKer` row sums)
#check @RBM.BA.QopAlgebra_ThetaN_sumZerog          -- ZeroModeGen:462 (W-z)
#check @RBM.BA.STEKSumNdecaygL                     -- Step34Gen:529 (row 5)
#check @RBM.BA.STEKSumRes2NALgL                    -- Step34Gen:552 (row 16)
#check @RBM.BA.IniTermGen_CltFlow                  -- CltFarUGen:62 (row 9′; W-a)
-- BA discharges of the family table (read by V1-BA / U3-BA; never imported by the new files)
#check @RBM.BA.baStep5CasesGen_flowFacts           -- BA/SEforLnBA:152 (row 3)
#check @RBM.BA.baIniTermGen_cltFlow                -- BA/CltFlowBA:566 (row 9′)
#check @RBM.BA.baEKSumNdecay_holds                 -- BA/EKPins:218 (row 5)
#check @RBM.BA.baEKSumDecayNAL_holds               -- BA/EKSum:290 (row 16)
#check @RBM.BA.baKbound_holds                      -- BA/KBound:245 (row 17)
#check @RBM.BA.baB45Gen_facts                      -- BA/B45BA:205 (row 19′)
#check @RBM.BA.baStep5KerGen_thDecay               -- BA/Step5KerBA:132 (row 22)
#check @RBM.BA.baStep5CasesGen_wardIdent           -- BA/Step5CasesBA:128 (row 23)
#check @RBM.BA.BATwistAvgLaw                       -- BA/TwistPins:91 (TL1; row 21 via 16c, V1-BA; bridge `TwistPins_circ_term` `:440` is private)

/-! ## Part 2: Prop values -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ### Binding: the primed vocabulary (row a, `Chain/ExpIntIGen`; X1-C4: one text per pin) -/
/-- **Target 5, `STExpIntQConclgL'`** (band `STExpIntQConcl'`, `ExpIntI:56`): `STExpIntQConclgL` (`Step6Gen:280`) with `0 < Cq → 0 < c →`. -/
def T2508_ExpIntQConclgL' {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ (Cq c : ℝ), 0 < Cq → 0 < c → ∀ (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
    (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) Cq c (ϑ n)) → STExpDuhEqQgL C μ s t ϑ →
    ∀ F : ∀ n, STIdx2P sz STSigMixed s t n → ℝ, (∀ n p, 0 ≤ F n p) →
      PrecL sz μ (U := STIdx2P sz STSigMixed s t)
        (fun n p _ => ‖Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ)
          (STQop (d := d) (ϑ n) (s n) (fun b => STExpErrg C μ n (s n) p.2.1.1 b)) p.2.2‖)
        (fun n p _ => F n p) →
      PrecL sz μ (U := STIdx2P sz STSigMixed s t)
        (fun n p _ => ‖STQop (d := d) (ϑ n) (p.1 : ℝ)
          (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) p.2.2‖)
        (fun n p _ => F n p + STExpTarget sz n (p.1 : ℝ))

/-- **Target 5, `STExpIntIgL'`** (band `STExpIntI'`, `ExpIntI:71`): `STExpIntIgL` (`Step6Gen:375`) with the primed Ward premise and second conjunct. -/
def T2508_ExpIntIgL' (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngR6gL d STReg5I law Flow mk T0 (fun sz z s t =>
    STExpDuhEqgL (mk sz z) (law sz) s t → STExpDriftHiConclgL (mk sz z) (law sz) s t →
      STExpDriftDecayConclgL (mk sz z) (law sz) s t → STExpWardIConclgL' (mk sz z) (law sz) s t →
        STExpIntConclgL (mk sz z) (law sz) ∅ STSigSame s t ∧ T2508_ExpIntQConclgL' (mk sz z) (law sz) s t)

/-! ### Binding (V1L-C1): the regime-(i) core and the consumer's conclusion, average per flow -/
/-- **Target 7, `st6_caseI_coreg'`**: `st6_caseI_coreg` (`Step6KitGen:601`), primed Ward/initial/integrated inputs; `hAvgU : STExpAvgUgL` (BA: 16c). -/
def T2508_CaseICoreg' {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) : Prop :=
  ∀ {𝔠 𝔡 : ℝ}, 3 ≤ d → 0 < 𝔡 → sz.Admissible 𝔠 𝔡 → ∀ {s t : ℕ → ℝ}, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) →
    (∀ n, t n < 1) → STReg5I sz s t → STExpLKLKHiConclgL C μ s t → STExpEGtHiConclgL C μ s t →
    STExpDriftDecayConclgL C μ s t → STExpAvgUgL C μ s t → (STExpAvgUgL C μ s t → STExpWardIConclgL' C μ s t) →
    STExpIniIConclgL' C μ s t → STExpDuhEqgL C μ s t →
    (∀ (Cq c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
      (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) Cq c (ϑ n)) → STExpDuhEqQgL C μ s t ϑ) →
    (STExpDuhEqgL C μ s t → STExpDriftHiConclgL C μ s t → STExpDriftDecayConclgL C μ s t →
      STExpWardIConclgL' C μ s t → STExpIntConclgL C μ ∅ STSigSame s t ∧ T2508_ExpIntQConclgL' C μ s t) →
    STStep6ConclgL C μ s t

/-- **Target 8, conclusion of `ST_step6_caseI_of_pinsgL''`**: `STStep6IgL` (`Step6Gen:127`) with `STExpAvgUgL` on `[s,t]` on the `Concl` slot (V1L-C1). -/
def T2508_Step6IAvgUgL (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngR6gL d STReg5I law Flow mk T0 (fun sz z s t =>
    STExpAvgUgL (mk sz z) (law sz) s t → STStep6ConclgL (mk sz z) (law sz) s t)

/-! ### Not binding: the 16c-input form, family rows (numbers of the ticket's table), row shapes -/
/-- Target 8 corollary (16c inputs on the `Concl` slot): W1 (iii) at every `u ∈ [s,t]`; with `STImproveCoregL` (16a) as premise. -/
def T2508_Step6ICoreAvgUgL (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngR6gL d STReg5I law Flow mk T0 (fun sz z s t =>
    (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) → ExpAvgGen_W1iii (mk sz z) (law sz) u) →
      STStep6ConclgL (mk sz z) (law sz) s t)

/-- Rows 1–3, 9′, 17 (as `T2506_FamBase` without row 20). -/
def T2508_FamBase (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  (∀ sz : Sizes d, IsProbabilityMeasure (law sz)) ∧ Step2EventsGen_Flow d Flow T0 ∧ Step5CasesGen_FlowFacts d Flow mk T0 ∧
    IniTermGen_CltFlow d law Flow mk T0 ∧
    ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → STKboundgL (mk sz z) (law sz)

/-- T2502 row 9 (loops integrable; W-w), guarded. -/
def T2508_FamRep (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) : Prop :=
  ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
    ∃ (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (g' E : ℕ → ℝ), CltRepg (mk sz z) (law sz) H₀ g' E

/-- Row 19, the `𝒦^{(1)} = m_σ` conjunct (guarded, eventual; the form of T2506 Amend 1, `ExpEtermsBGen:724-727`). -/
def T2508_FamK1 (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) : Prop :=
  ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
    ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (τ : Bool) (x : Zd d (sz.L n)),
      (mk sz z).K n u (fun _ : Fin 1 => τ) (fun _ => x) = if τ then (mk sz z).m n else (starRingEnd ℂ) ((mk sz z).m n)

/-- Row 23 (W-w): the `(zYU1)` identity along every flow, guarded. -/
def T2508_FamWardIdent (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) : Prop :=
  ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → Step5CasesGen_WardIdent (mk sz z)

/-- Row 22 (W-q): the `Θ`-kernel decay at `gK`, `∃ C₆` after `(𝔡, κ)` (the form of T2498 row 9, `QEndB1Gen:941-942`). -/
def T2508_FamThDecay (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  ∀ 𝔡 : ℝ, 0 < 𝔡 → ∀ κ : ℝ, 0 < κ → ∃ C₆ : ℝ, 0 < C₆ ∧ ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ),
    Flow sz κ ε 𝔠 𝔡 z → Step5KerGen_ThDecay (mk sz z) (gK sz z) 𝔡⁻¹ C₆

/-- Row 5 (regimes (iii), (iv)): the kernel data at `gK`, `∃ κm` (the `hKer` of `ST_step6_caseIII_of_pinsgL`, `Step6KitGen:682-684`). -/
def T2508_FamKer5 (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (Ker : STEKKer d) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, 0 < κm ∧ ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
    (∀ n, κm ≤ ((mk sz z).m n).im) ∧ Ker sz (mk sz z) (gK sz z) κm ∧ ∀ᶠ n in atTop, 0 < gK sz z n ∧ gK sz z n ≤ 𝔡⁻¹

/-- Rows 6/16 with R1 (regime (i); W-b′, W-q): the `hKer` of `stExpIniIgL'_of` (`ExpIniIGen:794-796`) and `1 ≤ Aof`. -/
def T2508_FamKerR1 (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (Ker : STEKKer d) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Aof : ℝ → ℝ) : Prop :=
  (∀ κm : ℝ, 0 < κm → 1 ≤ Aof κm) ∧ ∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, 0 < κm ∧
    ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      (∀ n, κm ≤ ((mk sz z).m n).im) ∧ Ker sz (mk sz z) (gK sz z) κm ∧ (∀ᶠ n in atTop, 0 < gK sz z n ∧ gK sz z n ≤ 𝔡⁻¹) ∧
        ∀ n, 0 ≤ gK sz z n * sz.lam n ∧ gK sz z n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ Aof κm * gK sz z n ^ 2

/-- Row a, targets 2 and 4: the three merged pins of `Chain/Step6Gen` from the family rows. -/
def T2508_RowAOf (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (Ker : STEKKer d)
    (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  T2508_FamBase d law Flow mk T0 →
    (T2508_FamRep d law Flow mk → T2508_FamK1 d Flow mk → T2508_FamWardIdent d Flow mk → B45Gen_Facts d Flow mk →
      STExpWardIIgL d law Flow mk T0) ∧
    (STEKSumNdecaygL d law Ker → T2508_FamKer5 d Flow mk Ker gK →
      STExpIntIIIgL d law Flow mk T0 ∧ STExpIntIVgL d law Flow mk T0)

/-- Row a, target 8: the premises of the merged wrapper (`Step6KitGen:795-801`) with the primed pins; no `STImproveExpAvergL`. -/
def T2508_ConsumerPrem (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  (∀ sz, IsProbabilityMeasure (law sz)) ∧ Step5CasesGen_FlowFacts d Flow mk T0 ∧ (∀ sz z, Step2EventsGen_Rot3 (mk sz z)) ∧
    (∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (τ : ℝ) (a : Zd d (sz.L n)), 0 ≤ τ → τ < 1 →
      (mk sz z).K n τ (fun _ : Fin 1 => true) (fun _ => a) = (mk sz z).m n) ∧
    LWtermEXPG d law Flow mk T0 ∧ STExpDuhamelZgL d law Flow mk ∧ STExpDuhamelQgL d law Flow mk ∧
    STExpLKLKHigL d law Flow mk T0 ∧ STExpDriftDecaygL d law Flow mk T0 ∧ STExpWardIgL' d law Flow mk T0 ∧
    STExpIniIgL' d law Flow mk T0 ∧ T2508_ExpIntIgL' d law Flow mk T0

/-- Row a, target 8 (`ST_step6_caseI_of_pinsgL''`) and its corollary with 16a and the 16c inputs (`stExpAvgUgL_of_core`, `ExpAvgGen:1416`). -/
def T2508_ConsumerOf (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  (T2508_ConsumerPrem d law Flow mk T0 → T2508_Step6IAvgUgL d law Flow mk T0) ∧
    (T2508_ConsumerPrem d law Flow mk T0 → STImproveCoregL d law Flow mk T0 → T2508_Step6ICoreAvgUgL d law Flow mk T0)

/-- Row b, target 9 (W-q): `Θ^{(n)}` of the carrier propagates `(deccA0)` at `sz.lam`, from the class at `gK ≤ sz.lam`. -/
def T2508_QopDecayGenOf (d n : ℕ) : Prop :=
  3 ≤ d → ∀ (Λ K C₀ ε D C₆ : ℝ), 0 < Λ → 0 < ε → 0 < C₆ → ∃ W₀ : ℝ, 1 < W₀ ∧
    ∀ (sz : Sizes d) (C : FlowFM sz) (gK : ℕ → ℝ), Step5KerGen_ThDecay C gK Λ C₆ →
      ∀ k : ℕ, 0 < gK k → gK k ≤ Λ → gK k ≤ sz.lam k → W₀ ≤ ((sz.W k : ℕ) : ℝ) →
        ((sz.L k : ℕ) : ℝ) ^ d ≤ ((sz.W k : ℕ) : ℝ) ^ K →
        ∀ u : ℝ, 0 ≤ u → u < 1 → (1 - u)⁻¹ ≤ ((sz.W k : ℕ) : ℝ) ^ K →
        ∀ (σ : Fin n → Bool) (A : (Fin n → Zd d (sz.L k)) → ℂ), ‖A‖ ≤ ((sz.W k : ℕ) : ℝ) ^ C₀ →
          EKFastDecay (sz.lam k) u ((sz.W k : ℕ) : ℝ) ε D A →
          EKFastDecay (sz.lam k) u ((sz.W k : ℕ) : ℝ) (2 * ε) (D - (K + 1)) (Step2Gen_ThetaN C k σ u A)

/-- Row b, target 12: the primed integrated pin from the family rows. -/
def T2508_RowBOf (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (Ker : STEKKer d)
    (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (Aof : ℝ → ℝ) : Prop :=
  T2508_FamBase d law Flow mk T0 → T2508_FamKerR1 d Flow mk Ker gK Aof → T2508_FamThDecay d Flow mk gK →
    B45Gen_Facts d Flow mk → STEKSumRes2NALgL d law Ker → STEKSumRes2gL d law Ker → STExpDuhamelQgL d law Flow mk →
      T2508_ExpIntIgL' d law Flow mk T0

-- band reading: `T2508_ExpIntIgL'` at `(seqP, STFlow, bandFM ∘ STflowE, lemT)`; bridge `STExpIntI'_of_gL'` one way (D725), as `Step6Gen:645`.

end RBM.BA
