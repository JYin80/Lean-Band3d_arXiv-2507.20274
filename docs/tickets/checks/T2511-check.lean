/-
Release check for T2511 (dispatcher V4, 2026-10-15; DECISIONS §334; supervisor 2026-10-14-1743 V2O-C1, O2;
design `docs/reports/T2503-design.md:131, 136-143`; not compiled by the dispatcher).  V V2a 1b: the BA main induction per regime
in family form with TL2, concluding the merged def `BAMainIndFamTL d R` (`BA/MainIndOutBA.lean:60`, T2504), never restated.
Row a (`t/T2511`): targets 1-10: K2, the family Step-1 call, the private single-flow step and wrapper, the generic step in slot
form (Step 6 = any slot `Concl6` of the merged `STIngR6gL`, with the TL bridge), the four regime theorems with T2509's Steps 3-4,
and the four closed regimes with T2510's `baStep6Reg*_holds` (`BAStep6R` read by name, no second text).  Row b (`t/T2511b`):
the terminal, sole writer under V2O-C1; T2512's `baMainIndFamTL_of_regimes` is unmerged and named in prose only.
Part 1: merged names (`main` dd605b0c).  Part 2: pins `T2511_*`, binding unless marked; `T2511_S3` … `T2511_Bridge6` are
check-local abbreviations of merged texts.  Statements only.  Run: lake env lean docs/tickets/checks/T2511-check.lean
-/
import RBM3D.BA.MainIndOutBA
import RBM3D.BA.Step1Prime
import RBM3D.BA.TwistLoop
import RBM3D.BA.TwistStep2
import RBM3D.BA.DecayLoopBA
import RBM3D.BA.Step5CasesBA
import RBM3D.BA.Step5IIITargets
import RBM3D.BA.Step34BA
import RBM3D.BA.Step6PinsBA
import RBM3D.BA.Step6BA
import RBM3D.Chain.Step34Gen
import RBM3D.Chain.Step6Gen
import RBM3D.Graph.BATermHoldsB
import RBM3D.Induction.MainIndRegimes

set_option linter.style.longLine false

/-! ## Part 1: merged names -/
-- V3 (T2504): the family step (T2503 D1 text), TL2 tail-locality, a member as a flow, the terminal plug-ins
#check @RBM.BA.BAMainIndFamTL                     -- BA/MainIndOutBA:60
#check @RBM.BA.BATwistLoopLaw_congr               -- MainIndOutBA:79
#check @RBM.BA.baFamMember_flow                   -- MainIndOutBA:90
#check @RBM.BA.baMLOutTL_of_famStep               -- MainIndOutBA:315 (target 11)
#check @RBM.BA.unMLOutBA_of_famStep               -- MainIndOutBA:326 (target 11)
-- TL pins and producers (`BA/TwistPins.lean`; single-flow `BAMainIndTL` :169 is off the route, not read)
#check @RBM.BA.BATwistAvgLaw                      -- TwistPins:91
#check @RBM.BA.BATwistLoopLaw                     -- TwistPins:95
#check @RBM.BA.BATwistLoopStep                    -- TwistPins:160
#check @RBM.BA.BAMLOutTL                          -- TwistPins:178
#check @RBM.BA.TwistStep2_tl1                     -- BA/TwistStep2:1137
#check @RBM.BA.baTwistLoopStep_caseI              -- BA/TwistLoop:705
#check @RBM.BA.baTwistLoopStep_caseII             -- TwistLoop:709
-- the family, the members, Step 1 (K2 route `BAFlowMember_holds` `Step1Fam:624`, `STKboundgL_congr` `:247`: prose)
#check @RBM.BA.BAFamZ                             -- BA/Step1Trivial:42
#check @RBM.BA.BAFamZ_main                        -- Step1Trivial:56
#check @RBM.BA.BAStep1                            -- BA/Step1Fam:361
#check @RBM.BA.baStep1_holds'                     -- BA/Step1Prime:892 (`2 ≤ d`)
#check @RBM.BA.STLKgL_congr                       -- Step1Fam:205 (the ten `_congr` of `:205-260`, `STStep1Loop/WeakgL` included)
#check @RBM.BA.BAWinBulk                          -- BA/CouplingWindow:799
-- K12; Step 2 at exact type (0947 O4; T7-BA `baDecayLoopU_of` `DecayLoopBA:60` inside)
#check @RBM.BA.baKbound_holds                     -- BA/KBound:245
#check @RBM.BA.baKward_holds                      -- KBound:302
#check @RBM.BA.baStep2Decay_holds                 -- BA/DecayLoopBA:114
#check @RBM.BA.baLWterm_holds                     -- Graph/BATermHolds:706
#check @RBM.BA.baLWtermExp_holds                  -- BATermHoldsB:865
-- Steps 3-6 over the carrier tuple (endpoint readings, `twSteps`, K2 internals: ticket prose with file:line)
#check @RBM.BA.STStep3RgL                         -- Chain/Step34Gen:347
#check @RBM.BA.STStep4RgL                         -- Step34Gen:359
-- T2509 (U3-BA (b), merged beefb80b): Steps 3-4 at the BA tuple, read by name in 7-9 (§331 (2): `R34 = R` for (iii), (i))
#check @RBM.BA.baStep3RegIII_holds                -- BA/Step34BA:188
#check @RBM.BA.baStep3RegI_holds                  -- Step34BA:197
#check @RBM.BA.baStep3II_holds                    -- Step34BA:206
#check @RBM.BA.baStep4II_holds                    -- Step34BA:223
#check @RBM.BA.baStep4RegIII_holds                -- Step34BA:232
#check @RBM.BA.baStep4RegI_holds                  -- Step34BA:238
#check @RBM.BA.STStep5ConclgL                     -- Chain/Step5Gen:62
#check @RBM.BA.STStep5RgL                         -- Step5Gen:214
#check @RBM.BA.STStep5IIIgL                       -- Step5Gen:228 (Q4: the explicit hypothesis at general `d`)
#check @RBM.BA.baStep5I_holds                     -- BA/Step5CasesBA:248
#check @RBM.BA.baStep5II_holds                    -- Step5CasesBA:254
#check @RBM.BA.baStep5IV_holds                    -- Step5CasesBA:260
#check @RBM.BA.baStep5III_holds                   -- BA/Step5IIITargets:57 (`d = 3`)
#check @RBM.BA.STIngR6gL                          -- Chain/Step6Gen:100
#check @RBM.BA.STStep6ConclgL                     -- Step6Gen:93
-- T2510 (V1-BA, merged dc358686 / dd605b0c): Step 6 at the BA tuple, read by name in target 10 only
#check @RBM.BA.BAStep6R                           -- BA/Step6PinsBA:59 (= `STIngR6gL` at the TL slot; never restated)
#check @RBM.BA.baStep6RegIII_holds                -- BA/Step6BA:148
#check @RBM.BA.baStep6RegI_holds                  -- Step6BA:151
#check @RBM.BA.baStep6RegII_holds                 -- Step6BA:154
#check @RBM.BA.baStep6RegIV_holds                 -- Step6BA:157
-- regimes and cases; the band proof model
#check @RBM.Gauss.Sizes.ST_mainIndR_of_steps      -- Induction/MainIndRegimes:165
#check @RBM.Gauss.Sizes.st_caseI_of_reg5III       -- MainIndRegimes:125
#check @RBM.Gauss.Sizes.st_caseI_of_reg5I         -- MainIndRegimes:137
#check @RBM.Gauss.Sizes.st_caseII_of_reg5II       -- MainIndRegimes:141
#check @RBM.Gauss.Sizes.st_caseII_of_reg5IV       -- MainIndRegimes:145 (`2 ≤ d`)
#check @RBM.Gauss.Sizes.st5_conStInd_mono         -- Induction/Step5Kit:101

open MeasureTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## Part 2: pins -/

/-! ### Check-local abbreviations of merged texts at the BA tuple -/

/-- Steps 3 and 4 in regime `R` at the BA tuple (the spelling of T2509's statements, `BA/Step34BA:189-240`); hypotheses of target 6 only. -/
def T2511_S3 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  STStep3RgL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)
def T2511_S4 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  STStep4RgL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)
/-- Step 5 in regime `R` at the BA tuple (probe `T2503_Step5BA`, `t/T2503:RBM3D/Probe/T2503Pins.lean:300`). -/
def T2511_S5 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  STStep5RgL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)
/-- Step 6 in regime `R` with an arbitrary conclusion slot `Concl6` (the merged `STIngR6gL`; generic target 6).  `BAStep6R d R`
(`Step6PinsBA:59`) is this at the TL slot, so target 10 passes `baStep6Reg*_holds` by unfolding: no second text of `BAStep6R` (X1-C4). -/
def T2511_S6In (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Concl6 : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  STIngR6gL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) Concl6
/-- TL1 and TL2 at every `u ∈ [s, t]` along the carrier (what V2a supplies: `TwistStep2_tl1`, `baTwistLoopStep_caseI/II`). -/
def T2511_TLOn {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) : Prop :=
  ∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
    BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u ∧ BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u
/-- The Step-6 bridge: TL on `[s, t]` and the slot give `(Eq:Gtlp_exp_flow)` on `[s, t]` (T2510's slot: `fun _ _ _ _ h c => c h`). -/
def T2511_Bridge6 (d : ℕ) (Concl6 : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  ∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ), T2511_TLOn sz z s t → Concl6 sz z s t →
    STStep6ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t

/-! ### Row a -/

/-- **Target 1, `baKboundMember_holds`** (K2; probe `T2503_k2Member`, `:103-109`; `T2503-check:224-229`). -/
def T2511_K2Member (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
      ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
      ∀ s : ℕ → ℝ, (∀ n, 0 ≤ s n) → ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ s z' →
        STKboundgL (baFMz sz z') (Sizes.seqP (sz.withLam 0))

/-- **Target 2, `baStep1Fam_call`** (probe `T2503_famStep1Call`, `:110-114`; `T2503-check:207-220`): `baStep1_holds'` at exact type. -/
def T2511_FamStep1Call (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 1 / 100 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
      ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ BAflowT0 sz z n) → (∀ n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        (∀ z' : ℕ → ℂ, BAFamZ sz z c₁ s z' →
          let C := baFMz sz z'; let μ := Sizes.seqP (sz.withLam 0)
          STLKgL C μ s ∧ STDecaygL C μ s ∧ STDecayStronggL C μ s ∧ STLocalMaxgL C μ s ∧ STExp2gL C μ s ∧ BATwistLoopLaw C μ s) →
        sz.STConStInd 𝔠d s t →
        ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ t z' →
          STStep1LoopgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s t ∧ STStep1WeakgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s t

/-- **Target 3, private def `MainIndFamTL_S1`** (T2503 D1 (b) `BAMainIndS1TL`, `T2503-check:183-193`; private: no later row reads it). -/
def T2511_S1 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ BAflowT0 sz z n) → (∀ n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) → R sz s t →
        let C := baFMz sz z; let μ := Sizes.seqP (sz.withLam 0)
        (STLKgL C μ s ∧ STDecaygL C μ s ∧ STDecayStronggL C μ s ∧ STLocalMaxgL C μ s ∧ STExp2gL C μ s ∧ BATwistLoopLaw C μ s) →
        sz.STConStInd 𝔠d s t → STStep1LoopgL C μ s t → STStep1WeakgL C μ s t →
          STLKgL C μ t ∧ STLmaxgL C μ t ∧ STDecaygL C μ t ∧ STExp2gL C μ t ∧ STLocalEntrygL C μ t ∧
            STDecayStronggL C μ t ∧ BATwistLoopLaw C μ t

/-- **Target 4, private `MainIndFamTL_famOfS1`** (probe `T2503_famOfS1`, `:124-139`, with V3's `baFamMember_flow`, `BATwistLoopLaw_congr`). -/
def T2511_FamOfS1 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  T2511_S1 d R → BAMainIndFamTL d R

/-- The frame of targets 5, 6: regime `R`, Steps 3-4 regime `R34 ⊇ R`, TL2-step case `Rtl ⊇ R`, Steps 3-6 at the BA tuple. -/
def T2511_StepsTo (d : ℕ) (R R34 Rtl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (Q : Prop) : Prop :=
  (3 ≤ d → ∀ (sz : Sizes d) (s t : ℕ → ℝ), R sz s t → R34 sz s t) →
  (3 ≤ d → ∀ (sz : Sizes d) (s t : ℕ → ℝ), R sz s t → Rtl sz s t) →
  BATwistLoopStep d Rtl → T2511_S3 d R34 → T2511_S4 d R34 → T2511_S5 d R →
  ∀ Concl6 : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop, T2511_S6In d R Concl6 → T2511_Bridge6 d Concl6 → Q

/-- **Target 5, private `MainIndFamTL_s1OfSteps`**: the port of `ST_mainIndR_of_steps` (`MainIndRegimes:165-214`) at BA, with
K12, Step 2 (`baStep2Decay_holds` at `baLWterm_holds`, `baLWtermExp_holds`), TL1/TL2 on `[s, t]` fed to the bridge. -/
def T2511_S1OfSteps (d : ℕ) (R R34 Rtl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  T2511_StepsTo d R R34 Rtl (T2511_S1 d R)

/-- **Target 6, `baMainIndFamTL_of_steps`** (public, generic in `R, R34, Rtl`): 4 after 5. -/
def T2511_FamOfSteps (d : ℕ) (R R34 Rtl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  T2511_StepsTo d R R34 Rtl (BAMainIndFamTL d R)

/-- **Target 7, `baMainIndFamTL_III_of`**: regime (iii); Steps 3-4 `baStep3RegIII_holds`, `baStep4RegIII_holds` (§331 (2)); TL2 `STCaseI`; Step 5 (iii) the hypothesis (Q4). -/
def T2511_RegIIIOf (d : ℕ) : Prop :=
  STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) →
    ∀ Concl6 : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop, T2511_S6In d STReg5III Concl6 → T2511_Bridge6 d Concl6 →
      BAMainIndFamTL d STReg5III
/-- **Target 8, `baMainIndFamTL_I_of`**: regime (i); Steps 3-4 `baStep3RegI_holds`, `baStep4RegI_holds` (§331 (2)); TL2 `STCaseI`; Step 5 `baStep5I_holds`. -/
def T2511_RegIOf (d : ℕ) : Prop :=
  ∀ Concl6 : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop, T2511_S6In d STReg5I Concl6 → T2511_Bridge6 d Concl6 →
    BAMainIndFamTL d STReg5I
/-- **Target 9 (a), `baMainIndFamTL_II_of`**: regime (ii); Steps 3-4 `baStep3II_holds`, `baStep4II_holds`; TL2 `STCaseII`; Step 5 `baStep5II_holds`. -/
def T2511_RegIIOf (d : ℕ) : Prop :=
  ∀ Concl6 : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop, T2511_S6In d STReg5II Concl6 → T2511_Bridge6 d Concl6 →
    BAMainIndFamTL d STReg5II
/-- **Target 9 (b), `baMainIndFamTL_IV_of`**: regime (iv); as (ii) along `st_caseII_of_reg5IV`; Step 5 `baStep5IV_holds`. -/
def T2511_RegIVOf (d : ℕ) : Prop :=
  ∀ Concl6 : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop, T2511_S6In d STReg5IV Concl6 → T2511_Bridge6 d Concl6 →
    BAMainIndFamTL d STReg5IV

/-! ### Row a, file 2: the closed regimes (T2510 names) -/

/-- **Target 10, `baMainIndFamTL_III`, `baMainIndFamTL_III_three`, `baMainIndFamTL_I`, `_II`, `_IV`**: 7-9 with `baStep6Reg*_holds` and the
bridge `fun _ _ _ _ h c => c h`; general `d` ((iii) with the Q4 hypothesis), unconditional at `d = 3` through `baStep5III_holds`. -/
def T2511_Closed : Prop :=
  (∀ d : ℕ, STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) → BAMainIndFamTL d STReg5III) ∧ BAMainIndFamTL 3 STReg5III ∧
    (∀ d : ℕ, BAMainIndFamTL d STReg5I) ∧ (∀ d : ℕ, BAMainIndFamTL d STReg5II) ∧ (∀ d : ℕ, BAMainIndFamTL d STReg5IV)

/-! ### Row b: the terminal (V2O-C1: T2511 row b is the sole writer; input T2512 `baMainIndFamTL_of_regimes`, prose only) -/

/-- **Target 11, `baMainIndFamTL_three`, `baMLOutTL_three`, `unMLOutBA_three`**: T2512's glue at 10's `d = 3` names, then
`baMLOutTL_of_famStep` (`MainIndOutBA:315`), `unMLOutBA_of_famStep` (`:326`); V closing (i). -/
def T2511_Terminal : Prop :=
  BAMainIndFamTL 3 STAny ∧ BAMLOutTL 3 ∧ Univ.UNMLOutBA 3

/-- **Target 12, `baMainIndFamTL_any`**: the general-`d` step at `STAny` under `STStep5IIIgL d` (0342 Q4; T2512 `T2512_AnyD` text). -/
def T2511_AnyD : Prop :=
  ∀ d : ℕ, STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) → BAMainIndFamTL d STAny

end RBM.BA

end
