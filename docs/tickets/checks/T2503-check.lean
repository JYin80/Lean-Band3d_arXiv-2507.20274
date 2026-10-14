/-
Release check for T2503 (dispatcher V4, 2026-10-14; DECISIONS §314).  V V2a design gate: 1a + probe, no 1b
(supervisor 2026-10-14-0342 V-F1, V-C1 steps 1-4 (binding), Q1 closing condition (v), Q4, Q5 (a)/(b), O2, O4;
REQ-2026-10-14-0330-Vopen, Interfaces / Q4 / Q5).  The single-flow step `BAMainIndTL` (`BA/TwistPins.lean:169`) cannot be fed
from the family Step 1 `BAStep1` (`BA/Step1Fam.lean:361`); the gate states the family step (V-C1 step 1), compiles the family
Step-1 call and the K2 per-member `STKboundgL` in the probe (step 2), checks the members (step 3) and prices the family chain
and the tail passage (step 4).
Part 1: merged names (`main` 5d4ea2ed), declaration lines from `grep` at drafting.
Part 2: pins (prefix `T2503_`).  Binding: `T2503_BAMainIndFamTL` (D1).  Proposed (D1 (b), not binding): `T2503_BAMainIndS1TL`,
`T2503_FamOfS1`.  The probe's statements (D2, D3; proved in the probe from merged names): `T2503_FamStep1Call`,
`T2503_K2Member`, `T2503_MemberFlow`, `T2503_TL2Congr`.  Shapes (not binding; D4 and the 1b table): `T2503_BAChainFamTL`,
`T2503_RegShape` and its four regime readings.
No `open`, no namespace: every name is fully qualified.  Statements only; no proof.
Run: lake env lean docs/tickets/checks/T2503-check.lean
-/
import RBM3D.BA.TwistChain
import RBM3D.BA.TwistLoop
import RBM3D.BA.TwistStep2
import RBM3D.BA.Step1Prime
import RBM3D.BA.Step1Fam
import RBM3D.BA.CouplingWindow
import RBM3D.BA.KBound
import RBM3D.BA.Step5IIITargets
import RBM3D.BA.DecayLoopBA
import RBM3D.Chain.Step5Gen
import RBM3D.Chain.Step34Gen
import RBM3D.Induction.MainIndRegimes
import RBM3D.Graph.BATermHoldsB

/-! ## Part 1: merged names (`main` 5d4ea2ed) -/

-- TL pins (`BA/TwistPins.lean`): TL2 `:95`, `twSteps` `:133`, frame `:146`, TL2 step `:160`, base `:164`,
-- the single-flow step `:169` (V-F1: off the route), output `:178`, chain pin `:185`
#check @RBM.BA.BATwistLoopLaw
#check @RBM.BA.twSteps
#check @RBM.BA.BATwFrame
#check @RBM.BA.BATwistLoopStep
#check @RBM.BA.BATwistLoopBase
#check @RBM.BA.BAMainIndTL
#check @RBM.BA.BAMLOutTL
#check @RBM.BA.BAChainTL
-- TL chain (`BA/TwistChain.lean`, 297 lines): base `:110`, chain `:240` (premise `BAMainIndTL d STAny`)
#check @RBM.BA.baTwistLoopBase_holds
#check @RBM.BA.baChainTL_holds
-- the family (`BA/Step1Trivial.lean`): `BAFamZ` `:42`, `BAflow_T0_bounds` `:47`, main flow `:56`, window `:61`
#check @RBM.BA.BAFamZ
#check @RBM.BA.BAflow_T0_bounds
#check @RBM.BA.BAFamZ_main
#check @RBM.BA.BAFamZ_lam0_window
-- (`BA/Step1Boot.lean`): finite modification `:133`, `Fam(t) ⊆ Fam(s)` `:173`, horizon `t ≤ t₀(z')` `:179`, tail `:185`
#check @RBM.BA.BAFlowMember
#check @RBM.BA.BAFamZ_mono
#check @RBM.BA.BAFamZ_horizon
#check @RBM.BA.PrecL_congr
-- (`BA/Step1Fam.lean`): closure `:158`, `mono_max` `:172`, `EvEq` `:197`, congruences `:205-260`, carrier `:273`,
-- `BAflowT0_congr` `:74`, Step 1 family pin `:361`, finite modification proved `:624`
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
#check @RBM.BA.STStep1LoopgL_congr
#check @RBM.BA.STStep1WeakgL_congr
#check @RBM.BA.baFMz_eqAt
#check @RBM.BA.BAflowT0_congr
#check @RBM.BA.BAStep1
#check @RBM.BA.BAFlowMember_holds
-- Step 1 at BA, `2 ≤ d` (`BA/Step1Prime.lean:892`)
#check @RBM.BA.baStep1_holds'
-- window (`BA/CouplingWindow.lean`): `:799`, `:807`, `:836`
#check @RBM.BA.BAWinBulk
#check @RBM.BA.BAWinBulk_of_dom_stmt
#check @RBM.BA.BAWinBulk_of_dom_holds
-- K2 inputs: `BAKbound` `BA/KBound.lean:196`, `:245`, `baKward_holds` `:302`; carrier pins `Chain/Carrier.lean:80-184`
#check @RBM.BA.BAKbound
#check @RBM.BA.baKbound_holds
#check @RBM.BA.baKward_holds
#check @RBM.BA.STKboundgL
#check @RBM.BA.STKwardgL
#check @RBM.BA.STLKgL
#check @RBM.BA.STLmaxgL
#check @RBM.BA.STDecaygL
#check @RBM.BA.STDecayStronggL
#check @RBM.BA.STLocalMaxgL
#check @RBM.BA.STLocalEntrygL
#check @RBM.BA.STExp2gL
#check @RBM.BA.STStep1LoopgL
#check @RBM.BA.STStep1WeakgL
-- base and chain (`Induction/MainIndBase.lean:45, 54, 58`; `Induction/MainIndChain.lean:43, 51, 80, 126, 148`);
-- flow data (`BA/FlowPins.lean:380, 389, 393, 408, 432`)
#check @RBM.BA.STConclgL
#check @RBM.BA.STG0M
#check @RBM.BA.STBaseG
#check @RBM.BA.STHorizonG
#check @RBM.BA.stChainTime
#check @RBM.BA.stChainSteps
#check @RBM.BA.STLocalMaxgL_of_STLocalEntrygL
#check @RBM.BA.stPosConclG_of_mainIndG
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAFlow
#check @RBM.BA.baFMz
#check @RBM.BA.STMainIndG
#check @RBM.BA.BAStep2
-- Step 2 at BA (`Graph/BATermHoldsB.lean:879`), its decay / LW inputs (`BA/DecayLoopBA.lean:114, 135, 140`;
-- `Graph/BATermHolds.lean:706`; `Graph/BATermHoldsB.lean:865`); TL1 / TL2 producers (`BA/TwistStep2.lean:1137`,
-- `BA/TwistLoop.lean:705, 709`)
#check @RBM.BA.baStep2_closed
#check @RBM.BA.baStep2Decay_holds
#check @RBM.BA.baSTLWB_of
#check @RBM.BA.baSTLWT_of
#check @RBM.BA.baLWterm_holds
#check @RBM.BA.baLWtermExp_holds
#check @RBM.BA.TwistStep2_tl1
#check @RBM.BA.baTwistLoopStep_caseI
#check @RBM.BA.baTwistLoopStep_caseII
-- Steps 3-4 per regime over a carrier (`Chain/Step34Gen.lean:347, 359`; U3-BA (b) = these at the BA tuple)
#check @RBM.BA.STStep3RgL
#check @RBM.BA.STStep4RgL
-- Step 5 (`Chain/Step5Gen.lean:214, 226-229`); case (iii) at BA, d = 3 only (`BA/Step5IIITargets.lean:57`); `baPin`
-- (`BA/LWPinsBA.lean:39`)
#check @RBM.BA.STStep5RgL
#check @RBM.BA.STStep5IgL
#check @RBM.BA.STStep5IIgL
#check @RBM.BA.STStep5IIIgL
#check @RBM.BA.STStep5IVgL
#check @RBM.BA.baStep5III_holds
#check @RBM.BA.baPin
-- regimes and the band models of the V2a 1b targets (`Induction/Step5Pins.lean:44, 48, 58, 63`;
-- `Induction/Step34Pins.lean:237, 241, 272`; `Induction/Defs.lean:168`; `Induction/MainIndRegimes.lean:64, 125-145, 165,
-- 217, 222, 227, 232`)
#check @RBM.Gauss.Sizes.STReg5I
#check @RBM.Gauss.Sizes.STReg5II
#check @RBM.Gauss.Sizes.STReg5III
#check @RBM.Gauss.Sizes.STReg5IV
#check @RBM.Gauss.Sizes.STCaseI
#check @RBM.Gauss.Sizes.STCaseII
#check @RBM.Gauss.Sizes.STAny
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STMainIndR
#check @RBM.Gauss.Sizes.st_caseI_of_reg5III
#check @RBM.Gauss.Sizes.st_caseI_of_reg5I
#check @RBM.Gauss.Sizes.st_caseII_of_reg5II
#check @RBM.Gauss.Sizes.st_caseII_of_reg5IV
#check @RBM.Gauss.Sizes.ST_mainIndR_of_steps
#check @RBM.Gauss.Sizes.ST_mainIndR_III_of_steps
#check @RBM.Gauss.Sizes.ST_mainIndR_I_of_steps
#check @RBM.Gauss.Sizes.ST_mainIndR_II_of_steps
#check @RBM.Gauss.Sizes.ST_mainIndR_IV_of_steps

/-! ## Part 2: pins -/

/-- **D1 (binding; V-C1 step 1): the family step** `BAMainIndFamTL d R`.  `BAMainIndTL` (`BA/TwistPins.lean:169`) with the
premises of `BAStep1` (`BA/Step1Fam.lean:361`: `∀ n, 0 < sz.lam n`, `∀ c₁ ∈ (0, 1/2]`, `BAWinBulk sz z c₁ κ`), the six
hypotheses at `s` for **every member** of `Fam(s)` and the seven conclusions at `t` for **every member** of `Fam(t)`
(`BAFamZ`, `BA/Step1Trivial.lean:42`); quantifier order as T2205's `BAMainInd` (`t/T2205:RBM3D/Probe/T2205Pins.lean:1715`)
with the TL2 conjunct.  `BAMLOutTL` is recovered at the main flow through `BAFamZ_main` (V-C1; Q1 (i) as amended). -/
def T2503_BAMainIndFamTL (d : ℕ) (R : ∀ {d : ℕ}, RBM.Gauss.Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
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

/-- **D1 (b) (proposed, not binding): the single-flow step with the Step-1 outputs given.**  `BAMainIndTL` plus the two
Step-1 conclusions `STStep1LoopgL`, `STStep1WeakgL` on `[s, t]` as hypotheses.  Each regime of V2a's 1b proves this per
flow (the successors of `ST_mainIndR_*_of_steps`, `Induction/MainIndRegimes.lean:217-232`, with `h1` removed); the family
enters once, through `T2503_FamOfS1`.  `BAMainIndTL d R → T2503_BAMainIndS1TL d R` is a weakening. -/
def T2503_BAMainIndS1TL (d : ℕ) (R : ∀ {d : ℕ}, RBM.Gauss.Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
    ∀ (𝔠 : ℝ) (sz : RBM.Gauss.Sizes d) (z : ℕ → ℂ), RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ RBM.BA.BAflowT0 sz z n) → (∀ n, s n < t n) →
        (∀ n, t n ≤ RBM.BA.BAflowT0 sz z n) → R sz s t →
        let C := RBM.BA.baFMz sz z; let μ := RBM.Gauss.Sizes.seqP (sz.withLam 0)
        (RBM.BA.STLKgL C μ s ∧ RBM.BA.STDecaygL C μ s ∧ RBM.BA.STDecayStronggL C μ s ∧ RBM.BA.STLocalMaxgL C μ s ∧
            RBM.BA.STExp2gL C μ s ∧ RBM.BA.BATwistLoopLaw C μ s) →
        sz.STConStInd 𝔠d s t → RBM.BA.STStep1LoopgL C μ s t → RBM.BA.STStep1WeakgL C μ s t →
          RBM.BA.STLKgL C μ t ∧ RBM.BA.STLmaxgL C μ t ∧ RBM.BA.STDecaygL C μ t ∧ RBM.BA.STExp2gL C μ t ∧
            RBM.BA.STLocalEntrygL C μ t ∧ RBM.BA.STDecayStronggL C μ t ∧ RBM.BA.BATwistLoopLaw C μ t

/-- **D1 (b), the wrapper** (proposed; generic in `R`): the family step from the single-flow step, through `baStep1_holds'`
(family Step 1 at the main flow), K2, `BAFlowMember_holds` (finite modification at `(κ', ε')`) and the congruences. -/
def T2503_FamOfS1 (d : ℕ) (R : ∀ {d : ℕ}, RBM.Gauss.Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  T2503_BAMainIndS1TL d R → T2503_BAMainIndFamTL d R

/-- The weakening (shape): the single-flow step gives the step with Step 1 given. -/
example (d : ℕ) (R : ∀ {d : ℕ}, RBM.Gauss.Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  RBM.BA.BAMainIndTL d R → T2503_BAMainIndS1TL d R

/-- **D2 (V-C1 step 2): the family Step-1 call.**  From the family hypothesis of `T2503_BAMainIndFamTL` (six conjuncts per
member of `Fam(s)`), the Step-1 pair for every member of `Fam(t)`: `baStep1_holds'` at `2 ≤ d`, applied at exact type, its
`STKboundgL` conjunct from `T2503_K2Member`.  Proved in the probe from merged names. -/
def T2503_FamStep1Call (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 1 / 100 →
    ∀ (𝔠 : ℝ) (sz : RBM.Gauss.Sizes d) (z : ℕ → ℂ), RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
      ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → RBM.BA.BAWinBulk sz z c₁ κ →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ RBM.BA.BAflowT0 sz z n) → (∀ n, s n < t n) →
        (∀ n, t n ≤ RBM.BA.BAflowT0 sz z n) →
        (∀ z' : ℕ → ℂ, RBM.BA.BAFamZ sz z c₁ s z' →
          let C := RBM.BA.baFMz sz z'; let μ := RBM.Gauss.Sizes.seqP (sz.withLam 0)
          RBM.BA.STLKgL C μ s ∧ RBM.BA.STDecaygL C μ s ∧ RBM.BA.STDecayStronggL C μ s ∧ RBM.BA.STLocalMaxgL C μ s ∧
            RBM.BA.STExp2gL C μ s ∧ RBM.BA.BATwistLoopLaw C μ s) →
        sz.STConStInd 𝔠d s t →
        ∀ z' : ℕ → ℂ, RBM.BA.BAFamZ sz z c₁ t z' →
          RBM.BA.STStep1LoopgL (RBM.BA.baFMz sz z') (RBM.Gauss.Sizes.seqP (sz.withLam 0)) s t ∧
            RBM.BA.STStep1WeakgL (RBM.BA.baFMz sz z') (RBM.Gauss.Sizes.seqP (sz.withLam 0)) s t

/-- **D2: K2, the per-member `ML:Kbound`** (supervisor 2026-10-11-0150 `:79-85`): `BAFamZ_mono` (to `Fam(0)`),
`BAFlowMember_holds`, `baKbound_holds` at the modified flow, `baFMz_eqAt` + `STKboundgL_congr`.  Proved in the probe. -/
def T2503_K2Member (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : RBM.Gauss.Sizes d) (z : ℕ → ℂ), RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
      ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → RBM.BA.BAWinBulk sz z c₁ κ →
      ∀ s : ℕ → ℝ, (∀ n, 0 ≤ s n) → ∀ z' : ℕ → ℂ, RBM.BA.BAFamZ sz z c₁ s z' →
        RBM.BA.STKboundgL (RBM.BA.baFMz sz z') (RBM.Gauss.Sizes.seqP (sz.withLam 0))

/-- **D3 (V-C1 step 3): the members.**  A member `z'` of `Fam(t)` runs to `t` (`BAFamZ_horizon`), and after the finite
modification `z'' = if n < n₀ then z n else z' n` it is a `BAFlow` at `(κ', ε', 𝔠, 𝔡)` with `κ' ≤ κ`, `ε' ≤ ε`
(`BAFlowMember_holds`; not at `(κ, ε)`), with horizon `≥ t` at every `n` and carrier eventually equal to the member's.
Proved in the probe. -/
def T2503_MemberFlow (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ κ' ε' : ℝ, 0 < κ' ∧ κ' ≤ κ ∧ 0 < ε' ∧ ε' ≤ ε ∧
    ∀ (𝔠 : ℝ) (sz : RBM.Gauss.Sizes d) (z : ℕ → ℂ), RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
      ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → RBM.BA.BAWinBulk sz z c₁ κ →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ RBM.BA.BAflowT0 sz z n) →
      ∀ z' : ℕ → ℂ, RBM.BA.BAFamZ sz z c₁ t z' →
        (∀ n, t n ≤ RBM.BA.BAflowT0 sz z' n) ∧
          ∃ z'' : ℕ → ℂ, RBM.BA.BAFlow sz κ' ε' 𝔠 𝔡 z'' ∧ (∀ n, t n ≤ RBM.BA.BAflowT0 sz z'' n) ∧
            RBM.BA.FlowFM.EvEq (RBM.BA.baFMz sz z'') (RBM.BA.baFMz sz z')

/-- **D3: TL2 is tail-local** (the one congruence missing on `main`; `twL2'` reads `C.G n`, `twK` reads `C.M n`,
`BA/TwistPins.lean:70, 76`; `PrecL_congr`).  Proved in the probe; V2a's 1b makes it public. -/
def T2503_TL2Congr : Prop :=
  ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d) (C C' : RBM.BA.FlowFM sz) (μ : MeasureTheory.Measure sz.SeqΩ) (τ : ℕ → ℝ),
    RBM.BA.FlowFM.EvEq C C' → (RBM.BA.BATwistLoopLaw C μ τ ↔ RBM.BA.BATwistLoopLaw C' μ τ)

/-! ### Shapes (not binding) -/

/-- **D4: the family twin of `BAChainTL`** (`BA/TwistPins.lean:185`; proof model `baChainTL_holds`, `BA/TwistChain.lean:240`):
the same premises with the family step at `STAny`; motive "every member of `Fam(t_k)`"; output `BAMLOutTL` at the main flow
(`BAFamZ_main`).  The tail passage (`∀ n, 0 < sz.lam n ≤ 𝔡⁻¹` from `WO`, the window at `κ/2` through
`BAWinBulk_of_dom_holds`) sits inside its proof. -/
def T2503_BAChainFamTL (d : ℕ) : Prop :=
  T2503_BAMainIndFamTL d RBM.Gauss.Sizes.STAny →
    RBM.BA.STHorizonG d (fun sz κ ε 𝔠 𝔡 z => RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => RBM.BA.BAflowT0 sz z) →
    RBM.BA.STBaseG d (fun sz => RBM.Gauss.Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z)
      RBM.BA.baFMz →
    RBM.BA.BATwistLoopBase d →
    (∀ κ ε 𝔠 𝔡 (sz : RBM.Gauss.Sizes d) z, RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z → RBM.BA.STG0M (RBM.BA.baFMz sz z)) →
    RBM.BA.BAMLOutTL d

/-- **The 1b targets (shape):** one regime `R` with its case `Rc` (as `ST_mainIndR_of_steps`, `MainIndRegimes:165`):
Steps 3-4 at the BA tuple in case `Rc` (U3-BA (b)), Step 5 in regime `R` (T2501 row b; U5e at d = 3; the explicit
hypothesis `STStep5IIIgL d` for (iii), Q4), Step 6 in regime `R` (V1-BA; text from T2502, here the abstract `S6`) give the
single-flow step with Step 1 given.  Step 2 (`baStep2_closed`), K12 (`baKbound_holds`, `baKward_holds`), TL1/TL2
(`TwistStep2_tl1`, `baTwistLoopStep_caseI/II`) are merged and read under their names. -/
def T2503_RegShape (d : ℕ) (R Rc : ∀ {d : ℕ}, RBM.Gauss.Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (S6 : Prop) : Prop :=
  RBM.BA.STStep3RgL d Rc (fun sz => RBM.Gauss.Sizes.seqP (sz.withLam 0))
      (fun sz κ ε 𝔠 𝔡 z => RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z) RBM.BA.baFMz RBM.BA.BAflowT0 →
    RBM.BA.STStep4RgL d Rc (fun sz => RBM.Gauss.Sizes.seqP (sz.withLam 0))
      (fun sz κ ε 𝔠 𝔡 z => RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z) RBM.BA.baFMz RBM.BA.BAflowT0 →
    RBM.BA.STStep5RgL d R (fun sz => RBM.Gauss.Sizes.seqP (sz.withLam 0))
      (fun sz κ ε 𝔠 𝔡 z => RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z) RBM.BA.baFMz RBM.BA.BAflowT0 →
    S6 → T2503_BAMainIndS1TL d R

/-- Regime (iii) (`ST_mainIndR_III_of_steps`, `MainIndRegimes:217`): case (i); Step 5 (iii) is the explicit hypothesis
`STStep5IIIgL d` at the BA tuple for `d ≥ 3` (Q4), discharged at `d = 3` through `baStep5III_holds`. -/
example (d : ℕ) (S6 : Prop) : Prop := T2503_RegShape d RBM.Gauss.Sizes.STReg5III RBM.Gauss.Sizes.STCaseI S6
/-- Regime (i) (`:222`): case (i); Step 5 (i) from `baStep5I_holds` (T2501 row b, running). -/
example (d : ℕ) (S6 : Prop) : Prop := T2503_RegShape d RBM.Gauss.Sizes.STReg5I RBM.Gauss.Sizes.STCaseI S6
/-- Regime (ii) (`:227`): case (ii); Step 5 (ii) from `baStep5II_holds` (T2501 row b). -/
example (d : ℕ) (S6 : Prop) : Prop := T2503_RegShape d RBM.Gauss.Sizes.STReg5II RBM.Gauss.Sizes.STCaseII S6
/-- Regime (iv) (`:232`): case (ii) (`3 ≤ d`); Step 5 (iv) from `baStep5IV_holds` (T2501 row b). -/
example (d : ℕ) (S6 : Prop) : Prop := T2503_RegShape d RBM.Gauss.Sizes.STReg5IV RBM.Gauss.Sizes.STCaseII S6

/-- Q4: the case-(iii) input at the BA tuple is the merged text of `baStep5III_holds` at general `d`. -/
example (d : ℕ) : Prop :=
  RBM.BA.STStep5IIIgL d (fun sz => RBM.Gauss.Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => RBM.BA.BAFlow sz κ ε 𝔠 𝔡 z)
    RBM.BA.baFMz RBM.BA.BAflowT0
