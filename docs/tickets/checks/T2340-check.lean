/-
Release check for T2340 (dispatcher V1, Thu Oct 8 18:44 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §151, §145).
ST-6 rows R1–R3 of the T2338 design (`docs/reports/T2338-design.md` §7), one ticket: the base case `t = 0`, the chain,
the output `STMainInd → UNMLOut` over a carrier (route G), band and BA instances, `stMainInd_of_LW`.
Section 1: merged names (`main` 7154d50).  Section 2: the new pins, verbatim from the probe `RBM3D/Probe/T2338Pins.lean:40-79`
(branch `t/T2338` at 854aa29), prefixed `T2340_`.  Section 3: the targets as `Prop`s.  `#check`, definitions and `Prop`s only.
Run: `lake env lean docs/tickets/checks/T2340-check.lean`.
-/
import RBM3D.Induction.Step4
import RBM3D.Induction.Step3
import RBM3D.Induction.DuhamelI
import RBM3D.Induction.DuhamelII
import RBM3D.Induction.IniTermI
import RBM3D.Induction.LocalAvg2
import RBM3D.Induction.AzumaProxyN
import RBM3D.Graph.LWExpTerm6
import RBM3D.Universality.Pins
import RBM3D.BA.UNPins
import RBM3D.Main.FixedZ

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.unusedVariables false

open MeasureTheory Filter
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.BA RBM.Ind

/-! ## 1. Merged names -/

#check @RBM.Gauss.Sizes.STMainInd                  -- Induction/Defs.lean:294 (owed; deleted by R4, not here)
#check @RBM.Gauss.Sizes.ST_mainInd_of_regimes      -- Induction/MainIndRegimes.lean
#check @RBM.Gauss.Sizes.STLocalMax_of_STLocalEntry -- Induction/MainIndRegimes.lean
#check @RBM.Gauss.Sizes.ST_mainInd_of_pins'
#check @RBM.Gauss.Sizes.ST_step2_of_pinsLW'
#check @RBM.Gauss.Sizes.stDuhamelI_holds
#check @RBM.Gauss.Sizes.stDuhamelII_holds          -- T2339, 0853ac1
#check @RBM.Gauss.Sizes.stIniTermI_holds
#check @RBM.Gauss.Sizes.stEtermsMid_of_LWT
#check @RBM.Gauss.Sizes.LWterm                     -- Graph/LWPins.lean:240 (owed, LW-01)
#check @RBM.Gauss.Sizes.LWtermExp                  -- Graph/LWPins.lean:290 (owed, LW-01 / LW-16)
#check @RBM.Gauss.Sizes.STFlow                     -- Induction/Defs.lean:286
#check @RBM.BA.STMainIndG                          -- BA/FlowPins.lean:565
#check @RBM.BA.FlowFM                              -- BA/FlowPins.lean:332
#check @RBM.BA.bandFM                              -- BA/FlowPins.lean:469
#check @RBM.BA.STLKgL                              -- BA/FlowPins.lean:357
#check @RBM.BA.STLocalEntrygL                      -- BA/FlowPins.lean:398
#check @RBM.BA.BAFlow                              -- BA/FlowPins.lean:546
#check @RBM.BA.baFMz                               -- BA/FlowPins.lean:550
#check @RBM.BA.BAflowT0                            -- BA/FlowPins.lean:537
#check @RBM.Univ.UNMLOut                           -- Universality/Pins.lean:432 (owed; deleted by R4, not here)
#check @RBM.Univ.UNMLOutBA                         -- BA/UNPins.lean:110 (owed, BA-V3)
-- `azumaProxy_loopFine_sub_STKloop` (`Induction/AzumaProxyN.lean:597`) is `private` on main: R1 drops the keyword (§151 (2)).

namespace RBM.T2340Check

/-! ## 2. The new pins (namespace `RBM.BA` in the ticket; here prefixed `T2340_`) -/

variable {d : ℕ}

/-- The six conclusions of `lem:main_ind` at the time sequence `τ` over a carrier (the order of `STMainIndG`). -/
def T2340_STConclgL {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (τ : ℕ → ℝ) : Prop :=
  STLKgL C μ τ ∧ STLmaxgL C μ τ ∧ STDecaygL C μ τ ∧ STExp2gL C μ τ ∧ STLocalEntrygL C μ τ ∧
    STDecayStronggL C μ τ

/-- R1: `𝓛_0 = 𝒦_0` (`1_2:1240-1243`) for every loop length `k ≥ 1`. -/
def T2340_STLK0 {sz : Sizes d} (C : FlowFM sz) : Prop :=
  ∀ (n k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) (ω : sz.SeqΩ), 1 ≤ k → C.L n 0 σ a ω = C.K n 0 σ a

/-- R1: `G_0 = M` (`1_2:1240`). -/
def T2340_STG0M {sz : Sizes d} (C : FlowFM sz) : Prop :=
  ∀ (n : ℕ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)), C.G n 0 ω x y = C.M n x y

/-- **R1 (base case)**: the six conclusions at the zero sequence, for every flow. -/
def T2340_STBaseG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 𝔠 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ),
    Flow sz κ ε 𝔠 𝔡 z → T2340_STConclgL (mk sz z) (law sz) (fun _ => 0)

/-- **R2 (horizon)**: what the chain needs of the flow and its horizon `T0`: admissible sizes, `0 < T0 < 1`, and
`N^{-1+ε/2} ≤ 1 - T0` eventually (band: `T0 = lemT z`, `1 - lemT z ≥ Im z/(1+|z|)`). -/
def T2340_STHorizonG (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → 0 < ε → Flow sz κ ε 𝔠 𝔡 z →
    sz.Admissible 𝔠 𝔡 ∧ (∀ n, 0 < T0 sz z n ∧ T0 sz z n < 1) ∧
      ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2) ≤ 1 - T0 sz z n

/-- **R3 (the ST-6 output)**: `ML:GLoop`, `ML:GLoop_expec`, `ML:GtLocal` at every `0 ≤ t_n ≤ T0`; band: `UNMLOut`. -/
def T2340_STMLOutG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 𝔠 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ),
    Flow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
      STLKgL (mk sz z) (law sz) t ∧ STLmaxgL (mk sz z) (law sz) t ∧ STDecaygL (mk sz z) (law sz) t ∧
        STExp2gL (mk sz z) (law sz) t ∧ STLocalEntrygL (mk sz z) (law sz) t

/-- The geometric chain `1 - p_k = (1 - t)^{k/K}`: `p_0 = 0`, `p_K = t` (RBM2D `chainTime`, `Induction/Defs.lean:318` at `c9a24cf`). -/
noncomputable def T2340_stChainTime (t : ℕ → ℝ) (K k : ℕ) : ℕ → ℝ := fun n => 1 - (1 - t n) ^ ((k : ℝ) / K)

/-! ## 3. The targets as `Prop`s -/

/-- R1: band base case, no hypothesis (the identity `𝓛_0 = 𝒦_0` from the now public `RBM.Ind.azumaProxy_loopFine_sub_STKloop`). -/
def T2340_stBase_band : Prop := ∀ d : ℕ,
  T2340_STBaseG d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z))

/-- R2: band horizon. -/
def T2340_stHorizon_band : Prop := ∀ d : ℕ,
  T2340_STHorizonG d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun _ z n => lemT (z n))

/-- R3, generic: `lem:main_ind` over a carrier + horizon + base case give the output at every `0 ≤ t_n ≤ T0`. -/
def T2340_stMLOutG_of_mainIndG : Prop := ∀ (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ),
  STMainIndG d law Flow mk T0 → T2340_STHorizonG d Flow T0 → T2340_STBaseG d law Flow mk → T2340_STMLOutG d law Flow mk T0

/-- R3, band: the candidate of ST-D6, with no extra hypothesis. -/
def T2340_unMLOut_of_mainInd : Prop := ∀ d : ℕ, STMainInd d → RBM.Univ.UNMLOut d

/-- R3, BA: by instantiation (the three BA instances stay owed, BA-V). -/
def T2340_unMLOutBA_of_pins : Prop := ∀ d : ℕ,
  STMainIndG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 →
  T2340_STHorizonG d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) BAflowT0 →
  T2340_STBaseG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz →
  RBM.Univ.UNMLOutBA d

/-- R3: `STMainInd` from the two owed LW pins (every other premise of `ST_mainInd_of_pins'` is proved on main). -/
def T2340_stMainInd_of_LW : Prop := ∀ d : ℕ, LWterm d → LWtermExp d → STMainInd d

/-- R3: the ST-6 output from the two owed LW pins. -/
def T2340_unMLOut_of_LW : Prop := ∀ d : ℕ, LWterm d → LWtermExp d → RBM.Univ.UNMLOut d

end RBM.T2340Check
