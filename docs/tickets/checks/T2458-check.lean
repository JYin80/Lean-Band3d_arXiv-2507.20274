/-
Release check for T2458 (dispatcher V3, Mon Oct 12 13:50 UTC 2026; DECISIONS §266).  BA-U U6 (ST side, additive): the generic Step 5 vocabulary of
`Induction/Step5Pins.lean` over the carrier, in the new file `Chain/Step5Gen.lean`; `Step5Pins` is not edited (outside the
certificate lane).  One kernel (supervisor 1152 U-C4): T8b's `Step2Gen_UN`; the `Ugen` bridge is T4s1's `bandStep2_Ugen`.
X1-C4: the CLT pins `STCltFargL`, `STCltIsogL`, `STExpInvgL` are X1a's (`Chain/CltGen`, T2455) and appear nowhere here.
Part 1: merged names.  Part 2: the target statements as Prop values (prefix `T2458_`; content binding up to the name).  The
vocabulary of target 3 (`STLK2g`, `STELKLKg`) is the subterm marked `-- STLK2g` / `-- STELKLKg` in the pins.  The Steps 3-4
premises of target 8 are `T2458_LmaxU_inline`, `T2458_LKU_inline` (conjuncts 2-3 of `twSteps`, TLF-C5; not target names: U3s1
names them).  `T2458_STLemDecCalEConclgL` (target 11, conditional) is binding up to the plug-in `ee` (U3s1's generic `STee`).
Then shapes (not binding): band bridges, BA readings, the kernel.  Part 3 (G1): the public band names of `Step5Pins` §2-§6,
unchanged.  Part 4: not this row.
Merged names only.  No proofs, no placeholders.
Run: lake env lean docs/tickets/checks/T2458-check.lean
-/
import RBM3D.Induction.Step5Pins
import RBM3D.Chain.GridDuhamelGen
import RBM3D.Chain.Step2Kern
import RBM3D.Chain.NewKLKGen
import RBM3D.BA.Step2BA
import RBM3D.BA.TwistPins
import RBM3D.Induction.TailtoTail
import RBM3D.Induction.NewKLKL
import RBM3D.Induction.ConArgDet
import RBM3D.Induction.DuhamelII
import RBM3D.Induction.IniTermI
import RBM3D.Induction.EtermsMid
import RBM3D.Induction.LemDecCalEPrec
import RBM3D.Induction.PfStep5
import RBM3D.Induction.MainIndRegimes
import RBM3D.Induction.Step6Pins
import RBM3D.Evolution.MeanFar

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- target 1: size-level names used as they are
#check @RBM.Gauss.Sizes.STReg5I
#check @RBM.Gauss.Sizes.STReg5II
#check @RBM.Gauss.Sizes.STReg5Mid
#check @RBM.Gauss.Sizes.STReg5III
#check @RBM.Gauss.Sizes.STReg5IV
#check @RBM.Gauss.Sizes.STIdx2
#check @RBM.Gauss.Sizes.STIdx2P
#check @RBM.Gauss.Sizes.STtailTD
#check @RBM.Gauss.Sizes.STSigSame
#check @RBM.Gauss.Sizes.STSigMixed
#check @RBM.Gauss.Sizes.STSigAll
#check @RBM.Gauss.Sizes.st5_reg5I_mid
#check @RBM.Gauss.Sizes.STAI
#check @RBM.Gauss.Sizes.STAny
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STprof
#check @RBM.tailTD
#check @RBM.zeroModeSet
-- target 8: the band premises of `STIngR5` and their carrier forms
#check @RBM.Gauss.Sizes.STIngR5
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.STKward
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.STDecay
#check @RBM.Gauss.Sizes.STDecayStrong
#check @RBM.Gauss.Sizes.STStep1Loop
#check @RBM.Gauss.Sizes.STStep2Concl
#check @RBM.Gauss.Sizes.STGdecayW
#check @RBM.Gauss.Sizes.STLmaxU
#check @RBM.Gauss.Sizes.STLKU
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.lemT
#check @RBM.BA.FlowFM
#check @RBM.BA.PrecL
#check @RBM.BA.bandFM
#check @RBM.BA.STKboundgL
#check @RBM.BA.STKwardgL
#check @RBM.BA.STLKgL
#check @RBM.BA.STDecaygL
#check @RBM.BA.STDecayStronggL
#check @RBM.BA.STStep1LoopgL
#check @RBM.BA.STStep2ConclgL
#check @RBM.BA.STGdecayWgL
#check @RBM.BA.bandFM_STKward
#check @RBM.BA.bandFM_STStep2Concl
#check @RBM.BA.bandFM_STGdecayW
#check @RBM.BA.bandFM_STKbound
#check @RBM.BA.bandFM_STLK
#check @RBM.BA.bandFM_STDecay
#check @RBM.BA.bandFM_STDecayStrong
#check @RBM.BA.bandFM_STStep1Loop
#check @RBM.BA.STStep2G
#check @RBM.BA.STMainIndG
#check @RBM.BA.STMainInd_iff
-- TLF-C5: the merged inline forms of the Steps 3-4 conclusions (conjuncts 2-3) and the BA frame with the same `Concl`-style
#check @RBM.BA.twSteps
#check @RBM.BA.BATwFrame
-- targets 2-4: model-level vocabulary
#check @RBM.Gauss.Sizes.STDecayStrongU
#check @RBM.Gauss.Sizes.STStep5Concl
#check @RBM.Gauss.Sizes.STLK2
#check @RBM.Gauss.Sizes.STELKLK
#check @RBM.Gauss.Sizes.STLKM
#check @RBM.Gauss.Sizes.STELKLKM
#check @RBM.Gauss.Sizes.STEGt
#check @RBM.Gauss.Sizes.STEEk
#check @RBM.BA.STELKLKMg
#check @RBM.BA.STEGtg
#check @RBM.BA.STEEg
#check @RBM.BA.bandFM_STEGt
#check @RBM.BA.bandFM_STEEk
-- target 12: the one kernel (U-C4), T4s1's bridge, the BA reading (E-C1)
#check @RBM.Ind.Ugen
#check @RBM.UN
#check @RBM.BA.Step2Mat
#check @RBM.BA.bandStep2Mat
#check @RBM.BA.Step2Gen_UN
#check @RBM.BA.Step2Kern_UN_band
#check @RBM.BA.bandStep2_Ugen
#check @RBM.BA.Step2Gen_USemigroup
#check @RBM.BA.Step2Gen_UN_self
#check @RBM.BA.Step2Kern_UN_BA
#check @RBM.BA.BAUN
-- targets 6-7: matrix-level vocabulary, the primed precedent, band facts
#check @RBM.Gauss.Sizes.STNewKLKLAt
#check @RBM.Gauss.Sizes.STNewKLKL
#check @RBM.Gauss.Sizes.STTailtoTail
#check @RBM.BA.STGMMg
#check @RBM.BA.STJhatMg
#check @RBM.BA.bandStep2_STELKLKM
#check @RBM.BA.bandStep2_STJhatM
#check @RBM.BA.bandStep2_STGMM
#check @RBM.BA.STNewKLKAtgL'
#check @RBM.BA.STNewKLKgL'
#check @RBM.BA.stNewKLKgL_of_primed
#check @RBM.Gauss.Sizes.stNewKLKL_holds
#check @RBM.Gauss.Sizes.stTailtoTail_holds
#check @RBM.EKsgn
#check @RBM.PropSpin
#check @RBM.mSigma
#check @RBM.mE_im
#check @RBM.norm_mE
#check @RBM.Ind.half_le_mE_im
-- BA readings (statement level only)
#check @RBM.BA.baFM
#check @RBM.BA.baFMz
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAStep2
#check @RBM.BA.baStep2Mat
#check @RBM.BA.BAmF
-- consumers (statement lines)
#check @RBM.Gauss.Sizes.ST_step5_caseI_of_pins
#check @RBM.Gauss.Sizes.ST_step5_caseII_of_pins
#check @RBM.Gauss.Sizes.ST_step5_caseIII_of_pf
#check @RBM.Gauss.Sizes.stStep5IV_holds
#check @RBM.Gauss.Sizes.ST_mainIndR_of_steps
#check @RBM.Gauss.Sizes.stCltFar_uniform
#check @RBM.Gauss.Sizes.STMeanFar
#check @RBM.Gauss.Sizes.stEtermsMid_of_LWT
#check @RBM.Gauss.Sizes.stDuhamelI_holds
#check @RBM.Gauss.Sizes.stDuhamelII_holds
#check @RBM.Gauss.Sizes.stIniTermI_holds
#check @RBM.Gauss.Sizes.stIniTermII_holds
#check @RBM.Gauss.Sizes.stWardII_holds
#check @RBM.Gauss.Sizes.stLemDecCalE_holds
#check @RBM.Gauss.Sizes.stPfStep5_holds
#check @RBM.Gauss.Sizes.STIngR6
-- target 15: the band instances re-derived through the bridges
#check @RBM.Gauss.Step5Inst.inst_etermsMid
#check @RBM.Gauss.Step5Inst.inst_duhamelI
#check @RBM.Gauss.Step5Inst.inst_iniTermI
#check @RBM.Gauss.Step5Inst.inst_wardII
#check @RBM.Gauss.Step5Inst.inst_pfStep5

/-! ## Part 2: the target statements (content binding) and shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 2** (content binding): `(Eq:Gdecay+s<g_flow)` over the carrier, the band `STDecayStrongU` (`Step5Pins.lean:69`) with
`C.L`/`C.K` for `Lloop`/`STKloop` and `PrecL μ` for `Prec`. -/
def T2458_STDecayStrongUgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    PrecL sz μ
      (U := fun n => {_p : TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // sz.lam n ^ 2 ≤ 1 - t n})
      (fun n p ω => ‖C.L n (p.1.1 : ℝ) p.1.2.1 p.1.2.2 ω - C.K n (p.1.1 : ℝ) p.1.2.1 p.1.2.2‖)
      (fun n p _ => (sz.Bctl n (p.1.1 : ℝ)) ^ 2 *
          Real.exp (-((zdistInf d (sz.L n) (p.1.2.2 0 - p.1.2.2 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **Target 2** (content binding): the Step-5 conclusion (`Step5Pins.lean:97`), loss exponent `0`. -/
def T2458_STStep5ConclgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  STGdecayWgL C μ s t 0 ∧ T2458_STDecayStrongUgL C μ s t

/-- **Target 4** (content binding): `(S5WG+M000)`, `(S5WG+M)` (`Step5Pins.lean:259`) over the carrier: `STELKLKg` (marked),
`STEGtg`, `STEEg`, and `C.eta n` for `etaT (E n)`. -/
def T2458_STEtermsMidConclgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    PrecL sz μ (U := STIdx2 sz s t)
      (fun n p ω => ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n), -- STELKLKg
          (C.L n (p.1 : ℝ) p.2.1 ![x, p.2.2 1] ω - C.K n (p.1 : ℝ) p.2.1 ![x, p.2.2 1]) * C.S n x y *
            (C.L n (p.1 : ℝ) p.2.1 ![p.2.2 0, y] ω - C.K n (p.1 : ℝ) p.2.1 ![p.2.2 0, y])‖)
      (fun n p _ => (STAI sz n) ^ (-(1 / 3) : ℝ) * (C.eta n (p.1 : ℝ))⁻¹ *
        STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) ∧
    PrecL sz μ (U := STIdx2 sz s t)
      (fun n p ω => ‖STEGtg C n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => (STAI sz n) ^ (-(1 / 2) : ℝ) * (C.eta n (p.1 : ℝ))⁻¹ *
        STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) ∧
    PrecL sz μ (U := fun n => STIdx2 sz s t n × Fin 2)
      (fun n p ω => ‖STEEg C n (p.1.1 : ℝ) p.2 p.1.2.1 p.1.2.2 ω‖)
      (fun n p _ => (STAI sz n) ^ (-(1 / 2) : ℝ) * (C.eta n (p.1.1 : ℝ))⁻¹ *
        STprof sz n (p.1.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.1.2.2 0) (p.1.2.2 1) ^ 2)

/-- **Target 4** (content binding): the initial term (`Step5Pins.lean:280`) with the one kernel `Step2Gen_UN C` for `Ugen` (U-C4)
and `C.L - C.K` at the time `s n` for `STLKM … (seqHflow …)`. -/
def T2458_STIniTermConclgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (Q : Finset (Fin 2))
    (P : (Fin 2 → Bool) → Prop) (s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    PrecL sz μ (U := STIdx2P sz P s t)
      (fun n p ω => ‖zeroModeSet d (sz.L n) Q
        (Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ)
          (fun b => C.L n (s n) p.2.1.1 b ω - C.K n (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => (STAI sz n) ^ (-(1 / 5) : ℝ) *
          STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **Target 4** (content binding): the integrated hierarchy at `n = 2` (`Step5Pins.lean:297`), same kernel rule. -/
def T2458_STDuhamelConclgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (Q : Finset (Fin 2))
    (P : (Fin 2 → Bool) → Prop) (s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D → ∀ F : ∀ n, STIdx2P sz P s t n → ℝ, (∀ n p, 0 ≤ F n p) →
    PrecL sz μ (U := STIdx2P sz P s t)
      (fun n p ω => ‖zeroModeSet d (sz.L n) Q
        (Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ)
          (fun b => C.L n (s n) p.2.1.1 b ω - C.K n (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => F n p) →
    PrecL sz μ (U := STIdx2P sz P s t)
      (fun n p ω => ‖zeroModeSet d (sz.L n) Q
        (fun a' => C.L n (p.1 : ℝ) p.2.1.1 a' ω - C.K n (p.1 : ℝ) p.2.1.1 a') p.2.2‖)
      (fun n p _ => F n p + (STAI sz n) ^ (-(1 / 5) : ℝ) *
          STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **Target 4** (content binding): `(zYU1)` (`Step5Pins.lean:340`) with `C.eta n` for `etaT (E n)`. -/
def T2458_STWardIIConclgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := STIdx2P sz STSigMixed s t)
    (fun n p ω => ‖(C.L n (p.1 : ℝ) p.2.1.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1.1 p.2.2) -
      zeroModeSet d (sz.L n) {0}
        (fun a' => C.L n (p.1 : ℝ) p.2.1.1 a' ω - C.K n (p.1 : ℝ) p.2.1.1 a') p.2.2‖)
    (fun n p _ => (STAI sz n)⁻¹ * (((sz.size n : ℕ) : ℝ) * C.eta n (p.1 : ℝ))⁻¹)

/-- **Target 5** (content binding): `lem:pf_step5` at the sequence level (`Step5Pins.lean:202`); `STLK2g` marked. -/
def T2458_STPfConclgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    PrecL sz μ
      (U := fun n => {_p : STIdx2 sz s t n // sz.lam n ^ 2 ≤ 1 - t n})
      (fun n p ω => ‖C.L n (p.1.1 : ℝ) p.1.2.1 p.1.2.2 ω - C.K n (p.1.1 : ℝ) p.1.2.1 p.1.2.2‖) -- STLK2g
      (fun n p _ => STtailTD sz n (p.1.1 : ℝ) D p.1.2.2)

/-- **Target 6** (content binding): `lem:newKLK` at `ℓ = L`, sharp form (`Step5Pins.lean:235`), primed: `κ ≤ Im m` of the family
at the constant sequence for `|E| ≤ 2 - κ` (the shape of `STNewKLKAtgL'`, `Chain/NewKLKGen.lean:58`). -/
def T2458_STNewKLKLAtgL' (d : ℕ) (κ 𝔡 Ck δ₀ : ℝ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u D : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → κ ≤ ((mk sz (fun _ => E)).m n).im →
    0 ≤ u → u < 1 → 0 ≤ D →
    ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
      (∀ x y, ‖STGMMg (mk sz (fun _ => E)) n u H x y‖ ≤ δ₀) →
      ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STELKLKMg (mk sz (fun _ => E)) n u H σ a‖ ≤
          Ck / (1 - u) * (STJhatMg (mk sz (fun _ => E)) n D ((sz.L n : ℕ) : ℝ) u H ^ 2 *
              STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) +
            STJhatMg (mk sz (fun _ => E)) n D ((sz.L n : ℕ) : ℝ) u H * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
              ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **Target 6** (content binding): the pin (`Step5Pins.lean:247`). -/
def T2458_STNewKLKLgL' (d : ℕ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ Ck δ₀ : ℝ, 0 < Ck ∧ 0 < δ₀ ∧ T2458_STNewKLKLAtgL' d κ 𝔡 Ck δ₀ mk

/-- **Target 7** (content binding): the conclusion of `(neiwuj)` (`Step5Pins.lean:121`) for the one kernel `Step2Gen_UN C`
(U-C4) at size index `n`. -/
def T2458_STTailtoTailConclgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (Cc D s t : ℝ) : Prop :=
  ∀ (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L n)) → ℂ),
    (∀ b, ‖A b‖ ≤ tailTD d ((sz.W n : ℕ) : ℝ) s D (zdistInf d (sz.L n) (b 0 - b 1) : ℝ)) →
    ∀ a, ‖Step2Gen_UN C n σ s t A a‖ ≤
      Cc * tailTD d ((sz.W n : ℕ) : ℝ) t D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) +
        ((1 - s) / (1 - t)) ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D)

/-- **Target 7** (content binding): the pin, primed (`κ ≤ Im m` and `0 < sz.lam n` for `‖m‖ = 1`, `0 < g`). -/
def T2458_STTailtoTailgL' (d : ℕ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → FlowFM sz) : Prop :=
  3 ≤ d → ∀ κ : ℝ, 0 < κ → ∃ Cc : ℝ, 0 < Cc ∧
    ∀ (sz : Sizes d) (n : ℕ) (E D s t : ℝ), 0 < sz.lam n → κ ≤ ((mk sz (fun _ => E)).m n).im →
      0 ≤ s → s ≤ t → t < 1 → sz.lam n ^ 2 ≤ 1 - t →
        T2458_STTailtoTailConclgL (mk sz (fun _ => E)) n Cc D s t

/-- Not a target name (TLF-C5: U3s1 names it `STLmaxUgL`, T2457 target 1): conjunct 2 of the merged `twSteps`
(`BA/TwistPins.lean:135-136`) verbatim, the carrier form of `STLmaxU` (`Step34Pins.lean:176`).  Target 8 writes it inline. -/
def T2458_LmaxU_inline {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
    (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (k - 1))

/-- Not a target name (U3s1's `STLKUgL`): conjunct 3 of `twSteps` (`BA/TwistPins.lean:137-138`), the carrier form of `STLKU`. -/
def T2458_LKU_inline {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
    (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ k)

/-- **Target 8** (content binding): the shape of every Step-5 pin (`STIngR5`, `Step5Pins.lean:82`) over a carrier
`(law, Flow, mk, T0)`, binder order and `Concl` index of U3s1's `STIngRgL` (T2457, D2 default); the band order of premises is
kept; the Steps 3-4 premises are written inline. -/
def T2458_STIngR5gL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Concl : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ T0 sz z n) →
          R sz s t → STKboundgL (mk sz z) (law sz) → STKwardgL (mk sz z) (law sz) →
          STLKgL (mk sz z) (law sz) s → STDecaygL (mk sz z) (law sz) s →
          STDecayStronggL (mk sz z) (law sz) s → STConStInd sz 𝔠d s t →
          STStep1LoopgL (mk sz z) (law sz) s t → STStep2ConclgL (mk sz z) (law sz) s t Cd →
          T2458_LmaxU_inline (mk sz z) (law sz) s t → T2458_LKU_inline (mk sz z) (law sz) s t →
            Concl sz z s t

/-- **Target 9** (content binding): Step 5 under a regime `R` (`Step5Pins.lean:101`). -/
def T2458_STStep5RgL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  T2458_STIngR5gL d R law Flow mk T0 (fun sz z s t => T2458_STStep5ConclgL (mk sz z) (law sz) s t)

section Wrapped

variable (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
  (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)

/-- **Target 9** (content binding): the four regimes and the general statement (`Step5Pins.lean:453-463`). -/
def T2458_STStep5IgL : Prop := T2458_STStep5RgL d STReg5I law Flow mk T0
def T2458_STStep5IIgL : Prop := T2458_STStep5RgL d STReg5II law Flow mk T0
def T2458_STStep5IIIgL : Prop := T2458_STStep5RgL d STReg5III law Flow mk T0
def T2458_STStep5IVgL : Prop := T2458_STStep5RgL d STReg5IV law Flow mk T0
def T2458_STStep5gL : Prop := T2458_STStep5RgL d STAny law Flow mk T0

/-- **Target 10** (content binding): the wrapped case pins (`Step5Pins.lean:211, 275, 317-348`). -/
def T2458_STEtermsMidgL : Prop :=
  T2458_STIngR5gL d STReg5Mid law Flow mk T0 (fun sz z s t => T2458_STEtermsMidConclgL (mk sz z) (law sz) s t)
def T2458_STDuhamelIgL : Prop :=
  T2458_STIngR5gL d STReg5I law Flow mk T0 (fun sz z s t =>
    T2458_STEtermsMidConclgL (mk sz z) (law sz) s t → T2458_STDuhamelConclgL (mk sz z) (law sz) ∅ STSigAll s t)
def T2458_STIniTermIgL : Prop :=
  T2458_STIngR5gL d STReg5I law Flow mk T0 (fun sz z s t => T2458_STIniTermConclgL (mk sz z) (law sz) ∅ STSigAll s t)
def T2458_STDuhamelIIgL : Prop :=
  T2458_STIngR5gL d STReg5II law Flow mk T0 (fun sz z s t =>
    T2458_STEtermsMidConclgL (mk sz z) (law sz) s t →
      T2458_STDuhamelConclgL (mk sz z) (law sz) {0} STSigMixed s t ∧
        T2458_STDuhamelConclgL (mk sz z) (law sz) ∅ STSigSame s t)
def T2458_STIniTermIIgL : Prop :=
  T2458_STIngR5gL d STReg5II law Flow mk T0 (fun sz z s t =>
    T2458_STIniTermConclgL (mk sz z) (law sz) {0} STSigMixed s t ∧
      T2458_STIniTermConclgL (mk sz z) (law sz) ∅ STSigSame s t)
def T2458_STWardIIgL : Prop :=
  T2458_STIngR5gL d STReg5II law Flow mk T0 (fun sz z s t => T2458_STWardIIConclgL (mk sz z) (law sz) s t)
def T2458_STPfStep5gL : Prop :=
  T2458_STIngR5gL d STReg5III law Flow mk T0 (fun sz z s t => T2458_STPfConclgL (mk sz z) (law sz) s t)

end Wrapped

/-- **Target 11** (conditional; content binding up to `ee` := U3s1's generic `STee`, `Step34Pins.lean:159`, T2457 target 3):
`lem_dec_calE` (`Step5Pins.lean:161`) over the carrier; `STLK2g`, `STELKLKg` marked. -/
def T2458_STLemDecCalEConclgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)
    (ee : ∀ n : ℕ, ℝ → sz.SeqΩ → (Fin 2 → Bool) → (Fin 2 → Zd d (sz.L n)) → (Fin 2 → Zd d (sz.L n)) → ℂ)
    (s t : ℕ → ℝ) : Prop :=
  ∀ Jst : ℕ → ℝ → ℝ → ℝ, (∀ n u D, 1 ≤ Jst n u D) →
    (∀ n u D, Jst n u D ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ)) →
    ∀ D : ℝ, 0 < D →
      (∀ᶠ n in atTop, (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D) →
      PrecL sz μ (U := STIdx2 sz s t)
        (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖) -- STLK2g
        (fun n p _ => Jst n (p.1 : ℝ) D * STtailTD sz n (p.1 : ℝ) D p.2.2) →
      PrecL sz μ (U := STIdx2 sz s t)
        (fun n p ω => ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n), -- STELKLKg
          (C.L n (p.1 : ℝ) p.2.1 ![x, p.2.2 1] ω - C.K n (p.1 : ℝ) p.2.1 ![x, p.2.2 1]) * C.S n x y *
            (C.L n (p.1 : ℝ) p.2.1 ![p.2.2 0, y] ω - C.K n (p.1 : ℝ) p.2.1 ![p.2.2 0, y])‖)
        (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - (p.1 : ℝ)|)⁻¹ * Jst n (p.1 : ℝ) D ^ 2 *
          STtailTD sz n (p.1 : ℝ) D p.2.2) ∧
      PrecL sz μ (U := STIdx2 sz s t)
        (fun n p ω => ‖STEGtg C n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => (1 - (p.1 : ℝ))⁻¹ *
          ((if ((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)
              then 1 else 0) +
            (((sz.W n : ℕ) : ℝ) ^ d * |1 - (p.1 : ℝ)|)⁻¹ ^ (1 / 2 : ℝ) * Jst n (p.1 : ℝ) D ^ (3 / 2 : ℝ)) *
          STtailTD sz n (p.1 : ℝ) D p.2.2) ∧
      PrecL sz μ
        (U := fun n => {q : STIdx2 sz s t n × (Fin 2 → Zd d (sz.L n)) //
          ∀ i : Fin 2, ((zdistInf d (sz.L n) (q.1.2.2 i - q.2 i) : ℕ) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)})
        (fun n q ω => ‖ee n (q.1.1.1 : ℝ) ω q.1.1.2.1 q.1.1.2.2 q.1.2‖)
        (fun n q _ => (1 - (q.1.1.1 : ℝ))⁻¹ *
          ((if ((zdistInf d (sz.L n) (q.1.1.2.2 0 - q.1.1.2.2 1) : ℕ) : ℝ) ≤ 4 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)
              then 1 else 0) +
            (((sz.W n : ℕ) : ℝ) ^ d * |1 - (q.1.1.1 : ℝ)|)⁻¹ ^ (1 / 2 : ℝ) * Jst n (q.1.1.1 : ℝ) D ^ (3 : ℝ)) *
          STtailTD sz n (q.1.1.1 : ℝ) D q.1.1.2.2 ^ 2)

/-! ### Shapes (not binding) -/

/-- TLF-C5: the inline premises of target 8 are conjuncts 2-3 of `twSteps` (on the branch: the projections `h.2.1`, `h.2.2.1`). -/
example : Prop := ∀ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) (Cd : ℝ),
  twSteps C μ s t Cd → STStep2ConclgL C μ s t Cd ∧ T2458_LmaxU_inline C μ s t ∧ T2458_LKU_inline C μ s t

/-- Band readings of the inline premises (definitional on the branch). -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ),
  (STLmaxU sz E s t ↔ T2458_LmaxU_inline (bandFM sz E) (Sizes.seqP sz) s t) ∧
    (STLKU sz E s t ↔ T2458_LKU_inline (bandFM sz E) (Sizes.seqP sz) s t)

/-- Target 8, band bridge of the setting (proved on the branch, through `bandFM_STKward`; the rest definitional). -/
example : Prop := ∀ (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop),
  STIngR5 d R Concl ↔ T2458_STIngR5gL d R (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) (fun sz z s t => Concl sz (STflowE z) s t)

/-- Target 9, band bridge. -/
example : Prop := ∀ (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop),
  STStep5R d R ↔ T2458_STStep5RgL d R (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))

/-- Target 10, band bridges (two of seven). -/
example : Prop := ∀ d : ℕ,
  STEtermsMid d ↔ T2458_STEtermsMidgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))
example : Prop := ∀ d : ℕ,
  STPfStep5 d ↔ T2458_STPfStep5gL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))

/-- Targets 2, 4, 5, band bridges of the conclusions (definitional, except the two `Ugen` ones: proved through `bandStep2_Ugen`). -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ),
  (STDecayStrongU sz E s t ↔ T2458_STDecayStrongUgL (bandFM sz E) (Sizes.seqP sz) s t) ∧
  (STStep5Concl sz E s t ↔ T2458_STStep5ConclgL (bandFM sz E) (Sizes.seqP sz) s t) ∧
  (STEtermsMidConcl sz E s t ↔ T2458_STEtermsMidConclgL (bandFM sz E) (Sizes.seqP sz) s t) ∧
  (STWardIIConcl sz E s t ↔ T2458_STWardIIConclgL (bandFM sz E) (Sizes.seqP sz) s t) ∧
  (STPfConcl sz E s t ↔ T2458_STPfConclgL (bandFM sz E) (Sizes.seqP sz) s t)
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (Q : Finset (Fin 2)) (P : (Fin 2 → Bool) → Prop) (E s t : ℕ → ℝ),
  (STIniTermConcl sz Q P E s t ↔ T2458_STIniTermConclgL (bandFM sz E) (Sizes.seqP sz) Q P s t) ∧
  (STDuhamelConcl sz Q P E s t ↔ T2458_STDuhamelConclgL (bandFM sz E) (Sizes.seqP sz) Q P s t)

/-- Targets 6-7, band theorems (band ⇒ generic; proved on the branch). -/
example : Prop := ∀ d : ℕ, STNewKLKL d → T2458_STNewKLKLgL' d (fun sz E => bandStep2Mat sz E)
example : Prop := ∀ d : ℕ, STTailtoTail d → T2458_STTailtoTailgL' d (fun sz E => bandFM sz E)

/-- Target 11, band reading at `ee := STee`. -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ),
  STLemDecCalEConcl sz E s t ↔
    T2458_STLemDecCalEConclgL (bandFM sz E) (Sizes.seqP sz) (fun n u ω σ a a' => STee sz n (E n) u ω σ a a') s t

/-- E-C1 / U-C4: the BA reading of the one kernel is stage E's `BAUN` (merged `Step2Kern_UN_BA`, `Chain/Step2Kern.lean:124`). -/
example : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n k : ℕ) (σ : Fin k → Bool) (s t : ℝ) (A : (Fin k → Zd d (sz.L n)) → ℂ),
    Step2Gen_UN (baFM sz lam0 E) n σ s t A = BAUN d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) σ s t A

/-- BA readings (statement level; U6-BA, U5): the tuple of `BAStep2` (`BA/FlowPins.lean:432`). -/
example : Prop := T2458_STStep5IIIgL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
  baFMz BAflowT0
example : Prop := T2458_STPfStep5gL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
  baFMz BAflowT0
example : Prop := ∀ lam0 : ℕ → ℝ, T2458_STNewKLKLgL' 3 (fun sz E => baStep2Mat sz lam0 E)
example : Prop := ∀ lam0 : ℕ → ℝ, T2458_STTailtoTailgL' 3 (fun sz E => baFM sz lam0 E)

end RBM.BA

end

/-! ## Part 3 (G1): the public band names of `Step5Pins` §2-§6 (file not edited; statements unchanged) -/
#check @RBM.Gauss.Sizes.STReg5I
#check @RBM.Gauss.Sizes.STReg5II
#check @RBM.Gauss.Sizes.STReg5Mid
#check @RBM.Gauss.Sizes.STReg5III
#check @RBM.Gauss.Sizes.STReg5IV
#check @RBM.Gauss.Sizes.STDecayStrongU
#check @RBM.Gauss.Sizes.STIngR5
#check @RBM.Gauss.Sizes.STStep5Concl
#check @RBM.Gauss.Sizes.STStep5R
#check @RBM.Gauss.Sizes.STTailtoTail
#check @RBM.Gauss.Sizes.STIdx2
#check @RBM.Gauss.Sizes.STLK2
#check @RBM.Gauss.Sizes.STELKLK
#check @RBM.Gauss.Sizes.STtailTD
#check @RBM.Gauss.Sizes.STLemDecCalEConcl
#check @RBM.Gauss.Sizes.STLemDecCalE
#check @RBM.Gauss.Sizes.STPfConcl
#check @RBM.Gauss.Sizes.STPfStep5
#check @RBM.Gauss.Sizes.STIdx2P
#check @RBM.Gauss.Sizes.STNewKLKLAt
#check @RBM.Gauss.Sizes.STNewKLKL
#check @RBM.Gauss.Sizes.STEtermsMidConcl
#check @RBM.Gauss.Sizes.STEtermsMid
#check @RBM.Gauss.Sizes.STIniTermConcl
#check @RBM.Gauss.Sizes.STDuhamelConcl
#check @RBM.Gauss.Sizes.STSigSame
#check @RBM.Gauss.Sizes.STSigMixed
#check @RBM.Gauss.Sizes.STSigAll
#check @RBM.Gauss.Sizes.STDuhamelI
#check @RBM.Gauss.Sizes.STIniTermI
#check @RBM.Gauss.Sizes.STDuhamelII
#check @RBM.Gauss.Sizes.STIniTermII
#check @RBM.Gauss.Sizes.STWardIIConcl
#check @RBM.Gauss.Sizes.STWardII
#check @RBM.Gauss.Sizes.STfFar
#check @RBM.Gauss.Sizes.STCltFarConcl
#check @RBM.Gauss.Sizes.STCltFar
#check @RBM.Gauss.Sizes.STcltB
#check @RBM.Gauss.Sizes.STcltX
#check @RBM.Gauss.Sizes.STCltIsoConcl
#check @RBM.Gauss.Sizes.STCltIso
#check @RBM.Gauss.Sizes.STExpInv
#check @RBM.Gauss.Sizes.STStep5I
#check @RBM.Gauss.Sizes.STStep5II
#check @RBM.Gauss.Sizes.STStep5III
#check @RBM.Gauss.Sizes.STStep5IV
#check @RBM.Gauss.Sizes.STStep5
#check @RBM.Gauss.Sizes.st5_reg5I_mid

/-! ## Part 4: not this row -/
-- X1-C4: owner X1a (`Chain/CltGen`, T2455; not merged at drafting): the band CLT pins and their band theorems
#check @RBM.Gauss.Sizes.stCltFar_holds
#check @RBM.Gauss.Sizes.stCltIso_holds
#check @RBM.Gauss.Sizes.stExpInv_holds
-- U-C2 / TLF-C5: owner U3s1 (`Chain/Step34Gen`, T2457): `STLmaxU`, `STLKU` (Part 1) and the list-indexed `STee`
#check @RBM.Gauss.Sizes.STee
#check @RBM.Gauss.Sizes.STeeLoop
