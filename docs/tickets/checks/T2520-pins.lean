/-
Proposals for T2520 (dispatcher V5, 2026-10-16 12:58 UTC; DECISIONS §353): the `T2520_*` texts (the filtered pins and chain are
the compiled MN-D3 probe texts, a6d9966e, renamed; the other texts are new).  NOT a release gate: the hub compiles this file for
information and pastes the error lines; the 1a restates in its probe what it needs; the texts bind after N2's 1a.
Statements only; no proofs.
Run: lake env lean docs/tickets/checks/T2520-pins.lean
-/
import RBM3D.Main.BandTerminal
import RBM3D.BA.UNPins
import RBM3D.BA.EMCTE2BA
import RBM3D.BA.RandomLayerBGBA
import RBM3D.BA.MReg
import RBM3D.BA.MALocal
import RBM3D.BA.MATrLocalBA
import RBM3D.BA.MAQDiff
import RBM3D.BA.MADecolQUE
import RBM3D.BA.GUEKPrim
import RBM3D.BA.MainIndTermBA
import RBM3D.Universality.GUEPhase.RandomLayerBG
import RBM3D.Universality.OUInterfaceK
import RBM3D.Universality.QUEFlow
import RBM3D.Universality.UnivMain
import RBM3D.Universality.NormBand
import RBM3D.Universality.GUELocalBootstrap
import RBM3D.Universality.GUELocalSchur

set_option linter.style.longLine false
set_option linter.unusedVariables false

/-! ## Part 3: proposals (NOT a gate; prefix `T2520_`, the final names drop it; bind after N2's 1a) -/

open MeasureTheory Filter Topology

noncomputable section

namespace RBM.Univ

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.BA RBM.Endpoints RBM.Univ.GUEPhase

/-! ### G1 `Universality/PinsKD` (1): the eight filtered pins = probe :38-86 (filter `Dm`, order `∀ d, Dm d → 3 ≤ d →`) -/

/-- G1: `UNQuekD` (merged `UNQuek`, PinsK:398, with the filter). -/
def T2520_UNQuekD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) : Prop :=
  ∀ d : ℕ, Dm d → 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ ε₀ c τ : ℝ, 0 < ε₀ → ε₀ < 𝔡 / 2 → 0 < c → c < ε₀ → c < 𝔡 / 5 → 0 < τ →
      ∀ᶠ n in atTop, ∀ E : ℝ, (K d).bulk sz κ E n → ∀ a : Zd d (sz.L n),
        ((K d).M sz).μ {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (((K d).M sz).H n ω)} ≤
          queBound (sz.W n) 𝔡 ε₀ c τ

/-- G1: `UNLocAvgkD` (merged `UNLocAvgk`, PinsK:406). -/
def T2520_UNLocAvgkD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) : Prop :=
  ∀ d : ℕ, Dm d → 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      ((K d).M sz).μ {ω | ∃ z : ℂ, ((K d).bulk sz κ z.re n ∧ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ z.im ∧ z.im ≤ 1) ∧
          ∃ a : Zd d (sz.L n),
          ((sz.W n : ℕ) : ℝ) ^ τ * sz.Bctl n (1 - z.im) <
            ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a,
                Gres (((K d).M sz).H n ω) z true x x - (K d).mdet sz n z‖} ≤
        ENNReal.ofReal (Nsz sz n ^ (-D))

/-- G1: `UNOUClaimskD` (merged `UNOUClaimsk`, PinsK:421). -/
def T2520_UNOUClaimskD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) : Prop :=
  ∀ d : ℕ, Dm d → 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → UNOUQUEk (K d) sz 𝔡 τU ∧ UNOUDiagk (K d) sz τU

/-- G1: `UNOURowkD` (merged `UNOURowk`, PinsK:426). -/
def T2520_UNOURowkD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) (ML Loc Que : Prop) : Prop :=
  ML → Loc → Que → T2520_UNOUClaimskD Dm K

/-- G1: `UNEMCTE2RowkD` (merged `UNEMCTE2Rowk`, PinsK:429). -/
def T2520_UNEMCTE2RowkD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) : Prop :=
  ∀ d : ℕ, Dm d → 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → ∀ nf : ℕ, ∃ Cn τ₀ : ℝ, 0 < τ₀ ∧
      ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → UNEMCTE2k (K d) sz E nf τU Cn

/-- G1: `UNJakUywRowkD` (merged `UNJakUywRowk`, PinsK:435; the claim it consumes is the filtered one). -/
def T2520_UNJakUywRowkD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) (Loc : Prop) : Prop :=
  Loc → T2520_UNOUClaimskD Dm K → ∀ d : ℕ, Dm d → 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → ∀ nf : ℕ, ∃ C τ₀ : ℝ, 0 < τ₀ ∧
      ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
        UNJakk (K d) sz E nf τU C (𝔠 * 𝔡 / 30) ∧ UNUywk (K d) sz E nf τU C (𝔠 * 𝔡 / 30)

/-- G1: `UNClaimRowkD` (merged `UNClaimRowk`, PinsK:442; hypothesis and conclusion filtered). -/
def T2520_UNClaimRowkD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) : Prop :=
  (∀ d : ℕ, Dm d → 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → ∀ nf : ℕ, ∃ Cn C τ₀ : ℝ, 0 < τ₀ ∧
      ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
        UNEMCTE2k (K d) sz E nf τU Cn ∧ UNJakk (K d) sz E nf τU C (𝔠 * 𝔡 / 30) ∧
          UNUywk (K d) sz E nf τU C (𝔠 * 𝔡 / 30)) →
  ∀ d : ℕ, Dm d → 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → UNClaimAllC sz ((K d).M sz) E

/-- G1: `UNG1RowkD` (merged `UNG1Rowk`, OUInterfaceK:101). -/
def T2520_UNG1RowkD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) (P : ∀ d, UNOUProfile (K d)) (ML Loc Que : Prop) : Prop :=
  ML → Loc → Que →
    ∀ d : ℕ, Dm d → 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ τU : ℝ, 0 < τU → τU ≤ ouTauMax 𝔠 𝔡 →
        UNOULLk (K d) sz τU ∧ UNOUEq747k (K d) (P d) sz 𝔡 τU

/-! ### G1 (2): MNO-C1, the band recovery at `Dm = fun _ => True` (probe :91-116) -/

def T2520_QuekD_true : Prop := ∀ (K : ∀ d, UNKind d), T2520_UNQuekD (fun _ => True) K ↔ UNQuek K
def T2520_LocAvgkD_true : Prop := ∀ (K : ∀ d, UNKind d), T2520_UNLocAvgkD (fun _ => True) K ↔ UNLocAvgk K
def T2520_OUClaimskD_true : Prop := ∀ (K : ∀ d, UNKind d), T2520_UNOUClaimskD (fun _ => True) K ↔ UNOUClaimsk K
def T2520_OURowkD_true : Prop :=
  ∀ (K : ∀ d, UNKind d) (ML Loc Que : Prop), T2520_UNOURowkD (fun _ => True) K ML Loc Que ↔ UNOURowk K ML Loc Que
def T2520_EMCTE2RowkD_true : Prop := ∀ (K : ∀ d, UNKind d), T2520_UNEMCTE2RowkD (fun _ => True) K ↔ UNEMCTE2Rowk K
def T2520_JakUywRowkD_true : Prop :=
  ∀ (K : ∀ d, UNKind d) (Loc : Prop), T2520_UNJakUywRowkD (fun _ => True) K Loc ↔ UNJakUywRowk K Loc
def T2520_ClaimRowkD_true : Prop := ∀ (K : ∀ d, UNKind d), T2520_UNClaimRowkD (fun _ => True) K ↔ UNClaimRowk K
def T2520_G1RowkD_true : Prop :=
  ∀ (K : ∀ d, UNKind d) (P : ∀ d, UNOUProfile (K d)) (ML Loc Que : Prop),
    T2520_UNG1RowkD (fun _ => True) K P ML Loc Que ↔ UNG1Rowk K P ML Loc Que
/-- The two band `Iff`s at `UNKind.band` (probe :113-116, with `UNLocAvgk_band` PinsK:554, `UNOURowk_band` :560). -/
def T2520_band_locAvg : Prop := T2520_UNLocAvgkD (fun _ => True) (fun d => UNKind.band d) ↔ UNLocAvgBand
def T2520_band_ouRow : Prop :=
  T2520_UNOURowkD (fun _ => True) (fun d => UNKind.band d) (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand ↔ UNOURow

/-! ### G2 `Universality/GUEPhase/RandomLayerBGD`: the filtered chain (statements of probe :120-188) -/

/-- G2: `un_claimAll_of_rowskD` (probe :120-132; merged `un_claimAll_of_rowsk` PinsK:454). -/
def T2520_ClaimAllOfRowskD : Prop :=
  ∀ (Dm : ℕ → Prop) (K : ∀ d, UNKind d) (ML Loc Que : Prop),
    T2520_UNClaimRowkD Dm K → T2520_UNEMCTE2RowkD Dm K → T2520_UNJakUywRowkD Dm K Loc →
      T2520_UNOURowkD Dm K ML Loc Que → ML → Loc → Que →
        ∀ d : ℕ, Dm d → 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
          ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → UNClaimAllC sz ((K d).M sz) E

/-- G2: `unClaimRowkD` (probe :134-140; merged `unClaimRowk` UnivMain:471). -/
def T2520_UnClaimRowkD : Prop := ∀ (Dm : ℕ → Prop) (K : ∀ d, UNKind d), T2520_UNClaimRowkD Dm K

/-- G2: `ouRowk_of_pinsD` (probe :152-158; merged `ouRowk_of_pins` OUInterfaceK:292). -/
def T2520_OuRowkOfPinsD : Prop :=
  ∀ (Dm : ℕ → Prop) (K : ∀ d, UNKind d) (P : ∀ d, UNOUProfile (K d)) (ML Loc Que : Prop),
    (∀ d : ℕ, Dm d → 3 ≤ d → UNOUProfRowk (K d) (P d)) →
      T2520_UNG1RowkD Dm K P ML Loc Que → UNG2bRowk K P → T2520_UNOURowkD Dm K ML Loc Que

/-- G2: `g1Rowk_of_inputsGD` (probe :160-174; merged `g1Rowk_of_inputsG` RandomLayerBG:399). -/
def T2520_G1RowkOfInputsGD : Prop :=
  ∀ (Dm : ℕ → Prop) (K : ∀ d, UNKind d) (P : ∀ d, UNOUProfile (K d)) (ML Loc Que : Prop)
    (Ed : ∀ d : ℕ, ℝ → Sizes d → ℕ → ℂ → Prop) (fE fT : ∀ d : ℕ, Sizes d → ℕ → ℂ → ℝ)
    (Fl : ∀ d : ℕ, Sizes d → ℝ → ℝ → ℝ → ℝ → (ℕ → ℂ) → Prop)
    (MO : ∀ d : ℕ, Sizes d → (ℕ → ℂ) → (ℕ → ℝ) → Prop)
    (KF PB : ∀ d : ℕ, ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) →
      (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop),
    (∀ d, Dm d → 3 ≤ d → RBG_Flow (K d) (Ed d) (fT d)) →
    (∀ d, Dm d → 3 ≤ d → RBG_Dom (K d) (Fl d)) →
    (∀ d, Dm d → 3 ≤ d → RBG_Comp (K d) (P d)) →
    (∀ d, Dm d → 3 ≤ d → RBG_Prod (Ed d) (fE d) (fT d) (MO d) (KF d) (PB d)) →
    (∀ d, Dm d → 3 ≤ d → RandomLayerB_LL (K d) (fE d) (fT d) (PB d)) →
    (∀ d, Dm d → 3 ≤ d → RBG_Que (K d) (P d) (Ed d) (fE d) (fT d) (MO d) (KF d) (PB d)) →
    (ML → ∀ d, Dm d → 3 ≤ d → RandomLayerB_MLout (fT d) (Fl d) (MO d)) →
    T2520_UNG1RowkD Dm K P ML Loc Que

/-! ### BA leaf `BA/UNBUniv` (1): the BA readings and the one-line links to M1's and M3's per-`d` texts (DECISIONS §340 (2)) -/

def T2520_UNLocAvgBAD (Dm : ℕ → Prop) : Prop := T2520_UNLocAvgkD Dm (fun d => UNKind.ba d)
def T2520_UNQueBAD (Dm : ℕ → Prop) : Prop := T2520_UNQuekD Dm (fun d => UNKind.ba d)
def T2520_UNOURowBAD (Dm : ℕ → Prop) : Prop :=
  T2520_UNOURowkD Dm (fun d => UNKind.ba d) (∀ d : ℕ, Dm d → UNMLOutBA d) (T2520_UNLocAvgBAD Dm) (T2520_UNQueBAD Dm)
def T2520_UNEMCTE2RowBAD (Dm : ℕ → Prop) : Prop := T2520_UNEMCTE2RowkD Dm (fun d => UNKind.ba d)
def T2520_UNJakUywRowBAD (Dm : ℕ → Prop) : Prop := T2520_UNJakUywRowkD Dm (fun d => UNKind.ba d) (T2520_UNLocAvgBAD Dm)
def T2520_UNClaimRowBAD (Dm : ℕ → Prop) : Prop := T2520_UNClaimRowkD Dm (fun d => UNKind.ba d)

/-- `unLocAvgBAD_iff_at`: the filtered BA reading at `Dm = (· = d)` is M1's per-`d` text `UNLocAvgBAAt` (MAPins:170). -/
def T2520_LocAvgAtIff : Prop := ∀ d : ℕ, T2520_UNLocAvgBAD (· = d) ↔ (3 ≤ d → UNLocAvgBAAt d)
/-- `unQueBAD_iff_at`: the same for M3's `UNQueBAAt` (MADecolQUE:52). -/
def T2520_QueAtIff : Prop := ∀ d : ℕ, T2520_UNQueBAD (· = d) ↔ (3 ≤ d → UNQueBAAt d)
/-- The TrLocal inputs of the assembly are the types of M1 row b's merged cores `unTrLocalBAAt_of_locAvg` (MATrLocalBA:80) and
`unTrLocalInitBAAt'_of_locAvg` (:237): they replace the probe's `T2513_TrLocalCore`, `T2513_TrLocalInitCore` (probe :242-251). -/
def T2520_TrLocalAt : Prop := ∀ d : ℕ, 3 ≤ d → UNLocAvgBAAt d → UNTrLocalBAAt d
def T2520_TrLocalInitAt : Prop := ∀ d : ℕ, 3 ≤ d → UNLocAvgBAAt d → UNTrLocalInitBAAt' d

/-! ### BA leaf (2): the filtered assembly (statements of probe :142-150, :266-288) -/

/-- `jakUywRowkD` (probe :142-150; merged `jakUywRowk` EMCTE2BA:629; it imports `BA/EMCTE2BA`, so it lives in the BA leaf). -/
def T2520_JakUywRowkD : Prop :=
  ∀ (Dm : ℕ → Prop) (K : ∀ d, UNKind d), UNBulkWindowk K → UNBadBoundk K → UNBad2Boundk K →
    ∀ Loc : Prop, T2520_UNJakUywRowkD Dm K Loc

/-- `un_claimAll_of_rowsBAD` (probe :266-271; merged `un_claimAll_of_rowsBA` UNPins:142). -/
def T2520_ClaimAllOfRowsBAD : Prop :=
  ∀ Dm : ℕ → Prop, T2520_UNClaimRowBAD Dm → T2520_UNEMCTE2RowBAD Dm → T2520_UNJakUywRowBAD Dm → T2520_UNOURowBAD Dm →
    (∀ d : ℕ, Dm d → UNMLOutBA d) → T2520_UNLocAvgBAD Dm → T2520_UNQueBAD Dm →
      ∀ d : ℕ, Dm d → 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
        ∀ E : ℝ, (∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E) → UNClaimAllC sz (UNModelC.ba sz) E

/-- `baBUniv_of_rowsD` (probe :273-288; merged `baBUniv_of_rows` UNPins:367), with the TrLocal inputs at M1 b's merged types. -/
def T2520_BaBUnivOfRowsD : Prop :=
  ∀ Dm : ℕ → Prop, UNCoreC'' → UNL32 → UNGUELocal → UNGreenCorrAllC → UNDensBARow' →
    T2520_TrLocalAt → T2520_TrLocalInitAt → UNNormBARow →
    T2520_UNClaimRowBAD Dm → T2520_UNEMCTE2RowBAD Dm → T2520_UNJakUywRowBAD Dm → T2520_UNOURowBAD Dm →
    (∀ d : ℕ, Dm d → UNMLOutBA d) → T2520_UNLocAvgBAD Dm → T2520_UNQueBAD Dm →
      ∀ d : ℕ, Dm d → BAEnd_BUnivL d

/-! ### BA leaf (3): N2's rows (concluded, so the scan needs no line for them) -/

/-- `unNormBARow_holds` (UNPins:190; twin `unNormBandRow` NormBand:173 at `sz.withLam 0`, plus the `λ Ψ` entries). -/
def T2520_NormBARow : Prop := UNNormBARow
/-- `unEMCTE2RowBAD_holds` (from `unEMCTE2RowBA_holds` EMCTE2BA:656; probe :310). -/
def T2520_EMCTE2RowBAD : Prop := ∀ Dm : ℕ → Prop, T2520_UNEMCTE2RowBAD Dm
/-- `unG1RowkBAD_holds` (probe :302-308 with C5's producers; filtered reading of `RandomLayerBGBA:199-212`). -/
def T2520_G1RowBAD : Prop :=
  ∀ Dm : ℕ → Prop, T2520_UNG1RowkD Dm (fun d => UNKind.ba d) (fun d => UNOUProfile.ba d) (∀ d : ℕ, Dm d → UNMLOutBA d)
    (T2520_UNLocAvgBAD Dm) (T2520_UNQueBAD Dm)
/-- `unOURowBAD_holds` (probe :312: `ouRowk_of_pinsD` with `baOUProfRowk_holds`, `g2bRowk`). -/
def T2520_OURowBAD : Prop := ∀ Dm : ℕ → Prop, T2520_UNOURowBAD Dm
/-- `unG1RowkBA_holds`, unfiltered (the merged reading `RandomLayerBGBA:199-212` with C5's names; needs C5's `∀ d` producers). -/
def T2520_G1RowBA : Prop :=
  UNG1Rowk (fun d => UNKind.ba d) (fun d => UNOUProfile.ba d) (∀ d : ℕ, UNMLOutBA d) UNLocAvgBA UNQueBA
/-- `unOURowBA_holds`: the merged `∀ d` implication `UNOURowBA` (UNPins:123; its premise `∀ d, UNMLOutBA d` stays a premise). -/
def T2520_OURowBA : Prop := UNOURowBA

/-! ### BA leaf (4): the end (MN-D3 D6, report `:162-168`; closing (vi)) -/

/-- `baEnd_BUnivL_of_ML` (per `d`, the `d > 3` form in hypothesis form, closing (vii)). -/
def T2520_BUnivOfML : Prop := ∀ d : ℕ, 3 ≤ d → UNL32 → UNMLOutBA d → BAEnd_BUnivL d
/-- `baThm27L_of_ML` (`BAThm27L` MAPins:126, conjuncts from `baEnd_decolL`, `baEnd_locSCL`, `baEnd_QUEL`, `baEnd_QDiffL`). -/
def T2520_Thm27OfML : Prop := ∀ d : ℕ, 3 ≤ d → UNL32 → UNMLOutBA d → BAThm27L d
/-- **D6 `baEnd_BUnivL_three`**, verbatim (report :164). -/
def T2520_BUnivThree : Prop := UNL32 → BAEnd_BUnivL 3
/-- **D6 `baThm27L_three`**, verbatim (report :165); the input of MA-06b. -/
def T2520_Thm27Three : Prop := UNL32 → BAThm27L 3
/-- Optional `baThm27L_any` (closing (iii), D723): the general `d` under Step 5 (iii), via `baMainIndFamTL_any` (MainIndTermBA:53). -/
def T2520_Thm27Any : Prop :=
  ∀ d : ℕ, 3 ≤ d →
    STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) → UNL32 → BAThm27L d

/-! ### C5 wiring at exact type, for the 1a probe before T2519 row d merges (copies of `T2519_ProdBA` `:28`, `T2519_LLBA` `:33`,
`T2519_QueBA` `:38`; at the 1b `KF := BAKFam`, `PB := BAPB`) -/

def T2520_C5ProdBA (KF PB : ∀ d : ℕ, ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) →
    (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop) : Prop :=
  ∀ d : ℕ, 3 ≤ d → RBG_Prod (BAEd d) (BAfE d) (BAfT d) (BAMO d) (KF d) (PB d)

def T2520_C5LLBA (PB : ∀ d : ℕ, ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) →
    (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop) : Prop :=
  ∀ d : ℕ, 3 ≤ d → RandomLayerB_LL (UNKind.ba d) (BAfE d) (BAfT d) (PB d)

def T2520_C5QueBA (KF PB : ∀ d : ℕ, ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) →
    (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop) : Prop :=
  ∀ d : ℕ, 3 ≤ d → RBG_Que (UNKind.ba d) (UNOUProfile.ba d) (BAEd d) (BAfE d) (BAfT d) (BAMO d) (KF d) (PB d)

/-- The unfiltered BA layer row from C5's `∀ d` producers (the 1a probe form of `unG1RowkBA_holds`). -/
def T2520_G1RowBAOfC5 : Prop :=
  ∀ KF PB : (∀ d : ℕ, ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop),
    T2520_C5ProdBA KF PB → T2520_C5LLBA PB → T2520_C5QueBA KF PB → T2520_G1RowBA

/-- D6 from C5's `∀ d` producers (the 1a probe form of `baThm27L_three`; `KF`, `PB` free, as `T2513_n2_three`, probe :294). -/
def T2520_Thm27ThreeOfC5 : Prop :=
  ∀ KF PB : (∀ d : ℕ, ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop),
    T2520_C5ProdBA KF PB → T2520_C5LLBA PB → T2520_C5QueBA KF PB → T2520_Thm27Three

/-- The same from the `d = 3` producers only (the hypotheses of `T2513_n2_three`, probe :299-301): the form N2 keeps if T2519's
1a-audit signs the producers at `d = 3` only (then `UNOURowBA` stays owed with the DECISIONS §316 wording). -/
def T2520_Thm27ThreeOfC5At3 : Prop :=
  ∀ KF PB : (∀ d : ℕ, ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop),
    RBG_Prod (BAEd 3) (BAfE 3) (BAfT 3) (BAMO 3) (KF 3) (PB 3) →
    RandomLayerB_LL (UNKind.ba 3) (BAfE 3) (BAfT 3) (PB 3) →
    RBG_Que (UNKind.ba 3) (UNOUProfile.ba 3) (BAEd 3) (BAfE 3) (BAfT 3) (BAMO 3) (KF 3) (PB 3) → T2520_Thm27Three

end RBM.Univ

end
