/-
Release check for T2475 (dispatcher V3, Mon Oct 12 21:29 UTC 2026; DECISIONS §278).  BA stage M/N row C5g (T2449 §1.3, row `:131`): the generic
repair of UN-51 (E5).  New generic file `Universality/GUEPhase/RandomLayerBG.lean` (no `BA/*` import): the primed inputs
`RBG_Flow`, `RBG_Dom`, `RBG_Prod`, `RBG_Que`, the compatibility input that replaces `RandomLayerB_Bulk`, and
`g1Rowk_of_inputsG` concluding the merged `UNG1Rowk`.  New BA leaf `BA/RandomLayerBGBA.lean`: the four BA instances of
supervisor 2049 GMN-C3 (`ba_dom_of_bulk`, `ba_flowG`, `ba_domG`, `ba_mlout`) and the BA half of the compatibility input.
Part 1: merged names.  Part 2: the probe texts as Prop values (prefix `T2475_`; content binding).  `T2475_RBG_*` are
`t/T2449:RBM3D/Probe/T2449Pins.lean:34-69` (commit 921369b) verbatim, names prefixed (the dispatcher compared the md5 of the copied lines with the
probe).  The BA statements are the probe's `:71-148` statements with `BAfT`, `BAfE` (`:87-89`) inlined.
Part 3: the design-gate proposals D1 (compatibility input) and D2 (`g1Rowk_of_inputsG`): NOT binding until the 1a-audit.
Part 4: shapes (not binding).
Merged names only.  No proofs.
Run: lake env lean docs/tickets/checks/T2475-check.lean
-/
import RBM3D.Main.BandTerminal
import RBM3D.Main.BUnivHolds
import RBM3D.BA.UNPins
import RBM3D.BA.MReg
import RBM3D.Universality.GUEPhase.RandomLayerB
import RBM3D.Induction.SizesComp
import Mathlib.Data.Nat.Nth

set_option linter.style.longLine false
set_option linter.unusedVariables false

/-! ## Part 1: merged names -/

-- UN-51 (band): the inputs T1-T6, their vocabulary, the generic result, the band discharges (`GUEPhase/RandomLayerB.lean`)
#check @RBM.Univ.GUEPhase.RandomLayerB_Flow
#check @RBM.Univ.GUEPhase.RandomLayerB_Dom
#check @RBM.Univ.GUEPhase.RandomLayerB_Bulk
#check @RBM.Univ.GUEPhase.RandomLayerB_MLout
#check @RBM.Univ.GUEPhase.RandomLayerB_Prod
#check @RBM.Univ.GUEPhase.RandomLayerB_LL
#check @RBM.Univ.GUEPhase.RandomLayerB_Que
#check @RBM.Univ.GUEPhase.RandomLayerB_LLAt
#check @RBM.Univ.GUEPhase.RandomLayerB_QueAt
#check @RBM.Univ.GUEPhase.RandomLayerB_KFam
#check @RBM.Univ.GUEPhase.RandomLayerB_PBband
#check @RBM.Univ.GUEPhase.RandomLayerB_Flband
#check @RBM.Univ.GUEPhase.RandomLayerB_MOband
#check @RBM.Univ.GUEPhase.g1Rowk_of_inputs
#check @RBM.Univ.GUEPhase.RandomLayerB_flow_band
#check @RBM.Univ.GUEPhase.RandomLayerB_dom_band
#check @RBM.Univ.GUEPhase.RandomLayerB_bulk_band
#check @RBM.Univ.GUEPhase.RandomLayerB_ML_band
#check @RBM.Univ.GUEPhase.RandomLayerB_prod_band
#check @RBM.Univ.GUEPhase.RandomLayerB_LL_band
#check @RBM.Univ.GUEPhase.RandomLayerB_Que_band
#check @RBM.Univ.GUEPhase.g1Rowk_band
#check @RBM.Univ.GUEPhase.RandomLayerBInst.inst_g1Rowk_of_inputs
-- the rows (`GUEPhase/RandomLayerA.lean`): `rows_flow` is copied and edited (E-f); `rowsLL`, `rowsQ` are reused
#check @RBM.Univ.GUEPhase.RandomLayer_lem28
#check @RBM.Univ.GUEPhase.RandomLayer_rows_flow
#check @RBM.Univ.GUEPhase.RandomLayer_rowsLL
#check @RBM.Univ.GUEPhase.RandomLayer_rowsQ
#check @RBM.Univ.GUEPhase.RandomLayer_etaLL_pos
#check @RBM.Univ.GUEPhase.RandomLayer_etaLL_le_one
#check @RBM.Univ.GUEPhase.gueScale
#check @RBM.Gauss.etaT
#check @RBM.lemE
#check @RBM.lemT
-- the conclusion and its readers (`OUInterfaceK.lean`, `BA/UNPins.lean`): unchanged
#check @RBM.Univ.UNG1Rowk
#check @RBM.Univ.UNOULLk
#check @RBM.Univ.UNOUEq747k
#check @RBM.Univ.UNG2bRowk
#check @RBM.Univ.UNOUProfRowk
#check @RBM.Univ.ouRowk_of_pins
#check @RBM.Univ.UNOURowBA
#check @RBM.Univ.baBUniv_of_rows
-- the kind, the profile, the carrier (`PinsK.lean`, `Pins.lean`, `ZeroModeProfile.lean`)
#check @RBM.Univ.UNKind
#check @RBM.Univ.UNKind.bulk
#check @RBM.Univ.UNKind.band
#check @RBM.Univ.UNOUProfile
#check @RBM.Univ.UNOUProfile.band
#check @RBM.Univ.UNModel
#check @RBM.Univ.UNModel.band
#check @RBM.Univ.UNModel.ba
#check @RBM.Univ.UNModelC
#check @RBM.Univ.ouMatC
#check @RBM.Univ.ouP
#check @RBM.Univ.Nsz
#check @RBM.Univ.ouTStar
#check @RBM.Univ.ouTauMax
#check @RBM.Univ.ouEtaQ
#check @RBM.Univ.ouEtaLL
#check @RBM.Univ.ouZeta
#check @RBM.Univ.profPMTilde
#check @RBM.Univ.profPPTilde
#check @RBM.Univ.UNMLOut
#check @RBM.Univ.UNLocAvgBand
#check @RBM.Univ.UNQueBand
-- the subsequence (`Induction/SizesComp.lean`; E-e)
#check @RBM.Gauss.Sizes.comp
#check @RBM.Gauss.Sizes.comp_L
#check @RBM.Gauss.Sizes.comp_lam
#check @RBM.Gauss.Sizes.comp_size
#check @RBM.Gauss.Sizes.withLam_comp
#check @RBM.Gauss.Sizes.comp_admissible
#check @RBM.Gauss.Sizes.reindex
#check @RBM.Gauss.Sizes.measurePreserving_reindex
#check @RBM.Gauss.Sizes.integral_reindex
#check @RBM.Gauss.Sizes.seqP_withLam_reindex_preimage
#check @RBM.Gauss.Sizes.seqXmat_reindex
#check @RBM.Gauss.Sizes.neZeroL
#check @Nat.nth_strictMono
#check @Nat.nth_mem_of_infinite
#check @Nat.frequently_atTop_iff_infinite
-- the BA kind and the BA inputs of the leaf (`BA/UNPins.lean`, `BA/MReg.lean`, `BA/MFixedPoint.lean`, `BA/FlowPins.lean`, `Chain/Carrier.lean`)
#check @RBM.Univ.UNKind.ba
#check @RBM.Univ.UNKind.ba_M
#check @RBM.Univ.UNModelC.ba
#check @RBM.Univ.UNMLOutBA
#check @RBM.Univ.UNLocAvgBA
#check @RBM.Univ.UNQueBA
#check @RBM.BA.BAm_im_lower_window
#check @RBM.BA.BAbulk
#check @RBM.BA.BAm
#check @RBM.BA.BAm_self
#check @RBM.BA.BAt0
#check @RBM.BA.BAt0_lt_one
#check @RBM.BA.BAflowE
#check @RBM.BA.BAReal
#check @RBM.BA.BAdom_real
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowEs
#check @RBM.BA.baFMz
#check @RBM.BA.STLKgL
#check @RBM.BA.STLocalEntrygL
#check @RBM.BA.STExp2gL
-- instance data (target 14; probe `:273-326`)
#check @RBM.Univ.BAInst.S0
#check @RBM.Univ.BAInst.S0_adm
#check @RBM.BA.UNPinsInst.fp
#check @RBM.BA.UNPinsInst.clsκ
#check @RBM.BA.UNPinsInst.clsκ_pos
#check @RBM.BA.UNPinsInst.cls_bulk
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_admissible
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.t0_sz0
-- the band terminal (acceptance: axioms unchanged)
#check @RBM.Endpoints.band_terminal
#check @RBM.Endpoints.bUniv_holds

/-! ## Part 2: the probe texts (content binding) -/

noncomputable section

namespace RBM.BA

open MeasureTheory Filter Topology
open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Univ RBM.Univ.GUEPhase RBM.Endpoints

section Generic

variable {d : ℕ}

-- Targets 1-4 (generic file): probe `:34-69` verbatim, names `RBG_*` read as `T2475_RBG_*`.
/-- `Flow′` (replaces `RandomLayerB_Flow` = T1, `:103`): `|fE| ≤ 2 - κ` ↦ `Ed κ'` at a margin `κ'`, `1/16 ≤ fT` ↦ `cT ≤ fT`, `etaT = √fT Im z` dropped. -/
def T2475_RBG_Flow (K : UNKind d) (Ed : ℝ → Sizes d → ℕ → ℂ → Prop) (fT : Sizes d → ℕ → ℂ → ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ κ' c cT : ℝ, 0 < κ' ∧ 0 < c ∧ 0 < cT ∧ ∀ (sz : Sizes d) (n : ℕ) (z : ℂ),
    K.bulk sz κ z.re n → 0 < z.im → z.im ≤ 1 →
      Ed κ' sz n z ∧ cT ≤ fT sz n z ∧ fT sz n z < 1 ∧ 1 - fT sz n z ≤ z.im / c
/-- `Dom′` (replaces `RandomLayerB_Dom`, `:111`): the flow domain `Fl` holds at a margin `κ'(κ)`. -/
def T2475_RBG_Dom (K : UNKind d) (Fl : Sizes d → ℝ → ℝ → ℝ → ℝ → (ℕ → ℂ) → Prop) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ κ' : ℝ, 0 < κ' ∧ ∀ (𝔠 𝔡 ε : ℝ) (sz : Sizes d), sz.Admissible 𝔠 𝔡 → 0 < ε → ∀ E η : ℕ → ℝ,
    (∀ n, K.bulk sz κ (E n) n) → (∀ n, Nsz sz n ^ (-1 + ε) ≤ η n) → (∀ n, η n ≤ 1) →
      Fl sz κ' ε 𝔠 𝔡 (fun n => (E n : ℂ) + (η n : ℂ) * Complex.I)
/-- `Prod′` (replaces `RandomLayerB_Prod` = T2, `:132`): `|fE| ≤ 2 - κ` ↦ `Ed κ'`; `etaT (fE) (fT)`, `gueScale` ↦ `√fT Im z`, `N √fT Im z`. -/
def T2475_RBG_Prod (Ed : ℝ → Sizes d → ℕ → ℂ → Prop) (fE fT : Sizes d → ℕ → ℂ → ℝ)
    (MO : ∀ _ : Sizes d, (ℕ → ℂ) → (ℕ → ℝ) → Prop)
    (KF PB : ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop) : Prop :=
  ∀ (𝔠 𝔡 κ' τD : ℝ) (sz : Sizes d), sz.Admissible 𝔠 𝔡 → 0 < κ' → 0 < τD → ∀ (z : ℕ → ℂ) (t1 : ℕ → ℝ),
    (∀ n, Ed κ' sz n (z n)) → (∀ n, 0 ≤ t1 n) → (∀ n, t1 n ≤ fT sz n (z n)) → (∀ n, fT sz n (z n) < 1) →
    (∀ᶠ n in atTop, fT sz n (z n) - t1 n ≤ Nsz sz n ^ (-τD) * (Real.sqrt (fT sz n (z n)) * (z n).im)) →
    (∀ᶠ n in atTop, (Nsz sz n * (Real.sqrt (fT sz n (z n)) * (z n).im))⁻¹ ≤ Nsz sz n ^ (-τD)) →
    (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2) →
    (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ 1) → MO sz z t1 →
    ∃ Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ,
      KF sz (fun n => fE sz n (z n)) t1 (fun n => fT sz n (z n)) Kt ∧
        PB sz (fun n => fE sz n (z n)) t1 (fun n => fT sz n (z n)) Kt
/-- `Que′` (replaces `RandomLayerB_Que` = T4, `:166`): `|fE| ≤ 2 - κ` ↦ `Ed κ'` at a margin `κ' > 0` (T4 has no `etaT`, `gueScale`). -/
def T2475_RBG_Que (K : UNKind d) (P : UNOUProfile K) (Ed : ℝ → Sizes d → ℕ → ℂ → Prop) (fE fT : Sizes d → ℕ → ℂ → ℝ)
    (MO : ∀ _ : Sizes d, (ℕ → ℂ) → (ℕ → ℝ) → Prop)
    (KF PB : ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop) : Prop :=
  ∀ (𝔠 𝔡 κ κ' τU : ℝ) (sz : Sizes d), sz.Admissible 𝔠 𝔡 → 0 < κ → 0 < κ' → 0 < τU → τU ≤ ouTauMax 𝔠 𝔡 →
    ∀ E t : ℕ → ℝ, (∀ n, K.bulk sz κ (E n) n) → (∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n) →
      ∀ z : ℕ → ℂ, (∀ᶠ n in atTop, z n = (E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) →
        (∀ n, Ed κ' sz n (z n) ∧ 0 ≤ (1 - ouZeta (t n)) * fT sz n (z n) ∧
          (1 - ouZeta (t n)) * fT sz n (z n) ≤ fT sz n (z n) ∧ fT sz n (z n) < 1) →
        ∀ Kt, KF sz (fun n => fE sz n (z n)) (fun n => (1 - ouZeta (t n)) * fT sz n (z n)) (fun n => fT sz n (z n)) Kt →
          MO sz z (fun n => (1 - ouZeta (t n)) * fT sz n (z n)) →
          PB sz (fun n => fE sz n (z n)) (fun n => (1 - ouZeta (t n)) * fT sz n (z n)) (fun n => fT sz n (z n)) Kt →
          ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, RandomLayerB_QueAt K P sz 𝔡 n (E n) (t n) τ

end Generic

/-- Target 5 helper (generic file; probe `:79`, `pad_subseq`, proved there in 8 lines): the padding along the subsequence
`Nat.nth` of the bad `n` that replaces `RandomLayerB_Bulk` (`RandomLayerB.lean:117`) and the private `RandomLayerB_pad`
(`:186`).  Statement only. -/
def T2475_PadSubseq : Prop :=
  ∀ S Q : ℕ → Prop, (∀ φ : ℕ → ℕ, StrictMono φ → (∀ j, S (φ j)) → ∀ᶠ j in atTop, Q (φ j)) → ∀ᶠ n in atTop, S n → Q n

/-- Target 8 (generic file; probe `:71`, `flowG_of_band`, proved there): the band keeps its T1. -/
def T2475_FlowGOfBand (d : ℕ) : Prop :=
  RandomLayerB_Flow (UNKind.band d) (fun _ _ z => lemE z) (fun _ _ z => lemT z) →
    T2475_RBG_Flow (UNKind.band d) (fun κ _ _ z => |lemE z| ≤ 2 - κ) (fun _ _ z => lemT z)

/-- The BA margin datum `Ed κ'` (probe `:91`, `BAEd`), with `BAfT d sz n w = BAt0 w (BAm d (sz.L n) (sz.lam n) w)` (`:87`)
and `BAfE d sz n w = BAflowE w (BAm d (sz.L n) (sz.lam n) w)` (`:89`) inlined. -/
def T2475_BAEd (d : ℕ) (κ' : ℝ) (sz : Sizes d) (n : ℕ) (w : ℂ) : Prop :=
  ∃ m₀ : ℂ, BAReal d (sz.L n) (Real.sqrt (BAt0 w (BAm d (sz.L n) (sz.lam n) w)) * sz.lam n) κ'
    (BAflowE w (BAm d (sz.L n) (sz.lam n) w)) m₀

/-- The BA `G`-loop outputs `MO` (probe `:94`, `BAMO`, verbatim up to the name): conjuncts 1, 5, 4 of `UNMLOutBA`. -/
def T2475_BAMO (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ) (t : ℕ → ℝ) : Prop :=
  STLKgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ∧ STLocalEntrygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ∧
    STExp2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t

/-- Target 9 (leaf; probe `:98`, `ba_dom_of_bulk`): the chain domain from the ρ-bulk, uniformly in `L`, `g`
(`BAm_im_lower_window`, `BA/MReg.lean:227`, at `x = E`). -/
def T2475_ba_dom_of_bulk : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g κ : ℝ), 0 < κ → ∀ {z : ℂ}, BAbulk d L g κ z.re → 0 < z.im → z.im ≤ 1 →
    (Real.pi * κ) ^ 5 / 2048 ≤ (BAm d L g z).im

/-- Target 10 (leaf; probe `:116`, `ba_flowG`): `Flow′` at `UNKind.ba`. -/
def T2475_ba_flowG (d : ℕ) : Prop :=
  T2475_RBG_Flow (UNKind.ba d) (T2475_BAEd d) (fun (sz : Sizes d) (n : ℕ) (w : ℂ) => BAt0 w (BAm d (sz.L n) (sz.lam n) w))

/-- Target 11 (leaf; probe `:131`, `ba_domG`): `Dom′` at `UNKind.ba`, `Fl = BAFlow`. -/
def T2475_ba_domG (d : ℕ) : Prop :=
  T2475_RBG_Dom (UNKind.ba d) (fun (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) => BAFlow sz κ ε 𝔠 𝔡 z)

/-- Target 12 (leaf; probe `:144`, `ba_mlout`): the merged T5 `RandomLayerB_MLout` (unchanged) at `Fl = BAFlow`,
`fT = BAt0`, `MO = BAMO`, from `UNMLOutBA`. -/
def T2475_ba_mlout (d : ℕ) : Prop :=
  3 ≤ d → UNMLOutBA d →
    RandomLayerB_MLout (fun (sz : Sizes d) (n : ℕ) (w : ℂ) => BAt0 w (BAm d (sz.L n) (sz.lam n) w))
      (fun (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) => BAFlow sz κ ε 𝔠 𝔡 z) (T2475_BAMO d)

/-! ## Part 3: design-gate proposals (D1, D2; NOT binding until the 1a-audit signs them) -/

section Proposals

variable {d : ℕ}

/-- **D1 proposal (target 5).**  The compatibility input that replaces `RandomLayerB_Bulk` (T2449 E-e): along a strictly
monotone `φ`, the bulk, `RandomLayerB_LLAt` and `RandomLayerB_QueAt` pass from `Sizes.comp φ` (`Induction/SizesComp.lean:55`)
back to `sz` at `φ j`.  Band: bulk definitional, the two integrals through `integral_reindex` (`:253`) on `ouP = μ.prod gueP`.
BA: the same with the law `seqP (sz.withLam 0)` (`seqP_withLam_reindex_preimage`, `:239`; `withLam_comp`, `:70`). -/
def T2475_RBG_Comp (K : UNKind d) (P : UNOUProfile K) : Prop :=
  ∀ (sz : Sizes d) (φ : ℕ → ℕ), StrictMono φ → ∀ j : ℕ,
    (∀ κ e : ℝ, K.bulk sz κ e (φ j) → K.bulk (sz.comp φ) κ e j) ∧
    (∀ (τU e s δ : ℝ) (p : ℕ),
      RandomLayerB_LLAt K (sz.comp φ) τU j e s δ p → RandomLayerB_LLAt K sz τU (φ j) e s δ p) ∧
    (∀ 𝔡 e s τ : ℝ, RandomLayerB_QueAt K P (sz.comp φ) 𝔡 j e s τ → RandomLayerB_QueAt K P sz 𝔡 (φ j) e s τ)

/-- **D1 proposal (profile half).**  The profile reads `sz` at the index only (band: `profPMTilde`, `profPPTilde`,
`ZeroModeProfile.lean:88, 93`).  At BA, C3 owes the profile `UNOUProfile.ba`, so the BA half of target 13 takes this as
a hypothesis. -/
def T2475_ProfComp (K : UNKind d) (P : UNOUProfile K) : Prop :=
  ∀ (sz : Sizes d) (φ : ℕ → ℕ) (j : ℕ) (ζ : ℝ) (z : ℂ) (a b : Zd d (sz.L (φ j))),
    P.pm (sz.comp φ) j ζ z a b = P.pm sz (φ j) ζ z a b ∧ P.pp (sz.comp φ) j ζ z a b = P.pp sz (φ j) ζ z a b

end Proposals

/-- **D2 proposal (target 7, `g1Rowk_of_inputsG`).**  The primed successor of `g1Rowk_of_inputs` (`RandomLayerB.lean:316`):
T1 ↦ `RBG_Flow` (margin datum `Ed`), T1′ ↦ `RBG_Dom`, T6 ↦ the compatibility input, T2 ↦ `RBG_Prod`, T3 unchanged,
T4 ↦ `RBG_Que`, T5 unchanged; the conclusion is the merged `UNG1Rowk` (`OUInterfaceK.lean:101`), unchanged. -/
def T2475_g1Rowk_of_inputsG : Prop :=
  ∀ (K : ∀ d, UNKind d) (P : ∀ d, UNOUProfile (K d)) (ML Loc Que : Prop)
    (Ed : ∀ d : ℕ, ℝ → Sizes d → ℕ → ℂ → Prop) (fE fT : ∀ d : ℕ, Sizes d → ℕ → ℂ → ℝ)
    (Fl : ∀ d : ℕ, Sizes d → ℝ → ℝ → ℝ → ℝ → (ℕ → ℂ) → Prop)
    (MO : ∀ d : ℕ, Sizes d → (ℕ → ℂ) → (ℕ → ℝ) → Prop)
    (KF PB : ∀ d : ℕ, ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) →
      (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop),
    (∀ d, 3 ≤ d → T2475_RBG_Flow (K d) (Ed d) (fT d)) →
    (∀ d, 3 ≤ d → T2475_RBG_Dom (K d) (Fl d)) →
    (∀ d, 3 ≤ d → T2475_RBG_Comp (K d) (P d)) →
    (∀ d, 3 ≤ d → T2475_RBG_Prod (Ed d) (fE d) (fT d) (MO d) (KF d) (PB d)) →
    (∀ d, 3 ≤ d → RandomLayerB_LL (K d) (fE d) (fT d) (PB d)) →
    (∀ d, 3 ≤ d → T2475_RBG_Que (K d) (P d) (Ed d) (fE d) (fT d) (MO d) (KF d) (PB d)) →
    (ML → ∀ d, 3 ≤ d → RandomLayerB_MLout (fT d) (Fl d) (MO d)) →
    UNG1Rowk K P ML Loc Que

/-! ## Part 4: shapes (not binding) -/

-- Target 13 (leaf): the BA half of the compatibility input, the profile half as a hypothesis (P is a variable until C3).
example : Prop := ∀ (d : ℕ) (P : UNOUProfile (UNKind.ba d)),
  T2475_ProfComp (UNKind.ba d) P → T2475_RBG_Comp (UNKind.ba d) P

-- Target 8 (generic): the band halves.
example : Prop := ∀ d : ℕ,
  T2475_ProfComp (UNKind.band d) (UNOUProfile.band d) ∧ T2475_RBG_Comp (UNKind.band d) (UNOUProfile.band d)

-- Target 8 (generic): band recovery of `Dom′` at the merged band domain (`RandomLayerB_dom_band`, `κ' = κ`).
example : Prop := ∀ d : ℕ, T2475_RBG_Dom (UNKind.band d) (RandomLayerB_Flband (d := d))

-- Target 8 (generic): band recovery of `Prod′` with one possible band datum `Ed` (the T1 identity `etaT = √t₀ Im z` carried
-- in `Ed`, so that `RandomLayerB_prod_band` applies; the 1a decides the band `Ed`).
example : Prop := ∀ d : ℕ, 3 ≤ d →
  T2475_RBG_Prod (fun (κ : ℝ) (_ : Sizes d) (_ : ℕ) (z : ℂ) => |lemE z| ≤ 2 - κ ∧ etaT (lemE z) (lemT z) = Real.sqrt (lemT z) * z.im)
    (fun _ _ z => lemE z) (fun _ _ z => lemT z) RandomLayerB_MOband (RandomLayerB_KFam (d := d)) (RandomLayerB_PBband (d := d))

-- Target 8 (generic): band recovery of `Que′` (`RandomLayerB_Que_band` at `min κ κ'`).
example : Prop := ∀ d : ℕ, 3 ≤ d →
  T2475_RBG_Que (UNKind.band d) (UNOUProfile.band d) (fun (κ : ℝ) (_ : Sizes d) (_ : ℕ) (z : ℂ) => |lemE z| ≤ 2 - κ)
    (fun _ _ z => lemE z) (fun _ _ z => lemT z) RandomLayerB_MOband (RandomLayerB_KFam (d := d)) (RandomLayerB_PBband (d := d))

-- Target 8 (generic): the band reading of D2 (nonvacuity instance at `sz0`, as `inst_g1Rowk_of_inputs`, `RandomLayerB.lean:497`).
example : Prop := T2475_g1Rowk_of_inputsG →
  UNG1Rowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d) (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand

-- The BA reading of D2 that N2 instantiates: targets 9-13 plus C5's producers (`Prod′`, LL, `Que′` at BA) and C3's profile.
example : Prop := ∀ (P : ∀ d, UNOUProfile (UNKind.ba d))
    (KF PB : ∀ d : ℕ, ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop),
  (∀ d, 3 ≤ d → T2475_ProfComp (UNKind.ba d) (P d)) →
  (∀ d, 3 ≤ d → T2475_RBG_Prod (T2475_BAEd d)
    (fun (sz : Sizes d) (n : ℕ) (w : ℂ) => BAflowE w (BAm d (sz.L n) (sz.lam n) w))
    (fun (sz : Sizes d) (n : ℕ) (w : ℂ) => BAt0 w (BAm d (sz.L n) (sz.lam n) w)) (T2475_BAMO d) (KF d) (PB d)) →
  (∀ d, 3 ≤ d → RandomLayerB_LL (UNKind.ba d)
    (fun (sz : Sizes d) (n : ℕ) (w : ℂ) => BAflowE w (BAm d (sz.L n) (sz.lam n) w))
    (fun (sz : Sizes d) (n : ℕ) (w : ℂ) => BAt0 w (BAm d (sz.L n) (sz.lam n) w)) (PB d)) →
  (∀ d, 3 ≤ d → T2475_RBG_Que (UNKind.ba d) (P d) (T2475_BAEd d)
    (fun (sz : Sizes d) (n : ℕ) (w : ℂ) => BAflowE w (BAm d (sz.L n) (sz.lam n) w))
    (fun (sz : Sizes d) (n : ℕ) (w : ℂ) => BAt0 w (BAm d (sz.L n) (sz.lam n) w)) (T2475_BAMO d) (KF d) (PB d)) →
  UNG1Rowk (fun d => UNKind.ba d) P (∀ d : ℕ, UNMLOutBA d) UNLocAvgBA UNQueBA

-- Targets 9-12 at `d = 3` together (instances: probe `:301-326`).
example : Prop := T2475_ba_dom_of_bulk ∧ T2475_ba_flowG 3 ∧ T2475_ba_domG 3 ∧ T2475_ba_mlout 3

end RBM.BA

end
