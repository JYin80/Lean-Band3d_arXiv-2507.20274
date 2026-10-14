/-
Release check for T2507 (dispatcher V4, 2026-10-14; DECISIONS §327 (3), §328; not compiled by the dispatcher).  U U3-BA (a): the BA
kernel layer of U3 (REQ-1418 `:44-49`; 1457 UBA-C1 (b), UBA-C2): class `BAEKKer`, the five `STEK*` forms at BA, the A-form Nonzero
lemma, the BA discharges of T2491 D1, T2498 D1, T2505 D1 (moved to U3-BA (b), Decision (2)) and of the `𝒦` time modulus (T2491 D2, `baKloop_lip`).
BA tuple `(fun sz => Sizes.seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`; `gK = BAflowLam0`; `Aof κ = (κ+1)/κ`.  Part 1: merged names
(`main` 3e514c5c).  Part 2: pins `T2507_*` (binding, except the section moved to U3-BA (b)), then shapes (not binding).  Row b's `T2507_KerNZ(Fam)` COPY `T2505_KerNZ(Fam)`
(`T2505-check.lean:154-167`, fixed at T2505 b's 1a-audit, §325 (2)); after T2505 b merges, row b's 1b reads the merged
`QtNZGen_KerNZFam` (`Chain/QtNonzeroGen`) by name and the auditor diffs it against the copy.  Statements only; merged modules only.
Run: lake env lean docs/tickets/checks/T2507-check.lean
-/
import RBM3D.Chain.Step34Gen
import RBM3D.Chain.Step2Kern
import RBM3D.Chain.NQGood1Gen
import RBM3D.Chain.NQEndFlowGen
import RBM3D.Chain.QEndB1Gen
import RBM3D.Chain.QtXiRoundLiftGen
import RBM3D.Chain.Step6KitGen
import RBM3D.Chain.ExpIniIGen
import RBM3D.Chain.ExpIntIIGen
import RBM3D.Induction.QProxy
import RBM3D.Induction.NQEndFlowLift
import RBM3D.Evolution.Prec
import RBM3D.BA.EKPins
import RBM3D.BA.EKSum
import RBM3D.BA.EKNonzero
import RBM3D.BA.TwistKer
import RBM3D.BA.TwistStep2
import RBM3D.BA.GreenSchur
import RBM3D.BA.EMn2BA
import RBM3D.BA.SEforLnBA
import RBM3D.BA.KBound
import RBM3D.BA.KSolve
import RBM3D.BA.KTreeRep
import RBM3D.BA.Step5KerBA
import RBM3D.BA.Step2BA
import RBM3D.BA.FlowPins

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- U3s1 = T2457 (`Chain/Step34Gen`): the class type, the five forms (D3), the vocabulary, the band instances, the UBA-C1 tools
#check @RBM.BA.STEKKer -- Chain/Step34Gen.lean:526
#check @RBM.BA.STEKSumNdecaygL -- Chain/Step34Gen.lean:529
#check @RBM.BA.STEKSumRes1gL -- Chain/Step34Gen.lean:540
#check @RBM.BA.STEKSumRes2NALgL -- Chain/Step34Gen.lean:552
#check @RBM.BA.STEKSumRes2gL -- Chain/Step34Gen.lean:563
#check @RBM.BA.STEKNonzerogL -- Chain/Step34Gen.lean:575
#check @RBM.BA.STEKWinKgL -- Chain/Step34Gen.lean:503
#check @RBM.BA.STEKDecaygL -- Chain/Step34Gen.lean:516
#check @RBM.BA.STEKLowgL -- Chain/Step34Gen.lean:521
#check @RBM.BA.stek_sumNdecaygL_band -- Chain/Step34Gen.lean:617
#check @RBM.BA.stek_nonzerogL_band -- Chain/Step34Gen.lean:644
#check @RBM.BA.step34Gen_winK_of_cmp -- Chain/Step34Gen.lean:683
#check @RBM.BA.step34Gen_decayK_of_cmp -- Chain/Step34Gen.lean:805
#check @RBM.BA.Step34Gen_LCompat -- Chain/Step34Gen.lean:164
#check @RBM.BA.Step34Gen_KCompat -- Chain/Step34Gen.lean:168
-- the band ≺ lifts (the shared core `prec_core`, `Evolution/Prec.lean:130`, is private and band-typed)
#check @RBM.Gauss.Sizes.stek_sumNdecay_holds -- Evolution/Prec.lean:215
#check @RBM.Gauss.Sizes.stek_nonzero_holds -- Evolution/Prec.lean:422
-- the kernel bridge (E-C1, U-C4)
#check @RBM.BA.Step2Kern_UN_BA -- Chain/Step2Kern.lean:124
-- U3s2 = T2491 D1, D2 and U3s3 = T2498 D1: the deterministic kernel classes and the `𝒦` modulus (BA owner U3-BA (a))
#check @RBM.BA.NQGoodGen_KerNAL -- Chain/NQGood1Gen.lean:54
#check @RBM.BA.NQGoodGen_KerNALFam -- Chain/NQGood1Gen.lean:67
#check @RBM.BA.NQGood1Gen_eta_anti -- Chain/NQGood1Gen.lean:437
#check @RBM.Ind.QProxyG_KerEK4 -- Induction/QProxy.lean:680
#check @RBM.Ind.QProxyG_KerEK4Fam -- Induction/QProxy.lean:692
#check @RBM.BA.NQEndFlowGen_KLipFam -- Chain/NQEndFlowGen.lean:215
#check @RBM.BA.nqEndFlowGen_kLip_band -- Chain/NQEndFlowGen.lean:222
#check @RBM.Gauss.Sizes.stKloop_lip -- Induction/NQEndFlowLift.lean:581
-- readers downstream (unchanged): U3-BA (b) and V1-BA
#check @RBM.BA.stOeqNQPTgL''_of -- Chain/NQEndFlowGen.lean:673
#check @RBM.BA.stOeqQtRoundPTgL''_of -- Chain/QEndB1Gen.lean:886
#check @RBM.BA.stXiRoundgL'_of_PTfam -- Chain/QtXiRoundLiftGen.lean:364
#check @RBM.BA.stOeqQtgL'_of -- Chain/QtXiRoundLiftGen.lean:466
#check @RBM.BA.st6_ini_sumNdecayg -- Chain/Step6KitGen.lean:365
#check @RBM.BA.ST_step6_caseII_of_pinsgL -- Chain/Step6KitGen.lean:746
#check @RBM.BA.stExpIniIgL'_of -- Chain/ExpIniIGen.lean:787
#check @RBM.BA.stExpIntIIgL_of -- Chain/ExpIntIIGen.lean:313
-- BA sources: stage E (deterministic pins at `BAUN`), TL's projected one-index factor, stage K, the flow data
#check @RBM.BA.BAUN -- BA/EKPins.lean:53
#check @RBM.BA.BAEKSumDecayNonzero -- BA/EKPins.lean:134
#check @RBM.BA.baEKSumNdecay_holds -- BA/EKPins.lean:218
#check @RBM.BA.baEKSumDecay1_holds -- BA/EKSum.lean:200
#check @RBM.BA.baEKSumDecayNAL_holds -- BA/EKSum.lean:290
#check @RBM.BA.baEKSumDecay2_holds -- BA/EKSum.lean:1772
#check @RBM.BA.baEKSumDecayNonzero_holds -- BA/EKNonzero.lean:261
#check @RBM.BA.baTwKerZero_holds -- BA/TwistKer.lean:256
#check @RBM.BA.baKBoundAt_holds -- BA/KBound.lean:85
#check @RBM.BA.BAKsol_isKLoopS -- BA/KSolve.lean:606
#check @RBM.BA.baKcac_isKLoopS -- BA/KTreeRep.lean:1674
#check @RBM.BA.baKLip_two -- BA/Step5KerBA.lean:476
#check @RBM.BA.BAReal -- BA/MFixedPoint.lean:432
#check @RBM.BA.BAmF -- BA/FlowPins.lean:252
#check @RBM.BA.baFM -- BA/FlowPins.lean:322
#check @RBM.BA.BAflowT0 -- BA/FlowPins.lean:380
#check @RBM.BA.BAflowLam0 -- BA/FlowPins.lean:386
#check @RBM.BA.BAFlow -- BA/FlowPins.lean:389
#check @RBM.BA.baFMz -- BA/FlowPins.lean:393
#check @RBM.BA.baStep2Mat -- BA/Step2BA.lean:54
#check @RBM.BA.BAflow_real -- BA/GreenSchur.lean:59
#check @RBM.BA.BAflow_lam0_window -- BA/GreenSchur.lean:72
#check @RBM.BA.TwistStep2_lam0_sq -- BA/TwistStep2.lean:740
#check @RBM.BA.EMn2BA_one_sub_T0 -- BA/EMn2BA.lean:111
#check @RBM.BA.EMn2BA_mF_data -- BA/EMn2BA.lean:125
-- covered REQ items (no target): `LCompat`/`KCompat` at `baStep2Mat` (T2486), `η` antitone via `LoopForm` (U-D P7)
#check @RBM.BA.baStep34_LCompat -- BA/SEforLnBA.lean:122
#check @RBM.BA.baStep34_KCompat -- BA/SEforLnBA.lean:129
#check @RBM.BA.baStep2Mat_loopForm -- BA/SEforLnBA.lean:135
-- `d = 3` data
#check @RBM.Gauss.SizesInst.sz0 -- Defs/Sizes.lean:260
#check @RBM.BA.FlowPinsInst.zSeq -- BA/FlowPins.lean:1181
#check @RBM.BA.FlowPinsInst.flow_sz0 -- BA/FlowPins.lean:1214

/-! ## Part 2: the target statements (prefix `T2507_`), then shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ### Row a (`t/T2507`, `BA/EKGenBA`, `BA/KLipBA`) -/

/-- **Target 1, `BAEKKer`** (binding; the only new public `def`; 1457 UBA-C2: no `0 < lam0 n ≤ Λ` field, the window is the forms'
own `∀ᶠ n, 0 < gK n ∧ gK n ≤ 𝔡⁻¹`; the class carries `gK = lam0`).  Its type is `STEKKer d` (read as `@BAEKKer d`). -/
def T2507_EKKer {d : ℕ} (sz : Sizes d) (C : FlowFM sz) (gK : ℕ → ℝ) (κ : ℝ) : Prop :=
  ∃ E : ℕ → ℝ, C = baFM sz gK E ∧ ∀ n, BAReal d (sz.L n) (gK n) κ (E n) (BAmF sz gK E n)

/-- **Target 2, `baEKKer_flow`** (binding): the `hKer` bundle of `ST_step6_caseII_of_pinsgL` (`Step6KitGen:752-754`),
`stExpIniIgL'_of` (`ExpIniIGen:794-796`), `stExpIntIIgL_of` (`ExpIntIIGen:318-320`) at the BA family, `Aof κm = (κm+1)/κm`. -/
def T2507_KerFlowBA (d : ℕ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, 0 < κm ∧ ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    (∀ n, κm ≤ ((baFMz sz z).m n).im) ∧ T2507_EKKer sz (baFMz sz z) (BAflowLam0 sz z) κm ∧
      (∀ᶠ n in atTop, 0 < BAflowLam0 sz z n ∧ BAflowLam0 sz z n ≤ 𝔡⁻¹) ∧
      ∀ n, 0 ≤ BAflowLam0 sz z n * sz.lam n ∧ BAflowLam0 sz z n ^ 2 ≤ sz.lam n ^ 2 ∧
        sz.lam n ^ 2 ≤ (κm + 1) / κm * BAflowLam0 sz z n ^ 2

/-- **Target 3 (a), `baEKSumNdecaygL_holds`** (binding). -/
def T2507_SumNdecayBA (d : ℕ) : Prop :=
  STEKSumNdecaygL d (fun sz => Sizes.seqP (sz.withLam 0)) (@T2507_EKKer d)

/-- **Target 3 (b), `baEKSumRes1gL_holds`** (binding). -/
def T2507_SumRes1BA (d : ℕ) : Prop :=
  STEKSumRes1gL d (fun sz => Sizes.seqP (sz.withLam 0)) (@T2507_EKKer d)

/-- **Target 3 (c), `baEKSumRes2NALgL_holds`** (binding). -/
def T2507_SumRes2NALBA (d : ℕ) : Prop :=
  STEKSumRes2NALgL d (fun sz => Sizes.seqP (sz.withLam 0)) (@T2507_EKKer d)

/-- **Target 3 (d), `baEKSumRes2gL_holds`** (binding). -/
def T2507_SumRes2BA (d : ℕ) : Prop :=
  STEKSumRes2gL d (fun sz => Sizes.seqP (sz.withLam 0)) (@T2507_EKKer d)

/-- **Target 3 (e), `baEKNonzerogL_holds`** (binding; every `Aof`, the A-form of UBA-C1 (b); the readers take `Aof κ = (κ+1)/κ`). -/
def T2507_NonzeroBA (d : ℕ) : Prop :=
  ∀ Aof : ℝ → ℝ, STEKNonzerogL d (fun sz => Sizes.seqP (sz.withLam 0)) (@T2507_EKKer d) Aof

/-- **Target 4, `baEKSumDecayNonzeroA_holds`** (binding; the theorem states `∀ d n Λ κ, T2507_EKNonzeroA d n Λ κ` inline, no new
`def`): `BAEKSumDecayNonzero` (`EKPins:134`) with the threshold `1 - g²/L² ≤ s` replaced by `(1 - s) L² ≤ A g²`, every `A > 0`
(`BATwKerZero`'s range).  The one BA lemma behind targets 3 (e) and 7 (DECISIONS §323 (1) (3)). -/
def T2507_EKNonzeroA (d n : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ → ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ s t : ℝ, 0 ≤ s → (1 - s) * (L : ℝ) ^ 2 ≤ A * g ^ 2 → s ≤ t → t < 1 →
      ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ σ : Fin n → Bool, ∀ Aset : Finset (Fin n), (∀ i, σ i ≠ σ (finRotate n i) → i ∈ Aset) →
          ∀ 𝒜 : (Fin n → Zd d L) → ℂ, ‖zeroModeSet d L Aset (BAUN d L g E m σ s t 𝒜)‖ ≤ C * ‖𝒜‖

/-- **Target 5 (a), `baNQGoodGen_kerNAL`** (binding): T2491 D1 at the BA family (`Ck` from `baEKSumDecayNAL_holds d k 𝔡⁻¹ κ`). -/
def T2507_KerNALBA (d : ℕ) : Prop :=
  NQGoodGen_KerNALFam d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowLam0 sz z)

/-- **Target 5 (b), `baQProxyG_kerEK4`** (binding): T2498 D1 at the BA family (`C4` from `baEKSumDecay2_holds d k 𝔡⁻¹ κ KL`). -/
def T2507_KerEK4BA (d : ℕ) : Prop :=
  RBM.Ind.QProxyG_KerEK4Fam d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowLam0 sz z)

/-- **Target 6, `baKloop_lip`** (binding): T2491 D2 (T2505 family row 15) at the BA family, every `k ≥ 2` (the twin of `stKloop_lip`;
`baKLip_two` is its `k = 2` case). -/
def T2507_KLipBA (d : ℕ) : Prop :=
  NQEndFlowGen_KLipFam d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)

/-! ### Moved to U3-BA (b) (T2507 Decision (2), DECISIONS §328): the D1 text at BA, NOT binding for T2507 -/

/-- Copy of `T2505_KerNZ` (`T2505-check.lean:154-160`; merged name will be `QtNZGen_KerNZ`, `Chain/QtNonzeroGen`). -/
def T2507_KerNZ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (gK : ℕ → ℝ) (k : ℕ) (A C5 : ℝ) (n : ℕ) : Prop :=
  ∀ v w : ℝ, 0 ≤ v → (1 - v) * ((sz.L n : ℕ) : ℝ) ^ 2 ≤ A * gK n ^ 2 → v ≤ w → w < 1 →
    ∀ (σ : Fin k → Bool) (Aset : Finset (Fin k)), (∀ i, σ i ≠ σ (finRotate k i) → i ∈ Aset) →
      ∀ X : (Fin k → Zd d (sz.L n)) → ℂ, ‖zeroModeSet d (sz.L n) Aset (Step2Gen_UN C n σ v w X)‖ ≤ C5 * ‖X‖

/-- Copy of `T2505_KerNZFam` (`T2505-check.lean:162-167`; merged name will be `QtNZGen_KerNZFam`). -/
def T2507_KerNZFam (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (Aof : ℝ → ℝ) : Prop :=
  3 ≤ d → ∀ k : ℕ, 2 ≤ k → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C5 : ℝ, 0 < C5 ∧
    ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, T2507_KerNZ (mk sz z) (gK sz z) k (Aof κ) C5 n

/-- **Target 7, `baQtNZGen_kerNZ`** (binding; at the merged `QtNZGen_KerNZFam` once T2505 b merges): T2505 D1 (family row 14) at the
BA family, `Aof κ = (κ+1)/κ`, `C5` from target 4 at `Λ = 𝔡⁻¹`. -/
def T2507_KerNZBA (d : ℕ) : Prop :=
  T2507_KerNZFam d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowLam0 sz z)
    (fun κ => (κ + 1) / κ)

/-! ### Shapes (not binding) -/

/-- U-D P7 (`baEta_antitone`), covered: `NQGood1Gen_eta_anti (baStep2Mat_loopForm d sz κ ε 𝔠 𝔡 z hκ hflow) n hu` (row a: `example`). -/
def T2507_shape_EtaAnti : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → ∀ (n : ℕ) (u u' : ℝ), u ≤ u' →
    (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).eta n u' ≤ (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).eta n u

/-- REQ-1418 `:48` (`LCompat`/`KCompat` at `baStep2Mat`), covered by `baStep34_LCompat`, `baStep34_KCompat` (T2486). -/
def T2507_shape_Compat : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ),
    Step34Gen_LCompat (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (sz.seqHflowBA (BAflowLam0 sz z)) ∧
      Step34Gen_KCompat (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))

end RBM.BA

end
