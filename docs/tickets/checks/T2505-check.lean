/-
Release check for T2505 (dispatcher V4, 2026-10-14; DECISIONS §323; not compiled by the dispatcher).  U U3s4 (sub-stage U, ST side): the Step 3 `Qt`
layer over the flow carrier: case (i) `lem:STOeq_Qt` (the uniform round from U3s3's per-time round, then the bootstrap) and case (ii)
`lem:STOeq_Qt_nonzero`.  Layout: NEW FILES (UP-C2 at ×2.54, 0843): row a `Chain/QtBootGen`, `Chain/QtXiRoundLiftGen`; row b
`Chain/QtNonzeroGen`, `Chain/QtNonzeroEndGen`; row c `Chain/QtNonzeroFlowGen`, `Chain/QtNonzeroBootGen`.  The six band files are not edited.
Part 1: merged names (`file:line` on `main` de05a3b1).  Part 2: the target statements as Prop values (prefix `T2505_`).  Binding:
`T2505_XiRoundgL'`, `T2505_NZConclPTgL''`, `T2505_OeqNZPTgL''`, `T2505_NZConclgL''`, `T2505_OeqNZgL''`, the conclusion of
`T2505_XiBootROfRound` (its bundle `Hyp` is fixed at row a's 1a).  Targets 4 and 14 conclude the merged T2491 pins `STOeqQtgL'`,
`STOeqQtNZgL'` (read under their names, never restated).  Design-gate default (fixed at row b's 1a-audit): D1 `T2505_KerNZ`,
`T2505_KerNZFam`.  `T2505_FlowModFam` copies the merged U4s3 hypothesis text (family row 16).  Shapes at the end are not binding.
Statements only; merged modules only.  Run: lake env lean docs/tickets/checks/T2505-check.lean
-/
import RBM3D.Induction.QtXiRoundLift
import RBM3D.Chain.QEndB1Gen
import RBM3D.BA.EKNonzero
import RBM3D.BA.TwistKer
import RBM3D.BA.Step5KerBA
import RBM3D.BA.B45BA

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the carrier, the kernel (U-C4), the setting and the A-form Nonzero pin (U3s1)
#check @RBM.BA.FlowFM -- Chain/Carrier.lean:55
#check @RBM.BA.Step2Gen_UN -- Chain/Step2Gen.lean:202
#check @RBM.BA.STIngRgL -- Chain/Step34Gen.lean:373
#check @RBM.BA.STEKNonzerogL -- Chain/Step34Gen.lean:575
#check @RBM.BA.StepDecompGen_LoopForm -- Chain/StepDecompGen.lean:60
-- U3s2c (`Chain/NQEndFlowGen`): the pins this row proves, the `𝒦` modulus (family row 15)
#check @RBM.BA.STXiBootgL' -- Chain/NQEndFlowGen.lean:57
#check @RBM.BA.STOeqQtgL' -- Chain/NQEndFlowGen.lean:110
#check @RBM.BA.STOeqQtNZgL' -- Chain/NQEndFlowGen.lean:116
#check @RBM.BA.NQEndFlowGen_KLipFam -- Chain/NQEndFlowGen.lean:215
#check @RBM.BA.nqEndFlowGen_kLip_band -- Chain/NQEndFlowGen.lean:222
-- U3s3c (`Chain/QEndB1Gen`, 39db8072): the per-time round read in target 4
#check @RBM.BA.STXiRoundPTgL'' -- Chain/QEndB1Gen.lean:67
#check @RBM.BA.STOeqQtRoundPTgL'' -- Chain/QEndB1Gen.lean:80
#check @RBM.BA.stOeqQtRoundPTgL''_of -- Chain/QEndB1Gen.lean:886
-- U3s2a/b, T4s2: good events, exit time, assembly, drift envelope (UP-C4)
#check @RBM.BA.gridGoodNgL_of -- Chain/GridGoodGen.lean:839
#check @RBM.BA.nqLinGoodgL_of -- Chain/NQLinGen.lean:358
#check @RBM.BA.assembledNg -- Chain/GridAssemblyGen.lean:807
#check @RBM.BA.gridDriftNg_envelope_ev -- Chain/NQEndLinGen.lean:93
-- U1s1 (`Chain/ZeroModeGen`), U2 (`Chain/B45Gen`): commutation, `newPQ`, the carrier facts (`KerSums`, `WardCls`)
#check @RBM.BA.zeroModeSet_UNg -- Chain/ZeroModeGen.lean:161
#check @RBM.BA.zeroModeCalc_LK_expansion_emptyg -- Chain/ZeroModeGen.lean:364
#check @RBM.BA.B45Gen_Facts -- Chain/B45Gen.lean:61
-- U4s3 (`Induction/LemDecCalELip`): the `𝓛` modulus (family row 16)
#check @RBM.Gauss.Sizes.LemDecCalELipG_FlowMod -- Induction/LemDecCalELip.lean:311
#check @RBM.Gauss.Sizes.lemDecCalELipG_flowMod_band -- Induction/LemDecCalELip.lean:355
#check @RBM.Gauss.Sizes.LemDecCalELip_Lloop_subg -- Induction/LemDecCalELip.lean:434
-- band sources (unedited; `Step3`, `Step4` read the first two)
#check @RBM.Ind.stOeqQt'_holds -- Induction/QtXiRoundLift.lean:736
#check @RBM.Ind.stOeqQtNZ'_holds -- Induction/QtNonzeroBoot.lean:1074
#check @RBM.Gauss.Sizes.STXiRound' -- Induction/QtNonzeroBoot.lean:92
#check @RBM.Gauss.Sizes.STNZConclPT'' -- Induction/QtNonzeroFlow.lean:75
#check @RBM.Gauss.Sizes.STNZConcl'' -- Induction/QtNonzeroFlowLift.lean:68
#check @RBM.Ind.nzUgen_holds -- Induction/QtNonzero.lean:299
#check @RBM.Ind.nzGridEndN -- Induction/QtNonzeroEnd.lean:979
-- BA sources of the family premises (read only; owners U3-BA (a)/(b), T2501)
#check @RBM.BA.BAEKSumDecayNonzero -- BA/EKPins.lean:134
#check @RBM.BA.baEKSumDecayNonzero_holds -- BA/EKNonzero.lean:261
#check @RBM.BA.baTwKerZero_holds -- BA/TwistKer.lean:256
#check @RBM.BA.baLemDecCalELipG_flowMod -- BA/Step5KerBA.lean:390
#check @RBM.BA.baB45Gen_facts -- BA/B45BA.lean:205
#check @RBM.BA.baStep2Mat -- BA/Step2BA.lean:54
#check @RBM.BA.BAFlow -- BA/FlowPins.lean:389
#check @RBM.BA.baFMz -- BA/FlowPins.lean:393
#check @RBM.BA.BAflowLam0 -- BA/FlowPins.lean:386
#check @RBM.BA.BAflowEs -- BA/FlowPins.lean:383

/-! ## Part 2: the target statements, then shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 1, `STXiRoundgL'`** (binding; band `STXiRound'`, `QtNonzeroBoot.lean:92`): `STXiBootgL'` with `m ≤ n_` in the `XLK`
hypotheses and the summand `B_u^{1/6} XLK n_ u`; the merged `STXiRoundPTgL''` with `PrecPTL` replaced with `PrecL`. -/
def T2505_XiRoundgL' {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 n_ ω)
      (fun n q _ => sz.Bctl n q.1.2 ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
        STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p)

/-- **Target 10, `STNZConclPTgL''`** (binding; band `STNZConclPT''`, `QtNonzeroFlow.lean:75`): the merged `STNQConclPTgL''` with the
index set "every `σ`, every `A ⊇ I_diff(σ)`" and the quantity `‖(Q^{(A)}(𝓛 - 𝒦)^{(n_)})_{u,σ,a}‖`. -/
def T2505_NZConclPTgL'' {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    PrecPTL sz μ (U := fun n => TimeIcc s t n × {σA : (Fin n_ → Bool) × Finset (Fin n_) // STIdiff σA.1 ⊆ σA.2} ×
        (Fin n_ → Zd d (sz.L n)))
      (fun n q ω => ‖zeroModeSet d (sz.L n) q.2.1.1.2
          (fun b : Fin n_ → Zd d (sz.L n) => Cf.L n (q.1 : ℝ) q.2.1.1.1 b ω - Cf.K n (q.1 : ℝ) q.2.1.1.1 b) q.2.2‖ /
        (sz.Bctl n (q.1 : ℝ)) ^ n_)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n (q.1 : ℝ) +
        STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (s n)) n_ p)

/-- **Target 10, `STOeqNZPTgL''`** (binding; band `STOeqNZPT''`, `QtNonzeroFlow.lean:95`): case (ii) setting of a carrier family. -/
def T2505_OeqNZPTgL'' (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngRgL d STCaseII law Flow mk T0 (fun sz z s t => T2505_NZConclPTgL'' (mk sz z) (law sz) s t)

/-- **Target 10, `STNZConclgL''`** (binding; band `STNZConcl''`, `QtNonzeroFlowLift.lean:68`): `T2505_NZConclPTgL''` with `PrecL`. -/
def T2505_NZConclgL'' {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    PrecL sz μ (U := fun n => TimeIcc s t n × {σA : (Fin n_ → Bool) × Finset (Fin n_) // STIdiff σA.1 ⊆ σA.2} ×
        (Fin n_ → Zd d (sz.L n)))
      (fun n q ω => ‖zeroModeSet d (sz.L n) q.2.1.1.2
          (fun b : Fin n_ → Zd d (sz.L n) => Cf.L n (q.1 : ℝ) q.2.1.1.1 b ω - Cf.K n (q.1 : ℝ) q.2.1.1.1 b) q.2.2‖ /
        (sz.Bctl n (q.1 : ℝ)) ^ n_)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n (q.1 : ℝ) +
        STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (s n)) n_ p)

/-- **Target 10, `STOeqNZgL''`** (binding; band `STOeqNZ''`, `QtNonzeroFlowLift.lean:88`). -/
def T2505_OeqNZgL'' (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngRgL d STCaseII law Flow mk T0 (fun sz z s t => T2505_NZConclgL'' (mk sz z) (law sz) s t)

/-- **Target 2, `stXiBootRgL'_of_round`** (conclusion binding; `Hyp` = the flow premises of the crude start and the contraction, fixed
at row a's 1a; band `stXiBootR_of_round`, `QtNonzeroBoot.lean:581`): regime-free, the regime `R` a parameter. -/
def T2505_XiBootROfRound
    (Hyp : ∀ (d : ℕ), (∀ sz : Sizes d, Measure sz.SeqΩ) → (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) →
      (∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) → (∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) → Prop) : Prop :=
  ∀ (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ), Hyp d law Flow mkM T0 →
    STIngRgL d R law Flow (fun sz z => (mkM sz z).toFlowFM) T0
        (fun sz z s t => T2505_XiRoundgL' (mkM sz z).toFlowFM (law sz) s t) →
      STIngRgL d R law Flow (fun sz z => (mkM sz z).toFlowFM) T0
        (fun sz z s t => STXiBootgL' (mkM sz z).toFlowFM (law sz) s t)

/-- **D1 default, `QtNZGen_KerNZ`** (text fixed at row b's 1a-audit): `lem:sum_decay_nonzero` (`3_5:1666`), loss-free (EK-5), for the
carrier kernel at index `n`, every `σ` and `Aset ⊇ I_diff(σ)`, in the A-form window `(1 - v) L² ≤ A gK²` (UBA-C1 (b)).  Band: `nzUgen_holds`
(`A = 1`, `gK = sz.lam`); BA: U3-BA (a), `baEKSumDecayNonzero_holds` with `baTwKerZero_holds` (`A = (κ+1)/κ`). -/
def T2505_KerNZ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (gK : ℕ → ℝ) (k : ℕ) (A C5 : ℝ) (n : ℕ) : Prop :=
  ∀ v w : ℝ, 0 ≤ v → (1 - v) * ((sz.L n : ℕ) : ℝ) ^ 2 ≤ A * gK n ^ 2 → v ≤ w → w < 1 →
    ∀ (σ : Fin k → Bool) (Aset : Finset (Fin k)), (∀ i, σ i ≠ σ (finRotate k i) → i ∈ Aset) →
      ∀ X : (Fin k → Zd d (sz.L n)) → ℂ, ‖zeroModeSet d (sz.L n) Aset (Step2Gen_UN C n σ v w X)‖ ≤ C5 * ‖X‖

/-- **D1 default, the family form** (guarded; `∃ C5` after `(k, κ, 𝔡)`, before `(sz, z)`: U5S-C3; per index, eventually in `n`). -/
def T2505_KerNZFam (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (Aof : ℝ → ℝ) : Prop :=
  3 ≤ d → ∀ k : ℕ, 2 ≤ k → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C5 : ℝ, 0 < C5 ∧
    ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, T2505_KerNZ (mk sz z) (gK sz z) k (Aof κ) C5 n

/-- **Family row 16** (the merged U4s3 hypothesis text `hFM`, `DuhamelII.lean:726-727`, copied; no new class): the flow modulus of `𝓛`. -/
def T2505_FlowModFam (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ c : ℝ, 0 ≤ c ∧
    ∀ (sz : Sizes d) (𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → LemDecCalELipG_FlowMod (mkM sz z) (law sz) c

/-! ### Shapes (not binding): band and BA readings (BA: U3-BA, statement level only) -/

/-- Band reading of target 10 (the bridge goes through `bandFM_STIngR`; the band file `QtNonzeroFlow` is not edited). -/
def T2505_shape_bandNZPT : Prop := ∀ d : ℕ,
  STOeqNZPT'' d ↔ T2505_OeqNZPTgL'' d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))

/-- D1 at the band family (`Aof = 1`, `gK = sz.lam`) and at the BA family (`Aof κ = (κ+1)/κ`, `gK = BAflowLam0`; U3-BA (a)). -/
def T2505_shape_KerNZ : Prop := ∀ d : ℕ,
  T2505_KerNZFam d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun sz _ => sz.lam) (fun _ => 1) ∧
    T2505_KerNZFam d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowLam0 sz z)
      (fun κ => (κ + 1) / κ)

/-- Row 16 at BA (the statement of the merged `baLemDecCalELipG_flowMod`) and targets 4, 14 at the BA family (U3-BA). -/
def T2505_shape_BA : Prop := ∀ d : ℕ,
  T2505_FlowModFam d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) ∧
    STOeqQtgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) ∧
    STOeqQtNZgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z)

end RBM.BA

end
