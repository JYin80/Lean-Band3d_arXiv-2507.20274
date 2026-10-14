/-
Release check for T2498 (dispatcher V4, 2026-10-14; DECISIONS §310, drafted under §299).  U U3s3 (sub-stage U, ST side): the Step 3 `Q*` layer
(`lem:STOeq_Qt`, alternating signs, `(eq:alternatecase1)`) over the flow carrier.  Layout (UP-C2, ×1.74 sensitivity price kept it, DECISIONS §308 (2), §310): mixed.  In place (row a):
`Induction/QProxy`, `QDriftA`, `QDriftB`, `QLevelsA`, `QLevelsB`, `QBudgetA`, `QBudgetB`, `QEndA`, with the instance siblings
`Induction/QProxy2`, `QEndA2` (new).  New files: `Chain/QEndGridGen` (row b), `Chain/QEndB1Gen` (row c).  `Induction/QEndGrid` and
`Induction/QEndB1` stay band, unedited.
Part 1: merged names.  Part 2: the target statements as Prop values (prefix `T2498_`).  Binding: `T2498_XiRoundPTgL''`,
`T2498_OeqQtRoundPTgL''` and the conclusion of `T2498_OeqQtRoundPTOf` (its hypothesis bundle is a shape fixed at the 1a-audit).
Design-gate default (text fixed at the 1a-audit): D1 `T2498_KerEK4`, `T2498_KerEK4Fam`.  The comparison is the R1 text
`T2491_R1Fam` of `docs/tickets/checks/T2491-check.lean` (one text, not restated here).  D2 (the eventual envelope of the
`𝒬`-remainder) is stated against T2497's merged `Chain/QGridGen` / `Chain/QGridGen2` texts (2ee4af8a) and is not in this file.  Then shapes (not
binding): band and BA readings.
Part 3 (G1): the band names read outside the writable files (U3s4's `QtXiRoundLift`), and the names of the in-place files that
the band files `QEndGrid`, `QEndB1` read; name and type unchanged; the auditor adds `example : <statement> := <name>`.
Merged names only; statements only.
Run: lake env lean docs/tickets/checks/T2498-check.lean
-/
import RBM3D.Induction.QEndB1
import RBM3D.Chain.NQLinGen
import RBM3D.Chain.AzumaProxyGen
import RBM3D.Chain.GridEnvelopeGen
import RBM3D.Chain.HierDriftGen
import RBM3D.Chain.GridRepTailGen2
import RBM3D.Chain.DecayGen
import RBM3D.Chain.B45Gen
import RBM3D.Chain.Step5KerGen
import RBM3D.Chain.Step2EventsGenTw
import RBM3D.Chain.DecayGenTw
import RBM3D.Chain.Step34GenTw
import RBM3D.BA.EKSum
import RBM3D.BA.GridRepTailBA
import RBM3D.BA.EMn2BA
import RBM3D.BA.GreenLDE
import RBM3D.BA.Ward
import RBM3D.BA.TwistStep2
import RBM3D.BA.GreenSchur
import RBM3D.BA.Step2BA
import RBM3D.BA.FlowPins
import RBM3D.BA.B45BA
import RBM3D.BA.GridGoodBA

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the carrier and T8b's kernel (U-C4: the one kernel)
#check @RBM.BA.FlowFM
#check @RBM.BA.Step2Mat
#check @RBM.BA.bandFM
#check @RBM.BA.bandStep2Mat
#check @RBM.BA.PrecL
#check @RBM.BA.PrecPTL
#check @RBM.BA.Step2Gen_UN
#check @RBM.BA.Step2Gen_ThetaN
#check @RBM.BA.bandStep2_Ugen
#check @RBM.BA.Step2Kern_UN_BA
#check @RBM.BA.STLKMg
#check @RBM.BA.STKboundgL
#check @RBM.BA.STKwardgL
#check @RBM.BA.STLKgL
#check @RBM.BA.STStep2ConclgL
-- U3s1 (`Chain/Step34Gen`): the setting, the controls, the R1 crossing steps
#check @RBM.BA.STIngRgL
#check @RBM.BA.bandFM_STIngR
#check @RBM.BA.STXiLg
#check @RBM.BA.STXiLKg
#check @RBM.BA.STSEforLngL
#check @RBM.BA.Step34Gen_LCompat
#check @RBM.BA.step34Gen_winK_of_cmp
#check @RBM.BA.step34Gen_ratio_pow_le
#check @RBM.BA.step34Gen_ellT_ge
#check @RBM.BA.step34Gen_decayK_of_cmp
-- T4s2 (`Chain/GridGoodGen`, `GridAssemblyGen`, `AzumaProxyGen`)
#check @RBM.BA.GoodSetNg
#check @RBM.BA.STmaxLKMg
#check @RBM.BA.GridGoodNConclg
#check @RBM.BA.GridGoodNgL
#check @RBM.BA.gridGoodNgL_of
#check @RBM.BA.qvFormNg
#check @RBM.BA.GridAssemblyHypNg
#check @RBM.BA.AssembledNg
#check @RBM.BA.assembledNg
#check @RBM.BA.YMomentBoundsNg
#check @RBM.BA.yMomentsUnifNg
-- T5s2 (`Chain/StepDecompGen`, `HierDriftGen`), T7 (`DecayGen`), P1b-1 (`GridRepTailGen`)
#check @RBM.BA.StepDecompGen_LoopForm
#check @RBM.BA.StepDecompGen_WalkForm
#check @RBM.BA.SubGaussStopNg
#check @RBM.BA.QVPropagatedNg
#check @RBM.BA.qvPropagatedNg
#check @RBM.BA.stepErrNg
#check @RBM.BA.GridDriftNg
#check @RBM.BA.exists_norm_KI_le_wing
#check @RBM.BA.gridDriftNg_envelope
#check @RBM.BA.Step2EventsGen_Flow
#check @RBM.BA.Step2EventsGen_Law
#check @RBM.BA.DecayGen_Spec
#check @RBM.BA.DecayGen_WardPair
#check @RBM.BA.STKcalDecaygL
#check @RBM.BA.STDecayLoopUgL
#check @RBM.BA.stDecayLoopUgL_of_step2
#check @RBM.BA.GridRepTailGen_Ker
-- U2 (`Chain/B45Gen`), U4s1 (`Chain/Step5KerGen`): the levels of `ℬ₄ + ℬ₅` and the `Θ`-decay class (merged texts)
#check @RBM.BA.B45Gen_Facts
#check @RBM.BA.b45Gen_facts_band
#check @RBM.BA.B45_det2g
#check @RBM.BA.B45_norm_ThetaN_leg
#check @RBM.BA.Step5KerGen_ThDecay
#check @RBM.BA.step5KerGen_thDecay_band
-- U3s2a (`Chain/NQGood1Gen`, `NQGood2Gen`, 9df6a9e7)
#check @RBM.BA.NQGoodGen_KerNAL
#check @RBM.BA.NQGoodGen_KerNALFam
#check @RBM.BA.driftTensorNg
#check @RBM.BA.driftTensorNg_far_of_goodSetNg
#check @RBM.BA.hker_of_case1Ng
#check @RBM.BA.qvFormNg_le_of_goodSetNg
#check @RBM.BA.NQGood1Gen_eta_anti
#check @RBM.BA.norm_loopFine_crudeNg
#check @RBM.BA.STmaxLKMg_crudeNg
#check @RBM.BA.eeShiftErrNg
#check @RBM.BA.norm_STeeMg_shiftNg_le
#check @RBM.BA.dDriftNonAltNg
#check @RBM.BA.goodSetNg_A0clsNg
#check @RBM.BA.hQ_nonAltNg
-- U3s2b (`Chain/NQBudgetGen`, `NQLinGen`, c2542930)
#check @RBM.BA.tbInitNg
#check @RBM.BA.tbDriftNg
#check @RBM.BA.tbQvNg
#check @RBM.BA.nqBudget_merged_inputsg
#check @RBM.BA.GoodLinNg
#check @RBM.BA.NQLinConclg
#check @RBM.BA.NQLinGoodgL
#check @RBM.BA.nqLinGoodgL_of
#check @RBM.BA.measurableGoodLinNg
#check @RBM.BA.goodSetNg_subset_goodLinNg
#check @RBM.BA.dDriftLinNg
#check @RBM.BA.driftTensorNg_norm_le_of_goodLin
-- band inputs of D1 and of the vocabulary constant
#check @RBM.EKFastDecay
#check @RBM.EKSumZero
#check @RBM.EKSumDecay2
#check @RBM.ekSumDecay2_holds
#check @RBM.Ind.qProxy4C
#check @RBM.Ind.qProxyCn
#check @RBM.Ind.nqGood1_mE_im_ge
-- BA sources of the family premises (read only; owners U3-BA, U4-BA, T5-BA, U2-BA)
#check @RBM.BA.BAEKSumDecay2
#check @RBM.BA.baEKSumDecay2_holds
#check @RBM.BA.baB45Gen_facts
#check @RBM.BA.baGridDrift_envelope
#check @RBM.BA.gridRepTailGen_ker_BA
#check @RBM.BA.Step2EventsGenTw_baFlow
#check @RBM.BA.Step2EventsGenTw_baLaw
#check @RBM.BA.DecayGenTw_baWardPair
#check @RBM.BA.EMn2BA_mF_data
#check @RBM.BA.EMn2BA_one_sub_T0
#check @RBM.BA.ba_G_data
#check @RBM.BA.BAm_norm_le_one
#check @RBM.BA.TwistStep2_lam0_sq
#check @RBM.BA.BAflow_lam0_window
#check @RBM.BA.BAflow_real
#check @RBM.BA.baStep2Mat
#check @RBM.BA.baStep2Mat_KI
#check @RBM.BA.baFMz
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.BA.BAflowT0

/-! ## Part 2: the target statements, then shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 11, `STXiRoundPTgL''`** (binding; band `STXiRoundPT''`, `Induction/QEndB1.lean:100`): the per-time round of
`(am;asoi222)` at `n_ ≥ 2` over a flow carrier: `Prec sz` is `PrecL sz μ`, `PrecPT sz` is `PrecPTL sz μ`, `STXiL`/`STXiLK` are U3s1's
`STXiLg`/`STXiLKg`; `sz.Bctl` and `STbootRHS` stay (size level, model-free).  Consumer: U3s4 (the lift of `QtXiRoundLift`). -/
def T2498_XiRoundPTgL'' {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    PrecPTL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 n_ ω)
      (fun n q _ => sz.Bctl n q.1.2 ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
        STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p)

/-- **Target 11, `STOeqQtRoundPTgL''`** (binding; band `STOeqQtRoundPT''`, `QEndB1.lean:121`): the round in the setting
`STIngRgL d STCaseI` of a carrier family. -/
def T2498_OeqQtRoundPTgL'' (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngRgL d STCaseI law Flow mk T0 (fun sz z s t => T2498_XiRoundPTgL'' (mk sz z) (law sz) s t)

/-- **Target 12, `stOeqQtRoundPTgL''_of`** (conclusion binding; `Hyp` is the family-premise bundle of the ticket's table, fixed
at the 1a-audit; band `stOeqQtRoundPT''_holds`, `QEndB1.lean:1841`, unedited). -/
def T2498_OeqQtRoundPTOf
    (Hyp : ∀ (d : ℕ), (∀ sz : Sizes d, Measure sz.SeqΩ) → (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) →
      (∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) → (∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) → Prop) : Prop :=
  ∀ (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ),
    Hyp d law Flow mkM T0 → T2498_OeqQtRoundPTgL'' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0

/-- **D1 default, `QProxyG_KerEK4`** (text fixed at the 1a-audit): the deterministic `(sum_res_2)` (EK-4: every `σ`, sum-zero
`A`) for the carrier kernel `Step2Gen_UN C` at the kernel coupling `gK`, index `n`, explicit constant `C4`, with `L^d ≤ W^{KL}`
(band: the input `ekSumDecay2_holds` of `qProxy4C`, `Induction/QProxy.lean:444`; BA: `BAEKSumDecay2`, `BA/EKPins.lean:124`). -/
def T2498_KerEK4 {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (gK : ℕ → ℝ) (k : ℕ) (KL C4 : ℝ) (n : ℕ) : Prop :=
  1 < ((sz.W n : ℕ) : ℝ) → ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ KL →
  ∀ ε D : ℝ, 0 < ε → ε < 1 → 1 < D → 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε →
    Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ ε →
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 - gK n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 →
      (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t) / (1 - s) →
      ∀ σ : Fin k → Bool, ∀ A : (Fin k → Zd d (sz.L n)) → ℂ,
        EKFastDecay (gK n) s ((sz.W n : ℕ) : ℝ) ε D A → EKSumZero A →
        ‖Step2Gen_UN C n σ s t A‖ ≤
          ((sz.W n : ℕ) : ℝ) ^ (C4 * ε) * ((gK n ^ 2 + |1 - s|) / (gK n ^ 2 + |1 - t|)) ^ k * ‖A‖ +
            ((sz.W n : ℕ) : ℝ) ^ (-D + C4)

/-- **D1 default, the family form** (guarded; `∃ C4` after `(k, κ, ε, 𝔡, KL)` and before `(sz, z)`: U5S-C3, no F1 case; `KL` is
explicit because the band constant depends on it, `KL = 1/𝔠` at the consumer).  Band `gK = sz.lam`; BA `gK = BAflowLam0 sz z`
(U3-BA (a), from `baEKSumDecay2_holds`, `BAflow_real`, `BAflow_lam0_window`). -/
def T2498_KerEK4Fam (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ k : ℕ, 2 ≤ k → ∀ κ ε 𝔡 KL : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → 0 < KL → ∃ C4 : ℝ, 0 < C4 ∧
    ∀ (sz : Sizes d) (𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, T2498_KerEK4 (mk sz z) (gK sz z) k KL C4 n

/-! ### Shapes (not binding): band readings -/

/-- Band reading of target 11 (the bridge goes through `bandFM_STIngR`; the band file `QEndB1` is not edited). -/
example : Prop := ∀ d : ℕ,
  STOeqQtRoundPT'' d ↔ T2498_OeqQtRoundPTgL'' d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))

/-- Band discharge of D1 (`ekSumDecay2_holds` at `g = sz.lam`, `C4 = qProxy4C d k 𝔡⁻¹ κ' KL`), next to the merged band
discharges of the `Θ`-decay class and of `B45Gen_Facts`. -/
example : Prop := ∀ d : ℕ,
  T2498_KerEK4Fam d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun sz _ => sz.lam) ∧
    B45Gen_Facts d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z))

/-! ### Shapes (not binding): BA readings (U3-BA; statement level only) -/

/-- Targets 11-12 at the BA carrier family `(seqP ∘ withLam 0, BAFlow, baFMz, BAflowT0)` (as `Step34GenTw:84-90`). -/
example : Prop := ∀ d : ℕ,
  T2498_OeqQtRoundPTgL'' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)

/-- D1 and the merged `Θ`-decay class at the BA family (owners: U3-BA (a) for D1, U4-BA (a) for `Step5KerGen_ThDecay`). -/
example : Prop := ∀ d : ℕ,
  T2498_KerEK4Fam d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowLam0 sz z) ∧
    ∀ 𝔡 : ℝ, 0 < 𝔡 → ∃ C₆ : ℝ, 0 < C₆ ∧ ∀ (sz : Sizes d) (κ ε 𝔠 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
      Step5KerGen_ThDecay (baFMz sz z) (BAflowLam0 sz z) 𝔡⁻¹ C₆

end RBM.BA

end

/-! ## Part 3 (G1): band names that keep name and type (files `QEndGrid`, `QEndB1`, `QtXiRoundLift` are not edited) -/

-- read outside the ten files (U3s4, `Induction/QtXiRoundLift`)
#check @RBM.Gauss.Sizes.STXiRoundPT''
#check @RBM.Gauss.Sizes.STOeqQtRoundPT''
#check @RBM.Ind.stOeqQtRoundPT''_holds
-- `QProxy`, read from band `QEndGrid`
#check @RBM.Ind.zVecQN
#check @RBM.Ind.yVecQN
#check @RBM.Ind.qProxy4C_pos
#check @RBM.Ind.yMomentsQUnifN
-- `QDriftA`, read from band `QEndGrid`
#check @RBM.Ind.kappaAltQN
#check @RBM.Ind.epsAltQN
-- `QLevelsA`, read from band `QEndB1`
#check @RBM.Ind.startLevelQN
-- `QBudgetA`, `QBudgetB`, read from band `QEndGrid`
#check @RBM.Ind.qvBdAltQN
#check @RBM.Ind.cQVAltQN
#check @RBM.Ind.dDriftAltLinQN
#check @RBM.Ind.assembledRHSAltQN
#check @RBM.Ind.dDriftAltLinQN_le_shape
#check @RBM.Ind.budgetAltQN
#check @RBM.Ind.dDriftAltLinQN_nonneg
#check @RBM.Ind.altBudgetNumQN_eventually
-- `QEndA`, read from band `QEndGrid` (`altYGridN` from `QEndB1`)
#check @RBM.Ind.altYSetN
#check @RBM.Ind.altExitTauN
#check @RBM.Ind.mem_of_lt_altExitTauN
#check @RBM.Ind.altExitMeasN
#check @RBM.Ind.altYGridN
#check @RBM.Ind.gridDriftQN_envelope'
#check @RBM.Ind.assembledRHSAltQN_qErr_le
#check @RBM.Ind.subGaussStop_altQN
#check @RBM.Ind.alt_hkerGridQN
#check @RBM.Ind.alt_hdriftGridQN
#check @RBM.Ind.alt_hA0clsGridQN
#check @RBM.Ind.alt_hDclsGridQN
#check @RBM.Ind.altEnd_driftSup
#check @RBM.Ind.altEnd_hexp
#check @RBM.Ind.altEnd_stronglyMeasurable_zVecQN
#check @RBM.Ind.altEnd_aFroz_eq_aTrue
#check @RBM.Ind.altEnd_unQ
-- the grid endpoint read from band `QEndB1` (file `QEndGrid` not edited; generic successor `altGridEndQNg` in row b)
#check @RBM.Ind.altGridEndQN'
