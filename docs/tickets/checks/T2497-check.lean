/-
Release check for T2497 (dispatcher V4, 2026-10-14; DECISIONS §309).  U U1s2 (sub-stage U, ST side): the Step 1 / iteration
layer over the flow carrier, in two independent rows.  Row a (U1s2a, QGrid): the `𝒬`-grid layer of `int_K-L+Q` (band
`Induction/QGridA`, `QGridB`).  Row b (U1s2b, Iterations): `lem:iterations`, R2* (band `Induction/IterationsA`, `IterationsB`).
NEW-FILE layout (supervisor 0658 UP-C2 with the ×1.74 sensitivity price, DECISIONS §308 (2), §309): new files
`Chain/QGridGen`, `Chain/QGridGen2` (row a) and `Chain/IterationsGen`, `Chain/IterationsGen2` (row b); the four band files are
not edited (Part 3 is then immediate).
Part 1: merged names.  Part 2: Prop values (prefix `T2497_`).  Binding: the vocabulary twins `T2497_aTrueQNg`,
`T2497_dGridQNg`, `T2497_aFrozQNg`, `T2497_martIncQNg`, `T2497_rGridQNg`, `T2497_lkEnvNg`, `T2497_driftEnvNg`, `T2497_qErrQNg`;
the statement `T2497_SumWeightedQErrQNg`; the conclusion heads `T2497_GridDriftQNgAt`, `T2497_StoppedDuhamelQNg`; the content of
`T2497_IterScaleg` (the 1b may write it as a Lean record with these fields); the conclusions of `T2497_IterationsOf`,
`T2497_IterationsIIOf` (the hypothesis bundle `T2497_IterFam` is a draft, fixed at the 1a).
The R2* texts are the merged `STXiBootgL'`, `STIterRgL'`, `STIterationsgL'`, `STIterationsIIgL'` (T2491 row c, `Chain/NQEndFlowGen`,
merged c72bc745); the earlier draft's verbatim copies were checked equal to them (dispatcher text diff, 2026-10-14) and removed.
Then shapes (not binding): band and BA readings, per-index premises, R1 (not used here).
Part 3 (G1): the band names read outside the four files; name and statement unchanged after the row.
Merged names only; statements only.
Run: lake env lean docs/tickets/checks/T2497-check.lean
-/
import RBM3D.Induction.IterationsB
import RBM3D.Induction.QGridB
import RBM3D.Chain.NQEndFlowGen
import RBM3D.Chain.Step34Gen
import RBM3D.Chain.KDecayGen
import RBM3D.Chain.NQGood1Gen
import RBM3D.Chain.ZeroModeGen
import RBM3D.Chain.Step2EventsGen
import RBM3D.Chain.Step2EventsGenTw
import RBM3D.Chain.Step2Kern
import RBM3D.BA.FlowPins
import RBM3D.BA.Step2BA
import RBM3D.BA.SEforLnBA
import RBM3D.BA.EMn2BA
import RBM3D.BA.GreenLDE
import RBM3D.BA.Ward
import RBM3D.BA.GridDriftBA
import RBM3D.BA.TwistGrid

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- row 0 / T8 / U3s1 (`Chain/Carrier`, `Step2Gen`, `Step34Gen`): carrier, law, the iteration vocabulary and its band bridges
#check @RBM.BA.FlowFM
#check @RBM.BA.Step2Mat
#check @RBM.BA.PrecL
#check @RBM.BA.bandFM
#check @RBM.BA.bandStep2Mat
#check @RBM.BA.STKboundgL
#check @RBM.BA.STLKgL
#check @RBM.BA.STStep1LoopgL
#check @RBM.BA.STStep2ConclgL
#check @RBM.BA.STAvgUgL
#check @RBM.BA.STmaxLg
#check @RBM.BA.STXiLg
#check @RBM.BA.STXiLKg
#check @RBM.BA.STIterHypgL
#check @RBM.BA.STXiBootgL
#check @RBM.BA.STIterRgL
#check @RBM.BA.bandFM_STIterHyp
#check @RBM.BA.bandFM_STIterR
#check @RBM.BA.bandStep34_STXiL
#check @RBM.BA.Step34Gen_LCompat
#check @RBM.BA.bandStep34_LCompat
#check @RBM.BA.bandStep34_ThetaN
#check @RBM.BA.Step2Gen_UN
#check @RBM.BA.Step2Gen_ThetaN
#check @RBM.BA.Step2Gen_uKer
#check @RBM.BA.STksimLKMg
#check @RBM.BA.STelklkMg
#check @RBM.BA.STegtMg
-- U2 (`Chain/KDecayGen`): the uniform `𝒦` bound from the per-sequence pin
#check @RBM.BA.stKbound_timeIccgL
-- T1 (`Chain/Step2EventsGen`): the flow facts (Admissible, `T0 < 1`)
#check @RBM.BA.Step2EventsGen_Flow
-- T5s2 (`Chain/StepDecompGen`, `HierDriftGen`): carrier classes, the per-index grid drift, the step error
#check @RBM.BA.StepDecompGen_LoopForm
#check @RBM.BA.StepDecompGen_WalkForm
#check @RBM.BA.stepDecompGen_loopForm_band
#check @RBM.BA.stepDecompGen_walkForm_band
#check @RBM.BA.HierDriftGen_Expand
#check @RBM.BA.HierDriftGen_KLoop
#check @RBM.BA.HierDriftGen_KTwo
#check @RBM.BA.HierDriftGen_UStep
#check @RBM.BA.HierDriftGen_KLink
#check @RBM.BA.stepErrNg
#check @RBM.BA.bandFM_stepErrN
#check @RBM.BA.GridDriftNg
#check @RBM.BA.gridDriftNg_at
#check @RBM.BA.hierDriftGen_uStep_band
#check @RBM.BA.hierDriftGen_expand_band
#check @RBM.BA.hierDriftGen_kLoop_band
#check @RBM.BA.hierDriftGen_kTwo_band
#check @RBM.BA.hierDriftGen_kLink_band
-- T4s1 (`Chain/GridDuhamelGen`): grid vocabulary, semigroup class, stopped Duhamel at one index
#check @RBM.BA.AvecNg
#check @RBM.BA.martIncNg
#check @RBM.BA.predIncNg
#check @RBM.BA.Step2Gen_USemigroup
#check @RBM.BA.step2Gen_USemigroup_band
#check @RBM.BA.stoppedDuhamelNg_at
#check @RBM.BA.bandStep2_AvecN
#check @RBM.BA.bandStep2_Ugen
-- T4s2 (`Chain/GridEnvelopeGen`): the deterministic envelope and the energy substitution `E' = 2 √(1 - (Im m)²)`
#check @RBM.BA.SumWeightedStepErrNg_Stmt
#check @RBM.BA.sum_weighted_stepErrNg_le
#check @RBM.BA.GridEnvelopeGen_mE_im_Ep
#check @RBM.BA.GridEnvelopeGen_abs_Ep_le
#check @RBM.BA.GridEnvelopeGen_stepErrNg_eta
#check @RBM.BA.DecayGen_Spec
-- U1s1 (`Chain/ZeroModeGen`, target 6): the `𝒬`-algebra over the one kernel
#check @RBM.BA.QopAlgebra_UN_subg
#check @RBM.BA.QopAlgebra_ThetaN_subg
#check @RBM.BA.QopAlgebra_commutator_UNg
#check @RBM.BA.QopAlgebra_commutator_ThetaNg
-- U3s2a (`Chain/NQGood1Gen`, merged 9df6a9e7): `η` facts under `LoopForm` and the crude loop bound
#check @RBM.BA.NQGood1Gen_eta_eq
#check @RBM.BA.NQGood1Gen_eta_pos
#check @RBM.BA.NQGood1Gen_eta_anti
#check @RBM.BA.NQGood1Gen_eta_le_one
#check @RBM.BA.norm_loopFine_crudeNg
-- model-free, reused under their names (band files, not converted)
#check @RBM.Gauss.Sizes.STQop
#check @RBM.Gauss.Sizes.STPsum
#check @RBM.Gauss.Sizes.STPsi
#check @RBM.Gauss.Sizes.STbootRHS
#check @RBM.Gauss.Sizes.STlenL
#check @RBM.Gauss.Sizes.STPair
#check @RBM.Gauss.Sizes.STAI
#check @RBM.Gauss.Sizes.STAII
#check @RBM.Gauss.Sizes.STRegIterI
#check @RBM.Gauss.Sizes.STCaseII
#check @RBM.Gauss.Sizes.STMollifierProps
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier_props
#check @RBM.Ind.QGridA_Taylor2
#check @RBM.Ind.QGridA_mollifier_taylor2
#check @RBM.Ind.qStepErrN
#check @RBM.Ind.uStepC
#check @RBM.Ind.loopXi_le
#check @RBM.Ind.loopMax_odd_sq_le
#check @RBM.Gauss.Sizes.iterationsA_chain_term
#check @RBM.Gauss.Sizes.iterationsA_boot_bound
#check @RBM.Gauss.Sizes.iterationsA_STPsi_nonneg
-- BA sources of the family rows (statement level here; the BA readings are U1-BA)
#check @RBM.BA.baStep2Mat
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowEs
#check @RBM.BA.BAflowLam0
#check @RBM.BA.Step2EventsGenTw_baFlow
#check @RBM.BA.baStep2Mat_loopForm
#check @RBM.BA.baStep34_LCompat
#check @RBM.BA.EMn2BA_seqHflowBA_herm
#check @RBM.BA.EMn2BA_mF_data
#check @RBM.BA.ba_G_data
#check @RBM.BA.BAm_norm_le_one
#check @RBM.BA.baStep2Mat_walkForm
#check @RBM.BA.baStep2Mat_imLeOne
#check @RBM.BA.baHierDrift_classes
#check @RBM.BA.baHierDrift_uStep
#check @RBM.BA.BAuKer_self
#check @RBM.BA.BAuKer_comp
#check @RBM.BA.Step2Kern_uKer_BA
#check @RBM.Gauss.Sizes.isProbabilityMeasure_seqP

-- U3s2c = T2491 row c (`Chain/NQEndFlowGen`, merged c72bc745): the R2* texts over a carrier (binding T2491 texts)
#check @RBM.BA.STXiBootgL'
#check @RBM.BA.STIterRgL'
#check @RBM.BA.STIterationsgL'
#check @RBM.BA.STIterationsIIgL'

/-! ## Part 2: the target statements, then shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ### QGrid half: vocabulary twins (binding texts; band `Induction/QGridA.lean:1263-1355`) -/

/-- **Target 1, `aTrueQNg`** (band `aTrueQN`, `QGridA:1263`): `A^Q_j = 𝒬_{u_j} A_j` with T4s1's `AvecNg`. -/
def T2497_aTrueQNg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (j : ℕ) (ω : PathΩ sz) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  STQop (d := d) ϑ (gridTime s t K n j) (AvecNg Cm s t K n j σ ω)

/-- **Target 1, `dGridQNg`** (band `dGridQN`, `QGridA:1274`): `𝒬_u D + ℬ₄ + ℬ₅` with the drift of `GridDriftNg`
(`STksimLKMg`, `STelklkMg`, `STegtMg` at `KLloopOf`) and the kernel `Step2Gen_ThetaN` (U-C4: one kernel). -/
def T2497_dGridQNg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (j : ℕ) (ω : PathΩ sz) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  fun a =>
    STQop (d := d) ϑ (gridTime s t K n j)
        (fun b => ∑ l ∈ Finset.Icc 3 (m + 1),
            STksimLKMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) l (KLloopOf d (sz.L n) σ b) +
          STelklkMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ b) +
          STegtMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ b)) a +
      (STQop (d := d) ϑ (gridTime s t K n j)
          (Step2Gen_ThetaN Cm.toFlowFM n σ (gridTime s t K n j) (AvecNg Cm s t K n j σ ω)) a -
        Step2Gen_ThetaN Cm.toFlowFM n σ (gridTime s t K n j)
          (STQop (d := d) ϑ (gridTime s t K n j) (AvecNg Cm s t K n j σ ω)) a) -
      STPsum (d := d) (AvecNg Cm s t K n j σ ω) (a 0) * deriv (fun τ => ϑ τ a) (gridTime s t K n j)

/-- **Target 1, `aFrozQNg`** (band `aFrozQN`, `QGridA:1292`). -/
def T2497_aFrozQNg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (τ : PathΩ sz → ℕ) (j : ℕ)
    (ω : PathΩ sz) : (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (min j (τ ω))) (gridTime s t K n j)
    (T2497_aTrueQNg Cm s t K n ϑ σ (min j (τ ω)) ω)

/-- **Target 1, `martIncQNg`** (band `martIncQN`, `QGridA:1299`); the law of the walk is `Cm.Pp`. -/
def T2497_martIncQNg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (j : ℕ) (ω : PathΩ sz) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  fun a => T2497_aTrueQNg Cm s t K n ϑ σ (j + 1) ω a -
    MeasureTheory.condExp (filt sz j) Cm.Pp (fun ω' => T2497_aTrueQNg Cm s t K n ϑ σ (j + 1) ω' a) ω

/-- **Target 1, `rGridQNg`** (band `rGridQN`, `QGridA:1307`): the one-step remainder, named as a difference. -/
def T2497_rGridQNg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (j : ℕ) (ω : PathΩ sz) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  fun a => MeasureTheory.condExp (filt sz j) Cm.Pp (fun ω' => T2497_aTrueQNg Cm s t K n ϑ σ (j + 1) ω' a) ω -
    Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n j) (gridTime s t K n (j + 1))
      (T2497_aTrueQNg Cm s t K n ϑ σ j ω) a -
    (gridStep s t K n : ℂ) * T2497_dGridQNg Cm s t K n ϑ σ j ω a

/-- **Target 1, `lkEnvNg`** (band `lkEnvN`, `QGridA:1319`): `etaT E u` read as `Cf.eta n u` (as `stepErrNg`). -/
def T2497_lkEnvNg {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (n k : ℕ) (u Bk : ℝ) : ℝ :=
  (Cf.eta n u)⁻¹ ^ k * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (k - 1) + Bk

/-- **Target 1, `driftEnvNg`** (band `driftEnvN`, `QGridA:1326`). -/
def T2497_driftEnvNg {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (n k : ℕ) (u Bk : ℝ) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d *
    ((k : ℝ) * (2 * (k : ℝ) ^ 2 * (((Cf.eta n u)⁻¹ ^ k + Bk) * Bk)) +
      (k : ℝ) ^ 2 * (((Cf.eta n u)⁻¹ ^ k + Bk) * ((Cf.eta n u)⁻¹ ^ k + Bk)) +
      (k : ℝ) * (((Cf.eta n u)⁻¹ + 1) * (Cf.eta n u)⁻¹ ^ (k + 1)))

/-- **Target 1, `qErrQNg`** (band `qErrQN`, `QGridA:1349`): the model-free `qStepErrN` at the three generic envelopes. -/
def T2497_qErrQNg {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n m : ℕ) (C C₂ Bk : ℝ)
    (j : ℕ) : ℝ :=
  RBM.Ind.qStepErrN d (sz.L n) m C C₂ (gridTime s t K n j) (gridStep s t K n)
    (T2497_lkEnvNg Cf n (m + 1) (gridTime s t K n j) Bk)
    (T2497_driftEnvNg Cf n (m + 1) (gridTime s t K n j) Bk)
    (stepErrNg Cf n (m + 1) (gridTime s t K n j) (gridTime s t K n (j + 1)) (gridStep s t K n) Bk)

/-! ### QGrid half: conclusions (binding) -/

/-- **Target 6, head of `gridDriftQNg`** (band `gridDriftQN`, `QGridA:2114`): one index `n`, one grid step `j`, the merged
mollifier at the size-level `sz.lam n` (UBA-C1: size level; no comparison with the carrier coupling). -/
def T2497_GridDriftQNgAt {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {m : ℕ}
    (σ : Fin (m + 1) → Bool) (Bk : ℝ) : Prop :=
  ∀ᵐ ω ∂(Cm.Pp), ∀ a : Fin (m + 1) → Zd d (sz.L n),
    ‖MeasureTheory.condExp (filt sz j) Cm.Pp
          (fun ω' => T2497_aTrueQNg Cm s t K n (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ (j + 1) ω' a) ω -
        Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n j) (gridTime s t K n (j + 1))
          (T2497_aTrueQNg Cm s t K n (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ j ω) a -
        (gridStep s t K n : ℂ) * T2497_dGridQNg Cm s t K n (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ j ω a‖ ≤
      T2497_qErrQNg Cm.toFlowFM s t K n m ((1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m))
        (1000 * (1 + ((d * m : ℕ) : ℝ)) ^ 2) Bk j

/-- **Target 7, conclusion of `stoppedDuhamelQNg`** (band `stoppedDuhamelQN`, `QGridA:2168`): pathwise, any `ϑ`, any
stopping index `τ`, one index `n`. -/
def T2497_StoppedDuhamelQNg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (τ : PathΩ sz → ℕ) (j : ℕ)
    (ω : PathΩ sz) : Prop :=
  T2497_aFrozQNg Cm s t K n ϑ σ τ j ω =
    Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n 0) (gridTime s t K n j) (T2497_aTrueQNg Cm s t K n ϑ σ 0 ω) +
      ∑ i ∈ Finset.range (min j (τ ω)),
        Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (i + 1)) (gridTime s t K n j)
          ((gridStep s t K n : ℂ) • T2497_dGridQNg Cm s t K n ϑ σ i ω + T2497_martIncQNg Cm s t K n ϑ σ i ω +
            T2497_rGridQNg Cm s t K n ϑ σ i ω)

/-- **Target 8, `sum_weighted_qErrQNg_le`** (band `sum_weighted_qErrQN_le`, `QGridB:565`, not edited; new file `Chain/QGridGen2`): the
four rows of the band statement, `|E n| ≤ 2 - κ` replaced with T4s2's `DecayGen_Spec`, `Im m ≤ 1` (the premises of
`SumWeightedStepErrNg_Stmt`, `GridEnvelopeGen:235`). -/
def T2497_SumWeightedQErrQNg : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (Cm : Step2Mat sz) {κm τ' τK C_K D_t C C₂ : ℝ} {s t : ℕ → ℝ} {K : ℕ → ℕ} (m : ℕ),
    0 ≤ C → 0 ≤ C₂ → DecayGen_Spec Cm.toFlowFM κm → (∀ n, (Cm.m n).im ≤ 1) → 0 < τ' → τ' ≤ 1 → 0 < τK →
    0 ≤ D_t → 1 ≤ m → sz.SizeTendsto → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
    sz.RangeCond τ' t →
    8 + (4 * ((m : ℝ) + 1) + 8) * (1 - τ') + 2 * (D_t + ((m : ℝ) + 1)) < C_K →
    3 + 4 * τK + 5 * ((m : ℝ) + 1) * (1 - τ') + (D_t + ((m : ℝ) + 1)) < C_K →
    2 * (1 - τ') + τK + 2 * ((m : ℝ) + 1) * (1 - τ') + (D_t + ((m : ℝ) + 1)) < C_K → 1 - τ' < C_K →
    (∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) →
    ∀ᶠ n : ℕ in atTop, ∀ p ≤ K n,
      ∑ j ∈ Finset.range p, (1 + (1 - gridTime s t K n p)⁻¹) ^ (m + 1) *
          T2497_qErrQNg Cm.toFlowFM s t K n m C C₂
            (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s t K n (j + 1)))⁻¹ ^ (m + 1)) j ≤
        ((sz.size n : ℕ) : ℝ) ^ (-D_t)

/-! ### Iterations half: the scale facts (content binding; band record `IterationsAScale`, `IterationsA:1058`) -/

/-- **Target 12, `IterationsAScaleg`** (content binding): the nine fields of the band record, `etaT (E n)` read as
`Cf.eta n`. -/
def T2497_IterScaleg {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (s t A T : ℕ → ℝ) (cB cv K : ℝ) : Prop :=
  0 ≤ cB ∧ 1 ≤ cv ∧ 1 ≤ K ∧ (∀ n, 0 ≤ A n) ∧ (∀ n, 0 ≤ T n) ∧ (∀ n, t n < 1) ∧
    (∀ᶠ n in atTop, 1 ≤ A n) ∧
    (∀ᶠ n in atTop, ∀ q : STPair s t n, 1 ≤ Cf.eta n (s n) / Cf.eta n q.1.2 ∧
      (Cf.eta n (s n) / Cf.eta n q.1.2) ^ 2 ≤ K * A n ^ (1 / 8 : ℝ) ∧
      T n * (Cf.eta n (s n) / Cf.eta n q.1.2) ^ 2 * A n ^ (7 / 8 : ℝ) ≤ cB * K) ∧
    (∀ᶠ n in atTop, T n * A n ^ (3 / 4 : ℝ) ≤ cB) ∧
    (∀ᶠ n in atTop, ∀ w : TimeIcc s t n, (cv * A n)⁻¹ ≤ sz.Bctl n (w : ℝ) ∧ sz.Bctl n (w : ℝ) ≤ T n)

/-! ### Iterations half: the R2* texts are the merged `STXiBootgL'`, `STIterRgL'`, `STIterationsgL'`, `STIterationsIIgL'`
(`Chain/NQEndFlowGen.lean:53-150`, Part 1) -/

/-! ### Iterations half: the family bundle (draft, fixed at the 1a) and the two pins (conclusions binding) -/

/-- **Family bundle (draft)**: rows 1-6 of the ticket's table.  Row 1 own; row 2 unguarded; rows 3-4 guarded (`0 < Im m` and
`‖m‖ ≤ 1` need the flow at BA); rows 5-6 unguarded (the loop class of the odd chain bound: `LCompat` and a Hermitian `Hf`). -/
def T2497_IterFam (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ →
      Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (Es T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  Step2EventsGen_Flow d Flow T0 ∧ (∀ sz : Sizes d, IsProbabilityMeasure (law sz)) ∧
    (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_LoopForm (mkM sz z) (Es sz z) ∧ ∀ n : ℕ, ‖(mkM sz z).m n‖ ≤ 1) ∧
    (∀ (sz : Sizes d) (z : ℕ → ℂ), Step34Gen_LCompat (mkM sz z) (Hf sz z) ∧
      ∀ (n : ℕ) (u : ℝ) (ω : sz.SeqΩ), (Hf sz z n u ω).IsHermitian)

/-- **Target 14, `stIterationsgL'_of`** (conclusion binding; band `stIterations'_holds`, `IterationsB:570`): the R2* pin
of case (i) at the carrier family `(mkM sz z).toFlowFM`. -/
def T2497_IterationsOf
    (Hyp : ∀ (d : ℕ), (∀ sz : Sizes d, Measure sz.SeqΩ) → (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) →
      (∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) →
      (∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ →
        Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) →
      (∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) → (∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) → Prop) : Prop :=
  ∀ (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ →
      Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (Es T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ),
    Hyp d law Flow mkM Hf Es T0 → STIterationsgL' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0

/-- **Target 14, `stIterationsIIgL'_of`** (conclusion binding; band `stIterationsII'_holds`, `IterationsB:581`): case (ii). -/
def T2497_IterationsIIOf
    (Hyp : ∀ (d : ℕ), (∀ sz : Sizes d, Measure sz.SeqΩ) → (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) →
      (∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) →
      (∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ →
        Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) →
      (∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) → (∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) → Prop) : Prop :=
  ∀ (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ →
      Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (Es T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ),
    Hyp d law Flow mkM Hf Es T0 → STIterationsIIgL' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0

/-! ### Shapes (not binding) -/

/-- The two pins at the draft bundle. -/
example : Prop := T2497_IterationsOf T2497_IterFam ∧ T2497_IterationsIIOf T2497_IterFam

/-- Target 6 as used: the per-index premises (T5s2 classes at `n`, row sums at `n`, `0 < sz.lam n` for the mollifier,
inline `‖m‖ ≤ 1`); consumers take them under `∀ᶠ n` (UP-C4; BA `baHierDrift_classes`). -/
example : Prop := ∀ {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (E lam' : ℕ → ℝ)
    (Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    {m : ℕ} (σ : Fin (m + 1) → Bool) (Bk : ℝ),
  StepDecompGen_LoopForm Cm E → StepDecompGen_WalkForm Cm lam' Ψ → HierDriftGen_Expand Cm s t K n →
    HierDriftGen_KLoop Cm n → HierDriftGen_KTwo Cm n → HierDriftGen_UStep Cm.toFlowFM n →
    (∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1) → HierDriftGen_KLink Cm n → ‖Cm.m n‖ ≤ 1 →
    0 < sz.lam n → 0 ≤ s n → s n ≤ t n → t n < 1 → K n ≠ 0 → j < K n → 1 ≤ m → 0 ≤ Bk →
    (∀ w ∈ Set.Icc (0 : ℝ) (gridTime s t K n (j + 1)), ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length →
      J.length ≤ m + 1 → ‖Cm.KI n w J‖ ≤ Bk) →
    T2497_GridDriftQNgAt Cm s t K n j σ Bk

/-- Target 7 as used: the semigroup class at the index `n` (band `step2Gen_USemigroup_band`; BA from `BAuKer_self`,
`BAuKer_comp` through `Step2Kern_uKer_BA`, U1-BA). -/
example : Prop := ∀ {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (τ : PathΩ sz → ℕ) (j : ℕ) (ω : PathΩ sz),
  Step2Gen_USemigroup Cm.toFlowFM n → 0 ≤ s n → s n ≤ t n → t n < 1 → K n ≠ 0 → j ≤ K n →
    T2497_StoppedDuhamelQNg Cm s t K n ϑ σ τ j ω

/-- Band readings of target 1 (`bandStep2_AvecN`; the drift through `bandStep34_ThetaN` and `loopOf`/`KLloopOf`). -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (ω : PathΩ sz),
  RBM.Ind.aTrueQN sz E s t K n ϑ σ j ω = T2497_aTrueQNg (bandStep2Mat sz E) s t K n ϑ σ j ω ∧
    RBM.Ind.dGridQN sz E s t K n ϑ σ j ω = T2497_dGridQNg (bandStep2Mat sz E) s t K n ϑ σ j ω

/-- Band reading of the envelopes (definitional at `bandFM`, as `bandFM_stepErrN`). -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n m : ℕ) (C C₂ Bk : ℝ) (j : ℕ),
  RBM.Ind.qErrQN sz E s t K n m C C₂ Bk j = T2497_qErrQNg (bandFM sz E) s t K n m C C₂ Bk j

/-- Target 8 at BA: the premises from `EMn2BA_mF_data` (`κm = κ`) and `baStep2Mat_imLeOne`. -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
  DecayGen_Spec (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).toFlowFM κ ∧
    ∀ n, ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).m n).im ≤ 1

/-- Target 6 at the BA carrier (statement level; U1-BA / U3-BA read it past the window). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {m : ℕ}
    (σ : Fin (m + 1) → Bool) (Bk : ℝ),
  T2497_GridDriftQNgAt (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s t K n j σ Bk

/-- Band reading of targets 12-14: the bundle at the band tuple and the band pin through the R2* bridge of T2491 row c. -/
example : Prop := ∀ d : ℕ,
  T2497_IterFam d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandStep2Mat sz (STflowE z)) (fun sz _ => seqHflow sz) (fun _ z => STflowE z)
      (fun _ z n => lemT (z n)) ∧
    (STIterations' d ↔ STIterationsgL' d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)))

/-- BA reading of targets 12-14 (U1-BA): the bundle at `(seqP ∘ withLam 0, BAFlow, baStep2Mat (BAflowLam0) (BAflowEs),
seqHflowBA, BAflowEs, BAflowT0)` and the pin of case (i). -/
example : Prop := ∀ d : ℕ,
  T2497_IterFam d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => sz.seqHflowBA (BAflowLam0 sz z))
      (fun sz z => BAflowEs sz z) (fun sz z => BAflowT0 sz z) ∧
    STIterationsgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).toFlowFM) (fun sz z => BAflowT0 sz z)

/-- Band reading of the scale facts (band `IterationsAScale` at `bandFM`, `etaT (E n)` = the `eta` field). -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (E s t A T : ℕ → ℝ) (cB cv K : ℝ),
  IterationsAScale sz E s t A T cB cv K ↔ T2497_IterScaleg (bandFM sz E) s t A T cB cv K

/-- UBA-C1 (DECISIONS §273 (1)): the only comparison text; not used in this row (R1 never enters, ticket table). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (gK : ℕ → ℝ) (A : ℝ),
  ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2

end RBM.BA

end

/-! ## Part 3 (G1): band names read outside the four files (readers: `Step3`, `Step4`, `MainIndRegimes`, `Test/Axioms`,
`QDriftA`, `QDriftB`, `QBudgetB`, `QLevelsB`, `QEndA`, `QEndGrid`, `QProxy`); name and statement unchanged after the row -/

-- `IterationsA` (new-file layout: not edited)
#check @RBM.Gauss.Sizes.st_prec_one_add_sup
#check @RBM.Gauss.Sizes.st_prec_of_xi
#check @RBM.Gauss.Sizes.st_one_le_XiL
#check @RBM.Gauss.Sizes.st_one_le_XiLK
#check @RBM.Gauss.Sizes.iterationsA_prec_mono_right
#check @RBM.Gauss.Sizes.iterationsA_prec_mono_left
#check @RBM.Gauss.Sizes.iterationsA_prec_absorb
#check @RBM.Gauss.Sizes.iterationsA_prec_rpow
#check @RBM.Gauss.Sizes.iterationsA_prec_one_add_mul
#check @RBM.Gauss.Sizes.IterationsAScale
#check @RBM.Gauss.Sizes.iterationsA_step
#check @RBM.Gauss.Sizes.iterationsA_avg_of_STAvgU
#check @RBM.Gauss.Sizes.iterationsA_apriori_of_lRB1
#check @RBM.Gauss.Sizes.iterationsA_rela_of_K
#check @RBM.Gauss.Sizes.iterationsA_scale_I
#check @RBM.Gauss.Sizes.iterationsA_scale_II
#check @RBM.Gauss.Sizes.iterationsA_xiL_odd_le
-- `IterationsB` (new-file layout: not edited)
#check @RBM.Gauss.Sizes.iterationsB_step
#check @RBM.Gauss.Sizes.stIterations'_holds
#check @RBM.Gauss.Sizes.stIterationsII'_holds
#check @RBM.Gauss.IterationsBInst.inst_iterations'
#check @RBM.Gauss.IterationsBInst.inst_iterationsII'
-- the R2* band texts read in `IterationsB` (`NQEndFlow`, not edited)
#check @RBM.Gauss.Sizes.STXiBoot'
#check @RBM.Gauss.Sizes.STIterR'
#check @RBM.Gauss.Sizes.STIterations'
#check @RBM.Gauss.Sizes.STIterationsII'
#check @RBM.Gauss.Sizes.stXiBoot'_of_stXiBoot
-- `QGridA` (new-file layout: not edited)
#check @RBM.Ind.aTrueQN
#check @RBM.Ind.dGridQN
#check @RBM.Ind.aFrozQN
#check @RBM.Ind.martIncQN
#check @RBM.Ind.rGridQN
#check @RBM.Ind.lkEnvN
#check @RBM.Ind.driftEnvN
#check @RBM.Ind.qErrQN
#check @RBM.Ind.QGridA_condExp_aTrueQN
#check @RBM.Ind.QGridA_gridDriftQN_of
#check @RBM.Ind.gridDriftQN
#check @RBM.Ind.stoppedDuhamelQN
#check @RBM.Ind.QGridACheck.sigma4
#check @RBM.Ind.QGridACheck.sigma4_alternating
#check @RBM.Ind.QGridACheck.moll
#check @RBM.Ind.QGridACheck.lam_pos
-- `QGridB` (new-file layout: not edited)
#check @RBM.Ind.sum_weighted_qErrQN_le
#check @RBM.Ind.QGridBCheck.Kc31
#check @RBM.Ind.QGridBCheck.Kc31_ne_zero
#check @RBM.Ind.QGridBCheck.sum_weighted_qErrQN_instance
