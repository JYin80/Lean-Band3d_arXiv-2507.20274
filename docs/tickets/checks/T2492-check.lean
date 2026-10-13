/-
Release check for T2492 (dispatcher V3, 2026-10-13 05:43 UTC; DECISIONS §294).  BA-T T5-BA with the T4-BA items folded in (supervisor 2351
T4S2-C1): the BA discharges of T5s2's carrier classes (T2474: `StepDecompGen_WalkForm`, `HierDriftGen_KLoop`, `_KTwo`, `_UStep`,
`_Expand`, `_KLink`) in the new leaf `BA/GridDriftBA.lean` (targets 1-6, reserve `BA/GridDriftBA2.lean`), and the BA readings of
T4s2's outputs (T2473: `Im m ≤ 1`, the initial membership of `GoodSetNg`, the pin `GridGoodNgL` through `gridGoodNgL_of`, the
envelope, the Azuma proxies) in `BA/GridGoodBA.lean` (targets 7-11, reserve `BA/GridGoodBA2.lean`).  No merged file is edited.
Part 1: merged names.  Part 2: pins (prefix `T2492_`, content binding).  Then shapes (not binding): the eventual drift reading
(finding F1), the envelope, QV / Y moments / Azuma at BA, the conditional GridGood with the T2486 (a) texts of exact type, R1.
Finding F1: `KLoop`, `KTwo` at BA need `0 < BAflowLam0 sz z n`, which holds only eventually (`BAflow_lam0_window`), so the drift
classes along the flow are stated with `∀ᶠ n`; `Expand`, `KLink`, the row sums hold at every `n`.
Coupling (UBA-C1; R1 = DECISIONS §273 (1)): no pin compares `BAflowLam0` with `sz.lam`; `withLam` occurs only in the law
`seqP (sz.withLam 0)` and in `WalkForm` at the walk coupling `0`.  TN-C4: no `STGridRepNgL` below.
Merged names only.  Statements only; no proof terms, no placeholders.
Run: lake env lean docs/tickets/checks/T2492-check.lean
-/
import RBM3D.Chain.AzumaProxyGen
import RBM3D.Chain.GridEnvelopeGen
import RBM3D.Chain.HierDriftGen
import RBM3D.Chain.Step2EventsGenTw
import RBM3D.Chain.DecayGenTw
import RBM3D.BA.Step2IterBA
import RBM3D.BA.GridRepTailBA
import RBM3D.BA.TwistGridRem2
import RBM3D.BA.TwistGridWTail
import RBM3D.BA.GreenLDE
import RBM3D.BA.KInduct
import RBM3D.BA.KTreeRep
import RBM3D.BA.KBase
import RBM3D.BA.KBound
import RBM3D.BA.CombesThomas
import RBM3D.BA.Ward
import RBM3D.BA.EKPins
import RBM3D.Induction.AzumaProxyN

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the BA carrier and flow (row 0, T8-BA, T1-BA)
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.BA.BAmF
#check @RBM.BA.BAReal
#check @RBM.BA.baFM
#check @RBM.BA.baFMz
#check @RBM.BA.baStep2Mat
#check @RBM.BA.baStep2Mat_Pp
#check @RBM.BA.baStep2Mat_Hpath
#check @RBM.BA.baStep2Mat_KI
#check @RBM.BA.baStep2Mat_Hpath_herm
#check @RBM.BA.baStep2Mat_listLink
#check @RBM.BA.baStep2_oneLoop
#check @RBM.BA.BAKsol
#check @RBM.BA.BAMLoop
#check @RBM.BA.BAMfine
#check @RBM.Gauss.PsiI
#check @RBM.Gauss.PsiI_isHermitian
#check @RBM.Gauss.Sizes.seqHflowBA
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Path.pathP
#check @RBM.Path.pathH
#check @RBM.Path.pathH_isHermitian
#check @RBM.Path.isProbabilityMeasure_pathP
#check @RBM.Path.gridTime
#check @RBM.Path.gridStep
#check @RBM.Path.filt

-- T5s2 (T2474): the carrier classes, the drift, the readings
#check @RBM.BA.StepDecompGen_LoopForm
#check @RBM.BA.StepDecompGen_WalkForm
#check @RBM.BA.StepDecompGen_Hpath_eq
#check @RBM.BA.stepDecompGen_walkForm_band
#check @RBM.BA.QVPropagatedNg
#check @RBM.BA.qvPropagatedNg
#check @RBM.BA.HierDriftGen_KLoop
#check @RBM.BA.HierDriftGen_KTwo
#check @RBM.BA.HierDriftGen_Expand
#check @RBM.BA.HierDriftGen_UStep
#check @RBM.BA.HierDriftGen_KLink
#check @RBM.BA.GridDriftNg
#check @RBM.BA.gridDriftNg_at
#check @RBM.BA.gridDriftNg
#check @RBM.BA.stepErrNg
#check @RBM.BA.predIncNg
#check @RBM.BA.HierarchyNg
#check @RBM.BA.hierarchyNg_of
#check @RBM.Ind.genMatOf
#check @RBM.Ind.loopGenNOf

-- T4s2 (T2473): the good set, the pin, the envelope, the Azuma proxies
#check @RBM.BA.GoodSetNg
#check @RBM.BA.GridGoodNConclg
#check @RBM.BA.GridGoodNgL
#check @RBM.BA.gridGoodNgL_of
#check @RBM.BA.gridDriftNg_envelope
#check @RBM.BA.azumaProxy_Hpath_zerog
#check @RBM.BA.azumaProxy_pos_goodExitTauNg
#check @RBM.BA.azumaProxy_subG_goodExitg
#check @RBM.BA.AzumaSubGNg
#check @RBM.BA.azumaSubGNg
#check @RBM.BA.YMomentsNg
#check @RBM.BA.yMomentsNg
#check @RBM.BA.GridRepTailGen_Ker
#check @RBM.Ind.zero_mem_goodSetN_of_levels
#check @RBM.Ind.azumaProxy_hee_of_levels

-- the family premises of `gridGoodNgL_of` and their merged BA discharges (table F3 of the ticket)
#check @RBM.BA.STSEforLngL
#check @RBM.BA.STKcalDecaygL
#check @RBM.BA.STEKDecaygL
#check @RBM.BA.STDecayLoopUgL
#check @RBM.BA.STKboundgL
#check @RBM.BA.STegtg
#check @RBM.BA.STksimLKg
#check @RBM.BA.STelklkg
#check @RBM.BA.STeeg
#check @RBM.BA.Step34Gen_LCompat
#check @RBM.BA.Step34Gen_KCompat
#check @RBM.BA.Step2EventsGen_Law
#check @RBM.BA.DecayGen_WardPair
#check @RBM.BA.DecayGen_Spec
#check @RBM.Gauss.Sizes.STAny
#check @RBM.BA.Step2EventsGenTw_baFlow
#check @RBM.BA.Step2EventsGenTw_baLaw
#check @RBM.BA.DecayGenTw_baWardPair

-- BA sources of the targets
#check @RBM.BA.EMn2BA_mF_data
#check @RBM.BA.EMn2BA_T0_lt_one
#check @RBM.BA.EMn2BA_SB_zero
#check @RBM.BA.ba_G_data
#check @RBM.BA.BAGt_sub_BAMfine
#check @RBM.BA.BAm_norm_le_one
#check @RBM.BA.BAflow_real
#check @RBM.BA.BAflow_lam0_window
#check @RBM.BA.BAKsol_isKLoopS
#check @RBM.BA.baKsolve
#check @RBM.BA.baKsol_two
#check @RBM.BA.Step2Kern_thetaKer_BA
#check @RBM.BA.Step2Kern_uKer_BA
#check @RBM.BA.twU_eq_uKer
#check @RBM.BA.TwistGridWTail_norm_twU_sub_one_le
#check @RBM.BA.BAuKer_eq_one_add
#check @RBM.BA.EKPins_norm_Theta_le
#check @RBM.BA.TwistGridRem_envelope_word
#check @RBM.BA.TwistGridRem2_condExp_step
#check @RBM.BA.BAMB_ct_core
#check @RBM.BA.BAMB_row_l1
#check @RBM.BA.BAMB_diag_eq
#check @RBM.BA.BAMLoop_trace
#check @RBM.BA.gridRepTailGen_ker_BA
#check @RBM.BA.baKbound_holds
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.Gauss.SizesInst.sz0

/-! ## Part 2: pins (content binding) -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 1 (a), `baStep2Mat_walkForm`** (supervisor 0149 O4): the walk class of T5s2 at the BA carrier, for every `lam0, E`:
walk coupling `0`, shift `lam0 n • Ψ` (`Pp`, `Hpath` definitional, `BA/Step2BA.lean:68, 70`; the `Ψ` clause from
`baStep2Mat_Hpath_herm` at `k = 0`, or `PsiI_isHermitian` as in `BA/ConArg.lean:308-316`).  It is `hW` of `gridGoodNgL_of`. -/
def T2492_WalkForm : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ),
    StepDecompGen_WalkForm (baStep2Mat sz lam0 E) 0 (fun n => ((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n))

/-- **Target 1 (b)** (T2473 Amend 1 S2; supervisor 2351 T4S2-C3): `Im m ≤ 1` at the BA family along the flow, every `n`
(`EMn2BA_mF_data`, the `BAflow_real` + `BAm_norm_le_one` chain; no `open private`). -/
def T2492_ImLeOne : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ n : ℕ, ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).m n).im ≤ 1

/-- **Target 1 (c)**: the variance law of the BA walk, `S = SB d L 0` (`EMn2BA_SB_zero`): the premise `hS` of
`qvPropagatedNg` and `hierarchyNg_of` at `g = 0`. -/
def T2492_SLaw : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ), (baStep2Mat sz lam0 E).S n = SB d (sz.L n) 0

/-- **Target 1 (c)**: the law of the BA walk is a probability measure (`isProbabilityMeasure_pathP (sz.withLam 0)`), the instance
argument of `AzumaSubGNg`, `SubGaussFormNg` at BA. -/
def T2492_ProbPp : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ), IsProbabilityMeasure (baStep2Mat sz lam0 E).Pp

/-- **Target 2, `KLink`** (definitional, `baStep2Mat_KI`), for every `lam0, E`. -/
def T2492_KLink : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ), HierDriftGen_KLink (baStep2Mat sz lam0 E) n

/-- **Targets 2-4, per index** (the T2474 BA shape, `T2474-check.lean:373-376`): `KLoop` (`BAKsol_isKLoopS (baKsolve d)`,
`S = 1`, initial data `BAMLoop`), `KTwo` (`baKsol_two`, `Step2Kern_thetaKer_BA`; the class-(t) twin, C6) and `UStep`
(K3 from `TwistGridWTail_norm_twU_sub_one_le`; the order-2 field new) at one index with `0 < lam0 n` and `BAReal`. -/
def T2492_KClasses : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (κ : ℝ), 0 < κ → 0 < lam0 n →
    BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n) →
      HierDriftGen_KLoop (baStep2Mat sz lam0 E) n ∧ HierDriftGen_KTwo (baStep2Mat sz lam0 E) n ∧
        HierDriftGen_UStep (baFM sz lam0 E) n

/-- **Target 5, `Expand`** (per index under `BAReal`; no merged BA statement): the freeze at coupling `0`, the word envelope
`TwistGridRem_envelope_word` for the loop word, the generator `genMatOf 0` written as `treeEqRhsS (S) + STegtMg`. -/
def T2492_Expand : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (κ : ℝ), 0 < κ →
    BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n) →
      ∀ (s t : ℕ → ℝ) (K : ℕ → ℕ), HierDriftGen_Expand (baStep2Mat sz lam0 E) s t K n

/-- **Target 6, `baHierDrift_classes`** (finding F1): along the BA flow, `Expand`, `KLink` and the row sums at every index, and
`KLoop`, `KTwo`, `UStep` eventually (the window `0 < BAflowLam0 sz z n`, `BAflow_lam0_window`). -/
def T2492_DriftClasses : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
    (∀ (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ),
        HierDriftGen_Expand (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s t K n) ∧
      (∀ n : ℕ, HierDriftGen_KLink (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n) ∧
      (∀ (n : ℕ) (a : Zd d (sz.L n)),
        ∑ b : Zd d (sz.L n), ‖(baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).S n a b‖ ≤ 1) ∧
      ∀ᶠ n in Filter.atTop,
        HierDriftGen_KLoop (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n ∧
          HierDriftGen_KTwo (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n ∧
          HierDriftGen_UStep (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).toFlowFM n

/-- **Target 7, `baGoodSetNg_init`** (supervisor 2351 T4S2-C2, F5): the initial membership at BA, the hypothesis `h0` of
`azumaProxy_pos_goodExitTauNg`, in the eventual form.  The (D4) level `C₀` depends on `(d, κ, ε, 𝔡, k)` only and is fixed before
`(𝔠, sz, z)` (supervisor 0349 U5S-C3, the F1 pattern).  Route (ticket F2): `G₀ = M`, `𝒦₀ = 𝓛₀ = BAMLoop`, `M_aa = m`; the far
clauses through Combes-Thomas (`BAMB_ct_core`), (D4) through `BAMB_row_l1`. -/
def T2492_InitMem : Prop :=
  ∀ {d : ℕ} (κ ε 𝔡 : ℝ), 0 < κ → 0 < ε → 0 < 𝔡 → ∀ k : ℕ, 1 ≤ k → ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ Γ Λ Φ : ℕ → ℝ, (∀ n, 0 ≤ Γ n) → (∀ n, 1 ≤ Γ n * Φ n) → (∀ n, C₀ ≤ Γ n * (Γ n * Λ n)) →
        ∀ τ' D' : ℝ, 0 < τ' → 0 < D' →
          ∀ᶠ n in Filter.atTop, ∀ (s v : ℕ → ℝ) (K : ℕ → ℕ) (ω : PathΩ sz), s n = 0 →
            GoodSetNg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (gridTime s v K n 0) k (Γ n) (Λ n) (Φ n) τ' D'
              ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Hpath s v K n 0 ω)

/-- **Target 8, `baGridGood_holds`**: T4s2a's pin `GridGoodNgL` at the BA family `(seqP ∘ withLam 0, BAFlow, baStep2Mat, BAflowT0)`
(the shape of `Chain/Step34GenTw.lean:89-90`), every `d`, through `gridGoodNgL_of` (premise table F3 of the ticket). -/
def T2492_BAGridGood (d : ℕ) : Prop :=
  GridGoodNgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => BAflowT0 sz z)

/-! ### Shapes (not binding) -/

/-- Target 6, the eventual drift reading `baGridDrift_ev` (finding F1): `gridDriftNg_at` for `n` past the window, with the BA
`LoopForm` as a hypothesis (T2486's `baStep2Mat_loopForm` closes it). -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
  let Cm := baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z);
  StepDecompGen_LoopForm Cm (BAflowEs sz z) →
  ∀ (s t : ℕ → ℝ) (K : ℕ → ℕ), (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
  ∀ᶠ n in Filter.atTop, ∀ j : ℕ, j < K n → ∀ k : ℕ, 2 ≤ k → ∀ (σ : Fin k → Bool) (Bk : ℝ), 0 ≤ Bk →
    (∀ w ∈ Set.Icc (0 : ℝ) (gridTime s t K n (j + 1)), ∀ J : LoopIdx (Zd d (sz.L n)), J.WF →
      2 ≤ J.length → J.length ≤ k → ‖Cm.KI n w J‖ ≤ Bk) →
    ∀ᵐ ω ∂(Cm.Pp), ∀ a : Fin k → Zd d (sz.L n),
      ‖predIncNg Cm s t K n j σ ω a - (gridStep s t K n : ℂ) *
          (∑ l ∈ Finset.Icc 3 k, STksimLKMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) l (KLloopOf d (sz.L n) σ a) +
            STelklkMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a) +
            STegtMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a))‖ ≤
        stepErrNg Cm.toFlowFM n k (gridTime s t K n j) (gridTime s t K n (j + 1)) (gridStep s t K n) Bk

/-- Target 9, the envelope `baGridDrift_envelope`: the conclusion of `gridDriftNg_envelope` (`Chain/GridEnvelopeGen.lean:62`) at
the BA family, through a private copy with the eventual drift (finding F1); `hη` from target 1 (b), `hKK` from target 2. -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
  let Cm := baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z);
  StepDecompGen_LoopForm Cm (BAflowEs sz z) → STKboundgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) →
  ∀ k : ℕ, 2 ≤ k → ∀ τK : ℝ, 0 < τK → ∀ (s t : ℕ → ℝ) (K : ℕ → ℕ), (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) →
    (∀ n, t n ≤ BAflowT0 sz z n) → (∀ n, K n ≠ 0) → ∀ σ : Fin k → Bool,
    ∀ᶠ n in Filter.atTop, ∀ᵐ ω ∂(Cm.Pp), ∀ j : ℕ, j < K n → ∀ a : Fin k → Zd d (sz.L n),
      ‖predIncNg Cm s t K n j σ ω a - (gridStep s t K n : ℂ) *
          (∑ l ∈ Finset.Icc 3 k, STksimLKMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) l (KLloopOf d (sz.L n) σ a) +
            STelklkMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a) +
            STegtMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a))‖ ≤
        stepErrNg Cm.toFlowFM n k (gridTime s t K n j) (gridTime s t K n (j + 1)) (gridStep s t K n)
          (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s t K n (j + 1)))⁻¹ ^ k)

/-- Target 6, the quadratic variation at BA (`qvPropagatedNg` at `g = 0`, with target 1 (c)). -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ),
  StepDecompGen_LoopForm (baStep2Mat sz lam0 E) E → QVPropagatedNg (baStep2Mat sz lam0 E) 0

/-- Target 10, the `Y` moments at BA (`yMomentsNg`; K1-K4 from `gridRepTailGen_ker_BA` under `BAflow_real`). -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
  StepDecompGen_LoopForm (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (BAflowEs sz z) →
  ∀ (κm τ' : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ), YMomentsNg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) κm τ' s t K

/-- Target 10, the Azuma sub-Gaussian pin at BA (`azumaSubGNg` with target 1 (a); the instance argument is target 1 (c)). -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) [IsProbabilityMeasure (baStep2Mat sz lam0 E).Pp]
  (s t : ℕ → ℝ) (K : ℕ → ℕ), AzumaSubGNg (baStep2Mat sz lam0 E) 0 s t K

/-- Target 8, the conditional form `baGridGood_of`: input (a) of the ticket, the four T2486 (a) pins verbatim
(`T2486-check.lean:196-260`: `T2486_BAKcalDecay`, `T2486_BACarrierFacts` in its Amend 1 form, `T2486_BASEforLn`,
`T2486_BAEtermDecay`), then the pin.  `hFlow`, `hLaw`, `hWard` are merged, `hW` is target 1 (a), `hSpec` is inline (`κm = κ`). -/
example : Prop := ∀ d : ℕ,
  (3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → STKcalDecaygL (baFMz sz z)) →
  ((∀ (sz : Sizes d) (lam0 E : ℕ → ℝ),
      Step34Gen_LCompat (baStep2Mat sz lam0 E) (sz.seqHflowBA lam0) ∧ Step34Gen_KCompat (baStep2Mat sz lam0 E)) ∧
    (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_LoopForm (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (BAflowEs sz z))) →
  (∀ (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop),
    STSEforLngL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => sz.seqHflowBA (BAflowLam0 sz z))
      (fun sz z => BAflowT0 sz z)) →
  (3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ,
    (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    STDecayLoopUgL (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).toFlowFM (Sizes.seqP (sz.withLam 0)) s t →
    ∀ k : ℕ, 2 ≤ k → ∀ σ : Fin k → Bool,
      STEKDecaygL (Sizes.seqP (sz.withLam 0)) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STegtg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (sz.seqHflowBA (BAflowLam0 sz z)) n (v : ℝ) ω
            ⟨List.ofFn σ, List.ofFn a⟩) ∧
        (∀ l : ℕ, STEKDecaygL (Sizes.seqP (sz.withLam 0)) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STksimLKg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (sz.seqHflowBA (BAflowLam0 sz z)) n (v : ℝ) ω l
            ⟨List.ofFn σ, List.ofFn a⟩)) ∧
        STEKDecaygL (Sizes.seqP (sz.withLam 0)) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STelklkg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (sz.seqHflowBA (BAflowLam0 sz z)) n (v : ℝ) ω
            ⟨List.ofFn σ, List.ofFn a⟩) ∧
        STEKDecaygL (Sizes.seqP (sz.withLam 0)) s t (m := k + k) (fun n v ω (b : Fin (k + k) → Zd d (sz.L n)) =>
          STeeg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (sz.seqHflowBA (BAflowLam0 sz z)) n (v : ℝ) ω σ
            (fun i => b (Fin.castAdd k i)) (fun i => b (Fin.natAdd k i)))) →
  T2492_BAGridGood d

/-- UBA-C1 as amended (DECISIONS §273 (1)): the R1 literal, the only admissible comparison text if a target statement ever crosses
size level and kernel level (not expected; ticket UBA-C1 table). -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (gK : ℕ → ℝ) (A : ℝ),
  ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2

end RBM.BA

end
