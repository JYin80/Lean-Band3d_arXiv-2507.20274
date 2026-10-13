/-
Release check for T2493 (dispatcher V3, 2026-10-13 06:17 UTC; DECISIONS §295).  U U5d = `BA/Step5IIIWalk` (+ named second file
`BA/Step5IIIWalk2`): the stopped grid walk and the lift of BA case (iii) of Step 5 (design `docs/reports/T2459-design.md`
U5-3 `:184-191`, (H1)-(H3) `:168`, row U5d `:257`; probe `t/T2459:RBM3D/Probe/T2459Pins.lean` `:197-226`, never merged).
Coupling (supervisor 1457 UBA-C1; R1 = supervisor 1752 TN-C1, DECISIONS §273 (1)): one crossing, inside the walk (target 6):
the premises `lam0 n ≤ sz.lam n` of `BAStep5IIIKernel` and `BAStep5IIITailSqQV` are read through the merged guarded per-index
consequence `baStep5III_lam0_le_lam` at `0 < BAflowLam0` (window `BAflow_lam0_window`).  No other comparison text, no `A`.
TN-C4: no `STGridRepNgL`; the martingale is clause 4 of `STGridRepNAtgL 3 2` (`baGridRepNAt2_holds 3`).
Part 1: merged names.  Part 2: pins (prefix `T2493_`; content binding as marked), then shapes (not binding).  Part 3: the band
twins (unchanged; not edited).
Merged names only.  No proof terms, no placeholders.
Run: lake env lean docs/tickets/checks/T2493-check.lean
-/
import RBM3D.BA.Step5IIIGood2
import RBM3D.BA.Step5IIIEdet2
import RBM3D.BA.Step5IIIKer2
import RBM3D.BA.GridRepTailBA
import RBM3D.BA.Step2IterBA
import RBM3D.BA.Step2CloseBA
import RBM3D.BA.Step1Prime
import RBM3D.BA.NetLiftBA
import RBM3D.BA.TwistGrid
import RBM3D.Chain.Step2EventsGenTw
import RBM3D.Chain.Step2CloseGen
import RBM3D.Chain.GridDuhamelGen
import RBM3D.Chain.Step5Gen
import RBM3D.Induction.PfStep5
import RBM3D.Induction.Step1Setup
import RBM3D.Induction.ContinuityNet

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- U5a-U5c (merged a2f86197, 6482d46a, e0043e75, 12f5d1ba): the bundle, the ℰ-bounds, `J♯`, the good event, the kernel, (H1)-(H3)
#check @RBM.BA.BAStep5IIIEScalar
#check @RBM.BA.BAStep5IIIEMatrix
#check @RBM.BA.BAStep5IIIEdet
#check @RBM.BA.baStep5IIIEdet_holds
#check @RBM.BA.baStep5IIIE_sumTheta
#check @RBM.BA.BAStep5IIIJsharp
#check @RBM.BA.baStep5IIIJsharp_spec
#check @RBM.BA.baStep5III_matrix_level
#check @RBM.BA.BAStep5IIIGood
#check @RBM.BA.BAStep5IIIGoodThm
#check @RBM.BA.baStep5IIIGoodThm_holds
#check @RBM.BA.baStep5III_scalar_flow
#check @RBM.BA.baStep5III_lam0_le_lam
#check @RBM.BA.BAStep5IIIKernel
#check @RBM.BA.baStep5IIIKernel_holds
#check @RBM.BA.baStep5IIIKernel_at_flow
#check @RBM.BA.baStep5III_Theta_far
#check @RBM.BA.baStep5III_uKer_far
#check @RBM.BA.BAStep5IIITailSq
#check @RBM.BA.BAStep5IIITailSqQV
#check @RBM.BA.baStep5IIITailSqQV_holds
-- P1 = TN-C2 row (T2471, merged): the two-slot tail at `m = 2`; the kernel class K1-K4 (K1 = the semigroup instance); the window, `η`, (H2)
#check @RBM.BA.STGridRepNAtgL
#check @RBM.BA.baGridRepNAt2_holds
#check @RBM.BA.GridRepTailGen_Ker
#check @RBM.BA.gridRepTailGen_ker_BA
#check @RBM.BA.Step2Gen_USemigroup
#check @RBM.BA.BAuKerSemigroup_holds
#check @RBM.BA.gridRepTailBA_eta
#check @RBM.BA.gridRepTailGen_window_BA
#check @RBM.BA.gridRepTailBA_norm_G_le
#check @RBM.BA.gridRepTailBA_STeeMg_norm_le
#check @RBM.BA.gridRepTailBA_measurable_STeeMg
#check @RBM.BA.Step2Kern_uKer_BA
#check @RBM.BA.Step2Kern_UN_BA
-- the grid vocabulary over the carrier: kernel, drift, observable, QV, the stopped Duhamel identity
#check @RBM.BA.Step2Mat
#check @RBM.BA.Step2Gen_uKer
#check @RBM.BA.Step2Gen_UN
#check @RBM.BA.Step2Gen_ThetaN
#check @RBM.BA.STgANg
#check @RBM.BA.STgDriftNg
#check @RBM.BA.STeeMg
#check @RBM.BA.STeeUMg
#check @RBM.BA.STLKMg
#check @RBM.BA.STavgMg
#check @RBM.BA.STELKLKMg
#check @RBM.BA.STEGtMg
#check @RBM.BA.StoppedDuhamelNg
#check @RBM.BA.stoppedDuhamelNg_at
-- the list-loop bridge (merged: T2487 target 3 and T1b's identities)
#check @RBM.BA.Step2IterGen_ListLink
#check @RBM.BA.baStep2Mat_listLink
#check @RBM.BA.STLKMg_eq_STLKIMg
#check @RBM.BA.STELKLKMg_eq_STelklkMg
#check @RBM.BA.STEGtMg_eq_STegtMg
-- the law of the grid walk (`pathP (sz.withLam 0)`) against the model at the grid time; measurability in the matrix
#check @RBM.BA.baStep2Mat
#check @RBM.BA.baStep2Mat_Hpath
#check @RBM.BA.baStep2Mat_Pp
#check @RBM.BA.Step2EventsGenTw_baLaw
#check @RBM.BA.Step2EventsGenTw_baGrid
#check @RBM.BA.Step2EventsGen_STLKMg_measurable
#check @RBM.Gauss.walk_measurable_loopFine
#check @RBM.Gauss.Sizes.ST_pathP_eq_seqP
#check @RBM.Path.pathP
#check @RBM.Path.PathΩ
#check @RBM.Path.gridTime
#check @RBM.Path.TimeIcc
-- the carrier tuple, U6's shape and conclusions
#check @RBM.BA.STIngR5gL
#check @RBM.BA.STPfConclgL
#check @RBM.BA.STPfStep5gL
#check @RBM.BA.STStep5IIIgL
#check @RBM.BA.STTailtoTailConclgL
#check @RBM.BA.baFM
#check @RBM.BA.baFMz
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAReal
#check @RBM.BA.BAmF
#check @RBM.BA.BAflow_real
#check @RBM.BA.BAflow_lam0_window
#check @RBM.BA.EMn2BA_T0_lt_one
#check @RBM.Gauss.Sizes.seqHflowBA
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.withLam
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.STReg5III
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STtailTD
-- the premises of `STIngR5gL` (Steps 1-4 at BA): read (`T2493_ReadPremises`) or carried
#check @RBM.BA.PrecL
#check @RBM.BA.STKboundgL
#check @RBM.BA.STKwardgL
#check @RBM.BA.STLKgL
#check @RBM.BA.STDecaygL
#check @RBM.BA.STDecayStronggL
#check @RBM.BA.STStep1LoopgL
#check @RBM.BA.STStep2ConclgL
#check @RBM.BA.STLocalEntryUgL
#check @RBM.BA.STAvgUgL
#check @RBM.BA.STGdecayWgL
#check @RBM.BA.STLmaxUgL
#check @RBM.BA.STLKUgL
-- merged at BA and used through their names (not hypotheses): stage K, the far field, Step 1 (G7, primed), Step 2 (T1-BA)
#check @RBM.BA.baKbound_holds
#check @RBM.BA.baEMn2ExpHK
#check @RBM.BA.BAStep1
#check @RBM.BA.baStep1_holds'
#check @RBM.BA.BAStep2
#check @RBM.BA.baStep2_holds
#check @RBM.BA.baSTGijDecgL_holds
-- the lift: the BA net lift (T2461) and the continuity core
#check @RBM.BA.STNetLift2gL
#check @RBM.BA.baNetLift2_holds
#check @RBM.Ind.ContinuityNet.cont_core
-- model-free band facts imported (sizes only)
#check @RBM.Gauss.Sizes.PfStep5Grid_level
#check @RBM.Gauss.Sizes.pfStep5Grid_level
#check @RBM.Gauss.Sizes.pfStep5Alg_tailAnti
#check @RBM.Gauss.Sizes.pfStep5Alg_riemann
#check @RBM.Gauss.Sizes.pfStep5Alg_closure
#check @RBM.Gauss.Sizes.pfStep5_farAbsorb
-- size-level facts
#check @RBM.Gauss.Sizes.WO
#check @RBM.Gauss.Sizes.Bandwidth
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.lam_sq_mul_pow_ge
#check @RBM.Gauss.Sizes.Bctl
-- instance data (`sz0`, `zSeq`, `flow_sz0`, `t₀ > 1/2`, `(con_st_ind)` at constant times)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0
#check @RBM.BA.FlowPinsInst.sz0_lam_pos
#check @RBM.Ind.Step1SetupInst.s1Setup_conStInd_const

/-! ## Part 2: pins (content binding as marked) and shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 1 (a)** (content binding; U5c target 2 in the bundle's name, T2485 answer (1)): the matrix part `BAStep5IIIEMatrix`
at `(D, J)` gives it at `(D', J♯(D'))` for `D' ≤ D`.  The 1b states it inline, so that its conclusion head is
`BAStep5IIIEMatrix` (registry, DECISIONS §290 (3)). -/
def T2493_EMatrixLevel (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D D' Λ K₀ J θ Cd : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
    D' ≤ D → BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H →
      BAStep5IIIEMatrix sz lam0 E n u D' Λ K₀ (BAStep5IIIJsharp sz lam0 E n D' u H) θ Cd H

/-- **Target 1 (b)** (content binding): U5c's good event with its matrix part read as `BAStep5IIIEMatrix` (definitional). -/
def T2493_GoodBundle : Prop :=
  ∀ (sz : Sizes 3) (z : ℕ → ℂ) (s t : ℕ → ℝ) (D Cd : ℝ), BAStep5IIIGood sz z s t D Cd →
    ∀ τ' D₁ θ : ℝ, 0 < τ' → 0 < D₁ → 0 < θ → θ < 1 → ∀ᶠ n in atTop, ∀ u : TimeIcc s t n, ∃ G : Set sz.SeqΩ,
      Sizes.seqP (sz.withLam 0) Gᶜ ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁)) ∧ ∀ ω ∈ G,
        BAStep5IIIEMatrix sz (BAflowLam0 sz z) (BAflowEs sz z) n (u : ℝ) D (((sz.size n : ℕ) : ℝ) ^ τ') (((sz.size n : ℕ) : ℝ) ^ τ')
          (BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n D (u : ℝ) (sz.seqHflowBA (BAflowLam0 sz z) n (u : ℝ) ω)) θ Cd
          (sz.seqHflowBA (BAflowLam0 sz z) n (u : ℝ) ω)

/-- **Target 2 (a)** (content binding; band `pfStep5Grid_JsharpM_measurable`, private): `J♯` is measurable in the matrix. -/
def T2493_JsharpMeas (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (D u : ℝ),
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => BAStep5IIIJsharp sz lam0 E n D u H

/-- **Target 2 (b)** (content binding; band `pfStep5_goodMeas`, `Induction/PfStep5.lean:270`; T2485 answer (4)): the matrix
part at the realized control is a measurable set of matrices, so the good set of U5c contains the preimage under
`seqHflowBA` of a measurable set, and `Step2EventsGenTw_baLaw` moves it to the grid walk. -/
def T2493_GoodMeas (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D Λ K₀ θ Cd : ℝ),
    MeasurableSet {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
      BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ (BAStep5IIIJsharp sz lam0 E n D u H) θ Cd H}

/-- **Target 3** (content binding; (H2) of `BAStep5IIITailSqQV` at the flow; band `difRep2_norm_STeeM_le_N`, `Path/DifREP2.lean:1277`):
eventually, for `u ≤ t n ≤ t₀` and Hermitian `H`, `‖STeeMg‖ ≤ 2N(16N)⁶`, the `Y` of `pfStep5_farAbsorb`.  Sources:
`gridRepTailBA_STeeMg_norm_le` at `η = 1/(16N)`, `gridRepTailBA_eta` (`N^ε ≥ 1/(8κ)` eventually). -/
def T2493_CrudeQV (d : ℕ) : Prop :=
  ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → 0 < ε → BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ,
    (∀ n, t n ≤ BAflowT0 sz z n) → ∀ᶠ n in atTop, ∀ u : ℝ, u ≤ t n →
      ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
        ∀ (σ : Fin 2 → Bool) (b b' : Fin 2 → Zd d (sz.L n)),
          ‖STeeMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n u H σ b b'‖ ≤
            2 * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ 6

/-- **Target 4** (content binding; band `pfStep5_perj`, `Induction/PfStep5.lean:1406`): on the matrix part at the crude level `D*` and
`J♯(u, D_u) < W^{ε₀}` (`ε₀ ≤ 1/2`), both bundle parts hold at the walk level `D_u = PfStep5Grid_level W D* u`, with the control
`J♯(u, D_u)` and `Λ = K₀ = N^{τ'}`.  Reads U5c target 2 (`baStep5III_matrix_level`, `D_u ≤ D*`) and target 4
(`baStep5III_scalar_flow` at `D* - 6 ≤ D_u`, from `1 - u ≥ lam² ≥ W^{-3}`). -/
def T2493_WalkLevel : Prop :=
  ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes 3) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) →
    STReg5III sz s t → ∀ Dst τ' θ Cd ε₀ : ℝ, 0 ≤ τ' → ε₀ ≤ 1 / 2 →
    (∀ᶠ n in atTop, (((sz.L n : ℕ) : ℝ) ^ 3 * ((sz.W n : ℕ) : ℝ) ^ (6 * 3)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ (Dst - 2 * 3)) →
    ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (H : Matrix (Idx 3 (sz.L n) (sz.W n)) (Idx 3 (sz.L n) (sz.W n)) ℂ),
      BAStep5IIIEMatrix sz (BAflowLam0 sz z) (BAflowEs sz z) n (u : ℝ) Dst (((sz.size n : ℕ) : ℝ) ^ τ') (((sz.size n : ℕ) : ℝ) ^ τ')
        (BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n Dst (u : ℝ) H) θ Cd H →
      BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u : ℝ)) (u : ℝ) H <
        ((sz.W n : ℕ) : ℝ) ^ ε₀ →
      BAStep5IIIEScalar sz n (u : ℝ) (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u : ℝ)) (((sz.size n : ℕ) : ℝ) ^ τ')
          (((sz.size n : ℕ) : ℝ) ^ τ')
          (BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u : ℝ)) (u : ℝ) H) ∧
        BAStep5IIIEMatrix sz (BAflowLam0 sz z) (BAflowEs sz z) n (u : ℝ) (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u : ℝ))
          (((sz.size n : ℕ) : ℝ) ^ τ') (((sz.size n : ℕ) : ℝ) ^ τ')
          (BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u : ℝ)) (u : ℝ) H) θ Cd H

/-- **Target 5** (content binding up to the constant `Cdu` and the exponent `7`, which the 1a fixes and reports; band
`pfStep5Grid_duhamel`, `Induction/PfStep5Grid.lean:892`, with `Step2Gen_UN`, `Step2Gen_ThetaN` at `baFM` in place of `Ugen`, `ThetaN`
at `mSigma E`, and `BAReal` in place of `|E| ≤ 2`): the Duhamel form `(int_K-L_ST)` from the additive grid decomposition of
clause 1 of `STGridRepNAtgL`; the martingale sum is the one of clause 4. -/
def T2493_Duhamel (d : ℕ) : Prop :=
  ∃ Cdu : ℝ, 0 < Cdu ∧ ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (κ : ℝ), 0 < κ →
    BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n) →
    ∀ (Δ M R : ℝ) (σ : Fin 2 → Bool) (k : ℕ) (u : ℕ → ℝ) (A F Rem Mart : ℕ → (Fin 2 → Zd d (sz.L n)) → ℂ),
      0 ≤ Δ → 0 ≤ u 0 → (∀ j, u (j + 1) = u j + Δ) → u k < 1 →
      (∀ j, j ≤ k → ∀ b, ‖A j b‖ ≤ M) → (∀ j, j ≤ k → ∀ b, ‖Rem j b‖ ≤ R) →
      (∀ j, j ≤ k → ∀ b, A j b = A 0 b + (Δ : ℂ) * ∑ i ∈ Finset.range j,
          (Step2Gen_ThetaN (baFM sz lam0 E) n σ (u i) (A i) b + F i b) + Rem j b + Mart j b) →
      ∀ a, ‖A k a - Step2Gen_UN (baFM sz lam0 E) n σ (u 0) (u k) (A 0) a -
          ∑ j ∈ Finset.range k, (Δ : ℂ) * Step2Gen_UN (baFM sz lam0 E) n σ (u j) (u k) (F j) a -
          ∑ j ∈ Finset.range k,
            Step2Gen_UN (baFM sz lam0 E) n σ (u j) (u k) (fun b => Mart (j + 1) b - Mart j b) a‖ ≤
        Cdu * ((1 - u k)⁻¹) ^ 7 * (R + Δ * M)

/-- **Target 6 (a)** (content binding; the probe's `T2459_BAWalkConcl`, `:199`, with `J♯` the merged `BAStep5IIIJsharp`; band
`PfStep5_walkConcl`, `Induction/PfStep5.lean:79`): the grid conclusion b1-b3 at the BA carrier. -/
def T2493_BAWalkConcl {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < ε₁ → ∀ D : ℝ, 0 < D → ∃ Dst : ℝ, D + 2 * (d : ℝ) ≤ Dst ∧
    ∀ tt : ∀ n, TimeIcc s t n, ∀ D' : ℝ, 0 < D' → ∃ K : ℕ → ℕ, (∀ n, K n ≠ 0) ∧ ∀ᶠ n in atTop,
      (baStep2Mat sz lam0 E).Pp {ω | ∀ k, k ≤ K n → BAStep5IIIJsharp sz lam0 E n
          (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s (fun m => (tt m : ℝ)) K n k)) (gridTime s (fun m => (tt m : ℝ)) K n k)
          ((baStep2Mat sz lam0 E).Hpath s (fun m => (tt m : ℝ)) K n k ω) < ((sz.W n : ℕ) : ℝ) ^ ε₀}ᶜ ≤
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D'))

/-- **The premises of `STIngR5gL` the walk reads** (content binding as a read set: the 1b reads no other premise of the shape;
the 1a may drop a member, never add one without a stop).  `STDecayStronggL` at `s` is the initial term (band
`pfStep5_init_le`; ticket question (1)); the other four go to `baStep5IIIGoodThm_holds`.  Carried unread: `STKboundgL`,
`STKwardgL`, `STLKgL`, `STDecaygL`, `STConStInd`, `STStep1LoopgL`, `STLocalEntryUgL`. -/
def T2493_ReadPremises (sz : Sizes 3) (z : ℕ → ℂ) (s t : ℕ → ℝ) (Cd : ℝ) : Prop :=
  STDecayStronggL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s ∧ STAvgUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t ∧
    STGdecayWgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd ∧ STLmaxUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t ∧
    STLKUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t

/-- **Target 6 (b)** (content binding; the per-flow walk, conclusion head `BAStep5IIIWalkConcl`): the grid conclusion from the
flow, the horizon, the regime and the five read premises. -/
def T2493_WalkAt : Prop :=
  ∀ (κ ε 𝔡 Cd : ℝ), 0 < κ → 0 < ε → 0 < 𝔡 → 0 < Cd → ∀ (𝔠 : ℝ) (sz : Sizes 3) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) → STReg5III sz s t →
      T2493_ReadPremises sz z s t Cd → T2493_BAWalkConcl sz (BAflowLam0 sz z) (BAflowEs sz z) s t

/-- **Target 6 (c)** (content binding; the probe's `T2459_BAWalk`, `:213`): the walk pin, the shape of `STPfStep5gL` with the grid
conclusion.  An input of U5e. -/
def T2493_BAWalk : Prop :=
  STIngR5gL 3 STReg5III (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0
    (fun sz z s t => T2493_BAWalkConcl sz (BAflowLam0 sz z) (BAflowEs sz z) s t)

/-- **Target 7** (content binding; the probe's `T2459_BAfromWalk`, `:218`, with correction (a): `0 < ε`, `0 < 𝔡` added for the
`η`-window and the `𝒦` window of the net lift): endpoint, sections, descent `D_u ≥ D` and the net lift give `STPfConclgL`.
An input of U5e. -/
def T2493_BAFromWalk : Prop :=
  ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes 3) (z : ℕ → ℂ), 0 < κ → 0 < ε → 0 < 𝔡 → BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) → STReg5III sz s t →
      T2493_BAWalkConcl sz (BAflowLam0 sz z) (BAflowEs sz z) s t → STPfConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t

/-! ### Shapes (not binding) -/

/-- The closure `T2459_BAclosure` (`:224`) with its four inputs, each merged: `baGridRepNAt2_holds 3`, `baStep5IIIKernel_holds 3`,
`baStep5IIIEdet_holds 3`, `baStep5IIIGoodThm_holds`.  It is the proof of `baStep5IIIWalk_holds`, not a public text (X1-C4). -/
example : Prop :=
  (∃ C₀ : ℝ, 0 ≤ C₀ ∧ STGridRepNAtgL 3 2 C₀ BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0) →
    BAStep5IIIKernel 3 → BAStep5IIIEdet 3 → BAStep5IIIGoodThm → T2493_BAWalk

/-- The per-flow walk gives the walk pin (`𝔠d = 1/100`, as the band `pfStep5_walk`): the five read premises are projections of
the premises of `STIngR5gL` (`STStep2ConclgL` conjuncts 2-3, the inline Steps 3-4 premises). -/
example : Prop := T2493_WalkAt → T2493_BAWalk

/-- U5e's reading (the probe's `T2459_main_of_parts`, `:227`): the target `STPfStep5gL` at BA from the two inputs. -/
example : Prop := T2493_BAWalk → T2493_BAFromWalk →
  STPfStep5gL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0

/-- Target 8 (a): the walk and the lift at the instance (`sz0`, `zSeq`, `flow_sz0`, `s ≡ 1/10 < t ≡ 1/2 < t₀`, `Cd = 1`); the regime
and `(con_st_ind)` (`s1Setup_conStInd_const`) are discharged; the Steps 1-4 carrier predicates stay hypotheses. -/
example : Prop := T2493_BAWalk → T2493_BAFromWalk →
  STKboundgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) →
  STKwardgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) →
  STLKgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) →
  STDecaygL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) →
  STDecayStronggL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) →
  STStep1LoopgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) →
  STStep2ConclgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) 1 →
  STLmaxUgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) →
  STLKUgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) →
    STPfConclgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ))

/-- Target 8 (b): target 2 at `n = 1` (`L = 8`, `W = 1024`), `u = 1/2`, level `40`: the stopping set of the walk is measurable. -/
example : Prop := T2493_JsharpMeas 3 →
  MeasurableSet {H : Matrix (Idx 3 (SizesInst.sz0.L 1) (SizesInst.sz0.W 1)) (Idx 3 (SizesInst.sz0.L 1) (SizesInst.sz0.W 1)) ℂ |
    BAStep5IIIJsharp SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq) 1 40 (1 / 2) H <
      ((SizesInst.sz0.W 1 : ℕ) : ℝ) ^ (1 / 100 : ℝ)}

/-- Target 8 (c): target 3 along the instance, `t ≡ 1/2`. -/
example : Prop := T2493_CrudeQV 3 → ∀ᶠ n in atTop, ∀ u : ℝ, u ≤ 1 / 2 →
  ∀ H : Matrix (Idx 3 (SizesInst.sz0.L n) (SizesInst.sz0.W n)) (Idx 3 (SizesInst.sz0.L n) (SizesInst.sz0.W n)) ℂ, H.IsHermitian →
    ∀ (σ : Fin 2 → Bool) (b b' : Fin 2 → Zd 3 (SizesInst.sz0.L n)),
      ‖STeeMg (baStep2Mat SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq)) n u H σ b b'‖ ≤
        2 * ((SizesInst.sz0.size n : ℕ) : ℝ) * (16 * ((SizesInst.sz0.size n : ℕ) : ℝ)) ^ 6

/-- R1 at BA for the record, in the guarded per-index form the walk reads (= `baStep5III_lam0_le_lam`): `0 < g₀ → g₀ ≤ sz.lam`. -/
example : Prop := ∀ {d : ℕ} (κ ε 𝔠 𝔡 : ℝ), 0 < κ → ∀ (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
  ∀ n, 0 < BAflowLam0 sz z n → BAflowLam0 sz z n ≤ sz.lam n

end RBM.BA

/-! ## Part 3: the band twins (the walk, the lift and their layers; unchanged, not edited) -/

#check @RBM.Gauss.Sizes.PfStep5_walkConcl
#check @RBM.Gauss.Sizes.pfStep5_goodMeas
#check @RBM.Gauss.Sizes.pfStep5_walk
#check @RBM.Gauss.Sizes.pfStep5_PT_of_walk
#check @RBM.Gauss.Sizes.pfStep5_lift
#check @RBM.Gauss.Sizes.stPfStep5_holds
#check @RBM.Gauss.Sizes.stStep5III_holds
#check @RBM.Gauss.Sizes.PfStep5Grid_JsharpM
#check @RBM.Gauss.Sizes.pfStep5Grid_duhamel
#check @RBM.Gauss.Sizes.pfStep5Alg_ugenSum'
#check @RBM.Gauss.Sizes.lemDecCalEPrec_lift

end
