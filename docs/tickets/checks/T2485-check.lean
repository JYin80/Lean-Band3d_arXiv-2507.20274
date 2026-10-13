/-
Release check for T2485 (dispatcher V3, 2026-10-13 02:11 UTC; DECISIONS §285).  U U5c = `BA/Step5IIIGood` (+ named second file
`BA/Step5IIIGood2`): the realized control `J♯`, the per-time good event and its probability for BA case (iii) of Step 5
(design `docs/reports/T2459-design.md` U5-2 `:173-174`, U5-3 `:185`, row U5c `:256`; probe `t/T2459:RBM3D/Probe/T2459Pins.lean`
`:107-128`, `:170-195`, `:373`, never merged; audit O2 `docs/reports/T2459-audit.md:116-120`).
The good event concludes the matrix part of U5b's premise bundle (T2482 target 3, `BAStep5IIIEMatrix`, not merged).
`T2485_BAScalar`, `T2485_BAMatrix` below are verbatim copies of `docs/tickets/checks/T2482-check.lean:155-176` (one text,
X1-C4).  They follow the text fixed at T2482's 1a-audit and are definitionally equal to `BAStep5IIIEScalar`,
`BAStep5IIIEMatrix` once U5b-1 merges.
Coupling (supervisor 1457 UBA-C1; R1 = supervisor 1752 TN-C1, DECISIONS §273 (1)): not triggered.  The regime, `Bctl`,
`STWB`, `ellT` read `sz.lam` (size level); the kernel objects are `baFMz sz z`, `baStep2Mat` and `seqHflowBA` at
`BAflowLam0 sz z`; no `lam0 ≤ sz.lam`, no comparison text, no `A`.  No grid statement (TN-C4): no `STGridRepNgL` below.
Part 1: merged names.  Part 2: pins (prefix `T2485_`): `T2485_BAScalar`, `T2485_BAMatrix` (copies, binding as T2482's
text); `T2485_JsharpSpec`, `T2485_BAGood`, `T2485_BAGoodThm` (the probe texts `:170`, `:186`, `:191`; the last with the four
corrections of the ticket's note (2); binding); `T2485_MatrixLevel`, `T2485_ScalarFlow` (new; binding, an equivalent
restatement only if the 1a reports it); then shapes (not binding): the interpolation (vi), the instances, the composed
instance of audit O2, R1 at BA for the record.  Part 3: the band twins (unchanged; not edited).
Merged names only.  No proof terms, no placeholders.
Run: lake env lean docs/tickets/checks/T2485-check.lean
-/
import RBM3D.Chain.Step5Gen
import RBM3D.Chain.Step2Gen
import RBM3D.Chain.Carrier
import RBM3D.Chain.Step34Gen
import RBM3D.Chain.Step34GenTw
import RBM3D.BA.Step2BA
import RBM3D.BA.FlowPins
import RBM3D.BA.KBound
import RBM3D.BA.KInduct
import RBM3D.BA.EMn2BA
import RBM3D.BA.GreenSchur
import RBM3D.BA.Step1Fam
import RBM3D.BA.Step1Prime
import RBM3D.BA.Step5IIIKer
import RBM3D.Graph.BAAuxGraph2
import RBM3D.Gauss.BlockAnderson
import RBM3D.Gauss.FineModel
import RBM3D.Defs.StochDomAt
import RBM3D.Defs.Params
import RBM3D.Path.Walk
import RBM3D.Propagator.Pins
import RBM3D.Induction.Step34Pins
import RBM3D.Induction.Step5Pins
import RBM3D.Induction.EMn2Exp1
import RBM3D.Induction.EMn2Exp2
import RBM3D.Induction.PfStep5Grid
import RBM3D.Induction.PfStep5Alg
import RBM3D.Induction.PfStep5
import RBM3D.Induction.LemDecCalEPrec
import RBM3D.Induction.LemDecCalELip

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the Step 2 vocabulary over a matrix carrier (`Chain/Step2Gen`): loops of a fine matrix, `(𝓛-𝒦)`, the average, `m(σ)`
#check @RBM.BA.Step2Mat
#check @RBM.BA.STLMg
#check @RBM.BA.STLKMg
#check @RBM.BA.STavgMg
#check @RBM.BA.STmsigg
#check @RBM.Gauss.Sizes.STtailTD
#check @RBM.tailTD
#check @RBM.Gauss.zdistInf
-- the BA carrier, the flow data and the flow matrix (Hermitian)
#check @RBM.BA.baStep2Mat
#check @RBM.BA.baStep2Mat_LM
#check @RBM.BA.baStep2Mat_toFlowFM
#check @RBM.BA.baStep2Mat_Hpath
#check @RBM.BA.baFM
#check @RBM.BA.baFMz
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.BA.BAflowT0
#check @RBM.Gauss.Sizes.seqHflowBA
#check @RBM.Graph.BAAuxGraph2_seqHflowBA_herm
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.isProbabilityMeasure_seqP
#check @RBM.Gauss.Sizes.withLam
#check @RBM.Gauss.Sizes.size
-- `≺` at a law, the bad set (index inside the event), the time window
#check @RBM.BA.PrecL
#check @RBM.StochDomAt
#check @RBM.badSetAt
#check @RBM.Path.TimeIcc
-- Steps 2-4 at BA, taken as hypotheses (carrier predicates; BA producers owed: `BAStep2` T1/T1-BA, `STStep3RgL`/`STStep4RgL` U3-BA)
#check @RBM.BA.STAvgUgL
#check @RBM.BA.STGdecayWgL
#check @RBM.BA.STStep2ConclgL
#check @RBM.BA.BAStep2
#check @RBM.BA.STLmaxUgL
#check @RBM.BA.STLKUgL
#check @RBM.BA.STStep3RgL
#check @RBM.BA.STStep4RgL
#check @RBM.BA.STIngR5gL
#check @RBM.Gauss.Sizes.STReg5III
-- merged at BA and used through their names (not hypotheses): Step 1 (G7), the 𝒦 bound (stage K), the 𝒦 far field, `𝒦^{(1)} = m(σ)`
#check @RBM.BA.BAStep1
#check @RBM.BA.baStep1_holds'
#check @RBM.BA.STStep1LoopgL
#check @RBM.BA.STKboundgL
#check @RBM.BA.BAKbound
#check @RBM.BA.baKbound_holds
#check @RBM.BA.baEMn2ExpHK
#check @RBM.Gauss.Sizes.emn2ExpHK
#check @RBM.Gauss.Sizes.emn2ExpEllStar
#check @RBM.BA.baKsol_one
#check @RBM.PropSpin
#check @RBM.BA.BAflow_real
#check @RBM.BA.BAflow_lam0_window
#check @RBM.BA.EMn2BA_T0_lt_one
-- size-level facts (regime, `Bctl`, `STWB`, `ellT`, `WO`, bandwidth)
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.STWB
#check @RBM.Bparam
#check @RBM.ellT
#check @RBM.Gauss.Sizes.WO
#check @RBM.Gauss.Sizes.Bandwidth
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.lam_sq_mul_pow_ge
-- the guarded per-index consequence of R1 at BA (merged, T2481 target 1; read only if the 1a finds a crossing)
#check @RBM.BA.baStep5III_lam0_le_lam
-- the walk vocabulary U5d reads (targets 1, 2)
#check @RBM.Gauss.Sizes.PfStep5Grid_level
#check @RBM.Path.gridTime
-- instance data (`sz0`, `zSeq`, `flow_sz0`, `t₀ > 1/2`)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0
#check @RBM.BA.FlowPinsInst.sz0_lam_pos

/-! ## Part 2: pins (content binding as marked) and shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Copy of `T2482_BAScalar`** (T2482-check `:155-158`, verbatim up to the prefix; binding as T2482's 1a-audit text): the
scalar part of U5b's bundle. -/
def T2485_BAScalar {d : ℕ} (sz : Sizes d) (n : ℕ) (u D Λ K₀ J : ℝ) : Prop :=
  3 ≤ d ∧ 0 ≤ u ∧ u < 1 ∧ 0 < sz.lam n ∧ sz.lam n ^ 2 ≤ 1 - u ∧ 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d ∧ 1 ≤ Λ ∧ 1 ≤ K₀ ∧
    4 ≤ Real.log ((sz.W n : ℕ) : ℝ) ∧ (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D ∧
    1 ≤ J ∧ J ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ)

/-- **Copy of `T2482_BAMatrix`** (T2482-check `:163-176`, verbatim up to the prefix; binding as T2482's 1a-audit text): `H`
Hermitian; (i) the stopped control; (ii) `‖𝒦^{(2)}_{(+,-)}‖ ≤ K₀ M_u⁻¹`; (iii) its far field at `ℓ* = (log W)^{3/2}`;
(iv) `STavgMg`; (v) `𝓛^{(k)}`, `k = 2, 3, 4, 6`; (vi) the `J`-free decay of `(𝓛-𝒦)^{(2)}`. -/
def T2485_BAMatrix {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D Λ K₀ J θ Cd : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : Prop :=
  H.IsHermitian ∧ (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STLKMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ J * STtailTD sz n u D a) ∧
  (∀ a b : Zd d (sz.L n), ‖(baStep2Mat sz lam0 E).K n u ![true, false] ![a, b]‖ ≤ K₀ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ∧
  (∀ a b : Zd d (sz.L n), Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (a - b) : ℝ) →
    ‖(baStep2Mat sz lam0 E).K n u ![true, false] ![a, b]‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)) ∧
  (∀ (σ : Bool) (a : Zd d (sz.L n)), ‖STavgMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ∧
  (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ∧
  (∀ (σ : Fin 3 → Bool) (a : Fin 3 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2) ∧
  (∀ (σ : Fin 4 → Bool) (a : Fin 4 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 3) ∧
  (∀ (σ : Fin 6 → Bool) (a : Fin 6 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 5) ∧
  (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STLKMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (θ * (d * (Cd + 1))) * Λ *
    ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 * Real.exp (-(θ * Real.sqrt (zdistInf d (sz.L n) (a 0 - a 1) : ℝ))) + ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **Target 1** (content binding): `J♯_{u,D}(H) = max(1, max_{σ,a} ‖(𝓛-𝒦)^{(2)}_{u,σ,a}(H)‖ / T_{u,D}(a))` (the probe's
`T2459_BAJsharp`, `:170`, written inline; band `PfStep5Grid_JsharpM`, `Induction/PfStep5Grid.lean:76`) is `≥ 1` and dominates
conjunct (i) at every level `D` (`T_{u,D} ≥ W^{-D} > 0`). -/
def T2485_JsharpSpec (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (D u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
    let J := max 1 (Finset.univ.sup' ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
      (fun p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) =>
        ‖STLKMg (baStep2Mat sz lam0 E) n u H p.1 p.2‖ / STtailTD sz n u D p.2));
    1 ≤ J ∧ ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STLKMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ J * STtailTD sz n u D a

/-- **Target 2** (content binding, new): the bundle's matrix part passes from the level `D` to every lower level `D' ≤ D`, with
the control recomputed at `D'` ((iii), (vi) carry the floor `W^{-D}`; (i) is target 1).  U5d's walk level
`D_u = PfStep5Grid_level W D* u ≤ D*` reads it. -/
def T2485_MatrixLevel (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D D' Λ K₀ J θ Cd : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
    D' ≤ D → T2485_BAMatrix sz lam0 E n u D Λ K₀ J θ Cd H →
      T2485_BAMatrix sz lam0 E n u D' Λ K₀
        (max 1 (Finset.univ.sup' ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
          (fun p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) =>
            ‖STLKMg (baStep2Mat sz lam0 E) n u H p.1 p.2‖ / STtailTD sz n u D' p.2))) θ Cd H

/-- **Target 3 (a)** (content binding; the probe's `T2459_BAgood`, `:186`, with the law written out, `J♯` inline and the matrix
part U5b's text): for `τ', D₁ > 0`, `0 < θ < 1`, eventually, at every `u ∈ [s_n, t_n]`, an event of probability
`≥ 1 - N^{-D₁}` on which the matrix part holds at `H = seqHflowBA`, `Λ = K₀ = N^{τ'}` and the realized control. -/
def T2485_BAGood (sz : Sizes 3) (z : ℕ → ℂ) (s t : ℕ → ℝ) (D Cd : ℝ) : Prop :=
  ∀ τ' D₁ θ : ℝ, 0 < τ' → 0 < D₁ → 0 < θ → θ < 1 → ∀ᶠ n in atTop, ∀ u : TimeIcc s t n, ∃ G : Set sz.SeqΩ,
    Sizes.seqP (sz.withLam 0) Gᶜ ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁)) ∧ ∀ ω ∈ G,
      let H := sz.seqHflowBA (BAflowLam0 sz z) n (u : ℝ) ω;
      let J := max 1 (Finset.univ.sup' ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
        (fun p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz.L n)) =>
          ‖STLKMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (u : ℝ) H p.1 p.2‖ / STtailTD sz n (u : ℝ) D p.2));
      T2485_BAMatrix sz (BAflowLam0 sz z) (BAflowEs sz z) n (u : ℝ) D (((sz.size n : ℕ) : ℝ) ^ τ') (((sz.size n : ℕ) : ℝ) ^ τ')
        J θ Cd H

/-- **Target 3 (b)** (content binding; the probe's `T2459_BAgoodThm`, `:191`, corrected): the merged `STLmaxUgL`, `STLKUgL`
replace the probe's local copies; `0 < ε`, `0 < 𝔡` (for `baEMn2ExpHK`, `baKbound_holds`) and `0 < Cd` (for (vi)) are added;
`STKboundgL` is not a hypothesis (merged at BA: `baKbound_holds`).  The Steps 2-4 inputs are exactly the carrier
predicates of `STIngR5gL` (`Chain/Step5Gen.lean:191`). -/
def T2485_BAGoodThm : Prop :=
  ∀ (κ ε 𝔠 𝔡 Cd : ℝ) (sz : Sizes 3) (z : ℕ → ℂ), 0 < κ → 0 < ε → 0 < 𝔡 → 0 < Cd → BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) → STReg5III sz s t →
      STAvgUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t → STLmaxUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t →
      STLKUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t → STGdecayWgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd →
        ∀ D : ℝ, 0 < D → T2485_BAGood sz z s t D Cd

/-- **Target 4** (content binding, new; audit O2, second half): along a flow in the regime, eventually, every `u ∈ [s_n, t_n]`,
every level `D' ≥ D` and every control `1 ≤ J ≤ W^{1/2}` meet the scalar part at `Λ = K₀ = N^{τ'}` (from `WO`, `Bandwidth`,
`SizeTendsto`). -/
def T2485_ScalarFlow : Prop :=
  ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes 3) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) →
    STReg5III sz s t → ∀ D τ' : ℝ, 0 ≤ τ' →
      (∀ᶠ n in atTop, (((sz.L n : ℕ) : ℝ) ^ 3 * ((sz.W n : ℕ) : ℝ) ^ (6 * 3)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D) →
      ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (D' J : ℝ), D ≤ D' → 1 ≤ J → J ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ) →
        T2485_BAScalar sz n (u : ℝ) D' (((sz.size n : ℕ) : ℝ) ^ τ') (((sz.size n : ℕ) : ℝ) ^ τ') J

/-! ### Shapes (not binding) -/

/-- The interpolation behind (vi) (a model-free step of target 3; the floor `F` stays outside): `min(A₁, A₂ e^{-√r} + F)` is at
most `A₁^{1-θ} A₂^θ e^{-θ√r} + F`. -/
example : Prop := ∀ a A₁ A₂ F θ r : ℝ, 0 ≤ a → 0 ≤ A₁ → 0 ≤ A₂ → 0 ≤ F → 0 < θ → θ < 1 → 0 ≤ r →
  a ≤ A₁ → a ≤ A₂ * Real.exp (-Real.sqrt r) + F → a ≤ A₁ ^ (1 - θ) * A₂ ^ θ * Real.exp (-(θ * Real.sqrt r)) + F

/-- Target 5 (a): the good event at the instance (`sz0`, `zSeq`, `s ≡ 1/10 < t ≡ 1/2 < t₀`, `D = 40`, `Cd = 1`); the flow, window,
regime and `T0` premises are discharged; the four Steps 2-4 predicates stay hypotheses. -/
example : Prop := T2485_BAGoodThm →
  STAvgUgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) →
  STLmaxUgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) →
  STLKUgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) →
  STGdecayWgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) 1 →
    T2485_BAGood SizesInst.sz0 FlowPinsInst.zSeq (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) 40 1

/-- Target 5 (b), the composed instance (audit O2; T2482 dispatcher answer (4)): on the good event and `J♯ ≤ W^{1/2}`, both
parts of the bundle hold at the instance (`θ = 1/10`); the 1b then applies `BAStep5IIIEdet 3` (an exact-type hypothesis,
`T2482_BAEdet 3`, until U5b-2 merges). -/
example : Prop := T2485_BAGoodThm → T2485_ScalarFlow →
  STAvgUgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) →
  STLmaxUgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) →
  STLKUgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) →
  STGdecayWgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) 1 →
  ∀ τ' D₁ : ℝ, 0 < τ' → 0 < D₁ → ∀ᶠ n in atTop, ∀ u : TimeIcc (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) n,
    ∃ G : Set SizesInst.sz0.SeqΩ,
      Sizes.seqP (SizesInst.sz0.withLam 0) Gᶜ ≤ ENNReal.ofReal (((SizesInst.sz0.size n : ℕ) : ℝ) ^ (-D₁)) ∧ ∀ ω ∈ G,
        let H := SizesInst.sz0.seqHflowBA (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) n (u : ℝ) ω;
        let J := max 1 (Finset.univ.sup' ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
          (fun p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (SizesInst.sz0.L n)) =>
            ‖STLKMg (baStep2Mat SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq))
                n (u : ℝ) H p.1 p.2‖ / STtailTD SizesInst.sz0 n (u : ℝ) 40 p.2));
        J ≤ ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ) →
          T2485_BAScalar SizesInst.sz0 n (u : ℝ) 40 (((SizesInst.sz0.size n : ℕ) : ℝ) ^ τ') (((SizesInst.sz0.size n : ℕ) : ℝ) ^ τ') J ∧
          T2485_BAMatrix SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq) n (u : ℝ) 40
            (((SizesInst.sz0.size n : ℕ) : ℝ) ^ τ') (((SizesInst.sz0.size n : ℕ) : ℝ) ^ τ') J (1 / 10) 1 H

/-- Target 5 (c): conjunct (i) of target 1 at `sz0`, `n = 1` (`L = 8`, `W = 1024`), `u = 1/2`, `H = 0`, level `30` (target 2's
instance at the same data moves the bundle from level `40` to `30`). -/
example : Prop := T2485_JsharpSpec 3 →
  ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (SizesInst.sz0.L 1)),
    ‖STLKMg (baStep2Mat SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq)) 1 (1 / 2)
        (0 : Matrix (Idx 3 (SizesInst.sz0.L 1) (SizesInst.sz0.W 1)) (Idx 3 (SizesInst.sz0.L 1) (SizesInst.sz0.W 1)) ℂ) σ a‖ ≤
      max 1 (Finset.univ.sup' ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
        (fun p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (SizesInst.sz0.L 1)) =>
          ‖STLKMg (baStep2Mat SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq)) 1 (1 / 2)
              (0 : Matrix (Idx 3 (SizesInst.sz0.L 1) (SizesInst.sz0.W 1)) (Idx 3 (SizesInst.sz0.L 1) (SizesInst.sz0.W 1)) ℂ) p.1 p.2‖ /
            STtailTD SizesInst.sz0 1 (1 / 2) 30 p.2)) * STtailTD SizesInst.sz0 1 (1 / 2) 30 a

/-- R1 (the one comparison text, TN-C1, DECISIONS §273 (1)) at BA, for the record: no U5c statement reads it (UBA-C1 not
triggered); a crossing found at 1a would use this text or its guarded per-index consequence (`baStep5III_lam0_le_lam`). -/
example : Prop := ∀ {d : ℕ} (κ ε 𝔠 𝔡 : ℝ), 0 < κ → ∀ (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
  ∀ n, 0 ≤ BAflowLam0 sz z n * sz.lam n ∧ BAflowLam0 sz z n ^ 2 ≤ sz.lam n ^ 2 ∧
    sz.lam n ^ 2 ≤ (κ + 1) / κ * BAflowLam0 sz z n ^ 2

end RBM.BA

/-! ## Part 3: the band twins (the good event and `J♯` of the band layer; unchanged, not edited) -/

#check @RBM.Gauss.Sizes.lemDecCalEPrec_good
#check @RBM.Gauss.Sizes.lemDecCalEPrec_prob
#check @RBM.Gauss.Sizes.lemDecCalEPrec_goodDet
#check @RBM.Gauss.Sizes.LemDecCalELip_Jsharp
#check @RBM.Gauss.Sizes.PfStep5Grid_JsharpM
#check @RBM.Gauss.Sizes.PfStep5_walkConcl
#check @RBM.Gauss.Sizes.pfStep5_goodMeas
#check @RBM.Gauss.Sizes.pfStep5Alg_goodProb
#check @RBM.Gauss.Sizes.pfStep5Alg_goodStop'
#check @RBM.Gauss.Sizes.STLmaxU
#check @RBM.Gauss.Sizes.STLKU

end
