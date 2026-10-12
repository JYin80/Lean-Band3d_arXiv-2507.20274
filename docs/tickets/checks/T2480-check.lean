/-
Release check for T2480 (dispatcher V3, Mon Oct 12 23:12 UTC 2026; DECISIONS §280).  U U2 (sub-stage U, ST side): `lem:SEforLn`, the Eterm decays
(T7a target 7), `(eq:Ward_typeP)` / `(y27kasdfg)` and the time-uniform `𝒦` bounds over the carrier, in the new files
`Chain/KDecayGen.lean`, `Chain/SEforLnGen.lean` (U2a) and `Chain/B45Gen.lean` (U2b); the band files `Induction/SEforLn1`,
`SEforLn2`, `B45`, `KDecay`, `DecayLoopB` are not edited (outside the certificate lane).  The class-(t) segment of `KDecay`
(§1-§8) is not restated: its generic form is T7a's premise `STKcalDecaygL` (C6, supervisor 1155 `:182-187`).
Part 1: merged names.  Part 2: the target statements as Prop values (prefix `T2480_`): the two family classes and the
conclusions are content binding (a class field may be added or dropped only with a named band discharge, reported in
1a (iii)); the hypothesis lists of the per-carrier results are shapes fixed in 1a (iii).  Then shapes (not binding): band
discharges, the BA readings (U2-BA), the UBA-C1 literal.  Part 3 (G1): the public band names the row restates or that
other rows read, unchanged; the auditor adds `example : <statement> := <name>` for each.
Merged names only; statements only.
Run: lake env lean docs/tickets/checks/T2480-check.lean
-/
import RBM3D.Chain.Step34GenTw
import RBM3D.Chain.DecayGenTw
import RBM3D.Chain.StepDecompGen
import RBM3D.Chain.ZeroModeGen
import RBM3D.Chain.Step5CasesGen
import RBM3D.Chain.Step5KerGen
import RBM3D.Induction.SEforLn2
import RBM3D.Induction.B45
import RBM3D.BA.KBound
import RBM3D.BA.KInduct
import RBM3D.BA.Ward
import RBM3D.BA.TwistStep2
import RBM3D.BA.Prop6Path
import RBM3D.BA.KTreeRep
import RBM3D.BA.EMn2BA

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the carrier and T8b's Step 2 family (U-C4: the kernels are `Step2Gen_ThetaN`, `Step2Gen_thetaKer`, `Step2Gen_UN`)
#check @RBM.BA.FlowFM
#check @RBM.BA.Step2Mat
#check @RBM.BA.bandFM
#check @RBM.BA.bandStep2Mat
#check @RBM.BA.PrecL
#check @RBM.BA.STKboundgL
#check @RBM.BA.STKwardgL
#check @RBM.BA.STStep2ConclgL
#check @RBM.BA.STAvgUgL
#check @RBM.BA.STGdecayWgL
#check @RBM.BA.STmsigg
#check @RBM.BA.STLIMg
#check @RBM.BA.STegtMg
#check @RBM.BA.STksimLKMg
#check @RBM.BA.STelklkMg
#check @RBM.BA.STeeMg
#check @RBM.BA.Step2Gen_ThetaN
#check @RBM.BA.Step2Gen_thetaKer
#check @RBM.BA.Step2Gen_UN
#check @RBM.BA.Step2Kern_Mss
#check @RBM.BA.Step2Kern_ThetaN_band
-- U3s1 (`Chain/Step34Gen`): the conclusions this row produces and the vocabulary they read
#check @RBM.BA.STSEforLnConclgL
#check @RBM.BA.STSEforLngL
#check @RBM.BA.STIngRgL
#check @RBM.BA.STWardTypePgL
#check @RBM.BA.STB45gL
#check @RBM.BA.STWardTypePPingL
#check @RBM.BA.STB45PingL
#check @RBM.BA.STEKDecaygL
#check @RBM.BA.STEKDecayKgL
#check @RBM.BA.STXiLg
#check @RBM.BA.STXiLKg
#check @RBM.BA.STLKtensorg
#check @RBM.BA.STKIg
#check @RBM.BA.STegtg
#check @RBM.BA.STksimLKg
#check @RBM.BA.STelklkg
#check @RBM.BA.STeeg
#check @RBM.BA.Step34Gen_LCompat
#check @RBM.BA.Step34Gen_KCompat
#check @RBM.BA.bandStep34_LCompat
#check @RBM.BA.bandStep34_KCompat
#check @RBM.BA.bandStep34_STegt
#check @RBM.BA.bandFM_STSEforLnConcl
#check @RBM.BA.bandFM_STSEforLn
#check @RBM.BA.bandFM_STWardTypeP
#check @RBM.BA.bandFM_STB45
#check @RBM.BA.bandFM_STWardTypePPin
#check @RBM.BA.bandFM_STB45Pin
#check @RBM.BA.bandFM_STEKDecay
#check @RBM.BA.step34Gen_band_hg
-- T7a (`Chain/DecayGen`, `DecayGenTw`): the far decay of `𝒦`, the loop decay and the carrier facts F3, F4
#check @RBM.BA.STDecayLoopUgL
#check @RBM.BA.STKcalDecaygL
#check @RBM.BA.DecayGen_Spec
#check @RBM.BA.DecayGen_WardPair
#check @RBM.BA.stDecayLoopUgL_of_step2
#check @RBM.BA.bandFM_STKcalDecay
#check @RBM.BA.bandFM_STDecayLoopU
#check @RBM.BA.DecayGen_bandSpec
#check @RBM.BA.DecayGen_bandWardPair
#check @RBM.BA.DecayGenTw_baWardPair
-- T5s2 (`Chain/StepDecompGen`): the loop form (the only T5s2 name read here, §276 (3))
#check @RBM.BA.StepDecompGen_LoopForm
#check @RBM.BA.stepDecompGen_loopForm_band
-- U1s1 (`Chain/ZeroModeGen`): the one Ward text (UN-C3) and the kernel algebra
#check @RBM.BA.ZeroModeGen_WardCls
#check @RBM.BA.ZeroModeGen_WardFam
#check @RBM.BA.zeroModeGen_wardCls_band
#check @RBM.BA.ZeroModeGen_KerSums
#check @RBM.BA.zeroModeGen_kerSums_band
#check @RBM.BA.QopAlgebra_commutator_ThetaNg
#check @RBM.BA.QopAlgebra_col_sum_thetaKerg
-- U4s1 (`Chain/Step5CasesGen`, `Step5KerGen`): the flow facts of a carrier tuple; the row-sum text of the kernel
#check @RBM.BA.Step5CasesGen_FlowFacts
#check @RBM.BA.step5CasesGen_flowFacts_band
#check @RBM.BA.Step5KerGen_ThDecay
#check @RBM.BA.step5KerGen_thDecay_band
-- model-free or size-level band names, reused (no copy)
#check @RBM.Gauss.Sizes.STContractM
#check @RBM.Gauss.Sizes.stContractM_holds
#check @RBM.Green.perTime_timeIcc_of_forall_seq
#check @RBM.Ind.LoopDecay
#check @RBM.Ind.DecayLoopB_loopDecay_of
#check @RBM.Ind.DecayLoopB_bound_of
#check @RBM.Gauss.Sizes.B45_Psum_le
#check @RBM.Gauss.Sizes.B45_Psum_snoc
#check @RBM.Gauss.Sizes.B45_scale
#check @RBM.Gauss.Sizes.B45_master_real
#check @RBM.Gauss.Sizes.B45_vth_sup
#check @RBM.Gauss.Sizes.B45_vth_mid
#check @RBM.Gauss.Sizes.B45_cmp
#check @RBM.Gauss.Sizes.B45_C_nonneg
#check @RBM.Gauss.Sizes.B45_log_le
#check @RBM.Gauss.Sizes.B45_window_pow_le
#check @RBM.Gauss.Sizes.B45_W_pow_neg_le
#check @RBM.Gauss.Sizes.B45_alt_last
#check @RBM.Gauss.Sizes.B45_sgnCons
#check @RBM.Gauss.Sizes.STMollifierProps
#check @RBM.Gauss.Sizes.STAlternating
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STn12E
#check @RBM.Gauss.Sizes.STn12
#check @RBM.Gauss.zdistInf
#check @RBM.Gauss.Idx
#check @RBM.Path.TimeIcc
-- band producers of the discharges (band readings, re-derivations)
#check @RBM.Gauss.Sizes.stKbound_holds
#check @RBM.Gauss.Sizes.stKward_holds
#check @RBM.Gauss.Sizes.seqHflow
#check @RBM.Gauss.Sizes.seqHflow_isHermitian
#check @RBM.Gauss.Sizes.isProbabilityMeasure_seqP
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.STAny
#check @RBM.Gauss.Sizes.STCaseI
#check @RBM.Gauss.Sizes.STKI
#check @RBM.Gauss.Sizes.STKloop
-- BA names read in the shapes (U2-BA; names only)
#check @RBM.BA.baFM
#check @RBM.BA.baFMz
#check @RBM.BA.baStep2Mat
#check @RBM.BA.baStep2Mat_toFlowFM
#check @RBM.BA.baStep2Mat_KI
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.Gauss.Sizes.seqHflowBA
#check @RBM.BA.baKbound_holds
#check @RBM.BA.baKward_holds
#check @RBM.BA.baKsol_one
#check @RBM.BA.BAm_norm_le_one
#check @RBM.BA.TwistStep2_lam0_sq
#check @RBM.BA.BAKsol_isKLoopS
#check @RBM.BA.baKsolve
#check @RBM.BA.baProp5to8_holds
#check @RBM.BA.EMn2BA_mF_data

/-! ## Part 2: the target statements (content binding), then shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 1, conclusion** (binding): `STKbound` uniformly in `u ∈ [s_n, t_n]` over a carrier (band `stKbound_timeIcc`,
`Induction/KDecay.lean:1062`; the time inside the `≺`). -/
def T2480_KboundU {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p _ => ‖C.K n (p.1 : ℝ) p.2.1 p.2.2‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (k - 1))

/-- **Target 1, conclusion** (binding): `STKward` uniformly in `u ∈ [s_n, t_n]` over a carrier (band `stKward_timeIcc`,
`Induction/KDecay.lean:1081`), in the label convention of `STKwardgL` (`Chain/Carrier.lean:169`). -/
def T2480_KwardU {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin (k - 1) → Zd d (sz.L n)))
      (fun n p _ => ∑ x : Zd d (sz.L n),
        ‖C.K n (p.1 : ℝ) p.2.1 (fun i : Fin k => if h : (i : ℕ) < k - 1 then p.2.2 ⟨i, h⟩ else x)‖)
      (fun n p _ => (((sz.W n : ℕ) : ℝ) ^ d * C.eta n (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (k - 2))

/-- **Target 1, `stKbound_timeIccgL`** (conclusion binding): the per-time `STKboundgL` of a deterministic `𝒦` and a probability
law give the time-uniform bound. -/
def T2480_KboundTimeIcc : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ],
    sz.SizeTendsto → STKboundgL C μ →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → T2480_KboundU C μ s t

/-- **Target 1, `stKward_timeIccgL`** (conclusion binding). -/
def T2480_KwardTimeIcc : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ],
    sz.SizeTendsto → STKwardgL C μ →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → T2480_KwardU C μ s t

/-- **Target 3, class `SEforLnGen_Facts`** (binding, see the header): the carrier facts of a flow family that replace the band
objects of `SEforLn1/2` and `DecayLoopB` §9: the loop form at `ztOf` (in place of `|E| < 2`, `zt E`, `etaT E`; the contraction
inequality `stContractM_holds` then applies), a Hermitian flow matrix, the two compatibility facts of U3s1, the one Ward text of
U1s1 (rotation of `𝒦`), the row and column sums and the support of `S` (in place of `SB`), `Im m ≤ 1` (in place of `norm_mE`)
and the one-loop value `𝒦^{(1)}_σ = m_σ` (in place of `KLK_one`; the first conjunct of T2478's `OneLoop` text). -/
def T2480_SEforLnFacts (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ →
      Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : Prop :=
  ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
    (∃ E : ℕ → ℝ, StepDecompGen_LoopForm (mkM sz z) E) ∧
    (∀ (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ), (Hf sz z n τ ω).IsHermitian) ∧
    Step34Gen_LCompat (mkM sz z) (Hf sz z) ∧ Step34Gen_KCompat (mkM sz z) ∧
    ZeroModeGen_WardCls sz (mkM sz z).toFlowFM ∧
    (∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖(mkM sz z).S n a b‖ ≤ 1) ∧
    (∀ (n : ℕ) (b : Zd d (sz.L n)), ∑ a : Zd d (sz.L n), ‖(mkM sz z).S n a b‖ ≤ 1) ∧
    (∀ (n : ℕ) (a b : Zd d (sz.L n)), (mkM sz z).S n a b ≠ 0 → zdistInf d (sz.L n) (a - b) ≤ 1) ∧
    (∀ n : ℕ, ((mkM sz z).m n).im ≤ 1) ∧
    ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)),
      (mkM sz z).K n u (fun _ : Fin 1 => σ) (fun _ => a) = STmsigg (mkM sz z) n σ

/-- **Target 4, `stSEforLnConclgL_of`** (conclusion `STSEforLnConclgL` binding; the hypothesis list is a shape fixed in
1a (iii)): the four estimates of `lem:SEforLn` over one carrier (band `stSEforLn_part1` … `stSEforLn_part4`,
`SEforLn1:466, 702`, `SEforLn2:1007, 1264`). -/
def T2480_SEforLnConclOf : Prop :=
  ∀ {d : ℕ}, 3 ≤ d → ∀ (sz : Sizes d) (Cm : Step2Mat sz)
    (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ] (κm 𝔠 𝔡 Cd 𝔠d : ℝ) (E s t : ℕ → ℝ),
    DecayGen_Spec Cm.toFlowFM κm → sz.Admissible 𝔠 𝔡 → StepDecompGen_LoopForm Cm E →
    (∀ (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ), (Hf n τ ω).IsHermitian) →
    Step34Gen_LCompat Cm Hf → Step34Gen_KCompat Cm → ZeroModeGen_WardCls sz Cm.toFlowFM →
    (∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1) →
    (∀ (n : ℕ) (b : Zd d (sz.L n)), ∑ a : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1) →
    (∀ n : ℕ, (Cm.m n).im ≤ 1) →
    (∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)),
      Cm.K n u (fun _ : Fin 1 => σ) (fun _ => a) = STmsigg Cm n σ) →
    0 < Cd → 0 < 𝔠d → 𝔠d * Cd ≤ 1 / 30 →
    (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n < 1) → sz.STConStInd 𝔠d s t →
    STKwardgL Cm.toFlowFM μ → STStep2ConclgL Cm.toFlowFM μ s t Cd →
    STSEforLnConclgL Cm Hf μ s t

/-- **Target 5, the pin `stSEforLngL_of`** (binding): the ℰ-term setting over a carrier family, for every regime `R` (the band
proof reads none); band `stSEforLn_holds` (`SEforLn2:1287`) through `bandFM_STSEforLn` (`Chain/Step34Gen.lean:460`). -/
def T2480_SEforLngLOf : Prop :=
  ∀ (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ →
      Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ),
    (∀ sz : Sizes d, IsProbabilityMeasure (law sz)) →
    Step5CasesGen_FlowFacts d Flow (fun sz z => (mkM sz z).toFlowFM) T0 →
    T2480_SEforLnFacts d Flow mkM Hf →
    STSEforLngL d R law Flow mkM Hf T0

/-- **Target 6, conclusion** (binding): the label decay of the four ℰ-terms (band `stEtermDecay`, `DecayLoopB:2209`, read
through `bandFM_STEKDecay` and U3s1's ℰ-forms); `STEKDecaygL` at `sz.lam` (DECISIONS §269 (2), option (B)).  The 1b states
the four conjuncts as four results with conclusion head `STEKDecaygL` and this bundle. -/
def T2480_EtermDecay {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)
    (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) (k : ℕ) (σ : Fin k → Bool) : Prop :=
  STEKDecaygL μ s t (m := k)
      (fun n v ω (a : Fin k → Zd d (sz.L n)) => STegtg Cm Hf n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
    (∀ l : ℕ, STEKDecaygL μ s t (m := k)
      (fun n v ω (a : Fin k → Zd d (sz.L n)) => STksimLKg Cm Hf n (v : ℝ) ω l ⟨List.ofFn σ, List.ofFn a⟩)) ∧
    STEKDecaygL μ s t (m := k)
      (fun n v ω (a : Fin k → Zd d (sz.L n)) => STelklkg Cm Hf n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
    STEKDecaygL μ s t (m := k + k)
      (fun n v ω (b : Fin (k + k) → Zd d (sz.L n)) =>
        STeeg Cm Hf n (v : ℝ) ω σ (fun i => b (Fin.castAdd k i)) (fun i => b (Fin.natAdd k i)))

/-- **Target 6, `stEtermDecaygL`** (conclusion binding; the hypothesis list is a shape fixed in 1a (iii)). -/
def T2480_EtermDecaygL : Prop :=
  ∀ {d : ℕ}, 3 ≤ d → ∀ (sz : Sizes d) (Cm : Step2Mat sz)
    (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ] (κm 𝔠 𝔡 : ℝ) (E s t : ℕ → ℝ),
    DecayGen_Spec Cm.toFlowFM κm → sz.Admissible 𝔠 𝔡 → StepDecompGen_LoopForm Cm E →
    (∀ (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ), (Hf n τ ω).IsHermitian) →
    (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    Step34Gen_LCompat Cm Hf → Step34Gen_KCompat Cm →
    (∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1) →
    (∀ (n : ℕ) (a b : Zd d (sz.L n)), Cm.S n a b ≠ 0 → zdistInf d (sz.L n) (a - b) ≤ 1) →
    STKboundgL Cm.toFlowFM μ → STKcalDecaygL Cm.toFlowFM → STDecayLoopUgL Cm.toFlowFM μ s t →
    ∀ k : ℕ, 2 ≤ k → ∀ σ : Fin k → Bool, T2480_EtermDecay Cm Hf μ s t k σ

/-- **Target 7, class `B45Gen_Facts`** (binding, see the header): the last-label Ward step (one Ward text, UN-C3), the Ward pair
F4 of T7a (for `stDecayLoopUgL_of_step2`), and the row sums and column-sum moduli of `Step2Gen_thetaKer` (in place of
`B45_row_thetaKer`, `QopAlgebra_col_sum_thetaKer`, `‖μ‖ = 1`; the row-sum text is the second conjunct of
`Step5KerGen_ThDecay`).  `STKcalDecaygL` is not a field: it stays an explicit premise of targets 6 and 9. -/
def T2480_B45Facts (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ C₆ : ℝ, 0 < C₆ ∧
    ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ZeroModeGen_WardCls sz (mk sz z) ∧ DecayGen_WardPair (mk sz z) ∧
        ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 →
          (∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer (mk sz z) n σ σ' t a b‖ ≤ C₆ / (1 - t)) ∧
          ∀ b : Zd d (sz.L n), ‖∑ a : Zd d (sz.L n), Step2Gen_thetaKer (mk sz z) n σ σ' t a b‖ ≤ C₆ / (1 - t)

/-- **Target 9, the pin `stWardTypePPingL_of`** (binding at the band regime `STCaseI`; for every `R` if 1a (ix) finds the
regime unread): band `stWardTypePPin_holds` (`B45:2935`) through `bandFM_STWardTypePPin`. -/
def T2480_WardTypePPinOf : Prop :=
  ∀ (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ),
    (∀ sz : Sizes d, IsProbabilityMeasure (law sz)) →
    Step5CasesGen_FlowFacts d Flow mk T0 → T2480_B45Facts d Flow mk →
    (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → STKcalDecaygL (mk sz z)) →
    STWardTypePPingL d STCaseI law Flow mk T0

/-- **Target 9, the pin `stB45PingL_of`** (binding as above): band `stB45Pin_holds` (`B45:2943`) through `bandFM_STB45Pin`. -/
def T2480_B45PinOf : Prop :=
  ∀ (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ),
    (∀ sz : Sizes d, IsProbabilityMeasure (law sz)) →
    Step5CasesGen_FlowFacts d Flow mk T0 → T2480_B45Facts d Flow mk →
    (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → STKcalDecaygL (mk sz z)) →
    STB45PingL d STCaseI law Flow mk T0

/-! ### Shapes (not binding): band discharges -/

/-- Target 3 at the band family `(STFlow, bandStep2Mat ∘ STflowE, seqHflow)`. -/
example : Prop := ∀ d : ℕ, T2480_SEforLnFacts d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
  (fun sz z => bandStep2Mat sz (STflowE z)) (fun sz _ => seqHflow sz)

/-- Target 7 at the band family (`C₆ = 1`). -/
example : Prop := ∀ d : ℕ, T2480_B45Facts d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z))

/-- The far decay of `𝒦` at the band family (from `bandFM_STKcalDecay`; `Admissible` and `|E n| ≤ 2 - κ` from `STFlow`). -/
example : Prop := ∀ d : ℕ, 3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ →
  STFlow sz κ ε 𝔠 𝔡 z → STKcalDecaygL (bandFM sz (STflowE z))

/-! ### Shapes (not binding): the BA readings (U2-BA) -/

/-- `BAKcalDecay`, the BA reading of `STKcalDecaygL` (supervisor 1457 Q1; DECISIONS §264 (3)): the tree-sum twin. -/
example : Prop := ∀ d : ℕ, 3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ →
  BAFlow sz κ ε 𝔠 𝔡 z → STKcalDecaygL (baFMz sz z)

/-- Targets 3 and 7 at the BA families. -/
example : Prop := ∀ d : ℕ,
  T2480_SEforLnFacts d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => sz.seqHflowBA (BAflowLam0 sz z)) ∧
    T2480_B45Facts d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)

/-- `BASEforLn` (the shape of `Chain/Step34GenTw.lean:89`), `BAWardTypePPin`, `BAB45Pin`. -/
example : Prop := ∀ d : ℕ,
  STSEforLngL d STAny (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => sz.seqHflowBA (BAflowLam0 sz z))
      (fun sz z => BAflowT0 sz z) ∧
    STWardTypePPingL d STCaseI (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) ∧
    STB45PingL d STCaseI (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)

/-- The flow facts at the BA family (the input of targets 5 and 9 at BA). -/
example : Prop := ∀ d : ℕ, Step5CasesGen_FlowFacts d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
  (fun sz z => (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).toFlowFM) (fun sz z => BAflowT0 sz z)

/-- Target 6 at the BA carrier and flow matrix. -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (k : ℕ) (σ : Fin k → Bool),
  T2480_EtermDecay (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (sz.seqHflowBA (BAflowLam0 sz z))
    (Sizes.seqP (sz.withLam 0)) s t k σ

/-- UBA-C1 (DECISIONS §273 (1)): the only comparison text, should a crossing appear (expected: not triggered). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (gK : ℕ → ℝ) (A : ℝ),
  ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2

end RBM.BA

end

/-! ## Part 3 (G1): public band names restated here or read elsewhere; statements unchanged -/

#check @RBM.Gauss.Sizes.STSEforLn
#check @RBM.Gauss.Sizes.STSEforLnConcl
#check @RBM.Gauss.Sizes.STWardTypePPin
#check @RBM.Gauss.Sizes.STB45Pin
#check @RBM.Gauss.Sizes.STEKDecay
#check @RBM.Gauss.Sizes.STDecayLoopU
#check @RBM.Gauss.Sizes.stSEforLn_part1
#check @RBM.Gauss.Sizes.stSEforLn_part2
#check @RBM.Gauss.Sizes.stSEforLn_part3
#check @RBM.Gauss.Sizes.stSEforLn_part4
#check @RBM.Gauss.Sizes.stSEforLn_holds
#check @RBM.Gauss.Sizes.stWardTypePPin_holds
#check @RBM.Gauss.Sizes.stB45Pin_holds
#check @RBM.Gauss.Sizes.stEtermDecay
#check @RBM.Gauss.Sizes.STKcalDecay
#check @RBM.Gauss.Sizes.stKcalDecay_holds
#check @RBM.Gauss.KDecayInst.inst_stKcalDecay_admissible
#check @RBM.Gauss.Sizes.stKbound_timeIcc
#check @RBM.Gauss.Sizes.stKward_timeIcc
#check @RBM.Gauss.Sizes.stSumTwoLoop
#check @RBM.Gauss.Sizes.stSumTwoLoop_exists
#check @RBM.Loop.KDecay_sum_tailT_le
#check @RBM.Loop.KDecay_tailC
#check @RBM.Loop.KDecay_one_le_tailC
-- `B45` helpers read outside the file (U3s3 `QLevelsA`, `QDriftB`; V1s3 `ExpWardI`, `ExpIntIQ`, `QopDecay`; U4s2 `IniTermI`)
#check @RBM.Gauss.Sizes.B45_far_main
#check @RBM.Gauss.Sizes.B45_ward_fin
#check @RBM.Gauss.Sizes.B45_Psum_LK_le
#check @RBM.Gauss.Sizes.B45_norm_kappa
#check @RBM.Gauss.Sizes.B45_STKloop_eq
#check @RBM.Gauss.Sizes.B45_row_thetaKer
#check @RBM.Gauss.Sizes.B45_norm_ThetaN_le
#check @RBM.Gauss.Sizes.B45_norm_EKsgn
#check @RBM.Gauss.Sizes.B45_B4_le
#check @RBM.Gauss.Sizes.B45_scales
#check @RBM.Gauss.Sizes.B45_det
#check @RBM.Gauss.Sizes.B45_det2
#check @RBM.Gauss.Sizes.B45_ofFn_sigma
#check @RBM.Gauss.Sizes.B45_ofFn_sgnCons
#check @RBM.Gauss.Sizes.B45_ofFn_snoc
