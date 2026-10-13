/-
Release check for T2486 (dispatcher V3, 2026-10-13 03:12 UTC; DECISIONS §287).  U U2-BA (sub-stage U, BA side): the BA twin of U2 = T2480,
in the new leaves `BA/KDecayBA.lean` (target 1, reserve `BA/KDecayBA2.lean`), `BA/SEforLnBA.lean` (targets 2-5) and
`BA/B45BA.lean` (targets 6-8).  No merged file is edited (outside the certificate lane).
Target 1 is `BAKcalDecay`, the BA proof of the far-decay segment of `Induction/KDecay.lean` (§1-§8, `:52-998`, class (t)) at
the BA carrier `baFMz sz z`: the merged generic premise `STKcalDecaygL` (`Chain/DecayGen.lean:83`) along every BA flow.
Targets 2-8 discharge, at the BA tuple, every field of the merged classes `SEforLnGen_Facts` (`Chain/SEforLnGen.lean:57`) and
`B45Gen_Facts` (`Chain/B45Gen.lean:61`, U2b merged 78f4cc14, imported here), and conclude the BA forms of `STSEforLnConclgL`,
`STSEforLngL`, `STEKDecaygL`, `STWardTypePgL`/`STB45gL` and the two pins.
UN-C3 (supervisor 1852 `:77-82`, widened in 0149 U2-C3 `:78-81`): this row writes the one BA proof of
`ZeroModeGen_WardCls (baFMz sz z)` (target 2 (a)).  The one-loop value at BA is one `baKsol_one` proof whose text is the first
conjunct of `Step2IterGen_OneLoop` (target 2 (b)); no named `Prop` is added for it.
Coupling (supervisor 1457 UBA-C1; R1 = 1752 TN-C1, DECISIONS §273 (1)): not triggered.  The far cutoff of `STKcalDecaygL` reads
`ellT (sz.L n) (sz.lam n) u` (size level); the kernels are at `BAflowLam0 sz z` (kernel level); the crossing is 1457 F1 (f),
free since `ell(g0) <= ell(g)` where `0 < g0` (the guarded consequence `baStep5III_lam0_le_lam`).  No grid statement (TN-C4).
Part 1: merged names.  Part 2: pins (prefix `T2486_`): content binding as marked; the hypothesis lists of the per-carrier
readings (targets 4 (a), 7) are shapes fixed in 1a; then shapes (not binding).  Part 3: the band twin of target 1, unchanged.
Merged names only.  Statements only: no proof terms, no placeholders.
Run: lake env lean docs/tickets/checks/T2486-check.lean
-/
import RBM3D.Chain.B45Gen
import RBM3D.Chain.SEforLnGen2
import RBM3D.Chain.DecayGenTw
import RBM3D.Chain.Step34GenTw
import RBM3D.Chain.Step2Kern
import RBM3D.Chain.Step2IterGen
import RBM3D.Chain.GridGoodGen
import RBM3D.BA.FlowPins
import RBM3D.BA.Step2BA
import RBM3D.BA.KBound
import RBM3D.BA.KInduct
import RBM3D.BA.KKernel
import RBM3D.BA.KBase
import RBM3D.BA.KWard
import RBM3D.BA.KSolve
import RBM3D.BA.KTreeRep
import RBM3D.BA.KTreeDeriv
import RBM3D.BA.KCactus
import RBM3D.BA.Prop6Path
import RBM3D.BA.CombesThomas
import RBM3D.BA.Ward
import RBM3D.BA.MFixedPoint
import RBM3D.BA.EMn2BA
import RBM3D.BA.GreenSchur
import RBM3D.BA.TwistStep2
import RBM3D.BA.Step5IIIKer
import RBM3D.Induction.KDecay

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the generic premise and conclusions (U3s1, T7a, U2): what this row reads at the BA tuple
#check @RBM.BA.STKcalDecaygL
#check @RBM.BA.STKboundgL
#check @RBM.BA.STKwardgL
#check @RBM.BA.STStep2ConclgL
#check @RBM.BA.STGdecayWgL
#check @RBM.BA.STDecayLoopUgL
#check @RBM.BA.STEKDecaygL
#check @RBM.BA.STSEforLnConclgL
#check @RBM.BA.STSEforLngL
#check @RBM.BA.STWardTypePgL
#check @RBM.BA.STB45gL
#check @RBM.BA.STWardTypePPingL
#check @RBM.BA.STB45PingL
#check @RBM.BA.STegtg
#check @RBM.BA.STksimLKg
#check @RBM.BA.STelklkg
#check @RBM.BA.STeeg
#check @RBM.BA.STmsigg
-- the merged carrier classes (one text each; X1-C4)
#check @RBM.BA.DecayGen_Spec
#check @RBM.BA.DecayGen_WardPair
#check @RBM.BA.StepDecompGen_LoopForm
#check @RBM.BA.Step34Gen_LCompat
#check @RBM.BA.Step34Gen_KCompat
#check @RBM.BA.ZeroModeGen_WardCls
#check @RBM.BA.ZeroModeGen_WardFam
#check @RBM.BA.zeroModeGen_loopL_wardFam
#check @RBM.BA.ZeroModeGen_KerSums
#check @RBM.BA.Step5CasesGen_FlowFacts
#check @RBM.BA.Step2IterGen_OneLoop
#check @RBM.BA.Step2Kern_Mss
#check @RBM.BA.Step2Gen_thetaKer
-- U2 (T2480): the classes and the generic results applied at BA
#check @RBM.BA.SEforLnGen_Facts
#check @RBM.BA.stSEforLnConclgL_of
#check @RBM.BA.stSEforLngL_of
#check @RBM.BA.stEtermDecaygL
#check @RBM.BA.stKbound_timeIccgL
#check @RBM.BA.B45Gen_Facts
#check @RBM.BA.stWardTypePgL_of
#check @RBM.BA.stB45gL_of
#check @RBM.BA.stWardTypePPingL_of
#check @RBM.BA.stB45PingL_of
-- T7a, T4s2a: the consumers of target 1 and of the BA ℰ-term decays
#check @RBM.BA.stDecayLoopUgL_of_step2
#check @RBM.BA.DecayGenTw_baWardPair
#check @RBM.BA.gridGoodNgL_of
-- the BA carrier, the flow data, the flow matrix, the law
#check @RBM.BA.baFM
#check @RBM.BA.baFMz
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAKloop
#check @RBM.BA.BAKsol
#check @RBM.BA.BAmF
#check @RBM.BA.baStep2Mat
#check @RBM.BA.baStep2Mat_toFlowFM
#check @RBM.BA.baStep2Mat_KI
#check @RBM.BA.Step2Kern_Mss_BA
#check @RBM.BA.Step2Kern_thetaKer_BA
#check @RBM.Gauss.Sizes.seqHflowBA
#check @RBM.BA.EMn2BA_seqHflowBA_herm
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.isProbabilityMeasure_seqP
#check @RBM.Gauss.loopM_eq_loopL
#check @RBM.BA.BAStep2
-- flow facts and the coupling (`g0 = sqrt t0 * g`; guarded R1 consequence)
#check @RBM.BA.BAflow_real
#check @RBM.BA.BAflow_lam0_window
#check @RBM.BA.EMn2BA_mF_data
#check @RBM.BA.EMn2BA_T0_lt_one
#check @RBM.BA.TwistStep2_lam0_sq
#check @RBM.BA.TwistStep2_T0_ge
#check @RBM.BA.baStep5III_lam0_le_lam
#check @RBM.BA.BAm_norm_le_one
#check @RBM.ellT
-- stage K: the BA `𝒦` (existence, uniqueness, rotation, Ward, tree representation, cactus, one-loop value, bounds)
#check @RBM.BA.BAReal
#check @RBM.BA.BAKsolve
#check @RBM.BA.baKsolve
#check @RBM.BA.BAKsol_isKLoopS
#check @RBM.BA.baK_unique
#check @RBM.BA.baK_rotate
#check @RBM.BA.baK_ward
#check @RBM.BA.BAKcac
#check @RBM.BA.BAKcac_spliced
#check @RBM.BA.baKcac_isKLoopS
#check @RBM.BA.BATreeRep
#check @RBM.BA.baTreeRep
#check @RBM.BA.BAGamma
#check @RBM.BA.BACactusVal
#check @RBM.BA.BAnextSlot_orbit
#check @RBM.BA.baKsol_one
#check @RBM.BA.baKsol_two
#check @RBM.BA.BAKbound
#check @RBM.BA.BAKward
#check @RBM.BA.baKbound_holds
#check @RBM.BA.baKward_holds
#check @RBM.BA.BAKbound_of_uniform
#check @RBM.BA.baKBoundAt_holds
#check @RBM.Loop.KLmaxDist
#check @RBM.Loop.TSP
#check @RBM.Loop.KLIsTSP
-- the edge kernels: Θ_BA (properties 5, 5') and `M^{(B)}` (`lem:propM`)
#check @RBM.BA.BAProp5to8
#check @RBM.BA.baProp5to8_holds
#check @RBM.BA.BAProp5
#check @RBM.BA.BAProp5s
#check @RBM.BA.BAPropM
#check @RBM.BA.baPropM_holds
#check @RBM.BA.BATheta
#check @RBM.BA.BAMss
-- the kernel sums (target 6): mixed pairs `BAK`, equal pairs through translation and symmetry
#check @RBM.BA.BAMss_pm_eq
#check @RBM.BA.BAMss_mp_eq
#check @RBM.BA.BAMss_norm_eq_BAK
#check @RBM.BA.BAK_row_sum
#check @RBM.BA.BAK_col_sum
#check @RBM.BA.BAMB_shift
#check @RBM.BA.BAMB_symm
#check @RBM.BA.BATheta_row_sum_pm
-- instance data
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0

/-! ## Part 2: pins (content binding as marked) and shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 1, `BAKcalDecay`** (binding; REQ-1418-UBA `:39`; supervisor 1457 Q1 `:103-105`): the far decay of the BA `𝒦`
along every BA flow, the BA reading of `STKcalDecaygL`, in the `hKcal` shape of `gridGoodNgL_of` (`GridGoodGen:855`) and of
`stWardTypePPingL_of`/`stB45PingL_of`.  Route: `BAKsol = BAKcac` on lengths at least 2 (`baK_unique`), the cactus sum of
`BAKcac_spliced` (lengths at least 3) and its closed form (length 2), edge bounds from `baProp5to8_holds`, `baPropM_holds`,
the diameter of the slot graph (`BAnextSlot_orbit`), absorption into `W^{-D}`. -/
def T2486_BAKcalDecay (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → STKcalDecaygL (baFMz sz z)

/-- **Target 2 (a), UN-C3** (binding): the one BA proof of the Ward class, at every size index (`TL` the loop of
`blockMat (seqHflowBA …)` at `ztOf`; `TK = BAKsol` through `baKcac_isKLoopS`, `baK_unique`, `baK_rotate`, `baK_ward`). -/
def T2486_BAWardCls (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → ZeroModeGen_WardCls sz (baFMz sz z)

/-- **Target 2 (b)** (binding): the first conjunct of `Step2IterGen_OneLoop (baFMz sz z)` (`Chain/Step2IterGen.lean:81-83`)
verbatim; it is also the `hone` field of target 3 (`STmsigg` unfolds to it).  One `baKsol_one` proof; a named result, not a named `Prop`. -/
def T2486_BAOneLoop (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)),
      (baFMz sz z).K n u (fun _ : Fin 1 => σ) (fun _ => a) =
        if σ then (baFMz sz z).m n else (starRingEnd ℂ) ((baFMz sz z).m n)

/-- **Target 2 (c)** (binding): the loop form, the two compatibility facts at the BA flow matrix (owner note (1) of the ticket). -/
def T2486_BACarrierFacts (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
    StepDecompGen_LoopForm (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (BAflowEs sz z) ∧
      Step34Gen_LCompat (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (sz.seqHflowBA (BAflowLam0 sz z)) ∧
      Step34Gen_KCompat (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))

/-- **Target 2 (c)** (binding): the flow facts of the BA tuple (`κm = κ`; `EMn2BA_T0_lt_one`, `EMn2BA_mF_data`). -/
def T2486_BAFlowFacts (d : ℕ) : Prop :=
  Step5CasesGen_FlowFacts d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)

/-- **Target 3** (binding): `SEforLnGen_Facts` at the BA tuple, every `d`. -/
def T2486_BASEforLnFacts (d : ℕ) : Prop :=
  SEforLnGen_Facts d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => sz.seqHflowBA (BAflowLam0 sz z))

/-- **Target 4 (b), `BASEforLn`** (binding, every regime `R`; the shape of `Chain/Step34GenTw.lean:89`): unconditional. -/
def T2486_BASEforLn (d : ℕ) : Prop :=
  ∀ (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop),
    STSEforLngL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => sz.seqHflowBA (BAflowLam0 sz z))
      (fun sz z => BAflowT0 sz z)

/-- The four ℰ-term label decays at one carrier, flow matrix and law: a verbatim copy of `T2480_EtermDecay`
(`docs/tickets/checks/T2480-check.lean:272-286`), the conclusion of the merged `stEtermDecaygL`. -/
def T2486_EtermDecay {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)
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

/-- **Target 5** (binding): the ℰ-term decays at the BA tuple in the `hEK` shape of `gridGoodNgL_of` (`GridGoodGen:857-868`):
no `0 < ε` (the `STKboundgL` input is the ε-free reduction, ticket note (2)); `STDecayLoopUgL` is the consumer's input. -/
def T2486_BAEtermDecay (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ,
    (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    STDecayLoopUgL (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).toFlowFM (Sizes.seqP (sz.withLam 0)) s t →
    ∀ k : ℕ, 2 ≤ k → ∀ σ : Fin k → Bool,
      T2486_EtermDecay (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (sz.seqHflowBA (BAflowLam0 sz z))
        (Sizes.seqP (sz.withLam 0)) s t k σ

/-- **Target 6** (binding; DECISIONS §286 (2)): `ZeroModeGen_KerSums` at BA (`S = 1`: constant row and column sums of
`Step2Kern_Mss = BAMss`; mixed pairs `BAK`, equal pairs through `BAMB_shift`, `BAMB_symm`). -/
def T2486_BAKerSums (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ n : ℕ, ZeroModeGen_KerSums (baFMz sz z) n

/-- **Target 6** (binding): `B45Gen_Facts` at the BA family (`C₆ = 1`), with its two fields of §286 (2). -/
def T2486_BAB45Facts (d : ℕ) : Prop :=
  B45Gen_Facts d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)

/-- **Target 8, `BAWardTypePPin`** (binding, every regime `R`): unconditional. -/
def T2486_BAWardTypePPin (d : ℕ) : Prop :=
  ∀ (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop),
    STWardTypePPingL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)

/-- **Target 8, `BAB45Pin`** (binding, every regime `R`): unconditional. -/
def T2486_BAB45Pin (d : ℕ) : Prop :=
  ∀ (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop),
    STB45PingL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)

/-! ### Shapes (not binding) -/

/-- Target 4 (a), per carrier (conclusion head binding; hypothesis list fixed in 1a): only the Step 2 conclusions (T1-BA),
the window and the constants stay; `STKwardgL` from `baKward_holds`. -/
example : Prop := ∀ (d : ℕ), 3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 Cd 𝔠d : ℝ) (z : ℕ → ℂ) (s t : ℕ → ℝ),
  0 < κ → 0 < ε → BAFlow sz κ ε 𝔠 𝔡 z → 0 < Cd → 0 < 𝔠d → 𝔠d * Cd ≤ 1 / 30 →
  (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n < 1) → sz.STConStInd 𝔠d s t →
  STStep2ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd →
  STSEforLnConclgL (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (sz.seqHflowBA (BAflowLam0 sz z))
    (Sizes.seqP (sz.withLam 0)) s t

/-- Target 7, per carrier (conclusion heads binding; hypothesis list fixed in 1a): only `STGdecayWgL` (T1-BA), the window
and the eventual `N⁻¹ ≤ 1 - t_n` stay. -/
example : Prop := ∀ (d : ℕ), 3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 Cd : ℝ) (z : ℕ → ℂ) (s t : ℕ → ℝ),
  0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 ≤ s n) → (∀ n, t n < 1) →
  (∀ᶠ n in atTop, (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - t n) →
  STGdecayWgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd →
  STWardTypePgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t ∧ STB45gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t

/-- Ticket note (2): the ε-free `STKboundgL` along a BA flow (private in `SEforLnBA`; the reduction `BAKbound_of_uniform`
reads `0 < 𝔡`, which `BAFlow` gives through `BAflow_lam0_window`, and never `0 < ε`). -/
example : Prop := ∀ d : ℕ, 3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
  STKboundgL (baFMz sz z) (Sizes.seqP (sz.withLam 0))

/-- The T7-BA reading that target 1 opens (`Chain/DecayGenTw.lean:71`): the loop decay at BA from the Step 2 decay alone. -/
example : Prop := ∀ (d : ℕ), 3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 Cd : ℝ) (z : ℕ → ℂ) (s t : ℕ → ℝ),
  0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 ≤ s n) → (∀ n, t n ≤ BAflowT0 sz z n) →
  STGdecayWgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd → STDecayLoopUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t

/-- UBA-C1 for the record (DECISIONS §273 (1)): R1 at BA, `gK = BAflowLam0 sz z`, `A = (κ+1)/κ`; read only if the 1a finds a
crossing other than 1457 F1 (f) (expected: none). -/
example : Prop := ∀ (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ) (κ : ℝ),
  ∀ n, 0 ≤ BAflowLam0 sz z n * sz.lam n ∧ BAflowLam0 sz z n ^ 2 ≤ sz.lam n ^ 2 ∧
    sz.lam n ^ 2 ≤ (κ + 1) / κ * BAflowLam0 sz z n ^ 2

end RBM.BA

end

/-! ## Part 3: the band twin of target 1 (`Induction/KDecay.lean` §1-§8; not edited, not restated) -/

#check @RBM.Gauss.Sizes.STKcalDecay
#check @RBM.Gauss.Sizes.stKcalDecay_holds
#check @RBM.Gauss.KDecayInst.inst_stKcalDecay_admissible
#check @RBM.BA.bandFM_STKcalDecay
