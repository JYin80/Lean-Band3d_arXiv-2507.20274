/-
Release check for T2461 (dispatcher V3, Mon Oct 12 14:45 UTC 2026; DECISIONS §268).  Sub-stage T producer row P2 (U-D, `docs/reports/T2452-design.md`
D3 (ii) `:144-150`, D5 `:182`, D6 `:193`): the generic net-lift pin `STNetLift2gL` (`Chain/Step2Gen.lean:602`) at the block Anderson
law `seqP (sz.withLam 0)`, setting `BAFlow`, carrier `baFMz` and horizon `BAflowT0` (the reading of `BAStep2`, `BA/FlowPins.lean:432`),
proved BA-direct in a new leaf file; `Path/NetLift1-2` are not edited.
Part 1: merged names.  Part 2: the target statements as Prop values (prefix `T2461_`; content binding): `T2461_NetLift2BA` is U-D's
T1-BA pin name `baNetLift2_holds` (`T2452-design.md:193`); `T2461_BAFlowPremises` is the probe theorem `T2452_ba_premises`
(`t/T2452:RBM3D/Probe/T2452Pins.lean:177-195`, commit 20d5f15, compiled exit 0) as a Prop.  Then shapes (not binding): the band bridge,
the route (one family; the new BA modulus of `𝒦^{(2)}`) and the `d = 3` instances.
Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2461-check.lean
-/
import RBM3D.Chain.Carrier
import RBM3D.Chain.Step2Gen
import RBM3D.BA.MFixedPoint
import RBM3D.BA.FlowPins
import RBM3D.BA.Ward
import RBM3D.BA.GreenSchur
import RBM3D.BA.KBase
import RBM3D.BA.KInduct
import RBM3D.BA.EKPins
import RBM3D.BA.EMn2BA
import RBM3D.BA.TwistKer
import RBM3D.BA.Step1Setup
import RBM3D.BA.TwistLoop
import RBM3D.Path.NetLift1
import RBM3D.Path.NetLift2
import RBM3D.Induction.ContinuityNet
import RBM3D.Induction.Step2Defs
import RBM3D.Induction.Step2Iterate
import RBM3D.Induction.LocalAvg1
import RBM3D.Induction.LocalAvg2
import RBM3D.Defs.StochDomAt
import RBM3D.Defs.Domination
import RBM3D.Defs.Sizes
import RBM3D.Green.Pins

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the generic pin (T8 = T2386), its band reading, the band pin and its producer, the consumer slot `hNet`
#check @RBM.BA.STNetLift2gL
#check @RBM.BA.bandFM_STNetLift2
#check @RBM.Gauss.Sizes.STNetLift2
#check @RBM.Gauss.Sizes.stNetLift2_holds
#check @RBM.Gauss.Sizes.stNetLift2_part1
#check @RBM.Gauss.Sizes.ST_step2_of_pins
-- the six families of the pin (per time -> uniform in `u ∈ [s,t]`) and the domination predicates
#check @RBM.BA.STStep2LocalPTgL
#check @RBM.BA.STStep2AvgPTgL
#check @RBM.BA.STStep2DecayPTgL
#check @RBM.BA.STStep2LocalgL
#check @RBM.BA.STStep2AvggL
#check @RBM.BA.STStep2DecaygL
#check @RBM.BA.STLocalEntryUgL
#check @RBM.BA.STGdecayWgL
#check @RBM.BA.PrecL
#check @RBM.BA.PrecPTL
#check @RBM.BA.FlowFM
#check @RBM.BA.FlowFM.GM
#check @RBM.StochDomAt
#check @RBM.Path.PerTimeDomAt
#check @RBM.Gauss.HighProbAt
#check @RBM.Path.TimeIcc
#check @RBM.Path.perTimeDomAt_iff_forall_section
-- merged generic producers of two of the three per-time families (premise scan)
#check @RBM.Gauss.Sizes.stStep2LocalPT_of_L2decayG
#check @RBM.Gauss.Sizes.stStep2AvgPT_of_L2decayG
-- the BA carrier, law, setting, horizon; the BA reading of Step 2
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.BA.baFMz
#check @RBM.BA.baFM
#check @RBM.BA.BAmF
#check @RBM.BA.BAGt
#check @RBM.BA.BALloop
#check @RBM.BA.BAKloop
#check @RBM.BA.BAKsol
#check @RBM.BA.BAMfine
#check @RBM.BA.BAStep2
#check @RBM.BA.STStep2G
#check @RBM.Gauss.Sizes.withLam
-- the band route (not reused for the model; its scalar privates may be reused through `open private`)
#check @RBM.Ind.Step2NetLift
#check @RBM.Ind.step2NetLift
#check @RBM.Ind.Step2LocalNetLift
#check @RBM.Ind.step2LocalNetLift
#check @RBM.Ind.Step2AvgNetLift
#check @RBM.Ind.step2AvgNetLift
#check @RBM.Green.v3_premises_of_stFlow
-- the BA route: the abstract net, the good events, the BA templates (Step 1 net lift; TL2e net)
#check @RBM.Ind.ContinuityNet.cont_core
#check @RBM.Ind.ContinuityNet.contGood
#check @RBM.Ind.ContinuityNet.cont_highProbAt_good
#check @RBM.Ind.ContinuityNet.cont_inv_add_one_sub_ratio
#check @RBM.Ind.ContinuityNet.cont_Bctl_ratio
#check @RBM.Ind.ContinuityNet.cont_inv_size_le_Bctl
#check @RBM.BA.baGopbound
#check @RBM.BA.baG_continuousOn
#check @RBM.BA.baNetLift
#check @RBM.BA.baTwistLoopStep_of_fixed
#check @RBM.BA.TwistKer_entry_le
#check @RBM.BA.EMn2BA_seqHflowBA_herm
-- the new BA modulus: `𝒦^{(2)}` in time, every charge pair
#check @RBM.BA.baKsol_two
#check @RBM.BA.EMn2BA_K_two
#check @RBM.BA.BATheta
#check @RBM.BA.BAMss
#check @RBM.BA.BAMB
#check @RBM.BA.BAReal
#check @RBM.BA.EKPins_norm_Theta_le
#check @RBM.BA.EKPins_norm_Q_le
-- the flow premises (target 2) and the data facts
#check @RBM.BA.EMn2BA_T0_lt_one
#check @RBM.BA.EMn2BA_one_sub_T0
#check @RBM.BA.EMn2BA_mF_data
#check @RBM.BA.BAflow_real
#check @RBM.BA.BAflow_lam0_window
#check @RBM.BA.BAm_norm_le_one
#check @RBM.Gauss.Sizes.RangeCond
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.WO
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.tendsto_size
#check @RBM.eventually_le_rpow
-- the controls of the pin
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.STWB
#check @RBM.ellT
-- the instance data
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_tendsto
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.t0_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0
#check @RBM.BA.Step1SetupInst.inst_im_m_ge
#check @RBM.BA.Step1SetupInst.inst_norm_m_le
#check @RBM.BA.Step1SetupInst.inst_baNetLift

/-! ## Part 2: the target statements (content binding) and shapes (not binding) -/

open MeasureTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 1** (content binding): the net lift of Step 2 at the block Anderson reading (U-D D6 `:193`, `baNetLift2_holds`): the
pin `STNetLift2gL` at the law `seqP (sz.withLam 0)`, the setting `BAFlow`, the carrier `baFMz` and the horizon `BAflowT0` (the
arguments of `BAStep2`, `FlowPins:432`).  Every `d` (as the band `stNetLift2_holds (d : ℕ) : STNetLift2 d`). -/
def T2461_NetLift2BA (d : ℕ) : Prop :=
  STNetLift2gL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0

/-- **Target 2** (content binding): the BA premises of the flow (U-D P6), `T2452_ba_premises` verbatim as a Prop: `t_n < 1` and
`RangeCond (ε/2) t` from `BAFlow` and `t ≤ BAflowT0`.  The BA reading of `v3_premises_of_stFlow` (`Green/Pins:1049`) without its
spectral conjunct. -/
def T2461_BAFlowPremises (d : ℕ) : Prop :=
  ∀ (κ ε 𝔠 𝔡 : ℝ), 0 < κ → 0 < ε → ∀ (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, t n ≤ BAflowT0 sz z n) → (∀ n, t n < 1) ∧ sz.RangeCond (ε / 2) t

/-- Targets 1 and 2 as Prop values. -/
example : Prop := ∀ d : ℕ, T2461_NetLift2BA d
example : Prop := ∀ d : ℕ, T2461_BAFlowPremises d

/-- Target 1 unfolded (shape, not binding: the content is `T2461_NetLift2BA`). -/
example : Prop := ∀ d : ℕ,
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ Cd : ℝ, STStep2LocalPTgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t →
          STStep2AvgPTgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t →
          STStep2DecayPTgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) Cd s t →
            STStep2LocalgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t ∧
              STStep2AvggL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t ∧
              STStep2DecaygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) Cd s t

/-- The band reading of the same pin (merged `bandFM_STNetLift2`, `Step2Gen:708`, a definitional bridge): only the law, setting, carrier and
horizon change. -/
example : Prop := ∀ d : ℕ,
  STNetLift2 d ↔ STNetLift2gL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))

/-- Route (not binding): the decay family alone at the BA flow, the BA twin of `stNetLift2_part1` (`NetLift1:853`).  Its per-time
premise `STStep2DecayPTgL` has no merged producer, so a theorem of this shape stays private (premise scan). -/
example : Prop := ∀ (d : ℕ) (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → 0 < ε → 0 < 𝔡 → BAFlow sz κ ε 𝔠 𝔡 z →
  ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ Cd : ℝ,
    STStep2DecayPTgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) Cd s t →
      STStep2DecaygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) Cd s t

/-- Route (not binding): the one new BA modulus, `𝒦^{(2)}` at `baFMz` is Lipschitz in time with constant `(1-u)⁻¹(1-u')⁻¹` for
every charge pair (same-charge included), eventually in `n` (`0 < g₀`): `baKsol_two` (every `σ`), the resolvent identity of `Θ`
(`BAKBase_sub`, `KBase:216`, private), `‖Θ_v‖ ≤ (1-v)⁻¹`, `‖M^{(σσ')}‖ ≤ 1`, `W^{-d} ≤ 1` (pattern `TwistLoop_K_diff`, `:208`). -/
example : Prop := ∀ (d : ℕ) (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
  ∀ᶠ n in atTop, ∀ u u' : ℝ, 0 ≤ u → u ≤ BAflowT0 sz z n → 0 ≤ u' → u' ≤ BAflowT0 sz z n →
    ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      ‖(baFMz sz z).K n u σ a - (baFMz sz z).K n u' σ a‖ ≤ |u - u'| * ((1 - u)⁻¹ * (1 - u')⁻¹)

open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst in
/-- Target 3 shape (a): target 1 at `d = 3`, `κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `sz0`, `zSeq` (`flow_sz0`), `s ≡ 1/2`,
`t ≡ 2/3 ≤ t₀` (`t0_sz0`), every `C_d`; the three per-time statements stay hypotheses (CLAUDE.md §4 step 2). -/
example : Prop := ∀ Cd : ℝ,
  STStep2LocalPTgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3) →
  STStep2AvgPTgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3) →
  STStep2DecayPTgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) Cd (fun _ => 1 / 2) (fun _ => 2 / 3) →
    STStep2LocalgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3) ∧
      STStep2AvggL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 2 / 3) ∧
      STStep2DecaygL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) Cd (fun _ => 1 / 2) (fun _ => 2 / 3)

open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst in
/-- Target 3 shape (b): the window `s ≡ 0`, `t ≡ 1/2 < t₀` (`half_lt_t0`), the start of the Step-2 chain. -/
example : Prop := ∀ Cd : ℝ,
  STStep2LocalPTgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 0) (fun _ => 1 / 2) →
  STStep2AvgPTgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 0) (fun _ => 1 / 2) →
  STStep2DecayPTgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) Cd (fun _ => 0) (fun _ => 1 / 2) →
    STStep2LocalgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 0) (fun _ => 1 / 2) ∧
      STStep2AvggL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 0) (fun _ => 1 / 2) ∧
      STStep2DecaygL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) Cd (fun _ => 0) (fun _ => 1 / 2)

open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst in
/-- Target 3 shape (c): target 2 at the same data, `t ≡ 2/3`, `ε/2 = 1/20`. -/
example : Prop := (∀ n : ℕ, (fun _ : ℕ => (2 / 3 : ℝ)) n < 1) ∧ sz0.RangeCond ((1 / 10) / 2) (fun _ => 2 / 3)

end RBM.BA

end
