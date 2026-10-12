/-
Release check for T2471 (dispatcher V3, Mon Oct 12 18:36 UTC 2026; DECISIONS §274).  Sub-stage T producer P1b (supervisor 1752 TN-F2, TN-C2,
TN-C4): the two-slot BA tail, i.e. clause 4 of `STGridRepNAtgL d 2` (`Chain/Step2Gen.lean:994`) at `baStep2Mat`, and the full
TN-C2 statement `∃ C₀, 0 ≤ C₀ ∧ STGridRepNAtgL d 2 C₀ BAFlow (fun sz z => baStep2Mat …) BAflowT0` (T2460's former target 4;
`T2459_P1`, `t/T2459:RBM3D/Probe/T2459Pins.lean:209-211`, at d = 3).  Default route (i): a carrier-generic successor of the
band tail `gridRepWTailQN_holds` (`Path/DifREP3.lean:2343`) at m = 2 over `Step2Gen_UN` / `STeeUMg`, instantiated at the band
and at BA; route (ii): a BA two-slot twin of `BA/TwistGridWTail*`.  New files only (outside the certificate lane).
Part 1: merged names.  Part 2: the target statements as `Prop` values (prefix `T2471_`): `T2471_GridRepN2` (TN-C2 verbatim,
binding), `T2471_Bridge` (= `T2460_Bridge` with the Amend 1 conjunct H3′, verbatim; the hypothesis of exact type of target
6 (a), binding), `T2471_WTail2` (generic clause 4 with the canonical martingale `Σ martIncNg`; binding unless D2 changes the
canonical `Mart`, then fixed at the 1a-audit); then shapes (not binding): the D2 kernel class, the band and BA readings, the
list identities, the assembly.  Part 3: the band twins and the per-step layer the census reads (unchanged; not edited).
m = 2 only (TN-C4): no statement here mentions `STGridRepNgL` as a premise.
Merged names only.  No proof terms, no placeholders.
Run: lake env lean docs/tickets/checks/T2471-check.lean
-/
import RBM3D.BA.TwistStep
import RBM3D.BA.TwistGridWTail2
import RBM3D.BA.TwistGridTail2
import RBM3D.BA.TwistGridRem2
import RBM3D.BA.Step2BA
import RBM3D.BA.FlowPins
import RBM3D.BA.EKPins
import RBM3D.BA.GreenSchur
import RBM3D.Chain.Step2Kern
import RBM3D.Chain.GridDuhamelGen
import RBM3D.Induction.Step2Iterate
import RBM3D.Induction.StepDecompN
import RBM3D.Induction.GridAssemblyN
import RBM3D.Induction.LoopC2N
import RBM3D.Induction.PfStep5
import RBM3D.Path.QVIdentity
import RBM3D.Path.DifREP3

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the generic pins over a carrier (T8b) and the clause-4 vocabulary
#check @RBM.BA.Step2Mat
#check @RBM.BA.FlowFM
#check @RBM.BA.STGridRepNAtgL
#check @RBM.BA.STGridRepNgL
#check @RBM.BA.STGridMartgL
#check @RBM.BA.STGridMartAtgL
#check @RBM.BA.STgANg
#check @RBM.BA.STgDriftNg
#check @RBM.BA.STgAg
#check @RBM.BA.STgDriftg
#check @RBM.BA.STEEMg
#check @RBM.BA.STeeMg
#check @RBM.BA.STeeUMg
#check @RBM.BA.STLKMg
#check @RBM.BA.STLKIMg
#check @RBM.BA.Step2Gen_uKer
#check @RBM.BA.Step2Gen_UN
#check @RBM.BA.Step2Gen_thetaKer
-- the kernel window and algebra, the canonical martingale (T4s1, `Chain/GridDuhamelGen.lean`)
#check @RBM.BA.Step2Gen_USemigroup
#check @RBM.BA.step2Gen_USemigroup_band
#check @RBM.BA.Step2Gen_UN_add
#check @RBM.BA.Step2Gen_UN_self
#check @RBM.BA.Step2Gen_UN_comp
#check @RBM.BA.AvecNg
#check @RBM.BA.martIncNg
#check @RBM.BA.predIncNg
#check @RBM.BA.AvecNg_two
#check @RBM.BA.StoppedAzumaNg
-- band bridges of the vocabulary
#check @RBM.BA.bandStep2Mat
#check @RBM.BA.bandFM
#check @RBM.BA.bandStep2_martIncN
#check @RBM.BA.bandStep2_Ugen
#check @RBM.BA.bandStep2_STeeM
#check @RBM.BA.bandStep2_STeeUM
#check @RBM.BA.bandStep2_STGridRepNAt
#check @RBM.BA.Step2Kern_uKer_band
#check @RBM.BA.Step2Kern_UN_band
-- the BA carrier and flow
#check @RBM.BA.baStep2Mat
#check @RBM.BA.baStep2Mat_toFlowFM
#check @RBM.BA.baStep2Mat_Hpath
#check @RBM.BA.baStep2Mat_Pp
#check @RBM.BA.baStep2Mat_LM
#check @RBM.BA.baStep2Mat_KI
#check @RBM.BA.baFM
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAmF
#check @RBM.BA.BAReal
#check @RBM.BA.BAflow_real
#check @RBM.BA.BAflow_lam0_window
-- the BA kernel facts (sources of the D2 kernel class at BA)
#check @RBM.BA.BAuKer
#check @RBM.BA.BAUN
#check @RBM.BA.BAuKerSemigroup
#check @RBM.BA.BAuKerSemigroup_holds
#check @RBM.BA.BAuKer_self
#check @RBM.BA.BAuKer_comp
#check @RBM.BA.BAuKer_eq_one_add
#check @RBM.BA.EKPins_norm_uKer_le
#check @RBM.BA.Step2Kern_uKer_BA
#check @RBM.BA.Step2Kern_UN_BA
#check @RBM.BA.twU
#check @RBM.BA.twU_eq_uKer
#check @RBM.BA.TwistGridWTail_twU_conj
#check @RBM.BA.TwistGridWTail_sum_norm_twU_le
#check @RBM.BA.TwistGridWTail_norm_twU_sub_one_le
#check @RBM.BA.TwistGridWTail_norm_twU_sub_le
-- TL's per-step layer (label type `ι` arbitrary; sources of the D2 increment class at BA) and the one-slot tail
#check @RBM.BA.TwistGridWTail_condMGF_generic
#check @RBM.BA.TwistGridWTail_Y_fields
#check @RBM.BA.TwistGridWTail_hermTestFun
#check @RBM.BA.TwistGridWTail_linTrVar_le_QV
#check @RBM.BA.TwistGridWTail_twEEM_norm_le
#check @RBM.BA.TwistGridWTail_twEEM_sub_le
#check @RBM.BA.TwistGridTail_condMGF_Z
#check @RBM.BA.TwistGridWTail2_core
#check @RBM.BA.TwistGridWTail2_tail_at
-- TL's grid pins with the explicit `twMart`, `twRem` (inputs of the assembly, target 6)
#check @RBM.BA.BATwistGridRem
#check @RBM.BA.BATwistGridTail
#check @RBM.BA.BATwistGridWTail
#check @RBM.BA.BATwistGridMartAt
#check @RBM.BA.baTwistGridRem_holds
#check @RBM.BA.baTwistGridTail_holds
#check @RBM.BA.baTwistGridWTail_holds
#check @RBM.BA.baTwistGridMart_holds
#check @RBM.BA.twAk
#check @RBM.BA.twMartInc
#check @RBM.BA.twMart
#check @RBM.BA.twRem
#check @RBM.BA.twDriftk
#check @RBM.BA.twEEk
#check @RBM.BA.twEEUk
-- loops, paths, instance data
#check @RBM.Gauss.loopFine
#check @RBM.Loop.KLloopOf
#check @RBM.Path.PathΩ
#check @RBM.Path.pathP
#check @RBM.Path.filt
#check @RBM.Path.pathH
#check @RBM.Path.gridTime
#check @RBM.Path.gridStep
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0

/-! ## Part 2: the target statements (content binding as marked) and shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Targets 6 (b) and 6 (a), conclusion** (content binding; TN-C2 verbatim, `T2459_P1` at `d = 3`, for every `d`): the
loop-length-2 list form of the grid pin at the BA carrier, all four clauses with one `Mart`, `Rem`.  It is T2460's former
`T2460_GridRepN2` (`docs/tickets/checks/T2460-check.lean:179-181`). -/
def T2471_GridRepN2 (d : ℕ) : Prop :=
  ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    STGridRepNAtgL d 2 C₀ BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0

/-- **Target 6 (a), hypothesis** (content binding): T2460's target 1 `T2460_Bridge` as amended (Amend 1: third conjunct H3′,
an inequality with the slot count 2), verbatim (`docs/tickets/checks/T2460-check.lean:159-172`).  Target 6 (a) takes it
inline as a hypothesis of exact type; target 6 (b) discharges it with T2460's `baGridBridge_holds` once T2460 is merged. -/
def T2471_Bridge (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
      ∀ᶠ n : ℕ in atTop, ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ∀ k ≤ K n, ∀ ω : PathΩ sz,
        twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ (a 1) (a 1) k ω (a 0) =
            STgAg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s t K n σ a k ω ∧
          twDriftk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ (a 0) (a 1) (a 1) k ω =
            STgDriftg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s t K n σ a k ω ∧
          ‖twEEk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ (a 0) (a 1) (a 1) k ω‖ ≤
            2 * ‖STEEMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (gridTime s t K n k)
              ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Hpath s t K n k ω) σ a‖

/-- **Target 2** (content binding unless D2 changes the canonical martingale): clause 4 of `STGridRepNAtgL d 2`
(`Chain/Step2Gen.lean:1026-1040`) for the canonical `Mart_k = Σ_{j<k} martIncNg` (`Chain/GridDuhamelGen.lean:198`), over a
carrier `(Flow, mk, T0)`; the generic twin of `GridRepWTailNAt d 2` (`Path/DifREP1.lean:112`).  Loop length 2 only (TN-C4). -/
def T2471_WTail2 (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
        ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
          ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) →
            ∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ i : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)),
              (mk sz z).Pp {ω | ∃ k, k ≤ K n ∧
                ((sz.size n : ℕ) : ℝ) ^ ε' *
                    (∑ j ∈ Finset.range k, gridStep s t K n *
                      ‖STeeUMg (mk sz z) n (gridTime s t K n j) (gridTime s t K n k)
                        ((mk sz z).Hpath s t K n j ω) i.1 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^
                        (1 / 2 : ℝ) <
                  ‖∑ j ∈ Finset.range k,
                    Step2Gen_UN (mk sz z).toFlowFM n i.1
                      (gridTime s t K n j) (gridTime s t K n k)
                      (fun b => (∑ j' ∈ Finset.range (j + 1), martIncNg (mk sz z) s t K n j' i.1 ω b) -
                        ∑ j' ∈ Finset.range j, martIncNg (mk sz z) s t K n j' i.1 ω b) i.2‖} ≤
                ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

-- Shape (D2 default, target 1): the kernel class `GridRepTailGen_Ker C n`: K1 the merged semigroup window, K2 row sums,
-- K3 near-identity, K4 conjugation (band: `norm_uKer_le` `Kernel/Evolution.lean:114`, `DifREP3:420, 226`; BA:
-- `TwistGridWTail_sum_norm_twU_le`, `_norm_twU_sub_one_le`, `_twU_conj` through `twU_eq_uKer`).
example : Prop := ∀ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ),
  Step2Gen_USemigroup C n ∧
  (∀ (σ σ' : Bool) (v w : ℝ), 0 ≤ v → v ≤ w → w < 1 → ∀ a : Zd d (sz.L n),
    ∑ b, ‖Step2Gen_uKer C n σ σ' v w a b‖ ≤ (1 - v) / (1 - w)) ∧
  (∀ (σ σ' : Bool) (s t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
    ∑ b, ‖Step2Gen_uKer C n σ σ' s t a b - (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b‖ ≤ |t - s| * (1 - t)⁻¹) ∧
  (∀ (σ σ' : Bool) (v w : ℝ), 0 ≤ w → w < 1 → ∀ a b : Zd d (sz.L n),
    Step2Gen_uKer C n (!σ) (!σ') v w a b = starRingEnd ℂ (Step2Gen_uKer C n σ σ' v w a b))

-- Shape (target 4, kernel part at BA): the window K1 at the BA carrier under `BAReal` at `g₀ = lam0 n` (no `sz.lam`).
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (κ : ℝ),
  BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n) → Step2Gen_USemigroup (baFM sz lam0 E) n

-- Shape (target 3 (a)): the generic clause 4 at the band carrier is the band's `GridRepWTailNAt d 2`.
example : Prop := ∀ d : ℕ,
  RBM.Ind.GridRepWTailNAt d 2 ↔
    T2471_WTail2 d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandStep2Mat sz (STflowE z))
      (fun _ z n => lemT (z n))

-- Shape (target 4): the generic clause 4 at the BA carrier along the flow, every `d`.
example : Prop := ∀ d : ℕ,
  T2471_WTail2 d BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0

-- Shapes (target 5; T2460's former target 4 (a), `docs/tickets/checks/T2460-check.lean:196-208`): the loop-length-2 list
-- identities at the BA carrier (twins of `STgA_eq_STgAN`, `STgDrift_eq_STgDriftN`, `STEEM_eq_STeeM`,
-- `Induction/Step2Iterate.lean:1602, 1709, 1698`).  The 1a checks each one in formulas and numerics.
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (lam0 E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz),
  STgAg (baStep2Mat sz lam0 E) s t K n σ a k ω = STgANg (baStep2Mat sz lam0 E) s t K n σ a k ω

example : Prop := ∀ {d : ℕ} (sz : Sizes d) (lam0 E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz),
  STgDriftg (baStep2Mat sz lam0 E) s t K n σ a k ω = STgDriftNg (baStep2Mat sz lam0 E) s t K n σ a k ω

example : Prop := ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
  STEEMg (baStep2Mat sz lam0 E) n u H σ a = STeeMg (baStep2Mat sz lam0 E) n u H σ a a

-- Shape (target 6 (a)): the assembly with the bridge as a hypothesis of exact type.
example : Prop := ∀ d : ℕ, T2471_Bridge d → T2471_GridRepN2 d

-- Shape (route of target 6 (a)): TL's explicit parts, the bridge and the BA clause 4 give the full pin.
example : Prop := ∀ (d : ℕ) (C₀ : ℝ), 0 ≤ C₀ → BATwistGridRem d C₀ → BATwistGridTail d → T2471_Bridge d →
  T2471_WTail2 d BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0 → T2471_GridRepN2 d

-- Shape (consumer U5d): the TN-C2 statement at `d = 3`, i.e. `T2459_P1` with `T2459_Flow 3` unfolded to `BAFlow`.
example : Prop := T2471_GridRepN2 3

-- Shape (UBA-C1 as amended, DECISIONS §273 (1)): the R1 literal, the only admissible comparison text if a generic statement
-- here ever crosses size level and kernel level (not expected; target 8 (a)).
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (gK : ℕ → ℝ) (A : ℝ),
  ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2

-- Shape (target 7): the BA flow datum of the instances, the statements of `flow_sz0` and `half_lt_t0`.
open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst in
example : Prop := BAFlow sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq ∧ ∀ n : ℕ, (1 / 2 : ℝ) < BAflowT0 sz0 zSeq n

end RBM.BA

end

/-! ## Part 3: the band twins, the per-step layer of the D1 census, the `m = 2` readers (unchanged; not edited) -/

-- the band tail and its pins (`Path/DifREP1-3`)
#check @RBM.Ind.gridRepWTailQN_holds
#check @RBM.Ind.gridRepWTailN_holds
#check @RBM.Ind.GridRepWTailQNAt
#check @RBM.Ind.GridRepWTailNAt
#check @RBM.Ind.GridRepTailNAt
#check @RBM.Ind.GridRepRemNAt
#check @RBM.Ind.difRepMartN
#check @RBM.Ind.difRep3_UN_transfer
#check @RBM.Ind.zeroModeSet_UN_eq_uKerQ
#check @RBM.Ind.gridRepTailN_holds
#check @RBM.Ind.gridRepRemN_holds
#check @RBM.Ind.stGridRepNAt_of_parts
#check @RBM.Ind.stGridRepN_of_tails
#check @RBM.Ind.stGridRepN_holds
-- the `Z` peeling and the proxy (`Path/DifREP2`)
#check @RBM.Ind.difRep2_peel
#check @RBM.Ind.difRep2_norm_STeeM_le_N
#check @RBM.Ind.difRepTail_condMGF_Z
-- the per-step layer (band)
#check @RBM.Ind.AbCN
#check @RBM.Ind.stepZCN
#check @RBM.Ind.stepXiCN
#check @RBM.Ind.ZvecN
#check @RBM.Ind.YvecN
#check @RBM.Ind.YMomentsN
#check @RBM.Ind.HermTestFunLoopN
#check @RBM.Ind.hermTestFunLoopN
#check @RBM.Path.HermTestFun
#check @RBM.Path.EEShift
#check @RBM.Path.eeShift
#check @RBM.Path.QVPropagated
#check @RBM.Path.qvPropagated
-- the band kernel
#check @RBM.uKer
#check @RBM.UN
#check @RBM.norm_uKer_le
-- the loop-length-2 identities and the readers (all `m = 2`)
#check @RBM.Gauss.Sizes.STeeUM
#check @RBM.Gauss.Sizes.STgA_eq_STgAN
#check @RBM.Gauss.Sizes.STgDrift_eq_STgDriftN
#check @RBM.Gauss.Sizes.STEEM_eq_STeeM
#check @RBM.Gauss.Sizes.ST_gridMart_of_repN
#check @RBM.Gauss.Sizes.pfStep5_walk
