/-
Release check for T2217 (dispatcher V1, Mon Oct  5 21:00 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20, §29,
§45 O2, §67, §68).
S6-03 (stochastic layer ST-5, Step 6): proves the merged pin `STImproveExpAver` (`lem:improve_exp_aver`, `6:12-21`;
`RBM3D/Induction/Step6Pins.lean:191`, unchanged) by porting RBM2D `Evolution/Step61.lean` (c9a24cf) to `d ≥ 3`, in the
new file `RBM3D/Induction/ExpAvg.lean`; deletes its owed registry line (`RBM3D/Test/Axioms.lean:229`).
Section 1: the merged names the port uses (exact namespaces; file and last commit on `main` 0bc4633).
Section 2: the statements of the public theorems of `ExpAvg.lean` as closed `Prop`s, in the temporary namespace
`RBM.Gauss.Sizes.T2217Check` (T2217 proves each, same name, in `RBM.Gauss.Sizes`; the section variables
`{d : ℕ} (sz : Sizes d)` are written out where Lean includes them).  RBM2D source of each in the comment above it.
Section 3: the statements of the instances T2217 compiles (`RBM.Gauss.Step6Inst`; the merged Step-6 instance data
`sz0, z0, sInst, tInst` / `szB, zB` / `szG, zB`), as `Prop`-valued `example`s (no proof obligation).
Statement and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Imports: merged modules only, not `RBM3D`.  No Mathlib lemma is `#check`ed.
Run from the main worktree: `lake env lean docs/tickets/checks/T2217-check.lean`.
-/
import RBM3D.Induction.Step6Kit
import RBM3D.Induction.ConArgDet
import RBM3D.Gauss.LoopGenerator
import RBM3D.Gauss.DominationAt
import RBM3D.Evolution.XiPins
import RBM3D.Propagator.Pins

/-! ## 1. Merged names -/

-- `RBM3D/Induction/Step6Pins.lean` (cda3bb2; S6-01 = T2204): the pin and its conclusion predicates, the merged instance
#check @RBM.Gauss.Sizes.STExpAvgAt
#check @RBM.Gauss.Sizes.STImproveExpAver
#check @RBM.Gauss.Sizes.STExpAvgU
#check @RBM.Gauss.Sizes.STStep2Core
#check @RBM.Gauss.Sizes.STStep6Concl
#check @RBM.Gauss.Sizes.STExpLKLKHi
#check @RBM.Gauss.Sizes.STExpDuhamelZ
#check @RBM.Gauss.Sizes.STExpDuhamelQ
#check @RBM.Gauss.Sizes.STExpDriftLo
#check @RBM.Gauss.Sizes.STExpDriftDecay
#check @RBM.Gauss.Sizes.STExpWardI
#check @RBM.Gauss.Sizes.STExpWardII
#check @RBM.Gauss.Sizes.STExpIntI
#check @RBM.Gauss.Sizes.STExpIntII
#check @RBM.Gauss.Sizes.STExpIntIV
#check @RBM.Gauss.Sizes.STExpIniI
#check @RBM.Gauss.Step6Inst.InstIng6Concl
#check @RBM.Gauss.Step6Inst.inst_improveExpAver
-- `RBM3D/Induction/Step6Kit.lean` (9e0d6a7; S6-02 = T2211): the consumers of the pin and the kit lemmas the port uses
#check @RBM.Gauss.Sizes.st6_prec_det_iff
#check @RBM.Gauss.Sizes.st6_lam_pos
#check @RBM.Gauss.Sizes.st6_flowE_le
#check @RBM.Gauss.Sizes.st6_mE_im_ge
#check @RBM.Gauss.Sizes.st6_expAvgU_of_pin
#check @RBM.Gauss.Sizes.ST_step6_caseIV_of_pins
#check @RBM.Gauss.Sizes.ST_step6_caseII_of_pins
#check @RBM.Gauss.Sizes.ST_step6_caseI_of_pins
#check @RBM.Gauss.Step6Inst.inst_skeleton6I
#check @RBM.Gauss.Step6Inst.inst_skeleton6II
#check @RBM.Gauss.Step6Inst.inst_skeleton6IV
#check @RBM.Gauss.Step6Inst.inst_expAvgU
-- `RBM3D/Induction/Step2Iterate.lean` (c5bbae7)
#check @RBM.Gauss.Sizes.ST_one_sub_lemT
#check @RBM.Gauss.Sizes.ST_Gres_false
#check @RBM.Gauss.Sizes.ST_Eblk_herm
#check @RBM.Gauss.Sizes.ST_Lloop_one_false
#check @RBM.Gauss.Sizes.ST_Kloop_one
-- `RBM3D/Induction/Step5Kit.lean` (85e43db), `ScaleFacts.lean` (5d1e6b1), `ScaleFacts3.lean` (7c3072a)
#check @RBM.Gauss.Sizes.st5_t_lt_one
#check @RBM.Gauss.Sizes.STBctl_pos
#check @RBM.Gauss.Sizes.st_Bctl_ge
-- `RBM3D/Induction/Defs.lean` (64bdfd3)
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.InductionDefsInst.z0
#check @RBM.Gauss.InductionDefsInst.flow_z0
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.InductionDefsInst.tInst
-- `RBM3D/Induction/Step34Pins.lean` (fc76526), `Step5Pins.lean` (d7da51e): instance data
#check @RBM.Gauss.Sizes.STLKU
#check @RBM.Gauss.Step34Inst.szB
#check @RBM.Gauss.Step34Inst.zB
#check @RBM.Gauss.Step34Inst.sz0_hs0
#check @RBM.Gauss.Step34Inst.sz0_hst
#check @RBM.Gauss.Step34Inst.sz0_ht
#check @RBM.Gauss.Step5Inst.szG
-- `RBM3D/Graph/LWPins.lean` (975f4ff): the premise `(Gt_avgbound_flow)`; `LWtermEXP` (premise of skeletons I, II)
#check @RBM.Gauss.Sizes.LWAvgLaw
#check @RBM.Gauss.Sizes.LWtermEXP
-- `RBM3D/Induction/ConArgDet.lean` (bbd22a5)
#check @RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero
-- `RBM3D/Gauss/FineModel.lean` (0a873f1): the model at one size and along the sequence
#check @RBM.Gauss.CoordF
#check @RBM.Gauss.Ω
#check @RBM.Gauss.gvarF
#check @RBM.Gauss.PF
#check @RBM.Gauss.Xmat
#check @RBM.Gauss.Hflow
#check @RBM.Gauss.Hflow_isHermitian
#check @RBM.Gauss.Sizes.SeqΩ
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.slice
#check @RBM.Gauss.Sizes.measurable_slice
#check @RBM.Gauss.Sizes.seqP_map_slice
#check @RBM.Gauss.Sizes.seqHflow
-- `RBM3D/Loop/GLoopFlow.lean` (868b3b4): `G`, loops on the block index and along the sequence
#check @RBM.Gauss.Gres
#check @RBM.Gauss.loopM
#check @RBM.Gauss.blockMat
#check @RBM.Gauss.loopFine
#check @RBM.Gauss.loopOf
#check @RBM.Gauss.loopL
#check @RBM.Gauss.loopM_eq_loopL
#check @RBM.Gauss.Sizes.Lloop
-- `RBM3D/Loop/GLoop.lean` (e0c58e6), `Loop/TreeRep.lean` (b06ff9b)
#check @RBM.Gauss.Eblk
#check @RBM.Gauss.etaT
#check @RBM.Gauss.etaT_pos
#check @RBM.Loop.LoopIdx
-- `RBM3D/Gauss/FlowCalculus.lean` (6f99812)
#check @RBM.Gauss.spectralM_quadratic
#check @RBM.Gauss.HflowBlock
#check @RBM.Gauss.HflowBlock_isHermitian
#check @RBM.Gauss.continuous_matrixTrace
#check @RBM.Gauss.continuous_gloop_HflowBlock_sample
#check @RBM.Gauss.measurable_gloop_HflowBlock_sample
#check @RBM.Gauss.norm_gloop_le_crude
-- `RBM3D/Gauss/LoopCoordinate.lean` (31476de), `LoopFlowStein.lean` (06429ba)
#check @RBM.Gauss.coordinateBlock
#check @RBM.Gauss.HflowBlock_update
#check @RBM.Gauss.hasDerivAt_HflowBlock_update
#check @RBM.Gauss.Xblock_eq_sum_coordinates
#check @RBM.Gauss.stein_gloop_first_coordinate_derivative
-- `RBM3D/Gauss/DominationAt.lean` (9e2b00f): Stein (RBM2D `Gauss/SteinMatrix`) and the reverse moment bridge
-- (RBM2D `Gauss/MomentBridge`)
#check @RBM.Gauss.GaussianProduct.law
#check @RBM.Gauss.GaussianProduct.stein
#check @RBM.Gauss.MomentDomAt
#check @RBM.Gauss.momentDomAt_of_stochDomAt
#check @RBM.Gauss.momentDomAt_of_stochDomAt_of_nonneg
-- `RBM3D/Gauss/LoopGenerator.lean` (3b98b27): initial values at `u = 0`, `E_a` traces (RBM2D `LoopInitialValueScalar`)
#check @RBM.Gauss.initialLoopValue
#check @RBM.Gauss.gloop_HflowBlock_zero
#check @RBM.Gauss.integral_gloop_HflowBlock_zero
#check @RBM.Gauss.Gres_zero_eq_scalar
#check @RBM.Gauss.trace_Eblk_eq_one
#check @RBM.Gauss.initialGreenScalar
#check @RBM.Gauss.initialLoopValue_one_edge
#check @RBM.Gauss.trace_Eblk_mul_Eblk
-- `RBM3D/Hierarchy/ContractionSecondLoop.lean` (64a33ea; RBM2D `ContractionSecondLoopSameEdge`)
#check @RBM.Gauss.sum_coordinateBlock_trace_pair
-- `RBM3D/Defs/Block.lean` (a722f63): the block profile `S^(B)(g)`
#check @RBM.SB
#check @RBM.SB_transpose
#check @RBM.sum_SB_row
#check @RBM.sum_nnnorm_SB_row
#check @RBM.norm_SB
-- `RBM3D/Propagator/Basic.lean` (020ec7a), `Props4.lean` (892334b), `Pins.lean` (b06ff9b)
#check @RBM.Theta
#check @RBM.Theta_mul_of_three_le
#check @RBM.norm_t_mul_lt_one
#check @RBM.PropSpin
-- `RBM3D/Kernel/Evolution.lean` (ff8d36d), `Evolution/XiPins.lean` (3dc4f1c): the `d ≥ 3` row sum of `Θ_{u m²}`
-- (replaces RBM2D `xiRowBoundShort`, `cShortRow`)
#check @RBM.uKer
#check @RBM.EKSameRow
#check @RBM.ekSameRow_holds
-- `RBM3D/Defs/StochDomAt.lean` (9e2b00f)
#check @RBM.StochDomAt
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.one_le_size
#check @RBM.Gauss.Sizes.tendsto_size
-- `RBM3D/Defs/Sizes.lean` (0a873f1), `Defs/Params.lean` (c3f3d5d)
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.WO
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.locDomain
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Bparam
-- `RBM3D/Defs/Semicircle.lean` (fbc9870)
#check @RBM.mE
#check @RBM.mE_mul
#check @RBM.norm_mE
#check @RBM.mE_im_pos
#check @RBM.mSigma
#check @RBM.zt
#check @RBM.zt_im
#check @RBM.lemE
#check @RBM.lemT
#check @RBM.lemT_lt_one
-- `RBM3D/Defs/Lattice.lean` (51f1a17)
#check @RBM.Zd

/-! ## 2. Statements of the public theorems of `ExpAvg.lean` (closed `Prop`s) -/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes.T2217Check

open RBM RBM.Gauss

/-! ### Fixed size (RBM2D `Step61.lean` §FixedSize, §Deterministic, §Combine; renaming rules R1-R4) -/

-- RBM2D `step61_stein` (`Step61.lean:271`, private there): Stein for `H_u = √u X`,
-- `𝔼 tr(H G E_a) = -u Σ_p S_{pa} 𝔼[g_p g_a]`, `g_b = tr(G E_b)`; the variance profile of `PF d L W g` is `SB d L g`.
def expAvg_stein : Prop :=
  ∀ {d : ℕ} (L W : ℕ) [NeZero L] [NeZero W] (g u : ℝ), 0 ≤ u → ∀ {z : ℂ}, z.im ≠ 0 → ∀ a : Zd d L,
    ∫ ω : Ω d L W, Matrix.trace (HflowBlock d L W u ω * Gres (HflowBlock d L W u ω) z true *
        Eblk d L W a) ∂(PF d L W g) =
      -(u : ℂ) * ∑ p : Zd d L, SB d L g p a * ∫ ω : Ω d L W,
        loopL d L W (HflowBlock d L W u ω) z ⟨[true], [p]⟩ *
          loopL d L W (HflowBlock d L W u ω) z ⟨[true], [a]⟩ ∂(PF d L W g)

-- RBM2D `step61_selfcons` (`Step61.lean:339`): the self-consistent equation `x = u m² S x + y` at `z = z_u`.
def expAvg_selfcons : Prop :=
  ∀ {d : ℕ} (L W : ℕ) [NeZero L] [NeZero W] (g : ℝ), 3 ≤ L → ∀ {E u : ℝ}, |E| < 2 → 0 ≤ u → u < 1 →
    ∀ a : Zd d L,
      (∫ ω : Ω d L W, loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [a]⟩ ∂(PF d L W g)) - mE E =
        (u : ℂ) * mE E ^ 2 * ∑ b : Zd d L, SB d L g b a *
            ((∫ ω : Ω d L W, loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [b]⟩ ∂(PF d L W g)) -
              mE E) +
          (u : ℂ) * mE E * ∑ b : Zd d L, SB d L g b a * ∫ ω : Ω d L W,
            (loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [b]⟩ - mE E) *
              (loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [a]⟩ - mE E) ∂(PF d L W g)

-- RBM2D `step61_theta_solve` + `step61_theta_row_sum` + `step61_norm_solve` (`Step61.lean:428-504`), `d ≥ 3`:
-- `Θ_{u m²}` inverts the equation and its row sums are bounded by the constant of `ekSameRow_holds`
-- (`EKSameRow` at `s = 0`, `σ = +`, `κ' = √(2κ)/2`), with no `log L` (RBM2D: `1 + cShortRow κ (1 + log L)`).
def expAvg_norm_solve : Prop :=
  ∀ {d : ℕ}, 3 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ Λ →
      ∀ E u : ℝ, |E| ≤ 2 - κ → 0 ≤ u → u < 1 →
        ∀ x y : Zd d L → ℂ, (∀ a, x a = ((u : ℂ) * mE E ^ 2) * ∑ b, SB d L g b a * x b + y a) →
          ∀ K : ℝ, (∀ a, ‖y a‖ ≤ K) → ∀ a, ‖x a‖ ≤ C * K

-- RBM2D `step61_expErr_le` (`Step61.lean:528`): second moments of `g_b - m` bound `|𝔼 g_a - m|`; the constant
-- depends on `d, Λ, κ` only (no `L`, `W`, `g`, `u`, `E`).
def expAvg_expErr_le : Prop :=
  ∀ {d : ℕ}, 3 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧ ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ Λ →
      ∀ E u : ℝ, |E| ≤ 2 - κ → 0 ≤ u → u < 1 → ∀ K : ℝ,
        (∀ b : Zd d L, ∫ ω : Ω d L W,
          ‖loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [b]⟩ - mE E‖ ^ 2 ∂(PF d L W g) ≤ K) →
        ∀ a : Zd d L,
          ‖(∫ ω : Ω d L W, loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [a]⟩ ∂(PF d L W g)) - mE E‖ ≤
            C * K

/-! ### Along the sequence (RBM2D §ScaleFacts, §Moment, §Main) -/

-- new (`d ≥ 3`; RBM2D `scaleM ≤ N`, `Step61.lean:631`): the lower bound `hΦlow` of the moment bridge at `B = 1`.
def expAvg_Bctl_ge : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ}, 0 ≤ u → u < 1 → ((sz.size n : ℕ) : ℝ)⁻¹ ≤ sz.Bctl n u

-- new (`d ≥ 3`; RBM2D `RangeCond`, `Step61.lean:744-787`): `η_u⁻¹ ≤ N` along the flow for `u ≤ lemT z`
-- (`1 - u ≥ Im z/(1+|z|) ≥ N^{-1+ε}/4`, `ST_one_sub_lemT`; `Im m ≥ √(2κ)/2`, `st6_mE_im_ge`).
def expAvg_eta_inv_le : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → 0 < ε → ∀ {z : ℕ → ℂ}, STFlow sz κ ε 𝔠 𝔡 z →
    ∀ᶠ n in atTop, ∀ u : ℝ, u ≤ lemT (z n) → (etaT (STflowE z n) u)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)

-- RBM2D `step61_moment` (`Step61.lean:683`): second (all) moments of `|g_b - m|` from `(Gt_avgbound_flow)` at `u`
-- (`LWAvgLaw`, the `k = 1`, charge `+` case of `STLK`), through the reverse bridge `momentDomAt_of_stochDomAt`.
def expAvg_moment : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → 0 < ε → ∀ {z : ℕ → ℂ}, STFlow sz κ ε 𝔠 𝔡 z →
    ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ lemT (z n)) → LWAvgLaw sz (STflowE z) u →
      MomentDomAt sz.seqP sz.size (U := fun n => Zd d (sz.L n))
        (fun n b ω => ‖Lloop sz n (STflowE z n) (u n) (fun _ : Fin 1 => true) (fun _ => b) ω -
          mE (STflowE z n)‖)
        (fun n _ => sz.Bctl n (u n))

-- new (the charge `-`; RBM2D `Step61Concl` has charge `+` only): `𝔼 𝓛^{(1)}_{-} = conj 𝔼 𝓛^{(1)}_{+}`
-- (`ST_Lloop_one_false` under the integral).
def expAvg_integral_conj : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (a : Zd d (sz.L n)),
    ∫ ω, Lloop sz n E u (fun _ : Fin 1 => false) (fun _ => a) ω ∂(sz.seqP) =
      (starRingEnd ℂ) (∫ ω, Lloop sz n E u (fun _ : Fin 1 => true) (fun _ => a) ω ∂(sz.seqP))

-- RBM2D `step61_check_u_zero` (`Step61.lean:998`): at `u = 0` the left side of the pin vanishes (`G_0 = m I`).
def expAvg_u_zero : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ}, |E| < 2 → ∀ a : Zd d (sz.L n),
    ∫ ω, Lloop sz n E 0 (fun _ : Fin 1 => true) (fun _ => a) ω ∂(sz.seqP) = mE E

-- RBM2D `step61` (`Step61.lean:853`), `d ≥ 3`, both charges: the pin's conclusion from `LWAvgLaw` alone
-- (the premise `STLK` of the pin is not used: T2191 prove report (d) item 2).
def STExpAvgAt_of_LWAvgLaw : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), 3 ≤ d → ∀ {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → 0 < ε → ∀ {z : ℕ → ℂ},
    STFlow sz κ ε 𝔠 𝔡 z → ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ lemT (z n)) →
      LWAvgLaw sz (STflowE z) u → STExpAvgAt sz (STflowE z) u

-- The merged pin `STImproveExpAver` (`Step6Pins.lean:191`), proved.
def stImproveExpAver_holds : Prop := ∀ d : ℕ, STImproveExpAver d

end RBM.Gauss.Sizes.T2217Check

/-! ## 3. The statements of the instances T2217 compiles (`d = 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`) -/

namespace RBM.Gauss.Step6Inst.T2217Check

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.Step5Inst RBM.Path Filter

-- statement of `inst_expAvgAt_holds` (from `STExpAvgAt_of_LWAvgLaw` at `(sz0, z0, tInst)`; `STLK` not needed)
example : Prop := ∀ (hA : LWAvgLaw sz0 (STflowE z0) tInst), STExpAvgAt sz0 (STflowE z0) tInst

-- statement of `inst_improveExpAver_holds` (the merged `inst_improveExpAver` with `h := stImproveExpAver_holds 3`)
example : Prop :=
  ∀ (hA : LWAvgLaw sz0 (STflowE z0) tInst) (hK : STLK sz0 (STflowE z0) tInst), STExpAvgAt sz0 (STflowE z0) tInst

-- statement of `inst_expAvgU_holds` (the merged `inst_expAvgU` with `hAvg` discharged)
example : Prop :=
  ∀ (hS2 : STStep2Core sz0 (STflowE z0) sInst tInst) (hLKU : STLKU sz0 (STflowE z0) sInst tInst),
    STExpAvgU sz0 (STflowE z0) sInst tInst

-- statement of `inst_skeleton6I_avg` (the merged `inst_skeleton6I` with `hAvg` discharged; regime (i))
example : Prop :=
  ∀ (hLK : STExpLKLKHi 3) (hLW : LWtermEXP 3) (hDu : STExpDuhamelZ 3) (hDuQ : STExpDuhamelQ 3)
    (hDec : STExpDriftDecay 3) (hWd : STExpWardI 3) (hIni : STExpIniI 3) (hInt : STExpIntI 3),
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)

-- statement of `inst_skeleton6II_avg` (the merged `inst_skeleton6II` with `hAvg` discharged; regime (ii))
example : Prop :=
  ∀ (hLK : STExpLKLKHi 3) (hLW : LWtermEXP 3) (hDu : STExpDuhamelZ 3) (hInt : STExpIntII 3) (hWd : STExpWardII 3),
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32)

-- statement of `inst_skeleton6IV_avg` (the merged `inst_skeleton6IV` with `hAvg` discharged; regime (iv))
example : Prop :=
  ∀ (hDu : STExpDuhamelZ 3) (hLo : STExpDriftLo 3) (hInt : STExpIntIV 3),
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4)

-- statement of `inst_eta_inv_le` (`expAvg_eta_inv_le` at `(sz0, z0)`)
example : Prop :=
  ∀ᶠ n in atTop, ∀ u : ℝ, u ≤ lemT (z0 n) → (etaT (STflowE z0 n) u)⁻¹ ≤ ((sz0.size n : ℕ) : ℝ)

-- statement of `inst_expAvg_u_zero` (`expAvg_u_zero` at `sz0`, `n = 0`, `E = 1/2`, `a = 0`)
example : Prop :=
  ∫ ω, Lloop sz0 0 (1 / 2) 0 (fun _ : Fin 1 => true) (fun _ => 0) ω ∂(sz0.seqP) = mE (1 / 2)

end RBM.Gauss.Step6Inst.T2217Check
