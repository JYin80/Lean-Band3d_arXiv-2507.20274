/-
Release check for T2218 (dispatcher V1, Mon Oct  5 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20, §29,
§45 O2, §64 (4), §67, §68).
S6-04 (stochastic layer ST-5, Step 6): proves the merged pin `STExpHier` (`(eq_L-Keee)` `3_5:73` at `n = 2` after
expectation, `6:90`; `RBM3D/Induction/Step6Pins.lean:213`, unchanged) by porting RBM2D `Evolution/MLExpHier.lean`
(c9a24cf, `expHierPin` `:643`) to `d ≥ 3`, in the new file `RBM3D/Induction/ExpHier.lean`; deletes its owed registry
line (`RBM3D/Test/Axioms.lean:230`).
Section 1: the merged names the port uses (exact namespaces, from the enclosing `namespace … end` blocks; file and
last commit on `main` 14513ee).
Section 2: the statements of the public theorems of `ExpHier.lean` as closed `Prop`s, in the temporary namespace
`RBM.Gauss.Sizes.T2218Check` (T2218 proves each, same name, in `RBM.Gauss.Sizes`; `{d : ℕ}` first).  RBM2D source of
each in the comment above it.
Section 3: the statements of the instances T2218 compiles (`RBM.Gauss.Step6Inst`; the merged instance data `sz0`,
`n = 0`: `L = 4`, `W = 32`, `lam = 1/64`, `E = 1/2`), as `Prop`-valued `example`s (no proof obligation).
Statement and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Imports: merged modules only, not `RBM3D`.  No Mathlib lemma is `#check`ed.
Run from the main worktree: `lake env lean docs/tickets/checks/T2218-check.lean`.
-/
import RBM3D.Induction.Step6Kit
import RBM3D.Induction.LoopGenN
import RBM3D.Path.DriftAlgebra
import RBM3D.Loop.KLTree
import RBM3D.Gauss.LoopGenerator

/-! ## 1. Merged names -/

-- `RBM3D/Induction/Step6Pins.lean` (cda3bb2; S6-01 = T2204): the pin, its vocabulary, its instance; the downstream pins
#check @RBM.Gauss.Sizes.STExpHier
#check @RBM.Gauss.Sizes.STExpErr
#check @RBM.Gauss.Sizes.STExpDrift
#check @RBM.Gauss.Sizes.STExpELKLK
#check @RBM.Gauss.Sizes.STExpEGt
#check @RBM.Gauss.Sizes.STExpDuhamelZ
#check @RBM.Gauss.Sizes.STExpDuhamelQ
#check @RBM.Gauss.Step6Inst.inst_expHier
#check @RBM.Gauss.Step6Inst.inst_duhamelZ
#check @RBM.Gauss.Step6Inst.inst_duhamelQ
-- `RBM3D/Induction/Step6Kit.lean` (9e0d6a7; S6-02 = T2211): the consumers of `STExpDuhamelZ/Q` (downstream via S6-05)
#check @RBM.Gauss.Sizes.st6_duhEq_of_pin
#check @RBM.Gauss.Sizes.st6_duhEqQ_of_pin
#check @RBM.Gauss.Sizes.ST_step6_caseIII_of_pins
#check @RBM.Gauss.Sizes.ST_step6_caseIV_of_pins
#check @RBM.Gauss.Sizes.ST_step6_caseII_of_pins
#check @RBM.Gauss.Sizes.ST_step6_caseI_of_pins
-- `RBM3D/Induction/Step2Defs.lean` (86124dc): the matrix-level `n = 2` objects and their list-index forms
#check @RBM.Gauss.Sizes.STmsig
#check @RBM.Gauss.Sizes.STLM
#check @RBM.Gauss.Sizes.STLM_seqHflow
#check @RBM.Gauss.Sizes.STLKM
#check @RBM.Gauss.Sizes.STavgM
#check @RBM.Gauss.Sizes.STEGtM
#check @RBM.Gauss.Sizes.STELKLKM
#check @RBM.Gauss.Sizes.STthetaOp
#check @RBM.Gauss.Sizes.STEGt
#check @RBM.Gauss.Sizes.STLIM
#check @RBM.Gauss.Sizes.STLKIM
#check @RBM.Gauss.Sizes.STksimLKM
#check @RBM.Gauss.Sizes.STelklkM
#check @RBM.Gauss.Sizes.STegtM
-- `RBM3D/Induction/Step5Pins.lean` (d7da51e), `Induction/Defs.lean` (64bdfd3)
#check @RBM.Gauss.Sizes.STELKLK
#check @RBM.Gauss.Sizes.STKloop
-- `RBM3D/Induction/HierarchyN.lean` (9bb2cbe), `Induction/LoopGenN.lean` (e56d95c): the general-`n` hierarchy, proved
-- (RBM2D `hierarchyN_two`, `MLExpVocab.lean:239`); its `k = 2` reductions `HierarchyN.lean:81-140` are private
#check @RBM.Ind.HierarchyN
#check @RBM.Ind.hierarchyN_two
#check @RBM.Ind.STLoopGenNForm
#check @RBM.Ind.hierarchyN_holds
-- `RBM3D/Kernel/Evolution.lean` (ff8d36d): `Θ^{(n)}` of `HierarchyN`
#check @RBM.ThetaN
#check @RBM.thetaKer
#check @RBM.cycProd
-- `RBM3D/Path/OneStep.lean` (593e519), `Path/DriftAlgebra.lean` (07ede19): the generator and the `σ = (+,-)` forms
#check @RBM.Path.genMat
#check @RBM.Path.KpmODE
#check @RBM.Path.kpmODE
#check @RBM.Path.HierarchyN2
-- `RBM3D/Loop/Primitive.lean` (58329b9), `Loop/KLTree.lean` (b06ff9b): the `𝒦` ODE at `n = 2`, every sign
-- (replaces RBM2D `KLoop.isPrimitive_Kcal`, `Loop/TreeRep`)
#check @RBM.Loop.kTwo
#check @RBM.Loop.hasDerivAt_kTwo
#check @RBM.Loop.norm_mul_lt_one
#check @RBM.Loop.KLK
#check @RBM.Loop.KLloopOf
#check @RBM.Loop.KLK_two_eq_kTwo
#check @RBM.Loop.LoopIdx
#check @RBM.Loop.LoopIdx.WF
-- `RBM3D/Gauss/LoopGenerator.lean` (3b98b27): the expected generator (RBM2D `Gauss/LoopGeneratorExpectation`) and
-- the window continuity (RBM2D `Hierarchy/LoopHierarchyCutContinuity`)
#check @RBM.Gauss.samplewiseLoopGeneratorCuts
#check @RBM.Gauss.samplewise_loop_generator_eq_cuts
#check @RBM.Gauss.integrable_samplewiseLoopGeneratorCuts
#check @RBM.Gauss.deriv_integral_gloop_eq_integral_samplewiseLoopGeneratorCuts
#check @RBM.Gauss.continuousOn_gloop_any_window
#check @RBM.Gauss.norm_gloop_any_window_le
-- `RBM3D/Gauss/LoopFlowStein.lean` (06429ba; RBM2D `Gauss/LoopExpectationDerivative`, `LoopFlowCoordinateChain`)
#check @RBM.Gauss.hasDerivAt_integral_gloop_HflowBlock_spectralZ
#check @RBM.Gauss.gsigSpectralFlowDeriv
#check @RBM.Gauss.spectralWordDeriv
-- `RBM3D/Gauss/LoopCoordinate.lean` (31476de): coordinate lines and their derivatives
#check @RBM.Gauss.coordinateBlock
#check @RBM.Gauss.HflowBlock_update
#check @RBM.Gauss.coordinateWordDeriv
#check @RBM.Gauss.coordinateSecondWordDeriv
#check @RBM.Gauss.hasDerivAt_gloop_update
#check @RBM.Gauss.hasDerivAt_deriv_gloop_update
-- `RBM3D/Gauss/FlowCalculus.lean` (6f99812)
#check @RBM.Gauss.HflowBlock
#check @RBM.Gauss.HflowBlock_isHermitian
#check @RBM.Gauss.continuous_matrixTrace
#check @RBM.Gauss.continuous_gloopProd_HflowBlock_sample
#check @RBM.Gauss.continuous_gloop_HflowBlock_sample
#check @RBM.Gauss.measurable_gloop_HflowBlock_sample
#check @RBM.Gauss.spectralZ_im_gap
#check @RBM.Gauss.spectralZ_im
#check @RBM.Gauss.spectralM_im_pos
#check @RBM.Gauss.continuous_spectralZ
#check @RBM.Gauss.hasDerivAt_spectralZ
#check @RBM.Gauss.hasDerivAt_green_moving
#check @RBM.Gauss.spectralMSign
-- `RBM3D/Gauss/FineModel.lean` (0a873f1): the model at one size and along the sequence
#check @RBM.Gauss.CoordF
#check @RBM.Gauss.Ω
#check @RBM.Gauss.gvarF
#check @RBM.Gauss.PF
#check @RBM.Gauss.Xmat
#check @RBM.Gauss.coordinateMatrix
#check @RBM.Gauss.Hflow
#check @RBM.Gauss.Hflow_isHermitian
#check @RBM.Gauss.Sizes.SeqΩ
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.slice
#check @RBM.Gauss.Sizes.measurable_slice
#check @RBM.Gauss.Sizes.seqP_map_slice
#check @RBM.Gauss.Sizes.seqXmat
#check @RBM.Gauss.Sizes.seqHflow
-- `RBM3D/Loop/GLoopFlow.lean` (868b3b4)
#check @RBM.Gauss.Gres
#check @RBM.Gauss.loopM
#check @RBM.Gauss.blockMat
#check @RBM.Gauss.loopFine
#check @RBM.Gauss.loopOf
#check @RBM.Gauss.loopL
#check @RBM.Gauss.loopM_eq_loopL
#check @RBM.Gauss.gloopProd
#check @RBM.Gauss.Sizes.Lloop
-- `RBM3D/Defs/Sizes.lean` (0a873f1), `Gauss/Model.lean` (a722f63)
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.neZeroL
#check @RBM.Gauss.Idx
#check @RBM.Gauss.Vtx
#check @RBM.Gauss.SizesInst.sz0
-- `RBM3D/Defs/Block.lean` (a722f63), `Propagator/Basic.lean` (020ec7a)
#check @RBM.SB
#check @RBM.SB_transpose
#check @RBM.sum_SB_row
#check @RBM.norm_SB
#check @RBM.Theta
-- `RBM3D/Defs/Semicircle.lean` (fbc9870), `Defs/Lattice.lean` (51f1a17)
#check @RBM.mE
#check @RBM.norm_mE
#check @RBM.mE_im_pos
#check @RBM.mSigma
#check @RBM.norm_mSigma
#check @RBM.zt
#check @RBM.zt_im
#check @RBM.Zd

/-! ## 2. Statements of the public theorems of `ExpHier.lean` (closed `Prop`s) -/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes.T2218Check

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ### Fixed size (RBM2D `MLExpHier.lean` §1 `Good`, §3 Bridge, §4 FixedSize; renaming rules R1-R4) -/

-- RBM2D `MLExpHier_continuousOn_Lexp` (`MLExpHier.lean:499`, private there; via the class `Good`, `:63-158`):
-- the expected loop is continuous on `[0,1)`, **including `u = 0`**, for every loop index (no `WF` needed).
def expHier_continuousOn_integral_loopL : Prop :=
  ∀ {d : ℕ} (L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) {E : ℝ}, |E| < 2 → ∀ I : LoopIdx (Zd d L),
    ContinuousOn (fun u : ℝ => ∫ ω : Ω d L W, loopL d L W (HflowBlock d L W u ω) (zt E u) I ∂(PF d L W g))
      (Set.Ico 0 1)

-- RBM2D `MLExpHier_genMat_eq_cuts` (`MLExpHier.lean:436`, private there; with `_second_deriv` `:313`, the factor `u`
-- of `H_u = √u X`, and `_deriv_spec` `:415`): the one-step generator at the flow sample is the merged cut expression.
def expHier_genMat_eq_cuts : Prop :=
  ∀ {d : ℕ} (L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) {E u : ℝ}, |E| < 2 → 0 < u → u < 1 →
    ∀ (ω : Ω d L W) (I : LoopIdx (Zd d L)), I.WF →
      genMat d L W g E u (Hflow d L W u ω) I = samplewiseLoopGeneratorCuts d L W g ω E u I

-- new form (`d ≥ 3`, every sign; RBM2D `KLoop.isPrimitive_Kcal` at length `2`; the merged `KpmODE` is `σ = (+,-)`
-- only): `(pro_dyncalK)` at `n = 2` for `STKloop` (= `kTwo`, `KLK_two_eq_kTwo`; `hasDerivAt_kTwo`, `‖SB‖ = 1`).
def expHier_Kloop_hasDerivAt : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ}, |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      HasDerivAt (fun v : ℝ => sz.STKloop n E v σ a)
        ((((sz.W n : ℕ) : ℂ) ^ d) * ∑ c : Zd d (sz.L n), ∑ e : Zd d (sz.L n),
          sz.STKloop n E u σ ![a 0, c] * SB d (sz.L n) (sz.lam n) c e * sz.STKloop n E u σ ![e, a 1]) u

-- RBM2D `hierarchyN_two` (`MLExpVocab.lean:239`) / merged `HierarchyN2` (`DriftAlgebra.lean:75`, `σ = (+,-)` only):
-- the matrix-level hierarchy at `n = 2` for **every** `σ`, from `hierarchyN_holds` at `k = 2` and the private
-- reductions of `HierarchyN.lean:81-140` (`Σ_{l ∈ Icc 3 2}` empty).
def expHier_hierarchy_two : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ}, |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
      ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        genMat d (sz.L n) (sz.W n) (sz.lam n) E u M (loopOf σ a) -
            deriv (fun v : ℝ => sz.STKloop n E v σ a) u =
          sz.STthetaOp n E u σ (sz.STLKM n E u M σ) a + sz.STELKLKM n E u M σ a +
            sz.STEGtM n E u M σ a

-- RBM2D `MLExpHier_hasDerivAt` (`MLExpHier.lean:515`, private there): the expected hierarchy at one size, on `(0,1)`,
-- over the one-size law `PF d L W g` at `(L, W, g) = (sz.L n, sz.W n, sz.lam n)`; the drift as the two integrals of
-- `STExpDrift`.
def expHier_hasDerivAt_fixed : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ}, |E| < 2 → ∀ u : ℝ, 0 < u → u < 1 →
    ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      HasDerivAt (fun v : ℝ =>
          (∫ ω, loopL d (sz.L n) (sz.W n) (HflowBlock d (sz.L n) (sz.W n) v ω) (zt E v) (loopOf σ a)
            ∂(PF d (sz.L n) (sz.W n) (sz.lam n))) - sz.STKloop n E v σ a)
        (sz.STthetaOp n E u σ (fun b =>
            (∫ ω, loopL d (sz.L n) (sz.W n) (HflowBlock d (sz.L n) (sz.W n) u ω) (zt E u) (loopOf σ b)
              ∂(PF d (sz.L n) (sz.W n) (sz.lam n))) - sz.STKloop n E u σ b) a +
          ((∫ ω, sz.STELKLKM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ a ∂(PF d (sz.L n) (sz.W n) (sz.lam n))) +
            ∫ ω, sz.STEGtM n E u (Hflow d (sz.L n) (sz.W n) u ω) σ a ∂(PF d (sz.L n) (sz.W n) (sz.lam n)))) u

/-! ### Along the sequence (RBM2D §5 Target: transfer from `seqP` to `PF` by `seqP_map_slice`) -/

-- RBM2D `expHierPin`, second conjunct (`MLExpHier.lean:649-651`): `f = 𝔼(𝓛 - 𝒦)` is continuous on `[0,1)`.
def expHier_continuousOn_err : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ}, |E| < 2 → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
    ContinuousOn (fun u => sz.STExpErr n E u σ a) (Set.Ico 0 1)

-- RBM2D `expHierPin`, third conjunct (`MLExpHier.lean:652-653`): the drift `D = 𝔼ℰ^{LK×LK} + 𝔼ℰ^{G̃}` is continuous
-- on `[0,1)`.
def expHier_continuousOn_drift : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ}, |E| < 2 → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
    ContinuousOn (fun u => sz.STExpDrift n E u σ a) (Set.Ico 0 1)

-- RBM2D `expHierPin`, fourth conjunct (`MLExpHier.lean:654-664`): `∂_u f = Θ^{(2)}_{u,σ} f + D` on `(0,1)`.
def expHier_hasDerivAt : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ}, |E| < 2 → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
    ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun v => sz.STExpErr n E v σ a)
      (sz.STthetaOp n E u σ (fun b => sz.STExpErr n E u σ b) a + sz.STExpDrift n E u σ a) u

-- The merged pin `STExpHier` (`Step6Pins.lean:213`), proved (the premise `3 ≤ d` is not used).
def stExpHier_holds : Prop := ∀ d : ℕ, STExpHier d

end RBM.Gauss.Sizes.T2218Check

/-! ## 3. The statements of the instances T2218 compiles (`d = 3`, `sz0`, `n = 0`, `E = 1/2`) -/

namespace RBM.Gauss.Step6Inst.T2218Check

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Path Filter

-- statement of `inst_expHier_holds` (the merged `inst_expHier` with `h := stExpHier_holds 3`; `σ = (+,-)`)
example : Prop :=
  ContinuousOn (fun u => sz0.STExpErr 0 (1 / 2) u ![true, false] ![0, Pi.single 0 1]) (Set.Ico 0 1) ∧
    ContinuousOn (fun u => sz0.STExpDrift 0 (1 / 2) u ![true, false] ![0, Pi.single 0 1]) (Set.Ico 0 1) ∧
    ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun v => sz0.STExpErr 0 (1 / 2) v ![true, false] ![0, Pi.single 0 1])
      (sz0.STthetaOp 0 (1 / 2) u ![true, false] (fun b => sz0.STExpErr 0 (1 / 2) u ![true, false] b)
          ![0, Pi.single 0 1] + sz0.STExpDrift 0 (1 / 2) u ![true, false] ![0, Pi.single 0 1]) u

-- statement of `inst_expHier_pp` (the repeated sign `σ = (+,+)`, outside `HierarchyN2`/`KpmODE`)
example : Prop :=
  ContinuousOn (fun u => sz0.STExpErr 0 (1 / 2) u ![true, true] ![0, Pi.single 0 1]) (Set.Ico 0 1) ∧
    ContinuousOn (fun u => sz0.STExpDrift 0 (1 / 2) u ![true, true] ![0, Pi.single 0 1]) (Set.Ico 0 1) ∧
    ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun v => sz0.STExpErr 0 (1 / 2) v ![true, true] ![0, Pi.single 0 1])
      (sz0.STthetaOp 0 (1 / 2) u ![true, true] (fun b => sz0.STExpErr 0 (1 / 2) u ![true, true] b)
          ![0, Pi.single 0 1] + sz0.STExpDrift 0 (1 / 2) u ![true, true] ![0, Pi.single 0 1]) u

-- statement of `inst_expHier_half` (the drift identity at the interior time `u = 1/2`, `σ = (-,-)`)
example : Prop :=
  HasDerivAt (fun v => sz0.STExpErr 0 (1 / 2) v ![false, false] ![0, Pi.single 0 1])
    (sz0.STthetaOp 0 (1 / 2) (1 / 2) ![false, false] (fun b => sz0.STExpErr 0 (1 / 2) (1 / 2) ![false, false] b)
        ![0, Pi.single 0 1] + sz0.STExpDrift 0 (1 / 2) (1 / 2) ![false, false] ![0, Pi.single 0 1]) (1 / 2)

-- statement of `inst_expHier_Kloop` (`expHier_Kloop_hasDerivAt` at `sz0`, `n = 0`, `E = u = 1/2`, `σ = (+,+)`)
example : Prop :=
  HasDerivAt (fun v : ℝ => sz0.STKloop 0 (1 / 2) v ![true, true] ![0, Pi.single 0 1])
    ((((sz0.W 0 : ℕ) : ℂ) ^ 3) * ∑ c : Zd 3 (sz0.L 0), ∑ e : Zd 3 (sz0.L 0),
      sz0.STKloop 0 (1 / 2) (1 / 2) ![true, true] ![0, c] * SB 3 (sz0.L 0) (sz0.lam 0) c e *
        sz0.STKloop 0 (1 / 2) (1 / 2) ![true, true] ![e, Pi.single 0 1]) (1 / 2)

-- statement of `inst_expHier_hierarchy_two` (`expHier_hierarchy_two` at `sz0`, `n = 0`, `E = u = 1/2`, `M = 1`,
-- `σ = (-,-)`, `a = (0, 0)`)
example : Prop :=
  genMat 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (1 / 2) (1 / 2)
        (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
        (loopOf ![false, false] ![(0 : Zd 3 (sz0.L 0)), 0]) -
      deriv (fun v : ℝ => sz0.STKloop 0 (1 / 2) v ![false, false] ![(0 : Zd 3 (sz0.L 0)), 0]) (1 / 2) =
    sz0.STthetaOp 0 (1 / 2) (1 / 2) ![false, false]
        (sz0.STLKM 0 (1 / 2) (1 / 2) (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
          ![false, false]) ![0, 0] +
      sz0.STELKLKM 0 (1 / 2) (1 / 2) (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
        ![false, false] ![0, 0] +
      sz0.STEGtM 0 (1 / 2) (1 / 2) (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
        ![false, false] ![0, 0]

end RBM.Gauss.Step6Inst.T2218Check
