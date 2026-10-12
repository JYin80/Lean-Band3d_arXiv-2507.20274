/-
Release check for T2474 (dispatcher V3, Mon Oct 12 20:33 UTC 2026; DECISIONS §276).  ST T5s2 (sub-stage T): the step decomposition, the `C²`
loop bound, the hierarchy algebra, the quadratic variation and the grid drift over the carrier, in the new files
`Chain/StepDecompGen.lean` and `Chain/HierDriftGen.lean`; the band files `Induction/StepDecompN`, `LoopC2N`, `HierAlgebra`,
`QVN`, `GridDriftN`, `HierarchyN` are not edited (outside the certificate lane).
Part 1: merged names.  Part 2: the target statements as Prop values (prefix `T2474_`): conclusions content binding; carrier
classes binding (a field may be added only with a named band discharge, reported in 1a (iii)); then shapes (not binding):
the generic results, the band routes, the BA readings (T5-BA), the UBA-C1 literal.  Part 3 (G1): the public band names of the
six files, unchanged; the auditor adds `example : <statement> := <name>` for each.
Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2474-check.lean
-/
import RBM3D.Induction.StepDecompN
import RBM3D.Induction.GridDriftN
import RBM3D.Chain.GridDuhamelGen
import RBM3D.Chain.Step2Kern
import RBM3D.BA.Step2BA
import RBM3D.BA.KInduct
import RBM3D.BA.TwistGridRem2
import RBM3D.BA.TwistGridWTail

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the carrier, T8b's kernels (U-C4: no new kernel) and the generic vocabulary the targets read
#check @RBM.BA.FlowFM
#check @RBM.BA.Step2Mat
#check @RBM.BA.bandFM
#check @RBM.BA.bandStep2Mat
#check @RBM.BA.baFM
#check @RBM.BA.baStep2Mat
#check @RBM.BA.baStep2Mat_Hpath
#check @RBM.BA.baStep2Mat_KI
#check @RBM.BA.Step2Gen_uKer
#check @RBM.BA.Step2Gen_thetaKer
#check @RBM.BA.Step2Gen_ThetaN
#check @RBM.BA.Step2Gen_UN
#check @RBM.BA.Step2Kern_ThetaN_band
#check @RBM.BA.Step2Kern_thetaKer_band
#check @RBM.BA.Step2Kern_uKer_band
#check @RBM.BA.Step2Kern_UN_band
#check @RBM.BA.Step2Kern_thetaKer_BA
#check @RBM.BA.Step2Kern_uKer_BA
#check @RBM.BA.STLIMg
#check @RBM.BA.STLKIMg
#check @RBM.BA.STksimLKMg
#check @RBM.BA.STelklkMg
#check @RBM.BA.STegtMg
#check @RBM.BA.STeeMg
#check @RBM.BA.STgDriftNg
#check @RBM.BA.bandStep2_STLIM
#check @RBM.BA.bandStep2_STLKIM
#check @RBM.BA.bandStep2_STksimLKM
#check @RBM.BA.bandStep2_STelklkM
#check @RBM.BA.bandStep2_STegtM
#check @RBM.BA.bandStep2_STeeM
#check @RBM.BA.STGridRepNgL
#check @RBM.BA.STKboundgL
-- T4s1 (`Chain/GridDuhamelGen`)
#check @RBM.BA.AvecNg
#check @RBM.BA.martIncNg
#check @RBM.BA.predIncNg
#check @RBM.BA.bandStep2_martIncN
#check @RBM.BA.bandStep2_predIncN
#check @RBM.BA.bandStep2_Ugen
#check @RBM.BA.Step2Gen_USemigroup
#check @RBM.BA.step2Gen_USemigroup_band
#check @RBM.BA.StoppedAzumaNg
-- T5s1 (`Induction/LoopGenN`, generic in `m` and `g`)
#check @RBM.Ind.genMatOf
#check @RBM.Ind.genMat_eq_genMatOf
#check @RBM.Ind.loopGenNOf
#check @RBM.Ind.loopGenN
#check @RBM.Ind.stLoopGenNForm_holds
#check @RBM.Ind.hierarchyN_holds
-- loops, spectral parameter, walk, test class (targets 1-5)
#check @RBM.Gauss.ztOf
#check @RBM.Gauss.etaOf
#check @RBM.Gauss.loopFine
#check @RBM.Gauss.loopL
#check @RBM.Gauss.blockMat
#check @RBM.Gauss.loopOf
#check @RBM.Gauss.loopM_eq_loopL
#check @RBM.Gauss.gvarF
#check @RBM.Gauss.coordinateMatrix
#check @RBM.Gauss.PsiI_isHermitian
#check @RBM.Path.HermTestFun
#check @RBM.Path.PathΩ
#check @RBM.Path.pathP
#check @RBM.Path.pathH
#check @RBM.Path.filt
#check @RBM.Path.gridTime
#check @RBM.Path.gridStep
#check @RBM.Path.pathH_succ
#check @RBM.Path.pathH_isHermitian
#check @RBM.Path.isProbabilityMeasure_pathP
#check @RBM.Ind.norm_gloop_le_of_le_abs_im
-- the K-loop equation, the generator, the one-step expansion (targets 6-10)
#check @RBM.Loop.IsKLoopS
#check @RBM.Loop.IsKLoop_iff_IsKLoopS
#check @RBM.Loop.treeEqRhsS
#check @RBM.Loop.treeEqRhs_eq_treeEqRhsS
#check @RBM.Loop.KLK_isKLoop
#check @RBM.Loop.KLloopOf
#check @RBM.PropSpin
#check @RBM.sum_nnnorm_SB_row
#check @RBM.Path.genMat
#check @RBM.Path.envConst
#check @RBM.Path.condExp_loop_drift
-- BA sources of the classes (T5-BA; read here as names only)
#check @RBM.BA.BAKsol
#check @RBM.BA.BAKsol_isKLoopS
#check @RBM.BA.baKsol_two
#check @RBM.BA.TwistGridRem_envelope_word
#check @RBM.BA.baTwistGridRem_holds
#check @RBM.BA.TwistGridWTail_norm_twU_sub_one_le
#check @RBM.BA.TwistGridWTail_hermTestFun
#check @RBM.BA.twU_eq_uKer
#check @RBM.BA.BATwistHier
#check @RBM.BA.BAm_norm_le_one
#check @RBM.BA.BAReal
#check @RBM.BA.BAmF
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs

/-! ## Part 2: the target statements (content binding), the classes, and shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 1, class `StepDecompGen_LoopForm`** (binding): the loops of the carrier are the loops at the spectral parameter
`ztOf (Cm.m n) (E n) u` (`Loop/GLoopFlow.lean:55`), with `η = etaOf (Cm.m n) u` and `0 < Im m`.  It replaces `|E| < 2`,
`zt E`, `etaT E` of the six band files (band: `m = mE E`, every field definitional; BA: `baStep2Mat`, `Step2BA:57-62`). -/
def T2474_LoopForm {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (E : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 0 < (Cm.m n).im ∧
    (∀ (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (k : ℕ)
        (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Cm.LM n u H σ a = loopFine d (sz.L n) (sz.W n) H (ztOf (Cm.m n) (E n) u) σ a) ∧
    (∀ (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
        (I : LoopIdx (Zd d (sz.L n))),
      Cm.LIM n u H I =
        loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) H) (ztOf (Cm.m n) (E n) u) I) ∧
    (∀ u : ℝ, Cm.eta n u = etaOf (Cm.m n) u)

/-- **Target 1, class `StepDecompGen_WalkForm`** (binding): the walk of the carrier is the band walk of the model at the
coupling `lam'` shifted with a Hermitian `Ψ n` (the shape of `baStep2Mat`, `Step2BA:68-72`; band: `lam' = sz.lam`, `Ψ = 0`). -/
def T2474_WalkForm {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (lam' : ℕ → ℝ)
    (Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : Prop :=
  (∀ n, (Ψ n).IsHermitian) ∧
    Cm.Pp = (show Measure (PathΩ sz) from pathP (sz.withLam lam')) ∧
    ∀ (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz),
      Cm.Hpath s t K n k ω = Ψ n +
        (show Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ from
          pathH (sz.withLam lam') s t K n k ω)

open scoped Matrix.Norms.L2Operator in
/-- **Target 2** (content binding): the pin `HermTestFunLoopN` (`LoopC2N.lean:453`) with `ztOf m E u`, `etaOf m u` and
`0 < m.im` in place of `zt E u`, `etaT E u` and `|E| < 2` (`0 ≤ u` dropped: unused, `LoopC2N:470`). -/
def T2474_HermLoopOf : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (k n : ℕ) (m : ℂ) (E u : ℝ), 0 < m.im → u < 1 →
    ∀ (σ : Fin k → Bool) (b : Fin k → Zd d (sz.L n)),
      HermTestFun sz n (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
        loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) (ztOf m E u) (loopOf σ b)) ∧
      ∀ M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
        y.IsHermitian →
        ‖fderiv ℝ (fderiv ℝ (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
            loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) (ztOf m E u)
              (loopOf σ b))) M y y‖ ≤
          ((k * (k + 1) : ℕ) : ℝ) * (Sizes.size sz n : ℝ) * (etaOf m u)⁻¹ ^ (k + 2) * ‖y‖ ^ 2

/-- **Target 3** (content binding): the pin `QVPropagatedN` (`QVN.lean:799`) over the carrier: the loop derivative is
`dirDerivN` of `Cm.LM`, the proxy is `STeeMg`, the coordinate variance is `gvarF` at the walk coupling `g n`. -/
def T2474_QVg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (g : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (u : ℝ), 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
      ∀ (k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (κ : (Fin k → Zd d (sz.L n)) → ℂ),
        ∑ c : CoordF d (sz.L n) (sz.W n), (gvarF d (sz.L n) (sz.W n) (g n) c : ℝ) *
            ‖∑ b : Fin k → Zd d (sz.L n), κ b *
              RBM.Ind.dirDerivN (fun H => Cm.LM n u H σ b) M (coordinateMatrix d (sz.L n) (sz.W n) c)‖ ^ 2 ≤
          (k : ℝ) * (∑ b : Fin k → Zd d (sz.L n), ∑ b' : Fin k → Zd d (sz.L n),
            κ b * (starRingEnd ℂ) (κ b') * STeeMg Cm n u M σ b b').re

/-- **Target 4, `SubGaussFormNg`** (content binding): `SubGaussFormN` (`StepDecompN.lean:206`) with `Cm.Pp` for `pathP sz`. -/
def T2474_SubGaussFormNg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) [IsProbabilityMeasure Cm.Pp] (j : ℕ)
    (τ : PathΩ sz → ℕ) (F : PathΩ sz → ℂ) (c : ℝ≥0) : Prop :=
  HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
    (fun ω => ({ω' | j < τ ω'}.indicator F ω).re) c Cm.Pp ∧
  HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
    (fun ω => ({ω' | j < τ ω'}.indicator F ω).im) c Cm.Pp

/-- **Target 4, `SubGaussStopNg`** (content binding): `SubGaussStopN` (`StepDecompN.lean:215`) with `Step2Gen_UN` for `Ugen`
(U-C4). -/
def T2474_SubGaussStopNg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) [IsProbabilityMeasure Cm.Pp] {n k : ℕ}
    (σ : Fin k → Bool) (u : ℕ → ℝ) (τ : PathΩ sz → ℕ) (Z : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ) (m : ℕ)
    (a : Fin k → Zd d (sz.L n)) (j : ℕ) (c : ℝ≥0) : Prop :=
  T2474_SubGaussFormNg Cm j τ (fun ω' => Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) (Z j ω') a) c

/-- **Target 6, class `HierDriftGen_KLoop`** (binding): `𝒦` of the carrier solves the convolution tree equations with the
carrier kernel `Cm.S n` on `[0, 1)` (the merged `IsKLoopS`, `Loop/KLTree.lean:828`; band `KLK_isKLoop` through
`IsKLoop_iff_IsKLoopS`; BA `BAKsol_isKLoopS` at `S = 1`). -/
def T2474_KLoop {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (n : ℕ) : Prop :=
  ∃ M0 : LoopIdx (Zd d (sz.L n)) → ℂ,
    IsKLoopS d (sz.L n) (sz.W n) (Cm.S n) (PropSpin (Cm.m n)) M0 (Set.Ico (0 : ℝ) 1) (Cm.KI n)

/-- **Target 6, class `HierDriftGen_KTwo`** (binding; class (t), C6): the `l = 2` coupling of `𝒦_u` is `Θ^{(k)}_{u,σ}`
(`couplingLen_two_Kval_eq_thetaOp`, `HierAlgebra.lean:620`, read through the private `HierAlgebra_couplingLen_eq_ksimLK`
`:714` and `Step2Kern_ThetaN_band`; BA `baKsol_two` with `Step2Kern_thetaKer_BA`). -/
def T2474_KTwo {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (n : ℕ) : Prop :=
  ∀ u ∈ Set.Ico (0 : ℝ) 1, ∀ (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (k : ℕ),
    2 ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      STksimLKMg Cm n u H 2 (KLloopOf d (sz.L n) σ a) =
        Step2Gen_ThetaN Cm.toFlowFM n σ u (fun b => STLKIMg Cm n u H (KLloopOf d (sz.L n) σ b)) a

/-- **Target 6, `loopDrift_sub_K_deriv_ng`** (content binding): `loopDrift_sub_K_deriv_n` (`HierAlgebra.lean:729`) over the
carrier; the pair term is `STllPairNg = treeEqRhsS (Cm.S n) (STLIMg …)`, the right side is `STgDriftNg`'s at `H = M`. -/
def T2474_LoopDrift {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (n : ℕ) : Prop :=
  ∀ u ∈ Set.Ico (0 : ℝ) 1, ∀ (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (k : ℕ),
    2 ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      (treeEqRhsS d (sz.L n) (sz.W n) (Cm.S n) (STLIMg Cm n u M) (KLloopOf d (sz.L n) σ a) +
            STegtMg Cm n u M (KLloopOf d (sz.L n) σ a)) -
          deriv (fun v : ℝ => Cm.KI n v (KLloopOf d (sz.L n) σ a)) u =
        Step2Gen_ThetaN Cm.toFlowFM n σ u (fun b => STLKIMg Cm n u M (KLloopOf d (sz.L n) σ b)) a +
          ∑ l ∈ Finset.Icc 3 k, STksimLKMg Cm n u M l (KLloopOf d (sz.L n) σ a) +
          STelklkMg Cm n u M (KLloopOf d (sz.L n) σ a) + STegtMg Cm n u M (KLloopOf d (sz.L n) σ a)

/-- **Target 7** (content binding): `HierarchyN` (`HierarchyN.lean:56`) over the carrier, the generator being T5s1's
`genMatOf` (`LoopGenN.lean:554`) at the walk coupling `g n`, the one-loop value `Cm.m n` and the energy `E n`. -/
def T2474_HierarchyNg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (E g : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (u : ℝ), 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
      ∀ (k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
        RBM.Ind.genMatOf d (sz.L n) (sz.W n) (g n) (Cm.m n) (E n) u M (KLloopOf d (sz.L n) σ a) -
            deriv (fun v : ℝ => Cm.KI n v (KLloopOf d (sz.L n) σ a)) u =
          Step2Gen_ThetaN Cm.toFlowFM n σ u (fun b => STLKIMg Cm n u M (KLloopOf d (sz.L n) σ b)) a +
            ∑ l ∈ Finset.Icc 3 k, STksimLKMg Cm n u M l (KLloopOf d (sz.L n) σ a) +
            STelklkMg Cm n u M (KLloopOf d (sz.L n) σ a) + STegtMg Cm n u M (KLloopOf d (sz.L n) σ a)

/-- **Target 8, `GridDriftNg`** (content binding): the pin `GridDriftN` (`GridDriftN.lean:663`) over `Step2Mat`, without the
premise `∀ n, |E n| < 2`; the error is `stepErrNg` = `stepErrN` (`:289`, with `envConst`, `Path/OneStep.lean:78`, unfolded)
with `etaT (E n)` read as `Cm.eta n` (band: definitional). -/
def T2474_GridDriftNg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
  ∀ (n j : ℕ), j < K n → ∀ (k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (Bk : ℝ), 0 ≤ Bk →
    (∀ w ∈ Set.Icc (0 : ℝ) (gridTime s t K n (j + 1)), ∀ J : LoopIdx (Zd d (sz.L n)), J.WF →
      2 ≤ J.length → J.length ≤ k → ‖Cm.KI n w J‖ ≤ Bk) →
    ∀ᵐ ω ∂(Cm.Pp), ∀ a : Fin k → Zd d (sz.L n),
      ‖predIncNg Cm s t K n j σ ω a - (gridStep s t K n : ℂ) *
          (∑ l ∈ Finset.Icc 3 k, STksimLKMg Cm n (gridTime s t K n j)
              (Cm.Hpath s t K n j ω) l (KLloopOf d (sz.L n) σ a) +
            STelklkMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a) +
            STegtMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a))‖ ≤
        16 * ((k : ℝ) + 3) ^ 4 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 4 *
            (1 + (Cm.eta n (gridTime s t K n (j + 1)))⁻¹) ^ (k + 4) * gridStep s t K n ^ ((3 : ℝ) / 2) +
          RBM.Ind.kStepC d (sz.L n) (sz.W n) k Bk * gridStep s t K n ^ 2 +
          RBM.Ind.uStepC k (gridStep s t K n) (gridTime s t K n (j + 1)) *
            ((Cm.eta n (gridTime s t K n j))⁻¹ ^ k * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (k - 1) + Bk)

/-- **Target 9, class `HierDriftGen_Expand`** (binding): one grid step of a loop observable along the carrier walk, the merged
`condExp_loop_drift` (`Path/LoopStep.lean:310`) with the generator written as `STllPairNg + STegtMg` (`loopGenN`) and
`envConst` unfolded with `Cm.eta`.  Band: `condExp_loop_drift` + `loopGenN`; BA: TL's word envelope
`TwistGridRem_envelope_word` (`BA/TwistGridRem.lean:572`) on the walk of `TwistGridRem2` (T5-BA). -/
def T2474_Expand {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) : Prop :=
  0 ≤ s n → s n ≤ t n → t n < 1 → K n ≠ 0 →
  ∀ j : ℕ, j < K n → ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → 2 ≤ I.length →
    ∀ᵐ ω ∂(Cm.Pp),
      ‖MeasureTheory.condExp (filt sz j) Cm.Pp
            (fun ω' => STLIMg Cm n (gridTime s t K n (j + 1)) (Cm.Hpath s t K n (j + 1) ω') I) ω -
          STLIMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) I -
          (gridStep s t K n : ℂ) *
            (treeEqRhsS d (sz.L n) (sz.W n) (Cm.S n)
                (STLIMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω)) I +
              STegtMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) I)‖ ≤
        16 * ((I.length : ℝ) + 3) ^ 4 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 4 *
          (1 + (Cm.eta n (gridTime s t K n (j + 1)))⁻¹) ^ (I.length + 4) * gridStep s t K n ^ ((3 : ℝ) / 2)

/-- **Target 9, class `HierDriftGen_UStep`** (binding): the row bounds of one step of the carrier kernel.  The first field is
T2471's K3 verbatim (`docs/tickets/checks/T2471-check.lean:215-216`); the second is the order-2 bound of the private
`gdn_row_UG` (`GridDriftN.lean:428`), the generator being `Step2Gen_thetaKer` (band: `Step2Kern_thetaKer_band`). -/
def T2474_UStep {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) : Prop :=
  (∀ (σ σ' : Bool) (s t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
    ∑ b, ‖Step2Gen_uKer C n σ σ' s t a b - (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b‖ ≤ |t - s| * (1 - t)⁻¹) ∧
  (∀ (σ σ' : Bool) (u Δ : ℝ), 0 ≤ u → 0 ≤ Δ → u + Δ < 1 → ∀ a : Zd d (sz.L n),
    ∑ b, ‖Step2Gen_uKer C n σ σ' u (u + Δ) a b - (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b -
        (Δ : ℂ) * Step2Gen_thetaKer C n σ σ' u a b‖ ≤ Δ ^ 2 * (1 - (u + Δ))⁻¹ ^ 2)

/-! ### Shapes (not binding): the generic results, the band routes, the BA readings -/

/-- Target 2, band route (`recovers` direction, as `LoopGenN.lean:665`). -/
example : Prop := T2474_HermLoopOf → ∀ {d : ℕ} (sz : Sizes d), RBM.Ind.HermTestFunLoopN sz

/-- Target 3, the generic result and its band route (`g = sz.lam`, `m = mE E`). -/
example : Prop := ∀ {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (E g : ℕ → ℝ),
  T2474_LoopForm Cm E → (∀ n, Cm.S n = SB d (sz.L n) (g n)) → T2474_QVg Cm g
example : Prop := ∀ d : ℕ,
  (∀ (sz : Sizes d) (E : ℕ → ℝ), (∀ n, |E n| < 2) → T2474_QVg (bandStep2Mat sz E) sz.lam) → RBM.Ind.QVPropagatedN d

/-- Target 4, the bodies of `ZvecNg` (the `dirDerivN` term) and `YvecNg` (the bracket): `martIncNg = ZvecNg + YvecNg`. -/
example : Prop :=
  ∀ {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j k : ℕ) (σ : Fin k → Bool)
    (ω : PathΩ sz) (b : Fin k → Zd d (sz.L n)),
    martIncNg Cm s t K n j σ ω b =
      RBM.Ind.dirDerivN (fun H => Cm.LM n (gridTime s t K n (j + 1)) H σ b) (Cm.Hpath s t K n j ω)
          (Cm.Hpath s t K n (j + 1) ω - Cm.Hpath s t K n j ω) +
        (martIncNg Cm s t K n j σ ω b -
          RBM.Ind.dirDerivN (fun H => Cm.LM n (gridTime s t K n (j + 1)) H σ b) (Cm.Hpath s t K n j ω)
            (Cm.Hpath s t K n (j + 1) ω - Cm.Hpath s t K n j ω))

/-- Target 4, the band bridge of `ZvecN` (proved: `pathH_succ` and scaling of `deriv`). -/
example : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j k : ℕ) (σ : Fin k → Bool) (ω : PathΩ sz)
    (b : Fin k → Zd d (sz.L n)),
    RBM.Ind.ZvecN sz E s t K n j σ ω b =
      RBM.Ind.dirDerivN (fun H => (bandStep2Mat sz E).LM n (gridTime s t K n (j + 1)) H σ b)
        ((bandStep2Mat sz E).Hpath s t K n j ω)
        ((bandStep2Mat sz E).Hpath s t K n (j + 1) ω - (bandStep2Mat sz E).Hpath s t K n j ω)

/-- Target 6, the generic result. -/
example : Prop := ∀ {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (n : ℕ),
  T2474_KLoop Cm n → T2474_KTwo Cm n → T2474_LoopDrift Cm n

/-- Target 7, the generic result (from T5s1's `loopGenNOf`) and its band route. -/
example : Prop := ∀ {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (E g : ℕ → ℝ),
  T2474_LoopForm Cm E → (∀ n, Cm.S n = SB d (sz.L n) (g n)) → (∀ n, T2474_KLoop Cm n) →
    (∀ n, T2474_KTwo Cm n) → T2474_HierarchyNg Cm E g
example : Prop := ∀ d : ℕ,
  (∀ (sz : Sizes d) (E : ℕ → ℝ), (∀ n, |E n| < 2) → T2474_HierarchyNg (bandStep2Mat sz E) E sz.lam) →
    RBM.Ind.HierarchyN d

/-- Target 9 (b), the generic result `gridDriftNg` (`gridDriftNg_at`: the same with every class at the one index `n`). -/
example : Prop := ∀ {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (E lam' : ℕ → ℝ)
    (Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (s t : ℕ → ℝ) (K : ℕ → ℕ),
  T2474_LoopForm Cm E → T2474_WalkForm Cm lam' Ψ → (∀ n, T2474_Expand Cm s t K n) →
    (∀ n, T2474_KLoop Cm n) → (∀ n, T2474_KTwo Cm n) → (∀ n, T2474_UStep Cm.toFlowFM n) →
    (∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b, ‖Cm.S n a b‖ ≤ 1) → T2474_GridDriftNg Cm s t K

/-- Target 8, band route: the generic pin at `bandStep2Mat` gives the merged band pin. -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ),
  ((∀ n, |E n| < 2) → T2474_GridDriftNg (bandStep2Mat sz E) s t K) → RBM.Ind.GridDriftN sz E s t K

/-- Target 10, `exists_norm_KI_le_wing` (`exists_norm_Kcal_le_win`, `GridDriftN.lean:1098`, over the carrier). -/
example : Prop := ∀ {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ],
  sz.SizeTendsto → STKboundgL Cm.toFlowFM μ →
  (∀ (n : ℕ) (w : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
    Cm.KI n w (KLloopOf d (sz.L n) σ a) = Cm.K n w σ a) →
  (∀ (n : ℕ) (v : ℝ), 0 ≤ v → v < 1 → 0 < Cm.eta n v ∧ Cm.eta n v ≤ 1 - v) →
  ∀ (v : ℕ → ℝ), (∀ n, 0 ≤ v n) → (∀ n, v n < 1) → ∀ (m : ℕ) (τ : ℝ), 0 < τ →
    ∀ᶠ n in atTop, ∀ w ∈ Set.Icc (0 : ℝ) (v n), ∀ J : LoopIdx (Zd d (sz.L n)), J.WF →
      2 ≤ J.length → J.length ≤ m →
        ‖Cm.KI n w J‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ((Cm.eta n (v n))⁻¹) ^ m

/-- Target 10, `HierDriftGen_exists_envelope` (`GridDriftN_exists_envelope`, `GridDriftN.lean:950`, over the carrier). -/
example : Prop := ∀ {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (n : ℕ), T2474_KLoop Cm n →
  ∀ v : ℝ, 0 ≤ v → v < 1 → ∀ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ w ∈ Set.Icc (0 : ℝ) v, ∀ J : LoopIdx (Zd d (sz.L n)),
    J.WF → 2 ≤ J.length → J.length ≤ k → ‖Cm.KI n w J‖ ≤ B

/-- Target 1, band instances (this row). -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ), (∀ n, |E n| < 2) → T2474_LoopForm (bandStep2Mat sz E) E
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ), T2474_WalkForm (bandStep2Mat sz E) sz.lam (fun _ => 0)

/-- BA readings, statement level (T5-BA, not this row): the classes at `baStep2Mat`. -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ), (∀ n, 0 < (BAmF sz lam0 E n).im) →
  T2474_LoopForm (baStep2Mat sz lam0 E) E
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ),
  T2474_WalkForm (baStep2Mat sz lam0 E) (fun _ => 0) (fun n => ((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n))
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (κ : ℝ), 0 < κ → 0 < lam0 n →
  BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n) →
    T2474_KLoop (baStep2Mat sz lam0 E) n ∧ T2474_KTwo (baStep2Mat sz lam0 E) n ∧
      T2474_UStep (baFM sz lam0 E) n
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ),
  T2474_QVg (baStep2Mat sz lam0 E) (fun _ => 0) ∧ T2474_HierarchyNg (baStep2Mat sz lam0 E) E (fun _ => 0)

/-- BA reading of target 8 along the flow (statement level; T5-BA through target 9 (b)). -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
  ∀ (s t : ℕ → ℝ) (K : ℕ → ℕ), (∀ n, t n ≤ BAflowT0 sz z n) →
    T2474_GridDriftNg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s t K

/-- UBA-C1 as amended (DECISIONS §273 (1)): the R1 literal, the only admissible comparison text if a generic statement here
ever crosses size level and kernel level (not expected). -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (gK : ℕ → ℝ) (A : ℝ),
  ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2

end RBM.BA

end

/-! ## Part 3 (G1): the public band names of the six files (not edited; statements unchanged) -/
-- `Induction/StepDecompN.lean` (model-free per-step layer: reused as named)
#check @RBM.Ind.AbCN
#check @RBM.Ind.stepZCN_re
#check @RBM.Ind.stepZCN_im
#check @RBM.Ind.stepZCN
#check @RBM.Ind.stepXiCN
#check @RBM.Ind.stepYCN
#check @RBM.Ind.StepDecompCN_Stmt
#check @RBM.Ind.stepDecompCN
#check @RBM.Ind.stepDecompCN_Z_subG
#check @RBM.Ind.integrable_stepZCN_re_of_hermTestFun
#check @RBM.Ind.integrable_stepZCN_im_of_hermTestFun
#check @RBM.Ind.stepDecompCN_Y_sq
#check @RBM.Ind.dirDerivN
-- `Induction/StepDecompN.lean` (loop layer: targets 4, 5)
#check @RBM.Ind.loopFamN
#check @RBM.Ind.ZfamN
#check @RBM.Ind.ZvecN
#check @RBM.Ind.YvecN
#check @RBM.Ind.stoppedEdgeN
#check @RBM.Ind.SubGaussFormN
#check @RBM.Ind.SubGaussStopN
#check @RBM.Ind.ZvecN_eq_stepZCN
#check @RBM.Ind.Ugen_stepZCN
#check @RBM.Ind.martIncN_eq_stepXiCN
#check @RBM.Ind.YvecN_eq_stepYCN
#check @RBM.Ind.Ugen_stepYCN
#check @RBM.Ind.StepDecompN_subGaussStopN_zvecN
-- `Induction/LoopC2N.lean` (target 2)
#check @RBM.Ind.HermTestFunLoopN
#check @RBM.Ind.hermTestFunLoopN
-- `Induction/QVN.lean` (target 3)
#check @RBM.Ind.loopDerivN
#check @RBM.Ind.QVPropagatedN
#check @RBM.Ind.qvPropagatedN
-- `Induction/HierAlgebra.lean` (target 6)
#check @RBM.Ind.primBil
#check @RBM.Ind.primBil_self
#check @RBM.Ind.primBil_add_left
#check @RBM.Ind.primBil_add_right
#check @RBM.Ind.primBil_add_add
#check @RBM.Ind.primRhs_sub
#check @RBM.Ind.primBilLen
#check @RBM.Ind.primBilLenR
#check @RBM.Ind.couplingLen
#check @RBM.Ind.sum_primBilLen
#check @RBM.Ind.sum_primBilLenR
#check @RBM.Ind.sum_couplingLen
#check @RBM.Ind.couplingLen_eq_zero_outside
#check @RBM.Ind.primRhs_split
#check @RBM.Ind.norm_primBil_le
#check @RBM.Ind.couplingLen_two_Kval_eq_thetaOp
#check @RBM.Gauss.Sizes.STllPairN
#check @RBM.Gauss.Sizes.STllPairN_eq_treeEqRhs
#check @RBM.Ind.loopDrift_sub_K_deriv_n
-- `Induction/HierarchyN.lean` (target 7)
#check @RBM.Ind.STLoopGenNForm
#check @RBM.Ind.HierarchyN
#check @RBM.Ind.hierarchyN_of_loopGenN
#check @RBM.Ind.hierarchyN_two
#check @RBM.Ind.loopGenNForm_two_of_loopGenN2
-- `Induction/GridDriftN.lean` (targets 8-10)
#check @RBM.Ind.kStepC
#check @RBM.Ind.uStepC
#check @RBM.Ind.stepErrN
#check @RBM.Ind.GridDriftN
#check @RBM.Ind.gridDriftN_at
#check @RBM.Ind.gridDriftN
#check @RBM.Ind.GridDriftN_exists_envelope
#check @RBM.Ind.exists_norm_Kcal_le_win
