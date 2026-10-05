/-
Release check for T2196 (dispatcher V1, Mon Oct  5 15:58 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §20, §29, §57 (2)).
UN-25 (bulk universality, GUE phase, first ticket): the auxiliary carrier and the row-chaos (LDE) layer, port of
RBM2D `Universality/GUEPhase/AuxCarrier.lean` at `c9a24cf`, written model-generically (DECISIONS §57 (2)): any
variance family `v`, the profile coupling `g` (instantiated by `UNKind.lamV`) and a deterministic Hermitian shift `A`
(instantiated by `UNModelC.mean`).
Section 1: the merged names the new file builds on, and the Mathlib names of the route.
Section 2: the pinned statements as `def … : Prop` in the temporary namespace `RBM.Univ.T2196Check`.  The library
states each as a theorem in `RBM.Univ` whose type unfolds to exactly this body (only `Type` → `Type*` in the index
binder of `T2196_chaos_tail`, `T2196_aux_lin_tail` may differ); `T2196_QuadTailAt` is the unfolded form of the
library's `gaussLaw d L W v {s | lam * quadVqS d L W v A z i s < ‖quadQS d L W v A z i s‖ ^ 2} ≤ …`.
Statement and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2196-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- MD-1 = T2006 (0a873f1): `RBM3D/Defs/Sizes.lean`
#check @RBM.Gauss.Idx
#check @RBM.Gauss.blk
#check @RBM.Gauss.split
#check @RBM.Gauss.card_Idx
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.neZeroL
#check @RBM.Gauss.Sizes.neZeroW
#check @RBM.Gauss.Sizes.card_Idx
#check @RBM.Gauss.Sizes.withLam
#check @RBM.Gauss.SizesInst.sz0
-- MD-1 = T2006 (0a873f1): `RBM3D/Gauss/FineModel.lean`
#check @RBM.Gauss.svarF
#check @RBM.Gauss.svarF_nonneg
#check @RBM.Gauss.svarF_comm
#check @RBM.Gauss.svarF_diag
#check @RBM.Gauss.idxKey
#check @RBM.Gauss.idxKey_injective
#check @RBM.Gauss.CoordF
#check @RBM.Gauss.Ω
#check @RBM.Gauss.gvarF
#check @RBM.Gauss.PF
#check @RBM.Gauss.isProbabilityMeasure_PF
#check @RBM.Gauss.Xentry
#check @RBM.Gauss.Xmat
#check @RBM.Gauss.Xentry_swap
#check @RBM.Gauss.Xmat_isHermitian
#check @RBM.Gauss.Xmat_add
#check @RBM.Gauss.measurable_Xentry
#check @RBM.Gauss.continuous_Xmat
#check @RBM.Gauss.Sizes.SeqCoord
#check @RBM.Gauss.Sizes.SeqΩ
#check @RBM.Gauss.Sizes.seqGvar
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.isProbabilityMeasure_seqP
-- the block profile: `RBM3D/Defs/Block.lean` (a722f63), `RBM3D/Propagator/Props4.lean` (892334b)
#check @RBM.sbKernelR
#check @RBM.sum_sbKernelR
#check @RBM.SBR
-- S1-10 = T2029 (890a89f): `RBM3D/Green/EntryCore.lean`
#check @RBM.green
#check @RBM.Green.minorMat
-- S1-12 = T2031 (cca94be): `RBM3D/Green/LDEQuad.lean`
#check @RBM.Green.GaussIBP
#check @RBM.Green.RowChaos
#check @RBM.Green.RowChaos.sg
#check @RBM.Green.RowChaos.chaos
-- S1-13 = T2044 (84e54a8): `RBM3D/Green/LDEQuadMom.lean`
#check @RBM.Green.RowChaos.mom
#check @RBM.Green.RowChaos.integrable_norm_pow
#check @RBM.Green.RowChaos.Vq
-- S1-14 = T2052 (bc637ce): `RBM3D/Green/LDEQuadT.lean`
#check @RBM.Green.RowChaos.Vq_nonneg
#check @RBM.Green.RowChaos.integrable_Vq_pow
#check @RBM.Green.RowChaos.momVpow
#check @RBM.Green.RowChaos.mom_le_momVpow
-- S1-11 = T2038 (cace419): `RBM3D/Green/RowIndep.lean` (the seq-level row coordinates; templates)
#check @RBM.Green.rowCoord
#check @RBM.Green.rowSign
-- S1-19 = T2088 (3b8c687): `RBM3D/Green/IBPPoly.lean` (the band instance: template of §§3-4)
#check @RBM.Green.gaussIBP
#check @RBM.Green.minorRes
#check @RBM.Green.norm_minorRes_le
#check @RBM.Green.continuous_minorRes
#check @RBM.Green.modelChaos
#check @RBM.Green.modelChaosEps
#check @RBM.Green.hwConst
#check @RBM.Green.meas_lt_normSq_chaos_le_eps
#check @RBM.Green.meas_lt_normSq_chaos_le
-- S1-23 = T2091 (382b6d9): `RBM3D/Green/IBP.lean`
#check @RBM.Green.IBP_sum_svarF_row
-- resolvent and norms: `Loop/GLoopFlow` (868b3b4), `Gauss/FlowCalculus` (6f99812), `Induction/Split` (aa42e43),
-- `Induction/ConArgDet` (bbd22a5), `Gauss/Domination` (1c2e756)
#check @RBM.Gauss.Gres
#check @RBM.Gauss.continuous_green_of_isHermitian
#check @RBM.Gauss.norm_Gsig_le_inv_eta
#check @RBM.Ind.norm_apply_le_l2_opNorm
#check @RBM.Ind.Gres_eq_green_zSig
#check @RBM.Gauss.meas_gt_le_of_moment
-- UN-01 = T2174 (f8ad4b4): `RBM3D/Universality/Pins.lean`
#check @RBM.Univ.gueVar
#check @RBM.Univ.gueP
#check @RBM.Univ.isProbabilityMeasure_gueP
#check @RBM.Univ.UNModel
#check @RBM.Univ.UNModel.band
#check @RBM.Univ.UNModel.ba
-- UN-02a = T2177 (a52eb85): `RBM3D/Universality/OU.lean`
#check @RBM.Univ.ouVar
#check @RBM.Univ.ouSample_law
-- UN-01b = T2187 (fdbb6f0): `RBM3D/Universality/PinsK.lean`
#check @RBM.Univ.UNModelC
#check @RBM.Univ.UNModelC.mean
#check @RBM.Univ.UNModelC.mean_herm
#check @RBM.Univ.UNModel.toC
#check @RBM.Univ.UNKind
#check @RBM.Univ.UNKind.M
#check @RBM.Univ.UNKind.lamV
#check @RBM.Univ.UNKind.band
-- Mathlib names of the route
#check @MeasureTheory.Measure.infinitePi
#check @MeasureTheory.Measure.infinitePi_map_pi
#check @MeasureTheory.Measure.eq_infinitePi
#check @MeasureTheory.Measure.infinitePi_pi
#check @ProbabilityTheory.gaussianReal
#check @ProbabilityTheory.gaussianReal_map_const_mul
#check @MeasureTheory.tendsto_measure_iUnion_atTop
#check @Matrix.IsHermitian.submatrix
#check @Matrix.IsHermitian.add

/-! ## 2. Pinned statements -/

set_option linter.unusedVariables false

noncomputable section

namespace RBM.Univ.T2196Check

open MeasureTheory ProbabilityTheory Filter Matrix
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
open scoped NNReal ENNReal

/-- Target 2 (`svarF_pos_of_block_eq`): the band variance is positive on every pair of points of one block, for every
coupling `g` (`sbKernelR 0 = (1 + 2 d g²)⁻¹ > 0`).  The `d ≥ 3` replacement of the `sbSupport` step of RBM2D
`svar_aux_pos` (`AuxCarrier.lean:127`). -/
def T2196_svarF_pos_of_block_eq : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) (i j : Idx d L W),
    (split d L W i).1 = (split d L W j).1 → 0 < svarF d L W g i j

/-- Target 3 (`exists_seqP_map_eq_gaussLaw`): every variance family on one size is realised by a continuous map
from a sequence carrier (the auxiliary carrier `auxSizes d`, `auxT`; RBM2D `auxT_law`, `AuxCarrier.lean:203`). -/
def T2196_exists_seqP_map_eq_gaussLaw : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (v : CoordF d L W → ℝ≥0),
    ∃ (sz : Sizes d) (T : Sizes.SeqΩ sz → Ω d L W), Continuous T ∧
      (Sizes.seqP sz).map T = Measure.infinitePi (fun c : CoordF d L W => gaussianReal 0 (v c))

/-- Target 4 (`sum_Smix_row`): the mixture profile `S_u = a S(g) + b N⁻¹` has row sums `a + b`, `N = (W L)^d`
(RBM2D `sum_Smix_row`, `AuxCarrier.lean:284`, with `(W L)^2 ↦ (W L)^d` and the coupling `g`). -/
def T2196_sum_Smix_row : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g a b : ℝ) (i : Idx d L W),
    ∑ j : Idx d L W, (a * svarF d L W g i j + b / (((W * L) ^ d : ℕ) : ℝ)) = a + b

/-- Target 5 (`chaos_tail`): the Hanson–Wright tail for an arbitrary merged row chaos with its random control
(RBM2D `chaos_tail`, `AuxCarrier.lean:472`; the band instance is the merged `meas_lt_normSq_chaos_le`). -/
def T2196_chaos_tail : Prop :=
  ∀ {d : ℕ} {sz : Sizes d} {κ : Type} [Fintype κ] [DecidableEq κ] (C : RBM.Green.RowChaos sz κ)
    {lam : ℝ}, 0 < lam → ∀ q : ℕ,
      (Sizes.seqP sz) {ω | lam * C.Vq ω < ‖C.chaos ω‖ ^ 2} ≤
        ENNReal.ofReal (RBM.Green.hwConst q / lam ^ (q + 1))

/-- The quadratic large deviation estimate (4.7) at fixed data, with merged names only.  Under the Gaussian law with
coordinate variances `v`, for `X = Xmat s` and `G = (((A + X)^{(i)}) - z)⁻¹` (minor of the **shifted** matrix),
`P(λ ∑_{k,l} σ_ik |G_kl|² σ_il < |∑_{k,l} X_ik G_kl X_li − ∑_k σ_ik G_kk|²) ≤ A_q / λ^{q+1}`,
`σ_ik = E|X_ik|² = 2 v(rowCoordF i k true)`.  This is the unfolded type of the library's
`gaussLaw d L W v {s | lam * quadVqS d L W v A z i s < ‖quadQS d L W v A z i s‖ ^ 2} ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1))`
(RBM2D `quadVqS` `:782`, `quadQS` `:789`, at `A = 0`). -/
def T2196_QuadTailAt (d L W : ℕ) [NeZero L] [NeZero W] (v : CoordF d L W → ℝ≥0)
    (A : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) (i : Idx d L W) (lam : ℝ) (q : ℕ) : Prop :=
  Measure.infinitePi (fun c : CoordF d L W => gaussianReal 0 (v c))
      {s : Ω d L W | lam * (∑ k : {a : Idx d L W // a ≠ i}, ∑ l : {a : Idx d L W // a ≠ i},
          (2 * (v (if idxKey d L W i < idxKey d L W k.1 then (i, k.1, true) else (k.1, i, true)) : ℝ)) *
            ‖green ((A + Xmat d L W s).submatrix Subtype.val Subtype.val) z k l‖ ^ 2 *
            (2 * (v (if idxKey d L W i < idxKey d L W l.1 then (i, l.1, true) else (l.1, i, true)) : ℝ))) <
        ‖(∑ k : {a : Idx d L W // a ≠ i}, ∑ l : {a : Idx d L W // a ≠ i},
            Xmat d L W s i k.1 * green ((A + Xmat d L W s).submatrix Subtype.val Subtype.val) z k l *
              Xmat d L W s l.1 i) -
          ∑ k : {a : Idx d L W // a ≠ i},
            (((2 * (v (if idxKey d L W i < idxKey d L W k.1 then (i, k.1, true) else (k.1, i, true)) : ℝ)) : ℝ) : ℂ) *
              green ((A + Xmat d L W s).submatrix Subtype.val Subtype.val) z k k‖ ^ 2}
    ≤ ENNReal.ofReal (RBM.Green.hwConst q / lam ^ (q + 1))

/-- Target 6 (`gaussLaw_quad_tail`): (4.7) for every tag-free variance family and every deterministic Hermitian shift
(RBM2D `gaussLaw_quad_tail`, `AuxCarrier.lean:836`, which is the case `A = 0`). -/
def T2196_gaussLaw_quad_tail : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (v : CoordF d L W → ℝ≥0),
    (∀ i j : Idx d L W, v (i, j, true) = v (i, j, false)) →
    ∀ A : Matrix (Idx d L W) (Idx d L W) ℂ, A.IsHermitian →
    ∀ {z : ℂ}, z.im ≠ 0 → ∀ (i : Idx d L W) {lam : ℝ}, 0 < lam → ∀ q : ℕ,
      T2196_QuadTailAt d L W v A z i lam q

/-- Target 7 (`gue_quad_tail`): (4.7) for the GUE rows, `E|h_ik|² = N⁻¹`, `N = (W L)^d` (RBM2D `gue_quad_tail`,
`AuxCarrier.lean:876`, with `(W L)^2 ↦ (W L)^d`; consumer RBM2D `GUELocalSchur.lean:393`, UN-10). -/
def T2196_gue_quad_tail : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] {z : ℂ}, z.im ≠ 0 → ∀ (i : Idx d L W) {lam : ℝ}, 0 < lam → ∀ q : ℕ,
    gueP d L W {s : Ω d L W | lam * ((((((W * L) ^ d : ℕ) : ℝ))⁻¹) ^ 2 *
        ∑ k : {a : Idx d L W // a ≠ i}, ∑ l : {a : Idx d L W // a ≠ i},
          ‖green ((Xmat d L W s).submatrix Subtype.val Subtype.val) z k l‖ ^ 2) <
      ‖(∑ k : {a : Idx d L W // a ≠ i}, ∑ l : {a : Idx d L W // a ≠ i},
          Xmat d L W s i k.1 * green ((Xmat d L W s).submatrix Subtype.val Subtype.val) z k l *
            Xmat d L W s l.1 i) -
        ((((W * L) ^ d : ℕ) : ℝ))⁻¹ * ∑ k : {a : Idx d L W // a ≠ i},
          green ((Xmat d L W s).submatrix Subtype.val Subtype.val) z k k‖ ^ 2}
      ≤ ENNReal.ofReal (RBM.Green.hwConst q / lam ^ (q + 1))

/-- Target 8 (`kind_quad_tail`, model-generic per DECISIONS §57 (2)): (4.7) for the mixture law of a model class
`K` at size `n` — variances `a S(K.lamV sz n) + b N⁻¹` (`mixVar`), shift the model's mean `(K.M sz).mean n` — i.e.
for the matrix `μ + X` of the GUE-phase path and of the centred OU marginal `ouMatC`.  Band: `lamV = sz.lam`, mean `0`. -/
def T2196_quad_tail_kind : Prop :=
  ∀ {d : ℕ} (K : UNKind d) (sz : Sizes d) (n : ℕ) (a b : ℝ) {z : ℂ}, z.im ≠ 0 →
    ∀ (i : Idx d (sz.L n) (sz.W n)) {lam : ℝ}, 0 < lam → ∀ q : ℕ,
      T2196_QuadTailAt d (sz.L n) (sz.W n)
        (fun c => a.toNNReal * gvarF d (sz.L n) (sz.W n) (K.lamV sz n) c +
          b.toNNReal * gueVar d (sz.L n) (sz.W n) c)
        ((K.M sz).mean n) z i lam q

/-- Target 9 (`aux_lin_tail`): the rank-one tail `Q = Y − R`, `V_q = R²` for an arbitrary merged row chaos
(RBM2D `aux_lin_tail`, `AuxCarrier.lean:1076`; consumers RBM2D `EntryTail.lean:542`, `:616`). -/
def T2196_aux_lin_tail : Prop :=
  ∀ {d : ℕ} {sz : Sizes d} {κ : Type} [Fintype κ] [DecidableEq κ] (C : RBM.Green.RowChaos sz κ)
    (Y R : Sizes.SeqΩ sz → ℝ), (∀ ω, 0 ≤ R ω) →
    (∀ ω, C.chaos ω = ((Y ω - R ω : ℝ) : ℂ)) → (∀ ω, C.Vq ω = R ω ^ 2) →
    ∀ {Λ : ℝ}, 1 < Λ → ∀ q : ℕ,
      (Sizes.seqP sz) {ω | Λ * R ω < Y ω} ≤
        ENNReal.ofReal (RBM.Green.hwConst q / ((Λ - 1) ^ 2) ^ (q + 1))

/-- The instance bounds are nontrivial (`1/2 < 1`): `A_0 / 4 = 1/2` (`inst_chaos_tail`, `inst_gue_quad_tail`,
`inst_shift_quad_tail`, `inst_kind_quad_tail_band`) and `A_0 / (3 − 1)² = 1/2` (`inst_aux_lin_tail`). -/
def T2196_inst_bounds : Prop :=
  RBM.Green.hwConst 0 / (4 : ℝ) ^ (0 + 1) = 1 / 2 ∧
    RBM.Green.hwConst 0 / (((3 : ℝ) - 1) ^ 2) ^ (0 + 1) = 1 / 2

end RBM.Univ.T2196Check

end

#check (RBM.Univ.T2196Check.T2196_svarF_pos_of_block_eq : Prop)
#check (RBM.Univ.T2196Check.T2196_exists_seqP_map_eq_gaussLaw : Prop)
#check (RBM.Univ.T2196Check.T2196_sum_Smix_row : Prop)
#check (RBM.Univ.T2196Check.T2196_chaos_tail : Prop)
#check @RBM.Univ.T2196Check.T2196_QuadTailAt
#check (RBM.Univ.T2196Check.T2196_gaussLaw_quad_tail : Prop)
#check (RBM.Univ.T2196Check.T2196_gue_quad_tail : Prop)
#check (RBM.Univ.T2196Check.T2196_quad_tail_kind : Prop)
#check (RBM.Univ.T2196Check.T2196_aux_lin_tail : Prop)
#check (RBM.Univ.T2196Check.T2196_inst_bounds : Prop)
