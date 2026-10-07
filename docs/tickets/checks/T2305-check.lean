/-
Release check for T2305 (UN-28) (dispatcher V1, Tue Oct  6 14:15 UTC 2026; CLAUDE.md §4 step 0;
DECISIONS §16, §20, §29, §45 O2, §54, §57 (1)(2), §90, §91 (1)).
UN-28 (bulk universality, GUE phase): port of RBM2D `Universality/GUEPhase/Generator.lean` at `c9a24cf`
(1199 lines; `:1-1148` ported, the instance namespace `GeneratorCheck` `:1150-1192` rewritten at `d = 3`) to `d ≥ 3`:
Lemma 2.11 for the GUE profile, `genMatGUE(𝓛) = primRhsGUE(𝓛) + 𝓔^{(G̃)}_{GUE}`, with `N = (WL)^d`,
`S_GUE = L^{-d}`, prefactor `W^d`.
Class P of T2173 (`docs/reports/T2173-portmap.md:247`): the identity is pinned for the merged generic flow
`ztOf m E u` (`Loop/GLoopFlow.lean:55`) at every `m` with `0 < m.im` (`loopGenGUEOf`); the band names
(`genMatGUE`, `egtNGUE`, `loopGenGUE`, `loopGenGUE_one`, the RBM2D shapes) are its instance `m = mE E`.
New file `RBM3D/Universality/GUEPhase/Generator.lean`, namespace `RBM.Univ.GUEPhase`.
Section 1: the merged names the new file builds on (full namespaces).
Section 2: vocabulary (`mSigOfV`, `genMatGUEOfV`, `egtNGUEOfV`, `genMatGUEV`, `egtNGUEV`) and the pinned statements
as `def … : Prop` in the temporary namespace `RBM.Univ.GUEPhase.T2305Check`.  The library states each pin as a
theorem in `RBM.Univ.GUEPhase` whose type is exactly this body after unfolding the vocabulary.
Statement and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2305-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- `RBM3D/Universality/GUEPhase/Bootstrap.lean` (98e6d5b, UN-26a = T2202)
#check @RBM.Univ.GUEPhase.SBgue
#check @RBM.Univ.GUEPhase.SBgue_apply
#check @RBM.Univ.GUEPhase.sum_SBgue_col
#check @RBM.Univ.GUEPhase.primBilGUE
#check @RBM.Univ.GUEPhase.primRhsGUE
-- `RBM3D/Universality/Pins.lean` (f8ad4b4, UN-01 = T2174): the GUE coordinate variances at `N = (WL)^d`
#check @RBM.Univ.gueVar
-- `RBM3D/Green/Pins.lean` (64bdfd3): `avgErr` (twin of RBM2D `Path/Step2Vocab.lean:49`)
#check @RBM.Green.greenBlk
#check @RBM.Green.avgErr
-- `RBM3D/Loop/GLoopFlow.lean` (868b3b4): the generic spectral flow and the loop functional
#check @RBM.Gauss.ztOf
#check @RBM.Gauss.etaOf
#check @RBM.Gauss.zt_eq_ztOf
#check @RBM.Gauss.ztOf_im
#check @RBM.Gauss.Gres
#check @RBM.Gauss.blockMat
#check @RBM.Gauss.loopOf
#check @RBM.Gauss.loopL
#check @RBM.Gauss.gloopProd
#check @RBM.Gauss.trace_Eblk
#check @RBM.Loop.LoopIdx.cutGlue
-- `RBM3D/Loop/TreeRep.lean` (b06ff9b)
#check @RBM.Loop.LoopIdx
#check @RBM.Loop.LoopIdx.WF
#check @RBM.Loop.LoopIdx.length
#check @RBM.Loop.LoopIdx.cutGlueL
#check @RBM.Loop.LoopIdx.cutGlueR
-- `RBM3D/Loop/GLoop.lean` (e0c58e6)
#check @RBM.Gauss.Eblk
-- `RBM3D/Gauss/FineModel.lean`, `Defs/Sizes.lean` (0a873f1), `Gauss/Model.lean` (a722f63)
#check @RBM.Gauss.Idx
#check @RBM.Gauss.Vtx
#check @RBM.Gauss.CoordF
#check @RBM.Gauss.Ω
#check @RBM.Gauss.idxKey
#check @RBM.Gauss.idxKey_injective
#check @RBM.Gauss.idxKey_lt_or_eq_or_lt
#check @RBM.Gauss.Xentry
#check @RBM.Gauss.Xmat
#check @RBM.Gauss.coordinateMatrix
#check @RBM.Gauss.Hflow
#check @RBM.Gauss.split
#check @RBM.Gauss.splitEquiv
-- `RBM3D/Gauss/FlowCalculus.lean` (6f99812)
#check @RBM.Gauss.spectralM_im_pos
#check @RBM.Gauss.spectralZ_im
#check @RBM.Gauss.hasDerivAt_spectralZ
#check @RBM.Gauss.HflowBlock
#check @RBM.Gauss.hasDerivAt_green_moving
#check @RBM.Gauss.spectralMSign
#check @RBM.Gauss.spectralMSign_eq_mSigma
-- `RBM3D/Gauss/LoopCoordinate.lean` (31476de)
#check @RBM.Gauss.coordinateBlock
#check @RBM.Gauss.HflowBlock_update
#check @RBM.Gauss.gsigCoordinateDeriv
#check @RBM.Gauss.gsigCoordinateSecondDeriv
#check @RBM.Gauss.coordinateSecondWordDeriv
#check @RBM.Gauss.hasDerivAt_deriv_gloop_update
-- `RBM3D/Hierarchy/ContractionBasic.lean` (e318c24)
#check @RBM.Gauss.trace_coordinate_real
#check @RBM.Gauss.trace_coordinate_imag
#check @RBM.Gauss.trace_coordinate_diag
#check @RBM.Gauss.blockRelabel
#check @RBM.Gauss.coordinateMatrix_diag_imag_zero
#check @RBM.Gauss.coordinateMatrix_lower_zero
#check @RBM.Gauss.cutLeftChain
#check @RBM.Gauss.cutRightChain
#check @RBM.Gauss.trace_cutLeftChain_Eblk
#check @RBM.Gauss.trace_cutRightChain_Eblk
#check @RBM.Gauss.blockRelabel_submatrix_split
#check @RBM.Gauss.neg_trace_scalarDrift_cutGlue_split
-- `RBM3D/Hierarchy/ContractionSecondLoop.lean` (64a33ea; the RBM2D `ContractionSecondLoopAllCuts` and 12 more)
#check @RBM.Gauss.trace_twoEdge_mixed_eq_cutChains
#check @RBM.Gauss.sum_coordinateBlock_trace_pair
#check @RBM.Gauss.trace_gsigCoordinateSecondDeriv_word
#check @RBM.Gauss.trace_sameEdge_cutLoop
#check @RBM.Gauss.trace_sameEdge_oneLoop
#check @RBM.Gauss.EdgeSplit
#check @RBM.Gauss.edgeSplits
#check @RBM.Gauss.edgeSplits_reconstruct
#check @RBM.Gauss.edgeSplits_prefix_lengths
#check @RBM.Gauss.PairSplit
#check @RBM.Gauss.pairSplits
#check @RBM.Gauss.pairSplits_reconstruct
#check @RBM.Gauss.coordinateSameEdgeTerm
#check @RBM.Gauss.coordinatePairTerm
#check @RBM.Gauss.coordinateSameEdgeSum
#check @RBM.Gauss.coordinatePairSum
#check @RBM.Gauss.coordinateSecondWordDeriv_eq_position_sums
#check @RBM.Gauss.segmentLoopIdx
#check @RBM.Gauss.segmentLoopIdx_WF
#check @RBM.Gauss.coordinateWordProduct_eq_gloopProd
#check @RBM.Gauss.sameEdgeCutValue
#check @RBM.Gauss.pairCutValue
#check @RBM.Gauss.sum_coordinateSecondWordDeriv_allCuts
-- the band twin (template, not imported by the new file): `RBM3D/Induction/LoopGenN.lean` (e56d95c),
-- `RBM3D/Path/OneStep.lean` (593e519), the sized `STLIM` (`Induction/Step2Defs.lean:713`)
#check @RBM.Ind.loopGenN
#check @RBM.Path.genMat
-- `RBM3D/Defs/Semicircle.lean` (fbc9870), `RBM3D/Defs/Lattice.lean` (51f1a17)
#check @RBM.mE
#check @RBM.mSigma
#check @RBM.zt
#check @RBM.Zd
#check @RBM.card_Zd

/-! ## 2. Vocabulary and pins -/

namespace RBM.Univ.GUEPhase.T2305Check

/-- The generic Green sign value: `m` for `σ = +`, `m̄` for `σ = -` (`mSigOf (mE E) = mSigma E`, `rfl`). -/
noncomputable def mSigOfV (m : ℂ) (σ : Bool) : ℂ :=
  if σ then m else (starRingEnd ℂ) m

/-- **`genMatGUEOf`** (class P): the generator of one GUE increment on the loop functional along the generic
flow `ztOf m E u`, `½ Σ_c gueVar(c) ∂²_c 𝓛 + ∂_u 𝓛` (RBM2D `genMatGUE`, `Generator.lean:78`). -/
noncomputable def genMatGUEOfV (d L W : ℕ) [NeZero L] [NeZero W] (m : ℂ) (E u : ℝ)
    (M : Matrix (RBM.Gauss.Idx d L W) (RBM.Gauss.Idx d L W) ℂ) (I : RBM.Loop.LoopIdx (RBM.Zd d L)) : ℂ :=
  (1 / 2 : ℂ) * ∑ c : RBM.Gauss.CoordF d L W, ((RBM.Univ.gueVar d L W c : ℝ) : ℂ) *
      deriv (deriv (fun y : ℝ =>
        RBM.Gauss.loopL d L W (RBM.Gauss.blockMat d L W (M + (y : ℂ) • RBM.Gauss.coordinateMatrix d L W c))
          (RBM.Gauss.ztOf m E u) I)) 0 +
    deriv (fun v : ℝ => RBM.Gauss.loopL d L W (RBM.Gauss.blockMat d L W M) (RBM.Gauss.ztOf m E v) I) u

/-- **`egtNGUEOf`** (class P): `𝓔^{(G̃)}` of the GUE phase along `ztOf m E u`,
`W^d Σ_k Σ_{a,b} (tr(G(σ_k) E_a) - m(σ_k)) L^{-d} 𝓛(cut_k^{(b)})` (RBM2D `egtNGUE`, `Generator.lean:86`). -/
noncomputable def egtNGUEOfV (d L W : ℕ) [NeZero L] [NeZero W] (m : ℂ) (E u : ℝ)
    (M : Matrix (RBM.Gauss.Idx d L W) (RBM.Gauss.Idx d L W) ℂ) (I : RBM.Loop.LoopIdx (RBM.Zd d L)) : ℂ :=
  (W : ℂ) ^ d * ∑ k ∈ Finset.Icc 1 I.length, ∑ a : RBM.Zd d L, ∑ b : RBM.Zd d L,
    (Matrix.trace (RBM.Gauss.Gres (RBM.Gauss.blockMat d L W M) (RBM.Gauss.ztOf m E u)
        (I.σ.getD (k - 1) false) * RBM.Gauss.Eblk d L W a) - mSigOfV m (I.σ.getD (k - 1) false)) *
      RBM.Univ.GUEPhase.SBgue d L a b *
      RBM.Gauss.loopL d L W (RBM.Gauss.blockMat d L W M) (RBM.Gauss.ztOf m E u) (I.cutGlue k b)

/-- **`genMatGUE`** (band; the RBM2D shape at `d`): the source's body with `zt E u`, `gueVar d L W`. -/
noncomputable def genMatGUEV (d L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (RBM.Gauss.Idx d L W) (RBM.Gauss.Idx d L W) ℂ) (I : RBM.Loop.LoopIdx (RBM.Zd d L)) : ℂ :=
  (1 / 2 : ℂ) * ∑ c : RBM.Gauss.CoordF d L W, ((RBM.Univ.gueVar d L W c : ℝ) : ℂ) *
      deriv (deriv (fun y : ℝ =>
        RBM.Gauss.loopL d L W (RBM.Gauss.blockMat d L W (M + (y : ℂ) • RBM.Gauss.coordinateMatrix d L W c))
          (RBM.zt E u) I)) 0 +
    deriv (fun v : ℝ => RBM.Gauss.loopL d L W (RBM.Gauss.blockMat d L W M) (RBM.zt E v) I) u

/-- **`egtNGUE`** (band; the RBM2D shape at `d`): the source's body with `RBM.Green.avgErr d L W`. -/
noncomputable def egtNGUEV (d L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (RBM.Gauss.Idx d L W) (RBM.Gauss.Idx d L W) ℂ) (I : RBM.Loop.LoopIdx (RBM.Zd d L)) : ℂ :=
  (W : ℂ) ^ d * ∑ k ∈ Finset.Icc 1 I.length, ∑ a : RBM.Zd d L, ∑ b : RBM.Zd d L,
    RBM.Green.avgErr d L W E u M (I.σ.getD (k - 1) false) a * RBM.Univ.GUEPhase.SBgue d L a b *
      RBM.Gauss.loopL d L W (RBM.Gauss.blockMat d L W M) (RBM.zt E u) (I.cutGlue k b)

/-- Pin `T2305_genMatGUE_eq_Of`: the band generator is the generic one at `m = mE E` (`rfl`). -/
def T2305_genMatGUE_eq_Of : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (RBM.Gauss.Idx d L W) (RBM.Gauss.Idx d L W) ℂ) (I : RBM.Loop.LoopIdx (RBM.Zd d L)),
    genMatGUEV d L W E u M I = genMatGUEOfV d L W (RBM.mE E) E u M I

/-- Pin `T2305_egtNGUE_eq_Of`: the band `𝓔^{(G̃)}` is the generic one at `m = mE E` (`tr E_a = 1`). -/
def T2305_egtNGUE_eq_Of : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (RBM.Gauss.Idx d L W) (RBM.Gauss.Idx d L W) ℂ) (I : RBM.Loop.LoopIdx (RBM.Zd d L)),
    egtNGUEV d L W E u M I = egtNGUEOfV d L W (RBM.mE E) E u M I

/-- Pin `T2305_loopGenGUEOf` (class P core; RBM2D `Generator_core`, `:1066`): Lemma 2.11 for the GUE profile
along the generic flow, every `m` with `0 < m.im`, every `u < 1`, every Hermitian `M`, every loop length `k`. -/
def T2305_loopGenGUEOf : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (m : ℂ), 0 < m.im → ∀ (E u : ℝ), u < 1 →
    ∀ M : Matrix (RBM.Gauss.Idx d L W) (RBM.Gauss.Idx d L W) ℂ, M.IsHermitian →
    ∀ (k : ℕ) (σ : Fin k → Bool) (a : Fin k → RBM.Zd d L),
      genMatGUEOfV d L W m E u M (RBM.Gauss.loopOf σ a) =
        RBM.Univ.GUEPhase.primRhsGUE d L W
            (RBM.Gauss.loopL d L W (RBM.Gauss.blockMat d L W M) (RBM.Gauss.ztOf m E u))
            (RBM.Gauss.loopOf σ a) +
          egtNGUEOfV d L W m E u M (RBM.Gauss.loopOf σ a)

/-- Pin `T2305_loopGenGUE` (RBM2D `loopGenGUE`, `:1123`, binders unchanged, `LLf ↦ loopL … (zt E u)`). -/
def T2305_loopGenGUE : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (E : ℝ), 3 ≤ L → |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ M : Matrix (RBM.Gauss.Idx d L W) (RBM.Gauss.Idx d L W) ℂ, M.IsHermitian →
    ∀ (k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → RBM.Zd d L),
      genMatGUEV d L W E u M (RBM.Gauss.loopOf σ a) =
        RBM.Univ.GUEPhase.primRhsGUE d L W
            (RBM.Gauss.loopL d L W (RBM.Gauss.blockMat d L W M) (RBM.zt E u)) (RBM.Gauss.loopOf σ a) +
          egtNGUEV d L W E u M (RBM.Gauss.loopOf σ a)

/-- Pin `T2305_loopGenGUE_one` (RBM2D `loopGenGUE_one`, `:1134`). -/
def T2305_loopGenGUE_one : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (E : ℝ), 3 ≤ L → |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ M : Matrix (RBM.Gauss.Idx d L W) (RBM.Gauss.Idx d L W) ℂ, M.IsHermitian →
    ∀ (σ : Fin 1 → Bool) (a : Fin 1 → RBM.Zd d L),
      genMatGUEV d L W E u M (RBM.Gauss.loopOf σ a) = egtNGUEV d L W E u M (RBM.Gauss.loopOf σ a)

/-! Prop-valued shape checks (no proof obligation): the instance data of the ticket at `d = 3`, `L = 3`, `W = 2`. -/

example : Prop := T2305_loopGenGUEOf ∧ T2305_loopGenGUE ∧ T2305_loopGenGUE_one ∧
  T2305_genMatGUE_eq_Of ∧ T2305_egtNGUE_eq_Of

example : Prop :=
  genMatGUEOfV 3 3 2 Complex.I 0 (1 / 2)
      (Matrix.diagonal fun _ : RBM.Gauss.Idx 3 3 2 => (2 : ℂ))
      (RBM.Gauss.loopOf ![true, false] ![(0 : RBM.Zd 3 3), 0]) =
    RBM.Univ.GUEPhase.primRhsGUE 3 3 2
        (RBM.Gauss.loopL 3 3 2 (RBM.Gauss.blockMat 3 3 2
          (Matrix.diagonal fun _ : RBM.Gauss.Idx 3 3 2 => (2 : ℂ))) (RBM.Gauss.ztOf Complex.I 0 (1 / 2)))
        (RBM.Gauss.loopOf ![true, false] ![(0 : RBM.Zd 3 3), 0]) +
      egtNGUEOfV 3 3 2 Complex.I 0 (1 / 2)
        (Matrix.diagonal fun _ : RBM.Gauss.Idx 3 3 2 => (2 : ℂ))
        (RBM.Gauss.loopOf ![true, false] ![(0 : RBM.Zd 3 3), 0])

example : Prop :=
  genMatGUEV 3 3 2 0 (1 / 2) (Matrix.diagonal fun _ : RBM.Gauss.Idx 3 3 2 => (2 : ℂ))
      (RBM.Gauss.loopOf ![true] ![(0 : RBM.Zd 3 3)]) =
    egtNGUEV 3 3 2 0 (1 / 2) (Matrix.diagonal fun _ : RBM.Gauss.Idx 3 3 2 => (2 : ℂ))
      (RBM.Gauss.loopOf ![true] ![(0 : RBM.Zd 3 3)])

end RBM.Univ.GUEPhase.T2305Check
