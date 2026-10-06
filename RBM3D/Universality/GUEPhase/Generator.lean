/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.Bootstrap
import RBM3D.Universality.Pins
import RBM3D.Green.Pins
import RBM3D.Hierarchy.ContractionSecondLoop

/-!
# Lemma 2.11 for the GUE profile: the generator of one GUE-phase increment (UN-28, T2305)

Port of RBM2D `Universality/GUEPhase/Generator.lean` at commit `c9a24cf` (cited `Generator:<line>`;
1199 lines there, `:1-1148` ported, the instances `:1150-1192` rewritten at `d = 3`) to `d ≥ 3`.
Renaming rules as `Induction/LoopGenN.lean:15-20`: `Z2 L → Zd d L`, `Idx L W → Idx d L W`,
`BlockIndex L W → Vtx d L W`, `Coord L W → CoordF d L W`, `Gsig → Gres`, `gloop L W → loopL d L W`,
`RBM.Univ.gueVar L W → RBM.Univ.gueVar d L W`, `SBgue L → SBgue d L` (`L^{-d}`),
`W ^ 2 → W ^ d`, `(W * L) ^ 2 → (W * L) ^ d`.

## Main results

* `genMatGUE`, `egtNGUE` (band, `E`-indexed) and `genMatGUEOf`, `egtNGUEOf` (class P of T2173, the
  scalar `m(E, ilambda)` as a parameter: `ztOf m E u`, `mSigOf m σ`); `genMatGUE_eq_Of` (`rfl`) and
  `egtNGUE_eq_Of` (`tr E_a = 1`) identify the band forms with the instance `m = mE E`.
* `loopGenGUEOf` : for every `m` with `0 < m.im`, every `u < 1`, every Hermitian `M` and every loop
  `(σ, a)` of every length `k`: `genMatGUEOf (𝓛_{σ,a}) = primRhsGUE (𝓛) + egtNGUEOf (𝓛_{σ,a})`
  (Lemma 2.11 for the GUE profile `S_GUE = L^{-d}`).
* `loopGenGUE`, `loopGenGUE_one` : the band forms (`m = mE E`, `|E| < 2`), `k ≥ 2` and `k = 1`
  (where `primRhsGUE` of a 1-loop is `0`).

## Route (RBM2D `Generator:16-55`, with `gvar ↦ gueVar`, `SB ↦ SBgue`)

The GUE contraction chain (the leaf `Σ_c gueVar_c tr(A D_c C D_c) = N⁻¹ tr A tr C`, `N = (W L)^d`,
then `W^d Σ_{p,q} tr(A E_p) SBgue_{pq} tr(C E_q)`), the matrix bridge `M = Xmat ω_M`, the line
Hessian at the auxiliary flow time `1`, the spectral bridge (the `v`-derivative of the loop is a sum
of scalar insertions, turned into single-edge cuts by `neg_trace_scalarDrift_cutGlue_split`), the
reindexing of the `edgeSplits`/`pairSplits` list sums and the `m`-cancellation (only the column
sums `Σ_a SBgue_{ab} = 1`).  The spectral part holds for every `m` with `0 < m.im`
(`d_u ztOf m E u = -m`).  No statement uses `3 ≤ d`; `3 ≤ L` and `0 ≤ u` are carried by the band
pins only and are unused (as in the source).  Every unpinned helper is `private` and prefixed
`Generator_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open Matrix RBM RBM.Loop RBM.Gauss

/-! ## 0. The definitions -/

section Defs

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- The generic Green sign value: `m` for `σ = +`, `m̄` for `σ = -` (`mSigOf (mE E) = mSigma E`,
`rfl`). -/
def mSigOf (m : ℂ) (σ : Bool) : ℂ :=
  if σ then m else (starRingEnd ℂ) m

/-- **`genMatGUEOf`** (class P): the generator of one GUE-phase increment on the loop functional
along the generic flow `ztOf m E u`, `½ ∑_c gueVar(c) ∂²_c Φ_u(M) + ∂_u Φ_u(M)` (RBM2D `genMatGUE`,
`Generator:78`, with `spectralZ E u ↦ ztOf m E u`). -/
def genMatGUEOf (m : ℂ) (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (I : LoopIdx (Zd d L)) : ℂ :=
  (1 / 2 : ℂ) * ∑ c : CoordF d L W, ((RBM.Univ.gueVar d L W c : ℝ) : ℂ) *
      deriv (deriv (fun y : ℝ =>
        loopL d L W (blockMat d L W (M + (y : ℂ) • coordinateMatrix d L W c))
          (ztOf m E u) I)) 0 +
    deriv (fun v : ℝ => loopL d L W (blockMat d L W M) (ztOf m E v) I) u

/-- **`egtNGUEOf`** (class P): `𝓔^{(G̃)}` of the GUE phase along `ztOf m E u`,
`W^d ∑_k ∑_{a,b} (tr(G(σ_k) E_a) - m(σ_k)) L^{-d} 𝓛(cut_k^{(b)})` (RBM2D `egtNGUE`,
`Generator:86`; RBM1D `eGtermGUE`, `Flow/GUEPhaseStep.lean:55`). -/
def egtNGUEOf (m : ℂ) (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (I : LoopIdx (Zd d L)) : ℂ :=
  (W : ℂ) ^ d * ∑ k ∈ Finset.Icc 1 I.length, ∑ a : Zd d L, ∑ b : Zd d L,
    (Matrix.trace (Gres (blockMat d L W M) (ztOf m E u) (I.σ.getD (k - 1) false) *
        Eblk d L W a) - mSigOf m (I.σ.getD (k - 1) false)) *
      SBgue d L a b *
      loopL d L W (blockMat d L W M) (ztOf m E u) (I.cutGlue k b)

/-- The generator of one GUE-phase increment for the loop functional (band `m = mE E`),
`½ ∑_c gueVar(c) ∂²_c Φ_u(M) + ∂_u Φ_u(M)` (`genMat` with `gvarF ↦ gueVar`; RBM2D `Generator:78`). -/
def genMatGUE (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (I : LoopIdx (Zd d L)) : ℂ :=
  (1 / 2 : ℂ) * ∑ c : CoordF d L W, ((RBM.Univ.gueVar d L W c : ℝ) : ℂ) *
      deriv (deriv (fun y : ℝ =>
        loopL d L W (blockMat d L W (M + (y : ℂ) • coordinateMatrix d L W c))
          (zt E u) I)) 0 +
    deriv (fun v : ℝ => loopL d L W (blockMat d L W M) (zt E v) I) u

/-- `𝓔^{(G̃)}` of the GUE phase (band; `egtN` with `SB ↦ SBgue`; RBM2D `Generator:86`). -/
def egtNGUE (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (I : LoopIdx (Zd d L)) : ℂ :=
  (W : ℂ) ^ d * ∑ k ∈ Finset.Icc 1 I.length, ∑ a : Zd d L, ∑ b : Zd d L,
    RBM.Green.avgErr d L W E u M (I.σ.getD (k - 1) false) a * SBgue d L a b *
      loopL d L W (blockMat d L W M) (zt E u) (I.cutGlue k b)

end Defs

/-! ## 1. The GUE contraction chain -/

section Contraction

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- A diagonal GUE coordinate has variance `N⁻¹`, `N = (W L)^d`. -/
private theorem Generator_gueVar_diag (i : Idx d L W) (b : Bool) :
    ((RBM.Univ.gueVar d L W (i, i, b) : NNReal) : ℝ) = ((((W * L) ^ d : ℕ) : ℝ))⁻¹ := by
  simp [RBM.Univ.gueVar]

/-- An off-diagonal GUE coordinate has variance `(2N)⁻¹`. -/
private theorem Generator_gueVar_offDiag {i j : Idx d L W} (b : Bool) (hij : i ≠ j) :
    ((RBM.Univ.gueVar d L W (i, j, b) : NNReal) : ℝ) = (2 * (((W * L) ^ d : ℕ) : ℝ))⁻¹ := by
  simp [RBM.Univ.gueVar, hij]

/-- An upper-triangular sum, with its transposed term, plus the diagonal is the full
ordered-pair sum (copy of the private `contraction_sum_orderedPairs_from_upper`,
`Hierarchy/ContractionBasic.lean:321`; RBM2D `Hierarchy/ContractionSum.lean:22`). -/
private theorem Generator_sum_orderedPairs_from_upper
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (key : ι → ℕ) (hkey : Function.Injective key)
    (S : ι → ι → ℂ) (hS : ∀ i j, S i j = S j i)
    (f : ι → ι → ℂ) :
    ∑ i : ι, ∑ j : ι,
      (if key i < key j then S i j * (f i j + f j i)
       else if i = j then S i i * f i i else 0) =
      ∑ i : ι, ∑ j : ι, S i j * f i j := by
  classical
  have point (i j : ι) : S i j * f i j =
      (if key i < key j then S i j * f i j else 0) +
      (if i = j then S i i * f i i else 0) +
      (if key j < key i then S i j * f i j else 0) := by
    rcases lt_trichotomy (key i) (key j) with h | h | h
    · have hij : i ≠ j := by
        intro he
        subst j
        exact (lt_irrefl _) h
      simp [h, hij, not_lt_of_ge (le_of_lt h)]
    · have hij : i = j := hkey h
      subst j
      simp
    · have hij : i ≠ j := by
        intro he
        subst j
        exact (lt_irrefl _) h
      simp [h, hij, not_lt_of_ge (le_of_lt h)]
  have hswap :
      (∑ i : ι, ∑ j : ι, if key i < key j then S i j * f j i else 0) =
      (∑ i : ι, ∑ j : ι, if key j < key i then S i j * f i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hS]
  calc
    (∑ i : ι, ∑ j : ι,
      (if key i < key j then S i j * (f i j + f j i)
       else if i = j then S i i * f i i else 0)) =
        (∑ i : ι, ∑ j : ι, if key i < key j then S i j * f i j else 0) +
        (∑ i : ι, ∑ j : ι, if i = j then S i i * f i i else 0) +
        (∑ i : ι, ∑ j : ι, if key i < key j then S i j * f j i else 0) := by
          simp_rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          by_cases hij : key i < key j
          · have hne : i ≠ j := by
              intro he
              subst j
              exact (lt_irrefl _) hij
            simp [hij, hne, mul_add]
          · simp [hij]
    _ = (∑ i : ι, ∑ j : ι, if key i < key j then S i j * f i j else 0) +
        (∑ i : ι, ∑ j : ι, if i = j then S i i * f i i else 0) +
        (∑ i : ι, ∑ j : ι, if key j < key i then S i j * f i j else 0) := by
          rw [hswap]
    _ = ∑ i : ι, ∑ j : ι, S i j * f i j := by
          symm
          calc
            (∑ i : ι, ∑ j : ι, S i j * f i j) =
                ∑ i : ι, ∑ j : ι,
                  ((if key i < key j then S i j * f i j else 0) +
                   (if i = j then S i i * f i i else 0) +
                   (if key j < key i then S i j * f i j else 0)) := by
                    refine Finset.sum_congr rfl fun i _ =>
                      Finset.sum_congr rfl fun j _ => point i j
            _ = _ := by simp only [Finset.sum_add_distrib]

/-- **The GUE coordinate contraction** (leaf): the sum over all product coordinates of
`gueVar_c tr(A D_c C D_c)` is `N⁻¹ tr A tr C`, `N = (W L)^d`. -/
private theorem Generator_leaf (A C : Matrix (Idx d L W) (Idx d L W) ℂ) :
    ∑ c : CoordF d L W, ((RBM.Univ.gueVar d L W c : ℝ) : ℂ) *
        Matrix.trace (A * coordinateMatrix d L W c * C * coordinateMatrix d L W c) =
      (((W * L) ^ d : ℕ) : ℂ)⁻¹ * ((∑ i, A i i) * (∑ j, C j j)) := by
  classical
  have splitCoord (f : CoordF d L W → ℂ) :
      ∑ c : CoordF d L W, f c =
        ∑ i : Idx d L W, ∑ j : Idx d L W, ∑ b : Bool, f (i, j, b) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    exact Fintype.sum_prod_type (fun jb : Idx d L W × Bool => f (i, jb))
  rw [splitCoord]
  have hpoint (i j : Idx d L W) :
      ∑ b : Bool, ((RBM.Univ.gueVar d L W (i, j, b) : ℝ) : ℂ) *
        Matrix.trace (A * coordinateMatrix d L W (i, j, b) * C * coordinateMatrix d L W (i, j, b)) =
      (if idxKey d L W i < idxKey d L W j then
        (((W * L) ^ d : ℕ) : ℂ)⁻¹ * (A i i * C j j + A j j * C i i)
       else if i = j then (((W * L) ^ d : ℕ) : ℂ)⁻¹ * (A i i * C i i) else 0) := by
    rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
    · have hne : i ≠ j := by
        intro he
        subst j
        exact (lt_irrefl _) h
      have hv (b : Bool) : ((RBM.Univ.gueVar d L W (i, j, b) : ℝ) : ℂ) =
          (2 * (((W * L) ^ d : ℕ) : ℂ))⁻¹ := by
        have hr := Generator_gueVar_offDiag (d := d) (L := L) (W := W) b hne
        rw [hr]
        push_cast
        rfl
      simp only [h, ite_true, Fintype.sum_bool]
      rw [trace_coordinate_real d L W A C h, trace_coordinate_imag d L W A C h, hv true, hv false]
      ring
    · subst j
      have hv (b : Bool) : ((RBM.Univ.gueVar d L W (i, i, b) : ℝ) : ℂ) =
          (((W * L) ^ d : ℕ) : ℂ)⁻¹ := by
        rw [Generator_gueVar_diag (d := d) (L := L) (W := W) i b]
        push_cast
        rfl
      simp only [lt_irrefl, ite_false, ite_true, Fintype.sum_bool]
      rw [coordinateMatrix_diag_imag_zero d L W i, trace_coordinate_diag d L W A C i, hv true]
      simp
    · have hne : i ≠ j := by
        intro he
        subst j
        exact (lt_irrefl _) h
      have hrev : ¬ idxKey d L W i < idxKey d L W j := not_lt_of_ge (le_of_lt h)
      simp only [hrev, hne, ite_false, Fintype.sum_bool]
      rw [coordinateMatrix_lower_zero d L W h true, coordinateMatrix_lower_zero d L W h false]
      simp
  simp_rw [hpoint]
  rw [Generator_sum_orderedPairs_from_upper (idxKey d L W) (idxKey_injective d L W)
    (fun _ _ => (((W * L) ^ d : ℕ) : ℂ)⁻¹) (fun _ _ => rfl) (fun i j => A i i * C j j)]
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]

/-- Relabelling preserves the trace (copy of the private `trace_blockRelabel`,
`Hierarchy/ContractionSecondLoop.lean:42`; RBM2D `Hierarchy/ContractionSecondLoop.lean:19`). -/
private theorem Generator_trace_blockRelabel (M : Matrix (Idx d L W) (Idx d L W) ℂ) :
    Matrix.trace (blockRelabel d L W M) = Matrix.trace M := by
  simp only [Matrix.trace, Matrix.diag, blockRelabel]
  exact (Equiv.sum_comp (splitEquiv d L W).symm (fun i => M i i))

private theorem Generator_blockRelabel_mul (M N : Matrix (Idx d L W) (Idx d L W) ℂ) :
    blockRelabel d L W (M * N) = blockRelabel d L W M * blockRelabel d L W N :=
  (Matrix.submatrix_mul_equiv M N
    (splitEquiv d L W).symm (splitEquiv d L W).symm (splitEquiv d L W).symm).symm

/-- The block trace pattern in physical-site coordinates (copy of the private
`trace_coordinateBlock_pair`, `Hierarchy/ContractionSecondLoop.lean:54`; RBM2D
`Hierarchy/ContractionSecondLoop.lean:31`). -/
private theorem Generator_trace_coordinateBlock_pair
    (A C : Matrix (Vtx d L W) (Vtx d L W) ℂ) (γ : CoordF d L W) :
    Matrix.trace (A * coordinateBlock d L W γ * C * coordinateBlock d L W γ) =
    Matrix.trace (A.submatrix (split d L W) (split d L W) * coordinateMatrix d L W γ *
      C.submatrix (split d L W) (split d L W) * coordinateMatrix d L W γ) := by
  let P := A.submatrix (split d L W) (split d L W)
  let Q := C.submatrix (split d L W) (split d L W)
  have hA : blockRelabel d L W P = A := blockRelabel_submatrix_split d L W A
  have hC : blockRelabel d L W Q = C := blockRelabel_submatrix_split d L W C
  change Matrix.trace (A * blockRelabel d L W (coordinateMatrix d L W γ) *
    C * blockRelabel d L W (coordinateMatrix d L W γ)) =
    Matrix.trace (P * coordinateMatrix d L W γ * Q * coordinateMatrix d L W γ)
  rw [← hA, ← hC, ← Generator_blockRelabel_mul, ← Generator_blockRelabel_mul,
    ← Generator_blockRelabel_mul]
  exact Generator_trace_blockRelabel d L W _

/-- The blocks partition the identity with factor `W^{-d}` (private copy of the private
`contraction_sum_Eblk`, `Hierarchy/ContractionBasic.lean:755`; RBM2D `Defs/Model.lean:83`). -/
private theorem Generator_sum_Eblk :
    ∑ a, Eblk d L W a = (((W : ℂ) ^ d)⁻¹) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) := by
  ext p q
  simp only [Matrix.sum_apply, Eblk, Matrix.diagonal_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  split_ifs with h
  · simp [Finset.sum_ite_eq]
  · simp

/-- **The GUE coordinate contraction in block notation**: the analogue of
`sum_coordinateBlock_trace_pair` (`Hierarchy/ContractionSecondLoopSameEdge.lean:52`) with
`gvar ↦ gueVar`, `SB ↦ SBgue`. -/
private theorem Generator_blockContraction
    (A C : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    ∑ γ : CoordF d L W, ((RBM.Univ.gueVar d L W γ : ℝ) : ℂ) *
        Matrix.trace (A * coordinateBlock d L W γ * C * coordinateBlock d L W γ) =
      (W : ℂ) ^ d * ∑ p : Zd d L, ∑ q : Zd d L,
        Matrix.trace (A * Eblk d L W p) * SBgue d L p q * Matrix.trace (C * Eblk d L W q) := by
  simp_rw [Generator_trace_coordinateBlock_pair (d := d) (L := L) (W := W) A C]
  rw [Generator_leaf]
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have hL : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  have htr (B : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
      ∑ i : Idx d L W, B.submatrix (split d L W) (split d L W) i i = Matrix.trace B :=
    Equiv.sum_comp (splitEquiv d L W) (fun p => B p p)
  have hsumE (B : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
      ∑ p : Zd d L, Matrix.trace (B * Eblk d L W p) = (((W : ℂ) ^ d)⁻¹) * Matrix.trace B := by
    rw [← Matrix.trace_sum, ← Finset.mul_sum, Generator_sum_Eblk d L W, Matrix.mul_smul, Matrix.mul_one,
      Matrix.trace_smul, smul_eq_mul]
  simp only [SBgue_apply]
  have h2 : ∑ p : Zd d L, ∑ q : Zd d L,
      Matrix.trace (A * Eblk d L W p) * ((L : ℂ) ^ d)⁻¹ * Matrix.trace (C * Eblk d L W q) =
      ((L : ℂ) ^ d)⁻¹ * ((∑ p : Zd d L, Matrix.trace (A * Eblk d L W p)) *
        (∑ q : Zd d L, Matrix.trace (C * Eblk d L W q))) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [h2, hsumE, hsumE, htr, htr]
  push_cast
  field_simp
  ring

/-! ### The same-edge contraction -/

/-- The cut-loop product attached to one same-edge position, without its common coefficient
`2uW^d` (`sameEdgeCutValue`, `Hierarchy/ContractionSecondLoopAllCuts.lean:20`, with
`SB ↦ SBgue`). -/
private def Generator_sameEdgeCutValue (u : ℝ) (ω : Ω d L W) (z : ℂ)
    (e : EdgeSplit (Bool × Zd d L)) : ℂ :=
  let H := HflowBlock d L W u ω
  let I₁ := segmentLoopIdx d L e.before
  let I₂ := segmentLoopIdx d L e.after
  ∑ p : Zd d L, ∑ q : Zd d L,
    loopL d L W H z
      ⟨e.selected.1 :: (I₂.σ ++ (I₁.σ ++ [e.selected.1])),
        e.selected.2 :: (I₂.a ++ (I₁.a ++ [p]))⟩ *
      SBgue d L p q * loopL d L W H z ⟨[e.selected.1], [q]⟩

/-- The left/right cut-loop product attached to one pair of distinct edges, without its common
coefficient (`pairCutValue`, `Hierarchy/ContractionSecondLoopAllCuts.lean:33`, with
`SB ↦ SBgue`). -/
private def Generator_pairCutValue (u : ℝ) (ω : Ω d L W) (z : ℂ)
    (p : PairSplit (Bool × Zd d L)) : ℂ :=
  let H := HflowBlock d L W u ω
  let I₁ := segmentLoopIdx d L p.before
  let I₂ := segmentLoopIdx d L p.middle
  let I₃ := segmentLoopIdx d L p.after
  ∑ v : Zd d L, ∑ w : Zd d L,
    loopL d L W H z
      ((⟨I₁.σ ++ p.first.1 :: I₂.σ ++ p.second.1 :: I₃.σ,
          I₁.a ++ p.first.2 :: I₂.a ++ p.second.2 :: I₃.a⟩ : LoopIdx (Zd d L)).cutGlueL
        (I₁.σ.length + 1) (I₁.σ.length + I₂.σ.length + 2) v) *
      SBgue d L v w *
    loopL d L W H z
      ((⟨I₁.σ ++ p.first.1 :: I₂.σ ++ p.second.1 :: I₃.σ,
          I₁.a ++ p.first.2 :: I₂.a ++ p.second.2 :: I₃.a⟩ : LoopIdx (Zd d L)).cutGlueR
        (I₁.σ.length + 1) (I₁.σ.length + I₂.σ.length + 2) w)

/-- The weighted same-edge term at one chosen position of a finite word (GUE version of
`sum_gsigCoordinateSecondDeriv_word`, `Hierarchy/ContractionSecondLoopSameEdgeWord.lean:56`). -/
private theorem Generator_sum_gsigSecondDeriv_word
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω d L W) (z : ℂ) (s : Bool) (a : Zd d L)
    (P T : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    let G := Gres (HflowBlock d L W u ω) z s
    ∑ γ : CoordF d L W, ((RBM.Univ.gueVar d L W γ : ℝ) : ℂ) *
        Matrix.trace (P * (gsigCoordinateSecondDeriv d L W u ω γ z s * Eblk d L W a) * T) =
      (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ d *
        ∑ p : Zd d L, ∑ q : Zd d L,
          Matrix.trace (((G * Eblk d L W a * T * P) * G) * Eblk d L W p) *
            SBgue d L p q * Matrix.trace (G * Eblk d L W q) := by
  dsimp only
  simp_rw [trace_gsigCoordinateSecondDeriv_word d L W u hu ω]
  calc
    _ = ((2 : ℂ) * (u : ℂ)) * ∑ γ : CoordF d L W,
          (((RBM.Univ.gueVar d L W γ : ℝ) : ℂ) *
            Matrix.trace (((Gres (HflowBlock d L W u ω) z s * Eblk d L W a *
              T * P) * Gres (HflowBlock d L W u ω) z s) *
              coordinateBlock d L W γ * Gres (HflowBlock d L W u ω) z s *
              coordinateBlock d L W γ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun γ _ => ?_
        ring
    _ = _ := by
      rw [Generator_blockContraction]
      ring

/-- The same-edge variance contraction at the specified split of a finite loop word (GUE
version of `sum_sameEdge_cutLoops`, `Hierarchy/ContractionSecondLoopSameEdgeCut.lean:47`). -/
private theorem Generator_sum_sameEdge_cutLoops
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω d L W) (z : ℂ)
    (σ₁ σ₂ : List Bool) (a₁ a₂ : List (Zd d L))
    (s : Bool) (a : Zd d L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    let H := HflowBlock d L W u ω
    let P := gloopProd d L W H z ⟨σ₁, a₁⟩
    let T := gloopProd d L W H z ⟨σ₂, a₂⟩
    ∑ γ : CoordF d L W, ((RBM.Univ.gueVar d L W γ : ℝ) : ℂ) *
        Matrix.trace (P * (gsigCoordinateSecondDeriv d L W u ω γ z s * Eblk d L W a) * T) =
    (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ d *
      ∑ p : Zd d L, ∑ q : Zd d L,
        loopL d L W H z
          ⟨s :: (σ₂ ++ (σ₁ ++ [s])), a :: (a₂ ++ (a₁ ++ [p]))⟩ *
          SBgue d L p q * loopL d L W H z ⟨[s], [q]⟩ := by
  dsimp only
  rw [Generator_sum_gsigSecondDeriv_word d L W u hu ω z s a
    (gloopProd d L W (HflowBlock d L W u ω) z ⟨σ₁, a₁⟩)
    (gloopProd d L W (HflowBlock d L W u ω) z ⟨σ₂, a₂⟩)]
  simp_rw [trace_sameEdge_cutLoop d L W (HflowBlock d L W u ω) z
    σ₁ σ₂ a₁ a₂ s a _ h₁ h₂,
    trace_sameEdge_oneLoop d L W (HflowBlock d L W u ω) z s]

/-- At any chosen edge, the weighted second-coordinate insertion is the GUE same-edge cut-loop
double sum (`sum_coordinateSameEdgeTerm_cutLoops`,
`Hierarchy/ContractionSameEdgePositionCut.lean:20`). -/
private theorem Generator_sum_sameEdgeTerm
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω d L W) (z : ℂ) (e : EdgeSplit (Bool × Zd d L)) :
    ∑ γ : CoordF d L W, ((RBM.Univ.gueVar d L W γ : ℝ) : ℂ) *
        Matrix.trace (coordinateSameEdgeTerm d L W u ω γ z e) =
      (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ d * Generator_sameEdgeCutValue d L W u ω z e := by
  have h₁ : (e.before.map Prod.fst).length = (e.before.map Prod.snd).length :=
    segmentLoopIdx_WF d L e.before
  have h₂ : (e.after.map Prod.fst).length = (e.after.map Prod.snd).length :=
    segmentLoopIdx_WF d L e.after
  unfold Generator_sameEdgeCutValue
  dsimp only [coordinateSameEdgeTerm, segmentLoopIdx]
  rw [coordinateWordProduct_eq_gloopProd d L W u ω z e.before,
    coordinateWordProduct_eq_gloopProd d L W u ω z e.after]
  exact Generator_sum_sameEdge_cutLoops d L W u hu ω z
    (e.before.map Prod.fst) (e.after.map Prod.fst)
    (e.before.map Prod.snd) (e.after.map Prod.snd)
    e.selected.1 e.selected.2 h₁ h₂

/-! ### The two-edge contraction -/

omit [NeZero W] in
private theorem Generator_trace_two_smul (u : ℝ) (hu : 0 ≤ u)
    (A B C : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    Matrix.trace (A * (Real.sqrt u • B) * C * (Real.sqrt u • B)) =
      (u : ℂ) * Matrix.trace (A * B * C * B) := by
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_smul]
  rw [Real.mul_self_sqrt hu]
  rfl

private theorem Generator_trace_twoEdge_deriv_signs
    (u : ℝ) (ω : Ω d L W) (γ : CoordF d L W) (z : ℂ)
    (P M T : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (s t : Bool) (a c : Zd d L) :
    let H := HflowBlock d L W u ω
    let B := Real.sqrt u • coordinateBlock d L W γ
    Matrix.trace (P * (gsigCoordinateDeriv d L W u ω γ z s * Eblk d L W a) * M *
      (gsigCoordinateDeriv d L W u ω γ z t * Eblk d L W c) * T) =
    Matrix.trace (P * (Gres H z s * B * Gres H z s * Eblk d L W a) * M *
      (Gres H z t * B * Gres H z t * Eblk d L W c) * T) := by
  simp only [gsigCoordinateDeriv, neg_mul, mul_neg, neg_neg]

/-- Covariance summation of one ordered, unscaled two-edge cross term (GUE version of
`sum_twoEdge_mixed_cutChains`, `Hierarchy/ContractionSecondLoop.lean:78`). -/
private theorem Generator_sum_twoEdge_mixed_cutChains
    (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Zd d L))
    (s t : Bool) (a c : Zd d L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    ∑ γ : CoordF d L W, ((RBM.Univ.gueVar d L W γ : ℝ) : ℂ) *
        Matrix.trace (cutLeftChain d L W H z σ₁ σ₃ a₁ a₃ s t c *
          coordinateBlock d L W γ * cutRightChain d L W H z σ₂ a₂ s t a *
          coordinateBlock d L W γ) =
    (W : ℂ) ^ d * ∑ u : Zd d L, ∑ v : Zd d L,
      loopL d L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx (Zd d L)).cutGlueL
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) u) *
        SBgue d L u v *
      loopL d L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx (Zd d L)).cutGlueR
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) v) := by
  rw [Generator_blockContraction]
  congr 1
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rw [trace_cutLeftChain_Eblk d L W H z σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c u h₁ h₂,
    trace_cutRightChain_Eblk d L W H z σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c v h₁ h₂]

/-- One ordered cross term, after the GUE coordinate weights are summed (GUE version of
`sum_twoEdge_mixed_coordinate`, `Hierarchy/ContractionSecondLoop.lean:126`). -/
private theorem Generator_sum_twoEdge_mixed_coordinate
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω d L W) (z : ℂ)
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Zd d L))
    (s t : Bool) (a c : Zd d L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    let H := HflowBlock d L W u ω
    let Gs := Gres H z s
    let Gt := Gres H z t
    let P := gloopProd d L W H z ⟨σ₁, a₁⟩
    let M := gloopProd d L W H z ⟨σ₂, a₂⟩
    let T := gloopProd d L W H z ⟨σ₃, a₃⟩
    (∑ γ : CoordF d L W,
      let B := Real.sqrt u • coordinateBlock d L W γ
      (((RBM.Univ.gueVar d L W γ : ℝ) : ℂ) *
        Matrix.trace (P * (Gs * B * Gs * Eblk d L W a) * M *
          (Gt * B * Gt * Eblk d L W c) * T))) =
    (u : ℂ) * (W : ℂ) ^ d * ∑ p : Zd d L, ∑ q : Zd d L,
      loopL d L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx (Zd d L)).cutGlueL
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) p) *
        SBgue d L p q *
      loopL d L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx (Zd d L)).cutGlueR
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) q) := by
  dsimp only
  simp_rw [trace_twoEdge_mixed_eq_cutChains d L W]
  simp_rw [Generator_trace_two_smul d L W u hu]
  calc
    _ = (u : ℂ) * ∑ γ : CoordF d L W,
          (((RBM.Univ.gueVar d L W γ : ℝ) : ℂ) *
            Matrix.trace (cutLeftChain d L W (HflowBlock d L W u ω) z
              σ₁ σ₃ a₁ a₃ s t c * coordinateBlock d L W γ *
              cutRightChain d L W (HflowBlock d L W u ω) z
                σ₂ a₂ s t a * coordinateBlock d L W γ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun γ _ => ?_
        ring
    _ = _ := by
      rw [Generator_sum_twoEdge_mixed_cutChains d L W (HflowBlock d L W u ω) z
        σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c h₁ h₂]
      ring

/-- The same contraction written with the two actual first derivatives of the signed Green
factors in `coordinateSecondWordDeriv` (GUE version of `sum_twoEdge_mixed_deriv`,
`Hierarchy/ContractionSecondLoop.lean:172`). -/
private theorem Generator_sum_twoEdge_mixed_deriv
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω d L W) (z : ℂ)
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Zd d L))
    (s t : Bool) (a c : Zd d L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    let H := HflowBlock d L W u ω
    let P := gloopProd d L W H z ⟨σ₁, a₁⟩
    let M := gloopProd d L W H z ⟨σ₂, a₂⟩
    let T := gloopProd d L W H z ⟨σ₃, a₃⟩
    (∑ γ : CoordF d L W,
      (((RBM.Univ.gueVar d L W γ : ℝ) : ℂ) *
        Matrix.trace (P *
          (gsigCoordinateDeriv d L W u ω γ z s * Eblk d L W a) * M *
          (gsigCoordinateDeriv d L W u ω γ z t * Eblk d L W c) * T))) =
    (u : ℂ) * (W : ℂ) ^ d * ∑ p : Zd d L, ∑ q : Zd d L,
      loopL d L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx (Zd d L)).cutGlueL
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) p) *
        SBgue d L p q *
      loopL d L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx (Zd d L)).cutGlueR
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) q) := by
  dsimp only
  simp_rw [Generator_trace_twoEdge_deriv_signs d L W u ω]
  exact Generator_sum_twoEdge_mixed_coordinate d L W u hu ω z
    σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c h₁ h₂

/-- At any chosen ordered pair of edges, the GUE variance contraction is the corresponding
left/right cut-loop double sum (`sum_coordinatePairTerm_cutLoops`,
`Hierarchy/ContractionPairPositionCut.lean:20`). -/
private theorem Generator_sum_pairTerm
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω d L W) (z : ℂ) (p : PairSplit (Bool × Zd d L)) :
    ∑ γ : CoordF d L W, ((RBM.Univ.gueVar d L W γ : ℝ) : ℂ) *
        Matrix.trace (coordinatePairTerm d L W u ω γ z p) =
      (u : ℂ) * (W : ℂ) ^ d * Generator_pairCutValue d L W u ω z p := by
  have h₁ : (p.before.map Prod.fst).length = (p.before.map Prod.snd).length :=
    segmentLoopIdx_WF d L p.before
  have h₂ : (p.middle.map Prod.fst).length = (p.middle.map Prod.snd).length :=
    segmentLoopIdx_WF d L p.middle
  unfold Generator_pairCutValue
  dsimp only [coordinatePairTerm, segmentLoopIdx]
  rw [coordinateWordProduct_eq_gloopProd d L W u ω z p.before,
    coordinateWordProduct_eq_gloopProd d L W u ω z p.middle,
    coordinateWordProduct_eq_gloopProd d L W u ω z p.after]
  exact Generator_sum_twoEdge_mixed_deriv d L W u hu ω z
    (p.before.map Prod.fst) (p.middle.map Prod.fst) (p.after.map Prod.fst)
    (p.before.map Prod.snd) (p.middle.map Prod.snd) (p.after.map Prod.snd)
    p.first.1 p.second.1 p.first.2 p.second.2 h₁ h₂

/-! ### The full cut formula -/

private theorem Generator_sum_weighted_trace_list {α : Type*}
    (es : List α) (w : CoordF d L W → ℂ)
    (T : CoordF d L W → α → Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    ∑ γ : CoordF d L W, w γ * Matrix.trace ((es.map (T γ)).sum) =
      (es.map (fun e => ∑ γ : CoordF d L W, w γ * Matrix.trace (T γ e))).sum := by
  induction es with
  | nil =>
      simp only [List.map_nil, List.sum_nil, Matrix.trace_zero, mul_zero,
        Finset.sum_const_zero]
  | cons e es ih =>
      simp only [List.map_cons, List.sum_cons, Matrix.trace_add, mul_add,
        Finset.sum_add_distrib, ih]

omit [NeZero L] [NeZero W] in
private theorem Generator_list_sum_map_mul_left {α : Type*} (c : ℂ)
    (es : List α) (f : α → ℂ) :
    (es.map (fun e => c * f e)).sum = c * (es.map f).sum := by
  induction es with
  | nil => simp only [List.map_nil, List.sum_nil, mul_zero]
  | cons e es ih =>
      simp only [List.map_cons, List.sum_cons, mul_add, ih]

/-- Exact finite exchange of coordinate and edge-position sums in the traced second product
rule, with the GUE weights (`sum_coordinateSecondWordDeriv_trace_positions`,
`Hierarchy/ContractionSecondDerivativeTraceSum.lean:33`). -/
private theorem Generator_sum_csd_trace_positions
    (u : ℝ) (ω : Ω d L W) (z : ℂ) (l : List (Bool × Zd d L)) :
    ∑ γ : CoordF d L W, ((RBM.Univ.gueVar d L W γ : ℝ) : ℂ) *
        Matrix.trace (coordinateSecondWordDeriv d L W u ω γ z l) =
    ((edgeSplits l).map (fun e => ∑ γ : CoordF d L W,
      ((RBM.Univ.gueVar d L W γ : ℝ) : ℂ) *
        Matrix.trace (coordinateSameEdgeTerm d L W u ω γ z e))).sum +
    (2 : ℂ) * ((pairSplits l).map (fun p => ∑ γ : CoordF d L W,
      ((RBM.Univ.gueVar d L W γ : ℝ) : ℂ) *
        Matrix.trace (coordinatePairTerm d L W u ω γ z p))).sum := by
  simp_rw [coordinateSecondWordDeriv_eq_position_sums d L W]
  simp only [two_nsmul, Matrix.trace_add, mul_add, Finset.sum_add_distrib,
    coordinateSameEdgeSum, coordinatePairSum]
  rw [Generator_sum_weighted_trace_list d L W (edgeSplits l),
    Generator_sum_weighted_trace_list d L W (pairSplits l)]
  ring

/-- **The GUE all-cuts formula**: the full finite samplewise cut formula for any signed word, at
the GUE weights.  Both same-edge and distinct-edge families have coefficient `2uW^d`
(`sum_coordinateSecondWordDeriv_allCuts`, `Hierarchy/ContractionSecondLoopAllCuts.lean:61`). -/
private theorem Generator_sum_csd_allCuts
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω d L W) (z : ℂ) (l : List (Bool × Zd d L)) :
    ∑ γ : CoordF d L W, ((RBM.Univ.gueVar d L W γ : ℝ) : ℂ) *
        Matrix.trace (coordinateSecondWordDeriv d L W u ω γ z l) =
      (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ d *
        ((edgeSplits l).map (Generator_sameEdgeCutValue d L W u ω z)).sum +
      (2 : ℂ) * (u : ℂ) * (W : ℂ) ^ d *
        ((pairSplits l).map (Generator_pairCutValue d L W u ω z)).sum := by
  rw [Generator_sum_csd_trace_positions d L W u ω z l]
  simp_rw [Generator_sum_sameEdgeTerm d L W u hu ω z]
  simp_rw [Generator_sum_pairTerm d L W u hu ω z]
  rw [Generator_list_sum_map_mul_left, Generator_list_sum_map_mul_left]
  ring

end Contraction

/-! ## 2. The matrix bridge -/

section MatrixBridge

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The real coordinates of a matrix: real parts on `true`, imaginary parts on `false`. -/
private def Generator_omega (M : Matrix (Idx d L W) (Idx d L W) ℂ) : Ω d L W :=
  fun c => if c.2.2 then (M c.1 c.2.1).re else (M c.1 c.2.1).im

/-- A Hermitian matrix is the Gaussian matrix of its coordinates. -/
private theorem Generator_Xmat_omega {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) :
    Xmat d L W (Generator_omega M) = M := by
  ext i j
  change Xentry d L W (Generator_omega M) i j = M i j
  rw [Xentry]
  simp only [Generator_omega, ite_true, Bool.false_eq_true, ite_false]
  split_ifs with h1 h2
  · apply Complex.ext <;> simp
  · rw [← hM.apply i j]
    apply Complex.ext <;> simp
  · have hij : i = j := by
      rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
      · exact absurd h h1
      · exact h
      · exact absurd h h2
    subst hij
    exact hM.coe_re_apply_self i

/-- At the auxiliary flow time `1`, the flow sample of `ω_M` is `blockMat d L W M`. -/
private theorem Generator_HflowBlock_one {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) :
    HflowBlock d L W 1 (Generator_omega M) = blockMat d L W M := by
  rw [HflowBlock, Hflow, Real.sqrt_one, Complex.ofReal_one, one_smul, Generator_Xmat_omega hM]

end MatrixBridge

/-! ## 3. The second-derivative bridge -/

section SecondBridge

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The line Hessian of the loop along `coordinateMatrix c` at a Hermitian `M` is the coordinate
Hessian of the flow sample `ω_M` at the auxiliary time `1`. -/
private theorem Generator_deriv2 {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian)
    (c : CoordF d L W) {z : ℂ} (hz : z.im ≠ 0) (I : LoopIdx (Zd d L)) (hI : I.WF) :
    deriv (deriv (fun y : ℝ =>
        loopL d L W (blockMat d L W (M + (y : ℂ) • coordinateMatrix d L W c)) z I)) 0 =
      Matrix.trace (coordinateSecondWordDeriv d L W 1 (Generator_omega M) c z (I.σ.zip I.a)) := by
  set ω := Generator_omega M with hω
  set g : ℝ → ℂ := fun s => loopL d L W (HflowBlock d L W 1 (Function.update ω c s)) z I with hg
  have hfg : (fun y : ℝ =>
      loopL d L W (blockMat d L W (M + (y : ℂ) • coordinateMatrix d L W c)) z I) =
      fun y => g (y + ω c) := by
    funext y
    simp only [hg, HflowBlock_update, hω, Generator_HflowBlock_one hM, Real.sqrt_one, one_mul,
      add_sub_cancel_right]
    congr 1
  rw [hfg]
  have h1 : deriv (fun y : ℝ => g (y + ω c)) = fun y => deriv g (y + ω c) := by
    funext y
    exact deriv_comp_add_const _ _ _
  rw [h1, deriv_comp_add_const, zero_add]
  exact (hasDerivAt_deriv_gloop_update d L W 1 ω c hz I hI).deriv

end SecondBridge

/-! ## 4. The spectral bridge at a general Hermitian block matrix -/

section SpectralBridge

open scoped Matrix.Norms.L2Operator

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The derivative of the generic spectral flow: `d_u ztOf m E u = -m` (the generic form of
`hasDerivAt_spectralZ`, `Gauss/FlowCalculus.lean:100`). -/
private theorem Generator_hasDerivAt_ztOf (m : ℂ) (E u : ℝ) :
    HasDerivAt (ztOf m E) (-m) u := by
  have h1 : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 u := (hasDerivAt_id u).ofReal_comp
  have h2 : HasDerivAt (fun v : ℝ => ((E : ℂ) + (1 - (v : ℂ)) * m)) (-m) u := by
    have h := (((hasDerivAt_const u (1 : ℂ)).sub h1).mul_const m).const_add (E : ℂ)
    simpa using h
  exact h2

/-- The signed word `Π G(σ) E_a` of a list of edges, at a general block matrix. -/
private def Generator_word (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (l : List (Bool × Zd d L)) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1

private theorem Generator_word_eq (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (l : List (Bool × Zd d L)) :
    Generator_word H z l = gloopProd d L W H z ⟨l.map Prod.fst, l.map Prod.snd⟩ := by
  have hzip : (l.map Prod.fst).zip (l.map Prod.snd) = l := by
    induction l with
    | nil => rfl
    | cons p l ih => simp [ih]
  rw [gloopProd, hzip]
  rfl

/-- The spectral derivative of one signed resolvent at a fixed Hermitian matrix, along the
generic flow `ztOf m E` with `0 < m.im` (the generic-`H`, generic-`m` form of the private
`OneStep_hasDerivAt_spec0`; RBM2D `Generator_hasDerivAt_Gsig_spec`, `:716`). -/
private theorem Generator_hasDerivAt_Gsig_spec {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {m : ℂ} (hm : 0 < m.im) {E u : ℝ} (hu : u < 1) (σ : Bool) :
    HasDerivAt (fun v : ℝ => Gres H (ztOf m E v) σ)
      (-(Gres H (ztOf m E u) σ *
        (mSigOf m σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) *
        Gres H (ztOf m E u) σ)) u := by
  have him : (ztOf m E u).im ≠ 0 := by
    rw [ztOf_im, etaOf]
    exact ne_of_gt (mul_pos (by linarith) hm)
  cases σ with
  | true =>
      have h := hasDerivAt_green_moving (hasDerivAt_const u H) (Generator_hasDerivAt_ztOf m E u)
        hH him
      simpa only [mSigOf, ite_true, zero_sub, neg_smul, neg_neg, Matrix.mul_neg,
        Matrix.neg_mul] using h
  | false =>
      have hz : HasDerivAt (fun v : ℝ => (starRingEnd ℂ) (ztOf m E v))
          (-((starRingEnd ℂ) m)) u := by
        simpa using (Generator_hasDerivAt_ztOf m E u).star
      have him' : ((starRingEnd ℂ) (ztOf m E u)).im ≠ 0 := by simpa using him
      have h := hasDerivAt_green_moving (hasDerivAt_const u H) hz hH him'
      have hfun : (fun v : ℝ => Gres H (ztOf m E v) false) =
          fun v : ℝ => Gres H ((starRingEnd ℂ) (ztOf m E v)) true := by
        funext v
        simp [Gres]
      rw [hfun]
      have hG : Gres H (ztOf m E u) false = Gres H ((starRingEnd ℂ) (ztOf m E u)) true := by
        simp [Gres]
      rw [hG]
      simpa only [mSigOf, Bool.false_eq_true, ite_false, zero_sub, neg_smul, neg_neg] using h

/-- The scalar insertion at one selected edge. -/
private def Generator_edgeTerm (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (m : ℂ) (E u : ℝ)
    (e : EdgeSplit (Bool × Zd d L)) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  -(Generator_word H (ztOf m E u) e.before *
    (Gres H (ztOf m E u) e.selected.1 *
        (mSigOf m e.selected.1 • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) *
      (Gres H (ztOf m E u) e.selected.1 * Eblk d L W e.selected.2 *
        Generator_word H (ztOf m E u) e.after)))

/-- The product rule over the word: the spectral derivative is the sum of the edge insertions. -/
private theorem Generator_hasDerivAt_word_spec {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {m : ℂ} (hm : 0 < m.im) {E u : ℝ} (hu : u < 1)
    (l : List (Bool × Zd d L)) :
    HasDerivAt (fun v : ℝ => Generator_word H (ztOf m E v) l)
      (((edgeSplits l).map (Generator_edgeTerm H m E u)).sum) u := by
  induction l with
  | nil =>
      simpa [Generator_word, edgeSplits] using
        hasDerivAt_const u (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)
  | cons p l ih =>
      have h := ((Generator_hasDerivAt_Gsig_spec (E := E) hH hm hu p.1).mul_const (Eblk d L W p.2)).mul ih
      have hfun : (fun v : ℝ => Gres H (ztOf m E v) p.1 * Eblk d L W p.2) *
          (fun v : ℝ => Generator_word H (ztOf m E v) l) =
          fun v : ℝ => Generator_word H (ztOf m E v) (p :: l) := by
        funext v
        rfl
      rw [hfun] at h
      refine h.congr_deriv ?_
      have hcons : ∀ e : EdgeSplit (Bool × Zd d L),
          Generator_edgeTerm H m E u ⟨p :: e.before, e.selected, e.after⟩ =
            (Gres H (ztOf m E u) p.1 * Eblk d L W p.2) * Generator_edgeTerm H m E u e := by
        intro e
        simp only [Generator_edgeTerm, Generator_word, List.foldr_cons, Matrix.mul_neg,
          Matrix.mul_assoc]
      simp only [edgeSplits, List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
        hcons, List.sum_map_mul_left]
      simp only [Generator_edgeTerm, Generator_word, List.foldr_nil, Matrix.one_mul,
        Matrix.mul_assoc, Matrix.neg_mul]

/-- The spectral derivative of a loop at a fixed Hermitian block matrix. -/
private theorem Generator_deriv_spec {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {m : ℂ} (hm : 0 < m.im) {E u : ℝ} (hu : u < 1)
    (I : LoopIdx (Zd d L)) :
    deriv (fun v : ℝ => loopL d L W H (ztOf m E v) I) u =
      ((edgeSplits (I.σ.zip I.a)).map
        (fun e => Matrix.trace (Generator_edgeTerm H m E u e))).sum := by
  set T : Matrix (Vtx d L W) (Vtx d L W) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((Matrix.traceLinearMap (Vtx d L W) ℂ ℂ).restrictScalars ℝ)
  have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
  have h := T.hasFDerivAt.comp_hasDerivAt u
    (Generator_hasDerivAt_word_spec (E := E) hH hm hu (I.σ.zip I.a))
  simp only [hT, Function.comp_def] at h
  have hfun : (fun v : ℝ => loopL d L W H (ztOf m E v) I) =
      fun v : ℝ => Matrix.trace (Generator_word H (ztOf m E v) (I.σ.zip I.a)) := by
    funext v
    rfl
  rw [hfun, h.deriv, Matrix.trace_list_sum, List.map_map]
  rfl

/-- One edge insertion is a sum of single-edge cuts. -/
private theorem Generator_trace_edgeTerm (H : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (m : ℂ) (E u : ℝ) (e : EdgeSplit (Bool × Zd d L)) :
    Matrix.trace (Generator_edgeTerm H m E u e) =
      -(mSigOf m e.selected.1 * (W : ℂ) ^ d) *
        ∑ b : Zd d L, loopL d L W H (ztOf m E u)
          ((⟨e.before.map Prod.fst ++ e.selected.1 :: e.after.map Prod.fst,
              e.before.map Prod.snd ++ e.selected.2 :: e.after.map Prod.snd⟩ :
            LoopIdx (Zd d L)).cutGlue ((e.before.map Prod.fst).length + 1) b) := by
  have hpre : (e.before.map Prod.fst).length = (e.before.map Prod.snd).length := by simp
  have h := neg_trace_scalarDrift_cutGlue_split d L W H (ztOf m E u)
    (e.before.map Prod.fst) (e.after.map Prod.fst)
    (e.before.map Prod.snd) (e.after.map Prod.snd)
    e.selected.1 e.selected.2 (mSigOf m e.selected.1) hpre
  rw [← h, Generator_edgeTerm, Matrix.trace_neg, Generator_word_eq, Generator_word_eq]

end SpectralBridge

/-! ## 5. Reindexing the cut enumerations -/

section Reindex

/-- A list sum over `List.range n` is the `Finset.range` sum. -/
private theorem Generator_sum_listRange (n : ℕ) (f : ℕ → ℂ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- `Σ_{i<n} F(i+1) = Σ_{k ∈ [1,n]} F k`. -/
private theorem Generator_sum_range_Icc (n : ℕ) (F : ℕ → ℂ) :
    ∑ i ∈ Finset.range n, F (i + 1) = ∑ k ∈ Finset.Icc 1 n, F k := by
  refine Finset.sum_nbij' (fun i => i + 1) (fun k => k - 1) ?_ ?_ ?_ ?_ ?_
  · intro i hi; simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Icc]; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]; omega
  · intro i _; simp
  · intro k hk; simp only [Finset.mem_Icc] at hk; omega
  · intro i _; rfl

/-- A sum over the edge enumeration, whose summand depends only on the one-based position. -/
private theorem Generator_sum_edgeSplits {α : Type*} (l : List α) (f : EdgeSplit α → ℂ)
    (F : ℕ → ℂ) (h : ∀ e ∈ edgeSplits l, f e = F (e.before.length + 1)) :
    ((edgeSplits l).map f).sum = ∑ k ∈ Finset.Icc 1 l.length, F k := by
  rw [List.map_congr_left h]
  have hmap : (edgeSplits l).map (fun e => F (e.before.length + 1)) =
      ((edgeSplits l).map (fun e => e.before.length)).map (fun i => F (i + 1)) := by
    rw [List.map_map]
    rfl
  rw [hmap, edgeSplits_prefix_lengths, Generator_sum_listRange, Generator_sum_range_Icc]

/-- The sum of a `flatMap` is the sum of the inner sums. -/
private theorem Generator_sum_flatMap {α β : Type*} (xs : List α) (g : α → List β) (f : β → ℂ) :
    ((xs.flatMap g).map f).sum = (xs.map fun x => ((g x).map f).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih]; simp

/-- A sum over the pair enumeration, whose summand depends only on the two one-based positions. -/
private theorem Generator_sum_pairSplits {α : Type*} (l : List α) (f : PairSplit α → ℂ)
    (F : ℕ → ℕ → ℂ)
    (h : ∀ p ∈ pairSplits l,
      f p = F (p.before.length + 1) (p.before.length + p.middle.length + 2)) :
    ((pairSplits l).map f).sum =
      ∑ k ∈ Finset.Icc 1 l.length, ∑ l' ∈ Finset.Ioc k l.length, F k l' := by
  rw [List.map_congr_left h, pairSplits, Generator_sum_flatMap]
  refine Generator_sum_edgeSplits l _ _ fun e he => ?_
  have hlen : l.length = e.before.length + 1 + e.after.length := by
    have hr := edgeSplits_reconstruct l e he
    rw [← hr, List.length_append, List.length_cons]
    omega
  rw [List.map_map]
  rw [Generator_sum_edgeSplits e.after _
    (fun j => F (e.before.length + 1) (e.before.length + j + 1)) (fun d _ => by
      simp only [Function.comp_apply]
      congr 1)]
  refine Finset.sum_nbij' (fun j => e.before.length + j + 1)
    (fun l' => l' - (e.before.length + 1)) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [Finset.mem_Icc] at hj
    simp only [Finset.mem_Ioc]; omega
  · intro l' hl'; simp only [Finset.mem_Ioc] at hl'
    simp only [Finset.mem_Icc]; omega
  · intro j hj; simp only [Finset.mem_Icc] at hj; omega
  · intro l' hl'; simp only [Finset.mem_Ioc] at hl'; omega
  · intro j _; rfl

end Reindex

/-! ## 6. Identifying each cut term with the loop's own cuts -/

section Cuts

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- A selected edge of the zipped word of a well-formed loop splits that loop. -/
private theorem Generator_edge_eq (I : LoopIdx (Zd d L)) (hI : I.WF)
    (e : EdgeSplit (Bool × Zd d L)) (he : e ∈ edgeSplits (I.σ.zip I.a)) :
    I = ⟨e.before.map Prod.fst ++ e.selected.1 :: e.after.map Prod.fst,
      e.before.map Prod.snd ++ e.selected.2 :: e.after.map Prod.snd⟩ := by
  have hr := edgeSplits_reconstruct _ e he
  have h1 := congrArg (List.map Prod.fst) hr
  have h2 := congrArg (List.map Prod.snd) hr
  rw [List.map_fst_zip hI.le] at h1
  rw [List.map_snd_zip hI.ge] at h2
  simp only [List.map_append, List.map_cons] at h1 h2
  cases I with
  | mk σ a =>
      simp only at h1 h2
      subst h1 h2
      rfl

/-- Two selected edges of the zipped word of a well-formed loop split that loop. -/
private theorem Generator_pair_eq (I : LoopIdx (Zd d L)) (hI : I.WF)
    (p : PairSplit (Bool × Zd d L)) (hp : p ∈ pairSplits (I.σ.zip I.a)) :
    I = ⟨p.before.map Prod.fst ++ p.first.1 :: p.middle.map Prod.fst ++
          p.second.1 :: p.after.map Prod.fst,
      p.before.map Prod.snd ++ p.first.2 :: p.middle.map Prod.snd ++
          p.second.2 :: p.after.map Prod.snd⟩ := by
  have hr := pairSplits_reconstruct _ p hp
  have h1 := congrArg (List.map Prod.fst) hr
  have h2 := congrArg (List.map Prod.snd) hr
  rw [List.map_fst_zip hI.le] at h1
  rw [List.map_snd_zip hI.ge] at h2
  simp only [List.map_append, List.map_cons] at h1 h2
  cases I with
  | mk σ a =>
      simp only at h1 h2
      subst h1 h2
      rfl

/-- The sign at the selected edge. -/
private theorem Generator_getD (b a : List (Bool × Zd d L)) (s : Bool) :
    (b.map Prod.fst ++ s :: a.map Prod.fst).getD (b.length + 1 - 1) false = s := by
  rw [Nat.add_sub_cancel]
  simp [List.getD_eq_getElem?_getD]

/-- Cut-and-glue at the edge after a matching prefix (RBM2D `LoopIdx.cutGlue_split`,
`Hierarchy/Operations.lean:40`; private copy, as `LoopGenN_cutGlue_split`). -/
private theorem Generator_cutGlue_split (σ₁ σ₂ : List Bool) (a₁ a₂ : List (Zd d L))
    (s : Bool) (a b : Zd d L) (h₁ : σ₁.length = a₁.length) :
    LoopIdx.cutGlue (σ₁.length + 1) b
      (⟨σ₁ ++ s :: σ₂, a₁ ++ a :: a₂⟩ : LoopIdx (Zd d L)) =
      ⟨σ₁ ++ s :: s :: σ₂, a₁ ++ b :: a :: a₂⟩ := by
  simp [LoopIdx.cutGlue, List.take_append, h₁]

private theorem Generator_loopL_eq (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (I : LoopIdx (Zd d L)) :
    loopL d L W H z I = Matrix.trace (gloopProd d L W H z I) := rfl

private theorem Generator_gloopProd_nil (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) :
    gloopProd d L W H z ⟨[], []⟩ = 1 := rfl

private theorem Generator_gloopProd_cons (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)) :
    gloopProd d L W H z ⟨s :: σ, b :: a⟩ =
      Gres H z s * Eblk d L W b * gloopProd d L W H z ⟨σ, a⟩ := rfl

private theorem Generator_gloopProd_append (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    {σ₁ : List Bool} {a₁ : List (Zd d L)} (h₁ : σ₁.length = a₁.length)
    (σ₂ : List Bool) (a₂ : List (Zd d L)) :
    gloopProd d L W H z ⟨σ₁ ++ σ₂, a₁ ++ a₂⟩ =
      gloopProd d L W H z ⟨σ₁, a₁⟩ * gloopProd d L W H z ⟨σ₂, a₂⟩ := by
  induction σ₁ generalizing a₁ with
  | nil =>
    obtain rfl : a₁ = [] := List.eq_nil_of_length_eq_zero h₁.symm
    simp [gloopProd]
  | cons s σ ih =>
    obtain ⟨b, a, rfl⟩ : ∃ b a, a₁ = b :: a := by
      cases a₁ with
      | nil => simp at h₁
      | cons b a => exact ⟨b, a, rfl⟩
    have h : σ.length = a.length := by simpa using h₁
    simp only [List.cons_append, Generator_gloopProd_cons, ih h, Matrix.mul_assoc]

/-- The rotated same-edge loop is the single-edge cut of the original loop. -/
private theorem Generator_gloop_same (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (b a : List (Bool × Zd d L)) (s : Bool) (x p : Zd d L) :
    loopL d L W H z ⟨s :: (a.map Prod.fst ++ (b.map Prod.fst ++ [s])),
        x :: (a.map Prod.snd ++ (b.map Prod.snd ++ [p]))⟩ =
      loopL d L W H z ((⟨b.map Prod.fst ++ s :: a.map Prod.fst,
        b.map Prod.snd ++ x :: a.map Prod.snd⟩ : LoopIdx (Zd d L)).cutGlue (b.length + 1) p) := by
  have hb : (b.map Prod.fst).length = (b.map Prod.snd).length := by simp
  have ha : (a.map Prod.fst).length = (a.map Prod.snd).length := by simp
  have hc := Generator_cutGlue_split (b.map Prod.fst) (a.map Prod.fst) (b.map Prod.snd)
    (a.map Prod.snd) s x p hb
  rw [List.length_map] at hc
  rw [hc]
  simp only [Generator_loopL_eq, Generator_gloopProd_cons, Generator_gloopProd_append H z ha,
    Generator_gloopProd_append H z hb, Generator_gloopProd_nil]
  have h := Matrix.trace_mul_comm (Gres H z s * Eblk d L W x * gloopProd d L W H z
      ⟨a.map Prod.fst, a.map Prod.snd⟩)
    (gloopProd d L W H z ⟨b.map Prod.fst, b.map Prod.snd⟩ * (Gres H z s * Eblk d L W p))
  simp only [Matrix.mul_assoc, Matrix.mul_one] at h ⊢
  exact h

/-- The same-edge cut value at a selected edge, as a function of its one-based position. -/
private theorem Generator_sameEdge {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian)
    (z : ℂ) (I : LoopIdx (Zd d L)) (hI : I.WF)
    (e : EdgeSplit (Bool × Zd d L)) (he : e ∈ edgeSplits (I.σ.zip I.a)) :
    Generator_sameEdgeCutValue d L W 1 (Generator_omega M) z e =
      ∑ p : Zd d L, ∑ q : Zd d L, loopL d L W (blockMat d L W M) z (I.cutGlue (e.before.length + 1) p) *
        SBgue d L p q * Matrix.trace (Gres (blockMat d L W M) z (I.σ.getD (e.before.length + 1 - 1) false) *
          Eblk d L W q) := by
  have hIe := Generator_edge_eq I hI e he
  simp only [Generator_sameEdgeCutValue, segmentLoopIdx, Generator_HflowBlock_one hM]
  rw [hIe, Generator_getD]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [Generator_gloop_same]
  congr 1
  simp [loopL]

/-- The pair cut value at two selected edges, as a function of their one-based positions. -/
private theorem Generator_pairCut {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian)
    (z : ℂ) (I : LoopIdx (Zd d L)) (hI : I.WF)
    (p : PairSplit (Bool × Zd d L)) (hp : p ∈ pairSplits (I.σ.zip I.a)) :
    Generator_pairCutValue d L W 1 (Generator_omega M) z p =
      ∑ v : Zd d L, ∑ w : Zd d L,
        loopL d L W (blockMat d L W M) z (I.cutGlueL (p.before.length + 1)
            (p.before.length + p.middle.length + 2) v) * SBgue d L v w *
          loopL d L W (blockMat d L W M) z (I.cutGlueR (p.before.length + 1)
            (p.before.length + p.middle.length + 2) w) := by
  have hIp := Generator_pair_eq I hI p hp
  simp only [Generator_pairCutValue, segmentLoopIdx, Generator_HflowBlock_one hM, List.length_map]
  rw [← hIp]

/-- The spectral insertion at a selected edge, as a function of its one-based position. -/
private theorem Generator_specEdge (H : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (m : ℂ) (E u : ℝ) (I : LoopIdx (Zd d L)) (hI : I.WF)
    (e : EdgeSplit (Bool × Zd d L)) (he : e ∈ edgeSplits (I.σ.zip I.a)) :
    Matrix.trace (Generator_edgeTerm H m E u e) =
      -(mSigOf m (I.σ.getD (e.before.length + 1 - 1) false) * (W : ℂ) ^ d) *
        ∑ b : Zd d L, loopL d L W H (ztOf m E u) (I.cutGlue (e.before.length + 1) b) := by
  have hIe := Generator_edge_eq I hI e he
  rw [Generator_trace_edgeTerm, List.length_map]
  conv_rhs => rw [hIe, Generator_getD]

end Cuts

/-! ## 7. The single-edge algebra -/

section Assembly

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `⟨G̃(σ) E_a⟩ = ⟨G(σ) E_a⟩ - m(σ)` for the band `avgErr` (`tr E_a = 1`, RBM2D
`Generator_avgErr`, `:1005`). -/
private theorem Generator_avgErr (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (σ : Bool)
    (a : Zd d L) :
    RBM.Green.avgErr d L W E u M σ a =
      Matrix.trace (Gres (blockMat d L W M) (zt E u) σ * Eblk d L W a) - mSigOf (mE E) σ := by
  rw [RBM.Green.avgErr, RBM.Green.greenBlk, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul,
    Matrix.one_mul, Matrix.trace_smul, trace_Eblk, smul_eq_mul, mul_one]
  rfl

/-- `Σ_{a,b} (t_a - m) S_{ab} f_b = Σ_{p,q} f_p S_{pq} t_q - m Σ_b f_b` (the column sums of
`SBgue` are `1`: `sum_SBgue_col`, replacing RBM2D `Generator_sum_SBgue_col`, `:1014`). -/
private theorem Generator_sum_algebra (f t : Zd d L → ℂ) (m : ℂ) :
    ∑ a' : Zd d L, ∑ b' : Zd d L, (t a' - m) * SBgue d L a' b' * f b' =
      ∑ p : Zd d L, ∑ q : Zd d L, f p * SBgue d L p q * t q - m * ∑ p : Zd d L, f p := by
  have hS : ∀ p q : Zd d L, SBgue d L p q = SBgue d L q p := fun p q => rfl
  have h1 : ∑ a' : Zd d L, ∑ b' : Zd d L, t a' * SBgue d L a' b' * f b' =
      ∑ p : Zd d L, ∑ q : Zd d L, f p * SBgue d L p q * t q := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hS q p]
    ring
  have h2 : ∑ a' : Zd d L, ∑ b' : Zd d L, m * SBgue d L a' b' * f b' = m * ∑ p : Zd d L, f p := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_SBgue_col, mul_one]
  rw [← h1, ← h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b' _ => ?_
  ring

/-- The same-edge cuts and the spectral cuts of one edge combine into its `𝓔^{(G̃)}` term. -/
private theorem Generator_edge_algebra (m : ℂ) (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (I : LoopIdx (Zd d L)) (k : ℕ) :
    (W : ℂ) ^ d * ∑ p : Zd d L, ∑ q : Zd d L,
        loopL d L W (blockMat d L W M) (ztOf m E u) (I.cutGlue k p) * SBgue d L p q *
          Matrix.trace (Gres (blockMat d L W M) (ztOf m E u) (I.σ.getD (k - 1) false) *
            Eblk d L W q) +
      -(mSigOf m (I.σ.getD (k - 1) false) * (W : ℂ) ^ d) *
        ∑ b : Zd d L, loopL d L W (blockMat d L W M) (ztOf m E u) (I.cutGlue k b) =
    (W : ℂ) ^ d * ∑ a : Zd d L, ∑ b : Zd d L,
      (Matrix.trace (Gres (blockMat d L W M) (ztOf m E u) (I.σ.getD (k - 1) false) *
          Eblk d L W a) - mSigOf m (I.σ.getD (k - 1) false)) * SBgue d L a b *
        loopL d L W (blockMat d L W M) (ztOf m E u) (I.cutGlue k b) := by
  rw [Generator_sum_algebra (fun b => loopL d L W (blockMat d L W M) (ztOf m E u) (I.cutGlue k b))
    (fun a => Matrix.trace (Gres (blockMat d L W M) (ztOf m E u) (I.σ.getD (k - 1) false) *
      Eblk d L W a))]
  ring

end Assembly

/-! ## 8. The identification of the band forms -/

/-- The band generator is the generic one at `m = mE E` (`rfl`: `zt_eq_ztOf`). -/
theorem genMatGUE_eq_Of :
    ∀ (d L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ)
      (M : Matrix (Idx d L W) (Idx d L W) ℂ) (I : LoopIdx (Zd d L)),
      genMatGUE d L W E u M I = genMatGUEOf d L W (mE E) E u M I :=
  fun _ _ _ _ _ _ _ _ _ => rfl

/-- The band `𝓔^{(G̃)}` is the generic one at `m = mE E` (`tr E_a = 1`). -/
theorem egtNGUE_eq_Of :
    ∀ (d L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ)
      (M : Matrix (Idx d L W) (Idx d L W) ℂ) (I : LoopIdx (Zd d L)),
      egtNGUE d L W E u M I = egtNGUEOf d L W (mE E) E u M I := by
  intro d L W _ _ E u M I
  unfold egtNGUE egtNGUEOf
  refine congrArg _ (Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_)
  rw [Generator_avgErr]
  rfl

/-! ## 9. The assembly -/

/-- **Lemma 2.11 for the GUE profile, class P, every loop length** (RBM2D `Generator_core`, `:1066`,
with `spectralZ E ↦ ztOf m E`; RBM1D `c06b103` `generator_add_zMotion_gue`,
`Flow/GUEPhaseStep.lean:459`): for every `m` with `0 < m.im`, every `u < 1`, every Hermitian `M`
and every loop `(σ, a)` of every length `k` (`k = 0, 1` included),
`genMatGUEOf(𝓛_{σ,a}) = W^d Σ_{k<l} 𝓛 S_GUE 𝓛 + 𝓔^{(G̃)}_{GUE}`, the first sum being
`primRhsGUE (𝓛)`.  No `3 ≤ L`, no `0 ≤ u`, no `|E| < 2`. -/
theorem loopGenGUEOf :
    ∀ (d L W : ℕ) [NeZero L] [NeZero W] (m : ℂ), 0 < m.im → ∀ (E u : ℝ), u < 1 →
      ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian →
      ∀ (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d L),
        genMatGUEOf d L W m E u M (loopOf σ a) =
          primRhsGUE d L W (loopL d L W (blockMat d L W M) (ztOf m E u)) (loopOf σ a) +
            egtNGUEOf d L W m E u M (loopOf σ a) := by
  intro d L W _ _ m hm E u hu1 M hM k σ a
  set I : LoopIdx (Zd d L) := loopOf σ a with hIdef
  have hI : I.WF := by simp [hIdef, loopOf, LoopIdx.WF]
  have hlen : (I.σ.zip I.a).length = I.length := by
    simp [LoopIdx.length, List.length_zip, hI.symm]
  have hz : (ztOf m E u).im ≠ 0 := by
    rw [ztOf_im, etaOf]
    exact ne_of_gt (mul_pos (by linarith) hm)
  have hH : (blockMat d L W M).IsHermitian := hM.submatrix _
  set l := I.σ.zip I.a with hl
  set ω := Generator_omega M with hω
  set z := ztOf m E u with hzdef
  -- the three families of cut terms as functions of the one-based positions
  set Fs : ℕ → ℂ := fun k' => ∑ p : Zd d L, ∑ q : Zd d L,
    loopL d L W (blockMat d L W M) z (I.cutGlue k' p) * SBgue d L p q *
      Matrix.trace (Gres (blockMat d L W M) z (I.σ.getD (k' - 1) false) * Eblk d L W q) with hFs
  set Fsp : ℕ → ℂ := fun k' => -(mSigOf m (I.σ.getD (k' - 1) false) * (W : ℂ) ^ d) *
    ∑ b : Zd d L, loopL d L W (blockMat d L W M) z (I.cutGlue k' b) with hFsp
  set Fp : ℕ → ℕ → ℂ := fun k' l' => ∑ v : Zd d L, ∑ w : Zd d L,
    loopL d L W (blockMat d L W M) z (I.cutGlueL k' l' v) * SBgue d L v w *
      loopL d L W (blockMat d L W M) z (I.cutGlueR k' l' w) with hFp
  have hsame := Generator_sum_edgeSplits l (Generator_sameEdgeCutValue d L W 1 ω z) Fs
    (fun e he => Generator_sameEdge hM z I hI e he)
  have hpair := Generator_sum_pairSplits l (Generator_pairCutValue d L W 1 ω z) Fp
    (fun p hp => Generator_pairCut hM z I hI p hp)
  have hspec := Generator_sum_edgeSplits l
    (fun e => Matrix.trace (Generator_edgeTerm (blockMat d L W M) m E u e)) Fsp
    (fun e he => Generator_specEdge (blockMat d L W M) m E u I hI e he)
  -- the left side
  have hlhs : genMatGUEOf d L W m E u M I =
      (W : ℂ) ^ d * ∑ k' ∈ Finset.Icc 1 I.length, Fs k' +
        (W : ℂ) ^ d * ∑ k' ∈ Finset.Icc 1 I.length, ∑ l' ∈ Finset.Ioc k' I.length, Fp k' l' +
        ∑ k' ∈ Finset.Icc 1 I.length, Fsp k' := by
    rw [genMatGUEOf, Finset.sum_congr rfl fun c _ => by rw [Generator_deriv2 hM c hz I hI],
      Generator_sum_csd_allCuts d L W 1 zero_le_one ω z l,
      Generator_deriv_spec hH hm hu1 I, hsame, hpair, hspec, hlen]
    push_cast
    ring
  have hedge : ∑ k' ∈ Finset.Icc 1 I.length, ((W : ℂ) ^ d * Fs k' + Fsp k') =
      (W : ℂ) ^ d * ∑ k' ∈ Finset.Icc 1 I.length, ∑ a : Zd d L, ∑ b : Zd d L,
        (Matrix.trace (Gres (blockMat d L W M) z (I.σ.getD (k' - 1) false) * Eblk d L W a) -
          mSigOf m (I.σ.getD (k' - 1) false)) * SBgue d L a b *
          loopL d L W (blockMat d L W M) z (I.cutGlue k' b) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k' _ => Generator_edge_algebra m E u M I k'
  rw [hlhs]
  unfold primRhsGUE primBilGUE egtNGUEOf
  rw [← hedge, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [hFp]
  ring

/-- **Lemma 2.11 for the GUE profile, band form, loops of length `k ≥ 2`** (RBM2D `loopGenGUE`,
`:1123`; the source's statement at `d`, binders unchanged incl. the unused `3 ≤ L`, `0 ≤ u`): the
instance `m = mE E` of `loopGenGUEOf`. -/
theorem loopGenGUE :
    ∀ (d L W : ℕ) [NeZero L] [NeZero W] (E : ℝ), 3 ≤ L → |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
      ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian →
      ∀ (k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d L),
        genMatGUE d L W E u M (loopOf σ a) =
          primRhsGUE d L W (loopL d L W (blockMat d L W M) (zt E u)) (loopOf σ a) +
            egtNGUE d L W E u M (loopOf σ a) := by
  intro d L W _ _ E _hL hE u _hu0 hu1 M hM k _hk σ a
  rw [genMatGUE_eq_Of, egtNGUE_eq_Of]
  exact loopGenGUEOf d L W (mE E) (spectralM_im_pos hE) E u hu1 M hM k σ a

/-- **The same at `k = 1`**, where `primRhsGUE` of a 1-loop is `0` (`Finset.Ioc 1 1 = ∅`; RBM2D
`loopGenGUE_one`, `:1134`). -/
theorem loopGenGUE_one :
    ∀ (d L W : ℕ) [NeZero L] [NeZero W] (E : ℝ), 3 ≤ L → |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
      ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian →
      ∀ (σ : Fin 1 → Bool) (a : Fin 1 → Zd d L),
        genMatGUE d L W E u M (loopOf σ a) = egtNGUE d L W E u M (loopOf σ a) := by
  intro d L W _ _ E _hL hE u _hu0 hu1 M hM σ a
  have hlen : (loopOf σ a).length = 1 := by simp [loopOf, LoopIdx.length]
  have h0 : primRhsGUE d L W (loopL d L W (blockMat d L W M) (ztOf (mE E) E u)) (loopOf σ a) =
      0 := by
    unfold primRhsGUE primBilGUE
    rw [hlen]
    simp
  rw [genMatGUE_eq_Of, egtNGUE_eq_Of,
    loopGenGUEOf d L W (mE E) (spectralM_im_pos hE) E u hu1 M hM 1 σ a, h0, zero_add]

/-! ## 10. Compiled nonempty instances

Every target at `d = 3`, `L = 3`, `W = 2` (`Idx 3 3 2` has `(W L)^d = 216` sites, `27` blocks),
`E = 0`, `u = 1/2`, the Hermitian `M = diag(2)` (and, for `loopGenGUE_one`, `loopGenGUEOf`, also
the non-scalar Hermitian `M₀ = X_{(0,1,true)} + X_{(1,0,true)}`).  `loopGenGUE` at `k = 2`
(`σ = (+,-)`, `a = (0,0)`) and `k = 3` (`(+,-,+)`, `(0,0,0)`), `loopGenGUE_one` at `(+)`, `(0)`
and (`M₀`) `(-)`, `(1)`; `loopGenGUEOf` at `m = I` (`0 < 1`) for `k = 0, 1, 2` and at the generic
`m = 1/5 + (9/10) I` for `k = 3`; `genMatGUE_eq_Of`, `egtNGUE_eq_Of` at the same data (`k = 2`).
No hypothesis is left open (every hypothesis is a scalar, size or Hermiticity condition). -/

namespace GeneratorCheck

/-- `diag(2)` on `Idx 3 3 2` is Hermitian. -/
private theorem Generator_diag_isHermitian :
    (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ)).IsHermitian :=
  Matrix.isHermitian_diagonal_iff.mpr fun _ => by simp [IsSelfAdjoint]

/-- The non-scalar Hermitian test matrix `X_{(0,1,true)} + X_{(1,0,true)}` of `Idx 3 3 2` (exactly
one of the two summands is nonzero, according to `idxKey`; `Generator_M0_apply`). -/
private noncomputable def Generator_M0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ :=
  coordinateMatrix 3 3 2 ((0 : Idx 3 3 2), (1 : Idx 3 3 2), true) +
    coordinateMatrix 3 3 2 ((1 : Idx 3 3 2), (0 : Idx 3 3 2), true)

private theorem Generator_M0_isHermitian : Generator_M0.IsHermitian :=
  (coordinateMatrix_isHermitian 3 3 2 _).add (coordinateMatrix_isHermitian 3 3 2 _)

/-- `Generator_M0` is not the zero matrix: its `(0, 1)` entry is `1`. -/
private theorem Generator_M0_apply : Generator_M0 (0 : Idx 3 3 2) (1 : Idx 3 3 2) = 1 := by
  have h01 : (0 : Idx 3 3 2) ≠ 1 := by decide
  change Xentry 3 3 2 (Pi.single ((0 : Idx 3 3 2), (1 : Idx 3 3 2), true) 1) 0 1 +
    Xentry 3 3 2 (Pi.single ((1 : Idx 3 3 2), (0 : Idx 3 3 2), true) 1) 0 1 = 1
  simp only [Xentry]
  rcases idxKey_lt_or_eq_or_lt 3 3 2 (0 : Idx 3 3 2) 1 with h | h | h
  · simp [h, h01, h01.symm]
  · exact absurd h h01
  · simp [h, not_lt.mpr h.le, h01, h01.symm]

/-- Compile check: `loopGenGUE` at `d = 3`, `L = 3`, `W = 2`, `E = 0`, `u = 1/2`, `k = 2`,
`σ = (+,-)`, `a = (0,0)`, `M = diag(2)` (as `LoopGenNCheck`, `Induction/LoopGenN.lean`). -/
example :
    genMatGUE 3 3 2 0 (1 / 2) (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ))
        (loopOf ![true, false] ![(0 : Zd 3 3), 0]) =
      primRhsGUE 3 3 2 (loopL 3 3 2 (blockMat 3 3 2 (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ)))
          (zt 0 (1 / 2))) (loopOf ![true, false] ![(0 : Zd 3 3), 0]) +
        egtNGUE 3 3 2 0 (1 / 2) (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ))
          (loopOf ![true, false] ![(0 : Zd 3 3), 0]) :=
  loopGenGUE 3 3 2 0 (by norm_num) (by norm_num) (1 / 2) (by norm_num) (by norm_num)
    (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ)) Generator_diag_isHermitian
    2 le_rfl ![true, false] ![(0 : Zd 3 3), 0]

/-- Compile check: `loopGenGUE` at the same data with `k = 3`, `σ = (+,-,+)`, `a = (0,0,0)`
(three pair cuts). -/
example :
    genMatGUE 3 3 2 0 (1 / 2) (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ))
        (loopOf ![true, false, true] ![(0 : Zd 3 3), 0, 0]) =
      primRhsGUE 3 3 2 (loopL 3 3 2 (blockMat 3 3 2 (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ)))
          (zt 0 (1 / 2))) (loopOf ![true, false, true] ![(0 : Zd 3 3), 0, 0]) +
        egtNGUE 3 3 2 0 (1 / 2) (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ))
          (loopOf ![true, false, true] ![(0 : Zd 3 3), 0, 0]) :=
  loopGenGUE 3 3 2 0 (by norm_num) (by norm_num) (1 / 2) (by norm_num) (by norm_num)
    (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ)) Generator_diag_isHermitian
    3 (by norm_num) ![true, false, true] ![(0 : Zd 3 3), 0, 0]

/-- Compile check: `loopGenGUE_one` at the same data with the 1-loop `σ = (+)`, `a = (0)`. -/
example :
    genMatGUE 3 3 2 0 (1 / 2) (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ))
        (loopOf ![true] ![(0 : Zd 3 3)]) =
      egtNGUE 3 3 2 0 (1 / 2) (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ))
        (loopOf ![true] ![(0 : Zd 3 3)]) :=
  loopGenGUE_one 3 3 2 0 (by norm_num) (by norm_num) (1 / 2) (by norm_num) (by norm_num)
    (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ)) Generator_diag_isHermitian
    ![true] ![(0 : Zd 3 3)]

/-- Compile check: `loopGenGUE_one` at the 1-loop `σ = (-)`, `a = (1)` and the non-scalar
Hermitian `M₀`. -/
example :
    genMatGUE 3 3 2 0 (1 / 2) Generator_M0 (loopOf ![false] ![(1 : Zd 3 3)]) =
      egtNGUE 3 3 2 0 (1 / 2) Generator_M0 (loopOf ![false] ![(1 : Zd 3 3)]) :=
  loopGenGUE_one 3 3 2 0 (by norm_num) (by norm_num) (1 / 2) (by norm_num) (by norm_num)
    Generator_M0 Generator_M0_isHermitian ![false] ![(1 : Zd 3 3)]

/-- Compile check: the class-P core `loopGenGUEOf` at `m = I` (`0 < Im I = 1`), `E = 0`, `u = 1/2`,
`M = diag(2)`, `k = 2`, `σ = (+,-)`, `a = (0,0)`. -/
example :
    genMatGUEOf 3 3 2 Complex.I 0 (1 / 2) (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ))
        (loopOf ![true, false] ![(0 : Zd 3 3), 0]) =
      primRhsGUE 3 3 2 (loopL 3 3 2 (blockMat 3 3 2 (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ)))
          (ztOf Complex.I 0 (1 / 2))) (loopOf ![true, false] ![(0 : Zd 3 3), 0]) +
        egtNGUEOf 3 3 2 Complex.I 0 (1 / 2) (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ))
          (loopOf ![true, false] ![(0 : Zd 3 3), 0]) :=
  loopGenGUEOf 3 3 2 Complex.I (by simp) 0 (1 / 2) (by norm_num)
    (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ)) Generator_diag_isHermitian
    2 ![true, false] ![(0 : Zd 3 3), 0]

/-- Compile check: `loopGenGUEOf` at a generic `m = 1/5 + (9/10) I` (not `mE E` for any `E`), the
non-scalar Hermitian `M₀`, `k = 3`, `σ = (+,-,+)`, `a = (0,1,2)`. -/
example :
    genMatGUEOf 3 3 2 (1 / 5 + (9 / 10) * Complex.I) 0 (1 / 2) Generator_M0
        (loopOf ![true, false, true] ![(0 : Zd 3 3), 1, 2]) =
      primRhsGUE 3 3 2 (loopL 3 3 2 (blockMat 3 3 2 Generator_M0)
          (ztOf (1 / 5 + (9 / 10) * Complex.I) 0 (1 / 2)))
          (loopOf ![true, false, true] ![(0 : Zd 3 3), 1, 2]) +
        egtNGUEOf 3 3 2 (1 / 5 + (9 / 10) * Complex.I) 0 (1 / 2) Generator_M0
          (loopOf ![true, false, true] ![(0 : Zd 3 3), 1, 2]) :=
  loopGenGUEOf 3 3 2 _ (by simp) 0 (1 / 2) (by norm_num) Generator_M0 Generator_M0_isHermitian
    3 ![true, false, true] ![(0 : Zd 3 3), 1, 2]

/-- Compile check: `loopGenGUEOf` at the empty loop (`k = 0`, both sides `0`). -/
example :
    genMatGUEOf 3 3 2 Complex.I 0 (1 / 2) (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ))
        (loopOf (![] : Fin 0 → Bool) (![] : Fin 0 → Zd 3 3)) =
      primRhsGUE 3 3 2 (loopL 3 3 2 (blockMat 3 3 2 (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ)))
          (ztOf Complex.I 0 (1 / 2))) (loopOf (![] : Fin 0 → Bool) (![] : Fin 0 → Zd 3 3)) +
        egtNGUEOf 3 3 2 Complex.I 0 (1 / 2) (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ))
          (loopOf (![] : Fin 0 → Bool) (![] : Fin 0 → Zd 3 3)) :=
  loopGenGUEOf 3 3 2 Complex.I (by simp) 0 (1 / 2) (by norm_num)
    (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ)) Generator_diag_isHermitian
    0 ![] ![]

/-- Compile check: `loopGenGUEOf` at the 1-loop (`k = 1`, `primRhsGUE` of a 1-loop is `0`). -/
example :
    genMatGUEOf 3 3 2 Complex.I 0 (1 / 2) (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ))
        (loopOf ![true] ![(0 : Zd 3 3)]) =
      primRhsGUE 3 3 2 (loopL 3 3 2 (blockMat 3 3 2 (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ)))
          (ztOf Complex.I 0 (1 / 2))) (loopOf ![true] ![(0 : Zd 3 3)]) +
        egtNGUEOf 3 3 2 Complex.I 0 (1 / 2) (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ))
          (loopOf ![true] ![(0 : Zd 3 3)]) :=
  loopGenGUEOf 3 3 2 Complex.I (by simp) 0 (1 / 2) (by norm_num)
    (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ)) Generator_diag_isHermitian
    1 ![true] ![(0 : Zd 3 3)]

/-- Compile check: `genMatGUE_eq_Of` and `egtNGUE_eq_Of` at the same data (`k = 2`). -/
example :
    genMatGUE 3 3 2 0 (1 / 2) (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ))
        (loopOf ![true, false] ![(0 : Zd 3 3), 0]) =
      genMatGUEOf 3 3 2 (mE 0) 0 (1 / 2) (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ))
        (loopOf ![true, false] ![(0 : Zd 3 3), 0]) :=
  genMatGUE_eq_Of 3 3 2 0 (1 / 2) (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ))
    (loopOf ![true, false] ![(0 : Zd 3 3), 0])

example :
    egtNGUE 3 3 2 0 (1 / 2) (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ))
        (loopOf ![true, false] ![(0 : Zd 3 3), 0]) =
      egtNGUEOf 3 3 2 (mE 0) 0 (1 / 2) (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ))
        (loopOf ![true, false] ![(0 : Zd 3 3), 0]) :=
  egtNGUE_eq_Of 3 3 2 0 (1 / 2) (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ))
    (loopOf ![true, false] ![(0 : Zd 3 3), 0])

end GeneratorCheck

end RBM.Univ.GUEPhase

end

#print axioms RBM.Univ.GUEPhase.genMatGUE_eq_Of
#print axioms RBM.Univ.GUEPhase.egtNGUE_eq_Of
#print axioms RBM.Univ.GUEPhase.loopGenGUEOf
#print axioms RBM.Univ.GUEPhase.loopGenGUE
#print axioms RBM.Univ.GUEPhase.loopGenGUE_one
