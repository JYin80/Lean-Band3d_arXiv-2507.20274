/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Loop.GLoopFlow
import RBM3D.Gauss.FineModel

/-!
# The contraction algebra of the loop hierarchy (S1-03)

Ticket T2032.  Paper: arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex` (cited
`1_2:line`): `(eq:variancematrix)` `1_2:303-305`, `(Eq:defGLoop)` `1_2:823-824`.  Port of the six
files `RBM2D/Hierarchy/Contraction{Basic,Directions,Sum,Unused,CutWords,Drift}.lean` at commit
`c9a24cf`, with the renaming rules R1-R4 of `docs/tickets/ST1-COMMON.md` (item 2): `Z2 L`
becomes `Zd d L`, `BlockIndex L W` becomes `Vtx d L W`, `W^2` becomes `W^d`, the fibre
`Fin W × Fin W` becomes `Fin (W^d)`, `Coord`, `gvar` become `CoordF`, `gvarF`, `Gsig` becomes
`Gres`, the list-based `gloop` becomes `loopL`.  The complex-valued `Svar`, `Spaper` of RBM2D
have no analogue: the real profiles `svar`, `svarF` cast to `ℂ` replace them.

Everything here is a finite-matrix identity for arbitrary matrices; no generator, expectation
or loop derivative is asserted.  The coefficient of the contraction is `W^d`
(`W^d · (W^{-d})² = W^{-d}`: two weights `W^{-d}` of `E_a`, `E_b` against one `W^{-d}` of `S`).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace RBM.Gauss

open Matrix Finset

/-! ## 1. Elementary contractions (`ContractionBasic`) -/

/-- Contract two elementary matrix directions in a cyclic trace.
`RBM2D/Hierarchy/ContractionBasic.lean:22`. -/
theorem trace_mul_single_mul_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A C : Matrix ι ι ℂ) (p q r s : ι) (c e : ℂ) :
    Matrix.trace (A * Matrix.single p q c * C * Matrix.single r s e) =
      c * e * (A s p * C q r) := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and,
    Finset.sum_ite_eq]
  ring

section Basic

variable (d L W : ℕ) (g : ℝ) [NeZero L]

/-- A block projector trace is the normalized sum of diagonal entries in that block.  The fibre
has `W^d` sites, indexed by `Fin (W^d)`.  `RBM2D/Hierarchy/ContractionBasic.lean:32`. -/
theorem trace_mul_Eblk (A : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a : Zd d L) :
    Matrix.trace (A * Eblk d L W a) =
      (((W : ℂ) ^ d)⁻¹) * ∑ α : Fin (W ^ d), A (a, α) (a, α) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Eblk, Matrix.mul_diagonal]
  rw [Fintype.sum_prod_type]
  simp only [mul_ite, mul_zero, sum_ite_irrel, sum_const_zero,
    sum_ite_eq', mem_univ, ↓reduceIte]
  rw [Finset.mul_sum]
  simp only [mul_comm]

omit [NeZero L] in
/-- The variance profile of the block-product index, entrywise, in `ℂ`:
`S_{(a,α),(b,β)} = W^{-d} S^(B)_{ab}` (`(eq:variancematrix)`, `1_2:304`). -/
private theorem contraction_svar_apply (a b : Zd d L) (α β : Fin (W ^ d)) :
    ((svar d L W g (a, α) (b, β) : ℝ) : ℂ) = ((W : ℂ) ^ d)⁻¹ * SB d L g a b := by
  rw [SB_eq_map_SBR]
  simp [svar]

/-- Collapse the site variance contraction to block traces.  The `W^d` coefficient cancels one of
the two `W^{-d}` normalizations from the block projectors, leaving the `W^{-d}` variance at site
level.  `RBM2D/Hierarchy/ContractionBasic.lean:47` (`sum_Svar_diag_mul`), with `Svar` replaced by
the cast of `svar` (paper-delta candidate T2032a). -/
theorem sum_Svar_diag_mul [NeZero W]
    (A C : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    ∑ i : Vtx d L W, ∑ j : Vtx d L W,
        ((svar d L W g i j : ℝ) : ℂ) * (A i i * C j j) =
      (W : ℂ) ^ d * ∑ a : Zd d L, ∑ b : Zd d L,
        Matrix.trace (A * Eblk d L W a) * SB d L g a b *
          Matrix.trace (C * Eblk d L W b) := by
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have expand : ∀ (c : ℂ) (f g : Fin (W ^ d) → ℂ),
      ∑ α, ∑ β, c * (f α * g β) = c * ((∑ α, f α) * (∑ β, g β)) := by
    intro c f g
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
  have split (f : Vtx d L W → ℂ) :
      ∑ i : Vtx d L W, f i =
        ∑ a : Zd d L, ∑ α : Fin (W ^ d), f (a, α) := Fintype.sum_prod_type f
  simp only [split, trace_mul_Eblk, contraction_svar_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [expand]
  field_simp

end Basic

/-! ## 2. Hermitian coordinate directions (`ContractionDirections`)

The directions are the actual coordinate matrices `coordinateMatrix` of the finite product
Gaussian model on `Z_{WL}^d`.  An oriented off-diagonal pair has independent real and imaginary
coordinates, each of variance `svarF/2`; the diagonal has one used real coordinate of variance
`svarF`.  Their trace contractions leave precisely the diagonal-entry terms needed by the block
collapse theorem.  This section is dimension-free except for the block normalization `W^{-d}`
of the `_blocks` statement. -/

section Directions

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- Entrywise definition of `coordinateMatrix` (`RBM2D/Gauss/Model.lean:280`, `rfl`). -/
private theorem contraction_coordinateMatrix_apply (c : CoordF d L W) (k l : Idx d L W) :
    coordinateMatrix d L W c k l = Xentry d L W (Pi.single c (1 : ℝ)) k l := rfl

/-- The diagonal coordinate variance is `S_ii` (`RBM2D/Gauss/Model.lean:115`; the merged copy
`fineModel_gvarF_diag` is private). -/
private theorem contraction_gvarF_diag (i : Idx d L W) (b : Bool) :
    (gvarF d L W g (i, i, b) : ℝ) = svarF d L W g i i := by
  change (if i = i then svarF d L W g i i else svarF d L W g i i / 2) = _
  simp

/-- The off-diagonal coordinate variance is `S_ij / 2` (`RBM2D/Gauss/Model.lean:121`). -/
private theorem contraction_gvarF_offDiag (i j : Idx d L W) (b : Bool) (hij : i ≠ j) :
    (gvarF d L W g (i, j, b) : ℝ) = svarF d L W g i j / 2 := by
  change (if i = j then svarF d L W g i j else svarF d L W g i j / 2) = _
  simp [hij]

/-- The real coordinate matrix for an oriented off-diagonal pair.
`RBM2D/Hierarchy/ContractionDirections.lean:26`. -/
theorem coordinateMatrix_real_eq {i j : Idx d L W}
    (hij : idxKey d L W i < idxKey d L W j) :
    coordinateMatrix d L W (i, j, true) =
      Matrix.single i j 1 + Matrix.single j i 1 := by
  ext k l
  by_cases h₁ : k = i ∧ l = j
  · rcases h₁ with ⟨rfl, rfl⟩
    have hne : k ≠ l := by
      intro he
      subst l
      exact (lt_irrefl _) hij
    simp [contraction_coordinateMatrix_apply, Xentry, hij, hne]
  · by_cases h₂ : k = j ∧ l = i
    · rcases h₂ with ⟨rfl, rfl⟩
      have hne : k ≠ l := by
        intro he
        subst l
        exact (lt_irrefl _) hij
      have hrev : ¬ idxKey d L W k < idxKey d L W l := not_lt_of_ge (le_of_lt hij)
      simp [contraction_coordinateMatrix_apply, Xentry, hij, hrev, hne]
    · have hn₁ : (k, l, true) ≠ (i, j, true) := by
        intro he
        exact h₁ ⟨congrArg Prod.fst he, congrArg (fun p => p.2.1) he⟩
      have hn₂ : (l, k, true) ≠ (i, j, true) := by
        intro he
        exact h₂ ⟨congrArg (fun p => p.2.1) he, congrArg Prod.fst he⟩
      have hr₁ : ¬(i = k ∧ j = l) := by
        rintro ⟨rfl, rfl⟩
        exact h₁ ⟨rfl, rfl⟩
      have hr₂ : ¬(j = k ∧ i = l) := by
        rintro ⟨rfl, rfl⟩
        exact h₂ ⟨rfl, rfl⟩
      simp [contraction_coordinateMatrix_apply, Xentry, hr₁, hr₂, hn₁, hn₂]

/-- The imaginary coordinate matrix for an oriented off-diagonal pair.
`RBM2D/Hierarchy/ContractionDirections.lean:61`. -/
theorem coordinateMatrix_imag_eq {i j : Idx d L W}
    (hij : idxKey d L W i < idxKey d L W j) :
    coordinateMatrix d L W (i, j, false) =
      Matrix.single i j Complex.I + Matrix.single j i (-Complex.I) := by
  ext k l
  by_cases h₁ : k = i ∧ l = j
  · rcases h₁ with ⟨rfl, rfl⟩
    have hne : k ≠ l := by
      intro he
      subst l
      exact (lt_irrefl _) hij
    simp [contraction_coordinateMatrix_apply, Xentry, hij, hne]
  · by_cases h₂ : k = j ∧ l = i
    · rcases h₂ with ⟨rfl, rfl⟩
      have hne : k ≠ l := by
        intro he
        subst l
        exact (lt_irrefl _) hij
      have hrev : ¬ idxKey d L W k < idxKey d L W l := not_lt_of_ge (le_of_lt hij)
      simp [contraction_coordinateMatrix_apply, Xentry, hij, hrev, hne]
    · have hn₁ : (k, l, false) ≠ (i, j, false) := by
        intro he
        exact h₁ ⟨congrArg Prod.fst he, congrArg (fun p => p.2.1) he⟩
      have hn₂ : (l, k, false) ≠ (i, j, false) := by
        intro he
        exact h₂ ⟨congrArg (fun p => p.2.1) he, congrArg Prod.fst he⟩
      have hr₁ : ¬(i = k ∧ j = l) := by
        rintro ⟨rfl, rfl⟩
        exact h₁ ⟨rfl, rfl⟩
      have hr₂ : ¬(j = k ∧ i = l) := by
        rintro ⟨rfl, rfl⟩
        exact h₂ ⟨rfl, rfl⟩
      simp [contraction_coordinateMatrix_apply, Xentry, hr₁, hr₂, hn₁, hn₂]

/-- Only the real diagonal coordinate acts on a diagonal matrix entry.
`RBM2D/Hierarchy/ContractionDirections.lean:96`. -/
theorem coordinateMatrix_diag_eq (i : Idx d L W) :
    coordinateMatrix d L W (i, i, true) = Matrix.single i i 1 := by
  ext k l
  by_cases h : k = i ∧ l = i
  · rcases h with ⟨rfl, rfl⟩
    simp [contraction_coordinateMatrix_apply, Xentry]
  · have hn₁ : (k, l, true) ≠ (i, i, true) := by
      intro he
      exact h ⟨congrArg Prod.fst he, congrArg (fun p => p.2.1) he⟩
    have hn₂ : (l, k, true) ≠ (i, i, true) := by
      intro he
      exact h ⟨congrArg (fun p => p.2.1) he, congrArg Prod.fst he⟩
    have hr : ¬(i = k ∧ i = l) := by
      rintro ⟨rfl, rfl⟩
      exact h ⟨rfl, rfl⟩
    simp [contraction_coordinateMatrix_apply, Xentry, hr, hn₁, hn₂]

/-- The real coordinate contributes four elementary trace contractions.
`RBM2D/Hierarchy/ContractionDirections.lean:114`. -/
theorem trace_coordinate_real (A C : Matrix (Idx d L W) (Idx d L W) ℂ)
    {i j : Idx d L W} (hij : idxKey d L W i < idxKey d L W j) :
    Matrix.trace (A * coordinateMatrix d L W (i, j, true) * C *
        coordinateMatrix d L W (i, j, true)) =
      A j i * C j i + A i i * C j j + A j j * C i i + A i j * C i j := by
  rw [coordinateMatrix_real_eq d L W hij]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add,
    trace_mul_single_mul_single]
  ring

/-- The imaginary coordinate cancels the same-orientation terms.
`RBM2D/Hierarchy/ContractionDirections.lean:125`. -/
theorem trace_coordinate_imag (A C : Matrix (Idx d L W) (Idx d L W) ℂ)
    {i j : Idx d L W} (hij : idxKey d L W i < idxKey d L W j) :
    Matrix.trace (A * coordinateMatrix d L W (i, j, false) * C *
        coordinateMatrix d L W (i, j, false)) =
      -(A j i * C j i) + A i i * C j j + A j j * C i i - A i j * C i j := by
  rw [coordinateMatrix_imag_eq d L W hij]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add,
    trace_mul_single_mul_single]
  linear_combination
    (A j i * C j i - A i i * C j j - A j j * C i i + A i j * C i j) *
      Complex.I_mul_I

/-- The diagonal real coordinate contributes one diagonal product.
`RBM2D/Hierarchy/ContractionDirections.lean:138`. -/
theorem trace_coordinate_diag (A C : Matrix (Idx d L W) (Idx d L W) ℂ)
    (i : Idx d L W) :
    Matrix.trace (A * coordinateMatrix d L W (i, i, true) * C *
        coordinateMatrix d L W (i, i, true)) = A i i * C i i := by
  rw [coordinateMatrix_diag_eq d L W i, trace_mul_single_mul_single]
  norm_num

/-- The two independent off-diagonal Gaussian coordinates have variance `svarF_ij/2` each.  Their
weighted trace contractions leave the two diagonal products, with exactly one factor of the site
variance.  `RBM2D/Hierarchy/ContractionDirections.lean:148` (`weighted_trace_coordinate_offDiag`;
`Spaper` becomes the cast of `svarF`, paper-delta candidate T2032a). -/
theorem weighted_trace_coordinate_offDiag
    (A C : Matrix (Idx d L W) (Idx d L W) ℂ)
    {i j : Idx d L W} (hij : idxKey d L W i < idxKey d L W j) :
    (((gvarF d L W g (i, j, true) : ℝ) : ℂ) *
        Matrix.trace (A * coordinateMatrix d L W (i, j, true) * C *
          coordinateMatrix d L W (i, j, true))) +
      (((gvarF d L W g (i, j, false) : ℝ) : ℂ) *
        Matrix.trace (A * coordinateMatrix d L W (i, j, false) * C *
          coordinateMatrix d L W (i, j, false))) =
      ((svarF d L W g i j : ℝ) : ℂ) * (A i i * C j j + A j j * C i i) := by
  have hne : i ≠ j := by
    intro he
    subst j
    exact (lt_irrefl _) hij
  have hv (b : Bool) : (((gvarF d L W g (i, j, b) : ℝ) : ℂ)) =
      (svarF d L W g i j : ℂ) / 2 := by
    have hr := contraction_gvarF_offDiag d L W g i j b hne
    exact_mod_cast hr
  rw [trace_coordinate_real d L W A C hij,
    trace_coordinate_imag d L W A C hij, hv true, hv false]
  ring

/-- The same contraction with its block normalization shown explicitly: each physical-site
variance is `SB_ab W^{-d}`.  `RBM2D/Hierarchy/ContractionDirections.lean:173`
(`weighted_trace_coordinate_offDiag_blocks`). -/
theorem weighted_trace_coordinate_offDiag_blocks
    (A C : Matrix (Idx d L W) (Idx d L W) ℂ)
    {i j : Idx d L W} (hij : idxKey d L W i < idxKey d L W j) :
    (((gvarF d L W g (i, j, true) : ℝ) : ℂ) *
        Matrix.trace (A * coordinateMatrix d L W (i, j, true) * C *
          coordinateMatrix d L W (i, j, true))) +
      (((gvarF d L W g (i, j, false) : ℝ) : ℂ) *
        Matrix.trace (A * coordinateMatrix d L W (i, j, false) * C *
          coordinateMatrix d L W (i, j, false))) =
      (SB d L g (split d L W i).1 (split d L W j).1 * ((W : ℂ) ^ d)⁻¹) *
        (A i i * C j j + A j j * C i i) := by
  rw [weighted_trace_coordinate_offDiag d L W g A C hij]
  rw [svarF, SB_eq_map_SBR]
  simp only [Matrix.map_apply]
  push_cast
  ring

/-- The single used diagonal Gaussian coordinate has the full site variance.
`RBM2D/Hierarchy/ContractionDirections.lean:189` (`weighted_trace_coordinate_diag`). -/
theorem weighted_trace_coordinate_diag
    (A C : Matrix (Idx d L W) (Idx d L W) ℂ) (i : Idx d L W) :
    (((gvarF d L W g (i, i, true) : ℝ) : ℂ) *
      Matrix.trace (A * coordinateMatrix d L W (i, i, true) * C *
        coordinateMatrix d L W (i, i, true))) =
      ((svarF d L W g i i : ℝ) : ℂ) * (A i i * C i i) := by
  rw [trace_coordinate_diag d L W A C i, contraction_gvarF_diag d L W g i true]

end Directions

/-! ## 3. Sum over the used coordinates (`ContractionSum`) -/

/-- An upper-triangular sum, with its transposed term, plus the diagonal is the full
ordered-pair sum.  The key is injective, so its order chooses exactly one orientation of every
distinct pair.  `RBM2D/Hierarchy/ContractionSum.lean:22` (private there too). -/
private theorem contraction_sum_orderedPairs_from_upper
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

section Sum

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- Exactly the independent coordinates read by `Xentry`: both tags for each oriented
off-diagonal pair, and the real tag on the diagonal.
`RBM2D/Hierarchy/ContractionSum.lean:94`. -/
noncomputable def usedCoords : Finset (CoordF d L W) := by
  classical
  exact Finset.univ.filter fun c =>
    idxKey d L W c.1 < idxKey d L W c.2.1 ∨
      (c.1 = c.2.1 ∧ c.2.2 = true)

/-- Summing the actual coordinate trace contractions gives the complete ordered-pair diagonal
contraction with the paper's site covariance.  `RBM2D/Hierarchy/ContractionSum.lean:102`
(`sum_usedCoords_trace`; `Spaper` becomes the cast of `svarF`, paper-delta candidate T2032a). -/
theorem sum_usedCoords_trace
    (A C : Matrix (Idx d L W) (Idx d L W) ℂ) :
    ∑ c ∈ usedCoords d L W,
        (((gvarF d L W g c : ℝ) : ℂ) *
          Matrix.trace (A * coordinateMatrix d L W c * C * coordinateMatrix d L W c)) =
      ∑ i : Idx d L W, ∑ j : Idx d L W,
        ((svarF d L W g i j : ℝ) : ℂ) * (A i i * C j j) := by
  classical
  have splitCoord (f : CoordF d L W → ℂ) :
      ∑ c : CoordF d L W, f c =
        ∑ i : Idx d L W, ∑ j : Idx d L W, ∑ b : Bool, f (i, j, b) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    exact Fintype.sum_prod_type (fun jb : Idx d L W × Bool => f (i, jb))
  unfold usedCoords
  rw [Finset.sum_filter, splitCoord]
  calc
    (∑ i : Idx d L W, ∑ j : Idx d L W, ∑ b : Bool,
      if idxKey d L W i < idxKey d L W j ∨ (i = j ∧ b = true) then
        (((gvarF d L W g (i, j, b) : ℝ) : ℂ) *
          Matrix.trace (A * coordinateMatrix d L W (i, j, b) * C *
            coordinateMatrix d L W (i, j, b))) else 0) =
      ∑ i : Idx d L W, ∑ j : Idx d L W,
        (if idxKey d L W i < idxKey d L W j then
          ((svarF d L W g i j : ℝ) : ℂ) * (A i i * C j j + A j j * C i i)
         else if i = j then ((svarF d L W g i i : ℝ) : ℂ) * (A i i * C i i) else 0) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
        · have hne : i ≠ j := by
            intro he
            subst j
            exact (lt_irrefl _) h
          simp only [h, true_or, ite_true, Fintype.sum_bool]
          simp [weighted_trace_coordinate_offDiag d L W g A C h]
        · subst j
          simp only [lt_irrefl, false_or, true_and,
            Fintype.sum_bool, ite_true, ite_false]
          simpa using weighted_trace_coordinate_diag d L W g A C i
        · have hne : i ≠ j := by
            intro he
            subst j
            exact (lt_irrefl _) h
          have hrev : ¬ idxKey d L W i < idxKey d L W j := not_lt_of_ge (le_of_lt h)
          simp [hrev, hne]
    _ = ∑ i : Idx d L W, ∑ j : Idx d L W,
          ((svarF d L W g i j : ℝ) : ℂ) * (A i i * C j j) := by
        apply contraction_sum_orderedPairs_from_upper (idxKey d L W) (idxKey_injective d L W)
          (fun i j => ((svarF d L W g i j : ℝ) : ℂ)) _ (fun i j => A i i * C j j)
        intro i j
        rw [svarF_comm d L W g i j]

/-- Relabel a physical-site matrix by the block/offset equivalence.  It is the merged `blockMat`
(`blockRelabel_eq_blockMat`, `rfl`); the name is RBM2D's, as the later tickets refer to it.
`RBM2D/Hierarchy/ContractionSum.lean:156`. -/
noncomputable def blockRelabel
    (A : Matrix (Idx d L W) (Idx d L W) ℂ) :
    Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  A.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm

theorem blockRelabel_eq_blockMat (A : Matrix (Idx d L W) (Idx d L W) ℂ) :
    blockRelabel d L W A = blockMat d L W A := rfl

/-- `RBM2D/Hierarchy/ContractionSum.lean:161`. -/
theorem blockRelabel_apply_split
    (A : Matrix (Idx d L W) (Idx d L W) ℂ) (i j : Idx d L W) :
    blockRelabel d L W A (split d L W i) (split d L W j) = A i j := by
  change A ((splitEquiv d L W).symm ((splitEquiv d L W) i))
    ((splitEquiv d L W).symm ((splitEquiv d L W) j)) = A i j
  simp

/-- The physical-site diagonal contraction is the same sum in block/offset coordinates.
`RBM2D/Hierarchy/ContractionSum.lean:170` (`sum_Spaper_diag_mul_relabel`; renamed because
`Spaper` has no analogue, paper-delta candidate T2032a). -/
theorem sum_svarF_diag_mul_relabel
    (A C : Matrix (Idx d L W) (Idx d L W) ℂ) :
    (∑ i : Idx d L W, ∑ j : Idx d L W,
      ((svarF d L W g i j : ℝ) : ℂ) * (A i i * C j j)) =
      ∑ u : Vtx d L W, ∑ v : Vtx d L W,
        ((svar d L W g u v : ℝ) : ℂ) *
          (blockRelabel d L W A u u * blockRelabel d L W C v v) := by
  let e := splitEquiv d L W
  calc
    (∑ i : Idx d L W, ∑ j : Idx d L W,
      ((svarF d L W g i j : ℝ) : ℂ) * (A i i * C j j)) =
        ∑ i : Idx d L W, ∑ v : Vtx d L W,
          ((svar d L W g (e i) v : ℝ) : ℂ) *
            (blockRelabel d L W A (e i) (e i) * blockRelabel d L W C v v) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              exact Fintype.sum_equiv e _ _ (fun j => by
                change ((svar d L W g (e i) (e j) : ℝ) : ℂ) * (A i i * C j j) =
                  ((svar d L W g (e i) (e j) : ℝ) : ℂ) *
                    (blockRelabel d L W A (e i) (e i) *
                      blockRelabel d L W C (e j) (e j))
                rw [← blockRelabel_apply_split d L W A i i,
                  ← blockRelabel_apply_split d L W C j j]
                rfl)
    _ = ∑ u : Vtx d L W, ∑ v : Vtx d L W,
          ((svar d L W g u v : ℝ) : ℂ) *
            (blockRelabel d L W A u u * blockRelabel d L W C v v) := by
              exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- Full coordinate contraction in the paper's block variables, with the dimension-correct `W^d`
coefficient.  This is a matrix identity for arbitrary `A, C`; it does not assert a generator or
loop derivative identity.  `RBM2D/Hierarchy/ContractionSum.lean:201`. -/
theorem sum_usedCoords_trace_blocks
    (A C : Matrix (Idx d L W) (Idx d L W) ℂ) :
    ∑ c ∈ usedCoords d L W,
        (((gvarF d L W g c : ℝ) : ℂ) *
          Matrix.trace (A * coordinateMatrix d L W c * C * coordinateMatrix d L W c)) =
      (W : ℂ) ^ d * ∑ a : Zd d L, ∑ b : Zd d L,
        Matrix.trace (blockRelabel d L W A * Eblk d L W a) * SB d L g a b *
          Matrix.trace (blockRelabel d L W C * Eblk d L W b) := by
  rw [sum_usedCoords_trace, sum_svarF_diag_mul_relabel]
  exact sum_Svar_diag_mul d L W g (blockRelabel d L W A) (blockRelabel d L W C)

end Sum

/-! ## 4. Unused coordinates (`ContractionUnused`)

The finite product includes lower-triangular and imaginary diagonal noise coordinates.
`Xentry` never reads them, so their `coordinateMatrix` is zero. -/

section Unused

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- The imaginary diagonal coordinate is unused by the Hermitian model.
`RBM2D/Hierarchy/ContractionUnused.lean:22`. -/
theorem coordinateMatrix_diag_imag_zero (i : Idx d L W) :
    coordinateMatrix d L W (i, i, false) = 0 := by
  ext k l
  change Xentry d L W (Pi.single (i, i, false) (1 : ℝ)) k l = 0
  unfold Xentry
  split_ifs with hkl hlk
  · have hn : (k, l, false) ≠ (i, i, false) := by
      intro he
      have hk : k = i := congrArg Prod.fst he
      have hl : l = i := congrArg (fun p => p.2.1) he
      exact (lt_irrefl _) (hk.symm ▸ hl.symm ▸ hkl)
    simp [Pi.single_eq_of_ne hn]
  · have hn : (l, k, false) ≠ (i, i, false) := by
      intro he
      have hl : l = i := congrArg Prod.fst he
      have hk : k = i := congrArg (fun p => p.2.1) he
      exact (lt_irrefl _) (hl.symm ▸ hk.symm ▸ hlk)
    simp [Pi.single_eq_of_ne hn]
  · simp

/-- A lower-triangular coordinate is unused: the model always reads the oppositely ordered
coordinate of the Hermitian pair.  `RBM2D/Hierarchy/ContractionUnused.lean:44`. -/
theorem coordinateMatrix_lower_zero {i j : Idx d L W}
    (hji : idxKey d L W j < idxKey d L W i) (b : Bool) :
    coordinateMatrix d L W (i, j, b) = 0 := by
  ext k l
  change Xentry d L W (Pi.single (i, j, b) (1 : ℝ)) k l = 0
  unfold Xentry
  split_ifs with hkl hlk
  · have hn (t : Bool) : (k, l, t) ≠ (i, j, b) := by
      intro he
      have hk : k = i := congrArg Prod.fst he
      have hl : l = j := congrArg (fun p => p.2.1) he
      have hij : idxKey d L W i < idxKey d L W j := hk.symm ▸ hl.symm ▸ hkl
      exact (not_lt_of_ge (le_of_lt hji)) hij
    simp [Pi.single_eq_of_ne (hn true), Pi.single_eq_of_ne (hn false)]
  · have hn (t : Bool) : (l, k, t) ≠ (i, j, b) := by
      intro he
      have hl : l = i := congrArg Prod.fst he
      have hk : k = j := congrArg (fun p => p.2.1) he
      have hij : idxKey d L W i < idxKey d L W j := hl.symm ▸ hk.symm ▸ hlk
      exact (not_lt_of_ge (le_of_lt hji)) hij
    simp [Pi.single_eq_of_ne (hn true), Pi.single_eq_of_ne (hn false)]
  · have hn : (k, l, true) ≠ (i, j, b) := by
      intro he
      have hk : k = i := congrArg Prod.fst he
      have hl : l = j := congrArg (fun p => p.2.1) he
      have h : idxKey d L W l < idxKey d L W k := hl ▸ hk ▸ hji
      exact hlk h
    simp [Pi.single_eq_of_ne hn]

/-- Every product coordinate omitted from `usedCoords` has zero derivative direction in `Xmat`.
`RBM2D/Hierarchy/ContractionUnused.lean:75`. -/
theorem coordinateMatrix_zero_of_not_mem_usedCoords
    (c : CoordF d L W) (hc : c ∉ usedCoords d L W) :
    coordinateMatrix d L W c = 0 := by
  rcases c with ⟨i, j, b⟩
  have hnot : ¬(idxKey d L W i < idxKey d L W j ∨
      (i = j ∧ b = true)) := by
    simpa [usedCoords] using hc
  rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
  · exact False.elim (hnot (Or.inl h))
  · subst j
    cases b with
    | false => exact coordinateMatrix_diag_imag_zero d L W i
    | true => exact False.elim (hnot (Or.inr ⟨rfl, rfl⟩))
  · exact coordinateMatrix_lower_zero d L W h b

/-- The full finite product coordinate contraction equals the contraction over the coordinates
read by `Xmat`; every omitted summand vanishes.  `RBM2D/Hierarchy/ContractionUnused.lean:92`. -/
theorem sum_allCoords_trace_eq_usedCoords
    (A C : Matrix (Idx d L W) (Idx d L W) ℂ) :
    ∑ c : CoordF d L W,
        (((gvarF d L W g c : ℝ) : ℂ) *
          Matrix.trace (A * coordinateMatrix d L W c * C * coordinateMatrix d L W c)) =
      ∑ c ∈ usedCoords d L W,
        (((gvarF d L W g c : ℝ) : ℂ) *
          Matrix.trace (A * coordinateMatrix d L W c * C * coordinateMatrix d L W c)) := by
  classical
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro c _ hc
  rw [coordinateMatrix_zero_of_not_mem_usedCoords d L W c hc]
  simp

/-- Full product-coordinate contraction in the block variables of the `d`-dimensional lattice,
with coefficient `W^d`.  `RBM2D/Hierarchy/ContractionUnused.lean:110`. -/
theorem sum_allCoords_trace_blocks
    (A C : Matrix (Idx d L W) (Idx d L W) ℂ) :
    ∑ c : CoordF d L W,
        (((gvarF d L W g c : ℝ) : ℂ) *
          Matrix.trace (A * coordinateMatrix d L W c * C * coordinateMatrix d L W c)) =
      (W : ℂ) ^ d * ∑ a : Zd d L, ∑ b : Zd d L,
        Matrix.trace (blockRelabel d L W A * Eblk d L W a) * SB d L g a b *
          Matrix.trace (blockRelabel d L W C * Eblk d L W b) := by
  rw [sum_allCoords_trace_eq_usedCoords, sum_usedCoords_trace_blocks]

end Unused

/-! ## 5. Two cut chains as the left and right `G`-loops (`ContractionCutWords`)

At two distinguished Green edges, the trace contraction has the form `trace (A B C B)`.  The
matrices `A` and `C` below are the two open chains.  Inserting a normalized block projector into
either chain closes it into the corresponding cut-and-glue loop. -/

section CutWords

variable (d L W : ℕ) (g : ℝ) [NeZero L]
variable (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)

/-- The open chain containing the original final block label, ordered for the cyclic trace
contraction.  `RBM2D/Hierarchy/ContractionCutWords.lean:26`. -/
noncomputable def cutLeftChain
    (σ₁ σ₃ : List Bool) (a₁ a₃ : List (Zd d L))
    (s t : Bool) (c : Zd d L) :
    Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  (Gres H z t * Eblk d L W c * gloopProd d L W H z ⟨σ₃, a₃⟩) *
    gloopProd d L W H z ⟨σ₁, a₁⟩ * Gres H z s

/-- The open chain between the two distinguished Green edges.
`RBM2D/Hierarchy/ContractionCutWords.lean:34`. -/
noncomputable def cutRightChain
    (σ₂ : List Bool) (a₂ : List (Zd d L))
    (s t : Bool) (a : Zd d L) :
    Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  Gres H z s * Eblk d L W a * gloopProd d L W H z ⟨σ₂, a₂⟩ * Gres H z t

/-- Closing the first chain with `E_b` gives the left cut-and-glue loop.
`RBM2D/Hierarchy/ContractionCutWords.lean:41`. -/
theorem trace_cutLeftChain_Eblk
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Zd d L))
    (s t : Bool) (a c b : Zd d L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    Matrix.trace (cutLeftChain d L W H z σ₁ σ₃ a₁ a₃ s t c * Eblk d L W b) =
      loopL d L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : Loop.LoopIdx (Zd d L)).cutGlueL
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) b) := by
  rw [gloop_cutGlueL_split d L W H z σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c b h₁ h₂]
  unfold cutLeftChain
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- Closing the second chain with `E_b` gives the right cut-and-glue loop.
`RBM2D/Hierarchy/ContractionCutWords.lean:61`. -/
theorem trace_cutRightChain_Eblk
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Zd d L))
    (s t : Bool) (a c b : Zd d L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    Matrix.trace (cutRightChain d L W H z σ₂ a₂ s t a * Eblk d L W b) =
      loopL d L W H z
        ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
            a₁ ++ a :: a₂ ++ c :: a₃⟩ : Loop.LoopIdx (Zd d L)).cutGlueR
          (σ₁.length + 1) (σ₁.length + σ₂.length + 2) b) := by
  rw [gloop_cutGlueR_split d L W H z σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c b h₁ h₂]
  simp only [cutRightChain, Matrix.mul_assoc]

/-- Pulling a block matrix back to the physical lattice and relabeling it again recovers the
original matrix.  `RBM2D/Hierarchy/ContractionCutWords.lean:75`. -/
theorem blockRelabel_submatrix_split [NeZero W]
    (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    blockRelabel d L W (M.submatrix (split d L W) (split d L W)) = M := by
  ext u v
  obtain ⟨i, rfl⟩ := (split_bijective d L W).2 u
  obtain ⟨j, rfl⟩ := (split_bijective d L W).2 v
  rw [blockRelabel_apply_split]
  rfl

/-- The full Gaussian coordinate contraction of the two open chains is the block-weighted product
of their cut-and-glue loop traces, with coefficient `W^d`.  This is a fixed matrix identity,
independent of any loop derivative or expected generator.
`RBM2D/Hierarchy/ContractionCutWords.lean:87`. -/
theorem sum_coordinate_cutChains [NeZero W]
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Zd d L))
    (s t : Bool) (a c : Zd d L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    let A := (cutLeftChain d L W H z σ₁ σ₃ a₁ a₃ s t c).submatrix
      (split d L W) (split d L W)
    let C := (cutRightChain d L W H z σ₂ a₂ s t a).submatrix
      (split d L W) (split d L W)
    ∑ γ : CoordF d L W,
        (((gvarF d L W g γ : ℝ) : ℂ) *
          Matrix.trace (A * coordinateMatrix d L W γ * C *
            coordinateMatrix d L W γ)) =
      (W : ℂ) ^ d * ∑ u : Zd d L, ∑ v : Zd d L,
        loopL d L W H z
          ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
              a₁ ++ a :: a₂ ++ c :: a₃⟩ : Loop.LoopIdx (Zd d L)).cutGlueL
            (σ₁.length + 1) (σ₁.length + σ₂.length + 2) u) *
          SB d L g u v *
        loopL d L W H z
          ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
              a₁ ++ a :: a₂ ++ c :: a₃⟩ : Loop.LoopIdx (Zd d L)).cutGlueR
            (σ₁.length + 1) (σ₁.length + σ₂.length + 2) v) := by
  dsimp only
  rw [sum_allCoords_trace_blocks d L W g]
  rw [blockRelabel_submatrix_split, blockRelabel_submatrix_split]
  congr 1
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rw [trace_cutLeftChain_Eblk d L W H z σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c u h₁ h₂,
    trace_cutRightChain_Eblk d L W H z σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c v h₁ h₂]

end CutWords

/-! ## 6. Scalar drift insertions and single-edge cut-and-glue loops (`ContractionDrift`)

At a fixed matrix and spectral parameter, summing the inserted block label replaces `E_b` by
`W^{-d} I`.  Thus a scalar identity inserted between the two copies of a Green edge is `W^d`
times the cut-and-glue loop sum.  Both the positive insertion and the negative sign from
resolvent differentiation are recorded here; no generator or expectation is asserted. -/

section Drift

variable (d L W : ℕ) [NeZero L]
variable (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)

/-- The blocks partition the identity with factor `W^{-d}`.  `RBM2D/Defs/Model.lean:83`
(`sum_Eblk`), not on `main`; private here. -/
private theorem contraction_sum_Eblk :
    ∑ a, Eblk d L W a = (((W : ℂ) ^ d)⁻¹) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) := by
  ext p q
  simp only [Matrix.sum_apply, Eblk, Matrix.diagonal_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  split_ifs with h
  · simp [Finset.sum_ite_eq]
  · simp

/-- `loopL` is the trace of `gloopProd` (`RBM2D/Hierarchy/Loops.lean:92`, `gloop`, by `rfl`). -/
private theorem contraction_loopL_eq (I : Loop.LoopIdx (Zd d L)) :
    loopL d L W H z I = Matrix.trace (gloopProd d L W H z I) := rfl

private theorem contraction_gloopProd_cons (s : Bool) (b : Zd d L)
    (σ : List Bool) (a : List (Zd d L)) :
    gloopProd d L W H z ⟨s :: σ, b :: a⟩ =
      Gres H z s * Eblk d L W b * gloopProd d L W H z ⟨σ, a⟩ := rfl

/-- `RBM2D/Hierarchy/Loops.lean:117` (`gloopProd_append`); the merged copy is private. -/
private theorem contraction_gloopProd_append {σ₁ : List Bool} {a₁ : List (Zd d L)}
    (h₁ : σ₁.length = a₁.length)
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
    simp only [List.cons_append, contraction_gloopProd_cons, ih h, Matrix.mul_assoc]

/-- `RBM2D/Hierarchy/Operations.lean:40` (`cutGlue_split`), not on `main`; private here. -/
private theorem contraction_cutGlue_split (σ₁ σ₂ : List Bool) (a₁ a₂ : List (Zd d L))
    (s : Bool) (a b : Zd d L) (h₁ : σ₁.length = a₁.length) :
    Loop.LoopIdx.cutGlue (σ₁.length + 1) b
      (⟨σ₁ ++ s :: σ₂, a₁ ++ a :: a₂⟩ : Loop.LoopIdx (Zd d L)) =
      ⟨σ₁ ++ s :: s :: σ₂, a₁ ++ b :: a :: a₂⟩ := by
  simp [Loop.LoopIdx.cutGlue, List.take_append, h₁]

/-- At any edge selected by a matching prefix, the matrix word has the literal local replacement
`G_s E_a ↦ G_s E_b G_s E_a`.  `RBM2D/Hierarchy/Operations.lean:83` (`gloopProd_cutGlue_split`),
not on `main`; private here. -/
private theorem contraction_gloopProd_cutGlue_split
    (σ₁ σ₂ : List Bool) (a₁ a₂ : List (Zd d L))
    (s : Bool) (a b : Zd d L) (h₁ : σ₁.length = a₁.length) :
    gloopProd d L W H z
      ((⟨σ₁ ++ s :: σ₂, a₁ ++ a :: a₂⟩ : Loop.LoopIdx (Zd d L)).cutGlue
        (σ₁.length + 1) b) =
      gloopProd d L W H z ⟨σ₁, a₁⟩ *
        (Gres H z s * Eblk d L W b *
          (Gres H z s * Eblk d L W a * gloopProd d L W H z ⟨σ₂, a₂⟩)) := by
  rw [contraction_cutGlue_split d L σ₁ σ₂ a₁ a₂ s a b h₁]
  rw [contraction_gloopProd_append d L W H z h₁]
  simp only [contraction_gloopProd_cons]

/-- Sum over the inserted block at a general one-based Green edge.
`RBM2D/Hierarchy/ContractionDrift.lean:26`. -/
theorem sum_gloop_cutGlue_split
    (σ₁ σ₂ : List Bool) (a₁ a₂ : List (Zd d L))
    (s : Bool) (a : Zd d L) (h₁ : σ₁.length = a₁.length) :
    ∑ b : Zd d L,
      loopL d L W H z
        ((⟨σ₁ ++ s :: σ₂, a₁ ++ a :: a₂⟩ : Loop.LoopIdx (Zd d L)).cutGlue
          (σ₁.length + 1) b) =
      (((W : ℂ) ^ d)⁻¹) *
        Matrix.trace (gloopProd d L W H z ⟨σ₁, a₁⟩ *
          (Gres H z s * (Gres H z s * Eblk d L W a *
            gloopProd d L W H z ⟨σ₂, a₂⟩))) := by
  simp_rw [contraction_loopL_eq,
    contraction_gloopProd_cutGlue_split d L W H z σ₁ σ₂ a₁ a₂ s a _ h₁]
  rw [← Matrix.trace_sum]
  simp only [Matrix.mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul,
    contraction_sum_Eblk d L W]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_smul, smul_eq_mul]

/-- A positive scalar insertion `G_s (m I) G_s` has coefficient `m W^d` relative to the sum of
single-edge cut-and-glue loops.  `RBM2D/Hierarchy/ContractionDrift.lean:45`. -/
theorem trace_scalarDrift_cutGlue_split [NeZero W]
    (σ₁ σ₂ : List Bool) (a₁ a₂ : List (Zd d L))
    (s : Bool) (a : Zd d L) (m : ℂ)
    (h₁ : σ₁.length = a₁.length) :
    Matrix.trace (gloopProd d L W H z ⟨σ₁, a₁⟩ *
      (Gres H z s * (m • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) *
        (Gres H z s * Eblk d L W a * gloopProd d L W H z ⟨σ₂, a₂⟩))) =
      (m * (W : ℂ) ^ d) *
        ∑ b : Zd d L,
          loopL d L W H z
            ((⟨σ₁ ++ s :: σ₂, a₁ ++ a :: a₂⟩ : Loop.LoopIdx (Zd d L)).cutGlue
              (σ₁.length + 1) b) := by
  rw [sum_gloop_cutGlue_split d L W H z σ₁ σ₂ a₁ a₂ s a h₁]
  have hW : (W : ℂ) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne W))
  simp only [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]
  field_simp

/-- The same identity with the negative sign contributed by differentiating an inverse matrix.
The sign is explicit; this theorem does not formalize the derivative itself.
`RBM2D/Hierarchy/ContractionDrift.lean:66`. -/
theorem neg_trace_scalarDrift_cutGlue_split [NeZero W]
    (σ₁ σ₂ : List Bool) (a₁ a₂ : List (Zd d L))
    (s : Bool) (a : Zd d L) (m : ℂ)
    (h₁ : σ₁.length = a₁.length) :
    -Matrix.trace (gloopProd d L W H z ⟨σ₁, a₁⟩ *
      (Gres H z s * (m • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) *
        (Gres H z s * Eblk d L W a * gloopProd d L W H z ⟨σ₂, a₂⟩))) =
      -(m * (W : ℂ) ^ d) *
        ∑ b : Zd d L,
          loopL d L W H z
            ((⟨σ₁ ++ s :: σ₂, a₁ ++ a :: a₂⟩ : Loop.LoopIdx (Zd d L)).cutGlue
              (σ₁.length + 1) b) := by
  rw [trace_scalarDrift_cutGlue_split d L W H z σ₁ σ₂ a₁ a₂ s a m h₁]
  ring

end Drift

/-! ## 7. Compiled nonempty instances

Every target applied at `d = 3`, `L = 3`, `W = 2`, `g = 1/2`: the fine lattice `Z_6^3` has
`(W L)^d = 216` points, the block-product index `Z_3^3 × Fin 8` also, there are `27` blocks.  The
statements are unconditional matrix identities, so no hypothesis is left open; the chain data
have two cut positions (`σ₁ = [+, -]`, `σ₂ = [-, +]`, `σ₃ = [+]`, loop length `7`), the length
hypotheses are discharged by `rfl`. -/

namespace ContractionInst

/-- A block label of `Z_3^3`. -/
private def lab (n : ℕ) : Zd 3 3 := fun i => ((n + i.val : ℕ) : ZMod 3)

/-- `sum_Svar_diag_mul` at `d = 3`, `L = 3`, `W = 2`. -/
example :
    ∑ i : Vtx 3 3 2, ∑ j : Vtx 3 3 2,
        ((svar 3 3 2 (1 / 2) i j : ℝ) : ℂ) *
          ((1 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) i i *
            (Eblk 3 3 2 (lab 1) : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) j j) =
      (2 : ℂ) ^ 3 * ∑ a : Zd 3 3, ∑ b : Zd 3 3,
        Matrix.trace ((1 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) * Eblk 3 3 2 a) * SB 3 3 (1 / 2) a b *
          Matrix.trace (Eblk 3 3 2 (lab 1) * Eblk 3 3 2 b) := by
  have h := sum_Svar_diag_mul 3 3 2 (1 / 2) (1 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ)
    (Eblk 3 3 2 (lab 1))
  exact_mod_cast h

/-- `weighted_trace_coordinate_diag` at `d = 3`, `L = 3`, `W = 2`, at the diagonal coordinate of
the point `0` of the fine lattice. -/
example :=
  weighted_trace_coordinate_diag 3 3 2 (1 / 2)
    (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) 0

/-- `sum_usedCoords_trace_blocks` at `d = 3`, `L = 3`, `W = 2`. -/
example :=
  sum_usedCoords_trace_blocks 3 3 2 (1 / 2)
    (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)

/-- `sum_allCoords_trace_blocks` at `d = 3`, `L = 3`, `W = 2` (the honest sum over all
`2 · 216²` coordinates, unused ones included). -/
example :=
  sum_allCoords_trace_blocks 3 3 2 (1 / 2)
    (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)

/-- `sum_coordinate_cutChains` at `d = 3`, `L = 3`, `W = 2`, with the two-edge cut at the edges
`k = 3`, `l = 5` of a loop of length `7`. -/
example :=
  sum_coordinate_cutChains 3 3 2 (1 / 2) (1 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I
    [true, false] [false, true] [true] [lab 4, lab 17] [lab 9, lab 22] [lab 0]
    true false (lab 5) (lab 2) rfl rfl

/-- `neg_trace_scalarDrift_cutGlue_split` at `d = 3`, `L = 3`, `W = 2`, with `m = 7/10 - i/5`. -/
example :=
  neg_trace_scalarDrift_cutGlue_split 3 3 2 (1 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I
    [true, false] [false, true] [lab 4, lab 17] [lab 9, lab 22] true (lab 5)
    ((7 : ℂ) / 10 - Complex.I / 5) rfl

end ContractionInst

end RBM.Gauss
