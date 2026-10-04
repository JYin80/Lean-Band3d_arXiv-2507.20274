/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step34Pins
import RBM3D.Induction.Step2Defs
import RBM3D.Path.QVIdentity

/-!
# The general-`n` variance proxy `QVPropagatedN` (ST2-28, ticket T2103, part 2)

Port of RBM2D `Induction/QVN.lean` at commit `c9a24cf` (cited `QVN:<line>`; 739 lines there) and of
the definitions `loopDerivN`, `QVPropagatedN` of `Induction/HierVocab.lean` (`HierVocab:479`,
`:486`), onto the merged vocabulary and in the shape of the merged `QVPropagated`
(`Path/QVIdentity.lean`, T2084; D152-D155).  Renaming rules R1-R4 of `docs/tickets/ST1-COMMON.md`;
`Z2 L → Zd d L`, `Idx L W → Idx d L W`, `BlockIndex L W → Vtx d L W`, `Gsig → Gres`,
`spectralZ → zt`, `gloop → loopL`, `Coord/gvar → CoordF/gvarF`, `SB L → SB d L g`, `W ^ 2 → W ^ d`,
`eeLoop/eeN → STeeLoop/STeeM`.

## Main results

* `RBM.Ind.loopDerivN` : the directional derivative of `𝓛_{u,σ,b}(M)` along `X` (`HierVocab:479`).
* `RBM.Ind.QVPropagatedN d` : the pin (`∀ sz n`, `g = sz.lam n`, `STeeM`, factor `k`).
* `RBM.Ind.qvPropagatedN d` : its proof.  For Hermitian `M`, a loop of length `k ≥ 2`, every sign
  vector `σ` and coefficient family `κ`,
  `Σ_c gvar_c |Σ_b κ_b ∂_c 𝓛_{σ,b}|² ≤ k · Re Σ_{b,b'} κ_b conj κ_{b'} (𝓔⊗𝓔)_{σ,b,b'}`
  (`def:CALE`, `defEOTE` `3_5:176`, `def_diffakn_k` `3_5:187`; RBM2D `QVN:622`).

## Proof (as in RBM2D, `QVN:1-40`)

* section 1 (`QVN:54-278`): the coordinate algebra
  `Σ_c gvar_c ⟨X̂_c, F⟩ conj ⟨X̂_c, G⟩ = W^d Σ S^{(B)} tr(F E G* E)`, copied (and renamed) from the
  `private` lemmas of `Path/QVIdentity.lean:430-688`, which cannot be imported;
* sections 2-3 (`QVN:280-552`): words `∏ G^{σ_i} E_{a_i}`, Leibniz
  `∂_X 𝓛_{σ,b} = -Σ_j tr(X̂ A_j(b))` with the cut chain `A_j(b)`, and the glued loop
  `STeeLoop σ b b' (j+1) β β' = tr(A_j(b) E_{β'} A_j(b')ᴴ E_β)`;
* section 4 (`QVN:553-615`): the per-cut identity `𝓔⊗𝓔 = Σ_j (cut j)` and Cauchy–Schwarz over the
  `k` cuts (`‖Σ_j P_j‖² ≤ k Σ_j ‖P_j‖²`, dimension-free).

Every helper is `private` and prefixed `QVN_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Ind

open Matrix RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Green
open scoped Matrix.Norms.L2Operator

/-! ## 0. Vocabulary and small helpers -/

section Vocab

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- The derivative of `𝓛_{u,σ,b}(M)` along a direction `X` (RBM2D `loopDerivN`,
`Induction/HierVocab.lean:479`). -/
def loopDerivN (E u : ℝ) (M X : Matrix (Idx d L W) (Idx d L W) ℂ)
    {k : ℕ} (σ : Fin k → Bool) (b : Fin k → Zd d L) : ℂ :=
  deriv (fun y : ℝ => loopL d L W (blockMat d L W (M + (y : ℂ) • X)) (zt E u) (loopOf σ b)) 0

/-- `(𝓔⊗𝓔)_{u,σ,a,a'}` of a fine matrix (`defEOTE`, `3_5:176`) at general `(d, L, W, g)`: the body of
`STeeM` (`QVN_STeeM_eq`; RBM2D `eeN`, `HierVocab:190`). -/
private def QVN_eeN (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) {m : ℕ} (σ : Fin m → Bool)
    (a a' : Fin m → Zd d L) : ℂ :=
  (W : ℂ) ^ d * ∑ k ∈ Finset.Icc 1 m, ∑ b : Zd d L, ∑ b' : Zd d L,
    SB d L g b b' *
      loopL d L W (blockMat d L W M) (zt E u) (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b')

end Vocab

section Aux

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W]

private theorem QVN_Gres_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (z : ℂ) (σ : Bool) :
    (Gres H z σ)ᴴ = Gres H z (!σ) := by
  have hH' : Hᴴ = H := hH
  cases σ with
  | true =>
    simp only [Gres, ↓reduceIte, Bool.not_true, Bool.false_eq_true,
      ← Matrix.nonsing_inv_eq_ringInverse, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH',
      Complex.star_def]
  | false =>
    simp only [Gres, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      ← Matrix.nonsing_inv_eq_ringInverse, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH',
      Complex.star_def, Complex.conj_conj]

omit [NeZero L] in
private theorem QVN_Eblk_conjTranspose (b : Zd d L) : (Eblk d L W b)ᴴ = Eblk d L W b :=
  Eblk_isHermitian b

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- The affine line `s ↦ M + s • A` has derivative `A`. -/
private theorem QVN_hasDerivAt_line {n : Type*} [Fintype n] [DecidableEq n]
    (M A : Matrix n n ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => M + (s : ℂ) • A) A t := by
  have h : HasDerivAt (fun s : ℝ => (s : ℂ) • A) A t := by
    simpa using (hasDerivAt_id t).smul_const A
  simpa using h.const_add M

end Aux

section CoordAlgebra

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W]

private theorem QVN_cm_apply (c : CoordF d L W) (k l : Idx d L W) :
    coordinateMatrix d L W c k l = Xentry d L W (Pi.single c 1) k l := rfl

private theorem QVN_cm_lt {i j : Idx d L W} (h : idxKey d L W i < idxKey d L W j)
    (b : Bool) :
    coordinateMatrix d L W (i, j, b) =
      Matrix.single i j (if b then (1 : ℂ) else Complex.I) +
        Matrix.single j i (if b then (1 : ℂ) else -Complex.I) := by
  have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
  ext k l
  simp only [QVN_cm_apply, Xentry, Matrix.add_apply, Matrix.single_apply,
    Pi.single_apply, Prod.mk.injEq]
  cases b <;> split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind

private theorem QVN_cm_diag_true (i : Idx d L W) :
    coordinateMatrix d L W (i, i, true) = Matrix.single i i (1 : ℂ) := by
  ext k l
  simp only [QVN_cm_apply, Xentry, Matrix.single_apply, Pi.single_apply, Prod.mk.injEq]
  split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind

private theorem QVN_cm_diag_false (i : Idx d L W) :
    coordinateMatrix d L W (i, i, false) = 0 := by
  ext k l
  simp only [QVN_cm_apply, Xentry, Matrix.zero_apply, Pi.single_apply, Prod.mk.injEq]
  split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind

private theorem QVN_cm_gt {i j : Idx d L W} (h : idxKey d L W j < idxKey d L W i)
    (b : Bool) :
    coordinateMatrix d L W (i, j, b) = 0 := by
  have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
  ext k l
  simp only [QVN_cm_apply, Xentry, Matrix.zero_apply, Pi.single_apply, Prod.mk.injEq]
  cases b <;> split_ifs <;> (try push_cast) <;>
    (try simp only [zero_add, add_zero, mul_zero, mul_one, sub_zero, zero_sub]) <;> grind

/-- The diagonal coordinate variance is `S_ii` (the private `fineModel_gvarF_diag` of
`Gauss/FineModel.lean:233`, re-proved). -/
private theorem QVN_gvar_diag (g : ℝ) (i : Idx d L W) (b : Bool) :
    (gvarF d L W g (i, i, b) : ℝ) = svarF d L W g i i := by
  change (if i = i then svarF d L W g i i else svarF d L W g i i / 2) = _
  simp

/-- The off-diagonal coordinate variance is `S_ij / 2` (the private `fineModel_gvarF_offDiag` of
`Gauss/FineModel.lean:241`, re-proved). -/
private theorem QVN_gvar_offDiag (g : ℝ) (i j : Idx d L W) (b : Bool) (hij : i ≠ j) :
    (gvarF d L W g (i, j, b) : ℝ) = svarF d L W g i j / 2 := by
  change (if i = j then svarF d L W g i j else svarF d L W g i j / 2) = _
  simp [hij]

/-- The pairing `Σ_{k,l} X_{kl} f_{lk}` (the trace `tr(X F)` with `F_{lk} = f l k`). -/
private def QVN_pair (X : Matrix (Idx d L W) (Idx d L W) ℂ)
    (f : Idx d L W → Idx d L W → ℂ) : ℂ :=
  ∑ k, ∑ l, X k l * f l k

private theorem QVN_pair_single (i j : Idx d L W) (x : ℂ)
    (f : Idx d L W → Idx d L W → ℂ) :
    QVN_pair (Matrix.single i j x) f = x * f j i := by
  simp only [QVN_pair, Matrix.single_apply]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro l _ hl; simp [Ne.symm hl]
    · simp
  · intro k _ hk; simp [Ne.symm hk]
  · simp

private theorem QVN_pair_add (X Y : Matrix (Idx d L W) (Idx d L W) ℂ)
    (f : Idx d L W → Idx d L W → ℂ) :
    QVN_pair (X + Y) f = QVN_pair X f + QVN_pair Y f := by
  simp only [QVN_pair, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

private theorem QVN_pair_zero (f : Idx d L W → Idx d L W → ℂ) :
    QVN_pair (0 : Matrix (Idx d L W) (Idx d L W) ℂ) f = 0 := by
  simp [QVN_pair]

/-- Sum of an ordered-pair function over the three cases of `idxKey`. -/
private theorem QVN_sum_tri (T : Idx d L W → Idx d L W → ℂ) :
    (∑ i, ∑ j, if idxKey d L W i < idxKey d L W j then T i j + T j i
      else if i = j then T i i else 0) = ∑ i, ∑ j, T i j := by
  have hpt : ∀ i j, (if idxKey d L W i < idxKey d L W j then T i j + T j i
      else if i = j then T i i else 0) =
      ((if idxKey d L W i < idxKey d L W j then T i j else 0) +
        (if idxKey d L W i < idxKey d L W j then T j i else 0)) +
        (if i = j then T i j else 0) := by
    intro i j
    rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
    · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
      simp [h, hij]
    · subst h; simp
    · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
      simp [not_lt.mpr h.le, hij]
  have hswap : (∑ i, ∑ j, if idxKey d L W i < idxKey d L W j then T j i else 0) =
      ∑ i, ∑ j, if idxKey d L W j < idxKey d L W i then T i j else 0 := Finset.sum_comm
  calc (∑ i, ∑ j, if idxKey d L W i < idxKey d L W j then T i j + T j i
        else if i = j then T i i else 0)
      = (∑ i, ∑ j, if idxKey d L W i < idxKey d L W j then T i j else 0) +
          (∑ i, ∑ j, if idxKey d L W i < idxKey d L W j then T j i else 0) +
          ∑ i, ∑ j, (if i = j then T i j else 0) := by
        simp only [hpt, Finset.sum_add_distrib]
    _ = (∑ i, ∑ j, if idxKey d L W i < idxKey d L W j then T i j else 0) +
          (∑ i, ∑ j, if idxKey d L W j < idxKey d L W i then T i j else 0) +
          ∑ i, ∑ j, (if i = j then T i j else 0) := by rw [hswap]
    _ = ∑ i, ∑ j, (((if idxKey d L W i < idxKey d L W j then T i j else 0) +
          (if idxKey d L W j < idxKey d L W i then T i j else 0)) +
          (if i = j then T i j else 0)) := by simp only [Finset.sum_add_distrib]
    _ = ∑ i, ∑ j, T i j := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
        · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
          simp [h, hij, not_lt.mpr h.le]
        · subst h; simp
        · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
          simp [h, hij, not_lt.mpr h.le]

/-- **Coordinate sum of a sesquilinear pairing.**  For every pair of kernels `f, f'`,
`Σ_c gvar_c ⟨X_c, f⟩ conj ⟨X_c, f'⟩ = Σ_{k,l} svar_{kl} f_{lk} conj f'_{lk}`. -/
private theorem QVN_coord_sum (g : ℝ) (f f' : Idx d L W → Idx d L W → ℂ) :
    ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        (QVN_pair (coordinateMatrix d L W c) f *
          (starRingEnd ℂ) (QVN_pair (coordinateMatrix d L W c) f')) =
      ∑ k, ∑ l, (svarF d L W g k l : ℂ) * (f l k * (starRingEnd ℂ) (f' l k)) := by
  have hc : ∀ F : CoordF d L W → ℂ,
      ∑ c : CoordF d L W, F c =
        ∑ i : Idx d L W, ∑ j : Idx d L W, (F (i, j, true) + F (i, j, false)) := by
    intro F
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun j _ => Fintype.sum_bool _
  rw [← QVN_sum_tri, hc]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
  · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
    rw [ite_eq_left h, QVN_cm_lt h, QVN_cm_lt h,
      QVN_gvar_offDiag g i j true hij,
      QVN_gvar_offDiag g i j false hij, svarF_comm d L W g j i]
    simp only [QVN_pair_add, QVN_pair_single, ite_true, Bool.false_eq_true,
      ite_false, map_add, map_mul, map_neg, map_one, Complex.conj_I]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  · subst h
    rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl, QVN_cm_diag_true,
      QVN_cm_diag_false, QVN_gvar_diag, QVN_gvar_diag]
    simp [QVN_pair_single, QVN_pair_zero]
  · have hij : i ≠ j := fun he => absurd (he ▸ h) (lt_irrefl _)
    rw [ite_eq_right (not_lt.mpr h.le), ite_eq_right hij, QVN_cm_gt h, QVN_cm_gt h]
    simp [QVN_pair_zero]

/-- `tr(blockMat X · A) = Σ_{k,l} X_{kl} A_{e l, e k}` with `e = splitEquiv`. -/
private theorem QVN_trace_blockMat_mul (X : Matrix (Idx d L W) (Idx d L W) ℂ)
    (A : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    Matrix.trace (blockMat d L W X * A) =
      QVN_pair X (fun l k => A (splitEquiv d L W l) (splitEquiv d L W k)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, blockMat, Matrix.submatrix_apply,
    QVN_pair]
  rw [← (splitEquiv d L W).sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← (splitEquiv d L W).sum_comp]
  simp

/-- Reordering four finite sums. -/
private theorem QVN_sum_swap4 {α β : Type*} [Fintype α] [Fintype β]
    (F : α → α → β → β → ℂ) :
    ∑ b, ∑ b', ∑ q, ∑ p, F b b' q p = ∑ q, ∑ p, ∑ b, ∑ b', F b b' q p := by
  calc ∑ b, ∑ b', ∑ q, ∑ p, F b b' q p = ∑ b, ∑ q, ∑ p, ∑ b', F b b' q p := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun q _ => Finset.sum_comm
    _ = ∑ q, ∑ p, ∑ b, ∑ b', F b b' q p := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun q _ => Finset.sum_comm

/-- `S_{xy}` of the fine lattice as `W^{-d} S^{(B)}_{[x][y]}`, in `ℂ`. -/
private theorem QVN_svarF_cast (g : ℝ) (p q : Vtx d L W) :
    (svarF d L W g ((splitEquiv d L W).symm p) ((splitEquiv d L W).symm q) : ℂ) =
      SB d L g p.1 q.1 * ((W : ℂ) ^ d)⁻¹ := by
  have h1 : svarF d L W g ((splitEquiv d L W).symm p) ((splitEquiv d L W).symm q) =
      ((W : ℝ) ^ d)⁻¹ * SBR d L g p.1 q.1 := by
    rw [svarF_eq_svar]
    have e1 : split d L W ((splitEquiv d L W).symm p) = p :=
      (splitEquiv d L W).apply_symm_apply p
    have e2 : split d L W ((splitEquiv d L W).symm q) = q :=
      (splitEquiv d L W).apply_symm_apply q
    rw [e1, e2]
    rfl
  have h2 : SB d L g p.1 q.1 = ((SBR d L g p.1 q.1 : ℝ) : ℂ) := by
    rw [SB_eq_map_SBR]; rfl
  rw [h1, h2]
  push_cast
  ring

/-- **From the fine variance to block insertions.**
`Σ_{k,l} svar_{kl} A_{e l,e k} conj B_{e l,e k} = W^d Σ_{b,b'} S^{(B)}_{bb'} tr(A E_b Bᴴ E_{b'})`. -/
private theorem QVN_svar_sum (g : ℝ) (A B : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    ∑ k, ∑ l, (svarF d L W g k l : ℂ) *
        (A (splitEquiv d L W l) (splitEquiv d L W k) *
          (starRingEnd ℂ) (B (splitEquiv d L W l) (splitEquiv d L W k))) =
      (W : ℂ) ^ d * ∑ b : Zd d L, ∑ b' : Zd d L, SB d L g b b' *
        Matrix.trace (A * Eblk d L W b * Bᴴ * Eblk d L W b') := by
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  -- the left side over block indices
  have hL : ∑ k, ∑ l, (svarF d L W g k l : ℂ) *
        (A (splitEquiv d L W l) (splitEquiv d L W k) *
          (starRingEnd ℂ) (B (splitEquiv d L W l) (splitEquiv d L W k))) =
      ∑ p : Vtx d L W, ∑ q : Vtx d L W,
        SB d L g p.1 q.1 * ((W : ℂ) ^ d)⁻¹ * (A q p * (starRingEnd ℂ) (B q p)) := by
    rw [← (splitEquiv d L W).symm.sum_comp]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← (splitEquiv d L W).symm.sum_comp]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [QVN_svarF_cast]
    simp only [Equiv.apply_symm_apply]
  have htr : ∀ b b' : Zd d L, Matrix.trace (A * Eblk d L W b * Bᴴ * Eblk d L W b') =
      ∑ q : Vtx d L W, ∑ p : Vtx d L W,
        (if p.1 = b then ((W : ℂ) ^ d)⁻¹ else 0) * (if q.1 = b' then ((W : ℂ) ^ d)⁻¹ else 0) *
          (A q p * (starRingEnd ℂ) (B q p)) := by
    intro b b'
    simp only [Matrix.trace, Matrix.diag, Eblk, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.conjTranspose_apply, mul_ite, ite_mul, mul_zero, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : q.1 = b'
    · simp only [hq, ite_true]
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hp : p.1 = b
      · simp only [hp, ite_true, RCLike.star_def]; ring
      · simp [hp]
    · simp [hq]
  have hcollapse : ∀ (x y : Vtx d L W) (C : ℂ),
      ∑ b : Zd d L, ∑ b' : Zd d L, (W : ℂ) ^ d * (SB d L g b b' *
        ((if x.1 = b then ((W : ℂ) ^ d)⁻¹ else 0) * (if y.1 = b' then ((W : ℂ) ^ d)⁻¹ else 0) *
          C)) =
        (W : ℂ) ^ d * (SB d L g x.1 y.1 * (((W : ℂ) ^ d)⁻¹ * ((W : ℂ) ^ d)⁻¹ * C)) := by
    intro x y C
    rw [Finset.sum_eq_single x.1]
    · rw [Finset.sum_eq_single y.1]
      · simp
      · intro b' _ hb'; simp [Ne.symm hb']
      · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  rw [hL]
  simp only [htr, Finset.mul_sum]
  rw [QVN_sum_swap4, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [hcollapse]
  have hWd : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ hW
  field_simp

end CoordAlgebra

/-! ## 2. Words, reversal and the glued loop -/

section Words

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W]

/-- The word `∏_{p ∈ l} G_{p.1} E_{p.2}` of a list of `(sign, label)` pairs at `(E, u, M)`. -/
private def QVN_wd (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (l : List (Bool × Zd d L)) :
    Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  l.foldr (fun p Z => greenBlk d L W E u M p.1 * Eblk d L W p.2 * Z) 1

private theorem QVN_wd_nil (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) :
    QVN_wd E u M ([] : List (Bool × Zd d L)) =
      (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) := rfl

private theorem QVN_wd_cons (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (p : Bool × Zd d L)
    (l : List (Bool × Zd d L)) :
    QVN_wd E u M (p :: l) = greenBlk d L W E u M p.1 * Eblk d L W p.2 * QVN_wd E u M l := rfl

private theorem QVN_wd_append (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (l₁ l₂ : List (Bool × Zd d L)) :
    QVN_wd E u M (l₁ ++ l₂) = QVN_wd E u M l₁ * QVN_wd E u M l₂ := by
  induction l₁ with
  | nil => simp [QVN_wd_nil]
  | cons p l ih => simp [QVN_wd_cons, ih, Matrix.mul_assoc]

private theorem QVN_greenBlk_conjTranspose (E u : ℝ) {M : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hM : M.IsHermitian) (σ : Bool) :
    (greenBlk d L W E u M σ)ᴴ = greenBlk d L W E u M (!σ) :=
  QVN_Gres_conjTranspose (hM.submatrix _) _ σ

/-- **Reverse a chain and flip its charges** (RBM1D `EEBridge.rflip`,
`RBM1D/Hierarchy/EEBridge.lean:149`, commit `c06b103`, with `ZMod L` replaced by `Zd d L`):
`QVN_rflip t l c` reads `l` backwards with every charge flipped, prefixed by the charge `t` and
closed by the label `c`. -/
private def QVN_rflip (t : Bool) : List (Bool × Zd d L) → Zd d L → List (Bool × Zd d L)
  | [], c => [(t, c)]
  | p :: l, c => QVN_rflip t l p.2 ++ [(!p.1, c)]

/-- **The conjugate-transposed chain is a chain again** (RBM1D
`Gsig_mul_conjTranspose_prodList_mul`, `RBM1D/Hierarchy/EEBridge.lean:195`, commit `c06b103`):
`G(t) · (∏ G E)ᴴ · E_c` is the word of `QVN_rflip t l c`, for Hermitian `M`. -/
private theorem QVN_wd_rflip (E u : ℝ) {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian)
    (t : Bool) (l : List (Bool × Zd d L)) (c : Zd d L) :
    greenBlk d L W E u M t * (QVN_wd E u M l)ᴴ * Eblk d L W c = QVN_wd E u M (QVN_rflip t l c) := by
  induction l generalizing c with
  | nil => simp [QVN_rflip, QVN_wd_nil, QVN_wd_cons]
  | cons p l ih =>
    rw [QVN_rflip, QVN_wd_append, ← ih p.2, QVN_wd_cons, QVN_wd_cons,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, QVN_Eblk_conjTranspose,
      QVN_greenBlk_conjTranspose E u hM]
    simp [Matrix.mul_assoc, QVN_wd_nil]

/-- `QVN_rflip` in closed form: the zip of the flipped reversed charges (led by `t`) with the
reversed labels (closed by `c`). -/
private theorem QVN_rflip_eq_zip (t : Bool) (l : List (Bool × Zd d L)) (c : Zd d L) :
    QVN_rflip t l c =
      (t :: l.reverse.map (fun p => !p.1)).zip (l.reverse.map Prod.snd ++ [c]) := by
  induction l generalizing c with
  | nil => simp [QVN_rflip]
  | cons p l ih =>
    rw [QVN_rflip, ih]
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
    rw [← List.cons_append, List.zip_append (by simp)]
    rfl

/-- Rotation of a zipped chain is the zip of the rotations. -/
private theorem QVN_rot_zip {α β : Type*} (σ : List α) (a : List β) (h : σ.length = a.length)
    (q : ℕ) :
    (σ.zip a).drop q ++ (σ.zip a).take q = (σ.drop q ++ σ.take q).zip (a.drop q ++ a.take q) := by
  rw [List.zip_append (by simp [h]), List.zip_eq_zipWith, List.drop_zipWith, List.take_zipWith]
  simp [List.zip_eq_zipWith]

/-- The charges and labels of a zipped chain, reversed (and flipped). -/
private theorem QVN_flip_zip (σ : List Bool) (a : List (Zd d L)) (h : σ.length = a.length) :
    ((σ.zip a).reverse.map (fun p => !p.1)) = σ.reverse.map not ∧
      ((σ.zip a).reverse.map Prod.snd) = a.reverse := by
  have h1 : (σ.zip a).map Prod.fst = σ := List.map_fst_zip h.le
  have h2 : (σ.zip a).map Prod.snd = a := List.map_snd_zip h.ge
  have e : (σ.zip a).map (fun p => !p.1) = σ.map not := by
    have := congrArg (List.map not) h1
    simpa [List.map_map, Function.comp_def] using this
  refine ⟨?_, ?_⟩
  · rw [List.map_reverse, e, ← List.map_reverse]
  · rw [List.map_reverse, h2]

/-- **The glued `(2n+2)`-loop as a chain** (the layout `eeLoop` of `Induction/HierVocab.lean` at
cut `q + 1`, read as pairs): the cut chain `rot_q(σ,a) · (σ_q, b')`, then the reversed and
flipped rotated chain of `a'` closed by `b`. -/
private theorem QVN_eeLoop_zip (σ : List Bool) (a a' : List (Zd d L)) (h1 : σ.length = a.length)
    (h2 : σ.length = a'.length) {q : ℕ} (hq : q < σ.length) (b b' : Zd d L) :
    (STeeLoop σ a a' (q + 1) b b').σ.zip (STeeLoop σ a a' (q + 1) b b').a =
      (((σ.zip a).drop q ++ (σ.zip a).take q) ++ [(σ[q], b')]) ++
        QVN_rflip (!σ[q]) ((σ.zip a').drop q ++ (σ.zip a').take q) b := by
  rw [QVN_rot_zip σ a h1, QVN_rot_zip σ a' h2, QVN_rflip_eq_zip]
  have hlen : (σ.drop q ++ σ.take q).length = (a'.drop q ++ a'.take q).length := by simp [h2]
  have hlen1 : (σ.drop q ++ σ.take q).length = (a.drop q ++ a.take q).length := by simp [h1]
  obtain ⟨f1, f2⟩ := QVN_flip_zip (σ.drop q ++ σ.take q) (a'.drop q ++ a'.take q) hlen
  rw [f1, f2, show [(σ[q], b')] = [σ[q]].zip [b'] from rfl, ← List.zip_append hlen1,
    ← List.zip_append (by simp only [List.length_append, List.length_singleton, hlen1])]
  simp only [STeeLoop, Nat.add_sub_cancel]
  congr 1
  · rw [List.take_succ_eq_append_getElem hq]
    simp only [List.reverse_append, List.map_append, List.map_cons, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append, List.append_assoc]
  · simp [List.reverse_append, List.append_assoc]

end Words

/-! ## 3. The Leibniz rule and the cut decomposition -/

section Deriv

open scoped Matrix.Norms.L2Operator

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W]

set_option linter.unusedDecidableInType false in
/-- The trace of a differentiable matrix path (copy of the `private` `QVIdentity_hasDerivAt_trace`
of `Path/QVIdentity.lean`). -/
private theorem QVN_hasDerivAt_trace {n : Type*} [Fintype n] [DecidableEq n]
    {f : ℝ → Matrix n n ℂ} {f' : Matrix n n ℂ} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => Matrix.trace (f s)) (Matrix.trace f') t := by
  set T : Matrix n n ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap ((Matrix.traceLinearMap n ℂ ℂ).restrictScalars ℝ)
  have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
  have := T.hasFDerivAt.comp_hasDerivAt t h
  simpa only [hT, Function.comp_def] using this

/-- `∂_y G^σ(M + yX)|_{y=0} = -G^σ X̂ G^σ` (the resolvent derivative, as in the proof of
`QVIdentity_loopDeriv_eq` of `Path/QVIdentity.lean`, for either sign). -/
private theorem QVN_hasDerivAt_greenBlk {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian)
    (X : Matrix (Idx d L W) (Idx d L W) ℂ) (σ : Bool) :
    HasDerivAt (fun y : ℝ => greenBlk d L W E u (M + (y : ℂ) • X) σ)
      (-(greenBlk d L W E u M σ * blockMat d L W X * greenBlk d L W E u M σ)) 0 := by
  have hH : (blockMat d L W M).IsHermitian := hM.submatrix _
  have hz : (zt E u).im ≠ 0 := by
    rw [spectralZ_im]
    exact (mul_pos (by linarith) (spectralM_im_pos hE)).ne'
  set Hy : ℝ → Matrix (Vtx d L W) (Vtx d L W) ℂ :=
    fun y => blockMat d L W M + (y : ℂ) • blockMat d L W X with hHy
  have hH0 : Hy 0 = blockMat d L W M := by simp [hHy]
  have hline : HasDerivAt Hy (blockMat d L W X) 0 := QVN_hasDerivAt_line _ _ 0
  have hfun : (fun y : ℝ => greenBlk d L W E u (M + (y : ℂ) • X) σ) =
      fun y => Gres (Hy y) (zt E u) σ := by
    funext y
    simp only [greenBlk, hHy]
    rfl
  rw [hfun]
  cases σ with
  | true =>
      have h := hasDerivAt_green_moving hline (hasDerivAt_const (0 : ℝ) (zt E u))
        (by rw [hH0]; exact hH) hz
      simpa [hH0, greenBlk] using h
  | false =>
      have hz' : ((starRingEnd ℂ) (zt E u)).im ≠ 0 := by simpa using hz
      have h := hasDerivAt_green_moving hline
        (hasDerivAt_const (0 : ℝ) ((starRingEnd ℂ) (zt E u))) (by rw [hH0]; exact hH) hz'
      simpa [hH0, greenBlk, Gres] using h

/-- Differentiate the first factor of the word `m`: `head (p :: m') = (-(G X̂ G) E_p) · wd m'`. -/
private def QVN_head (E u : ℝ) (M X : Matrix (Idx d L W) (Idx d L W) ℂ) :
    List (Bool × Zd d L) → Matrix (Vtx d L W) (Vtx d L W) ℂ
  | [] => 0
  | p :: m => (-(greenBlk d L W E u M p.1 * blockMat d L W X * greenBlk d L W E u M p.1) *
      Eblk d L W p.2) * QVN_wd E u M m

/-- The Leibniz sum of a word: differentiate the `q`-th factor, `q < |l|`. -/
private def QVN_wordDeriv (E u : ℝ) (M X : Matrix (Idx d L W) (Idx d L W) ℂ)
    (l : List (Bool × Zd d L)) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  ∑ q ∈ Finset.range l.length, QVN_wd E u M (l.take q) * QVN_head E u M X (l.drop q)

private theorem QVN_wordDeriv_cons (E u : ℝ) (M X : Matrix (Idx d L W) (Idx d L W) ℂ)
    (p : Bool × Zd d L) (l : List (Bool × Zd d L)) :
    QVN_wordDeriv E u M X (p :: l) = QVN_head E u M X (p :: l) +
      greenBlk d L W E u M p.1 * Eblk d L W p.2 * QVN_wordDeriv E u M X l := by
  unfold QVN_wordDeriv
  rw [List.length_cons, Finset.sum_range_succ']
  simp only [List.take_succ_cons, List.drop_succ_cons, QVN_wd_cons, List.take_zero,
    List.drop_zero, QVN_wd_nil, Matrix.one_mul, Finset.mul_sum, Matrix.mul_assoc]
  rw [add_comm]

/-- **Leibniz rule for a word** in the direction `X`. -/
private theorem QVN_hasDerivAt_wd {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) (X : Matrix (Idx d L W) (Idx d L W) ℂ)
    (l : List (Bool × Zd d L)) :
    HasDerivAt (fun y : ℝ => QVN_wd E u (M + (y : ℂ) • X) l) (QVN_wordDeriv E u M X l) 0 := by
  induction l with
  | nil =>
      have h0 : QVN_wordDeriv E u M X ([] : List (Bool × Zd d L)) = 0 := by
        simp [QVN_wordDeriv]
      rw [h0]
      simpa only [QVN_wd_nil] using
        hasDerivAt_const (0 : ℝ) (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)
  | cons p l ih =>
      have hhead := (QVN_hasDerivAt_greenBlk hE hu hM X p.1).mul_const (Eblk d L W p.2)
      have h := hhead.mul ih
      rw [QVN_wordDeriv_cons]
      have hfun : (fun y : ℝ => QVN_wd E u (M + (y : ℂ) • X) (p :: l)) =
          fun y : ℝ => greenBlk d L W E u (M + (y : ℂ) • X) p.1 * Eblk d L W p.2 *
            QVN_wd E u (M + (y : ℂ) • X) l := rfl
      rw [hfun]
      convert h using 1
      simp [QVN_head]

/-- The `q`-th Leibniz term as a pairing against the cut chain:
`tr(wd(l[:q]) · ∂_q) = -tr(X̂ · wd(l[q:] ++ l[:q]) · G^{l_q})` (cyclicity of the trace). -/
private theorem QVN_trace_term (E u : ℝ) (M X : Matrix (Idx d L W) (Idx d L W) ℂ)
    (l : List (Bool × Zd d L)) {q : ℕ} (hq : q < l.length) :
    Matrix.trace (QVN_wd E u M (l.take q) * QVN_head E u M X (l.drop q)) =
      -Matrix.trace (blockMat d L W X * (QVN_wd E u M (l.drop q ++ l.take q) *
        greenBlk d L W E u M l[q].1)) := by
  rw [List.drop_eq_getElem_cons hq, QVN_head, QVN_wd_append, QVN_wd_cons]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.trace_neg]
  congr 1
  rw [show QVN_wd E u M (l.take q) * (greenBlk d L W E u M l[q].1 * blockMat d L W X *
        greenBlk d L W E u M l[q].1 * Eblk d L W l[q].2 * QVN_wd E u M (l.drop (q + 1))) =
      (QVN_wd E u M (l.take q) * greenBlk d L W E u M l[q].1) *
        (blockMat d L W X * (greenBlk d L W E u M l[q].1 * Eblk d L W l[q].2 *
          QVN_wd E u M (l.drop (q + 1)))) by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- The cut chain of edge `j`: `A_j(b) = wd(rot_j(σ, b)) · G^{σ_j}`, where `rot_j` starts the
chain at the `j`-th factor. -/
private def QVN_cut (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) {k : ℕ} (σ : Fin k → Bool)
    (b : Fin k → Zd d L) (j : Fin k) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  QVN_wd E u M (((List.ofFn σ).zip (List.ofFn b)).drop j ++
      ((List.ofFn σ).zip (List.ofFn b)).take j) * greenBlk d L W E u M (σ j)

/-- **Leibniz decomposition of the loop derivative** (RBM1D `gradMat_loopObs`,
`RBM1D/Gauss/EETensorBound.lean:267`, commit `c06b103`, read through `loopCut_eq` of
`Hierarchy/EEBridge.lean:256`): `∂_X 𝓛_{σ,b} = -Σ_j tr(X̂ · A_j(b))`. -/
private theorem QVN_loopDerivN_eq {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) (X : Matrix (Idx d L W) (Idx d L W) ℂ)
    {k : ℕ} (σ : Fin k → Bool) (b : Fin k → Zd d L) :
    loopDerivN d L W E u M X σ b =
      ∑ j : Fin k, -Matrix.trace (blockMat d L W X * QVN_cut E u M σ b j) := by
  set l : List (Bool × Zd d L) := (List.ofFn σ).zip (List.ofFn b) with hl
  have hlen : l.length = k := by simp [hl]
  have hfun : (fun y : ℝ => loopL d L W (blockMat d L W (M + (y : ℂ) • X)) (zt E u)
      (loopOf σ b)) = fun y : ℝ => Matrix.trace (QVN_wd E u (M + (y : ℂ) • X) l) := rfl
  have hD := QVN_hasDerivAt_trace (QVN_hasDerivAt_wd hE hu hM X l)
  rw [loopDerivN, hfun, hD.deriv, QVN_wordDeriv, Matrix.trace_sum, hlen, Finset.sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [QVN_trace_term E u M X l (by omega : (j : ℕ) < l.length)]
  simp [QVN_cut, hl]

/-- **The glued `(2k+2)`-loop of the cut `j` is `tr(A_j(a) E_{β'} A_j(a')ᴴ E_β)`** (RBM1D
`glueLoop_prodList`, `RBM1D/Hierarchy/EEBridge.lean:208`, commit `c06b103`; the layout is
`eeLoop` of `Induction/HierVocab.lean`). -/
private theorem QVN_eeLoop_gloop (E u : ℝ) {M : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hM : M.IsHermitian) {k : ℕ} (σ : Fin k → Bool) (a a' : Fin k → Zd d L) (j : Fin k)
    (β β' : Zd d L) :
    loopL d L W (blockMat d L W M) (zt E u) (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') ((j : ℕ) + 1) β β') =
      Matrix.trace (QVN_cut E u M σ a j * Eblk d L W β' * (QVN_cut E u M σ a' j)ᴴ *
        Eblk d L W β) := by
  have hq : (j : ℕ) < (List.ofFn σ).length := by simp
  have hz := QVN_eeLoop_zip (L := L) (List.ofFn σ) (List.ofFn a) (List.ofFn a') (by simp)
    (by simp) hq β β'
  have hs : (List.ofFn σ)[(j : ℕ)] = σ j := by simp
  rw [hs] at hz
  have hL : loopL d L W (blockMat d L W M) (zt E u) (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') ((j : ℕ) + 1) β β') =
      Matrix.trace (QVN_wd E u M ((STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a')
        ((j : ℕ) + 1) β β').σ.zip (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a')
        ((j : ℕ) + 1) β β').a)) := rfl
  rw [hL, hz, QVN_wd_append, QVN_wd_append, ← QVN_wd_rflip E u hM]
  simp only [QVN_cut, Matrix.conjTranspose_mul, QVN_greenBlk_conjTranspose E u hM,
    QVN_wd_cons, QVN_wd_nil, Matrix.mul_one, Matrix.mul_assoc]

end Deriv

/-! ## 4. The per-cut identity and the assembly -/

section Assembly

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W]

/-- Swapping the summation labels of an `S^{(B)}`-weighted double sum (copy of the `private`
`QVIdentity_SB_swap`). -/
private theorem QVN_SB_swap (F : Zd d L → Zd d L → ℂ) :
    ∑ b : Zd d L, ∑ b' : Zd d L, SB d L g b b' * F b' b = ∑ b : Zd d L, ∑ b' : Zd d L, SB d L g b b' * F b b' := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  rw [show SB d L g b' b = SB d L g b b' from congrFun (congrFun (SB_transpose d L g) b) b']

/-- **The per-cut identity of `def:CALE`** (paper-delta #22): for two block matrices `A, A'`,
`Σ_c gvar_c ⟨X̂_c, A⟩ conj ⟨X̂_c, A'⟩ = W² Σ_{x,y} S^B_{xy} tr(A E_x A'ᴴ E_y)`, with
`⟨X̂, A⟩ = -tr(X̂ A)`. -/
private theorem QVN_cut_pair (A A' : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        (-Matrix.trace (blockMat d L W (coordinateMatrix d L W c) * A) *
          (starRingEnd ℂ) (-Matrix.trace (blockMat d L W (coordinateMatrix d L W c) * A'))) =
      (W : ℂ) ^ d * ∑ x : Zd d L, ∑ y : Zd d L, SB d L g x y *
        Matrix.trace (A * Eblk d L W x * A'ᴴ * Eblk d L W y) := by
  simp only [QVN_trace_blockMat_mul, map_neg, neg_mul_neg]
  rw [QVN_coord_sum, QVN_svar_sum]

/-- `Σ_{k' ∈ [1,n]} F k' = Σ_{j : Fin n} F (j + 1)`. -/
private theorem QVN_sum_Icc_fin (n : ℕ) (F : ℕ → ℂ) :
    ∑ k' ∈ Finset.Icc 1 n, F k' = ∑ j : Fin n, F ((j : ℕ) + 1) := by
  rw [← Finset.sum_range (fun j => F (j + 1)), Finset.range_eq_Ico, Finset.sum_Ico_add' F 0 n 1]
  rfl

/-- The `j`-th cut of `𝓔⊗𝓔`: `W² Σ_{x,y} S^B_{xy} tr(A_j(b) E_x A_j(b')ᴴ E_y)`. -/
private def QVN_Ecut (g : ℝ) (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) {k : ℕ} (σ : Fin k → Bool)
    (j : Fin k) (b b' : Fin k → Zd d L) : ℂ :=
  (W : ℂ) ^ d * ∑ x : Zd d L, ∑ y : Zd d L, SB d L g x y *
    Matrix.trace (QVN_cut E u M σ b j * Eblk d L W x * (QVN_cut E u M σ b' j)ᴴ * Eblk d L W y)

/-- **`𝓔⊗𝓔` is the sum of its `k` cuts.** -/
private theorem QVN_eeN_eq (E u : ℝ) {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian)
    {k : ℕ} (σ : Fin k → Bool) (b b' : Fin k → Zd d L) :
    QVN_eeN d L W g E u M σ b b' = ∑ j : Fin k, QVN_Ecut g E u M σ j b b' := by
  rw [QVN_eeN, QVN_sum_Icc_fin, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [QVN_Ecut]
  congr 1
  simp only [QVN_eeLoop_gloop E u hM]
  exact QVN_SB_swap (fun x y => Matrix.trace (QVN_cut E u M σ b j * Eblk d L W x *
    (QVN_cut E u M σ b' j)ᴴ * Eblk d L W y))

/-- Cauchy–Schwarz over the `k` cuts: `‖Σ_j P_j‖² ≤ k Σ_j ‖P_j‖²`. -/
private theorem QVN_norm_sum_sq_le {k : ℕ} (P : Fin k → ℂ) :
    ‖∑ j, P j‖ ^ 2 ≤ (k : ℝ) * ∑ j, ‖P j‖ ^ 2 := by
  calc ‖∑ j, P j‖ ^ 2 ≤ (∑ j, ‖P j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ ((Finset.univ : Finset (Fin k)).card : ℝ) * ∑ j, ‖P j‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    _ = (k : ℝ) * ∑ j, ‖P j‖ ^ 2 := by simp

/-- `‖x‖² = x · conj x`, as a complex identity (copy of `QVIdentity_mul_conj`). -/
private theorem QVN_mul_conj (x : ℂ) : x * (starRingEnd ℂ) x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

end Assembly

/-! ## 5. The pinned theorem -/

section Final

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W]

/-- The variance proxy at general `(d, L, W, g)`: Cauchy–Schwarz over the `k` cuts, the per-cut
identity `QVN_cut_pair` and the glued loop `QVN_eeLoop_gloop`. -/
private theorem QVN_core (E u : ℝ) (hE : |E| < 2) (hu : u < 1)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) {k : ℕ}
    (σ : Fin k → Bool) (κ : (Fin k → Zd d L) → ℂ) :
    ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) *
        ‖∑ b : Fin k → Zd d L, κ b * loopDerivN d L W E u M (coordinateMatrix d L W c) σ b‖ ^ 2 ≤
      (k : ℝ) * (∑ b : Fin k → Zd d L, ∑ b' : Fin k → Zd d L,
        κ b * (starRingEnd ℂ) (κ b') * QVN_eeN d L W g E u M σ b b').re := by
  -- the `j`-th cut of the propagated increment
  set P : Fin k → CoordF d L W → ℂ := fun j c =>
    ∑ b : Fin k → Zd d L, κ b *
      (-Matrix.trace (blockMat d L W (coordinateMatrix d L W c) * QVN_cut E u M σ b j)) with hP
  have hsplit : ∀ c : CoordF d L W,
      ∑ b : Fin k → Zd d L, κ b * loopDerivN d L W E u M (coordinateMatrix d L W c) σ b =
        ∑ j : Fin k, P j c := by
    intro c
    simp only [hP, QVN_loopDerivN_eq hE hu hM, Finset.mul_sum]
    exact Finset.sum_comm
  -- the per-cut variance identity
  have hcut : ∀ j : Fin k, ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        (P j c * (starRingEnd ℂ) (P j c)) =
      ∑ b : Fin k → Zd d L, ∑ b' : Fin k → Zd d L,
        κ b * (starRingEnd ℂ) (κ b') * QVN_Ecut g E u M σ j b b' := by
    intro j
    have hPP : ∀ c : CoordF d L W, P j c * (starRingEnd ℂ) (P j c) =
        ∑ b : Fin k → Zd d L, ∑ b' : Fin k → Zd d L, κ b * (starRingEnd ℂ) (κ b') *
          (-Matrix.trace (blockMat d L W (coordinateMatrix d L W c) * QVN_cut E u M σ b j) *
            (starRingEnd ℂ) (-Matrix.trace (blockMat d L W (coordinateMatrix d L W c) *
              QVN_cut E u M σ b' j))) := by
      intro c
      simp only [hP, map_sum, map_mul, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
      ring
    simp only [hPP, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [QVN_Ecut, ← QVN_cut_pair (QVN_cut E u M σ b j) (QVN_cut E u M σ b' j), Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hre : ∀ j : Fin k, ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) * ‖P j c‖ ^ 2 =
      (∑ b : Fin k → Zd d L, ∑ b' : Fin k → Zd d L,
        κ b * (starRingEnd ℂ) (κ b') * QVN_Ecut g E u M σ j b b').re := by
    intro j
    rw [← hcut j, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [QVN_mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp only [hsplit]
  calc ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) * ‖∑ j : Fin k, P j c‖ ^ 2
      ≤ ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) * ((k : ℝ) * ∑ j : Fin k, ‖P j c‖ ^ 2) := by
        refine Finset.sum_le_sum fun c _ => ?_
        exact mul_le_mul_of_nonneg_left (QVN_norm_sum_sq_le _) (gvarF d L W g c).2
    _ = (k : ℝ) * ∑ j : Fin k, ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) * ‖P j c‖ ^ 2 := by
        have h1 : ∀ c : CoordF d L W, (gvarF d L W g c : ℝ) * ((k : ℝ) * ∑ j : Fin k, ‖P j c‖ ^ 2) =
            (k : ℝ) * ∑ j : Fin k, (gvarF d L W g c : ℝ) * ‖P j c‖ ^ 2 := by
          intro c
          rw [← Finset.mul_sum]
          ring
        rw [Finset.sum_congr rfl fun c _ => h1 c, ← Finset.mul_sum, Finset.sum_comm]
    _ = (k : ℝ) * ∑ j : Fin k, (∑ b : Fin k → Zd d L, ∑ b' : Fin k → Zd d L,
          κ b * (starRingEnd ℂ) (κ b') * QVN_Ecut g E u M σ j b b').re := by
        simp only [hre]
    _ = (k : ℝ) * (∑ b : Fin k → Zd d L, ∑ b' : Fin k → Zd d L,
          κ b * (starRingEnd ℂ) (κ b') * QVN_eeN d L W g E u M σ b b').re := by
        congr 1
        rw [← Complex.re_sum]
        congr 1
        simp only [QVN_eeN_eq E u hM, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]



end Final

/-- **The general-`n` variance proxy `QVPropagatedN`** (`def:CALE`, `defEOTE` `3_5:176`,
`def_diffakn_k` `3_5:187`; RBM2D `QVPropagatedN`, `Induction/HierVocab.lean:486`), in the shape of
the merged `QVPropagated` (`Path/QVIdentity.lean`, D152-D155: `(𝓔⊗𝓔)` is not literally the quadratic
variation; the inequality carries the number `k` of cuts): for Hermitian `M`, a loop of length
`k ≥ 2`, every sign vector `σ` and every coefficient family `κ`,
`Σ_c gvar_c |Σ_b κ_b ∂_c 𝓛_{σ,b}|² ≤ k · Re Σ_{b,b'} κ_b conj κ_{b'} (𝓔⊗𝓔)_{σ,b,b'}`
(`STeeM`), with `∀ sz n` and `g = sz.lam n`. -/
def QVPropagatedN (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
      ∀ (k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (κ : (Fin k → Zd d (sz.L n)) → ℂ),
        ∑ c : CoordF d (sz.L n) (sz.W n), (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ) *
            ‖∑ b : Fin k → Zd d (sz.L n), κ b *
              loopDerivN d (sz.L n) (sz.W n) E u M
                (coordinateMatrix d (sz.L n) (sz.W n) c) σ b‖ ^ 2 ≤
          (k : ℝ) * (∑ b : Fin k → Zd d (sz.L n), ∑ b' : Fin k → Zd d (sz.L n),
            κ b * (starRingEnd ℂ) (κ b') * sz.STeeM n E u M σ b b').re

/-- **`qvPropagatedN`** (RBM2D `Induction/QVN.lean:622`): the variance proxy of a propagated
increment, every `d`.  Its `n = 2` analogue is the merged `qvPropagated` (`Path/QVIdentity.lean`; the
relation between the two is not proved here). -/
theorem qvPropagatedN (d : ℕ) : QVPropagatedN d := by
  intro sz n E hE u _ hu M hM k _ σ κ
  exact QVN_core (g := sz.lam n) E u hE hu hM σ κ

/-! ## Compiled nonempty instances

`qvPropagatedN 3` at the merged admissible sequence `sz0` (`RBM.Gauss.SizesInst.sz0`: `d = 3`,
`L_0 = 4`, `W_0 = 32`, `lam_0 = 1/64`), size index `0`, loops of length `k = 3`, with every
hypothesis discharged: (1) `E = 0`, `u = 1/2`, `M = 1`, `σ = (+,-,+)`, `κ ≡ 1`; (2) `E = 1/2`,
`u = 1/3`, the non-scalar Hermitian `M = X_{(0,0,true)}` (`coordinateMatrix_isHermitian`),
non-alternating signs `(+,+,-)` and the non-constant `κ_b = 1(b₀ = b₁)`. -/

section Instances

open RBM.Gauss.SizesInst

/-- **Instance 1** of `qvPropagatedN` at `sz0`, `k = 3`. -/
theorem QVN_check_sz0_one :
    ∑ c : CoordF 3 (sz0.L 0) (sz0.W 0), (gvarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) c : ℝ) *
        ‖∑ b : Fin 3 → Zd 3 (sz0.L 0), (fun _ => (1 : ℂ)) b *
          loopDerivN 3 (sz0.L 0) (sz0.W 0) 0 (1 / 2)
            (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
            (coordinateMatrix 3 (sz0.L 0) (sz0.W 0) c) ![true, false, true] b‖ ^ 2 ≤
      ((3 : ℕ) : ℝ) * (∑ b : Fin 3 → Zd 3 (sz0.L 0), ∑ b' : Fin 3 → Zd 3 (sz0.L 0),
        (fun _ => (1 : ℂ)) b * (starRingEnd ℂ) ((fun _ => (1 : ℂ)) b') *
          sz0.STeeM 0 0 (1 / 2)
            (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
            ![true, false, true] b b').re :=
  qvPropagatedN 3 sz0 0 0 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 1
    Matrix.isHermitian_one 3 (by norm_num) ![true, false, true] (fun _ => 1)

/-- **Instance 2** of `qvPropagatedN` at `sz0`, `k = 3`: non-scalar `M`, non-alternating signs,
non-constant `κ`. -/
theorem QVN_check_sz0_two :
    ∑ c : CoordF 3 (sz0.L 0) (sz0.W 0), (gvarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) c : ℝ) *
        ‖∑ b : Fin 3 → Zd 3 (sz0.L 0),
          (fun b : Fin 3 → Zd 3 (sz0.L 0) => if b 0 = b 1 then (1 : ℂ) else 0) b *
          loopDerivN 3 (sz0.L 0) (sz0.W 0) (1 / 2) (1 / 3)
            (coordinateMatrix 3 (sz0.L 0) (sz0.W 0)
              ((0 : Idx 3 (sz0.L 0) (sz0.W 0)), (0 : Idx 3 (sz0.L 0) (sz0.W 0)), true))
            (coordinateMatrix 3 (sz0.L 0) (sz0.W 0) c) ![true, true, false] b‖ ^ 2 ≤
      ((3 : ℕ) : ℝ) * (∑ b : Fin 3 → Zd 3 (sz0.L 0), ∑ b' : Fin 3 → Zd 3 (sz0.L 0),
        (fun b : Fin 3 → Zd 3 (sz0.L 0) => if b 0 = b 1 then (1 : ℂ) else 0) b *
          (starRingEnd ℂ) ((fun b : Fin 3 → Zd 3 (sz0.L 0) => if b 0 = b 1 then (1 : ℂ) else 0) b') *
          sz0.STeeM 0 (1 / 2) (1 / 3)
            (coordinateMatrix 3 (sz0.L 0) (sz0.W 0)
              ((0 : Idx 3 (sz0.L 0) (sz0.W 0)), (0 : Idx 3 (sz0.L 0) (sz0.W 0)), true))
            ![true, true, false] b b').re :=
  qvPropagatedN 3 sz0 0 (1 / 2) (by norm_num [abs_of_pos]) (1 / 3) (by norm_num) (by norm_num)
    (coordinateMatrix 3 (sz0.L 0) (sz0.W 0)
      ((0 : Idx 3 (sz0.L 0) (sz0.W 0)), (0 : Idx 3 (sz0.L 0) (sz0.W 0)), true))
    (coordinateMatrix_isHermitian 3 (sz0.L 0) (sz0.W 0) _) 3 (by norm_num) ![true, true, false]
    (fun b => if b 0 = b 1 then 1 else 0)

end Instances

end RBM.Ind

end

#print axioms RBM.Ind.qvPropagatedN
#print axioms RBM.Ind.loopDerivN
