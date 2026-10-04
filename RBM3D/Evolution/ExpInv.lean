/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step5Pins
import RBM3D.Gauss.FineModel

/-!
# Translation and reflection invariance of `𝔼 𝓛^{(2)}` (the pin `STExpInv`, ticket T2155)

Paper: `paper/tex/3_5_Loop_Hierarchy.tex:2196-2200` ("by the translation invariance and symmetry
of our model on the block level"), cited `3_5:line`.

**Target** (`RBM.Gauss.Sizes.stExpInv_holds d : STExpInv d`): the merged pin
(`Induction/Step5Pins.lean`, `STExpInv`) verbatim, proved.  The route is that of RBM2D
`Evolution/MLExpInv.lean` at `c9a24cf` (§1-§4), `Z2 L` replaced by `Zd d L`, `svar`/`gvar`/`P` by
`svarF`/`gvarF`/`PF`, with `𝔼 𝓛^{(2)}` only (no `𝒦`, no `Θ`, no drift tensors, hence `|E| < 2`
and `0 ≤ u < 1` are not used).

1. §1: a bijection `T` of `Z_L^d` is an *automorphism* of `S^{(B)}(g)` if `SBR (T a) (T b) = SBR a b`
   (`SBR`, `Propagator/Props4.lean:48`); translations (`add_sub_add_right_eq_sub`) and the
   negation (`sbKernelR_neg`, `Defs/Block.lean:84`) are.
2. §2: the lift `φ = split⁻¹ ∘ (T × id) ∘ split` of `T` to the fine lattice preserves `svarF`;
   `blockMat`, `Gres`, `Eblk`, the trace, `loopM` and `loopFine` are equivariant:
   `loopFine (M_{φ,φ}) z σ b = loopFine M z σ (T ∘ b)`.
3. §3: `Xentry` is oriented by `idxKey`; for a bijection `φ` preserving `svarF` the coordinate
   bijection `π` and the sign flips of the imaginary coordinates of reversed pairs give
   `Xmat (Φω) = (Xmat ω)_{φ,φ}` and `gvarF ∘ π = gvarF`.
4. §4: `Φ` extends to a measure-preserving measurable equivalence of the common sample space
   `SeqΩ sz` (identity on the sizes `m ≠ n`), so `∫ F(H_u) d seqP` is `Φ`-invariant for every `F`
   (`MeasurePreserving.integral_comp'`: no measurability of `F` is needed).
5. §5: `stExpInv_holds`; §6: the compiled instances.

All helpers are `private`, prefixed `expInv_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss

/-! ## 1. Automorphisms of `S^{(B)}` -/

section Aut

variable {d L : ℕ} [NeZero L] (g : ℝ)

/-- A bijection of `Z_L^d` preserving the kernel `SBR` (an automorphism of `S^{(B)}(g)`). -/
private def expInv_Aut (T : Zd d L ≃ Zd d L) : Prop :=
  ∀ a b : Zd d L, SBR d L g (T a) (T b) = SBR d L g a b

private theorem expInv_Aut_addRight (c : Zd d L) : expInv_Aut g (Equiv.addRight c) := by
  intro a b
  simp only [SBR, Matrix.of_apply, Equiv.coe_addRight, add_sub_add_right_eq_sub]

private theorem expInv_Aut_neg : expInv_Aut g (Equiv.neg (Zd d L)) := by
  intro a b
  simp only [SBR, Matrix.of_apply, Equiv.neg_apply, neg_sub_neg]
  rw [show b - a = -(a - b) from (neg_sub a b).symm, sbKernelR_neg]

private theorem expInv_Aut_refl : expInv_Aut g (Equiv.refl (Zd d L)) := fun _ _ => rfl

end Aut

/-! ## 2. The relabelling of the fine lattice and the equivariance of the loops -/

section Mat

variable {d L : ℕ} [NeZero L] (W : ℕ) [NeZero W]

/-- `(a, o) ↦ (T a, o)` on block labels and offsets. -/
private def expInv_psi (T : Zd d L ≃ Zd d L) : Vtx d L W ≃ Vtx d L W :=
  Equiv.prodCongr T (Equiv.refl _)

/-- The relabelling of the fine lattice `Z_{WL}^d` that moves the block label by `T` and keeps the
offset. -/
private def expInv_phi (T : Zd d L ≃ Zd d L) : Idx d L W ≃ Idx d L W :=
  ((splitEquiv d L W).trans (expInv_psi W T)).trans (splitEquiv d L W).symm

private theorem expInv_split_phi (T : Zd d L ≃ Zd d L) (i : Idx d L W) :
    split d L W (expInv_phi W T i) = expInv_psi W T (split d L W i) := by
  have h : splitEquiv d L W (expInv_phi W T i) = expInv_psi W T (splitEquiv d L W i) := by
    simp [expInv_phi]
  exact h

/-- The variance profile `S_ij` is invariant under the relabelling. -/
private theorem expInv_svarF_phi {g : ℝ} {T : Zd d L ≃ Zd d L} (hT : expInv_Aut g T)
    (i j : Idx d L W) :
    svarF d L W g (expInv_phi W T i) (expInv_phi W T j) = svarF d L W g i j := by
  have hi : (split d L W (expInv_phi W T i)).1 = T (split d L W i).1 :=
    congrArg Prod.fst (expInv_split_phi W T i)
  have hj : (split d L W (expInv_phi W T j)).1 = T (split d L W j).1 :=
    congrArg Prod.fst (expInv_split_phi W T j)
  unfold svarF
  rw [hi, hj, hT]

private theorem expInv_blockMat_submatrix (T : Zd d L ≃ Zd d L)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) :
    blockMat d L W (M.submatrix (expInv_phi W T) (expInv_phi W T)) =
      (blockMat d L W M).submatrix (expInv_psi W T) (expInv_psi W T) := by
  unfold blockMat
  rw [Matrix.submatrix_submatrix, Matrix.submatrix_submatrix]
  have h : ⇑(expInv_phi W T) ∘ ⇑(splitEquiv d L W).symm =
      ⇑(splitEquiv d L W).symm ∘ ⇑(expInv_psi W T) := by
    funext b
    simp [expInv_phi]
  rw [h]

private theorem expInv_Gres_submatrix (T : Zd d L ≃ Zd d L)
    (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (s : Bool) :
    Gres (H.submatrix (expInv_psi W T) (expInv_psi W T)) z s =
      (Gres H z s).submatrix (expInv_psi W T) (expInv_psi W T) := by
  unfold Gres
  generalize (if s then z else (starRingEnd ℂ) z) = w
  have h : H.submatrix (expInv_psi W T) (expInv_psi W T) -
      w • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
      (H - w • 1).submatrix (expInv_psi W T) (expInv_psi W T) := by
    simp [Matrix.submatrix_sub, Matrix.submatrix_smul]
  rw [h, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.inv_submatrix_equiv]

private theorem expInv_Eblk_submatrix (T : Zd d L ≃ Zd d L) (a : Zd d L) :
    (Eblk d L W (T a)).submatrix (expInv_psi W T) (expInv_psi W T) = Eblk d L W a := by
  unfold Eblk
  rw [Matrix.submatrix_diagonal_equiv]
  congr 1
  funext p
  simp [expInv_psi]

private theorem expInv_trace_submatrix {m : Type*} [Fintype m] (e : m ≃ m) (A : Matrix m m ℂ) :
    Matrix.trace (A.submatrix e e) = Matrix.trace A := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e (fun i => A i i)

private theorem expInv_prod_submatrix {m : Type*} [Fintype m] [DecidableEq m] (e : m ≃ m)
    (l : List (Matrix m m ℂ)) :
    (l.map fun A => A.submatrix e e).prod = l.prod.submatrix e e := by
  induction l with
  | nil => simp
  | cons A l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih, Matrix.submatrix_mul_equiv]

/-- The loop of a relabelled block matrix: `loopM (H_{ψ,ψ}) z σ b = loopM H z σ (T ∘ b)`. -/
private theorem expInv_loopM_submatrix {k : ℕ} (T : Zd d L ≃ Zd d L)
    (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (σ : Fin k → Bool) (b : Fin k → Zd d L) :
    loopM d L W (H.submatrix (expInv_psi W T) (expInv_psi W T)) z σ b =
      loopM d L W H z σ (fun i => T (b i)) := by
  unfold loopM
  have h : (List.ofFn fun i => Gres (H.submatrix (expInv_psi W T) (expInv_psi W T)) z (σ i) *
        Eblk d L W (b i)) =
      (List.ofFn fun i => Gres H z (σ i) * Eblk d L W (T (b i))).map
        (fun A => A.submatrix (expInv_psi W T) (expInv_psi W T)) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    simp only [Function.comp_apply]
    rw [← expInv_Eblk_submatrix W T (b i), expInv_Gres_submatrix, Matrix.submatrix_mul_equiv]
  rw [h, expInv_prod_submatrix, expInv_trace_submatrix]

/-- `𝓛_{σ,b}(M_{φ,φ}) = 𝓛_{σ,T b}(M)`. -/
private theorem expInv_loopFine_submatrix {k : ℕ} (T : Zd d L ≃ Zd d L)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) (σ : Fin k → Bool) (b : Fin k → Zd d L) :
    loopFine d L W (M.submatrix (expInv_phi W T) (expInv_phi W T)) z σ b =
      loopFine d L W M z σ (fun i => T (b i)) := by
  unfold loopFine
  rw [expInv_blockMat_submatrix, expInv_loopM_submatrix]

end Mat

/-! ## 3. The coordinate map of the Gaussian sample space

For a bijection `φ` of the fine lattice with `S_{φi,φj} = S_{ij}`, the coordinates
`(i,j,b) ↦ s(i,j,b) ω(π(i,j,b))` (a coordinate bijection `π` and sign flips `s`) give a
sample `Φω` with `X(Φω) = X(ω)_{φ,φ}` (the orientation of `Xentry` by `idxKey` is the only
obstruction; `π` swaps the pair where `φ` reverses the orientation, and the imaginary coordinate
changes sign there). -/

section Coord

variable {d L W : ℕ} [NeZero L] [NeZero W] (g : ℝ)

omit [NeZero L] in
/-- The diagonal coordinate variance is `S_ii` (the private `fineModel_gvarF_diag`, `Gauss/FineModel.lean`). -/
private theorem expInv_gvarF_diag (i : Idx d L W) (b : Bool) :
    (gvarF d L W g (i, i, b) : ℝ) = svarF d L W g i i := by
  change (if i = i then svarF d L W g i i else svarF d L W g i i / 2) = _
  simp

omit [NeZero L] in
/-- The off-diagonal coordinate variance is `S_ij / 2`. -/
private theorem expInv_gvarF_offDiag (i j : Idx d L W) (b : Bool) (hij : i ≠ j) :
    (gvarF d L W g (i, j, b) : ℝ) = svarF d L W g i j / 2 := by
  change (if i = j then svarF d L W g i j else svarF d L W g i j / 2) = _
  simp [hij]

/-- `φ` keeps the `idxKey`-orientation of the pair `(i,j)`. -/
private def expInv_pres (φ : Idx d L W ≃ Idx d L W) (i j : Idx d L W) : Prop :=
  idxKey d L W i < idxKey d L W j ↔ idxKey d L W (φ i) < idxKey d L W (φ j)

private instance expInv_pres_dec (φ : Idx d L W ≃ Idx d L W) (i j : Idx d L W) :
    Decidable (expInv_pres φ i j) := by
  unfold expInv_pres; infer_instance

private theorem expInv_pres_self (φ : Idx d L W ≃ Idx d L W) (i : Idx d L W) : expInv_pres φ i i := by
  unfold expInv_pres; simp

private theorem expInv_pres_comm (φ : Idx d L W ≃ Idx d L W) {i j : Idx d L W}
    (h : expInv_pres φ i j) : expInv_pres φ j i := by
  by_cases hij : i = j
  · subst hij; exact h
  · have hk : idxKey d L W i ≠ idxKey d L W j := fun e => hij (idxKey_injective d L W e)
    have hk' : idxKey d L W (φ i) ≠ idxKey d L W (φ j) := fun e =>
      hij (φ.injective (idxKey_injective d L W e))
    unfold expInv_pres at h ⊢
    omega

/-- The coordinate map: `(i,j,b) ↦ (φi, φj, b)` if `φ` keeps the orientation of `(i,j)`, else
`(φj, φi, b)`. -/
private def expInv_piFun (φ : Idx d L W ≃ Idx d L W) (c : CoordF d L W) : CoordF d L W :=
  if expInv_pres φ c.1 c.2.1 then (φ c.1, φ c.2.1, c.2.2) else (φ c.2.1, φ c.1, c.2.2)

private theorem expInv_piFun_pos (φ : Idx d L W ≃ Idx d L W) {i j : Idx d L W}
    (h : expInv_pres φ i j) (b : Bool) : expInv_piFun φ (i, j, b) = (φ i, φ j, b) := by
  simp [expInv_piFun, h]

private theorem expInv_piFun_neg (φ : Idx d L W ≃ Idx d L W) {i j : Idx d L W}
    (h : ¬ expInv_pres φ i j) (b : Bool) : expInv_piFun φ (i, j, b) = (φ j, φ i, b) := by
  simp [expInv_piFun, h]

private theorem expInv_piFun_injective (φ : Idx d L W ≃ Idx d L W) :
    Function.Injective (expInv_piFun φ) := by
  rintro ⟨i, j, b⟩ ⟨i', j', b'⟩ h
  by_cases h1 : expInv_pres φ i j <;> by_cases h2 : expInv_pres φ i' j'
  · rw [expInv_piFun_pos φ h1, expInv_piFun_pos φ h2] at h
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h; rfl
  · rw [expInv_piFun_pos φ h1, expInv_piFun_neg φ h2] at h
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
    obtain ⟨e1, e2, e3⟩ := h
    subst e1 e2
    exact absurd (expInv_pres_comm φ h1) h2
  · rw [expInv_piFun_neg φ h1, expInv_piFun_pos φ h2] at h
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
    obtain ⟨e1, e2, e3⟩ := h
    subst e1 e2
    exact absurd (expInv_pres_comm φ h2) h1
  · rw [expInv_piFun_neg φ h1, expInv_piFun_neg φ h2] at h
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h; rfl

/-- The coordinate bijection. -/
private def expInv_pi (φ : Idx d L W ≃ Idx d L W) : CoordF d L W ≃ CoordF d L W :=
  Equiv.ofBijective (expInv_piFun φ)
    (Finite.injective_iff_bijective.mp (expInv_piFun_injective φ))

private theorem expInv_pi_apply (φ : Idx d L W ≃ Idx d L W) (c : CoordF d L W) :
    expInv_pi φ c = expInv_piFun φ c := rfl

/-- The coordinate variance is invariant under the coordinate bijection. -/
private theorem expInv_gvar_pi (φ : Idx d L W ≃ Idx d L W)
    (hφ : ∀ i j, svarF d L W g (φ i) (φ j) = svarF d L W g i j) (c : CoordF d L W) :
    gvarF d L W g (expInv_pi φ c) = gvarF d L W g c := by
  apply NNReal.eq
  obtain ⟨i, j, b⟩ := c
  rw [expInv_pi_apply]
  by_cases hij : i = j
  · subst hij
    rw [expInv_piFun_pos φ (expInv_pres_self φ i), expInv_gvarF_diag, expInv_gvarF_diag, hφ]
  · have hne : φ i ≠ φ j := fun h => hij (φ.injective h)
    by_cases h : expInv_pres φ i j
    · rw [expInv_piFun_pos φ h, expInv_gvarF_offDiag g _ _ _ hne, expInv_gvarF_offDiag g _ _ _ hij, hφ]
    · rw [expInv_piFun_neg φ h, expInv_gvarF_offDiag g _ _ _ hne.symm, expInv_gvarF_offDiag g _ _ _ hij,
        hφ, svarF_comm d L W g j i]

/-- The coordinates whose sign is reversed: `(i,j,false)` with reversed orientation. -/
private def expInv_flip (φ : Idx d L W ≃ Idx d L W) (c : CoordF d L W) : Prop :=
  ¬ expInv_pres φ c.1 c.2.1 ∧ c.2.2 = false

private instance expInv_flip_dec (φ : Idx d L W ≃ Idx d L W) (c : CoordF d L W) :
    Decidable (expInv_flip φ c) := by
  unfold expInv_flip; infer_instance

/-- The transformed sample `Φω`. -/
private def expInv_Phi (φ : Idx d L W ≃ Idx d L W) (ω : Ω d L W) : Ω d L W := fun c =>
  if expInv_flip φ c then -ω (expInv_pi φ c) else ω (expInv_pi φ c)

private theorem expInv_Phi_true (φ : Idx d L W ≃ Idx d L W) (ω : Ω d L W) (i j : Idx d L W) :
    expInv_Phi φ ω (i, j, true) =
      if expInv_pres φ i j then ω (φ i, φ j, true) else ω (φ j, φ i, true) := by
  have hf : ¬ expInv_flip φ (i, j, true) := fun h => by
    have := h.2; simp at this
  unfold expInv_Phi
  rw [ite_eq_right hf, expInv_pi_apply]
  by_cases h : expInv_pres φ i j
  · rw [expInv_piFun_pos φ h, ite_eq_left h]
  · rw [expInv_piFun_neg φ h, ite_eq_right h]

private theorem expInv_Phi_false (φ : Idx d L W ≃ Idx d L W) (ω : Ω d L W) (i j : Idx d L W) :
    expInv_Phi φ ω (i, j, false) =
      if expInv_pres φ i j then ω (φ i, φ j, false) else -ω (φ j, φ i, false) := by
  unfold expInv_Phi
  rw [expInv_pi_apply]
  by_cases h : expInv_pres φ i j
  · have hf : ¬ expInv_flip φ (i, j, false) := fun hh => hh.1 h
    rw [ite_eq_right hf, expInv_piFun_pos φ h, ite_eq_left h]
  · have hf : expInv_flip φ (i, j, false) := ⟨h, rfl⟩
    rw [ite_eq_left hf, expInv_piFun_neg φ h, ite_eq_right h]

/-- The oriented matrix entries of `Φω` are the entries of `ω` at the relabelled indices. -/
private theorem expInv_Xentry (φ : Idx d L W ≃ Idx d L W) (ω : Ω d L W) (i j : Idx d L W) :
    Xentry d L W (expInv_Phi φ ω) i j = Xentry d L W ω (φ i) (φ j) := by
  have hinj : ∀ x y : Idx d L W, idxKey d L W x = idxKey d L W y → x = y :=
    fun x y h => idxKey_injective d L W h
  unfold Xentry
  rcases lt_trichotomy (idxKey d L W i) (idxKey d L W j) with hij | hij | hij
  · rcases lt_trichotomy (idxKey d L W (φ i)) (idxKey d L W (φ j)) with h' | h' | h'
    · have hp : expInv_pres φ i j := by unfold expInv_pres; omega
      rw [ite_eq_left hij, ite_eq_left h', expInv_Phi_true, expInv_Phi_false,
        ite_eq_left hp, ite_eq_left hp]
    · exfalso
      have h1 : φ i = φ j := hinj _ _ h'
      have h2 := φ.injective h1
      subst h2
      exact lt_irrefl _ hij
    · have hp : ¬ expInv_pres φ i j := by unfold expInv_pres; omega
      rw [ite_eq_left hij, ite_eq_right (not_lt.2 h'.le), ite_eq_left h', expInv_Phi_true,
        expInv_Phi_false, ite_eq_right hp, ite_eq_right hp]
      push_cast; ring
  · have hi : i = j := hinj _ _ hij
    subst hi
    have hp := expInv_pres_self φ i
    rw [ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _),
      ite_eq_right (lt_irrefl _), expInv_Phi_true, ite_eq_left hp]
  · rcases lt_trichotomy (idxKey d L W (φ i)) (idxKey d L W (φ j)) with h' | h' | h'
    · have hp : ¬ expInv_pres φ j i := by unfold expInv_pres; omega
      rw [ite_eq_right (not_lt.2 hij.le), ite_eq_left hij, ite_eq_left h', expInv_Phi_true,
        expInv_Phi_false, ite_eq_right hp, ite_eq_right hp]
      push_cast; ring
    · exfalso
      have h1 : φ i = φ j := hinj _ _ h'
      have h2 := φ.injective h1
      subst h2
      exact lt_irrefl _ hij
    · have hp : expInv_pres φ j i := by unfold expInv_pres; omega
      rw [ite_eq_right (not_lt.2 hij.le), ite_eq_left hij, ite_eq_right (not_lt.2 h'.le),
        ite_eq_left h', expInv_Phi_true, expInv_Phi_false, ite_eq_left hp, ite_eq_left hp]

/-- `X(Φω) = X(ω)_{φ,φ}` as matrices. -/
private theorem expInv_Xmat (φ : Idx d L W ≃ Idx d L W) (ω : Ω d L W) :
    Xmat d L W (expInv_Phi φ ω) = (Xmat d L W ω).submatrix φ φ := by
  ext i j
  exact expInv_Xentry φ ω i j

end Coord

/-! ## 4. The measure-preserving relabelling of the common sample space -/

namespace Sizes

section Seq

variable {d : ℕ} (sz : Sizes d)

/-- **The change of variables**: for a family of bijections `φ m` of the fine lattices with
`S_{φi,φj} = S_{ij}`, there is a measure-preserving measurable equivalence `Φ` of the common sample
space `SeqΩ sz` (`seqP sz`, the product of independent centred Gaussians) whose size-`m` slice is
`expInv_Phi (φ m)`.  It is the composition of the reindexing of the coordinates by the
bijection `Ψ` (`π m` on the `m`-th block of coordinates) and of the sign flips
(`gaussianReal 0 v` is symmetric). -/
private theorem expInv_seq (φ : ∀ m, Idx d (sz.L m) (sz.W m) ≃ Idx d (sz.L m) (sz.W m))
    (hφ : ∀ m i j, svarF d (sz.L m) (sz.W m) (sz.lam m) (φ m i) (φ m j) =
      svarF d (sz.L m) (sz.W m) (sz.lam m) i j) :
    ∃ Φ : SeqΩ sz ≃ᵐ SeqΩ sz, MeasurePreserving Φ (seqP sz) (seqP sz) ∧
      ∀ (m : ℕ) (ω : SeqΩ sz),
        slice sz m (Φ ω) = expInv_Phi (φ m) (slice sz m ω) := by
  classical
  let Ψ : SeqCoord sz ≃ SeqCoord sz :=
    Equiv.sigmaCongrRight (fun m => expInv_pi (φ m))
  let fl : SeqCoord sz → Prop := fun c => expInv_flip (φ c.1) c.2
  let μ : SeqCoord sz → Measure ℝ := fun c => gaussianReal 0 (seqGvar sz c)
  let e1 : SeqΩ sz ≃ᵐ SeqΩ sz :=
    MeasurableEquiv.piCongrLeft (fun _ : SeqCoord sz => ℝ) Ψ.symm
  let e2 : SeqΩ sz ≃ᵐ SeqΩ sz :=
    MeasurableEquiv.piCongrRight
      (fun c => if fl c then MeasurableEquiv.neg ℝ else MeasurableEquiv.refl ℝ)
  have hg : ∀ c, seqGvar sz (Ψ c) = seqGvar sz c := by
    rintro ⟨m, c⟩
    exact expInv_gvar_pi (sz.lam m) (φ m) (hφ m) c
  have hP : seqP sz = Measure.infinitePi μ := rfl
  have he1 : ∀ (ω : SeqΩ sz) (c : SeqCoord sz), e1 ω c = ω (Ψ c) := by
    intro ω c
    obtain ⟨a, rfl⟩ := Ψ.symm.surjective c
    rw [Equiv.apply_symm_apply]
    exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : SeqCoord sz => ℝ) Ψ.symm ω a
  have he2 : ∀ (x : SeqΩ sz) (c : SeqCoord sz),
      e2 x c = (if fl c then (fun y : ℝ => -y) else (fun y : ℝ => y)) (x c) := by
    intro x c
    change (if fl c then MeasurableEquiv.neg ℝ else MeasurableEquiv.refl ℝ) (x c) = _
    by_cases hc : fl c <;> simp [hc]
  have h1 : Measure.map e1 (seqP sz) = seqP sz := by
    have h := Measure.infinitePi_map_piCongrLeft (X := fun _ : SeqCoord sz => ℝ) μ Ψ.symm
    have hμ : (fun i => μ (Ψ.symm i)) = μ := by
      funext i
      have h' := hg (Ψ.symm i)
      rw [Equiv.apply_symm_apply] at h'
      simp only [μ, h']
    rw [hμ] at h
    rw [hP]
    exact h
  have h2 : Measure.map e2 (seqP sz) = seqP sz := by
    have h := Measure.infinitePi_map_pi (X := fun _ : SeqCoord sz => ℝ) μ
      (f := fun c => if fl c then (fun x : ℝ => -x) else (fun x : ℝ => x))
      (fun c => by
        by_cases hc : fl c
        · simp only [hc, ite_true]; fun_prop
        · simp only [hc, ite_false]; fun_prop)
    have hμ : (fun c => (μ c).map (if fl c then (fun x : ℝ => -x) else (fun x : ℝ => x))) = μ := by
      funext c
      by_cases hc : fl c
      · simp only [hc, ite_true, μ, gaussianReal_map_neg, neg_zero]
      · simp only [hc, ite_false, Measure.map_id']
    rw [hμ] at h
    have hfun : (⇑e2 : SeqΩ sz → SeqΩ sz) =
        fun x c => (if fl c then (fun y : ℝ => -y) else (fun y : ℝ => y)) (x c) := by
      funext x c
      exact he2 x c
    rw [hP, hfun]
    exact h
  refine ⟨e1.trans e2, ?_, ?_⟩
  · have hm1 : MeasurePreserving e1 (seqP sz) (seqP sz) := ⟨e1.measurable, h1⟩
    have hm2 : MeasurePreserving e2 (seqP sz) (seqP sz) := ⟨e2.measurable, h2⟩
    rw [MeasurableEquiv.coe_trans]
    exact hm2.comp hm1
  · intro m ω
    funext c
    have h3 : (e1.trans e2) ω ⟨m, c⟩ =
        (if fl ⟨m, c⟩ then (fun y : ℝ => -y) else (fun y : ℝ => y)) (ω (Ψ ⟨m, c⟩)) := by
      rw [MeasurableEquiv.coe_trans]
      change e2 (e1 ω) ⟨m, c⟩ = _
      rw [he2, he1]
    change (e1.trans e2) ω ⟨m, c⟩ = expInv_Phi (φ m) (slice sz m ω) c
    rw [h3]
    unfold expInv_Phi
    by_cases hc : expInv_flip (φ m) c
    · have hc' : fl ⟨m, c⟩ := hc
      simp only [hc, hc', ite_true]
      rfl
    · have hc' : ¬ fl ⟨m, c⟩ := hc
      simp only [hc, hc', ite_false]
      rfl

/-- The expectation of a matrix functional along `seqHflow` is unchanged by the relabelling:
if `F(M_{φ,φ}) = F'(M)` for every `M`, then `𝔼F'(H_u) = 𝔼F(H_u)`. -/
private theorem expInv_integral_eq (n : ℕ) (u : ℝ) {T : Zd d (sz.L n) ≃ Zd d (sz.L n)}
    (hT : expInv_Aut (sz.lam n) T)
    (F F' : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ)
    (hF : ∀ M, F (M.submatrix (expInv_phi (sz.W n) T) (expInv_phi (sz.W n) T)) = F' M) :
    ∫ ω, F' (seqHflow sz n u ω) ∂(seqP sz) =
      ∫ ω, F (seqHflow sz n u ω) ∂(seqP sz) := by
  classical
  obtain ⟨Tf, hTf, hTn⟩ : ∃ Tf : ∀ m, Zd d (sz.L m) ≃ Zd d (sz.L m),
      (∀ m, expInv_Aut (sz.lam m) (Tf m)) ∧ Tf n = T := by
    let f0 : ∀ m, Zd d (sz.L m) ≃ Zd d (sz.L m) := fun m => Equiv.refl _
    refine ⟨Function.update f0 n T, fun m => ?_, Function.update_self n T f0⟩
    by_cases h : m = n
    · subst h
      rw [Function.update_self]; exact hT
    · rw [Function.update_of_ne h]; exact expInv_Aut_refl _
  obtain ⟨Φ, hΦ, hsl⟩ := expInv_seq sz (fun m => expInv_phi (sz.W m) (Tf m))
    (fun m => expInv_svarF_phi (sz.W m) (hTf m))
  have hH : ∀ ω, seqHflow sz n u (Φ ω) =
      (seqHflow sz n u ω).submatrix (expInv_phi (sz.W n) T) (expInv_phi (sz.W n) T) := by
    intro ω
    unfold seqHflow seqXmat
    rw [hsl, expInv_Xmat]
    simp only [hTn]
    rfl
  calc ∫ ω, F' (seqHflow sz n u ω) ∂(seqP sz)
      = ∫ ω, F ((seqHflow sz n u ω).submatrix (expInv_phi (sz.W n) T)
          (expInv_phi (sz.W n) T)) ∂(seqP sz) := by
        simp_rw [hF]
    _ = ∫ ω, F (seqHflow sz n u (Φ ω)) ∂(seqP sz) := by
        simp_rw [hH]
    _ = ∫ ω, F (seqHflow sz n u ω) ∂(seqP sz) :=
        hΦ.integral_comp' (fun ω => F (seqHflow sz n u ω))

end Seq

/-! ## 5. The target -/

end Sizes

end RBM.Gauss

namespace RBM.Gauss.Sizes

open RBM RBM.Gauss

/-- **Translation and reflection invariance of `𝔼 𝓛^{(2)}`** (`3_5:2196-2200`): the merged pin
`STExpInv` (`Induction/Step5Pins.lean`), proved.  Neither `|E| < 2` nor `0 ≤ u < 1` is used:
`𝓛 = loopFine (√u X) (z_u)` is equivariant for every `E`, `u` (the relabelling is a
measure-preserving change of variables of the Gaussian sample space). -/
theorem stExpInv_holds (d : ℕ) : STExpInv d := by
  intro sz n E u _ _ _ σ a c
  have key : ∀ T : Zd d (sz.L n) ≃ Zd d (sz.L n), expInv_Aut (sz.lam n) T →
      ∫ ω, Lloop sz n E u σ (fun i => T (a i)) ω ∂(sz.seqP) =
        ∫ ω, Lloop sz n E u σ a ω ∂(sz.seqP) := fun T hT =>
    expInv_integral_eq sz n u hT
      (fun M => loopFine d (sz.L n) (sz.W n) M (zt E u) σ a)
      (fun M => loopFine d (sz.L n) (sz.W n) M (zt E u) σ (fun i => T (a i)))
      (fun M => expInv_loopFine_submatrix (sz.W n) T M (zt E u) σ a)
  exact ⟨key (Equiv.addRight c) (expInv_Aut_addRight _ c), key (Equiv.neg _) (expInv_Aut_neg _)⟩

end RBM.Gauss.Sizes

/-! ## 6. Compiled nonempty instances (CLAUDE.md §4 step 2) -/

namespace RBM.Gauss.SizesInst

open RBM RBM.Gauss RBM.Gauss.Sizes

/-- The pin at `d = 3`. -/
example : STExpInv 3 := stExpInv_holds 3

/-- Both identities at the merged `sz0` (`L_0 = 4`, `W_0 = 32`, `λ_0 = 1/64`), `n = 0`, `E = 0`,
`u = 1/2`, `σ = (+,-)`, labels `a = (0, (0,1,2))` and shift `c = (1,1,1)` on `Z_4^3`. -/
example :
    let a : Fin 2 → Zd 3 (sz0.L 0) := ![fun _ => 0, fun k => ((k : ℕ) : ZMod (sz0.L 0))]
    let c : Zd 3 (sz0.L 0) := fun _ => 1
    (∫ ω, Lloop sz0 0 0 (1 / 2) ![true, false] (fun i => a i + c) ω ∂(sz0.seqP) =
        ∫ ω, Lloop sz0 0 0 (1 / 2) ![true, false] a ω ∂(sz0.seqP)) ∧
      (∫ ω, Lloop sz0 0 0 (1 / 2) ![true, false] (fun i => -a i) ω ∂(sz0.seqP) =
        ∫ ω, Lloop sz0 0 0 (1 / 2) ![true, false] a ω ∂(sz0.seqP)) :=
  stExpInv_holds 3 sz0 0 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) ![true, false]
    ![fun _ => 0, fun k => ((k : ℕ) : ZMod (sz0.L 0))] (fun _ => 1)

end RBM.Gauss.SizesInst
