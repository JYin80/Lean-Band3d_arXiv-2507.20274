/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import RBM3D.Defs.Lattice

/-!
# Resolvent-entry core of `lem_GbEXP`: minors (4.7)-(4.9) and the dimension-free entry estimates

Port of `RBM2D/Green/Minor.lean` (lines 1-271) and `RBM2D/Green/EntryCore.lean` (lines 1-844)
of RBM2D at commit `c9a24cf` (T2029, portmap P.7 row S1-10).  Everything here is finite algebra
over an arbitrary index type `n` with `[Fintype n] [DecidableEq n]` and an arbitrary variance
profile `S : n → n → ℝ`: no lattice, block, bandwidth or dimension appears, so the statements
are the same as in RBM2D (`Zd d L` or a block-site type is instantiated downstream).

* `RBM.green H z = (H - z)⁻¹` (RBM2D `Delocalization.lean:42`, copied verbatim).
* `RBM.Green.minorGreen`, `inv_minorMat`, `green_off_diag_paper`, `green_diag_paper`,
  `inv_minor_resolvent`: (4.7)-(4.9).
* `GoodEvent`, `norm_sq_green_le_row/col` (4.10), `norm_sq_green_le_two_sided`,
  `norm_sq_green_offdiag_le` (4.11), `norm_sq_green_diag_sub_le` (4.3), `norm_condExp_le`,
  `norm_sum_coef_green_sub_le` (4.5).

The probabilistic inputs enter as the explicit `Prop`s `LDERow`, `LDECol`, `LDEQuad`.
-/

namespace RBM

open Matrix

/-- The Green's function `G(z) = (H - z)⁻¹`. -/
noncomputable def green {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (z : ℂ) :
    Matrix n n ℂ := (H - z • 1)⁻¹

end RBM

namespace RBM.Green

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [Field R]

/-- Summing over every index different from `i` is summing over everything and
subtracting the `i`-th term. -/
theorem sum_subtype_ne (i : n) (f : n → R) :
    ∑ k : {a : n // a ≠ i}, f k.1 = (∑ k, f k) - f i := by
  have h1 : ∑ k ∈ Finset.univ.erase i, f k = ∑ k : {a : n // a ≠ i}, f k.1 :=
    Finset.sum_subtype _ (fun x => by simp) f
  rw [← h1, Finset.sum_erase_eq_sub (Finset.mem_univ i)]

/-- The minor `M^(i)`: delete row `i` and column `i`. -/
def minorMat (M : Matrix n n R) (i : n) : Matrix {a : n // a ≠ i} {a : n // a ≠ i} R :=
  M.submatrix Subtype.val Subtype.val

/-- The right-hand side of (4.9), taken as a definition.  It is proved below to be the
inverse of `minorMat M i`. -/
def minorGreen (G : Matrix n n R) (i : n) : Matrix {a : n // a ≠ i} {a : n // a ≠ i} R :=
  Matrix.of fun j k => G j.1 k.1 - G j.1 i * G i k.1 / G i i

omit [Fintype n] [DecidableEq n] [Field R] in
@[simp] theorem minorMat_apply (M : Matrix n n R) (i : n) (j k : {a : n // a ≠ i}) :
    minorMat M i j k = M j.1 k.1 := rfl

omit [Fintype n] [DecidableEq n] in
@[simp] theorem minorGreen_apply (G : Matrix n n R) (i : n) (j k : {a : n // a ≠ i}) :
    minorGreen G i j k = G j.1 k.1 - G j.1 i * G i k.1 / G i i := rfl

section Abstract

variable {M G : Matrix n n R}

/-- Row identity coming from `G * M = 1`, with the `i`-th term split off. -/
theorem sum_ne_green_mul (hGM : G * M = 1) (i : n) (a l : n) :
    ∑ k : {b : n // b ≠ i}, G a k.1 * M k.1 l = (if a = l then (1 : R) else 0) - G a i * M i l := by
  rw [sum_subtype_ne i (fun k => G a k * M k l)]
  have h : ∑ k, G a k * M k l = (if a = l then (1 : R) else 0) := by
    have h2 := congrArg (fun X : Matrix n n R => X a l) hGM
    simpa [Matrix.mul_apply, Matrix.one_apply] using h2
  rw [h]

/-- Row identity coming from `M * G = 1`, with the `i`-th term split off. -/
theorem sum_ne_mul_green (hMG : M * G = 1) (i : n) (a b : n) :
    ∑ k : {c : n // c ≠ i}, M a k.1 * G k.1 b = (if a = b then (1 : R) else 0) - M a i * G i b := by
  rw [sum_subtype_ne i (fun k => M a k * G k b)]
  have h : ∑ k, M a k * G k b = (if a = b then (1 : R) else 0) := by
    have h2 := congrArg (fun X : Matrix n n R => X a b) hMG
    simpa [Matrix.mul_apply, Matrix.one_apply] using h2
  rw [h]

/-- **(4.9)**, in the form "the candidate is a left inverse of the minor".
Only `G i i /= 0` is needed; invertibility of the minor is a *conclusion*. -/
theorem minorGreen_mul_minorMat (hGM : G * M = 1) (i : n) (hGii : G i i ≠ 0) :
    minorGreen G i * minorMat M i = 1 := by
  ext j l
  have hil : (i : n) ≠ l.1 := fun h => l.2 h.symm
  have hjl : ((1 : Matrix {a : n // a ≠ i} {a : n // a ≠ i} R) j l)
      = (if j.1 = l.1 then (1 : R) else 0) := by
    by_cases h : j = l
    · subst h
      simp [Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne h, ite_eq_right (fun hh => h (Subtype.ext hh))]
  rw [hjl, Matrix.mul_apply]
  have hsplit : ∑ k : {a : n // a ≠ i}, minorGreen G i j k * minorMat M i k l
      = (∑ k : {a : n // a ≠ i}, G j.1 k.1 * M k.1 l.1)
        - (G j.1 i / G i i) * ∑ k : {a : n // a ≠ i}, G i k.1 * M k.1 l.1 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [minorGreen_apply, minorMat_apply]
    ring
  rw [hsplit, sum_ne_green_mul hGM i j.1 l.1, sum_ne_green_mul hGM i i l.1, ite_eq_right hil]
  have hcancel : G j.1 i / G i i * ((0 : R) - G i i * M i l.1) = -(G j.1 i * M i l.1) := by
    rw [zero_sub, mul_neg, neg_inj]
    field_simp
  rw [hcancel]
  ring

/-- **(4.9)**: the inverse of the minor is given by the explicit formula. -/
theorem inv_minorMat (hGM : G * M = 1) (i : n) (hGii : G i i ≠ 0) :
    (minorMat M i)⁻¹ = minorGreen G i :=
  Matrix.inv_eq_left_inv (minorGreen_mul_minorMat hGM i hGii)

/-- The minor is invertible as soon as `G i i /= 0`. -/
theorem isUnit_det_minorMat (hGM : G * M = 1) (i : n) (hGii : G i i ≠ 0) :
    IsUnit (minorMat M i).det :=
  Matrix.isUnit_det_of_left_inverse (minorGreen_mul_minorMat hGM i hGii)

/-- The sum appearing in **(4.8)**. -/
theorem sum_minorGreen_row (hMG : M * G = 1) (i : n) (hGii : G i i ≠ 0)
    (j : {a : n // a ≠ i}) :
    ∑ k : {a : n // a ≠ i}, M i k.1 * minorGreen G i k j = -(G i j.1 / G i i) := by
  have hsplit : ∑ k : {a : n // a ≠ i}, M i k.1 * minorGreen G i k j
      = (∑ k : {a : n // a ≠ i}, M i k.1 * G k.1 j.1)
        - (G i j.1 / G i i) * ∑ k : {a : n // a ≠ i}, M i k.1 * G k.1 i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [minorGreen_apply]
    ring
  rw [hsplit, sum_ne_mul_green hMG i i j.1, sum_ne_mul_green hMG i i i,
    ite_eq_right (fun h => j.2 h.symm), ite_eq_left rfl]
  field_simp
  ring

/-- **(4.8)**.  Note the sign: the paper writes this without the minus. -/
theorem green_off_diag_eq (hMG : M * G = 1) (i : n) (hGii : G i i ≠ 0)
    (j : {a : n // a ≠ i}) :
    G i j.1 = -G i i * ∑ k : {a : n // a ≠ i}, M i k.1 * minorGreen G i k j := by
  rw [sum_minorGreen_row hMG i hGii j]
  field_simp

/-- The column analogue of `sum_minorGreen_row`, used for (4.7). -/
theorem sum_minorGreen_col (hGM : G * M = 1) (i : n) (hGii : G i i ≠ 0)
    (k : {a : n // a ≠ i}) :
    ∑ l : {a : n // a ≠ i}, minorGreen G i k l * M l.1 i = -(G k.1 i / G i i) := by
  have hsplit : ∑ l : {a : n // a ≠ i}, minorGreen G i k l * M l.1 i
      = (∑ l : {a : n // a ≠ i}, G k.1 l.1 * M l.1 i)
        - (G k.1 i / G i i) * ∑ l : {a : n // a ≠ i}, G i l.1 * M l.1 i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [minorGreen_apply]
    ring
  rw [hsplit, sum_ne_green_mul hGM i k.1 i, sum_ne_green_mul hGM i i i,
    ite_eq_right k.2, ite_eq_left rfl]
  field_simp
  ring

/-- **(4.7)**. -/
theorem green_diag_eq (hGM : G * M = 1) (hMG : M * G = 1) (i : n) (hGii : G i i ≠ 0) :
    G i i = (M i i - ∑ k : {a : n // a ≠ i}, ∑ l : {a : n // a ≠ i},
        M i k.1 * minorGreen G i k l * M l.1 i)⁻¹ := by
  have hinner : ∀ k : {a : n // a ≠ i},
      (∑ l : {a : n // a ≠ i}, M i k.1 * minorGreen G i k l * M l.1 i)
        = M i k.1 * -(G k.1 i / G i i) := by
    intro k
    rw [← sum_minorGreen_col hGM i hGii k, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => (mul_assoc _ _ _)
  have hstep : (∑ k : {a : n // a ≠ i}, ∑ l : {a : n // a ≠ i},
      M i k.1 * minorGreen G i k l * M l.1 i)
      = ∑ k : {a : n // a ≠ i}, M i k.1 * -(G k.1 i / G i i) :=
    Finset.sum_congr rfl fun k _ => hinner k
  have hcol : ∑ k : {a : n // a ≠ i}, M i k.1 * G k.1 i = 1 - M i i * G i i := by
    rw [sum_ne_mul_green hMG i i i, ite_eq_left rfl]
  have houter : ∑ k : {a : n // a ≠ i}, M i k.1 * -(G k.1 i / G i i)
      = -(1 / G i i) * (1 - M i i * G i i) := by
    rw [← hcol, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hval : M i i - -(1 / G i i) * (1 - M i i * G i i) = (G i i)⁻¹ := by
    field_simp
    ring
  rw [hstep, houter, hval, inv_inv]

end Abstract

section Resolvent

variable {H : Matrix n n ℂ} {z : ℂ}

omit [Fintype n] in
theorem sub_smul_one_apply_self (H : Matrix n n ℂ) (z : ℂ) (i : n) :
    (H - z • (1 : Matrix n n ℂ)) i i = H i i - z := by
  simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]

omit [Fintype n] in
theorem sub_smul_one_apply_ne (H : Matrix n n ℂ) (z : ℂ) {i k : n} (h : i ≠ k) :
    (H - z • (1 : Matrix n n ℂ)) i k = H i k := by
  simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne h]

omit [Fintype n] in
/-- The minor of `H - z` is `H^(i) - z`: so `minorGreen (green H z) i` really is the
Green's function of the submatrix `H^(i)`, which is what the paper calls `G^(i)`. -/
theorem minorMat_sub_smul_one (H : Matrix n n ℂ) (z : ℂ) (i : n) :
    minorMat (H - z • (1 : Matrix n n ℂ)) i
      = H.submatrix Subtype.val Subtype.val - z • 1 := by
  ext j k
  by_cases h : j = k
  · subst h
    simp [minorMat, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
  · have h' : j.1 ≠ k.1 := fun hh => h (Subtype.ext hh)
    simp [minorMat, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne h,
      Matrix.one_apply_ne h']

theorem green_mul_self (h : IsUnit (H - z • (1 : Matrix n n ℂ)).det) :
    green H z * (H - z • (1 : Matrix n n ℂ)) = 1 :=
  Matrix.nonsing_inv_mul _ h

theorem self_mul_green (h : IsUnit (H - z • (1 : Matrix n n ℂ)).det) :
    (H - z • (1 : Matrix n n ℂ)) * green H z = 1 :=
  Matrix.mul_nonsing_inv _ h

/-- **(4.9)** for the resolvent: `G^(i) = (H^(i) - z)` inverse is given by the explicit
formula in terms of `G`. -/
theorem inv_minor_resolvent (h : IsUnit (H - z • (1 : Matrix n n ℂ)).det) (i : n)
    (hGii : green H z i i ≠ 0) :
    (H.submatrix Subtype.val Subtype.val - z • (1 : Matrix {a : n // a ≠ i} _ ℂ))⁻¹
      = minorGreen (green H z) i := by
  rw [← minorMat_sub_smul_one H z i]
  exact inv_minorMat (green_mul_self h) i hGii

/-- **(4.8)** in the paper's notation: the entries of `M` off the diagonal are entries
of `H`. -/
theorem green_off_diag_paper (h : IsUnit (H - z • (1 : Matrix n n ℂ)).det) (i : n)
    (hGii : green H z i i ≠ 0) (j : {a : n // a ≠ i}) :
    green H z i j.1
      = -green H z i i * ∑ k : {a : n // a ≠ i}, H i k.1 * minorGreen (green H z) i k j := by
  have hsum : (∑ k : {a : n // a ≠ i},
        (H - z • (1 : Matrix n n ℂ)) i k.1 * minorGreen (green H z) i k j)
      = ∑ k : {a : n // a ≠ i}, H i k.1 * minorGreen (green H z) i k j := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have hik : (i : n) ≠ k.1 := fun hh => k.2 hh.symm
    rw [sub_smul_one_apply_ne H z hik]
  rw [green_off_diag_eq (self_mul_green h) i hGii j, hsum]

/-- **(4.7)** in the paper's notation. -/
theorem green_diag_paper (h : IsUnit (H - z • (1 : Matrix n n ℂ)).det) (i : n)
    (hGii : green H z i i ≠ 0) :
    green H z i i = (H i i - z - ∑ k : {a : n // a ≠ i}, ∑ l : {a : n // a ≠ i},
        H i k.1 * minorGreen (green H z) i k l * H l.1 i)⁻¹ := by
  have hsum : (∑ k : {a : n // a ≠ i}, ∑ l : {a : n // a ≠ i},
        (H - z • (1 : Matrix n n ℂ)) i k.1 * minorGreen (green H z) i k l
          * (H - z • (1 : Matrix n n ℂ)) l.1 i)
      = ∑ k : {a : n // a ≠ i}, ∑ l : {a : n // a ≠ i},
        H i k.1 * minorGreen (green H z) i k l * H l.1 i := by
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    have hik : (i : n) ≠ k.1 := fun hh => k.2 hh.symm
    have hli : l.1 ≠ (i : n) := l.2
    rw [sub_smul_one_apply_ne H z hik, sub_smul_one_apply_ne H z hli]
  rw [green_diag_eq (green_mul_self h) (self_mul_green h) i hGii,
    sub_smul_one_apply_self H z i, hsum]

end Resolvent

section Core

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The entries `G^(i)_{kl}` of the Green's function of the minor, written through the
right-hand side of (4.9) on the full index set.  For `k, l ≠ i` this is
`minorGreen G i k l` (`RBM.minorGreen_apply`). -/
noncomputable def greenMinor (G : Matrix n n ℂ) (i k l : n) : ℂ :=
  G k l - G k i * G i l / G i i

omit [Fintype n] [DecidableEq n] in
theorem minorGreen_eq_greenMinor (G : Matrix n n ℂ) (i : n) (k l : {a : n // a ≠ i}) :
    minorGreen G i k l = greenMinor G i k.1 l.1 := rfl

omit [Fintype n] [DecidableEq n] in
theorem greenMinor_sub (G : Matrix n n ℂ) (i k l : n) :
    greenMinor G i k l - G k l = -(G k i * G i l / G i i) := by
  rw [greenMinor]; ring

variable {M G : Matrix n n ℂ}

/-- Row identity from `M G = 1`, with the `i`-th term removed. -/
private theorem sum_erase_mul_green (hMG : M * G = 1) (i a b : n) :
    ∑ k ∈ univ.erase i, M a k * G k b = (if a = b then (1 : ℂ) else 0) - M a i * G i b := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  have h := congrArg (fun X : Matrix n n ℂ => X a b) hMG
  simp only [Matrix.mul_apply, Matrix.one_apply] at h
  rw [h]

/-- Column identity from `G M = 1`, with the `j`-th term removed. -/
private theorem sum_erase_green_mul (hGM : G * M = 1) (j a b : n) :
    ∑ l ∈ univ.erase j, G a l * M l b = (if a = b then (1 : ℂ) else 0) - G a j * M j b := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ j)]
  have h := congrArg (fun X : Matrix n n ℂ => X a b) hGM
  simp only [Matrix.mul_apply, Matrix.one_apply] at h
  rw [h]

/-- The row sum in **(4.8)**, on the full index set. -/
private theorem sum_erase_mul_greenMinor (hMG : M * G = 1) {i j : n}
    (hGii : G i i ≠ 0) (hij : i ≠ j) :
    ∑ k ∈ univ.erase i, M i k * greenMinor G i k j = -(G i j / G i i) := by
  have hsplit : ∑ k ∈ univ.erase i, M i k * greenMinor G i k j
      = (∑ k ∈ univ.erase i, M i k * G k j)
        - (G i j / G i i) * ∑ k ∈ univ.erase i, M i k * G k i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [greenMinor]; ring
  rw [hsplit, sum_erase_mul_green hMG, sum_erase_mul_green hMG, ite_eq_right hij, ite_eq_left rfl]
  field_simp
  ring

/-- **(4.8)** on the full index set (with our sign, see `RBM.green_off_diag_eq`):
`G_{ij} = -G_{ii} ∑_{k ≠ i} M_{ik} G^(i)_{kj}`. -/
private theorem green_eq_neg_mul_sum_row (hMG : M * G = 1) {i j : n}
    (hGii : G i i ≠ 0) (hij : i ≠ j) :
    G i j = -G i i * ∑ k ∈ univ.erase i, M i k * greenMinor G i k j := by
  rw [sum_erase_mul_greenMinor hMG hGii hij]
  field_simp

/-- The column analogue of the sum in (4.8). -/
private theorem sum_erase_greenMinor_mul (hGM : G * M = 1) {k j : n}
    (hGjj : G j j ≠ 0) (hkj : k ≠ j) :
    ∑ l ∈ univ.erase j, greenMinor G j k l * M l j = -(G k j / G j j) := by
  have hsplit : ∑ l ∈ univ.erase j, greenMinor G j k l * M l j
      = (∑ l ∈ univ.erase j, G k l * M l j)
        - (G k j / G j j) * ∑ l ∈ univ.erase j, G j l * M l j := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [greenMinor]; ring
  rw [hsplit, sum_erase_green_mul hGM, sum_erase_green_mul hGM, ite_eq_right hkj, ite_eq_left rfl]
  field_simp
  ring

/-- **(4.8), column form**: `G_{kj} = -G_{jj} ∑_{l ≠ j} G^(j)_{kl} M_{lj}`. -/
private theorem green_eq_neg_mul_sum_col (hGM : G * M = 1) {k j : n}
    (hGjj : G j j ≠ 0) (hkj : k ≠ j) :
    G k j = -G j j * ∑ l ∈ univ.erase j, greenMinor G j k l * M l j := by
  rw [sum_erase_greenMinor_mul hGM hGjj hkj]
  field_simp

/-- **(4.7)** on the full index set:
`G_{ii}⁻¹ = M_{ii} - ∑_{k, l ≠ i} M_{ik} G^(i)_{kl} M_{li}`. -/
private theorem inv_green_diag_eq (hGM : G * M = 1) (hMG : M * G = 1) {i : n} (hGii : G i i ≠ 0) :
    (G i i)⁻¹ = M i i - ∑ k ∈ univ.erase i, ∑ l ∈ univ.erase i,
      M i k * greenMinor G i k l * M l i := by
  have hinner : ∀ k ∈ univ.erase i, ∑ l ∈ univ.erase i, M i k * greenMinor G i k l * M l i
      = M i k * -(G k i / G i i) := by
    intro k hk
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    rw [← sum_erase_greenMinor_mul hGM hGii hki, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => mul_assoc _ _ _
  rw [Finset.sum_congr rfl hinner]
  have hcol : ∑ k ∈ univ.erase i, M i k * G k i = 1 - M i i * G i i := by
    rw [sum_erase_mul_green hMG, ite_eq_left rfl]
  have houter : ∑ k ∈ univ.erase i, M i k * -(G k i / G i i)
      = -(1 / G i i) * (1 - M i i * G i i) := by
    rw [← hcol, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [houter]
  field_simp
  ring

/-- Off-diagonal entries of `H - z` are those of `H`: the row sum in (4.8). -/
private theorem sum_erase_sub_smul_row (H G : Matrix n n ℂ) (z : ℂ) (i j : n) :
    ∑ k ∈ univ.erase i, (H - z • (1 : Matrix n n ℂ)) i k * greenMinor G i k j
      = ∑ k ∈ univ.erase i, H i k * greenMinor G i k j := by
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [sub_smul_one_apply_ne H z (Finset.ne_of_mem_erase hk).symm]

/-- Off-diagonal entries of `H - z` are those of `H`: the column sum in (4.8). -/
private theorem sum_erase_sub_smul_col (H G : Matrix n n ℂ) (z : ℂ) (k j : n) :
    ∑ l ∈ univ.erase j, greenMinor G j k l * (H - z • (1 : Matrix n n ℂ)) l j
      = ∑ l ∈ univ.erase j, greenMinor G j k l * H l j := by
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [sub_smul_one_apply_ne H z (Finset.ne_of_mem_erase hl)]

/-- Off-diagonal entries of `H - z` are those of `H`: the quadratic form in (4.7). -/
private theorem sum_erase_sub_smul_quad (H G : Matrix n n ℂ) (z : ℂ) (i : n) :
    ∑ k ∈ univ.erase i, ∑ l ∈ univ.erase i,
        (H - z • (1 : Matrix n n ℂ)) i k * greenMinor G i k l * (H - z • (1 : Matrix n n ℂ)) l i
      = ∑ k ∈ univ.erase i, ∑ l ∈ univ.erase i, H i k * greenMinor G i k l * H l i := by
  refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl => ?_
  rw [sub_smul_one_apply_ne H z (Finset.ne_of_mem_erase hk).symm,
    sub_smul_one_apply_ne H z (Finset.ne_of_mem_erase hl)]

end Core

section Event

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The event `Ω(t,c)` of (4.1), for one fixed matrix: `‖G - m‖_max ≤ δ`.  The paper takes
`δ = W^{-c}`. -/
def GoodEvent (G : Matrix n n ℂ) (m : ℂ) (δ : ℝ) : Prop :=
  ∀ x y, ‖G x y - (if x = y then m else 0)‖ ≤ δ

variable {G : Matrix n n ℂ} {m : ℂ} {δ : ℝ}

omit [Fintype n] in
theorem GoodEvent.norm_offdiag_le (h : GoodEvent G m δ) {x y : n} (hxy : x ≠ y) :
    ‖G x y‖ ≤ δ := by
  simpa [hxy] using h x y

omit [Fintype n] in
theorem GoodEvent.norm_diag_sub_le (h : GoodEvent G m δ) (x : n) : ‖G x x - m‖ ≤ δ := by
  simpa using h x x

omit [Fintype n] in
theorem GoodEvent.norm_diag_le (h : GoodEvent G m δ) (hm : ‖m‖ = 1) (x : n) :
    ‖G x x‖ ≤ 1 + δ := by
  calc ‖G x x‖ = ‖m + (G x x - m)‖ := by rw [add_sub_cancel]
    _ ≤ ‖m‖ + ‖G x x - m‖ := norm_add_le _ _
    _ ≤ 1 + δ := by rw [hm]; linarith [h.norm_diag_sub_le x]

omit [Fintype n] in
theorem GoodEvent.one_sub_le_norm_diag (h : GoodEvent G m δ) (hm : ‖m‖ = 1) (x : n) :
    1 - δ ≤ ‖G x x‖ := by
  have h1 : ‖m‖ ≤ ‖G x x‖ + ‖m - G x x‖ := by
    calc ‖m‖ = ‖G x x + (m - G x x)‖ := by rw [add_sub_cancel]
      _ ≤ ‖G x x‖ + ‖m - G x x‖ := norm_add_le _ _
  rw [norm_sub_rev, hm] at h1
  linarith [h.norm_diag_sub_le x]

omit [Fintype n] in
theorem GoodEvent.half_le_norm_diag (h : GoodEvent G m δ) (hm : ‖m‖ = 1) (hδ : δ ≤ 1 / 2)
    (x : n) : 1 / 2 ≤ ‖G x x‖ := by
  linarith [h.one_sub_le_norm_diag hm x]

omit [Fintype n] in
theorem GoodEvent.diag_ne_zero (h : GoodEvent G m δ) (hm : ‖m‖ = 1) (hδ : δ ≤ 1 / 2)
    (x : n) : G x x ≠ 0 := by
  intro h0
  have := h.half_le_norm_diag hm hδ x
  rw [h0, norm_zero] at this
  norm_num at this

omit [Fintype n] in
theorem GoodEvent.norm_sq_diag_le (h : GoodEvent G m δ) (hm : ‖m‖ = 1) (hδ : δ ≤ 1 / 2)
    (x : n) : ‖G x x‖ ^ 2 ≤ 9 / 4 := by
  have h1 := h.norm_diag_le hm x
  have h0 := norm_nonneg (G x x)
  nlinarith

omit [Fintype n] in
/-- On the event, removing the `(i)` superscript costs `2 |G_{ki}| |G_{il}|`: this is (4.9). -/
theorem GoodEvent.norm_greenMinor_sub_le (h : GoodEvent G m δ) (hm : ‖m‖ = 1)
    (hδ : δ ≤ 1 / 2) (i k l : n) :
    ‖greenMinor G i k l - G k l‖ ≤ 2 * (‖G k i‖ * ‖G i l‖) := by
  rw [greenMinor_sub, norm_neg, norm_div, norm_mul]
  have h1 := h.half_le_norm_diag hm hδ i
  rw [div_le_iff₀ (by linarith)]
  have h2 : 0 ≤ ‖G k i‖ * ‖G i l‖ := by positivity
  nlinarith

end Event

section Absorb

/-- The absorption step at the end of (4.10). -/
theorem absorb_le {x Y Φ δ : ℝ} (hx : 0 ≤ x) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (h : x ≤ 9 / 4 * (Φ * (2 * Y + 8 * δ ^ 2 * x))) : x ≤ 9 * Φ * Y := by
  have h1 : 36 * Φ * δ ^ 2 * x ≤ x := by nlinarith
  nlinarith

variable {n : Type*} [Fintype n]

/-- A weighted sum of squares of perturbed quantities. -/
theorem sum_mul_sq_le_of_le_add (s : Finset n) {w a b : n → ℝ} {ε : ℝ} (hw : ∀ k, 0 ≤ w k)
    (hw1 : ∑ k, w k ≤ 1) (ha : ∀ k, 0 ≤ a k) (hab : ∀ k ∈ s, a k ≤ b k + ε) :
    ∑ k ∈ s, w k * a k ^ 2 ≤ 2 * ∑ k, w k * b k ^ 2 + 2 * ε ^ 2 := by
  have hpt : ∀ k ∈ s, w k * a k ^ 2 ≤ w k * (2 * b k ^ 2 + 2 * ε ^ 2) := by
    intro k hk
    have h1 := hab k hk
    have h2 : a k ^ 2 ≤ 2 * b k ^ 2 + 2 * ε ^ 2 := by nlinarith [ha k, sq_nonneg (b k - ε)]
    exact mul_le_mul_of_nonneg_left h2 (hw k)
  calc ∑ k ∈ s, w k * a k ^ 2 ≤ ∑ k ∈ s, w k * (2 * b k ^ 2 + 2 * ε ^ 2) := sum_le_sum hpt
    _ ≤ ∑ k, w k * (2 * b k ^ 2 + 2 * ε ^ 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
          fun k _ _ => mul_nonneg (hw k) (by positivity)
    _ = 2 * ∑ k, w k * b k ^ 2 + 2 * ε ^ 2 * ∑ k, w k := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ 2 * ∑ k, w k * b k ^ 2 + 2 * ε ^ 2 := by
        have : 2 * ε ^ 2 * ∑ k, w k ≤ 2 * ε ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hw1 (by positivity)
        linarith

end Absorb

section EntryBound

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The large deviation input `[39, Lemma 3.3]`

We do not formalize the large deviation bound; we take its *conclusion*, for the vectors
where the paper applies it, as a hypothesis with an explicit factor `Φ` (in the stochastic
domination layer `Φ = N^τ`).  All three are stated for squared moduli, i.e.
`|∑ H X|² ≤ Φ ∑ S |X|²` is the paper's `|∑ H X| ≺ (∑ S |X|²)^{1/2}`. -/

/-- Left-hand side of the LDE for the row sum in (4.8): `|∑_{k≠i} H_{ik} G^(i)_{kj}|²`. -/
noncomputable def ldeRowLHS (H G : Matrix n n ℂ) (i j : n) : ℝ :=
  ‖∑ k ∈ univ.erase i, H i k * greenMinor G i k j‖ ^ 2

/-- Right-hand side of the LDE for the row sum in (4.8): `∑_{k≠i} S_{ik} |G^(i)_{kj}|²`. -/
noncomputable def ldeRowRHS (S : n → n → ℝ) (G : Matrix n n ℂ) (i j : n) : ℝ :=
  ∑ k ∈ univ.erase i, S i k * ‖greenMinor G i k j‖ ^ 2

/-- Left-hand side of the LDE for the column sum: `|∑_{l≠j} G^(j)_{kl} H_{lj}|²`. -/
noncomputable def ldeColLHS (H G : Matrix n n ℂ) (k j : n) : ℝ :=
  ‖∑ l ∈ univ.erase j, greenMinor G j k l * H l j‖ ^ 2

/-- Right-hand side of the LDE for the column sum: `∑_{l≠j} |G^(j)_{kl}|² S_{lj}`. -/
noncomputable def ldeColRHS (S : n → n → ℝ) (G : Matrix n n ℂ) (k j : n) : ℝ :=
  ∑ l ∈ univ.erase j, ‖greenMinor G j k l‖ ^ 2 * S l j

/-- Left-hand side of the LDE for the quadratic form in (4.7):
`|∑_{k,l≠i} H_{ik} G^(i)_{kl} H_{li} - t ∑_{k≠i} S_{ik} G^(i)_{kk}|²`. -/
noncomputable def ldeQuadLHS (H G : Matrix n n ℂ) (S : n → n → ℝ) (t : ℝ) (i : n) : ℝ :=
  ‖∑ k ∈ univ.erase i, ∑ l ∈ univ.erase i, H i k * greenMinor G i k l * H l i
    - (t : ℂ) * ∑ k ∈ univ.erase i, (S i k : ℂ) * greenMinor G i k k‖ ^ 2

/-- Right-hand side of the LDE for the quadratic form in (4.7):
`∑_{k,l≠i} S_{ik} |G^(i)_{kl}|² S_{li}`. -/
noncomputable def ldeQuadRHS (S : n → n → ℝ) (G : Matrix n n ℂ) (i : n) : ℝ :=
  ∑ k ∈ univ.erase i, ∑ l ∈ univ.erase i, S i k * ‖greenMinor G i k l‖ ^ 2 * S l i

/-- The row LDE, with factor `Φ`, for all `i ≠ j`. -/
def LDERow (H G : Matrix n n ℂ) (S : n → n → ℝ) (Φ : ℝ) : Prop :=
  ∀ i j, i ≠ j → ldeRowLHS H G i j ≤ Φ * ldeRowRHS S G i j

/-- The column LDE, with factor `Φ`, for all `k ≠ j`. -/
def LDECol (H G : Matrix n n ℂ) (S : n → n → ℝ) (Φ : ℝ) : Prop :=
  ∀ k j, k ≠ j → ldeColLHS H G k j ≤ Φ * ldeColRHS S G k j

/-- The quadratic LDE, with factor `Φ`, for all `i`. -/
def LDEQuad (H G : Matrix n n ℂ) (S : n → n → ℝ) (t Φ : ℝ) : Prop :=
  ∀ i, ldeQuadLHS H G S t i ≤ Φ * ldeQuadRHS S G i

variable {H G : Matrix n n ℂ} {z m : ℂ} {δ Φ : ℝ} {S : n → n → ℝ}

/-- **(4.10)**: on the event `Ω`, `|G_{ij}|² ≤ 9 Φ ∑_k S_{ik} |G_{kj}|²` for `i ≠ j`. -/
theorem norm_sq_green_le_row (hMG : (H - z • (1 : Matrix n n ℂ)) * G = 1) (hm : ‖m‖ = 1)
    (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k)
    (hS1 : ∀ i, ∑ k, S i k ≤ 1) (hΦ : 0 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (hLDE : LDERow H G S Φ) {i j : n} (hij : i ≠ j) :
    ‖G i j‖ ^ 2 ≤ 9 * Φ * ∑ k, S i k * ‖G k j‖ ^ 2 := by
  have hGii := hΩ.diag_ne_zero hm hδ i
  have h48 := green_eq_neg_mul_sum_row hMG hGii hij
  rw [sum_erase_sub_smul_row] at h48
  have hnorm := congrArg norm h48
  rw [norm_mul, norm_neg] at hnorm
  have hsq : ‖G i j‖ ^ 2 ≤ 9 / 4 * ldeRowLHS H G i j := by
    rw [hnorm, ldeRowLHS, mul_pow]
    exact mul_le_mul_of_nonneg_right (hΩ.norm_sq_diag_le hm hδ i) (sq_nonneg _)
  have hrhs : ldeRowRHS S G i j ≤ 2 * ∑ k, S i k * ‖G k j‖ ^ 2 + 2 * (2 * δ * ‖G i j‖) ^ 2 := by
    refine sum_mul_sq_le_of_le_add _ (hS0 i) (hS1 i) (fun _ => norm_nonneg _) ?_
    intro k hk
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    have h1 := hΩ.norm_greenMinor_sub_le hm hδ i k j
    have h2 := hΩ.norm_offdiag_le hki
    have h3 : ‖greenMinor G i k j‖ ≤ ‖G k j‖ + ‖greenMinor G i k j - G k j‖ := by
      calc ‖greenMinor G i k j‖ = ‖G k j + (greenMinor G i k j - G k j)‖ := by
            rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have h4 : ‖G k i‖ * ‖G i j‖ ≤ δ * ‖G i j‖ :=
      mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    linarith
  have hlde := hLDE i j hij
  refine absorb_le (sq_nonneg _) hΦδ ?_
  calc ‖G i j‖ ^ 2 ≤ 9 / 4 * ldeRowLHS H G i j := hsq
    _ ≤ 9 / 4 * (Φ * ldeRowRHS S G i j) := by linarith
    _ ≤ 9 / 4 * (Φ * (2 * ∑ k, S i k * ‖G k j‖ ^ 2 + 2 * (2 * δ * ‖G i j‖) ^ 2)) := by
        gcongr
    _ = 9 / 4 * (Φ * (2 * ∑ k, S i k * ‖G k j‖ ^ 2 + 8 * δ ^ 2 * ‖G i j‖ ^ 2)) := by ring

/-- **(4.10), column form**: on the event `Ω`, `|G_{kj}|² ≤ 9 Φ ∑_l |G_{kl}|² S_{lj}` for
`k ≠ j`.  The paper uses this (the same estimate, expanded along the column) in the
iteration leading to (4.11). -/
theorem norm_sq_green_le_col (hGM : G * (H - z • (1 : Matrix n n ℂ)) = 1) (hm : ‖m‖ = 1)
    (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k)
    (hS1 : ∀ j, ∑ l, S l j ≤ 1) (hΦ : 0 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (hLDE : LDECol H G S Φ) {k j : n} (hkj : k ≠ j) :
    ‖G k j‖ ^ 2 ≤ 9 * Φ * ∑ l, S l j * ‖G k l‖ ^ 2 := by
  have hGjj := hΩ.diag_ne_zero hm hδ j
  have h48 := green_eq_neg_mul_sum_col hGM hGjj hkj
  rw [sum_erase_sub_smul_col] at h48
  have hnorm := congrArg norm h48
  rw [norm_mul, norm_neg] at hnorm
  have hsq : ‖G k j‖ ^ 2 ≤ 9 / 4 * ldeColLHS H G k j := by
    rw [hnorm, ldeColLHS, mul_pow]
    exact mul_le_mul_of_nonneg_right (hΩ.norm_sq_diag_le hm hδ j) (sq_nonneg _)
  have hrhs : ldeColRHS S G k j ≤ 2 * ∑ l, S l j * ‖G k l‖ ^ 2 + 2 * (2 * δ * ‖G k j‖) ^ 2 := by
    have hre : ldeColRHS S G k j = ∑ l ∈ univ.erase j, S l j * ‖greenMinor G j k l‖ ^ 2 := by
      rw [ldeColRHS]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    rw [hre]
    refine sum_mul_sq_le_of_le_add _ (fun l => hS0 l j) (hS1 j) (fun _ => norm_nonneg _) ?_
    intro l hl
    have hlj : l ≠ j := Finset.ne_of_mem_erase hl
    have h1 := hΩ.norm_greenMinor_sub_le hm hδ j k l
    have h2 := hΩ.norm_offdiag_le hlj.symm
    have h3 : ‖greenMinor G j k l‖ ≤ ‖G k l‖ + ‖greenMinor G j k l - G k l‖ := by
      calc ‖greenMinor G j k l‖ = ‖G k l + (greenMinor G j k l - G k l)‖ := by
            rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have h4 : ‖G k j‖ * ‖G j l‖ ≤ ‖G k j‖ * δ :=
      mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    linarith
  have hlde := hLDE k j hkj
  refine absorb_le (sq_nonneg _) hΦδ ?_
  calc ‖G k j‖ ^ 2 ≤ 9 / 4 * ldeColLHS H G k j := hsq
    _ ≤ 9 / 4 * (Φ * ldeColRHS S G k j) := by linarith
    _ ≤ 9 / 4 * (Φ * (2 * ∑ l, S l j * ‖G k l‖ ^ 2 + 2 * (2 * δ * ‖G k j‖) ^ 2)) := by
        gcongr
    _ = 9 / 4 * (Φ * (2 * ∑ l, S l j * ‖G k l‖ ^ 2 + 8 * δ ^ 2 * ‖G k j‖ ^ 2)) := by ring

/-- **(4.11)**: iterating (4.10) once along the row and once along the column,
`|G_{ij}|² ≤ 81 Φ² (∑_{k,l} S_{ik} |G_{kl}|² S_{lj} + S_{ij})` for `i ≠ j`.
The term `S_{ij}` is the contribution `k = j` of the paper, where `|G_{jj}|² = O(1)`. -/
theorem norm_sq_green_le_two_sided (hGM : G * (H - z • (1 : Matrix n n ℂ)) = 1)
    (hMG : (H - z • (1 : Matrix n n ℂ)) * G = 1) (hm : ‖m‖ = 1)
    (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k)
    (hSrow : ∀ i, ∑ k, S i k ≤ 1) (hScol : ∀ j, ∑ l, S l j ≤ 1) (hΦ1 : 1 ≤ Φ)
    (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hLrow : LDERow H G S Φ) (hLcol : LDECol H G S Φ)
    {i j : n} (hij : i ≠ j) :
    ‖G i j‖ ^ 2 ≤ 81 * Φ ^ 2 * (∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j + S i j) := by
  have hΦ : 0 ≤ Φ := by linarith
  have h1 := norm_sq_green_le_row hMG hm hΩ hδ hS0 hSrow hΦ hΦδ hLrow hij
  have hk : ∀ k, ‖G k j‖ ^ 2
      ≤ 9 * Φ * ∑ l, S l j * ‖G k l‖ ^ 2 + (if k = j then 9 / 4 else 0) := by
    intro k
    by_cases hkj : k = j
    · subst hkj
      rw [ite_eq_left rfl]
      have h2 := hΩ.norm_sq_diag_le hm hδ k
      have h3 : 0 ≤ 9 * Φ * ∑ l, S l k * ‖G k l‖ ^ 2 :=
        mul_nonneg (by linarith) (Finset.sum_nonneg fun l _ =>
          mul_nonneg (hS0 l k) (sq_nonneg _))
      linarith
    · rw [ite_eq_right hkj, add_zero]
      exact norm_sq_green_le_col hGM hm hΩ hδ hS0 hScol hΦ hΦδ hLcol hkj
  have hsum : ∑ k, S i k * ‖G k j‖ ^ 2
      ≤ 9 * Φ * (∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j) + 9 / 4 * S i j := by
    calc ∑ k, S i k * ‖G k j‖ ^ 2
        ≤ ∑ k, S i k * (9 * Φ * ∑ l, S l j * ‖G k l‖ ^ 2 + (if k = j then 9 / 4 else 0)) :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hk k) (hS0 i k)
      _ = 9 * Φ * (∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j)
            + ∑ k, S i k * (if k = j then 9 / 4 else 0) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun l _ => by ring
      _ = 9 * Φ * (∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j) + 9 / 4 * S i j := by
          congr 1
          simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
          ring
  have hX : 0 ≤ ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
      mul_nonneg (mul_nonneg (hS0 i k) (sq_nonneg _)) (hS0 l j)
  have hSij := hS0 i j
  have hΦ2 : Φ ≤ Φ ^ 2 := by nlinarith
  calc ‖G i j‖ ^ 2 ≤ 9 * Φ * ∑ k, S i k * ‖G k j‖ ^ 2 := h1
    _ ≤ 9 * Φ * (9 * Φ * (∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j) + 9 / 4 * S i j) :=
        mul_le_mul_of_nonneg_left hsum (by linarith)
    _ ≤ 81 * Φ ^ 2 * (∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j + S i j) := by
        nlinarith [mul_le_mul_of_nonneg_right hΦ2 hSij]

/-- (4.11) in the form used below: with `Λ` bounding both terms on the right,
`|G_{ij}|² ≤ 162 Φ² Λ` for `i ≠ j`. -/
theorem norm_sq_green_offdiag_le (hGM : G * (H - z • (1 : Matrix n n ℂ)) = 1)
    (hMG : (H - z • (1 : Matrix n n ℂ)) * G = 1) (hm : ‖m‖ = 1)
    (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k)
    (hSrow : ∀ i, ∑ k, S i k ≤ 1) (hScol : ∀ j, ∑ l, S l j ≤ 1) (hΦ1 : 1 ≤ Φ)
    (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hLrow : LDERow H G S Φ) (hLcol : LDECol H G S Φ) {Λ : ℝ}
    (hΛ1 : ∀ i j, ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j ≤ Λ) (hΛ2 : ∀ i j, S i j ≤ Λ)
    {i j : n} (hij : i ≠ j) :
    ‖G i j‖ ^ 2 ≤ 162 * Φ ^ 2 * Λ := by
  have h := norm_sq_green_le_two_sided hGM hMG hm hΩ hδ hS0 hSrow hScol hΦ1 hΦδ hLrow hLcol hij
  have h2 : ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j + S i j ≤ 2 * Λ := by
    linarith [hΛ1 i j, hΛ2 i j]
  have hΦ2 : 0 ≤ 81 * Φ ^ 2 := by positivity
  calc ‖G i j‖ ^ 2 ≤ 81 * Φ ^ 2 * (∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j + S i j) := h
    _ ≤ 81 * Φ ^ 2 * (2 * Λ) := mul_le_mul_of_nonneg_left h2 hΦ2
    _ = 162 * Φ ^ 2 * Λ := by ring

omit [DecidableEq n] in
/-- A double sum over a subset is bounded by the full double sum, for non-negative terms. -/
private theorem sum_sum_le_sum_sum (s : Finset n) {f : n → n → ℝ} (hf : ∀ k l, 0 ≤ f k l) :
    ∑ k ∈ s, ∑ l ∈ s, f k l ≤ ∑ k, ∑ l, f k l := by
  calc ∑ k ∈ s, ∑ l ∈ s, f k l ≤ ∑ k ∈ s, ∑ l, f k l :=
        Finset.sum_le_sum fun k _ =>
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) fun l _ _ => hf k l
    _ ≤ ∑ k, ∑ l, f k l :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) fun k _ _ =>
          Finset.sum_nonneg fun l _ => hf k l

/-- The right-hand side of the quadratic LDE, after removing the `(i)` superscript with
(4.9) and using (4.11): `∑_{k,l≠i} S_{ik} |G^(i)_{kl}|² S_{li} ≤ 38 Φ Λ`. -/
theorem ldeQuadRHS_le (hGM : G * (H - z • (1 : Matrix n n ℂ)) = 1)
    (hMG : (H - z • (1 : Matrix n n ℂ)) * G = 1) (hm : ‖m‖ = 1)
    (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k)
    (hSrow : ∀ i, ∑ k, S i k ≤ 1) (hScol : ∀ j, ∑ l, S l j ≤ 1) (hΦ1 : 1 ≤ Φ)
    (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hLrow : LDERow H G S Φ) (hLcol : LDECol H G S Φ) {Λ : ℝ}
    (hΛ1 : ∀ i j, ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j ≤ Λ) (hΛ2 : ∀ i j, S i j ≤ Λ)
    (i : n) :
    ldeQuadRHS S G i ≤ 38 * Φ * Λ := by
  have hΛ0 : 0 ≤ Λ := le_trans (hS0 i i) (hΛ2 i i)
  have hpt : ∀ k ∈ univ.erase i, ∀ l ∈ univ.erase i,
      S i k * ‖greenMinor G i k l‖ ^ 2 * S l i
        ≤ S i k * (2 * ‖G k l‖ ^ 2 + 36 * Φ * Λ) * S l i := by
    intro k hk l hl
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    have hli : l ≠ i := Finset.ne_of_mem_erase hl
    have h1 := hΩ.norm_greenMinor_sub_le hm hδ i k l
    have h2 := hΩ.norm_offdiag_le hli.symm
    have h3 : ‖greenMinor G i k l‖ ≤ ‖G k l‖ + ‖greenMinor G i k l - G k l‖ := by
      calc ‖greenMinor G i k l‖ = ‖G k l + (greenMinor G i k l - G k l)‖ := by
            rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have h4 : ‖G k i‖ * ‖G i l‖ ≤ ‖G k i‖ * δ :=
      mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    have h5 : ‖greenMinor G i k l‖ ≤ ‖G k l‖ + 2 * δ * ‖G k i‖ := by linarith
    have h6 := norm_sq_green_offdiag_le hGM hMG hm hΩ hδ hS0 hSrow hScol hΦ1 hΦδ hLrow hLcol
      hΛ1 hΛ2 hki
    have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) (hΩ i i)
    have h7 : ‖greenMinor G i k l‖ ^ 2 ≤ 2 * ‖G k l‖ ^ 2 + 8 * δ ^ 2 * ‖G k i‖ ^ 2 := by
      have := norm_nonneg (greenMinor G i k l)
      nlinarith [sq_nonneg (‖G k l‖ - 2 * δ * ‖G k i‖), norm_nonneg (G k i),
        norm_nonneg (G k l)]
    have h8 : 8 * δ ^ 2 * ‖G k i‖ ^ 2 ≤ 36 * Φ * Λ := by
      have h9 : 8 * δ ^ 2 * ‖G k i‖ ^ 2 ≤ 8 * δ ^ 2 * (162 * Φ ^ 2 * Λ) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
      have h10 : 8 * δ ^ 2 * (162 * Φ ^ 2 * Λ) = 36 * (36 * Φ * δ ^ 2) * (Φ * Λ) := by ring
      have h11 : 36 * (36 * Φ * δ ^ 2) * (Φ * Λ) ≤ 36 * 1 * (Φ * Λ) := by
        have : 0 ≤ Φ * Λ := mul_nonneg (by linarith) hΛ0
        nlinarith
      linarith
    have h12 : ‖greenMinor G i k l‖ ^ 2 ≤ 2 * ‖G k l‖ ^ 2 + 36 * Φ * Λ := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h12 (hS0 i k)) (hS0 l i)
  have hnn : ∀ k l, 0 ≤ S i k * (2 * ‖G k l‖ ^ 2 + 36 * Φ * Λ) * S l i := by
    intro k l
    have : 0 ≤ 36 * Φ * Λ := mul_nonneg (by linarith) hΛ0
    exact mul_nonneg (mul_nonneg (hS0 i k) (by positivity)) (hS0 l i)
  calc ldeQuadRHS S G i
      ≤ ∑ k ∈ univ.erase i, ∑ l ∈ univ.erase i,
          S i k * (2 * ‖G k l‖ ^ 2 + 36 * Φ * Λ) * S l i :=
        Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun l hl => hpt k hk l hl
    _ ≤ ∑ k, ∑ l, S i k * (2 * ‖G k l‖ ^ 2 + 36 * Φ * Λ) * S l i :=
        sum_sum_le_sum_sum _ hnn
    _ = 2 * ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l i
          + 36 * Φ * Λ * ((∑ k, S i k) * ∑ l, S l i) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ ≤ 2 * Λ + 36 * Φ * Λ * (1 * 1) := by
        have h1 := hΛ1 i i
        have h2 : (∑ k, S i k) * ∑ l, S l i ≤ 1 * 1 :=
          mul_le_mul (hSrow i) (hScol i) (Finset.sum_nonneg fun l _ => hS0 l i) zero_le_one
        have h3 : 0 ≤ 36 * Φ * Λ := mul_nonneg (by linarith) hΛ0
        nlinarith
    _ ≤ 38 * Φ * Λ := by nlinarith

/-- **The self-consistent equation behind (4.3).**  On the event, (4.7), the quadratic LDE,
(4.9) and (4.11) give
`G_{ii}⁻¹ = -z - t ∑_k S_{ik} G_{kk} + e_i` with `|e_i|² ≤ 240 Φ² Λ`. -/
theorem norm_sq_selfEnergy_err_le (hGM : G * (H - z • (1 : Matrix n n ℂ)) = 1)
    (hMG : (H - z • (1 : Matrix n n ℂ)) * G = 1) (hm : ‖m‖ = 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k)
    (hSrow : ∀ i, ∑ k, S i k ≤ 1) (hScol : ∀ j, ∑ l, S l j ≤ 1) (hΦ1 : 1 ≤ Φ)
    (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hLrow : LDERow H G S Φ) (hLcol : LDECol H G S Φ)
    (hLquad : LDEQuad H G S t Φ) (hLdiag : ∀ i, ‖H i i‖ ^ 2 ≤ Φ * S i i) {Λ : ℝ}
    (hΛ1 : ∀ i j, ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j ≤ Λ) (hΛ2 : ∀ i j, S i j ≤ Λ)
    (i : n) :
    ‖(G i i)⁻¹ + z + (t : ℂ) * ∑ k, (S i k : ℂ) * G k k‖ ^ 2 ≤ 240 * Φ ^ 2 * Λ := by
  have hΛ0 : 0 ≤ Λ := le_trans (hS0 i i) (hΛ2 i i)
  have hΦ : 0 ≤ Φ := by linarith
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) (hΩ i i)
  have hGii := hΩ.diag_ne_zero hm hδ i
  have hinv := inv_green_diag_eq hGM hMG hGii
  rw [sum_erase_sub_smul_quad, sub_smul_one_apply_self] at hinv
  set Q := ∑ k ∈ univ.erase i, ∑ l ∈ univ.erase i, H i k * greenMinor G i k l * H l i with hQ
  set A2 := Q - (t : ℂ) * ∑ k ∈ univ.erase i, (S i k : ℂ) * greenMinor G i k k with hA2
  set A3 := (t : ℂ) * ((S i i : ℂ) * G i i) with hA3
  set A4 := (t : ℂ) * ∑ k ∈ univ.erase i, (S i k : ℂ) * (G k k - greenMinor G i k k) with hA4
  have hsplit : ∑ k, (S i k : ℂ) * G k k
      = (S i i : ℂ) * G i i + ∑ k ∈ univ.erase i, (S i k : ℂ) * greenMinor G i k k
        + ∑ k ∈ univ.erase i, (S i k : ℂ) * (G k k - greenMinor G i k k) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_assoc, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  have heq : (G i i)⁻¹ + z + (t : ℂ) * ∑ k, (S i k : ℂ) * G k k = H i i - A2 + A3 + A4 := by
    rw [hinv, hsplit, hA2, hA3, hA4]
    ring
  rw [heq]
  -- the four pieces
  have hb1 : ‖H i i‖ ^ 2 ≤ Φ * Λ :=
    (hLdiag i).trans (mul_le_mul_of_nonneg_left (hΛ2 i i) hΦ)
  have hb2 : ‖A2‖ ^ 2 ≤ 38 * Φ ^ 2 * Λ := by
    have h1 := hLquad i
    have h2 := ldeQuadRHS_le hGM hMG hm hΩ hδ hS0 hSrow hScol hΦ1 hΦδ hLrow hLcol hΛ1 hΛ2 i
    have h3 : ‖A2‖ ^ 2 = ldeQuadLHS H G S t i := rfl
    calc ‖A2‖ ^ 2 ≤ Φ * ldeQuadRHS S G i := h3 ▸ h1
      _ ≤ Φ * (38 * Φ * Λ) := mul_le_mul_of_nonneg_left h2 hΦ
      _ = 38 * Φ ^ 2 * Λ := by ring
  have hSii1 : S i i ≤ 1 :=
    le_trans (Finset.single_le_sum (fun k _ => hS0 i k) (Finset.mem_univ i)) (hSrow i)
  have hb3 : ‖A3‖ ^ 2 ≤ 9 / 4 * Λ := by
    have hn : ‖A3‖ = t * (S i i * ‖G i i‖) := by
      rw [hA3, norm_mul, norm_mul, Complex.norm_of_nonneg ht0, Complex.norm_of_nonneg (hS0 i i)]
    have h1 := hΩ.norm_sq_diag_le hm hδ i
    have h2 : ‖A3‖ ^ 2 ≤ S i i ^ 2 * ‖G i i‖ ^ 2 := by
      have h0 : 0 ≤ S i i * ‖G i i‖ := mul_nonneg (hS0 i i) (norm_nonneg _)
      have h5 : t * (S i i * ‖G i i‖) ≤ S i i * ‖G i i‖ := by nlinarith
      calc ‖A3‖ ^ 2 = (t * (S i i * ‖G i i‖)) ^ 2 := by rw [hn]
        _ ≤ (S i i * ‖G i i‖) ^ 2 := pow_le_pow_left₀ (mul_nonneg ht0 h0) h5 2
        _ = S i i ^ 2 * ‖G i i‖ ^ 2 := by ring
    have h3 : S i i ^ 2 ≤ Λ := by nlinarith [hS0 i i, hΛ2 i i]
    have h4 : S i i ^ 2 * ‖G i i‖ ^ 2 ≤ Λ * (9 / 4) :=
      mul_le_mul h3 h1 (sq_nonneg _) hΛ0
    linarith
  have hb4 : ‖A4‖ ^ 2 ≤ 18 * Φ * Λ := by
    have hpt : ∀ k ∈ univ.erase i,
        ‖(S i k : ℂ) * (G k k - greenMinor G i k k)‖ ≤ S i k * (2 * δ * ‖G i k‖) := by
      intro k hk
      have hki : k ≠ i := Finset.ne_of_mem_erase hk
      rw [norm_mul, Complex.norm_of_nonneg (hS0 i k), norm_sub_rev]
      refine mul_le_mul_of_nonneg_left ?_ (hS0 i k)
      have h1 := hΩ.norm_greenMinor_sub_le hm hδ i k k
      have h2 := hΩ.norm_offdiag_le hki
      have h3 : ‖G k i‖ * ‖G i k‖ ≤ δ * ‖G i k‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      linarith
    have hA4le : ‖A4‖ ≤ ∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖) := by
      rw [hA4, norm_mul, Complex.norm_of_nonneg ht0]
      calc t * ‖∑ k ∈ univ.erase i, (S i k : ℂ) * (G k k - greenMinor G i k k)‖
          ≤ 1 * ‖∑ k ∈ univ.erase i, (S i k : ℂ) * (G k k - greenMinor G i k k)‖ :=
            mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
        _ ≤ ∑ k ∈ univ.erase i, ‖(S i k : ℂ) * (G k k - greenMinor G i k k)‖ := by
            rw [one_mul]; exact norm_sum_le _ _
        _ ≤ _ := Finset.sum_le_sum hpt
    have hCS : (∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖)) ^ 2
        ≤ (∑ k ∈ univ.erase i, S i k) * ∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖) ^ 2 := by
      refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun k _ => hS0 i k)
        (fun k _ => mul_nonneg (hS0 i k) (sq_nonneg _)) fun k _ => le_of_eq (by ring)
    have hE1 : ∑ k ∈ univ.erase i, S i k ≤ 1 :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i univ)
        fun k _ _ => hS0 i k) (hSrow i)
    have hE2 : ∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖) ^ 2
        ≤ ∑ k ∈ univ.erase i, S i k * (4 * δ ^ 2 * (162 * Φ ^ 2 * Λ)) := by
      refine Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left ?_ (hS0 i k)
      have hki : i ≠ k := (Finset.ne_of_mem_erase hk).symm
      have h1 := norm_sq_green_offdiag_le hGM hMG hm hΩ hδ hS0 hSrow hScol hΦ1 hΦδ hLrow hLcol
        hΛ1 hΛ2 hki
      calc (2 * δ * ‖G i k‖) ^ 2 = 4 * δ ^ 2 * ‖G i k‖ ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
    have hE3 : ∑ k ∈ univ.erase i, S i k * (4 * δ ^ 2 * (162 * Φ ^ 2 * Λ))
        ≤ 4 * δ ^ 2 * (162 * Φ ^ 2 * Λ) := by
      rw [← Finset.sum_mul]
      have : 0 ≤ 4 * δ ^ 2 * (162 * Φ ^ 2 * Λ) := by positivity
      nlinarith
    have hE4 : 4 * δ ^ 2 * (162 * Φ ^ 2 * Λ) ≤ 18 * Φ * Λ := by
      have h1 : 4 * δ ^ 2 * (162 * Φ ^ 2 * Λ) = 18 * (36 * Φ * δ ^ 2) * (Φ * Λ) := by ring
      have h2 : 0 ≤ Φ * Λ := mul_nonneg hΦ hΛ0
      nlinarith
    have hS : 0 ≤ ∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖) ^ 2 :=
      Finset.sum_nonneg fun k _ => mul_nonneg (hS0 i k) (sq_nonneg _)
    have hA4sq : ‖A4‖ ^ 2 ≤ (∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hA4le 2
    have hE5 : (∑ k ∈ univ.erase i, S i k) * ∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖) ^ 2
        ≤ 1 * ∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖) ^ 2 :=
      mul_le_mul_of_nonneg_right hE1 hS
    linarith
  -- assemble
  have htri : ‖H i i - A2 + A3 + A4‖ ≤ ‖H i i‖ + ‖A2‖ + ‖A3‖ + ‖A4‖ := by
    calc ‖H i i - A2 + A3 + A4‖ ≤ ‖H i i - A2 + A3‖ + ‖A4‖ := norm_add_le _ _
      _ ≤ ‖H i i - A2‖ + ‖A3‖ + ‖A4‖ := by linarith [norm_add_le (H i i - A2) A3]
      _ ≤ ‖H i i‖ + ‖A2‖ + ‖A3‖ + ‖A4‖ := by linarith [norm_sub_le (H i i) A2]
  have hsq : ‖H i i - A2 + A3 + A4‖ ^ 2
      ≤ 4 * (‖H i i‖ ^ 2 + ‖A2‖ ^ 2 + ‖A3‖ ^ 2 + ‖A4‖ ^ 2) := by
    have h0 := norm_nonneg (H i i - A2 + A3 + A4)
    have h1 : ‖H i i - A2 + A3 + A4‖ ^ 2 ≤ (‖H i i‖ + ‖A2‖ + ‖A3‖ + ‖A4‖) ^ 2 :=
      pow_le_pow_left₀ h0 htri 2
    nlinarith [sq_nonneg (‖H i i‖ - ‖A2‖), sq_nonneg (‖H i i‖ - ‖A3‖),
      sq_nonneg (‖H i i‖ - ‖A4‖), sq_nonneg (‖A2‖ - ‖A3‖), sq_nonneg (‖A2‖ - ‖A4‖),
      sq_nonneg (‖A3‖ - ‖A4‖)]
  have hΦΛ : Φ * Λ ≤ Φ ^ 2 * Λ := by
    have : Φ ≤ Φ ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hΛ0
  have hΛΦ : Λ ≤ Φ ^ 2 * Λ := by
    have : 1 ≤ Φ ^ 2 := by nlinarith
    nlinarith
  nlinarith

/-- **Stability of `1 - ξ S` in `max → max` norm**, with constant `K`: whenever
`|v_i - ξ (S v)_i| ≤ B` for all `i`, then `|v_i| ≤ K B` for all `i`.  This is the paper's
`‖(1 - t m² S)⁻¹‖_{max→max} = O(1)`, stated without forming the inverse. -/
def Stable (S : n → n → ℝ) (ξ : ℂ) (K : ℝ) : Prop :=
  ∀ (v : n → ℂ) (B : ℝ), (∀ i, ‖v i - ξ * ∑ k, (S i k : ℂ) * v k‖ ≤ B) → ∀ i, ‖v i‖ ≤ K * B

/-- **(4.3)**, deterministic form.  On the event `Ω`, given the three LDE inputs, the bound
`|H_{ii}|² ≤ Φ S_{ii}` and stability of `1 - t m² S` with constant `K`,
`|G_{ii} - m|² ≤ 2160 K² Φ² Λ`, where `Λ` bounds `∑_{k,l} S_{ik}|G_{kl}|²S_{lj}` and `S_{ij}`
(in the block model `Λ = 2 max_{a,b} L_{(+,-),(a,b)}`, see `RBM.norm_sq_green_diag_sub_le_blk`). -/
theorem norm_sq_green_diag_sub_le [Nonempty n] (hGM : G * (H - z • (1 : Matrix n n ℂ)) = 1)
    (hMG : (H - z • (1 : Matrix n n ℂ)) * G = 1) (hm : ‖m‖ = 1) {t : ℝ}
    (hmz : m * ((t : ℂ) * m + z) = -1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hΩ : GoodEvent G m δ)
    (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k) (hSrow : ∀ i, ∑ k, S i k = 1)
    (hScol : ∀ j, ∑ l, S l j ≤ 1) (hΦ1 : 1 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (hLrow : LDERow H G S Φ) (hLcol : LDECol H G S Φ) (hLquad : LDEQuad H G S t Φ)
    (hLdiag : ∀ i, ‖H i i‖ ^ 2 ≤ Φ * S i i) {Λ : ℝ}
    (hΛ1 : ∀ i j, ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j ≤ Λ) (hΛ2 : ∀ i j, S i j ≤ Λ)
    {K : ℝ} (hKδ : K * δ ≤ 1 / 2) (hStab : Stable S ((t : ℂ) * m ^ 2) K)
    (i : n) :
    ‖G i i - m‖ ^ 2 ≤ 2160 * K ^ 2 * Φ ^ 2 * Λ := by
  obtain ⟨i₀⟩ := (inferInstance : Nonempty n)
  have hΛ0 : 0 ≤ Λ := le_trans (hS0 i₀ i₀) (hΛ2 i₀ i₀)
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) (hΩ i₀ i₀)
  have hSrow' : ∀ i, ∑ k, S i k ≤ 1 := fun i => (hSrow i).le
  have hm0 : m ≠ 0 := by
    intro h; rw [h, norm_zero] at hm; exact zero_ne_one hm
  set ε := Real.sqrt (240 * Φ ^ 2 * Λ) with hε
  have hε0 : 0 ≤ ε := Real.sqrt_nonneg _
  set e : n → ℂ := fun i => (G i i)⁻¹ + z + (t : ℂ) * ∑ k, (S i k : ℂ) * G k k with he
  have heb : ∀ i, ‖e i‖ ≤ ε := by
    intro i
    rw [hε, Real.le_sqrt (norm_nonneg _) (by positivity)]
    exact norm_sq_selfEnergy_err_le hGM hMG hm ht0 ht1 hΩ hδ hS0 hSrow' hScol hΦ1 hΦδ hLrow
      hLcol hLquad hLdiag hΛ1 hΛ2 i
  set v : n → ℂ := fun k => G k k - m with hv
  have hvδ : ∀ k, ‖v k‖ ≤ δ := fun k => hΩ.norm_diag_sub_le k
  obtain ⟨k₀, hk₀⟩ := Finite.exists_max fun k => ‖v k‖
  set V := ‖v k₀‖ with hV
  -- the exact identity `v_i - t m² (S v)_i = -m² e_i + m v_i x_i`
  have hident : ∀ i, v i - (t : ℂ) * m ^ 2 * ∑ k, (S i k : ℂ) * v k
      = -(m ^ 2 * e i) + m * v i * ((t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i) := by
    intro i
    have hGii := hΩ.diag_ne_zero hm hδ i
    have hSv : ∑ k, (S i k : ℂ) * G k k = ∑ k, (S i k : ℂ) * v k + m := by
      have h1 : ∑ k, (S i k : ℂ) * v k = ∑ k, (S i k : ℂ) * G k k - m := by
        have h2 : ∑ k, (S i k : ℂ) = 1 := by exact_mod_cast hSrow i
        rw [hv]
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h2, one_mul]
      rw [h1]; ring
    have hinv : (G i i)⁻¹ = m⁻¹ - ((t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i) := by
      have hz : z = -m⁻¹ - (t : ℂ) * m := by
        field_simp
        linear_combination hmz
      simp only [he, hSv, hz]
      ring
    have h1 : G i i * (m⁻¹ - ((t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i)) = 1 := by
      rw [← hinv]; exact mul_inv_cancel₀ hGii
    have hmm : m * m⁻¹ = 1 := mul_inv_cancel₀ hm0
    simp only [hv]
    linear_combination m * h1 - G i i * hmm
  -- bound on the right-hand side
  have hSvb : ∀ i, ‖∑ k, (S i k : ℂ) * v k‖ ≤ V := by
    intro i
    calc ‖∑ k, (S i k : ℂ) * v k‖ ≤ ∑ k, ‖(S i k : ℂ) * v k‖ := norm_sum_le _ _
      _ ≤ ∑ k, S i k * V := Finset.sum_le_sum fun k _ => by
          rw [norm_mul, Complex.norm_of_nonneg (hS0 i k)]
          exact mul_le_mul_of_nonneg_left (hk₀ k) (hS0 i k)
      _ = V := by rw [← Finset.sum_mul, hSrow i, one_mul]
  have hBi : ∀ i, ‖v i - (t : ℂ) * m ^ 2 * ∑ k, (S i k : ℂ) * v k‖ ≤ 3 / 2 * ε + δ * V := by
    intro i
    rw [hident i]
    have hx : ‖(t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i‖ ≤ V + ε := by
      calc ‖(t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i‖
          ≤ ‖(t : ℂ) * ∑ k, (S i k : ℂ) * v k‖ + ‖e i‖ := norm_sub_le _ _
        _ ≤ V + ε := by
          rw [norm_mul, Complex.norm_of_nonneg ht0]
          have h1 := hSvb i
          have h2 : t * ‖∑ k, (S i k : ℂ) * v k‖ ≤ 1 * V :=
            mul_le_mul ht1 h1 (norm_nonneg _) zero_le_one
          linarith [heb i]
    have hV0 : 0 ≤ V := norm_nonneg _
    calc ‖-(m ^ 2 * e i) + m * v i * ((t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i)‖
        ≤ ‖-(m ^ 2 * e i)‖ + ‖m * v i * ((t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i)‖ :=
          norm_add_le _ _
      _ = ‖e i‖ + ‖v i‖ * ‖(t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i‖ := by
          rw [norm_neg, norm_mul, norm_mul, norm_mul, norm_pow, hm]; ring
      _ ≤ ε + δ * (V + ε) := by
          have := mul_le_mul (hvδ i) hx (norm_nonneg _) hδ0
          linarith [heb i]
      _ ≤ 3 / 2 * ε + δ * V := by nlinarith
  have hst := hStab v (3 / 2 * ε + δ * V) hBi
  have hVb : V ≤ 3 * K * ε := by
    have h1 := hst k₀
    have h2 : K * (δ * V) ≤ 1 / 2 * V := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hKδ (norm_nonneg _)
    rw [← hV] at h1
    nlinarith
  have hvi : ‖v i‖ ≤ 3 * K * ε := (hk₀ i).trans hVb
  have hsq : ‖v i‖ ^ 2 ≤ (3 * K * ε) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hvi 2
  have hε2 : ε ^ 2 = 240 * Φ ^ 2 * Λ := Real.sq_sqrt (by positivity)
  calc ‖G i i - m‖ ^ 2 = ‖v i‖ ^ 2 := rfl
    _ ≤ (3 * K * ε) ^ 2 := hsq
    _ = 9 * K ^ 2 * ε ^ 2 := by ring
    _ = 2160 * K ^ 2 * Φ ^ 2 * Λ := by rw [hε2]; ring

end EntryBound

section Averaged

variable {n : Type*} [Fintype n]

/-- **The self-consistent step of (4.5).**  Let `x_i` stand for `E_i(G_{ii} - m)`.  If
`x_i = ξ ∑_k S_{ik}(G_{kk} - m) + O(A)` (the Gaussian integration by parts display on p. 50)
and `∑_k S_{ik}(1 - E_k)(G_{kk} - m) = O(B)` (the fluctuation averaging (4.12) with
`t_k = S_{ik}`), then stability of `1 - ξS` gives `|x_i| ≤ K (A + B)`. -/
theorem norm_condExp_le {S : n → n → ℝ} {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1)
    {K : ℝ} (hStab : Stable S ξ K) {G : Matrix n n ℂ} {m : ℂ} (x : n → ℂ) {A B : ℝ}
    (hIBP : ∀ i, ‖x i - ξ * ∑ k, (S i k : ℂ) * (G k k - m)‖ ≤ A)
    (hFA : ∀ i, ‖∑ k, (S i k : ℂ) * ((G k k - m) - x k)‖ ≤ B) (i : n) :
    ‖x i‖ ≤ K * (A + B) := by
  refine hStab x (A + B) (fun j => ?_) i
  have hsplit : x j - ξ * ∑ k, (S j k : ℂ) * x k
      = (x j - ξ * ∑ k, (S j k : ℂ) * (G k k - m))
        + ξ * ∑ k, (S j k : ℂ) * ((G k k - m) - x k) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  calc ‖(x j - ξ * ∑ k, (S j k : ℂ) * (G k k - m))
        + ξ * ∑ k, (S j k : ℂ) * ((G k k - m) - x k)‖
      ≤ ‖x j - ξ * ∑ k, (S j k : ℂ) * (G k k - m)‖
        + ‖ξ * ∑ k, (S j k : ℂ) * ((G k k - m) - x k)‖ := norm_add_le _ _
    _ ≤ A + 1 * B := by
        rw [norm_mul]
        have := mul_le_mul hξ (hFA j) (norm_nonneg _) zero_le_one
        linarith [hIBP j]
    _ = A + B := by ring

/-- **(4.5)**, deterministic form: for coefficients with `∑_k |c_k| ≤ 1`, if
`∑_k c_k (1 - E_k)(G_{kk} - m) = O(B')` (fluctuation averaging (4.12)) then
`|∑_k c_k (G_{kk} - m)| ≤ B' + K (A + B)`. -/
theorem norm_sum_coef_green_sub_le [Nonempty n] {S : n → n → ℝ}
    {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {K : ℝ} (hStab : Stable S ξ K) {G : Matrix n n ℂ} {m : ℂ}
    (x : n → ℂ) {A B B' : ℝ}
    (hIBP : ∀ i, ‖x i - ξ * ∑ k, (S i k : ℂ) * (G k k - m)‖ ≤ A)
    (hFA : ∀ i, ‖∑ k, (S i k : ℂ) * ((G k k - m) - x k)‖ ≤ B)
    {c : n → ℝ} (hc : ∑ k, |c k| ≤ 1)
    (hFA' : ‖∑ k, (c k : ℂ) * ((G k k - m) - x k)‖ ≤ B') :
    ‖∑ k, (c k : ℂ) * (G k k - m)‖ ≤ B' + K * (A + B) := by
  have hx := norm_condExp_le hξ hStab x hIBP hFA
  obtain ⟨i₀⟩ := (inferInstance : Nonempty n)
  have hX0 : 0 ≤ K * (A + B) := le_trans (norm_nonneg _) (hx i₀)
  have hsplit : ∑ k, (c k : ℂ) * (G k k - m)
      = ∑ k, (c k : ℂ) * ((G k k - m) - x k) + ∑ k, (c k : ℂ) * x k := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsplit]
  have hcx : ‖∑ k, (c k : ℂ) * x k‖ ≤ K * (A + B) := by
    calc ‖∑ k, (c k : ℂ) * x k‖ ≤ ∑ k, ‖(c k : ℂ) * x k‖ := norm_sum_le _ _
      _ ≤ ∑ k, |c k| * (K * (A + B)) := Finset.sum_le_sum fun k _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hx k) (abs_nonneg _)
      _ = (∑ k, |c k|) * (K * (A + B)) := by rw [Finset.sum_mul]
      _ ≤ 1 * (K * (A + B)) := mul_le_mul_of_nonneg_right hc hX0
      _ = K * (A + B) := one_mul _
  linarith [norm_add_le (∑ k, (c k : ℂ) * ((G k k - m) - x k)) (∑ k, (c k : ℂ) * x k)]

end Averaged

/-! ### Instances: the checked `2 × 2` data of RBM2D (`Minor.lean:273-315`,
`EntryCore.lean:846-976`, `c9a24cf`) and the targets of T2029 applied at them -/

/-! ### Check: the Schur identity at a `2 × 2` Hermitian matrix with `z = I` -/

section Check

set_option linter.flexible false in
open Complex in
private theorem minor_check_fin2 :
    let H : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
    let G : Matrix (Fin 2) (Fin 2) ℂ := !![I / 2, 1 / 2; 1 / 2, I / 2]
    H.IsHermitian ∧ green H I = G ∧ G 0 0 ≠ 0 ∧
      (H.submatrix Subtype.val Subtype.val
          - I • (1 : Matrix {a : Fin 2 // a ≠ 0} {a : Fin 2 // a ≠ 0} ℂ))⁻¹ = minorGreen G 0 ∧
      minorGreen G 0 ⟨1, by decide⟩ ⟨1, by decide⟩ = I := by
  intro H G
  have hdet : (H - I • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = -2 := by
    rw [Matrix.det_fin_two]
    simp [H]
    ring_nf
  have hu : IsUnit (H - I • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det := by
    rw [hdet]; exact isUnit_iff_ne_zero.mpr (by norm_num)
  have hGM : G * (H - I • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [G, H, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
      first | ring1 | (ring_nf; simp [Complex.I_sq]; norm_num)
  have hG : green H I = G := by
    unfold green
    exact Matrix.inv_eq_left_inv hGM
  have hG00 : G 0 0 ≠ 0 := by simp [G]
  refine ⟨?_, hG, hG00, ?_, ?_⟩
  · ext a b
    fin_cases a <;> fin_cases b <;> simp [H, Matrix.conjTranspose_apply]
  · rw [← hG] at hG00 ⊢
    exact inv_minor_resolvent hu 0 hG00
  · simp only [minorGreen_apply, G]
    simp
    ring_nf
    rw [Complex.inv_I]
    ring


end Check

/-! ### Check: `norm_sq_green_offdiag_le` and `norm_sq_green_diag_sub_le` at a `2 × 2` Hermitian
matrix with `z = I` and a constant profile `S`

`H = [[0, 1/8], [1/8, 0]]`, `G = (H - I)⁻¹ = [[64/65 I, 8/65], [8/65, 64/65 I]]`, `m = I`,
`t = 0`, `δ = 1/8`, `Φ = K = 1`, `Λ = 1/2`, `S ≡ 1/2`.  All hypotheses of the two theorems hold
together, with nonzero off-diagonal entries.  Here `t = 0`, so the `t`-dependent terms of the
two theorems are exercised only through their proofs. -/

section Check

open Complex

private noncomputable def chkH : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1 / 8; 1 / 8, 0]
private noncomputable def chkG : Matrix (Fin 2) (Fin 2) ℂ :=
  !![64 / 65 * I, 8 / 65; 8 / 65, 64 / 65 * I]
private noncomputable def chkS : Fin 2 → Fin 2 → ℝ := fun _ _ => 1 / 2

set_option linter.flexible false in
private theorem chk_hGM : chkG * (chkH - I • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [chkG, chkH, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    first | ring1 | (ring_nf; simp [Complex.I_sq]; norm_num)

private theorem chk_hMG : (chkH - I • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * chkG = 1 :=
  mul_eq_one_comm.mp chk_hGM

private theorem chk_herm : chkH.IsHermitian := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [chkH, Matrix.conjTranspose_apply]

private theorem chk_erase {α : Type*} [AddCommMonoid α] (f : Fin 2 → α) {i j : Fin 2}
    (hij : i ≠ j) : ∑ k ∈ univ.erase i, f k = f j := by
  have h0 : (univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have h1 : (univ : Finset (Fin 2)).erase 1 = {0} := by decide
  fin_cases i <;> fin_cases j <;> simp_all

private theorem chk_minor {i j : Fin 2} (hij : i ≠ j) : greenMinor chkG i j j = I := by
  fin_cases i <;> fin_cases j <;> simp_all [greenMinor, chkG]
  all_goals
    field_simp
    ring_nf
    simp [Complex.I_sq]
    norm_num

private theorem chk_norm_diag : ‖(64 / 65 * I - I : ℂ)‖ = 1 / 65 := by
  have : (64 / 65 * I - I : ℂ) = ((-(1 / 65) : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, norm_mul, Complex.norm_I, Complex.norm_real]; norm_num

private theorem chk_norm_G00 : ‖chkG 0 0‖ = 64 / 65 := by
  simp [chkG]

private theorem chk_norm_G01 : ‖chkG 0 1‖ = 8 / 65 := by
  simp [chkG]

private theorem chk_norm_G10 : ‖chkG 1 0‖ = 8 / 65 := by
  simp [chkG]

private theorem chk_norm_G11 : ‖chkG 1 1‖ = 64 / 65 := by
  simp [chkG]

private theorem chk_good : GoodEvent chkG I (1 / 8) := by
  intro x y
  fin_cases x <;> fin_cases y <;> simp [chkG, chk_norm_diag]
  all_goals norm_num

private theorem chk_minor01 : greenMinor chkG 0 1 1 = I := chk_minor (by decide)

private theorem chk_minor10 : greenMinor chkG 1 0 0 = I := chk_minor (by decide)

private theorem chk_erase0 : (univ : Finset (Fin 2)).erase 0 = {1} := by decide

private theorem chk_erase1 : (univ : Finset (Fin 2)).erase 1 = {0} := by decide

private theorem chk_row : LDERow chkH chkG chkS 1 := by
  intro i j hij
  unfold ldeRowLHS ldeRowRHS
  rw [chk_erase _ hij, chk_erase _ hij, chk_minor hij]
  fin_cases i <;> fin_cases j <;> simp_all [chkH, chkS] <;> norm_num

private theorem chk_col : LDECol chkH chkG chkS 1 := by
  intro k j hkj
  unfold ldeColLHS ldeColRHS
  rw [chk_erase _ hkj.symm, chk_erase _ hkj.symm, chk_minor hkj.symm]
  fin_cases k <;> fin_cases j <;> simp_all [chkH, chkS] <;> norm_num

private theorem chk_quad : LDEQuad chkH chkG chkS 0 1 := by
  intro i
  fin_cases i <;>
    simp [ldeQuadLHS, ldeQuadRHS, chk_erase0, chk_erase1, chk_minor01, chk_minor10, chkH, chkS] <;>
    norm_num

private theorem chk_diag_H : ∀ i, ‖chkH i i‖ ^ 2 ≤ 1 * chkS i i := by
  intro i
  fin_cases i <;> simp [chkH, chkS]

private theorem chk_Lam1 :
    ∀ i j, ∑ k, ∑ l, chkS i k * ‖chkG k l‖ ^ 2 * chkS l j ≤ 1 / 2 := by
  intro i j
  simp [Fin.sum_univ_two, chkS, chk_norm_G00, chk_norm_G01, chk_norm_G10, chk_norm_G11]
  norm_num

private theorem chk_stable : Stable chkS (((0 : ℝ) : ℂ) * I ^ 2) 1 := by
  intro v B h i
  simpa using h i

private theorem entry_core_check_fin2 :
    chkH.IsHermitian ∧ green chkH I = chkG ∧
      (∀ i j : Fin 2, i ≠ j → ‖chkG i j‖ ^ 2 ≤ 162 * 1 ^ 2 * (1 / 2)) ∧
      ∀ i : Fin 2, ‖chkG i i - I‖ ^ 2 ≤ 2160 * 1 ^ 2 * 1 ^ 2 * (1 / 2) := by
  have hS0 : ∀ i k, 0 ≤ chkS i k := fun _ _ => by norm_num [chkS]
  have hSsum : ∀ i, ∑ k, chkS i k = 1 := fun i => by
    simp [chkS]
  have hScol : ∀ j, ∑ l, chkS l j ≤ 1 := fun j => by
    simp [chkS]
  have hLam2 : ∀ i j, chkS i j ≤ 1 / 2 := fun _ _ => le_rfl
  have hm : ‖(I : ℂ)‖ = 1 := Complex.norm_I
  refine ⟨chk_herm, ?_, ?_, ?_⟩
  · unfold green
    exact Matrix.inv_eq_left_inv chk_hGM
  · intro i j hij
    exact norm_sq_green_offdiag_le chk_hGM chk_hMG hm chk_good (by norm_num) hS0
      (fun i => (hSsum i).le) hScol le_rfl (by norm_num) chk_row chk_col chk_Lam1 hLam2 hij
  · intro i
    exact norm_sq_green_diag_sub_le chk_hGM chk_hMG hm (t := 0) (by simp) le_rfl zero_le_one
      chk_good (by norm_num) hS0 hSsum hScol le_rfl (by norm_num) chk_row chk_col chk_quad
      chk_diag_H chk_Lam1 hLam2 (K := 1) (by norm_num) chk_stable i


end Check

section Instances

open Complex

private theorem chk_green : green chkH I = chkG := by
  unfold green
  exact Matrix.inv_eq_left_inv chk_hGM

private theorem chk_unit : IsUnit (chkH - I • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det := by
  have hdet : (chkH - I • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = -(65 / 64) := by
    rw [Matrix.det_fin_two]
    simp [chkH]
    ring_nf
  rw [hdet]; exact isUnit_iff_ne_zero.mpr (by norm_num)

/-- Instance of `green_diag_paper` (4.7) at `H = [[0, 1/8], [1/8, 0]]`, `z = I`, `i = 0`. -/
example : green chkH I 0 0 = (chkH 0 0 - I - ∑ k : {a : Fin 2 // a ≠ 0},
    ∑ l : {a : Fin 2 // a ≠ 0}, chkH 0 k.1 * minorGreen (green chkH I) 0 k l * chkH l.1 0)⁻¹ :=
  green_diag_paper chk_unit 0 (by rw [chk_green]; simp [chkG])

/-- Instance of `green_off_diag_paper` (4.8) at the same data, `j = 1`. -/
example : green chkH I 0 1 = -green chkH I 0 0 * ∑ k : {a : Fin 2 // a ≠ 0},
    chkH 0 k.1 * minorGreen (green chkH I) 0 k ⟨1, by decide⟩ :=
  green_off_diag_paper chk_unit 0 (by rw [chk_green]; simp [chkG]) ⟨1, by decide⟩

/-- Instance of `norm_sum_coef_green_sub_le` (4.5) at `G = chkG`, `m = I`, `ξ = 0`, `x = 0`,
`c ≡ 1/2`, `K = 1`, `A = 0`, `B = B' = 1/65`. -/
example : ‖∑ k, (((fun _ : Fin 2 => (1 / 2 : ℝ)) k : ℝ) : ℂ) * (chkG k k - I)‖
    ≤ 1 / 65 + 1 * (0 + 1 / 65) := by
  have hd : ∀ k : Fin 2, chkG k k - I = ((-(1 / 65) : ℝ) : ℂ) * I := by
    intro k
    fin_cases k <;> simp [chkG] <;> ring_nf
  refine norm_sum_coef_green_sub_le (S := chkS) (ξ := ((0 : ℝ) : ℂ) * I ^ 2)
    (by simp) chk_stable (G := chkG) (m := I) (fun _ => 0) (A := 0) (B := 1 / 65) (B' := 1 / 65)
    (by intro i; simp) ?_ (c := fun _ => 1 / 2) (by simp) ?_
  · intro i
    simp only [hd, sub_zero, ← Finset.mul_sum, Fin.sum_univ_two, chkS]
    norm_num [← two_mul, norm_mul, Complex.norm_real]
  · simp only [hd, sub_zero]
    simp

end Instances

section Instance3

open Complex

/-- The constant profile `S ≡ 1/27` on `Zd 3 3` (`27 = 3 ^ 3` sites). -/
private noncomputable def zS : Zd 3 3 → Zd 3 3 → ℝ := fun _ _ => 1 / 27

private theorem zsumc (a : ℂ) : ∑ _k : Zd 3 3, a = 27 * a := by
  simp [Zd, ZMod.card]

private theorem zsumr (a : ℝ) : ∑ _k : Zd 3 3, a = 27 * a := by
  simp [Zd, ZMod.card]

private theorem zsum (i : Zd 3 3) (f : Zd 3 3 → ℂ) :
    ∑ k, (zS i k : ℂ) * f k = (1 / 27 : ℂ) * ∑ k, f k := by
  simp [zS, Finset.mul_sum]

private theorem zstable : Stable zS (1 / 2 : ℂ) 2 := by
  intro v B h i
  obtain ⟨i0, hi0⟩ := Finite.exists_max (fun k => ‖v k‖)
  have hsum : ‖∑ k, (zS i0 k : ℂ) * v k‖ ≤ ‖v i0‖ := by
    rw [zsum, norm_mul]
    have h1 : ‖∑ k, v k‖ ≤ ∑ k, ‖v k‖ := norm_sum_le _ _
    have h2 : ∑ k, ‖v k‖ ≤ ∑ _k : Zd 3 3, ‖v i0‖ := Finset.sum_le_sum fun k _ => hi0 k
    have h3 : ∑ _k : Zd 3 3, ‖v i0‖ = 27 * ‖v i0‖ := zsumr _
    have h4 : ‖(1 / 27 : ℂ)‖ = 1 / 27 := by simp
    rw [h4]
    nlinarith [norm_nonneg (v i0)]
  have h0 := h i0
  have hn : ‖(1 / 2 : ℂ) * ∑ k, (zS i0 k : ℂ) * v k‖ ≤ 1 / 2 * ‖v i0‖ := by
    rw [norm_mul]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [this]; nlinarith [norm_nonneg (v i0)]
  have := norm_sub_norm_le (v i0) ((1 / 2 : ℂ) * ∑ k, (zS i0 k : ℂ) * v k)
  linarith [hi0 i]

/-- Instance of `norm_sum_coef_green_sub_le` (4.5) on the index set `Zd 3 3` of `d = 3`,
`L = 3` (27 sites): `S ≡ 1/27`, `ξ = 1/2`, `K = 2`, `G = 1`, `m = 0`, `x ≡ 1/2`, `c ≡ 1/27`,
`A = 0`, `B = B' = 1/2`; the conclusion is `1 ≤ 3/2`. -/
example : ‖∑ k : Zd 3 3, (((fun _ : Zd 3 3 => (1 / 27 : ℝ)) k : ℝ) : ℂ)
      * ((1 : Matrix (Zd 3 3) (Zd 3 3) ℂ) k k - 0)‖ ≤ 1 / 2 + 2 * (0 + 1 / 2) := by
  refine norm_sum_coef_green_sub_le (S := zS) (ξ := (1 / 2 : ℂ)) (by simp; norm_num) zstable
    (G := (1 : Matrix (Zd 3 3) (Zd 3 3) ℂ)) (m := 0) (fun _ => 1 / 2) (A := 0) (B := 1 / 2)
    (B' := 1 / 2) ?_ ?_ (c := fun _ => 1 / 27) ?_ ?_
  · intro i
    simp [zS]
  · intro i
    simp [zS]
    norm_num
  · simp
  · simp
    norm_num

end Instance3

end RBM.Green
