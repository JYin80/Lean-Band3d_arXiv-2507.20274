/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GreenCore

/-!
# The block Anderson minors: vocabulary, the structural fact, the tower (BA-G5a, file 1 of 3)

Ticket T2401 (design gate `docs/reports/T2401-prove.md`, sections (a), (a′), (G); stage 1b under
Amend 1).  Paper: `paper/tex/7_8_light_weight.tex` (`lem_GbEXP_BA`, `7_8:1916-1948`), band
`paper/tex/3_5_Loop_Hierarchy.tex`.  Everything is deterministic, for one sample.  Sites are
`u = (a, o)` of `Vtx d L W` (block `a`, offset `o`), `M = M^{(B)} ⊗ I` (`hM`), `G^{(S)}` the
resolvent of the principal submatrix on the sites outside `S`, zero-padded.

* `GreenMinor_T`, `GreenMinor_R`, `GreenMinor_Tower`, `GreenMinor_good`, `GreenMinor_YA`,
  `GreenMinor_YX`: the vocabulary of G.8 (`T_{β,o} = Y_o ∪ [β]`, the protected rows
  `R_{β,o} = [β] ∖ {(β, o)}`, the tower of minors `(4.9)`, the protected good event, the
  polynomial families `Y^A`, `Y^X`).
* S1 and the structural fact (ii): `o(x) ≠ o(y) ⇒ M_{xy} = 0` (`GreenMinor_cross`), the removal
  bounds `|G^{(w)}_{xy} - G_{xy}| ≤ (2/κ) |G_{xw}| |G_{wy}|` (`GreenMinor_removal`, one-sided and
  cross-offset forms), `GreenMinor_offset_ne` (the offset fact used by the recursion of S2).
* R1: the tower for the real minors.  `GreenMinor_Gs H z S = (H^{(S)} - z)⁻¹`, zero-padded,
  satisfies `GreenMinor_Tower ((H - z)⁻¹) (GreenMinor_Gs H z)` for Hermitian `H` and `Im z ≠ 0`
  (`GreenMinor_tower`), and at the BA carrier (`GreenMinor_tower_carrier`).

Every theorem has a compiled nonempty instance in the last section (`d = 3`, `L = 3`, `W = 2`;
the BA carrier `sz0`).
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.setOption false
set_option linter.flexible false

noncomputable section
open Filter Matrix Finset
open scoped Kronecker
open RBM RBM.Green RBM.Gauss

namespace RBM.BA

/-! ## 0. Vocabulary: `T_{β,o}`, `R_{β,o}`, the tower of minors, the protected good event, the families `Y^A`, `Y^X` -/

section Setting
variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `T_{β,o} = Y_o ∪ [β]`: the sites of offset `o` and the sites of block `β`. -/
def GreenMinor_T (β : Zd d L) (o : Fin (W ^ d)) : Set (Vtx d L W) := {x | x.2 = o ∨ x.1 = β}

/-- `R_{β,o} = [β] ∖ {(β, o)}`: the protected rows (block `β`, offset `≠ o`). -/
def GreenMinor_R (β : Zd d L) (o : Fin (W ^ d)) : Set (Vtx d L W) := {x | x.1 = β ∧ x.2 ≠ o}

/-- The tower of minors: `Gs S = G^{(S)}` (rows and columns of `S` removed and zero-padded), `Gs ∅ = G`, one step is `(4.9)`. -/
structure GreenMinor_Tower (G : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (Gs : Finset (Vtx d L W) → Matrix (Vtx d L W) (Vtx d L W) ℂ) : Prop where
  base : Gs ∅ = G
  step : ∀ S κ, κ ∉ S → ∀ x y, Gs (insert κ S) x y = greenMinor (Gs S) κ x y

/-- The BA good event on the protected levels: for `S ⊆ R_{β,o}`, `|S| ≤ m₀`, `x, y ∈ T_{β,o} ∖ S`:
`|G^{(S)}_{xy} - M_{xy}| ≤ 2δ` and `|G^{(S)}_{xx}| ≥ κ/2`. -/
def GreenMinor_good (Gs : Finset (Vtx d L W) → Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) (κ δ : ℝ) (m₀ : ℕ) (β : Zd d L) (o : Fin (W ^ d)) : Prop :=
  ∀ S : Finset (Vtx d L W), ↑S ⊆ GreenMinor_R β o → S.card ≤ m₀ → ∀ x y, x ∈ GreenMinor_T β o → y ∈ GreenMinor_T β o →
    x ∉ S → y ∉ S → ‖Gs S x y - M x y‖ ≤ 2 * δ ∧ κ / 2 ≤ ‖Gs S x x‖

/-- `Y^A_u = (s Δ_{uu} - Σ_l D_{ul} Δ_{lu}) / m` (G.8, S3). -/
def GreenMinor_YA (G M D : Matrix (Vtx d L W) (Vtx d L W) ℂ) (s m : ℂ) (u : Vtx d L W) : ℂ :=
  (s * (G u u - M u u) - ∑ l, D u l * (G l u - M l u)) / m

/-- `Y^X_{uy}` (G.8, S3). -/
def GreenMinor_YX (G M D : Matrix (Vtx d L W) (Vtx d L W) ℂ) (s m : ℂ) (u y : Vtx d L W) : ℂ :=
  M u y * (s * (G u u - M u u) - ∑ l, D u l * (G l u - M l u)) / m
    + (∑ l, D u l * (G l y - M l y) - s * (G u y - M u y))
    + ((G u u - M u u) * ∑ l, D u l * (G l y - M l y) - (G u y - M u y) * ∑ l, D u l * (G l u - M l u)) / m

end Setting

/-! ## 1. S1 and the structural fact (ii) -/

/-- **S1** (the `(4.9)` removal bound): `|G^{(w)}_{xy} - G_{xy}| ≤ (2/κ) |G_{xw}| |G_{wy}|` when `|G_{ww}| ≥ κ/2`. -/
theorem GreenMinor_removal {d L W : ℕ} [NeZero L] [NeZero W] {G : Matrix (Vtx d L W) (Vtx d L W) ℂ} {κ : ℝ}
    {w : Vtx d L W} (hκ : 0 < κ) (hw : κ / 2 ≤ ‖G w w‖) (x y : Vtx d L W) :
    ‖greenMinor G w x y - G x y‖ ≤ (2 / κ) * ‖G x w‖ * ‖G w y‖ := by
  have h0 : 0 < ‖G w w‖ := lt_of_lt_of_le (by positivity) hw
  rw [greenMinor_sub, norm_neg, norm_div, norm_mul, div_le_iff₀ h0]
  have h2 : (2 / κ) * ‖G x w‖ * ‖G w y‖ * (κ / 2) ≤ (2 / κ) * ‖G x w‖ * ‖G w y‖ * ‖G w w‖ :=
    mul_le_mul_of_nonneg_left hw (by positivity)
  have h3 : (2 / κ) * ‖G x w‖ * ‖G w y‖ * (κ / 2) = ‖G x w‖ * ‖G w y‖ := by field_simp
  linarith

/-- (ii): `o(x) ≠ o(y) ⇒ M_{xy} = 0` (Kronecker form, `BAMfine_eq`, `GreenSchur.lean:93`); hence `G_{xy} = Δ_{xy}`. -/
theorem GreenMinor_cross {d L W : ℕ} [NeZero L] [NeZero W] {M : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    {Mb : Zd d L → Zd d L → ℂ} (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) {x y : Vtx d L W}
    (h : x.2 ≠ y.2) : M x y = 0 := by
  rw [hM]; simp [h]

/-- One-sided removal bound: `(2/κ) δ ‖G_{wy}‖` when `o(x) ≠ o(w)`. -/
theorem GreenMinor_removal_crossL {d L W : ℕ} [NeZero L] [NeZero W] {G M : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    {Mb : Zd d L → Zd d L → ℂ} {κ δ : ℝ} {w : Vtx d L W}
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hΔ : ∀ a b, ‖G a b - M a b‖ ≤ δ) (hκ : 0 < κ)
    (hw : κ / 2 ≤ ‖G w w‖) (x y : Vtx d L W) (hxw : x.2 ≠ w.2) :
    ‖greenMinor G w x y - G x y‖ ≤ (2 / κ) * δ * ‖G w y‖ := by
  have h1 : ‖G x w‖ ≤ δ := by
    have := hΔ x w
    rwa [GreenMinor_cross hM hxw, sub_zero] at this
  calc ‖greenMinor G w x y - G x y‖ ≤ (2 / κ) * ‖G x w‖ * ‖G w y‖ := GreenMinor_removal hκ hw x y
    _ ≤ (2 / κ) * δ * ‖G w y‖ := by gcongr

/-- One-sided removal bound: `(2/κ) δ ‖G_{xw}‖` when `o(w) ≠ o(y)`. -/
theorem GreenMinor_removal_crossR {d L W : ℕ} [NeZero L] [NeZero W] {G M : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    {Mb : Zd d L → Zd d L → ℂ} {κ δ : ℝ} {w : Vtx d L W}
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hΔ : ∀ a b, ‖G a b - M a b‖ ≤ δ) (hκ : 0 < κ)
    (hw : κ / 2 ≤ ‖G w w‖) (x y : Vtx d L W) (hwy : w.2 ≠ y.2) :
    ‖greenMinor G w x y - G x y‖ ≤ (2 / κ) * δ * ‖G x w‖ := by
  have h1 : ‖G w y‖ ≤ δ := by
    have := hΔ w y
    rwa [GreenMinor_cross hM hwy, sub_zero] at this
  calc ‖greenMinor G w x y - G x y‖ ≤ (2 / κ) * ‖G x w‖ * ‖G w y‖ := GreenMinor_removal hκ hw x y
    _ ≤ (2 / κ) * ‖G x w‖ * δ := by gcongr
    _ = (2 / κ) * δ * ‖G x w‖ := by ring

/-- **S1, cross-offset form**: `(2/κ) δ²` when `o(x) ≠ o(w)` and `o(w) ≠ o(y)`. -/
theorem GreenMinor_removal_cross {d L W : ℕ} [NeZero L] [NeZero W] {G M : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    {Mb : Zd d L → Zd d L → ℂ} {κ δ : ℝ} {w : Vtx d L W}
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hΔ : ∀ a b, ‖G a b - M a b‖ ≤ δ) (hκ : 0 < κ)
    (hw : κ / 2 ≤ ‖G w w‖) (x y : Vtx d L W) (hxw : x.2 ≠ w.2) (hwy : w.2 ≠ y.2) :
    ‖greenMinor G w x y - G x y‖ ≤ (2 / κ) * δ ^ 2 := by
  have h1 : ‖G w y‖ ≤ δ := by
    have := hΔ w y
    rwa [GreenMinor_cross hM hwy, sub_zero] at this
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) (hΔ w y)
  calc ‖greenMinor G w x y - G x y‖ ≤ (2 / κ) * δ * ‖G w y‖ := GreenMinor_removal_crossL hM hΔ hκ hw x y hxw
    _ ≤ (2 / κ) * δ * δ := by gcongr
    _ = (2 / κ) * δ ^ 2 := by ring

/-- (ii) in the `T`/`R` form used by the recursion of S2: for `w ∈ R_{β,o}` and `x ∈ T_{β,o}`, `x ≠ w`, the offsets differ
(`x` of offset `o`: `o(w) ≠ o`; `x` in block `β`: same block, different site). -/
theorem GreenMinor_offset_ne {d L W : ℕ} [NeZero L] [NeZero W] {β : Zd d L} {o : Fin (W ^ d)} {w x : Vtx d L W}
    (hw : w ∈ GreenMinor_R β o) (hx : x ∈ GreenMinor_T β o) (hxw : x ≠ w) : x.2 ≠ w.2 := by
  obtain ⟨hw1, hw2⟩ := hw
  intro h
  rcases hx with hx | hx
  · exact hw2 (h.symm.trans hx)
  · exact hxw (Prod.ext (hx.trans hw1.symm) h)

/-! ## 2. R1: the tower for the real minors

`GreenMinor_Gs H z S` is the resolvent `(H^{(S)} - z)⁻¹` of the principal submatrix of `H` on the sites outside `S`,
zero-padded (the twin of `Green.greenSetMat` for an arbitrary matrix: the band's version is tied to the band Hamiltonian).
For Hermitian `H` and `Im z ≠ 0` every principal submatrix of `H - z` is invertible with nonvanishing diagonal resolvent
(`green_diag_ne_zero`), so `(4.9)` passes from `S` to `insert κ S` (`GreenMinor_Gs_insert`): this is the `GreenMinor_Tower`. -/

section Tower
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `G^{(S)} = (H^{(S)} - z)⁻¹` with `H^{(S)}` the principal submatrix of `H` on `{a ∉ S}`, extended by `0` to the rows and
columns of `S` (the extension makes the difference calculus total: no side condition travels with the recursion). -/
def GreenMinor_Gs (H : Matrix ι ι ℂ) (z : ℂ) (S : Finset ι) : Matrix ι ι ℂ :=
  Matrix.of fun x y => if hx : x ∈ S then 0 else if hy : y ∈ S then 0 else
    green (H.submatrix (Subtype.val : {a // a ∉ S} → ι) Subtype.val) z ⟨x, hx⟩ ⟨y, hy⟩

variable (H : Matrix ι ι ℂ) (z : ℂ)

theorem GreenMinor_Gs_of_mem_left {S : Finset ι} {x : ι} (hx : x ∈ S) (y : ι) : GreenMinor_Gs H z S x y = 0 := by
  simp [GreenMinor_Gs, hx]

theorem GreenMinor_Gs_of_mem_right {S : Finset ι} {y : ι} (hy : y ∈ S) (x : ι) : GreenMinor_Gs H z S x y = 0 := by
  by_cases hx : x ∈ S <;> simp [GreenMinor_Gs, hx, hy]

theorem GreenMinor_Gs_apply {S : Finset ι} {x y : ι} (hx : x ∉ S) (hy : y ∉ S) :
    GreenMinor_Gs H z S x y = green (H.submatrix (Subtype.val : {a // a ∉ S} → ι) Subtype.val) z ⟨x, hx⟩ ⟨y, hy⟩ := by
  simp [GreenMinor_Gs, hx, hy]

/-- Level `∅` is the full resolvent. -/
theorem GreenMinor_Gs_empty : GreenMinor_Gs H z ∅ = green H z := by
  ext x y
  rw [GreenMinor_Gs_apply H z (Finset.notMem_empty x) (Finset.notMem_empty y)]
  set e : {a : ι // a ∉ (∅ : Finset ι)} ≃ ι := Equiv.subtypeUnivEquiv fun a => Finset.notMem_empty a with he
  have hsub : (H.submatrix (Subtype.val : {a : ι // a ∉ (∅ : Finset ι)} → ι) Subtype.val) -
      z • (1 : Matrix {a : ι // a ∉ (∅ : Finset ι)} {a : ι // a ∉ (∅ : Finset ι)} ℂ) =
      (H - z • (1 : Matrix ι ι ℂ)).submatrix ⇑e ⇑e := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.submatrix_apply, smul_eq_mul, he, Equiv.subtypeUnivEquiv_apply]
    by_cases h : i = j
    · subst h; simp
    · have h' : i.1 ≠ j.1 := fun hh => h (Subtype.ext hh)
      rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h']
  unfold green
  rw [hsub, Matrix.inv_submatrix_equiv]
  simp [he]

/-- Removing `κ` from `{a ∉ S}` is passing to `{a ∉ insert κ S}`. -/
def GreenMinor_insertEquiv {S : Finset ι} {κ : ι} (hκ : κ ∉ S) :
    {y : {x : ι // x ∉ S} // y ≠ ⟨κ, hκ⟩} ≃ {x : ι // x ∉ insert κ S} where
  toFun y := ⟨y.1.1, by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun h => y.2 (Subtype.ext h), y.1.2⟩⟩
  invFun x := ⟨⟨x.1, fun h => x.2 (Finset.mem_insert_of_mem h)⟩, by
    intro h
    exact x.2 (by rw [show x.1 = κ from congrArg Subtype.val h]; exact Finset.mem_insert_self κ S)⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

/-- `(4.9)` between `G^{(S)}` and `G^{(insert κ S)}` at the entries that survive. -/
theorem GreenMinor_Gs_insert_apply (hH : H.IsHermitian) (hz : z.im ≠ 0) {S : Finset ι} {κ : ι} (hκ : κ ∉ S)
    {x y : ι} (hx : x ∉ insert κ S) (hy : y ∉ insert κ S) :
    GreenMinor_Gs H z (insert κ S) x y = greenMinor (GreenMinor_Gs H z S) κ x y := by
  classical
  have hxS : x ∉ S := fun h => hx (Finset.mem_insert_of_mem h)
  have hyS : y ∉ S := fun h => hy (Finset.mem_insert_of_mem h)
  set Hν : Matrix {a : ι // a ∉ S} {a : ι // a ∉ S} ℂ := H.submatrix Subtype.val Subtype.val with hHν
  have hHνh : Hν.IsHermitian := hH.submatrix _
  have hdet : IsUnit (Hν - z • (1 : Matrix {a : ι // a ∉ S} {a : ι // a ∉ S} ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (RBM.isUnit_sub_smul_of_isHermitian hHνh hz)
  set Mν : Matrix {a : ι // a ∉ S} {a : ι // a ∉ S} ℂ := Hν - z • 1 with hMν
  set Gν : Matrix {a : ι // a ∉ S} {a : ι // a ∉ S} ℂ := green Hν z with hGν
  have hGM : Gν * Mν = 1 := Matrix.nonsing_inv_mul Mν hdet
  set i : {a : ι // a ∉ S} := ⟨κ, hκ⟩ with hi
  have hGii : Gν i i ≠ 0 := green_diag_ne_zero hHνh hz i
  set e := GreenMinor_insertEquiv hκ with he
  set A : Matrix {a : ι // a ∉ insert κ S} {a : ι // a ∉ insert κ S} ℂ :=
    H.submatrix Subtype.val Subtype.val - z • 1 with hA
  have hminor : minorMat Mν i = A.submatrix ⇑e ⇑e := by
    ext y w
    have hone : (1 : Matrix {a : ι // a ∉ S} {a : ι // a ∉ S} ℂ) y.1 w.1 =
        (1 : Matrix {a : ι // a ∉ insert κ S} {a : ι // a ∉ insert κ S} ℂ) (e y) (e w) := by
      by_cases h : y.1.1 = w.1.1
      · have h1 : y.1 = w.1 := Subtype.ext h
        have h2 : e y = e w := Subtype.ext h
        rw [h1, h2, Matrix.one_apply_eq, Matrix.one_apply_eq]
      · have h1 : y.1 ≠ w.1 := fun hh => h (congrArg Subtype.val hh)
        have h2 : e y ≠ e w := fun hh => h (congrArg (fun x : {a : ι // a ∉ insert κ S} => x.1) hh)
        rw [Matrix.one_apply_ne h1, Matrix.one_apply_ne h2]
    simp only [minorMat_apply, hMν, hHν, hA, Matrix.sub_apply, Matrix.smul_apply, Matrix.submatrix_apply, smul_eq_mul]
    rw [hone]
    rfl
  have hinv : minorGreen Gν i =
      (green (H.submatrix (Subtype.val : {a : ι // a ∉ insert κ S} → ι) Subtype.val) z).submatrix ⇑e ⇑e := by
    rw [← inv_minorMat hGM i hGii, hminor, Matrix.inv_submatrix_equiv]
    rfl
  have hane : (⟨x, hxS⟩ : {a : ι // a ∉ S}) ≠ i := by
    intro h
    exact hx (by rw [show x = κ from congrArg Subtype.val h]; exact Finset.mem_insert_self κ S)
  have hbne : (⟨y, hyS⟩ : {a : ι // a ∉ S}) ≠ i := by
    intro h
    exact hy (by rw [show y = κ from congrArg Subtype.val h]; exact Finset.mem_insert_self κ S)
  have key := congrFun (congrFun hinv ⟨_, hane⟩) ⟨_, hbne⟩
  simp only [minorGreen_apply, Matrix.submatrix_apply] at key
  rw [GreenMinor_Gs_apply H z hx hy, greenMinor, GreenMinor_Gs_apply H z hxS hyS, GreenMinor_Gs_apply H z hxS hκ,
    GreenMinor_Gs_apply H z hκ hyS, GreenMinor_Gs_apply H z hκ hκ]
  exact key.symm

/-- `(4.9)` between consecutive iterated minors, at every entry (the padding makes the removed rows consistent). -/
theorem GreenMinor_Gs_insert (hH : H.IsHermitian) (hz : z.im ≠ 0) {S : Finset ι} {κ : ι} (hκ : κ ∉ S) (x y : ι) :
    GreenMinor_Gs H z (insert κ S) x y = greenMinor (GreenMinor_Gs H z S) κ x y := by
  have hκκ : GreenMinor_Gs H z S κ κ ≠ 0 := by
    rw [GreenMinor_Gs_apply H z hκ hκ]
    exact green_diag_ne_zero (H := H.submatrix (Subtype.val : {a // a ∉ S} → ι) Subtype.val)
      (hH.submatrix (Subtype.val : {a // a ∉ S} → ι)) hz (⟨κ, hκ⟩ : {a // a ∉ S})
  by_cases hx : x ∈ insert κ S
  · rw [GreenMinor_Gs_of_mem_left H z hx, greenMinor]
    rcases Finset.mem_insert.1 hx with rfl | hxS
    · field_simp
      ring
    · rw [GreenMinor_Gs_of_mem_left H z hxS, GreenMinor_Gs_of_mem_left H z hxS]
      simp
  by_cases hy : y ∈ insert κ S
  · rw [GreenMinor_Gs_of_mem_right H z hy, greenMinor]
    rcases Finset.mem_insert.1 hy with rfl | hyS
    · field_simp
      ring
    · rw [GreenMinor_Gs_of_mem_right H z hyS, GreenMinor_Gs_of_mem_right H z hyS]
      simp
  exact GreenMinor_Gs_insert_apply H z hH hz hκ hx hy

end Tower

section TowerVtx
variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- **R1**: for Hermitian `H` and `Im z ≠ 0` the principal-submatrix resolvents form a tower over `G = (H - z)⁻¹`. -/
theorem GreenMinor_tower {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    GreenMinor_Tower (green H z) (GreenMinor_Gs H z) where
  base := GreenMinor_Gs_empty H z
  step := fun _ _ hκ x y => GreenMinor_Gs_insert H z hH hz hκ x y

end TowerVtx

section Carrier
variable {d : ℕ}

/-- `D + X` of the BA carrier is the fine Hamiltonian `g₀ Ψ + V` read on the block-product index: it is Hermitian. -/
theorem GreenMinor_carrier_herm (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) :
    (GreenCore_Dc sz z n + GreenCore_Xc sz n t ω).IsHermitian := by
  have hH : (sz.seqHflowBA (BAflowLam0 sz z) n t ω).IsHermitian := by
    unfold Sizes.seqHflowBA
    refine IsHermitian.add ?_ (Sizes.seqHflow_isHermitian (sz.withLam 0) n t ω)
    unfold IsHermitian
    rw [conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
      show star (BAflowLam0 sz z n : ℂ) = (BAflowLam0 sz z n : ℂ) from Complex.conj_ofReal _]
  have h : GreenCore_Dc sz z n + GreenCore_Xc sz n t ω =
      blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA (BAflowLam0 sz z) n t ω) := by
    ext u v
    simp [blockMat, Sizes.seqHflowBA, PsiI, GreenCore_Dc, GreenCore_Xc, BAX]
  rw [h]
  exact hH.submatrix _

/-- **R1 at the BA carrier**: the real minors of `G_t = (D + X - z_t)⁻¹` (`D = g₀ Ψ`, `X` the Gaussian part, `z_t = E + (1 - t) m`)
form a tower, for every sample `ω` and `0 ≤ t ≤ T₀` (the structural input is `GreenCore_carrier`; `Im z_t > 0` is `ba_G_data`). -/
theorem GreenMinor_tower_carrier {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) {z : ℕ → ℂ} (h : BAFlow sz κ ε 𝔠 𝔡 z)
    (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) (ω : sz.SeqΩ) :
    GreenMinor_Tower (GreenCore_Gc sz z n t ω)
      (GreenMinor_Gs (GreenCore_Dc sz z n + GreenCore_Xc sz n t ω)
        (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t)) := by
  obtain ⟨hGR, -⟩ := GreenCore_carrier hκ sz h n ht0 ht ω (m := BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
    (s := (BAflowEs sz z n : ℂ) + BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
    (zt := ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t) rfl rfl rfl
  have him : (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t).im ≠ 0 :=
    (ba_G_data hκ sz h n ht0 ht).2.2.2.1.ne'
  have hG : GreenCore_Gc sz z n t ω =
      green (GreenCore_Dc sz z n + GreenCore_Xc sz n t ω)
        (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t) := by
    unfold green
    exact (Matrix.inv_eq_left_inv hGR).symm
  rw [hG]
  exact GreenMinor_tower (GreenMinor_carrier_herm sz z n t ω) him

end Carrier

/-! ## 3. Nonempty instances (`d = 3`, `L = 3`, `W = 2`: the hand-made datum; `sz0` at `n = 0`: the BA carrier)

The hand-made datum `GreenMinorInst` is one block `0` with the two sites `p = (0, 0)`, `q = (0, 1)` of different offsets,
`m = i`, `M = m I` (zero inter-block coupling), `Δ = ε (E_{pq} + E_{qp})` with `ε = 1/100`, so `G = M + Δ ≠ M`; `H := Δ` is a
Hermitian matrix with a nonzero off-diagonal entry, whose principal-submatrix resolvents form the tower of R1. -/

namespace GreenMinorInst

abbrev HV : Type := Vtx 3 3 2
/-- the site `p = (block 0, offset 0)` -/
def hp : HV := (0, 0)
/-- the site `q = (block 0, offset 1)`, in the protected rows `R_{0,0}` -/
def hq : HV := (0, 1)
/-- `m = i` -/
def hm : ℂ := Complex.I
/-- the cross-offset entry `Δ_{pq} = Δ_{qp} = ε = 1/100` -/
def hε : ℂ := ((1 / 100 : ℝ) : ℂ)
/-- zero inter-block coupling: `M^{(B)} = m I` -/
def hMb : Zd 3 3 → Zd 3 3 → ℂ := fun a b => if a = b then hm else 0
def hM : Matrix HV HV ℂ := Matrix.of fun u v => if u.2 = v.2 then hMb u.1 v.1 else 0
def hΔ : Matrix HV HV ℂ := Matrix.of fun x y => if (x = hp ∧ y = hq) ∨ (x = hq ∧ y = hp) then hε else 0
/-- `G = M + Δ`: block diagonal, one `2 × 2` block on `{p, q}`, `‖Δ‖_max = ε ≠ 0` -/
def hG : Matrix HV HV ℂ := hM + hΔ
/-- the hopping `D = g₀ Ψ`, `g₀ = 1/10` -/
def hD : Matrix HV HV ℂ := Matrix.of fun u l => if u.2 = l.2 ∧ Adj 3 3 u.1 l.1 then ((1 / 10 : ℝ) : ℂ) else 0
/-- `y = (e_0, offset 0)`: a block `≠ 0`, the offset of `p` -/
def hy : HV := (Pi.single 0 1, 0)

theorem hΔ_herm : hΔ.IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply, hΔ, Matrix.of_apply]
  by_cases h : (x = hp ∧ y = hq) ∨ (x = hq ∧ y = hp)
  · have h' : (y = hp ∧ x = hq) ∨ (y = hq ∧ x = hp) := by tauto
    simp [h, h', hε]
  · have h' : ¬ ((y = hp ∧ x = hq) ∨ (y = hq ∧ x = hp)) := by tauto
    simp [h, h']

end GreenMinorInst

section HandMade
open GreenMinorInst

-- S1: the removal bound at `w = q`, `x = y = p` (`G^{(q)}_{pp} - G_{pp} = -ε²/m`)
example : ‖greenMinor hG hq hp hp - hG hp hp‖ ≤ (2 / (1 / 2 : ℝ)) * ‖hG hp hq‖ * ‖hG hq hp‖ := by
  have hqq : hG hq hq = hm := by
    have : hq ≠ hp := fun h' => (by decide : hp ≠ hq) h'.symm
    simp [hG, hM, hΔ, hMb, this]
  refine GreenMinor_removal (by norm_num) ?_ _ _
  rw [hqq]
  simp [hm]
  norm_num

-- (ii): `M_{pq} = 0` (offsets `0 ≠ 1`)
example : hM hp hq = 0 :=
  GreenMinor_cross (M := hM) (Mb := hMb) (fun _ _ => rfl) (x := hp) (y := hq) (by decide)

-- S1: the one-sided and the cross-offset forms at `w = q`, `x = y = p`, `δ = 1/100 = ‖Δ‖_max`
example :
    ‖greenMinor hG hq hp hp - hG hp hp‖ ≤ (2 / (1 / 2 : ℝ)) * (1 / 100) * ‖hG hq hp‖ ∧
    ‖greenMinor hG hq hp hp - hG hp hp‖ ≤ (2 / (1 / 2 : ℝ)) * (1 / 100) * ‖hG hp hq‖ ∧
    ‖greenMinor hG hq hp hp - hG hp hp‖ ≤ (2 / (1 / 2 : ℝ)) * (1 / 100) ^ 2 := by
  have hqq : hG hq hq = hm := by
    have : hq ≠ hp := fun h' => (by decide : hp ≠ hq) h'.symm
    simp [hG, hM, hΔ, hMb, this]
  have hΔb : ∀ a b, ‖hG a b - hM a b‖ ≤ 1 / 100 := by
    intro a b
    simp only [hG, Matrix.add_apply, add_sub_cancel_left, hΔ, Matrix.of_apply]
    split_ifs
    · simp [hε]
    · simp
  have hw : (1 / 2 : ℝ) / 2 ≤ ‖hG hq hq‖ := by rw [hqq]; simp [hm]; norm_num
  have h1 : hp.2 ≠ hq.2 := by decide
  have h2 : hq.2 ≠ hp.2 := by decide
  exact ⟨GreenMinor_removal_crossL (Mb := hMb) (fun _ _ => rfl) hΔb (by norm_num) hw _ _ h1,
    GreenMinor_removal_crossR (Mb := hMb) (fun _ _ => rfl) hΔb (by norm_num) hw _ _ h2,
    GreenMinor_removal_cross (Mb := hMb) (fun _ _ => rfl) hΔb (by norm_num) hw _ _ h1 h2⟩

-- (ii) in the `T`/`R` form: `q ∈ R_{0,0}`; `p` (offset 0) and `(0, 2)` (block 0) in `T_{0,0}`
example : (hp.2 ≠ hq.2) ∧ (((0 : Zd 3 3), (2 : Fin (2 ^ 3))) : HV).2 ≠ hq.2 := by
  have hR : hq ∈ GreenMinor_R (0 : Zd 3 3) (0 : Fin (2 ^ 3)) := ⟨rfl, by decide⟩
  exact ⟨GreenMinor_offset_ne hR (Or.inl rfl) (by decide), GreenMinor_offset_ne hR (Or.inr rfl) (by decide)⟩

-- R1: the principal-submatrix resolvents of the Hermitian `H = Δ` at `z = i` form a tower over `(Δ - i)⁻¹`
example : GreenMinor_Tower (green hΔ Complex.I) (GreenMinor_Gs hΔ Complex.I) :=
  GreenMinor_tower hΔ_herm (by simp)

end HandMade

section CarrierInst
open SizesInst FlowPinsInst

-- R1 at the BA carrier: `d = 3`, `sz0` at `n = 0` (`L = 4`, `W = 32`), the flow `flow_sz0` (`κ = 1/2`), `t = 1/2 ≤ T₀`, every sample `ω`
example (ω : sz0.SeqΩ) :
    GreenMinor_Tower (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω)
      (GreenMinor_Gs (GreenCore_Dc sz0 zSeq 0 + GreenCore_Xc sz0 0 (1 / 2) ω)
        (ztOf (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0) (BAflowEs sz0 zSeq 0) (1 / 2))) :=
  GreenMinor_tower_carrier (by norm_num : (0 : ℝ) < 1 / 2) sz0 flow_sz0 0 (t := 1 / 2) (by norm_num) (half_lt_t0 0).le ω

end CarrierInst

end RBM.BA
