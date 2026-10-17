/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GreenCore

/-!
# The block Anderson minors: vocabulary, the offset fact, the tower

Paper: Lemma 8.4 (`lem_GbEXP_BA`), the block Anderson version of Lemma 3.1 (`lem_GbEXP`).  Everything is deterministic, for one
sample.  Sites are
`u = (a, o)` of `Vtx d L W` (block `a`, offset `o`), `M = M^{(B)} ⊗ I` (`hM`), `G^{(S)}` the
resolvent of the principal submatrix on the sites outside `S`, zero-padded.

* `GreenMinor_T`, `GreenMinor_R`, `GreenMinor_Tower`, `GreenMinor_good`, `GreenMinor_YA`,
  `GreenMinor_YX`: the vocabulary (`T_{β,o} = Y_o ∪ [β]`, the protected rows
  `R_{β,o} = [β] ∖ {(β, o)}`, the tower of minors, the protected good event, the
  polynomial families `Y^A`, `Y^X`).
* The offset fact: `o(x) ≠ o(y) ⇒ M_{xy} = 0` (`GreenMinor_cross`) and `GreenMinor_offset_ne`
  (the offset fact used by the recursion of the minor differences).
* The tower for the real minors.  `GreenMinor_Gs H z S = (H^{(S)} - z)⁻¹`, zero-padded,
  satisfies `GreenMinor_Tower ((H - z)⁻¹) (GreenMinor_Gs H z)` for Hermitian `H` and `Im z ≠ 0`
  (`GreenMinor_tower`), and at the BA carrier (`GreenMinor_tower_carrier`).
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

/-- The tower of minors: `Gs S = G^{(S)}` (rows and columns of `S` removed and zero-padded), `Gs ∅ = G`, one step is the minor identity. -/
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

/-- `Y^A_u = (s Δ_{uu} - Σ_l D_{ul} Δ_{lu}) / m`. -/
def GreenMinor_YA (G M D : Matrix (Vtx d L W) (Vtx d L W) ℂ) (s m : ℂ) (u : Vtx d L W) : ℂ :=
  (s * (G u u - M u u) - ∑ l, D u l * (G l u - M l u)) / m

/-- `Y^X_{uy}`. -/
def GreenMinor_YX (G M D : Matrix (Vtx d L W) (Vtx d L W) ℂ) (s m : ℂ) (u y : Vtx d L W) : ℂ :=
  M u y * (s * (G u u - M u u) - ∑ l, D u l * (G l u - M l u)) / m
    + (∑ l, D u l * (G l y - M l y) - s * (G u y - M u y))
    + ((G u u - M u u) * ∑ l, D u l * (G l y - M l y) - (G u y - M u y) * ∑ l, D u l * (G l u - M l u)) / m

end Setting

/-! ## 1. The offset fact -/

/-- `o(x) ≠ o(y) ⇒ M_{xy} = 0` (Kronecker form, `BAMfine_eq`, `GreenSchur.lean`); hence `G_{xy} = Δ_{xy}`. -/
theorem GreenMinor_cross {d L W : ℕ} [NeZero L] [NeZero W] {M : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    {Mb : Zd d L → Zd d L → ℂ} (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) {x y : Vtx d L W}
    (h : x.2 ≠ y.2) : M x y = 0 := by
  rw [hM]; simp [h]

/-- The offset fact in the `T`/`R` form used by the recursion of the minor differences: for `w ∈ R_{β,o}` and `x ∈ T_{β,o}`, `x ≠ w`, the offsets differ
(`x` of offset `o`: `o(w) ≠ o`; `x` in block `β`: same block, different site). -/
theorem GreenMinor_offset_ne {d L W : ℕ} [NeZero L] [NeZero W] {β : Zd d L} {o : Fin (W ^ d)} {w x : Vtx d L W}
    (hw : w ∈ GreenMinor_R β o) (hx : x ∈ GreenMinor_T β o) (hxw : x ≠ w) : x.2 ≠ w.2 := by
  obtain ⟨hw1, hw2⟩ := hw
  intro h
  rcases hx with hx | hx
  · exact hw2 (h.symm.trans hx)
  · exact hxw (Prod.ext (hx.trans hw1.symm) h)

/-! ## 2. The tower for the real minors

`GreenMinor_Gs H z S` is the resolvent `(H^{(S)} - z)⁻¹` of the principal submatrix of `H` on the sites outside `S`,
zero-padded (the analogue of `Green.greenSetMat` for an arbitrary matrix: the band's version is tied to the band Hamiltonian).
For Hermitian `H` and `Im z ≠ 0` every principal submatrix of `H - z` is invertible with nonvanishing diagonal resolvent
(`green_diag_ne_zero`), so the minor identity passes from `S` to `insert κ S` (`GreenMinor_Gs_insert`): this is the `GreenMinor_Tower`. -/

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

/-- The minor identity between `G^{(S)}` and `G^{(insert κ S)}` at the entries that survive. -/
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

/-- The minor identity between consecutive iterated minors, at every entry (the padding makes the removed rows consistent). -/
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

/-- For Hermitian `H` and `Im z ≠ 0` the principal-submatrix resolvents form a tower over `G = (H - z)⁻¹`. -/
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

/-- **The tower at the BA carrier**: the real minors of `G_t = (D + X - z_t)⁻¹` (`D = g₀ Ψ`, `X` the Gaussian part, `z_t = E + (1 - t) m`)
form a tower, for every sample `ω` and `0 ≤ t ≤ T₀` (the input is `GreenCore_carrier`; `Im z_t > 0` is `ba_G_data`). -/
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

end RBM.BA
