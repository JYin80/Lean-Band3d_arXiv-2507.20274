/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GreenMinor3
import RBM3D.Green.MinorDiffCond
import RBM3D.Green.LDE

/-!
# The block Anderson minors, conditionalised: the sample-level minor tower, the gain interface off a good event
(BA-G5b, file 1 of 2)

Ticket T2411 (design gate `docs/reports/T2401-prove.md` (G.5)-(G.6); G5a is `BA/GreenMinor*.lean`).  Paper:
`paper/tex/7_8_light_weight.tex` (`lem_GbEXP_BA`, `7_8:1916-1948`), band `paper/tex/3_5_Loop_Hierarchy.tex`.

* §1 the fine-index minor tower of the carrier `GreenCond_Gs` (the real minors of `D + X(ω)`, indexed by `Finset (Idx d L W)`,
  read through `splitEquiv`): base, measurability, the envelope `|G^{(S)}_{xy}| ≤ η_t⁻¹`, strict independence of the rows of `S`.
* §2 the minor families of `Y^A`, `Y^X` and the minor difference estimate on the good event (the transport of `GreenMinor_diff`
  along `splitEquiv`).
* §3 the conditionalised gain interface (the twin of `Green/MinorDiffCond.lean` `norm_applyOps_minorDiff_flucDiagSet_le_badFamily`,
  `integral_prod_applyOps_minorDiff_le_on`, `minorDiffGainUpTo'_of_le_on`, for an abstract family of minors with envelope `Env`):
  `GreenMinor_famGain` from a good event, the tower `badTower` over its complement, and the smallness `hsmall`.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.setOption false
set_option linter.flexible false

noncomputable section
open Filter Matrix Finset MeasureTheory ProbabilityTheory
open scoped Kronecker ENNReal NNReal
open RBM RBM.Green RBM.Gauss

namespace RBM.BA

/-! ## 1. The sample-level minor tower of the carrier -/

section Transport
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- `Δ_{l} (F ∘ map e) = (Δ_{e l} F) ∘ map e`: the iterated difference is transported by an equivalence of the index types. -/
theorem GreenCond_iterDeltaFam_map (e : α ≃ β) (F : Finset β → ℂ) :
    ∀ (l : List α) (S : Finset α),
      iterDeltaFam l (fun S' => F (S'.map e.toEmbedding)) S = iterDeltaFam (l.map e) F (S.map e.toEmbedding) := by
  intro l
  induction l generalizing F with
  | nil => intro S; rfl
  | cons κ l ih =>
      intro S
      have h : deltaFam κ (fun S' => F (S'.map e.toEmbedding)) =
          fun S' => deltaFam (e κ) F (S'.map e.toEmbedding) := by
        funext S'
        simp only [deltaFam_apply, Finset.map_insert, Equiv.coe_toEmbedding]
      rw [iterDeltaFam_cons, h, ih (deltaFam (e κ) F) S, List.map_cons, iterDeltaFam_cons]

end Transport

section Gs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `GreenMinor_Gs H z S` reads `H` only off the rows and columns of `S`. -/
theorem GreenCond_Gs_congr {H H' : Matrix ι ι ℂ} (z : ℂ) (S : Finset ι) (h : ∀ x y, x ∉ S → y ∉ S → H x y = H' x y) :
    GreenMinor_Gs H z S = GreenMinor_Gs H' z S := by
  have hsub : H.submatrix (Subtype.val : {a // a ∉ S} → ι) (Subtype.val : {a // a ∉ S} → ι) =
      H'.submatrix (Subtype.val : {a // a ∉ S} → ι) (Subtype.val : {a // a ∉ S} → ι) := by
    ext a b
    exact h a.1 b.1 a.2 b.2
  ext x y
  by_cases hx : x ∈ S
  · simp [GreenMinor_Gs, hx]
  by_cases hy : y ∈ S
  · simp [GreenMinor_Gs, hx, hy]
  simp only [GreenMinor_Gs, Matrix.of_apply, hx, hy, dite_eq_right, not_false_eq_true, hsub]

/-- Entries of `A⁻¹` are measurable in `A`. -/
private theorem GreenCond_measurable_inv_apply {Θ : Type*} [MeasurableSpace Θ] {M : Θ → Matrix ι ι ℂ} (hM : Measurable M)
    (i j : ι) : Measurable fun ω => (M ω)⁻¹ i j := by
  have h : (fun ω => (M ω)⁻¹ i j) = fun ω => Ring.inverse (M ω).det * (M ω).adjugate i j := by
    funext ω; rw [Matrix.inv_def]; rfl
  rw [h]
  refine Measurable.mul ?_ ?_
  · have hinv : Measurable (Ring.inverse : ℂ → ℂ) := by
      rw [Ring.inverse_eq_inv']; exact measurable_inv
    exact hinv.comp ((continuous_id.matrix_det).measurable.comp hM)
  · exact ((continuous_id.matrix_adjugate).measurable.comp hM).eval_matrix

end Gs

section Carrier
variable {d : ℕ}

/-- **The fine-index minor tower of the carrier at `(n, t, ω)`**: `S ↦ G^{(S)}`, the resolvent of the principal submatrix of `D + X`
on the sites outside `S.map splitEquiv`, zero-padded (`GreenMinor_Gs`), for `S : Finset (Idx d L W)` (the index type of
`applyOps`, `qRow`, `rowSplit`). -/
def GreenCond_Gs (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (S : Finset (Idx d (sz.L n) (sz.W n))) (ω : sz.SeqΩ) :
    Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ :=
  GreenMinor_Gs (GreenCore_Dc sz z n + GreenCore_Xc sz n t ω)
    (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t)
    (S.map (splitEquiv d (sz.L n) (sz.W n)).toEmbedding)

/-- The minors of the vertex-level tower, as a function of the vertex-level removed set. -/
def GreenCond_GsV (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) :
    Finset (Vtx d (sz.L n) (sz.W n)) → Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ :=
  GreenMinor_Gs (GreenCore_Dc sz z n + GreenCore_Xc sz n t ω)
    (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t)

theorem GreenCond_Gs_eq (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (S : Finset (Idx d (sz.L n) (sz.W n))) (ω : sz.SeqΩ) :
    GreenCond_Gs sz z n t S ω = GreenCond_GsV sz z n t ω (S.map (splitEquiv d (sz.L n) (sz.W n)).toEmbedding) := rfl

/-- The base level is the carrier resolvent `G_t(ω)`. -/
theorem GreenCond_Gs_empty {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) {z : ℕ → ℂ} (h : BAFlow sz κ ε 𝔠 𝔡 z)
    (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) (ω : sz.SeqΩ) :
    GreenCond_Gs sz z n t ∅ ω = GreenCore_Gc sz z n t ω := by
  have := (GreenMinor_tower_carrier hκ sz h n ht0 ht ω).base
  rw [GreenCond_Gs, Finset.map_empty]
  exact this

/-- The entries of `D + X(ω)` away from the rows `S.map splitEquiv` read only coordinates that avoid the rows of `S`. -/
theorem GreenCond_HV_congr (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (S : Finset (Idx d (sz.L n) (sz.W n)))
    {ω ω' : sz.SeqΩ} (h : AgreeOffRows sz n S ω ω') (x y : Vtx d (sz.L n) (sz.W n))
    (hx : x ∉ S.map (splitEquiv d (sz.L n) (sz.W n)).toEmbedding) (hy : y ∉ S.map (splitEquiv d (sz.L n) (sz.W n)).toEmbedding) :
    (GreenCore_Dc sz z n + GreenCore_Xc sz n t ω) x y = (GreenCore_Dc sz z n + GreenCore_Xc sz n t ω') x y := by
  set e := splitEquiv d (sz.L n) (sz.W n) with he
  have hx' : e.symm x ∉ S := fun hm => hx (Finset.mem_map.2 ⟨_, hm, by simp [he]⟩)
  have hy' : e.symm y ∉ S := fun hm => hy (Finset.mem_map.2 ⟨_, hm, by simp [he]⟩)
  have hs := congrFun (congrFun (Hflow_submatrix_set_congr (sz := sz.withLam 0) (n := n) t h) ⟨e.symm x, hx'⟩) ⟨e.symm y, hy'⟩
  simp only [Matrix.submatrix_apply] at hs
  simp only [Matrix.add_apply, GreenCore_Xc, blockMat, Matrix.submatrix_apply, BAX, Matrix.of_apply]
  rw [hs]

/-- Anything read off the minor `G^{(S)}` is strictly independent of every row in `S`. -/
theorem GreenCond_finDepOffRows (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (S : Finset (Idx d (sz.L n) (sz.W n)))
    {V : Type*} (Φ : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ → V) :
    FinDepOffRows sz n S fun ω => Φ (GreenCond_Gs sz z n t S ω) := by
  refine ⟨offRowsCoords sz n S, fun c hc => forall_not_isRowCoord_of_mem_offRowsCoords hc, fun ω ω' hω => ?_⟩
  have hagree : AgreeOffRows sz n S ω ω' := fun i j b hi hj => hω _ (mem_offRowsCoords hi hj)
  show Φ _ = Φ _
  rw [GreenCond_Gs, GreenCond_Gs, GreenCond_Gs_congr _ _ (GreenCond_HV_congr sz z n t S hagree)]

theorem GreenCond_measurable_HV (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (x y : Vtx d (sz.L n) (sz.W n)) :
    Measurable fun ω : sz.SeqΩ => (GreenCore_Dc sz z n + GreenCore_Xc sz n t ω) x y := by
  simp only [Matrix.add_apply, GreenCore_Xc, blockMat, Matrix.submatrix_apply, BAX, Matrix.of_apply]
  exact measurable_const.add (Sizes.measurable_seqHflow_entry (sz.withLam 0) n t _ _)

/-- Every entry of the vertex-level minor tower is measurable in `ω`. -/
theorem GreenCond_measurable_GsV (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (S : Finset (Vtx d (sz.L n) (sz.W n)))
    (x y : Vtx d (sz.L n) (sz.W n)) : Measurable fun ω : sz.SeqΩ => GreenCond_GsV sz z n t ω S x y := by
  unfold GreenCond_GsV
  by_cases hx : x ∈ S
  · simp only [GreenMinor_Gs_of_mem_left _ _ hx]; exact measurable_const
  by_cases hy : y ∈ S
  · simp only [GreenMinor_Gs_of_mem_right _ _ hy]; exact measurable_const
  simp only [GreenMinor_Gs_apply _ _ hx hy]
  unfold green
  refine GreenCond_measurable_inv_apply (M := fun ω : sz.SeqΩ => (GreenCore_Dc sz z n + GreenCore_Xc sz n t ω).submatrix
    (Subtype.val : {a // a ∉ S} → Vtx d (sz.L n) (sz.W n)) (Subtype.val : {a // a ∉ S} → Vtx d (sz.L n) (sz.W n)) -
      ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t • (1 : Matrix {a // a ∉ S} {a // a ∉ S} ℂ)) ?_ _ _
  refine Matrix.measurable_iff.2 fun p q => ?_
  simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.smul_apply]
  exact (GreenCond_measurable_HV sz z n t p.1 q.1).sub measurable_const

theorem GreenCond_measurable_Gs (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (S : Finset (Idx d (sz.L n) (sz.W n)))
    (x y : Vtx d (sz.L n) (sz.W n)) : Measurable fun ω : sz.SeqΩ => GreenCond_Gs sz z n t S ω x y :=
  GreenCond_measurable_GsV sz z n t _ x y

/-- **The envelope**: `|G^{(S)}_{xy}| ≤ |Im z_t|⁻¹` for every `ω` (the principal submatrix of the Hermitian `D + X` is Hermitian;
no spectral information on `D`). -/
theorem GreenCond_norm_GsV_le (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (hz : (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
    (BAflowEs sz z n) t).im ≠ 0) (ω : sz.SeqΩ) (S : Finset (Vtx d (sz.L n) (sz.W n))) (x y : Vtx d (sz.L n) (sz.W n)) :
    ‖GreenCond_GsV sz z n t ω S x y‖ ≤ |(ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t).im|⁻¹ := by
  unfold GreenCond_GsV
  by_cases hx : x ∈ S
  · rw [GreenMinor_Gs_of_mem_left _ _ hx, norm_zero]; exact inv_nonneg.2 (abs_nonneg _)
  by_cases hy : y ∈ S
  · rw [GreenMinor_Gs_of_mem_right _ _ hy, norm_zero]; exact inv_nonneg.2 (abs_nonneg _)
  rw [GreenMinor_Gs_apply _ _ hx hy]
  have hH := ((GreenMinor_carrier_herm sz z n t ω).submatrix (Subtype.val : {a // a ∉ S} → Vtx d (sz.L n) (sz.W n)))
  have h := norm_Gsig_le_inv_eta hH (abs_pos.2 hz) le_rfl true
  have e : Gres ((GreenCore_Dc sz z n + GreenCore_Xc sz n t ω).submatrix (Subtype.val : {a // a ∉ S} → Vtx d (sz.L n) (sz.W n))
      (Subtype.val : {a // a ∉ S} → Vtx d (sz.L n) (sz.W n)))
      (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t) true =
      green ((GreenCore_Dc sz z n + GreenCore_Xc sz n t ω).submatrix (Subtype.val : {a // a ∉ S} → Vtx d (sz.L n) (sz.W n))
      (Subtype.val : {a // a ∉ S} → Vtx d (sz.L n) (sz.W n)))
      (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t) := by
    simp only [green, Gres, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]
  rw [e] at h
  exact (norm_matrix_entry_le_opNorm _ _ _).trans h

/-- The data of the carrier that do not depend on the sample point (`m = m_F`, `s = E + m`, the profile of `M`, `D`). -/
abbrev GreenCond_m (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) : ℂ := BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n
abbrev GreenCond_s (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) : ℂ := (BAflowEs sz z n : ℂ) + GreenCond_m sz z n
abbrev GreenCond_zt (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  ztOf (GreenCond_m sz z n) (BAflowEs sz z n) t

/-- **The structural facts of the carrier at `(n, t)`**, from `BAFlow` and `0 ≤ t ≤ T₀` only: `κ ≤ ‖m‖ ≤ 1`, `κ ≤ 1`, `L ≥ 3`, `g₀ ≥ 0`,
`‖M‖_max ≤ 1`, `M = M^{(B)} ⊗ I`, `D = g₀ Ψ`, `Im z_t > 0`, `‖s‖ (‖m‖) ≤ 1 + 2 d g₀`. -/
structure GreenCond_Data (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t κ : ℝ) : Prop where
  hκ : 0 < κ
  hκm : κ ≤ ‖GreenCond_m sz z n‖
  hm1 : ‖GreenCond_m sz z n‖ ≤ 1
  hκ1 : κ ≤ 1
  hL : 3 ≤ sz.L n
  hg0 : 0 ≤ BAflowLam0 sz z n
  hMle : ∀ u v, ‖GreenCore_Mc sz z n u v‖ ≤ 1
  hM : ∀ u v, GreenCore_Mc sz z n u v =
    if u.2 = v.2 then BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (GreenCond_m sz z n) u.1 v.1 else 0
  hMd : ∀ a, BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (GreenCond_m sz z n) a a = GreenCond_m sz z n
  hD : ∀ u l, GreenCore_Dc sz z n u l =
    if u.2 = l.2 ∧ Adj d (sz.L n) u.1 l.1 then ((BAflowLam0 sz z n : ℝ) : ℂ) else 0
  him : 0 < (GreenCond_zt sz z n t).im
  hs : ‖GreenCond_s sz z n‖ * ‖GreenCond_m sz z n‖ ≤ 1 + 2 * d * BAflowLam0 sz z n

theorem GreenCond_data {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) {z : ℕ → ℂ} (h : BAFlow sz κ ε 𝔠 𝔡 z)
    (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) (hg0 : 0 ≤ BAflowLam0 sz z n) :
    GreenCond_Data sz z n t κ := by
  obtain ⟨hGR, hRG, hDM, hMD, hz, hM, hMd, hD, hG0⟩ := GreenCore_carrier hκ sz h n ht0 ht (ω := fun _ => 0)
    (m := GreenCond_m sz z n) (s := GreenCond_s sz z n) (zt := GreenCond_zt sz z n t) rfl rfl rfl
  obtain ⟨ht1, hr, hmi, hzi, -, hMle'⟩ := ba_G_data hκ sz h n ht0 ht
  have hMle : ∀ u v : Vtx d (sz.L n) (sz.W n), ‖GreenCore_Mc sz z n u v‖ ≤ 1 := fun u v => by
    simpa [GreenCore_Mc, blockMat] using hMle' ((splitEquiv d (sz.L n) (sz.W n)).symm u) ((splitEquiv d (sz.L n) (sz.W n)).symm v)
  have hm1 : ‖GreenCond_m sz z n‖ ≤ 1 :=
    BAm_norm_le_one (d := d) (L := sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (GreenCond_m sz z n) (by simp) hr.1
  have hκm : κ ≤ ‖GreenCond_m sz z n‖ := hr.2.trans ((le_abs_self _).trans (Complex.abs_im_le_norm _))
  have hL := sz.three_le_L n
  -- `s m = Σ_l D_{ul} M_{lu} - 1` at `u = (0, 0)`
  have hs : ‖GreenCond_s sz z n‖ * ‖GreenCond_m sz z n‖ ≤ 1 + 2 * d * BAflowLam0 sz z n := by
    set u : Vtx d (sz.L n) (sz.W n) := (0, ⟨0, pow_pos (sz.W_pos n) d⟩) with hu
    have hrow := GreenMinor_row_DM (d := d) (L := sz.L n) (W := sz.W n) (D := GreenCore_Dc sz z n) (M := GreenCore_Mc sz z n)
      (s := GreenCond_s sz z n) hMD u u
    have hMuu : GreenCore_Mc sz z n u u = GreenCond_m sz z n := by rw [hM u u]; simpa using hMd u.1
    have h11 : (if u = u then (1 : ℂ) else 0) = 1 := by simp
    rw [h11, hMuu] at hrow
    have hsm : GreenCond_s sz z n * GreenCond_m sz z n = ∑ l, GreenCore_Dc sz z n u l * GreenCore_Mc sz z n l u - 1 := by
      rw [hrow]; ring
    rw [← norm_mul, hsm]
    calc ‖∑ l, GreenCore_Dc sz z n u l * GreenCore_Mc sz z n l u - 1‖
        ≤ ‖∑ l, GreenCore_Dc sz z n u l * GreenCore_Mc sz z n l u‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ (∑ l, ‖GreenCore_Dc sz z n u l‖ * 1) + 1 := by
          rw [norm_one]
          refine add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)) le_rfl
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hMle l u) (norm_nonneg _)
      _ = 1 + 2 * d * BAflowLam0 sz z n := by
          simp only [mul_one]
          rw [GreenCore_Drow hg0 hL hD u]; ring
  exact ⟨hκ, hκm, hm1, hκm.trans hm1, hL, hg0, hMle, hM, hMd, hD, hzi, hs⟩

end Carrier

/-! ## 2. The minor families of `Y^A`, `Y^X` and the minor difference on the good event -/

section Const
variable {κ : ℝ}

theorem GreenCond_a_mono (hκ : 0 < κ) (hκ1 : κ ≤ 1) : Monotone (GreenMinor_a κ) := by
  refine monotone_nat_of_le_succ fun r => ?_
  have h1 := GreenMinor_one_le_a hκ hκ1 r
  have h5 : GreenMinor_a κ r ≤ GreenMinor_a κ r ^ 5 :=
    calc GreenMinor_a κ r = GreenMinor_a κ r ^ 1 := (pow_one _).symm
      _ ≤ GreenMinor_a κ r ^ 5 := pow_le_pow_right₀ h1 (by norm_num)
  have h16 : (1 : ℝ) ≤ 16 ^ r := one_le_pow₀ (by norm_num)
  rw [GreenMinor_a_succ]
  nlinarith

/-- `c_Y(r)` is monotone in `r`, `g₀` and `‖s‖`: the constants of the pins are bounded by those at `(M, Λ, sbd)`. -/
theorem GreenCond_cY_mono {d : ℕ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) {g₀ g₀' s s' : ℝ} {r r' : ℕ} (hg : 0 ≤ g₀) (hgg : g₀ ≤ g₀')
    (hs : 0 ≤ s) (hss : s ≤ s') (hr : r ≤ r') : GreenMinor_cY d κ g₀ s r ≤ GreenMinor_cY d κ g₀' s' r' := by
  unfold GreenMinor_cY
  have ha := GreenCond_a_mono hκ hκ1 hr
  have ha0 := GreenMinor_a_nonneg hκ hκ1 r
  have h2 : (2 : ℝ) ^ r ≤ 2 ^ r' := pow_le_pow_right₀ (by norm_num) hr
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hκ' : (0 : ℝ) ≤ 1 / κ + 1 := by positivity
  have hg' : 0 ≤ g₀' := hg.trans hgg
  have h1 : (s + 2 * d * g₀) * (1 / κ + 1) * GreenMinor_a κ r ≤ (s' + 2 * d * g₀') * (1 / κ + 1) * GreenMinor_a κ r' := by
    have : s + 2 * d * g₀ ≤ s' + 2 * d * g₀' := by nlinarith
    exact mul_le_mul (mul_le_mul_of_nonneg_right this hκ') ha ha0 (by nlinarith [mul_nonneg hd (hg.trans hgg), hs.trans hss])
  have h3 : (4 * d * g₀ / κ) * 2 ^ r * GreenMinor_a κ r ^ 2 ≤ (4 * d * g₀' / κ) * 2 ^ r' * GreenMinor_a κ r' ^ 2 := by
    have e1 : 4 * d * g₀ / κ ≤ 4 * d * g₀' / κ := div_le_div_of_nonneg_right (by nlinarith) hκ.le
    have e2 : 0 ≤ 4 * (d : ℝ) * g₀ / κ := by positivity
    exact mul_le_mul (mul_le_mul e1 h2 (by positivity) (by positivity)) (pow_le_pow_left₀ ha0 ha 2) (by positivity)
      (by positivity)
  linarith

end Const

section Families
variable {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ)

/-- The observable `G ↦ Y^A_{split k}(G)` of the carrier. -/
def GreenCond_ΦA (k : Idx d (sz.L n) (sz.W n)) (G : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ) : ℂ :=
  GreenMinor_YA G (GreenCore_Mc sz z n) (GreenCore_Dc sz z n) (GreenCond_s sz z n) (GreenCond_m sz z n) (split d (sz.L n) (sz.W n) k)

/-- The observable `G ↦ Y^X_{split k, (α, o(k))}(G)` of the carrier. -/
def GreenCond_ΦX (α : Zd d (sz.L n)) (k : Idx d (sz.L n) (sz.W n))
    (G : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ) : ℂ :=
  GreenMinor_YX G (GreenCore_Mc sz z n) (GreenCore_Dc sz z n) (GreenCond_s sz z n) (GreenCond_m sz z n)
    (split d (sz.L n) (sz.W n) k) (α, (split d (sz.L n) (sz.W n) k).2)

/-- The family of minors of an observable: `S ↦ (ω ↦ Φ(G^{(S)}(ω)))`. -/
def GreenCond_famS (t : ℝ) (Φ : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ → ℂ)
    (S : Finset (Idx d (sz.L n) (sz.W n))) (ω : sz.SeqΩ) : ℂ := Φ (GreenCond_Gs sz z n t S ω)

theorem GreenCond_famS_empty {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) (Φ : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ → ℂ) :
    GreenCond_famS sz z n t Φ ∅ = fun ω => Φ (GreenCore_Gc sz z n t ω) := by
  funext ω
  unfold GreenCond_famS
  rw [GreenCond_Gs_empty hκ sz h n ht0 ht]

theorem GreenCond_famA_eq (t : ℕ → ℝ) (k : Idx d (sz.L n) (sz.W n)) :
    GreenMinor_famA sz z t n k = fun ω => GreenCond_ΦA sz z n k (GreenCore_Gc sz z n (t n) ω) := rfl

theorem GreenCond_famX_eq (t : ℕ → ℝ) (α : Zd d (sz.L n)) (k : Idx d (sz.L n) (sz.W n)) :
    GreenMinor_famX sz z t n α k = fun ω => GreenCond_ΦX sz z n α k (GreenCore_Gc sz z n (t n) ω) := rfl

end Families

section ObsMeas
variable {d L W : ℕ} [NeZero L] [NeZero W] {Θ : Type*} [MeasurableSpace Θ] {G : Θ → Matrix (Vtx d L W) (Vtx d L W) ℂ}

theorem GreenCond_measurable_YA (hG : ∀ x y, Measurable fun ω => G ω x y) (M D : Matrix (Vtx d L W) (Vtx d L W) ℂ) (s m : ℂ)
    (u : Vtx d L W) : Measurable fun ω => GreenMinor_YA (G ω) M D s m u := by
  unfold GreenMinor_YA
  exact ((measurable_const.mul ((hG u u).sub measurable_const)).sub
    (Finset.measurable_sum _ fun l _ => measurable_const.mul ((hG l u).sub measurable_const))).div_const _

theorem GreenCond_measurable_YX (hG : ∀ x y, Measurable fun ω => G ω x y) (M D : Matrix (Vtx d L W) (Vtx d L W) ℂ) (s m : ℂ)
    (u y : Vtx d L W) : Measurable fun ω => GreenMinor_YX (G ω) M D s m u y := by
  unfold GreenMinor_YX
  have h1 : Measurable fun ω => ∑ l, D u l * (G ω l u - M l u) :=
    Finset.measurable_sum _ fun l _ => measurable_const.mul ((hG l u).sub measurable_const)
  have h2 : Measurable fun ω => ∑ l, D u l * (G ω l y - M l y) :=
    Finset.measurable_sum _ fun l _ => measurable_const.mul ((hG l y).sub measurable_const)
  have h3 : Measurable fun ω => (s * (G ω u u - M u u) - ∑ l, D u l * (G ω l u - M l u)) :=
    (measurable_const.mul ((hG u u).sub measurable_const)).sub h1
  exact ((((measurable_const.mul h3).div_const _).add (h2.sub (measurable_const.mul ((hG u y).sub measurable_const)))).add
    (((((hG u u).sub measurable_const).mul h2).sub (((hG u y).sub measurable_const).mul h1)).div_const _))

end ObsMeas

section MinorDiff
variable {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ)

/-- The envelope constant of the minor families: `((‖s‖ + 2 d g₀)(1/κ + 1) + 4 d g₀ e/κ) e`, `e = |Im z_t|⁻¹ + 1`. -/
def GreenCond_Env (d : ℕ) (κ g₀ s e : ℝ) : ℝ := ((s + 2 * d * g₀) * (1 / κ + 1) + 4 * d * g₀ * e / κ) * e

theorem GreenCond_Env_nonneg {κ g₀ s e : ℝ} (hκ : 0 < κ) (hg : 0 ≤ g₀) (hs : 0 ≤ s) (he : 0 ≤ e) :
    0 ≤ GreenCond_Env d κ g₀ s e := by
  unfold GreenCond_Env; positivity

/-- The two envelopes: `‖Y^A‖, ‖Y^X‖ ≤ Env` for every `ω` and every level `S`, `Env` depending on `η_t = Im z_t` through `e = η_t⁻¹ + 1`. -/
theorem GreenCond_norm_fam_le {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) (hg0 : 0 ≤ BAflowLam0 sz z n) (S : Finset (Idx d (sz.L n) (sz.W n))) (ω : sz.SeqΩ)
    (k : Idx d (sz.L n) (sz.W n)) (α : Zd d (sz.L n)) :
    ‖GreenCond_ΦA sz z n k (GreenCond_Gs sz z n t S ω)‖ ≤
        GreenCond_Env d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ (|(GreenCond_zt sz z n t).im|⁻¹ + 1) ∧
      ‖GreenCond_ΦX sz z n α k (GreenCond_Gs sz z n t S ω)‖ ≤
        GreenCond_Env d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ (|(GreenCond_zt sz z n t).im|⁻¹ + 1) := by
  have dat := GreenCond_data hκ sz h n ht0 ht hg0
  have hΔ : ∀ a b, ‖GreenCond_Gs sz z n t S ω a b - GreenCore_Mc sz z n a b‖ ≤ |(GreenCond_zt sz z n t).im|⁻¹ + 1 := fun a b =>
    (norm_sub_le _ _).trans (add_le_add (GreenCond_norm_GsV_le sz z n t dat.him.ne' ω _ a b) (dat.hMle a b))
  have he : 0 ≤ |(GreenCond_zt sz z n t).im|⁻¹ + 1 := by positivity
  have hs0 : 0 ≤ ‖GreenCond_s sz z n‖ := norm_nonneg _
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  constructor
  · refine (GreenMinor_YA_le dat.hL dat.hg0 dat.hD hΔ dat.hκ dat.hκm _).trans ?_
    unfold GreenCond_Env
    have h1 : (‖GreenCond_s sz z n‖ + 2 * d * BAflowLam0 sz z n) / κ ≤
        (‖GreenCond_s sz z n‖ + 2 * d * BAflowLam0 sz z n) * (1 / κ + 1) + 4 * d * BAflowLam0 sz z n * (|(GreenCond_zt sz z n t).im|⁻¹ + 1) / κ := by
      have : 0 ≤ 4 * (d : ℝ) * BAflowLam0 sz z n * (|(GreenCond_zt sz z n t).im|⁻¹ + 1) / κ := by positivity
      have h2 : (‖GreenCond_s sz z n‖ + 2 * d * BAflowLam0 sz z n) / κ ≤ (‖GreenCond_s sz z n‖ + 2 * d * BAflowLam0 sz z n) * (1 / κ + 1) := by
        rw [mul_add, mul_one, ← div_eq_mul_one_div]
        have : 0 ≤ ‖GreenCond_s sz z n‖ + 2 * d * BAflowLam0 sz z n := by positivity
        linarith
      linarith
    exact mul_le_mul_of_nonneg_right h1 he
  · exact GreenMinor_YX_le dat.hL dat.hg0 dat.hD hΔ dat.hκ dat.hκm _ _ (dat.hMle _ _)

theorem GreenCond_bddMeas_A {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) (hg0 : 0 ≤ BAflowLam0 sz z n) (k : Idx d (sz.L n) (sz.W n)) (S : Finset (Idx d (sz.L n) (sz.W n))) :
    BddMeas (sz.withLam 0) (GreenCond_famS sz z n t (GreenCond_ΦA sz z n k) S) :=
  ⟨GreenCond_measurable_YA (fun x y => GreenCond_measurable_Gs sz z n t S x y) _ _ _ _ _, _,
    fun ω => (GreenCond_norm_fam_le sz z n hκ h ht0 ht hg0 S ω k 0).1⟩

theorem GreenCond_bddMeas_X {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) (hg0 : 0 ≤ BAflowLam0 sz z n) (α : Zd d (sz.L n)) (k : Idx d (sz.L n) (sz.W n))
    (S : Finset (Idx d (sz.L n) (sz.W n))) :
    BddMeas (sz.withLam 0) (GreenCond_famS sz z n t (GreenCond_ΦX sz z n α k) S) :=
  ⟨GreenCond_measurable_YX (fun x y => GreenCond_measurable_Gs sz z n t S x y) _ _ _ _ _ _, _,
    fun ω => (GreenCond_norm_fam_le sz z n hκ h ht0 ht hg0 S ω k α).2⟩

theorem GreenCond_minorDiff_eq (t : ℝ) (Φ : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ → ℂ)
    (l : List (Idx d (sz.L n) (sz.W n))) (ω : sz.SeqΩ) :
    minorDiff (sz.withLam 0) n l (GreenCond_famS sz z n t Φ) ω =
      iterDeltaFam (l.map (splitEquiv d (sz.L n) (sz.W n))) (fun S' => Φ (GreenCond_GsV sz z n t ω S')) ∅ := by
  refine (minorDiff_eq_iterDeltaFam (sz := sz.withLam 0) (n := n) l (GreenCond_famS sz z n t Φ) ω).trans ?_
  have := GreenCond_iterDeltaFam_map (splitEquiv d (sz.L n) (sz.W n)) (fun S' => Φ (GreenCond_GsV sz z n t ω S')) l ∅
  rw [Finset.map_empty] at this
  exact this

/-- **The minor difference on the good event** (`GreenMinor_diff` transported along `splitEquiv`): for `ω` with `‖G_t - M‖_max ≤ δ`, a word `L`
on the slot `k` whose rows `x` are `≠ k` and in the block of `k`, and `α` another block, the `numQ L`-fold difference of `Y^A_{[k]}` and of
`Y^X_{[k], (α, o(k))}` is `≤ c_Y(numQ L) (2δ)^{numQ L + 1}`. -/
theorem GreenCond_minorDiff_le {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) (hg0 : 0 ≤ BAflowLam0 sz z n) {δ : ℝ} {m₀ : ℕ} (hδ0 : 0 ≤ δ) (hδ4 : 4 * δ ≤ κ)
    (hMδ : 8 * (m₀ : ℝ) * δ ≤ κ) (hδ2 : 2 * δ ≤ 1) {ω : sz.SeqΩ}
    (hG : ∀ x y, ‖GreenCore_Gc sz z n t ω x y - GreenCore_Mc sz z n x y‖ ≤ δ)
    (k : Idx d (sz.L n) (sz.W n)) (L : List (Bool × Idx d (sz.L n) (sz.W n))) (hL1 : (L.map Prod.snd).Nodup)
    (hL2 : ∀ x ∈ L, x.2 ≠ k ∧ (split d (sz.L n) (sz.W n) x.2).1 = (split d (sz.L n) (sz.W n) k).1) (hLm : numQ L ≤ m₀)
    (α : Zd d (sz.L n)) (hα : α ≠ (split d (sz.L n) (sz.W n) k).1) :
    ‖minorDiff (sz.withLam 0) n (qList L) (GreenCond_famS sz z n t (GreenCond_ΦA sz z n k)) ω‖ ≤
        GreenMinor_cY d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ (numQ L) * (2 * δ) ^ (numQ L + 1) ∧
      ‖minorDiff (sz.withLam 0) n (qList L) (GreenCond_famS sz z n t (GreenCond_ΦX sz z n α k)) ω‖ ≤
        GreenMinor_cY d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ (numQ L) * (2 * δ) ^ (numQ L + 1) := by
  have dat := GreenCond_data hκ sz h n ht0 ht hg0
  have hT := GreenMinor_tower_carrier hκ sz h n ht0 ht ω
  set e := splitEquiv d (sz.L n) (sz.W n) with he
  set u := split d (sz.L n) (sz.W n) k with hu
  have hgood := GreenMinor_good_of_event dat.hM dat.hMd dat.hκ dat.hκm hδ0 hδ4 hMδ hT hG u.1 u.2
  have hlq : (qList L).length = numQ L := length_qList L
  have hnd : ((qList L).map e).Nodup := (qList_nodup hL1).map e.injective
  have hR : ∀ k' ∈ (qList L).map e, k' ∈ GreenMinor_R u.1 u.2 := by
    intro k' hk'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hk'
    obtain ⟨p, hp, hpx⟩ : ∃ p ∈ L, p.2 = x := by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (show x ∈ (L.filter (·.1)).map Prod.snd from hx)
      exact ⟨q, List.mem_of_mem_filter hq, rfl⟩
    obtain ⟨hpk, hpb⟩ := hL2 p hp
    subst hpx
    refine ⟨hpb, fun ho => hpk ?_⟩
    apply e.injective
    exact Prod.ext hpb ho
  have hlen : ((qList L).map e).length ≤ m₀ := by rw [List.length_map, hlq]; exact hLm
  have hdiff := GreenMinor_diff (G := GreenCore_Gc sz z n t ω) (M := GreenCore_Mc sz z n) (D := GreenCore_Dc sz z n)
    (Gs := GreenCond_GsV sz z n t ω) (s := GreenCond_s sz z n) (m := GreenCond_m sz z n) (κ := κ) (δ := δ) (g₀ := BAflowLam0 sz z n)
    (m₀ := m₀) (β := u.1) (o := u.2) (u := u) (y := (α, u.2)) dat.hL dat.hg0 dat.hD dat.hM dat.hκ dat.hκ1 dat.hκm
    (dat.hMle _ _) hT hgood rfl ⟨rfl, hα⟩ _ hnd hR hlen hδ2
  simp only [List.length_map, hlq] at hdiff
  exact ⟨(le_of_eq (congrArg norm (GreenCond_minorDiff_eq sz z n t (GreenCond_ΦA sz z n k) (qList L) ω))).trans hdiff.2,
    (le_of_eq (congrArg norm (GreenCond_minorDiff_eq sz z n t (GreenCond_ΦX sz z n α k) (qList L) ω))).trans hdiff.1⟩

end MinorDiff

/-! ## 3. The conditionalised gain interface

The twin of `Green/MinorDiffCond.lean` (`norm_applyOps_minorDiff_flucDiagSet_le_badFamily`, `integral_prod_applyOps_minorDiff_le_on`,
`minorDiffGainUpTo'_of_le_on`) for an abstract family of minors `Yq k S` (the `S`-minor version of the slot `k`) with a uniform envelope
`Env`: the constants `condEnv`, `condCost` of the band, with `η_t⁻¹ + 1` replaced by `Env`.  `badStep`, `badTower`, `BadFamily`,
`meas_badTower_le`, `norm_applyOps_le_badFamily`, `integral_prod_norm_le_of_bounds_on` are the band's, used as they are. -/

section Cond
variable {d : ℕ} {sz : Sizes d} {n : ℕ}

/-- The envelope of a word of at most `M` letters on a slot of envelope `Env`: `2^{2M+1} Env`. -/
def GreenCond_genv (Env : ℝ) (M : ℕ) : ℝ := 2 ^ (2 * M + 1) * Env

/-- The price of conditionalising, per factor (`condCost`): `(M+1) 2^{2M+1} Env ε (2Ψ)^{-M}`. -/
def GreenCond_cost (Env : ℝ) (M : ℕ) (Ψ ε : ℝ) : ℝ := ((M : ℝ) + 1) * GreenCond_genv Env M * ε * ((2 * Ψ) ^ M)⁻¹

theorem GreenCond_genv_nonneg {Env : ℝ} (hEnv : 0 ≤ Env) (M : ℕ) : 0 ≤ GreenCond_genv Env M := by
  unfold GreenCond_genv; positivity

theorem GreenCond_one_le_genv {Env : ℝ} (hEnv : 1 ≤ Env) (M : ℕ) : 1 ≤ GreenCond_genv Env M := by
  unfold GreenCond_genv
  have h1 : (1 : ℝ) ≤ 2 ^ (2 * M + 1) := one_le_pow₀ (by norm_num)
  nlinarith

theorem GreenCond_cost_nonneg {Env : ℝ} (hEnv : 0 ≤ Env) (M : ℕ) {Ψ ε : ℝ} (hΨ : 0 ≤ Ψ) (hε : 0 ≤ ε) :
    0 ≤ GreenCond_cost Env M Ψ ε := by
  have := GreenCond_genv_nonneg hEnv M
  unfold GreenCond_cost
  positivity

/-- **One word on one slot, conditionalised.**  If the `numQ L`-fold minor difference `Δ_{qList L} Y_k` obeys the sharp bound `c` off `Bad 0`
and the family has the envelope `Env`, the word `L` applied to `Q_k Y_k` obeys `2^{q+1}(c + (|L|+1) 2^q Env ε)` off `Bad (|L| + 1)`. -/
theorem GreenCond_norm_word_le {Yq : Idx d (sz.L n) (sz.W n) → Finset (Idx d (sz.L n) (sz.W n)) → sz.SeqΩ → ℂ} {Env c ε : ℝ}
    {Bad : ℕ → Set sz.SeqΩ} (hY : ∀ k S, BddMeas sz (Yq k S)) (hind : ∀ k S, FinDepOffRows sz n S (Yq k S))
    (hEnv : ∀ k S ω, ‖Yq k S ω‖ ≤ Env) (hfam : BadFamily sz n ε Bad) (hε : 0 ≤ ε) (hc : 0 ≤ c)
    (k : Idx d (sz.L n) (sz.W n)) (L : List (Bool × Idx d (sz.L n) (sz.W n)))
    (hgood : ∀ ω ∉ Bad 0, ‖minorDiff sz n (qList L) (Yq k) ω‖ ≤ c) (ω : sz.SeqΩ) (hω : ω ∉ Bad (L.length + 1)) :
    ‖applyOps sz n L (qRow sz n k (Yq k ∅)) ω‖ ≤ 2 ^ (numQ L + 1) * (c + ((L.length : ℝ) + 1) * (2 ^ numQ L * Env) * ε) := by
  classical
  have hrw : applyOps sz n L (qRow sz n k (Yq k ∅)) = applyOps sz n (L ++ [(true, k)]) (minorDiff sz n (qList L) (Yq k)) := by
    have h1 := applyOps_eq_applyOps_minorDiff L (fun S => qRow sz n k (Yq k S)) (fun S => (hY k S).qRow k)
      (fun S κ hκ => (finDepOffRows_qRow (hind k S)).finDepOffRow hκ)
    have h2 := minorDiff_qRow k (qList L) (Yq k) (hY k)
    rw [h1, h2, applyOps_append]
    rfl
  have hXb : BddMeas sz (minorDiff sz n (qList L) (Yq k)) := bddMeas_minorDiff _ _ (hY k)
  have hXe : ∀ ω', ‖minorDiff sz n (qList L) (Yq k) ω'‖ ≤ 2 ^ numQ L * Env := by
    intro ω'
    have := norm_minorDiff_le (qList L) (Yq k) (hEnv k) ω'
    rwa [length_qList] at this
  have hlen : (L ++ [(true, k)]).length = L.length + 1 := by simp
  have hωa : ω ∉ Bad ((L ++ [(true, k)]).length) := by rwa [hlen]
  have hkey := norm_applyOps_le_badFamily hXb hfam hXe hc hε hgood (L ++ [(true, k)]) ω hωa
  rw [numQ_append_true, hlen] at hkey
  rw [hrw]
  refine hkey.trans (le_of_eq ?_)
  push_cast
  ring

/-- **The conditionalised gain interface from a good event.**  Let `Yq k S` be the `S`-minor version of the slot `k ∈ A` (bounded measurable,
strictly independent of the rows of `S`, envelope `Env`), `Bad` a `BadFamily` of threshold `ε`, and assume the sharp minor-difference bound
`‖Δ_{qList L} Y_k‖ ≤ c_M Ψ^{numQ L + 1}` off `Bad 0` for the words `L` of the interface (rows distinct, `≠ k`, in `A`, `|L| ≤ M`).  Then
`famGain(B, 2Ψ, M, K)` holds with `B = 2 (2 c_M Ψ + condCost)`, provided `hB1` (`B₀ ≤ 1`) and `hsmall` (the tower is small at the two budgets).
(The twin of `minorDiffGainUpTo'_of_le_on` for a family of minors.) -/
theorem GreenCond_famGain_of_good {A : Finset (Idx d (sz.L n) (sz.W n))}
    {Yq : Idx d (sz.L n) (sz.W n) → Finset (Idx d (sz.L n) (sz.W n)) → sz.SeqΩ → ℂ} {Env cM Ψ ε : ℝ} {M K : ℕ}
    {Bad : ℕ → Set sz.SeqΩ} (hY : ∀ k S, BddMeas sz (Yq k S)) (hind : ∀ k S, FinDepOffRows sz n S (Yq k S))
    (hEnv : ∀ k S ω, ‖Yq k S ω‖ ≤ Env) (hfam : BadFamily sz n ε Bad) (hε : 0 ≤ ε) (hΨ0 : 0 < Ψ) (hΨ1 : 2 * Ψ ≤ 1)
    (hcM : 0 ≤ cM) (hEnv1 : 1 ≤ Env)
    (hgood : ∀ ω ∉ Bad 0, ∀ k ∈ A, ∀ L : List (Bool × Idx d (sz.L n) (sz.W n)), (L.map Prod.snd).Nodup →
      (∀ x ∈ L, x.2 ≠ k ∧ x.2 ∈ A) → L.length ≤ M → ‖minorDiff sz n (qList L) (Yq k) ω‖ ≤ cM * Ψ ^ (numQ L + 1))
    (hB1 : 2 * cM * Ψ + GreenCond_cost Env M Ψ ε ≤ 1)
    (hsmall : GreenCond_genv Env M ^ K * (Sizes.seqP sz).real (Bad (M + 1)) ≤
      (2 * cM * Ψ + GreenCond_cost Env M Ψ ε) ^ K * (2 * Ψ) ^ (K * M)) :
    GreenMinor_famGain sz n A (fun k => Yq k ∅) (2 * (2 * cM * Ψ + GreenCond_cost Env M Ψ ε)) (2 * Ψ) M K := by
  classical
  have hEnv0 : 0 ≤ Env := le_trans zero_le_one hEnv1
  have h2Ψ0 : (0 : ℝ) < 2 * Ψ := by linarith
  have hcost0 : 0 ≤ GreenCond_cost Env M Ψ ε := GreenCond_cost_nonneg hEnv0 M hΨ0.le hε
  have hG1 : 1 ≤ GreenCond_genv Env M := GreenCond_one_le_genv hEnv1 M
  set B₀ : ℝ := 2 * cM * Ψ + GreenCond_cost Env M Ψ ε with hB₀
  have hB₀0 : 0 ≤ B₀ := by
    have : (0 : ℝ) ≤ 2 * cM * Ψ := by positivity
    rw [hB₀]; linarith
  refine ⟨by positivity, by positivity, fun ι _ k L hkA h1 h2 hlen hcard => ?_⟩
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · have hemp : IsEmpty ι := Fintype.card_eq_zero_iff.1 h0
    simp [Finset.univ_eq_empty]
  -- the per-factor bound off the exceptional set
  have hb : ∀ ω ∉ Bad (M + 1), ∀ i : ι,
      ‖applyOps sz n (L i) (qRow sz n (k i) (Yq (k i) ∅)) ω‖ ≤ B₀ * (2 * Ψ) ^ numQ (L i) := by
    intro ω hω i
    have hωi : ω ∉ Bad ((L i).length + 1) := by
      intro hmem
      exact hω (hfam.mono_le (by have := hlen i; omega) hmem)
    have hkey := GreenCond_norm_word_le hY hind hEnv hfam hε (by positivity) (k i) (L i)
      (fun ω' hω' => hgood ω' hω' (k i) (hkA i) (L i) (h1 i) (h2 i) (hlen i)) ω hωi
    refine hkey.trans ?_
    set q : ℕ := numQ (L i) with hq
    have hqM : q ≤ M := le_trans List.countP_le_length (hlen i)
    have hgain : (2 : ℝ) ^ (q + 1) * (cM * Ψ ^ (q + 1)) = (2 * Ψ) ^ q * (2 * cM * Ψ) := by
      rw [mul_pow, pow_succ, pow_succ]; ring
    have hpowle : ((2 * Ψ) ^ M : ℝ) ≤ (2 * Ψ) ^ q := pow_le_pow_of_le_one h2Ψ0.le hΨ1 hqM
    have hexact : (2 * Ψ) ^ M * GreenCond_cost Env M Ψ ε = ((M : ℝ) + 1) * GreenCond_genv Env M * ε := by
      unfold GreenCond_cost
      field_simp
    have hlenR : ((L i).length : ℝ) + 1 ≤ (M : ℝ) + 1 := by
      have : ((L i).length : ℝ) ≤ (M : ℝ) := by exact_mod_cast hlen i
      linarith
    have h2q : (2 : ℝ) ^ (q + 1) * (2 ^ q * Env) ≤ GreenCond_genv Env M := by
      unfold GreenCond_genv
      have hrw : (2 : ℝ) ^ (q + 1) * (2 ^ q * Env) = 2 ^ (2 * q + 1) * Env := by
        rw [show 2 * q + 1 = q + q + 1 by omega, pow_succ, pow_add]; ring
      rw [hrw]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hEnv0
    have hexc : (2 : ℝ) ^ (q + 1) * (((L i).length + 1) * (2 ^ q * Env) * ε) ≤ (2 * Ψ) ^ q * GreenCond_cost Env M Ψ ε := by
      have hstep : (2 : ℝ) ^ (q + 1) * (((L i).length + 1) * (2 ^ q * Env) * ε)
          = (((L i).length : ℝ) + 1) * (2 ^ (q + 1) * (2 ^ q * Env)) * ε := by ring
      rw [hstep]
      have hA : (((L i).length : ℝ) + 1) * (2 ^ (q + 1) * (2 ^ q * Env)) * ε ≤ ((M : ℝ) + 1) * GreenCond_genv Env M * ε := by
        have hnn2 : (0 : ℝ) ≤ (2 : ℝ) ^ (q + 1) * (2 ^ q * Env) := by positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul hlenR h2q hnn2 (by positivity)) hε
      refine hA.trans ?_
      rw [← hexact]
      exact mul_le_mul_of_nonneg_right hpowle hcost0
    have hsplit : (2 : ℝ) ^ (q + 1) * (cM * Ψ ^ (q + 1) + ((L i).length + 1) * (2 ^ q * Env) * ε)
        = 2 ^ (q + 1) * (cM * Ψ ^ (q + 1)) + 2 ^ (q + 1) * (((L i).length + 1) * (2 ^ q * Env) * ε) := by ring
    rw [hsplit, hgain, hB₀]
    calc (2 * Ψ) ^ q * (2 * cM * Ψ) + 2 ^ (q + 1) * (((L i).length + 1) * (2 ^ q * Env) * ε)
        ≤ (2 * Ψ) ^ q * (2 * cM * Ψ) + (2 * Ψ) ^ q * GreenCond_cost Env M Ψ ε := by linarith
      _ = (2 * cM * Ψ + GreenCond_cost Env M Ψ ε) * (2 * Ψ) ^ q := by ring
  -- the global envelope
  have hqb : ∀ (k' : Idx d (sz.L n) (sz.W n)) ω', ‖qRow sz n k' (Yq k' ∅) ω'‖ ≤ 2 * Env := fun k' ω' =>
    norm_sub_condRow_le (hEnv k' ∅) ω'
  have hG : ∀ ω : sz.SeqΩ, ∏ i, ‖applyOps sz n (L i) (qRow sz n (k i) (Yq (k i) ∅)) ω‖ ≤ GreenCond_genv Env M ^ Fintype.card ι := by
    intro ω
    calc ∏ i, ‖applyOps sz n (L i) (qRow sz n (k i) (Yq (k i) ∅)) ω‖ ≤ ∏ _i : ι, GreenCond_genv Env M := by
          refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
          refine (norm_applyOps_le (L i) (fun ω' => hqb (k i) ω') ω).trans ?_
          have hqM : numQ (L i) ≤ M := le_trans List.countP_le_length (hlen i)
          unfold GreenCond_genv
          have : (2 : ℝ) ^ numQ (L i) * (2 * Env) = 2 ^ (numQ (L i) + 1) * Env := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hEnv0
      _ = GreenCond_genv Env M ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]
  have hbm : ∀ i : ι, BddMeas sz (applyOps sz n (L i) (qRow sz n (k i) (Yq (k i) ∅))) :=
    fun i => ((hY (k i) ∅).qRow (k i)).applyOps (L i)
  have hb0 : ∀ i : ι, 0 ≤ B₀ * (2 * Ψ) ^ numQ (L i) := fun i => by positivity
  refine le_trans (integral_prod_norm_le_of_bounds_on hbm (hfam.meas (M + 1)) hb0 hb hG) ?_
  have heq : (∏ i : ι, B₀ * (2 * Ψ) ^ numQ (L i)) = B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum, Finset.card_univ]
  rw [heq]
  -- absorption
  have hq : (∑ i, numQ (L i)) ≤ K * M := by
    have hstep : (∑ i, numQ (L i)) ≤ ∑ _i : ι, M :=
      Finset.sum_le_sum fun i _ => le_trans List.countP_le_length (hlen i)
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hstep
    exact le_trans hstep (Nat.mul_le_mul_right M hcard)
  have hPnn : 0 ≤ (Sizes.seqP sz).real (Bad (M + 1)) := measureReal_nonneg
  have hmainnn : 0 ≤ B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) := by positivity
  have hrem : GreenCond_genv Env M ^ Fintype.card ι * (Sizes.seqP sz).real (Bad (M + 1))
      ≤ B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) := by
    calc GreenCond_genv Env M ^ Fintype.card ι * (Sizes.seqP sz).real (Bad (M + 1))
        ≤ GreenCond_genv Env M ^ K * (Sizes.seqP sz).real (Bad (M + 1)) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hG1 hcard) hPnn
      _ ≤ B₀ ^ K * (2 * Ψ) ^ (K * M) := hsmall
      _ ≤ B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) := by
          refine mul_le_mul (pow_le_pow_of_le_one hB₀0 hB1 hcard) (pow_le_pow_of_le_one h2Ψ0.le hΨ1 hq) (by positivity)
            (by positivity)
  have hdouble : (2 : ℝ) ≤ 2 ^ Fintype.card ι := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ Fintype.card ι := pow_le_pow_right₀ one_le_two hpos
  calc B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) + GreenCond_genv Env M ^ Fintype.card ι * (Sizes.seqP sz).real (Bad (M + 1))
      ≤ B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) + B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) := by
        linarith
    _ = 2 * (B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i)) := by ring
    _ ≤ 2 ^ Fintype.card ι * (B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i)) :=
        mul_le_mul_of_nonneg_right hdouble hmainnn
    _ = (2 * B₀) ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) := by
        rw [mul_pow (2 : ℝ) B₀ (Fintype.card ι)]; ring

section Slice
variable {d : ℕ}

/-- **The base of the tower of exceptional sets**: a measurable hull (for the carrier law `seqP (sz.withLam 0)`) of the complement of the per-time
good event `{ω | ‖G_t(ω) - M‖_max ≤ δ}`. -/
def GreenCond_badBase (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t δ : ℝ) : Set (sz.withLam 0).SeqΩ :=
  toMeasurable (Sizes.seqP (sz.withLam 0))
    {ω : (sz.withLam 0).SeqΩ | ¬ ∀ x y : Vtx d (sz.L n) (sz.W n), ‖GreenCore_Gc sz z n t ω x y - GreenCore_Mc sz z n x y‖ ≤ δ}

theorem GreenCond_measurableSet_badBase (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t δ : ℝ) :
    MeasurableSet (GreenCond_badBase sz z n t δ) := measurableSet_toMeasurable _ _

theorem GreenCond_meas_badBase (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t δ : ℝ) :
    (Sizes.seqP (sz.withLam 0)) (GreenCond_badBase sz z n t δ) =
      (Sizes.seqP (sz.withLam 0)) {ω : (sz.withLam 0).SeqΩ | ¬ ∀ x y : Vtx d (sz.L n) (sz.W n),
        ‖GreenCore_Gc sz z n t ω x y - GreenCore_Mc sz z n x y‖ ≤ δ} := measure_toMeasurable _

theorem GreenCond_good_of_notMem_badBase (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t δ : ℝ) {ω : (sz.withLam 0).SeqΩ}
    (hω : ω ∉ GreenCond_badBase sz z n t δ) (x y : Vtx d (sz.L n) (sz.W n)) :
    ‖GreenCore_Gc sz z n t ω x y - GreenCore_Mc sz z n x y‖ ≤ δ := by
  by_contra hxy
  exact hω (subset_toMeasurable _ _ fun hall => hxy (hall x y))

/-- **The BA gain interface at one slice**: with `Bad = badTower` over the hull of the complement of `{‖G_t - M‖_max ≤ δ}` (row-section
threshold `ε'`), `Ψ = 2δ` (`4δ ≤ κ`, `8Mδ ≤ κ`, `2δ ≤ 1`), `c_M ≥ c_Y(M)`, the envelope `Env ≥ GreenCond_Env`, and the two numerical conditions
`hB1`, `hsmall`, the families `Y^A` and `Y^X_{·, (α, o)}` on the block `β ≠ α` satisfy `famGain(B, 4δ, M, K)`, `B = 2 (4 c_M δ + condCost)`. -/
theorem GreenCond_famGain_slice {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) {z : ℕ → ℂ} (h : BAFlow sz κ ε 𝔠 𝔡 z) (t : ℕ → ℝ) (n : ℕ)
    (ht0 : 0 ≤ t n) (ht : t n ≤ BAflowT0 sz z n) (hg0 : 0 ≤ BAflowLam0 sz z n) {δ ε' Env cM : ℝ} {M K : ℕ}
    (hδ0 : 0 < δ) (hδ4 : 4 * δ ≤ κ) (hMδ : 8 * (M : ℝ) * δ ≤ κ) (hδ2 : 2 * δ ≤ 1) (hε' : 0 ≤ ε')
    (hEnv : GreenCond_Env d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ (|(GreenCond_zt sz z n (t n)).im|⁻¹ + 1) ≤ Env) (hEnv1 : 1 ≤ Env)
    (hcM : GreenMinor_cY d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ M ≤ cM)
    (hB1 : 2 * cM * (2 * δ) + GreenCond_cost Env M (2 * δ) ε' ≤ 1)
    (hsmall : GreenCond_genv Env M ^ K *
        (Sizes.seqP (sz.withLam 0)).real (badTower (sz.withLam 0) n ε' (GreenCond_badBase sz z n (t n) δ) (M + 1)) ≤
      (2 * cM * (2 * δ) + GreenCond_cost Env M (2 * δ) ε') ^ K * (2 * (2 * δ)) ^ (K * M))
    (β α : Zd d (sz.L n)) (hβα : β ≠ α) :
    GreenMinor_famGain (sz.withLam 0) n (Iblk d (sz.L n) (sz.W n) β) (GreenMinor_famA sz z t n)
        (2 * (2 * cM * (2 * δ) + GreenCond_cost Env M (2 * δ) ε')) (2 * (2 * δ)) M K ∧
      GreenMinor_famGain (sz.withLam 0) n (Iblk d (sz.L n) (sz.W n) β) (GreenMinor_famX sz z t n α)
        (2 * (2 * cM * (2 * δ) + GreenCond_cost Env M (2 * δ) ε')) (2 * (2 * δ)) M K := by
  classical
  have dat := GreenCond_data hκ sz h n ht0 ht hg0
  have hfam : BadFamily (sz.withLam 0) n ε' (badTower (sz.withLam 0) n ε' (GreenCond_badBase sz z n (t n) δ)) :=
    badFamily_badTower (sz.withLam 0) n ε' (GreenCond_measurableSet_badBase sz z n (t n) δ)
  have hs0 : 0 ≤ ‖GreenCond_s sz z n‖ := norm_nonneg _
  have hcM0 : 0 ≤ cM := by
    refine le_trans ?_ hcM
    have ha := GreenMinor_a_nonneg dat.hκ dat.hκ1 M
    unfold GreenMinor_cY
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have := dat.hκ
    positivity
  have hΨ0 : 0 < 2 * δ := by linarith
  have hΨ1 : 2 * (2 * δ) ≤ 1 := by linarith [dat.hκ1]
  have hgoodX : ∀ ω ∉ badTower (sz.withLam 0) n ε' (GreenCond_badBase sz z n (t n) δ) 0, ∀ k ∈ Iblk d (sz.L n) (sz.W n) β,
      ∀ L : List (Bool × Idx d (sz.L n) (sz.W n)), (L.map Prod.snd).Nodup →
      (∀ x ∈ L, x.2 ≠ k ∧ x.2 ∈ Iblk d (sz.L n) (sz.W n) β) → L.length ≤ M →
      (‖minorDiff (sz.withLam 0) n (qList L) (GreenCond_famS sz z n (t n) (GreenCond_ΦA sz z n k)) ω‖ ≤ cM * (2 * δ) ^ (numQ L + 1)) ∧
      (‖minorDiff (sz.withLam 0) n (qList L) (GreenCond_famS sz z n (t n) (GreenCond_ΦX sz z n α k)) ω‖ ≤ cM * (2 * δ) ^ (numQ L + 1)) := by
    intro ω hω k hk L hL1 hL2 hlen
    have hG := GreenCond_good_of_notMem_badBase sz z n (t n) δ (by simpa using hω)
    have hkβ : (split d (sz.L n) (sz.W n) k).1 = β := by simpa [Iblk] using hk
    have hL2' : ∀ x ∈ L, x.2 ≠ k ∧ (split d (sz.L n) (sz.W n) x.2).1 = (split d (sz.L n) (sz.W n) k).1 :=
      fun x hx => ⟨(hL2 x hx).1, by rw [hkβ]; simpa [Iblk] using (hL2 x hx).2⟩
    have hqM : numQ L ≤ M := le_trans List.countP_le_length hlen
    have hmain := GreenCond_minorDiff_le sz z n hκ h ht0 ht hg0 hδ0.le hδ4 hMδ hδ2 hG k L hL1 hL2' hqM α (by rw [hkβ]; exact hβα.symm)
    have hc : GreenMinor_cY d κ (BAflowLam0 sz z n) ‖GreenCond_s sz z n‖ (numQ L) ≤ cM :=
      (GreenCond_cY_mono dat.hκ dat.hκ1 hg0 le_rfl hs0 le_rfl hqM).trans hcM
    have hp : 0 ≤ (2 * δ) ^ (numQ L + 1) := by positivity
    exact ⟨hmain.1.trans (mul_le_mul_of_nonneg_right hc hp), hmain.2.trans (mul_le_mul_of_nonneg_right hc hp)⟩
  have hempA : (fun k => GreenCond_famS sz z n (t n) (GreenCond_ΦA sz z n k) ∅) = GreenMinor_famA sz z t n := by
    funext k
    rw [GreenCond_famS_empty sz z n hκ h ht0 ht]
    rfl
  have hempX : (fun k => GreenCond_famS sz z n (t n) (GreenCond_ΦX sz z n α k) ∅) = GreenMinor_famX sz z t n α := by
    funext k
    rw [GreenCond_famS_empty sz z n hκ h ht0 ht]
    rfl
  constructor
  · rw [← hempA]
    exact GreenCond_famGain_of_good (sz := sz.withLam 0) (n := n) (A := Iblk d (sz.L n) (sz.W n) β)
      (Yq := fun k S => GreenCond_famS sz z n (t n) (GreenCond_ΦA sz z n k) S) (Env := Env) (cM := cM) (Ψ := 2 * δ) (ε := ε')
      (M := M) (K := K) (Bad := badTower (sz.withLam 0) n ε' (GreenCond_badBase sz z n (t n) δ))
      (fun k S => GreenCond_bddMeas_A sz z n hκ h ht0 ht hg0 k S) (fun k S => GreenCond_finDepOffRows sz z n (t n) S _)
      (fun k S ω => (GreenCond_norm_fam_le sz z n hκ h ht0 ht hg0 S ω k α).1.trans hEnv) hfam hε' hΨ0 hΨ1 hcM0 hEnv1
      (fun ω hω k hk L hL1 hL2 hlen => (hgoodX ω hω k hk L hL1 hL2 hlen).1) hB1 hsmall
  · rw [← hempX]
    exact GreenCond_famGain_of_good (sz := sz.withLam 0) (n := n) (A := Iblk d (sz.L n) (sz.W n) β)
      (Yq := fun k S => GreenCond_famS sz z n (t n) (GreenCond_ΦX sz z n α k) S) (Env := Env) (cM := cM) (Ψ := 2 * δ) (ε := ε')
      (M := M) (K := K) (Bad := badTower (sz.withLam 0) n ε' (GreenCond_badBase sz z n (t n) δ))
      (fun k S => GreenCond_bddMeas_X sz z n hκ h ht0 ht hg0 α k S) (fun k S => GreenCond_finDepOffRows sz z n (t n) S _)
      (fun k S ω => (GreenCond_norm_fam_le sz z n hκ h ht0 ht hg0 S ω k α).2.trans hEnv) hfam hε' hΨ0 hΨ1 hcM0 hEnv1
      (fun ω hω k hk L hL1 hL2 hlen => (hgoodX ω hω k hk L hL1 hL2 hlen).2) hB1 hsmall

end Slice

end Cond

/-! ## 4. The Gaussian row of the carrier: coordinate moments

`seqP` is a product of centred Gaussians; the row `H_{u·}` of `H_T = √T X` is a vector of centred complex Gaussians with independent
real and imaginary parts (`Xentry_eq_rowCoord`).  The facts used by the conditional means: `E H_{uk} = 0`, `E H_{uk} conj H_{ul} = δ_{kl} T S_{uk}`,
`E |H_{uk}|⁴ ≤ 6 T² S_{uk}²`. -/

section RowGauss
variable {d : ℕ} (sz : Sizes d)

theorem GreenCond_memLp_coord (c : Sizes.SeqCoord sz) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (fun ω : Sizes.SeqΩ sz => ω c) p (Sizes.seqP sz) :=
  (LinearForm.hasLaw_coord sz c).memLp (memLp_id_gaussianReal' p hp)

theorem GreenCond_integral_coord (c : Sizes.SeqCoord sz) : ∫ ω, ω c ∂(Sizes.seqP sz) = 0 := by
  have h := (LinearForm.hasLaw_coord sz c).integral_eq
  rw [h, integral_id_gaussianReal]

theorem GreenCond_integral_coord_mul {c c' : Sizes.SeqCoord sz} (h : c ≠ c') :
    ∫ ω, ω c * ω c' ∂(Sizes.seqP sz) = 0 := by
  have hind := (LinearForm.iIndepFun_coord sz).indepFun h
  have := hind.integral_mul_eq_mul_integral (measurable_pi_apply c).aestronglyMeasurable (measurable_pi_apply c').aestronglyMeasurable
  simpa [GreenCond_integral_coord] using this



variable {sz}

theorem GreenCond_h_eq {n : ℕ} (T : ℝ) {u k : Idx d (sz.L n) (sz.W n)} (hk : u ≠ k) (ω : Sizes.SeqΩ sz) :
    Sizes.seqHflow sz n T ω u k = (Real.sqrt T : ℂ) * ((ω (rowCoord sz n u k true) : ℂ) +
      (rowSign sz n u k : ℂ) * Complex.I * (ω (rowCoord sz n u k false) : ℂ)) := by
  show (Real.sqrt T : ℂ) * Xentry d (sz.L n) (sz.W n) (Sizes.slice sz n ω) u k = _
  rw [Xentry_eq_rowCoord hk ω]

theorem GreenCond_h_diag {n : ℕ} (T : ℝ) (u : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    Sizes.seqHflow sz n T ω u u = (Real.sqrt T : ℂ) * ((ω ⟨n, u, u, true⟩ : ℝ) : ℂ) := by
  show (Real.sqrt T : ℂ) * Xentry d (sz.L n) (sz.W n) (Sizes.slice sz n ω) u u = _
  unfold Xentry
  simp only [lt_self_iff_false, ↓reduceIte]
  rfl

theorem GreenCond_integrable_coordC (sz : Sizes d) (c : Sizes.SeqCoord sz) :
    Integrable (fun ω : Sizes.SeqΩ sz => ((ω c : ℝ) : ℂ)) (Sizes.seqP sz) :=
  (memLp_one_iff_integrable.1 (GreenCond_memLp_coord sz c 1 ENNReal.one_ne_top)).ofReal

theorem GreenCond_integral_coordC (sz : Sizes d) (c : Sizes.SeqCoord sz) :
    ∫ ω, ((ω c : ℝ) : ℂ) ∂(Sizes.seqP sz) = 0 := by
  rw [integral_complex_ofReal, GreenCond_integral_coord]; simp

/-- **Mean zero**: `E H_{uk} = 0`. -/
theorem GreenCond_integral_h {n : ℕ} (T : ℝ) {u k : Idx d (sz.L n) (sz.W n)} (hk : u ≠ k) :
    ∫ ω, Sizes.seqHflow sz n T ω u k ∂(Sizes.seqP sz) = 0 := by
  simp_rw [GreenCond_h_eq T hk]
  rw [integral_const_mul, integral_add (GreenCond_integrable_coordC sz _) ((GreenCond_integrable_coordC sz _).const_mul _),
    integral_const_mul, GreenCond_integral_coordC, GreenCond_integral_coordC]
  simp

theorem GreenCond_integral_h_diag {n : ℕ} (T : ℝ) (u : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, Sizes.seqHflow sz n T ω u u ∂(Sizes.seqP sz) = 0 := by
  simp_rw [GreenCond_h_diag T u]
  rw [integral_const_mul, GreenCond_integral_coordC]; simp

end RowGauss

/-! ## 5. The abstract row model: moments of the polynomial `Φ = t m + h_u - Σ_{k,l} h_k c_{kl} (D_l + conj h_l)` of a Gaussian row

A pure measure-theory statement (the row law is a structure `GreenCond_RowLaw`): the mean of `Φ` is `t m - Σ_k σ_k c_{kk}`, the second moment is
`≤ 3 (‖tm‖² + S_u + 2 γ² δ_D² ν² + 12 γ² ν⁴)`; the linear form `Σ_k h_k c_k` has mean zero and second moment `≤ γ² ν²`. -/

section RowModel
variable {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'} [IsProbabilityMeasure P] {κ : Type*} [DecidableEq κ]

/-- The law of a Gaussian row: measurable entries with integrable fourth moments, mean zero, `E h_k conj h_l = δ_{kl} σ_k`, `E |h_k|⁴ ≤ 6 σ_k²`. -/
structure GreenCond_RowLaw (P : Measure Ω') (s : Finset κ) (h : κ → Ω' → ℂ) (σ : κ → ℝ) : Prop where
  meas : ∀ k ∈ s, Measurable (h k)
  int4 : ∀ k ∈ s, Integrable (fun ω => ‖h k ω‖ ^ 4) P
  mean : ∀ k ∈ s, ∫ ω, h k ω ∂P = 0
  cov : ∀ k ∈ s, ∀ l ∈ s, ∫ ω, h k ω * (starRingEnd ℂ) (h l ω) ∂P = if k = l then (σ k : ℂ) else 0
  fourth : ∀ k ∈ s, ∫ ω, ‖h k ω‖ ^ 4 ∂P ≤ 6 * σ k ^ 2

variable {s : Finset κ} {h : κ → Ω' → ℂ} {σ : κ → ℝ}

theorem GreenCond_RowLaw.int2 (H : GreenCond_RowLaw P s h σ) {k : κ} (hk : k ∈ s) : Integrable (fun ω => ‖h k ω‖ ^ 2) P := by
  refine ((H.int4 k hk).add (integrable_const (1 : ℝ))).mono' ((H.meas k hk).norm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  have h0 : 0 ≤ ‖h k ω‖ ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  have : ‖h k ω‖ ^ 2 ≤ ‖h k ω‖ ^ 4 + 1 := by nlinarith [sq_nonneg (‖h k ω‖ ^ 2 - 1)]
  exact this

theorem GreenCond_RowLaw.int1 (H : GreenCond_RowLaw P s h σ) {k : κ} (hk : k ∈ s) : Integrable (h k) P := by
  refine ((H.int2 hk).add (integrable_const (1 : ℝ))).mono' (H.meas k hk).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  have h0 : 0 ≤ ‖h k ω‖ := norm_nonneg _
  have : ‖h k ω‖ ≤ ‖h k ω‖ ^ 2 + 1 := by nlinarith [sq_nonneg (‖h k ω‖ - 1)]
  simpa using this

theorem GreenCond_RowLaw.intCov (H : GreenCond_RowLaw P s h σ) {k l : κ} (hk : k ∈ s) (hl : l ∈ s) :
    Integrable (fun ω => h k ω * (starRingEnd ℂ) (h l ω)) P := by
  refine ((H.int2 hk).add (H.int2 hl)).mono' ((H.meas k hk).mul (Complex.continuous_conj.measurable.comp (H.meas l hl))).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply, norm_mul, Complex.norm_conj]
  nlinarith [sq_nonneg (‖h k ω‖ - ‖h l ω‖)]

theorem GreenCond_RowLaw.sigma_nonneg (H : GreenCond_RowLaw P s h σ) {k : κ} (hk : k ∈ s) : 0 ≤ σ k := by
  have := H.cov k hk k hk
  simp only [↓reduceIte] at this
  have h2 : ∫ ω, ‖h k ω‖ ^ 2 ∂P = σ k := by
    have e : ∀ ω, h k ω * (starRingEnd ℂ) (h k ω) = ((‖h k ω‖ ^ 2 : ℝ) : ℂ) := fun ω => by rw [Complex.mul_conj']; push_cast; rfl
    simp_rw [e] at this
    rw [integral_complex_ofReal] at this
    exact_mod_cast this
  rw [← h2]
  exact integral_nonneg fun ω => by positivity



/-- `Φ = t m + h_u - Σ_{k,l ∈ s} h_k c_{kl} (D_l + conj h_l)`: the random re-entry `A_u` as a polynomial of the row. -/
def GreenCond_Phi (s : Finset κ) (h : κ → Ω' → ℂ) (hu : Ω' → ℂ) (c : κ → κ → ℂ) (D : κ → ℂ) (tm : ℂ) (ω : Ω') : ℂ :=
  tm + hu ω - ∑ k ∈ s, ∑ l ∈ s, h k ω * c k l * (D l + (starRingEnd ℂ) (h l ω))

/-- `R = Σ_{k ∈ s} ‖h_k‖`. -/
def GreenCond_R (s : Finset κ) (h : κ → Ω' → ℂ) (ω : Ω') : ℝ := ∑ k ∈ s, ‖h k ω‖

theorem GreenCond_R_nonneg (s : Finset κ) (h : κ → Ω' → ℂ) (ω : Ω') : 0 ≤ GreenCond_R s h ω :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- **The mean of `Φ`**: `E Φ = t m - Σ_k σ_k c_{kk}`. -/
theorem GreenCond_integral_Phi (H : GreenCond_RowLaw P s h σ) {hu : Ω' → ℂ} (hui : Integrable hu P) (hum : ∫ ω, hu ω ∂P = 0)
    (c : κ → κ → ℂ) (D : κ → ℂ) (tm : ℂ) :
    ∫ ω, GreenCond_Phi s h hu c D tm ω ∂P = tm - ∑ k ∈ s, (σ k : ℂ) * c k k := by
  have e : ∀ ω, GreenCond_Phi s h hu c D tm ω = tm + hu ω - (∑ k ∈ s, ∑ l ∈ s, (c k l * D l) * h k ω +
      ∑ k ∈ s, ∑ l ∈ s, c k l * (h k ω * (starRingEnd ℂ) (h l ω))) := by
    intro ω
    unfold GreenCond_Phi
    rw [← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  simp_rw [e]
  have i1 : ∀ k ∈ s, ∀ l ∈ s, Integrable (fun ω => (c k l * D l) * h k ω) P := fun k hk l _ => (H.int1 hk).const_mul _
  have i2 : ∀ k ∈ s, ∀ l ∈ s, Integrable (fun ω => c k l * (h k ω * (starRingEnd ℂ) (h l ω))) P :=
    fun k hk l hl => (H.intCov hk hl).const_mul _
  have iS1 : Integrable (fun ω => ∑ k ∈ s, ∑ l ∈ s, (c k l * D l) * h k ω) P :=
    integrable_finsetSum _ fun k hk => integrable_finsetSum _ fun l hl => i1 k hk l hl
  have iS2 : Integrable (fun ω => ∑ k ∈ s, ∑ l ∈ s, c k l * (h k ω * (starRingEnd ℂ) (h l ω))) P :=
    integrable_finsetSum _ fun k hk => integrable_finsetSum _ fun l hl => i2 k hk l hl
  have hS1 : ∫ ω, ∑ k ∈ s, ∑ l ∈ s, (c k l * D l) * h k ω ∂P = 0 := by
    rw [integral_finsetSum _ (fun k hk => integrable_finsetSum _ fun l hl => i1 k hk l hl)]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [integral_finsetSum _ (fun l hl => i1 k hk l hl)]
    refine Finset.sum_eq_zero fun l hl => ?_
    rw [integral_const_mul, H.mean k hk]; simp
  have hS2 : ∫ ω, ∑ k ∈ s, ∑ l ∈ s, c k l * (h k ω * (starRingEnd ℂ) (h l ω)) ∂P = ∑ k ∈ s, (σ k : ℂ) * c k k := by
    rw [integral_finsetSum _ (fun k hk => integrable_finsetSum _ fun l hl => i2 k hk l hl)]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [integral_finsetSum _ (fun l hl => i2 k hk l hl)]
    have : ∀ l ∈ s, ∫ ω, c k l * (h k ω * (starRingEnd ℂ) (h l ω)) ∂P = c k l * (if k = l then (σ k : ℂ) else 0) :=
      fun l hl => by rw [integral_const_mul, H.cov k hk l hl]
    rw [Finset.sum_congr rfl this]
    simp [mul_ite, Finset.sum_ite_eq, hk, mul_comm]
  have iT : Integrable (fun ω => tm + hu ω) P := (integrable_const tm).add hui
  have iSS : Integrable (fun ω => (∑ k ∈ s, ∑ l ∈ s, (c k l * D l) * h k ω) +
      ∑ k ∈ s, ∑ l ∈ s, c k l * (h k ω * (starRingEnd ℂ) (h l ω))) P := iS1.add iS2
  rw [integral_sub iT iSS, integral_add (integrable_const tm) hui, integral_add iS1 iS2, hS1, hS2, hum]
  simp

theorem GreenCond_RowLaw.integral_sq (H : GreenCond_RowLaw P s h σ) {k : κ} (hk : k ∈ s) : ∫ ω, ‖h k ω‖ ^ 2 ∂P = σ k := by
  have := H.cov k hk k hk
  simp only [↓reduceIte] at this
  have e : ∀ ω, h k ω * (starRingEnd ℂ) (h k ω) = ((‖h k ω‖ ^ 2 : ℝ) : ℂ) := fun ω => by rw [Complex.mul_conj']; push_cast; rfl
  simp_rw [e] at this
  rw [integral_complex_ofReal] at this
  exact_mod_cast this

/-- The pointwise polynomial bound on `Φ`. -/
theorem GreenCond_norm_Phi_le {hu : Ω' → ℂ} {c : κ → κ → ℂ} {D : κ → ℂ} {tm : ℂ} {γ : ℝ} (hγ : 0 ≤ γ) (hc : ∀ k ∈ s, ∀ l ∈ s, ‖c k l‖ ≤ γ)
    (ω : Ω') : ‖GreenCond_Phi s h hu c D tm ω‖ ≤
      ‖tm‖ + ‖hu ω‖ + γ * GreenCond_R s h ω * (∑ l ∈ s, ‖D l‖ + GreenCond_R s h ω) := by
  unfold GreenCond_Phi
  have h1 : ‖∑ k ∈ s, ∑ l ∈ s, h k ω * c k l * (D l + (starRingEnd ℂ) (h l ω))‖ ≤
      γ * GreenCond_R s h ω * (∑ l ∈ s, ‖D l‖ + GreenCond_R s h ω) := by
    calc ‖∑ k ∈ s, ∑ l ∈ s, h k ω * c k l * (D l + (starRingEnd ℂ) (h l ω))‖
        ≤ ∑ k ∈ s, ∑ l ∈ s, ‖h k ω‖ * γ * (‖D l‖ + ‖h l ω‖) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => ?_))
          rw [norm_mul, norm_mul]
          refine mul_le_mul (mul_le_mul_of_nonneg_left (hc k hk l hl) (norm_nonneg _)) ?_ (norm_nonneg _) (by positivity)
          exact (norm_add_le _ _).trans (by rw [Complex.norm_conj])
      _ = γ * GreenCond_R s h ω * (∑ l ∈ s, ‖D l‖ + GreenCond_R s h ω) := by
          unfold GreenCond_R
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
          ring
  calc ‖tm + hu ω - ∑ k ∈ s, ∑ l ∈ s, h k ω * c k l * (D l + (starRingEnd ℂ) (h l ω))‖
      ≤ ‖tm + hu ω‖ + ‖∑ k ∈ s, ∑ l ∈ s, h k ω * c k l * (D l + (starRingEnd ℂ) (h l ω))‖ := norm_sub_le _ _
    _ ≤ (‖tm‖ + ‖hu ω‖) + _ := add_le_add (norm_add_le _ _) h1
    _ = _ := by ring

theorem GreenCond_R_sq_le (s : Finset κ) (h : κ → Ω' → ℂ) (ω : Ω') :
    GreenCond_R s h ω ^ 2 ≤ (s.card : ℝ) * ∑ k ∈ s, ‖h k ω‖ ^ 2 := sq_sum_le_card_mul_sum_sq

theorem GreenCond_R_pow4_le (s : Finset κ) (h : κ → Ω' → ℂ) (ω : Ω') :
    GreenCond_R s h ω ^ 4 ≤ (s.card : ℝ) ^ 3 * ∑ k ∈ s, ‖h k ω‖ ^ 4 := by
  have h1 := GreenCond_R_sq_le s h ω
  have h2 : (∑ k ∈ s, ‖h k ω‖ ^ 2) ^ 2 ≤ (s.card : ℝ) * ∑ k ∈ s, (‖h k ω‖ ^ 2) ^ 2 := sq_sum_le_card_mul_sum_sq
  have hν : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
  have hR2 : 0 ≤ GreenCond_R s h ω ^ 2 := by positivity
  calc GreenCond_R s h ω ^ 4 = (GreenCond_R s h ω ^ 2) ^ 2 := by ring
    _ ≤ ((s.card : ℝ) * ∑ k ∈ s, ‖h k ω‖ ^ 2) ^ 2 := pow_le_pow_left₀ hR2 h1 2
    _ = (s.card : ℝ) ^ 2 * (∑ k ∈ s, ‖h k ω‖ ^ 2) ^ 2 := by ring
    _ ≤ (s.card : ℝ) ^ 2 * ((s.card : ℝ) * ∑ k ∈ s, (‖h k ω‖ ^ 2) ^ 2) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (s.card : ℝ) ^ 3 * ∑ k ∈ s, ‖h k ω‖ ^ 4 := by
        rw [← mul_assoc, ← pow_succ]
        congr 1
        refine Finset.sum_congr rfl fun k _ => by ring

/-- `‖Φ‖² ≤ 3 (‖tm‖² + ‖hu‖² + 2γ² δ_D² ν Σ‖h_k‖² + 2 γ² ν³ Σ‖h_k‖⁴)`, `ν = #s`, `δ_D = Σ‖D_l‖`. -/
theorem GreenCond_normSq_Phi_le {hu : Ω' → ℂ} {c : κ → κ → ℂ} {D : κ → ℂ} {tm : ℂ} {γ : ℝ} (hγ : 0 ≤ γ)
    (hc : ∀ k ∈ s, ∀ l ∈ s, ‖c k l‖ ≤ γ) (ω : Ω') :
    ‖GreenCond_Phi s h hu c D tm ω‖ ^ 2 ≤ 3 * (‖tm‖ ^ 2 + ‖hu ω‖ ^ 2 + 2 * γ ^ 2 * (∑ l ∈ s, ‖D l‖) ^ 2 * ((s.card : ℝ) * ∑ k ∈ s, ‖h k ω‖ ^ 2) +
      2 * γ ^ 2 * ((s.card : ℝ) ^ 3 * ∑ k ∈ s, ‖h k ω‖ ^ 4)) := by
  have hb := GreenCond_norm_Phi_le (h := h) (hu := hu) (D := D) (tm := tm) hγ hc ω
  set R := GreenCond_R s h ω with hR
  have hR0 : 0 ≤ R := GreenCond_R_nonneg s h ω
  set δD := ∑ l ∈ s, ‖D l‖ with hδD
  have hδD0 : 0 ≤ δD := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h2 := GreenCond_R_sq_le s h ω
  have h4 := GreenCond_R_pow4_le s h ω
  set a := ‖tm‖ with ha
  set b := ‖hu ω‖ with hb'
  set c' := γ * R * (δD + R) with hc'
  have hc0 : 0 ≤ c' := by positivity
  have hP : 0 ≤ ‖GreenCond_Phi s h hu c D tm ω‖ := norm_nonneg _
  have hP2 : ‖GreenCond_Phi s h hu c D tm ω‖ ^ 2 ≤ (a + b + c') ^ 2 := pow_le_pow_left₀ hP hb 2
  have h3 : (a + b + c') ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c' ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c'), sq_nonneg (b - c')]
  have hcc : c' ^ 2 ≤ 2 * γ ^ 2 * δD ^ 2 * R ^ 2 + 2 * γ ^ 2 * R ^ 4 := by
    rw [hc']
    nlinarith [sq_nonneg (δD - R), mul_nonneg (sq_nonneg γ) (sq_nonneg R)]
  have hν : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
  have e1 : 2 * γ ^ 2 * δD ^ 2 * R ^ 2 ≤ 2 * γ ^ 2 * δD ^ 2 * ((s.card : ℝ) * ∑ k ∈ s, ‖h k ω‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have e2 : 2 * γ ^ 2 * R ^ 4 ≤ 2 * γ ^ 2 * ((s.card : ℝ) ^ 3 * ∑ k ∈ s, ‖h k ω‖ ^ 4) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  nlinarith [hP2, h3, hcc, e1, e2]

theorem GreenCond_measurable_Phi (H : GreenCond_RowLaw P s h σ) {hu : Ω' → ℂ} (hum : Measurable hu) (c : κ → κ → ℂ) (D : κ → ℂ) (tm : ℂ) :
    Measurable (GreenCond_Phi s h hu c D tm) := by
  unfold GreenCond_Phi
  refine (measurable_const.add hum).sub (Finset.measurable_sum _ fun k hk => Finset.measurable_sum _ fun l hl => ?_)
  exact ((H.meas k hk).mul measurable_const).mul (measurable_const.add (Complex.continuous_conj.measurable.comp (H.meas l hl)))

/-- **The second moment of `Φ`**: `Φ² ` is integrable and `E ‖Φ‖² ≤ 3 (‖tm‖² + S_u + 2 γ² δ_D² ν² + 12 γ² ν⁴)`, `σ_k ≤ 1`, `ν = #s`. -/
theorem GreenCond_integral_normSq_Phi_le (H : GreenCond_RowLaw P s h σ) {hu : Ω' → ℂ} (hum : Measurable hu)
    (hui2 : Integrable (fun ω => ‖hu ω‖ ^ 2) P) {Su : ℝ} (hSu : ∫ ω, ‖hu ω‖ ^ 2 ∂P ≤ Su) {c : κ → κ → ℂ} {D : κ → ℂ} {tm : ℂ} {γ : ℝ}
    (hγ : 0 ≤ γ) (hc : ∀ k ∈ s, ∀ l ∈ s, ‖c k l‖ ≤ γ) (hσ : ∀ k ∈ s, σ k ≤ 1) :
    Integrable (fun ω => ‖GreenCond_Phi s h hu c D tm ω‖ ^ 2) P ∧
      ∫ ω, ‖GreenCond_Phi s h hu c D tm ω‖ ^ 2 ∂P ≤
        3 * (‖tm‖ ^ 2 + Su + 2 * γ ^ 2 * (∑ l ∈ s, ‖D l‖) ^ 2 * (s.card : ℝ) ^ 2 + 12 * γ ^ 2 * (s.card : ℝ) ^ 4) := by
  set ν : ℝ := (s.card : ℝ) with hν
  have hν0 : 0 ≤ ν := Nat.cast_nonneg _
  set δD := ∑ l ∈ s, ‖D l‖ with hδD
  have i2 : Integrable (fun ω => ∑ k ∈ s, ‖h k ω‖ ^ 2) P := integrable_finsetSum _ fun k hk => H.int2 hk
  have i4 : Integrable (fun ω => ∑ k ∈ s, ‖h k ω‖ ^ 4) P := integrable_finsetSum _ fun k hk => H.int4 k hk
  set g : Ω' → ℝ := fun ω => 3 * (‖tm‖ ^ 2 + ‖hu ω‖ ^ 2 + 2 * γ ^ 2 * δD ^ 2 * (ν * ∑ k ∈ s, ‖h k ω‖ ^ 2) +
      2 * γ ^ 2 * (ν ^ 3 * ∑ k ∈ s, ‖h k ω‖ ^ 4)) with hg
  have ig : Integrable g P := by
    rw [hg]
    refine Integrable.const_mul ?_ _
    exact (((integrable_const _).add hui2).add (i2.const_mul ν |>.const_mul _)).add ((i4.const_mul (ν ^ 3)).const_mul _)
  have hmeas : Measurable fun ω => ‖GreenCond_Phi s h hu c D tm ω‖ ^ 2 := ((GreenCond_measurable_Phi H hum c D tm).norm).pow_const 2
  have hdom : ∀ ω, ‖GreenCond_Phi s h hu c D tm ω‖ ^ 2 ≤ g ω := fun ω => GreenCond_normSq_Phi_le hγ hc ω
  refine ⟨ig.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun ω => ?_), ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hdom ω
  · refine (integral_mono (ig.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)) ig hdom).trans ?_
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hdom ω
    have iA : Integrable (fun ω => ‖tm‖ ^ 2 + ‖hu ω‖ ^ 2 + 2 * γ ^ 2 * δD ^ 2 * (ν * ∑ k ∈ s, ‖h k ω‖ ^ 2)) P :=
      ((integrable_const _).add hui2).add (i2.const_mul ν |>.const_mul _)
    have iB : Integrable (fun ω => 2 * γ ^ 2 * (ν ^ 3 * ∑ k ∈ s, ‖h k ω‖ ^ 4)) P := (i4.const_mul (ν ^ 3)).const_mul _
    have iC : Integrable (fun ω => ‖tm‖ ^ 2 + ‖hu ω‖ ^ 2) P := (integrable_const _).add hui2
    have iD : Integrable (fun ω => 2 * γ ^ 2 * δD ^ 2 * (ν * ∑ k ∈ s, ‖h k ω‖ ^ 2)) P := (i2.const_mul ν).const_mul _
    have hI2 : ∫ ω, ∑ k ∈ s, ‖h k ω‖ ^ 2 ∂P = ∑ k ∈ s, σ k := by
      rw [integral_finsetSum _ fun k hk => H.int2 hk]
      exact Finset.sum_congr rfl fun k hk => H.integral_sq hk
    have hI4 : ∫ ω, ∑ k ∈ s, ‖h k ω‖ ^ 4 ∂P ≤ 6 * ν := by
      rw [integral_finsetSum _ fun k hk => H.int4 k hk]
      calc ∑ k ∈ s, ∫ ω, ‖h k ω‖ ^ 4 ∂P ≤ ∑ k ∈ s, 6 * σ k ^ 2 := Finset.sum_le_sum fun k hk => H.fourth k hk
        _ ≤ ∑ _k ∈ s, 6 * 1 := Finset.sum_le_sum fun k hk => by
            have h0 := H.sigma_nonneg hk
            have := hσ k hk
            nlinarith
        _ = 6 * ν := by simp [hν]; ring
    have hsumσ : ∑ k ∈ s, σ k ≤ ν := by
      calc ∑ k ∈ s, σ k ≤ ∑ _k ∈ s, (1 : ℝ) := Finset.sum_le_sum fun k hk => hσ k hk
        _ = ν := by simp [hν]
    have key : ∫ ω, g ω ∂P = 3 * (‖tm‖ ^ 2 + ∫ ω, ‖hu ω‖ ^ 2 ∂P + 2 * γ ^ 2 * δD ^ 2 * (ν * ∑ k ∈ s, σ k) +
        2 * γ ^ 2 * (ν ^ 3 * ∫ ω, ∑ k ∈ s, ‖h k ω‖ ^ 4 ∂P)) := by
      simp only [hg]
      rw [integral_const_mul]
      congr 1
      rw [integral_add (f := fun ω => ‖tm‖ ^ 2 + ‖hu ω‖ ^ 2 + 2 * γ ^ 2 * δD ^ 2 * (ν * ∑ k ∈ s, ‖h k ω‖ ^ 2))
        (g := fun ω => 2 * γ ^ 2 * (ν ^ 3 * ∑ k ∈ s, ‖h k ω‖ ^ 4)) iA iB,
        integral_add (f := fun ω => ‖tm‖ ^ 2 + ‖hu ω‖ ^ 2) (g := fun ω => 2 * γ ^ 2 * δD ^ 2 * (ν * ∑ k ∈ s, ‖h k ω‖ ^ 2)) iC iD,
        integral_add (f := fun _ => ‖tm‖ ^ 2) (g := fun ω => ‖hu ω‖ ^ 2) (integrable_const _) hui2,
        integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, hI2]
      simp
    rw [key]
    have h4 : ν ^ 3 * ∫ ω, ∑ k ∈ s, ‖h k ω‖ ^ 4 ∂P ≤ ν ^ 3 * (6 * ν) := mul_le_mul_of_nonneg_left hI4 (by positivity)
    have hS : ν * ∑ k ∈ s, σ k ≤ ν * ν := mul_le_mul_of_nonneg_left hsumσ hν0
    have hγ2 : 0 ≤ γ ^ 2 := sq_nonneg γ
    have hδ2 : 0 ≤ δD ^ 2 := sq_nonneg δD
    have e1 : 2 * γ ^ 2 * δD ^ 2 * (ν * ∑ k ∈ s, σ k) ≤ 2 * γ ^ 2 * δD ^ 2 * (ν * ν) := mul_le_mul_of_nonneg_left hS (by positivity)
    have e2 : 2 * γ ^ 2 * (ν ^ 3 * ∫ ω, ∑ k ∈ s, ‖h k ω‖ ^ 4 ∂P) ≤ 2 * γ ^ 2 * (ν ^ 3 * (6 * ν)) := mul_le_mul_of_nonneg_left h4 (by positivity)
    nlinarith [e1, e2, hSu]

/-- **The linear form** `Λ = Σ_{k ∈ s} h_k c_k`: mean zero, `E ‖Λ‖² ≤ γ² ν²` (`‖c_k‖ ≤ γ`, `σ_k ≤ 1`, `ν = #s`). -/
theorem GreenCond_lin (H : GreenCond_RowLaw P s h σ) (c : κ → ℂ) {γ : ℝ} (hγ : 0 ≤ γ) (hc : ∀ k ∈ s, ‖c k‖ ≤ γ) (hσ : ∀ k ∈ s, σ k ≤ 1) :
    Integrable (fun ω => ∑ k ∈ s, h k ω * c k) P ∧ ∫ ω, ∑ k ∈ s, h k ω * c k ∂P = 0 ∧
      Integrable (fun ω => ‖∑ k ∈ s, h k ω * c k‖ ^ 2) P ∧
      ∫ ω, ‖∑ k ∈ s, h k ω * c k‖ ^ 2 ∂P ≤ γ ^ 2 * (s.card : ℝ) ^ 2 := by
  have ih : ∀ k ∈ s, Integrable (fun ω => h k ω * c k) P := fun k hk => (H.int1 hk).mul_const _
  have hmeas : Measurable fun ω => ∑ k ∈ s, h k ω * c k := Finset.measurable_sum _ fun k hk => (H.meas k hk).mul_const _
  set ν : ℝ := (s.card : ℝ) with hν
  have hν0 : 0 ≤ ν := Nat.cast_nonneg _
  have i2 : Integrable (fun ω => ∑ k ∈ s, ‖h k ω‖ ^ 2) P := integrable_finsetSum _ fun k hk => H.int2 hk
  have hdom : ∀ ω, ‖∑ k ∈ s, h k ω * c k‖ ^ 2 ≤ ν * γ ^ 2 * ∑ k ∈ s, ‖h k ω‖ ^ 2 := by
    intro ω
    have h1 : ‖∑ k ∈ s, h k ω * c k‖ ≤ ∑ k ∈ s, ‖h k ω‖ * γ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hc k hk) (norm_nonneg _))
    have h2 : (∑ k ∈ s, ‖h k ω‖ * γ) ^ 2 ≤ ν * ∑ k ∈ s, (‖h k ω‖ * γ) ^ 2 := sq_sum_le_card_mul_sum_sq
    have h3 : ∑ k ∈ s, (‖h k ω‖ * γ) ^ 2 = γ ^ 2 * ∑ k ∈ s, ‖h k ω‖ ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    calc ‖∑ k ∈ s, h k ω * c k‖ ^ 2 ≤ (∑ k ∈ s, ‖h k ω‖ * γ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ ν * ∑ k ∈ s, (‖h k ω‖ * γ) ^ 2 := h2
      _ = ν * γ ^ 2 * ∑ k ∈ s, ‖h k ω‖ ^ 2 := by rw [h3]; ring
  have iint : Integrable (fun ω => ‖∑ k ∈ s, h k ω * c k‖ ^ 2) P :=
    (i2.const_mul (ν * γ ^ 2)).mono' (hmeas.norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hdom ω)
  refine ⟨integrable_finsetSum _ ih, ?_, iint, ?_⟩
  · rw [integral_finsetSum _ ih]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [integral_mul_const, H.mean k hk]; simp
  · refine (integral_mono iint (i2.const_mul (ν * γ ^ 2)) hdom).trans ?_
    rw [integral_const_mul, integral_finsetSum _ fun k hk => H.int2 hk]
    have hsumσ : ∑ k ∈ s, ∫ ω, ‖h k ω‖ ^ 2 ∂P ≤ ν := by
      calc ∑ k ∈ s, ∫ ω, ‖h k ω‖ ^ 2 ∂P = ∑ k ∈ s, σ k := Finset.sum_congr rfl fun k hk => H.integral_sq hk
        _ ≤ ∑ _k ∈ s, (1 : ℝ) := Finset.sum_le_sum fun k hk => hσ k hk
        _ = ν := by simp [hν]
    calc ν * γ ^ 2 * ∑ k ∈ s, ∫ ω, ‖h k ω‖ ^ 2 ∂P ≤ ν * γ ^ 2 * ν := mul_le_mul_of_nonneg_left hsumσ (by positivity)
      _ = γ ^ 2 * ν ^ 2 := by ring

end RowModel

end RBM.BA
