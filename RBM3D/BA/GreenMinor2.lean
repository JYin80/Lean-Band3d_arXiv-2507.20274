/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GreenMinor

/-!
# The block Anderson minors: the protected good event, the polynomial families (BA-G5a, 2 of 3)

Ticket T2401 (design gate `docs/reports/T2401-prove.md`, sections (a), (a′), (G); stage 1b under
Amend 1).  Paper: `paper/tex/7_8_light_weight.tex` (`lem_GbEXP_BA`, `7_8:1916-1948`).  Everything
is deterministic, for one sample.

* R2 (S2): the protected good event from `‖G - M‖_max ≤ δ` (`GreenMinor_good_of_event`): for
  `S ⊆ R_{β,o}`, `|S| ≤ m₀`, `x, y ∈ T_{β,o} ∖ S`, `|G^{(S)}_{xy} - M_{xy}| ≤ 2δ` and
  `|G^{(S)}_{xx}| ≥ κ/2`.  Only the rows of the block `β` of offset `≠ o` are removed, so each
  removal is between two different offsets: `M_{xκ} = M_{κy} = 0` (`GreenMinor_offset_ne`,
  `GreenMinor_cross`) and one step costs `δ_j²/(|m| - δ_j)`.
* R3 (S3): the polynomial families `Y^A`, `Y^X` and the entry forms of the random re-entry
  `A_u = Y^A_u m / G_{uu}`, `𝔛_{uy} = -Y^X_{uy} m / G_{uu}`, the splits
  `A_u = Y^A_u - A_u (G_{uu} - m)/m`, and the base bounds `‖Y^A_u‖ ≤ (‖s‖ + 2 d g₀) δ'/κ`,
  `‖Y^X_{uy}‖ ≤ ((‖s‖ + 2 d g₀)(1/κ + 1) + 4 d g₀ δ'/κ) δ'` (uniform in the coupling: `g₀` enters
  only through `Σ_l ‖D_{ul}‖ = 2 d g₀`).

Every target theorem has a compiled nonempty instance in the last section.
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

/-! ## 1. R2 (S2): the protected good event from `‖G - M‖_max ≤ δ` -/

section GoodEvent
variable {d L W : ℕ} [NeZero L] [NeZero W] {G M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Zd d L → Zd d L → ℂ} {m : ℂ}
  {Gs : Finset (Vtx d L W) → Matrix (Vtx d L W) (Vtx d L W) ℂ} {κ δ : ℝ} {m₀ : ℕ}

/-- `R_{β,o} ⊆ T_{β,o}`. -/
theorem GreenMinor_R_subset_T (β : Zd d L) (o : Fin (W ^ d)) {x : Vtx d L W} (hx : x ∈ GreenMinor_R β o) :
    x ∈ GreenMinor_T β o := Or.inr hx.1

/-- The recursion of `(4.9)` on the protected levels: `|G^{(S)}_{xy} - M_{xy}| ≤ δ + 8 |S| δ²/κ`, `|S| ≤ m₀`. -/
theorem GreenMinor_good_aux (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hMd : ∀ a, Mb a a = m)
    (hκ : 0 < κ) (hm : κ ≤ ‖m‖) (hδ0 : 0 ≤ δ) (hMδ : 8 * (m₀ : ℝ) * δ ≤ κ) (hδ4 : 4 * δ ≤ κ)
    (hT : GreenMinor_Tower G Gs) (hG : ∀ x y, ‖G x y - M x y‖ ≤ δ) (β : Zd d L) (o : Fin (W ^ d)) :
    ∀ j : ℕ, j ≤ m₀ → ∀ S : Finset (Vtx d L W), ↑S ⊆ GreenMinor_R β o → S.card = j →
      ∀ x y, x ∈ GreenMinor_T β o → y ∈ GreenMinor_T β o → x ∉ S → y ∉ S →
        ‖Gs S x y - M x y‖ ≤ δ + 8 * (j : ℝ) * δ ^ 2 / κ := by
  intro j
  induction j with
  | zero =>
      intro _ S _ hS x y _ _ _ _
      have hS0 : S = ∅ := Finset.card_eq_zero.1 hS
      subst hS0
      rw [hT.base]
      simpa using hG x y
  | succ j ih =>
      intro hj S hSR hS x y hx hy hxS hyS
      have hjm : j ≤ m₀ := by omega
      obtain ⟨κ', hκ'⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
      set S' := S.erase κ' with hS'
      have hSS : insert κ' S' = S := Finset.insert_erase hκ'
      have hκS' : κ' ∉ S' := Finset.notMem_erase κ' S
      have hS'R : ↑S' ⊆ GreenMinor_R β o := fun a ha => hSR (Finset.mem_of_mem_erase ha)
      have hS'c : S'.card = j := by rw [hS', Finset.card_erase_of_mem hκ', hS]; rfl
      have hκR : κ' ∈ GreenMinor_R β o := hSR hκ'
      have hκT : κ' ∈ GreenMinor_T β o := GreenMinor_R_subset_T β o hκR
      have hxS' : x ∉ S' := fun h => hxS (Finset.mem_of_mem_erase h)
      have hyS' : y ∉ S' := fun h => hyS (Finset.mem_of_mem_erase h)
      have hxκ : x ≠ κ' := fun h => hxS (h ▸ hκ')
      have hyκ : y ≠ κ' := fun h => hyS (h ▸ hκ')
      -- the bound at level `S'`
      have hb := ih hjm S' hS'R hS'c
      set δj : ℝ := δ + 8 * (j : ℝ) * δ ^ 2 / κ with hδj
      have hjδ : 8 * (j : ℝ) * δ ≤ κ := by
        have : (j : ℝ) ≤ m₀ := by exact_mod_cast hjm
        nlinarith
      have hδj2 : δj ≤ 2 * δ := by
        rw [hδj]
        have : 8 * (j : ℝ) * δ ^ 2 / κ ≤ δ := by
          rw [div_le_iff₀ hκ]
          nlinarith [sq_nonneg δ]
        linarith
      have hδj0 : 0 ≤ δj := by
        rw [hδj]; positivity
      -- the three entries of the removed row
      have hxκ2 : x.2 ≠ κ'.2 := GreenMinor_offset_ne hκR hx hxκ
      have hyκ2 : y.2 ≠ κ'.2 := GreenMinor_offset_ne hκR hy hyκ
      have ha : ‖Gs S' x κ'‖ ≤ 2 * δ := by
        have := hb x κ' hx hκT hxS' hκS'
        rw [GreenMinor_cross hM hxκ2, sub_zero] at this
        linarith
      have hbb : ‖Gs S' κ' y‖ ≤ 2 * δ := by
        have := hb κ' y hκT hy hκS' hyS'
        rw [GreenMinor_cross hM (Ne.symm hyκ2), sub_zero] at this
        linarith
      have hc : κ / 2 ≤ ‖Gs S' κ' κ'‖ := by
        have h1 := hb κ' κ' hκT hκT hκS' hκS'
        have h2 : M κ' κ' = m := by simp [hM, hMd]
        rw [h2] at h1
        have h3 : ‖m‖ - ‖Gs S' κ' κ'‖ ≤ ‖Gs S' κ' κ' - m‖ := by
          rw [norm_sub_rev]; exact norm_sub_norm_le _ _
        linarith
      have hfrac : ‖Gs S' x κ' * Gs S' κ' y / Gs S' κ' κ'‖ ≤ 8 * δ ^ 2 / κ := by
        rw [norm_div, norm_mul, div_le_iff₀ (lt_of_lt_of_le (by positivity) hc)]
        calc ‖Gs S' x κ'‖ * ‖Gs S' κ' y‖ ≤ (2 * δ) * (2 * δ) :=
              mul_le_mul ha hbb (norm_nonneg _) (by positivity)
          _ = 8 * δ ^ 2 / κ * (κ / 2) := by field_simp; ring
          _ ≤ 8 * δ ^ 2 / κ * ‖Gs S' κ' κ'‖ := mul_le_mul_of_nonneg_left hc (by positivity)
      have hstep : Gs S x y = Gs S' x y - Gs S' x κ' * Gs S' κ' y / Gs S' κ' κ' := by
        rw [← hSS, hT.step S' κ' hκS' x y, greenMinor]
      have h0 := hb x y hx hy hxS' hyS'
      rw [hstep]
      calc ‖Gs S' x y - Gs S' x κ' * Gs S' κ' y / Gs S' κ' κ' - M x y‖
          = ‖(Gs S' x y - M x y) - Gs S' x κ' * Gs S' κ' y / Gs S' κ' κ'‖ := by congr 1; ring
        _ ≤ ‖Gs S' x y - M x y‖ + ‖Gs S' x κ' * Gs S' κ' y / Gs S' κ' κ'‖ := norm_sub_le _ _
        _ ≤ δj + 8 * δ ^ 2 / κ := add_le_add h0 hfrac
        _ = δ + 8 * ((j + 1 : ℕ) : ℝ) * δ ^ 2 / κ := by rw [hδj]; push_cast; ring

/-- **S2** (`GreenMinor_good_of_event`): from the event `‖G - M‖_max ≤ δ` with `4δ ≤ κ ≤ |m|`, `8 m₀ δ ≤ κ`, the tower of minors
satisfies the protected good event `GreenMinor_good`: for `S ⊆ R_{β,o}`, `|S| ≤ m₀`, `x, y ∈ T_{β,o} ∖ S`,
`|G^{(S)}_{xy} - M_{xy}| ≤ 2δ` and `|G^{(S)}_{xx}| ≥ κ/2` (the twin of `minorGoodLe_of_goodEvent` with `|m| = 1` replaced by `|m| ≥ κ`). -/
theorem GreenMinor_good_of_event (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hMd : ∀ a, Mb a a = m)
    (hκ : 0 < κ) (hm : κ ≤ ‖m‖) (hδ0 : 0 ≤ δ) (hδ4 : 4 * δ ≤ κ) (hMδ : 8 * (m₀ : ℝ) * δ ≤ κ)
    (hT : GreenMinor_Tower G Gs) (hG : ∀ x y, ‖G x y - M x y‖ ≤ δ) (β : Zd d L) (o : Fin (W ^ d)) :
    GreenMinor_good Gs M κ δ m₀ β o := by
  intro S hSR hS x y hx hy hxS hyS
  have hb := GreenMinor_good_aux hM hMd hκ hm hδ0 hMδ hδ4 hT hG β o S.card hS S hSR rfl x y hx hy hxS hyS
  have hjδ : 8 * (S.card : ℝ) * δ ≤ κ := by
    have : (S.card : ℝ) ≤ m₀ := by exact_mod_cast hS
    nlinarith
  have hle : δ + 8 * (S.card : ℝ) * δ ^ 2 / κ ≤ 2 * δ := by
    have : 8 * (S.card : ℝ) * δ ^ 2 / κ ≤ δ := by
      rw [div_le_iff₀ hκ]
      nlinarith [sq_nonneg δ]
    linarith
  refine ⟨hb.trans hle, ?_⟩
  have h1 := (GreenMinor_good_aux hM hMd hκ hm hδ0 hMδ hδ4 hT hG β o S.card hS S hSR rfl x x hx hx hxS hxS).trans hle
  have h2 : M x x = m := by simp [hM, hMd]
  rw [h2] at h1
  have h3 : ‖m‖ - ‖Gs S x x‖ ≤ ‖Gs S x x - m‖ := by
    rw [norm_sub_rev]; exact norm_sub_norm_le _ _
  linarith

end GoodEvent

/-! ## 2. R3 (S3): the entry forms of the random re-entry, the splits and the base bounds -/

section Families
variable {d L W : ℕ} [NeZero L] [NeZero W] {G X D M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Zd d L → Zd d L → ℂ}
  {t g₀ : ℝ} {m s z : ℂ}

/-- `(D + X - z) G = 1` read at the entry `(u, y)`: `Σ_v X_{uv} G_{vy} = 1_{u=y} + z G_{uy} - Σ_v D_{uv} G_{vy}`. -/
theorem GreenMinor_row_XG (hRG : (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1) (u y : Vtx d L W) :
    ∑ v, X u v * G v y = (if u = y then 1 else 0) + z * G u y - ∑ v, D u v * G v y := by
  have h := congrFun (congrFun hRG u) y
  simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, sub_mul, add_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, smul_eq_mul, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
  linear_combination h

/-- `M (D - s) = 1` read at the entry `(u, y)`: `Σ_l D_{ul} M_{ly} = 1_{u=y} + s M_{uy}`. -/
theorem GreenMinor_row_DM (hMR : M * (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1) (u y : Vtx d L W) :
    ∑ l, D u l * M l y = (if u = y then 1 else 0) + s * M u y := by
  have hMR' : (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * M = 1 := mul_eq_one_comm.1 hMR
  have h := congrFun (congrFun hMR' u) y
  simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.sub_apply, Matrix.smul_apply, sub_mul, Finset.sum_sub_distrib,
    smul_eq_mul, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
  linear_combination h

/-- `A_u = t m + X_{uu} - Q_u`, entry form: `A_u G_{uu} = 1 + s G_{uu} - Σ_l D_{ul} G_{lu}`. -/
theorem GreenMinor_Arow_mul (hGR : G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1)
    (hRG : (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1) (hz : z = s - (t : ℂ) * m)
    {u : Vtx d L W} (hG0 : G u u ≠ 0) :
    GreenCore_Arow G X D t m u * G u u = 1 + s * G u u - ∑ l, D u l * G l u := by
  have hE := GreenCore_E1 (H := D + X) (X := X) hGR u u hG0
  have h0 : ∑ v ∈ univ.erase u, X u v * greenMinor G u v u = 0 :=
    Finset.sum_eq_zero fun v _ => by rw [GreenCore_minor_right hG0]; ring
  rw [h0, add_zero] at hE
  have hR := GreenMinor_row_XG (G := G) (X := X) (D := D) hRG u u
  have hu : (if u = u then (1 : ℂ) else 0) = 1 := by simp
  rw [hu] at hR
  unfold GreenCore_Arow
  rw [hz] at hR
  linear_combination hR - hE

end Families

section Entries
variable {d L W : ℕ} [NeZero L] [NeZero W] {G X D M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Zd d L → Zd d L → ℂ}
  {t g₀ : ℝ} {m s z : ℂ}

/-- **S3** (`GreenMinor_Arow_eq`): `A_u = Y^A_u m / G_{uu}`, i.e. `A_u G_{uu} = s Δ_{uu} - Σ_l D_{ul} Δ_{lu}` (with `m ≠ 0`:
the identity is false at `m = 0` for the Lean value `x/0 = 0`). -/
theorem GreenMinor_Arow_eq (hGR : G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1)
    (hRG : (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1)
    (hMR : M * (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1) (hz : z = s - (t : ℂ) * m)
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hMd : ∀ a, Mb a a = m)
    (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0) (hm : m ≠ 0)
    {u : Vtx d L W} (hG0 : G u u ≠ 0) :
    GreenCore_Arow G X D t m u = GreenMinor_YA G M D s m u * m / G u u := by
  have hA := GreenMinor_Arow_mul hGR hRG hz hG0
  have hDM := GreenMinor_row_DM hMR u u
  have hMuu : M u u = m := by simp [hM, hMd]
  have hu : (if u = u then (1 : ℂ) else 0) = 1 := by simp
  rw [hu, hMuu] at hDM
  have hYAm : GreenMinor_YA G M D s m u * m = s * (G u u - M u u) - ∑ l, D u l * (G l u - M l u) := by
    unfold GreenMinor_YA; field_simp
  have hsplit : ∑ l, D u l * (G l u - M l u) = ∑ l, D u l * G l u - ∑ l, D u l * M l u := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [eq_div_iff hG0, hYAm, hsplit, hA, hMuu]
  linear_combination (-1 : ℂ) * hDM

/-- **S3** (`GreenMinor_Xrow_eq`): `𝔛_{uy} = -Y^X_{uy} m / G_{uu}` for `y ≠ u`. -/
theorem GreenMinor_Xrow_eq (hGR : G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1)
    (hRG : (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1)
    (hMR : M * (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1) (hz : z = s - (t : ℂ) * m)
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hMd : ∀ a, Mb a a = m)
    (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0) (hm : m ≠ 0)
    {u y : Vtx d L W} (hG0 : G u u ≠ 0) (hyu : y ≠ u) :
    GreenCore_Xrow G X u y = -(GreenMinor_YX G M D s m u y * m / G u u) := by
  have hE := GreenCore_E1 (H := D + X) (X := X) hGR u y hG0
  have hA := GreenMinor_Arow_mul hGR hRG hz hG0
  have hR1 := GreenMinor_row_XG (G := G) (X := X) (D := D) hRG u y
  have hR2 := GreenMinor_row_DM hMR u y
  have hR2u := GreenMinor_row_DM hMR u u
  have hMuu : M u u = m := by simp [hM, hMd]
  have huy : (if u = y then (1 : ℂ) else 0) = 0 := by simp [Ne.symm hyu]
  have hu : (if u = u then (1 : ℂ) else 0) = 1 := by simp
  rw [huy] at hR1 hR2
  rw [hu, hMuu] at hR2u
  have hYXm : GreenMinor_YX G M D s m u y * m =
      M u y * (s * (G u u - M u u) - ∑ l, D u l * (G l u - M l u)) + m * (∑ l, D u l * (G l y - M l y) - s * (G u y - M u y))
        + ((G u u - M u u) * ∑ l, D u l * (G l y - M l y) - (G u y - M u y) * ∑ l, D u l * (G l u - M l u)) := by
    unfold GreenMinor_YX; field_simp
  have hsp : ∑ l, D u l * (G l y - M l y) = ∑ l, D u l * G l y - ∑ l, D u l * M l y := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  have hsq : ∑ l, D u l * (G l u - M l u) = ∑ l, D u l * G l u - ∑ l, D u l * M l u := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  have key : GreenCore_Xrow G X u y * G u u = -(GreenMinor_YX G M D s m u y * m) := by
    rw [hYXm, hsp, hsq, hMuu]
    unfold GreenCore_Arow at hA
    unfold GreenCore_Xrow
    rw [hz] at hR1
    linear_combination (-(G u u)) * hE + (G u u) * hR1 - (G u y) * hA - (G u u) * hR2 + (G u y) * hR2u
  have h2 : GreenCore_Xrow G X u y = -(GreenMinor_YX G M D s m u y * m) / G u u := by
    rw [eq_div_iff hG0]; exact key
  rw [h2, neg_div]

/-- **S3** (`GreenMinor_split_A`): `A_u = Y^A_u - A_u (G_{uu} - m)/m`. -/
theorem GreenMinor_split_A (hGR : G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1)
    (hRG : (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1)
    (hMR : M * (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1) (hz : z = s - (t : ℂ) * m)
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hMd : ∀ a, Mb a a = m)
    (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0) (hm : m ≠ 0)
    {u : Vtx d L W} (hG0 : G u u ≠ 0) :
    GreenCore_Arow G X D t m u = GreenMinor_YA G M D s m u - GreenCore_Arow G X D t m u * (G u u - m) / m := by
  have h := (eq_div_iff hG0).1 (GreenMinor_Arow_eq hGR hRG hMR hz hM hMd hD hm hG0)
  field_simp
  linear_combination (1 : ℂ) * h

/-- **S3** (`GreenMinor_split_X`): `𝔛_{uy} = -Y^X_{uy} - 𝔛_{uy} (G_{uu} - m)/m`, `y ≠ u`. -/
theorem GreenMinor_split_X (hGR : G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1)
    (hRG : (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1)
    (hMR : M * (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1) (hz : z = s - (t : ℂ) * m)
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hMd : ∀ a, Mb a a = m)
    (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0) (hm : m ≠ 0)
    {u y : Vtx d L W} (hG0 : G u u ≠ 0) (hyu : y ≠ u) :
    GreenCore_Xrow G X u y = -GreenMinor_YX G M D s m u y - GreenCore_Xrow G X u y * (G u u - m) / m := by
  have h0 := GreenMinor_Xrow_eq hGR hRG hMR hz hM hMd hD hm hG0 hyu
  have h : GreenCore_Xrow G X u y * G u u = -(GreenMinor_YX G M D s m u y * m) := by
    rw [h0, neg_mul, div_mul_cancel₀ _ hG0]
  field_simp
  linear_combination h

end Entries

section BaseBounds
variable {d L W : ℕ} [NeZero L] [NeZero W] {G M D : Matrix (Vtx d L W) (Vtx d L W) ℂ} {s m : ℂ} {κ δ' g₀ : ℝ}

/-- `‖Σ_l D_{ul} Δ_{ly}‖ ≤ 2 d g₀ δ'`: the hopping row has `2d` entries `g₀` (`GreenCore_Drow`), whatever `g₀ ≥ 0`. -/
theorem GreenMinor_sum_le (hL : 3 ≤ L) (hg : 0 ≤ g₀)
    (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0)
    (hΔ : ∀ a b, ‖G a b - M a b‖ ≤ δ') (u y : Vtx d L W) :
    ‖∑ l, D u l * (G l y - M l y)‖ ≤ 2 * d * g₀ * δ' := by
  calc ‖∑ l, D u l * (G l y - M l y)‖ ≤ ∑ l, ‖D u l * (G l y - M l y)‖ := norm_sum_le _ _
    _ ≤ ∑ l, ‖D u l‖ * δ' := Finset.sum_le_sum fun l _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hΔ l y) (norm_nonneg _)
    _ = 2 * d * g₀ * δ' := by rw [← Finset.sum_mul, GreenCore_Drow hg hL hD u]

/-- **S3** (`GreenMinor_YA_le`): `‖Y^A_u‖ ≤ (‖s‖ + 2 d g₀) δ' / κ`. -/
theorem GreenMinor_YA_le (hL : 3 ≤ L) (hg : 0 ≤ g₀)
    (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0)
    (hΔ : ∀ a b, ‖G a b - M a b‖ ≤ δ') (hκ : 0 < κ) (hm : κ ≤ ‖m‖) (u : Vtx d L W) :
    ‖GreenMinor_YA G M D s m u‖ ≤ (‖s‖ + 2 * d * g₀) / κ * δ' := by
  have hδ0 : 0 ≤ δ' := le_trans (norm_nonneg _) (hΔ u u)
  have hq := GreenMinor_sum_le hL hg hD hΔ u u
  have hs : ‖s * (G u u - M u u) - ∑ l, D u l * (G l u - M l u)‖ ≤ ‖s‖ * δ' + 2 * d * g₀ * δ' := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ hq)
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hΔ u u) (norm_nonneg _)
  have hnn : 0 ≤ ‖s‖ * δ' + 2 * d * g₀ * δ' := le_trans (norm_nonneg _) hs
  unfold GreenMinor_YA
  rw [norm_div]
  calc ‖s * (G u u - M u u) - ∑ l, D u l * (G l u - M l u)‖ / ‖m‖
      ≤ (‖s‖ * δ' + 2 * d * g₀ * δ') / ‖m‖ := div_le_div_of_nonneg_right hs (norm_nonneg _)
    _ ≤ (‖s‖ * δ' + 2 * d * g₀ * δ') / κ := div_le_div_of_nonneg_left hnn hκ hm
    _ = (‖s‖ + 2 * d * g₀) / κ * δ' := by ring

/-- **S3** (`GreenMinor_YX_le`): `‖Y^X_{uy}‖ ≤ ((‖s‖ + 2 d g₀)(1/κ + 1) + 4 d g₀ δ'/κ) δ'` when `‖M_{uy}‖ ≤ 1`. -/
theorem GreenMinor_YX_le (hL : 3 ≤ L) (hg : 0 ≤ g₀)
    (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0)
    (hΔ : ∀ a b, ‖G a b - M a b‖ ≤ δ') (hκ : 0 < κ) (hm : κ ≤ ‖m‖) (u y : Vtx d L W) (hMuy : ‖M u y‖ ≤ 1) :
    ‖GreenMinor_YX G M D s m u y‖ ≤ ((‖s‖ + 2 * d * g₀) * (1 / κ + 1) + 4 * d * g₀ * δ' / κ) * δ' := by
  have hδ0 : 0 ≤ δ' := le_trans (norm_nonneg _) (hΔ u u)
  have hdg : 0 ≤ 2 * (d : ℝ) * g₀ := by positivity
  have hq := GreenMinor_sum_le hL hg hD hΔ u u
  have hp := GreenMinor_sum_le hL hg hD hΔ u y
  have hs : ‖s * (G u u - M u u) - ∑ l, D u l * (G l u - M l u)‖ ≤ ‖s‖ * δ' + 2 * d * g₀ * δ' := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ hq)
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hΔ u u) (norm_nonneg _)
  have hnn : 0 ≤ ‖s‖ * δ' + 2 * d * g₀ * δ' := le_trans (norm_nonneg _) hs
  have hκm : (1 : ℝ) / ‖m‖ ≤ 1 / κ := one_div_le_one_div_of_le hκ hm
  have hm0 : 0 < ‖m‖ := lt_of_lt_of_le hκ hm
  -- the three terms
  have t1 : ‖M u y * (s * (G u u - M u u) - ∑ l, D u l * (G l u - M l u)) / m‖ ≤ (‖s‖ + 2 * d * g₀) * δ' / κ := by
    rw [norm_div, norm_mul]
    calc ‖M u y‖ * ‖s * (G u u - M u u) - ∑ l, D u l * (G l u - M l u)‖ / ‖m‖
        ≤ 1 * (‖s‖ * δ' + 2 * d * g₀ * δ') / ‖m‖ := by
          gcongr
      _ ≤ 1 * (‖s‖ * δ' + 2 * d * g₀ * δ') / κ := div_le_div_of_nonneg_left (by positivity) hκ hm
      _ = (‖s‖ + 2 * d * g₀) * δ' / κ := by ring
  have t2 : ‖∑ l, D u l * (G l y - M l y) - s * (G u y - M u y)‖ ≤ (‖s‖ + 2 * d * g₀) * δ' := by
    refine (norm_sub_le _ _).trans ?_
    have : ‖s * (G u y - M u y)‖ ≤ ‖s‖ * δ' := by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hΔ u y) (norm_nonneg _)
    nlinarith
  have t3 : ‖((G u u - M u u) * ∑ l, D u l * (G l y - M l y) - (G u y - M u y) * ∑ l, D u l * (G l u - M l u)) / m‖ ≤
      4 * d * g₀ * δ' ^ 2 / κ := by
    rw [norm_div]
    have h1 : ‖(G u u - M u u) * ∑ l, D u l * (G l y - M l y)‖ ≤ δ' * (2 * d * g₀ * δ') := by
      rw [norm_mul]; exact mul_le_mul (hΔ u u) hp (norm_nonneg _) hδ0
    have h2 : ‖(G u y - M u y) * ∑ l, D u l * (G l u - M l u)‖ ≤ δ' * (2 * d * g₀ * δ') := by
      rw [norm_mul]; exact mul_le_mul (hΔ u y) hq (norm_nonneg _) hδ0
    have h3 := (norm_sub_le _ _).trans (add_le_add h1 h2)
    calc ‖(G u u - M u u) * ∑ l, D u l * (G l y - M l y) - (G u y - M u y) * ∑ l, D u l * (G l u - M l u)‖ / ‖m‖
        ≤ (δ' * (2 * d * g₀ * δ') + δ' * (2 * d * g₀ * δ')) / ‖m‖ := div_le_div_of_nonneg_right h3 (norm_nonneg _)
      _ ≤ (δ' * (2 * d * g₀ * δ') + δ' * (2 * d * g₀ * δ')) / κ :=
          div_le_div_of_nonneg_left (by positivity) hκ hm
      _ = 4 * d * g₀ * δ' ^ 2 / κ := by ring
  unfold GreenMinor_YX
  calc ‖M u y * (s * (G u u - M u u) - ∑ l, D u l * (G l u - M l u)) / m +
        (∑ l, D u l * (G l y - M l y) - s * (G u y - M u y)) +
        ((G u u - M u u) * ∑ l, D u l * (G l y - M l y) - (G u y - M u y) * ∑ l, D u l * (G l u - M l u)) / m‖
      ≤ ‖M u y * (s * (G u u - M u u) - ∑ l, D u l * (G l u - M l u)) / m‖ +
        ‖∑ l, D u l * (G l y - M l y) - s * (G u y - M u y)‖ +
        ‖((G u u - M u u) * ∑ l, D u l * (G l y - M l y) - (G u y - M u y) * ∑ l, D u l * (G l u - M l u)) / m‖ :=
        (norm_add₃_le)
    _ ≤ (‖s‖ + 2 * d * g₀) * δ' / κ + (‖s‖ + 2 * d * g₀) * δ' + 4 * d * g₀ * δ' ^ 2 / κ := by
        gcongr
    _ = ((‖s‖ + 2 * d * g₀) * (1 / κ + 1) + 4 * d * g₀ * δ' / κ) * δ' := by ring

end BaseBounds

/-! ## 3. Nonempty instances

The hand-made datum of file 1 (`GreenMinorInst`: `d = 3`, `L = 3`, `W = 2`, `m = i`, `Δ = ε (E_{pq} + E_{qp})`, `ε = 1/100`) with the
explicit tower `hGs` of `G = M + Δ` (removing `q` turns `G_{pp}` into `m - ε²/m`): S2 (`κ = 1/2`, `δ = 1/100`, `m₀ = 3`) and the base
bounds of S3.  The BA carrier (`sz0` at `n = 0`: `L = 4`, `W = 32`; the flow `flow_sz0`, `κ = 1/2`, `t = 1/2`, every sample `ω`): the
four identities of S3. -/

namespace GreenMinorInst

theorem hpq : hp ≠ hq := by decide
theorem hqp : hq ≠ hp := by decide
theorem hm0 : hm ≠ 0 := Complex.I_ne_zero

/-- `G^{(q)}_{pp} = G^{(p)}_{qq} = m - ε²/m` -/
def hc : ℂ := hm - hε ^ 2 / hm

theorem hc_ne : hc ≠ 0 := by
  intro h0
  have := congrArg Complex.im h0
  simp [hc, hm, hε] at this
  norm_num at this

theorem hMe : ∀ x y, hM x y = if x = y then hm else 0 := by
  intro x y
  simp only [hM, hMb, Matrix.of_apply, Prod.ext_iff]
  split_ifs <;> simp_all

theorem hΔb : ∀ a b, ‖hG a b - hM a b‖ ≤ 1 / 100 := by
  intro a b
  simp only [hG, Matrix.add_apply, add_sub_cancel_left, hΔ, Matrix.of_apply]
  split_ifs
  · simp [hε]
  · simp

/-- the explicit tower of `G`: the levels `S ⊆ {p, q}` (padded by `0`), `G^{(q)}_{pp} = G^{(p)}_{qq} = hc`, all other entries of `G` unchanged -/
def hgS (S : Finset HV) (x y : HV) : ℂ :=
  if x ∈ S ∨ y ∈ S then 0
  else if x = y then (if (x = hp ∧ hq ∈ S) ∨ (x = hq ∧ hp ∈ S) then hc else hm)
  else if (x = hp ∧ y = hq) ∨ (x = hq ∧ y = hp) then hε else 0

def hGs (S : Finset HV) : Matrix HV HV ℂ := Matrix.of (hgS S)

theorem hTower : GreenMinor_Tower hG hGs := by
  refine ⟨?_, ?_⟩
  · ext x y
    simp only [hGs, hgS, hG, hΔ, Matrix.add_apply, hMe, Matrix.of_apply, Finset.notMem_empty, or_self, ite_false, and_false,
      false_and, or_false]
    by_cases hxy : x = y
    · subst hxy
      have : ¬ ((x = hp ∧ x = hq) ∨ (x = hq ∧ x = hp)) := by
        rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact hpq (h1.symm.trans h2)
        · exact hqp (h1.symm.trans h2)
      simp [this]
    · simp [hxy]
  · intro S κ hκ x y
    change hgS (insert κ S) x y = hgS S x y - hgS S x κ * hgS S κ y / hgS S κ κ
    have hgκκ : hgS S κ κ ≠ 0 := by
      simp only [hgS, hκ, or_self, ite_false, ite_true]
      split_ifs
      · exact hc_ne
      · exact hm0
    by_cases hxS : x ∈ S
    · have e1 : hgS (insert κ S) x y = 0 := by simp [hgS, hxS]
      have e2 : hgS S x y = 0 := by simp [hgS, hxS]
      have e3 : hgS S x κ = 0 := by simp [hgS, hxS]
      rw [e1, e2, e3]; simp
    by_cases hyS : y ∈ S
    · have e1 : hgS (insert κ S) x y = 0 := by simp [hgS, hyS]
      have e2 : hgS S x y = 0 := by simp [hgS, hyS]
      have e3 : hgS S κ y = 0 := by simp [hgS, hyS]
      rw [e1, e2, e3]; simp
    by_cases hxκ : x = κ
    · subst hxκ
      have e1 : hgS (insert x S) x y = 0 := by simp [hgS]
      rw [e1, mul_div_cancel_left₀ _ hgκκ, sub_self]
    by_cases hyκ : y = κ
    · subst hyκ
      have e1 : hgS (insert y S) x y = 0 := by simp [hgS]
      rw [e1, mul_div_assoc, div_self hgκκ, mul_one, sub_self]
    have hκx : κ ≠ x := fun h => hxκ h.symm
    have hκy : κ ≠ y := fun h => hyκ h.symm
    simp only [hgS, hxS, hyS, hκ, hxκ, hyκ, hκx, hκy, Finset.mem_insert, or_self, ite_false, or_false, false_or]
    by_cases hκp : κ = hp
    · subst hκp
      by_cases hxq : x = hq
      · subst hxq
        by_cases hyq : y = hq
        · subst hyq
          simp [hpq, hqp, hxS, hκ]
          rw [hc]; ring
        · simp [hpq, hqp, hxS, hyq, Ne.symm hyq]
      · simp [hpq, hqp, hxq, Ne.symm hxq]
    by_cases hκq : κ = hq
    · subst hκq
      by_cases hxp : x = hp
      · subst hxp
        by_cases hyp : y = hp
        · subst hyp
          simp [hpq, hqp, hxS, hκ]
          rw [hc]; ring
        · simp [hpq, hqp, hxS, hyp, Ne.symm hyp]
      · simp [hpq, hqp, hxp, Ne.symm hxp]
    simp [hpq, hqp, hκp, hκq, Ne.symm hκp, Ne.symm hκq]

end GreenMinorInst

/-! ### The real resolvent: `H = ε J_C`, `z = i`

`H = ε J_C` with `J_C = 1_C 1_Cᵀ` on the cluster `C = {p, q, y}` (`p = (0, 0)`, `q = (0, 1)` a protected row of `R_{0,0}`, `y = (e_0, 0)` of
offset `0` in another block), `ε = 1/100`.  By Sherman-Morrison `G = (H - i)⁻¹ = i I + c J_C`, `c = ε/(1 + 3 i ε)`, so `M = i I` (the resolvent of `0`),
`Δ = c J_C ≠ 0` and `‖Δ‖_max = |c| ≤ ε`.  Here the minors are the real ones (`GreenMinor_Gs`, R1). -/

namespace GreenMinorInst
theorem hpy : hp ≠ hy := by decide
theorem hqy : hq ≠ hy := by decide

/-- the cluster `C = {p, q, y}` -/
def hC : Finset HV := {hp, hq, hy}

theorem hC_card : hC.card = 3 := by
  have h1 : hq ∉ ({hy} : Finset HV) := by simpa using hqy
  have h2 : hp ∉ ({hq, hy} : Finset HV) := by simp [hpq, hpy]
  rw [hC, Finset.card_insert_of_notMem h2, Finset.card_insert_of_notMem h1]
  rfl

/-- `J_C = 1_C 1_Cᵀ` -/
def hJ : Matrix HV HV ℂ := Matrix.of fun x y => if x ∈ hC ∧ y ∈ hC then 1 else 0

theorem hJJ : hJ * hJ = (3 : ℂ) • hJ := by
  ext x y
  simp only [Matrix.mul_apply, hJ, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hx : x ∈ hC
  · by_cases hy' : y ∈ hC
    · simp [hx, hy', Finset.sum_boole, Finset.filter_mem_eq_inter, hC_card]
    · simp [hx, hy']
  · simp [hx]

/-- `H = ε J_C` -/
def hH : Matrix HV HV ℂ := hε • hJ

/-- `c = ε/(1 + 3 i ε)` -/
def hcc : ℂ := hε / (1 + 3 * Complex.I * hε)

/-- `G = i I + c J_C` -/
def hGex : Matrix HV HV ℂ := Complex.I • (1 : Matrix HV HV ℂ) + hcc • hJ

theorem hH_herm : hH.IsHermitian := by
  ext x y
  have hstar : star hε = hε := by simp [hε]
  by_cases h : x ∈ hC ∧ y ∈ hC
  · have h' : y ∈ hC ∧ x ∈ hC := ⟨h.2, h.1⟩
    simp [hH, hJ, Matrix.conjTranspose_apply, h, h', hstar]
  · have h' : ¬ (y ∈ hC ∧ x ∈ hC) := fun hh => h ⟨hh.2, hh.1⟩
    simp [hH, hJ, Matrix.conjTranspose_apply, h, h']

theorem hden : (1 + 3 * Complex.I * hε : ℂ) ≠ 0 := by
  intro h0
  have := congrArg Complex.re h0
  simp [hε] at this

theorem hcc_eq : Complex.I * hε + 3 * hcc * hε - hcc * Complex.I = 0 := by
  have hc : hcc * (1 + 3 * Complex.I * hε) = hε := by
    unfold hcc; exact div_mul_cancel₀ _ hden
  linear_combination (-Complex.I) * hc + (3 * hε * hcc) * Complex.I_sq

theorem hGex_mul : hGex * (hH - Complex.I • (1 : Matrix HV HV ℂ)) = 1 := by
  have h : hGex * (hH - Complex.I • (1 : Matrix HV HV ℂ)) = 1 + (Complex.I * hε + 3 * hcc * hε - hcc * Complex.I) • hJ := by
    unfold hGex hH
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hJJ,
      smul_smul, smul_sub, smul_add]
    have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
    rw [hII]
    module
  rw [h, hcc_eq, zero_smul, add_zero]

theorem green_hH : green hH Complex.I = hGex := by
  unfold green
  exact Matrix.inv_eq_left_inv hGex_mul

theorem hGex_sub (x y : HV) : hGex x y - hM x y = if x ∈ hC ∧ y ∈ hC then hcc else 0 := by
  rw [hMe]
  simp only [hGex, hJ, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, smul_eq_mul]
  split_ifs <;> simp [hm]

theorem hcc_norm : ‖hcc‖ ≤ 1 / 100 := by
  unfold hcc
  rw [norm_div]
  have h1 : (1 : ℝ) ≤ ‖(1 + 3 * Complex.I * hε : ℂ)‖ := by
    have := Complex.abs_re_le_norm (1 + 3 * Complex.I * hε : ℂ)
    simpa [hε] using this
  have h2 : ‖hε‖ = 1 / 100 := by simp [hε]
  rw [h2]
  calc (1 / 100 : ℝ) / ‖(1 + 3 * Complex.I * hε : ℂ)‖ ≤ 1 / 100 / 1 := by
        gcongr
    _ = 1 / 100 := by norm_num

theorem hcc_ne : hcc ≠ 0 := by
  unfold hcc
  exact div_ne_zero (by simp [hε]) hden

theorem hGΔ (x y : HV) : ‖green hH Complex.I x y - hM x y‖ ≤ 1 / 100 := by
  rw [green_hH, hGex_sub]
  split_ifs
  · exact hcc_norm
  · simp

end GreenMinorInst

section RealResolvent
open GreenMinorInst

-- R1, S2 and the base bounds of S3 on the real resolvent `G = (H - i)⁻¹`: the principal-submatrix resolvents of `H` form the tower
-- (`GreenMinor_tower`), the good event holds at `κ = 1/2`, `δ = 1/100`, `m₀ = 3` (S2), `Δ_{py} = c ≠ 0`, and the bounds of S3 hold at `d = 3`,
-- `g₀ = 1/10`, `s = m = i`, `δ' = 1/100` (`Y^A_p` and `Y^X_{py}` involve `Δ_{pp} = c`, `D_{py} Δ_{yp} = g₀ c`, `Δ_{py} = c`: nonzero)
example :
    GreenMinor_Tower (green hH Complex.I) (GreenMinor_Gs hH Complex.I) ∧
    GreenMinor_good (GreenMinor_Gs hH Complex.I) hM (1 / 2) (1 / 100) 3 0 0 ∧
    green hH Complex.I hp hy - hM hp hy ≠ 0 ∧
    ‖GreenMinor_YA (green hH Complex.I) hM hD hm hm hp‖ ≤ (‖hm‖ + 2 * ((3 : ℕ) : ℝ) * (1 / 10)) / (1 / 2) * (1 / 100) ∧
    ‖GreenMinor_YX (green hH Complex.I) hM hD hm hm hp hy‖ ≤
      ((‖hm‖ + 2 * ((3 : ℕ) : ℝ) * (1 / 10)) * (1 / (1 / 2) + 1) + 4 * ((3 : ℕ) : ℝ) * (1 / 10) * (1 / 100) / (1 / 2)) * (1 / 100) := by
  have hT : GreenMinor_Tower (green hH Complex.I) (GreenMinor_Gs hH Complex.I) :=
    GreenMinor_tower hH_herm (by simp)
  have hgood : GreenMinor_good (GreenMinor_Gs hH Complex.I) hM (1 / 2) (1 / 100) 3 0 0 :=
    GreenMinor_good_of_event (Mb := hMb) (m := hm) (fun _ _ => rfl) (fun a => by simp [hMb]) (by norm_num)
      (by simp [hm]; norm_num) (by norm_num) (by norm_num) (by norm_num) hT hGΔ 0 0
  have hy1 : hy.1 ≠ 0 := by decide
  have hMuy : ‖hM hp hy‖ ≤ 1 := by
    rw [hMe]
    simp [hpy]
  have hΔpy : green hH Complex.I hp hy - hM hp hy ≠ 0 := by
    rw [green_hH, hGex_sub]
    have hp' : hp ∈ hC := by simp [hC]
    have hy' : hy ∈ hC := by simp [hC]
    simp [hp', hy', hcc_ne]
  have hmκ : (1 / 2 : ℝ) ≤ ‖hm‖ := by simp [hm]; norm_num
  exact ⟨hT, hgood, hΔpy,
    GreenMinor_YA_le (G := green hH Complex.I) (M := hM) (D := hD) (g₀ := 1 / 10) (κ := 1 / 2) (δ' := 1 / 100) (by norm_num) (by norm_num)
      (fun _ _ => rfl) hGΔ (by norm_num) hmκ hp,
    GreenMinor_YX_le (G := green hH Complex.I) (M := hM) (D := hD) (g₀ := 1 / 10) (κ := 1 / 2) (δ' := 1 / 100) (by norm_num) (by norm_num)
      (fun _ _ => rfl) hGΔ (by norm_num) hmκ hp hy hMuy⟩

end RealResolvent

section HandMade
open GreenMinorInst

-- S2 at the hand datum: the tower `hGs` of `hG`, the event `‖Δ‖_max ≤ δ = 1/100`, `κ = 1/2 ≤ ‖m‖ = 1`, `4δ ≤ κ`, `8 m₀ δ = 24/100 ≤ κ`
example : GreenMinor_good hGs hM (1 / 2) (1 / 100) 3 0 0 :=
  GreenMinor_good_of_event (Mb := hMb) (m := hm) (fun _ _ => rfl) (fun a => by simp [hMb]) (by norm_num)
    (by simp [hm]; norm_num) (by norm_num) (by norm_num) (by norm_num) hTower hΔb 0 0

-- S3: the base bounds at the datum (`d = 3`, `g₀ = 1/10`, `κ = 1/2`, `δ' = 1/100`)
example :
    ‖GreenMinor_YA hG hM hD hm hm hp‖ ≤ (‖hm‖ + 2 * ((3 : ℕ) : ℝ) * (1 / 10)) / (1 / 2) * (1 / 100) ∧
    ‖GreenMinor_YX hG hM hD hm hm hp hy‖ ≤
      ((‖hm‖ + 2 * ((3 : ℕ) : ℝ) * (1 / 10)) * (1 / (1 / 2) + 1) + 4 * ((3 : ℕ) : ℝ) * (1 / 10) * (1 / 100) / (1 / 2)) * (1 / 100) := by
  have hy1 : hy.1 ≠ 0 := by decide
  have hMuy : ‖hM hp hy‖ ≤ 1 := by
    rw [hMe]
    have : hp ≠ hy := fun h' => hy1 (by rw [← h']; rfl)
    simp [this]
  have hmκ : (1 / 2 : ℝ) ≤ ‖hm‖ := by simp [hm]; norm_num
  exact ⟨GreenMinor_YA_le (G := hG) (M := hM) (D := hD) (g₀ := 1 / 10) (κ := 1 / 2) (δ' := 1 / 100) (by norm_num) (by norm_num)
      (fun _ _ => rfl) hΔb (by norm_num) hmκ hp,
    GreenMinor_YX_le (G := hG) (M := hM) (D := hD) (g₀ := 1 / 10) (κ := 1 / 2) (δ' := 1 / 100) (by norm_num) (by norm_num)
      (fun _ _ => rfl) hΔb (by norm_num) hmκ hp hy hMuy⟩

end HandMade

section CarrierInst
open SizesInst FlowPinsInst

private abbrev c_g₀ : ℝ := BAflowLam0 sz0 zSeq 0
private abbrev c_E₀ : ℝ := BAflowEs sz0 zSeq 0
private abbrev c_m₀ : ℂ := BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0
private abbrev c_s₀ : ℂ := (c_E₀ : ℂ) + c_m₀

-- S3: the four identities at the carrier; the structural hypotheses come from `GreenCore_carrier`, `m ≠ 0` from `BAflow_real`
example (ω : sz0.SeqΩ) (u y : Vtx 3 (sz0.L 0) (sz0.W 0)) (hyu : y ≠ u) :
    GreenCore_Arow (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Xc sz0 0 (1 / 2) ω) (GreenCore_Dc sz0 zSeq 0) (1 / 2) c_m₀ u =
      GreenMinor_YA (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Mc sz0 zSeq 0) (GreenCore_Dc sz0 zSeq 0) c_s₀ c_m₀ u * c_m₀ /
        GreenCore_Gc sz0 zSeq 0 (1 / 2) ω u u ∧
    GreenCore_Xrow (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Xc sz0 0 (1 / 2) ω) u y =
      -(GreenMinor_YX (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Mc sz0 zSeq 0) (GreenCore_Dc sz0 zSeq 0) c_s₀ c_m₀ u y * c_m₀ /
        GreenCore_Gc sz0 zSeq 0 (1 / 2) ω u u) ∧
    GreenCore_Arow (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Xc sz0 0 (1 / 2) ω) (GreenCore_Dc sz0 zSeq 0) (1 / 2) c_m₀ u =
      GreenMinor_YA (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Mc sz0 zSeq 0) (GreenCore_Dc sz0 zSeq 0) c_s₀ c_m₀ u -
        GreenCore_Arow (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Xc sz0 0 (1 / 2) ω) (GreenCore_Dc sz0 zSeq 0) (1 / 2) c_m₀ u *
          (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω u u - c_m₀) / c_m₀ ∧
    GreenCore_Xrow (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Xc sz0 0 (1 / 2) ω) u y =
      -GreenMinor_YX (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Mc sz0 zSeq 0) (GreenCore_Dc sz0 zSeq 0) c_s₀ c_m₀ u y -
        GreenCore_Xrow (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω) (GreenCore_Xc sz0 0 (1 / 2) ω) u y *
          (GreenCore_Gc sz0 zSeq 0 (1 / 2) ω u u - c_m₀) / c_m₀ := by
  obtain ⟨hGR, hRG, -, hMR, hz, hM, hMd, hD, hG0⟩ :=
    GreenCore_carrier (by norm_num : (0 : ℝ) < 1 / 2) sz0 flow_sz0 0 (t := 1 / 2) (by norm_num) (half_lt_t0 0).le ω
      (m := c_m₀) (s := c_s₀) (zt := ztOf c_m₀ c_E₀ (1 / 2)) rfl rfl rfl
  have hr := BAflow_real (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq flow_sz0 0
  have hm0 : c_m₀ ≠ 0 := fun h0 => by
    have h1 : (1 / 2 : ℝ) ≤ c_m₀.im := hr.2
    rw [h0] at h1
    simp at h1
    linarith
  exact ⟨GreenMinor_Arow_eq hGR hRG hMR hz hM hMd hD hm0 (hG0 u), GreenMinor_Xrow_eq hGR hRG hMR hz hM hMd hD hm0 (hG0 u) hyu,
    GreenMinor_split_A hGR hRG hMR hz hM hMd hD hm0 (hG0 u), GreenMinor_split_X hGR hRG hMR hz hM hMd hD hm0 (hG0 u) hyu⟩

end CarrierInst

end RBM.BA
