/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GreenMinor

/-!
# The block Anderson minors: the protected good event, the polynomial families

Paper: Lemma 8.4 (`lem_GbEXP_BA`), the block Anderson version of Lemma 3.1 (`lem_GbEXP`).  Everything
is deterministic, for one sample.

* The protected good event from `‖G - M‖_max ≤ δ` (`GreenMinor_good_of_event`): for
  `S ⊆ R_{β,o}`, `|S| ≤ m₀`, `x, y ∈ T_{β,o} ∖ S`, `|G^{(S)}_{xy} - M_{xy}| ≤ 2δ` and
  `|G^{(S)}_{xx}| ≥ κ/2`.  Only the rows of the block `β` of offset `≠ o` are removed, so each
  removal is between two different offsets: `M_{xκ} = M_{κy} = 0` (`GreenMinor_offset_ne`,
  `GreenMinor_cross`) and one step costs `δ_j²/(|m| - δ_j)`.
* The polynomial families `Y^A`, `Y^X` and the entry forms of the random re-entry
  `A_u = Y^A_u m / G_{uu}`, `𝔛_{uy} = -Y^X_{uy} m / G_{uu}`, the splits
  `A_u = Y^A_u - A_u (G_{uu} - m)/m`, and the base bounds `‖Y^A_u‖ ≤ (‖s‖ + 2 d g₀) δ'/κ`,
  `‖Y^X_{uy}‖ ≤ ((‖s‖ + 2 d g₀)(1/κ + 1) + 4 d g₀ δ'/κ) δ'` (uniform in the coupling: `g₀` enters
  only through `Σ_l ‖D_{ul}‖ = 2 d g₀`).
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

/-! ## 1. The protected good event from `‖G - M‖_max ≤ δ` -/

section GoodEvent
variable {d L W : ℕ} [NeZero L] [NeZero W] {G M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Zd d L → Zd d L → ℂ} {m : ℂ}
  {Gs : Finset (Vtx d L W) → Matrix (Vtx d L W) (Vtx d L W) ℂ} {κ δ : ℝ} {m₀ : ℕ}

/-- `R_{β,o} ⊆ T_{β,o}`. -/
theorem GreenMinor_R_subset_T (β : Zd d L) (o : Fin (W ^ d)) {x : Vtx d L W} (hx : x ∈ GreenMinor_R β o) :
    x ∈ GreenMinor_T β o := Or.inr hx.1

/-- The recursion of the minor identity on the protected levels: `|G^{(S)}_{xy} - M_{xy}| ≤ δ + 8 |S| δ²/κ`, `|S| ≤ m₀`. -/
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

/-- **The protected good event**: from the event `‖G - M‖_max ≤ δ` with `4δ ≤ κ ≤ |m|`, `8 m₀ δ ≤ κ`, the tower of minors
satisfies the protected good event `GreenMinor_good`: for `S ⊆ R_{β,o}`, `|S| ≤ m₀`, `x, y ∈ T_{β,o} ∖ S`,
`|G^{(S)}_{xy} - M_{xy}| ≤ 2δ` and `|G^{(S)}_{xx}| ≥ κ/2` (the analogue of `minorGoodLe_of_goodEvent` with `|m| = 1` replaced by `|m| ≥ κ`). -/
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

/-! ## 2. The entry forms of the random re-entry, the splits and the base bounds -/

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

/-- **The entry form of `A_u`**: `A_u = Y^A_u m / G_{uu}`, i.e. `A_u G_{uu} = s Δ_{uu} - Σ_l D_{ul} Δ_{lu}` (with `m ≠ 0`:
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

/-- **The entry form of `𝔛`**: `𝔛_{uy} = -Y^X_{uy} m / G_{uu}` for `y ≠ u`. -/
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

/-- **The base bound of `Y^A`**: `‖Y^A_u‖ ≤ (‖s‖ + 2 d g₀) δ' / κ`. -/
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

/-- **The base bound of `Y^X`**: `‖Y^X_{uy}‖ ≤ ((‖s‖ + 2 d g₀)(1/κ + 1) + 4 d g₀ δ'/κ) δ'` when `‖M_{uy}‖ ≤ 1`. -/
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

end RBM.BA
