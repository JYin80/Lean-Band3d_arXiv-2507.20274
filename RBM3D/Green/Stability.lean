/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Green.EntryCore
import RBM3D.Propagator.Prop5Short
import RBM3D.Defs.RadialSum
import RBM3D.Gauss.FineModel
import RBM3D.Defs.Semicircle

/-!
# Stability of `1 - t m² S` on the band profile, `d ≥ 3`

Paper: arXiv:2507.20274, (2.5) `eq:variancematrix`; property 5 of Lemma 2.19 (`lem_propTH`),
(2.67) `prop:ThfadC_short` (the input of the uniform constant); property 4, (2.65)
`eq:THETAinftinf` (the row sum `(1-t)⁻¹`, not uniform in `t`).

* `stable_svar_vtx`: `Stable (svar d L W g) ξ (1 + KΘ)` from a row-sum bound `KΘ` of `Θ_ξ`
  (`S = S^(B) ⊗ W^{-d} J`, blocks of `W^d` sites).  Dimension-free: `3 ≤ L` and `‖ξ‖ < 1` only.
* `Kstab3`: the `d ≥ 3` stability constant `1 + C_s (1 + Λ² expC(d-2, c_s))`, `(C_s, c_s)`
  the constants of `prop5Short_holds` ((2.67) `prop:ThfadC_short`) at `(d, Λ, κ'')`,
  `κ'' = √(κ(4-κ))/2`.  It depends on `(d, Λ, κ)` only: **no `L`, no `log L`**.  (In RBM2D the
  corresponding constant `Kstab2 κ L` is `O(1 + log L)`, a `d = 2` lattice sum; at `d ≥ 3` the
  exponential lattice sum `Σ_a e^{-c|a|}` converges uniformly in `L`, `sum_radial_exp_decay_le`.)
* `stable_svar_bulk_vtx`, `stable_svar_bulk`:
  `Stable (svar d L W g) (t m(E)²) (Kstab3 d Λ κ)`, resp. `Stable (svarF d L W g) …`, uniformly
  in `t ∈ [0,1)`, `|E| ≤ 2 - κ`, `0 < g ≤ Λ`, `L ≥ 3`, `W ≥ 1`.
* `eventually_Kstab3_mul_rpow_le`: the absorption `Kstab3 d Λ κ · W^{-c} ≤ 1/2`,
  eventually, under `SizeTendsto` and `Bandwidth` (only `W → ∞` is used).
-/

namespace RBM.Green

open Matrix Finset Filter
open RBM.Gauss (svar svarF Vtx Idx split splitEquiv Sizes)

/-! ## 1. Relabelling and the block structure of the profile -/

/-- `Stable` is invariant under relabelling the index set. -/
private theorem stability_relabel {n n' : Type*} [Fintype n] [Fintype n'] (e : n ≃ n')
    {S : n → n → ℝ} {ξ : ℂ} {K : ℝ} (h : Stable S ξ K) :
    Stable (fun i j => S (e.symm i) (e.symm j)) ξ K := by
  intro v B hB i
  have h1 := h (fun k => v (e k)) B (fun j => by
    have h2 := hB (e j)
    have h3 : ∑ k', (S (e.symm (e j)) (e.symm k') : ℂ) * v k' = ∑ k, (S j k : ℂ) * v (e k) := by
      rw [← Equiv.sum_comp e]
      simp
    rw [h3] at h2
    simpa using h2) (e.symm i)
  simpa using h1

section StableSvar

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W]

omit [NeZero L] [NeZero W] in
/-- The variance profile of the block-product index, entrywise in `ℂ`:
`S_{(a,α),(b,β)} = W^{-d} S^(B)_{ab}` ((2.5) `eq:variancematrix`). -/
private theorem stability_svar_cast (a b : Zd d L) (α β : Fin (W ^ d)) :
    ((svar d L W g (a, α) (b, β) : ℝ) : ℂ) = ((W : ℂ) ^ d)⁻¹ * SB d L g a b := by
  rw [SB_eq_map_SBR]
  simp [RBM.Gauss.svar]

/-- **`‖(1 - ξ S)⁻¹‖_{max→max} ≤ 1 + max_a ∑_b |(Θ_ξ)_{ab}|`** for the variance profile `svar` of
the block-product index `Vtx d L W = Z_L^d × Fin (W^d)`.  `S = S^(B) ⊗ W^{-d} J` acts on block
averages only (blocks of `W^d` sites), so a solution of `v - ξ S v = r` has block averages `Θ_ξ r̃`
and is recovered from them up to `r` itself.  Dimension-free: `3 ≤ L` and `‖ξ‖ < 1` only. -/
theorem stable_svar_vtx (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) {KΘ : ℝ}
    (hΘ : ∀ a : Zd d L, ∑ b : Zd d L, ‖Theta d L g ξ a b‖ ≤ KΘ) :
    Stable (svar d L W g) ξ (1 + KΘ) := by
  intro v B hB
  have hW : (W : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne W
  have hWr : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hWd : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ hW
  have : NeZero (W ^ d) := ⟨pow_ne_zero _ (NeZero.ne W)⟩
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB ((0 : Zd d L), (0 : Fin (W ^ d))))
  set vt : Zd d L → ℂ := fun a => ((W : ℂ) ^ d)⁻¹ * ∑ γ : Fin (W ^ d), v (a, γ) with hvt
  have hSv : ∀ (a : Zd d L) (α : Fin (W ^ d)),
      ∑ k, (svar d L W g (a, α) k : ℂ) * v k = ∑ b, SB d L g a b * vt b := by
    intro a α
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hvt]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [stability_svar_cast]
    ring
  set r : Vtx d L W → ℂ :=
    fun i => v i - ξ * ∑ k, (svar d L W g i k : ℂ) * v k with hr
  set rt : Zd d L → ℂ := fun a => ((W : ℂ) ^ d)⁻¹ * ∑ γ : Fin (W ^ d), r (a, γ) with hrt
  have hcard : (∑ _γ : Fin (W ^ d), B) = (W : ℝ) ^ d * B := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hrt_le : ∀ a, ‖rt a‖ ≤ B := by
    intro a
    rw [hrt]
    simp only
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    calc ((W : ℝ) ^ d)⁻¹ * ‖∑ γ : Fin (W ^ d), r (a, γ)‖
        ≤ ((W : ℝ) ^ d)⁻¹ * ∑ γ : Fin (W ^ d), ‖r (a, γ)‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ ((W : ℝ) ^ d)⁻¹ * ∑ _γ : Fin (W ^ d), B :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun γ _ => hB _) (by positivity)
      _ = B := by
          rw [hcard]
          field_simp
  have hmv : (1 - ξ • SB d L g) *ᵥ vt = rt := by
    funext a
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    have h1 : (SB d L g *ᵥ vt) a = ∑ b, SB d L g a b * vt b := rfl
    rw [h1, hrt]
    simp only [hr]
    simp only [hSv, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have h3 : vt a = ((W : ℂ) ^ d)⁻¹ * ∑ γ : Fin (W ^ d), v (a, γ) := rfl
    rw [h3]
    push_cast
    field_simp
  have hvt_eq : vt = Theta d L g ξ *ᵥ rt := by
    rw [← hmv, Matrix.mulVec_mulVec, Theta_mul_of_three_le hL hξ, Matrix.one_mulVec]
  have hvt_le : ∀ b, ‖vt b‖ ≤ KΘ * B := by
    intro b
    rw [hvt_eq]
    calc ‖(Theta d L g ξ *ᵥ rt) b‖ = ‖∑ c, Theta d L g ξ b c * rt c‖ := rfl
      _ ≤ ∑ c, ‖Theta d L g ξ b c * rt c‖ := norm_sum_le _ _
      _ ≤ ∑ c, ‖Theta d L g ξ b c‖ * B := Finset.sum_le_sum fun c _ => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hrt_le c) (norm_nonneg _)
      _ = (∑ c, ‖Theta d L g ξ b c‖) * B := by rw [Finset.sum_mul]
      _ ≤ KΘ * B := mul_le_mul_of_nonneg_right (hΘ b) hB0
  have hrow : ∀ a : Zd d L, ∑ b : Zd d L, ‖SB d L g a b‖ = 1 := sum_norm_SB_row d L g hL
  rintro ⟨a, α⟩
  have hvi : v (a, α) = r (a, α) + ξ * ∑ b, SB d L g a b * vt b := by
    rw [hr]; simp only; rw [hSv a α]; ring
  rw [hvi]
  have hsum : ‖∑ b, SB d L g a b * vt b‖ ≤ KΘ * B := by
    calc ‖∑ b, SB d L g a b * vt b‖ ≤ ∑ b, ‖SB d L g a b * vt b‖ := norm_sum_le _ _
      _ ≤ ∑ b, ‖SB d L g a b‖ * (KΘ * B) := Finset.sum_le_sum fun b _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hvt_le b) (norm_nonneg _)
      _ = KΘ * B := by rw [← Finset.sum_mul, hrow, one_mul]
  calc ‖r (a, α) + ξ * ∑ b, SB d L g a b * vt b‖
      ≤ ‖r (a, α)‖ + ‖ξ‖ * ‖∑ b, SB d L g a b * vt b‖ := by
        rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ B + 1 * (KΘ * B) := by
        have := mul_le_mul hξ.le hsum (norm_nonneg _) zero_le_one
        linarith [hB (a, α)]
    _ = (1 + KΘ) * B := by ring

/-- The block-product form of stability gives the fine-lattice form: `svarF` is `svar` read through
`split` (`svarF_eq_svar`), and `splitEquiv` is the bijection `split`. -/
private theorem stability_vtx_to_idx {ξ : ℂ} {K : ℝ} (h : Stable (svar d L W g) ξ K) :
    Stable (svarF d L W g) ξ K := by
  have h' := stability_relabel (splitEquiv d L W).symm h
  simp only [Equiv.symm_symm] at h'
  exact h'

end StableSvar

/-! ## 2. The `d ≥ 3` stability constant

The row sums of `Θ_ξ`, `ξ = t m(E)²`, are bounded through `prop5Short_holds`
((2.67) `prop:ThfadC_short`) with `σ₁ = σ₂`, `m = m(E)` (so that
`m(σ) m(σ) = m²`), the translation invariance `Θ(a, b) = Θ(0, b - a)` (property 2), and the
exponential lattice sum `sum_radial_exp_decay_le`.  The constants of the estimate are
quantified before `L` and `g`, so they depend on `(d, Λ, κ'')` only. -/

section Constant

/-- The constant `C_s` of `prop5Short_holds` at `(d, Λ, κ)`: its first constant
(chosen); `1` outside `3 ≤ d`, `0 < Λ`, `0 < κ`. -/
private noncomputable def pin5sC (d : ℕ) (Λ κ : ℝ) : ℝ :=
  if h : 3 ≤ d ∧ 0 < Λ ∧ 0 < κ then
    Classical.choose (prop5Short_holds d Λ κ h.1 h.2.1 h.2.2)
  else 1

/-- The decay rate `c_s` of `prop5Short_holds` at `(d, Λ, κ)`: its second constant
(chosen); `1` outside `3 ≤ d`, `0 < Λ`, `0 < κ`. -/
private noncomputable def pin5sc (d : ℕ) (Λ κ : ℝ) : ℝ :=
  if h : 3 ≤ d ∧ 0 < Λ ∧ 0 < κ then
    Classical.choose (Classical.choose_spec (prop5Short_holds d Λ κ h.1 h.2.1 h.2.2)).2
  else 1

/-- **The `d ≥ 3` stability constant**:
`1 + C_s (1 + Λ² · expC(d-2, c_s))`, with `(C_s, c_s)` the
constants of `prop5Short_holds` ((2.67) `prop:ThfadC_short`) at `(d, Λ, κ'')`,
`κ'' = √(κ (4 - κ)) / 2` (the lower
bound of `Im m(E)` on `|E| ≤ 2 - κ`), and `expC` the constant of the exponential lattice sum
`Σ_{a ∈ Z_L^d} e^{-c|a|} ≤ expC(d-2, c)`, uniform in `L`.  It depends on `(d, Λ, κ)` only: no
`L`, no `log L`. -/
noncomputable def Kstab3 (d : ℕ) (Λ κ : ℝ) : ℝ :=
  1 + pin5sC d Λ (Real.sqrt (κ * (4 - κ)) / 2) *
    (1 + Λ ^ 2 * expC (d - 2) (pin5sc d Λ (Real.sqrt (κ * (4 - κ)) / 2)))

private theorem pin5sC_pos (d : ℕ) (Λ κ : ℝ) : 0 < pin5sC d Λ κ := by
  unfold pin5sC
  split_ifs with h
  · exact (Classical.choose_spec (prop5Short_holds d Λ κ h.1 h.2.1 h.2.2)).1
  · exact one_pos

private theorem pin5sc_pos (d : ℕ) (Λ κ : ℝ) : 0 < pin5sc d Λ κ := by
  unfold pin5sc
  split_ifs with h
  · exact (Classical.choose_spec
      (Classical.choose_spec (prop5Short_holds d Λ κ h.1 h.2.1 h.2.2)).2).1
  · exact one_pos

/-- `Kstab3 ≥ 1` (it is `1 +` a non-negative term). -/
theorem one_le_Kstab3 (d : ℕ) (Λ κ : ℝ) : 1 ≤ Kstab3 d Λ κ := by
  unfold Kstab3
  have hC := pin5sC_pos d Λ (Real.sqrt (κ * (4 - κ)) / 2)
  have hc := pin5sc_pos d Λ (Real.sqrt (κ * (4 - κ)) / 2)
  have hE : 0 ≤ expC (d - 2) (pin5sc d Λ (Real.sqrt (κ * (4 - κ)) / 2)) := by
    unfold expC; positivity
  have : 0 ≤ pin5sC d Λ (Real.sqrt (κ * (4 - κ)) / 2) *
      (1 + Λ ^ 2 * expC (d - 2) (pin5sc d Λ (Real.sqrt (κ * (4 - κ)) / 2))) := by positivity
  linarith

/-- The two chosen constants are those of `prop5Short_holds` ((2.67) `prop:ThfadC_short`),
`σ₁ = σ₂`. -/
private theorem pin5s_spec {d : ℕ} {Λ κ : ℝ} (hd : 3 ≤ d) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    0 < pin5sC d Λ κ ∧ 0 < pin5sc d Λ κ ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ : Bool, ∀ a : Zd d L,
          haveI : NeZero L := ⟨by omega⟩
          ‖Theta d L g ((t : ℂ) * (PropSpin m σ * PropSpin m σ)) 0 a‖
            ≤ pin5sC d Λ κ * ((if a = 0 then (1 : ℝ) else 0)
                + g ^ 2 * Real.exp (-pin5sc d Λ κ * (zdistD d L a : ℝ))) := by
  have h : 3 ≤ d ∧ 0 < Λ ∧ 0 < κ := ⟨hd, hΛ, hκ⟩
  have P := prop5Short_holds d Λ κ hd hΛ hκ
  have h1 := Classical.choose_spec P
  have h2 := Classical.choose_spec h1.2
  have e1 : pin5sC d Λ κ = Classical.choose P := by
    unfold pin5sC
    split_ifs
    rfl
  have e2 : pin5sc d Λ κ = Classical.choose h1.2 := by
    unfold pin5sc
    split_ifs
    rfl
  rw [e1, e2]
  exact ⟨h1.1, h2.1, h2.2⟩

/-- **The row sums of `Θ_ξ` from the pointwise bound of (2.67) `prop:ThfadC_short`**: if
`|Θ_ξ(0, x)| ≤ C (1_{x=0} + g² e^{-c|x|})` for all `x` (with `0 < g ≤ Λ`, `c > 0`), then
`max_a ∑_b |Θ_ξ(a, b)| ≤ C (1 + Λ² · expC(d-2, c))`, uniformly in `L`.  Translation invariance
(property 2) and `Σ_x e^{-c|x|} ≤ expC(d-2, c)` (`sum_radial_exp_decay_le`, `d = k + 2`). -/
private theorem stability_rowsum_le {d L : ℕ} [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L)
    {Λ g C c : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) (hc : 0 < c) (hC : 0 < C) {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    (hpin : ∀ a : Zd d L, ‖Theta d L g ξ 0 a‖
      ≤ C * ((if a = 0 then (1 : ℝ) else 0) + g ^ 2 * Real.exp (-c * (zdistD d L a : ℝ))))
    (a : Zd d L) :
    ∑ b : Zd d L, ‖Theta d L g ξ a b‖ ≤ C * (1 + Λ ^ 2 * expC (d - 2) c) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  have hk : k + 2 - 2 = k := by omega
  have htr : ∀ b : Zd (k + 2) L, Theta (k + 2) L g ξ a b = Theta (k + 2) L g ξ 0 (b - a) := by
    intro b
    have h := Theta_apply_add_right_of_three_le (d := k + 2) (g := g) hL hξ 0 (b - a) a
    simpa using h
  have hsum1 : ∑ b : Zd (k + 2) L, ‖Theta (k + 2) L g ξ a b‖
      = ∑ x : Zd (k + 2) L, ‖Theta (k + 2) L g ξ 0 x‖ := by
    simp only [htr]
    exact Fintype.sum_equiv (Equiv.subRight a) _ _ (fun b => rfl)
  have hexp : ∑ x : Zd (k + 2) L, Real.exp (-c * (zdistD (k + 2) L x : ℝ)) ≤ expC k c := by
    simpa only [neg_mul] using sum_radial_exp_decay_le (L := L) k hc
  have hg2 : g ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hg.le hgΛ 2
  have hexp0 : 0 ≤ ∑ x : Zd (k + 2) L, Real.exp (-c * (zdistD (k + 2) L x : ℝ)) :=
    Finset.sum_nonneg fun x _ => (Real.exp_pos _).le
  rw [hsum1, hk]
  calc ∑ x : Zd (k + 2) L, ‖Theta (k + 2) L g ξ 0 x‖
      ≤ ∑ x : Zd (k + 2) L, C * ((if x = 0 then (1 : ℝ) else 0)
          + g ^ 2 * Real.exp (-c * (zdistD (k + 2) L x : ℝ))) :=
        Finset.sum_le_sum fun x _ => hpin x
    _ = C * (1 + g ^ 2 * ∑ x : Zd (k + 2) L, Real.exp (-c * (zdistD (k + 2) L x : ℝ))) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib,
          Finset.sum_ite_eq' Finset.univ (0 : Zd (k + 2) L), ← Finset.mul_sum]
        simp
    _ ≤ C * (1 + Λ ^ 2 * expC k c) := by
        refine mul_le_mul_of_nonneg_left ?_ hC.le
        have h1 : g ^ 2 * ∑ x : Zd (k + 2) L, Real.exp (-c * (zdistD (k + 2) L x : ℝ))
            ≤ Λ ^ 2 * expC k c :=
          mul_le_mul hg2 hexp hexp0 (sq_nonneg Λ)
        linarith

/-- On `|E| ≤ 2 - κ`: `κ'' = √(κ (4 - κ)) / 2 ≤ Im m(E) = √(4 - E²) / 2`. -/
private theorem stability_bulkIm_le {κ E : ℝ} (hE : |E| ≤ 2 - κ) :
    Real.sqrt (κ * (4 - κ)) / 2 ≤ (mE E).im := by
  rw [mE_im]
  have hsq : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs E]; exact pow_le_pow_left₀ (abs_nonneg E) hE 2
  have h1 : κ * (4 - κ) ≤ 4 - E ^ 2 := by nlinarith
  exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt h1) (by norm_num)

variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W]

/-- **`‖(1 - t m² S)⁻¹‖_{max→max} ≤ Kstab3 d Λ κ`** for the block-product profile `svar` on
`Vtx d L W`, uniformly in `L ≥ 3`, `W ≥ 1`, `0 < g ≤ Λ`, `t ∈ [0, 1)`, `|E| ≤ 2 - κ`: the row sums
of `Θ_{t m²}` are bounded through `prop5Short_holds` and the exponential lattice sum, with the
constant `Kstab3 d Λ κ - 1`. -/
theorem stable_svar_bulk_vtx (hd : 3 ≤ d) (hL : 3 ≤ L) {Λ κ E t : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ)
    (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Stable (svar d L W g) ((t : ℂ) * mE E ^ 2) (Kstab3 d Λ κ) := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := by linarith
  have hΛ : 0 < Λ := lt_of_lt_of_le hg hgΛ
  have hpos : 0 < κ * (4 - κ) := by nlinarith
  have hκ'' : 0 < Real.sqrt (κ * (4 - κ)) / 2 := by positivity
  have hκm : Real.sqrt (κ * (4 - κ)) / 2 ≤ (mE E).im := stability_bulkIm_le hE
  have hm : ‖mE E‖ = 1 := norm_mE hE2
  set ξ : ℂ := (t : ℂ) * mE E ^ 2 with hξdef
  have hξ : ‖ξ‖ < 1 := by
    rw [hξdef, norm_mul, norm_pow, hm, Complex.norm_real, Real.norm_of_nonneg ht0, one_pow,
      mul_one]
    exact ht1
  obtain ⟨hC, hc, H⟩ := pin5s_spec hd hΛ hκ''
  have hpin : ∀ a : Zd d L, ‖Theta d L g ξ 0 a‖
      ≤ pin5sC d Λ (Real.sqrt (κ * (4 - κ)) / 2) * ((if a = 0 then (1 : ℝ) else 0)
        + g ^ 2 * Real.exp (-pin5sc d Λ (Real.sqrt (κ * (4 - κ)) / 2) * (zdistD d L a : ℝ))) := by
    intro a
    have h := H L hL g hg hgΛ t ht0 ht1 (mE E) hm hκm true a
    have hspin : (t : ℂ) * (PropSpin (mE E) true * PropSpin (mE E) true) = ξ := by
      simp only [PropSpin, ite_true, hξdef]
      ring
    simpa only [hspin] using h
  exact stable_svar_vtx (W := W) hL hξ (fun a => stability_rowsum_le hd hL hg hgΛ hc hC hξ hpin a)

/-- **`‖(1 - t m² S)⁻¹‖_{max→max} ≤ Kstab3 d Λ κ`** for the variance profile `svarF` on the fine
lattice `Idx d L W`, uniformly in `L ≥ 3`, `W ≥ 1`, `0 < g ≤ Λ`, `t ∈ [0, 1)`, `|E| ≤ 2 - κ`. -/
theorem stable_svar_bulk (hd : 3 ≤ d) (hL : 3 ≤ L) {Λ κ E t : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ)
    (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Stable (svarF d L W g) ((t : ℂ) * mE E ^ 2) (Kstab3 d Λ κ) :=
  stability_vtx_to_idx (stable_svar_bulk_vtx hd hL hg hgΛ hκ hE ht0 ht1)

end Constant

/-! ## 3. The absorption condition -/

section Absorption

/-- **The absorption condition** `hKδ : K δ ≤ 1/2` of `norm_sq_green_diag_sub_le` for the `d ≥ 3`
constant: with `δ = W^{-c}`, `K = Kstab3 d Λ κ` and `W ≥ N^𝔠` (`Bandwidth`).  `SizeTendsto` makes
`W → ∞`; `Kstab3 d Λ κ` does not depend on `n`, so a power of `W` beats it.  (In RBM2D the
analogous `eventually_Kstab2_mul_rpow_le` must in addition absorb the
growth `1 + log L ≤ 1 + 𝔠⁻¹ log W` of `Kstab2 κ L`; at `d ≥ 3` that step does not occur.) -/
theorem eventually_Kstab3_mul_rpow_le {d : ℕ} (sz : Sizes d) (Λ κ : ℝ) {𝔠 c : ℝ}
    (h𝔠 : 0 < 𝔠) (hc : 0 < c) (hsz : sz.SizeTendsto) (hbw : sz.Bandwidth 𝔠) :
    ∀ᶠ n in atTop, Kstab3 d Λ κ * (sz.W n : ℝ) ^ (-c) ≤ 1 / 2 := by
  have h1 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
    (tendsto_rpow_atTop h𝔠).comp hsz
  have hW : Tendsto (fun n => (sz.W n : ℝ)) atTop atTop := tendsto_atTop_mono' _ hbw h1
  have hlim : Tendsto (fun x : ℝ => Kstab3 d Λ κ * x ^ (-c)) atTop (nhds 0) := by
    simpa using (tendsto_rpow_neg_atTop hc).const_mul (Kstab3 d Λ κ)
  have hev := (hlim.comp hW).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  exact hev.mono fun n hn => hn.le

end Absorption

end RBM.Green
