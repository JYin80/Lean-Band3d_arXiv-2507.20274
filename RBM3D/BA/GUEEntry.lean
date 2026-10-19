/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.EntryTailMain
import RBM3D.BA.GreenCore
import RBM3D.BA.GreenStab
import RBM3D.BA.Ward
import RBM3D.BA.UNPins
import RBM3D.BA.CombesThomas
import RBM3D.BA.MFixedPoint

/-!
# The block Anderson entry layer of the GUE phase, deterministic part

The block Anderson version of the band file `Universality/GUEPhase/EntryDet.lean` (`stable_mix`, `mix_det`).
The matrix is the mixture `H = g Ψ + X` with `X = Xmat (mixSample (sz.withLam 0) n a b ω)`
(the block-diagonal GUE blocks at coupling `0` plus the flat GUE), the spectral parameter is
`z_u = E + (1 - u) m`, `u = a + b < 1`, and the reference matrix is `M = M^{(B)} ⊗ I`,
`M^{(B)} = BAMB d L g E m`, at a real-axis flow point `(g, E, m)` (`BAReal d L g κ E m`).
The variance profile of the mixture is `S_u = a S^{(B)}(0) + b / N` (`GUEEntry_Smv`).

* `stable_mixBA`: the stability of `1 - M^{(+,+)} S̃` at a flow point, from
  `baStab_of_real` and `BAoffDiag_scalar`, with the constant `16 κ⁻⁴ (1 + 16 κ⁻⁴)`.
* `mix_detBA`: on the a priori event `‖G - M‖_max ≤ δ` and the four large
  deviation inputs (`LDERow`, `LDECol`, `LDEQuad`, the diagonal bound) with the profile
  `S_u`, `|G_xy - M_xy|² ≤ C Φ² (max 𝓛 + W^{-d})` with `C = GUEEntry_C d Λ κ`. The
  deterministic core `GUEEntry_core` is the analogue of `GreenCore_diag` (`BA/GreenCore.lean`),
  with the flat part kept as an additive slack `Ξ = ΞC Φ L` (the Ward identity `Σ_k |G_ky|²
  ≤ (3/2) / Im z` and the `J`-part bound).
-/

open private EntryDet_card_vtx_real from RBM3D.Universality.GUEPhase.EntryDet

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false

noncomputable section
open Finset Matrix
namespace RBM.BA
open RBM RBM.Gauss RBM.Green RBM.Univ

section Stable
variable (d L : ℕ) [NeZero L]

private theorem GUEEntry_Q_symm (g : ℝ) (z m : ℂ) (x y : Zd d L) :
    BAMss d L (BAMB d L g z m) true true x y = BAMss d L (BAMB d L g z m) true true y x := by
  simp only [BAMss, BAMsigma, Matrix.of_apply, ite_true]
  exact mul_comm _ _

private theorem GUEEntry_Q_shift (g : ℝ) (z m : ℂ) (x y r : Zd d L) :
    BAMss d L (BAMB d L g z m) true true (x + r) (y + r) = BAMss d L (BAMB d L g z m) true true x y := by
  simp only [BAMss, BAMsigma, Matrix.of_apply, ite_true, BAMB_shift]

private theorem GUEEntry_Q_row (g : ℝ) (z m : ℂ) (x : Zd d L) :
    ∑ y, BAMss d L (BAMB d L g z m) true true x y = ∑ y, BAMss d L (BAMB d L g z m) true true 0 y := by
  have h : ∀ y, BAMss d L (BAMB d L g z m) true true x y =
      BAMss d L (BAMB d L g z m) true true 0 (y - x) := fun y => by
    have := GUEEntry_Q_shift d L g z m 0 (y - x) x
    rw [zero_add, sub_add_cancel] at this
    exact this
  simp only [h]
  exact Equiv.sum_comp (Equiv.subRight x) (fun y => BAMss d L (BAMB d L g z m) true true 0 y)

theorem stable_mixBA {g κ E : ℝ} {m : ℂ} (hκ : 0 < κ) (hr : BAReal d L g κ E m) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : a + b < 1) (v : Zd d L → ℂ) (B : ℝ)
    (hB : ∀ x, ‖v x - ∑ y, BAMss d L (BAMB d L g (E : ℂ) m) true true x y *
      ((a : ℂ) * v y + (b : ℂ) * ((((L ^ d : ℕ) : ℂ))⁻¹ * ∑ z, v z))‖ ≤ B) :
    ∀ x, ‖v x‖ ≤ 16 * κ⁻¹ ^ 4 * (1 + 16 * κ⁻¹ ^ 4) * B := by
  have hn : ‖m‖ ≤ 1 := BAm_norm_le_one d L g (E : ℂ) m (by simp) hr.1
  obtain ⟨hD1, hD2⟩ := BAoffDiag_scalar κ (a + b) m hκ hr.2 hn (by linarith) hu.le
  set Q := BAMss d L (BAMB d L g (E : ℂ) m) true true with hQ
  set r₂ : ℂ := ∑ y, Q 0 y with hr₂
  set S : ℂ := ∑ z, v z with hS
  set vb : ℂ := (((L ^ d : ℕ) : ℂ))⁻¹ * S with hvb
  have hLd : ((L ^ d : ℕ) : ℝ) ≠ 0 := by
    have : 0 < L ^ d := pow_pos (NeZero.pos L) d
    exact_mod_cast this.ne'
  have hLdC : ((L ^ d : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hLd
  have hcard : (Fintype.card (Zd d L) : ℝ) = ((L ^ d : ℕ) : ℝ) := by rw [BAcard_Zd]
  have hrow : ∀ x, ∑ y, Q x y = r₂ := fun x => GUEEntry_Q_row d L _ _ _ x
  have hcol : ∀ y, ∑ x, Q x y = r₂ := fun y => by
    rw [← hrow y]; exact Finset.sum_congr rfl fun x _ => GUEEntry_Q_symm d L _ _ _ x y
  -- `|r₂| ≤ 1` and `|1 - u r₂| ≥ (κ²/4)²`
  have hr2le : ‖r₂‖ ≤ 1 := by
    calc ‖r₂‖ ≤ ∑ y, ‖Q 0 y‖ := norm_sum_le _ _
      _ = ∑ y, ‖BAMB d L g (E : ℂ) m 0 y‖ ^ 2 := Finset.sum_congr rfl fun y _ => BAMss_ss_norm d L g (E : ℂ) m true 0 y
      _ = 1 := BAMB_row_sq_real d L g E m hr.1 0
  have hdiag : Q 0 0 = m ^ 2 := by
    have := BAMss_ss_diag d L g (E : ℂ) m hr.1 true 0
    simpa using this
  have hoff : ∑ y ∈ univ.erase 0, ‖Q 0 y‖ = 1 - ‖m‖ ^ 2 := BAMss_row_offdiag_sum d L g E m hr.1 true 0
  have hgap : (κ ^ 2 / 4) ^ 2 ≤ ‖1 - ((a + b : ℝ) : ℂ) * r₂‖ := by
    have hsplit : r₂ = m ^ 2 + ∑ y ∈ univ.erase 0, Q 0 y := by
      rw [hr₂, ← hdiag]; exact (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
    have hbd : ‖∑ y ∈ univ.erase 0, Q 0 y‖ ≤ 1 - ‖m‖ ^ 2 := hoff ▸ norm_sum_le _ _
    have h1 : ‖1 - ((a + b : ℝ) : ℂ) * m ^ 2‖ ≤ ‖1 - ((a + b : ℝ) : ℂ) * r₂‖ + (a + b) * (1 - ‖m‖ ^ 2) := by
      have e : (1 : ℂ) - ((a + b : ℝ) : ℂ) * m ^ 2 =
          (1 - ((a + b : ℝ) : ℂ) * r₂) + ((a + b : ℝ) : ℂ) * ∑ y ∈ univ.erase 0, Q 0 y := by
        rw [hsplit]; ring
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      exact mul_le_mul_of_nonneg_left hbd (by linarith)
    have h2 : (a + b) * (1 - ‖m‖ ^ 2) ≤ 1 - ‖m‖ ^ 2 := by
      have : 0 ≤ 1 - ‖m‖ ^ 2 := by nlinarith [norm_nonneg m]
      nlinarith
    have h3 : (κ ^ 2 / 4) * ‖1 - ((a + b : ℝ) : ℂ) * m ^ 2‖ ≤ ‖1 - ((a + b : ℝ) : ℂ) * r₂‖ := by
      nlinarith [norm_nonneg (1 - ((a + b : ℝ) : ℂ) * r₂)]
    have h4 : (κ ^ 2 / 4) * (κ ^ 2 / 4) ≤ (κ ^ 2 / 4) * ‖1 - ((a + b : ℝ) : ℂ) * m ^ 2‖ :=
      mul_le_mul_of_nonneg_left hD1 (by positivity)
    nlinarith
  -- the summed equation
  set R : Zd d L → ℂ := fun x => v x - ∑ y, Q x y * ((a : ℂ) * v y + (b : ℂ) * vb) with hR
  have hsum : ∑ x, R x = (1 - ((a + b : ℝ) : ℂ) * r₂) * S := by
    have e1 : ∑ x, ∑ y, Q x y * ((a : ℂ) * v y + (b : ℂ) * vb) = r₂ * ((a : ℂ) * S + (b : ℂ) * (((L ^ d : ℕ) : ℂ) * vb)) := by
      rw [Finset.sum_comm]
      have : ∀ y, ∑ x, Q x y * ((a : ℂ) * v y + (b : ℂ) * vb) = r₂ * ((a : ℂ) * v y + (b : ℂ) * vb) := fun y => by
        rw [← Finset.sum_mul, hcol y]
      simp only [this, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, BAcard_Zd]
      push_cast
      rw [hS]
    have e2 : ((L ^ d : ℕ) : ℂ) * vb = S := by rw [hvb, ← mul_assoc, mul_inv_cancel₀ hLdC, one_mul]
    simp only [hR, Finset.sum_sub_distrib]
    rw [e1, e2]
    push_cast
    ring
  have hRB : ‖∑ x, R x‖ ≤ ((L ^ d : ℕ) : ℝ) * B := by
    calc ‖∑ x, R x‖ ≤ ∑ x, ‖R x‖ := norm_sum_le _ _
      _ ≤ ∑ _x : Zd d L, B := Finset.sum_le_sum fun x _ => hB x
      _ = ((L ^ d : ℕ) : ℝ) * B := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  have hSle : ‖S‖ * (κ ^ 2 / 4) ^ 2 ≤ ((L ^ d : ℕ) : ℝ) * B := by
    calc ‖S‖ * (κ ^ 2 / 4) ^ 2 ≤ ‖S‖ * ‖1 - ((a + b : ℝ) : ℂ) * r₂‖ :=
          mul_le_mul_of_nonneg_left hgap (norm_nonneg _)
      _ = ‖∑ x, R x‖ := by rw [hsum, norm_mul, mul_comm]
      _ ≤ _ := hRB
  have hvbB : ‖vb‖ ≤ 16 * κ⁻¹ ^ 4 * B := by
    have hLpos : (0 : ℝ) < ((L ^ d : ℕ) : ℝ) := by positivity
    have hk4 : (0 : ℝ) < (κ ^ 2 / 4) ^ 2 := by positivity
    rw [hvb, norm_mul, norm_inv, Complex.norm_natCast, inv_mul_eq_div, div_le_iff₀ hLpos]
    have : ‖S‖ ≤ ((L ^ d : ℕ) : ℝ) * B / (κ ^ 2 / 4) ^ 2 := by rw [le_div_iff₀ hk4]; exact hSle
    refine this.trans (le_of_eq ?_)
    field_simp
    ring
  -- apply the max-principle stability at `t = a`
  have hB' : ∀ x, ‖v x - (a : ℂ) * ∑ y, Q x y * v y‖ ≤ (1 + 16 * κ⁻¹ ^ 4) * B := by
    intro x
    have e : v x - (a : ℂ) * ∑ y, Q x y * v y = R x + (b : ℂ) * vb * r₂ := by
      simp only [hR]
      have : ∑ y, Q x y * ((a : ℂ) * v y + (b : ℂ) * vb) = (a : ℂ) * ∑ y, Q x y * v y + (b : ℂ) * vb * r₂ := by
        rw [← hrow x, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun y _ => by ring
      rw [this]; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(b : ℂ) * vb * r₂‖ ≤ b * (16 * κ⁻¹ ^ 4 * B) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb]
      have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
      calc b * ‖vb‖ * ‖r₂‖ ≤ b * ‖vb‖ * 1 := mul_le_mul_of_nonneg_left hr2le (by positivity)
        _ ≤ b * (16 * κ⁻¹ ^ 4 * B) := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hvbB hb
    have hb1 : b ≤ 1 := by linarith
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    have hk : 0 ≤ 16 * κ⁻¹ ^ 4 * B := by positivity
    nlinarith [hB x]
  intro x
  have := baStab_of_real d L g κ E m hκ hr a ha (by linarith) v ((1 + 16 * κ⁻¹ ^ 4) * B) hB' x
  linarith

end Stable

private structure GUEEntry_Setup (d L W : ℕ) [NeZero L] [NeZero W] (G X M D : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (Mb : Matrix (Zd d L) (Zd d L) ℂ) (m s z : ℂ) (t g₀ κ δ c₀ ρ S : ℝ) : Prop where
  hL : 3 ≤ L
  hGR : G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1
  hRG : (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1
  hMR : (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * M = 1
  hMR' : M * (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1
  hz : z = s - (t : ℂ) * m
  hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0
  hMd : ∀ a, Mb a a = m
  hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0
  hκ : 0 < κ
  hκm : κ ≤ ‖m‖
  hm1 : ‖m‖ ≤ 1
  hMb1 : ∀ a b, ‖Mb a b‖ ≤ 1
  hc₀ : 0 < c₀
  hdec : ∀ a b, ‖Mb a b‖ ≤ c₀⁻¹ * Real.exp (-c₀ * (zdistD d L (a - b) : ℝ))
  hρ : ∀ c, ∑ b, ‖Mb b c‖ ≤ ρ
  hS : ∀ a, ∑ b, Real.exp (-(c₀ / 2) * (zdistD d L (a - b) : ℝ)) ≤ S
  hg : 0 ≤ g₀
  hδ : δ ≤ κ / 2
  hδ0 : 0 ≤ δ
  hwd : ((W : ℝ) ^ d)⁻¹ ≤ δ ^ 2
  hΩ : ∀ u v, ‖G u v - M u v‖ ≤ δ

section Rb
variable {d L W : ℕ} [NeZero L] [NeZero W] {G X M D : Matrix (Vtx d L W) (Vtx d L W) ℂ}
  {Mb : Matrix (Zd d L) (Zd d L) ℂ} {m s z : ℂ} {t g₀ κ δ c₀ ρ S Φ Ξ : ℝ}

theorem GUEEntry_Xcol_avg (hΦ : 0 ≤ Φ) (hκ : 0 < κ)
    (hX : ∀ x w, ‖GreenCore_Xcol G X x w‖ ^ 2 ≤
      Φ * (2 * GreenCore_Rrow G x w.1 + (8 / κ ^ 2) * ‖G x w‖ ^ 2 * GreenCore_Rrow G w w.1) + Ξ)
    (hRrow : ∀ x b, GreenCore_Rrow G x b ≤ 13 / 4 * δ ^ 2) (a : Zd d L) (w : Vtx d L W) :
    ((W : ℝ) ^ d)⁻¹ * ∑ o, ‖GreenCore_Xcol G X (a, o) w‖ ^ 2 ≤
      Φ * (2 * GreenCore_loop G a w.1 + (26 / κ ^ 2) * δ ^ 2 * GreenCore_R G a w) + Ξ := by
  have hw := GreenCore_w_pos (d := d) (W := W)
  have h1 : ∀ o, ‖GreenCore_Xcol G X (a, o) w‖ ^ 2 ≤
      Φ * (2 * GreenCore_Rrow G (a, o) w.1 + (26 / κ ^ 2) * δ ^ 2 * ‖G (a, o) w‖ ^ 2) + Ξ := by
    intro o
    refine (hX _ _).trans (add_le_add_left (mul_le_mul_of_nonneg_left ?_ hΦ) _)
    have := mul_le_mul_of_nonneg_left (hRrow w w.1) (by positivity : (0 : ℝ) ≤ 8 / κ ^ 2 * ‖G (a, o) w‖ ^ 2)
    have e : 8 / κ ^ 2 * ‖G (a, o) w‖ ^ 2 * (13 / 4 * δ ^ 2) = 26 / κ ^ 2 * δ ^ 2 * ‖G (a, o) w‖ ^ 2 := by ring
    linarith
  have e1 : ((W : ℝ) ^ d)⁻¹ * ∑ o, GreenCore_Rrow G (a, o) w.1 = GreenCore_loop G a w.1 := by
    unfold GreenCore_loop GreenCore_Rrow
    simp only [Finset.mul_sum, sq, mul_assoc]
  have e2 : ∑ o : Fin (W ^ d), (Φ * (2 * GreenCore_Rrow G (a, o) w.1 + (26 / κ ^ 2) * δ ^ 2 * ‖G (a, o) w‖ ^ 2) + Ξ) =
      Φ * (2 * ∑ o, GreenCore_Rrow G (a, o) w.1 + (26 / κ ^ 2) * δ ^ 2 * ∑ o, ‖G (a, o) w‖ ^ 2) + ((W : ℝ) ^ d) * Ξ := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  calc ((W : ℝ) ^ d)⁻¹ * ∑ o, ‖GreenCore_Xcol G X (a, o) w‖ ^ 2
      ≤ ((W : ℝ) ^ d)⁻¹ * ∑ o, (Φ * (2 * GreenCore_Rrow G (a, o) w.1 + (26 / κ ^ 2) * δ ^ 2 * ‖G (a, o) w‖ ^ 2) + Ξ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun o _ => h1 o) hw.le
    _ = Φ * (2 * (((W : ℝ) ^ d)⁻¹ * ∑ o, GreenCore_Rrow G (a, o) w.1) +
          (26 / κ ^ 2) * δ ^ 2 * (((W : ℝ) ^ d)⁻¹ * ∑ o, ‖G (a, o) w‖ ^ 2)) + (((W : ℝ) ^ d)⁻¹ * ((W : ℝ) ^ d)) * Ξ := by
        rw [e2]; ring
    _ = _ := by rw [e1, GreenCore_w_mul, one_mul]; rfl

theorem GUEEntry_twoSided {α2 : ℝ} (hρ0 : 0 ≤ ρ) (hκ : 0 < κ) (hΦ0 : 0 ≤ Φ) (hα : 0 ≤ α2) (hΞ : 0 ≤ Ξ)
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hρ : ∀ c, ∑ b, ‖Mb b c‖ ≤ ρ)
    (hΔ : ∀ x y : Vtx d L W, G x y - M x y = -∑ b', Mb b' y.1 *
      (GreenCore_Acol G X D t m (b', y.2) * G x (b', y.2) + GreenCore_Xcol G X x (b', y.2)))
    (hA : ∀ w, ‖GreenCore_Acol G X D t m w‖ ^ 2 ≤ α2)
    (hX : ∀ x w, ‖GreenCore_Xcol G X x w‖ ^ 2 ≤
      Φ * (2 * GreenCore_Rrow G x w.1 + (8 / κ ^ 2) * ‖G x w‖ ^ 2 * GreenCore_Rrow G w w.1) + Ξ)
    (hRrow : ∀ x b, GreenCore_Rrow G x b ≤ 13 / 4 * δ ^ 2) (a c : Zd d L) (o : Fin (W ^ d)) :
    GreenCore_R G a (c, o) ≤ 2 * ((W : ℝ) ^ d)⁻¹ * ‖Mb a c‖ ^ 2 +
      8 * ρ * Φ * ∑ b', ‖Mb b' c‖ * GreenCore_loop G a b' +
      4 * ρ * (α2 + 26 / κ ^ 2 * Φ * δ ^ 2) * ∑ b', ‖Mb b' c‖ * GreenCore_R G a (b', o) + 8 * ρ * ρ * Ξ := by
  have hw := GreenCore_w_pos (d := d) (W := W)
  have pt : ∀ x : Vtx d L W, ‖G x (c, o)‖ ^ 2 ≤ 2 * ‖M x (c, o)‖ ^ 2 + 2 * (ρ * ∑ b', ‖Mb b' c‖ *
      (2 * α2 * ‖G x (b', o)‖ ^ 2 + 2 * ‖GreenCore_Xcol G X x (b', o)‖ ^ 2)) := fun x => by
    have hZ : ∀ b', ‖GreenCore_Acol G X D t m (b', o) * G x (b', o) + GreenCore_Xcol G X x (b', o)‖ ^ 2 ≤
        2 * α2 * ‖G x (b', o)‖ ^ 2 + 2 * ‖GreenCore_Xcol G X x (b', o)‖ ^ 2 := fun b' => by
      have h3 := norm_add_le (GreenCore_Acol G X D t m (b', o) * G x (b', o)) (GreenCore_Xcol G X x (b', o))
      rw [norm_mul] at h3
      have h4 : (‖GreenCore_Acol G X D t m (b', o)‖ * ‖G x (b', o)‖) ^ 2 ≤ α2 * ‖G x (b', o)‖ ^ 2 := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_right (hA _) (sq_nonneg _)
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) h3 2,
        sq_nonneg (‖GreenCore_Acol G X D t m (b', o)‖ * ‖G x (b', o)‖ - ‖GreenCore_Xcol G X x (b', o)‖)]
    have h5 : ‖G x (c, o) - M x (c, o)‖ ^ 2 ≤ ρ * ∑ b', ‖Mb b' c‖ *
        (2 * α2 * ‖G x (b', o)‖ ^ 2 + 2 * ‖GreenCore_Xcol G X x (b', o)‖ ^ 2) := by
      rw [hΔ x (c, o), norm_neg]
      calc _ ≤ (∑ b', ‖Mb b' c‖ * ‖GreenCore_Acol G X D t m (b', o) * G x (b', o) + GreenCore_Xcol G X x (b', o)‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans (Finset.sum_le_sum fun b' _ => (norm_mul _ _).le)) 2
        _ ≤ (∑ b', ‖Mb b' c‖) * ∑ b', ‖Mb b' c‖ * ‖GreenCore_Acol G X D t m (b', o) * G x (b', o) + GreenCore_Xcol G X x (b', o)‖ ^ 2 :=
            Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun b' _ => norm_nonneg _) (fun b' _ => by positivity) fun b' _ => le_of_eq (by ring)
        _ ≤ _ := mul_le_mul (hρ c) (Finset.sum_le_sum fun b' _ => mul_le_mul_of_nonneg_left (hZ b') (norm_nonneg _))
            (Finset.sum_nonneg fun b' _ => by positivity) hρ0
    have h1 : ‖G x (c, o)‖ ≤ ‖M x (c, o)‖ + ‖G x (c, o) - M x (c, o)‖ := by linarith [norm_sub_norm_le (G x (c, o)) (M x (c, o))]
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) h1 2, sq_nonneg (‖M x (c, o)‖ - ‖G x (c, o) - M x (c, o)‖)]
  refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun o' _ => pt (a, o')) hw.le).trans ?_
  rw [GreenCore_dsum (fun o' => ‖M (a, o') (c, o)‖ ^ 2) (fun o' b' => ‖Mb b' c‖ * (2 * α2 * ‖G (a, o') (b', o)‖ ^ 2 +
    2 * ‖GreenCore_Xcol G X (a, o') (b', o)‖ ^ 2)) (((W : ℝ) ^ d)⁻¹) ρ, GreenCore_sumM2 hM a c o]
  have hb : ∀ b', ((W : ℝ) ^ d)⁻¹ * ∑ o', ‖Mb b' c‖ * (2 * α2 * ‖G (a, o') (b', o)‖ ^ 2 + 2 * ‖GreenCore_Xcol G X (a, o') (b', o)‖ ^ 2) ≤
      ‖Mb b' c‖ * (4 * Φ * GreenCore_loop G a b' + (2 * α2 + 52 / κ ^ 2 * Φ * δ ^ 2) * GreenCore_R G a (b', o) + 2 * Ξ) := fun b' => by
    have h1 := GUEEntry_Xcol_avg hΦ0 hκ hX hRrow a (b', o); dsimp only at h1
    have e1 : ((W : ℝ) ^ d)⁻¹ * ∑ o', ‖Mb b' c‖ * (2 * α2 * ‖G (a, o') (b', o)‖ ^ 2 + 2 * ‖GreenCore_Xcol G X (a, o') (b', o)‖ ^ 2) =
        ‖Mb b' c‖ * (2 * α2 * GreenCore_R G a (b', o) + 2 * (((W : ℝ) ^ d)⁻¹ * ∑ o', ‖GreenCore_Xcol G X (a, o') (b', o)‖ ^ 2)) := by
      unfold GreenCore_R; simp only [← Finset.mul_sum, mul_add, Finset.sum_add_distrib]; ring
    rw [e1]
    refine mul_le_mul_of_nonneg_left ((add_le_add le_rfl (mul_le_mul_of_nonneg_left h1 two_pos.le)).trans (le_of_eq (by ring))) (norm_nonneg _)
  have hρe : ∑ b', ‖Mb b' c‖ * (2 * Ξ) ≤ ρ * (2 * Ξ) := by
    rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hρ c) (by positivity)
  have hsum : ∑ b', ‖Mb b' c‖ * (4 * Φ * GreenCore_loop G a b' + (2 * α2 + 52 / κ ^ 2 * Φ * δ ^ 2) * GreenCore_R G a (b', o) + 2 * Ξ)
      = 4 * Φ * ∑ b', ‖Mb b' c‖ * GreenCore_loop G a b' + (2 * α2 + 52 / κ ^ 2 * Φ * δ ^ 2) * ∑ b', ‖Mb b' c‖ * GreenCore_R G a (b', o) + ∑ b', ‖Mb b' c‖ * (2 * Ξ) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1; congr 1
    · exact Finset.sum_congr rfl fun b' _ => by ring
    · exact Finset.sum_congr rfl fun b' _ => by ring
  have hfin := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b' (_ : b' ∈ (Finset.univ : Finset (Zd d L))) => hb b') (by positivity : (0 : ℝ) ≤ 2 * ρ)
  rw [hsum] at hfin
  have hr1 := mul_le_mul_of_nonneg_left hρe (by positivity : (0 : ℝ) ≤ 2 * ρ)
  refine le_trans (add_le_add le_rfl hfin) ?_
  have hρρΞ := mul_nonneg (mul_nonneg hρ0 hρ0) hΞ
  have hα' : (2 * α2 + 52 / κ ^ 2 * Φ * δ ^ 2) = 2 * (α2 + 26 / κ ^ 2 * Φ * δ ^ 2) := by ring
  rw [hα']
  nlinarith [hr1, hρρΞ]

private theorem GUEEntry_Rbound (hS : GUEEntry_Setup d L W G X M D Mb m s z t g₀ κ δ c₀ ρ S)
    (hΦ : 1 ≤ Φ) (hΞ : 0 ≤ Ξ)
    (hLcol : ∀ x w, ‖GreenCore_Xcol G X x w‖ ^ 2 ≤
      Φ * (2 * GreenCore_Rrow G x w.1 + (8 / κ ^ 2) * ‖G x w‖ ^ 2 * GreenCore_Rrow G w w.1) + Ξ)
    (hC1 : 8 * ρ * (c₀⁻¹ * S) * GreenCore_theta d κ Φ δ g₀ ≤ 1)
    (φ : Zd d L → Zd d L → ℝ) (hφ : ∀ a b, GreenCore_loop G a b ≤ φ a b ^ 2) (a c : Zd d L) (o : Fin (W ^ d)) :
    GreenCore_R G a (c, o) ≤ 4 * c₀⁻¹ ^ 2 * S * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c₀ / 2) * (zdistD d L (a - c) : ℝ)) +
      16 * ρ * Φ * c₀⁻¹ * S * ∑ b'', Real.exp (-(c₀ / 2) * (zdistD d L (c - b'') : ℝ)) * (φ a b'' ^ 2 + ρ * Ξ / (Φ * κ)) := by
  have hΦ0 : 0 ≤ Φ := by linarith
  have hΦp : 0 < Φ := by linarith
  have hκ := hS.hκ
  obtain ⟨hGuu, hG32, hGoff⟩ := GreenCore_crude hS.hM hS.hMd hS.hMb1 hS.hκm hS.hm1 hS.hδ hS.hΩ
  have hG0 : ∀ u, G u u ≠ 0 := fun u h => by
    have := hGuu u; rw [h, norm_zero] at this; linarith
  have hΔ := GreenCore_Delta_col (X := X) hS.hGR hS.hRG hS.hMR hS.hz hS.hM hG0
  have hA := fun w => GreenCore_Acol_sq hS.hL hS.hg hκ hS.hGR hS.hRG hS.hMR hS.hMR' hS.hz hS.hM hS.hMd hS.hD hS.hκm hS.hMb1 hGuu hS.hΩ w
  have hRrow := (GreenCore_apriori hG32 hGoff hS.hδ0 hS.hwd).2
  have hρ0 : 0 ≤ ρ := le_trans (Finset.sum_nonneg fun b _ => norm_nonneg _) (hS.hρ 0)
  have hα : 0 ≤ (4 / κ ^ 2) * (2 * d * g₀ + (1 + 2 * d * g₀) / κ) ^ 2 * δ ^ 2 := by
    have := hS.hg; positivity
  have h2 := GUEEntry_twoSided hρ0 hκ hΦ0 hα hΞ hS.hM hS.hρ hΔ hA hLcol hRrow
  obtain ⟨d0, dn, ds, dt⟩ := GreenCore_dist (d := d) (L := L)
  have hϑ : 0 ≤ GreenCore_theta d κ Φ δ g₀ := by unfold GreenCore_theta; have := hS.hg; positivity
  set e : ℝ := ρ * Ξ / (Φ * κ) with he
  have he0 : 0 ≤ e := by positivity
  have hsq : ∀ b'', Real.sqrt (φ a b'' ^ 2 + e) ^ 2 = φ a b'' ^ 2 + e := fun b'' =>
    Real.sq_sqrt (by positivity)
  have hrf : ∀ c, GreenCore_R G a (c, o) ≤ 2 * ((W : ℝ) ^ d)⁻¹ * ‖Mb a c‖ ^ 2 +
      8 * ρ * Φ * ∑ b'', ‖Mb b'' c‖ * Real.sqrt (φ a b'' ^ 2 + e) ^ 2 +
      4 * ρ * GreenCore_theta d κ Φ δ g₀ * ∑ b', ‖Mb b' c‖ * GreenCore_R G a (b', o) := by
    intro c
    refine (h2 a c o).trans ?_
    simp only [hsq]
    have h3 : ∑ b', ‖Mb b' c‖ * GreenCore_loop G a b' ≤ ∑ b', ‖Mb b' c‖ * φ a b' ^ 2 :=
      Finset.sum_le_sum fun b' _ => mul_le_mul_of_nonneg_left (hφ a b') (norm_nonneg _)
    have h4 : κ ≤ ∑ b'', ‖Mb b'' c‖ := by
      calc κ ≤ ‖Mb c c‖ := by rw [hS.hMd]; exact hS.hκm
        _ ≤ ∑ b'', ‖Mb b'' c‖ := Finset.single_le_sum (f := fun b'' => ‖Mb b'' c‖) (fun b _ => norm_nonneg _) (Finset.mem_univ c)
    have h5 : 8 * ρ * ρ * Ξ ≤ 8 * ρ * Φ * (e * ∑ b'', ‖Mb b'' c‖) := by
      have : Φ * e = ρ * Ξ / κ := by rw [he]; field_simp
      calc 8 * ρ * ρ * Ξ = 8 * ρ * (ρ * Ξ) := by ring
        _ = 8 * ρ * ((ρ * Ξ / κ) * κ) := by field_simp
        _ ≤ 8 * ρ * ((ρ * Ξ / κ) * ∑ b'', ‖Mb b'' c‖) := by
            gcongr
        _ = 8 * ρ * Φ * (e * ∑ b'', ‖Mb b'' c‖) := by rw [← this]; ring
    have h6 : ∑ b'', ‖Mb b'' c‖ * (φ a b'' ^ 2 + e) = ∑ b'', ‖Mb b'' c‖ * φ a b'' ^ 2 + e * ∑ b'', ‖Mb b'' c‖ := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun b _ => by ring
    have h7 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 8 * ρ * Φ)
    unfold GreenCore_theta
    rw [h6]
    nlinarith [h7, h5]
  have key := GreenCore_Rstar (B := Zd d L) (fun a b => ((zdistD d L (a - b) : ℕ) : ℝ)) d0 dn ds dt (fun a b => Mb a b) hS.hc₀ hκ
    (fun a => by rw [hS.hMd]; exact hS.hκm) hS.hdec (fun c => GreenCore_rhoe _ ds _ hS.hc₀ hS.hdec hS.hS c) hS.hS
    GreenCore_w_pos hρ0 hΦ0 hϑ hC1 a (fun b'' => Real.sqrt (φ a b'' ^ 2 + e)) (fun c => GreenCore_R G a (c, o))
    (fun c => mul_nonneg GreenCore_w_pos.le (Finset.sum_nonneg fun _ _ => by positivity)) hrf c
  simp only [hsq] at key
  exact key

end Rb

section Slack
variable {d L W : ℕ} [NeZero L] [NeZero W] {G X : Matrix (Vtx d L W) (Vtx d L W) ℂ} {a b Φ κ Y : ℝ}

/-- The mixture profile `a S^{(B)}(0) + b N⁻¹` on the block-product index. -/
def GUEEntry_Smv (d L W : ℕ) [NeZero L] [NeZero W] (a b : ℝ) (x y : Vtx d L W) : ℝ :=
  a * svar d L W 0 x y + b / (((W * L) ^ d : ℕ) : ℝ)

theorem GUEEntry_Smv_eq (a b : ℝ) (x y : Vtx d L W) :
    GUEEntry_Smv d L W a b x y =
      Smix d L W 0 a b ((splitEquiv d L W).symm x) ((splitEquiv d L W).symm y) := by
  unfold GUEEntry_Smv Smix
  have hx : split d L W ((splitEquiv d L W).symm x) = x := (splitEquiv d L W).apply_symm_apply x
  have hy : split d L W ((splitEquiv d L W).symm y) = y := (splitEquiv d L W).apply_symm_apply y
  rw [svarF_eq_svar, hx, hy]

/-- The first large-deviation error of the mixture: `Q^{XX}_w - ∑_{k≠w} S^{mix}_{wk} G^{(w)}_{kk}`. -/
def GUEEntry_eps1 (G X : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a b : ℝ) (w : Vtx d L W) : ℂ :=
  GreenCore_Qxx G X w - ∑ k ∈ univ.erase w, ((GUEEntry_Smv d L W a b w k : ℝ) : ℂ) * greenMinor G w k k

theorem GUEEntry_eps1_sq (a b : ℝ) (w : Vtx d L W) :
    ‖GUEEntry_eps1 G X a b w‖ ^ 2 = ldeQuadLHS X G (GUEEntry_Smv d L W a b) 1 w := by
  unfold GUEEntry_eps1 ldeQuadLHS GreenCore_Qxx
  simp only [Complex.ofReal_one, one_mul]

/-- The a priori facts on `G` used by the large-deviation conversions: the diagonal lower bound, the entry bound
and the Ward bounds `∑_k |G_{ky}|² ≤ Y`, `∑_l |G_{xl}|² ≤ Y`. -/
structure GUEEntry_WardData (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (κ Y : ℝ) : Prop where
  hκ : 0 < κ
  hGuu : ∀ u, κ / 2 ≤ ‖G u u‖
  hG32 : ∀ u v, ‖G u v‖ ≤ 3 / 2
  hYc : ∀ y, ∑ k, ‖G k y‖ ^ 2 ≤ Y
  hYr : ∀ x, ∑ l, ‖G x l‖ ^ 2 ≤ Y

/-- `∑_{k≠u} |G^{(u)}_{ky}|² ≤ (2 + 18 κ⁻²) Y` (Ward column bound and the minor identity). -/
theorem GUEEntry_minor_col (hw : GUEEntry_WardData G κ Y) (u y : Vtx d L W) :
    ∑ k ∈ univ.erase u, ‖greenMinor G u k y‖ ^ 2 ≤ (2 + 18 / κ ^ 2) * Y := by
  have hY0 : 0 ≤ Y := (Finset.sum_nonneg fun _ _ => by positivity).trans (hw.hYc y)
  calc ∑ k ∈ univ.erase u, ‖greenMinor G u k y‖ ^ 2
      ≤ ∑ k ∈ univ.erase u, (2 * ‖G k y‖ ^ 2 + (8 / κ ^ 2) * (‖G k u‖ ^ 2 * ‖G u y‖ ^ 2)) :=
        Finset.sum_le_sum fun k _ => GreenCore_m1 hw.hκ (hw.hGuu u) k y
    _ ≤ ∑ k, (2 * ‖G k y‖ ^ 2 + (8 / κ ^ 2) * (‖G k u‖ ^ 2 * ‖G u y‖ ^ 2)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun k _ _ => by positivity
    _ = 2 * ∑ k, ‖G k y‖ ^ 2 + (8 / κ ^ 2) * ‖G u y‖ ^ 2 * ∑ k, ‖G k u‖ ^ 2 := by
        have e : ∑ k, (8 / κ ^ 2) * (‖G k u‖ ^ 2 * ‖G u y‖ ^ 2) = (8 / κ ^ 2) * ‖G u y‖ ^ 2 * ∑ k, ‖G k u‖ ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, e]
    _ ≤ 2 * Y + (8 / κ ^ 2) * (9 / 4) * Y := by
        have h1 : ‖G u y‖ ^ 2 ≤ 9 / 4 := by nlinarith [norm_nonneg (G u y), hw.hG32 u y]
        have h2 := hw.hYc u
        have h3 := hw.hYc y
        have h4 : (8 / κ ^ 2) * ‖G u y‖ ^ 2 * ∑ k, ‖G k u‖ ^ 2 ≤ (8 / κ ^ 2) * (9 / 4) * Y := by
          have := mul_le_mul (mul_le_mul_of_nonneg_left h1 (by have := hw.hκ; positivity : (0 : ℝ) ≤ 8 / κ ^ 2)) h2
            (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
          exact this
        linarith
    _ = (2 + 18 / κ ^ 2) * Y := by field_simp; ring

/-- `∑_{l≠u} |G^{(u)}_{xl}|² ≤ (2 + 18 κ⁻²) Y` (Ward row bound and the minor identity). -/
theorem GUEEntry_minor_row (hw : GUEEntry_WardData G κ Y) (u x : Vtx d L W) :
    ∑ l ∈ univ.erase u, ‖greenMinor G u x l‖ ^ 2 ≤ (2 + 18 / κ ^ 2) * Y := by
  have hY0 : 0 ≤ Y := (Finset.sum_nonneg fun _ _ => by positivity).trans (hw.hYc x)
  calc ∑ l ∈ univ.erase u, ‖greenMinor G u x l‖ ^ 2
      ≤ ∑ l ∈ univ.erase u, (2 * ‖G x l‖ ^ 2 + (8 / κ ^ 2) * (‖G x u‖ ^ 2 * ‖G u l‖ ^ 2)) :=
        Finset.sum_le_sum fun l _ => GreenCore_m1 hw.hκ (hw.hGuu u) x l
    _ ≤ ∑ l, (2 * ‖G x l‖ ^ 2 + (8 / κ ^ 2) * (‖G x u‖ ^ 2 * ‖G u l‖ ^ 2)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun l _ _ => by positivity
    _ = 2 * ∑ l, ‖G x l‖ ^ 2 + (8 / κ ^ 2) * ‖G x u‖ ^ 2 * ∑ l, ‖G u l‖ ^ 2 := by
        have e : ∑ l, (8 / κ ^ 2) * (‖G x u‖ ^ 2 * ‖G u l‖ ^ 2) = (8 / κ ^ 2) * ‖G x u‖ ^ 2 * ∑ l, ‖G u l‖ ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, e]
    _ ≤ 2 * Y + (8 / κ ^ 2) * (9 / 4) * Y := by
        have h1 : ‖G x u‖ ^ 2 ≤ 9 / 4 := by nlinarith [norm_nonneg (G x u), hw.hG32 x u]
        have h2 := hw.hYr u
        have h3 := hw.hYr x
        have h4 : (8 / κ ^ 2) * ‖G x u‖ ^ 2 * ∑ l, ‖G u l‖ ^ 2 ≤ (8 / κ ^ 2) * (9 / 4) * Y := by
          have := mul_le_mul (mul_le_mul_of_nonneg_left h1 (by have := hw.hκ; positivity : (0 : ℝ) ≤ 8 / κ ^ 2)) h2
            (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
          exact this
        linarith
    _ = (2 + 18 / κ ^ 2) * Y := by field_simp; ring

theorem GUEEntry_N_pos (d L W : ℕ) [NeZero L] [NeZero W] : (0 : ℝ) < (((W * L) ^ d : ℕ) : ℝ) := by
  have : 0 < W * L := Nat.mul_pos (NeZero.pos W) (NeZero.pos L)
  positivity

theorem GUEEntry_Smv_le (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : a + b < 1) (x y : Vtx d L W) :
    GUEEntry_Smv d L W a b x y ≤ svar d L W 0 x y + 1 / (((W * L) ^ d : ℕ) : ℝ) := by
  unfold GUEEntry_Smv
  have h0 : 0 ≤ svar d L W 0 x y := svar_nonneg d L W 0 x y
  have hN := GUEEntry_N_pos d L W
  have h1 : a * svar d L W 0 x y ≤ svar d L W 0 x y := by nlinarith
  have h2 : b / (((W * L) ^ d : ℕ) : ℝ) ≤ 1 / (((W * L) ^ d : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) hN.le
  linarith

theorem GUEEntry_Y_nonneg (hw : GUEEntry_WardData G κ Y) : 0 ≤ Y := by
  obtain ⟨y⟩ : Nonempty (Vtx d L W) := inferInstance
  exact (Finset.sum_nonneg fun _ _ => by positivity).trans (hw.hYc y)

/-- The row large deviation of the mixture in the block form plus the flat slack `Ξ`. -/
theorem GUEEntry_X_row (hw : GUEEntry_WardData G κ Y) {Ξ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : a + b < 1)
    (hΦ : 0 ≤ Φ) (hΞ : 3 * Φ * ((2 + 18 / κ ^ 2) * Y / (((W * L) ^ d : ℕ) : ℝ)) ≤ Ξ)
    (hLrow : LDERow X G (GUEEntry_Smv d L W a b) Φ) (u y : Vtx d L W) :
    ‖GreenCore_Xrow G X u y‖ ^ 2 ≤
      Φ * (2 * GreenCore_R G u.1 y + (8 / κ ^ 2) * ‖G u y‖ ^ 2 * GreenCore_R G u.1 u) + Ξ := by
  have hκ := hw.hκ
  have hu0 : G u u ≠ 0 := fun h => by have := hw.hGuu u; rw [h, norm_zero] at this; linarith
  have hY0 := GUEEntry_Y_nonneg hw
  have hN := GUEEntry_N_pos d L W
  have hc2 : 0 ≤ 2 + 18 / κ ^ 2 := by positivity
  have hΞ0 : 0 ≤ Ξ := le_trans (by positivity) hΞ
  have hR0 : ∀ a' (y' : Vtx d L W), 0 ≤ GreenCore_R G a' y' := fun a' y' =>
    mul_nonneg GreenCore_w_pos.le (Finset.sum_nonneg fun _ _ => by positivity)
  by_cases hyu : y = u
  · subst hyu
    rw [show GreenCore_Xrow G X y y = 0 from Finset.sum_eq_zero fun v _ => by
      rw [GreenCore_minor_right hu0, mul_zero], norm_zero, zero_pow two_ne_zero]
    have := hR0 y.1 y
    have := hR0 y.1 y
    positivity
  · have h1 := hLrow u y (Ne.symm hyu)
    have e1 : ldeRowLHS X G u y = ‖GreenCore_Xrow G X u y‖ ^ 2 := rfl
    rw [e1] at h1
    have h2 : ldeRowRHS (GUEEntry_Smv d L W a b) G u y ≤
        ldeRowRHS (svar d L W 0) G u y + 1 / (((W * L) ^ d : ℕ) : ℝ) * ((2 + 18 / κ ^ 2) * Y) := by
      calc ldeRowRHS (GUEEntry_Smv d L W a b) G u y
          ≤ ∑ k ∈ univ.erase u, (svar d L W 0 u k * ‖greenMinor G u k y‖ ^ 2 +
              1 / (((W * L) ^ d : ℕ) : ℝ) * ‖greenMinor G u k y‖ ^ 2) :=
            Finset.sum_le_sum fun k _ => by
              rw [← add_mul]
              exact mul_le_mul_of_nonneg_right (GUEEntry_Smv_le ha hb hu u k) (sq_nonneg _)
        _ = ldeRowRHS (svar d L W 0) G u y + 1 / (((W * L) ^ d : ℕ) : ℝ) * ∑ k ∈ univ.erase u, ‖greenMinor G u k y‖ ^ 2 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]; rfl
        _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
            (GUEEntry_minor_col hw u y) (by positivity))
    have h3 : ldeRowRHS (svar d L W 0) G u y ≤ 2 * GreenCore_R G u.1 y + (8 / κ ^ 2) * ‖G u y‖ ^ 2 * GreenCore_R G u.1 u := by
      rw [GreenCore_ldeRowRHS hu0]
      exact GreenCore_blockMinorRow hκ (hw.hGuu u) y
    have h4 : Φ * (1 / (((W * L) ^ d : ℕ) : ℝ) * ((2 + 18 / κ ^ 2) * Y)) ≤ Ξ := by
      refine le_trans ?_ hΞ
      have : Φ * (1 / (((W * L) ^ d : ℕ) : ℝ) * ((2 + 18 / κ ^ 2) * Y)) = Φ * ((2 + 18 / κ ^ 2) * Y / (((W * L) ^ d : ℕ) : ℝ)) := by
        field_simp
      rw [this]
      have : 0 ≤ Φ * ((2 + 18 / κ ^ 2) * Y / (((W * L) ^ d : ℕ) : ℝ)) := by positivity
      nlinarith
    calc ‖GreenCore_Xrow G X u y‖ ^ 2 ≤ Φ * ldeRowRHS (GUEEntry_Smv d L W a b) G u y := h1
      _ ≤ Φ * (ldeRowRHS (svar d L W 0) G u y + 1 / (((W * L) ^ d : ℕ) : ℝ) * ((2 + 18 / κ ^ 2) * Y)) :=
          mul_le_mul_of_nonneg_left h2 hΦ
      _ ≤ Φ * (2 * GreenCore_R G u.1 y + (8 / κ ^ 2) * ‖G u y‖ ^ 2 * GreenCore_R G u.1 u) +
          Φ * (1 / (((W * L) ^ d : ℕ) : ℝ) * ((2 + 18 / κ ^ 2) * Y)) := by
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left (add_le_add h3 le_rfl) hΦ
      _ ≤ _ := add_le_add le_rfl h4

/-- The column large deviation of the mixture in the block form plus the flat slack `Ξ`. -/
theorem GUEEntry_X_col (hw : GUEEntry_WardData G κ Y) {Ξ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : a + b < 1)
    (hΦ : 0 ≤ Φ) (hΞ : 3 * Φ * ((2 + 18 / κ ^ 2) * Y / (((W * L) ^ d : ℕ) : ℝ)) ≤ Ξ)
    (hLcol : LDECol X G (GUEEntry_Smv d L W a b) Φ) (x w : Vtx d L W) :
    ‖GreenCore_Xcol G X x w‖ ^ 2 ≤
      Φ * (2 * GreenCore_Rrow G x w.1 + (8 / κ ^ 2) * ‖G x w‖ ^ 2 * GreenCore_Rrow G w w.1) + Ξ := by
  have hκ := hw.hκ
  have hw0 : G w w ≠ 0 := fun h => by have := hw.hGuu w; rw [h, norm_zero] at this; linarith
  have hY0 := GUEEntry_Y_nonneg hw
  have hN := GUEEntry_N_pos d L W
  have hc2 : 0 ≤ 2 + 18 / κ ^ 2 := by positivity
  have hΞ0 : 0 ≤ Ξ := le_trans (by positivity) hΞ
  have hR0 : ∀ (x' : Vtx d L W) b', 0 ≤ GreenCore_Rrow G x' b' := fun x' b' =>
    mul_nonneg GreenCore_w_pos.le (Finset.sum_nonneg fun _ _ => by positivity)
  by_cases hxw : x = w
  · subst hxw
    rw [show GreenCore_Xcol G X x x = 0 from Finset.sum_eq_zero fun v _ => by
      rw [GreenCore_minor_left hw0, zero_mul], norm_zero, zero_pow two_ne_zero]
    have := hR0 x x.1
    have := hR0 x x.1
    positivity
  · have h1 := hLcol x w hxw
    have e1 : ldeColLHS X G x w = ‖GreenCore_Xcol G X x w‖ ^ 2 := rfl
    rw [e1] at h1
    have h2 : ldeColRHS (GUEEntry_Smv d L W a b) G x w ≤
        ldeColRHS (svar d L W 0) G x w + 1 / (((W * L) ^ d : ℕ) : ℝ) * ((2 + 18 / κ ^ 2) * Y) := by
      calc ldeColRHS (GUEEntry_Smv d L W a b) G x w
          ≤ ∑ l ∈ univ.erase w, (‖greenMinor G w x l‖ ^ 2 * svar d L W 0 l w +
              1 / (((W * L) ^ d : ℕ) : ℝ) * ‖greenMinor G w x l‖ ^ 2) :=
            Finset.sum_le_sum fun l _ => by
              have := mul_le_mul_of_nonneg_left (GUEEntry_Smv_le ha hb hu l w) (sq_nonneg ‖greenMinor G w x l‖)
              linarith
        _ = ldeColRHS (svar d L W 0) G x w + 1 / (((W * L) ^ d : ℕ) : ℝ) * ∑ l ∈ univ.erase w, ‖greenMinor G w x l‖ ^ 2 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]; rfl
        _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
            (GUEEntry_minor_row hw w x) (by positivity))
    have h3 : ldeColRHS (svar d L W 0) G x w ≤ 2 * GreenCore_Rrow G x w.1 + (8 / κ ^ 2) * ‖G x w‖ ^ 2 * GreenCore_Rrow G w w.1 := by
      rw [GreenCore_ldeColRHS hw0]
      exact GreenCore_blockMinorCol hκ (hw.hGuu w) x
    have h4 : Φ * (1 / (((W * L) ^ d : ℕ) : ℝ) * ((2 + 18 / κ ^ 2) * Y)) ≤ Ξ := by
      refine le_trans ?_ hΞ
      have : Φ * (1 / (((W * L) ^ d : ℕ) : ℝ) * ((2 + 18 / κ ^ 2) * Y)) = Φ * ((2 + 18 / κ ^ 2) * Y / (((W * L) ^ d : ℕ) : ℝ)) := by
        field_simp
      rw [this]
      have : 0 ≤ Φ * ((2 + 18 / κ ^ 2) * Y / (((W * L) ^ d : ℕ) : ℝ)) := by positivity
      nlinarith
    calc ‖GreenCore_Xcol G X x w‖ ^ 2 ≤ Φ * ldeColRHS (GUEEntry_Smv d L W a b) G x w := h1
      _ ≤ Φ * (ldeColRHS (svar d L W 0) G x w + 1 / (((W * L) ^ d : ℕ) : ℝ) * ((2 + 18 / κ ^ 2) * Y)) :=
          mul_le_mul_of_nonneg_left h2 hΦ
      _ ≤ Φ * (2 * GreenCore_Rrow G x w.1 + (8 / κ ^ 2) * ‖G x w‖ ^ 2 * GreenCore_Rrow G w w.1) +
          Φ * (1 / (((W * L) ^ d : ℕ) : ℝ) * ((2 + 18 / κ ^ 2) * Y)) := by
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left (add_le_add h3 le_rfl) hΦ
      _ ≤ _ := add_le_add le_rfl h4

/-- The block quadratic proxy: `∑ S^{(B)}_{wk} |G^{(w)}_{kl}|² S^{(B)}_{lw} ≤ 2 𝓛_{[w],[w]} + 8 κ⁻² R R^{row}`. -/
theorem GUEEntry_quadRHS_block (hκ : 0 < κ) (hGuu : ∀ u, κ / 2 ≤ ‖G u u‖) (w : Vtx d L W) :
    ldeQuadRHS (svar d L W 0) G w ≤
      2 * GreenCore_loop G w.1 w.1 + (8 / κ ^ 2) * GreenCore_R G w.1 w * GreenCore_Rrow G w w.1 := by
  have hw0 : G w w ≠ 0 := fun h => by have := hGuu w; rw [h, norm_zero] at this; linarith
  rw [GreenCore_ldeQuadRHS hw0]
  calc (((W : ℝ) ^ d)⁻¹) ^ 2 * ∑ o, ∑ o', ‖greenMinor G w (w.1, o) (w.1, o')‖ ^ 2
      ≤ (((W : ℝ) ^ d)⁻¹) ^ 2 * ∑ o, ∑ o', (2 * ‖G (w.1, o) (w.1, o')‖ ^ 2 +
          (8 / κ ^ 2) * (‖G (w.1, o) w‖ ^ 2 * ‖G w (w.1, o')‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun o _ => Finset.sum_le_sum fun o' _ =>
          GreenCore_m1 hκ (hGuu w) _ _) (sq_nonneg _)
    _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        unfold GreenCore_loop GreenCore_R GreenCore_Rrow
        ring

theorem GUEEntry_quadRHS_flat (hw : GUEEntry_WardData G κ Y) (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : a + b < 1)
    (w : Vtx d L W) :
    ldeQuadRHS (GUEEntry_Smv d L W a b) G w ≤
      ldeQuadRHS (svar d L W 0) G w + 3 * ((2 + 18 / κ ^ 2) * Y / (((W * L) ^ d : ℕ) : ℝ)) := by
  have hκ := hw.hκ
  have hY0 := GUEEntry_Y_nonneg hw
  have hN := GUEEntry_N_pos d L W
  set β : ℝ := 1 / (((W * L) ^ d : ℕ) : ℝ) with hβ
  set c : ℝ := (2 + 18 / κ ^ 2) * Y with hc
  have hc0 : 0 ≤ c := by positivity
  have hβ0 : 0 ≤ β := by positivity
  set E := (univ : Finset (Vtx d L W)).erase w with hE
  have hs0 : ∀ k, 0 ≤ svar d L W 0 w k := fun k => svar_nonneg d L W 0 w k
  have hq0 : ∀ k l, 0 ≤ ‖greenMinor G w k l‖ ^ 2 := fun k l => sq_nonneg _
  have hsum1 : ∑ k ∈ E, svar d L W 0 w k ≤ 1 := by
    have h := GreenCore_sum_block w (fun _ => (1 : ℝ))
    simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    calc ∑ k ∈ E, svar d L W 0 w k ≤ ∑ k, svar d L W 0 w k :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun k _ _ => hs0 k
      _ = 1 := by rw [h]; push_cast; exact GreenCore_w_mul
  have hsum1' : ∑ l ∈ E, svar d L W 0 l w ≤ 1 := by
    calc ∑ l ∈ E, svar d L W 0 l w = ∑ l ∈ E, svar d L W 0 w l := Finset.sum_congr rfl fun l _ => svar_comm d L W 0 l w
      _ ≤ 1 := hsum1
  have hrowq : ∀ k, ∑ l ∈ E, ‖greenMinor G w k l‖ ^ 2 ≤ c := fun k => GUEEntry_minor_row hw w k
  have hcolq : ∀ l, ∑ k ∈ E, ‖greenMinor G w k l‖ ^ 2 ≤ c := fun l => GUEEntry_minor_col hw w l
  have hT1 : ∑ k ∈ E, ∑ l ∈ E, svar d L W 0 w k * ‖greenMinor G w k l‖ ^ 2 ≤ c := by
    calc _ = ∑ k ∈ E, svar d L W 0 w k * ∑ l ∈ E, ‖greenMinor G w k l‖ ^ 2 := by
          simp only [Finset.mul_sum]
      _ ≤ ∑ k ∈ E, svar d L W 0 w k * c := Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hrowq k) (hs0 k)
      _ = (∑ k ∈ E, svar d L W 0 w k) * c := by rw [Finset.sum_mul]
      _ ≤ 1 * c := mul_le_mul_of_nonneg_right hsum1 hc0
      _ = c := one_mul c
  have hT2 : ∑ k ∈ E, ∑ l ∈ E, ‖greenMinor G w k l‖ ^ 2 * svar d L W 0 l w ≤ c := by
    calc _ = ∑ l ∈ E, (∑ k ∈ E, ‖greenMinor G w k l‖ ^ 2) * svar d L W 0 l w := by
          rw [Finset.sum_comm]; simp only [Finset.sum_mul]
      _ ≤ ∑ l ∈ E, c * svar d L W 0 l w := Finset.sum_le_sum fun l _ =>
          mul_le_mul_of_nonneg_right (hcolq l) (svar_nonneg d L W 0 l w)
      _ = c * ∑ l ∈ E, svar d L W 0 l w := by rw [Finset.mul_sum]
      _ ≤ c * 1 := mul_le_mul_of_nonneg_left hsum1' hc0
      _ = c := mul_one c
  have hT3 : ∑ k ∈ E, ∑ l ∈ E, ‖greenMinor G w k l‖ ^ 2 ≤ (((W * L) ^ d : ℕ) : ℝ) * c := by
    calc _ ≤ ∑ _k ∈ E, c := Finset.sum_le_sum fun k _ => hrowq k
      _ = (E.card : ℝ) * c := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (((W * L) ^ d : ℕ) : ℝ) * c := by
          refine mul_le_mul_of_nonneg_right ?_ hc0
          calc (E.card : ℝ) ≤ (Fintype.card (Vtx d L W) : ℝ) := by
                exact_mod_cast (Finset.card_erase_le.trans (le_of_eq Finset.card_univ))
            _ = _ := EntryDet_card_vtx_real d L W
  calc ldeQuadRHS (GUEEntry_Smv d L W a b) G w
      ≤ ∑ k ∈ E, ∑ l ∈ E, (svar d L W 0 w k + β) * ‖greenMinor G w k l‖ ^ 2 * (svar d L W 0 l w + β) := by
        refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
        have h1 := GUEEntry_Smv_le ha hb hu w k
        have h2 := GUEEntry_Smv_le ha hb hu l w
        have h1' : 0 ≤ GUEEntry_Smv d L W a b w k := by
          unfold GUEEntry_Smv; have := hs0 k; positivity
        have h2' : 0 ≤ GUEEntry_Smv d L W a b l w := by
          unfold GUEEntry_Smv; have := svar_nonneg d L W 0 l w; positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_right h1 (hq0 k l)) h2 h2' (by
          have := hs0 k; positivity)
    _ = ldeQuadRHS (svar d L W 0) G w + β * ∑ k ∈ E, ∑ l ∈ E, svar d L W 0 w k * ‖greenMinor G w k l‖ ^ 2 +
          β * ∑ k ∈ E, ∑ l ∈ E, ‖greenMinor G w k l‖ ^ 2 * svar d L W 0 l w +
          β ^ 2 * ∑ k ∈ E, ∑ l ∈ E, ‖greenMinor G w k l‖ ^ 2 := by
        have hp : ∀ k l, (svar d L W 0 w k + β) * ‖greenMinor G w k l‖ ^ 2 * (svar d L W 0 l w + β) =
            svar d L W 0 w k * ‖greenMinor G w k l‖ ^ 2 * svar d L W 0 l w +
              β * (svar d L W 0 w k * ‖greenMinor G w k l‖ ^ 2) +
              β * (‖greenMinor G w k l‖ ^ 2 * svar d L W 0 l w) + β ^ 2 * ‖greenMinor G w k l‖ ^ 2 :=
          fun k l => by ring
        unfold ldeQuadRHS
        simp only [hp, Finset.sum_add_distrib, ← Finset.mul_sum]
        rfl
    _ ≤ ldeQuadRHS (svar d L W 0) G w + β * c + β * c + β ^ 2 * ((((W * L) ^ d : ℕ) : ℝ) * c) := by
        gcongr
    _ = ldeQuadRHS (svar d L W 0) G w + 3 * ((2 + 18 / κ ^ 2) * Y / (((W * L) ^ d : ℕ) : ℝ)) := by
        rw [hβ, hc]; field_simp; ring

theorem GUEEntry_eps1_loc (hw : GUEEntry_WardData G κ Y) {Ξ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : a + b < 1)
    (hΦ : 0 ≤ Φ) (hΞ : 3 * Φ * ((2 + 18 / κ ^ 2) * Y / (((W * L) ^ d : ℕ) : ℝ)) ≤ Ξ)
    (hLquad : LDEQuad X G (GUEEntry_Smv d L W a b) 1 Φ) (w : Vtx d L W) :
    ‖GUEEntry_eps1 G X a b w‖ ^ 2 ≤
      Φ * (2 * GreenCore_loop G w.1 w.1 + (8 / κ ^ 2) * GreenCore_R G w.1 w * GreenCore_Rrow G w w.1) + Ξ := by
  rw [GUEEntry_eps1_sq]
  refine (hLquad w).trans ?_
  calc Φ * ldeQuadRHS (GUEEntry_Smv d L W a b) G w
      ≤ Φ * (ldeQuadRHS (svar d L W 0) G w + 3 * ((2 + 18 / κ ^ 2) * Y / (((W * L) ^ d : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left (GUEEntry_quadRHS_flat hw ha hb hu w) hΦ
    _ = Φ * ldeQuadRHS (svar d L W 0) G w + 3 * Φ * ((2 + 18 / κ ^ 2) * Y / (((W * L) ^ d : ℕ) : ℝ)) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (GUEEntry_quadRHS_block hw.hκ hw.hGuu w) hΦ) hΞ

/-- `G` is the resolvent `green H z` when `G (H - z) = 1`. -/
theorem GUEEntry_G_eq_green {H G : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ}
    (hGR : G * (H - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1) : G = green H z := by
  unfold green
  exact (Matrix.inv_eq_left_inv hGR).symm

/-- The Ward bounds with `Y = (3/2)/Im z` from `‖G_{xx}‖ ≤ 3/2` (`ward_col`, `ward_row`). -/
theorem GUEEntry_wardData_of {H G : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ} (hκ : 0 < κ)
    (hH : H.IsHermitian) (hz : 0 < z.im) (hGR : G * (H - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1)
    (hGuu : ∀ u, κ / 2 ≤ ‖G u u‖) (hG32 : ∀ u v, ‖G u v‖ ≤ 3 / 2) :
    GUEEntry_WardData G κ ((3 / 2) / z.im) := by
  have e := GUEEntry_G_eq_green hGR
  have him : ∀ i, (G i i).im ≤ 3 / 2 := fun i =>
    (Complex.im_le_norm _).trans (hG32 i i)
  refine ⟨hκ, hGuu, hG32, fun y => ?_, fun x => ?_⟩
  · rw [e, ward_col hH hz.ne' y]
    have := him y
    rw [← e] at *
    exact div_le_div_of_nonneg_right this hz.le
  · rw [e, ward_row hH hz.ne' x]
    have := him x
    rw [← e] at *
    exact div_le_div_of_nonneg_right this hz.le

/-- **The `J`-part lemma** (Ward over one block row): `Y/N = (3/2)/(N η) ≤ 3 κ⁻¹ max 𝓛` (the block Anderson version of
`inv_N_le_maxLoopPM`, at the block Anderson `M`). -/
theorem GUEEntry_J {H G M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z m : ℂ} {δ Lm : ℝ}
    (hH : H.IsHermitian) (hz : 0 < z.im) (hGR : G * (H - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1)
    (hMxx : ∀ x, M x x = m) (hκ : 0 < κ) (hmim : κ ≤ m.im) (hδ : δ ≤ κ / 2)
    (hΩ : ∀ u v, ‖G u v - M u v‖ ≤ δ) (hLm : ∀ a b, GreenCore_loop G a b ≤ Lm) :
    (3 / 2) / z.im / (((W * L) ^ d : ℕ) : ℝ) ≤ 3 / κ * Lm := by
  have e := GUEEntry_G_eq_green hGR
  have hN := GUEEntry_N_pos d L W
  have hw := GreenCore_w_pos (d := d) (W := W)
  have hLm0 : 0 ≤ Lm := (by
    have : 0 ≤ GreenCore_loop G 0 0 := mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
    exact this.trans (hLm 0 0))
  have himm : ∀ x, m.im / 2 ≤ (G x x).im := fun x => by
    have h1 := hΩ x x
    rw [hMxx] at h1
    have h2 : |(G x x - m).im| ≤ ‖G x x - m‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im] at h2
    have := neg_abs_le ((G x x).im - m.im)
    linarith
  set a₀ : Zd d L := 0
  have hs : ∑ b : Zd d L, GreenCore_loop G a₀ b =
      (((W : ℝ) ^ d)⁻¹) ^ 2 * ∑ o : Fin (W ^ d), (G (a₀, o) (a₀, o)).im / z.im := by
    unfold GreenCore_loop
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun o _ => ?_
    have h := ward_row hH hz.ne' (a₀, o)
    rw [← e] at h
    rw [← h, Fintype.sum_prod_type]
  have hsumlow : ((W : ℝ) ^ d) * (m.im / 2 / z.im) ≤ ∑ o : Fin (W ^ d), (G (a₀, o) (a₀, o)).im / z.im := by
    calc ((W : ℝ) ^ d) * (m.im / 2 / z.im) = ∑ _o : Fin (W ^ d), m.im / 2 / z.im := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
      _ ≤ _ := Finset.sum_le_sum fun o _ => div_le_div_of_nonneg_right (himm _) hz.le
  have hup : ∑ b : Zd d L, GreenCore_loop G a₀ b ≤ (L : ℝ) ^ d * Lm := by
    calc _ ≤ ∑ _b : Zd d L, Lm := Finset.sum_le_sum fun b _ => hLm a₀ b
      _ = (L : ℝ) ^ d * Lm := by
          rw [Finset.sum_const, Finset.card_univ, BAcard_Zd, nsmul_eq_mul]; push_cast; ring
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := pow_pos (Nat.cast_pos.2 (NeZero.pos W)) d
  have hLd : (0 : ℝ) < (L : ℝ) ^ d := pow_pos (Nat.cast_pos.2 (NeZero.pos L)) d
  have h1 : m.im / 2 / z.im ≤ (W : ℝ) ^ d * (L : ℝ) ^ d * Lm := by
    have h2 : (((W : ℝ) ^ d)⁻¹) ^ 2 * ((W : ℝ) ^ d * (m.im / 2 / z.im)) ≤ (L : ℝ) ^ d * Lm := by
      calc _ ≤ (((W : ℝ) ^ d)⁻¹) ^ 2 * ∑ o : Fin (W ^ d), (G (a₀, o) (a₀, o)).im / z.im :=
            mul_le_mul_of_nonneg_left hsumlow (by positivity)
        _ = ∑ b : Zd d L, GreenCore_loop G a₀ b := hs.symm
        _ ≤ _ := hup
    have h3 : (((W : ℝ) ^ d)⁻¹) ^ 2 * ((W : ℝ) ^ d * (m.im / 2 / z.im)) = ((W : ℝ) ^ d)⁻¹ * (m.im / 2 / z.im) := by
      field_simp
    rw [h3, inv_mul_le_iff₀ hWd] at h2
    calc m.im / 2 / z.im ≤ (W : ℝ) ^ d * ((L : ℝ) ^ d * Lm) := h2
      _ = _ := by ring
  have hNc : (((W * L) ^ d : ℕ) : ℝ) = (W : ℝ) ^ d * (L : ℝ) ^ d := by push_cast; ring
  rw [hNc, div_le_iff₀ (mul_pos hWd hLd)]
  have hmpos : 0 < m.im := lt_of_lt_of_le hκ hmim
  have h4 : 1 / (2 * z.im) ≤ ((W : ℝ) ^ d * (L : ℝ) ^ d * Lm) / κ := by
    have : m.im / 2 / z.im = m.im * (1 / (2 * z.im)) := by field_simp
    rw [this] at h1
    rw [le_div_iff₀ hκ]
    have h5 : κ * (1 / (2 * z.im)) ≤ m.im * (1 / (2 * z.im)) :=
      mul_le_mul_of_nonneg_right hmim (by positivity)
    nlinarith
  calc (3 / 2) / z.im = 3 * (1 / (2 * z.im)) := by field_simp
    _ ≤ 3 * (((W : ℝ) ^ d * (L : ℝ) ^ d * Lm) / κ) := by linarith
    _ = 3 / κ * Lm * ((W : ℝ) ^ d * (L : ℝ) ^ d) := by field_simp

end Slack


section Mix
variable {d L W : ℕ} [NeZero L] [NeZero W] {G X M D : Matrix (Vtx d L W) (Vtx d L W) ℂ}
  {Mb : Matrix (Zd d L) (Zd d L) ℂ} {m : ℂ} {a b κ Y : ℝ}

/-- `w̄ = L^{-d} ∑_a v̄_a = N⁻¹ tr (G - M)`: the flat self-energy. -/
def GUEEntry_wbar (G M : Matrix (Vtx d L W) (Vtx d L W) ℂ) : ℂ :=
  (((L ^ d : ℕ) : ℂ))⁻¹ * ∑ a : Zd d L, GreenCore_vbar G M a

/-- `e₃ = N⁻¹ ∑_k G_{ku} G_{uk} / G_{uu}`: the flat minor correction. -/
def GUEEntry_e3 (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (u : Vtx d L W) : ℂ :=
  ((((W * L) ^ d : ℕ) : ℝ) : ℂ)⁻¹ * ∑ k, G k u * G u k / G u u

theorem GUEEntry_flat_sum (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0)
    (hMd : ∀ a, Mb a a = m) {w : Vtx d L W} (hw : G w w ≠ 0) :
    ((((W * L) ^ d : ℕ) : ℝ) : ℂ)⁻¹ * ∑ k ∈ univ.erase w, greenMinor G w k k =
      m + GUEEntry_wbar G M - GUEEntry_e3 G w := by
  have hWd : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W))
  have hLd : ((L : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne L))
  have hNc : ((((W * L) ^ d : ℕ) : ℝ) : ℂ) = ((W : ℂ) ^ d) * ((L : ℂ) ^ d) := by push_cast; ring
  have hN0 : ((((W * L) ^ d : ℕ) : ℝ) : ℂ) ≠ 0 := by rw [hNc]; exact mul_ne_zero hWd hLd
  have hMkk : ∀ k : Vtx d L W, M k k = m := fun k => by simp [hM, hMd]
  have h1 : ∑ k ∈ univ.erase w, greenMinor G w k k = ∑ k, greenMinor G w k k :=
    Finset.sum_erase _ (GreenCore_minor_left hw w)
  have h2 : ∑ k, greenMinor G w k k = ∑ k, G k k - ∑ k, G k w * G w k / G w w := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [greenMinor]
  have h3 : ∑ k, G k k = ((((W * L) ^ d : ℕ) : ℝ) : ℂ) * m + ∑ k, (G k k - M k k) := by
    have : ∑ k, G k k = ∑ k, (m + (G k k - M k k)) :=
      Finset.sum_congr rfl fun k _ => by rw [← hMkk k]; ring
    have hcard : ((Fintype.card (Vtx d L W) : ℕ) : ℂ) = ((((W * L) ^ d : ℕ) : ℝ) : ℂ) := by
      rw [← EntryDet_card_vtx_real d L W]; simp
    rw [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  have h4 : ∑ k, (G k k - M k k) = ((W : ℂ) ^ d) * ((L : ℂ) ^ d) * GUEEntry_wbar G M := by
    have hv : ∀ a : Zd d L, ∑ o : Fin (W ^ d), (G (a, o) (a, o) - M (a, o) (a, o)) = ((W : ℂ) ^ d) * GreenCore_vbar G M a := by
      intro a
      unfold GreenCore_vbar
      rw [← mul_assoc, show ((W : ℂ) ^ d) * ((((W : ℝ) ^ d)⁻¹ : ℝ) : ℂ) = 1 by
        push_cast; field_simp, one_mul]
    rw [Fintype.sum_prod_type]
    simp only [hv, ← Finset.mul_sum]
    unfold GUEEntry_wbar
    have hLd' : (((L ^ d : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast pow_ne_zero d (NeZero.ne L)
    rw [show ((L : ℂ) ^ d) = (((L ^ d : ℕ) : ℂ)) by push_cast; ring]
    field_simp
  rw [h1, h2, h3, h4, hNc]
  unfold GUEEntry_e3
  rw [hNc]
  field_simp

/-- **(E2) at the mixture**: `A_u + a v̄_{[u]} + b w̄ = a e₂ + b e₃ - ε₁ + X_{uu} - Q^{XD}_u`. -/
theorem GUEEntry_A_eq (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0)
    (hMd : ∀ a, Mb a a = m) {w : Vtx d L W} (hw : G w w ≠ 0) :
    GreenCore_Arow G X D (a + b) m w + (a : ℂ) * GreenCore_vbar G M w.1 + (b : ℂ) * GUEEntry_wbar G M =
      GreenCore_eps2 G a w + (b : ℂ) * GUEEntry_e3 G w - GUEEntry_eps1 G X a b w + X w w -
        GreenCore_Qxd G X D w := by
  have hQ : ∑ k ∈ univ.erase w, ∑ l ∈ univ.erase w, X w k * greenMinor G w k l * (D + X) l w =
      GreenCore_Qxx G X w + GreenCore_Qxd G X D w := by
    unfold GreenCore_Qxx GreenCore_Qxd
    rw [add_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.add_apply]; ring
  have hS : ∑ k ∈ univ.erase w, ((GUEEntry_Smv d L W a b w k : ℝ) : ℂ) * greenMinor G w k k =
      (a : ℂ) * ∑ k ∈ univ.erase w, ((svar d L W 0 w k : ℝ) : ℂ) * greenMinor G w k k +
        (b : ℂ) * (((((W * L) ^ d : ℕ) : ℝ) : ℂ)⁻¹ * ∑ k ∈ univ.erase w, greenMinor G w k k) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold GUEEntry_Smv
    push_cast
    ring
  have hB := GreenCore_Bsum hM hMd hw
  have hF := GUEEntry_flat_sum (G := G) hM hMd hw
  unfold GreenCore_Arow GUEEntry_eps1 GreenCore_eps2
  rw [hQ, hS, hB, hF]
  push_cast
  ring

theorem GUEEntry_e3_norm (hw : GUEEntry_WardData G κ Y) (hb : 0 ≤ b) (hb1 : b ≤ 1) (u : Vtx d L W) :
    ‖(b : ℂ) * GUEEntry_e3 G u‖ ≤ (2 / κ) * (Y / (((W * L) ^ d : ℕ) : ℝ)) := by
  have hκ := hw.hκ
  have hN := GUEEntry_N_pos d L W
  have hu : 0 < ‖G u u‖ := lt_of_lt_of_le (by positivity) (hw.hGuu u)
  have hY0 := GUEEntry_Y_nonneg hw
  have hsum : ∑ k, ‖G k u‖ * ‖G u k‖ ≤ Y := by
    calc ∑ k, ‖G k u‖ * ‖G u k‖ ≤ ∑ k, (‖G k u‖ ^ 2 + ‖G u k‖ ^ 2) / 2 :=
          Finset.sum_le_sum fun k _ => by nlinarith [sq_nonneg (‖G k u‖ - ‖G u k‖)]
      _ = (∑ k, ‖G k u‖ ^ 2 + ∑ k, ‖G u k‖ ^ 2) / 2 := by
          rw [← Finset.sum_div, Finset.sum_add_distrib]
      _ ≤ (Y + Y) / 2 := by
          have := hw.hYc u; have := hw.hYr u; linarith
      _ = Y := by ring
  have h1 : ‖∑ k, G k u * G u k / G u u‖ ≤ (2 / κ) * Y := by
    calc ‖∑ k, G k u * G u k / G u u‖ ≤ ∑ k, ‖G k u * G u k / G u u‖ := norm_sum_le _ _
      _ = (∑ k, ‖G k u‖ * ‖G u k‖) / ‖G u u‖ := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun k _ => by rw [norm_div, norm_mul]
      _ ≤ (∑ k, ‖G k u‖ * ‖G u k‖) / (κ / 2) :=
          div_le_div_of_nonneg_left (Finset.sum_nonneg fun _ _ => by positivity) (by positivity) (hw.hGuu u)
      _ ≤ Y / (κ / 2) := div_le_div_of_nonneg_right hsum (by positivity)
      _ = (2 / κ) * Y := by field_simp
  unfold GUEEntry_e3
  rw [← mul_assoc, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg hN.le]
  calc b * (((W * L) ^ d : ℕ) : ℝ)⁻¹ * ‖∑ k, G k u * G u k / G u u‖
      ≤ 1 * (((W * L) ^ d : ℕ) : ℝ)⁻¹ * ((2 / κ) * Y) := by
        gcongr
    _ = (2 / κ) * (Y / (((W * L) ^ d : ℕ) : ℝ)) := by field_simp

/-- **The mixture analogue of `GreenCore_coupled`**: `Δ = M 𝒮 M + M 𝒦` with the self-energy `𝒮 = a v̄ + b w̄`, the
stability being `stable_mixBA`; `‖Δ‖_max ≤ ρ (1 + ρ₂ K_θ) ‖𝒦‖_max`. -/
theorem GUEEntry_coupled {Δ 𝒦 : Vtx d L W → Vtx d L W → ℂ} {vb : Zd d L → ℂ} {wb : ℂ} {Kθ ρ ρ₂ K𝒦 : ℝ}
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1)
    (hKθ : 0 ≤ Kθ) (hρ : ∀ a, ∑ b, ‖Mb a b‖ ≤ ρ) (hρ₂ : ∀ a c, ∑ b, ‖Mb a b‖ * ‖Mb b c‖ ≤ ρ₂)
    (hv : ∀ x, vb x = (((W : ℝ) ^ d)⁻¹ : ℝ) * ∑ o, Δ (x, o) (x, o))
    (hwb : wb = (((L ^ d : ℕ) : ℂ))⁻¹ * ∑ c, vb c)
    (hE3 : ∀ x y, Δ x y = ∑ b', Mb x.1 b' * (((a : ℂ) * vb b' + (b : ℂ) * wb) * M (b', x.2) y) +
      ∑ b', Mb x.1 b' * 𝒦 (b', x.2) y)
    (hstab : ∀ (v : Zd d L → ℂ) (B : ℝ), (∀ x, ‖v x - ∑ y, (Mb y x * Mb x y) *
      ((a : ℂ) * v y + (b : ℂ) * ((((L ^ d : ℕ) : ℂ))⁻¹ * ∑ z, v z))‖ ≤ B) → ∀ x, ‖v x‖ ≤ Kθ * B)
    (hK : ∀ u y, ‖𝒦 u y‖ ≤ K𝒦) (x y : Vtx d L W) : ‖Δ x y‖ ≤ ρ * (1 + ρ₂ * Kθ) * K𝒦 := by
  have hw := GreenCore_w_pos (d := d) (W := W)
  have hK0 : 0 ≤ K𝒦 := le_trans (norm_nonneg _) (hK x y)
  have hρ0 : 0 ≤ ρ := le_trans (Finset.sum_nonneg fun b _ => norm_nonneg _) (hρ 0)
  have hM' : ∀ (b' a : Zd d L) (o : Fin (W ^ d)), M (b', o) (a, o) = Mb b' a := fun b' a o => by simp [hM]
  have hbar : ∀ a', vb a' - ∑ y, (Mb y a' * Mb a' y) * ((a : ℂ) * vb y + (b : ℂ) * wb) =
      (((W : ℝ) ^ d)⁻¹ : ℝ) * ∑ o, ∑ b', Mb a' b' * 𝒦 (b', o) (a', o) := by
    intro a'
    have h1 : ∀ o : Fin (W ^ d), Δ (a', o) (a', o) = ∑ y, (Mb y a' * Mb a' y) * ((a : ℂ) * vb y + (b : ℂ) * wb) +
        ∑ b', Mb a' b' * 𝒦 (b', o) (a', o) := by
      intro o
      rw [hE3 (a', o) (a', o)]
      congr 1
      exact Finset.sum_congr rfl fun y _ => by simp only [hM']; ring
    rw [hv a']
    simp only [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (((W : ℝ) ^ d)⁻¹ : ℝ) * (((W ^ d : ℕ) : ℂ) * ∑ y, (Mb y a' * Mb a' y) * ((a : ℂ) * vb y + (b : ℂ) * wb)) =
        ∑ y, (Mb y a' * Mb a' y) * ((a : ℂ) * vb y + (b : ℂ) * wb) := by
      have h3 : (((W : ℝ) ^ d)⁻¹ : ℝ) * ((W ^ d : ℕ) : ℂ) = 1 := by
        have := GreenCore_w_mul (d := d) (W := W)
        exact_mod_cast this
      rw [← mul_assoc, h3, one_mul]
    rw [mul_add, this]; ring
  have hv1 : ∀ a', ‖vb a'‖ ≤ Kθ * (ρ * K𝒦) := by
    refine hstab vb (ρ * K𝒦) fun a' => ?_
    rw [hwb] at hbar
    rw [hbar a', norm_mul, Complex.norm_real, Real.norm_of_nonneg hw.le]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hw.le).trans (GreenCore_avg_le fun o => ?_)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ b', ‖Mb a' b' * 𝒦 (b', o) (a', o)‖ ≤ ∑ b', ‖Mb a' b'‖ * K𝒦 :=
          Finset.sum_le_sum fun b' _ => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hK _ _) (norm_nonneg _)
      _ ≤ ρ * K𝒦 := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hρ _) hK0
  have hwn : ‖wb‖ ≤ Kθ * (ρ * K𝒦) := by
    have hLd : (0 : ℝ) < ((L ^ d : ℕ) : ℝ) := by
      have : 0 < L ^ d := pow_pos (NeZero.pos L) d
      exact_mod_cast this
    rw [hwb, norm_mul, norm_inv, Complex.norm_natCast]
    calc (((L ^ d : ℕ) : ℝ))⁻¹ * ‖∑ c, vb c‖ ≤ (((L ^ d : ℕ) : ℝ))⁻¹ * ∑ c, ‖vb c‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ (((L ^ d : ℕ) : ℝ))⁻¹ * ∑ _c : Zd d L, Kθ * (ρ * K𝒦) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => hv1 c) (by positivity)
      _ = Kθ * (ρ * K𝒦) := by
          rw [Finset.sum_const, Finset.card_univ, BAcard_Zd, nsmul_eq_mul]; field_simp
  have hS : ∀ b', ‖(a : ℂ) * vb b' + (b : ℂ) * wb‖ ≤ Kθ * (ρ * K𝒦) := fun b' => by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    have h0 : 0 ≤ Kθ * (ρ * K𝒦) := mul_nonneg hKθ (mul_nonneg hρ0 hK0)
    nlinarith [hv1 b', hwn, norm_nonneg (vb b'), norm_nonneg wb]
  rw [hE3 x y]
  have h2 : ‖∑ b', Mb x.1 b' * (((a : ℂ) * vb b' + (b : ℂ) * wb) * M (b', x.2) y)‖ ≤ (ρ₂ * Kθ * (ρ * K𝒦)) := by
    refine (norm_sum_le _ _).trans ?_
    have hMy : ∀ b', ‖M (b', x.2) y‖ ≤ ‖Mb b' y.1‖ := fun b' => by
      rw [hM]; split_ifs
      · exact le_rfl
      · simp
    calc ∑ b', ‖Mb x.1 b' * (((a : ℂ) * vb b' + (b : ℂ) * wb) * M (b', x.2) y)‖
        ≤ ∑ b', ‖Mb x.1 b'‖ * ‖Mb b' y.1‖ * (Kθ * (ρ * K𝒦)) := by
          refine Finset.sum_le_sum fun b' _ => ?_
          rw [norm_mul, norm_mul]
          have := mul_le_mul (hS b') (hMy b') (norm_nonneg _) (mul_nonneg hKθ (mul_nonneg hρ0 hK0))
          calc ‖Mb x.1 b'‖ * (‖(a : ℂ) * vb b' + (b : ℂ) * wb‖ * ‖M (b', x.2) y‖)
              ≤ ‖Mb x.1 b'‖ * ((Kθ * (ρ * K𝒦)) * ‖Mb b' y.1‖) := mul_le_mul_of_nonneg_left this (norm_nonneg _)
            _ = _ := by ring
      _ = (∑ b', ‖Mb x.1 b'‖ * ‖Mb b' y.1‖) * (Kθ * (ρ * K𝒦)) := by rw [Finset.sum_mul]
      _ ≤ ρ₂ * (Kθ * (ρ * K𝒦)) := mul_le_mul_of_nonneg_right (hρ₂ _ _) (mul_nonneg hKθ (mul_nonneg hρ0 hK0))
      _ = _ := by ring
  have h3 : ‖∑ b', Mb x.1 b' * 𝒦 (b', x.2) y‖ ≤ ρ * K𝒦 := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ b', ‖Mb x.1 b' * 𝒦 (b', x.2) y‖ ≤ ∑ b', ‖Mb x.1 b'‖ * K𝒦 :=
          Finset.sum_le_sum fun b' _ => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hK _ _) (norm_nonneg _)
      _ ≤ ρ * K𝒦 := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hρ _) hK0
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ ρ₂ * Kθ * (ρ * K𝒦) + ρ * K𝒦 := add_le_add h2 h3
    _ = ρ * (1 + ρ₂ * Kθ) * K𝒦 := by ring

/-- The residual of the mixture: `𝒦_{uy} = 𝒮_u Δ_{uy} - (A_u + 𝒮_u) G_{uy} - 𝔛_{uy}`, `𝒮_u = a v̄_{[u]} + b w̄`. -/
def GUEEntry_K (G M X D : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a b : ℝ) (m : ℂ) (u y : Vtx d L W) : ℂ :=
  ((a : ℂ) * GreenCore_vbar G M u.1 + (b : ℂ) * GUEEntry_wbar G M) * (G u y - M u y) -
    (GreenCore_Arow G X D (a + b) m u + ((a : ℂ) * GreenCore_vbar G M u.1 + (b : ℂ) * GUEEntry_wbar G M)) * G u y -
    GreenCore_Xrow G X u y

/-- **(E3) at the mixture**: `Δ = M 𝒮[Δ] M + M 𝒦`, `𝒮[Δ] = diag(a v̄_{[u]} + b w̄)`. -/
private theorem GUEEntry_E3 {s z : ℂ} {g₀ κ δ c₀ ρ Sc : ℝ}
    (hS : GUEEntry_Setup d L W G X M D Mb m s z (a + b) g₀ κ δ c₀ ρ Sc) (hG0 : ∀ u, G u u ≠ 0)
    (x y : Vtx d L W) :
    G x y - M x y = ∑ b', Mb x.1 b' * (((a : ℂ) * GreenCore_vbar G M b' + (b : ℂ) * GUEEntry_wbar G M) *
      M (b', x.2) y) + ∑ b', Mb x.1 b' * GUEEntry_K G M X D a b m (b', x.2) y := by
  rw [GreenCore_Delta_row hS.hGR hS.hRG hS.hMR' hS.hz hS.hM hG0, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b' _ => ?_
  unfold GUEEntry_K
  ring

end Mix

section Core
variable {d L W : ℕ} [NeZero L] [NeZero W] {G X M D : Matrix (Vtx d L W) (Vtx d L W) ℂ}
  {Mb : Matrix (Zd d L) (Zd d L) ℂ} {m : ℂ} {a b : ℝ}

/-- `R₀ = 4 c₀⁻² S W^{-d} + 16 ρ Φ c₀⁻¹ S² L'` (the sup form of (R*), `GreenCore_R0` with the loop bound `L'`). -/
def GUEEntry_R0 (c₀ ρ Sc Φ w₀ Lm' : ℝ) : ℝ := 4 * c₀⁻¹ ^ 2 * Sc * w₀ + 16 * ρ * Φ * c₀⁻¹ * Sc * (Sc * Lm')

/-- `X_b = Φ (2 + 18 κ⁻²) R₀ + Ξ` (bound of `|𝔛|²`). -/
def GUEEntry_Xb (κ Φ c₀ ρ Sc w₀ Lm' Ξ : ℝ) : ℝ := Φ * (2 + 18 / κ ^ 2) * GUEEntry_R0 c₀ ρ Sc Φ w₀ Lm' + Ξ

/-- `A_b` (bound of `|A_u + 𝒮_u|²`). -/
def GUEEntry_Ab (d : ℕ) (κ Φ δ c₀ ρ Sc g₀ w₀ Lm Lm' Ξ E3b : ℝ) : ℝ :=
  5 * ((4 / κ ^ 2) * GUEEntry_R0 c₀ ρ Sc Φ w₀ Lm' * (13 / 4 * δ ^ 2) +
    (Φ * (2 * Lm + (8 / κ ^ 2) * GUEEntry_R0 c₀ ρ Sc Φ w₀ Lm' * (13 / 4 * δ ^ 2)) + Ξ) + E3b + Φ * w₀ +
    (2 * d * g₀) ^ 2 * GUEEntry_Xb κ Φ c₀ ρ Sc w₀ Lm' Ξ)

/-- **The deterministic core at the mixture** (the analogue of `GreenCore_diag`): from the large-deviation inputs in the
block form with the flat slack `Ξ`, the stability of `1 - M^{(+,+)} S̃`, and `‖G - M‖_max ≤ δ`. -/
private theorem GUEEntry_core {s z : ℂ} {g₀ κ δ c₀ ρ Sc Φ Ξ Lm Kθ ρ₂ E3b : ℝ}
    (hS : GUEEntry_Setup d L W G X M D Mb m s z (a + b) g₀ κ δ c₀ ρ Sc)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) (hΦ : 1 ≤ Φ) (hΞ : 0 ≤ Ξ)
    (hXr : ∀ u y, ‖GreenCore_Xrow G X u y‖ ^ 2 ≤
      Φ * (2 * GreenCore_R G u.1 y + (8 / κ ^ 2) * ‖G u y‖ ^ 2 * GreenCore_R G u.1 u) + Ξ)
    (hXc : ∀ x w, ‖GreenCore_Xcol G X x w‖ ^ 2 ≤
      Φ * (2 * GreenCore_Rrow G x w.1 + (8 / κ ^ 2) * ‖G x w‖ ^ 2 * GreenCore_Rrow G w w.1) + Ξ)
    (hQ : ∀ w, ‖GUEEntry_eps1 G X a b w‖ ^ 2 ≤
      Φ * (2 * GreenCore_loop G w.1 w.1 + (8 / κ ^ 2) * GreenCore_R G w.1 w * GreenCore_Rrow G w w.1) + Ξ)
    (he3 : ∀ u, ‖(b : ℂ) * GUEEntry_e3 G u‖ ^ 2 ≤ E3b)
    (hdiag : ∀ i, ‖X i i‖ ^ 2 ≤ Φ * ((W : ℝ) ^ d)⁻¹)
    (hC1 : 8 * ρ * (c₀⁻¹ * Sc) * GreenCore_theta d κ Φ δ g₀ ≤ 1)
    (hLm : ∀ a b, GreenCore_loop G a b ≤ Lm) (hLm0 : 0 ≤ Lm) (hKθ : 0 ≤ Kθ)
    (hρr : ∀ a, ∑ b, ‖Mb a b‖ ≤ ρ) (hρ₂ : ∀ a c, ∑ b, ‖Mb a b‖ * ‖Mb b c‖ ≤ ρ₂)
    (hstab : ∀ (v : Zd d L → ℂ) (B : ℝ), (∀ x, ‖v x - ∑ y, (Mb y x * Mb x y) *
      ((a : ℂ) * v y + (b : ℂ) * ((((L ^ d : ℕ) : ℂ))⁻¹ * ∑ z, v z))‖ ≤ B) → ∀ x, ‖v x‖ ≤ Kθ * B)
    (hKδ : ρ * (1 + ρ₂ * Kθ) * δ ≤ 1 / 2) (x y : Vtx d L W) :
    ‖G x y - M x y‖ ^ 2 ≤ 8 * (ρ * (1 + ρ₂ * Kθ)) ^ 2 *
      (9 / 4 * GUEEntry_Ab d κ Φ δ c₀ ρ Sc g₀ ((W : ℝ) ^ d)⁻¹ Lm (Lm + ρ * Ξ / (Φ * κ)) Ξ E3b +
        GUEEntry_Xb κ Φ c₀ ρ Sc ((W : ℝ) ^ d)⁻¹ (Lm + ρ * Ξ / (Φ * κ)) Ξ) := by
  have hw := GreenCore_w_pos (d := d) (W := W)
  have hκ := hS.hκ
  have hΦ0 : 0 ≤ Φ := by linarith
  have hΦp : 0 < Φ := by linarith
  obtain ⟨hGuu, hG32, hGoff⟩ := GreenCore_crude hS.hM hS.hMd hS.hMb1 hS.hκm hS.hm1 hS.hδ hS.hΩ
  have hG0 : ∀ u, G u u ≠ 0 := fun u h => by
    have := hGuu u; rw [h, norm_zero] at this; linarith
  have hS0 : 0 ≤ Sc := le_trans (Finset.sum_nonneg fun b _ => (Real.exp_pos _).le) (hS.hS 0)
  have hρ0 : 0 ≤ ρ := le_trans (Finset.sum_nonneg fun b _ => norm_nonneg _) (hρr 0)
  have hρ20 : 0 ≤ ρ₂ := le_trans (Finset.sum_nonneg fun b _ => by positivity) (hρ₂ 0 0)
  have hap := GreenCore_apriori hG32 hGoff hS.hδ0 hS.hwd
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = ρ * Ξ / (Φ * κ) := ⟨_, rfl⟩
  have he0 : 0 ≤ e := by rw [he]; positivity
  rw [← he]
  obtain ⟨R0, hR0⟩ : ∃ R0 : ℝ, R0 = GUEEntry_R0 c₀ ρ Sc Φ ((W : ℝ) ^ d)⁻¹ (Lm + e) := ⟨_, rfl⟩
  -- (1) the sup form of (R*)
  have hR : ∀ a' y', GreenCore_R G a' y' ≤ R0 := by
    intro a' y'
    obtain ⟨c, o⟩ := y'
    have h := GUEEntry_Rbound hS hΦ hΞ hXc hC1 (fun _ _ => Real.sqrt Lm)
      (fun a'' b'' => by rw [Real.sq_sqrt hLm0]; exact hLm a'' b'') a' c o
    rw [← he] at h
    refine h.trans ?_
    rw [hR0]; unfold GUEEntry_R0
    have e1 : Real.exp (-(c₀ / 2) * (zdistD d L (a' - c) : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [(Nat.cast_nonneg (zdistD d L (a' - c)) : (0 : ℝ) ≤ _), hS.hc₀])
    have e2 : ∑ b'', Real.exp (-(c₀ / 2) * (zdistD d L (c - b'') : ℝ)) * (Real.sqrt Lm ^ 2 + e) ≤ Sc * (Lm + e) := by
      rw [Real.sq_sqrt hLm0, ← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hS.hS c) (by linarith)
    have h1 : 4 * c₀⁻¹ ^ 2 * Sc * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c₀ / 2) * (zdistD d L (a' - c) : ℝ)) ≤
        4 * c₀⁻¹ ^ 2 * Sc * ((W : ℝ) ^ d)⁻¹ := by
      calc _ ≤ 4 * c₀⁻¹ ^ 2 * Sc * ((W : ℝ) ^ d)⁻¹ * 1 := mul_le_mul_of_nonneg_left e1 (by positivity)
        _ = _ := mul_one _
    have h2 := mul_le_mul_of_nonneg_left e2 (by have := hS.hc₀; positivity : (0 : ℝ) ≤ 16 * ρ * Φ * c₀⁻¹ * Sc)
    linarith
  obtain ⟨y0⟩ : Nonempty (Vtx d L W) := inferInstance
  have hR0nn : 0 ≤ R0 := le_trans (mul_nonneg hw.le (Finset.sum_nonneg fun _ _ => by positivity)) (hR y0.1 y0)
  -- (2) the bound for `𝔛`
  have hXr' : ∀ u y', ‖GreenCore_Xrow G X u y'‖ ^ 2 ≤ GUEEntry_Xb κ Φ c₀ ρ Sc ((W : ℝ) ^ d)⁻¹ (Lm + e) Ξ := by
    intro u y'
    refine (hXr u y').trans ?_
    have h1 : ‖G u y'‖ ^ 2 ≤ 9 / 4 := by nlinarith [norm_nonneg (G u y'), hG32 u y']
    have h2 := hR u.1 y'
    have h3 := hR u.1 u
    have h4 : 0 ≤ GreenCore_R G u.1 u := mul_nonneg hw.le (Finset.sum_nonneg fun _ _ => by positivity)
    have h5 : (8 / κ ^ 2) * ‖G u y'‖ ^ 2 * GreenCore_R G u.1 u ≤ (8 / κ ^ 2) * (9 / 4) * R0 :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h3 h4 (by positivity)
    unfold GUEEntry_Xb
    rw [← hR0]
    have e' : Φ * (2 + 18 / κ ^ 2) * R0 = Φ * (2 * R0 + (8 / κ ^ 2) * (9 / 4) * R0) := by field_simp; ring
    rw [e']
    have := mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left h2 two_pos.le) h5) hΦ0
    linarith
  -- (3) the bound for `A_u + 𝒮_u`
  have hA : ∀ u, ‖GreenCore_Arow G X D (a + b) m u + (a : ℂ) * GreenCore_vbar G M u.1 +
      (b : ℂ) * GUEEntry_wbar G M‖ ^ 2 ≤
      GUEEntry_Ab d κ Φ δ c₀ ρ Sc g₀ ((W : ℝ) ^ d)⁻¹ Lm (Lm + e) Ξ E3b := by
    intro u
    rw [GUEEntry_A_eq hS.hM hS.hMd (hG0 u)]
    have hR1 := hR u.1 u
    have hR2 : 0 ≤ GreenCore_R G u.1 u := mul_nonneg hw.le (Finset.sum_nonneg fun _ _ => by positivity)
    have hR3 := hap.2 u u.1
    have hR4 : 0 ≤ GreenCore_Rrow G u u.1 := mul_nonneg hw.le (Finset.sum_nonneg fun _ _ => by positivity)
    have hRR : GreenCore_R G u.1 u * GreenCore_Rrow G u u.1 ≤ R0 * (13 / 4 * δ ^ 2) :=
      mul_le_mul hR1 hR3 hR4 (le_trans hR2 hR1)
    have b2 : ‖GreenCore_eps2 G a u‖ ^ 2 ≤ (4 / κ ^ 2) * R0 * (13 / 4 * δ ^ 2) := by
      refine (GreenCore_eps2_loc ha (by linarith) hκ hGuu u).trans ?_
      rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_left hRR (by positivity)
    have b1 : ‖GUEEntry_eps1 G X a b u‖ ^ 2 ≤ Φ * (2 * Lm + (8 / κ ^ 2) * R0 * (13 / 4 * δ ^ 2)) + Ξ := by
      refine (hQ u).trans (add_le_add (mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left (hLm _ _) two_pos.le) ?_) hΦ0) le_rfl)
      rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_left hRR (by positivity)
    have b4 := GreenCore_Qxd_sq (G := G) (X := X) hS.hg hS.hL hS.hD (fun l => hXr' u l)
    have hT : ‖GreenCore_eps2 G a u + (b : ℂ) * GUEEntry_e3 G u - GUEEntry_eps1 G X a b u + X u u -
        GreenCore_Qxd G X D u‖ ≤ ‖GreenCore_eps2 G a u‖ + ‖(b : ℂ) * GUEEntry_e3 G u‖ +
          ‖GUEEntry_eps1 G X a b u‖ + ‖X u u‖ + ‖GreenCore_Qxd G X D u‖ :=
      (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
        ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    have h5 := GreenCore_sq5 ‖GreenCore_eps2 G a u‖ ‖(b : ℂ) * GUEEntry_e3 G u‖ ‖GUEEntry_eps1 G X a b u‖
      ‖X u u‖ ‖GreenCore_Qxd G X D u‖
    refine le_trans (pow_le_pow_left₀ (norm_nonneg _) hT 2) (h5.trans ?_)
    unfold GUEEntry_Ab
    rw [← hR0]
    linarith [b2, he3 u, b1, hdiag u, b4]
  -- (4) the residual `𝒦` and the coupled bound at the maximum of `|Δ|`
  obtain ⟨p₀, hp₀⟩ := Finite.exists_max (fun p : Vtx d L W × Vtx d L W => ‖G p.1 p.2 - M p.1 p.2‖)
  have hDm : ∀ x y, ‖G x y - M x y‖ ≤ ‖G p₀.1 p₀.2 - M p₀.1 p₀.2‖ := fun x y => hp₀ (x, y)
  have hDm0 : 0 ≤ ‖G p₀.1 p₀.2 - M p₀.1 p₀.2‖ := norm_nonneg _
  generalize hDmdef : ‖G p₀.1 p₀.2 - M p₀.1 p₀.2‖ = Dm at hDm hDm0
  have hDmδ : Dm ≤ δ := hDmdef ▸ hS.hΩ _ _
  have hvb : ∀ a', ‖GreenCore_vbar G M a'‖ ≤ Dm := fun a' => by
    unfold GreenCore_vbar
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw.le]
    exact (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hw.le).trans (GreenCore_avg_le fun o => hDm _ _)
  have hwbn : ‖GUEEntry_wbar G M‖ ≤ Dm := by
    have hLd : (0 : ℝ) < ((L ^ d : ℕ) : ℝ) := by
      have : 0 < L ^ d := pow_pos (NeZero.pos L) d
      exact_mod_cast this
    unfold GUEEntry_wbar
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (((L ^ d : ℕ) : ℝ))⁻¹ * ‖∑ a' : Zd d L, GreenCore_vbar G M a'‖
        ≤ (((L ^ d : ℕ) : ℝ))⁻¹ * ∑ a' : Zd d L, ‖GreenCore_vbar G M a'‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ (((L ^ d : ℕ) : ℝ))⁻¹ * ∑ _a' : Zd d L, Dm :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a' _ => hvb a') (by positivity)
      _ = Dm := by rw [Finset.sum_const, Finset.card_univ, BAcard_Zd, nsmul_eq_mul]; field_simp
  have hS' : ∀ u : Vtx d L W, ‖(a : ℂ) * GreenCore_vbar G M u.1 + (b : ℂ) * GUEEntry_wbar G M‖ ≤ Dm := by
    intro u
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    nlinarith [hvb u.1, hwbn, norm_nonneg (GreenCore_vbar G M u.1), norm_nonneg (GUEEntry_wbar G M)]
  have hKb : ∀ u y', ‖GUEEntry_K G M X D a b m u y'‖ ≤
      Dm * δ + 3 / 2 * Real.sqrt (GUEEntry_Ab d κ Φ δ c₀ ρ Sc g₀ ((W : ℝ) ^ d)⁻¹ Lm (Lm + e) Ξ E3b) +
        Real.sqrt (GUEEntry_Xb κ Φ c₀ ρ Sc ((W : ℝ) ^ d)⁻¹ (Lm + e) Ξ) := by
    intro u y'
    unfold GUEEntry_K
    have h1 : ‖((a : ℂ) * GreenCore_vbar G M u.1 + (b : ℂ) * GUEEntry_wbar G M) * (G u y' - M u y')‖ ≤ Dm * δ := by
      rw [norm_mul]
      exact mul_le_mul (hS' u) (hS.hΩ _ _) (norm_nonneg _) hDm0
    have h2 : ‖(GreenCore_Arow G X D (a + b) m u + ((a : ℂ) * GreenCore_vbar G M u.1 + (b : ℂ) * GUEEntry_wbar G M)) *
        G u y'‖ ≤ Real.sqrt (GUEEntry_Ab d κ Φ δ c₀ ρ Sc g₀ ((W : ℝ) ^ d)⁻¹ Lm (Lm + e) Ξ E3b) * (3 / 2) := by
      rw [norm_mul, ← add_assoc]
      exact mul_le_mul ((le_abs_self _).trans (Real.abs_le_sqrt (hA u))) (hG32 u y') (norm_nonneg _) (Real.sqrt_nonneg _)
    have h3 : ‖GreenCore_Xrow G X u y'‖ ≤ Real.sqrt (GUEEntry_Xb κ Φ c₀ ρ Sc ((W : ℝ) ^ d)⁻¹ (Lm + e) Ξ) :=
      (le_abs_self _).trans (Real.abs_le_sqrt (hXr' u y'))
    calc _ ≤ ‖((a : ℂ) * GreenCore_vbar G M u.1 + (b : ℂ) * GUEEntry_wbar G M) * (G u y' - M u y') -
          (GreenCore_Arow G X D (a + b) m u + ((a : ℂ) * GreenCore_vbar G M u.1 + (b : ℂ) * GUEEntry_wbar G M)) *
            G u y'‖ + ‖GreenCore_Xrow G X u y'‖ := norm_sub_le _ _
      _ ≤ (‖((a : ℂ) * GreenCore_vbar G M u.1 + (b : ℂ) * GUEEntry_wbar G M) * (G u y' - M u y')‖ +
          ‖(GreenCore_Arow G X D (a + b) m u + ((a : ℂ) * GreenCore_vbar G M u.1 + (b : ℂ) * GUEEntry_wbar G M)) *
            G u y'‖) + ‖GreenCore_Xrow G X u y'‖ := add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ _ := by linarith
  have hmax := GUEEntry_coupled (M := M) (Mb := Mb) (Δ := fun x y => G x y - M x y)
    (𝒦 := GUEEntry_K G M X D a b m) (vb := GreenCore_vbar G M) (wb := GUEEntry_wbar G M)
    hS.hM ha hb hab hKθ hρr hρ₂ (fun a => rfl) rfl (fun x y => GUEEntry_E3 hS hG0 x y) hstab hKb p₀.1 p₀.2
  rw [hDmdef] at hmax
  have hAb0 : 0 ≤ GUEEntry_Ab d κ Φ δ c₀ ρ Sc g₀ ((W : ℝ) ^ d)⁻¹ Lm (Lm + e) Ξ E3b := le_trans (sq_nonneg _) (hA y0)
  have hXb0 : 0 ≤ GUEEntry_Xb κ Φ c₀ ρ Sc ((W : ℝ) ^ d)⁻¹ (Lm + e) Ξ := le_trans (sq_nonneg _) (hXr' y0 y0)
  have ha2 := Real.sq_sqrt hAb0
  have hb2 := Real.sq_sqrt hXb0
  generalize Real.sqrt (GUEEntry_Ab d κ Φ δ c₀ ρ Sc g₀ ((W : ℝ) ^ d)⁻¹ Lm (Lm + e) Ξ E3b) = aa at *
  generalize Real.sqrt (GUEEntry_Xb κ Φ c₀ ρ Sc ((W : ℝ) ^ d)⁻¹ (Lm + e) Ξ) = bb at *
  have hK0 : 0 ≤ ρ * (1 + ρ₂ * Kθ) := by positivity
  have h2 : Dm ≤ 2 * (ρ * (1 + ρ₂ * Kθ)) * (3 / 2 * aa + bb) := by
    have := mul_le_mul_of_nonneg_right hKδ hDm0
    nlinarith
  have h3 : ‖G x y - M x y‖ ^ 2 ≤ (2 * (ρ * (1 + ρ₂ * Kθ)) * (3 / 2 * aa + bb)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) ((hDm x y).trans h2) 2
  refine h3.trans ?_
  rw [← ha2, ← hb2]
  nlinarith [sq_nonneg (3 / 2 * aa - bb), sq_nonneg (ρ * (1 + ρ₂ * Kθ))]

end Core

section Const

/-- `C_R`, `C_X`, `C_A`: the constants of `R₀ ≤ Φ C_R Ω`, `X_b ≤ Φ² C_X Ω`, `A_b ≤ Φ² C_A Ω`, `Ω = L + W^{-d}`. -/
def GUEEntry_CR (c₀ ρ Sc cL : ℝ) : ℝ := 4 * c₀⁻¹ ^ 2 * Sc + 16 * ρ * c₀⁻¹ * Sc ^ 2 * cL
def GUEEntry_CX (κ CR Ξc : ℝ) : ℝ := (2 + 18 / κ ^ 2) * CR + Ξc
def GUEEntry_CA (d : ℕ) (κ Λ Ξc CR CX : ℝ) : ℝ :=
  5 * (13 / κ ^ 2 * CR + 26 / κ ^ 2 * CR + 2 + Ξc + 81 / κ ^ 4 + 1 + (2 * d * Λ) ^ 2 * CX)

theorem GUEEntry_R0_le {c₀ ρ Sc cL Φ Lm w₀ : ℝ} (hc₀ : 0 < c₀) (hρ0 : 0 ≤ ρ) (hS0 : 0 ≤ Sc) (hcL0 : 0 ≤ cL)
    (hΦ : 1 ≤ Φ) (hLm0 : 0 ≤ Lm) (hw0 : 0 ≤ w₀) :
    GUEEntry_R0 c₀ ρ Sc Φ w₀ (cL * Lm) ≤ Φ * GUEEntry_CR c₀ ρ Sc cL * (Lm + w₀) := by
  have hΦp : 0 < Φ := by linarith
  unfold GUEEntry_R0 GUEEntry_CR
  have e1 : 4 * c₀⁻¹ ^ 2 * Sc * w₀ ≤ Φ * (4 * c₀⁻¹ ^ 2 * Sc) * (Lm + w₀) := by
    have h0 : 0 ≤ 4 * c₀⁻¹ ^ 2 * Sc := by positivity
    have : w₀ ≤ Φ * (Lm + w₀) := by nlinarith [mul_nonneg hΦp.le hLm0]
    nlinarith [mul_le_mul_of_nonneg_left this h0]
  have e2 : 16 * ρ * Φ * c₀⁻¹ * Sc * (Sc * (cL * Lm)) ≤ Φ * (16 * ρ * c₀⁻¹ * Sc ^ 2 * cL) * (Lm + w₀) := by
    have h0 : 0 ≤ Φ * (16 * ρ * c₀⁻¹ * Sc ^ 2 * cL) := by positivity
    have : Lm ≤ Lm + w₀ := by linarith
    have := mul_le_mul_of_nonneg_left this h0
    nlinarith
  nlinarith [e1, e2]

theorem GUEEntry_Xb_le {κ Φ c₀ ρ Sc w₀ Lm' Ξ CR CX Ξc Lm : ℝ} (hκ : 0 < κ) (hΦ : 1 ≤ Φ) (hCR0 : 0 ≤ CR)
    (hLm0 : 0 ≤ Lm) (hw0 : 0 ≤ w₀) (hΞc0 : 0 ≤ Ξc) (hR : GUEEntry_R0 c₀ ρ Sc Φ w₀ Lm' ≤ Φ * CR * (Lm + w₀))
    (hΞ : Ξ = Ξc * Φ * Lm) (hCX : CX = GUEEntry_CX κ CR Ξc) :
    GUEEntry_Xb κ Φ c₀ ρ Sc w₀ Lm' Ξ ≤ Φ ^ 2 * CX * (Lm + w₀) := by
  have hΦp : 0 < Φ := by linarith
  unfold GUEEntry_Xb
  have h1 : Φ * (2 + 18 / κ ^ 2) * GUEEntry_R0 c₀ ρ Sc Φ w₀ Lm' ≤
      Φ * (2 + 18 / κ ^ 2) * (Φ * CR * (Lm + w₀)) := mul_le_mul_of_nonneg_left hR (by positivity)
  have h2 : Ξ ≤ Ξc * (Φ ^ 2 * (Lm + w₀)) := by
    rw [hΞ]
    have h3 : Φ * Lm ≤ Φ ^ 2 * (Lm + w₀) := by nlinarith [mul_nonneg hΦp.le hw0, mul_nonneg hΦp.le hLm0]
    have := mul_le_mul_of_nonneg_left h3 hΞc0
    linarith
  rw [hCX, GUEEntry_CX]
  calc _ ≤ Φ * (2 + 18 / κ ^ 2) * (Φ * CR * (Lm + w₀)) + Ξc * (Φ ^ 2 * (Lm + w₀)) := add_le_add h1 h2
    _ = _ := by ring

set_option maxHeartbeats 600000 in
-- the bound `A_b` is a long chain of explicit estimates
theorem GUEEntry_Ab_le (d : ℕ) {κ Φ δ Lm w₀ Ξ E3b R0 Xb g₀ Λ CR CX CA Ξc : ℝ} (hκ : 0 < κ) (hΦ : 1 ≤ Φ)
    (hCR0 : 0 ≤ CR) (hLm0 : 0 ≤ Lm) (hw0 : 0 ≤ w₀) (hΞc0 : 0 ≤ Ξc) (hg : 0 ≤ g₀) (hgΛ : g₀ ≤ Λ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hR : R0 ≤ Φ * CR * (Lm + w₀)) (hR00 : 0 ≤ R0)
    (hXb : Xb ≤ Φ ^ 2 * CX * (Lm + w₀)) (hXb0 : 0 ≤ Xb) (hΞ : Ξ = Ξc * Φ * Lm) (hE3 : E3b = 81 * Lm / κ ^ 4)
    (hCA : CA = GUEEntry_CA d κ Λ Ξc CR CX) :
    5 * ((4 / κ ^ 2) * R0 * (13 / 4 * δ ^ 2) + (Φ * (2 * Lm + (8 / κ ^ 2) * R0 * (13 / 4 * δ ^ 2)) + Ξ) + E3b +
      Φ * w₀ + (2 * d * g₀) ^ 2 * Xb) ≤ Φ ^ 2 * CA * (Lm + w₀) := by
  have hΦp : 0 < Φ := by linarith
  have hd2 : δ ^ 2 ≤ 1 := by nlinarith
  have hΩ0 : 0 ≤ Lm + w₀ := by positivity
  have hΦΩ : Φ * (Lm + w₀) ≤ Φ ^ 2 * (Lm + w₀) := by nlinarith [mul_nonneg hΦp.le hΩ0]
  have hRd : R0 * δ ^ 2 ≤ Φ * CR * (Lm + w₀) := (mul_le_mul_of_nonneg_left hd2 hR00).trans (by rw [mul_one]; exact hR)
  have hRΩ : Φ * CR * (Lm + w₀) ≤ Φ ^ 2 * CR * (Lm + w₀) := by
    have := mul_le_mul_of_nonneg_left hΦΩ hCR0
    nlinarith
  have t1 : (4 / κ ^ 2) * R0 * (13 / 4 * δ ^ 2) ≤ (13 / κ ^ 2) * (Φ ^ 2 * CR * (Lm + w₀)) := by
    have e : (4 / κ ^ 2) * R0 * (13 / 4 * δ ^ 2) = (13 / κ ^ 2) * (R0 * δ ^ 2) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (hRd.trans hRΩ) (by positivity)
  have t2 : Φ * (2 * Lm + (8 / κ ^ 2) * R0 * (13 / 4 * δ ^ 2)) ≤
      2 * (Φ ^ 2 * (Lm + w₀)) + (26 / κ ^ 2) * (Φ ^ 2 * CR * (Lm + w₀)) := by
    have e : (8 / κ ^ 2) * R0 * (13 / 4 * δ ^ 2) = (26 / κ ^ 2) * (R0 * δ ^ 2) := by ring
    rw [e]
    have h1 : (26 / κ ^ 2) * (R0 * δ ^ 2) ≤ (26 / κ ^ 2) * (Φ * CR * (Lm + w₀)) :=
      mul_le_mul_of_nonneg_left hRd (by positivity)
    have h2 : Φ * (2 * Lm + (26 / κ ^ 2) * (R0 * δ ^ 2)) ≤ Φ * (2 * Lm + (26 / κ ^ 2) * (Φ * CR * (Lm + w₀))) :=
      mul_le_mul_of_nonneg_left (by linarith) hΦp.le
    refine h2.trans ?_
    have h3 : Φ * (2 * Lm) ≤ 2 * (Φ ^ 2 * (Lm + w₀)) := by nlinarith [mul_nonneg hΦp.le hw0, mul_nonneg hΦp.le hLm0]
    have h4 : Φ * ((26 / κ ^ 2) * (Φ * CR * (Lm + w₀))) = (26 / κ ^ 2) * (Φ ^ 2 * CR * (Lm + w₀)) := by ring
    nlinarith [h3, h4]
  have t3 : Ξ ≤ Ξc * (Φ ^ 2 * (Lm + w₀)) := by
    rw [hΞ]
    have h3 : Φ * Lm ≤ Φ ^ 2 * (Lm + w₀) := by nlinarith [mul_nonneg hΦp.le hw0, mul_nonneg hΦp.le hLm0]
    have := mul_le_mul_of_nonneg_left h3 hΞc0
    linarith
  have t4 : E3b ≤ (81 / κ ^ 4) * (Φ ^ 2 * (Lm + w₀)) := by
    rw [hE3]
    have h : Lm ≤ Φ ^ 2 * (Lm + w₀) := by nlinarith [mul_nonneg hLm0 (sq_nonneg Φ), mul_nonneg hw0 (sq_nonneg Φ)]
    have := mul_le_mul_of_nonneg_left h (show 0 ≤ 81 / κ ^ 4 by positivity)
    calc 81 * Lm / κ ^ 4 = (81 / κ ^ 4) * Lm := by ring
      _ ≤ _ := this
  have t5 : Φ * w₀ ≤ Φ ^ 2 * (Lm + w₀) := by nlinarith [mul_nonneg hLm0 (sq_nonneg Φ), mul_nonneg hw0 hΦp.le]
  have t6 : (2 * d * g₀) ^ 2 * Xb ≤ (2 * d * Λ) ^ 2 * (Φ ^ 2 * CX * (Lm + w₀)) := by
    have h1 : (2 * d * g₀) ^ 2 ≤ (2 * d * Λ) ^ 2 := by
      have : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
      have : 2 * d * g₀ ≤ 2 * d * Λ := by nlinarith
      exact pow_le_pow_left₀ (by positivity) this 2
    calc (2 * d * g₀) ^ 2 * Xb ≤ (2 * d * Λ) ^ 2 * Xb := mul_le_mul_of_nonneg_right h1 hXb0
      _ ≤ _ := mul_le_mul_of_nonneg_left hXb (by positivity)
  have hsum : (4 / κ ^ 2) * R0 * (13 / 4 * δ ^ 2) + (Φ * (2 * Lm + (8 / κ ^ 2) * R0 * (13 / 4 * δ ^ 2)) + Ξ) + E3b +
      Φ * w₀ + (2 * d * g₀) ^ 2 * Xb ≤
      (13 / κ ^ 2) * (Φ ^ 2 * CR * (Lm + w₀)) + (2 * (Φ ^ 2 * (Lm + w₀)) + (26 / κ ^ 2) * (Φ ^ 2 * CR * (Lm + w₀)) +
        Ξc * (Φ ^ 2 * (Lm + w₀))) + (81 / κ ^ 4) * (Φ ^ 2 * (Lm + w₀)) + Φ ^ 2 * (Lm + w₀) +
        (2 * d * Λ) ^ 2 * (Φ ^ 2 * CX * (Lm + w₀)) := by
    have := add_le_add t2 t3
    linarith [t1, t4, t5, t6]
  calc _ ≤ 5 * ((13 / κ ^ 2) * (Φ ^ 2 * CR * (Lm + w₀)) + (2 * (Φ ^ 2 * (Lm + w₀)) + (26 / κ ^ 2) * (Φ ^ 2 * CR * (Lm + w₀)) +
        Ξc * (Φ ^ 2 * (Lm + w₀))) + (81 / κ ^ 4) * (Φ ^ 2 * (Lm + w₀)) + Φ ^ 2 * (Lm + w₀) +
        (2 * d * Λ) ^ 2 * (Φ ^ 2 * CX * (Lm + w₀))) := mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = Φ ^ 2 * CA * (Lm + w₀) := by rw [hCA, GUEEntry_CA]; ring

/-- `ρ = c₀⁻¹ S_{c₀}`, the `ℓ¹` row/column bound of `M^{(B)}`. -/
def GUEEntry_rho (d : ℕ) (Λ κ : ℝ) : ℝ := (BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ)
/-- `S = S_{c₀/2}`, the radial lattice sum. -/
def GUEEntry_Sc (d : ℕ) (Λ κ : ℝ) : ℝ := expC (d - 2) (BAct_rate d Λ κ / 2)
/-- The stability constant of `stable_mixBA`. -/
def GUEEntry_Kth (κ : ℝ) : ℝ := 16 * κ⁻¹ ^ 4 * (1 + 16 * κ⁻¹ ^ 4)
/-- `K_BA = ρ (1 + ρ₂ K_θ)`, `ρ₂ = 1`. -/
def GUEEntry_Kbd (d : ℕ) (Λ κ : ℝ) : ℝ := GUEEntry_rho d Λ κ * (1 + 1 * GUEEntry_Kth κ)
/-- The flat slack constant: `Ξ = ΞC Φ L`. -/
def GUEEntry_XiC (κ : ℝ) : ℝ := 9 * (2 + 18 / κ ^ 2) / κ
def GUEEntry_CRb (d : ℕ) (Λ κ : ℝ) : ℝ :=
  GUEEntry_CR (BAct_rate d Λ κ) (GUEEntry_rho d Λ κ) (GUEEntry_Sc d Λ κ) (1 + GUEEntry_rho d Λ κ * GUEEntry_XiC κ / κ)
def GUEEntry_CXb (d : ℕ) (Λ κ : ℝ) : ℝ := GUEEntry_CX κ (GUEEntry_CRb d Λ κ) (GUEEntry_XiC κ)
def GUEEntry_CAb (d : ℕ) (Λ κ : ℝ) : ℝ :=
  GUEEntry_CA d κ Λ (GUEEntry_XiC κ) (GUEEntry_CRb d Λ κ) (GUEEntry_CXb d Λ κ)
/-- **The constant of the deterministic bound of the mixture entry layer** (`d, Λ, κ` only). -/
def GUEEntry_C (d : ℕ) (Λ κ : ℝ) : ℝ :=
  8 * GUEEntry_Kbd d Λ κ ^ 2 * (9 / 4 * GUEEntry_CAb d Λ κ + GUEEntry_CXb d Λ κ)
/-- The smallness threshold of the a priori bound `δ`. -/
def GUEEntry_dlt (d : ℕ) (Λ κ : ℝ) : ℝ := min (κ / 2) (1 / (2 * GUEEntry_Kbd d Λ κ))
/-- The smallness constant of `Φ δ²`: the condition `GUEEntry_cs · Φ δ² ≤ 1` implies the smallness condition
`8 ρ c₀⁻¹ S ϑ ≤ 1` of the `GreenCore` lemmas. -/
def GUEEntry_cs (d : ℕ) (Λ κ : ℝ) : ℝ :=
  8 * GUEEntry_rho d Λ κ * ((BAct_rate d Λ κ)⁻¹ * GUEEntry_Sc d Λ κ) *
    ((4 / κ ^ 2) * (2 * d * Λ + (1 + 2 * d * Λ) / κ) ^ 2 + 26 / κ ^ 2)

/-- **The clean constant**: `8 K² (9/4 A_b + X_b) ≤ C Φ² (L + W^{-d})` at the slack `Ξ = ΞC Φ L`. -/
theorem GUEEntry_final (d : ℕ) {Λ κ g δ Φ Lm w₀ : ℝ} (hκ : 0 < κ) (hc₀ : 0 < BAct_rate d Λ κ) (hg : 0 ≤ g)
    (hgΛ : g ≤ Λ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hΦ : 1 ≤ Φ) (hLm0 : 0 ≤ Lm) (hw0 : 0 ≤ w₀) :
    8 * (GUEEntry_rho d Λ κ * (1 + 1 * GUEEntry_Kth κ)) ^ 2 *
      (9 / 4 * GUEEntry_Ab d κ Φ δ (BAct_rate d Λ κ) (GUEEntry_rho d Λ κ) (GUEEntry_Sc d Λ κ) g w₀ Lm
          (Lm + GUEEntry_rho d Λ κ * (GUEEntry_XiC κ * Φ * Lm) / (Φ * κ)) (GUEEntry_XiC κ * Φ * Lm)
          (81 * Lm / κ ^ 4) +
        GUEEntry_Xb κ Φ (BAct_rate d Λ κ) (GUEEntry_rho d Λ κ) (GUEEntry_Sc d Λ κ) w₀
          (Lm + GUEEntry_rho d Λ κ * (GUEEntry_XiC κ * Φ * Lm) / (Φ * κ)) (GUEEntry_XiC κ * Φ * Lm)) ≤
      GUEEntry_C d Λ κ * Φ ^ 2 * (Lm + w₀) := by
  have hρ0 : 0 ≤ GUEEntry_rho d Λ κ := by unfold GUEEntry_rho expC; positivity
  have hS0 : 0 ≤ GUEEntry_Sc d Λ κ := by unfold GUEEntry_Sc expC; positivity
  have hXiC : 0 ≤ GUEEntry_XiC κ := by unfold GUEEntry_XiC; positivity
  obtain ⟨cL, hcL⟩ : ∃ cL : ℝ, cL = 1 + GUEEntry_rho d Λ κ * GUEEntry_XiC κ / κ := ⟨_, rfl⟩
  have hcL0 : 0 ≤ cL := by rw [hcL]; positivity
  have hLm' : Lm + GUEEntry_rho d Λ κ * (GUEEntry_XiC κ * Φ * Lm) / (Φ * κ) = cL * Lm := by
    rw [hcL]; field_simp
  rw [hLm']
  have hCR : GUEEntry_CRb d Λ κ = GUEEntry_CR (BAct_rate d Λ κ) (GUEEntry_rho d Λ κ) (GUEEntry_Sc d Λ κ) cL := by
    subst hcL; rfl
  have hCR0 : 0 ≤ GUEEntry_CRb d Λ κ := by rw [hCR]; unfold GUEEntry_CR; positivity
  have hR := GUEEntry_R0_le hc₀ hρ0 hS0 hcL0 hΦ hLm0 hw0
  rw [← hCR] at hR
  have hR00 : 0 ≤ GUEEntry_R0 (BAct_rate d Λ κ) (GUEEntry_rho d Λ κ) (GUEEntry_Sc d Λ κ) Φ w₀ (cL * Lm) := by
    unfold GUEEntry_R0; positivity
  have hXb := GUEEntry_Xb_le (Ξ := GUEEntry_XiC κ * Φ * Lm) (CX := GUEEntry_CXb d Λ κ) hκ hΦ hCR0 hLm0 hw0 hXiC hR rfl rfl
  have hXb0 : 0 ≤ GUEEntry_Xb κ Φ (BAct_rate d Λ κ) (GUEEntry_rho d Λ κ) (GUEEntry_Sc d Λ κ) w₀ (cL * Lm)
      (GUEEntry_XiC κ * Φ * Lm) := by
    unfold GUEEntry_Xb; positivity
  have hAb := GUEEntry_Ab_le d (g₀ := g) (Λ := Λ) (Ξ := GUEEntry_XiC κ * Φ * Lm) (CA := GUEEntry_CAb d Λ κ)
    (CX := GUEEntry_CXb d Λ κ) (CR := GUEEntry_CRb d Λ κ) (Ξc := GUEEntry_XiC κ) hκ hΦ hCR0 hLm0 hw0 hXiC hg hgΛ hδ0
    hδ1 hR hR00 hXb hXb0 rfl rfl rfl
  have hK0 : 0 ≤ 8 * (GUEEntry_rho d Λ κ * (1 + 1 * GUEEntry_Kth κ)) ^ 2 := by positivity
  calc _ ≤ 8 * (GUEEntry_rho d Λ κ * (1 + 1 * GUEEntry_Kth κ)) ^ 2 *
        (9 / 4 * (Φ ^ 2 * GUEEntry_CAb d Λ κ * (Lm + w₀)) + Φ ^ 2 * GUEEntry_CXb d Λ κ * (Lm + w₀)) := by
        refine mul_le_mul_of_nonneg_left ?_ hK0
        unfold GUEEntry_Ab
        linarith [hAb, hXb]
    _ = GUEEntry_C d Λ κ * Φ ^ 2 * (Lm + w₀) := by unfold GUEEntry_C GUEEntry_Kbd; ring

end Const

section Det
variable {d L W : ℕ} [NeZero L] [NeZero W]

theorem GUEEntry_loop_le (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (hG32 : ∀ u v, ‖G u v‖ ≤ 3 / 2) (a b : Zd d L) :
    GreenCore_loop G a b ≤ 9 / 4 := by
  unfold GreenCore_loop
  have hw := GreenCore_w_pos (d := d) (W := W)
  have hwW : ((W : ℝ) ^ d)⁻¹ * ((W : ℝ) ^ d) = 1 := GreenCore_w_mul
  calc (((W : ℝ) ^ d)⁻¹) ^ 2 * ∑ o : Fin (W ^ d), ∑ o' : Fin (W ^ d), ‖G (a, o) (b, o')‖ ^ 2
      ≤ (((W : ℝ) ^ d)⁻¹) ^ 2 * ∑ _o : Fin (W ^ d), ∑ _o' : Fin (W ^ d), (9 / 4 : ℝ) := by
        gcongr with o _ o' _
        nlinarith [norm_nonneg (G (a, o) (b, o')), hG32 (a, o) (b, o')]
    _ = 9 / 4 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        have : (((W : ℝ) ^ d)⁻¹) ^ 2 * ((W : ℝ) ^ d * ((W : ℝ) ^ d * (9 / 4))) = 9 / 4 * (((W : ℝ) ^ d)⁻¹ * ((W : ℝ) ^ d)) ^ 2 := by ring
        rw [this, hwW]; ring

theorem GUEEntry_Smv_diag_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : a + b ≤ 1) (i : Vtx d L W) :
    GUEEntry_Smv d L W a b i i ≤ ((W : ℝ) ^ d)⁻¹ := by
  unfold GUEEntry_Smv
  have hsv : svar d L W 0 i i = ((W : ℝ) ^ d)⁻¹ := by rw [GreenCore_svar0]; simp
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := pow_pos (Nat.cast_pos.2 (NeZero.pos W)) d
  have hN : ((W : ℝ) ^ d) ≤ (((W * L) ^ d : ℕ) : ℝ) := by
    have : W ≤ W * L := Nat.le_mul_of_pos_right W (NeZero.pos L)
    exact_mod_cast Nat.pow_le_pow_left this d
  have h1 : b / (((W * L) ^ d : ℕ) : ℝ) ≤ b * ((W : ℝ) ^ d)⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hWd hN) hb
  rw [hsv]
  nlinarith [inv_pos.2 hWd]

set_option maxHeartbeats 1600000 in
-- the assembly of the core, the stability and the constant chain in one proof
/-- **The deterministic bridge at the mixture profile** (the analogue of `mix_det`): on `Ω`
(`‖G - M‖_max ≤ δ`, `M = M^{(B)} ⊗ I`, `G = (g Ψ + X - z)⁻¹`, `z = z_u^{(E)}`, `u = a + b`), given the four
large-deviation inputs at the profile `S_u = a S^{(B)}(0) + b N⁻¹` with the factor `Φ` and the loop bound `Lm`,
`|G_{xy} - M_{xy}|² ≤ C Φ² (Lm + W^{-d})`, `C = C(d, Λ, κ)`, `L`-free. -/
theorem mix_detBA {g Λ κ E a b δ Φ Lm : ℝ} {m s z : ℂ} {G X M D : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hg : 0 < g) (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu1 : a + b < 1)
    (hGR : G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1)
    (hRG : (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1)
    (hMR : (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * M = 1)
    (hMR' : M * (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1)
    (hz : z = s - ((a + b : ℝ) : ℂ) * m)
    (hM : ∀ u v, M u v = if u.2 = v.2 then BAMB d L g (E : ℂ) m u.1 v.1 else 0)
    (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g : ℂ) else 0)
    (hH : (D + X).IsHermitian) (hzim : 0 < z.im)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ GUEEntry_dlt d Λ κ) (hwd : ((W : ℝ) ^ d)⁻¹ ≤ δ ^ 2)
    (hΩ : ∀ u v, ‖G u v - M u v‖ ≤ δ) (hΦ : 1 ≤ Φ) (hΦδ : GUEEntry_cs d Λ κ * Φ * δ ^ 2 ≤ 1)
    (hLrow : LDERow X G (GUEEntry_Smv d L W a b) Φ) (hLcol : LDECol X G (GUEEntry_Smv d L W a b) Φ)
    (hLquad : LDEQuad X G (GUEEntry_Smv d L W a b) 1 Φ)
    (hLdiag : ∀ i, ‖X i i‖ ^ 2 ≤ Φ * GUEEntry_Smv d L W a b i i)
    (hLm : ∀ a b, GreenCore_loop G a b ≤ Lm) (x y : Vtx d L W) :
    ‖G x y - M x y‖ ^ 2 ≤ GUEEntry_C d Λ κ * Φ ^ 2 * (Lm + ((W : ℝ) ^ d)⁻¹) := by
  have hΛ : 0 < Λ := lt_of_lt_of_le hg hgΛ
  have hd2 : 2 ≤ d := by omega
  have hmim : κ ≤ m.im := hr.2
  have hn : ‖m‖ ≤ 1 := BAm_norm_le_one d L g (E : ℂ) m (by simp) hr.1
  have hκm : κ ≤ ‖m‖ := hmim.trans (Complex.im_le_norm m)
  have hκ1 : κ ≤ 1 := hκm.trans hn
  have hc₀ : 0 < BAct_rate d Λ κ := BAct_rate_pos d Λ κ (by omega) hΛ hκ
  have hMd : ∀ a', BAMB d L g (E : ℂ) m a' a' = m := BAMB_diag_eq d L g (E : ℂ) m hr.1
  have hMb1 : ∀ a' b', ‖BAMB d L g (E : ℂ) m a' b'‖ ≤ 1 := fun a' b' => by
    have hrow := BAMB_row_sq_real d L g E m hr.1 a'
    have hle : ‖BAMB d L g (E : ℂ) m a' b'‖ ^ 2 ≤ 1 := by
      rw [← hrow]
      exact Finset.single_le_sum (f := fun b'' => ‖BAMB d L g (E : ℂ) m a' b''‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ b')
    nlinarith [norm_nonneg (BAMB d L g (E : ℂ) m a' b')]
  have hdec := BAMB_decay_large d L hL (by omega) Λ g κ E m hΛ hg hgΛ hκ hr
  have hρc := baM_col_l1 hd2 hL Λ g κ E m hΛ hg hgΛ hκ hr
  have hρr := baM_row_l1 hd2 hL Λ g κ E m hΛ hg hgΛ hκ hr
  have hρ₂ := baM_rho2 g E m hr.1 (d := d) (L := L)
  have hSS : ∀ a' : Zd d L, ∑ b', Real.exp (-(BAct_rate d Λ κ / 2) * (zdistD d L (a' - b') : ℝ)) ≤
      GUEEntry_Sc d Λ κ := fun a' => by
    have := BAsum_exp_decay_le d L hd2 (BAct_rate d Λ κ / 2) (by positivity) a'
    simpa only [neg_mul, GUEEntry_Sc] using this
  have hδ' : δ ≤ κ / 2 := hδ.trans (min_le_left _ _)
  have hS : GUEEntry_Setup d L W G X M D (BAMB d L g (E : ℂ) m) m s z (a + b) g κ δ (BAct_rate d Λ κ)
      (GUEEntry_rho d Λ κ) (GUEEntry_Sc d Λ κ) :=
    ⟨hL, hGR, hRG, hMR, hMR', hz, hM, hMd, hD, hκ, hκm, hn, hMb1, hc₀, fun a' b' => by
      simpa only [neg_mul] using hdec a' b', hρc, hSS, hg.le, hδ', hδ0, hwd, hΩ⟩
  obtain ⟨hGuu, hG32, hGoff⟩ := GreenCore_crude hM hMd hMb1 hκm hn hδ' hΩ
  have hw := GUEEntry_wardData_of hκ hH hzim hGR hGuu hG32
  -- the Ward and `J`-part constants
  have hLm0 : 0 ≤ min Lm (9 / 4) := by
    refine le_min ?_ (by norm_num)
    exact (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)).trans
      (hLm 0 0)
  have hLmm : ∀ a' b', GreenCore_loop G a' b' ≤ min Lm (9 / 4) := fun a' b' =>
    le_min (hLm a' b') (GUEEntry_loop_le G hG32 a' b')
  have hMxx : ∀ x', M x' x' = m := fun x' => by simp [hM, hMd]
  have hJ := GUEEntry_J hH hzim hGR hMxx hκ hmim hδ' hΩ hLmm
  have hΦ0 : 0 ≤ Φ := by linarith
  have hc2 : 0 ≤ 2 + 18 / κ ^ 2 := by positivity
  have hXiC : 0 ≤ GUEEntry_XiC κ := by unfold GUEEntry_XiC; positivity
  have hΞ3 : 3 * Φ * ((2 + 18 / κ ^ 2) * ((3 / 2) / z.im) / (((W * L) ^ d : ℕ) : ℝ)) ≤
      GUEEntry_XiC κ * Φ * min Lm (9 / 4) := by
    have e : (2 + 18 / κ ^ 2) * ((3 / 2) / z.im) / (((W * L) ^ d : ℕ) : ℝ) =
        (2 + 18 / κ ^ 2) * ((3 / 2) / z.im / (((W * L) ^ d : ℕ) : ℝ)) := by ring
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left hJ hc2
    have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 3 * Φ by positivity)
    refine h2.trans (le_of_eq ?_)
    unfold GUEEntry_XiC
    field_simp
    ring
  have hΞ0 : 0 ≤ GUEEntry_XiC κ * Φ * min Lm (9 / 4) := by positivity
  have hXr := GUEEntry_X_row hw ha hb hu1 hΦ0 hΞ3 hLrow
  have hXc := GUEEntry_X_col hw ha hb hu1 hΦ0 hΞ3 hLcol
  have hQ := GUEEntry_eps1_loc hw ha hb hu1 hΦ0 hΞ3 hLquad
  have he3 : ∀ u, ‖(b : ℂ) * GUEEntry_e3 G u‖ ^ 2 ≤ 81 * min Lm (9 / 4) / κ ^ 4 := by
    intro u
    have h1 := GUEEntry_e3_norm hw hb (by linarith) u
    have h2 : (2 / κ) * ((3 / 2) / z.im / (((W * L) ^ d : ℕ) : ℝ)) ≤ (2 / κ) * (3 / κ * min Lm (9 / 4)) :=
      mul_le_mul_of_nonneg_left hJ (by positivity)
    have h3 := (h1.trans h2)
    have h4 : ‖(b : ℂ) * GUEEntry_e3 G u‖ ^ 2 ≤ ((2 / κ) * (3 / κ * min Lm (9 / 4))) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h3 2
    refine h4.trans ?_
    have h5 : min Lm (9 / 4) ≤ 9 / 4 := min_le_right _ _
    have e : ((2 / κ) * (3 / κ * min Lm (9 / 4))) ^ 2 = 36 * min Lm (9 / 4) * min Lm (9 / 4) / κ ^ 4 := by
      field_simp; ring
    rw [e]
    have : 36 * min Lm (9 / 4) * min Lm (9 / 4) ≤ 81 * min Lm (9 / 4) := by nlinarith
    exact div_le_div_of_nonneg_right this (by positivity)
  have hdiag : ∀ i, ‖X i i‖ ^ 2 ≤ Φ * ((W : ℝ) ^ d)⁻¹ := fun i =>
    (hLdiag i).trans (mul_le_mul_of_nonneg_left (GUEEntry_Smv_diag_le ha hb hu1.le i) hΦ0)
  have hC1 : 8 * GUEEntry_rho d Λ κ * ((BAct_rate d Λ κ)⁻¹ * GUEEntry_Sc d Λ κ) * GreenCore_theta d κ Φ δ g ≤ 1 := by
    have hρ0 : 0 ≤ GUEEntry_rho d Λ κ := by unfold GUEEntry_rho expC; positivity
    have hS0 : 0 ≤ GUEEntry_Sc d Λ κ := by unfold GUEEntry_Sc expC; positivity
    have hθ : GreenCore_theta d κ Φ δ g ≤ ((4 / κ ^ 2) * (2 * d * Λ + (1 + 2 * d * Λ) / κ) ^ 2 + 26 / κ ^ 2) * (Φ * δ ^ 2) := by
      unfold GreenCore_theta
      have h1 : 2 * (d : ℝ) * g ≤ 2 * d * Λ := by
        have : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
        nlinarith
      have h2 : (2 * d * g + (1 + 2 * d * g) / κ) ≤ 2 * d * Λ + (1 + 2 * d * Λ) / κ := by
        have : (1 + 2 * d * g) / κ ≤ (1 + 2 * d * Λ) / κ := div_le_div_of_nonneg_right (by linarith) hκ.le
        linarith
      have h3 : (2 * d * g + (1 + 2 * d * g) / κ) ^ 2 ≤ (2 * d * Λ + (1 + 2 * d * Λ) / κ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h2 2
      have h4 : δ ^ 2 ≤ Φ * δ ^ 2 := by nlinarith [sq_nonneg δ]
      have h5 : (4 / κ ^ 2) * (2 * d * g + (1 + 2 * d * g) / κ) ^ 2 * δ ^ 2 ≤
          (4 / κ ^ 2) * (2 * d * Λ + (1 + 2 * d * Λ) / κ) ^ 2 * (Φ * δ ^ 2) := by
        gcongr
      nlinarith [h5]
    calc 8 * GUEEntry_rho d Λ κ * ((BAct_rate d Λ κ)⁻¹ * GUEEntry_Sc d Λ κ) * GreenCore_theta d κ Φ δ g
        ≤ 8 * GUEEntry_rho d Λ κ * ((BAct_rate d Λ κ)⁻¹ * GUEEntry_Sc d Λ κ) *
          (((4 / κ ^ 2) * (2 * d * Λ + (1 + 2 * d * Λ) / κ) ^ 2 + 26 / κ ^ 2) * (Φ * δ ^ 2)) :=
          mul_le_mul_of_nonneg_left hθ (by positivity)
      _ = GUEEntry_cs d Λ κ * Φ * δ ^ 2 := by unfold GUEEntry_cs; ring
      _ ≤ 1 := hΦδ
  have hρp : 0 < GUEEntry_rho d Λ κ := by unfold GUEEntry_rho expC; positivity
  have hKth0 : 0 ≤ GUEEntry_Kth κ := by unfold GUEEntry_Kth; positivity
  have hKbd : 0 < GUEEntry_Kbd d Λ κ := by unfold GUEEntry_Kbd; positivity
  have hKδ : GUEEntry_rho d Λ κ * (1 + 1 * GUEEntry_Kth κ) * δ ≤ 1 / 2 := by
    have h1 : δ ≤ 1 / (2 * GUEEntry_Kbd d Λ κ) := hδ.trans (min_le_right _ _)
    have h2 : GUEEntry_Kbd d Λ κ * δ ≤ 1 / 2 := by
      calc GUEEntry_Kbd d Λ κ * δ ≤ GUEEntry_Kbd d Λ κ * (1 / (2 * GUEEntry_Kbd d Λ κ)) :=
            mul_le_mul_of_nonneg_left h1 hKbd.le
        _ = 1 / 2 := by field_simp
    exact h2
  have hstab : ∀ (v : Zd d L → ℂ) (B : ℝ), (∀ x', ‖v x' - ∑ y', (BAMB d L g (E : ℂ) m y' x' * BAMB d L g (E : ℂ) m x' y') *
      ((a : ℂ) * v y' + (b : ℂ) * ((((L ^ d : ℕ) : ℂ))⁻¹ * ∑ z', v z'))‖ ≤ B) → ∀ x', ‖v x'‖ ≤ GUEEntry_Kth κ * B := by
    intro v B hv x'
    have := stable_mixBA d L hκ hr ha hb hu1 v B (fun x'' => by simpa [BAMss, BAMsigma] using hv x'') x'
    simpa [GUEEntry_Kth, mul_assoc] using this
  have hcore := GUEEntry_core (Kθ := GUEEntry_Kth κ) (ρ₂ := 1) (E3b := 81 * min Lm (9 / 4) / κ ^ 4) hS ha hb
    hu1.le hΦ hΞ0 hXr hXc hQ he3 hdiag hC1 hLmm hLm0 hKth0 hρr (fun a' c => by simpa using hρ₂ a' c) hstab hKδ x y
  have hw0 : 0 ≤ ((W : ℝ) ^ d)⁻¹ := (GreenCore_w_pos (d := d) (W := W)).le
  have hδ1 : δ ≤ 1 := hδ'.trans (by linarith)
  have hfin := GUEEntry_final d (g := g) (Λ := Λ) (δ := δ) (Φ := Φ) (Lm := min Lm (9 / 4)) (w₀ := ((W : ℝ) ^ d)⁻¹)
    hκ hc₀ hg.le hgΛ hδ0 hδ1 hΦ hLm0 hw0
  have hCΦ : 0 ≤ GUEEntry_C d Λ κ * Φ ^ 2 := by
    unfold GUEEntry_C GUEEntry_CAb GUEEntry_CXb GUEEntry_CRb GUEEntry_CA GUEEntry_CX GUEEntry_CR GUEEntry_Kbd
      GUEEntry_rho GUEEntry_Sc GUEEntry_XiC expC
    positivity
  calc ‖G x y - M x y‖ ^ 2 ≤ _ := hcore
    _ ≤ GUEEntry_C d Λ κ * Φ ^ 2 * (min Lm (9 / 4) + ((W : ℝ) ^ d)⁻¹) := hfin
    _ ≤ GUEEntry_C d Λ κ * Φ ^ 2 * (Lm + ((W : ℝ) ^ d)⁻¹) :=
        mul_le_mul_of_nonneg_left (by have := min_le_left Lm (9 / 4); linarith) hCΦ

end Det

end RBM.BA
