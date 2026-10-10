/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.Step1Boot
import RBM3D.BA.GreenLDE
import RBM3D.BA.Prop5Short
import RBM3D.BA.Step1
import RBM3D.BA.Step1Fam

/-!
# The block Anderson entrywise layer with the deterministic part (BA-G3a)

Ticket T2390 (design gate `docs/reports/T2390-prove.md` (a), (a′), (G), stage 1b).  Paper:
`paper/tex/7_8_light_weight.tex` (`7_8:line`, `lem_GbEXP_BA` `:1916-1946`), band
`paper/tex/3_5_Loop_Hierarchy.tex`.  Everything here is deterministic, for one sample: the large
deviation inputs of `BALDEin` (T2389) enter as the per-sample events `LDERow`, `LDECol`, `LDEQuad`,
the diagonal bound, and `Ω = {‖G - M‖_max ≤ δ}`.  Sites are `u = (a, o)` of `Vtx d L W`
(block `a`, offset `o`), `M = M^{(B)} ⊗ I`, `D = g₀ Ψ`, `H = D + X`, `G = (H - z)⁻¹`,
`Δ = G - M`, `w₀ = W^{-d}`.
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

section Schur
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem GreenCore_sum_erase_green_mul {R G : Matrix ι ι ℂ} (hGR : G * R = 1) (u a b : ι) :
    ∑ l ∈ univ.erase u, G a l * R l b = (if a = b then (1 : ℂ) else 0) - G a u * R u b := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ u)]
  have h := congrArg (fun X : Matrix ι ι ℂ => X a b) hGR
  simp only [Matrix.mul_apply, Matrix.one_apply] at h
  rw [h]

private theorem GreenCore_sum_erase_mul_green {R G : Matrix ι ι ℂ} (hRG : R * G = 1) (u a b : ι) :
    ∑ k ∈ univ.erase u, R a k * G k b = (if a = b then (1 : ℂ) else 0) - R a u * G u b := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ u)]
  have h := congrArg (fun X : Matrix ι ι ℂ => X a b) hRG
  simp only [Matrix.mul_apply, Matrix.one_apply] at h
  rw [h]

/-- Column Schur: `G_{vu} = -G_{uu} Σ_{k≠u} G^{(u)}_{vk} H_{ku}` for `v ≠ u`. -/
private theorem GreenCore_col_schur {R G : Matrix ι ι ℂ} (hGR : G * R = 1) {u v : ι}
    (hGuu : G u u ≠ 0) (hvu : v ≠ u) :
    G v u = -G u u * ∑ k ∈ univ.erase u, greenMinor G u v k * R k u := by
  have hsplit : ∑ k ∈ univ.erase u, greenMinor G u v k * R k u
      = (∑ k ∈ univ.erase u, G v k * R k u) - (G v u / G u u) * ∑ k ∈ univ.erase u, G u k * R k u := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [greenMinor]; ring
  rw [hsplit, GreenCore_sum_erase_green_mul hGR, GreenCore_sum_erase_green_mul hGR, ite_eq_right hvu, ite_eq_left rfl]
  field_simp
  ring

/-- Row Schur: `G_{uw} = -G_{uu} Σ_{l≠u} R_{ul} G^{(u)}_{lw}` for `w ≠ u`. -/
private theorem GreenCore_row_schur {R G : Matrix ι ι ℂ} (hRG : R * G = 1) {u w : ι}
    (hGuu : G u u ≠ 0) (hwu : u ≠ w) :
    G u w = -G u u * ∑ l ∈ univ.erase u, R u l * greenMinor G u l w := by
  have hsplit : ∑ l ∈ univ.erase u, R u l * greenMinor G u l w
      = (∑ l ∈ univ.erase u, R u l * G l w) - (G u w / G u u) * ∑ l ∈ univ.erase u, R u l * G l u := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [greenMinor]; ring
  rw [hsplit, GreenCore_sum_erase_mul_green hRG, GreenCore_sum_erase_mul_green hRG, ite_eq_right hwu, ite_eq_left rfl]
  field_simp
  ring


/-- **(E1)** (`7_8:1930` display, row form): for `G (H - z) = 1`, `G_{uu} ≠ 0` and any matrix `X`,
`Σ_v X_{uv} G_{vy} = (X_{uu} - Q_u) G_{uy} + 𝔛_{uy}`, `Q_u = Σ_{k,l≠u} X_{uk} G^{(u)}_{kl} H_{lu}`,
`𝔛_{uy} = Σ_{v≠u} X_{uv} G^{(u)}_{vy}`. -/
theorem GreenCore_E1 {H X G : Matrix ι ι ℂ} {z : ℂ} (hGM : G * (H - z • (1 : Matrix ι ι ℂ)) = 1)
    (u y : ι) (hGuu : G u u ≠ 0) :
    ∑ v, X u v * G v y =
      (X u u - ∑ k ∈ univ.erase u, ∑ l ∈ univ.erase u, X u k * greenMinor G u k l * H l u) * G u y +
        ∑ v ∈ univ.erase u, X u v * greenMinor G u v y := by
  have hcol : ∀ v ∈ univ.erase u, G v u = -G u u * ∑ k ∈ univ.erase u, greenMinor G u v k * H k u := by
    intro v hv
    rw [GreenCore_col_schur hGM hGuu (Finset.ne_of_mem_erase hv)]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [sub_smul_one_apply_ne H z (Finset.ne_of_mem_erase hk)]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u)]
  have h1 : ∀ v ∈ univ.erase u, X u v * G v y =
      X u v * greenMinor G u v y + (G u y / G u u) * (X u v * G v u) := by
    intro v _
    rw [greenMinor]; field_simp; ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h2 : ∑ v ∈ univ.erase u, X u v * G v u =
      -G u u * ∑ k ∈ univ.erase u, ∑ l ∈ univ.erase u, X u k * greenMinor G u k l * H l u := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [hcol v hv, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [h2]
  field_simp
  ring

/-- **(E1′)** (column form): for `(H - z) G = 1`, `G_{ww} ≠ 0` and any matrix `X`,
`Σ_k G_{vk} X_{kw} = G_{vw} (X_{ww} - Q'_w) + 𝔛'_{vw}`, `Q'_w = Σ_{l,k≠w} H_{wl} G^{(w)}_{lk} X_{kw}`,
`𝔛'_{vw} = Σ_{k≠w} G^{(w)}_{vk} X_{kw}`. -/
theorem GreenCore_E1' {H X G : Matrix ι ι ℂ} {z : ℂ} (hMG : (H - z • (1 : Matrix ι ι ℂ)) * G = 1)
    (v w : ι) (hGww : G w w ≠ 0) :
    ∑ k, G v k * X k w =
      G v w * (X w w - ∑ l ∈ univ.erase w, ∑ k ∈ univ.erase w, H w l * greenMinor G w l k * X k w) +
        ∑ k ∈ univ.erase w, greenMinor G w v k * X k w := by
  have hrow : ∀ k ∈ univ.erase w, G w k = -G w w * ∑ l ∈ univ.erase w, H w l * greenMinor G w l k := by
    intro k hk
    rw [GreenCore_row_schur hMG hGww (Finset.ne_of_mem_erase hk).symm]
    congr 1
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [sub_smul_one_apply_ne H z (Finset.ne_of_mem_erase hl).symm]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w)]
  have h1 : ∀ k ∈ univ.erase w, G v k * X k w =
      greenMinor G w v k * X k w + (G v w / G w w) * (G w k * X k w) := by
    intro k _
    rw [greenMinor]; field_simp; ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h2 : ∑ k ∈ univ.erase w, G w k * X k w =
      -G w w * ∑ l ∈ univ.erase w, ∑ k ∈ univ.erase w, H w l * greenMinor G w l k * X k w := by
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hrow k hk, mul_assoc, Finset.sum_mul, Finset.mul_sum]
  rw [h2]
  field_simp
  ring

end Schur

section Setting
variable {d L W : ℕ} [NeZero L] [NeZero W]

theorem GreenCore_w_mul : ((W : ℝ) ^ d)⁻¹ * ((W : ℝ) ^ d) = 1 :=
  inv_mul_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W)))

theorem GreenCore_w_pos : 0 < ((W : ℝ) ^ d)⁻¹ :=
  inv_pos.2 (pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)) d)

theorem GreenCore_avg_le {f : Fin (W ^ d) → ℝ} {c : ℝ} (h : ∀ o, f o ≤ c) :
    ((W : ℝ) ^ d)⁻¹ * ∑ o, f o ≤ c := by
  have h1 : ∑ o, f o ≤ ∑ _o : Fin (W ^ d), c := Finset.sum_le_sum fun o _ => h o
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  calc ((W : ℝ) ^ d)⁻¹ * ∑ o, f o ≤ ((W : ℝ) ^ d)⁻¹ * (((W ^ d : ℕ) : ℝ) * c) :=
        mul_le_mul_of_nonneg_left h1 GreenCore_w_pos.le
    _ = c := by rw [Nat.cast_pow, ← mul_assoc, GreenCore_w_mul, one_mul]

theorem GreenCore_svar0 (u v : Vtx d L W) :
    svar d L W 0 u v = if u.1 = v.1 then ((W : ℝ) ^ d)⁻¹ else 0 := by
  by_cases h : u.1 = v.1
  · simp [svar, SBR, sbKernelR, h]
  · have h' : u.1 - v.1 ≠ 0 := sub_ne_zero.2 h
    simp [svar, SBR, sbKernelR, h, h']

/-- the offset average over a block, from the sum over all sites weighted by the profile -/
theorem GreenCore_sum_block (i : Vtx d L W) (f : Vtx d L W → ℝ) :
    ∑ k : Vtx d L W, svar d L W 0 i k * f k = ((W : ℝ) ^ d)⁻¹ * ∑ o, f (i.1, o) := by
  simp only [GreenCore_svar0]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i.1]
  · simp [Finset.mul_sum]
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem GreenCore_sum_block' (i : Vtx d L W) (f : Vtx d L W → ℝ) :
    ∑ k : Vtx d L W, f k * svar d L W 0 k i = ((W : ℝ) ^ d)⁻¹ * ∑ o, f (i.1, o) := by
  have : ∀ k, f k * svar d L W 0 k i = svar d L W 0 i k * f k := fun k => by
    rw [mul_comm, svar_comm]
  simp only [this]
  exact GreenCore_sum_block i f

theorem GreenCore_sum_block_c (i : Vtx d L W) (f : Vtx d L W → ℂ) :
    ∑ k : Vtx d L W, ((svar d L W 0 i k : ℝ) : ℂ) * f k = (((W : ℝ) ^ d)⁻¹ : ℝ) * ∑ o, f (i.1, o) := by
  simp only [GreenCore_svar0]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i.1]
  · simp [Finset.mul_sum]
  · intro b _ hb; simp [Ne.symm hb]
  · simp

variable {G : Matrix (Vtx d L W) (Vtx d L W) ℂ}

theorem GreenCore_minor_left {w : Vtx d L W} (h : G w w ≠ 0) (l : Vtx d L W) : greenMinor G w w l = 0 := by
  rw [greenMinor]; field_simp; ring

theorem GreenCore_minor_right {w : Vtx d L W} (h : G w w ≠ 0) (x : Vtx d L W) : greenMinor G w x w = 0 := by
  rw [greenMinor]; field_simp; ring

theorem GreenCore_ldeRowRHS {u : Vtx d L W} (h : G u u ≠ 0) (y : Vtx d L W) :
    ldeRowRHS (svar d L W 0) G u y = ((W : ℝ) ^ d)⁻¹ * ∑ o, ‖greenMinor G u (u.1, o) y‖ ^ 2 := by
  rw [ldeRowRHS, Finset.sum_erase _ (by rw [GreenCore_minor_left h]; simp)]
  exact GreenCore_sum_block u (fun k => ‖greenMinor G u k y‖ ^ 2)

theorem GreenCore_ldeColRHS {w : Vtx d L W} (h : G w w ≠ 0) (x : Vtx d L W) :
    ldeColRHS (svar d L W 0) G x w = ((W : ℝ) ^ d)⁻¹ * ∑ o, ‖greenMinor G w x (w.1, o)‖ ^ 2 := by
  rw [ldeColRHS, Finset.sum_erase _ (by rw [GreenCore_minor_right h]; simp)]
  exact GreenCore_sum_block' w (fun k => ‖greenMinor G w x k‖ ^ 2)

theorem GreenCore_ldeQuadRHS {w : Vtx d L W} (h : G w w ≠ 0) :
    ldeQuadRHS (svar d L W 0) G w = (((W : ℝ) ^ d)⁻¹) ^ 2 *
      ∑ o, ∑ o', ‖greenMinor G w (w.1, o) (w.1, o')‖ ^ 2 := by
  rw [ldeQuadRHS, Finset.sum_erase _ (by simp [GreenCore_minor_left h])]
  have h1 : ∀ k : Vtx d L W, ∑ l ∈ univ.erase w, svar d L W 0 w k * ‖greenMinor G w k l‖ ^ 2 * svar d L W 0 l w =
      svar d L W 0 w k * (((W : ℝ) ^ d)⁻¹ * ∑ o', ‖greenMinor G w k (w.1, o')‖ ^ 2) := by
    intro k
    rw [Finset.sum_erase _ (by simp [GreenCore_minor_right h]), ← GreenCore_sum_block' w
      (fun l => ‖greenMinor G w k l‖ ^ 2), Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [Finset.sum_congr rfl (fun k _ => h1 k), GreenCore_sum_block w
    (fun k => ((W : ℝ) ^ d)⁻¹ * ∑ o', ‖greenMinor G w k (w.1, o')‖ ^ 2), ← Finset.mul_sum]
  ring

end Setting

section Closure

variable {B : Type*} [Fintype B]

/-- **The weighted ratio-norm closure**: if `r ≤ f + P r` pointwise and the kernel `P ≥ 0` is a contraction with
constant `1/2` for the weight `e^{ν dd(c,b)}`, then `r_c ≤ 2 Σ_b e^{-ν dd(c,b)} f_b`. -/
theorem GreenCore_closure [Nonempty B] (dd : B → B → ℝ) (hd0 : ∀ a, dd a a = 0)
    (htri : ∀ a b c, dd a c ≤ dd a b + dd b c)
    {ν : ℝ} (hν : 0 ≤ ν) (P : B → B → ℝ) (hP : ∀ c b, 0 ≤ P c b)
    (hP2 : ∀ c, ∑ b, P c b * Real.exp (ν * dd c b) ≤ 1 / 2) (r f : B → ℝ)
    (hr : ∀ c, 0 ≤ r c) (hf : ∀ c, 0 ≤ f c) (hrf : ∀ c, r c ≤ f c + ∑ b, P c b * r b)
    (hF : ∀ c, 0 < ∑ b, Real.exp (-ν * dd c b) * f b) (c : B) :
    r c ≤ 2 * ∑ b, Real.exp (-ν * dd c b) * f b := by
  set F : B → ℝ := fun c => ∑ b, Real.exp (-ν * dd c b) * f b with hFdef
  -- `P F ≤ F / 2`
  have hPF : ∀ c, ∑ b, P c b * F b ≤ F c / 2 := by
    intro c
    have h1 : ∀ b, F b ≤ Real.exp (ν * dd c b) * F c := by
      intro b
      rw [hFdef]
      simp only
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun b' _ => ?_
      have : Real.exp (-ν * dd b b') ≤ Real.exp (ν * dd c b) * Real.exp (-ν * dd c b') := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have := htri c b b'
        nlinarith [mul_le_mul_of_nonneg_left this hν]
      calc Real.exp (-ν * dd b b') * f b' ≤ (Real.exp (ν * dd c b) * Real.exp (-ν * dd c b')) * f b' :=
            mul_le_mul_of_nonneg_right this (hf b')
        _ = Real.exp (ν * dd c b) * (Real.exp (-ν * dd c b') * f b') := by ring
    calc ∑ b, P c b * F b ≤ ∑ b, P c b * (Real.exp (ν * dd c b) * F c) :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (h1 b) (hP c b)
      _ = (∑ b, P c b * Real.exp (ν * dd c b)) * F c := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun b _ => by ring
      _ ≤ (1 / 2) * F c := mul_le_mul_of_nonneg_right (hP2 c) (hF c).le
      _ = F c / 2 := by ring
  have hfF : ∀ c, f c ≤ F c := by
    intro c
    have h0 : Real.exp (-ν * dd c c) * f c ≤ F c :=
      Finset.single_le_sum (f := fun b => Real.exp (-ν * dd c b) * f b)
        (fun b _ => mul_nonneg (Real.exp_pos _).le (hf b)) (Finset.mem_univ c)
    rwa [hd0, mul_zero, Real.exp_zero, one_mul] at h0
  -- the maximum of `r / F`
  obtain ⟨c₀, hc₀⟩ := Finite.exists_max (fun c => r c / F c)
  set lam := r c₀ / F c₀ with hlam
  have hlam0 : 0 ≤ lam := div_nonneg (hr c₀) (hF c₀).le
  have hrl : ∀ c, r c ≤ lam * F c := by
    intro c
    have := hc₀ c
    rw [div_le_iff₀ (hF c)] at this
    exact this
  have h1 : r c₀ ≤ F c₀ + lam * (F c₀ / 2) := by
    calc r c₀ ≤ f c₀ + ∑ b, P c₀ b * r b := hrf c₀
      _ ≤ F c₀ + ∑ b, P c₀ b * (lam * F b) :=
          add_le_add (hfF c₀) (Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hrl b) (hP c₀ b))
      _ = F c₀ + lam * ∑ b, P c₀ b * F b := by
          rw [Finset.mul_sum]; congr 1; exact Finset.sum_congr rfl fun b _ => by ring
      _ ≤ F c₀ + lam * (F c₀ / 2) := add_le_add le_rfl (mul_le_mul_of_nonneg_left (hPF c₀) hlam0)
  have h2 : lam * F c₀ = r c₀ := by rw [hlam, div_mul_cancel₀ _ (hF c₀).ne']
  have h3 : lam ≤ 2 := by
    by_contra hc
    have hc := not_le.mp hc
    nlinarith [hF c₀]
  calc r c ≤ lam * F c := hrl c
    _ ≤ 2 * F c := mul_le_mul_of_nonneg_right h3 (hF c).le


/-- `Σ_{b'} e^{-ν dd(c,b')} |M_{ab'}|² ≤ c₀⁻² S e^{-ν dd(a,c)}` (rate `ν = c₀/2`). -/
theorem GreenCore_conv1 (dd : B → B → ℝ) (hnn : ∀ a b, 0 ≤ dd a b) (hsymm : ∀ a b, dd a b = dd b a)
    (htri : ∀ a b c, dd a c ≤ dd a b + dd b c)
    (Mb : B → B → ℂ) {c₀ S : ℝ} (hc₀ : 0 < c₀)
    (hdec : ∀ a b, ‖Mb a b‖ ≤ c₀⁻¹ * Real.exp (-c₀ * dd a b))
    (hS : ∀ a, ∑ b, Real.exp (-(c₀ / 2) * dd a b) ≤ S) (a c : B) :
    ∑ b', Real.exp (-(c₀ / 2) * dd c b') * ‖Mb a b'‖ ^ 2 ≤ c₀⁻¹ ^ 2 * S * Real.exp (-(c₀ / 2) * dd a c) := by
  have hterm : ∀ b', Real.exp (-(c₀ / 2) * dd c b') * ‖Mb a b'‖ ^ 2 ≤
      c₀⁻¹ ^ 2 * Real.exp (-(c₀ / 2) * dd a c) * Real.exp (-(c₀ / 2) * dd a b') := by
    intro b'
    have h1 : ‖Mb a b'‖ ^ 2 ≤ (c₀⁻¹ * Real.exp (-c₀ * dd a b')) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hdec a b') 2
    have h2 : Real.exp (-(c₀ / 2) * dd c b') * (c₀⁻¹ * Real.exp (-c₀ * dd a b')) ^ 2 ≤
        c₀⁻¹ ^ 2 * Real.exp (-(c₀ / 2) * dd a c) * Real.exp (-(c₀ / 2) * dd a b') := by
      have e1 : (c₀⁻¹ * Real.exp (-c₀ * dd a b')) ^ 2 = c₀⁻¹ ^ 2 * Real.exp (-(2 * c₀) * dd a b') := by
        rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
      rw [e1]
      have e2 : Real.exp (-(c₀ / 2) * dd c b') * (c₀⁻¹ ^ 2 * Real.exp (-(2 * c₀) * dd a b')) =
          c₀⁻¹ ^ 2 * Real.exp (-(c₀ / 2) * dd c b' + -(2 * c₀) * dd a b') := by
        rw [Real.exp_add]; ring
      rw [e2, mul_assoc, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
      have h5 := htri a b' c
      rw [hsymm b' c] at h5
      have h3 := hnn a b'
      nlinarith [mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ c₀ / 2), mul_nonneg hc₀.le h3]
    calc Real.exp (-(c₀ / 2) * dd c b') * ‖Mb a b'‖ ^ 2
        ≤ Real.exp (-(c₀ / 2) * dd c b') * (c₀⁻¹ * Real.exp (-c₀ * dd a b')) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ ≤ _ := h2
  calc ∑ b', Real.exp (-(c₀ / 2) * dd c b') * ‖Mb a b'‖ ^ 2
      ≤ ∑ b', c₀⁻¹ ^ 2 * Real.exp (-(c₀ / 2) * dd a c) * Real.exp (-(c₀ / 2) * dd a b') :=
        Finset.sum_le_sum fun b' _ => hterm b'
    _ = c₀⁻¹ ^ 2 * Real.exp (-(c₀ / 2) * dd a c) * ∑ b', Real.exp (-(c₀ / 2) * dd a b') := by
        rw [Finset.mul_sum]
    _ ≤ c₀⁻¹ ^ 2 * Real.exp (-(c₀ / 2) * dd a c) * S :=
        mul_le_mul_of_nonneg_left (hS a) (by positivity)
    _ = c₀⁻¹ ^ 2 * S * Real.exp (-(c₀ / 2) * dd a c) := by ring


/-- `Σ_{b'} e^{-ν dd(c,b')} |M_{b''b'}| ≤ c₀⁻¹ S e^{-ν dd(c,b'')}` (rate `ν = c₀/2`). -/
theorem GreenCore_conv2 (dd : B → B → ℝ) (hsymm : ∀ a b, dd a b = dd b a)
    (htri : ∀ a b c, dd a c ≤ dd a b + dd b c) (Mb : B → B → ℂ) {c₀ S : ℝ} (hc₀ : 0 < c₀)
    (hdec : ∀ a b, ‖Mb a b‖ ≤ c₀⁻¹ * Real.exp (-c₀ * dd a b))
    (hS : ∀ a, ∑ b, Real.exp (-(c₀ / 2) * dd a b) ≤ S) (c b'' : B) :
    ∑ b', Real.exp (-(c₀ / 2) * dd c b') * ‖Mb b'' b'‖ ≤ c₀⁻¹ * S * Real.exp (-(c₀ / 2) * dd c b'') := by
  have hterm : ∀ b', Real.exp (-(c₀ / 2) * dd c b') * ‖Mb b'' b'‖ ≤
      c₀⁻¹ * Real.exp (-(c₀ / 2) * dd c b'') * Real.exp (-(c₀ / 2) * dd b'' b') := by
    intro b'
    have h1 : Real.exp (-(c₀ / 2) * dd c b') * ‖Mb b'' b'‖ ≤
        Real.exp (-(c₀ / 2) * dd c b') * (c₀⁻¹ * Real.exp (-c₀ * dd b'' b')) :=
      mul_le_mul_of_nonneg_left (hdec b'' b') (Real.exp_pos _).le
    have h2 : Real.exp (-(c₀ / 2) * dd c b') * (c₀⁻¹ * Real.exp (-c₀ * dd b'' b')) =
        c₀⁻¹ * Real.exp (-(c₀ / 2) * dd c b' + -c₀ * dd b'' b') := by
      rw [Real.exp_add]; ring
    have h3 : c₀⁻¹ * Real.exp (-(c₀ / 2) * dd c b' + -c₀ * dd b'' b') ≤
        c₀⁻¹ * Real.exp (-(c₀ / 2) * dd c b'' + -(c₀ / 2) * dd b'' b') := by
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
      have h5 := htri c b' b''
      rw [hsymm b' b''] at h5
      nlinarith [mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ c₀ / 2)]
    calc Real.exp (-(c₀ / 2) * dd c b') * ‖Mb b'' b'‖
        ≤ Real.exp (-(c₀ / 2) * dd c b') * (c₀⁻¹ * Real.exp (-c₀ * dd b'' b')) := h1
      _ = c₀⁻¹ * Real.exp (-(c₀ / 2) * dd c b' + -c₀ * dd b'' b') := h2
      _ ≤ c₀⁻¹ * Real.exp (-(c₀ / 2) * dd c b'' + -(c₀ / 2) * dd b'' b') := h3
      _ = c₀⁻¹ * Real.exp (-(c₀ / 2) * dd c b'') * Real.exp (-(c₀ / 2) * dd b'' b') := by
          rw [Real.exp_add]; ring
  calc ∑ b', Real.exp (-(c₀ / 2) * dd c b') * ‖Mb b'' b'‖
      ≤ ∑ b', c₀⁻¹ * Real.exp (-(c₀ / 2) * dd c b'') * Real.exp (-(c₀ / 2) * dd b'' b') :=
        Finset.sum_le_sum fun b' _ => hterm b'
    _ = c₀⁻¹ * Real.exp (-(c₀ / 2) * dd c b'') * ∑ b', Real.exp (-(c₀ / 2) * dd b'' b') := by
        rw [Finset.mul_sum]
    _ ≤ c₀⁻¹ * Real.exp (-(c₀ / 2) * dd c b'') * S :=
        mul_le_mul_of_nonneg_left (hS b'') (by positivity)
    _ = c₀⁻¹ * S * Real.exp (-(c₀ / 2) * dd c b'') := by ring


/-- `Σ_b |M_{bc}| e^{ν dd(c,b)} ≤ c₀⁻¹ S` for `ν = c₀/2` (from the decay and the lattice sum). -/
theorem GreenCore_rhoe (dd : B → B → ℝ) (hsymm : ∀ a b, dd a b = dd b a) (Mb : B → B → ℂ) {c₀ S : ℝ} (hc₀ : 0 < c₀)
    (hdec : ∀ a b, ‖Mb a b‖ ≤ c₀⁻¹ * Real.exp (-c₀ * dd a b))
    (hS : ∀ a, ∑ b, Real.exp (-(c₀ / 2) * dd a b) ≤ S) (c : B) :
    ∑ b, ‖Mb b c‖ * Real.exp ((c₀ / 2) * dd c b) ≤ c₀⁻¹ * S := by
  calc ∑ b, ‖Mb b c‖ * Real.exp ((c₀ / 2) * dd c b) ≤ ∑ b, c₀⁻¹ * Real.exp (-(c₀ / 2) * dd c b) := by
        refine Finset.sum_le_sum fun b _ => ?_
        have h1 := mul_le_mul_of_nonneg_right (hdec b c) (Real.exp_pos ((c₀ / 2) * dd c b)).le
        refine h1.trans (le_of_eq ?_)
        rw [mul_assoc, ← Real.exp_add, hsymm b c]; congr 2; ring
    _ = c₀⁻¹ * ∑ b, Real.exp (-(c₀ / 2) * dd c b) := by rw [Finset.mul_sum]
    _ ≤ c₀⁻¹ * S := mul_le_mul_of_nonneg_left (hS c) (inv_nonneg.2 hc₀.le)

/-- **(R*)**, the closure of the two-sided inequality in the weight `e^{-ν dd}`, `ν = c₀/2`
(`docs/reports/T2390-prove.md` (a′) D3.2): from `r_c ≤ 2 w₀ |M_{ac}|² + 8ρΦ Σ_{b''} |M_{b''c}| φ_{b''}² +
4ρϑ Σ_{b'} |M_{b'c}| r_{b'}` and `8ρρeϑ ≤ 1`, `r_c ≤ 4 c₀⁻² S w₀ e^{-ν dd(a,c)} + 16 ρ Φ c₀⁻¹ S Σ_{b''} e^{-ν dd(c,b'')} φ_{b''}²`. -/
theorem GreenCore_Rstar [Nonempty B] (dd : B → B → ℝ) (hd0 : ∀ a, dd a a = 0) (hnn : ∀ a b, 0 ≤ dd a b)
    (hsymm : ∀ a b, dd a b = dd b a) (htri : ∀ a b c, dd a c ≤ dd a b + dd b c)
    (Mb : B → B → ℂ) {c₀ κ ρ ρe S Φ ϑ w₀ : ℝ} (hc₀ : 0 < c₀) (hκ : 0 < κ)
    (hdiag : ∀ a, κ ≤ ‖Mb a a‖) (hdec : ∀ a b, ‖Mb a b‖ ≤ c₀⁻¹ * Real.exp (-c₀ * dd a b))
    (hρe : ∀ c, ∑ b, ‖Mb b c‖ * Real.exp ((c₀ / 2) * dd c b) ≤ ρe)
    (hS : ∀ a, ∑ b, Real.exp (-(c₀ / 2) * dd a b) ≤ S)
    (hw : 0 < w₀) (hρ : 0 ≤ ρ) (hΦ : 0 ≤ Φ) (hϑ : 0 ≤ ϑ) (hC1 : 8 * ρ * ρe * ϑ ≤ 1)
    (a : B) (φ r : B → ℝ) (hr0 : ∀ c, 0 ≤ r c)
    (hrf : ∀ c, r c ≤ 2 * w₀ * ‖Mb a c‖ ^ 2 + 8 * ρ * Φ * ∑ b'', ‖Mb b'' c‖ * φ b'' ^ 2 +
        4 * ρ * ϑ * ∑ b', ‖Mb b' c‖ * r b') (c : B) :
    r c ≤ 4 * c₀⁻¹ ^ 2 * S * w₀ * Real.exp (-(c₀ / 2) * dd a c) +
      16 * ρ * Φ * c₀⁻¹ * S * ∑ b'', Real.exp (-(c₀ / 2) * dd c b'') * φ b'' ^ 2 := by
  have hν : 0 ≤ c₀ / 2 := by positivity
  set f : B → ℝ := fun c => 2 * w₀ * ‖Mb a c‖ ^ 2 + 8 * ρ * Φ * ∑ b'', ‖Mb b'' c‖ * φ b'' ^ 2 with hf
  have hf0 : ∀ c, 0 ≤ f c := fun c => by
    refine add_nonneg (by positivity) (mul_nonneg (by positivity) (Finset.sum_nonneg fun b _ => by positivity))
  have hP0 : 0 ≤ 4 * ρ * ϑ := by positivity
  have hPsum : ∀ c, ∑ b, 4 * ρ * ϑ * ‖Mb b c‖ * Real.exp ((c₀ / 2) * dd c b) ≤ 1 / 2 := by
    intro c
    calc ∑ b, 4 * ρ * ϑ * ‖Mb b c‖ * Real.exp ((c₀ / 2) * dd c b)
        = 4 * ρ * ϑ * ∑ b, ‖Mb b c‖ * Real.exp ((c₀ / 2) * dd c b) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
      _ ≤ 4 * ρ * ϑ * ρe := mul_le_mul_of_nonneg_left (hρe c) hP0
      _ ≤ 1 / 2 := by nlinarith
  have hFpos : ∀ c, 0 < ∑ b, Real.exp (-(c₀ / 2) * dd c b) * f b := by
    intro c
    have h1 : Real.exp (-(c₀ / 2) * dd c a) * f a ≤ ∑ b, Real.exp (-(c₀ / 2) * dd c b) * f b :=
      Finset.single_le_sum (f := fun b => Real.exp (-(c₀ / 2) * dd c b) * f b)
        (fun b _ => mul_nonneg (Real.exp_pos _).le (hf0 b)) (Finset.mem_univ a)
    refine lt_of_lt_of_le ?_ h1
    refine mul_pos (Real.exp_pos _) ?_
    have : 0 < 2 * w₀ * ‖Mb a a‖ ^ 2 := by
      have h1 := hdiag a
      have h2 : 0 < ‖Mb a a‖ := lt_of_lt_of_le hκ h1
      positivity
    exact lt_of_lt_of_le this (le_add_of_nonneg_right (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun b _ => by positivity)))
  have hcl := GreenCore_closure dd hd0 htri hν (fun c b => 4 * ρ * ϑ * ‖Mb b c‖)
    (fun c b => by positivity) (fun c => by simpa only [] using hPsum c) r f hr0 hf0
    (fun c => by
      have := hrf c
      simpa only [hf, Finset.mul_sum, mul_assoc] using this) hFpos c
  refine hcl.trans ?_
  -- evaluate `F`
  have e1 : ∑ b', Real.exp (-(c₀ / 2) * dd c b') * f b' =
      2 * w₀ * ∑ b', Real.exp (-(c₀ / 2) * dd c b') * ‖Mb a b'‖ ^ 2 +
        8 * ρ * Φ * ∑ b'', φ b'' ^ 2 * ∑ b', Real.exp (-(c₀ / 2) * dd c b') * ‖Mb b'' b'‖ := by
    simp only [hf, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun b' _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun b'' _ => Finset.sum_congr rfl fun b' _ => by ring
  have c1 := GreenCore_conv1 dd hnn hsymm htri Mb hc₀ hdec hS a c
  have c2 : ∀ b'', ∑ b', Real.exp (-(c₀ / 2) * dd c b') * ‖Mb b'' b'‖ ≤
      c₀⁻¹ * S * Real.exp (-(c₀ / 2) * dd c b'') := fun b'' => GreenCore_conv2 dd hsymm htri Mb hc₀ hdec hS c b''
  have h3 : ∑ b'', φ b'' ^ 2 * ∑ b', Real.exp (-(c₀ / 2) * dd c b') * ‖Mb b'' b'‖ ≤
      c₀⁻¹ * S * ∑ b'', Real.exp (-(c₀ / 2) * dd c b'') * φ b'' ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b'' _ => ?_
    calc φ b'' ^ 2 * ∑ b', Real.exp (-(c₀ / 2) * dd c b') * ‖Mb b'' b'‖
        ≤ φ b'' ^ 2 * (c₀⁻¹ * S * Real.exp (-(c₀ / 2) * dd c b'')) :=
          mul_le_mul_of_nonneg_left (c2 b'') (sq_nonneg _)
      _ = c₀⁻¹ * S * (Real.exp (-(c₀ / 2) * dd c b'') * φ b'' ^ 2) := by ring
  rw [e1]
  have hS0 : 0 ≤ S := by
    obtain ⟨b⟩ := ‹Nonempty B›
    exact le_trans (Finset.sum_nonneg fun b' _ => (Real.exp_pos _).le) (hS b)
  nlinarith [mul_le_mul_of_nonneg_left c1 (by positivity : (0 : ℝ) ≤ 2 * w₀),
    mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 8 * ρ * Φ)]

end Closure

section Entry
variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `R_{a,y} = W^{-d} Σ_{x∈a} |G_{xy}|²`: the average over the block `a` of the column `y`. -/
def GreenCore_R (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a : Zd d L) (y : Vtx d L W) : ℝ :=
  ((W : ℝ) ^ d)⁻¹ * ∑ o : Fin (W ^ d), ‖G (a, o) y‖ ^ 2

/-- `W^{-d} Σ_{y∈b} |G_{xy}|²`: the average over the block `b` of the row `x`. -/
def GreenCore_Rrow (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (x : Vtx d L W) (b : Zd d L) : ℝ :=
  ((W : ℝ) ^ d)⁻¹ * ∑ o : Fin (W ^ d), ‖G x (b, o)‖ ^ 2

/-- `𝓛^{(2)}_{(-,+),(a,b)} = W^{-2d} Σ_{x∈a, y∈b} |G_{xy}|²` for a Hermitian `H`, `G = (H - z)⁻¹` (`1_2:78`). -/
def GreenCore_loop (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a b : Zd d L) : ℝ :=
  (((W : ℝ) ^ d)⁻¹) ^ 2 * ∑ o : Fin (W ^ d), ∑ o' : Fin (W ^ d), ‖G (a, o) (b, o')‖ ^ 2

/-- `v̄_a = W^{-d} Σ_{k∈a} Δ_{kk}`: the block average of the diagonal of `Δ = G - M`. -/
def GreenCore_vbar (G M : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a : Zd d L) : ℂ :=
  (((W : ℝ) ^ d)⁻¹ : ℝ) * ∑ o : Fin (W ^ d), (G (a, o) (a, o) - M (a, o) (a, o))

/-- `𝔛_{uy} = Σ_{v≠u} X_{uv} G^{(u)}_{vy}` (the row sum of `(4.8)`). -/
def GreenCore_Xrow (G X : Matrix (Vtx d L W) (Vtx d L W) ℂ) (u y : Vtx d L W) : ℂ :=
  ∑ v ∈ univ.erase u, X u v * greenMinor G u v y

/-- `𝔛'_{xw} = Σ_{k≠w} G^{(w)}_{xk} X_{kw}` (the column sum of `(4.8)`). -/
def GreenCore_Xcol (G X : Matrix (Vtx d L W) (Vtx d L W) ℂ) (x w : Vtx d L W) : ℂ :=
  ∑ k ∈ univ.erase w, greenMinor G w x k * X k w

/-- `A_u = t m + X_{uu} - Σ_{k,l≠u} X_{uk} G^{(u)}_{kl} H_{lu}`, `H = D + X` (the random re-entry, row form, (E1)). -/
def GreenCore_Arow (G X D : Matrix (Vtx d L W) (Vtx d L W) ℂ) (t : ℝ) (m : ℂ) (u : Vtx d L W) : ℂ :=
  (t : ℂ) * m + X u u - ∑ k ∈ univ.erase u, ∑ l ∈ univ.erase u, X u k * greenMinor G u k l * (D + X) l u

/-- `A'_w = t m + X_{ww} - Σ_{l,k≠w} H_{wl} G^{(w)}_{lk} X_{kw}`, `H = D + X` (column form, (E1′)). -/
def GreenCore_Acol (G X D : Matrix (Vtx d L W) (Vtx d L W) ℂ) (t : ℝ) (m : ℂ) (w : Vtx d L W) : ℂ :=
  (t : ℂ) * m + X w w - ∑ l ∈ univ.erase w, ∑ k ∈ univ.erase w, (D + X) w l * greenMinor G w l k * X k w

variable {G X : Matrix (Vtx d L W) (Vtx d L W) ℂ} {κ Φ : ℝ}

/-- **(4.9) with the diagonal bound**: `|G^{(w)}_{vy}|² ≤ 2|G_{vy}|² + 8κ⁻² |G_{vw}|² |G_{wy}|²` when `|G_{ww}| ≥ κ/2`. -/
theorem GreenCore_m1 {ι : Type*} {G : Matrix ι ι ℂ} (hκ : 0 < κ) {w : ι}
    (hw : κ / 2 ≤ ‖G w w‖) (v y : ι) :
    ‖greenMinor G w v y‖ ^ 2 ≤ 2 * ‖G v y‖ ^ 2 + (8 / κ ^ 2) * (‖G v w‖ ^ 2 * ‖G w y‖ ^ 2) := by
  have h0 : 0 < ‖G w w‖ := lt_of_lt_of_le (by positivity) hw
  have h1 : ‖greenMinor G w v y‖ ≤ ‖G v y‖ + (2 / κ) * (‖G v w‖ * ‖G w y‖) := by
    rw [greenMinor]
    refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_div, norm_mul, div_le_iff₀ h0]
    have h2 : (2 / κ) * (‖G v w‖ * ‖G w y‖) * ‖G w w‖ ≥ (2 / κ) * (‖G v w‖ * ‖G w y‖) * (κ / 2) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    have h3 : (2 / κ) * (‖G v w‖ * ‖G w y‖) * (κ / 2) = ‖G v w‖ * ‖G w y‖ := by field_simp
    linarith
  have h4 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h5 : (‖G v y‖ + (2 / κ) * (‖G v w‖ * ‖G w y‖)) ^ 2 ≤
      2 * ‖G v y‖ ^ 2 + 2 * ((2 / κ) * (‖G v w‖ * ‖G w y‖)) ^ 2 := by
    nlinarith [sq_nonneg (‖G v y‖ - (2 / κ) * (‖G v w‖ * ‖G w y‖))]
  have h6 : 2 * ((2 / κ) * (‖G v w‖ * ‖G w y‖)) ^ 2 = (8 / κ ^ 2) * (‖G v w‖ ^ 2 * ‖G w y‖ ^ 2) := by
    field_simp; ring
  linarith


/-- The block average of `|G^{(w)}|²` over the rows of the block of `w`, fixed column `y`. -/
theorem GreenCore_blockMinorRow (hκ : 0 < κ) {w : Vtx d L W} (hw : κ / 2 ≤ ‖G w w‖) (y : Vtx d L W) :
    ((W : ℝ) ^ d)⁻¹ * ∑ o, ‖greenMinor G w (w.1, o) y‖ ^ 2 ≤
      2 * GreenCore_R G w.1 y + (8 / κ ^ 2) * ‖G w y‖ ^ 2 * GreenCore_R G w.1 w := by
  unfold GreenCore_R
  calc ((W : ℝ) ^ d)⁻¹ * ∑ o, ‖greenMinor G w (w.1, o) y‖ ^ 2
      ≤ ((W : ℝ) ^ d)⁻¹ * ∑ o, (2 * ‖G (w.1, o) y‖ ^ 2 + (8 / κ ^ 2) * ‖G w y‖ ^ 2 * ‖G (w.1, o) w‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun o _ => by
          have := GreenCore_m1 hκ hw (w.1, o) y
          linarith [show (8 / κ ^ 2) * (‖G (w.1, o) w‖ ^ 2 * ‖G w y‖ ^ 2) =
            (8 / κ ^ 2) * ‖G w y‖ ^ 2 * ‖G (w.1, o) w‖ ^ 2 by ring]) GreenCore_w_pos.le
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring

/-- The block average of `|G^{(w)}|²` over the columns of the block of `w`, fixed row `x`. -/
theorem GreenCore_blockMinorCol (hκ : 0 < κ) {w : Vtx d L W} (hw : κ / 2 ≤ ‖G w w‖) (x : Vtx d L W) :
    ((W : ℝ) ^ d)⁻¹ * ∑ o, ‖greenMinor G w x (w.1, o)‖ ^ 2 ≤
      2 * GreenCore_Rrow G x w.1 + (8 / κ ^ 2) * ‖G x w‖ ^ 2 * GreenCore_Rrow G w w.1 := by
  unfold GreenCore_Rrow
  calc ((W : ℝ) ^ d)⁻¹ * ∑ o, ‖greenMinor G w x (w.1, o)‖ ^ 2
      ≤ ((W : ℝ) ^ d)⁻¹ * ∑ o, (2 * ‖G x (w.1, o)‖ ^ 2 + (8 / κ ^ 2) * ‖G x w‖ ^ 2 * ‖G w (w.1, o)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun o _ => by
          have := GreenCore_m1 hκ hw x (w.1, o)
          linarith [show (8 / κ ^ 2) * (‖G x w‖ ^ 2 * ‖G w (w.1, o)‖ ^ 2) =
            (8 / κ ^ 2) * ‖G x w‖ ^ 2 * ‖G w (w.1, o)‖ ^ 2 by ring]) GreenCore_w_pos.le
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring

/-- **(L1), row form** (`ldeRow` + (4.9)): `|𝔛_{uy}|² ≤ Φ (2 R_{[u],y} + 8κ⁻² |G_{uy}|² R_{[u],u})`,
`𝔛_{uy} = Σ_{v≠u} X_{uv} G^{(u)}_{vy}`. -/
theorem GreenCore_Xrow_sq (hκ : 0 < κ) (hΦ : 0 ≤ Φ) (hGuu : ∀ u, κ / 2 ≤ ‖G u u‖)
    (hLrow : LDERow X G (svar d L W 0) Φ) (u y : Vtx d L W) :
    ‖GreenCore_Xrow G X u y‖ ^ 2 ≤
      Φ * (2 * GreenCore_R G u.1 y + (8 / κ ^ 2) * ‖G u y‖ ^ 2 * GreenCore_R G u.1 u) := by
  unfold GreenCore_Xrow
  have hu : G u u ≠ 0 := fun h => by
    have := hGuu u; rw [h, norm_zero] at this; linarith
  have hpos : 0 ≤ GreenCore_R G u.1 y := mul_nonneg GreenCore_w_pos.le (Finset.sum_nonneg fun _ _ => by positivity)
  have hpos2 : 0 ≤ GreenCore_R G u.1 u := mul_nonneg GreenCore_w_pos.le (Finset.sum_nonneg fun _ _ => by positivity)
  by_cases hyu : y = u
  · subst hyu
    have : ∑ v ∈ univ.erase y, X y v * greenMinor G y v y = 0 :=
      Finset.sum_eq_zero fun v _ => by rw [GreenCore_minor_right hu, mul_zero]
    rw [this, norm_zero, zero_pow two_ne_zero]
    exact mul_nonneg hΦ (add_nonneg (mul_nonneg two_pos.le hpos)
      (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) hpos2))
  · have h1 := hLrow u y (Ne.symm hyu)
    unfold ldeRowLHS at h1
    rw [GreenCore_ldeRowRHS hu] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (GreenCore_blockMinorRow hκ (hGuu u) y) hΦ)

/-- **(L1), column form** (`ldeCol` + (4.9)): `|𝔛'_{xw}|² ≤ Φ (2 R^{row}_{x,[w]} + 8κ⁻² |G_{xw}|² R^{row}_{w,[w]})`,
`𝔛'_{xw} = Σ_{k≠w} G^{(w)}_{xk} X_{kw}`. -/
theorem GreenCore_Xcol_sq (hκ : 0 < κ) (hΦ : 0 ≤ Φ) (hGuu : ∀ u, κ / 2 ≤ ‖G u u‖)
    (hLcol : LDECol X G (svar d L W 0) Φ) (x w : Vtx d L W) :
    ‖GreenCore_Xcol G X x w‖ ^ 2 ≤
      Φ * (2 * GreenCore_Rrow G x w.1 + (8 / κ ^ 2) * ‖G x w‖ ^ 2 * GreenCore_Rrow G w w.1) := by
  unfold GreenCore_Xcol
  have hw : G w w ≠ 0 := fun h => by
    have := hGuu w; rw [h, norm_zero] at this; linarith
  have hpos : 0 ≤ GreenCore_Rrow G x w.1 := mul_nonneg GreenCore_w_pos.le (Finset.sum_nonneg fun _ _ => by positivity)
  have hpos2 : 0 ≤ GreenCore_Rrow G w w.1 := mul_nonneg GreenCore_w_pos.le (Finset.sum_nonneg fun _ _ => by positivity)
  by_cases hxw : x = w
  · subst hxw
    have : ∑ k ∈ univ.erase x, greenMinor G x x k * X k x = 0 :=
      Finset.sum_eq_zero fun v _ => by rw [GreenCore_minor_left hw, zero_mul]
    rw [this, norm_zero, zero_pow two_ne_zero]
    exact mul_nonneg hΦ (add_nonneg (mul_nonneg two_pos.le hpos)
      (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) hpos2))
  · have h1 := hLcol x w hxw
    unfold ldeColLHS at h1
    rw [GreenCore_ldeColRHS hw] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (GreenCore_blockMinorCol hκ (hGuu w) x) hΦ)


/-- the offset average of a function bounded by `c` off one offset `o₀` and by `c + e` at `o₀` -/
theorem GreenCore_avg_pt {f : Fin (W ^ d) → ℝ} {o₀ : Fin (W ^ d)} {c e : ℝ}
    (h : ∀ o, f o ≤ c + e * (if o = o₀ then 1 else 0)) :
    ((W : ℝ) ^ d)⁻¹ * ∑ o, f o ≤ c + e * ((W : ℝ) ^ d)⁻¹ := by
  have h1 : ∑ o, f o ≤ ∑ o, (c + e * (if o = o₀ then 1 else 0)) := Finset.sum_le_sum fun o _ => h o
  have h2 : ∑ o : Fin (W ^ d), (c + e * (if o = o₀ then 1 else 0)) = ((W : ℝ) ^ d) * c + e := by
    simp [Finset.sum_add_distrib, Finset.sum_ite_eq']
  rw [h2] at h1
  calc ((W : ℝ) ^ d)⁻¹ * ∑ o, f o ≤ ((W : ℝ) ^ d)⁻¹ * (((W : ℝ) ^ d) * c + e) :=
        mul_le_mul_of_nonneg_left h1 GreenCore_w_pos.le
    _ = c + e * ((W : ℝ) ^ d)⁻¹ := by
        rw [mul_add, ← mul_assoc, GreenCore_w_mul, one_mul, mul_comm]

variable {M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Matrix (Zd d L) (Zd d L) ℂ} {m : ℂ} {δ : ℝ}

/-- The elementary bounds on `G` from `Ω = {‖G - M‖_max ≤ δ}`, `M = M^{(B)} ⊗ I`, `δ ≤ κ/2`: `|G_{uu}| ≥ κ/2`,
`|G_{uv}| ≤ 3/2`, and `|G_{uv}| ≤ δ` between different offsets (where `M_{uv} = 0`). -/
theorem GreenCore_crude (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hMd : ∀ a, Mb a a = m)
    (hMb1 : ∀ a b, ‖Mb a b‖ ≤ 1) (hκm : κ ≤ ‖m‖) (hm1 : ‖m‖ ≤ 1) (hδ : δ ≤ κ / 2)
    (hΩ : ∀ u v, ‖G u v - M u v‖ ≤ δ) :
    (∀ u, κ / 2 ≤ ‖G u u‖) ∧ (∀ u v, ‖G u v‖ ≤ 3 / 2) ∧ (∀ u v, u.2 ≠ v.2 → ‖G u v‖ ≤ δ) := by
  refine ⟨fun u => ?_, fun u v => ?_, fun u v huv => ?_⟩
  · have h1 : M u u = m := by simp [hM, hMd]
    have h2 := norm_sub_norm_le (M u u) (G u u)
    have h3 := hΩ u u
    rw [h1] at h2 h3
    rw [norm_sub_rev] at h2
    linarith
  · have h1 : ‖M u v‖ ≤ 1 := by
      rw [hM]; split_ifs
      · exact hMb1 _ _
      · simp
    have h2 := norm_sub_norm_le (G u v) (M u v)
    linarith [hΩ u v]
  · have h1 : M u v = 0 := by simp [hM, huv]
    have := hΩ u v
    rwa [h1, sub_zero] at this

/-- **A priori block averages**: `R_{a,y} ≤ (13/4) δ²` and `R^{row}_{x,b} ≤ (13/4) δ²` (the entries are `≤ δ`
except at the one offset where `M` lives, there `≤ 3/2`; `W^{-d} ≤ δ²`). -/
theorem GreenCore_apriori (hG32 : ∀ u v, ‖G u v‖ ≤ 3 / 2) (hGoff : ∀ u v, u.2 ≠ v.2 → ‖G u v‖ ≤ δ)
    (hδ0 : 0 ≤ δ) (hwd : ((W : ℝ) ^ d)⁻¹ ≤ δ ^ 2) :
    (∀ a y, GreenCore_R G a y ≤ 13 / 4 * δ ^ 2) ∧ (∀ x b, GreenCore_Rrow G x b ≤ 13 / 4 * δ ^ 2) := by
  constructor
  · intro a y
    have := GreenCore_avg_pt (d := d) (W := W) (f := fun o => ‖G (a, o) y‖ ^ 2) (o₀ := y.2) (c := δ ^ 2) (e := 9 / 4)
      (fun o => by
        by_cases h : o = y.2
        · simp only [h, ite_true]
          have := hG32 (a, y.2) y
          nlinarith [norm_nonneg (G (a, y.2) y)]
        · simp only [h, ite_false]
          have := hGoff (a, o) y h
          nlinarith [norm_nonneg (G (a, o) y)])
    unfold GreenCore_R
    nlinarith
  · intro x b
    have := GreenCore_avg_pt (d := d) (W := W) (f := fun o => ‖G x (b, o)‖ ^ 2) (o₀ := x.2) (c := δ ^ 2) (e := 9 / 4)
      (fun o => by
        by_cases h : o = x.2
        · simp only [h, ite_true]
          have := hG32 x (b, x.2)
          nlinarith [norm_nonneg (G x (b, x.2))]
        · simp only [h, ite_false]
          have := hGoff x (b, o) (Ne.symm h)
          nlinarith [norm_nonneg (G x (b, o))])
    unfold GreenCore_Rrow
    nlinarith

end Entry

section Reentry
variable {d L W : ℕ} [NeZero L] [NeZero W] {G X M D : Matrix (Vtx d L W) (Vtx d L W) ℂ}
  {Mb : Matrix (Zd d L) (Zd d L) ℂ} {m : ℂ} {κ Φ δ : ℝ}

/-- `Q^{XX}_w = Σ_{k,l≠w} X_{wk} G^{(w)}_{kl} X_{lw}`. -/
def GreenCore_Qxx (G X : Matrix (Vtx d L W) (Vtx d L W) ℂ) (w : Vtx d L W) : ℂ :=
  ∑ k ∈ univ.erase w, ∑ l ∈ univ.erase w, X w k * greenMinor G w k l * X l w

/-- `ε_1 = Q^{XX}_w - t Σ_{k≠w} S_{wk} G^{(w)}_{kk}`, the quadratic large deviation error. -/
def GreenCore_eps1 (G X : Matrix (Vtx d L W) (Vtx d L W) ℂ) (t : ℝ) (w : Vtx d L W) : ℂ :=
  GreenCore_Qxx G X w - (t : ℂ) * ∑ k ∈ univ.erase w, ((svar d L W 0 w k : ℝ) : ℂ) * greenMinor G w k k

/-- `ε_2 = t W^{-d} Σ_{k∈[w]} G_{kw} G_{wk} / G_{ww}`. -/
def GreenCore_eps2 (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (t : ℝ) (w : Vtx d L W) : ℂ :=
  (t : ℂ) * (((W : ℝ) ^ d)⁻¹ : ℝ) * ∑ o, G (w.1, o) w * G w (w.1, o) / G w w

/-- `Q^{XD}_u = Σ_{k,l≠u} X_{uk} G^{(u)}_{kl} D_{lu}`. -/
def GreenCore_Qxd (G X D : Matrix (Vtx d L W) (Vtx d L W) ℂ) (u : Vtx d L W) : ℂ :=
  ∑ k ∈ univ.erase u, ∑ l ∈ univ.erase u, X u k * greenMinor G u k l * D l u

/-- `|ε_1|² ≤ Φ (2 𝓛_{[w],[w]} + 8κ⁻² R_{[w],w} R^{row}_{w,[w]})` (`hLquad` + (4.9)). -/
theorem GreenCore_eps1_loc {t : ℝ} (hκ : 0 < κ) (hΦ : 0 ≤ Φ) (hGuu : ∀ u, κ / 2 ≤ ‖G u u‖)
    (hLquad : LDEQuad X G (svar d L W 0) t Φ) (w : Vtx d L W) :
    ‖GreenCore_eps1 G X t w‖ ^ 2 ≤
      Φ * (2 * GreenCore_loop G w.1 w.1 + (8 / κ ^ 2) * GreenCore_R G w.1 w * GreenCore_Rrow G w w.1) := by
  have hw0 : G w w ≠ 0 := fun h => by
    have := hGuu w; rw [h, norm_zero] at this; linarith
  have h1 := hLquad w
  unfold ldeQuadLHS at h1
  rw [GreenCore_ldeQuadRHS hw0] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ hΦ)
  calc (((W : ℝ) ^ d)⁻¹) ^ 2 * ∑ o, ∑ o', ‖greenMinor G w (w.1, o) (w.1, o')‖ ^ 2
      ≤ (((W : ℝ) ^ d)⁻¹) ^ 2 * ∑ o, ∑ o', (2 * ‖G (w.1, o) (w.1, o')‖ ^ 2 +
          (8 / κ ^ 2) * (‖G (w.1, o) w‖ ^ 2 * ‖G w (w.1, o')‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun o _ => Finset.sum_le_sum fun o' _ =>
          GreenCore_m1 hκ (hGuu w) _ _) (sq_nonneg _)
    _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        unfold GreenCore_loop GreenCore_R GreenCore_Rrow
        ring

/-- `|ε_2|² ≤ 4κ⁻² R_{[w],w} R^{row}_{w,[w]}` (Cauchy–Schwarz). -/
theorem GreenCore_eps2_loc {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hκ : 0 < κ) (hGuu : ∀ u, κ / 2 ≤ ‖G u u‖)
    (w : Vtx d L W) :
    ‖GreenCore_eps2 G t w‖ ^ 2 ≤ (4 / κ ^ 2) * GreenCore_R G w.1 w * GreenCore_Rrow G w w.1 := by
  have hw : 0 < ‖G w w‖ := lt_of_lt_of_le (by positivity) (hGuu w)
  have hwp := GreenCore_w_pos (d := d) (W := W)
  set S := ∑ o, ‖G (w.1, o) w‖ * ‖G w (w.1, o)‖ with hS
  have h1 : ‖GreenCore_eps2 G t w‖ ≤ (2 / κ) * (((W : ℝ) ^ d)⁻¹ * S) := by
    unfold GreenCore_eps2
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg ht0,
      Real.norm_of_nonneg hwp.le, mul_assoc]
    have h2 : ‖∑ o, G (w.1, o) w * G w (w.1, o) / G w w‖ ≤ S / ‖G w w‖ := by
      refine (norm_sum_le _ _).trans ?_
      rw [hS, Finset.sum_div]
      exact Finset.sum_le_sum fun o _ => by rw [norm_div, norm_mul]
    have h3 : S / ‖G w w‖ ≤ (2 / κ) * S := by
      have hS0 : 0 ≤ S := Finset.sum_nonneg fun o _ => by positivity
      rw [div_le_iff₀ hw]
      have := mul_le_mul_of_nonneg_left (hGuu w) (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 / κ) hS0)
      have e : 2 / κ * S * (κ / 2) = S := by field_simp
      nlinarith
    calc t * ((((W : ℝ) ^ d)⁻¹) * ‖∑ o, G (w.1, o) w * G w (w.1, o) / G w w‖) ≤
        1 * (((W : ℝ) ^ d)⁻¹ * ((2 / κ) * S)) :=
          mul_le_mul ht1 (mul_le_mul_of_nonneg_left (h2.trans h3) hwp.le)
            (mul_nonneg hwp.le (norm_nonneg _)) zero_le_one
      _ = (2 / κ) * (((W : ℝ) ^ d)⁻¹ * S) := by ring
  have h4 : S ^ 2 ≤ (∑ o, ‖G (w.1, o) w‖ ^ 2) * ∑ o, ‖G w (w.1, o)‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ‖GreenCore_eps2 G t w‖ ^ 2 ≤ ((2 / κ) * (((W : ℝ) ^ d)⁻¹ * S)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = (4 / κ ^ 2) * ((((W : ℝ) ^ d)⁻¹) ^ 2 * S ^ 2) := by field_simp; ring
    _ ≤ (4 / κ ^ 2) * ((((W : ℝ) ^ d)⁻¹) ^ 2 * ((∑ o, ‖G (w.1, o) w‖ ^ 2) * ∑ o, ‖G w (w.1, o)‖ ^ 2)) := by
        gcongr
    _ = _ := by unfold GreenCore_R GreenCore_Rrow; ring


/-- `Σ_{k≠w} S_{wk} G^{(w)}_{kk} = m + v̄_{[w]} - ε_2/t` (block average of the minor diagonal; `M_{kk} = m`). -/
theorem GreenCore_Bsum (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hMd : ∀ a, Mb a a = m)
    {w : Vtx d L W} (hw : G w w ≠ 0) :
    ∑ k ∈ univ.erase w, ((svar d L W 0 w k : ℝ) : ℂ) * greenMinor G w k k =
      m + GreenCore_vbar G M w.1 - (((W : ℝ) ^ d)⁻¹ : ℝ) * ∑ o, G (w.1, o) w * G w (w.1, o) / G w w := by
  rw [Finset.sum_erase _ (by simp [GreenCore_minor_left hw]),
    GreenCore_sum_block_c w (fun k => greenMinor G w k k)]
  have h1 : ∀ o : Fin (W ^ d), M (w.1, o) (w.1, o) = m := fun o => by simp [hM, hMd]
  have h2 : (((W : ℝ) ^ d)⁻¹ : ℝ) * ∑ o : Fin (W ^ d), m = m := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : ((W : ℝ) ^ d)⁻¹ * ((W ^ d : ℕ) : ℝ) = 1 := by rw [Nat.cast_pow]; exact GreenCore_w_mul
    have h3 : (((W : ℝ) ^ d)⁻¹ : ℝ) * ((W ^ d : ℕ) : ℂ) = 1 := by exact_mod_cast this
    rw [← mul_assoc, h3, one_mul]
  unfold GreenCore_vbar
  have h4 : ∑ o, greenMinor G w (w.1, o) (w.1, o) =
      ∑ o, (G (w.1, o) (w.1, o) - M (w.1, o) (w.1, o)) + ∑ o : Fin (W ^ d), m -
        ∑ o, G (w.1, o) w * G w (w.1, o) / G w w := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [greenMinor, h1 o]; ring
  rw [h4, mul_sub, mul_add, h2]
  ring

/-- **(E2)**: `t m - Q^{XX}_w = -t v̄_{[w]} + ε_2 - ε_1`. -/
theorem GreenCore_E2 {t : ℝ} (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hMd : ∀ a, Mb a a = m)
    {w : Vtx d L W} (hw : G w w ≠ 0) :
    (t : ℂ) * m - GreenCore_Qxx G X w =
      -((t : ℂ) * GreenCore_vbar G M w.1) + GreenCore_eps2 G t w - GreenCore_eps1 G X t w := by
  unfold GreenCore_eps1 GreenCore_eps2
  rw [GreenCore_Bsum hM hMd hw]
  ring

/-- **(E2), row form**: `A_u = -t v̄_{[u]} + ε_2 - ε_1 + X_{uu} - Q^{XD}_u`. -/
theorem GreenCore_Arow_eq {t : ℝ} (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0)
    (hMd : ∀ a, Mb a a = m) {w : Vtx d L W} (hw : G w w ≠ 0) :
    GreenCore_Arow G X D t m w = -((t : ℂ) * GreenCore_vbar G M w.1) + GreenCore_eps2 G t w -
      GreenCore_eps1 G X t w + X w w - GreenCore_Qxd G X D w := by
  have h : ∑ k ∈ univ.erase w, ∑ l ∈ univ.erase w, X w k * greenMinor G w k l * (D + X) l w =
      GreenCore_Qxx G X w + GreenCore_Qxd G X D w := by
    unfold GreenCore_Qxx GreenCore_Qxd
    rw [add_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.add_apply]; ring
  unfold GreenCore_Arow
  rw [h, ← GreenCore_E2 (X := X) hM hMd hw]
  ring

/-- `Σ_{l ≠ w} |D_{wl}|`-type row sum of the adjacency part: `‖D‖` has `2d` entries `g₀` per row. -/
theorem GreenCore_adj_symm (a b : Zd d L) : Adj d L a b ↔ Adj d L b a := by
  simp only [Adj]
  rw [show b - a = -(a - b) by ring, zdistD_neg]

theorem GreenCore_Drow {D : Matrix (Vtx d L W) (Vtx d L W) ℂ} {g₀ : ℝ} (hg : 0 ≤ g₀) (hL : 3 ≤ L)
    (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0) (w : Vtx d L W) :
    ∑ l, ‖D w l‖ = 2 * d * g₀ := by
  simp only [hD, apply_ite (norm : ℂ → ℝ), Complex.norm_real, Real.norm_of_nonneg hg, norm_zero]
  rw [Fintype.sum_prod_type]
  have : ∀ a : Zd d L, ∑ o : Fin (W ^ d), (if w.2 = o ∧ Adj d L w.1 a then g₀ else 0) =
      if Adj d L w.1 a then g₀ else 0 := by
    intro a
    simp only [ite_and]
    rw [Finset.sum_ite_eq]
    simp
  simp only [this]
  rw [← Finset.sum_filter, Finset.sum_const, card_adj d L hL w.1, nsmul_eq_mul]
  push_cast; ring

theorem GreenCore_Dsymm {D : Matrix (Vtx d L W) (Vtx d L W) ℂ} {g₀ : ℝ}
    (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0) (u l : Vtx d L W) :
    D u l = D l u := by
  have h1 : (u.2 = l.2 ∧ Adj d L u.1 l.1) ↔ (l.2 = u.2 ∧ Adj d L l.1 u.1) :=
    and_congr eq_comm (GreenCore_adj_symm u.1 l.1)
  rw [hD, hD]
  split_ifs with h2 h3 h3 <;> first | rfl | exact absurd (h1.1 h2) h3 | exact absurd (h1.2 h3) h2



/-- `|Q^{XD}_u|² ≤ (2 d g₀)² Q` if `|𝔛_{ul}|² ≤ Q` for all `l`. -/
theorem GreenCore_Qxd_sq {g₀ Q : ℝ} (hg : 0 ≤ g₀) (hL : 3 ≤ L)
    (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0) {u : Vtx d L W}
    (hXr : ∀ l, ‖GreenCore_Xrow G X u l‖ ^ 2 ≤ Q) :
    ‖GreenCore_Qxd G X D u‖ ^ 2 ≤ (2 * d * g₀) ^ 2 * Q := by
  have hrow : ∑ l, ‖D l u‖ = 2 * d * g₀ := by
    simp only [← GreenCore_Dsymm hD u]; exact GreenCore_Drow (W := W) hg hL hD u
  have h1 : GreenCore_Qxd G X D u = ∑ l ∈ univ.erase u, D l u * GreenCore_Xrow G X u l := by
    unfold GreenCore_Qxd GreenCore_Xrow
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [h1]
  have h2 : ‖∑ l ∈ univ.erase u, D l u * GreenCore_Xrow G X u l‖ ≤ ∑ l, ‖D l u‖ * ‖GreenCore_Xrow G X u l‖ :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun l _ => (norm_mul _ _).le).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun l _ _ => by positivity))
  have h3 : (∑ l, ‖D l u‖ * ‖GreenCore_Xrow G X u l‖) ^ 2 ≤
      (∑ l, ‖D l u‖) * ∑ l, ‖D l u‖ * ‖GreenCore_Xrow G X u l‖ ^ 2 :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun l _ => norm_nonneg _) (fun l _ => by positivity)
      fun l _ => le_of_eq (by ring)
  have h4 : ∑ l, ‖D l u‖ * ‖GreenCore_Xrow G X u l‖ ^ 2 ≤ (∑ l, ‖D l u‖) * Q := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hXr l) (norm_nonneg _)
  calc _ ≤ (∑ l, ‖D l u‖ * ‖GreenCore_Xrow G X u l‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ ≤ (∑ l, ‖D l u‖) * ((∑ l, ‖D l u‖) * Q) :=
        h3.trans (mul_le_mul_of_nonneg_left h4 (Finset.sum_nonneg fun l _ => norm_nonneg _))
    _ = (2 * d * g₀) ^ 2 * Q := by rw [hrow]; ring

theorem GreenCore_sq5 (a b c e f : ℝ) : (a + b + c + e + f) ^ 2 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2 + f ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - e), sq_nonneg (a - f), sq_nonneg (b - c),
    sq_nonneg (b - e), sq_nonneg (b - f), sq_nonneg (c - e), sq_nonneg (c - f), sq_nonneg (e - f)]

/-- The four-term bound for the row form (the `t v̄` cancels): `|A_u + t v̄|² ≤ 5 (…)`. -/
theorem GreenCore_Arow_four {t : ℝ} (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0)
    (hMd : ∀ a, Mb a a = m) {w : Vtx d L W} (hw : G w w ≠ 0) :
    ‖GreenCore_Arow G X D t m w + (t : ℂ) * GreenCore_vbar G M w.1‖ ^ 2 ≤ 5 * (‖GreenCore_eps2 G t w‖ ^ 2 +
      ‖GreenCore_eps1 G X t w‖ ^ 2 + ‖X w w‖ ^ 2 + ‖GreenCore_Qxd G X D w‖ ^ 2) := by
  have h : GreenCore_Arow G X D t m w + (t : ℂ) * GreenCore_vbar G M w.1 =
      GreenCore_eps2 G t w - GreenCore_eps1 G X t w + X w w - GreenCore_Qxd G X D w := by
    rw [GreenCore_Arow_eq hM hMd hw]; ring
  rw [h]
  have := GreenCore_sq5 0 ‖GreenCore_eps2 G t w‖ ‖GreenCore_eps1 G X t w‖ ‖X w w‖ ‖GreenCore_Qxd G X D w‖
  refine le_trans (pow_le_pow_left₀ (norm_nonneg _) ?_ 2) (by simpa using this)
  exact (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _)) le_rfl)) le_rfl)


/-- The Kronecker reduction of a sum against `M = M^{(B)} ⊗ I`: only the sites of the offset of `y` contribute. -/
theorem GreenCore_sum_kron (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (F : Vtx d L W → ℂ)
    (y : Vtx d L W) : ∑ u, F u * M u y = ∑ b', F (b', y.2) * Mb b' y.1 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b' _ => ?_
  simp [hM]

theorem GreenCore_sum_kron' (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (F : Vtx d L W → ℂ)
    (x : Vtx d L W) : ∑ u, M x u * F u = ∑ b', Mb x.1 b' * F (b', x.2) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b' _ => ?_
  simp [hM]

/-- **(E0)**, column form: `G - M = -(G (X + t m) M)`. -/
theorem GreenCore_E0 {t : ℝ} {s z : ℂ} (hGR : G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1)
    (hMR : (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * M = 1) (hz : z = s - (t : ℂ) * m) :
    G - M = -(G * (X + ((t : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * M) := by
  have key : (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) - (D + X - z • 1) =
      -(X + ((t : ℂ) * m) • 1) := by rw [hz]; module
  calc G - M = G * (D - s • 1) * M - G * (D + X - z • 1) * M := by
        rw [mul_assoc G (D - s • 1) M, hMR, mul_one, hGR, one_mul]
    _ = _ := by rw [← sub_mul, ← mul_sub, key, mul_neg, neg_mul]

/-- `(G (X + t m))_{xu} = A'_u G_{xu} + 𝔛'_{xu}` (E1′ with the `t m` term). -/
theorem GreenCore_GYcol {t : ℝ} {z : ℂ} (hRG : (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1)
    (hG0 : ∀ u, G u u ≠ 0) (x u : Vtx d L W) :
    (G * (X + ((t : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))) x u =
      GreenCore_Acol G X D t m u * G x u + GreenCore_Xcol G X x u := by
  have h1 := GreenCore_E1' (X := X) hRG x u (hG0 u)
  have h2 : (G * (X + ((t : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))) x u =
      ∑ k, G x k * X k u + (t : ℂ) * m * G x u := by
    rw [Matrix.mul_apply]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, mul_add, Finset.sum_add_distrib, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, smul_eq_mul]
    ring
  rw [h2, h1]; unfold GreenCore_Acol GreenCore_Xcol; ring


/-- **(E0) + (E1′)** in entries: `Δ_{xy} = -Σ_{b'} M^{(B)}_{b'[y]} (A'_{(b',o_y)} G_{x(b',o_y)} + 𝔛'_{x(b',o_y)})`,
for `(H - z) G = 1`, `G (H - z) = 1`, `(D - s) M = 1`, `z = s - t m`, `H = D + X`, `M = M^{(B)} ⊗ I`. -/
theorem GreenCore_Delta_col {t : ℝ} {s z : ℂ} (hGR : G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1)
    (hRG : (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1)
    (hMR : (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * M = 1) (hz : z = s - (t : ℂ) * m)
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hG0 : ∀ u, G u u ≠ 0) (x y : Vtx d L W) :
    G x y - M x y = -∑ b', Mb b' y.1 * (GreenCore_Acol G X D t m (b', y.2) * G x (b', y.2) +
      GreenCore_Xcol G X x (b', y.2)) := by
  have h3 := congrFun (congrFun (GreenCore_E0 (X := X) hGR hMR hz) x) y
  rw [Matrix.sub_apply, Matrix.neg_apply, Matrix.mul_apply] at h3
  rw [h3]
  congr 1
  rw [GreenCore_sum_kron hM (fun u => (G * (X + ((t : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))) x u) y]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [GreenCore_GYcol hRG hG0 x (b', y.2)]; ring

/-- **(A\*)**, the a priori bound on the random re-entry (`(a′)` D3.1, shorter route): `A'_w G_{ww} = (G (X + t m))_{ww}` and
`G (X + t m) = -Δ (D - s)`, so `|A'_w| ≤ (2/κ)(2 d g₀ + (1 + 2 d g₀)/κ) δ`; `|s| |m| ≤ 2 d g₀ + 1` from `(D - s) M = 1`. -/
theorem GreenCore_Acol_sq {t g₀ : ℝ} {s z : ℂ} (hL : 3 ≤ L) (hg : 0 ≤ g₀) (hκ : 0 < κ)
    (hGR : G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1)
    (hRG : (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1)
    (hMR : (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * M = 1)
    (hMR' : M * (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1) (hz : z = s - (t : ℂ) * m)
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hMd : ∀ a, Mb a a = m)
    (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0)
    (hκm : κ ≤ ‖m‖) (hMb1 : ∀ a b, ‖Mb a b‖ ≤ 1) (hGuu : ∀ u, κ / 2 ≤ ‖G u u‖)
    (hΩ : ∀ u v, ‖G u v - M u v‖ ≤ δ) (w : Vtx d L W) :
    ‖GreenCore_Acol G X D t m w‖ ^ 2 ≤ (4 / κ ^ 2) * (2 * d * g₀ + (1 + 2 * d * g₀) / κ) ^ 2 * δ ^ 2 := by
  have hG0 : ∀ u, G u u ≠ 0 := fun u h => by
    have := hGuu u; rw [h, norm_zero] at this; linarith
  have hD1 : ∑ l, ‖D l w‖ = 2 * d * g₀ := by
    simp only [← GreenCore_Dsymm hD w]; exact GreenCore_Drow (W := W) hg hL hD w
  have hD2 : ∑ l, ‖D w l‖ = 2 * d * g₀ := GreenCore_Drow (W := W) hg hL hD w
  have hM1 : ∀ u v, ‖M u v‖ ≤ 1 := fun u v => by
    rw [hM]; split_ifs
    · exact hMb1 _ _
    · simp
  -- the bound on `|s|`
  have hs : ‖s‖ * κ ≤ 2 * d * g₀ + 1 := by
    have h1 := congrFun (congrFun hMR w) w
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    have h2 : ∑ l, (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) w l * M l w =
        ∑ l, D w l * M l w - s * m := by
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
        ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [show M w w = m by rw [hM]; simp [hMd]]
    have h3 : s * m = ∑ l, D w l * M l w - 1 := by rw [h2] at h1; linear_combination -h1
    have h4 : ‖s‖ * ‖m‖ ≤ 2 * d * g₀ + 1 := by
      rw [← norm_mul, h3]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one]
      refine add_le_add ((norm_sum_le _ _).trans ?_) le_rfl
      calc ∑ l, ‖D w l * M l w‖ ≤ ∑ l, ‖D w l‖ * 1 :=
            Finset.sum_le_sum fun l _ => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hM1 _ _) (norm_nonneg _)
        _ = 2 * d * g₀ := by simp [hD2]
    nlinarith [norm_nonneg s]
  -- `G (X + t m) = -Δ (D - s)` and its `(w, w)` entry
  have hGY : G * (X + ((t : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) =
      -((G - M) * (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))) := by
    calc _ = G * (X + ((t : ℂ) * m) • 1) * (M * (D - s • 1)) := by rw [hMR', mul_one]
      _ = G * (X + ((t : ℂ) * m) • 1) * M * (D - s • 1) := (mul_assoc _ _ _).symm
      _ = _ := by
          rw [show G * (X + ((t : ℂ) * m) • 1) * M = -(G - M) by rw [GreenCore_E0 (X := X) hGR hMR hz, neg_neg], neg_mul]
  -- the `(w, w)` entry
  have hxx : GreenCore_Xcol G X w w = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [GreenCore_minor_left (hG0 w), zero_mul]
  have hA : ‖GreenCore_Acol G X D t m w‖ * (κ / 2) ≤ δ * (2 * d * g₀ + ‖s‖) := by
    have h1 := GreenCore_GYcol (X := X) (D := D) (m := m) (t := t) hRG hG0 w w
    rw [hxx, add_zero, hGY] at h1
    have h2 : ‖GreenCore_Acol G X D t m w * G w w‖ ≤ δ * (2 * d * g₀ + ‖s‖) := by
      rw [← h1, Matrix.neg_apply, norm_neg, Matrix.mul_apply]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ l, ‖(G - M) w l * (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) l w‖
          ≤ ∑ l, δ * (‖D l w‖ + ‖s‖ * (if l = w then 1 else 0)) := by
            refine Finset.sum_le_sum fun l _ => ?_
            rw [norm_mul]
            refine mul_le_mul (by simpa using hΩ w l) ?_ (norm_nonneg _) (le_trans (norm_nonneg _) (hΩ w l))
            simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
            split_ifs with h
            · subst h; simpa using norm_sub_le (D l l) (s * 1)
            · simp
        _ = δ * (2 * d * g₀ + ‖s‖) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib, hD1]; simp [Finset.sum_ite_eq']
    rw [norm_mul] at h2
    nlinarith [mul_le_mul_of_nonneg_left (hGuu w) (norm_nonneg (GreenCore_Acol G X D t m w))]
  -- `‖s‖ ≤ (2 d g₀ + 1)/κ`
  have hs' : ‖s‖ ≤ (1 + 2 * d * g₀) / κ := by rw [le_div_iff₀ hκ]; linarith [hs]
  have hn : ‖GreenCore_Acol G X D t m w‖ ≤ (2 / κ) * (δ * (2 * d * g₀ + (1 + 2 * d * g₀) / κ)) := by
    have h5 : δ * (2 * d * g₀ + ‖s‖) ≤ δ * (2 * d * g₀ + (1 + 2 * d * g₀) / κ) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_trans (norm_nonneg _) (hΩ w w))
    have : ‖GreenCore_Acol G X D t m w‖ * (κ / 2) ≤ δ * (2 * d * g₀ + (1 + 2 * d * g₀) / κ) := hA.trans h5
    rw [show (2 / κ) * (δ * (2 * d * g₀ + (1 + 2 * d * g₀) / κ)) = (δ * (2 * d * g₀ + (1 + 2 * d * g₀) / κ)) / (κ / 2) by
      field_simp]
    rw [le_div_iff₀ (by positivity)]; exact this
  calc ‖GreenCore_Acol G X D t m w‖ ^ 2 ≤ ((2 / κ) * (δ * (2 * d * g₀ + (1 + 2 * d * g₀) / κ))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = _ := by ring


/-- The block average of the column `𝔛'` bound: `W^{-d} Σ_{x∈a} |𝔛'_{xw}|² ≤ Φ (2 𝓛_{a,[w]} + 26 κ⁻² δ² R_{a,w})`. -/
theorem GreenCore_Xcol_avg {κ Φ δ : ℝ} (hΦ : 0 ≤ Φ) (hκ : 0 < κ)
    (hX : ∀ x w, ‖GreenCore_Xcol G X x w‖ ^ 2 ≤
      Φ * (2 * GreenCore_Rrow G x w.1 + (8 / κ ^ 2) * ‖G x w‖ ^ 2 * GreenCore_Rrow G w w.1))
    (hRrow : ∀ x b, GreenCore_Rrow G x b ≤ 13 / 4 * δ ^ 2) (a : Zd d L) (w : Vtx d L W) :
    ((W : ℝ) ^ d)⁻¹ * ∑ o, ‖GreenCore_Xcol G X (a, o) w‖ ^ 2 ≤
      Φ * (2 * GreenCore_loop G a w.1 + (26 / κ ^ 2) * δ ^ 2 * GreenCore_R G a w) := by
  have hw := GreenCore_w_pos (d := d) (W := W)
  have h1 : ∀ o, ‖GreenCore_Xcol G X (a, o) w‖ ^ 2 ≤
      Φ * (2 * GreenCore_Rrow G (a, o) w.1 + (26 / κ ^ 2) * δ ^ 2 * ‖G (a, o) w‖ ^ 2) := by
    intro o
    refine (hX _ _).trans (mul_le_mul_of_nonneg_left ?_ hΦ)
    have := mul_le_mul_of_nonneg_left (hRrow w w.1) (by positivity : (0 : ℝ) ≤ 8 / κ ^ 2 * ‖G (a, o) w‖ ^ 2)
    have e : 8 / κ ^ 2 * ‖G (a, o) w‖ ^ 2 * (13 / 4 * δ ^ 2) = 26 / κ ^ 2 * δ ^ 2 * ‖G (a, o) w‖ ^ 2 := by ring
    linarith
  have e1 : ((W : ℝ) ^ d)⁻¹ * ∑ o, GreenCore_Rrow G (a, o) w.1 = GreenCore_loop G a w.1 := by
    unfold GreenCore_loop GreenCore_Rrow
    simp only [Finset.mul_sum, sq, mul_assoc]
  have e2 : ∑ o, Φ * (2 * GreenCore_Rrow G (a, o) w.1 + (26 / κ ^ 2) * δ ^ 2 * ‖G (a, o) w‖ ^ 2) =
      Φ * (2 * ∑ o, GreenCore_Rrow G (a, o) w.1 + (26 / κ ^ 2) * δ ^ 2 * ∑ o, ‖G (a, o) w‖ ^ 2) := by
    simp only [← Finset.mul_sum, Finset.sum_add_distrib]
  calc ((W : ℝ) ^ d)⁻¹ * ∑ o, ‖GreenCore_Xcol G X (a, o) w‖ ^ 2
      ≤ ((W : ℝ) ^ d)⁻¹ * ∑ o, Φ * (2 * GreenCore_Rrow G (a, o) w.1 + (26 / κ ^ 2) * δ ^ 2 * ‖G (a, o) w‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun o _ => h1 o) hw.le
    _ = Φ * (2 * (((W : ℝ) ^ d)⁻¹ * ∑ o, GreenCore_Rrow G (a, o) w.1) +
          (26 / κ ^ 2) * δ ^ 2 * (((W : ℝ) ^ d)⁻¹ * ∑ o, ‖G (a, o) w‖ ^ 2)) := by rw [e2]; ring
    _ = _ := by rw [e1]; rfl


/-- `W^{-d} Σ_{x∈a} |M_{xy}|² = W^{-d} |M^{(B)}_{a[y]}|²`: exactly one site of `a` has the offset of `y`. -/
theorem GreenCore_sumM2 (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (a c : Zd d L) (o : Fin (W ^ d)) :
    ((W : ℝ) ^ d)⁻¹ * ∑ o', ‖M (a, o') (c, o)‖ ^ 2 = ((W : ℝ) ^ d)⁻¹ * ‖Mb a c‖ ^ 2 := by
  congr 1
  simp only [hM]
  rw [Finset.sum_eq_single o]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem GreenCore_dsum {ι κ' : Type*} [Fintype ι] [Fintype κ'] (f : ι → ℝ) (T : ι → κ' → ℝ) (w ρ : ℝ) :
    w * ∑ i, (2 * f i + 2 * (ρ * ∑ j, T i j)) = 2 * (w * ∑ i, f i) + 2 * ρ * ∑ j, (w * ∑ i, T i j) := by
  simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-- **(R1)**, the two-sided inequality (`(a′)` D3.2): for `Δ_{xy} = -Σ_{b'} M_{b'c} (A'_{w} G_{xw} + 𝔛'_{xw})`,
`R_{a,(c,o)} ≤ 2 W^{-d}|M_{ac}|² + 8ρΦ Σ_{b'} |M_{b'c}| 𝓛_{a,b'} + 4ρϑ Σ_{b'} |M_{b'c}| R_{a,(b',o)}`,
`ϑ = α² + 26 κ⁻² Φ δ²`. -/
theorem GreenCore_twoSided {t ρ α2 : ℝ} (hρ0 : 0 ≤ ρ) (hκ : 0 < κ) (hΦ0 : 0 ≤ Φ) (hα : 0 ≤ α2)
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hρ : ∀ c, ∑ b, ‖Mb b c‖ ≤ ρ)
    (hΔ : ∀ x y : Vtx d L W, G x y - M x y = -∑ b', Mb b' y.1 *
      (GreenCore_Acol G X D t m (b', y.2) * G x (b', y.2) + GreenCore_Xcol G X x (b', y.2)))
    (hA : ∀ w, ‖GreenCore_Acol G X D t m w‖ ^ 2 ≤ α2)
    (hX : ∀ x w, ‖GreenCore_Xcol G X x w‖ ^ 2 ≤
      Φ * (2 * GreenCore_Rrow G x w.1 + (8 / κ ^ 2) * ‖G x w‖ ^ 2 * GreenCore_Rrow G w w.1))
    (hRrow : ∀ x b, GreenCore_Rrow G x b ≤ 13 / 4 * δ ^ 2) (a c : Zd d L) (o : Fin (W ^ d)) :
    GreenCore_R G a (c, o) ≤ 2 * ((W : ℝ) ^ d)⁻¹ * ‖Mb a c‖ ^ 2 +
      8 * ρ * Φ * ∑ b', ‖Mb b' c‖ * GreenCore_loop G a b' +
      4 * ρ * (α2 + 26 / κ ^ 2 * Φ * δ ^ 2) * ∑ b', ‖Mb b' c‖ * GreenCore_R G a (b', o) := by
  have hw := GreenCore_w_pos (d := d) (W := W)
  have pt : ∀ x : Vtx d L W, ‖G x (c, o)‖ ^ 2 ≤ 2 * ‖M x (c, o)‖ ^ 2 + 2 * (ρ * ∑ b', ‖Mb b' c‖ *
      (2 * α2 * ‖G x (b', o)‖ ^ 2 + 2 * ‖GreenCore_Xcol G X x (b', o)‖ ^ 2)) := by
    intro x
    have h1 : ‖G x (c, o)‖ ≤ ‖M x (c, o)‖ + ‖G x (c, o) - M x (c, o)‖ := by
      calc ‖G x (c, o)‖ = ‖M x (c, o) + (G x (c, o) - M x (c, o))‖ := by rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖G x (c, o)‖ ^ 2 ≤ 2 * ‖M x (c, o)‖ ^ 2 + 2 * ‖G x (c, o) - M x (c, o)‖ ^ 2 := by
      nlinarith [sq_nonneg (‖M x (c, o)‖ - ‖G x (c, o) - M x (c, o)‖), norm_nonneg (G x (c, o))]
    have hZ : ∀ b', ‖GreenCore_Acol G X D t m (b', o) * G x (b', o) + GreenCore_Xcol G X x (b', o)‖ ^ 2 ≤
        2 * α2 * ‖G x (b', o)‖ ^ 2 + 2 * ‖GreenCore_Xcol G X x (b', o)‖ ^ 2 := by
      intro b'
      have h3 := norm_add_le (GreenCore_Acol G X D t m (b', o) * G x (b', o)) (GreenCore_Xcol G X x (b', o))
      rw [norm_mul] at h3
      have h4 : (‖GreenCore_Acol G X D t m (b', o)‖ * ‖G x (b', o)‖) ^ 2 ≤ α2 * ‖G x (b', o)‖ ^ 2 := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_right (hA _) (sq_nonneg _)
      nlinarith [sq_nonneg (‖GreenCore_Acol G X D t m (b', o)‖ * ‖G x (b', o)‖ - ‖GreenCore_Xcol G X x (b', o)‖),
        norm_nonneg (GreenCore_Acol G X D t m (b', o) * G x (b', o) + GreenCore_Xcol G X x (b', o)),
        mul_nonneg (norm_nonneg (GreenCore_Acol G X D t m (b', o))) (norm_nonneg (G x (b', o)))]
    have h5 : ‖G x (c, o) - M x (c, o)‖ ^ 2 ≤ ρ * ∑ b', ‖Mb b' c‖ *
        (2 * α2 * ‖G x (b', o)‖ ^ 2 + 2 * ‖GreenCore_Xcol G X x (b', o)‖ ^ 2) := by
      rw [hΔ x (c, o), norm_neg]
      have h6 : ‖∑ b', Mb b' c * (GreenCore_Acol G X D t m (b', o) * G x (b', o) + GreenCore_Xcol G X x (b', o))‖ ≤
          ∑ b', ‖Mb b' c‖ * ‖GreenCore_Acol G X D t m (b', o) * G x (b', o) + GreenCore_Xcol G X x (b', o)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun b' _ => (norm_mul _ _).le)
      have h7 : (∑ b', ‖Mb b' c‖ * ‖GreenCore_Acol G X D t m (b', o) * G x (b', o) + GreenCore_Xcol G X x (b', o)‖) ^ 2 ≤
          (∑ b', ‖Mb b' c‖) * ∑ b', ‖Mb b' c‖ *
            ‖GreenCore_Acol G X D t m (b', o) * G x (b', o) + GreenCore_Xcol G X x (b', o)‖ ^ 2 :=
        Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun b' _ => norm_nonneg _) (fun b' _ => by positivity)
          fun b' _ => le_of_eq (by ring)
      have h8 : ∑ b', ‖Mb b' c‖ * ‖GreenCore_Acol G X D t m (b', o) * G x (b', o) + GreenCore_Xcol G X x (b', o)‖ ^ 2 ≤
          ∑ b', ‖Mb b' c‖ * (2 * α2 * ‖G x (b', o)‖ ^ 2 + 2 * ‖GreenCore_Xcol G X x (b', o)‖ ^ 2) :=
        Finset.sum_le_sum fun b' _ => mul_le_mul_of_nonneg_left (hZ b') (norm_nonneg _)
      calc _ ≤ (∑ b', ‖Mb b' c‖ * ‖GreenCore_Acol G X D t m (b', o) * G x (b', o) + GreenCore_Xcol G X x (b', o)‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h6 2
        _ ≤ _ := h7.trans (mul_le_mul (hρ c) h8 (Finset.sum_nonneg fun b' _ => by positivity) hρ0)
    linarith
  have hsum : GreenCore_R G a (c, o) ≤ ((W : ℝ) ^ d)⁻¹ * ∑ o', (2 * ‖M (a, o') (c, o)‖ ^ 2 +
      2 * (ρ * ∑ b', ‖Mb b' c‖ * (2 * α2 * ‖G (a, o') (b', o)‖ ^ 2 + 2 * ‖GreenCore_Xcol G X (a, o') (b', o)‖ ^ 2))) :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun o' _ => pt (a, o')) hw.le
  refine hsum.trans ?_
  have hX' : ∀ b', ((W : ℝ) ^ d)⁻¹ * ∑ o', ‖GreenCore_Xcol G X (a, o') (b', o)‖ ^ 2 ≤
      Φ * (2 * GreenCore_loop G a b' + (26 / κ ^ 2) * δ ^ 2 * GreenCore_R G a (b', o)) :=
    fun b' => GreenCore_Xcol_avg hΦ0 hκ hX hRrow a (b', o)
  -- the double sum over `(o', b')`, summed first over `o'`
  have e1 : ∀ b', ((W : ℝ) ^ d)⁻¹ * ∑ o', ‖Mb b' c‖ * (2 * α2 * ‖G (a, o') (b', o)‖ ^ 2 +
      2 * ‖GreenCore_Xcol G X (a, o') (b', o)‖ ^ 2) =
      ‖Mb b' c‖ * (2 * α2 * GreenCore_R G a (b', o) +
        2 * (((W : ℝ) ^ d)⁻¹ * ∑ o', ‖GreenCore_Xcol G X (a, o') (b', o)‖ ^ 2)) := by
    intro b'
    unfold GreenCore_R
    simp only [← Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    ring
  have e := GreenCore_dsum (fun o' => ‖M (a, o') (c, o)‖ ^ 2)
    (fun o' b' => ‖Mb b' c‖ * (2 * α2 * ‖G (a, o') (b', o)‖ ^ 2 + 2 * ‖GreenCore_Xcol G X (a, o') (b', o)‖ ^ 2))
    (((W : ℝ) ^ d)⁻¹) ρ
  rw [e]
  simp only [e1]
  rw [GreenCore_sumM2 hM a c o]
  have hb : ∀ b', ‖Mb b' c‖ * (2 * α2 * GreenCore_R G a (b', o) +
      2 * (((W : ℝ) ^ d)⁻¹ * ∑ o', ‖GreenCore_Xcol G X (a, o') (b', o)‖ ^ 2)) ≤
      ‖Mb b' c‖ * (2 * α2 * GreenCore_R G a (b', o) +
        2 * (Φ * (2 * GreenCore_loop G a b' + (26 / κ ^ 2) * δ ^ 2 * GreenCore_R G a (b', o)))) :=
    fun b' => mul_le_mul_of_nonneg_left (by linarith [hX' b']) (norm_nonneg _)
  have hb2 := Finset.sum_le_sum fun b' (_ : b' ∈ (Finset.univ : Finset (Zd d L))) => hb b'
  have hρ' : 0 ≤ 2 * ρ := by positivity
  calc 2 * (((W : ℝ) ^ d)⁻¹ * ‖Mb a c‖ ^ 2) + 2 * ρ * ∑ b', ‖Mb b' c‖ * (2 * α2 * GreenCore_R G a (b', o) +
        2 * (((W : ℝ) ^ d)⁻¹ * ∑ o', ‖GreenCore_Xcol G X (a, o') (b', o)‖ ^ 2))
      ≤ 2 * (((W : ℝ) ^ d)⁻¹ * ‖Mb a c‖ ^ 2) + 2 * ρ * ∑ b', ‖Mb b' c‖ * (2 * α2 * GreenCore_R G a (b', o) +
        2 * (Φ * (2 * GreenCore_loop G a b' + (26 / κ ^ 2) * δ ^ 2 * GreenCore_R G a (b', o)))) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hb2 hρ')
    _ = _ := by
        rw [add_assoc]
        congr 1
        · ring
        · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring


/-- The block distance `|a - b|` (`zdistD`) as a real function: the metric properties used by the closure. -/
theorem GreenCore_dist : (∀ a : Zd d L, ((zdistD d L (a - a) : ℕ) : ℝ) = 0) ∧
    (∀ a b : Zd d L, 0 ≤ ((zdistD d L (a - b) : ℕ) : ℝ)) ∧
    (∀ a b : Zd d L, ((zdistD d L (a - b) : ℕ) : ℝ) = ((zdistD d L (b - a) : ℕ) : ℝ)) ∧
    (∀ a b c : Zd d L, ((zdistD d L (a - c) : ℕ) : ℝ) ≤ ((zdistD d L (a - b) : ℕ) : ℝ) + ((zdistD d L (b - c) : ℕ) : ℝ)) := by
  refine ⟨fun a => by simp, fun a b => Nat.cast_nonneg _, fun a b => ?_, fun a b c => ?_⟩
  · rw [← neg_sub b a, zdistD_neg]
  · have := zdistD_add_le d L (a - b) (b - c)
    rw [show a - b + (b - c) = a - c by ring] at this
    exact_mod_cast this

/-- `ϑ = α² + 26 κ⁻² Φ δ²` with `α² = 4 κ⁻² (2 d g₀ + (1 + 2 d g₀)/κ)² δ²` (the bound of `|A'|²`): the closure constant of (R*). -/
def GreenCore_theta (d : ℕ) (κ Φ δ g₀ : ℝ) : ℝ :=
  (4 / κ ^ 2) * (2 * d * g₀ + (1 + 2 * d * g₀) / κ) ^ 2 * δ ^ 2 + 26 / κ ^ 2 * Φ * δ ^ 2

/-- **(R\*)**, `G3a` row R3: on `Ω ∩ LDE`, for every block `a`, column `y = (c, o)` and loop control `φ`
(`𝓛^{(2)}_{(-,+),(a,b)} ≤ φ(a,b)²`), `R_{a,(c,o)} ≤ 4 c₀⁻² S W^{-d} e^{-(c₀/2)|a-c|} +
16 ρ Φ c₀⁻¹ S Σ_{b''} e^{-(c₀/2)|c-b''|} φ(a,b'')²` (`(a′)` D3.2), under `8 ρ c₀⁻¹ S ϑ ≤ 1` (`GreenCore_theta`).
Only the uniform facts are used: Kronecker `M`, `|M_{ab}| ≤ c₀⁻¹ e^{-c₀|a-b|}`, `ℓ¹` rows (`ρ`, `S`), `κ ≤ |m|`. -/
theorem GreenCore_Rbound (hL : 3 ≤ L) {t g₀ c₀ ρ S : ℝ} {s z : ℂ}
    (hGR : G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1)
    (hRG : (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1)
    (hMR : (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * M = 1)
    (hMR' : M * (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1) (hz : z = s - (t : ℂ) * m)
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hMd : ∀ a, Mb a a = m)
    (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0)
    (hκ : 0 < κ) (hκm : κ ≤ ‖m‖) (hm1 : ‖m‖ ≤ 1) (hMb1 : ∀ a b, ‖Mb a b‖ ≤ 1) (hc₀ : 0 < c₀)
    (hdec : ∀ a b, ‖Mb a b‖ ≤ c₀⁻¹ * Real.exp (-c₀ * (zdistD d L (a - b) : ℝ)))
    (hρ : ∀ c, ∑ b, ‖Mb b c‖ ≤ ρ)
    (hS : ∀ a, ∑ b, Real.exp (-(c₀ / 2) * (zdistD d L (a - b) : ℝ)) ≤ S)
    (hg : 0 ≤ g₀) (hΦ : 1 ≤ Φ) (hδ : δ ≤ κ / 2) (hδ0 : 0 ≤ δ)
    (hwd : ((W : ℝ) ^ d)⁻¹ ≤ δ ^ 2) (hΩ : ∀ u v, ‖G u v - M u v‖ ≤ δ)
    (hLcol : LDECol X G (svar d L W 0) Φ) (hC1 : 8 * ρ * (c₀⁻¹ * S) * GreenCore_theta d κ Φ δ g₀ ≤ 1)
    (φ : Zd d L → Zd d L → ℝ) (hφ : ∀ a b, GreenCore_loop G a b ≤ φ a b ^ 2) (a c : Zd d L) (o : Fin (W ^ d)) :
    GreenCore_R G a (c, o) ≤ 4 * c₀⁻¹ ^ 2 * S * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c₀ / 2) * (zdistD d L (a - c) : ℝ)) +
      16 * ρ * Φ * c₀⁻¹ * S * ∑ b'', Real.exp (-(c₀ / 2) * (zdistD d L (c - b'') : ℝ)) * φ a b'' ^ 2 := by
  have hΦ0 : 0 ≤ Φ := by linarith
  have hκ1 : κ ≤ 1 := hκm.trans hm1
  obtain ⟨hGuu, hG32, hGoff⟩ := GreenCore_crude hM hMd hMb1 hκm hm1 hδ hΩ
  have hG0 : ∀ u, G u u ≠ 0 := fun u h => by
    have := hGuu u; rw [h, norm_zero] at this; linarith
  have hΔ := GreenCore_Delta_col (X := X) hGR hRG hMR hz hM hG0
  have hA := fun w => GreenCore_Acol_sq hL hg hκ hGR hRG hMR hMR' hz hM hMd hD hκm hMb1 hGuu hΩ w
  have hX := fun x w => GreenCore_Xcol_sq hκ hΦ0 hGuu hLcol x w
  have hRrow := (GreenCore_apriori hG32 hGoff hδ0 hwd).2
  have hρ0 : 0 ≤ ρ := le_trans (Finset.sum_nonneg fun b _ => norm_nonneg _) (hρ 0)
  have hα : 0 ≤ (4 / κ ^ 2) * (2 * d * g₀ + (1 + 2 * d * g₀) / κ) ^ 2 * δ ^ 2 := by positivity
  have h2 := GreenCore_twoSided hρ0 hκ hΦ0 hα hM hρ hΔ hA hX hRrow
  obtain ⟨d0, dn, ds, dt⟩ := GreenCore_dist (d := d) (L := L)
  have hϑ : 0 ≤ GreenCore_theta d κ Φ δ g₀ := by unfold GreenCore_theta; positivity
  refine GreenCore_Rstar (fun a b => ((zdistD d L (a - b) : ℕ) : ℝ)) d0 dn ds dt (fun a b => Mb a b) hc₀ hκ
    (fun a => by rw [hMd]; exact hκm) hdec (fun c => GreenCore_rhoe _ ds _ hc₀ hdec hS c) hS GreenCore_w_pos hρ0 hΦ0 hϑ hC1 a
    (fun b'' => φ a b'') (fun c => GreenCore_R G a (c, o)) (fun c => ?_) (fun c => ?_) c
  · exact mul_nonneg GreenCore_w_pos.le (Finset.sum_nonneg fun _ _ => by positivity)
  · refine (h2 a c o).trans ?_
    have : ∑ b', ‖Mb b' c‖ * GreenCore_loop G a b' ≤ ∑ b', ‖Mb b' c‖ * φ a b' ^ 2 :=
      Finset.sum_le_sum fun b' _ => mul_le_mul_of_nonneg_left (hφ a b') (norm_nonneg _)
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 8 * ρ * Φ)
    unfold GreenCore_theta
    linarith

end Reentry


section Coupled
variable {d L W : ℕ} [NeZero L] [NeZero W] {G X M D : Matrix (Vtx d L W) (Vtx d L W) ℂ}
  {Mb : Matrix (Zd d L) (Zd d L) ℂ} {m : ℂ} {κ Φ δ : ℝ}

/-- **(E0) + (E1)** in entries (row form): `Δ_{xy} = -Σ_{b'} M^{(B)}_{[x]b'} (A_u G_{uy} + 𝔛_{uy})`, `u = (b', o_x)`. -/
theorem GreenCore_Delta_row {t : ℝ} {s z : ℂ} (hGR : G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1)
    (hRG : (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1)
    (hMR : M * (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1) (hz : z = s - (t : ℂ) * m)
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hG0 : ∀ u, G u u ≠ 0) (x y : Vtx d L W) :
    G x y - M x y = -∑ b', Mb x.1 b' * (GreenCore_Arow G X D t m (b', x.2) * G (b', x.2) y +
      GreenCore_Xrow G X (b', x.2) y) := by
  have key : (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) - (D + X - z • 1) =
      -(X + ((t : ℂ) * m) • 1) := by rw [hz]; module
  have e0 : G - M = -(M * ((X + ((t : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G)) := by
    calc G - M = M * (D - s • 1) * G - M * (D + X - z • 1) * G := by
          rw [mul_assoc M (D + X - z • 1) G, hRG, mul_one, hMR, one_mul]
      _ = _ := by rw [← sub_mul, ← mul_sub, key, mul_neg, neg_mul, mul_assoc]
  have e1 : ∀ u, ((X + ((t : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G) u y =
      GreenCore_Arow G X D t m u * G u y + GreenCore_Xrow G X u y := by
    intro u
    have h1 := GreenCore_E1 (X := X) hGR u y (hG0 u)
    have h2 : ((X + ((t : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G) u y =
        ∑ v, X u v * G v y + (t : ℂ) * m * G u y := by
      rw [Matrix.mul_apply]
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single u (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp
    rw [h2, h1]; unfold GreenCore_Arow GreenCore_Xrow; ring
  have h3 := congrFun (congrFun e0 x) y
  rw [Matrix.sub_apply, Matrix.neg_apply] at h3
  rw [h3, Matrix.mul_apply]
  congr 1
  have h4 := GreenCore_sum_kron' hM (fun u => ((X + ((t : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G) u y) x
  rw [h4]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [e1 (b', x.2)]

/-- `𝒦_{uy} = t v̄_{[u]} Δ_{uy} - (A_u + t v̄_{[u]}) G_{uy} - 𝔛_{uy}`: the residual of the coupled system (E3). -/
def GreenCore_K (G M X D : Matrix (Vtx d L W) (Vtx d L W) ℂ) (t : ℝ) (m : ℂ) (u y : Vtx d L W) : ℂ :=
  (t : ℂ) * GreenCore_vbar G M u.1 * (G u y - M u y) -
    (GreenCore_Arow G X D t m u + (t : ℂ) * GreenCore_vbar G M u.1) * G u y - GreenCore_Xrow G X u y

/-- **(E3)**: `Δ = M 𝒮[Δ] M + M 𝒦`, `𝒮[Δ] = diag(t v̄_{[u]})`, in entries. -/
theorem GreenCore_E3 {t : ℝ} {s z : ℂ} (hGR : G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1)
    (hRG : (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1)
    (hMR : M * (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1) (hz : z = s - (t : ℂ) * m)
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hG0 : ∀ u, G u u ≠ 0) (x y : Vtx d L W) :
    G x y - M x y = ∑ b', Mb x.1 b' * ((t : ℂ) * GreenCore_vbar G M b' * M (b', x.2) y) +
      ∑ b', Mb x.1 b' * GreenCore_K G M X D t m (b', x.2) y := by
  rw [GreenCore_Delta_row hGR hRG hMR hz hM hG0, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b' _ => ?_
  unfold GreenCore_K
  ring


/-- **The stability of the coupled system**, the block Anderson twin of `Stable S ξ K` (`Green/EntryCore.lean:911`):
`‖(1 - t M^{(+,+)})⁻¹‖_{max→max} ≤ K` at the real-axis data `(g, E, m)` of `M^{(B)} = (g Ψ^{(B)} - E - m)⁻¹`,
`M^{(+,+)}_{ab} = M^{(B)}_{ba} M^{(B)}_{ab}` (`BAMss`, `BA/MFixedPoint.lean:511`); stated without forming the inverse.
`K = 16 κ⁻⁴` at `BAReal` data is G3b's theorem. -/
def BAStab (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (t K : ℝ) : Prop :=
  ∀ (v : Zd d L → ℂ) (B : ℝ),
    (∀ a, ‖v a - (t : ℂ) * ∑ b, BAMss d L (BAMB d L g (E : ℂ) m) true true a b * v b‖ ≤ B) →
      ∀ a, ‖v a‖ ≤ K * B

/-- **The coupled bound** `‖Δ‖_max ≤ K_BA ‖𝒦‖_max`, `K_BA = ρ (1 + ρ₂ K_Θ)`: from `Δ = M 𝒮[Δ] M + M 𝒦` (E3), the
stability `hstab` of `1 - t M^{(+,+)}` (block averages `v̄_a = W^{-d} Σ_{k∈a} Δ_{kk}` solve it with the right side
`⟨M𝒦⟩`), `ρ ≥ max_a Σ_b |M_{ab}|`, `ρ₂ ≥ max_{a,c} Σ_b |M_{ab}||M_{bc}|`. -/
theorem GreenCore_coupled {Δ 𝒦 : Vtx d L W → Vtx d L W → ℂ} {vb : Zd d L → ℂ} {t Kθ ρ ρ₂ K𝒦 : ℝ}
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hKθ : 0 ≤ Kθ)
    (hρ : ∀ a, ∑ b, ‖Mb a b‖ ≤ ρ) (hρ₂ : ∀ a c, ∑ b, ‖Mb a b‖ * ‖Mb b c‖ ≤ ρ₂)
    (hv : ∀ a, vb a = (((W : ℝ) ^ d)⁻¹ : ℝ) * ∑ o, Δ (a, o) (a, o))
    (hE3 : ∀ x y, Δ x y = ∑ b', Mb x.1 b' * ((t : ℂ) * vb b' * M (b', x.2) y) +
      ∑ b', Mb x.1 b' * 𝒦 (b', x.2) y)
    (hstab : ∀ (v : Zd d L → ℂ) (B : ℝ), (∀ a, ‖v a - (t : ℂ) * ∑ b, (Mb b a * Mb a b) * v b‖ ≤ B) →
      ∀ a, ‖v a‖ ≤ Kθ * B)
    (hK : ∀ u y, ‖𝒦 u y‖ ≤ K𝒦) (x y : Vtx d L W) : ‖Δ x y‖ ≤ ρ * (1 + ρ₂ * Kθ) * K𝒦 := by
  have hw := GreenCore_w_pos (d := d) (W := W)
  have hK0 : 0 ≤ K𝒦 := le_trans (norm_nonneg _) (hK x y)
  have hρ0 : 0 ≤ ρ := le_trans (Finset.sum_nonneg fun b _ => norm_nonneg _) (hρ 0)
  have hρ20 : 0 ≤ ρ₂ := le_trans (Finset.sum_nonneg fun b _ => by positivity) (hρ₂ 0 0)
  -- the averaged equation for `v̄`
  have hM' : ∀ (b' a : Zd d L) (o : Fin (W ^ d)), M (b', o) (a, o) = Mb b' a := fun b' a o => by simp [hM]
  have hbar : ∀ a, vb a - (t : ℂ) * ∑ b, (Mb b a * Mb a b) * vb b =
      (((W : ℝ) ^ d)⁻¹ : ℝ) * ∑ o, ∑ b', Mb a b' * 𝒦 (b', o) (a, o) := by
    intro a
    have h1 : ∀ o : Fin (W ^ d), Δ (a, o) (a, o) = (t : ℂ) * ∑ b, (Mb b a * Mb a b) * vb b +
        ∑ b', Mb a b' * 𝒦 (b', o) (a, o) := by
      intro o
      rw [hE3 (a, o) (a, o)]
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by simp only [hM']; ring
    rw [hv a]
    simp only [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_add]
    have : (((W : ℝ) ^ d)⁻¹ : ℝ) * (((W ^ d : ℕ) : ℂ) * ((t : ℂ) * ∑ b, (Mb b a * Mb a b) * vb b)) =
        (t : ℂ) * ∑ b, (Mb b a * Mb a b) * vb b := by
      have h3 : (((W : ℝ) ^ d)⁻¹ : ℝ) * ((W ^ d : ℕ) : ℂ) = 1 := by
        have := GreenCore_w_mul (d := d) (W := W)
        exact_mod_cast this
      rw [← mul_assoc, h3, one_mul]
    rw [this]; ring
  have hv1 : ∀ a, ‖vb a‖ ≤ Kθ * (ρ * K𝒦) := by
    refine hstab vb (ρ * K𝒦) fun a => ?_
    rw [hbar a, norm_mul, Complex.norm_real, Real.norm_of_nonneg hw.le]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hw.le).trans (GreenCore_avg_le fun o => ?_)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ b', ‖Mb a b' * 𝒦 (b', o) (a, o)‖ ≤ ∑ b', ‖Mb a b'‖ * K𝒦 :=
          Finset.sum_le_sum fun b' _ => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hK _ _) (norm_nonneg _)
      _ ≤ ρ * K𝒦 := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hρ _) hK0
  rw [hE3 x y]
  have h2 : ‖∑ b', Mb x.1 b' * ((t : ℂ) * vb b' * M (b', x.2) y)‖ ≤ (ρ₂ * Kθ * (ρ * K𝒦)) := by
    refine (norm_sum_le _ _).trans ?_
    have hMy : ∀ b', ‖M (b', x.2) y‖ ≤ ‖Mb b' y.1‖ := fun b' => by
      rw [hM]; split_ifs
      · exact le_rfl
      · simp
    calc ∑ b', ‖Mb x.1 b' * ((t : ℂ) * vb b' * M (b', x.2) y)‖
        ≤ ∑ b', ‖Mb x.1 b'‖ * ‖Mb b' y.1‖ * (Kθ * (ρ * K𝒦)) := by
          refine Finset.sum_le_sum fun b' _ => ?_
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
          have := mul_le_mul (mul_le_mul ht1 (hv1 b') (norm_nonneg _) zero_le_one) (hMy b') (norm_nonneg _)
            (mul_nonneg zero_le_one (mul_nonneg hKθ (mul_nonneg hρ0 hK0)))
          calc ‖Mb x.1 b'‖ * (t * ‖vb b'‖ * ‖M (b', x.2) y‖) ≤ ‖Mb x.1 b'‖ * (1 * (Kθ * (ρ * K𝒦)) * ‖Mb b' y.1‖) :=
                mul_le_mul_of_nonneg_left this (norm_nonneg _)
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


/-- Constants of the diagonal law: `R₀ = 4 c₀⁻² S W^{-d} + 16 ρ Φ c₀⁻¹ S² L` (the sup form of (R*)), `X_b = Φ (2 + 18 κ⁻²) R₀`
(bound of `|𝔛|²`), `A_b = 5 (4κ⁻² R₀ (13/4) δ² + Φ (2 L + 8 κ⁻² R₀ (13/4) δ²) + Φ W^{-d} + (2 d g₀)² X_b)` (bound of `|A_u + t v̄|²`). -/
def GreenCore_R0 (c₀ ρ S Φ w₀ Lm : ℝ) : ℝ := 4 * c₀⁻¹ ^ 2 * S * w₀ + 16 * ρ * Φ * c₀⁻¹ * S * (S * Lm)

def GreenCore_Xb (κ Φ c₀ ρ S w₀ Lm : ℝ) : ℝ := Φ * (2 + 18 / κ ^ 2) * GreenCore_R0 c₀ ρ S Φ w₀ Lm

def GreenCore_Ab (d : ℕ) (κ Φ δ c₀ ρ S g₀ w₀ Lm : ℝ) : ℝ :=
  5 * ((4 / κ ^ 2) * GreenCore_R0 c₀ ρ S Φ w₀ Lm * (13 / 4 * δ ^ 2) +
    Φ * (2 * Lm + (8 / κ ^ 2) * GreenCore_R0 c₀ ρ S Φ w₀ Lm * (13 / 4 * δ ^ 2)) + Φ * w₀ +
    (2 * d * g₀) ^ 2 * GreenCore_Xb κ Φ c₀ ρ S w₀ Lm)


/-- **The diagonal law**, `G3a` row R4 (the BA reading of `(4.3)`): on `Ω ∩ LDE`, with `L = max_{a,b} 𝓛^{(2)}_{(-,+),(a,b)}`
and `K_BA = ρ (1 + ρ₂ K_Θ)`, `K_BA δ ≤ 1/2`: `‖G - M‖²_max ≤ 8 K_BA² ((9/4) A_b + X_b)`, which is `≲ K_BA² Φ² (L + W^{-d})`
(`GreenCore_Ab`, `GreenCore_Xb`: polynomial in `L` and `W^{-d}`).  The stability of the coupled system enters only as
`BAStab` (G3b); the proof: (R*) in sup form, `|𝔛|` (`Xrow_sq`), `|A_u + t v̄| = |ε_2 - ε_1 + X_{uu} - Q^{XD}_u|` (E2), (E3), `coupled`. -/
theorem GreenCore_diag (hL : 3 ≤ L) {t g₀ c₀ ρ S E Kθ ρ₂ Lm : ℝ} {s z : ℂ}
    (hGR : G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1)
    (hRG : (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1)
    (hMR : (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * M = 1)
    (hMR' : M * (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1) (hz : z = s - (t : ℂ) * m)
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hMd : ∀ a, Mb a a = m)
    (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0)
    (hκ : 0 < κ) (hκm : κ ≤ ‖m‖) (hm1 : ‖m‖ ≤ 1) (hMb1 : ∀ a b, ‖Mb a b‖ ≤ 1) (hc₀ : 0 < c₀)
    (hdec : ∀ a b, ‖Mb a b‖ ≤ c₀⁻¹ * Real.exp (-c₀ * (zdistD d L (a - b) : ℝ)))
    (hρ : ∀ c, ∑ b, ‖Mb b c‖ ≤ ρ)
    (hS : ∀ a, ∑ b, Real.exp (-(c₀ / 2) * (zdistD d L (a - b) : ℝ)) ≤ S)
    (hg : 0 ≤ g₀) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hΦ : 1 ≤ Φ) (hδ : δ ≤ κ / 2) (hδ0 : 0 ≤ δ)
    (hwd : ((W : ℝ) ^ d)⁻¹ ≤ δ ^ 2) (hΩ : ∀ u v, ‖G u v - M u v‖ ≤ δ)
    (hLrow : LDERow X G (svar d L W 0) Φ) (hLcol : LDECol X G (svar d L W 0) Φ)
    (hLquad : LDEQuad X G (svar d L W 0) t Φ) (hLdiag : ∀ i, ‖X i i‖ ^ 2 ≤ Φ * svar d L W 0 i i)
    (hC1 : 8 * ρ * (c₀⁻¹ * S) * GreenCore_theta d κ Φ δ g₀ ≤ 1)
    (hLm : ∀ a b, GreenCore_loop G a b ≤ Lm) (hLm0 : 0 ≤ Lm)
    (hMb : Mb = BAMB d L g₀ (E : ℂ) m) (hstab : BAStab d L g₀ E m t Kθ) (hKθ : 0 ≤ Kθ)
    (hρr : ∀ a, ∑ b, ‖Mb a b‖ ≤ ρ) (hρ₂ : ∀ a c, ∑ b, ‖Mb a b‖ * ‖Mb b c‖ ≤ ρ₂)
    (hKδ : ρ * (1 + ρ₂ * Kθ) * δ ≤ 1 / 2) (x y : Vtx d L W) :
    ‖G x y - M x y‖ ^ 2 ≤ 8 * (ρ * (1 + ρ₂ * Kθ)) ^ 2 *
      (9 / 4 * GreenCore_Ab d κ Φ δ c₀ ρ S g₀ ((W : ℝ) ^ d)⁻¹ Lm + GreenCore_Xb κ Φ c₀ ρ S ((W : ℝ) ^ d)⁻¹ Lm) := by
  have hw := GreenCore_w_pos (d := d) (W := W)
  have hΦ0 : 0 ≤ Φ := by linarith
  have hκ1 : κ ≤ 1 := hκm.trans hm1
  obtain ⟨hGuu, hG32, hGoff⟩ := GreenCore_crude hM hMd hMb1 hκm hm1 hδ hΩ
  have hG0 : ∀ u, G u u ≠ 0 := fun u h => by
    have := hGuu u; rw [h, norm_zero] at this; linarith
  have hS0 : 0 ≤ S := le_trans (Finset.sum_nonneg fun b _ => (Real.exp_pos _).le) (hS 0)
  have hρ0 : 0 ≤ ρ := le_trans (Finset.sum_nonneg fun b _ => norm_nonneg _) (hρ 0)
  have hρ20 : 0 ≤ ρ₂ := le_trans (Finset.sum_nonneg fun b _ => by positivity) (hρ₂ 0 0)
  have hap := GreenCore_apriori hG32 hGoff hδ0 hwd
  -- (1) the sup form of (R*)
  have hR : ∀ a y, GreenCore_R G a y ≤ GreenCore_R0 c₀ ρ S Φ ((W : ℝ) ^ d)⁻¹ Lm := by
    intro a y
    obtain ⟨c, o⟩ := y
    have h := GreenCore_Rbound hL hGR hRG hMR hMR' hz hM hMd hD hκ hκm hm1 hMb1 hc₀ hdec hρ hS hg hΦ hδ hδ0
      hwd hΩ hLcol hC1 (fun _ _ => Real.sqrt Lm)
      (fun a b => by rw [Real.sq_sqrt hLm0]; exact hLm a b) a c o
    refine h.trans ?_
    unfold GreenCore_R0
    have e1 : Real.exp (-(c₀ / 2) * (zdistD d L (a - c) : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [(Nat.cast_nonneg (zdistD d L (a - c)) : (0 : ℝ) ≤ _)])
    have e2 : ∑ b'', Real.exp (-(c₀ / 2) * (zdistD d L (c - b'') : ℝ)) * Real.sqrt Lm ^ 2 ≤ S * Lm := by
      rw [Real.sq_sqrt hLm0, ← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hS c) hLm0
    have h1 : 4 * c₀⁻¹ ^ 2 * S * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c₀ / 2) * (zdistD d L (a - c) : ℝ)) ≤
        4 * c₀⁻¹ ^ 2 * S * ((W : ℝ) ^ d)⁻¹ := by
      calc _ ≤ 4 * c₀⁻¹ ^ 2 * S * ((W : ℝ) ^ d)⁻¹ * 1 := mul_le_mul_of_nonneg_left e1 (by positivity)
        _ = _ := mul_one _
    have h2 := mul_le_mul_of_nonneg_left e2 (by positivity : (0 : ℝ) ≤ 16 * ρ * Φ * c₀⁻¹ * S)
    linarith
  -- (2) the bound for `𝔛`
  have hXr : ∀ u y, ‖GreenCore_Xrow G X u y‖ ^ 2 ≤ GreenCore_Xb κ Φ c₀ ρ S ((W : ℝ) ^ d)⁻¹ Lm := by
    intro u y
    refine (GreenCore_Xrow_sq hκ hΦ0 hGuu hLrow u y).trans ?_
    have h1 : ‖G u y‖ ^ 2 ≤ 9 / 4 := by nlinarith [norm_nonneg (G u y), hG32 u y]
    have h2 := hR u.1 y
    have h3 := hR u.1 u
    have h4 : 0 ≤ GreenCore_R G u.1 u := mul_nonneg hw.le (Finset.sum_nonneg fun _ _ => by positivity)
    have h5 : (8 / κ ^ 2) * ‖G u y‖ ^ 2 * GreenCore_R G u.1 u ≤ (8 / κ ^ 2) * (9 / 4) * GreenCore_R0 c₀ ρ S Φ ((W : ℝ) ^ d)⁻¹ Lm :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h3 h4 (by positivity)
    unfold GreenCore_Xb
    have e : Φ * (2 + 18 / κ ^ 2) * GreenCore_R0 c₀ ρ S Φ ((W : ℝ) ^ d)⁻¹ Lm =
        Φ * (2 * GreenCore_R0 c₀ ρ S Φ ((W : ℝ) ^ d)⁻¹ Lm + (8 / κ ^ 2) * (9 / 4) * GreenCore_R0 c₀ ρ S Φ ((W : ℝ) ^ d)⁻¹ Lm) := by
      field_simp; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) hΦ0
  -- (3) the bound for `A_u + t v̄`
  have hA : ∀ u, ‖GreenCore_Arow G X D t m u + (t : ℂ) * GreenCore_vbar G M u.1‖ ^ 2 ≤
      GreenCore_Ab d κ Φ δ c₀ ρ S g₀ ((W : ℝ) ^ d)⁻¹ Lm := by
    intro u
    refine (GreenCore_Arow_four hM hMd (hG0 u)).trans ?_
    unfold GreenCore_Ab
    have hR1 := hR u.1 u
    have hR2 : 0 ≤ GreenCore_R G u.1 u := mul_nonneg hw.le (Finset.sum_nonneg fun _ _ => by positivity)
    have hR3 := hap.2 u u.1
    have hR4 : 0 ≤ GreenCore_Rrow G u u.1 := mul_nonneg hw.le (Finset.sum_nonneg fun _ _ => by positivity)
    have hRR : GreenCore_R G u.1 u * GreenCore_Rrow G u u.1 ≤ GreenCore_R0 c₀ ρ S Φ ((W : ℝ) ^ d)⁻¹ Lm * (13 / 4 * δ ^ 2) :=
      mul_le_mul hR1 hR3 hR4 (le_trans hR2 hR1)
    have b2 : ‖GreenCore_eps2 G t u‖ ^ 2 ≤
        (4 / κ ^ 2) * GreenCore_R0 c₀ ρ S Φ ((W : ℝ) ^ d)⁻¹ Lm * (13 / 4 * δ ^ 2) := by
      refine (GreenCore_eps2_loc (G := G) ht0 ht1 hκ hGuu u).trans ?_
      rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_left hRR (by positivity)
    have b1 : ‖GreenCore_eps1 G X t u‖ ^ 2 ≤ Φ * (2 * Lm + (8 / κ ^ 2) * GreenCore_R0 c₀ ρ S Φ ((W : ℝ) ^ d)⁻¹ Lm * (13 / 4 * δ ^ 2)) := by
      refine (GreenCore_eps1_loc hκ hΦ0 hGuu hLquad u).trans (mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left (hLm _ _) two_pos.le) ?_) hΦ0)
      rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_left hRR (by positivity)
    have b3 : ‖X u u‖ ^ 2 ≤ Φ * ((W : ℝ) ^ d)⁻¹ := by
      have := hLdiag u
      rw [GreenCore_svar0] at this; simpa using this
    have b4 := GreenCore_Qxd_sq (G := G) (X := X) hg hL hD (fun l => hXr u l)
    linarith
  -- (4) the residual `𝒦` and the coupled bound at the maximum of `|Δ|`
  obtain ⟨p₀, hp₀⟩ := Finite.exists_max (fun p : Vtx d L W × Vtx d L W => ‖G p.1 p.2 - M p.1 p.2‖)
  have hDm : ∀ x y, ‖G x y - M x y‖ ≤ ‖G p₀.1 p₀.2 - M p₀.1 p₀.2‖ := fun x y => hp₀ (x, y)
  have hDm0 : 0 ≤ ‖G p₀.1 p₀.2 - M p₀.1 p₀.2‖ := norm_nonneg _
  generalize hDmdef : ‖G p₀.1 p₀.2 - M p₀.1 p₀.2‖ = Dm at hDm hDm0
  have hDmδ : Dm ≤ δ := hDmdef ▸ hΩ _ _
  have hvb : ∀ a, ‖GreenCore_vbar G M a‖ ≤ Dm := fun a => by
    unfold GreenCore_vbar
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw.le]
    exact (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hw.le).trans (GreenCore_avg_le fun o => hDm _ _)
  have hKb : ∀ u y, ‖GreenCore_K G M X D t m u y‖ ≤
      Dm * δ + 3 / 2 * Real.sqrt (GreenCore_Ab d κ Φ δ c₀ ρ S g₀ ((W : ℝ) ^ d)⁻¹ Lm) +
        Real.sqrt (GreenCore_Xb κ Φ c₀ ρ S ((W : ℝ) ^ d)⁻¹ Lm) := by
    intro u y
    unfold GreenCore_K
    have h1 : ‖(t : ℂ) * GreenCore_vbar G M u.1 * (G u y - M u y)‖ ≤ Dm * δ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
      calc t * ‖GreenCore_vbar G M u.1‖ * ‖G u y - M u y‖ ≤ 1 * Dm * δ :=
            mul_le_mul (mul_le_mul ht1 (hvb _) (norm_nonneg _) zero_le_one) (hΩ _ _) (norm_nonneg _)
              (mul_nonneg zero_le_one hDm0)
        _ = Dm * δ := by ring
    have h2 : ‖(GreenCore_Arow G X D t m u + (t : ℂ) * GreenCore_vbar G M u.1) * G u y‖ ≤
        Real.sqrt (GreenCore_Ab d κ Φ δ c₀ ρ S g₀ ((W : ℝ) ^ d)⁻¹ Lm) * (3 / 2) := by
      rw [norm_mul]
      exact mul_le_mul ((le_abs_self _).trans (Real.abs_le_sqrt (hA u))) (hG32 u y) (norm_nonneg _) (Real.sqrt_nonneg _)
    have h3 : ‖GreenCore_Xrow G X u y‖ ≤ Real.sqrt (GreenCore_Xb κ Φ c₀ ρ S ((W : ℝ) ^ d)⁻¹ Lm) :=
      (le_abs_self _).trans (Real.abs_le_sqrt (hXr u y))
    calc _ ≤ ‖(t : ℂ) * GreenCore_vbar G M u.1 * (G u y - M u y) -
          (GreenCore_Arow G X D t m u + (t : ℂ) * GreenCore_vbar G M u.1) * G u y‖ + ‖GreenCore_Xrow G X u y‖ :=
          norm_sub_le _ _
      _ ≤ (‖(t : ℂ) * GreenCore_vbar G M u.1 * (G u y - M u y)‖ +
          ‖(GreenCore_Arow G X D t m u + (t : ℂ) * GreenCore_vbar G M u.1) * G u y‖) + ‖GreenCore_Xrow G X u y‖ :=
          add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ _ := by linarith
  have hstab' : ∀ (v : Zd d L → ℂ) (B : ℝ), (∀ a, ‖v a - (t : ℂ) * ∑ b, (Mb b a * Mb a b) * v b‖ ≤ B) →
      ∀ a, ‖v a‖ ≤ Kθ * B := by
    subst hMb
    intro v B hv a
    exact hstab v B (fun a' => by simpa [BAMss, BAMsigma] using hv a') a
  have hcoup := fun x y => GreenCore_coupled (M := M) (Mb := Mb) (Δ := fun x y => G x y - M x y)
    (𝒦 := GreenCore_K G M X D t m) (vb := GreenCore_vbar G M) hM ht0 ht1 hKθ hρr hρ₂ (fun a => rfl)
    (fun x y => GreenCore_E3 hGR hRG hMR' hz hM hG0 x y) hstab' hKb x y
  have hmax := hcoup p₀.1 p₀.2
  rw [hDmdef] at hmax
  have hAb0 : 0 ≤ GreenCore_Ab d κ Φ δ c₀ ρ S g₀ ((W : ℝ) ^ d)⁻¹ Lm := le_trans (sq_nonneg _) (hA x)
  have hXb0 : 0 ≤ GreenCore_Xb κ Φ c₀ ρ S ((W : ℝ) ^ d)⁻¹ Lm := le_trans (sq_nonneg _) (hXr x y)
  have ha := Real.sq_sqrt hAb0
  have hb := Real.sq_sqrt hXb0
  generalize Real.sqrt (GreenCore_Ab d κ Φ δ c₀ ρ S g₀ ((W : ℝ) ^ d)⁻¹ Lm) = a at *
  generalize Real.sqrt (GreenCore_Xb κ Φ c₀ ρ S ((W : ℝ) ^ d)⁻¹ Lm) = b at *
  have hK0 : 0 ≤ ρ * (1 + ρ₂ * Kθ) := by positivity
  have h2 : Dm ≤ 2 * (ρ * (1 + ρ₂ * Kθ)) * (3 / 2 * a + b) := by
    have := mul_le_mul_of_nonneg_right hKδ hDm0
    nlinarith
  have h3 : ‖G x y - M x y‖ ^ 2 ≤ (2 * (ρ * (1 + ρ₂ * Kθ)) * (3 / 2 * a + b)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) ((hDm x y).trans h2) 2
  refine h3.trans ?_
  rw [← ha, ← hb]
  nlinarith [sq_nonneg (3 / 2 * a - b), sq_nonneg (ρ * (1 + ρ₂ * Kθ))]

end Coupled


section Carrier

variable {d : ℕ}

/-- The carrier at `(n, t, ω)` on the block-product index: `G = blockMat G_t`, `X = blockMat (√t V)`, `D = g₀ Ψ`, `M = blockMat M`. -/
abbrev GreenCore_Gc (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ :=
  blockMat d (sz.L n) (sz.W n) (BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n t ω)
abbrev GreenCore_Xc (sz : Sizes d) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ :=
  blockMat d (sz.L n) (sz.W n) (BAX sz n t ω)
abbrev GreenCore_Mc (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ :=
  blockMat d (sz.L n) (sz.W n) (BAMfine sz (BAflowLam0 sz z) (BAflowEs sz z) n)
abbrev GreenCore_Dc (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ :=
  ((BAflowLam0 sz z n : ℝ) : ℂ) • PsiV d (sz.L n) (sz.W n)

/-- **The carrier satisfies the structural hypotheses of the entry layer**, for every `ω` and `0 ≤ t ≤ T₀`: the resolvent identities
`G (D + X - z_t) = 1 = (D + X - z_t) G`, `(D - s) M = 1 = M (D - s)` with `s = E + m`, `z_t = s - t m`; `M = M^{(B)} ⊗ I`
(`M_{uv} = 1_{o(u)=o(v)} M^{(B)}_{[u][v]}`); `D = g₀ Ψ` (`Ψ_{uv} = 1_{o(u)=o(v)} 1_{[u]∼[v]}`); `G_{uu} ≠ 0`. -/
theorem GreenCore_carrier {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) {z : ℕ → ℂ} (h : BAFlow sz κ ε 𝔠 𝔡 z)
    (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) (ω : sz.SeqΩ) {m s zt : ℂ}
    (hm : m = BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (hs : s = (BAflowEs sz z n : ℂ) + m)
    (hzt : zt = ztOf m (BAflowEs sz z n) t) :
    GreenCore_Gc sz z n t ω * (GreenCore_Dc sz z n + GreenCore_Xc sz n t ω - zt • 1) = 1 ∧
      (GreenCore_Dc sz z n + GreenCore_Xc sz n t ω - zt • 1) * GreenCore_Gc sz z n t ω = 1 ∧
      (GreenCore_Dc sz z n - s • 1) * GreenCore_Mc sz z n = 1 ∧ GreenCore_Mc sz z n * (GreenCore_Dc sz z n - s • 1) = 1 ∧
      zt = s - (t : ℂ) * m ∧
      (∀ u v, GreenCore_Mc sz z n u v =
        if u.2 = v.2 then BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) m u.1 v.1 else 0) ∧
      (∀ a, BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) m a a = m) ∧
      (∀ u l, GreenCore_Dc sz z n u l =
        if u.2 = l.2 ∧ Adj d (sz.L n) u.1 l.1 then ((BAflowLam0 sz z n : ℝ) : ℂ) else 0) ∧
      (∀ u, GreenCore_Gc sz z n t ω u u ≠ 0) := by
  obtain ⟨ht1, hr, hmi, hzi, -, -⟩ := ba_G_data hκ sz h n ht0 ht
  set e := splitEquiv d (sz.L n) (sz.W n) with he
  have hmm : 0 < m.im := by rw [hm]; exact hmi
  have hzim : 0 < zt.im := by rw [hzt, hm]; exact hzi
  have hsim : s.im ≠ 0 := by rw [hs]; simpa using hmm.ne'
  set H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ := sz.seqHflowBA (BAflowLam0 sz z) n t ω with hH
  have hHerm : H.IsHermitian := by
    rw [hH]; unfold Sizes.seqHflowBA
    refine IsHermitian.add ?_ (Sizes.seqHflow_isHermitian (sz.withLam 0) n t ω)
    unfold IsHermitian
    rw [conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
      show star (BAflowLam0 sz z n : ℂ) = (BAflowLam0 sz z n : ℂ) from Complex.conj_ofReal _]
  have hH0 : (((BAflowLam0 sz z n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
      show star (BAflowLam0 sz z n : ℂ) = (BAflowLam0 sz z n : ℂ) from Complex.conj_ofReal _]
  have hUH : IsUnit (H - zt • 1) := RBM.isUnit_sub_smul_of_isHermitian hHerm hzim.ne'
  have hU0 : IsUnit (((BAflowLam0 sz z n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) - s • 1) :=
    RBM.isUnit_sub_smul_of_isHermitian hH0 hsim
  have hGd : BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n t ω = Ring.inverse (H - zt • 1) := by
    rw [hzt, hm]; simp [BAGt, Gres, hH]
  have hMd : BAMfine sz (BAflowLam0 sz z) (BAflowEs sz z) n = Ring.inverse
      (((BAflowLam0 sz z n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) - s • 1) := by
    rw [hs, hm]; rfl
  have bm : ∀ A B : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      blockMat d (sz.L n) (sz.W n) (A * B) = blockMat d (sz.L n) (sz.W n) A * blockMat d (sz.L n) (sz.W n) B :=
    fun A B => (Matrix.submatrix_mul_equiv A B e.symm e.symm e.symm).symm
  have bm1 : blockMat d (sz.L n) (sz.W n) (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) = 1 :=
    Matrix.submatrix_one_equiv e.symm
  have bD : ∀ c : ℂ, blockMat d (sz.L n) (sz.W n) (c • PsiI d (sz.L n) (sz.W n)) = c • PsiV d (sz.L n) (sz.W n) := by
    intro c; ext u v; simp [blockMat, PsiI]
  have b1 : blockMat d (sz.L n) (sz.W n) (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) = 1 := bm1
  have bH : blockMat d (sz.L n) (sz.W n) (H - zt • 1) =
      GreenCore_Dc sz z n + GreenCore_Xc sz n t ω - zt • 1 := by
    rw [hH]; ext u v
    simp [blockMat, Sizes.seqHflowBA, PsiI, GreenCore_Dc, GreenCore_Xc, BAX, Matrix.one_apply]
  have bM : blockMat d (sz.L n) (sz.W n) (((BAflowLam0 sz z n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) - s • 1) =
      GreenCore_Dc sz z n - s • 1 := by
    ext u v; simp [blockMat, PsiI, GreenCore_Dc, Matrix.one_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← bH, GreenCore_Gc, hGd, ← bm, Ring.inverse_mul_cancel _ hUH, bm1]
  · rw [← bH, GreenCore_Gc, hGd, ← bm, Ring.mul_inverse_cancel _ hUH, bm1]
  · rw [← bM, GreenCore_Mc, hMd, ← bm, Ring.mul_inverse_cancel _ hU0, bm1]
  · rw [← bM, GreenCore_Mc, hMd, ← bm, Ring.inverse_mul_cancel _ hU0, bm1]
  · rw [hzt, hs, ztOf]; ring
  · intro u v
    have hk := BAMres_fine_kron d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) m (by simpa using hmm.ne')
    have hMf : GreenCore_Mc sz z n = BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) m ⊗ₖ
        (1 : Matrix (Fin (sz.W n ^ d)) (Fin (sz.W n ^ d)) ℂ) := by
      have : BAMfine sz (BAflowLam0 sz z) (BAflowEs sz z) n = Mres (((BAflowLam0 sz z n : ℝ) : ℂ) •
          PsiI d (sz.L n) (sz.W n)) (BAflowEs sz z n : ℂ) m := by rw [hm]; rfl
      rw [GreenCore_Mc, this, hk]; ext a b; simp [blockMat]
    rw [hMf]; simp only [Matrix.kroneckerMap_apply, Matrix.one_apply]; split_ifs <;> simp
  · intro a
    have := BAMB_diag_eq d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) m (by rw [hm]; exact hr.1) a
    exact this
  · intro u l
    simp only [GreenCore_Dc, PsiV, PsiB, Matrix.smul_apply, Matrix.kroneckerMap_apply, Matrix.of_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp_all
  · intro u
    simp only [GreenCore_Gc, blockMat, Matrix.submatrix_apply]
    rw [BAGt_eq_green, ← hm, ← hzt]
    exact green_diag_ne_zero hHerm hzim.ne' _

end Carrier

section Pins

/-- The loop premise `(eq:def_Psit)` (`7_8:1924`), event form: `1_Ω 𝓛^{(2)}_{t,(-,+),(a,b)} ≺ Φ_t(a,b)²` uniformly in `(a,b)`,
`Ω = {‖G_t - M‖_max ≤ W^{-ε₀}}`, over the BA carrier `baFMz sz z` and the law `seqP (sz.withLam 0)`. -/
def GreenCore_loopPrem {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t : ℕ → ℝ) (ε₀ : ℝ)
    (Φ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → ℝ) : Prop :=
  PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
    (fun n p ω => (baFMz sz z).indMax n (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω *
      ‖(baFMz sz z).L n (t n) ![false, true] ![p.1, p.2] ω‖)
    (fun n p _ => Φ n p.1 p.2 ^ 2)

/-- The right side of `(GijGEX_BA)` (`7_8:1942-1944`): `Σ_{a',b'} Φ(a',b') e^{-c(|a'-a| + |b'-b|)} + Ψ e^{-c|a-b|} + W^{-D}`
(`|·|` the periodic `L^∞` norm `zdistInf`, `1_2:274`). -/
def GreenCore_decayRHS (d L W : ℕ) [NeZero L] (c D : ℝ) (Φ : Zd d L → Zd d L → ℝ) (Ψ : ℝ) (a b : Zd d L) : ℝ :=
  (∑ a' : Zd d L, ∑ b' : Zd d L, Φ a' b' *
      Real.exp (-c * ((zdistInf d L (a' - a) : ℝ) + (zdistInf d L (b' - b) : ℝ)))) +
    Ψ * Real.exp (-c * (zdistInf d L (a - b) : ℝ)) + (W : ℝ) ^ (-D)

/-- The conclusion of `(GijGEX_BA)`, event form: `1_Ω |(G_t - M)_{xy}| ≺ decayRHS ([x], [y])`, uniformly in `x ≠ y`. -/
def GreenCore_decayConcl {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t : ℕ → ℝ) (ε₀ D c : ℝ)
    (Φ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → ℝ) (Ψ : ℕ → ℝ) : Prop :=
  PrecL sz (Sizes.seqP (sz.withLam 0))
    (U := fun n => {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2})
    (fun n p ω => (baFMz sz z).indMax n (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω *
      ‖(baFMz sz z).GM n (t n) ω p.1.1 p.1.2‖)
    (fun n p _ => GreenCore_decayRHS d (sz.L n) (sz.W n) c D (Φ n) (Ψ n) (Sizes.STblk sz n p.1.1) (Sizes.STblk sz n p.1.2))

/-- **`lem_GbEXP_BA` (b), `(GijGEX_BA)`, in the paper's shape, event form** (`7_8:1916-1946`; supervisor `2026-10-10-1155` C3;
paper-deltas T2390a, e, f): `c = c_λ` after `(κ, ε, 𝔡)` and before the sizes; for deterministic `0 < Φ_t(a,b) ≤ W^{-ε₀}` and
`W^{-d/2} ≤ Ψ_t ≤ W^{-ε₀}`: `1_Ω 𝓛^{(2)} ≺ Φ_t²` implies `1_Ω |(G_t - M)_{xy}| ≺ Σ Φ_t e^{-c(…)} + Ψ_t e^{-c|a-b|} + W^{-D}`
for all `x ≠ y`.  Registry class: owed (the deterministic core is G4, consumed by G6a / G6b; its local inputs are
`GreenCore_Rbound`, `GreenCore_Xrow_sq`, `GreenCore_Acol_sq`). -/
def BAGbEXPij' (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∃ c : ℝ, 0 < c ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
        ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
          ∀ ε₀ : ℝ, 0 < ε₀ → ∀ D : ℝ, 0 < D →
            ∀ (Φ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → ℝ) (Ψ : ℕ → ℝ),
              (∀ᶠ n in atTop, ∀ a b, 0 < Φ n a b ∧ Φ n a b ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
              (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
              (∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
              GreenCore_loopPrem sz z t ε₀ Φ → GreenCore_decayConcl sz z t ε₀ D c Φ Ψ

/-- A nonempty instance of `BAGbEXPij'` at `d = 3`, `sz0` (`L = 4`, `W = 32`, `N = 2097152`, `λ = 1/64` at `n = 0`), the flow
`flow_sz0` (`κ = 1/2`, `ε = 1/10`, `𝔠 = 1/6`, `𝔡 = 1/10`), `t ≡ 1/2 ≤ T₀`, `ε₀ = 1/10`, `Φ ≡ W^{-1/10}`, `Ψ = W^{-1}`: every
deterministic hypothesis is discharged; the pin and the premise `GreenCore_loopPrem` stay hypotheses. -/
example (h : BAGbEXPij' 3) :
    ∃ c : ℝ, 0 < c ∧ ∀ D : ℝ, 0 < D →
      GreenCore_loopPrem SizesInst.sz0 FlowPinsInst.zSeq (fun _ => 1 / 2) (1 / 10)
        (fun n _ _ => ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (-(1 / 10 : ℝ))) →
      GreenCore_decayConcl SizesInst.sz0 FlowPinsInst.zSeq (fun _ => 1 / 2) (1 / 10) D c
        (fun n _ _ => ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (-(1 / 10 : ℝ)))
        (fun n => ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (-1 : ℝ)) := by
  have h1 : ∀ n, (1 : ℝ) ≤ ((SizesInst.sz0.W n : ℕ) : ℝ) := fun n => by exact_mod_cast SizesInst.sz0.W_pos n
  obtain ⟨c, hc, hmain⟩ := h (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨c, hc, fun D hD hL => hmain (1 / 6) SizesInst.sz0 FlowPinsInst.zSeq FlowPinsInst.flow_sz0 (fun _ => 1 / 2)
    (fun _ => by norm_num) (fun n => (FlowPinsInst.half_lt_t0 n).le) (1 / 10) (by norm_num) D hD _
    (fun n => ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (-1 : ℝ)) ?_ ?_ ?_ hL⟩
  · exact Eventually.of_forall fun n a b => ⟨Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (h1 n)) _, le_rfl⟩
  · exact Eventually.of_forall fun n => Real.rpow_le_rpow_of_exponent_le (h1 n) (by norm_num)
  · exact Eventually.of_forall fun n => Real.rpow_le_rpow_of_exponent_le (h1 n) (by norm_num)

end Pins

/-! ## Nonempty instances of the targets (`d = 3`, `sz0` at `n = 3`: `L = 16`, `W = 32768`; the flow `flow_sz0`, `κ = 1/2`)

(i) R1 (identities) holds for every sample `ω` at `t = 1/2`: the carrier theorem `GreenCore_carrier` discharges the resolvent
identities from `BAFlow`.  (ii) R2-R4 (inequalities): the zero sample `ω₀` (`X = 0`) at `t₁ = 10⁻¹¹ > 0`, so `Δ = G - M ≠ 0`
(`iΔ`), with `Φ = 1`, `δ = 2·10⁻⁷ ≥ ‖Δ‖_max`, `W^{-d} ≤ δ²`, `ρ = S = 4096 = L^d`, `ρ₂ = 1`, `K_Θ = 256`, `K_BA δ ≈ 0.21 ≤ 1/2`,
`(C1) ≈ 0.24 ≤ 1`; every hypothesis is discharged, including the stability `BAStab` (Neumann series at `t₁ ≤ 1/2`). -/

namespace GreenCoreInst
open RBM.Gauss.Sizes SizesInst FlowPinsInst

private abbrev g₀ : ℝ := BAflowLam0 sz0 zSeq 3
private abbrev E₀ : ℝ := BAflowEs sz0 zSeq 3
private abbrev m₀ : ℂ := BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 3
private abbrev Mb₀ : Matrix (Zd 3 (sz0.L 3)) (Zd 3 (sz0.L 3)) ℂ := BAMB 3 (sz0.L 3) g₀ (E₀ : ℂ) m₀
private abbrev t₁ : ℝ := 1 / 10 ^ 11
private abbrev ω₀ : sz0.SeqΩ := fun _ => 0
private abbrev G₁ := GreenCore_Gc sz0 zSeq 3 t₁ ω₀
private abbrev X₁ := GreenCore_Xc sz0 3 t₁ ω₀
private abbrev M₁ := GreenCore_Mc sz0 zSeq 3
private abbrev D₁ := GreenCore_Dc sz0 zSeq 3
private abbrev s₀ : ℂ := (E₀ : ℂ) + m₀
private theorem hreal : BAReal 3 (sz0.L 3) g₀ (1 / 2) E₀ m₀ := BAflow_real (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq flow_sz0 3
private theorem hT0 : 1 / 2 < BAflowT0 sz0 zSeq 3 ∧ BAflowT0 sz0 zSeq 3 < 1 := ⟨half_lt_t0 3, Step1FamInst.sz0_T0_lt_one 3⟩
private theorem hg : 0 < g₀ ∧ g₀ ≤ 1 / 64 := by
  have h1 : sz0.lam 3 ≤ 1 / 64 := by norm_num [sz0]
  have h2 := Real.sqrt_le_one.2 hT0.2.le
  have h3 := sz0_lam_pos 3
  rw [show g₀ = Real.sqrt (BAflowT0 sz0 zSeq 3) * sz0.lam 3 from rfl]
  exact ⟨mul_pos (Real.sqrt_pos.2 (by linarith [hT0.1])) h3, by nlinarith [Real.sqrt_nonneg (BAflowT0 sz0 zSeq 3)]⟩
-- the kernel facts of `M^{(B)}`: `|m| ∈ [1/2, 1]`, entries `≤ 1` (Ward), the decay at the rate `c₀`, and `Σ_b |M_{ab}||M_{bc}| ≤ 1`
private theorem kern : 1 / 2 ≤ ‖m₀‖ ∧ ‖m₀‖ ≤ 1 ∧ (∀ a b, ‖Mb₀ a b‖ ≤ 1) ∧
    (∀ a b, ‖Mb₀ a b‖ ≤ (BAct_rate 3 10 (1 / 2))⁻¹ * Real.exp (-BAct_rate 3 10 (1 / 2) * (zdistD 3 (sz0.L 3) (a - b) : ℝ))) ∧
    (∀ a c, ∑ b, ‖Mb₀ a b‖ * ‖Mb₀ b c‖ ≤ 1) := by
  have hr := hreal
  refine ⟨(hr.2).trans ((le_abs_self _).trans (Complex.abs_im_le_norm _)), BAm_norm_le_one 3 (sz0.L 3) g₀ (E₀ : ℂ) m₀ (by simp) hr.1, ?_, ?_, ?_⟩
  · intro a b
    have h1 := BAMB_row_sq_real 3 (sz0.L 3) g₀ E₀ m₀ hr.1 a
    have h2 : ‖Mb₀ a b‖ ^ 2 ≤ 1 := h1 ▸ Finset.single_le_sum (f := fun b => ‖Mb₀ a b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ b)
    nlinarith [norm_nonneg (Mb₀ a b)]
  · intro a b
    have := BAMB_decay_large 3 (sz0.L 3) (sz0.three_le_L 3) (by norm_num) 10 g₀ (1 / 2) E₀ m₀ (by norm_num) hg.1
      (by linarith [hg.2]) (by norm_num) hr a b
    simpa [neg_mul] using this
  · intro a c
    have h1 := BAMB_row_sq_real 3 (sz0.L 3) g₀ E₀ m₀ hr.1 a
    have h3 : ∑ b, ‖Mb₀ b c‖ ^ 2 = 1 := by
      rw [← BAMB_row_sq_real 3 (sz0.L 3) g₀ E₀ m₀ hr.1 c]; exact Finset.sum_congr rfl fun b _ => by rw [BAMB_symm]
    have h4 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun b => ‖Mb₀ a b‖) (fun b => ‖Mb₀ b c‖)
    rw [h1, h3] at h4
    nlinarith [Finset.sum_nonneg (fun b (_ : b ∈ (Finset.univ : Finset (Zd 3 (sz0.L 3)))) => mul_nonneg (norm_nonneg (Mb₀ a b)) (norm_nonneg (Mb₀ b c)))]
-- the zero sample: `X = 0`
private theorem X0 : X₁ = 0 := by
  have h2 : (sz0.withLam 0).seqHflow 3 t₁ (fun _ => 0) = 0 := by
    rw [Sizes.seqHflow_eq_smul, show (sz0.withLam 0).seqXmat 3 (fun _ => 0) = 0 by ext i j; simp [Sizes.seqXmat, Xmat, Xentry, Sizes.slice], smul_zero]
  ext u v
  simp only [blockMat, BAX, Matrix.of_apply, Matrix.submatrix_apply, Matrix.zero_apply]
  exact congrFun (congrFun h2 _) _
private theorem card4096 : Fintype.card (Zd 3 (sz0.L 3)) = 4096 := by rw [card_Zd]; norm_num [sz0]
private theorem cnt (f : Zd 3 (sz0.L 3) → ℝ) (h : ∀ b, f b ≤ 1) : ∑ b, f b ≤ 4096 :=
  (Finset.sum_le_sum fun b _ => h b).trans (by rw [Finset.sum_const, Finset.card_univ, card4096]; simp)
private theorem c0_lb : 1 / 241 ≤ BAct_rate 3 10 (1 / 2) := by
  unfold BAct_rate
  refine le_min ?_ (by norm_num)
  have := Real.one_sub_inv_le_log_of_pos (x := 241 / 240) (by norm_num)
  rw [show (1 : ℝ) + (1 / 2) / (4 * ((3 : ℕ) : ℝ) * 10) = 241 / 240 by norm_num]
  linarith [this, show (1 : ℝ) - (241 / 240)⁻¹ = 1 / 241 by norm_num]
private theorem Gbd (u v : Vtx 3 (sz0.L 3) (sz0.W 3)) : ‖G₁ u v‖ ≤ 3 := by
  have hr := hreal
  have hpos : 0 < (1 - t₁) * m₀.im := mul_pos (by norm_num) (by linarith [hr.2])
  have hzi : 0 < (ztOf m₀ E₀ t₁).im := by rw [ztOf_im]; exact hpos
  have hH : ((g₀ : ℂ) • PsiI 3 (sz0.L 3) (sz0.W 3)).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_smul, (PsiI_isHermitian 3 _ _).eq, show star (g₀ : ℂ) = (g₀ : ℂ) from Complex.conj_ofReal _]
  simp only [blockMat, Matrix.submatrix_apply]
  rw [BAGt_eq_green]
  refine (Green.LDE_norm_green_apply_leD (sz := sz0.withLam 0) (n := 3) _ hH hzi.ne' _ _ _ _).trans ?_
  rw [abs_of_pos hzi, ztOf_im]; unfold etaOf
  rw [inv_le_comm₀ hpos (by norm_num)]; nlinarith [hr.2]
-- the carrier at `(t, ω)`: the resolvent identities, `M = M^{(B)} ⊗ I`, `D = g₀ Ψ`, `G_{uu} ≠ 0`
private abbrev iC {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz0 zSeq 3) (ω : sz0.SeqΩ) :=
  GreenCore_carrier (by norm_num : (0 : ℝ) < 1 / 2) sz0 flow_sz0 3 ht0 ht ω (m := m₀) (s := s₀) (zt := ztOf m₀ E₀ t) rfl rfl rfl
private abbrev iCh (ω : sz0.SeqΩ) := iC (t := 1 / 2) (by norm_num) (half_lt_t0 3).le ω
private abbrev iC1 := iC (t := t₁) (by norm_num) (by change (1 / 10 ^ 11 : ℝ) ≤ _; linarith [hT0.1]) ω₀
-- the three large deviation bounds and the diagonal bound hold at `X = 0` when `t² #n ≤ Φ`
private theorem lde_zero {n : Type*} [Fintype n] [DecidableEq n] (G : Matrix n n ℂ) (S : n → n → ℝ)
    (hS : ∀ i k, 0 ≤ S i k) (hsymm : ∀ i k, S i k = S k i) {Φ t : ℝ} (hΦ : 0 ≤ Φ) (ht : t ^ 2 * Fintype.card n ≤ Φ) :
    LDERow (0 : Matrix n n ℂ) G S Φ ∧ LDECol (0 : Matrix n n ℂ) G S Φ ∧ LDEQuad (0 : Matrix n n ℂ) G S t Φ ∧
      ∀ i, ‖(0 : Matrix n n ℂ) i i‖ ^ 2 ≤ Φ * S i i := by
  refine ⟨fun i j _ => ?_, fun k j _ => ?_, fun i => ?_, fun i => by simpa using mul_nonneg hΦ (hS i i)⟩
  · exact le_trans (by simp [ldeRowLHS]) (mul_nonneg hΦ (Finset.sum_nonneg fun k _ => mul_nonneg (hS _ _) (sq_nonneg _)))
  · exact le_trans (by simp [ldeColLHS]) (mul_nonneg hΦ (Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (hS _ _)))
  · unfold ldeQuadLHS ldeQuadRHS
    simp only [Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, zero_sub, norm_neg]
    set a : n → ℝ := fun k => S i k * ‖greenMinor G i k k‖ with ha
    have h1 : ‖(t : ℂ) * ∑ k ∈ Finset.univ.erase i, (S i k : ℂ) * greenMinor G i k k‖ ≤ |t| * ∑ k ∈ Finset.univ.erase i, a k := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)) (abs_nonneg t)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hS i k)]
    have h2 : (∑ k ∈ Finset.univ.erase i, a k) ^ 2 ≤ (Fintype.card n : ℝ) * ∑ k ∈ Finset.univ.erase i, a k ^ 2 :=
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ.erase i) (f := a)).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ _) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    have h3 : ∑ k ∈ Finset.univ.erase i, a k ^ 2 ≤ ∑ k ∈ Finset.univ.erase i, ∑ l ∈ Finset.univ.erase i,
        S i k * ‖greenMinor G i k l‖ ^ 2 * S l i :=
      Finset.sum_le_sum fun k hk => by
        have := Finset.single_le_sum (f := fun l => S i k * ‖greenMinor G i k l‖ ^ 2 * S l i)
          (fun l _ => mul_nonneg (mul_nonneg (hS _ _) (sq_nonneg _)) (hS _ _)) hk
        refine le_trans (le_of_eq ?_) this
        simp only [ha, hsymm k i]; ring
    calc ‖(t : ℂ) * ∑ k ∈ Finset.univ.erase i, (S i k : ℂ) * greenMinor G i k k‖ ^ 2
        ≤ (|t| * ∑ k ∈ Finset.univ.erase i, a k) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = t ^ 2 * (∑ k ∈ Finset.univ.erase i, a k) ^ 2 := by rw [mul_pow, sq_abs]
      _ ≤ t ^ 2 * ((Fintype.card n : ℝ) * ∑ k ∈ Finset.univ.erase i, a k ^ 2) := mul_le_mul_of_nonneg_left h2 (sq_nonneg t)
      _ = (t ^ 2 * Fintype.card n) * ∑ k ∈ Finset.univ.erase i, a k ^ 2 := by ring
      _ ≤ Φ * ∑ k ∈ Finset.univ.erase i, a k ^ 2 := mul_le_mul_of_nonneg_right ht (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 hΦ
-- at `X = 0`: `G - M = -t m G M`, so `‖G - M‖_max ≤ t ‖G‖_max · #blocks`
private theorem om_gen {d L W : ℕ} [NeZero L] [NeZero W] {G X M D : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    {Mb : Matrix (Zd d L) (Zd d L) ℂ} {m s z : ℂ} {t B : ℝ}
    (hGR : G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1)
    (hMR : (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * M = 1) (hz : z = s - (t : ℂ) * m)
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hX : X = 0) (ht0 : 0 ≤ t) (hm1 : ‖m‖ ≤ 1)
    (hMb1 : ∀ a b, ‖Mb a b‖ ≤ 1) (hG : ∀ u v, ‖G u v‖ ≤ B) (u v : Vtx d L W) :
    ‖G u v - M u v‖ ≤ t * B * Fintype.card (Zd d L) := by
  have h3 := congrFun (congrFun (GreenCore_E0 (X := X) hGR hMR hz) u) v
  rw [Matrix.sub_apply, Matrix.neg_apply, Matrix.mul_apply,
    GreenCore_sum_kron hM (fun k => (G * (X + ((t : ℂ) * m) • 1)) u k) v] at h3
  have h4 : ∀ k, (G * (X + ((t : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))) u k = t * m * G u k := fun k => by
    rw [hX, zero_add, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul]
  have ht : ‖((t : ℝ) : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  have hB : 0 ≤ B := (norm_nonneg _).trans (hG u v)
  rw [h3, norm_neg]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (g := fun _ => t * 1 * B * 1) fun b' _ => ?_).trans ?_)
  · rw [h4, norm_mul, norm_mul, norm_mul, ht]
    have := hG u (b', v.2)
    have := hMb1 b' v.1
    gcongr
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; exact le_of_eq (by ring)
private theorem Om (u v : Vtx 3 (sz0.L 3) (sz0.W 3)) : ‖G₁ u v - M₁ u v‖ ≤ 2 / 10 ^ 7 := by
  obtain ⟨hGR, hRG, hMR, hMR', hz, hM, hMd, hD, hG0⟩ := iC1
  refine (om_gen hGR hMR hz hM X0 (by norm_num) kern.2.1 kern.2.2.1 Gbd u v).trans ?_
  rw [card4096]; norm_num
private theorem hW : sz0.W 3 = 32768 := by norm_num [sz0]
private theorem iwd : (((sz0.W 3 : ℕ) : ℝ) ^ 3)⁻¹ ≤ (2 / 10 ^ 7) ^ 2 := by rw [hW]; norm_num
private theorem iLDE : LDERow X₁ G₁ (svar 3 (sz0.L 3) (sz0.W 3) 0) 1 ∧ LDECol X₁ G₁ (svar 3 (sz0.L 3) (sz0.W 3) 0) 1 ∧
    LDEQuad X₁ G₁ (svar 3 (sz0.L 3) (sz0.W 3) 0) t₁ 1 ∧ ∀ i, ‖X₁ i i‖ ^ 2 ≤ 1 * svar 3 (sz0.L 3) (sz0.W 3) 0 i i := by
  rw [X0]
  refine lde_zero G₁ _ (fun i k => ?_) (fun i k => ?_) zero_le_one ?_
  · rw [GreenCore_svar0]; split_ifs <;> positivity
  · rw [GreenCore_svar0, GreenCore_svar0]; simp only [eq_comm]
  · rw [Fintype.card_prod, card4096, Fintype.card_fin, hW]; norm_num
-- `GreenCore_crude` at the zero sample
private theorem icr : (∀ u, (1 / 2 : ℝ) / 2 ≤ ‖G₁ u u‖) ∧ (∀ u v, ‖G₁ u v‖ ≤ 3 / 2) ∧
    (∀ u v : Vtx 3 (sz0.L 3) (sz0.W 3), u.2 ≠ v.2 → ‖G₁ u v‖ ≤ 2 / 10 ^ 7) := by
  obtain ⟨hGR, hRG, hMR, hMR', hz, hM, hMd, hD, hG0⟩ := iC1
  exact GreenCore_crude hM hMd kern.2.2.1 kern.1 kern.2.1 (by norm_num) Om
-- `𝓛^{(2)}_{(a,b)} ≤ B²` when `|G_{xy}| ≤ B`
private theorem loop_le {d L W : ℕ} [NeZero L] [NeZero W] {G : Matrix (Vtx d L W) (Vtx d L W) ℂ} {B : ℝ}
    (hG : ∀ u v, ‖G u v‖ ≤ B) (a b : Zd d L) : GreenCore_loop G a b ≤ B ^ 2 := by
  unfold GreenCore_loop
  rw [sq, mul_assoc, Finset.mul_sum]
  exact GreenCore_avg_le fun o => GreenCore_avg_le fun o' => pow_le_pow_left₀ (norm_nonneg _) (hG _ _) 2
-- the stability of `1 - t P` for `t ≤ 1/2` and `ℓ¹` rows of `P` at most `1` (Neumann series): `‖v‖_∞ ≤ 2 B`
private theorem stab_small {ι : Type*} [Fintype ι] [Nonempty ι] (P : ι → ι → ℂ) {t K : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ 1 / 2) (hP : ∀ a, ∑ b, ‖P a b‖ ≤ 1) (hK : 2 ≤ K) :
    ∀ (v : ι → ℂ) (B : ℝ), (∀ a, ‖v a - (t : ℂ) * ∑ b, P a b * v b‖ ≤ B) → ∀ a, ‖v a‖ ≤ K * B := by
  intro v B hB a
  obtain ⟨a₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun a => ‖v a‖) Finset.univ_nonempty
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB a₀)
  have h1 : ‖(t : ℂ) * ∑ b, P a₀ b * v b‖ ≤ t * ‖v a₀‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) ht0
    calc ∑ b, ‖P a₀ b * v b‖ ≤ ∑ b, ‖P a₀ b‖ * ‖v a₀‖ := Finset.sum_le_sum fun b _ => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hmax b (Finset.mem_univ b)) (norm_nonneg _)
      _ = (∑ b, ‖P a₀ b‖) * ‖v a₀‖ := by rw [Finset.sum_mul]
      _ ≤ 1 * ‖v a₀‖ := mul_le_mul_of_nonneg_right (hP a₀) (norm_nonneg _)
      _ = ‖v a₀‖ := one_mul _
  have h2 := norm_sub_norm_le (v a₀) ((t : ℂ) * ∑ b, P a₀ b * v b)
  have h3 : ‖v a₀‖ ≤ 2 * B := by nlinarith [hB a₀, mul_nonneg (sub_nonneg.2 ht) (norm_nonneg (v a₀))]
  exact (hmax a (Finset.mem_univ a)).trans (h3.trans (mul_le_mul_of_nonneg_right hK hB0))
private theorem istab : ∀ (v : Zd 3 (sz0.L 3) → ℂ) (B : ℝ),
    (∀ a, ‖v a - (t₁ : ℂ) * ∑ b, (Mb₀ b a * Mb₀ a b) * v b‖ ≤ B) → ∀ a, ‖v a‖ ≤ 256 * B :=
  stab_small (fun a b => Mb₀ b a * Mb₀ a b) (by norm_num) (by norm_num)
    (fun a => by simpa [norm_mul, mul_comm] using kern.2.2.2.2 a a) (by norm_num)
-- the stability `BAStab` at the data `(g₀, E₀, m₀)`, `t₁`, `K_Θ = 256`
private theorem istabBA : BAStab 3 (sz0.L 3) g₀ E₀ m₀ t₁ 256 := fun v B hv a =>
  istab v B (fun a' => by simpa [BAMss, BAMsigma] using hv a') a
private theorem iC1n : 8 * 4096 * ((BAct_rate 3 10 (1 / 2))⁻¹ * 4096) * GreenCore_theta 3 (1 / 2) 1 (2 / 10 ^ 7) g₀ ≤ 1 := by
  have hc : (BAct_rate 3 10 (1 / 2))⁻¹ ≤ 241 := by
    rw [inv_le_comm₀ (by linarith [c0_lb]) (by norm_num)]; linarith [c0_lb]
  have h0 := hg.1
  have h1 := hg.2
  have hθ : GreenCore_theta 3 (1 / 2) 1 (2 / 10 ^ 7) g₀ ≤ GreenCore_theta 3 (1 / 2) 1 (2 / 10 ^ 7) (1 / 64) := by
    unfold GreenCore_theta; gcongr
  calc 8 * 4096 * ((BAct_rate 3 10 (1 / 2))⁻¹ * 4096) * GreenCore_theta 3 (1 / 2) 1 (2 / 10 ^ 7) g₀
      ≤ 8 * 4096 * (241 * 4096) * GreenCore_theta 3 (1 / 2) 1 (2 / 10 ^ 7) (1 / 64) := by
        have : 0 ≤ GreenCore_theta 3 (1 / 2) 1 (2 / 10 ^ 7) g₀ := by unfold GreenCore_theta; positivity
        gcongr
    _ ≤ 1 := by norm_num [GreenCore_theta]
private theorem c0pos : 0 < BAct_rate 3 10 (1 / 2) := lt_of_lt_of_le (by norm_num) c0_lb
private theorem iρ : ∀ c, ∑ b, ‖Mb₀ b c‖ ≤ 4096 := fun c => cnt _ fun b => kern.2.2.1 b c
private theorem iS : ∀ a, ∑ b, Real.exp (-(BAct_rate 3 10 (1 / 2) / 2) * (zdistD 3 (sz0.L 3) (a - b) : ℝ)) ≤ 4096 :=
  fun a => cnt _ fun b => Real.exp_le_one_iff.2 (by
    have := Nat.cast_nonneg (α := ℝ) (zdistD 3 (sz0.L 3) (a - b)); have := c0pos; nlinarith)
-- the residual `𝒦` at the zero sample: `K = t v̄ Δ - (t m + t v̄) G` (`A = t m`, `𝔛 = 0`), so `‖K‖ ≤ t δ² + (t + t δ) B`
private theorem K_gen {d L W : ℕ} [NeZero L] [NeZero W] {G X M D : Matrix (Vtx d L W) (Vtx d L W) ℂ} {m : ℂ} {t B δ' : ℝ}
    (hX : X = 0) (ht0 : 0 ≤ t) (hm1 : ‖m‖ ≤ 1) (hG : ∀ u v, ‖G u v‖ ≤ B) (hΩ : ∀ u v, ‖G u v - M u v‖ ≤ δ')
    (u y : Vtx d L W) : ‖GreenCore_K G M X D t m u y‖ ≤ t * δ' * δ' + (t + t * δ') * B := by
  have hw := GreenCore_w_pos (d := d) (W := W)
  have hδ : 0 ≤ δ' := (norm_nonneg _).trans (hΩ u y)
  have hvb : ‖GreenCore_vbar G M u.1‖ ≤ δ' := by
    unfold GreenCore_vbar
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw.le]
    exact (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hw.le).trans (GreenCore_avg_le fun o => hΩ _ _)
  have ht : ‖((t : ℝ) : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  unfold GreenCore_K
  rw [show GreenCore_Arow G X D t m u = (t : ℂ) * m by simp [GreenCore_Arow, hX],
    show GreenCore_Xrow G X u y = 0 by simp [GreenCore_Xrow, hX], sub_zero]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, norm_mul, ht]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hvb ht0) (hΩ u y) (norm_nonneg _) (mul_nonneg ht0 hδ)
  · rw [norm_mul]
    refine mul_le_mul ((norm_add_le _ _).trans (add_le_add ?_ ?_)) (hG u y) (norm_nonneg _) (by positivity)
    · rw [norm_mul, ht]; exact mul_le_of_le_one_right ht0 hm1
    · rw [norm_mul, ht]; exact mul_le_mul_of_nonneg_left hvb ht0
-- the zero sample is not degenerate: `G ≠ M` (else `(t m) M = 0`, `M = 0`, `1 = M (D - s) = 0`)
private theorem iΔ : ∃ x y, G₁ x y - M₁ x y ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  obtain ⟨hGR, -, -, hMR', hz, -, -, -, -⟩ := iC1
  have hGM : G₁ = M₁ := by ext x y; exact sub_eq_zero.1 (h x y)
  have hm : (t₁ : ℂ) * m₀ ≠ 0 := mul_ne_zero (by norm_num) (fun h0 => by have := kern.1; rw [h0, norm_zero] at this; linarith)
  have e1 : M₁ * (D₁ + 0 - (s₀ - (t₁ : ℂ) * m₀) • 1) = 1 := by rw [← hGM, ← X0, ← hz]; exact hGR
  have h1 := sub_eq_zero.2 (e1.trans hMR'.symm)
  rw [← mul_sub, show D₁ + 0 - (s₀ - (t₁ : ℂ) * m₀) • 1 - (D₁ - s₀ • 1) = ((t₁ : ℂ) * m₀) • 1 by module,
    Matrix.mul_smul, Matrix.mul_one, smul_eq_zero, or_iff_right hm] at h1
  simp [h1] at hMR'

-- R1: the identities (E1), (E1′), (E0), (E2), (E0)+(E1), (E0)+(E1′), (E3) at `t = 1/2`, for every sample `ω`
example (ω : sz0.SeqΩ) (u y : Vtx 3 (sz0.L 3) (sz0.W 3)) := by
  obtain ⟨hGR, hRG, hMR, hMR', hz, hM, hMd, hD, hG0⟩ := iCh ω; exact GreenCore_E1 (X := GreenCore_Xc sz0 3 (1 / 2) ω) hGR u y (hG0 u)
example (ω : sz0.SeqΩ) (v w : Vtx 3 (sz0.L 3) (sz0.W 3)) := by
  obtain ⟨hGR, hRG, hMR, hMR', hz, hM, hMd, hD, hG0⟩ := iCh ω; exact GreenCore_E1' (X := GreenCore_Xc sz0 3 (1 / 2) ω) hRG v w (hG0 w)
example (ω : sz0.SeqΩ) := by
  obtain ⟨hGR, hRG, hMR, hMR', hz, hM, hMd, hD, hG0⟩ := iCh ω; exact GreenCore_E0 (X := GreenCore_Xc sz0 3 (1 / 2) ω) hGR hMR hz
example (ω : sz0.SeqΩ) (w : Vtx 3 (sz0.L 3) (sz0.W 3)) := by
  obtain ⟨hGR, hRG, hMR, hMR', hz, hM, hMd, hD, hG0⟩ := iCh ω; exact GreenCore_E2 (X := GreenCore_Xc sz0 3 (1 / 2) ω) (t := 1 / 2) hM hMd (hG0 w)
example (ω : sz0.SeqΩ) (x y : Vtx 3 (sz0.L 3) (sz0.W 3)) := by
  obtain ⟨hGR, hRG, hMR, hMR', hz, hM, hMd, hD, hG0⟩ := iCh ω; exact GreenCore_Delta_col (X := GreenCore_Xc sz0 3 (1 / 2) ω) hGR hRG hMR hz hM hG0 x y
example (ω : sz0.SeqΩ) (x y : Vtx 3 (sz0.L 3) (sz0.W 3)) := by
  obtain ⟨hGR, hRG, hMR, hMR', hz, hM, hMd, hD, hG0⟩ := iCh ω; exact GreenCore_Delta_row (X := GreenCore_Xc sz0 3 (1 / 2) ω) hGR hRG hMR' hz hM hG0 x y
example (ω : sz0.SeqΩ) (x y : Vtx 3 (sz0.L 3) (sz0.W 3)) := by
  obtain ⟨hGR, hRG, hMR, hMR', hz, hM, hMd, hD, hG0⟩ := iCh ω; exact GreenCore_E3 (X := GreenCore_Xc sz0 3 (1 / 2) ω) hGR hRG hMR' hz hM hG0 x y
-- R2: the local large deviation bounds at the zero sample (`κ = 1/2`, `Φ = 1`, `δ = 2·10⁻⁷`)
example (u y : Vtx 3 (sz0.L 3) (sz0.W 3)) := GreenCore_Xrow_sq (by norm_num) zero_le_one icr.1 iLDE.1 u y
example (x w : Vtx 3 (sz0.L 3) (sz0.W 3)) := GreenCore_Xcol_sq (by norm_num) zero_le_one icr.1 iLDE.2.1 x w
example (w : Vtx 3 (sz0.L 3) (sz0.W 3)) := GreenCore_eps1_loc (by norm_num) zero_le_one icr.1 iLDE.2.2.1 w
example (w v y : Vtx 3 (sz0.L 3) (sz0.W 3)) := GreenCore_m1 (G := G₁) (by norm_num) (icr.1 w) v y
example (u : Vtx 3 (sz0.L 3) (sz0.W 3)) := by
  obtain ⟨hGR, hRG, hMR, hMR', hz, hM, hMd, hD, hG0⟩ := iC1
  exact GreenCore_Qxd_sq (G := G₁) (X := X₁) (Q := 0) hg.1.le (sz0.three_le_L 3) hD (u := u) fun l => by simp [GreenCore_Xrow, X0]
example (w : Vtx 3 (sz0.L 3) (sz0.W 3)) := GreenCore_eps2_loc (G := G₁) (t := t₁) (by norm_num) (by norm_num) (by norm_num) icr.1 w
example (w : Vtx 3 (sz0.L 3) (sz0.W 3)) := by
  obtain ⟨hGR, hRG, hMR, hMR', hz, hM, hMd, hD, hG0⟩ := iC1
  exact GreenCore_Acol_sq (sz0.three_le_L 3) hg.1.le (by norm_num) hGR hRG hMR hMR' hz hM hMd hD kern.1 kern.2.2.1 icr.1 Om w
example (w : Vtx 3 (sz0.L 3) (sz0.W 3)) := by
  obtain ⟨hGR, hRG, hMR, hMR', hz, hM, hMd, hD, hG0⟩ := iC1; exact GreenCore_Arow_four (X := X₁) (D := D₁) (t := t₁) hM hMd (hG0 w)
example (a : Zd 3 (sz0.L 3)) (w : Vtx 3 (sz0.L 3) (sz0.W 3)) :=
  GreenCore_Xcol_avg zero_le_one (by norm_num) (fun x w => GreenCore_Xcol_sq (by norm_num) zero_le_one icr.1 iLDE.2.1 x w)
    (GreenCore_apriori icr.2.1 icr.2.2 (by norm_num) iwd).2 a w
-- R3: the two-sided inequality, and its closure (R*) (`GreenCore_Rstar`, `GreenCore_closure` inside)
example (a c : Zd 3 (sz0.L 3)) (o : Fin (sz0.W 3 ^ 3)) := by
  obtain ⟨hGR, hRG, hMR, hMR', hz, hM, hMd, hD, hG0⟩ := iC1
  exact GreenCore_twoSided (by norm_num : (0 : ℝ) ≤ 4096) (by norm_num : (0 : ℝ) < 1 / 2) zero_le_one (by positivity) hM iρ
    (GreenCore_Delta_col hGR hRG hMR hz hM hG0)
    (fun w => GreenCore_Acol_sq (sz0.three_le_L 3) hg.1.le (by norm_num) hGR hRG hMR hMR' hz hM hMd hD kern.1 kern.2.2.1 icr.1 Om w)
    (fun x w => GreenCore_Xcol_sq (by norm_num) zero_le_one icr.1 iLDE.2.1 x w) (GreenCore_apriori icr.2.1 icr.2.2 (by norm_num) iwd).2 a c o
example (a c : Zd 3 (sz0.L 3)) (o : Fin (sz0.W 3 ^ 3)) := by
  obtain ⟨hGR, hRG, hMR, hMR', hz, hM, hMd, hD, hG0⟩ := iC1
  exact GreenCore_Rbound (sz0.three_le_L 3) hGR hRG hMR hMR' hz hM hMd hD (by norm_num) kern.1 kern.2.1 kern.2.2.1 c0pos kern.2.2.2.1 iρ iS
    hg.1.le le_rfl (by norm_num) (by norm_num) iwd Om iLDE.2.1 iC1n (fun _ _ => 3) (fun a b => loop_le Gbd a b) a c o
-- R4: the diagonal law (with `BAStab` discharged), and the coupled bound `‖Δ‖ ≤ ρ (1 + ρ₂ K_Θ) ‖𝒦‖`, `ρ (1 + ρ₂ K_Θ) = 4096 · 257`
example (x y : Vtx 3 (sz0.L 3) (sz0.W 3)) := by
  obtain ⟨hGR, hRG, hMR, hMR', hz, hM, hMd, hD, hG0⟩ := iC1
  exact GreenCore_diag (sz0.three_le_L 3) hGR hRG hMR hMR' hz hM hMd hD (by norm_num) kern.1 kern.2.1 kern.2.2.1 c0pos kern.2.2.2.1 iρ iS
    hg.1.le (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num) iwd Om iLDE.1 iLDE.2.1 iLDE.2.2.1 iLDE.2.2.2 iC1n
    (fun a b => loop_le Gbd a b) (by positivity) rfl istabBA (by norm_num) (fun a => cnt _ fun b => kern.2.2.1 a b) kern.2.2.2.2 (by norm_num) x y
example (x y : Vtx 3 (sz0.L 3) (sz0.W 3)) := by
  obtain ⟨hGR, hRG, hMR, hMR', hz, hM, hMd, hD, hG0⟩ := iC1
  exact GreenCore_coupled (Δ := fun x y => G₁ x y - M₁ x y) (𝒦 := GreenCore_K G₁ M₁ X₁ D₁ t₁ m₀) (vb := GreenCore_vbar G₁ M₁)
    (Kθ := 256) hM (by norm_num) (by norm_num) (by norm_num) (fun a => cnt _ fun b => kern.2.2.1 a b) kern.2.2.2.2 (fun a => rfl)
    (fun x y => GreenCore_E3 hGR hRG hMR' hz hM hG0 x y) istab (fun u y => K_gen X0 (by norm_num) kern.2.1 Gbd Om u y) x y

end GreenCoreInst

end RBM.BA
