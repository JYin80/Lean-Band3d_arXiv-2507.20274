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

Ticket T2390 (design gate `docs/reports/T2390-prove.md` (a), (a′), (G), stage 1b).  Paper: `paper/tex/7_8_light_weight.tex`
(`7_8:line`, `lem_GbEXP_BA` `:1916-1946`), band `paper/tex/3_5_Loop_Hierarchy.tex`.  Everything here is deterministic, for one
sample: the large deviation inputs of `BALDEin` (T2389) enter as the per-sample events `LDERow`, `LDECol`, `LDEQuad`, the
diagonal bound, and `Ω = {‖G - M‖_max ≤ δ}`.  Sites are `u = (a, o)` of `Vtx d L W` (block `a`, offset `o`), `M = M^{(B)} ⊗ I`,
`D = g₀ Ψ`, `H = D + X`, `G = (H - z)⁻¹`, `Δ = G - M`, `w₀ = W^{-d}`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
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
theorem GreenCore_m1 {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℂ} (hκ : 0 < κ) {w : ι}
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

/-- `Q^{DX}_w = Σ_{l,k≠w} D_{wl} G^{(w)}_{lk} X_{kw}` and `Q^{XD}_u = Σ_{k,l≠u} X_{uk} G^{(u)}_{kl} D_{lu}`. -/
def GreenCore_Qdx (G X D : Matrix (Vtx d L W) (Vtx d L W) ℂ) (w : Vtx d L W) : ℂ :=
  ∑ l ∈ univ.erase w, ∑ k ∈ univ.erase w, D w l * greenMinor G w l k * X k w

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

/-- **(E2), column form**: `A'_w = -t v̄_{[w]} + ε_2 - ε_1 + X_{ww} - Q^{DX}_w`. -/
theorem GreenCore_Acol_eq {t : ℝ} (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0)
    (hMd : ∀ a, Mb a a = m) {w : Vtx d L W} (hw : G w w ≠ 0) :
    GreenCore_Acol G X D t m w = -((t : ℂ) * GreenCore_vbar G M w.1) + GreenCore_eps2 G t w -
      GreenCore_eps1 G X t w + X w w - GreenCore_Qdx G X D w := by
  have h : ∑ l ∈ univ.erase w, ∑ k ∈ univ.erase w, (D + X) w l * greenMinor G w l k * X k w =
      GreenCore_Qxx G X w + GreenCore_Qdx G X D w := by
    unfold GreenCore_Qxx GreenCore_Qdx
    rw [add_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.add_apply]; ring
  unfold GreenCore_Acol
  rw [h, ← GreenCore_E2 (X := X) hM hMd hw]
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



/-- `|Q^{DX}_w|² ≤ (2 d g₀)² Q` if `|𝔛'_{lw}|² ≤ Q` for all `l`. -/
theorem GreenCore_Qdx_sq {g₀ Q : ℝ} (hg : 0 ≤ g₀) (hL : 3 ≤ L)
    (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0) {w : Vtx d L W}
    (hXc : ∀ l, ‖GreenCore_Xcol G X l w‖ ^ 2 ≤ Q) :
    ‖GreenCore_Qdx G X D w‖ ^ 2 ≤ (2 * d * g₀) ^ 2 * Q := by
  have hrow := GreenCore_Drow (W := W) hg hL hD w
  have h1 : ∀ l, ∑ k ∈ univ.erase w, D w l * greenMinor G w l k * X k w = D w l * GreenCore_Xcol G X l w :=
    fun l => by unfold GreenCore_Xcol; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  unfold GreenCore_Qdx
  simp only [h1]
  have h2 : ‖∑ l ∈ univ.erase w, D w l * GreenCore_Xcol G X l w‖ ≤ ∑ l, ‖D w l‖ * ‖GreenCore_Xcol G X l w‖ :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun l _ => (norm_mul _ _).le).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun l _ _ => by positivity))
  have h3 : (∑ l, ‖D w l‖ * ‖GreenCore_Xcol G X l w‖) ^ 2 ≤
      (∑ l, ‖D w l‖) * ∑ l, ‖D w l‖ * ‖GreenCore_Xcol G X l w‖ ^ 2 :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun l _ => norm_nonneg _) (fun l _ => by positivity)
      fun l _ => le_of_eq (by ring)
  have h4 : ∑ l, ‖D w l‖ * ‖GreenCore_Xcol G X l w‖ ^ 2 ≤ (∑ l, ‖D w l‖) * Q := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hXc l) (norm_nonneg _)
  calc _ ≤ (∑ l, ‖D w l‖ * ‖GreenCore_Xcol G X l w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ ≤ (∑ l, ‖D w l‖) * ((∑ l, ‖D w l‖) * Q) :=
        h3.trans (mul_le_mul_of_nonneg_left h4 (Finset.sum_nonneg fun l _ => norm_nonneg _))
    _ = (2 * d * g₀) ^ 2 * Q := by rw [hrow]; ring

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

/-- The five-term bound for the column form: `|A'_w|² ≤ 5 (|t v̄|² + |ε_2|² + |ε_1|² + |X_{ww}|² + |Q^{DX}_w|²)`. -/
theorem GreenCore_Acol_five {t : ℝ} (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0)
    (hMd : ∀ a, Mb a a = m) {w : Vtx d L W} (hw : G w w ≠ 0) :
    ‖GreenCore_Acol G X D t m w‖ ^ 2 ≤ 5 * (‖(t : ℂ) * GreenCore_vbar G M w.1‖ ^ 2 + ‖GreenCore_eps2 G t w‖ ^ 2 +
      ‖GreenCore_eps1 G X t w‖ ^ 2 + ‖X w w‖ ^ 2 + ‖GreenCore_Qdx G X D w‖ ^ 2) := by
  refine (pow_le_pow_left₀ (norm_nonneg _) ?_ 2).trans (GreenCore_sq5 _ _ _ _ _)
  rw [GreenCore_Acol_eq hM hMd hw]
  refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (le_of_eq (norm_neg _)) le_rfl))
      le_rfl)) le_rfl)) le_rfl)

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

/-- **(E0) + (E1′)** in entries: `Δ_{xy} = -Σ_{b'} M^{(B)}_{b'[y]} (A'_{(b',o_y)} G_{x(b',o_y)} + 𝔛'_{x(b',o_y)})`,
for `(H - z) G = 1`, `G (H - z) = 1`, `(D - s) M = 1`, `z = s - t m`, `H = D + X`, `M = M^{(B)} ⊗ I`. -/
theorem GreenCore_Delta_col {t : ℝ} {s z : ℂ} (hGR : G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1)
    (hRG : (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1)
    (hMR : (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * M = 1) (hz : z = s - (t : ℂ) * m)
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hG0 : ∀ u, G u u ≠ 0) (x y : Vtx d L W) :
    G x y - M x y = -∑ b', Mb b' y.1 * (GreenCore_Acol G X D t m (b', y.2) * G x (b', y.2) +
      GreenCore_Xcol G X x (b', y.2)) := by
  have key : (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) - (D + X - z • 1) =
      -(X + ((t : ℂ) * m) • 1) := by rw [hz]; module
  have e0 : G - M = -(G * (X + ((t : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * M) := by
    calc G - M = G * (D - s • 1) * M - G * (D + X - z • 1) * M := by
          rw [mul_assoc G (D - s • 1) M, hMR, mul_one, hGR, one_mul]
      _ = _ := by rw [← sub_mul, ← mul_sub, key, mul_neg, neg_mul]
  have e1 : ∀ u, (G * (X + ((t : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))) x u =
      GreenCore_Acol G X D t m u * G x u + GreenCore_Xcol G X x u := by
    intro u
    have h1 := GreenCore_E1' (X := X) hRG x u (hG0 u)
    have h2 : (G * (X + ((t : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))) x u =
        ∑ k, G x k * X k u + (t : ℂ) * m * G x u := by
      rw [Matrix.mul_apply]
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_add,
        Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring
    rw [h2, h1]; unfold GreenCore_Acol GreenCore_Xcol; ring
  have h3 := congrFun (congrFun e0 x) y
  simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.mul_apply] at h3
  rw [h3]
  congr 1
  have h4 := GreenCore_sum_kron hM (fun u => (G * (X + ((t : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))) x u) y
  simp only [Matrix.mul_apply] at h4
  rw [h4]
  refine Finset.sum_congr rfl fun b' _ => ?_
  have := e1 (b', y.2)
  simp only [Matrix.mul_apply] at this
  rw [this]; ring


/-- **(A\*)**: the a priori bound `|A'_w|² ≤ C_𝒜 Φ δ²`, `C_𝒜 = (225 + 1300 d² g₀²) κ⁻²` (`(a′)` D3.1). -/
theorem GreenCore_Acol_apriori {t g₀ : ℝ} (hL : 3 ≤ L) (hg : 0 ≤ g₀) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hΦ : 1 ≤ Φ)
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hMd : ∀ a, Mb a a = m)
    (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0)
    (hGuu : ∀ u, κ / 2 ≤ ‖G u u‖) (hG32 : ∀ u v, ‖G u v‖ ≤ 3 / 2)
    (hGoff : ∀ u v, u.2 ≠ v.2 → ‖G u v‖ ≤ δ) (hΩ : ∀ u v, ‖G u v - M u v‖ ≤ δ) (hδ : δ ≤ κ / 2)
    (hδ0 : 0 ≤ δ) (hwd : ((W : ℝ) ^ d)⁻¹ ≤ δ ^ 2) (hLcol : LDECol X G (svar d L W 0) Φ)
    (hLquad : LDEQuad X G (svar d L W 0) t Φ) (hLdiag : ∀ i, ‖X i i‖ ^ 2 ≤ Φ * svar d L W 0 i i)
    (w : Vtx d L W) :
    ‖GreenCore_Acol G X D t m w‖ ^ 2 ≤ ((225 + 1300 * d ^ 2 * g₀ ^ 2) / κ ^ 2) * Φ * δ ^ 2 := by
  have hΦ0 : 0 ≤ Φ := by linarith
  have hw0 : G w w ≠ 0 := fun h => by
    have := hGuu w; rw [h, norm_zero] at this; linarith
  have hap := GreenCore_apriori hG32 hGoff hδ0 hwd
  have hδ2 : δ ^ 2 ≤ 1 / 4 := by nlinarith
  have hk2 : 1 ≤ 1 / κ ^ 2 := by rw [le_div_iff₀ (by positivity)]; nlinarith
  have hΦδ : 0 ≤ Φ * δ ^ 2 := mul_nonneg hΦ0 (sq_nonneg δ)
  have hRR : GreenCore_R G w.1 w ≤ 13 / 4 * δ ^ 2 := hap.1 _ _
  have hRw : GreenCore_Rrow G w w.1 ≤ 13 / 4 * δ ^ 2 := hap.2 _ _
  have hR0 : 0 ≤ GreenCore_R G w.1 w := mul_nonneg GreenCore_w_pos.le (Finset.sum_nonneg fun _ _ => by positivity)
  have hRw0 : 0 ≤ GreenCore_Rrow G w w.1 := mul_nonneg GreenCore_w_pos.le (Finset.sum_nonneg fun _ _ => by positivity)
  have hRRw : GreenCore_R G w.1 w * GreenCore_Rrow G w w.1 ≤ 3 * δ ^ 2 := by
    nlinarith [mul_le_mul hRR hRw hRw0 (by positivity : (0 : ℝ) ≤ 13 / 4 * δ ^ 2), sq_nonneg δ]
  have hloop : GreenCore_loop G w.1 w.1 ≤ 13 / 4 * δ ^ 2 := by
    unfold GreenCore_loop
    have : (((W : ℝ) ^ d)⁻¹) ^ 2 * ∑ o, ∑ o', ‖G (w.1, o) (w.1, o')‖ ^ 2 =
        ((W : ℝ) ^ d)⁻¹ * ∑ o, GreenCore_Rrow G (w.1, o) w.1 := by
      rw [sq, mul_assoc, Finset.mul_sum]; unfold GreenCore_Rrow; simp only [Finset.mul_sum]
    rw [this]; exact GreenCore_avg_le fun o => hap.2 _ _
  have b1 : ‖(t : ℂ) * GreenCore_vbar G M w.1‖ ^ 2 ≤ δ ^ 2 := by
    have : ‖(t : ℂ) * GreenCore_vbar G M w.1‖ ≤ δ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
      have : ‖GreenCore_vbar G M w.1‖ ≤ δ := by
        unfold GreenCore_vbar
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg GreenCore_w_pos.le]
        exact (mul_le_mul_of_nonneg_left (norm_sum_le _ _) GreenCore_w_pos.le).trans
          (GreenCore_avg_le fun o => hΩ _ _)
      nlinarith [norm_nonneg (GreenCore_vbar G M w.1)]
    nlinarith [norm_nonneg ((t : ℂ) * GreenCore_vbar G M w.1)]
  have b2 : ‖GreenCore_eps2 G t w‖ ^ 2 ≤ 12 / κ ^ 2 * δ ^ 2 := by
    refine (GreenCore_eps2_loc ht0 ht1 hκ hGuu w).trans ?_
    have := mul_le_mul_of_nonneg_left hRRw (by positivity : (0 : ℝ) ≤ 4 / κ ^ 2)
    calc _ = 4 / κ ^ 2 * (GreenCore_R G w.1 w * GreenCore_Rrow G w w.1) := by ring
      _ ≤ 4 / κ ^ 2 * (3 * δ ^ 2) := this
      _ = _ := by ring
  have b3 : ‖GreenCore_eps1 G X t w‖ ^ 2 ≤ Φ * δ ^ 2 * (13 / 2 + 24 / κ ^ 2) := by
    refine (GreenCore_eps1_loc hκ hΦ0 hGuu hLquad w).trans ?_
    have := mul_le_mul_of_nonneg_left hRRw (by positivity : (0 : ℝ) ≤ 8 / κ ^ 2)
    have e : 8 / κ ^ 2 * (3 * δ ^ 2) = 24 / κ ^ 2 * δ ^ 2 := by ring
    nlinarith [mul_le_mul_of_nonneg_left (show 2 * GreenCore_loop G w.1 w.1 + 8 / κ ^ 2 * GreenCore_R G w.1 w * GreenCore_Rrow G w w.1
      ≤ (13 / 2 + 24 / κ ^ 2) * δ ^ 2 by nlinarith) hΦ0]
  have b4 : ‖X w w‖ ^ 2 ≤ Φ * δ ^ 2 := by
    have := hLdiag w
    rw [GreenCore_svar0] at this; simp only [ite_true] at this
    exact this.trans (mul_le_mul_of_nonneg_left hwd hΦ0)
  have hXc : ∀ l, ‖GreenCore_Xcol G X l w‖ ^ 2 ≤ (65 / κ ^ 2) * Φ * δ ^ 2 := by
    intro l
    have h1 := GreenCore_Xcol_sq hκ hΦ0 hGuu hLcol l w
    have h2 := hap.2 l w.1
    have h4 : ‖G l w‖ ^ 2 ≤ 9 / 4 := by nlinarith [norm_nonneg (G l w), hG32 l w]
    refine h1.trans ?_
    have h5 : 2 * GreenCore_Rrow G l w.1 + (8 / κ ^ 2) * ‖G l w‖ ^ 2 * GreenCore_Rrow G w w.1 ≤
        2 * (13 / 4 * δ ^ 2) + (8 / κ ^ 2) * (9 / 4) * (13 / 4 * δ ^ 2) := by
      have : (8 / κ ^ 2) * ‖G l w‖ ^ 2 * GreenCore_Rrow G w w.1 ≤ (8 / κ ^ 2) * (9 / 4) * (13 / 4 * δ ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h4 (by positivity)) hRw hRw0 (by positivity)
      linarith
    have h6 : 2 * (13 / 4 * δ ^ 2) + (8 / κ ^ 2) * (9 / 4) * (13 / 4 * δ ^ 2) ≤ (65 / κ ^ 2) * δ ^ 2 := by
      have e : (8 / κ ^ 2) * (9 / 4) * (13 / 4 * δ ^ 2) = (117 / 2) * (1 / κ ^ 2) * δ ^ 2 := by field_simp; ring
      have e2 : (65 / κ ^ 2) * δ ^ 2 = 65 * (1 / κ ^ 2) * δ ^ 2 := by ring
      rw [e, e2]
      nlinarith [sq_nonneg δ, mul_nonneg (sq_nonneg δ) (sub_nonneg.2 hk2)]
    calc Φ * (2 * GreenCore_Rrow G l w.1 + (8 / κ ^ 2) * ‖G l w‖ ^ 2 * GreenCore_Rrow G w w.1)
        ≤ Φ * ((65 / κ ^ 2) * δ ^ 2) := mul_le_mul_of_nonneg_left (h5.trans h6) hΦ0
      _ = (65 / κ ^ 2) * Φ * δ ^ 2 := by ring
  have b5 := GreenCore_Qdx_sq (G := G) (X := X) hg hL hD (fun l => hXc l)
  refine (GreenCore_Acol_five (G := G) (X := X) (D := D) hM hMd hw0).trans ?_
  -- clean the five bounds in terms of `P = Φ δ²`, `k = κ⁻²`, `c = d² g₀²`
  have hq : (2 * d * g₀) ^ 2 * ((65 / κ ^ 2) * Φ * δ ^ 2) = (260 * (d ^ 2 * g₀ ^ 2)) * ((1 / κ ^ 2) * (Φ * δ ^ 2)) := by
    field_simp; ring
  have e2 : 12 / κ ^ 2 * δ ^ 2 = 12 * ((1 / κ ^ 2) * δ ^ 2) := by ring
  have e3 : ((225 + 1300 * d ^ 2 * g₀ ^ 2) / κ ^ 2) * Φ * δ ^ 2 =
      (225 + 1300 * (d ^ 2 * g₀ ^ 2)) * ((1 / κ ^ 2) * (Φ * δ ^ 2)) := by ring
  have e4 : Φ * δ ^ 2 * (13 / 2 + 24 / κ ^ 2) = 13 / 2 * (Φ * δ ^ 2) + 24 * ((1 / κ ^ 2) * (Φ * δ ^ 2)) := by ring
  rw [hq] at b5
  rw [e2] at b2
  rw [e4] at b3
  rw [e3]
  have hk0 : 0 ≤ 1 / κ ^ 2 := by positivity
  have hc0 : 0 ≤ d ^ 2 * g₀ ^ 2 := by positivity
  have e1 : δ ^ 2 ≤ Φ * δ ^ 2 := le_mul_of_one_le_left (sq_nonneg δ) hΦ
  have f1 : 1 / κ ^ 2 * δ ^ 2 ≤ 1 / κ ^ 2 * (Φ * δ ^ 2) := mul_le_mul_of_nonneg_left e1 hk0
  have f2 : Φ * δ ^ 2 ≤ 1 / κ ^ 2 * (Φ * δ ^ 2) := le_mul_of_one_le_left hΦδ hk2
  have f3 : 0 ≤ (d ^ 2 * g₀ ^ 2) * ((1 / κ ^ 2) * (Φ * δ ^ 2)) := mul_nonneg hc0 (mul_nonneg hk0 hΦδ)
  generalize ‖(t : ℂ) * GreenCore_vbar G M w.1‖ ^ 2 = x1 at *
  generalize ‖GreenCore_eps2 G t w‖ ^ 2 = x2 at *
  generalize ‖GreenCore_eps1 G X t w‖ ^ 2 = x3 at *
  generalize ‖X w w‖ ^ 2 = x4 at *
  generalize ‖GreenCore_Qdx G X D w‖ ^ 2 = x5 at *
  generalize 1 / κ ^ 2 * (Φ * δ ^ 2) = kP at *
  generalize Φ * δ ^ 2 = P at *
  generalize d ^ 2 * g₀ ^ 2 = c at *
  linarith


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


/-- The block distance `|a - b|` (`zdistD`) as a real function: the axioms used by the closure. -/
theorem GreenCore_dist : (∀ a : Zd d L, ((zdistD d L (a - a) : ℕ) : ℝ) = 0) ∧
    (∀ a b : Zd d L, 0 ≤ ((zdistD d L (a - b) : ℕ) : ℝ)) ∧
    (∀ a b : Zd d L, ((zdistD d L (a - b) : ℕ) : ℝ) = ((zdistD d L (b - a) : ℕ) : ℝ)) ∧
    (∀ a b c : Zd d L, ((zdistD d L (a - c) : ℕ) : ℝ) ≤ ((zdistD d L (a - b) : ℕ) : ℝ) + ((zdistD d L (b - c) : ℕ) : ℝ)) := by
  refine ⟨fun a => by simp, fun a b => Nat.cast_nonneg _, fun a b => ?_, fun a b c => ?_⟩
  · rw [← neg_sub b a, zdistD_neg]
  · have := zdistD_add_le d L (a - b) (b - c)
    rw [show a - b + (b - c) = a - c by ring] at this
    exact_mod_cast this

/-- **(R\*)**, `G3a` row R3: on `Ω ∩ LDE`, for every block `a`, column `y = (c, o)` and loop control `φ`
(`𝓛^{(2)}_{(-,+),(a,b)} ≤ φ(a,b)²`), `R_{a,(c,o)} ≤ 4 c₀⁻² S W^{-d} e^{-(c₀/2)|a-c|} +
16 ρ Φ c₀⁻¹ S Σ_{b''} e^{-(c₀/2)|c-b''|} φ(a,b'')²` (`(a′)` D3.2; constants `C_𝒜 = (225 + 1300 d² g₀²) κ⁻²`).
Only the uniform facts are used: Kronecker `M`, `|M_{ab}| ≤ c₀⁻¹ e^{-c₀|a-b|}`, `ℓ¹` rows (`ρ`, `ρe`, `S`), `κ ≤ |m|`. -/
theorem GreenCore_Rbound (hL : 3 ≤ L) {t g₀ c₀ ρ ρe S : ℝ} {s z : ℂ}
    (hGR : G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1)
    (hRG : (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1)
    (hMR : (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * M = 1) (hz : z = s - (t : ℂ) * m)
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hMd : ∀ a, Mb a a = m)
    (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0)
    (hκ : 0 < κ) (hκm : κ ≤ ‖m‖) (hm1 : ‖m‖ ≤ 1) (hMb1 : ∀ a b, ‖Mb a b‖ ≤ 1) (hc₀ : 0 < c₀)
    (hdec : ∀ a b, ‖Mb a b‖ ≤ c₀⁻¹ * Real.exp (-c₀ * (zdistD d L (a - b) : ℝ)))
    (hρ : ∀ c, ∑ b, ‖Mb b c‖ ≤ ρ)
    (hρe : ∀ c, ∑ b, ‖Mb b c‖ * Real.exp ((c₀ / 2) * (zdistD d L (c - b) : ℝ)) ≤ ρe)
    (hS : ∀ a, ∑ b, Real.exp (-(c₀ / 2) * (zdistD d L (a - b) : ℝ)) ≤ S)
    (hg : 0 ≤ g₀) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hΦ : 1 ≤ Φ) (hδ : δ ≤ κ / 2) (hδ0 : 0 ≤ δ)
    (hwd : ((W : ℝ) ^ d)⁻¹ ≤ δ ^ 2) (hΩ : ∀ u v, ‖G u v - M u v‖ ≤ δ)
    (hLcol : LDECol X G (svar d L W 0) Φ) (hLquad : LDEQuad X G (svar d L W 0) t Φ)
    (hLdiag : ∀ i, ‖X i i‖ ^ 2 ≤ Φ * svar d L W 0 i i)
    (hC1 : 8 * ρ * ρe * (((251 + 1300 * d ^ 2 * g₀ ^ 2) / κ ^ 2) * Φ * δ ^ 2) ≤ 1)
    (φ : Zd d L → Zd d L → ℝ) (hφ : ∀ a b, GreenCore_loop G a b ≤ φ a b ^ 2) (a c : Zd d L) (o : Fin (W ^ d)) :
    GreenCore_R G a (c, o) ≤ 4 * c₀⁻¹ ^ 2 * S * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c₀ / 2) * (zdistD d L (a - c) : ℝ)) +
      16 * ρ * Φ * c₀⁻¹ * S * ∑ b'', Real.exp (-(c₀ / 2) * (zdistD d L (c - b'') : ℝ)) * φ a b'' ^ 2 := by
  have hΦ0 : 0 ≤ Φ := by linarith
  have hκ1 : κ ≤ 1 := hκm.trans hm1
  obtain ⟨hGuu, hG32, hGoff⟩ := GreenCore_crude hM hMd hMb1 hκm hm1 hδ hΩ
  have hG0 : ∀ u, G u u ≠ 0 := fun u h => by
    have := hGuu u; rw [h, norm_zero] at this; linarith
  have hΔ := GreenCore_Delta_col (X := X) hGR hRG hMR hz hM hG0
  have hA := fun w => GreenCore_Acol_apriori hL hg ht0 ht1 hκ hκ1 hΦ hM hMd hD hGuu hG32 hGoff hΩ hδ hδ0 hwd
    hLcol hLquad hLdiag w
  have hX := fun x w => GreenCore_Xcol_sq hκ hΦ0 hGuu hLcol x w
  have hRrow := (GreenCore_apriori hG32 hGoff hδ0 hwd).2
  have hρ0 : 0 ≤ ρ := le_trans (Finset.sum_nonneg fun b _ => norm_nonneg _) (hρ 0)
  have hα : 0 ≤ ((225 + 1300 * d ^ 2 * g₀ ^ 2) / κ ^ 2) * Φ * δ ^ 2 := by positivity
  have h2 := GreenCore_twoSided hρ0 hκ hΦ0 hα hM hρ hΔ hA hX hRrow
  obtain ⟨d0, dn, ds, dt⟩ := GreenCore_dist (d := d) (L := L)
  have hϑ : 0 ≤ ((225 + 1300 * d ^ 2 * g₀ ^ 2) / κ ^ 2) * Φ * δ ^ 2 + 26 / κ ^ 2 * Φ * δ ^ 2 := by positivity
  have hϑe : ((225 + 1300 * d ^ 2 * g₀ ^ 2) / κ ^ 2) * Φ * δ ^ 2 + 26 / κ ^ 2 * Φ * δ ^ 2 =
      ((251 + 1300 * d ^ 2 * g₀ ^ 2) / κ ^ 2) * Φ * δ ^ 2 := by ring
  refine GreenCore_Rstar (fun a b => ((zdistD d L (a - b) : ℕ) : ℝ)) d0 dn ds dt (fun a b => Mb a b) hc₀ hκ
    (fun a => by rw [hMd]; exact hκm) hdec hρe hS GreenCore_w_pos hρ0 hΦ0 hϑ (by rw [hϑe]; exact hC1) a
    (fun b'' => φ a b'') (fun c => GreenCore_R G a (c, o)) (fun c => ?_) (fun c => ?_) c
  · exact mul_nonneg GreenCore_w_pos.le (Finset.sum_nonneg fun _ _ => by positivity)
  · refine (h2 a c o).trans ?_
    have : ∑ b', ‖Mb b' c‖ * GreenCore_loop G a b' ≤ ∑ b', ‖Mb b' c‖ * φ a b' ^ 2 :=
      Finset.sum_le_sum fun b' _ => mul_le_mul_of_nonneg_left (hφ a b') (norm_nonneg _)
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 8 * ρ * Φ)
    linarith

end Reentry

end RBM.BA
