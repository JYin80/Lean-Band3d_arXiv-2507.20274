/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GreenCore
import RBM3D.BA.GreenStab
import RBM3D.BA.GreenLDE
import RBM3D.BA.KBase

/-!
# The off-diagonal decay `(GijGEX_BA)` of the block Anderson resolvent (BA-G4)

Ticket T2403 (with Amend 1).  Design gate `docs/reports/T2390-prove.md` (G) G.4, (a′) D3.2-D3.4.  Paper: `paper/tex/7_8_light_weight.tex`
(`7_8:line`), `lem_GbEXP_BA` `:1916-1946`.

* Section 1: the target kernel `𝔗_γ(a,c) = Σ_{a',b'} φ(a',b') e^{-γ(|a'-a|+|b'-c|)} + Ψ e^{-γ|a-c|}` and its shift, comparison and
  convolution estimates.
* Section 2 (**target 1**): the deterministic weighted closure `GreenOff_close`: on the event, `|Δ_xy| ≤ 2 C_ℓ' Φ_N 𝔗_γ([x],[y])`
  (D3.4: the expansion `Δ = L1 + L2 + L3 + Q` of (E3), the block averages `v̄ = Θ_t u`, the sources bounded by the local (X*), (Ξ),
  the kernel preservation, the weighted `ℓ¹` bound of `Θ`, absorption under (C2)), in the ratio norm.
* Section 3 (**target 2**): `baStab_holds`, the link `BAStab … (16 κ⁻⁴)` at `BAReal` data.
* Section 4 (**target 3**): `baGbEXPij'_holds`.
* Section 5: compiled nonempty instances.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSectionVars false

noncomputable section

open Filter Matrix Finset
open RBM RBM.Green RBM.Gauss

namespace RBM.BA

/-! ## 1. The target kernel -/

section Kernel

variable {d L : ℕ} [NeZero L]

/-- **The target kernel** `𝔗_γ(a,c) = Σ_{a',b'} φ(a',b') e^{-γ(|a'-a| + |b'-c|)} + Ψ e^{-γ|a-c|}` (`7_8:1942-1944` without the
`W^{-D}` term, with the block distance `zdistD ≥ zdistInf`). -/
def GreenOff_T (d L : ℕ) [NeZero L] (γ Ψ : ℝ) (φ : Zd d L → Zd d L → ℝ) (a c : Zd d L) : ℝ :=
  (∑ a' : Zd d L, ∑ b' : Zd d L,
      φ a' b' * Real.exp (-γ * ((zdistD d L (a' - a) : ℝ) + (zdistD d L (b' - c) : ℝ)))) +
    Ψ * Real.exp (-γ * (zdistD d L (a - c) : ℝ))

theorem GreenOff_T_pos {γ Ψ : ℝ} {φ : Zd d L → Zd d L → ℝ} (hφ : ∀ a b, 0 ≤ φ a b) (hΨ : 0 < Ψ) (a c : Zd d L) :
    0 < GreenOff_T d L γ Ψ φ a c :=
  add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun a' _ => Finset.sum_nonneg fun b' _ =>
    mul_nonneg (hφ _ _) (Real.exp_pos _).le) (mul_pos hΨ (Real.exp_pos _))

theorem GreenOff_T_nonneg {γ Ψ : ℝ} {φ : Zd d L → Zd d L → ℝ} (hφ : ∀ a b, 0 ≤ φ a b) (hΨ : 0 ≤ Ψ) (a c : Zd d L) :
    0 ≤ GreenOff_T d L γ Ψ φ a c :=
  add_nonneg (Finset.sum_nonneg fun a' _ => Finset.sum_nonneg fun b' _ =>
    mul_nonneg (hφ _ _) (Real.exp_pos _).le) (mul_nonneg hΨ (Real.exp_pos _).le)

private theorem GreenOff_term_le {γ f x y s : ℝ} (hγ : 0 ≤ γ) (hf : 0 ≤ f) (hxy : x ≤ y + s) :
    f * Real.exp (-γ * y) ≤ Real.exp (γ * s) * (f * Real.exp (-γ * x)) := by
  have h : -γ * y ≤ γ * s + -γ * x := by nlinarith [mul_le_mul_of_nonneg_left hxy hγ]
  calc f * Real.exp (-γ * y) ≤ f * Real.exp (γ * s + -γ * x) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h) hf
    _ = _ := by rw [Real.exp_add]; ring

/-- The shift: `𝔗(a'', c'') ≤ e^{γ(|a - a''| + |c' - c''|)} 𝔗(a, c')`. -/
theorem GreenOff_T_shift {γ Ψ : ℝ} {φ : Zd d L → Zd d L → ℝ} (hγ : 0 ≤ γ) (hφ : ∀ a b, 0 ≤ φ a b) (hΨ : 0 ≤ Ψ)
    (a a'' c' c'' : Zd d L) :
    GreenOff_T d L γ Ψ φ a'' c'' ≤
      Real.exp (γ * ((zdistD d L (a - a'') : ℝ) + (zdistD d L (c' - c'') : ℝ))) * GreenOff_T d L γ Ψ φ a c' := by
  obtain ⟨d0, dn, ds, dt⟩ := GreenCore_dist (d := d) (L := L)
  unfold GreenOff_T
  rw [mul_add, Finset.mul_sum]
  refine add_le_add (Finset.sum_le_sum fun a' _ => ?_) ?_
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b' _ => ?_
    have h1 := dt a' a'' a
    have h2 := dt b' c'' c'
    have h3 := ds a'' a
    have h4 := ds c'' c'
    exact GreenOff_term_le hγ (hφ a' b') (by linarith)
  · have h1 := dt a a'' c''
    have h2 := dt a c'' c'
    have h4 := ds c'' c'
    exact GreenOff_term_le hγ hΨ (by linarith)

/-- `φ(a, c) ≤ 𝔗(a, c)` (the term `a' = a`, `b' = c`). -/
theorem GreenOff_T_ge_phi {γ Ψ : ℝ} {φ : Zd d L → Zd d L → ℝ} (hφ : ∀ a b, 0 ≤ φ a b) (hΨ : 0 ≤ Ψ) (a c : Zd d L) :
    φ a c ≤ GreenOff_T d L γ Ψ φ a c := by
  unfold GreenOff_T
  have h1 : ∀ a' : Zd d L, 0 ≤ ∑ b' : Zd d L, φ a' b' * Real.exp (-γ * ((zdistD d L (a' - a) : ℝ) + (zdistD d L (b' - c) : ℝ))) :=
    fun a' => Finset.sum_nonneg fun b' _ => mul_nonneg (hφ _ _) (Real.exp_pos _).le
  have h2 := Finset.single_le_sum (f := fun a' : Zd d L => ∑ b' : Zd d L,
    φ a' b' * Real.exp (-γ * ((zdistD d L (a' - a) : ℝ) + (zdistD d L (b' - c) : ℝ)))) (fun a' _ => h1 a') (Finset.mem_univ a)
  have h3 := Finset.single_le_sum (f := fun b' : Zd d L =>
    φ a b' * Real.exp (-γ * ((zdistD d L (a - a) : ℝ) + (zdistD d L (b' - c) : ℝ))))
    (fun b' _ => mul_nonneg (hφ _ _) (Real.exp_pos _).le) (Finset.mem_univ c)
  have e : φ a c * Real.exp (-γ * ((zdistD d L (a - a) : ℝ) + (zdistD d L (c - c) : ℝ))) = φ a c := by simp
  simp only [e] at h3
  have h4 : 0 ≤ Ψ * Real.exp (-γ * (zdistD d L (a - c) : ℝ)) := mul_nonneg hΨ (Real.exp_pos _).le
  linarith

/-- `Ψ ≤ 𝔗(a, a)`. -/
theorem GreenOff_T_ge_psi {γ Ψ : ℝ} {φ : Zd d L → Zd d L → ℝ} (hφ : ∀ a b, 0 ≤ φ a b) (hΨ : 0 ≤ Ψ) (a : Zd d L) :
    Ψ ≤ GreenOff_T d L γ Ψ φ a a := by
  unfold GreenOff_T
  have h1 : 0 ≤ ∑ a' : Zd d L, ∑ b' : Zd d L,
      φ a' b' * Real.exp (-γ * ((zdistD d L (a' - a) : ℝ) + (zdistD d L (b' - a) : ℝ))) :=
    Finset.sum_nonneg fun a' _ => Finset.sum_nonneg fun b' _ => mul_nonneg (hφ _ _) (Real.exp_pos _).le
  simp only [sub_self, zdistD_zero, Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
  linarith

/-- The `a' = a` slice of `𝔗`: `Σ_b e^{-γ'|c-b|} φ(a,b) + Ψ e^{-γ|a-c|} ≤ 𝔗(a, c)` for `γ ≤ γ'`. -/
theorem GreenOff_T_slice {γ γ' Ψ : ℝ} {φ : Zd d L → Zd d L → ℝ} (hγ : γ ≤ γ') (hφ : ∀ a b, 0 ≤ φ a b)
    (a c : Zd d L) :
    (∑ b, Real.exp (-γ' * (zdistD d L (c - b) : ℝ)) * φ a b) + Ψ * Real.exp (-γ * (zdistD d L (a - c) : ℝ)) ≤
      GreenOff_T d L γ Ψ φ a c := by
  obtain ⟨d0, dn, ds, dt⟩ := GreenCore_dist (d := d) (L := L)
  unfold GreenOff_T
  have h1 : ∀ a' : Zd d L, 0 ≤ ∑ b' : Zd d L, φ a' b' * Real.exp (-γ * ((zdistD d L (a' - a) : ℝ) + (zdistD d L (b' - c) : ℝ))) :=
    fun a' => Finset.sum_nonneg fun b' _ => mul_nonneg (hφ _ _) (Real.exp_pos _).le
  have h2 := Finset.single_le_sum (f := fun a' : Zd d L => ∑ b' : Zd d L,
    φ a' b' * Real.exp (-γ * ((zdistD d L (a' - a) : ℝ) + (zdistD d L (b' - c) : ℝ)))) (fun a' _ => h1 a') (Finset.mem_univ a)
  have h3 : ∑ b, Real.exp (-γ' * (zdistD d L (c - b) : ℝ)) * φ a b ≤ ∑ b' : Zd d L,
      φ a b' * Real.exp (-γ * ((zdistD d L (a - a) : ℝ) + (zdistD d L (b' - c) : ℝ))) := by
    refine Finset.sum_le_sum fun b _ => ?_
    simp only [sub_self, zdistD_zero, Nat.cast_zero, zero_add]
    rw [mul_comm, ds c b]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hφ _ _)
    nlinarith [mul_le_mul_of_nonneg_right hγ (dn b c)]
  linarith

/-- `C_T = 2 c₀⁻¹ √S + √(16 ρ P c₀⁻¹ S)`: the comparison constant `T ≤ C_T 𝔗_γ` of the kernel of (X*), (Ξ). -/
def GreenOff_CT (c₀ ρ S P : ℝ) : ℝ := 2 * c₀⁻¹ * Real.sqrt S + Real.sqrt (16 * ρ * P * c₀⁻¹ * S)

/-- **`T ≤ C_T 𝔗_γ`** for `γ ≤ c₀/4` (`T = GreenCore_T`, the kernel of (X*), (Ξ), at the rate `c₀/4`; the first term uses
`Ψ ≥ W^{-d/2}`, the second the slice `a' = a`). -/
theorem GreenOff_T_le {W : ℕ} [NeZero W] {c₀ ρ S P γ Ψ : ℝ} {φ : Zd d L → Zd d L → ℝ}
    (hc₀ : 0 < c₀) (hS0 : 0 ≤ S) (hγ : γ ≤ c₀ / 4) (hφ : ∀ a b, 0 ≤ φ a b) (hΨ : 0 ≤ Ψ)
    (hΨw : Real.sqrt (((W : ℝ) ^ d)⁻¹) ≤ Ψ) (a c : Zd d L) :
    GreenCore_T d L W c₀ ρ S P φ a c ≤ GreenOff_CT c₀ ρ S P * GreenOff_T d L γ Ψ φ a c := by
  obtain ⟨d0, dn, ds, dt⟩ := GreenCore_dist (d := d) (L := L)
  have hw := GreenCore_w_pos (d := d) (W := W)
  have hsl := GreenOff_T_slice (γ' := c₀ / 4) (Ψ := Ψ) hγ hφ a c
  unfold GreenCore_T GreenOff_CT
  set X := Ψ * Real.exp (-γ * (zdistD d L (a - c) : ℝ)) with hX
  set Y := ∑ b, Real.exp (-(c₀ / 4) * (zdistD d L (c - b) : ℝ)) * φ a b with hY
  have hX0 : 0 ≤ X := mul_nonneg hΨ (Real.exp_pos _).le
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun b _ => mul_nonneg (Real.exp_pos _).le (hφ _ _)
  have hA : 0 ≤ 2 * c₀⁻¹ * Real.sqrt S := by positivity
  have hB : 0 ≤ Real.sqrt (16 * ρ * P * c₀⁻¹ * S) := Real.sqrt_nonneg _
  have hΨ2 : ((W : ℝ) ^ d)⁻¹ ≤ Ψ ^ 2 := by
    have := Real.sq_sqrt hw.le
    nlinarith [Real.sqrt_nonneg (((W : ℝ) ^ d)⁻¹), hΨw]
  have h1 : Real.sqrt (4 * c₀⁻¹ ^ 2 * S * ((W : ℝ) ^ d)⁻¹) ≤ 2 * c₀⁻¹ * Real.sqrt S * Ψ := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have := Real.sq_sqrt hS0
    calc 4 * c₀⁻¹ ^ 2 * S * ((W : ℝ) ^ d)⁻¹ ≤ 4 * c₀⁻¹ ^ 2 * S * Ψ ^ 2 :=
          mul_le_mul_of_nonneg_left hΨ2 (by positivity)
      _ = (2 * c₀⁻¹ * Real.sqrt S * Ψ) ^ 2 := by rw [mul_pow, mul_pow, mul_pow, this]; ring
  have h2 : Real.exp (-(c₀ / 4) * (zdistD d L (a - c) : ℝ)) ≤ Real.exp (-γ * (zdistD d L (a - c) : ℝ)) :=
    Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_right hγ (dn a c)])
  have h3 : Real.sqrt (4 * c₀⁻¹ ^ 2 * S * ((W : ℝ) ^ d)⁻¹) * Real.exp (-(c₀ / 4) * (zdistD d L (a - c) : ℝ)) ≤
      2 * c₀⁻¹ * Real.sqrt S * X := by
    calc _ ≤ (2 * c₀⁻¹ * Real.sqrt S * Ψ) * Real.exp (-γ * (zdistD d L (a - c) : ℝ)) :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
      _ = _ := by rw [hX]; ring
  have h4 : X + Y ≤ GreenOff_T d L γ Ψ φ a c := by rw [hX, hY]; linarith [hsl]
  nlinarith [mul_nonneg hA hY0, mul_nonneg hB hX0, mul_le_mul_of_nonneg_left h4 (add_nonneg hA hB)]

/-! ### The kernel `M^{(B)}` against `𝔗` -/

variable {Mb : Matrix (Zd d L) (Zd d L) ℂ} {c₀ S γ : ℝ}

theorem GreenOff_Mexp (hc₀ : 0 < c₀) (hγ : γ ≤ c₀ / 2)
    (hdec : ∀ a b, ‖Mb a b‖ ≤ c₀⁻¹ * Real.exp (-c₀ * (zdistD d L (a - b) : ℝ))) (a b : Zd d L) :
    ‖Mb a b‖ * Real.exp (γ * (zdistD d L (a - b) : ℝ)) ≤ c₀⁻¹ * Real.exp (-(c₀ / 2) * (zdistD d L (a - b) : ℝ)) := by
  calc ‖Mb a b‖ * Real.exp (γ * (zdistD d L (a - b) : ℝ))
      ≤ (c₀⁻¹ * Real.exp (-c₀ * (zdistD d L (a - b) : ℝ))) * Real.exp (γ * (zdistD d L (a - b) : ℝ)) :=
        mul_le_mul_of_nonneg_right (hdec a b) (Real.exp_pos _).le
    _ = c₀⁻¹ * Real.exp (-c₀ * (zdistD d L (a - b) : ℝ) + γ * (zdistD d L (a - b) : ℝ)) := by
        rw [mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by
        nlinarith [mul_le_mul_of_nonneg_right hγ (Nat.cast_nonneg (zdistD d L (a - b)) : (0 : ℝ) ≤ _)]))
        (inv_nonneg.2 hc₀.le)

/-- `Σ_b |M_ab| e^{γ|a-b|} ≤ c₀⁻¹ S` for `γ ≤ c₀/2` (`ρ̂`). -/
theorem GreenOff_Mrow (hc₀ : 0 < c₀) (hγ : γ ≤ c₀ / 2)
    (hdec : ∀ a b, ‖Mb a b‖ ≤ c₀⁻¹ * Real.exp (-c₀ * (zdistD d L (a - b) : ℝ)))
    (hS : ∀ a, ∑ b, Real.exp (-(c₀ / 2) * (zdistD d L (a - b) : ℝ)) ≤ S) (a : Zd d L) :
    ∑ b, ‖Mb a b‖ * Real.exp (γ * (zdistD d L (a - b) : ℝ)) ≤ c₀⁻¹ * S :=
  calc _ ≤ ∑ b, c₀⁻¹ * Real.exp (-(c₀ / 2) * (zdistD d L (a - b) : ℝ)) :=
        Finset.sum_le_sum fun b _ => GreenOff_Mexp hc₀ hγ hdec a b
    _ = c₀⁻¹ * ∑ b, Real.exp (-(c₀ / 2) * (zdistD d L (a - b) : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ c₀⁻¹ * S := mul_le_mul_of_nonneg_left (hS a) (inv_nonneg.2 hc₀.le)

theorem GreenOff_Mone (hc₀ : 0 < c₀) (hγ : γ ≤ c₀ / 2)
    (hdec : ∀ a b, ‖Mb a b‖ ≤ c₀⁻¹ * Real.exp (-c₀ * (zdistD d L (a - b) : ℝ))) (b c : Zd d L) :
    ‖Mb b c‖ * Real.exp (γ * (zdistD d L (c - b) : ℝ)) ≤ c₀⁻¹ := by
  obtain ⟨d0, dn, ds, dt⟩ := GreenCore_dist (d := d) (L := L)
  rw [ds c b]
  refine (GreenOff_Mexp hc₀ hγ hdec b c).trans ?_
  have : Real.exp (-(c₀ / 2) * (zdistD d L (b - c) : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [dn b c])
  nlinarith [inv_pos.2 hc₀]

variable {Ψ : ℝ} {φ : Zd d L → Zd d L → ℝ}

/-- Kernel preservation: `Σ_{b'} |M_{ab'}| 𝔗(b', c) ≤ ρ̂ 𝔗(a, c)`, `ρ̂ = c₀⁻¹ S`. -/
theorem GreenOff_convA (hc₀ : 0 < c₀) (hγ0 : 0 ≤ γ) (hγ : γ ≤ c₀ / 2) (hφ : ∀ a b, 0 ≤ φ a b) (hΨ : 0 ≤ Ψ)
    (hdec : ∀ a b, ‖Mb a b‖ ≤ c₀⁻¹ * Real.exp (-c₀ * (zdistD d L (a - b) : ℝ)))
    (hS : ∀ a, ∑ b, Real.exp (-(c₀ / 2) * (zdistD d L (a - b) : ℝ)) ≤ S) (a c : Zd d L) :
    ∑ b', ‖Mb a b'‖ * GreenOff_T d L γ Ψ φ b' c ≤ c₀⁻¹ * S * GreenOff_T d L γ Ψ φ a c := by
  calc ∑ b', ‖Mb a b'‖ * GreenOff_T d L γ Ψ φ b' c
      ≤ ∑ b', (‖Mb a b'‖ * Real.exp (γ * (zdistD d L (a - b') : ℝ))) * GreenOff_T d L γ Ψ φ a c := by
        refine Finset.sum_le_sum fun b' _ => ?_
        have := GreenOff_T_shift hγ0 hφ hΨ a b' c c
        simp only [sub_self, zdistD_zero, Nat.cast_zero, add_zero] at this
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = (∑ b', ‖Mb a b'‖ * Real.exp (γ * (zdistD d L (a - b') : ℝ))) * GreenOff_T d L γ Ψ φ a c := by
        rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (GreenOff_Mrow hc₀ hγ hdec hS a) (GreenOff_T_nonneg hφ hΨ a c)

/-- `Σ_{b'} |M_{ab'}| |M_{b'c}| 𝔗(b', b') ≤ ρ̂ c₀⁻¹ 𝔗(a, c)`. -/
theorem GreenOff_convB (hc₀ : 0 < c₀) (hγ0 : 0 ≤ γ) (hγ : γ ≤ c₀ / 2) (hφ : ∀ a b, 0 ≤ φ a b) (hΨ : 0 ≤ Ψ)
    (hdec : ∀ a b, ‖Mb a b‖ ≤ c₀⁻¹ * Real.exp (-c₀ * (zdistD d L (a - b) : ℝ)))
    (hS : ∀ a, ∑ b, Real.exp (-(c₀ / 2) * (zdistD d L (a - b) : ℝ)) ≤ S) (a c : Zd d L) :
    ∑ b', ‖Mb a b'‖ * ‖Mb b' c‖ * GreenOff_T d L γ Ψ φ b' b' ≤ c₀⁻¹ * S * c₀⁻¹ * GreenOff_T d L γ Ψ φ a c := by
  have hT0 := GreenOff_T_nonneg (γ := γ) hφ hΨ a c
  calc ∑ b', ‖Mb a b'‖ * ‖Mb b' c‖ * GreenOff_T d L γ Ψ φ b' b'
      ≤ ∑ b', (‖Mb a b'‖ * Real.exp (γ * (zdistD d L (a - b') : ℝ))) * c₀⁻¹ * GreenOff_T d L γ Ψ φ a c := by
        refine Finset.sum_le_sum fun b' _ => ?_
        have h1 := GreenOff_T_shift hγ0 hφ hΨ a b' c b'
        have h2 := GreenOff_Mone hc₀ hγ hdec b' c
        have hu : 0 ≤ ‖Mb a b'‖ * Real.exp (γ * (zdistD d L (a - b') : ℝ)) := by positivity
        calc ‖Mb a b'‖ * ‖Mb b' c‖ * GreenOff_T d L γ Ψ φ b' b'
            ≤ ‖Mb a b'‖ * ‖Mb b' c‖ * (Real.exp (γ * ((zdistD d L (a - b') : ℝ) + (zdistD d L (c - b') : ℝ))) *
                GreenOff_T d L γ Ψ φ a c) := mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = ((‖Mb a b'‖ * Real.exp (γ * (zdistD d L (a - b') : ℝ))) *
                (‖Mb b' c‖ * Real.exp (γ * (zdistD d L (c - b') : ℝ)))) * GreenOff_T d L γ Ψ φ a c := by
              rw [mul_add, Real.exp_add]; ring
          _ ≤ ((‖Mb a b'‖ * Real.exp (γ * (zdistD d L (a - b') : ℝ))) * c₀⁻¹) * GreenOff_T d L γ Ψ φ a c :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hu) hT0
    _ = (∑ b', ‖Mb a b'‖ * Real.exp (γ * (zdistD d L (a - b') : ℝ))) * c₀⁻¹ * GreenOff_T d L γ Ψ φ a c := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
    _ ≤ _ := by
        have := GreenOff_Mrow hc₀ hγ hdec hS a
        have h5 : 0 ≤ c₀⁻¹ * GreenOff_T d L γ Ψ φ a c := mul_nonneg (inv_nonneg.2 hc₀.le) hT0
        nlinarith [mul_le_mul_of_nonneg_right this h5]

end Kernel

/-! ## 2. Target 1: the deterministic weighted closure -/

section Close

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `e_X = √(2Φ) √13 κ⁻¹ δ`: the coefficient of `|Δ_{uy}|` in (X*) (`GreenCore_Xstar`). -/
def GreenOff_eX (κ P δ : ℝ) : ℝ := Real.sqrt (2 * P) * (Real.sqrt 13 / κ * δ)

/-- `s_X = √(2Φ) (1 + 2/(κ c₀)) C_T`: the source of `𝔛` in the kernel `𝔗`. -/
def GreenOff_sX (κ c₀ ρ S P : ℝ) : ℝ := Real.sqrt (2 * P) * (1 + 2 / (κ * c₀)) * GreenOff_CT c₀ ρ S P

/-- `s_A`: the source of `𝒜'` in the kernel `𝔗` (from (Ξ), `GreenCore_Xi`, with `T ≤ C_T 𝔗`, `φ ≤ 𝔗`, `W^{-d/2} ≤ Ψ ≤ 𝔗`). -/
def GreenOff_sA (d : ℕ) (κ c₀ ρ S P δ g₀ : ℝ) : ℝ :=
  (Real.sqrt 13 / κ * δ * (1 + Real.sqrt (2 * P)) +
      Real.sqrt (2 * P) * ((1 + 2 / (κ * c₀)) * Real.exp (c₀ / 4) * (2 * d * g₀))) * GreenOff_CT c₀ ρ S P +
    Real.sqrt (2 * P) + Real.sqrt P

/-- `η = α + e_X + 2 d g₀ e^γ e_X / c₀`: the total coefficient of the absorbed (`Δ`-linear) terms (`α` bounds `|A_w|`, (A*)). -/
def GreenOff_eta (d : ℕ) (κ c₀ P δ g₀ γ α : ℝ) : ℝ :=
  α + GreenOff_eX κ P δ + 2 * d * g₀ * Real.exp γ * GreenOff_eX κ P δ / c₀

/-- `C_ℓ' Φ_N = (1 + ρ̂ c₀⁻¹ C_Θ̂) ρ̂ (s_A / c₀ + s_X)`, `ρ̂ = c₀⁻¹ S`, `C_Θ̂ = CΘ`: the constant of the conclusion of the closure. -/
def GreenOff_Cl (d : ℕ) (κ c₀ ρ S P δ g₀ CΘ : ℝ) : ℝ :=
  (1 + c₀⁻¹ * S * c₀⁻¹ * CΘ) * (c₀⁻¹ * S * (GreenOff_sA d κ c₀ ρ S P δ g₀ / c₀ + GreenOff_sX κ c₀ ρ S P))

theorem GreenOff_CT_nonneg {c₀ ρ S P : ℝ} (hc₀ : 0 < c₀) : 0 ≤ GreenOff_CT c₀ ρ S P := by
  unfold GreenOff_CT; positivity

theorem GreenOff_eX_nonneg {κ P δ : ℝ} (hκ : 0 < κ) (hδ : 0 ≤ δ) : 0 ≤ GreenOff_eX κ P δ := by
  unfold GreenOff_eX; positivity

theorem GreenOff_sX_nonneg {κ c₀ ρ S P : ℝ} (hκ : 0 < κ) (hc₀ : 0 < c₀) : 0 ≤ GreenOff_sX κ c₀ ρ S P := by
  unfold GreenOff_sX; have := GreenOff_CT_nonneg (ρ := ρ) (S := S) (P := P) hc₀; positivity

theorem GreenOff_sA_nonneg {κ c₀ ρ S P δ g₀ : ℝ} (hκ : 0 < κ) (hc₀ : 0 < c₀) (hδ : 0 ≤ δ) (hg : 0 ≤ g₀) :
    0 ≤ GreenOff_sA d κ c₀ ρ S P δ g₀ := by
  unfold GreenOff_sA; have := GreenOff_CT_nonneg (ρ := ρ) (S := S) (P := P) hc₀; positivity

variable {Mb : Matrix (Zd d L) (Zd d L) ℂ} {M D : Matrix (Vtx d L W) (Vtx d L W) ℂ}
  {Δ 𝔛 : Vtx d L W → Vtx d L W → ℂ} {Ap : Vtx d L W → ℂ} {vb : Zd d L → ℂ}
  {t γ Ψ P κ δ g₀ c₀ ρ S α N : ℝ} {φ : Zd d L → Zd d L → ℝ}

/-- The `𝔛` part: `|𝔛_{uy}| ≤ (s_X + e_X N) 𝔗(u, y)` from (X*) and `|Δ| ≤ N 𝔗`. -/
theorem GreenOff_X_bd (hc₀ : 0 < c₀) (hS0 : 0 ≤ S) (hγ : γ ≤ c₀ / 4) (hφ : ∀ a b, 0 ≤ φ a b) (hΨ : 0 < Ψ)
    (hΨw : Real.sqrt (((W : ℝ) ^ d)⁻¹) ≤ Ψ) (hκ : 0 < κ) (hδ0 : 0 ≤ δ)
    (hX : ∀ u y, ‖𝔛 u y‖ ≤ Real.sqrt (2 * P) * ((1 + 2 / (κ * c₀)) * GreenCore_T d L W c₀ ρ S P φ u.1 y.1 +
      Real.sqrt 13 / κ * δ * ‖Δ u y‖))
    (hN : ∀ x y, ‖Δ x y‖ ≤ N * GreenOff_T d L γ Ψ φ x.1 y.1) (hN0 : 0 ≤ N) (u y : Vtx d L W) :
    ‖𝔛 u y‖ ≤ (GreenOff_sX κ c₀ ρ S P + GreenOff_eX κ P δ * N) * GreenOff_T d L γ Ψ φ u.1 y.1 := by
  have hT := GreenOff_T_le (W := W) (ρ := ρ) (S := S) (P := P) hc₀ hS0 hγ hφ hΨ.le hΨw u.1 y.1
  have hN' := hN u y
  have h1 : 0 ≤ Real.sqrt 13 / κ * δ := by positivity
  have h2 : 0 ≤ 1 + 2 / (κ * c₀) := by positivity
  have h3 := mul_le_mul_of_nonneg_left hT h2
  have h4 := mul_le_mul_of_nonneg_left hN' h1
  have h5 := mul_le_mul_of_nonneg_left (add_le_add h3 h4) (Real.sqrt_nonneg (2 * P))
  refine (hX u y).trans (h5.trans (le_of_eq ?_))
  unfold GreenOff_sX GreenOff_eX
  ring

/-- `Σ_l |D_{lw}| |Δ_{wl}| ≤ 2 d g₀ e^γ N 𝔗(w, w)`: only the `2d` neighbours `l ∼ w` contribute and `𝔗(b', l) ≤ e^γ 𝔗(b', b')`. -/
theorem GreenOff_Dsum_bd (hγ0 : 0 ≤ γ) (hφ : ∀ a b, 0 ≤ φ a b) (hΨ : 0 ≤ Ψ)
    (hD1 : ∀ w, ∑ l, ‖D l w‖ = 2 * d * g₀) (hDadj : ∀ l w, D l w ≠ 0 → zdistD d L (w.1 - l.1) = 1)
    (hN : ∀ x y, ‖Δ x y‖ ≤ N * GreenOff_T d L γ Ψ φ x.1 y.1) (hN0 : 0 ≤ N) (w : Vtx d L W) :
    ∑ l, ‖D l w‖ * ‖Δ w l‖ ≤ 2 * d * g₀ * Real.exp γ * N * GreenOff_T d L γ Ψ φ w.1 w.1 := by
  calc ∑ l, ‖D l w‖ * ‖Δ w l‖ ≤ ∑ l, ‖D l w‖ * (Real.exp γ * N * GreenOff_T d L γ Ψ φ w.1 w.1) := by
        refine Finset.sum_le_sum fun l _ => ?_
        by_cases hDl : D l w = 0
        · rw [hDl, norm_zero, zero_mul, zero_mul]
        · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have h1 := GreenOff_T_shift hγ0 hφ hΨ w.1 w.1 w.1 l.1
          rw [hDadj l w hDl, sub_self, zdistD_zero] at h1
          simp only [Nat.cast_zero, Nat.cast_one, zero_add, mul_one] at h1
          calc ‖Δ w l‖ ≤ N * GreenOff_T d L γ Ψ φ w.1 l.1 := hN w l
            _ ≤ N * (Real.exp γ * GreenOff_T d L γ Ψ φ w.1 w.1) := mul_le_mul_of_nonneg_left h1 hN0
            _ = _ := by ring
    _ = _ := by rw [← Finset.sum_mul, hD1 w]; ring

/-- The `𝒜'` part: `|𝒜'_w| ≤ (s_A + 2 d g₀ e^γ e_X N) 𝔗(w, w)` from (Ξ) and `|Δ| ≤ N 𝔗`. -/
theorem GreenOff_Ap_bd (hc₀ : 0 < c₀) (hS0 : 0 ≤ S) (hγ0 : 0 ≤ γ) (hγ : γ ≤ c₀ / 4) (hφ : ∀ a b, 0 ≤ φ a b)
    (hΨ : 0 < Ψ) (hΨw : Real.sqrt (((W : ℝ) ^ d)⁻¹) ≤ Ψ) (hP : 0 ≤ P) (hκ : 0 < κ) (hδ0 : 0 ≤ δ) (hg : 0 ≤ g₀)
    (hXi : ∀ w, ‖Ap w‖ ≤ Real.sqrt 13 / κ * δ * (1 + Real.sqrt (2 * P)) * GreenCore_T d L W c₀ ρ S P φ w.1 w.1 +
      Real.sqrt (2 * P) * φ w.1 w.1 + Real.sqrt (P * ((W : ℝ) ^ d)⁻¹) +
      Real.sqrt (2 * P) * ((1 + 2 / (κ * c₀)) * Real.exp (c₀ / 4) * (2 * d * g₀) * GreenCore_T d L W c₀ ρ S P φ w.1 w.1 +
        Real.sqrt 13 / κ * δ * ∑ l, ‖D l w‖ * ‖Δ w l‖))
    (hD1 : ∀ w, ∑ l, ‖D l w‖ = 2 * d * g₀) (hDadj : ∀ l w, D l w ≠ 0 → zdistD d L (w.1 - l.1) = 1)
    (hN : ∀ x y, ‖Δ x y‖ ≤ N * GreenOff_T d L γ Ψ φ x.1 y.1) (hN0 : 0 ≤ N) (w : Vtx d L W) :
    ‖Ap w‖ ≤ (GreenOff_sA d κ c₀ ρ S P δ g₀ + 2 * d * g₀ * Real.exp γ * GreenOff_eX κ P δ * N) *
      GreenOff_T d L γ Ψ φ w.1 w.1 := by
  have hT := GreenOff_T_le (W := W) (ρ := ρ) (S := S) (P := P) hc₀ hS0 hγ hφ hΨ.le hΨw w.1 w.1
  have hφw := GreenOff_T_ge_phi (γ := γ) hφ hΨ.le w.1 w.1
  have hψw := GreenOff_T_ge_psi (γ := γ) (Ψ := Ψ) hφ hΨ.le w.1
  have hDs := GreenOff_Dsum_bd (Ψ := Ψ) hγ0 hφ hΨ.le hD1 hDadj hN hN0 w
  have hw0 := GreenCore_w_pos (d := d) (W := W)
  have hsq : Real.sqrt (P * ((W : ℝ) ^ d)⁻¹) ≤ Real.sqrt P * GreenOff_T d L γ Ψ φ w.1 w.1 := by
    rw [Real.sqrt_mul hP]
    exact mul_le_mul_of_nonneg_left (hΨw.trans hψw) (Real.sqrt_nonneg _)
  have c1 : 0 ≤ Real.sqrt 13 / κ * δ * (1 + Real.sqrt (2 * P)) := by positivity
  have c2 : 0 ≤ (1 + 2 / (κ * c₀)) * Real.exp (c₀ / 4) * (2 * d * g₀) := by positivity
  have c3 : 0 ≤ Real.sqrt 13 / κ * δ := by positivity
  have e1 := mul_le_mul_of_nonneg_left hT c1
  have e2 := mul_le_mul_of_nonneg_left hφw (Real.sqrt_nonneg (2 * P))
  have e3 := mul_le_mul_of_nonneg_left hT c2
  have e4 := mul_le_mul_of_nonneg_left hDs c3
  have e5 := mul_le_mul_of_nonneg_left (add_le_add e3 e4) (Real.sqrt_nonneg (2 * P))
  refine (hXi w).trans ?_
  unfold GreenOff_sA GreenOff_eX
  nlinarith [e1, e2, hsq, e5]

/-- **The remainder `R = Δ - L3` is bounded linearly in `N`**: if `|Δ| ≤ N 𝔗` then
`|Δ_{xy} - Σ_{b'} M_{[x]b'} t v̄_{b'} M_{(b',o_x) y}| ≤ (S₀ + η₀ N) 𝔗([x],[y])`, `S₀ = ρ̂ (s_A/c₀ + s_X)`, `η₀ = ρ̂ η`
(`L1 + L2 + Q` of D3.4: the sources `s_A`, `s_X`, and the absorbed terms `α`, `e_X`, `2 d g₀ e^γ e_X/c₀`). -/
theorem GreenOff_R_bd (hc₀ : 0 < c₀) (hS0 : 0 ≤ S) (hγ0 : 0 ≤ γ) (hγ : γ ≤ c₀ / 4) (hφ : ∀ a b, 0 ≤ φ a b)
    (hΨ : 0 < Ψ) (hΨw : Real.sqrt (((W : ℝ) ^ d)⁻¹) ≤ Ψ) (hP : 0 ≤ P) (hκ : 0 < κ) (hδ0 : 0 ≤ δ) (hg : 0 ≤ g₀)
    (hdec : ∀ a b, ‖Mb a b‖ ≤ c₀⁻¹ * Real.exp (-c₀ * (zdistD d L (a - b) : ℝ)))
    (hS : ∀ a, ∑ b, Real.exp (-(c₀ / 2) * (zdistD d L (a - b) : ℝ)) ≤ S)
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0)
    (hE3 : ∀ x y, Δ x y = ∑ b', Mb x.1 b' * ((t : ℂ) * vb b' * M (b', x.2) y +
      ((t : ℂ) * vb b' - Ap (b', x.2)) * Δ (b', x.2) y - Ap (b', x.2) * M (b', x.2) y - 𝔛 (b', x.2) y))
    (hX : ∀ u y, ‖𝔛 u y‖ ≤ Real.sqrt (2 * P) * ((1 + 2 / (κ * c₀)) * GreenCore_T d L W c₀ ρ S P φ u.1 y.1 +
      Real.sqrt 13 / κ * δ * ‖Δ u y‖))
    (hXi : ∀ w, ‖Ap w‖ ≤ Real.sqrt 13 / κ * δ * (1 + Real.sqrt (2 * P)) * GreenCore_T d L W c₀ ρ S P φ w.1 w.1 +
      Real.sqrt (2 * P) * φ w.1 w.1 + Real.sqrt (P * ((W : ℝ) ^ d)⁻¹) +
      Real.sqrt (2 * P) * ((1 + 2 / (κ * c₀)) * Real.exp (c₀ / 4) * (2 * d * g₀) * GreenCore_T d L W c₀ ρ S P φ w.1 w.1 +
        Real.sqrt 13 / κ * δ * ∑ l, ‖D l w‖ * ‖Δ w l‖))
    (hA : ∀ w, ‖(t : ℂ) * vb w.1 - Ap w‖ ≤ α)
    (hD1 : ∀ w, ∑ l, ‖D l w‖ = 2 * d * g₀) (hDadj : ∀ l w, D l w ≠ 0 → zdistD d L (w.1 - l.1) = 1)
    (hN : ∀ x y, ‖Δ x y‖ ≤ N * GreenOff_T d L γ Ψ φ x.1 y.1) (hN0 : 0 ≤ N) (x y : Vtx d L W) :
    ‖Δ x y - ∑ b', Mb x.1 b' * ((t : ℂ) * vb b' * M (b', x.2) y)‖ ≤
      (c₀⁻¹ * S * (GreenOff_sA d κ c₀ ρ S P δ g₀ / c₀ + GreenOff_sX κ c₀ ρ S P) +
        c₀⁻¹ * S * GreenOff_eta d κ c₀ P δ g₀ γ α * N) * GreenOff_T d L γ Ψ φ x.1 y.1 := by
  have hγ2 : γ ≤ c₀ / 2 := by linarith
  have hα0 : 0 ≤ α := le_trans (norm_nonneg _) (hA x)
  have hsX := GreenOff_sX_nonneg (ρ := ρ) (S := S) (P := P) hκ hc₀
  have hsA := GreenOff_sA_nonneg (d := d) (ρ := ρ) (S := S) (P := P) hκ hc₀ hδ0 hg
  have heX := GreenOff_eX_nonneg (P := P) hκ hδ0
  have heP : 0 ≤ 2 * d * g₀ * Real.exp γ * GreenOff_eX κ P δ := by positivity
  have hR : Δ x y - ∑ b', Mb x.1 b' * ((t : ℂ) * vb b' * M (b', x.2) y) =
      ∑ b', Mb x.1 b' * (((t : ℂ) * vb b' - Ap (b', x.2)) * Δ (b', x.2) y - Ap (b', x.2) * M (b', x.2) y -
        𝔛 (b', x.2) y) := by
    rw [hE3 x y, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b' _ => ?_
    ring
  rw [hR]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ b' : Zd d L, ‖Mb x.1 b' * (((t : ℂ) * vb b' - Ap (b', x.2)) * Δ (b', x.2) y -
        Ap (b', x.2) * M (b', x.2) y - 𝔛 (b', x.2) y)‖ ≤
      ‖Mb x.1 b'‖ * ((α * N + (GreenOff_sX κ c₀ ρ S P + GreenOff_eX κ P δ * N)) * GreenOff_T d L γ Ψ φ b' y.1) +
        (‖Mb x.1 b'‖ * ‖Mb b' y.1‖) * ((GreenOff_sA d κ c₀ ρ S P δ g₀ + 2 * d * g₀ * Real.exp γ * GreenOff_eX κ P δ * N) *
          GreenOff_T d L γ Ψ φ b' b') := by
    intro b'
    rw [norm_mul]
    have h1 : ‖((t : ℂ) * vb b' - Ap (b', x.2)) * Δ (b', x.2) y‖ ≤ α * (N * GreenOff_T d L γ Ψ φ b' y.1) := by
      rw [norm_mul]
      exact mul_le_mul (hA (b', x.2)) (hN (b', x.2) y) (norm_nonneg _) hα0
    have h2 : ‖Ap (b', x.2) * M (b', x.2) y‖ ≤ ((GreenOff_sA d κ c₀ ρ S P δ g₀ +
        2 * d * g₀ * Real.exp γ * GreenOff_eX κ P δ * N) * GreenOff_T d L γ Ψ φ b' b') * ‖Mb b' y.1‖ := by
      rw [norm_mul]
      refine mul_le_mul (GreenOff_Ap_bd hc₀ hS0 hγ0 hγ hφ hΨ hΨw hP hκ hδ0 hg hXi hD1 hDadj hN hN0 (b', x.2)) ?_
        (norm_nonneg _) (by have := GreenOff_T_nonneg (γ := γ) hφ hΨ.le b' b'; positivity)
      rw [hM]
      split_ifs
      · exact le_rfl
      · simp
    have h3 := GreenOff_X_bd hc₀ hS0 hγ hφ hΨ hΨw hκ hδ0 hX hN hN0 (b', x.2) y
    have h4 : ‖((t : ℂ) * vb b' - Ap (b', x.2)) * Δ (b', x.2) y - Ap (b', x.2) * M (b', x.2) y - 𝔛 (b', x.2) y‖ ≤
        ‖((t : ℂ) * vb b' - Ap (b', x.2)) * Δ (b', x.2) y‖ + ‖Ap (b', x.2) * M (b', x.2) y‖ + ‖𝔛 (b', x.2) y‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    calc ‖Mb x.1 b'‖ * ‖((t : ℂ) * vb b' - Ap (b', x.2)) * Δ (b', x.2) y - Ap (b', x.2) * M (b', x.2) y -
          𝔛 (b', x.2) y‖ ≤ ‖Mb x.1 b'‖ * (α * (N * GreenOff_T d L γ Ψ φ b' y.1) +
            ((GreenOff_sA d κ c₀ ρ S P δ g₀ + 2 * d * g₀ * Real.exp γ * GreenOff_eX κ P δ * N) *
              GreenOff_T d L γ Ψ φ b' b') * ‖Mb b' y.1‖ +
            (GreenOff_sX κ c₀ ρ S P + GreenOff_eX κ P δ * N) * GreenOff_T d L γ Ψ φ b' y.1) :=
          mul_le_mul_of_nonneg_left (h4.trans (add_le_add (add_le_add h1 h2) h3)) (norm_nonneg _)
      _ = _ := by ring
  refine (Finset.sum_le_sum fun b' _ => hterm b').trans ?_
  have hc1 : 0 ≤ α * N + (GreenOff_sX κ c₀ ρ S P + GreenOff_eX κ P δ * N) := by positivity
  have hc2 : 0 ≤ GreenOff_sA d κ c₀ ρ S P δ g₀ + 2 * d * g₀ * Real.exp γ * GreenOff_eX κ P δ * N := by positivity
  have hA1 := GreenOff_convA (Mb := Mb) (φ := φ) hc₀ hγ0 hγ2 hφ hΨ.le hdec hS x.1 y.1
  have hB1 := GreenOff_convB (Mb := Mb) (φ := φ) hc₀ hγ0 hγ2 hφ hΨ.le hdec hS x.1 y.1
  calc ∑ b', (‖Mb x.1 b'‖ * ((α * N + (GreenOff_sX κ c₀ ρ S P + GreenOff_eX κ P δ * N)) * GreenOff_T d L γ Ψ φ b' y.1) +
        (‖Mb x.1 b'‖ * ‖Mb b' y.1‖) * ((GreenOff_sA d κ c₀ ρ S P δ g₀ + 2 * d * g₀ * Real.exp γ * GreenOff_eX κ P δ * N) *
          GreenOff_T d L γ Ψ φ b' b'))
      = (α * N + (GreenOff_sX κ c₀ ρ S P + GreenOff_eX κ P δ * N)) * ∑ b', ‖Mb x.1 b'‖ * GreenOff_T d L γ Ψ φ b' y.1 +
        (GreenOff_sA d κ c₀ ρ S P δ g₀ + 2 * d * g₀ * Real.exp γ * GreenOff_eX κ P δ * N) *
          ∑ b', ‖Mb x.1 b'‖ * ‖Mb b' y.1‖ * GreenOff_T d L γ Ψ φ b' b' := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        congr 1 <;> exact Finset.sum_congr rfl fun b' _ => by ring
    _ ≤ (α * N + (GreenOff_sX κ c₀ ρ S P + GreenOff_eX κ P δ * N)) * (c₀⁻¹ * S * GreenOff_T d L γ Ψ φ x.1 y.1) +
        (GreenOff_sA d κ c₀ ρ S P δ g₀ + 2 * d * g₀ * Real.exp γ * GreenOff_eX κ P δ * N) *
          (c₀⁻¹ * S * c₀⁻¹ * GreenOff_T d L γ Ψ φ x.1 y.1) :=
        add_le_add (mul_le_mul_of_nonneg_left hA1 hc1) (mul_le_mul_of_nonneg_left hB1 hc2)
    _ = _ := by unfold GreenOff_eta; field_simp; ring

/-- `v̄ = Θ u`: from `(1 - t M^{(+,+)}) v̄ = u` (`M^{(+,+)}_{ab} = M_{ba} M_{ab}`) and `Θ = 1 + t Θ M^{(+,+)}`. -/
theorem GreenOff_vb_theta {Θ : Matrix (Zd d L) (Zd d L) ℂ} {u : Zd d L → ℂ}
    (hΘ : ∀ b a, Θ b a = (if b = a then 1 else 0) + (t : ℂ) * ∑ c, Θ b c * (Mb a c * Mb c a))
    (h : ∀ a, vb a - (t : ℂ) * ∑ b, (Mb b a * Mb a b) * vb b = u a) (b : Zd d L) :
    vb b = ∑ a, Θ b a * u a := by
  have key : ∀ b' : Zd d L, (t : ℂ) * ∑ a, Θ b a * (Mb b' a * Mb a b') = Θ b b' - (if b = b' then 1 else 0) := by
    intro b'; rw [hΘ b b']; ring
  have e2 : ∑ a, Θ b a * ((t : ℂ) * ∑ b', (Mb b' a * Mb a b') * vb b') =
      ∑ b', (Θ b b' - if b = b' then 1 else 0) * vb b' := by
    calc ∑ a, Θ b a * ((t : ℂ) * ∑ b', (Mb b' a * Mb a b') * vb b')
        = ∑ b', ((t : ℂ) * ∑ a, Θ b a * (Mb b' a * Mb a b')) * vb b' := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun a _ => by ring
      _ = _ := Finset.sum_congr rfl fun b' _ => by rw [key b']
  have e1 : ∑ a, Θ b a * u a = ∑ a, Θ b a * vb a - ∑ b', (Θ b b' - if b = b' then 1 else 0) * vb b' := by
    rw [← e2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [← h a]; ring
  rw [e1]
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- **The `Θ` step** (`L3`): if the remainder `R = Δ - L3` satisfies `|R| ≤ K 𝔗`, then `|Δ| ≤ (1 + ρ̂ c₀⁻¹ C_Θ̂) K 𝔗`, with
`v̄ = Θ u` (the block averages), `u_a = W^{-d} Σ_{k∈a} R_{kk}`, the weighted `ℓ¹` bound `Σ_{a'} |Θ_{ba'}| e^{2γ|b-a'|} ≤ C_Θ̂` and
the kernel preservation (`GreenOff_convB`). -/
theorem GreenOff_theta_step {Θ : Matrix (Zd d L) (Zd d L) ℂ} {CΘ K : ℝ}
    (hc₀ : 0 < c₀) (hγ0 : 0 ≤ γ) (hγ : γ ≤ c₀ / 4) (hφ : ∀ a b, 0 ≤ φ a b) (hΨ : 0 < Ψ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hdec : ∀ a b, ‖Mb a b‖ ≤ c₀⁻¹ * Real.exp (-c₀ * (zdistD d L (a - b) : ℝ)))
    (hS : ∀ a, ∑ b, Real.exp (-(c₀ / 2) * (zdistD d L (a - b) : ℝ)) ≤ S)
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0)
    (hvb : ∀ a, vb a = (((W : ℝ) ^ d)⁻¹ : ℝ) * ∑ o, Δ (a, o) (a, o))
    (hΘ : ∀ b a, Θ b a = (if b = a then 1 else 0) + (t : ℂ) * ∑ c, Θ b c * (Mb a c * Mb c a))
    (hΘw : ∀ b, ∑ a', ‖Θ b a'‖ * Real.exp (2 * γ * (zdistD d L (b - a') : ℝ)) ≤ CΘ)
    (hR : ∀ x y : Vtx d L W, ‖Δ x y - ∑ b', Mb x.1 b' * ((t : ℂ) * vb b' * M (b', x.2) y)‖ ≤
      K * GreenOff_T d L γ Ψ φ x.1 y.1) (x y : Vtx d L W) :
    ‖Δ x y‖ ≤ (1 + c₀⁻¹ * S * c₀⁻¹ * CΘ) * K * GreenOff_T d L γ Ψ φ x.1 y.1 := by
  have hw := GreenCore_w_pos (d := d) (W := W)
  have hγ2 : γ ≤ c₀ / 2 := by linarith
  have hT0 : ∀ a c, 0 ≤ GreenOff_T d L γ Ψ φ a c := fun a c => GreenOff_T_nonneg hφ hΨ.le a c
  have hK0 : 0 ≤ K :=
    (mul_nonneg_iff_of_pos_right (GreenOff_T_pos hφ hΨ x.1 y.1)).1 ((norm_nonneg _).trans (hR x y))
  have hCΘ0 : 0 ≤ CΘ := (Finset.sum_nonneg fun a _ => by positivity).trans (hΘw x.1)
  set Rm : Vtx d L W → Vtx d L W → ℂ :=
    fun x y => Δ x y - ∑ b', Mb x.1 b' * ((t : ℂ) * vb b' * M (b', x.2) y) with hRm
  set u : Zd d L → ℂ := fun a => (((W : ℝ) ^ d)⁻¹ : ℝ) * ∑ o, Rm (a, o) (a, o) with hu
  have hu_bd : ∀ a, ‖u a‖ ≤ K * GreenOff_T d L γ Ψ φ a a := by
    intro a
    rw [hu]; dsimp only
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw.le]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hw.le).trans (GreenCore_avg_le fun o => ?_)
    exact hR (a, o) (a, o)
  have h3 : (((W : ℝ) ^ d)⁻¹ : ℝ) * ((W ^ d : ℕ) : ℂ) = 1 := by
    have := GreenCore_w_mul (d := d) (W := W)
    exact_mod_cast this
  have hvb_eq : ∀ a, vb a - (t : ℂ) * ∑ b, (Mb b a * Mb a b) * vb b = u a := by
    intro a
    have hM' : ∀ (b' : Zd d L) (o : Fin (W ^ d)), M (b', o) (a, o) = Mb b' a := fun b' o => by simp [hM]
    have h1 : ∀ o : Fin (W ^ d), Rm (a, o) (a, o) =
        Δ (a, o) (a, o) - ∑ b', Mb a b' * ((t : ℂ) * vb b' * Mb b' a) := fun o => by
      simp only [hRm, hM']
    have h2 : ∑ o, Rm (a, o) (a, o) = ∑ o, Δ (a, o) (a, o) -
        ((W ^ d : ℕ) : ℂ) * ∑ b', Mb a b' * ((t : ℂ) * vb b' * Mb b' a) := by
      simp only [h1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hu]; dsimp only
    rw [h2, mul_sub, ← mul_assoc, h3, one_mul, ← hvb a]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hvbΘ := GreenOff_vb_theta (Mb := Mb) (vb := vb) hΘ hvb_eq
  have hvb_bd : ∀ b, ‖vb b‖ ≤ K * CΘ * GreenOff_T d L γ Ψ φ b b := by
    intro b
    rw [hvbΘ b]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a, ‖Θ b a * u a‖ ≤ ∑ a, ‖Θ b a‖ * (Real.exp (2 * γ * (zdistD d L (b - a) : ℝ)) *
          (K * GreenOff_T d L γ Ψ φ b b)) := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [norm_mul]
          have h1 := GreenOff_T_shift hγ0 hφ hΨ.le b a b a
          refine mul_le_mul_of_nonneg_left ((hu_bd a).trans ?_) (norm_nonneg _)
          calc K * GreenOff_T d L γ Ψ φ a a ≤ K * (Real.exp (γ * ((zdistD d L (b - a) : ℝ) + (zdistD d L (b - a) : ℝ))) *
                GreenOff_T d L γ Ψ φ b b) := mul_le_mul_of_nonneg_left h1 hK0
            _ = _ := by rw [show γ * ((zdistD d L (b - a) : ℝ) + (zdistD d L (b - a) : ℝ)) =
                2 * γ * (zdistD d L (b - a) : ℝ) by ring]; ring
      _ = (∑ a, ‖Θ b a‖ * Real.exp (2 * γ * (zdistD d L (b - a) : ℝ))) * (K * GreenOff_T d L γ Ψ φ b b) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun a _ => by ring
      _ ≤ CΘ * (K * GreenOff_T d L γ Ψ φ b b) := mul_le_mul_of_nonneg_right (hΘw b) (mul_nonneg hK0 (hT0 b b))
      _ = _ := by ring
  have hB1 := GreenOff_convB (Mb := Mb) (φ := φ) hc₀ hγ0 hγ2 hφ hΨ.le hdec hS x.1 y.1
  have hL3 : ‖∑ b', Mb x.1 b' * ((t : ℂ) * vb b' * M (b', x.2) y)‖ ≤
      c₀⁻¹ * S * c₀⁻¹ * CΘ * K * GreenOff_T d L γ Ψ φ x.1 y.1 := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ b', ‖Mb x.1 b' * ((t : ℂ) * vb b' * M (b', x.2) y)‖
        ≤ ∑ b', ‖Mb x.1 b'‖ * ‖Mb b' y.1‖ * ((K * CΘ) * GreenOff_T d L γ Ψ φ b' b') := by
          refine Finset.sum_le_sum fun b' _ => ?_
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
          have hM1 : ‖M (b', x.2) y‖ ≤ ‖Mb b' y.1‖ := by
            rw [hM]; split_ifs
            · exact le_rfl
            · simp
          have h4 := mul_le_mul (mul_le_mul ht1 (hvb_bd b') (norm_nonneg _) zero_le_one) hM1 (norm_nonneg _)
            (mul_nonneg zero_le_one (mul_nonneg (mul_nonneg hK0 hCΘ0) (hT0 b' b')))
          calc ‖Mb x.1 b'‖ * (t * ‖vb b'‖ * ‖M (b', x.2) y‖)
              ≤ ‖Mb x.1 b'‖ * (1 * (K * CΘ * GreenOff_T d L γ Ψ φ b' b') * ‖Mb b' y.1‖) :=
                mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
            _ = _ := by ring
      _ = (K * CΘ) * ∑ b', ‖Mb x.1 b'‖ * ‖Mb b' y.1‖ * GreenOff_T d L γ Ψ φ b' b' := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b' _ => by ring
      _ ≤ (K * CΘ) * (c₀⁻¹ * S * c₀⁻¹ * GreenOff_T d L γ Ψ φ x.1 y.1) :=
          mul_le_mul_of_nonneg_left hB1 (mul_nonneg hK0 hCΘ0)
      _ = _ := by ring
  calc ‖Δ x y‖ = ‖(Δ x y - ∑ b', Mb x.1 b' * ((t : ℂ) * vb b' * M (b', x.2) y)) +
        ∑ b', Mb x.1 b' * ((t : ℂ) * vb b' * M (b', x.2) y)‖ := by rw [sub_add_cancel]
    _ ≤ _ := norm_add_le _ _
    _ ≤ K * GreenOff_T d L γ Ψ φ x.1 y.1 + c₀⁻¹ * S * c₀⁻¹ * CΘ * K * GreenOff_T d L γ Ψ φ x.1 y.1 :=
        add_le_add (hR x y) hL3
    _ = _ := by ring

/-- **Target 1: the deterministic weighted closure (D3.4)**, abstract form.  Data: the block kernel `M^{(B)} = Mb` with
`|Mb_{ab}| ≤ c₀⁻¹ e^{-c₀|a-b|}` and `max_a Σ_b e^{-(c₀/2)|a-b|} ≤ S` (so `ρ̂ = c₀⁻¹ S`), `M = Mb ⊗ I`; the array `Δ = G - M`, the sources
`𝔛` (`GreenCore_Xrow`) and `𝒜' = A + t v̄` (`GreenCore_Arow + t GreenCore_vbar`), the block averages `v̄_a = W^{-d} Σ_{k∈a} Δ_{kk}`; the
equation (E3) in the form `Δ_{xy} = Σ_{b'} M_{[x]b'} [t v̄_{b'} M_{wy} + (t v̄_{b'} - 𝒜'_w) Δ_{wy} - 𝒜'_w M_{wy} - 𝔛_{wy}]`, `w = (b', o_x)`;
the pointwise bounds (X*) `hX`, (Ξ) `hXi` (the conclusions of `GreenCore_Xstar`, `GreenCore_Xi`) and (A*) `hA` (`|A_w| ≤ α`);
the propagator `Θ = (1 - t M^{(+,+)})⁻¹` through `Θ = 1 + t Θ M^{(+,+)}` and its weighted `ℓ¹` bound with the constant `C_Θ̂` (`baTheta_weighted_l1`);
the loop control `φ ≥ 0` and `Ψ ≥ W^{-d/2}`, `Ψ > 0`; and absorption (C2) `(1 + ρ̂ c₀⁻¹ C_Θ̂) ρ̂ η ≤ 1/2`.  Conclusion: `|Δ_{xy}| ≤ 2 C_ℓ' Φ_N 𝔗_γ([x],[y])`
for all `x, y` (the diagonal included: it feeds `v̄`). -/
theorem GreenOff_close {Θ : Matrix (Zd d L) (Zd d L) ℂ} {CΘ : ℝ}
    (hc₀ : 0 < c₀) (hγ0 : 0 ≤ γ) (hγ : γ ≤ c₀ / 4) (hφ : ∀ a b, 0 ≤ φ a b)
    (hΨ : 0 < Ψ) (hΨw : Real.sqrt (((W : ℝ) ^ d)⁻¹) ≤ Ψ) (hP : 0 ≤ P) (hκ : 0 < κ) (hδ0 : 0 ≤ δ) (hg : 0 ≤ g₀)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hdec : ∀ a b, ‖Mb a b‖ ≤ c₀⁻¹ * Real.exp (-c₀ * (zdistD d L (a - b) : ℝ)))
    (hS : ∀ a, ∑ b, Real.exp (-(c₀ / 2) * (zdistD d L (a - b) : ℝ)) ≤ S)
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0)
    (hvb : ∀ a, vb a = (((W : ℝ) ^ d)⁻¹ : ℝ) * ∑ o, Δ (a, o) (a, o))
    (hE3 : ∀ x y, Δ x y = ∑ b', Mb x.1 b' * ((t : ℂ) * vb b' * M (b', x.2) y +
      ((t : ℂ) * vb b' - Ap (b', x.2)) * Δ (b', x.2) y - Ap (b', x.2) * M (b', x.2) y - 𝔛 (b', x.2) y))
    (hX : ∀ u y, ‖𝔛 u y‖ ≤ Real.sqrt (2 * P) * ((1 + 2 / (κ * c₀)) * GreenCore_T d L W c₀ ρ S P φ u.1 y.1 +
      Real.sqrt 13 / κ * δ * ‖Δ u y‖))
    (hXi : ∀ w, ‖Ap w‖ ≤ Real.sqrt 13 / κ * δ * (1 + Real.sqrt (2 * P)) * GreenCore_T d L W c₀ ρ S P φ w.1 w.1 +
      Real.sqrt (2 * P) * φ w.1 w.1 + Real.sqrt (P * ((W : ℝ) ^ d)⁻¹) +
      Real.sqrt (2 * P) * ((1 + 2 / (κ * c₀)) * Real.exp (c₀ / 4) * (2 * d * g₀) * GreenCore_T d L W c₀ ρ S P φ w.1 w.1 +
        Real.sqrt 13 / κ * δ * ∑ l, ‖D l w‖ * ‖Δ w l‖))
    (hA : ∀ w, ‖(t : ℂ) * vb w.1 - Ap w‖ ≤ α)
    (hD1 : ∀ w, ∑ l, ‖D l w‖ = 2 * d * g₀) (hDadj : ∀ l w, D l w ≠ 0 → zdistD d L (w.1 - l.1) = 1)
    (hΘ : ∀ b a, Θ b a = (if b = a then 1 else 0) + (t : ℂ) * ∑ c, Θ b c * (Mb a c * Mb c a))
    (hΘw : ∀ b, ∑ a', ‖Θ b a'‖ * Real.exp (2 * γ * (zdistD d L (b - a') : ℝ)) ≤ CΘ)
    (hC2 : (1 + c₀⁻¹ * S * c₀⁻¹ * CΘ) * (c₀⁻¹ * S * GreenOff_eta d κ c₀ P δ g₀ γ α) ≤ 1 / 2)
    (x y : Vtx d L W) :
    ‖Δ x y‖ ≤ 2 * GreenOff_Cl d κ c₀ ρ S P δ g₀ CΘ * GreenOff_T d L γ Ψ φ x.1 y.1 := by
  have hS0 : 0 ≤ S := (Finset.sum_nonneg fun b _ => (Real.exp_pos _).le).trans (hS 0)
  have hTpos : ∀ a c, 0 < GreenOff_T d L γ Ψ φ a c := fun a c => GreenOff_T_pos hφ hΨ a c
  obtain ⟨p₀, hp₀⟩ := Finite.exists_max
    (fun p : Vtx d L W × Vtx d L W => ‖Δ p.1 p.2‖ / GreenOff_T d L γ Ψ φ p.1.1 p.2.1)
  set N := ‖Δ p₀.1 p₀.2‖ / GreenOff_T d L γ Ψ φ p₀.1.1 p₀.2.1 with hNdef
  have hN : ∀ x y, ‖Δ x y‖ ≤ N * GreenOff_T d L γ Ψ φ x.1 y.1 := fun x y => by
    have := hp₀ (x, y)
    simp only at this
    rwa [div_le_iff₀ (hTpos _ _)] at this
  have hN0 : 0 ≤ N := div_nonneg (norm_nonneg _) (hTpos _ _).le
  have hRb := fun x y => GreenOff_R_bd hc₀ hS0 hγ0 hγ hφ hΨ hΨw hP hκ hδ0 hg hdec hS hM hE3 hX hXi hA hD1 hDadj hN hN0 x y
  have hTh := GreenOff_theta_step hc₀ hγ0 hγ hφ hΨ ht0 ht1 hdec hS hM hvb hΘ hΘw hRb p₀.1 p₀.2
  have hEq : ‖Δ p₀.1 p₀.2‖ = N * GreenOff_T d L γ Ψ φ p₀.1.1 p₀.2.1 := by
    rw [hNdef, div_mul_cancel₀ _ (hTpos _ _).ne']
  rw [hEq] at hTh
  have hN2 := le_of_mul_le_mul_right hTh (hTpos _ _)
  have hfin : N ≤ 2 * ((1 + c₀⁻¹ * S * c₀⁻¹ * CΘ) *
      (c₀⁻¹ * S * (GreenOff_sA d κ c₀ ρ S P δ g₀ / c₀ + GreenOff_sX κ c₀ ρ S P))) := by
    nlinarith [mul_le_mul_of_nonneg_right hC2 hN0]
  calc ‖Δ x y‖ ≤ N * GreenOff_T d L γ Ψ φ x.1 y.1 := hN x y
    _ ≤ 2 * ((1 + c₀⁻¹ * S * c₀⁻¹ * CΘ) * (c₀⁻¹ * S * (GreenOff_sA d κ c₀ ρ S P δ g₀ / c₀ + GreenOff_sX κ c₀ ρ S P))) *
        GreenOff_T d L γ Ψ φ x.1 y.1 := mul_le_mul_of_nonneg_right hfin (hTpos _ _).le
    _ = _ := by unfold GreenOff_Cl; ring

/-! ### The carrier form: (A*) in the row form, and the closure at the BA data -/

/-- `α = (2/κ) δ (2 d g₀ + (1 + 2 d g₀)/κ)`: the bound of `|A_w|` (A*). -/
def GreenOff_alpha (d : ℕ) (κ δ g₀ : ℝ) : ℝ := (2 / κ) * (δ * (2 * d * g₀ + (1 + 2 * d * g₀) / κ))

/-- **(A\*), row form** (`GreenCore_Acol_sq` is the column form): `(X + t m) G = -(D - s)(G - M)`, so `A_w G_{ww} = -Σ_l (D - s)_{wl} Δ_{lw}` and
`|A_w| ≤ (2/κ) δ (2 d g₀ + |s|)`, `|s| κ ≤ 1 + 2 d g₀`. -/
theorem GreenOff_Arow_bd {G X M D : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Matrix (Zd d L) (Zd d L) ℂ} {m s z : ℂ}
    {κ δ t g₀ : ℝ} (hL : 3 ≤ L) (hg : 0 ≤ g₀) (hκ : 0 < κ)
    (hGR : G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1)
    (hRG : (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1)
    (hMR : (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * M = 1) (hz : z = s - (t : ℂ) * m)
    (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hMd : ∀ a, Mb a a = m)
    (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0)
    (hκm : κ ≤ ‖m‖) (hMb1 : ∀ a b, ‖Mb a b‖ ≤ 1) (hGuu : ∀ u, κ / 2 ≤ ‖G u u‖)
    (hΩ : ∀ u v, ‖G u v - M u v‖ ≤ δ) (w : Vtx d L W) :
    ‖GreenCore_Arow G X D t m w‖ ≤ GreenOff_alpha d κ δ g₀ := by
  have hG0 : ∀ u, G u u ≠ 0 := fun u h => by have := hGuu u; rw [h, norm_zero] at this; linarith
  have hD1 : ∑ l, ‖D w l‖ = 2 * d * g₀ := GreenCore_Drow (W := W) hg hL hD w
  have hM1 : ∀ u v, ‖M u v‖ ≤ 1 := fun u v => by rw [hM]; split_ifs <;> simp [hMb1]
  have hs : ‖s‖ * κ ≤ 2 * d * g₀ + 1 := by
    have h1 := congrFun (congrFun hMR w) w
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    have h2 : ∑ l, (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) w l * M l w = ∑ l, D w l * M l w - s * m := by
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
        ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [show M w w = m by rw [hM]; simp [hMd]]
    have h4 : ‖s‖ * ‖m‖ ≤ 2 * d * g₀ + 1 := by
      rw [← norm_mul, show s * m = ∑ l, D w l * M l w - 1 by rw [h2] at h1; linear_combination -h1]
      refine (norm_sub_le _ _).trans (add_le_add ((norm_sum_le _ _).trans ?_) norm_one.le)
      calc ∑ l, ‖D w l * M l w‖ ≤ ∑ l, ‖D w l‖ * 1 :=
            Finset.sum_le_sum fun l _ => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hM1 _ _) (norm_nonneg _)
        _ = 2 * d * g₀ := by simp [hD1]
    nlinarith [norm_nonneg s]
  have hYG : (X + ((t : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G =
      -((D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * (G - M)) := by
    have e : X + ((t : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
        (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) - (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) := by
      rw [hz]; module
    calc (X + ((t : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G =
          ((D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) - (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ))) * G := by
          rw [e]
      _ = 1 - (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G := by rw [sub_mul, hRG]
      _ = _ := by rw [mul_sub, hMR]; abel
  have h1 : ((X + ((t : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G) w w =
      GreenCore_Arow G X D t m w * G w w := by
    have e1 := GreenCore_E1 (X := X) hGR w w (hG0 w)
    have e2 : ((X + ((t : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G) w w =
        ∑ v, X w v * G v w + (t : ℂ) * m * G w w := by
      rw [Matrix.mul_apply]
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single w (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp
    have e3 : ∑ v ∈ Finset.univ.erase w, X w v * greenMinor G w v w = 0 :=
      Finset.sum_eq_zero fun v _ => by rw [GreenCore_minor_right (hG0 w), mul_zero]
    rw [e2, e1, e3]; unfold GreenCore_Arow; ring
  have hA : ‖GreenCore_Arow G X D t m w‖ * (κ / 2) ≤ δ * (2 * d * g₀ + ‖s‖) := by
    have h2 : ‖GreenCore_Arow G X D t m w * G w w‖ ≤ δ * (2 * d * g₀ + ‖s‖) := by
      rw [← h1, hYG, Matrix.neg_apply, norm_neg, Matrix.mul_apply]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ l, ‖(D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) w l * (G - M) l w‖
          ≤ ∑ l, (‖D w l‖ + ‖s‖ * (if w = l then 1 else 0)) * δ := Finset.sum_le_sum fun l _ => by
            rw [norm_mul]
            refine mul_le_mul ?_ (by simpa using hΩ l w) (norm_nonneg _) (by positivity)
            simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
            split_ifs with h
            · subst h; simpa using norm_sub_le (D w w) (s * 1)
            · simp
        _ = δ * (2 * d * g₀ + ‖s‖) := by
            rw [← Finset.sum_mul, Finset.sum_add_distrib, hD1]; simp [Finset.sum_ite_eq]; ring
    rw [norm_mul] at h2
    nlinarith [mul_le_mul_of_nonneg_left (hGuu w) (norm_nonneg (GreenCore_Arow G X D t m w))]
  have hsκ : ‖s‖ ≤ (1 + 2 * d * g₀) / κ := by
    rw [le_div_iff₀ hκ]; linarith [hs]
  unfold GreenOff_alpha
  rw [show (2 / κ) * (δ * (2 * d * g₀ + (1 + 2 * d * g₀) / κ)) = (δ * (2 * d * g₀ + (1 + 2 * d * g₀) / κ)) / (κ / 2) by
    field_simp, le_div_iff₀ (by positivity)]
  exact hA.trans (mul_le_mul_of_nonneg_left (by linarith) (le_trans (norm_nonneg _) (hΩ w w)))

/-- `S = expC (d-2) (c₀/2) ≥ max_a Σ_b e^{-(c₀/2)|a-b|}`, `c₀ = BAct_rate d Λ κ` (`BAsum_exp_decay_le`). -/
def GreenOff_S (d : ℕ) (Λ κ : ℝ) : ℝ := expC (d - 2) (BAct_rate d Λ κ / 2)

/-- `ρ = c₀⁻¹ expC (d-2) c₀ ≥ max_c Σ_b |M_{bc}|` (`baM_col_l1`). -/
def GreenOff_rho (d : ℕ) (Λ κ : ℝ) : ℝ := (BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ)

/-- **The closure at the BA carrier** (the deterministic core of `(GijGEX_BA)`): for one sample, on `Ω = {‖G - M‖_max ≤ δ}` and the four
large deviation events (`LDERow`, `LDECol`, `LDEQuad`, the diagonal) with the factor `P = Φ_N`, and the loop control
`GreenCore_loop G a b ≤ φ(a,b)²`: `|(G - M)_{xy}| ≤ 2 C_ℓ' Φ_N 𝔗_{c_λ}([x],[y])`, with `c₀ = BAct_rate d Λ κ`, `c_λ = GreenStab_clam d Λ κ`,
`C_Θ̂ = GreenStab_CTheta d Λ κ`, `ρ`, `S` as above, under (C1) and (C2).  The sources are `GreenCore_Xstar`, `GreenCore_Xi`, `GreenOff_Arow_bd`,
the stability is `Θ = BATheta … t true true` with `baTheta_weighted_l1`; `GreenOff_close` closes. -/
theorem GreenOff_decay (hd : 2 ≤ d) (hL : 3 ≤ L)
    {Λ g₀ κ E t δ P Ψ : ℝ} {m s z : ℂ} {G X M D : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hΛ : 0 < Λ) (hg : 0 < g₀) (hgΛ : g₀ ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g₀ κ E m)
    (hGR : G * (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1)
    (hRG : (D + X - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1)
    (hMR : (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * M = 1)
    (hMR' : M * (D - s • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1) (hz : z = s - (t : ℂ) * m)
    (hM : ∀ u v, M u v = if u.2 = v.2 then BAMB d L g₀ (E : ℂ) m u.1 v.1 else 0)
    (hD : ∀ u l, D u l = if u.2 = l.2 ∧ Adj d L u.1 l.1 then (g₀ : ℂ) else 0)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hP : 1 ≤ P) (hδ : δ ≤ κ / 2) (hδ0 : 0 ≤ δ) (hwd : ((W : ℝ) ^ d)⁻¹ ≤ δ ^ 2)
    (hΩ : ∀ u v, ‖G u v - M u v‖ ≤ δ)
    (hLrow : LDERow X G (svar d L W 0) P) (hLcol : LDECol X G (svar d L W 0) P)
    (hLquad : LDEQuad X G (svar d L W 0) t P) (hLdiag : ∀ i, ‖X i i‖ ^ 2 ≤ P * svar d L W 0 i i)
    (hC1 : 8 * GreenOff_rho d Λ κ * ((BAct_rate d Λ κ)⁻¹ * GreenOff_S d Λ κ) * GreenCore_theta d κ P δ g₀ ≤ 1)
    (φ : Zd d L → Zd d L → ℝ) (hφ0 : ∀ a b, 0 ≤ φ a b) (hφ : ∀ a b, GreenCore_loop G a b ≤ φ a b ^ 2)
    (hΨ : 0 < Ψ) (hΨw : Real.sqrt (((W : ℝ) ^ d)⁻¹) ≤ Ψ)
    (hC2 : (1 + (BAct_rate d Λ κ)⁻¹ * GreenOff_S d Λ κ * (BAct_rate d Λ κ)⁻¹ * GreenStab_CTheta d Λ κ) *
      ((BAct_rate d Λ κ)⁻¹ * GreenOff_S d Λ κ *
        GreenOff_eta d κ (BAct_rate d Λ κ) P δ g₀ (GreenStab_clam d Λ κ) (GreenOff_alpha d κ δ g₀)) ≤ 1 / 2)
    (x y : Vtx d L W) :
    ‖G x y - M x y‖ ≤ 2 * GreenOff_Cl d κ (BAct_rate d Λ κ) (GreenOff_rho d Λ κ) (GreenOff_S d Λ κ) P δ g₀
      (GreenStab_CTheta d Λ κ) * GreenOff_T d L (GreenStab_clam d Λ κ) Ψ φ x.1 y.1 := by
  have hd0 : 0 < d := by omega
  have hc₀ := BAct_rate_pos d Λ κ hd0 hΛ hκ
  have hdec : ∀ a b, ‖BAMB d L g₀ (E : ℂ) m a b‖ ≤
      (BAct_rate d Λ κ)⁻¹ * Real.exp (-BAct_rate d Λ κ * (zdistD d L (a - b) : ℝ)) :=
    fun a b => BAMB_decay_large d L hL hd0 Λ g₀ κ E m hΛ hg hgΛ hκ hr a b
  have hS : ∀ a : Zd d L, ∑ b, Real.exp (-(BAct_rate d Λ κ / 2) * (zdistD d L (a - b) : ℝ)) ≤ GreenOff_S d Λ κ :=
    fun a => by
      have := BAsum_exp_decay_le d L hd (BAct_rate d Λ κ / 2) (by positivity) a
      unfold GreenOff_S
      simpa only [neg_mul] using this
  have hMd : ∀ a, BAMB d L g₀ (E : ℂ) m a a = m := fun a => BAMB_diag_eq d L g₀ (E : ℂ) m hr.1 a
  have hMb1 : ∀ a b, ‖BAMB d L g₀ (E : ℂ) m a b‖ ≤ 1 := by
    intro a b
    have h1 := BAMB_row_sq_real d L g₀ E m hr.1 a
    have h2 : ‖BAMB d L g₀ (E : ℂ) m a b‖ ^ 2 ≤ 1 :=
      h1 ▸ Finset.single_le_sum (f := fun b => ‖BAMB d L g₀ (E : ℂ) m a b‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ b)
    nlinarith [norm_nonneg (BAMB d L g₀ (E : ℂ) m a b)]
  have hκm : κ ≤ ‖m‖ := hr.2.trans ((le_abs_self _).trans (Complex.abs_im_le_norm _))
  have hm1 : ‖m‖ ≤ 1 := BAm_norm_le_one d L g₀ (E : ℂ) m (by simp) hr.1
  have hρ : ∀ c, ∑ b, ‖BAMB d L g₀ (E : ℂ) m b c‖ ≤ GreenOff_rho d Λ κ :=
    fun c => baM_col_l1 hd hL Λ g₀ κ E m hΛ hg hgΛ hκ hr c
  obtain ⟨hGuu, hG32, hGoff⟩ := GreenCore_crude hM hMd hMb1 hκm hm1 hδ hΩ
  have hG0 : ∀ u, G u u ≠ 0 := fun u h => by have := hGuu u; rw [h, norm_zero] at this; linarith
  have hX := fun u y => GreenCore_Xstar hL hGR hRG hMR hMR' hz hM hMd hD hκ hκm hm1 hMb1 hc₀ hdec hρ hS hg.le hP hδ hδ0
    hwd hΩ hLrow hLcol hC1 φ hφ0 hφ u y
  have hXi := fun w => GreenCore_Xi hL hGR hRG hMR hMR' hz hM hMd hD hκ hκm hm1 hMb1 hc₀ hdec hρ hS hg.le ht0 ht1.le hP
    hδ hδ0 hwd hΩ hLrow hLcol hLquad hLdiag hC1 φ hφ0 hφ w
  have hD1 : ∀ w, ∑ l, ‖D l w‖ = 2 * d * g₀ := fun w => by
    simp only [← GreenCore_Dsymm hD w]; exact GreenCore_Drow (W := W) hg.le hL hD w
  have hDadj : ∀ l w, D l w ≠ 0 → zdistD d L (w.1 - l.1) = 1 := fun l w hDl => by
    rw [hD] at hDl; split_ifs at hDl with hc
    · rw [← neg_sub, zdistD_neg]; exact hc.2
    · exact absurd rfl hDl
  have hA : ∀ w : Vtx d L W, ‖(t : ℂ) * GreenCore_vbar G M w.1 -
      (GreenCore_Arow G X D t m w + (t : ℂ) * GreenCore_vbar G M w.1)‖ ≤ GreenOff_alpha d κ δ g₀ := fun w => by
    rw [show (t : ℂ) * GreenCore_vbar G M w.1 - (GreenCore_Arow G X D t m w + (t : ℂ) * GreenCore_vbar G M w.1) =
      -GreenCore_Arow G X D t m w by ring, norm_neg]
    exact GreenOff_Arow_bd hL hg.le hκ hGR hRG hMR hz hM hMd hD hκm hMb1 hGuu hΩ w
  have hE3 : ∀ x y : Vtx d L W, G x y - M x y = ∑ b', BAMB d L g₀ (E : ℂ) m x.1 b' *
      ((t : ℂ) * GreenCore_vbar G M b' * M (b', x.2) y +
        ((t : ℂ) * GreenCore_vbar G M b' - (GreenCore_Arow G X D t m (b', x.2) + (t : ℂ) * GreenCore_vbar G M (b', x.2).1)) *
          (G (b', x.2) y - M (b', x.2) y) -
        (GreenCore_Arow G X D t m (b', x.2) + (t : ℂ) * GreenCore_vbar G M (b', x.2).1) * M (b', x.2) y -
        GreenCore_Xrow G X (b', x.2) y) := by
    intro x y
    rw [GreenCore_E3 hGR hRG hMR' hz hM hG0 x y, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b' _ => ?_
    unfold GreenCore_K
    ring
  have hΘ : ∀ b a, BATheta d L g₀ E m t true true b a = (if b = a then 1 else 0) + (t : ℂ) *
      ∑ c, BATheta d L g₀ E m t true true b c * (BAMB d L g₀ (E : ℂ) m a c * BAMB d L g₀ (E : ℂ) m c a) := by
    intro b a
    have h := congrFun (congrFun (BATheta_resolvent d L g₀ κ E m hr t ht0 ht1 true true).2 b) a
    simpa [Matrix.mul_apply, Matrix.one_apply, BAMss, BAMsigma] using h
  have hγ0 := GreenStab_clam_pos d Λ κ hd0 hΛ hκ
  have hγ := GreenStab_clam_le_c0 d Λ κ
  exact GreenOff_close (Mb := BAMB d L g₀ (E : ℂ) m) (M := M) (D := D) (Δ := fun u v => G u v - M u v)
    (𝔛 := GreenCore_Xrow G X) (Ap := fun w => GreenCore_Arow G X D t m w + (t : ℂ) * GreenCore_vbar G M w.1)
    (vb := GreenCore_vbar G M) hc₀ hγ0.le (by linarith) hφ0 hΨ hΨw (by linarith) hκ hδ0 hg.le ht0 ht1.le hdec hS hM
    (fun a => rfl) hE3 hX hXi hA hD1 hDadj hΘ
    (fun b => baTheta_weighted_l1 hd hL Λ g₀ κ E m hΛ hg hgΛ hκ hr t ht0 ht1.le true b) hC2 x y

end Close

/-! ## 3. Target 2: the link `BAStab` -/

/-- **Target 2**: `BAStab d L g E m t (16 κ⁻⁴)` at the bulk data `BAReal d L g κ E m`, `0 ≤ t ≤ 1` (the body of `BAStab` is
`baStab_of_real`, `GreenStab.lean:46`). -/
theorem baStab_holds (d L : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : BAStab d L g E m t (16 * κ⁻¹ ^ 4) :=
  baStab_of_real d L g κ E m hκ hr t ht0 ht1

/-! ## 4. The carrier: the two-loop in the entries and the closure at the flow -/

section Carrier

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem GreenOff_gres_blockMat_true (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) (x y : Vtx d L W) :
    Gres (blockMat d L W H) z true x y =
      Gres H z true ((splitEquiv d L W).symm x) ((splitEquiv d L W).symm y) := by
  unfold Gres blockMat
  simp only [ite_true]
  have e1 : H.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
      (H - z • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)).submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply]
  rw [e1, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse, Matrix.inv_submatrix_equiv]
  rfl

omit [NeZero L] [NeZero W] in
private theorem GreenOff_gres_false {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (z : ℂ) : Gres H z false = (Gres H z true)ᴴ := by
  unfold Gres
  simp only [Bool.false_eq_true, ite_false, ite_true]
  rw [← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse, Matrix.conjTranspose_nonsing_inv]
  congr 1
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH.eq]
  rfl

omit [NeZero W] in
private theorem GreenOff_trace_pm (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a b : Zd d L) :
    ((G * Eblk d L W a) * (Gᴴ * Eblk d L W b)).trace =
      ((((W : ℝ) ^ d)⁻¹ ^ 2 * ∑ v : Vtx d L W, ∑ w : Vtx d L W,
          (if v.1 = b ∧ w.1 = a then ‖G v w‖ ^ 2 else 0) : ℝ) : ℂ) := by
  have hE : ∀ c : Zd d L, Eblk d L W c = Matrix.diagonal fun x : Vtx d L W =>
      if x.1 = c then (((W : ℂ)) ^ d)⁻¹ else 0 := fun c => rfl
  rw [hE a, hE b]
  have h1 : G * Matrix.diagonal (fun x : Vtx d L W => if x.1 = a then (((W : ℂ)) ^ d)⁻¹ else 0) =
      Matrix.of fun i j => G i j * (if j.1 = a then (((W : ℂ)) ^ d)⁻¹ else 0) := by
    ext i j; simp [Matrix.mul_diagonal]
  have h2 : Gᴴ * Matrix.diagonal (fun x : Vtx d L W => if x.1 = b then (((W : ℂ)) ^ d)⁻¹ else 0) =
      Matrix.of fun i j => star (G j i) * (if j.1 = b then (((W : ℂ)) ^ d)⁻¹ else 0) := by
    ext i j; simp [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  rw [h1, h2]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hi : i.1 = b <;> by_cases hj : j.1 = a <;> simp [hi, hj]
  have h := Complex.mul_conj' (G i j)
  linear_combination (((W : ℂ) ^ d)⁻¹) ^ 2 * h

private theorem GreenOff_sum_vtx_ite (F : Vtx d L W → ℝ) (b : Zd d L) :
    ∑ v : Vtx d L W, (if v.1 = b then F v else 0) = ∑ β : Fin (W ^ d), F (b, β) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
  · simp
  · intro x _ hx
    simp [hx]
  · intro hb
    exact absurd (Finset.mem_univ b) hb

/-- **The two-loop in the entries**: for a Hermitian `H`, `‖𝓛^{(2)}_{(-,+),(a,b)}‖ = W^{-2d} Σ_{x∈a, y∈b} |G_{xy}|²`
(rows in block `a`, columns in `b`), `G = (H - z)⁻¹` on the block-product index (the merged proofs of this identity are
private to `Green/Pins.lean`). -/
theorem GreenOff_loop_eq {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (z : ℂ) (a b : Zd d L) :
    ‖loopFine d L W H z ![false, true] ![a, b]‖ =
      GreenCore_loop (blockMat d L W (Gres H z true)) a b := by
  have hB : (blockMat d L W H).IsHermitian := hH.submatrix _
  have hGb : Gres (blockMat d L W H) z true = blockMat d L W (Gres H z true) := by
    ext x y; exact GreenOff_gres_blockMat_true H z x y
  have h1 : loopFine d L W H z ![false, true] ![a, b] =
      ((blockMat d L W (Gres H z true) * Eblk d L W b) * ((blockMat d L W (Gres H z true))ᴴ * Eblk d L W a)).trace := by
    unfold loopFine loopM
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, Matrix.cons_val_zero,
      Matrix.cons_val_succ]
    rw [GreenOff_gres_false _ hB z, hGb, Matrix.trace_mul_comm]
  rw [h1, GreenOff_trace_pm, Complex.norm_real]
  have h2 : ∀ v : Vtx d L W, (∑ w : Vtx d L W, if v.1 = a ∧ w.1 = b then
      ‖blockMat d L W (Gres H z true) v w‖ ^ 2 else 0) =
      if v.1 = a then ∑ w : Vtx d L W, (if w.1 = b then ‖blockMat d L W (Gres H z true) v w‖ ^ 2 else 0) else 0 :=
    fun v => by by_cases hv : v.1 = a <;> simp [hv]
  have hsum : (∑ v : Vtx d L W, ∑ w : Vtx d L W, if v.1 = a ∧ w.1 = b then
      ‖blockMat d L W (Gres H z true) v w‖ ^ 2 else 0) =
      ∑ o : Fin (W ^ d), ∑ o' : Fin (W ^ d), ‖blockMat d L W (Gres H z true) (a, o) (b, o')‖ ^ 2 := by
    simp only [h2]
    rw [GreenOff_sum_vtx_ite (fun v => ∑ w : Vtx d L W, (if w.1 = b then
      ‖blockMat d L W (Gres H z true) v w‖ ^ 2 else 0)) a]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [GreenOff_sum_vtx_ite (fun w => ‖blockMat d L W (Gres H z true) (a, o) w‖ ^ 2) b]
  rw [hsum, Real.norm_of_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => by positivity))]
  rfl

end Carrier

section PinDet

variable {d : ℕ}

/-- **The closure along the flow, one sample** (`n`, `ω`): on `Ω = {‖G_t - M‖_max ≤ δ}`, the large deviation events at the factor
`P = Φ_N` and the loop control `‖𝓛^{(2)}_{(-,+),(a,b)}‖ ≤ φ(a,b)²`:
`|(G_t - M)_{xy}| ≤ 2 C_ℓ' Φ_N 𝔗_{c_λ}([x],[y])` with the constants of `(κ, 𝔡)` (`Λ = 𝔡⁻¹`, `GreenOff_decay`). -/
theorem GreenOff_carrier_decay (hd : 2 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) {z : ℕ → ℂ}
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ BAflowT0 sz z n) (ω : sz.SeqΩ)
    {P δ Ψ : ℝ} {φ : Zd d (sz.L n) → Zd d (sz.L n) → ℝ}
    (hg : 0 < BAflowLam0 sz z n) (hgΛ : BAflowLam0 sz z n ≤ 𝔡⁻¹)
    (hP : 1 ≤ P) (hδ : δ ≤ κ / 2) (hδ0 : 0 ≤ δ) (hwd : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ δ ^ 2)
    (hΩ : ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z).GM n t ω x y‖ ≤ δ)
    (hLrow : LDERow (GreenCore_Xc sz n t ω) (GreenCore_Gc sz z n t ω) (svar d (sz.L n) (sz.W n) 0) P)
    (hLcol : LDECol (GreenCore_Xc sz n t ω) (GreenCore_Gc sz z n t ω) (svar d (sz.L n) (sz.W n) 0) P)
    (hLquad : LDEQuad (GreenCore_Xc sz n t ω) (GreenCore_Gc sz z n t ω) (svar d (sz.L n) (sz.W n) 0) t P)
    (hLdiag : ∀ i, ‖GreenCore_Xc sz n t ω i i‖ ^ 2 ≤ P * svar d (sz.L n) (sz.W n) 0 i i)
    (hC1 : 8 * GreenOff_rho d 𝔡⁻¹ κ * ((BAct_rate d 𝔡⁻¹ κ)⁻¹ * GreenOff_S d 𝔡⁻¹ κ) *
      GreenCore_theta d κ P δ (BAflowLam0 sz z n) ≤ 1)
    (hφ0 : ∀ a b, 0 ≤ φ a b) (hφ : ∀ a b, ‖(baFMz sz z).L n t ![false, true] ![a, b] ω‖ ≤ φ a b ^ 2)
    (hΨ : 0 < Ψ) (hΨw : Real.sqrt ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ≤ Ψ)
    (hC2 : (1 + (BAct_rate d 𝔡⁻¹ κ)⁻¹ * GreenOff_S d 𝔡⁻¹ κ * (BAct_rate d 𝔡⁻¹ κ)⁻¹ * GreenStab_CTheta d 𝔡⁻¹ κ) *
      ((BAct_rate d 𝔡⁻¹ κ)⁻¹ * GreenOff_S d 𝔡⁻¹ κ *
        GreenOff_eta d κ (BAct_rate d 𝔡⁻¹ κ) P δ (BAflowLam0 sz z n) (GreenStab_clam d 𝔡⁻¹ κ)
          (GreenOff_alpha d κ δ (BAflowLam0 sz z n))) ≤ 1 / 2)
    (x y : Idx d (sz.L n) (sz.W n)) :
    ‖(baFMz sz z).GM n t ω x y‖ ≤ 2 * GreenOff_Cl d κ (BAct_rate d 𝔡⁻¹ κ) (GreenOff_rho d 𝔡⁻¹ κ) (GreenOff_S d 𝔡⁻¹ κ) P δ
      (BAflowLam0 sz z n) (GreenStab_CTheta d 𝔡⁻¹ κ) *
      GreenOff_T d (sz.L n) (GreenStab_clam d 𝔡⁻¹ κ) Ψ φ (Sizes.STblk sz n x) (Sizes.STblk sz n y) := by
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 hflow.1.2.1
  obtain ⟨ht1, hr, hmi, hzi, -, -⟩ := ba_G_data hκ sz hflow n ht0 htT
  obtain ⟨hGR, hRG, hMR, hMR', hz, hM, hMd, hD, hG0⟩ := GreenCore_carrier hκ sz hflow n ht0 htT ω
    (m := BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
    (s := (BAflowEs sz z n : ℂ) + BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
    (zt := ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t) rfl rfl rfl
  have hHerm : (sz.seqHflowBA (BAflowLam0 sz z) n t ω).IsHermitian := by
    unfold Sizes.seqHflowBA
    refine IsHermitian.add ?_ (Sizes.seqHflow_isHermitian (sz.withLam 0) n t ω)
    unfold IsHermitian
    rw [conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
      show star (BAflowLam0 sz z n : ℂ) = (BAflowLam0 sz z n : ℂ) from Complex.conj_ofReal _]
  have hloop : ∀ a b, GreenCore_loop (GreenCore_Gc sz z n t ω) a b ≤ φ a b ^ 2 := fun a b =>
    le_trans (le_of_eq (GreenOff_loop_eq hHerm (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t) a b).symm)
      (hφ a b)
  have hΩ' : ∀ u v : Vtx d (sz.L n) (sz.W n),
      ‖GreenCore_Gc sz z n t ω u v - GreenCore_Mc sz z n u v‖ ≤ δ := fun u v =>
    hΩ ((splitEquiv d (sz.L n) (sz.W n)).symm u) ((splitEquiv d (sz.L n) (sz.W n)).symm v)
  have key := GreenOff_decay hd (sz.three_le_L n) (Λ := 𝔡⁻¹) (g₀ := BAflowLam0 sz z n) (κ := κ) (E := BAflowEs sz z n)
    (t := t) (δ := δ) (P := P) (Ψ := Ψ) hΛ hg hgΛ hκ hr hGR hRG hMR hMR' hz hM hD ht0 ht1 hP hδ hδ0 hwd hΩ' hLrow hLcol
    hLquad hLdiag hC1 φ hφ0 hloop hΨ hΨw hC2 (splitEquiv d (sz.L n) (sz.W n) x) (splitEquiv d (sz.L n) (sz.W n) y)
  have e : (baFMz sz z).GM n t ω x y = GreenCore_Gc sz z n t ω (splitEquiv d (sz.L n) (sz.W n) x)
      (splitEquiv d (sz.L n) (sz.W n) y) - GreenCore_Mc sz z n (splitEquiv d (sz.L n) (sz.W n) x)
      (splitEquiv d (sz.L n) (sz.W n) y) := by
    simp [FlowFM.GM, baFMz, baFM, GreenCore_Gc, GreenCore_Mc, blockMat]
  rw [e]
  exact key

end PinDet

/-! ### The dependence on `Φ_N` and on the coupling: polynomial bounds -/

section Numerics

variable {d : ℕ}

theorem GreenOff_eta_le {κ c₀ P δ g₀ γ Λ : ℝ} (hκ : 0 < κ) (hc₀ : 0 < c₀) (hP : 1 ≤ P) (hδ0 : 0 ≤ δ) (hg0 : 0 ≤ g₀)
    (hgΛ : g₀ ≤ Λ) :
    GreenOff_eta d κ c₀ P δ g₀ γ (GreenOff_alpha d κ δ g₀) ≤
      ((2 / κ) * (2 * d * Λ + (1 + 2 * d * Λ) / κ) +
        Real.sqrt 2 * Real.sqrt 13 / κ * (1 + 2 * d * Λ * Real.exp γ / c₀)) * (Real.sqrt P * δ) := by
  have ha : 1 ≤ Real.sqrt P := Real.one_le_sqrt.2 hP
  have e2 : Real.sqrt (2 * P) = Real.sqrt 2 * Real.sqrt P := Real.sqrt_mul (by norm_num) P
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hq : 2 * (d : ℝ) * g₀ + (1 + 2 * d * g₀) / κ ≤ 2 * d * Λ + (1 + 2 * d * Λ) / κ := by
    have := div_le_div_of_nonneg_right (show 1 + 2 * (d : ℝ) * g₀ ≤ 1 + 2 * d * Λ by nlinarith) hκ.le
    nlinarith
  have hq0 : 0 ≤ 2 * (d : ℝ) * Λ + (1 + 2 * d * Λ) / κ := by
    have : 0 ≤ Λ := hg0.trans hgΛ
    positivity
  have h1 : δ * (2 * d * g₀ + (1 + 2 * d * g₀) / κ) ≤ Real.sqrt P * (δ * (2 * d * Λ + (1 + 2 * d * Λ) / κ)) :=
    (mul_le_mul_of_nonneg_left hq hδ0).trans (by nlinarith [mul_nonneg hδ0 hq0])
  have hex : 0 ≤ Real.sqrt 2 * Real.sqrt P * (Real.sqrt 13 / κ * δ) := by positivity
  have h2' : 2 * (d : ℝ) * g₀ * Real.exp γ * (Real.sqrt 2 * Real.sqrt P * (Real.sqrt 13 / κ * δ)) ≤
      2 * d * Λ * Real.exp γ * (Real.sqrt 2 * Real.sqrt P * (Real.sqrt 13 / κ * δ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_pos _).le) hex
  have h2 : 2 * (d : ℝ) * g₀ * Real.exp γ * (Real.sqrt 2 * Real.sqrt P * (Real.sqrt 13 / κ * δ)) / c₀ ≤
      2 * d * Λ * Real.exp γ / c₀ * (Real.sqrt 2 * Real.sqrt P * (Real.sqrt 13 / κ * δ)) := by
    rw [div_mul_eq_mul_div (2 * (d : ℝ) * Λ * Real.exp γ) c₀ (Real.sqrt 2 * Real.sqrt P * (Real.sqrt 13 / κ * δ))]
    exact div_le_div_of_nonneg_right h2' hc₀.le
  unfold GreenOff_eta GreenOff_alpha GreenOff_eX
  rw [e2]
  calc _ ≤ 2 / κ * (Real.sqrt P * (δ * (2 * d * Λ + (1 + 2 * d * Λ) / κ))) +
        Real.sqrt 2 * Real.sqrt P * (Real.sqrt 13 / κ * δ) +
        2 * d * Λ * Real.exp γ / c₀ * (Real.sqrt 2 * Real.sqrt P * (Real.sqrt 13 / κ * δ)) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity)) le_rfl) h2
    _ = _ := by ring

theorem GreenOff_theta_le {κ P δ g₀ Λ : ℝ} (hκ : 0 < κ) (hP : 1 ≤ P) (hg0 : 0 ≤ g₀) (hgΛ : g₀ ≤ Λ) :
    GreenCore_theta d κ P δ g₀ ≤
      ((4 / κ ^ 2) * (2 * d * Λ + (1 + 2 * d * Λ) / κ) ^ 2 + 26 / κ ^ 2) * (P * δ ^ 2) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hq : 2 * (d : ℝ) * g₀ + (1 + 2 * d * g₀) / κ ≤ 2 * d * Λ + (1 + 2 * d * Λ) / κ := by
    have := div_le_div_of_nonneg_right (show 1 + 2 * (d : ℝ) * g₀ ≤ 1 + 2 * d * Λ by nlinarith) hκ.le
    nlinarith
  have hq0 : 0 ≤ 2 * (d : ℝ) * g₀ + (1 + 2 * d * g₀) / κ := by positivity
  have h1 : (2 * (d : ℝ) * g₀ + (1 + 2 * d * g₀) / κ) ^ 2 ≤ (2 * d * Λ + (1 + 2 * d * Λ) / κ) ^ 2 :=
    pow_le_pow_left₀ hq0 hq 2
  unfold GreenCore_theta
  have h2 : (4 / κ ^ 2) * (2 * (d : ℝ) * g₀ + (1 + 2 * d * g₀) / κ) ^ 2 * δ ^ 2 ≤
      (4 / κ ^ 2) * (2 * d * Λ + (1 + 2 * d * Λ) / κ) ^ 2 * (P * δ ^ 2) := by
    have h3 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 4 / κ ^ 2 by positivity)
    have h4 : δ ^ 2 ≤ P * δ ^ 2 := by nlinarith [sq_nonneg δ]
    calc _ ≤ (4 / κ ^ 2) * (2 * d * Λ + (1 + 2 * d * Λ) / κ) ^ 2 * δ ^ 2 :=
          mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)
  nlinarith

theorem GreenOff_CT_le {c₀ ρ S P : ℝ} (hc₀ : 0 < c₀) (hP : 1 ≤ P) :
    GreenOff_CT c₀ ρ S P ≤ Real.sqrt P * GreenOff_CT c₀ ρ S 1 := by
  have ha : 1 ≤ Real.sqrt P := Real.one_le_sqrt.2 hP
  have e : Real.sqrt (16 * ρ * P * c₀⁻¹ * S) = Real.sqrt P * Real.sqrt (16 * ρ * 1 * c₀⁻¹ * S) := by
    rw [← Real.sqrt_mul (by linarith)]; congr 1; ring
  unfold GreenOff_CT
  rw [e]
  have h0 : 0 ≤ 2 * c₀⁻¹ * Real.sqrt S := by positivity
  nlinarith [mul_le_mul_of_nonneg_right ha h0]

theorem GreenOff_sX_le {κ c₀ ρ S P : ℝ} (hκ : 0 < κ) (hc₀ : 0 < c₀) (hP : 1 ≤ P) :
    GreenOff_sX κ c₀ ρ S P ≤ P * GreenOff_sX κ c₀ ρ S 1 := by
  have hCT := GreenOff_CT_le (ρ := ρ) (S := S) hc₀ hP
  have e2 : Real.sqrt (2 * P) = Real.sqrt 2 * Real.sqrt P := Real.sqrt_mul (by norm_num) P
  have ePP : Real.sqrt P * Real.sqrt P = P := Real.mul_self_sqrt (by linarith)
  unfold GreenOff_sX
  rw [e2, mul_one 2]
  calc Real.sqrt 2 * Real.sqrt P * (1 + 2 / (κ * c₀)) * GreenOff_CT c₀ ρ S P ≤
        Real.sqrt 2 * Real.sqrt P * (1 + 2 / (κ * c₀)) * (Real.sqrt P * GreenOff_CT c₀ ρ S 1) :=
        mul_le_mul_of_nonneg_left hCT (by positivity)
    _ = (Real.sqrt P * Real.sqrt P) * (Real.sqrt 2 * (1 + 2 / (κ * c₀)) * GreenOff_CT c₀ ρ S 1) := by ring
    _ = _ := by rw [ePP]

theorem GreenOff_sA_le {κ c₀ ρ S P δ g₀ Λ : ℝ} (hκ : 0 < κ) (hc₀ : 0 < c₀) (hP : 1 ≤ P) (hδ0 : 0 ≤ δ) (hδ : δ ≤ κ / 2)
    (hg0 : 0 ≤ g₀) (hgΛ : g₀ ≤ Λ) :
    GreenOff_sA d κ c₀ ρ S P δ g₀ ≤ P * GreenOff_sA d κ c₀ ρ S 1 (κ / 2) Λ := by
  have hCT := GreenOff_CT_le (ρ := ρ) (S := S) hc₀ hP
  have hCT0 := GreenOff_CT_nonneg (ρ := ρ) (S := S) (P := 1) hc₀
  have ha : 1 ≤ Real.sqrt P := Real.one_le_sqrt.2 hP
  have e2 : Real.sqrt (2 * P) = Real.sqrt 2 * Real.sqrt P := Real.sqrt_mul (by norm_num) P
  have ePP : Real.sqrt P * Real.sqrt P = P := Real.mul_self_sqrt (by linarith)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hΛ0 : 0 ≤ Λ := hg0.trans hgΛ
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hu : 0 ≤ Real.sqrt 13 / κ := by positivity
  have hv : 0 ≤ (1 + 2 / (κ * c₀)) * Real.exp (c₀ / 4) := by positivity
  have hv' : (1 + 2 / (κ * c₀)) * Real.exp (c₀ / 4) * (2 * d * g₀) ≤ (1 + 2 / (κ * c₀)) * Real.exp (c₀ / 4) * (2 * d * Λ) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hv
  have hv0 : 0 ≤ (1 + 2 / (κ * c₀)) * Real.exp (c₀ / 4) * (2 * d * Λ) := by positivity
  have hpa : Real.sqrt P ≤ P := by nlinarith
  have e1 : Real.sqrt (2 * 1) = Real.sqrt 2 := by rw [mul_one]
  have hb : Real.sqrt 13 / κ * δ * (1 + Real.sqrt 2 * Real.sqrt P) + Real.sqrt 2 * Real.sqrt P *
      ((1 + 2 / (κ * c₀)) * Real.exp (c₀ / 4) * (2 * d * g₀)) ≤
      Real.sqrt P * (Real.sqrt 13 / κ * (κ / 2) * (1 + Real.sqrt 2) + Real.sqrt 2 *
        ((1 + 2 / (κ * c₀)) * Real.exp (c₀ / 4) * (2 * d * Λ))) := by
    have h1 : Real.sqrt 13 / κ * δ ≤ Real.sqrt 13 / κ * (κ / 2) := mul_le_mul_of_nonneg_left hδ hu
    have h2 := mul_le_mul h1 (show 1 + Real.sqrt 2 * Real.sqrt P ≤ Real.sqrt P * (1 + Real.sqrt 2) by nlinarith)
      (by positivity) (by positivity)
    have h3 := mul_le_mul_of_nonneg_left hv' (mul_nonneg hs2 (Real.sqrt_nonneg P))
    nlinarith
  unfold GreenOff_sA
  rw [e2, e1, Real.sqrt_one]
  set Z : ℝ := Real.sqrt 13 / κ * (κ / 2) * (1 + Real.sqrt 2) + Real.sqrt 2 *
    ((1 + 2 / (κ * c₀)) * Real.exp (c₀ / 4) * (2 * d * Λ)) with hZ
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  calc (Real.sqrt 13 / κ * δ * (1 + Real.sqrt 2 * Real.sqrt P) + Real.sqrt 2 * Real.sqrt P *
        ((1 + 2 / (κ * c₀)) * Real.exp (c₀ / 4) * (2 * d * g₀))) * GreenOff_CT c₀ ρ S P +
        Real.sqrt 2 * Real.sqrt P + Real.sqrt P
      ≤ (Real.sqrt P * Z) * (Real.sqrt P * GreenOff_CT c₀ ρ S 1) + (Real.sqrt 2 + 1) * P := by
        have := mul_le_mul hb hCT (GreenOff_CT_nonneg hc₀) (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left hpa (show 0 ≤ Real.sqrt 2 by positivity)]
    _ = P * (Z * GreenOff_CT c₀ ρ S 1 + Real.sqrt 2 + 1) := by
        have : (Real.sqrt P * Z) * (Real.sqrt P * GreenOff_CT c₀ ρ S 1) =
          (Real.sqrt P * Real.sqrt P) * (Z * GreenOff_CT c₀ ρ S 1) := by ring
        rw [this, ePP]; ring

theorem GreenOff_Cl_le {κ c₀ ρ S P δ g₀ Λ CΘ : ℝ} (hκ : 0 < κ) (hc₀ : 0 < c₀) (hP : 1 ≤ P) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ κ / 2) (hg0 : 0 ≤ g₀) (hgΛ : g₀ ≤ Λ) (hρh : 0 ≤ c₀⁻¹ * S) (hCΘ : 0 ≤ CΘ) :
    GreenOff_Cl d κ c₀ ρ S P δ g₀ CΘ ≤ P * GreenOff_Cl d κ c₀ ρ S 1 (κ / 2) Λ CΘ := by
  have h1 := GreenOff_sA_le (d := d) (ρ := ρ) (S := S) hκ hc₀ hP hδ0 hδ hg0 hgΛ
  have h2 := GreenOff_sX_le (ρ := ρ) (S := S) hκ hc₀ hP
  have hA : 0 ≤ 1 + c₀⁻¹ * S * c₀⁻¹ * CΘ := by positivity
  unfold GreenOff_Cl
  calc (1 + c₀⁻¹ * S * c₀⁻¹ * CΘ) * (c₀⁻¹ * S * (GreenOff_sA d κ c₀ ρ S P δ g₀ / c₀ + GreenOff_sX κ c₀ ρ S P)) ≤
        (1 + c₀⁻¹ * S * c₀⁻¹ * CΘ) * (c₀⁻¹ * S * (P * GreenOff_sA d κ c₀ ρ S 1 (κ / 2) Λ / c₀ +
          P * GreenOff_sX κ c₀ ρ S 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add
          (div_le_div_of_nonneg_right h1 hc₀.le) h2) hρh) hA
    _ = _ := by ring

end Numerics

/-! ### The kernel against the printed right side of `(GijGEX_BA)` and the constants of `(κ, 𝔡)` -/

section Pin

variable {d : ℕ}

theorem GreenOff_T_scale {L : ℕ} [NeZero L] {γ Ψ s : ℝ} {Φ : Zd d L → Zd d L → ℝ} (hs : 1 ≤ s) (hΦ : ∀ a b, 0 ≤ Φ a b)
    (hΨ : 0 ≤ Ψ) (a c : Zd d L) :
    GreenOff_T d L γ Ψ (fun a b => s * Φ a b) a c ≤ s * GreenOff_T d L γ Ψ Φ a c := by
  unfold GreenOff_T
  rw [mul_add, Finset.mul_sum]
  refine add_le_add (le_of_eq (Finset.sum_congr rfl fun a' _ => ?_)) ?_
  · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b' _ => by ring
  · have := mul_nonneg hΨ (Real.exp_pos (-γ * (zdistD d L (a - c) : ℝ))).le
    nlinarith

/-- `𝔗_γ ≤` the printed right side `Σ Φ e^{-γ(…)} + Ψ e^{-γ|a-b|} + W^{-D}` of `(GijGEX_BA)` (`zdistInf ≤ zdistD`). -/
theorem GreenOff_T_le_decayRHS {L W : ℕ} [NeZero L] {γ D Ψ : ℝ} {Φ : Zd d L → Zd d L → ℝ} (hγ : 0 ≤ γ)
    (hΦ : ∀ a b, 0 ≤ Φ a b) (hΨ : 0 ≤ Ψ) (a b : Zd d L) :
    GreenOff_T d L γ Ψ Φ a b ≤ GreenCore_decayRHS d L W γ D Φ Ψ a b := by
  have hi : ∀ x : Zd d L, -γ * (zdistD d L x : ℝ) ≤ -γ * (zdistInf d L x : ℝ) := fun x => by
    nlinarith [mul_le_mul_of_nonneg_left (show (zdistInf d L x : ℝ) ≤ zdistD d L x by
      exact_mod_cast zdistInf_le_zdistD d L x) hγ]
  unfold GreenOff_T GreenCore_decayRHS
  have h0 : 0 ≤ (W : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h1 : (∑ a' : Zd d L, ∑ b' : Zd d L, Φ a' b' *
      Real.exp (-γ * ((zdistD d L (a' - a) : ℝ) + (zdistD d L (b' - b) : ℝ)))) ≤
      ∑ a' : Zd d L, ∑ b' : Zd d L, Φ a' b' *
        Real.exp (-γ * ((zdistInf d L (a' - a) : ℝ) + (zdistInf d L (b' - b) : ℝ))) :=
    Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun b' _ => mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by
      nlinarith [mul_le_mul_of_nonneg_left (show (zdistInf d L (a' - a) : ℝ) + zdistInf d L (b' - b) ≤
        zdistD d L (a' - a) + zdistD d L (b' - b) by
          exact_mod_cast add_le_add (zdistInf_le_zdistD d L _) (zdistInf_le_zdistD d L _)) hγ])) (hΦ _ _)
  have h2 : Ψ * Real.exp (-γ * (zdistD d L (a - b) : ℝ)) ≤ Ψ * Real.exp (-γ * (zdistInf d L (a - b) : ℝ)) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hi _)) hΨ
  linarith

/-- **The constants of the pin**: there are `ε', K` such that whenever `1 ≤ P`, `0 ≤ δ`, `0 ≤ g₀ ≤ Λ` and `√P δ ≤ ε'`, the conditions
`δ ≤ κ/2`, (C1), (C2) hold and `2 C_ℓ' Φ_N ≤ K Φ_N`. -/
theorem GreenOff_pin_consts_gen {κ c₀ ρ S CΘ γ Λ : ℝ} (hκ : 0 < κ) (hΛ : 0 < Λ) (hc₀ : 0 < c₀) (hρ0 : 0 ≤ ρ) (hS0 : 0 ≤ S)
    (hCΘ0 : 0 ≤ CΘ) :
    ∃ ε' Kcl : ℝ, 0 < ε' ∧ 0 ≤ Kcl ∧ ∀ P δ g₀ : ℝ, 1 ≤ P → 0 ≤ δ → 0 ≤ g₀ → g₀ ≤ Λ → Real.sqrt P * δ ≤ ε' →
      δ ≤ κ / 2 ∧ 8 * ρ * (c₀⁻¹ * S) * GreenCore_theta d κ P δ g₀ ≤ 1 ∧
      (1 + c₀⁻¹ * S * c₀⁻¹ * CΘ) * (c₀⁻¹ * S * GreenOff_eta d κ c₀ P δ g₀ γ (GreenOff_alpha d κ δ g₀)) ≤ 1 / 2 ∧
      2 * GreenOff_Cl d κ c₀ ρ S P δ g₀ CΘ ≤ Kcl * P := by
  have hρh : 0 ≤ c₀⁻¹ * S := mul_nonneg (inv_nonneg.2 hc₀.le) hS0
  have hA : 0 ≤ c₀⁻¹ * S * c₀⁻¹ * CΘ := by positivity
  obtain ⟨Keta, hKeta0, hKeta⟩ : ∃ Keta : ℝ, 0 ≤ Keta ∧ Keta = (2 / κ) * (2 * d * Λ + (1 + 2 * d * Λ) / κ) +
      Real.sqrt 2 * Real.sqrt 13 / κ * (1 + 2 * d * Λ * Real.exp γ / c₀) := ⟨_, by positivity, rfl⟩
  obtain ⟨Kθ, hKθ0, hKθ⟩ : ∃ Kθ : ℝ, 0 ≤ Kθ ∧ Kθ = (4 / κ ^ 2) * (2 * d * Λ + (1 + 2 * d * Λ) / κ) ^ 2 + 26 / κ ^ 2 :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨K₁, hK₁0, hK₁⟩ : ∃ K₁ : ℝ, 0 ≤ K₁ ∧ K₁ = 8 * ρ * (c₀⁻¹ * S) * Kθ := ⟨_, by positivity, rfl⟩
  obtain ⟨K₂, hK₂0, hK₂⟩ : ∃ K₂ : ℝ, 0 ≤ K₂ ∧ K₂ = (1 + c₀⁻¹ * S * c₀⁻¹ * CΘ) * (c₀⁻¹ * S) * Keta :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨Kcl, hKcl0, hKcl⟩ : ∃ Kcl : ℝ, 0 ≤ Kcl ∧ Kcl = 2 * GreenOff_Cl d κ c₀ ρ S 1 (κ / 2) Λ CΘ := by
    have h1 := GreenOff_sA_nonneg (d := d) (ρ := ρ) (S := S) (P := 1) (δ := κ / 2) (g₀ := Λ) hκ hc₀ (by positivity) hΛ.le
    have h2 := GreenOff_sX_nonneg (ρ := ρ) (S := S) (P := 1) hκ hc₀
    exact ⟨2 * GreenOff_Cl d κ c₀ ρ S 1 (κ / 2) Λ CΘ, by unfold GreenOff_Cl; positivity, rfl⟩
  refine ⟨min (κ / 2) (min (1 / (2 * (K₂ + 1))) (1 / (K₁ + 1))), Kcl,
    lt_min (by positivity) (lt_min (by positivity) (by positivity)), hKcl0, ?_⟩
  intro P δ g₀ hP hδ0 hg0 hgΛ hu
  have hu1 := hu.trans (min_le_left _ _)
  have hu2 := hu.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hu3 := hu.trans ((min_le_right _ _).trans (min_le_right _ _))
  rw [le_div_iff₀ (by positivity)] at hu2 hu3
  have ha : 1 ≤ Real.sqrt P := Real.one_le_sqrt.2 hP
  have hδu : δ ≤ Real.sqrt P * δ := by nlinarith
  have hδ : δ ≤ κ / 2 := hδu.trans hu1
  have hPδ : P * δ ^ 2 = (Real.sqrt P * δ) ^ 2 := by rw [mul_pow, Real.sq_sqrt (by linarith)]
  have hu0 : 0 ≤ Real.sqrt P * δ := by positivity
  refine ⟨hδ, ?_, ?_, ?_⟩
  · have h1 := mul_le_mul_of_nonneg_left (GreenOff_theta_le (d := d) (Λ := Λ) (δ := δ) hκ hP hg0 hgΛ) (by positivity :
      0 ≤ 8 * ρ * (c₀⁻¹ * S))
    have hu1' : Real.sqrt P * δ ≤ 1 := by linarith [mul_nonneg hK₁0 hu0]
    have h2 : (Real.sqrt P * δ) ^ 2 ≤ Real.sqrt P * δ := by nlinarith [mul_nonneg hu0 (sub_nonneg.2 hu1')]
    calc 8 * ρ * (c₀⁻¹ * S) * GreenCore_theta d κ P δ g₀ ≤ 8 * ρ * (c₀⁻¹ * S) * (Kθ * (P * δ ^ 2)) := by
          rw [hKθ]; exact h1
      _ = K₁ * (Real.sqrt P * δ) ^ 2 := by rw [hK₁, hPδ]; ring
      _ ≤ K₁ * (Real.sqrt P * δ) := mul_le_mul_of_nonneg_left h2 hK₁0
      _ ≤ 1 := by linarith
  · have h1 := GreenOff_eta_le (d := d) (γ := γ) (Λ := Λ) hκ hc₀ hP hδ0 hg0 hgΛ
    rw [← hKeta] at h1
    calc (1 + c₀⁻¹ * S * c₀⁻¹ * CΘ) * (c₀⁻¹ * S * GreenOff_eta d κ c₀ P δ g₀ γ (GreenOff_alpha d κ δ g₀)) ≤
          (1 + c₀⁻¹ * S * c₀⁻¹ * CΘ) * (c₀⁻¹ * S * (Keta * (Real.sqrt P * δ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hρh) (by positivity)
      _ = K₂ * (Real.sqrt P * δ) := by rw [hK₂]; ring
      _ ≤ 1 / 2 := by linarith
  · have := GreenOff_Cl_le (d := d) (ρ := ρ) (S := S) hκ hc₀ hP hδ0 hδ hg0 hgΛ hρh hCΘ0
    rw [hKcl]; linarith

theorem GreenOff_pin_consts (hd : 2 ≤ d) {κ 𝔡 : ℝ} (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) :
    ∃ ε' Kcl : ℝ, 0 < ε' ∧ 0 ≤ Kcl ∧ ∀ P δ g₀ : ℝ, 1 ≤ P → 0 ≤ δ → 0 ≤ g₀ → g₀ ≤ 𝔡⁻¹ → Real.sqrt P * δ ≤ ε' →
      δ ≤ κ / 2 ∧
      8 * GreenOff_rho d 𝔡⁻¹ κ * ((BAct_rate d 𝔡⁻¹ κ)⁻¹ * GreenOff_S d 𝔡⁻¹ κ) * GreenCore_theta d κ P δ g₀ ≤ 1 ∧
      (1 + (BAct_rate d 𝔡⁻¹ κ)⁻¹ * GreenOff_S d 𝔡⁻¹ κ * (BAct_rate d 𝔡⁻¹ κ)⁻¹ * GreenStab_CTheta d 𝔡⁻¹ κ) *
        ((BAct_rate d 𝔡⁻¹ κ)⁻¹ * GreenOff_S d 𝔡⁻¹ κ *
          GreenOff_eta d κ (BAct_rate d 𝔡⁻¹ κ) P δ g₀ (GreenStab_clam d 𝔡⁻¹ κ) (GreenOff_alpha d κ δ g₀)) ≤ 1 / 2 ∧
      2 * GreenOff_Cl d κ (BAct_rate d 𝔡⁻¹ κ) (GreenOff_rho d 𝔡⁻¹ κ) (GreenOff_S d 𝔡⁻¹ κ) P δ g₀
        (GreenStab_CTheta d 𝔡⁻¹ κ) ≤ Kcl * P := by
  have hd0 : 0 < d := by omega
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  have hc₀ := BAct_rate_pos d 𝔡⁻¹ κ hd0 hΛ hκ
  have hμ := BAp5s_rate_pos d 𝔡⁻¹ κ hd0 hΛ hκ
  have hC5 := BAp5s_C_pos d 𝔡⁻¹ κ hd0 hΛ hκ
  have hex : ∀ (k : ℕ) (c : ℝ), 0 < c → 0 < expC k c := fun k c hc => by unfold expC; positivity
  have hS0 : 0 ≤ GreenOff_S d 𝔡⁻¹ κ := (hex (d - 2) (BAct_rate d 𝔡⁻¹ κ / 2) (by positivity)).le
  have hρ0 : 0 ≤ GreenOff_rho d 𝔡⁻¹ κ :=
    mul_nonneg (inv_nonneg.2 hc₀.le) (hex (d - 2) (BAct_rate d 𝔡⁻¹ κ) hc₀).le
  have hCΘ0 : 0 ≤ GreenStab_CTheta d 𝔡⁻¹ κ := by
    unfold GreenStab_CTheta
    have := hex (d - 2) (2 * BAp5s_rate d 𝔡⁻¹ κ / 3) (by positivity)
    positivity
  exact GreenOff_pin_consts_gen hκ hΛ hc₀ hρ0 hS0 hCΘ0

end Pin

end RBM.BA
