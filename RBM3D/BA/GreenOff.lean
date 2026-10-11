/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GreenCore
import RBM3D.BA.GreenStab
import RBM3D.BA.GreenLDE

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

end Close

end RBM.BA
