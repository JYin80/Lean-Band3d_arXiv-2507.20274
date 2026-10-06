/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.JakSpectral
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# `RBM3D.Universality.JakKernel` (UN-20): the deterministic kernel layer of `(jaklsdufowe)`

Paper: arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex` (cited `1_2:line`), the proof of
`Thm: B_Univ` `1_2:566-581`, the weighted `y`-term of the pin `UNJak`.
Port of RBM2D `Universality/JakKernel.lean` (commit `c9a24cf`, 1121 lines) to `Idx d L W`,
`scirc d L W lam`, `N = (W L)^d`, the merged resolvent `Gres` (RBM2D `RBM.green`, `Gsig`) and the
merged UN-19 layer (`blockM d L W lam`, `siteBlock d L W`).

For a Hermitian matrix `H` on `Idx d L W`, per site `y`, this file bounds
`(∏_{j∈s} Im m(w_j)) |∑_x (G₁²)_{xx} S°_{xy} (G₂)_{yy}|` (the integrand of `UNJak`,
`Pins.lean:700-704`): the covering lemma (`sum_mass_window_le_im_green`,
`sum_mass_window_le_of_im_green_le`), the single-scale grid event `jakGridGood`, the bound on
the grid event (`jak_pointwise_good`), and the crude bound (`jak_pointwise_crude`), plus the
public `im_Gres_apply_self` (RBM2D `RBM.im_green_apply_self`, `Delocalization.lean:89`, outside
the closure).  Deterministic only: no pin is proved or stated; the file is `lam`-generic (band
data `sz.lam n`, model-generic data `K.lamV sz n`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Matrix
open RBM RBM.Gauss

namespace RBM.Univ

/-! ## 1. The covering lemma (generic index type) -/

section Generic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The imaginary part of the resolvent diagonal: for `0 < η`,
`Im Gres H (E + iη) true x x = ∑_l η |ψ_l(x)|² / ((λ_l - E)² + η²)` (RBM2D `RBM.im_green_apply_self`,
`Delocalization.lean:89`, `η ≠ 0` there; route `Gres_apply_self_spectral` at `σ = true`). -/
theorem im_Gres_apply_self {H : Matrix n n ℂ} (hH : H.IsHermitian) (E : ℝ) {η : ℝ}
    (hη : 0 < η) (x : n) :
    (Gres H (E + η * Complex.I) true x x).im =
      ∑ l, η * Complex.normSq (hH.eigenvectorBasis l x) / ((hH.eigenvalues l - E) ^ 2 + η ^ 2) := by
  have hz : 0 < ((E : ℂ) + η * Complex.I).im := by simpa using hη
  rw [Gres_apply_self_spectral hH hz true x, Complex.im_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hn : Complex.normSq ((hH.eigenvalues l : ℂ) - (E + η * Complex.I)) =
      (hH.eigenvalues l - E) ^ 2 + η ^ 2 := by
    rw [Complex.normSq_apply]
    simp
    ring
  have hi : ((hH.eigenvalues l : ℂ) - (E + η * Complex.I)).im = -η := by simp
  simp only [spectralGsigPole, spectralPole, ite_true, Complex.mul_im, Complex.inv_im, hi, hn,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero]
  ring

/-- Real core of the covering: every `a` with `|a - E₀| ≤ r` is within `η` of one of the
`⌈r/η⌉₊ + 1` centres `E₀ - r + 2ηj` (RBM1D `Step3KernelBounds.lean:40`). -/
private theorem JakKernel_covering_exists_center {η r E₀ a : ℝ} (hη : 0 < η)
    (ha : |a - E₀| ≤ r) :
    ∃ j ∈ Finset.range (⌈r / η⌉₊ + 1), |a - (E₀ - r + 2 * η * j)| ≤ η := by
  have hr : 0 ≤ r := (abs_nonneg _).trans ha
  set x : ℝ := (a - E₀ + r) / (2 * η) with hx
  have hx0 : 0 ≤ x := by
    rw [hx]; apply div_nonneg _ (by positivity); linarith [(abs_le.1 ha).1]
  have hxr : x ≤ r / η := by
    rw [hx, div_le_div_iff₀ (by positivity) hη]
    nlinarith [(abs_le.1 ha).2]
  set j : ℕ := ⌊x + 1 / 2⌋₊ with hj
  have hj1 : (j : ℝ) ≤ x + 1 / 2 := Nat.floor_le (by linarith)
  have hj2 : x + 1 / 2 < j + 1 := Nat.lt_floor_add_one _
  refine ⟨j, ?_, ?_⟩
  · rw [Finset.mem_range]
    have h1 : (j : ℝ) < r / η + 1 := by linarith [div_nonneg hr hη.le]
    have h2 : r / η ≤ (⌈r / η⌉₊ : ℝ) := Nat.le_ceil _
    exact_mod_cast (show (j : ℝ) < (⌈r / η⌉₊ : ℝ) + 1 by linarith)
  · have hax : a = E₀ - r + 2 * η * x := by rw [hx]; field_simp; ring
    rw [hax, abs_le]
    constructor <;> nlinarith

/-- **Covering lemma (one scale ⇒ every larger scale).**  The eigenvector mass at `x` of the
eigenvalues in `[E₀ - r, E₀ + r]` is bounded by `2η` times the sum of `Im G_xx` at the
`⌈r/η⌉₊ + 1` points `E₀ - r + 2ηj + iη` (all at the single scale `η`)
(RBM1D `Step3KernelBounds.lean:64`). -/
theorem sum_mass_window_le_im_green {H : Matrix n n ℂ} (hH : H.IsHermitian) {η r : ℝ}
    (hη : 0 < η) (_hr : 0 ≤ r) (E₀ : ℝ) (x : n) :
    ∑ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r),
        ‖hH.eigenvectorBasis l x‖ ^ 2 ≤
      2 * η * ∑ j ∈ Finset.range (⌈r / η⌉₊ + 1),
        (Gres H (((E₀ - r + 2 * η * j : ℝ) : ℂ) + η * Complex.I) true x x).im := by
  set K := ⌈r / η⌉₊ + 1
  set w : n → ℝ := fun l => ‖hH.eigenvectorBasis l x‖ ^ 2
  set k : ℕ → n → ℝ := fun j l =>
    w l * (η / ((hH.eigenvalues l - (E₀ - r + 2 * η * j)) ^ 2 + η ^ 2))
  have hk0 : ∀ j l, 0 ≤ k j l := fun j l => by
    simp only [k, w]; positivity
  have hG : ∀ j : ℕ, (Gres H (((E₀ - r + 2 * η * j : ℝ) : ℂ) + η * Complex.I) true x x).im =
      ∑ l, k j l := by
    intro j
    rw [im_Gres_apply_self hH _ hη]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [k, w, Complex.normSq_eq_norm_sq]
    ring
  have hpt : ∀ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r),
      w l ≤ 2 * η * ∑ j ∈ Finset.range K, k j l := by
    intro l hl
    obtain ⟨j, hjK, hjc⟩ := JakKernel_covering_exists_center hη (Finset.mem_filter.1 hl).2
    have hw : 0 ≤ w l := by simp only [w]; positivity
    set D := (hH.eigenvalues l - (E₀ - r + 2 * η * j)) ^ 2 + η ^ 2
    have hD : 0 < D := by positivity
    have hDle : D ≤ 2 * η ^ 2 := by
      have : (hH.eigenvalues l - (E₀ - r + 2 * η * j)) ^ 2 ≤ η ^ 2 := by
        apply sq_le_sq' <;> linarith [(abs_le.1 hjc).1, (abs_le.1 hjc).2]
      simp only [D]; linarith
    have hone : w l ≤ 2 * η * k j l := by
      simp only [k]
      rw [show 2 * η * (w l * (η / D)) = w l * (2 * η ^ 2 / D) by field_simp]
      have : 1 ≤ 2 * η ^ 2 / D := by rw [le_div_iff₀ hD]; linarith
      nlinarith
    calc w l ≤ 2 * η * k j l := hone
      _ ≤ 2 * η * ∑ j ∈ Finset.range K, k j l := by
        gcongr
        exact Finset.single_le_sum (fun j _ => hk0 j l) hjK
  calc ∑ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r), w l
      ≤ ∑ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r),
          2 * η * ∑ j ∈ Finset.range K, k j l := Finset.sum_le_sum hpt
    _ ≤ ∑ l, 2 * η * ∑ j ∈ Finset.range K, k j l := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro l _ _
        have := fun j => hk0 j l
        positivity
    _ = 2 * η * ∑ j ∈ Finset.range K,
          (Gres H (((E₀ - r + 2 * η * j : ℝ) : ℂ) + η * Complex.I) true x x).im := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [hG]

/-- Consumer form: a single-scale bound `Im G_xx ≤ Cb` at the grid points gives window mass
`≤ 2(r + 2η) Cb` at every scale `r ≥ 0` (RBM1D `Step3KernelBounds.lean:119`). -/
theorem sum_mass_window_le_of_im_green_le {H : Matrix n n ℂ} (hH : H.IsHermitian)
    {η r Cb : ℝ} (hη : 0 < η) (hr : 0 ≤ r) (hCb : 0 ≤ Cb) (E₀ : ℝ) (x : n)
    (hG : ∀ j ∈ Finset.range (⌈r / η⌉₊ + 1),
      (Gres H (((E₀ - r + 2 * η * j : ℝ) : ℂ) + η * Complex.I) true x x).im ≤ Cb) :
    ∑ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r),
        ‖hH.eigenvectorBasis l x‖ ^ 2 ≤ 2 * (r + 2 * η) * Cb := by
  refine (sum_mass_window_le_im_green hH hη hr E₀ x).trans ?_
  have hsum := Finset.sum_le_sum hG
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hK : ((⌈r / η⌉₊ + 1 : ℕ) : ℝ) ≤ r / η + 2 := by
    push_cast; linarith [Nat.ceil_lt_add_one (div_nonneg hr hη.le)]
  calc 2 * η * _ ≤ 2 * η * (((⌈r / η⌉₊ + 1 : ℕ) : ℝ) * Cb) := by gcongr
    _ ≤ 2 * η * ((r / η + 2) * Cb) := by gcongr
    _ = 2 * (r + 2 * η) * Cb := by field_simp

/-! ## 2. The single-scale grid event and its deterministic consequences -/

/-- The single-scale grid event (RBM1D `Step3KernelBounds.GridGood`,
`Flow/Step3KernelBounds.lean:143`): `Im G_xx ≤ Cb` on the covering grid of centre `E₀`, radius
`r`, scale `η`, for every site `x`. -/
def jakGridGood (H : Matrix n n ℂ) (η Cb E₀ r : ℝ) : Prop :=
  ∀ j ∈ Finset.range (⌈r / η⌉₊ + 1), ∀ x : n,
    (Gres H (((E₀ - r + 2 * η * j : ℝ) : ℂ) + η * Complex.I) true x x).im ≤ Cb

/-- The rows of the eigenvector matrix are unit vectors: `∑_l |ψ_l(x)|² = 1`
(RBM1D `Delocalization.lean:169`). -/
private theorem JakKernel_sum_sq_norm_row {H : Matrix n n ℂ} (hH : H.IsHermitian) (x : n) :
    ∑ l, ‖hH.eigenvectorBasis l x‖ ^ 2 = 1 := by
  have hUU' : (hH.eigenvectorUnitary : Matrix n n ℂ) *
      star (hH.eigenvectorUnitary : Matrix n n ℂ) = 1 := Unitary.coe_mul_star_self _
  have h := congrArg (fun M : Matrix n n ℂ => M x x) hUU'
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq,
    IsHermitian.eigenvectorUnitary_apply, RCLike.star_def] at h
  have h2 : ∑ l, ((‖hH.eigenvectorBasis l x‖ ^ 2 : ℝ) : ℂ) = (1 : ℂ) := by
    rw [← h]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact_mod_cast h2

/-- Eigenvectors are normalised: `∑_p |ψ_k(p)|² = 1` (RBM1D `Flow/Universality.lean:298`). -/
private theorem JakKernel_sum_sq_norm_col {H : Matrix n n ℂ} (hH : H.IsHermitian) (k : n) :
    ∑ p, ‖hH.eigenvectorBasis k p‖ ^ 2 = 1 := by
  have h := hH.eigenvectorBasis.orthonormal.1 k
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
  exact h

private theorem JakKernel_gridGood_mass {H : Matrix n n ℂ} (hH : H.IsHermitian)
    {η Cb E₀ r : ℝ} (hη : 0 < η) (hr : 0 ≤ r) (hCb : 0 ≤ Cb)
    (hG : jakGridGood H η Cb E₀ r) (x : n) :
    ∑ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r),
        ‖hH.eigenvectorBasis l x‖ ^ 2 ≤ 2 * (r + 2 * η) * Cb :=
  sum_mass_window_le_of_im_green_le hH hη hr hCb E₀ x fun j hj => hG j hj x

/-- Eigenvalue counting from the site masses: `#{l : |λ_l - E₀| ≤ r} ≤ |n| · 2(r+2η)Cb`. -/
private theorem JakKernel_gridGood_count {H : Matrix n n ℂ} (hH : H.IsHermitian)
    {η Cb E₀ r : ℝ} (hη : 0 < η) (hr : 0 ≤ r) (hCb : 0 ≤ Cb)
    (hG : jakGridGood H η Cb E₀ r) :
    ((Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r)).card : ℝ) ≤
      (Fintype.card n : ℝ) * (2 * (r + 2 * η) * Cb) := by
  have h1 : ((Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r)).card : ℝ) =
      ∑ x : n, ∑ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r),
        ‖hH.eigenvectorBasis l x‖ ^ 2 := by
    rw [Finset.sum_comm]
    simp_rw [JakKernel_sum_sq_norm_col hH]
    simp
  rw [h1]
  calc _ ≤ ∑ _x : n, 2 * (r + 2 * η) * Cb :=
        Finset.sum_le_sum fun x _ => JakKernel_gridGood_mass hH hη hr hCb hG x
    _ = _ := by simp

/-- Bulk delocalization from the grid: `|λ_α - E₀| ≤ R` gives `|ψ_α(x)|² ≤ 2η Cb`. -/
private theorem JakKernel_gridGood_deloc {H : Matrix n n ℂ} (hH : H.IsHermitian)
    {η Cb E₀ R : ℝ} (hη : 0 < η) (hG : jakGridGood H η Cb E₀ R) {α : n}
    (hα : |hH.eigenvalues α - E₀| ≤ R) (x : n) :
    ‖hH.eigenvectorBasis α x‖ ^ 2 ≤ 2 * η * Cb := by
  obtain ⟨j, hj, hjc⟩ := JakKernel_covering_exists_center hη hα
  have hGj := hG j hj x
  rw [im_Gres_apply_self hH _ hη] at hGj
  set e : ℝ := E₀ - R + 2 * η * j
  have hterm : η * Complex.normSq (hH.eigenvectorBasis α x) /
      ((hH.eigenvalues α - e) ^ 2 + η ^ 2) ≤
      ∑ l, η * Complex.normSq (hH.eigenvectorBasis l x) /
        ((hH.eigenvalues l - e) ^ 2 + η ^ 2) :=
    Finset.single_le_sum (f := fun l => η * Complex.normSq (hH.eigenvectorBasis l x) /
        ((hH.eigenvalues l - e) ^ 2 + η ^ 2))
      (fun l _ => div_nonneg (mul_nonneg hη.le (Complex.normSq_nonneg _)) (by positivity))
      (Finset.mem_univ α)
  have hsq : (hH.eigenvalues α - e) ^ 2 ≤ η ^ 2 := by
    apply sq_le_sq' <;> linarith [(abs_le.1 hjc).1, (abs_le.1 hjc).2]
  have hD : 0 < (hH.eigenvalues α - e) ^ 2 + η ^ 2 := by positivity
  have hv : 0 ≤ ‖hH.eigenvectorBasis α x‖ ^ 2 := by positivity
  rw [Complex.normSq_eq_norm_sq] at hterm
  have hle : ‖hH.eigenvectorBasis α x‖ ^ 2 ≤
      2 * η * (η * ‖hH.eigenvectorBasis α x‖ ^ 2 / ((hH.eigenvalues α - e) ^ 2 + η ^ 2)) := by
    rw [mul_div_assoc', le_div_iff₀ hD]
    nlinarith
  calc _ ≤ 2 * η * (η * ‖hH.eigenvectorBasis α x‖ ^ 2 /
        ((hH.eigenvalues α - e) ^ 2 + η ^ 2)) := hle
    _ ≤ 2 * η * Cb := by gcongr; exact hterm.trans hGj

/-- `Im m(w) = |n|⁻¹ ∑_x Im G_xx(w)` (`stieltjesN` is `|n|⁻¹ tr Gres`, `Pins.lean:88`). -/
private theorem JakKernel_stieltjesN_im_eq_diag (H : Matrix n n ℂ) (w : ℂ) :
    (stieltjesN H w).im = (Fintype.card n : ℝ)⁻¹ * ∑ x : n, (Gres H w true x x).im := by
  rw [stieltjesN, Matrix.trace, Complex.mul_im, Complex.im_sum, Complex.re_sum]
  have h1 : ((Fintype.card n : ℂ)⁻¹).im = 0 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_im]
  have h2 : ((Fintype.card n : ℂ)⁻¹).re = (Fintype.card n : ℝ)⁻¹ := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
  rw [h1, h2]
  simp [Matrix.diag]

/-- For a finite Hermitian matrix, `Im m(E + iη) = |n|⁻¹ ∑ₗ η / ((λₗ-E)²+η²)` for positive `η`
(RBM1D `StieltjesEtaMonotone.lean:22`; the `Gres` route: `im_Gres_apply_self` summed over `x`, template
`InjSum.lean:196`). -/
private theorem JakKernel_stieltjesN_im_eq (H : Matrix n n ℂ) (hH : H.IsHermitian) (E η : ℝ)
    (hη : 0 < η) :
    (stieltjesN H (E + η * Complex.I)).im =
      (Fintype.card n : ℝ)⁻¹ * ∑ l : n,
        (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2)) := by
  rw [JakKernel_stieltjesN_im_eq_diag]
  congr 1
  simp_rw [im_Gres_apply_self hH E hη]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hD : 0 < (hH.eigenvalues l - E) ^ 2 + η ^ 2 := by positivity
  rw [← Finset.sum_div, ← Finset.mul_sum]
  simp_rw [Complex.normSq_eq_norm_sq]
  rw [JakKernel_sum_sq_norm_col hH l, mul_one]

/-- Monotonicity used between (2.27) and (2.28): `η Im m(E+iη)` is nondecreasing in `η`
(RBM1D `StieltjesEtaMonotone.lean:64`). -/
private theorem JakKernel_stieltjesN_eta_mul_im_mono (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E η ηTilde : ℝ) (hη : 0 < η) (hηTilde : η ≤ ηTilde) :
    η * (stieltjesN H (E + η * Complex.I)).im ≤
      ηTilde * (stieltjesN H (E + ηTilde * Complex.I)).im := by
  have hformula := JakKernel_stieltjesN_im_eq H hH E η hη
  have hformulaT := JakKernel_stieltjesN_im_eq H hH E ηTilde (by linarith)
  rw [hformula, hformulaT]
  have hterm (l : n) :
      η * (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2)) ≤
        ηTilde * (ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2)) := by
    let x := (hH.eigenvalues l - E) ^ 2
    have hx : 0 ≤ x := sq_nonneg _
    have hy : 0 < x + η ^ 2 := by positivity
    have hηT : 0 < ηTilde := lt_of_lt_of_le hη hηTilde
    have hyt : 0 < x + ηTilde ^ 2 := by positivity
    have hsquares : η ^ 2 ≤ ηTilde ^ 2 := by nlinarith [sq_nonneg (ηTilde - η)]
    have hfrac : η ^ 2 / (x + η ^ 2) ≤ ηTilde ^ 2 / (x + ηTilde ^ 2) := by
      rw [div_le_div_iff₀ hy hyt]
      have hdiff : 0 ≤ ηTilde ^ 2 - η ^ 2 := by linarith
      nlinarith [mul_nonneg hx hdiff]
    calc
      η * (η / (x + η ^ 2)) = η ^ 2 / (x + η ^ 2) := by field_simp
      _ ≤ ηTilde ^ 2 / (x + ηTilde ^ 2) := hfrac
      _ = ηTilde * (ηTilde / (x + ηTilde ^ 2)) := by field_simp
  have hc : 0 ≤ (Fintype.card n : ℝ)⁻¹ := by positivity
  calc
    η * ((Fintype.card n : ℝ)⁻¹ * ∑ l : n, η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2))
        = (Fintype.card n : ℝ)⁻¹ *
            ∑ l : n, η * (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2)) := by
          calc
            η * ((Fintype.card n : ℝ)⁻¹ *
                ∑ l : n, η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2))
                = η * ∑ l : n, (Fintype.card n : ℝ)⁻¹ *
                    (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2)) := by rw [Finset.mul_sum]
            _ = ∑ l : n, η * ((Fintype.card n : ℝ)⁻¹ *
                    (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2))) := by rw [Finset.mul_sum]
            _ = ∑ l : n, (Fintype.card n : ℝ)⁻¹ *
                    (η * (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2))) := by
                      apply Finset.sum_congr rfl
                      intro l hl
                      ring
            _ = (Fintype.card n : ℝ)⁻¹ *
                    ∑ l : n, η * (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2)) := by
                      rw [Finset.mul_sum]
    _ ≤ (Fintype.card n : ℝ)⁻¹ *
          ∑ l : n, ηTilde * (ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2)) := by
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun l _ => hterm l) hc
    _ = ηTilde * ((Fintype.card n : ℝ)⁻¹ *
          ∑ l : n, ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2)) := by
          calc
            (Fintype.card n : ℝ)⁻¹ *
                ∑ l : n, ηTilde * (ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2))
                = ∑ l : n, (Fintype.card n : ℝ)⁻¹ *
                    (ηTilde * (ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2))) := by
                      rw [Finset.mul_sum]
            _ = ∑ l : n, ηTilde * ((Fintype.card n : ℝ)⁻¹ *
                    (ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2))) := by
                      apply Finset.sum_congr rfl
                      intro l hl
                      ring
            _ = ηTilde * ((Fintype.card n : ℝ)⁻¹ *
                    ∑ l : n, ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2)) := by
                      rw [Finset.mul_sum, Finset.mul_sum]

/-- The zero-radius grid is the single energy `E₀`: a bound on every `Im G_xx(E₀ + iη)` bounds
`Im m(E₀ + iη)`. -/
private theorem JakKernel_gridGood_zero_stieltjes [Nonempty n] {H : Matrix n n ℂ} {η Cb E₀ : ℝ}
    (hG : jakGridGood H η Cb E₀ 0) :
    (stieltjesN H ((E₀ : ℂ) + η * Complex.I)).im ≤ Cb := by
  have hx : ∀ x : n, (Gres H ((E₀ : ℂ) + η * Complex.I) true x x).im ≤ Cb := by
    intro x
    have := hG 0 (by simp) x
    simpa using this
  have hcard : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have htr : (stieltjesN H ((E₀ : ℂ) + η * Complex.I)).im =
      (Fintype.card n : ℝ)⁻¹ * ∑ x : n, (Gres H ((E₀ : ℂ) + η * Complex.I) true x x).im := by
    rw [stieltjesN, Matrix.trace, Complex.mul_im, Complex.im_sum, Complex.re_sum]
    have h1 : ((Fintype.card n : ℂ)⁻¹).im = 0 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_im]
    have h2 : ((Fintype.card n : ℂ)⁻¹).re = (Fintype.card n : ℝ)⁻¹ := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
    rw [h1, h2]
    simp [Matrix.diag]
  rw [htr]
  calc _ ≤ (Fintype.card n : ℝ)⁻¹ * ∑ _x : n, Cb := by
        gcongr with x; exact hx x
    _ = Cb := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp

/-! ## 3. Dyadic helpers -/

/-- Dyadic majorant: for `f` antitone and nonnegative on `(0,∞)`, `ρ < d ≤ 2^K ρ` gives
`f d ≤ ∑_{k<K} 1_{d ≤ 2^{k+1}ρ} f(2^k ρ)` (RBM1D `Step3KernelBounds.lean:238`). -/
private theorem JakKernel_dyadic_le_sum {f : ℝ → ℝ} (hf : ∀ a b, 0 < a → a ≤ b → f b ≤ f a)
    (hf0 : ∀ a, 0 < a → 0 ≤ f a) {ρ d : ℝ} (hρ : 0 < ρ) :
    ∀ K : ℕ, ρ < d → d ≤ 2 ^ K * ρ →
      f d ≤ ∑ k ∈ Finset.range K, (if d ≤ 2 ^ (k + 1) * ρ then f (2 ^ k * ρ) else 0) := by
  intro K
  induction K with
  | zero => intro h1 h2; simp at h2; linarith
  | succ K ih =>
    intro h1 h2
    rw [Finset.sum_range_succ]
    have hnn : 0 ≤ ∑ k ∈ Finset.range K,
        (if d ≤ 2 ^ (k + 1) * ρ then f (2 ^ k * ρ) else 0) :=
      Finset.sum_nonneg fun k _ => by
        split_ifs <;> first | exact hf0 _ (by positivity) | exact le_rfl
    by_cases hd : d ≤ 2 ^ K * ρ
    · have := ih h1 hd
      have hlast : 0 ≤ (if d ≤ 2 ^ (K + 1) * ρ then f (2 ^ K * ρ) else 0) := by
        split_ifs; exact hf0 _ (by positivity)
      linarith
    · push Not at hd
      simp only [h2, ite_true]
      have := hf (2 ^ K * ρ) d (by positivity) hd.le
      linarith

private theorem JakKernel_geom_half_sum_le (K : ℕ) :
    ∑ k ∈ Finset.range K, ((2 : ℝ) ^ k)⁻¹ ≤ 2 := by
  have h := sum_geometric_two_le K
  simpa [one_div, inv_pow] using h

/-! ## 4. Pole bounds (generic index type) -/

variable {H : Matrix n n ℂ} (hH : H.IsHermitian)

private theorem JakKernel_pole_norm_eq (u : ℂ) (α : n) :
    ‖spectralPole hH u α‖ = ‖(hH.eigenvalues α : ℂ) - u‖⁻¹ := by
  rw [spectralPole, norm_inv]

private theorem JakKernel_pole_norm_le_inv_im {u : ℂ} (hη : 0 < u.im) (α : n) :
    ‖spectralPole hH u α‖ ≤ u.im⁻¹ := by
  rw [JakKernel_pole_norm_eq]
  have h : u.im ≤ ‖(hH.eigenvalues α : ℂ) - u‖ := by
    have := Complex.abs_im_le_norm ((hH.eigenvalues α : ℂ) - u)
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at this
    rwa [abs_of_pos hη] at this
  exact inv_anti₀ hη h

private theorem JakKernel_pole_norm_le_inv_dist {u : ℂ} (α : n)
    (hd : 0 < |hH.eigenvalues α - u.re|) :
    ‖spectralPole hH u α‖ ≤ |hH.eigenvalues α - u.re|⁻¹ := by
  rw [JakKernel_pole_norm_eq]
  have h : |hH.eigenvalues α - u.re| ≤ ‖(hH.eigenvalues α : ℂ) - u‖ := by
    have := Complex.abs_re_le_norm ((hH.eigenvalues α : ℂ) - u)
    simpa only [Complex.sub_re, Complex.ofReal_re] using this
  exact inv_anti₀ hd h

private theorem JakKernel_pole_norm_sq_eq {u : ℂ} (α : n) :
    ‖spectralPole hH u α‖ ^ 2 = ((hH.eigenvalues α - u.re) ^ 2 + u.im ^ 2)⁻¹ := by
  rw [JakKernel_pole_norm_eq, inv_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  congr 1
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub]
  ring

private theorem JakKernel_pole_norm_sq_le_inv_dist_sq {u : ℂ} (α : n)
    (hd : 0 < |hH.eigenvalues α - u.re|) :
    ‖spectralPole hH u α‖ ^ 2 ≤ (|hH.eigenvalues α - u.re| ^ 2)⁻¹ := by
  rw [← inv_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (JakKernel_pole_norm_le_inv_dist hH α hd) 2

include hH in
/-- Crude bound `Im m(w) ≤ 1/Im w`, and `Im m(w) ≥ 0`. -/
private theorem JakKernel_stieltjesN_im_nonneg_le [Nonempty n] {w : ℂ} (hη : 0 < w.im) :
    0 ≤ (stieltjesN H w).im ∧ (stieltjesN H w).im ≤ w.im⁻¹ := by
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
  have hf := JakKernel_stieltjesN_im_eq H hH w.re w.im hη
  rw [← hw] at hf
  rw [hf]
  have hcard : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hterm : ∀ l : n, w.im / ((hH.eigenvalues l - w.re) ^ 2 + w.im ^ 2) ≤ w.im⁻¹ := by
    intro l
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [sq_nonneg (hH.eigenvalues l - w.re)]
  constructor
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun l _ => by positivity)
  · calc _ ≤ (Fintype.card n : ℝ)⁻¹ * ∑ _l : n, w.im⁻¹ := by
          gcongr with l; exact hterm l
      _ = w.im⁻¹ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

include hH in
/-- `Im m(w) ≤ (η̃/Im w) Cb` from the zero-radius grid at `Re w` (monotonicity in `η`). -/
private theorem JakKernel_stieltjesN_im_le_of_grid [Nonempty n] {w : ℂ} (hη : 0 < w.im)
    {ηt Cb : ℝ} (hηη : w.im ≤ ηt) (hG : jakGridGood H ηt Cb w.re 0) :
    (stieltjesN H w).im ≤ ηt / w.im * Cb := by
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
  have hmono := JakKernel_stieltjesN_eta_mul_im_mono H hH w.re w.im ηt hη hηη
  rw [← hw] at hmono
  have hT := JakKernel_gridGood_zero_stieltjes (H := H) hG
  have hηt : 0 < ηt := lt_of_lt_of_le hη hηη
  rw [div_mul_eq_mul_div, le_div_iff₀ hη, mul_comm]
  exact hmono.trans (mul_le_mul_of_nonneg_left hT hηt.le)

/-- `∑_α |p_α(u)|² ≤ (ηt/η²) |n| Cb` from the zero-radius grid at `Re u`. -/
private theorem JakKernel_sum_pole_sq_le_of_grid [Nonempty n] {u : ℂ} (hη : 0 < u.im)
    {ηt Cb : ℝ} (hηη : u.im ≤ ηt) (hG : jakGridGood H ηt Cb u.re 0) :
    ∑ α, ‖spectralPole hH u α‖ ^ 2 ≤ ηt / u.im ^ 2 * ((Fintype.card n : ℝ) * Cb) := by
  have hηt : 0 < ηt := lt_of_lt_of_le hη hηη
  have hT := JakKernel_gridGood_zero_stieltjes (H := H) hG
  have hf := JakKernel_stieltjesN_im_eq H hH u.re ηt hηt
  have hcard : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ l : n, ηt / ((hH.eigenvalues l - u.re) ^ 2 + ηt ^ 2) ≤
      (Fintype.card n : ℝ) * Cb := by
    rw [hf] at hT
    rw [inv_mul_le_iff₀ hcard] at hT
    exact hT
  have hterm : ∀ α : n, ‖spectralPole hH u α‖ ^ 2 ≤
      ηt / u.im ^ 2 * (ηt / ((hH.eigenvalues α - u.re) ^ 2 + ηt ^ 2)) := by
    intro α
    rw [JakKernel_pole_norm_sq_eq]
    set x := (hH.eigenvalues α - u.re) ^ 2
    have hx : 0 ≤ x := sq_nonneg _
    rw [show ηt / u.im ^ 2 * (ηt / (x + ηt ^ 2)) = ηt ^ 2 / (u.im ^ 2 * (x + ηt ^ 2)) by
      field_simp]
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h2 : u.im ^ 2 ≤ ηt ^ 2 := pow_le_pow_left₀ hη.le hηη 2
    nlinarith [mul_le_mul_of_nonneg_left h2 hx]
  calc _ ≤ ∑ α : n, ηt / u.im ^ 2 * (ηt / ((hH.eigenvalues α - u.re) ^ 2 + ηt ^ 2)) :=
        Finset.sum_le_sum fun α _ => hterm α
    _ = ηt / u.im ^ 2 * ∑ α : n, ηt / ((hH.eigenvalues α - u.re) ^ 2 + ηt ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ _ := by gcongr

include hH in
/-- **The `Q_y` row.** `∑_γ |p_γ(u)| |ψ_γ(y)|² ≤ 6(η̃/η)Cb + 8K Cb + (2^K η̃)⁻¹` from the grids of
radii `2^k η̃`, `k ≤ K` (near part, `K` dyadic shells, completeness beyond `2^K η̃`). -/
private theorem JakKernel_sum_pole_mass_le {u : ℂ} (hη : 0 < u.im) {ηt Cb : ℝ}
    (hηη : u.im ≤ ηt) (hCb : 0 ≤ Cb) (K : ℕ)
    (hG : ∀ k ≤ K, jakGridGood H ηt Cb u.re (2 ^ k * ηt)) (y : n) :
    ∑ γ, ‖spectralPole hH u γ‖ * ‖hH.eigenvectorBasis γ y‖ ^ 2 ≤
      6 * (ηt / u.im) * Cb + 8 * K * Cb + (2 ^ K * ηt)⁻¹ := by
  have hηt : 0 < ηt := lt_of_lt_of_le hη hηη
  set v : n → ℝ := fun γ => ‖hH.eigenvectorBasis γ y‖ ^ 2 with hv
  set dd : n → ℝ := fun γ => |hH.eigenvalues γ - u.re| with hdd
  have hv0 : ∀ γ, 0 ≤ v γ := fun γ => by positivity
  -- pointwise dyadic majorant
  have hpt : ∀ γ, ‖spectralPole hH u γ‖ * v γ ≤
      u.im⁻¹ * (if dd γ ≤ ηt then v γ else 0) +
        ∑ k ∈ Finset.range K, (2 ^ k * ηt)⁻¹ *
          (if dd γ ≤ 2 ^ (k + 1) * ηt then v γ else 0) + (2 ^ K * ηt)⁻¹ * v γ := by
    intro γ
    have hS0 : 0 ≤ ∑ k ∈ Finset.range K, (2 ^ k * ηt)⁻¹ *
        (if dd γ ≤ 2 ^ (k + 1) * ηt then v γ else 0) :=
      Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (by split_ifs <;> simp [hv0])
    have hT0 : 0 ≤ (2 ^ K * ηt)⁻¹ * v γ := mul_nonneg (by positivity) (hv0 γ)
    by_cases h1 : dd γ ≤ ηt
    · simp only [h1, ite_true]
      have := mul_le_mul_of_nonneg_right (JakKernel_pole_norm_le_inv_im hH hη γ) (hv0 γ)
      linarith
    · push Not at h1
      have hdpos : 0 < dd γ := lt_trans hηt h1
      have hpd := mul_le_mul_of_nonneg_right (JakKernel_pole_norm_le_inv_dist hH γ hdpos) (hv0 γ)
      simp only [not_le.2 h1, ite_false, mul_zero, zero_add]
      by_cases h2 : dd γ ≤ 2 ^ K * ηt
      · have hdy := JakKernel_dyadic_le_sum (f := fun x => x⁻¹)
          (fun a b ha hab => inv_anti₀ ha hab)
          (fun a ha => inv_nonneg.2 ha.le) hηt K h1 h2
        have hdy' : (dd γ)⁻¹ * v γ ≤ ∑ k ∈ Finset.range K, (2 ^ k * ηt)⁻¹ *
            (if dd γ ≤ 2 ^ (k + 1) * ηt then v γ else 0) := by
          calc (dd γ)⁻¹ * v γ ≤ (∑ k ∈ Finset.range K,
                (if dd γ ≤ 2 ^ (k + 1) * ηt then (2 ^ k * ηt)⁻¹ else 0)) * v γ :=
                mul_le_mul_of_nonneg_right hdy (hv0 γ)
            _ = _ := by
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl fun k _ => ?_
                split_ifs <;> ring
        linarith
      · push Not at h2
        have : (dd γ)⁻¹ * v γ ≤ (2 ^ K * ηt)⁻¹ * v γ :=
          mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) h2.le) (hv0 γ)
        linarith
  -- mass bounds from the grids
  have hmass : ∀ r : ℝ, 0 ≤ r → jakGridGood H ηt Cb u.re r →
      ∑ γ, (if dd γ ≤ r then v γ else 0) ≤ 2 * (r + 2 * ηt) * Cb := by
    intro r hr hGr
    rw [← Finset.sum_filter]
    exact JakKernel_gridGood_mass hH hηt hr hCb hGr y
  have hm0 : ∑ γ, (if dd γ ≤ ηt then v γ else 0) ≤ 2 * (ηt + 2 * ηt) * Cb :=
    hmass ηt hηt.le (by simpa using hG 0 (Nat.zero_le _))
  have hmk : ∀ k ∈ Finset.range K, (2 ^ k * ηt)⁻¹ *
      ∑ γ, (if dd γ ≤ 2 ^ (k + 1) * ηt then v γ else 0) ≤ 8 * Cb := by
    intro k hk
    have hkK : k + 1 ≤ K := Finset.mem_range.1 hk
    have h := hmass (2 ^ (k + 1) * ηt) (by positivity) (hG (k + 1) hkK)
    have hp : (0 : ℝ) < 2 ^ k * ηt := by positivity
    have h1 : (2 ^ k * ηt)⁻¹ * ∑ γ, (if dd γ ≤ 2 ^ (k + 1) * ηt then v γ else 0) ≤
        (2 ^ k * ηt)⁻¹ * (2 * (2 ^ (k + 1) * ηt + 2 * ηt) * Cb) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have h2 : (2 ^ k * ηt)⁻¹ * (2 * (2 ^ (k + 1) * ηt + 2 * ηt) * Cb) =
        (4 + 4 * ((2 : ℝ) ^ k)⁻¹) * Cb := by
      field_simp; ring
    have h3 : ((2 : ℝ) ^ k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    nlinarith
  have hsumv : ∑ γ, v γ = 1 := JakKernel_sum_sq_norm_row hH y
  calc ∑ γ, ‖spectralPole hH u γ‖ * ‖hH.eigenvectorBasis γ y‖ ^ 2
      = ∑ γ, ‖spectralPole hH u γ‖ * v γ := rfl
    _ ≤ ∑ γ, (u.im⁻¹ * (if dd γ ≤ ηt then v γ else 0) +
          ∑ k ∈ Finset.range K, (2 ^ k * ηt)⁻¹ *
            (if dd γ ≤ 2 ^ (k + 1) * ηt then v γ else 0) + (2 ^ K * ηt)⁻¹ * v γ) :=
        Finset.sum_le_sum fun γ _ => hpt γ
    _ = u.im⁻¹ * ∑ γ, (if dd γ ≤ ηt then v γ else 0) +
          ∑ k ∈ Finset.range K, (2 ^ k * ηt)⁻¹ *
            ∑ γ, (if dd γ ≤ 2 ^ (k + 1) * ηt then v γ else 0) +
          (2 ^ K * ηt)⁻¹ * ∑ γ, v γ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          Finset.sum_comm]
        congr 2
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
    _ ≤ u.im⁻¹ * (2 * (ηt + 2 * ηt) * Cb) + ∑ _k ∈ Finset.range K, 8 * Cb +
          (2 ^ K * ηt)⁻¹ * 1 := by
        rw [hsumv]
        have hA : u.im⁻¹ * ∑ γ, (if dd γ ≤ ηt then v γ else 0) ≤
            u.im⁻¹ * (2 * (ηt + 2 * ηt) * Cb) :=
          mul_le_mul_of_nonneg_left hm0 (by positivity)
        have hB := Finset.sum_le_sum hmk
        linarith
    _ = 6 * (ηt / u.im) * Cb + 8 * K * Cb + (2 ^ K * ηt)⁻¹ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
        ring

include hH in
/-- Crude `Q_y ≤ 1/η`. -/
private theorem JakKernel_sum_pole_mass_le_crude {u : ℂ} (hη : 0 < u.im) (y : n) :
    ∑ γ, ‖spectralPole hH u γ‖ * ‖hH.eigenvectorBasis γ y‖ ^ 2 ≤ u.im⁻¹ := by
  calc _ ≤ ∑ γ, u.im⁻¹ * ‖hH.eigenvectorBasis γ y‖ ^ 2 :=
        Finset.sum_le_sum fun γ _ =>
          mul_le_mul_of_nonneg_right (JakKernel_pole_norm_le_inv_im hH hη γ) (by positivity)
    _ = u.im⁻¹ := by rw [← Finset.mul_sum, JakKernel_sum_sq_norm_row hH y, mul_one]

end Generic

/-! ## 5. The block profile: the `A_y` factor -/

section Block

variable {d L W : ℕ} [NeZero L] [NeZero W]
variable {Hm : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : Hm.IsHermitian)

private theorem JakKernel_N_pos : (0 : ℝ) < (((W * L) ^ d : ℕ) : ℝ) := by
  exact_mod_cast pow_pos (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne W))
    (Nat.pos_of_ne_zero (NeZero.ne L))) d

/-- Column sums of the variance profile: `∑_x S_{xy} = 1` for `3 ≤ L`, every `lam` (copy of the private
`JakSpectral_sum_svarF_col`, `JakSpectral.lean:445`; replaces RBM2D `JakKernel_sum_norm_Spaper` `:642`). -/
private theorem JakKernel_sum_svarF_col (hL : 3 ≤ L) (lam : ℝ) (y : Idx d L W) :
    ∑ x : Idx d L W, svarF d L W lam x y = 1 := by
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := by
    have : (0 : ℝ) < (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
    positivity
  set a := (split d L W y).1 with ha
  have hrow : ∑ b : Zd d L, SBR d L lam b a = 1 := by
    simp_rw [SBR_comm _ a]
    exact sum_SBR_row hL a
  rw [← Finset.sum_fiberwise Finset.univ (fun x => (split d L W x).1)
    (fun x => svarF d L W lam x y)]
  have h1 : ∀ b : Zd d L,
      ∑ x ∈ Finset.univ.filter (fun x : Idx d L W => (split d L W x).1 = b),
        svarF d L W lam x y = SBR d L lam b a := by
    intro b
    have hc : ∀ x ∈ Finset.univ.filter (fun x : Idx d L W => (split d L W x).1 = b),
        svarF d L W lam x y = ((W : ℝ) ^ d)⁻¹ * SBR d L lam b a := by
      intro x hx
      have hxb : (split d L W x).1 = b := (Finset.mem_filter.mp hx).2
      simp only [svarF, ← ha, hxb]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ.filter (fun x : Idx d L W => (split d L W x).1 = b)).card = W ^ d :=
      card_Iblk d L W b
    rw [hcard]
    push_cast
    field_simp
  rw [Finset.sum_congr rfl fun b _ => h1 b]
  exact hrow

private theorem JakKernel_scirc_norm_le (lam : ℝ) (x y : Idx d L W) :
    ‖scirc d L W lam x y‖ ≤ svarF d L W lam x y + (((W * L) ^ d : ℕ) : ℝ)⁻¹ := by
  unfold scirc
  calc ‖((svarF d L W lam x y : ℝ) : ℂ) - ((((W * L) ^ d : ℕ) : ℂ))⁻¹‖
      ≤ ‖((svarF d L W lam x y : ℝ) : ℂ)‖ + ‖((((W * L) ^ d : ℕ) : ℂ))⁻¹‖ := norm_sub_le _ _
    _ = _ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (svarF_nonneg d L W lam x y),
          norm_inv, Complex.norm_natCast]

/-- The weight sum: `∑_x (S_{xy} + N⁻¹) = 2` (the constant `2` of RBM2D `:661`; copy of the private
`JakSpectral_profile_weight_sum`, `JakSpectral.lean:496`). -/
private theorem JakKernel_profile_weight_sum (hL : 3 ≤ L) (lam : ℝ) (y : Idx d L W) :
    ∑ x : Idx d L W, (svarF d L W lam x y + (((W * L) ^ d : ℕ) : ℝ)⁻¹) = 2 := by
  rw [Finset.sum_add_distrib, JakKernel_sum_svarF_col hL lam y]
  have hN : (((W * L) ^ d : ℕ) : ℝ) ≠ 0 := ne_of_gt JakKernel_N_pos
  have hconst : ∑ _x : Idx d L W, (((W * L) ^ d : ℕ) : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, card_Idx, nsmul_eq_mul]
    field_simp
  rw [hconst]
  norm_num

include hH in
/-- `|M_{y,α}| ≤ 2N · D` if `|ψ_α(x)|² ≤ D` for every `x`
(RBM1D `Step3KernelBounds.lean:492`, `norm_blockM_le_of_mass`). -/
private theorem JakKernel_norm_blockM_le_of_mass (hL : 3 ≤ L) (lam : ℝ) (y α : Idx d L W) {D : ℝ}
    (hMass : ∀ x, ‖hH.eigenvectorBasis α x‖ ^ 2 ≤ D) :
    ‖blockM d L W lam hH (siteBlock d L W y) α‖ ≤ 2 * (((W * L) ^ d : ℕ) : ℝ) * D := by
  rw [blockM_eq hL lam hH y α]
  have hN : (0 : ℝ) < (((W * L) ^ d : ℕ) : ℝ) := JakKernel_N_pos
  calc ‖(((W * L) ^ d : ℕ) : ℂ) *
        ∑ x, ((‖hH.eigenvectorBasis α x‖ ^ 2 : ℝ) : ℂ) * scirc d L W lam x y‖
      ≤ (((W * L) ^ d : ℕ) : ℝ) * ∑ x, D * (svarF d L W lam x y + (((W * L) ^ d : ℕ) : ℝ)⁻¹) := by
        rw [norm_mul, Complex.norm_natCast]
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) hN.le
        refine Finset.sum_le_sum fun x _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul (hMass x) (JakKernel_scirc_norm_le lam x y) (norm_nonneg _)
          ((sq_nonneg _).trans (hMass x))
    _ = 2 * (((W * L) ^ d : ℕ) : ℝ) * D := by
        rw [← Finset.mul_sum, JakKernel_profile_weight_sum hL lam y]; ring

include hH in
/-- Bulk bound `|M_{y,α}| ≤ 4Nη̃Cb` for `|λ_α - E₀| ≤ R`, from the grid of radius `R`
(RBM1D `Step3KernelBounds.lean:524`). -/
private theorem JakKernel_norm_blockM_le_of_grid (hL : 3 ≤ L) (lam : ℝ) (y : Idx d L W)
    {ηt Cb E₀ R : ℝ} (hηt : 0 < ηt) (hG : jakGridGood Hm ηt Cb E₀ R) {α : Idx d L W}
    (hα : |hH.eigenvalues α - E₀| ≤ R) :
    ‖blockM d L W lam hH (siteBlock d L W y) α‖ ≤ 4 * (((W * L) ^ d : ℕ) : ℝ) * ηt * Cb := by
  have := JakKernel_norm_blockM_le_of_mass hH hL lam y α (D := 2 * ηt * Cb)
    (fun x => JakKernel_gridGood_deloc hH hηt hG hα x)
  linarith

include hH in
/-- **The `A_y` row.** Window part (`|λ_α - Re u| ≤ w'`, `|M| ≤ Mwin`), dyadic bulk part
(`w' < |λ_α - Re u| ≤ 2^{K'}w'`, delocalization and counting) and the part outside
`2^{K'}w'` (completeness `∑_α|M_{y,α}| ≤ 2N`, `sum_norm_blockM_le`)
(RBM1D `Step3KernelBounds.lean:537`). -/
private theorem JakKernel_sum_pole_sq_blockM_le (hL : 3 ≤ L) (lam : ℝ) (y : Idx d L W) {u : ℂ}
    (hη : 0 < u.im) {ηt Cb w' Rd Mwin : ℝ} (hηη : u.im ≤ ηt) (hCb : 0 ≤ Cb) (hw' : 0 < w')
    (hMwin : 0 ≤ Mwin) (K' : ℕ) (hRd : 2 ^ K' * w' ≤ Rd)
    (hGd : jakGridGood Hm ηt Cb u.re Rd)
    (hGc : ∀ k ≤ K', jakGridGood Hm ηt Cb u.re (2 ^ k * w'))
    (hG0 : jakGridGood Hm ηt Cb u.re 0)
    (hwin : ∀ α, |hH.eigenvalues α - u.re| ≤ w' →
      ‖blockM d L W lam hH (siteBlock d L W y) α‖ ≤ Mwin) :
    ∑ α, ‖spectralPole hH u α‖ ^ 2 * ‖blockM d L W lam hH (siteBlock d L W y) α‖ ≤
      Mwin * (ηt / u.im ^ 2 * ((((W * L) ^ d : ℕ) : ℝ) * Cb)) +
        4 * (((W * L) ^ d : ℕ) : ℝ) * ηt * Cb *
          (2 * (((W * L) ^ d : ℕ) : ℝ) * Cb * (4 / w' + 4 * ηt / w' ^ 2)) +
        ((2 ^ K' * w') ^ 2)⁻¹ * (2 * (((W * L) ^ d : ℕ) : ℝ)) := by
  have hηt : 0 < ηt := lt_of_lt_of_le hη hηη
  have hN : (0 : ℝ) < (((W * L) ^ d : ℕ) : ℝ) := JakKernel_N_pos
  have hcard : (Fintype.card (Idx d L W) : ℝ) = (((W * L) ^ d : ℕ) : ℝ) := by
    rw [card_Idx]
  set dd : Idx d L W → ℝ := fun α => |hH.eigenvalues α - u.re| with hdd
  set Mb : ℝ := 4 * (((W * L) ^ d : ℕ) : ℝ) * ηt * Cb with hMb
  have hMb0 : 0 ≤ Mb := by positivity
  have hpt : ∀ α, ‖spectralPole hH u α‖ ^ 2 * ‖blockM d L W lam hH (siteBlock d L W y) α‖ ≤
      (if dd α ≤ w' then Mwin * ‖spectralPole hH u α‖ ^ 2 else 0) +
        Mb * ∑ k ∈ Finset.range K',
          (if dd α ≤ 2 ^ (k + 1) * w' then ((2 ^ k * w') ^ 2)⁻¹ else 0) +
        ((2 ^ K' * w') ^ 2)⁻¹ * ‖blockM d L W lam hH (siteBlock d L W y) α‖ := by
    intro α
    have hS0 : 0 ≤ Mb * ∑ k ∈ Finset.range K',
        (if dd α ≤ 2 ^ (k + 1) * w' then ((2 ^ k * w') ^ 2)⁻¹ else 0) :=
      mul_nonneg hMb0 (Finset.sum_nonneg fun k _ => by split_ifs <;> positivity)
    have hT0 : 0 ≤ ((2 ^ K' * w') ^ 2)⁻¹ * ‖blockM d L W lam hH (siteBlock d L W y) α‖ := by positivity
    by_cases h1 : dd α ≤ w'
    · simp only [h1, ite_true]
      have := mul_le_mul_of_nonneg_left (hwin α h1) (sq_nonneg ‖spectralPole hH u α‖)
      nlinarith
    · push Not at h1
      simp only [not_le.2 h1, ite_false, zero_add]
      have hdpos : 0 < dd α := lt_trans hw' h1
      have hp2 := JakKernel_pole_norm_sq_le_inv_dist_sq hH α hdpos
      by_cases h2 : dd α ≤ 2 ^ K' * w'
      · have hM := JakKernel_norm_blockM_le_of_grid hH hL lam y hηt hGd (h2.trans hRd)
        have hdy := JakKernel_dyadic_le_sum (f := fun x => (x ^ 2)⁻¹)
          (fun a b ha hab => inv_anti₀ (by positivity) (pow_le_pow_left₀ ha.le hab 2))
          (fun a ha => by positivity) hw' K' h1 h2
        have : ‖spectralPole hH u α‖ ^ 2 * ‖blockM d L W lam hH (siteBlock d L W y) α‖ ≤
            (dd α ^ 2)⁻¹ * Mb :=
          mul_le_mul hp2 hM (norm_nonneg _) (by positivity)
        have h3 : (dd α ^ 2)⁻¹ * Mb ≤ Mb * ∑ k ∈ Finset.range K',
            (if dd α ≤ 2 ^ (k + 1) * w' then ((2 ^ k * w') ^ 2)⁻¹ else 0) := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left hdy hMb0
        linarith
      · push Not at h2
        have h4 : (dd α ^ 2)⁻¹ ≤ ((2 ^ K' * w') ^ 2)⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h2.le 2)
        have : ‖spectralPole hH u α‖ ^ 2 * ‖blockM d L W lam hH (siteBlock d L W y) α‖ ≤
            ((2 ^ K' * w') ^ 2)⁻¹ * ‖blockM d L W lam hH (siteBlock d L W y) α‖ :=
          mul_le_mul_of_nonneg_right (hp2.trans h4) (norm_nonneg _)
        linarith
  -- window part
  have hW1 : ∑ α, (if dd α ≤ w' then Mwin * ‖spectralPole hH u α‖ ^ 2 else 0) ≤
      Mwin * (ηt / u.im ^ 2 * ((((W * L) ^ d : ℕ) : ℝ) * Cb)) := by
    calc _ ≤ ∑ α, Mwin * ‖spectralPole hH u α‖ ^ 2 :=
          Finset.sum_le_sum fun α _ => by split_ifs <;> [exact le_rfl; positivity]
      _ = Mwin * ∑ α, ‖spectralPole hH u α‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ _ := by
          gcongr
          have := JakKernel_sum_pole_sq_le_of_grid hH hη hηη hG0
          rwa [hcard] at this
  -- dyadic counting part
  have hcount : ∀ k ∈ Finset.range K',
      ∑ α, (if dd α ≤ 2 ^ (k + 1) * w' then ((2 ^ k * w') ^ 2)⁻¹ else 0) ≤
        2 * (((W * L) ^ d : ℕ) : ℝ) * Cb * (2 / w' + 2 * ηt / w' ^ 2) * ((2 : ℝ) ^ k)⁻¹ := by
    intro k hk
    have hkK : k + 1 ≤ K' := Finset.mem_range.1 hk
    have hc := JakKernel_gridGood_count hH hηt (by positivity) hCb (hGc (k + 1) hkK)
    rw [hcard] at hc
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hp : (0 : ℝ) < 2 ^ k * w' := by positivity
    calc _ ≤ (((W * L) ^ d : ℕ) : ℝ) * (2 * (2 ^ (k + 1) * w' + 2 * ηt) * Cb) *
            ((2 ^ k * w') ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = 2 * (((W * L) ^ d : ℕ) : ℝ) * Cb * (2 / w' * ((2 : ℝ) ^ k)⁻¹ +
            2 * ηt / w' ^ 2 * ((2 : ℝ) ^ k)⁻¹ * ((2 : ℝ) ^ k)⁻¹) := by
          field_simp; ring
      _ ≤ 2 * (((W * L) ^ d : ℕ) : ℝ) * Cb * (2 / w' * ((2 : ℝ) ^ k)⁻¹ +
            2 * ηt / w' ^ 2 * ((2 : ℝ) ^ k)⁻¹ * 1) := by
          gcongr
          exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
      _ = _ := by ring
  have hW2 : ∑ α, Mb * ∑ k ∈ Finset.range K',
      (if dd α ≤ 2 ^ (k + 1) * w' then ((2 ^ k * w') ^ 2)⁻¹ else 0) ≤
      Mb * (2 * (((W * L) ^ d : ℕ) : ℝ) * Cb * (4 / w' + 4 * ηt / w' ^ 2)) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    refine mul_le_mul_of_nonneg_left ?_ hMb0
    calc _ ≤ ∑ k ∈ Finset.range K',
          2 * (((W * L) ^ d : ℕ) : ℝ) * Cb * (2 / w' + 2 * ηt / w' ^ 2) * ((2 : ℝ) ^ k)⁻¹ :=
          Finset.sum_le_sum hcount
      _ = 2 * (((W * L) ^ d : ℕ) : ℝ) * Cb * (2 / w' + 2 * ηt / w' ^ 2) *
            ∑ k ∈ Finset.range K', ((2 : ℝ) ^ k)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ 2 * (((W * L) ^ d : ℕ) : ℝ) * Cb * (2 / w' + 2 * ηt / w' ^ 2) * 2 := by
          gcongr; exact JakKernel_geom_half_sum_le K'
      _ = _ := by ring
  -- outside part
  have hW3 : ∑ α, ((2 ^ K' * w') ^ 2)⁻¹ * ‖blockM d L W lam hH (siteBlock d L W y) α‖ ≤
      ((2 ^ K' * w') ^ 2)⁻¹ * (2 * (((W * L) ^ d : ℕ) : ℝ)) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_norm_blockM_le hL lam hH (siteBlock d L W y))
      (by positivity)
  calc _ ≤ ∑ α, ((if dd α ≤ w' then Mwin * ‖spectralPole hH u α‖ ^ 2 else 0) +
        Mb * ∑ k ∈ Finset.range K',
          (if dd α ≤ 2 ^ (k + 1) * w' then ((2 ^ k * w') ^ 2)⁻¹ else 0) +
        ((2 ^ K' * w') ^ 2)⁻¹ * ‖blockM d L W lam hH (siteBlock d L W y) α‖) :=
        Finset.sum_le_sum fun α _ => hpt α
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ _ := by linarith

include hH in
/-- Crude `A_y ≤ 2N/η²` (RBM1D `Step3KernelBounds.lean:649`). -/
private theorem JakKernel_sum_pole_sq_blockM_le_crude (hL : 3 ≤ L) (lam : ℝ) (y : Idx d L W) {u : ℂ}
    (hη : 0 < u.im) :
    ∑ α, ‖spectralPole hH u α‖ ^ 2 * ‖blockM d L W lam hH (siteBlock d L W y) α‖ ≤
      (u.im ^ 2)⁻¹ * (2 * (((W * L) ^ d : ℕ) : ℝ)) := by
  calc _ ≤ ∑ α, (u.im ^ 2)⁻¹ * ‖blockM d L W lam hH (siteBlock d L W y) α‖ := by
        refine Finset.sum_le_sum fun α _ => mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [← inv_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (JakKernel_pole_norm_le_inv_im hH hη α) 2
    _ = (u.im ^ 2)⁻¹ * ∑ α, ‖blockM d L W lam hH (siteBlock d L W y) α‖ := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_norm_blockM_le hL lam hH (siteBlock d L W y))
        (by positivity)

end Block

/-! ## 6. The pointwise bounds of the weighted `y`-term -/

section Pointwise

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- **Pointwise bound on the good event** (RBM1D `s3_pointwise_good`, `:741`, d = 2, per site
`y`).  On the single-scale grid event, with the window bound `|M_{y,α}| ≤ θ` off the blocks
flagged `Bad`, the weighted `y`-term of `L₁` (the integrand of the pin `Jak`) is at most the
product of the `Im m` rows times `N⁻¹ (α₁ + 1_{Bad} α₂) Q̄`; `N = (W L)²`. -/
theorem jak_pointwise_good (hL : 3 ≤ L) (lam : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) {m : ℕ} (s : Finset (Fin m))
    (w : Fin m → ℂ) (u : ℂ) {ηt Cb w' θ α₁ α₂ Qb : ℝ} (hηu : 0 < u.im) (hηu' : u.im ≤ ηt)
    (hηw : ∀ j, 0 < (w j).im) (hηw' : ∀ j, (w j).im ≤ ηt) (hCb : 0 ≤ Cb) (hw' : 0 < w')
    (hθ : 0 ≤ θ) (K K' : ℕ)
    (hG1 : ∀ k ≤ K, jakGridGood H ηt Cb u.re (2 ^ k * ηt))
    (hG2 : ∀ k ≤ K', jakGridGood H ηt Cb u.re (2 ^ k * w'))
    (hG3 : jakGridGood H ηt Cb u.re 0)
    (hG4 : ∀ j, jakGridGood H ηt Cb (w j).re 0)
    (Bad : Zd d L → Prop) [DecidablePred Bad]
    (hBad : ∀ a0, ¬ Bad a0 → ∀ α, |hH.eigenvalues α - u.re| ≤ w' →
      ‖blockM d L W lam hH a0 α‖ ≤ θ)
    (hα₁ : θ * (ηt / u.im ^ 2 * ((((W * L) ^ d : ℕ) : ℝ) * Cb)) +
        4 * (((W * L) ^ d : ℕ) : ℝ) * ηt * Cb *
          (2 * (((W * L) ^ d : ℕ) : ℝ) * Cb * (4 / w' + 4 * ηt / w' ^ 2)) +
        ((2 ^ K' * w') ^ 2)⁻¹ * (2 * (((W * L) ^ d : ℕ) : ℝ)) ≤ α₁)
    (hα₂ : 4 * (((W * L) ^ d : ℕ) : ℝ) * ηt * Cb *
        (ηt / u.im ^ 2 * ((((W * L) ^ d : ℕ) : ℝ) * Cb)) ≤ α₂)
    (hQb : 6 * (ηt / u.im) * Cb + 8 * K * Cb + (2 ^ K * ηt)⁻¹ ≤ Qb)
    (y : Idx d L W) (σ₁ σ₂ : Bool) :
    (∏ j ∈ s, (stieltjesN H (w j)).im) *
        ‖∑ x, (Gres H u σ₁ * Gres H u σ₁) x x * scirc d L W lam x y * Gres H u σ₂ y y‖ ≤
      (∏ j ∈ s, (ηt / (w j).im * Cb)) *
        ((((W * L) ^ d : ℕ) : ℝ)⁻¹ *
          ((α₁ + (if Bad (siteBlock d L W y) then α₂ else 0)) * Qb)) := by
  have hηt : 0 < ηt := lt_of_lt_of_le hηu hηu'
  have hN : (0 : ℝ) < (((W * L) ^ d : ℕ) : ℝ) := JakKernel_N_pos
  -- the `Im m` rows
  have hP : (∏ j ∈ s, (stieltjesN H (w j)).im) ≤ ∏ j ∈ s, (ηt / (w j).im * Cb) := by
    refine Finset.prod_le_prod₀
      (fun j _ => (JakKernel_stieltjesN_im_nonneg_le hH (hηw j)).1)
      fun j _ => JakKernel_stieltjesN_im_le_of_grid hH (hηw j) (hηw' j) (hG4 j)
  have hP0 : 0 ≤ ∏ j ∈ s, (ηt / (w j).im * Cb) :=
    Finset.prod_nonneg fun j _ => mul_nonneg (div_nonneg hηt.le (hηw j).le) hCb
  -- the `A_y` row
  have hA : ∑ α, ‖spectralPole hH u α‖ ^ 2 * ‖blockM d L W lam hH (siteBlock d L W y) α‖ ≤
      α₁ + (if Bad (siteBlock d L W y) then α₂ else 0) := by
    have hRd : (2 : ℝ) ^ K' * w' ≤ 2 ^ K' * w' := le_rfl
    have hGd := hG2 K' le_rfl
    by_cases hb : Bad (siteBlock d L W y)
    · simp only [hb, ite_true]
      have hwin : ∀ α, |hH.eigenvalues α - u.re| ≤ w' →
          ‖blockM d L W lam hH (siteBlock d L W y) α‖ ≤
            4 * (((W * L) ^ d : ℕ) : ℝ) * ηt * Cb := by
        intro α hα
        have h1 : w' ≤ 2 ^ K' * w' := le_mul_of_one_le_left hw'.le (one_le_pow₀ (by norm_num))
        exact JakKernel_norm_blockM_le_of_grid hH hL lam y hηt hGd (hα.trans h1)
      have h := JakKernel_sum_pole_sq_blockM_le hH hL lam y hηu hηu' hCb hw' (by positivity) K' hRd
        hGd hG2 hG3 hwin
      have hX : 0 ≤ θ * (ηt / u.im ^ 2 * ((((W * L) ^ d : ℕ) : ℝ) * Cb)) := by positivity
      linarith
    · simp only [hb, ite_false, add_zero]
      have h := JakKernel_sum_pole_sq_blockM_le hH hL lam y hηu hηu' hCb hw' hθ K' hRd hGd hG2 hG3
        (hBad _ hb)
      linarith
  have hQ : ∑ γ, ‖spectralPole hH u γ‖ * ‖hH.eigenvectorBasis γ y‖ ^ 2 ≤ Qb :=
    (JakKernel_sum_pole_mass_le hH hηu hηu' hCb K hG1 y).trans hQb
  have hα₁0 : 0 ≤ α₁ := le_trans (by positivity) hα₁
  have hα₂0 : 0 ≤ α₂ := le_trans (by positivity) hα₂
  have hAy0 : 0 ≤ α₁ + (if Bad (siteBlock d L W y) then α₂ else 0) :=
    add_nonneg hα₁0 (by split_ifs <;> linarith)
  -- the `y`-term
  have hK := norm_green_spectral_identity_blockM_le hL lam hH y hηu σ₁ σ₂
  simp only [spectralGsigPole_norm_eq_spectralPole, Complex.normSq_eq_norm_sq] at hK
  have hK' : ‖∑ x, (Gres H u σ₁ * Gres H u σ₁) x x * scirc d L W lam x y * Gres H u σ₂ y y‖ ≤
      (((W * L) ^ d : ℕ) : ℝ)⁻¹ *
        ((α₁ + (if Bad (siteBlock d L W y) then α₂ else 0)) * Qb) := by
    refine hK.trans ?_
    rw [mul_assoc]
    gcongr
  calc (∏ j ∈ s, (stieltjesN H (w j)).im) *
        ‖∑ x, (Gres H u σ₁ * Gres H u σ₁) x x * scirc d L W lam x y * Gres H u σ₂ y y‖
      ≤ (∏ j ∈ s, (ηt / (w j).im * Cb)) *
        ‖∑ x, (Gres H u σ₁ * Gres H u σ₁) x x * scirc d L W lam x y * Gres H u σ₂ y y‖ :=
        mul_le_mul_of_nonneg_right hP (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hK' hP0

/-- **Crude pointwise bound** (RBM1D `s3_pointwise_crude`, `:814`, d = 2, per site `y`), valid
for every Hermitian matrix: `∏ Im m(w_j) · |y-term| ≤ ∏ (Im w_j)⁻¹ · 2 (Im u)⁻³`. -/
theorem jak_pointwise_crude (hL : 3 ≤ L) (lam : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) {m : ℕ} (s : Finset (Fin m))
    (w : Fin m → ℂ) (u : ℂ) (hηu : 0 < u.im) (hηw : ∀ j, 0 < (w j).im)
    (y : Idx d L W) (σ₁ σ₂ : Bool) :
    (∏ j ∈ s, (stieltjesN H (w j)).im) *
        ‖∑ x, (Gres H u σ₁ * Gres H u σ₁) x x * scirc d L W lam x y * Gres H u σ₂ y y‖ ≤
      (∏ j ∈ s, (w j).im⁻¹) * (2 * (u.im⁻¹) ^ 3) := by
  have hN : (0 : ℝ) < (((W * L) ^ d : ℕ) : ℝ) := JakKernel_N_pos
  have hP : (∏ j ∈ s, (stieltjesN H (w j)).im) ≤ ∏ j ∈ s, (w j).im⁻¹ :=
    Finset.prod_le_prod₀ (fun j _ => (JakKernel_stieltjesN_im_nonneg_le hH (hηw j)).1)
      fun j _ => (JakKernel_stieltjesN_im_nonneg_le hH (hηw j)).2
  have hP0 : 0 ≤ ∏ j ∈ s, (w j).im⁻¹ := Finset.prod_nonneg fun j _ => (inv_pos.2 (hηw j)).le
  have hK := norm_green_spectral_identity_blockM_le hL lam hH y hηu σ₁ σ₂
  simp only [spectralGsigPole_norm_eq_spectralPole, Complex.normSq_eq_norm_sq] at hK
  have hA := JakKernel_sum_pole_sq_blockM_le_crude hH hL lam y hηu
  have hQ := JakKernel_sum_pole_mass_le_crude hH hηu y
  have hK' : ‖∑ x, (Gres H u σ₁ * Gres H u σ₁) x x * scirc d L W lam x y * Gres H u σ₂ y y‖ ≤
      2 * (u.im⁻¹) ^ 3 := by
    refine hK.trans ?_
    calc (((W * L) ^ d : ℕ) : ℝ)⁻¹ *
          (∑ α, ‖spectralPole hH u α‖ ^ 2 * ‖blockM d L W lam hH (siteBlock d L W y) α‖) *
          (∑ γ, ‖spectralPole hH u γ‖ * ‖hH.eigenvectorBasis γ y‖ ^ 2)
        ≤ (((W * L) ^ d : ℕ) : ℝ)⁻¹ * ((u.im ^ 2)⁻¹ * (2 * (((W * L) ^ d : ℕ) : ℝ))) *
            u.im⁻¹ := by
          gcongr
      _ = 2 * (u.im⁻¹) ^ 3 := by
          field_simp
  calc _ ≤ (∏ j ∈ s, (w j).im⁻¹) *
          ‖∑ x, (Gres H u σ₁ * Gres H u σ₁) x x * scirc d L W lam x y * Gres H u σ₂ y y‖ :=
        mul_le_mul_of_nonneg_right hP (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hK' hP0

end Pointwise

/-! ## 7. Compiled nonempty instances (`d = 3`, `L = 3`, `W = 2`, `N = 216`) -/

/-! At the scale `η = 1` one has `Im G_xx ≤ η⁻¹ = 1` at every energy for every Hermitian matrix, so the grid
event holds with `Cb = 1`, `ηt = 1` for every centre and radius (`gridGood_one`).  The data: `H = 1`
(the `216 × 216` identity), `u = w 0 = I`, `ηt = Cb = w' = 1`, `K = K' = 1`, `Bad ≡ False`, `θ = 2N = 432`,
`α₁ = 3079404`, `α₂ = 186624`, `Qb = 29/2`, `lam = 1/2`. -/
namespace JakKernelInst

/-- The `216 × 216` identity matrix, a Hermitian matrix on `Idx 3 3 2`. -/
noncomputable abbrev H1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ := 1

def y0 : Idx 3 3 2 := 0

theorem H1_herm : H1.IsHermitian := Matrix.isHermitian_one

/-- Crude bound for the diagonal of the resolvent: `Im G_xx(E + iη) ≤ η⁻¹` (RBM2D `im_green_le_inv`
`:978`; generic). -/
theorem im_Gres_le_inv {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) {η : ℝ} (hη : 0 < η) (E : ℝ) (x : n) :
    (Gres H ((E : ℂ) + η * Complex.I) true x x).im ≤ η⁻¹ := by
  rw [im_Gres_apply_self hH E hη]
  calc ∑ l, η * Complex.normSq (hH.eigenvectorBasis l x) /
        ((hH.eigenvalues l - E) ^ 2 + η ^ 2)
      ≤ ∑ l, η⁻¹ * ‖hH.eigenvectorBasis l x‖ ^ 2 := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [Complex.normSq_eq_norm_sq]
        have hv : 0 ≤ ‖hH.eigenvectorBasis l x‖ ^ 2 := by positivity
        have hD : 0 < (hH.eigenvalues l - E) ^ 2 + η ^ 2 := by positivity
        rw [div_le_iff₀ hD]
        have h1 : η * ‖hH.eigenvectorBasis l x‖ ^ 2 =
            η⁻¹ * ‖hH.eigenvectorBasis l x‖ ^ 2 * η ^ 2 := by field_simp
        rw [h1]
        have h2 : 0 ≤ η⁻¹ * ‖hH.eigenvectorBasis l x‖ ^ 2 := by positivity
        nlinarith [mul_nonneg h2 (sq_nonneg (hH.eigenvalues l - E))]
    _ = η⁻¹ := by rw [← Finset.mul_sum, JakKernel_sum_sq_norm_row hH x, mul_one]

/-- For `ηt = 1`, `Cb = 1` the grid event holds at every centre and radius, for every Hermitian matrix
(RBM2D `:999`). -/
theorem gridGood_one {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (E₀ r : ℝ) : jakGridGood H 1 1 E₀ r := by
  intro j _ x
  simpa using im_Gres_le_inv hH one_pos (E₀ - r + 2 * 1 * j) x

/-- The block bound `|M_{a₀,α}| ≤ 2N = 432` for every Hermitian matrix on `Idx 3 3 2`, every `lam`
(from `sum_norm_blockM_le`; RBM2D `blockM_le_72` `:1024`). -/
theorem blockM_le_432 {H : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ} (hH : H.IsHermitian) (lam : ℝ)
    (a0 : Zd 3 3) (α : Idx 3 3 2) : ‖blockM 3 3 2 lam hH a0 α‖ ≤ 432 := by
  have h := sum_norm_blockM_le (by norm_num : 3 ≤ 3) lam hH a0
  have h2 : ‖blockM 3 3 2 lam hH a0 α‖ ≤ ∑ β : Idx 3 3 2, ‖blockM 3 3 2 lam hH a0 β‖ :=
    Finset.single_le_sum (f := fun β : Idx 3 3 2 => ‖blockM 3 3 2 lam hH a0 β‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ α)
  have hN : (((2 * 3) ^ 3 : ℕ) : ℝ) = 216 := by norm_num
  have h3 : (((2 * 3) ^ 3 : ℕ) : ℝ) = 216 := hN
  rw [h3] at h
  linarith

/-- Target `sum_mass_window_le_of_im_green_le` at `H = 1`, `η = r = Cb = 1`, `E₀ = 0`, `x = y0`
(RBM2D `:1019`). -/
theorem inst_window :
    ∀ hH : H1.IsHermitian,
    ∑ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - 0| ≤ 1),
        ‖hH.eigenvectorBasis l y0‖ ^ 2 ≤ 2 * (1 + 2 * 1) * 1 :=
  fun hH => sum_mass_window_le_of_im_green_le hH one_pos zero_le_one zero_le_one 0 y0
    (fun j _ => by simpa using im_Gres_le_inv hH one_pos (0 - 1 + 2 * 1 * j) y0)

/-- Target `jak_pointwise_good` at the data above, every `y`, `σ₁`, `σ₂` (RBM2D `:1050`). -/
theorem inst_good (y : Idx 3 3 2) (σ₁ σ₂ : Bool) :
    (∏ _j ∈ ({0} : Finset (Fin 1)), (stieltjesN H1 Complex.I).im) *
        ‖∑ x, (Gres H1 Complex.I σ₁ * Gres H1 Complex.I σ₁) x x *
          scirc 3 3 2 (1 / 2) x y * Gres H1 Complex.I σ₂ y y‖ ≤
      (∏ _j ∈ ({0} : Finset (Fin 1)), (1 / Complex.I.im * 1)) *
        ((((2 * 3) ^ 3 : ℕ) : ℝ)⁻¹ * ((3079404 + (if False then (186624 : ℝ) else 0)) * (29 / 2))) :=
  jak_pointwise_good (d := 3) (L := 3) (W := 2) (by norm_num) (1 / 2) H1_herm
    ({0} : Finset (Fin 1)) (fun _ => Complex.I) Complex.I (ηt := 1) (Cb := 1) (w' := 1) (θ := 432)
    (α₁ := 3079404) (α₂ := 186624) (Qb := 29 / 2) (by simp) (by simp) (fun _ => by simp)
    (fun _ => by simp) zero_le_one one_pos (by norm_num) 1 1
    (fun k _ => gridGood_one H1_herm _ _) (fun k _ => gridGood_one H1_herm _ _)
    (gridGood_one H1_herm _ _) (fun _ => gridGood_one H1_herm _ _) (fun _ : Zd 3 3 => False)
    (fun a0 _ α _ => blockM_le_432 H1_herm _ a0 α) (by norm_num) (by norm_num) (by norm_num)
    y σ₁ σ₂

/-- A non-scalar Hermitian matrix on `Idx 3 3 2`: `diag(x₀.val)` (RBM2D `H2` `:1083`). -/
noncomputable abbrev H2 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ :=
  Matrix.diagonal (fun x : Idx 3 3 2 => ((((x 0).val : ℕ) : ℝ) : ℂ))

theorem H2_herm : H2.IsHermitian :=
  Matrix.isHermitian_diagonal_iff.mpr (fun i => by simp [IsSelfAdjoint])

/-- Target `jak_pointwise_good` at the non-scalar `H2`: `u = 1/2 + i`, `w 0 = -1 + i`, `s = {0}`,
`ηt = Cb = w' = 1`, `K = K' = 1`, `Bad a₀ ↔ a₀ = 0`, `θ = 432`, the same constants, any `y`, `σ₁`, `σ₂`
(RBM2D `:1099`). -/
example (y : Idx 3 3 2) (σ₁ σ₂ : Bool) :=
  jak_pointwise_good (d := 3) (L := 3) (W := 2) (by norm_num) (1 / 2) H2_herm
    ({0} : Finset (Fin 1)) (fun _ => (⟨-1, 1⟩ : ℂ)) (⟨1 / 2, 1⟩ : ℂ) (ηt := 1) (Cb := 1) (w' := 1)
    (θ := 432) (α₁ := 3079404) (α₂ := 186624) (Qb := 29 / 2) (by simp) (by simp)
    (fun _ => by simp) (fun _ => by simp) zero_le_one one_pos (by norm_num) 1 1
    (fun _ _ => gridGood_one H2_herm _ _) (fun _ _ => gridGood_one H2_herm _ _)
    (gridGood_one H2_herm _ _) (fun _ => gridGood_one H2_herm _ _) (fun a : Zd 3 3 => a = 0)
    (fun a0 _ α _ => blockM_le_432 H2_herm _ a0 α) (by norm_num) (by norm_num) (by norm_num)
    y σ₁ σ₂

/-- Target `jak_pointwise_crude` at `H = 1`, `s = {0}`, `w 0 = u = I`, `y = y0`, every `σ₁`, `σ₂`
(RBM2D `:1076`). -/
theorem inst_crude (σ₁ σ₂ : Bool) :
    (∏ _j ∈ ({0} : Finset (Fin 1)), (stieltjesN H1 Complex.I).im) *
        ‖∑ x, (Gres H1 Complex.I σ₁ * Gres H1 Complex.I σ₁) x x *
          scirc 3 3 2 (1 / 2) x y0 * Gres H1 Complex.I σ₂ y0 y0‖ ≤
      (∏ _j ∈ ({0} : Finset (Fin 1)), Complex.I.im⁻¹) * (2 * (Complex.I.im⁻¹) ^ 3) :=
  jak_pointwise_crude (d := 3) (L := 3) (W := 2) (by norm_num) (1 / 2) H1_herm
    ({0} : Finset (Fin 1)) (fun _ => Complex.I) Complex.I (by simp) (fun _ => by simp) y0 σ₁ σ₂

end JakKernelInst

#print axioms RBM.Univ.im_Gres_apply_self
#print axioms RBM.Univ.sum_mass_window_le_im_green
#print axioms RBM.Univ.sum_mass_window_le_of_im_green_le
#print axioms RBM.Univ.jak_pointwise_good
#print axioms RBM.Univ.jak_pointwise_crude
#print axioms RBM.Univ.JakKernelInst.im_Gres_le_inv
#print axioms RBM.Univ.JakKernelInst.gridGood_one
#print axioms RBM.Univ.JakKernelInst.blockM_le_432
#print axioms RBM.Univ.JakKernelInst.inst_window
#print axioms RBM.Univ.JakKernelInst.inst_good
#print axioms RBM.Univ.JakKernelInst.inst_crude

end RBM.Univ
