/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.JakKernel

/-!
# `RBM3D.Universality.UywKernel` (UN-22): the pair kernel layer of `(uywy7723r3rf)`

Paper: arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex` (cited `1_2:line`), the proof of
`Thm: B_Univ` `1_2:566-581`, the weighted `y`-term
`(∏_{j∈s} Im m(w_j)) |∑_x (G₁²)_{xy} S°_{xy} (G₂²)_{yx}|` of the pin `UNUyw` (`Pins.lean:708`,
integrand `:712-716`; model-generic `UNUywk`, `PinsK.lean:378`).
Port of RBM2D `Universality/UywKernel.lean` (commit `c9a24cf`, 1372 lines) to `Idx d L W`,
`scirc d L W lam`, `N = (W L)^d`, the merged resolvent `Gres` (RBM2D `RBM.green`, `Gsig`) and the
merged UN-19/UN-20 layers (`blockM`, `siteBlock`, `spectralPole`, `jakGridGood`,
`im_Gres_apply_self`).

* `blockM2`, the pair moment `M_{a₀,α,β}`: the `S^{(B)}(lam)`-weighted average (weights
  `SBR d L lam b a₀`, sum `1`, support `≤ 2d + 1` blocks; RBM2D: the `1/5` average over
  `a₀ + sbSupport L`) of the pair block QUE quantities `(N/W^d) ∑_{x∈[b]} conj ψ_β ψ_α - δ_{αβ}`
  (the overlap of the merged `queBadMat`); on the diagonal it is `blockM` (`blockM2_self`), and
  `M_{y,α,β} = N ∑_x ψ_α(x) conj ψ_β(x) S°_{xy}` (`blockM2_eq`);
* the exact spectral expansion of the `y`-term (`green_spectral_identity_blockM2`);
* the union bound from the pin `queBadMat` over the `2d + 1` blocks
  (`measure_bad2_le_of_queBadMat`);
* the bound on the single-scale grid event with the window bound `|M_{y,α,β}| ≤ θ` off the blocks
  flagged `Bad` (`uyw_pointwise_good`), and the crude bound valid for every Hermitian matrix
  (`uyw_pointwise_crude`).

Deterministic only: the one probability statement is the union bound from a hypothesised
`queBadMat` bound.  No pin is proved, stated or registered.  The file is `lam`-generic (band data
`sz.lam n`, model-generic data `K.lamV sz n`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Matrix
open RBM RBM.Gauss
open scoped ENNReal

namespace RBM.Univ

/-! ## 1. Generic index type: eigenvector normalisations, Stieltjes helpers, spectral decomposition -/

section Generic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The rows of the eigenvector matrix are unit vectors: `∑_l |ψ_l(x)|² = 1`
(RBM1D `Delocalization.lean:169`). -/
private theorem UywKernel_sum_sq_norm_row {H : Matrix n n ℂ} (hH : H.IsHermitian) (x : n) :
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
private theorem UywKernel_sum_sq_norm_col {H : Matrix n n ℂ} (hH : H.IsHermitian) (k : n) :
    ∑ p, ‖hH.eigenvectorBasis k p‖ ^ 2 = 1 := by
  have h := hH.eigenvectorBasis.orthonormal.1 k
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
  exact h

/-- `Im m(w) = |n|⁻¹ ∑_x Im G_xx(w)` (`stieltjesN` is `|n|⁻¹ tr Gres`, `Pins.lean:88`). -/
private theorem UywKernel_stieltjesN_im_eq_diag (H : Matrix n n ℂ) (w : ℂ) :
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
private theorem UywKernel_stieltjesN_im_eq (H : Matrix n n ℂ) (hH : H.IsHermitian) (E η : ℝ)
    (hη : 0 < η) :
    (stieltjesN H (E + η * Complex.I)).im =
      (Fintype.card n : ℝ)⁻¹ * ∑ l : n,
        (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2)) := by
  rw [UywKernel_stieltjesN_im_eq_diag]
  congr 1
  simp_rw [im_Gres_apply_self hH E hη]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hD : 0 < (hH.eigenvalues l - E) ^ 2 + η ^ 2 := by positivity
  rw [← Finset.sum_div, ← Finset.mul_sum]
  simp_rw [Complex.normSq_eq_norm_sq]
  rw [UywKernel_sum_sq_norm_col hH l, mul_one]

/-- Monotonicity used between (2.27) and (2.28): `η Im m(E+iη)` is nondecreasing in `η`
(RBM1D `StieltjesEtaMonotone.lean:64`). -/
private theorem UywKernel_stieltjesN_eta_mul_im_mono (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (E η ηTilde : ℝ) (hη : 0 < η) (hηTilde : η ≤ ηTilde) :
    η * (stieltjesN H (E + η * Complex.I)).im ≤
      ηTilde * (stieltjesN H (E + ηTilde * Complex.I)).im := by
  have hformula := UywKernel_stieltjesN_im_eq H hH E η hη
  have hformulaT := UywKernel_stieltjesN_im_eq H hH E ηTilde (by linarith)
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
private theorem UywKernel_gridGood_zero_stieltjes [Nonempty n] {H : Matrix n n ℂ} {η Cb E₀ : ℝ}
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
private theorem UywKernel_dyadic_le_sum {f : ℝ → ℝ} (hf : ∀ a b, 0 < a → a ≤ b → f b ≤ f a)
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

private theorem UywKernel_geom_half_sum_le (K : ℕ) :
    ∑ k ∈ Finset.range K, ((2 : ℝ) ^ k)⁻¹ ≤ 2 := by
  have h := sum_geometric_two_le K
  simpa [one_div, inv_pow] using h

/-! ## 2. Off-diagonal entries of `Gres * Gres` in the eigenbasis -/

private theorem UywKernel_eigenvalues_ne_of_im_ne {H : Matrix n n ℂ} (hH : H.IsHermitian)
    {w : ℂ} (hw : w.im ≠ 0) : ∀ α, (hH.eigenvalues α : ℂ) ≠ w := by
  intro α h
  have him := congrArg Complex.im h
  simp at him
  exact hw him.symm

private theorem UywKernel_im_gsig_ne {z : ℂ} (hη : 0 < z.im) (σ : Bool) :
    (if σ then z else (starRingEnd ℂ) z).im ≠ 0 := by
  cases σ <;> simp [hη.ne']

/-- `U* U = 1` for the matrix `U x α = ψ_α(x)` of an orthonormal family (copy of the private
`JakSpectral_star_mul_self`, `JakSpectral.lean:80`). -/
private theorem UywKernel_star_mul_self {H : Matrix n n ℂ} {μ : n → ℝ} {ψ : n → n → ℂ}
    (hψ : IsOrthoEigenbasis H μ ψ) :
    star (Matrix.of fun y l => ψ l y) * (Matrix.of fun y l => ψ l y) = 1 := by
  ext k k'
  have h := hψ.1 k k'
  simp only [dotProduct, Pi.star_apply] at h
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply]
  exact h

/-- The spectral decomposition `Gres H w true = U diag((μ_α - w)⁻¹) U*`, `U x α = ψ_α(x)` (copy of the
private `JakSpectral_Gres_eq_spectral`, `JakSpectral.lean:92`, which is not callable from another file;
replaces RBM2D `RBM.green_eq_spectral`, `Delocalization.lean:47`). -/
private theorem UywKernel_Gres_eq_spectral {H : Matrix n n ℂ} {μ : n → ℝ} {ψ : n → n → ℂ}
    (hψ : IsOrthoEigenbasis H μ ψ) {w : ℂ} (hz : ∀ l, (μ l : ℂ) ≠ w) :
    Gres H w true = (Matrix.of fun y l => ψ l y) * diagonal (fun l => ((μ l : ℂ) - w)⁻¹) *
      star (Matrix.of fun y l => ψ l y) := by
  set U : Matrix n n ℂ := Matrix.of fun y l => ψ l y with hU
  have hUU : star U * U = 1 := UywKernel_star_mul_self hψ
  have hUU' : U * star U = 1 := mul_eq_one_comm.mp hUU
  have hHU : H * U = U * diagonal (fun l => (μ l : ℂ)) := by
    ext y l
    have h := congrFun (hψ.2 l) y
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [mul_diagonal, Matrix.mul_apply]
    simp only [hU, Matrix.of_apply]
    rw [h, mul_comm]
  have hsub : (H - w • 1) * U = U * diagonal (fun l => (μ l : ℂ) - w) := by
    rw [Matrix.sub_mul, hHU, Matrix.smul_mul, Matrix.one_mul, ← diagonal_sub,
      Matrix.mul_sub, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  unfold Gres
  simp only [↓reduceIte, ← Matrix.nonsing_inv_eq_ringInverse]
  apply Matrix.inv_eq_right_inv
  calc (H - w • 1) * (U * diagonal (fun l => ((μ l : ℂ) - w)⁻¹) * star U)
      = ((H - w • 1) * U) * diagonal (fun l => ((μ l : ℂ) - w)⁻¹) * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * (diagonal (fun l => (μ l : ℂ) - w)
          * diagonal (fun l => ((μ l : ℂ) - w)⁻¹)) * star U := by
        rw [hsub]; simp only [Matrix.mul_assoc]
    _ = 1 := by
        have hd : (fun l => ((μ l : ℂ) - w) * ((μ l : ℂ) - w)⁻¹) = fun _ => (1 : ℂ) :=
          funext fun l => mul_inv_cancel₀ (sub_ne_zero.mpr (hz l))
        rw [diagonal_mul_diagonal, hd, diagonal_one, Matrix.mul_one, hUU']

/-- General (off-diagonal) entries of the squared resolvent in the eigenbasis (RBM2D `:258`,
`green H w ^ 2` ↦ `Gres H w true * Gres H w true`; the diagonal case is the merged `Gres_sq_apply_self`,
`JakSpectral.lean:125`). -/
private theorem UywKernel_Gres_sq_apply {H : Matrix n n ℂ} (hH : H.IsHermitian) {w : ℂ}
    (hw : ∀ α, (hH.eigenvalues α : ℂ) ≠ w) (x y : n) :
    (Gres H w true * Gres H w true) x y =
      ∑ α, spectralPole hH w α * spectralPole hH w α *
        (hH.eigenvectorBasis α x * star (hH.eigenvectorBasis α y)) := by
  have hψ := isOrthoEigenbasis_eigenvectorBasis hH
  set U : Matrix n n ℂ := Matrix.of fun y l => hH.eigenvectorBasis l y with hU
  let d : n → ℂ := fun α => spectralPole hH w α
  have hUU : star U * U = 1 := UywKernel_star_mul_self hψ
  have hG : Gres H w true = U * diagonal d * star U := by
    simpa [U, d, spectralPole] using UywKernel_Gres_eq_spectral hψ hw
  have hG2 : Gres H w true * Gres H w true = U * diagonal (fun α => d α * d α) * star U := by
    rw [hG]
    calc
      (U * diagonal d * star U) * (U * diagonal d * star U) =
          U * diagonal d * (star U * U) * diagonal d * star U := by noncomm_ring
      _ = U * diagonal d * 1 * diagonal d * star U := by rw [hUU]
      _ = U * (diagonal d * diagonal d) * star U := by
        simp only [mul_one]
        rw [← Matrix.mul_assoc U (diagonal d) (diagonal d)]
      _ = U * diagonal (fun α => d α * d α) * star U := by
        rw [diagonal_mul_diagonal]
  rw [hG2, mul_apply]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [mul_diagonal, star_apply]
  simp only [hU, Matrix.of_apply, RCLike.star_def, d]
  ring

/-- General (off-diagonal) entries of `Gres H z σ * Gres H z σ` in the eigenbasis (RBM2D `:290`,
`Gsig H z σ ^ 2` ↦ `Gres H z σ * Gres H z σ`). -/
private theorem UywKernel_Gsig_sq_apply {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hη : 0 < z.im) (σ : Bool) (x y : n) :
    (Gres H z σ * Gres H z σ) x y =
      ∑ α, spectralGsigPole hH z σ α * spectralGsigPole hH z σ α *
        (hH.eigenvectorBasis α x * star (hH.eigenvectorBasis α y)) := by
  have heig := UywKernel_eigenvalues_ne_of_im_ne hH (UywKernel_im_gsig_ne hη σ)
  have hG : Gres H z σ = Gres H (if σ then z else (starRingEnd ℂ) z) true := by
    cases σ <;> simp [Gres]
  rw [hG]
  exact UywKernel_Gres_sq_apply hH heig x y

/-! ## 3. Pole bounds (generic index type) -/

variable {H : Matrix n n ℂ} (hH : H.IsHermitian)

private theorem UywKernel_pole_norm_eq (u : ℂ) (α : n) :
    ‖spectralPole hH u α‖ = ‖(hH.eigenvalues α : ℂ) - u‖⁻¹ := by
  rw [spectralPole, norm_inv]

private theorem UywKernel_pole_norm_le_inv_im {u : ℂ} (hη : 0 < u.im) (α : n) :
    ‖spectralPole hH u α‖ ≤ u.im⁻¹ := by
  rw [UywKernel_pole_norm_eq]
  have h : u.im ≤ ‖(hH.eigenvalues α : ℂ) - u‖ := by
    have := Complex.abs_im_le_norm ((hH.eigenvalues α : ℂ) - u)
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at this
    rwa [abs_of_pos hη] at this
  exact inv_anti₀ hη h

private theorem UywKernel_pole_norm_le_inv_dist {u : ℂ} (α : n)
    (hd : 0 < |hH.eigenvalues α - u.re|) :
    ‖spectralPole hH u α‖ ≤ |hH.eigenvalues α - u.re|⁻¹ := by
  rw [UywKernel_pole_norm_eq]
  have h : |hH.eigenvalues α - u.re| ≤ ‖(hH.eigenvalues α : ℂ) - u‖ := by
    have := Complex.abs_re_le_norm ((hH.eigenvalues α : ℂ) - u)
    simpa only [Complex.sub_re, Complex.ofReal_re] using this
  exact inv_anti₀ hd h

private theorem UywKernel_pole_norm_sq_eq {u : ℂ} (α : n) :
    ‖spectralPole hH u α‖ ^ 2 = ((hH.eigenvalues α - u.re) ^ 2 + u.im ^ 2)⁻¹ := by
  rw [UywKernel_pole_norm_eq, inv_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  congr 1
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub]
  ring

private theorem UywKernel_pole_norm_sq_le_inv_dist_sq {u : ℂ} (α : n)
    (hd : 0 < |hH.eigenvalues α - u.re|) :
    ‖spectralPole hH u α‖ ^ 2 ≤ (|hH.eigenvalues α - u.re| ^ 2)⁻¹ := by
  rw [← inv_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (UywKernel_pole_norm_le_inv_dist hH α hd) 2

include hH in
/-- Crude bound `Im m(w) ≤ 1/Im w`, and `Im m(w) ≥ 0`. -/
private theorem UywKernel_stieltjesN_im_nonneg_le [Nonempty n] {w : ℂ} (hη : 0 < w.im) :
    0 ≤ (stieltjesN H w).im ∧ (stieltjesN H w).im ≤ w.im⁻¹ := by
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
  have hf := UywKernel_stieltjesN_im_eq H hH w.re w.im hη
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
private theorem UywKernel_stieltjesN_im_le_of_grid [Nonempty n] {w : ℂ} (hη : 0 < w.im)
    {ηt Cb : ℝ} (hηη : w.im ≤ ηt) (hG : jakGridGood H ηt Cb w.re 0) :
    (stieltjesN H w).im ≤ ηt / w.im * Cb := by
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
  have hmono := UywKernel_stieltjesN_eta_mul_im_mono H hH w.re w.im ηt hη hηη
  rw [← hw] at hmono
  have hT := UywKernel_gridGood_zero_stieltjes (H := H) hG
  have hηt : 0 < ηt := lt_of_lt_of_le hη hηη
  rw [div_mul_eq_mul_div, le_div_iff₀ hη, mul_comm]
  exact hmono.trans (mul_le_mul_of_nonneg_left hT hηt.le)

private theorem UywKernel_pole_norm_sq_le_inv_im {u : ℂ} (hη : 0 < u.im) (α : n) :
    ‖spectralPole hH u α‖ ^ 2 ≤ (u.im⁻¹) ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg _) (UywKernel_pole_norm_le_inv_im hH hη α) 2

/-- **The `Q` row.** `∑_α |p_α(u)|² |u_α(z)|² ≤ (η̃/η²) Cb` from the zero-radius grid at `Re u`. -/
private theorem UywKernel_sum_pole_sq_mass_le_of_grid {u : ℂ} (hη : 0 < u.im) {ηt Cb : ℝ}
    (hηη : u.im ≤ ηt) (hG : jakGridGood H ηt Cb u.re 0) (z : n) :
    ∑ α, ‖spectralPole hH u α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2 ≤ ηt / u.im ^ 2 * Cb := by
  have hηt : 0 < ηt := lt_of_lt_of_le hη hηη
  have hGz : (Gres H ((u.re : ℂ) + ηt * Complex.I) true z z).im ≤ Cb := by
    have := hG 0 (by simp) z
    simpa using this
  rw [im_Gres_apply_self hH u.re hηt z] at hGz
  have hterm : ∀ α : n, ‖spectralPole hH u α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2 ≤
      ηt / u.im ^ 2 * (ηt * Complex.normSq (hH.eigenvectorBasis α z) /
        ((hH.eigenvalues α - u.re) ^ 2 + ηt ^ 2)) := by
    intro α
    rw [UywKernel_pole_norm_sq_eq, Complex.normSq_eq_norm_sq]
    set x := (hH.eigenvalues α - u.re) ^ 2
    set v := ‖hH.eigenvectorBasis α z‖ ^ 2
    have hx : 0 ≤ x := sq_nonneg _
    have hv : 0 ≤ v := by positivity
    rw [show ηt / u.im ^ 2 * (ηt * v / (x + ηt ^ 2)) = ηt ^ 2 * v / (u.im ^ 2 * (x + ηt ^ 2)) by
      field_simp]
    rw [inv_mul_eq_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h2 : u.im ^ 2 ≤ ηt ^ 2 := pow_le_pow_left₀ hη.le hηη 2
    have h3 : u.im ^ 2 * (x + ηt ^ 2) ≤ ηt ^ 2 * (x + u.im ^ 2) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h3 hv]
  calc _ ≤ ∑ α : n, ηt / u.im ^ 2 * (ηt * Complex.normSq (hH.eigenvectorBasis α z) /
        ((hH.eigenvalues α - u.re) ^ 2 + ηt ^ 2)) := Finset.sum_le_sum fun α _ => hterm α
    _ = ηt / u.im ^ 2 * ∑ α : n, ηt * Complex.normSq (hH.eigenvectorBasis α z) /
        ((hH.eigenvalues α - u.re) ^ 2 + ηt ^ 2) := by rw [Finset.mul_sum]
    _ ≤ _ := by gcongr

/-- Crude `Q` row: `∑_α |p_α(u)|² |u_α(z)|² ≤ (Im u)⁻²`. -/
private theorem UywKernel_sum_pole_sq_mass_le_crude {u : ℂ} (hη : 0 < u.im) (z : n) :
    ∑ α, ‖spectralPole hH u α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2 ≤ (u.im⁻¹) ^ 2 := by
  calc _ ≤ ∑ α, (u.im⁻¹) ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2 :=
        Finset.sum_le_sum fun α _ =>
          mul_le_mul_of_nonneg_right (UywKernel_pole_norm_sq_le_inv_im hH hη α) (by positivity)
    _ = (u.im⁻¹) ^ 2 := by rw [← Finset.mul_sum, UywKernel_sum_sq_norm_row hH z, mul_one]

/-- `∑_α |p_α|² = ∑_z ∑_α |p_α|² |u_α(z)|²` (completeness of each eigenvector). -/
private theorem UywKernel_sum_pole_sq_eq (u : ℂ) :
    ∑ α, ‖spectralPole hH u α‖ ^ 2 =
      ∑ z : n, ∑ α, ‖spectralPole hH u α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Finset.mul_sum, UywKernel_sum_sq_norm_col hH α, mul_one]

/-- **The `Q^out` row.** Out-of-window part (`|λ_α - Re u| > w'`) of `∑_α |p_α|² |u_α(z)|²`, from
the grids of radii `2^k w'`, `k ≤ K'` (dyadic shells and the covering lemma), and completeness
beyond `2^{K'} w'`. -/
private theorem UywKernel_sum_pole_sq_mass_out_le {u : ℂ} {ηt Cb w' : ℝ} (hηt : 0 < ηt)
    (hCb : 0 ≤ Cb)
    (hw' : 0 < w') (K' : ℕ) (hG : ∀ k ≤ K', jakGridGood H ηt Cb u.re (2 ^ k * w')) (z : n) :
    ∑ α, (if |hH.eigenvalues α - u.re| ≤ w' then 0 else
        ‖spectralPole hH u α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2) ≤
      Cb * (8 / w' + 8 * ηt / w' ^ 2) + ((2 ^ K' * w') ^ 2)⁻¹ := by
  set v : n → ℝ := fun γ => ‖hH.eigenvectorBasis γ z‖ ^ 2 with hv
  set dd : n → ℝ := fun γ => |hH.eigenvalues γ - u.re| with hdd
  have hv0 : ∀ γ, 0 ≤ v γ := fun γ => by positivity
  have hpt : ∀ γ, (if dd γ ≤ w' then 0 else ‖spectralPole hH u γ‖ ^ 2 * v γ) ≤
      ∑ k ∈ Finset.range K', ((2 ^ k * w') ^ 2)⁻¹ *
          (if dd γ ≤ 2 ^ (k + 1) * w' then v γ else 0) + ((2 ^ K' * w') ^ 2)⁻¹ * v γ := by
    intro γ
    have hS0 : 0 ≤ ∑ k ∈ Finset.range K', ((2 ^ k * w') ^ 2)⁻¹ *
        (if dd γ ≤ 2 ^ (k + 1) * w' then v γ else 0) :=
      Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (by split_ifs <;> simp [hv0])
    have hT0 : 0 ≤ ((2 ^ K' * w') ^ 2)⁻¹ * v γ := mul_nonneg (by positivity) (hv0 γ)
    by_cases h1 : dd γ ≤ w'
    · simp only [h1, ite_true]; linarith
    · push Not at h1
      simp only [not_le.2 h1, ite_false]
      have hdpos : 0 < dd γ := lt_trans hw' h1
      have hpd := mul_le_mul_of_nonneg_right
        (UywKernel_pole_norm_sq_le_inv_dist_sq hH γ hdpos) (hv0 γ)
      by_cases h2 : dd γ ≤ 2 ^ K' * w'
      · have hdy := UywKernel_dyadic_le_sum (f := fun x => (x ^ 2)⁻¹)
          (fun a b ha hab => inv_anti₀ (by positivity) (pow_le_pow_left₀ ha.le hab 2))
          (fun a ha => by positivity) hw' K' h1 h2
        have hdy' : (dd γ ^ 2)⁻¹ * v γ ≤ ∑ k ∈ Finset.range K', ((2 ^ k * w') ^ 2)⁻¹ *
            (if dd γ ≤ 2 ^ (k + 1) * w' then v γ else 0) := by
          calc (dd γ ^ 2)⁻¹ * v γ ≤ (∑ k ∈ Finset.range K',
                (if dd γ ≤ 2 ^ (k + 1) * w' then ((2 ^ k * w') ^ 2)⁻¹ else 0)) * v γ :=
                mul_le_mul_of_nonneg_right hdy (hv0 γ)
            _ = _ := by
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl fun k _ => ?_
                split_ifs <;> ring
        linarith
      · push Not at h2
        have : (dd γ ^ 2)⁻¹ * v γ ≤ ((2 ^ K' * w') ^ 2)⁻¹ * v γ :=
          mul_le_mul_of_nonneg_right
            (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h2.le 2)) (hv0 γ)
        linarith
  have hmass : ∀ r : ℝ, 0 ≤ r → jakGridGood H ηt Cb u.re r →
      ∑ γ, (if dd γ ≤ r then v γ else 0) ≤ 2 * (r + 2 * ηt) * Cb := by
    intro r hr hGr
    rw [← Finset.sum_filter]
    exact sum_mass_window_le_of_im_green_le hH hηt hr hCb u.re z fun j hj => hGr j hj z
  have hmk : ∀ k ∈ Finset.range K', ((2 ^ k * w') ^ 2)⁻¹ *
      ∑ γ, (if dd γ ≤ 2 ^ (k + 1) * w' then v γ else 0) ≤
        Cb * (4 / w' + 4 * ηt / w' ^ 2) * ((2 : ℝ) ^ k)⁻¹ := by
    intro k hk
    have hkK : k + 1 ≤ K' := Finset.mem_range.1 hk
    have h := hmass (2 ^ (k + 1) * w') (by positivity) (hG (k + 1) hkK)
    have hp : (0 : ℝ) < 2 ^ k * w' := by positivity
    calc _ ≤ ((2 ^ k * w') ^ 2)⁻¹ * (2 * (2 ^ (k + 1) * w' + 2 * ηt) * Cb) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = Cb * (4 / w' * ((2 : ℝ) ^ k)⁻¹ +
            4 * ηt / w' ^ 2 * ((2 : ℝ) ^ k)⁻¹ * ((2 : ℝ) ^ k)⁻¹) := by
          field_simp; ring
      _ ≤ Cb * (4 / w' * ((2 : ℝ) ^ k)⁻¹ + 4 * ηt / w' ^ 2 * ((2 : ℝ) ^ k)⁻¹ * 1) := by
          gcongr
          exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
      _ = _ := by ring
  have hsumv : ∑ γ, v γ = 1 := UywKernel_sum_sq_norm_row hH z
  calc ∑ α, (if |hH.eigenvalues α - u.re| ≤ w' then 0 else
        ‖spectralPole hH u α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2)
      = ∑ γ, (if dd γ ≤ w' then 0 else ‖spectralPole hH u γ‖ ^ 2 * v γ) := rfl
    _ ≤ ∑ γ, (∑ k ∈ Finset.range K', ((2 ^ k * w') ^ 2)⁻¹ *
          (if dd γ ≤ 2 ^ (k + 1) * w' then v γ else 0) + ((2 ^ K' * w') ^ 2)⁻¹ * v γ) :=
        Finset.sum_le_sum fun γ _ => hpt γ
    _ = ∑ k ∈ Finset.range K', ((2 ^ k * w') ^ 2)⁻¹ *
            ∑ γ, (if dd γ ≤ 2 ^ (k + 1) * w' then v γ else 0) +
          ((2 ^ K' * w') ^ 2)⁻¹ * ∑ γ, v γ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range K', Cb * (4 / w' + 4 * ηt / w' ^ 2) * ((2 : ℝ) ^ k)⁻¹ +
          ((2 ^ K' * w') ^ 2)⁻¹ * 1 := by
        rw [hsumv]
        have := Finset.sum_le_sum hmk
        linarith
    _ = Cb * (4 / w' + 4 * ηt / w' ^ 2) * ∑ k ∈ Finset.range K', ((2 : ℝ) ^ k)⁻¹ +
          ((2 ^ K' * w') ^ 2)⁻¹ := by rw [Finset.mul_sum, mul_one]
    _ ≤ Cb * (4 / w' + 4 * ηt / w' ^ 2) * 2 + ((2 ^ K' * w') ^ 2)⁻¹ := by
        gcongr; exact UywKernel_geom_half_sum_le K'
    _ = _ := by ring

end Generic

/-! ## 4. Pair combinatorics (abstract, index-free) -/

section Pair

variable {ι : Type*} [Fintype ι]

/-- AM–GM on a (restricted) one-index sum: `∑_{α∉W} P_α a_α(x) a_α(y) ≤ o` whenever
`∑_{α∉W} P_α a_α(z)² ≤ o` for every `z`. -/
private theorem UywKernel_amgm_sum (P : ι → ℝ) (a : ι → ι → ℝ) (W : ι → Prop) [DecidablePred W]
    (hP : ∀ α, 0 ≤ P α) {o : ℝ}
    (ho : ∀ z, ∑ α, (if W α then 0 else P α * a α z ^ 2) ≤ o) (x y : ι) :
    ∑ α, (if W α then 0 else P α * (a α x * a α y)) ≤ o := by
  have hpt : ∀ α, (if W α then 0 else P α * (a α x * a α y)) ≤
      (1 / 2) * (if W α then 0 else P α * a α x ^ 2) +
        (1 / 2) * (if W α then 0 else P α * a α y ^ 2) := by
    intro α
    split_ifs
    · simp
    · have := mul_le_mul_of_nonneg_left (two_mul_le_add_sq (a α x) (a α y)) (hP α)
      nlinarith
  calc _ ≤ ∑ α, ((1 / 2) * (if W α then 0 else P α * a α x ^ 2) +
        (1 / 2) * (if W α then 0 else P α * a α y ^ 2)) := Finset.sum_le_sum fun α _ => hpt α
    _ = (1 / 2) * ∑ α, (if W α then 0 else P α * a α x ^ 2) +
        (1 / 2) * ∑ α, (if W α then 0 else P α * a α y ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ (1 / 2) * o + (1 / 2) * o := by gcongr <;> [exact ho x; exact ho y]
    _ = o := by ring

private theorem UywKernel_sum_ite_nonneg (P : ι → ℝ) (a : ι → ι → ℝ) (W : ι → Prop)
    [DecidablePred W]
    (hP : ∀ α, 0 ≤ P α) (ha : ∀ α x, 0 ≤ a α x) (x y : ι) :
    0 ≤ ∑ α, (if W α then 0 else P α * (a α x * a α y)) :=
  Finset.sum_nonneg fun α _ => by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hP α) (mul_nonneg (ha α x) (ha α y))

/-- The "rest" sum factorizes: `∑_{α∉W₁} ∑_β P₁P₂ (N∑_x s_x a_α(x)a_β(x)) a_α(y)a_β(y)
= N ∑_x s_x F₁^{out}(x) F₂(x)`. -/
private theorem UywKernel_rest_eq (P₁ P₂ : ι → ℝ) (a : ι → ι → ℝ) (s : ι → ℝ) (y : ι) (Nn : ℝ)
    (W₁ : ι → Prop) [DecidablePred W₁] :
    ∑ α, ∑ β, (if W₁ α then 0 else
        P₁ α * P₂ β * (Nn * ∑ x, s x * (a α x * a β x)) * (a α y * a β y)) =
      Nn * ∑ x, s x * ((∑ α, (if W₁ α then 0 else P₁ α * (a α x * a α y))) *
        ∑ β, P₂ β * (a β x * a β y)) := by
  have hpt : ∀ α β, (if W₁ α then 0 else
      P₁ α * P₂ β * (Nn * ∑ x, s x * (a α x * a β x)) * (a α y * a β y)) =
      ∑ x, Nn * (s x * ((if W₁ α then 0 else P₁ α * (a α x * a α y)) *
        (P₂ β * (a β x * a β y)))) := by
    intro α β
    split_ifs
    · simp
    · simp only [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
  simp_rw [hpt]
  rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul_sum, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm]

/-- **Pair combinatorics.** Window pairs (`W₁ × W₂`, where `M ≤ θ`) plus the rest (where
`M ≤ N ∑_x s_x a_α(x) a_β(x)`), each reduced by AM–GM to the one-index bounds `q_i`, `o_i`
(out-of-window) and `S_i` (total weight). -/
private theorem UywKernel_pair_abstract (P₁ P₂ : ι → ℝ) (a M : ι → ι → ℝ) (s : ι → ℝ) (y : ι)
    {Nn θ q₁ q₂ o₁ o₂ S₁ S₂ : ℝ} (W₁ W₂ : ι → Prop) [DecidablePred W₁] [DecidablePred W₂]
    (hP₁ : ∀ α, 0 ≤ P₁ α) (hP₂ : ∀ α, 0 ≤ P₂ α) (ha : ∀ α x, 0 ≤ a α x)
    (hs : ∀ x, 0 ≤ s x) (hsum : ∑ x, s x ≤ 2) (hN : 0 ≤ Nn) (hθ : 0 ≤ θ)
    (hM : ∀ α β, M α β ≤ Nn * ∑ x, s x * (a α x * a β x))
    (hMw : ∀ α β, W₁ α → W₂ β → M α β ≤ θ)
    (hq₁ : ∀ z, ∑ α, P₁ α * a α z ^ 2 ≤ q₁) (hq₂ : ∀ z, ∑ α, P₂ α * a α z ^ 2 ≤ q₂)
    (ho₁ : ∀ z, ∑ α, (if W₁ α then 0 else P₁ α * a α z ^ 2) ≤ o₁)
    (ho₂ : ∀ z, ∑ α, (if W₂ α then 0 else P₂ α * a α z ^ 2) ≤ o₂)
    (hS₁ : ∑ α, P₁ α ≤ S₁) (hS₂ : ∑ α, P₂ α ≤ S₂) :
    ∑ α, ∑ β, P₁ α * P₂ β * M α β * (a α y * a β y) ≤
      θ / 2 * (q₁ * S₂ + S₁ * q₂) + 2 * Nn * (o₁ * q₂ + q₁ * o₂) := by
  classical
  set X : ι → ι → ℝ := fun α β =>
    P₁ α * P₂ β * (Nn * ∑ x, s x * (a α x * a β x)) * (a α y * a β y) with hX
  have hX0 : ∀ α β, 0 ≤ X α β := fun α β => by
    have : 0 ≤ ∑ x, s x * (a α x * a β x) :=
      Finset.sum_nonneg fun x _ => mul_nonneg (hs x) (mul_nonneg (ha α x) (ha β x))
    have := hP₁ α; have := hP₂ β; have := ha α y; have := ha β y
    simp only [X]; positivity
  have hpt : ∀ α β, P₁ α * P₂ β * M α β * (a α y * a β y) ≤
      θ / 2 * (P₁ α * a α y ^ 2 * P₂ β + P₁ α * (P₂ β * a β y ^ 2)) +
        (if W₁ α then 0 else X α β) + (if W₂ β then 0 else X α β) := by
    intro α β
    have hc : 0 ≤ P₁ α * P₂ β * (a α y * a β y) :=
      mul_nonneg (mul_nonneg (hP₁ α) (hP₂ β)) (mul_nonneg (ha α y) (ha β y))
    have hθt : 0 ≤ θ / 2 * (P₁ α * a α y ^ 2 * P₂ β + P₁ α * (P₂ β * a β y ^ 2)) := by
      have := hP₁ α; have := hP₂ β; positivity
    have hrest : P₁ α * P₂ β * M α β * (a α y * a β y) ≤ X α β := by
      have := mul_le_mul_of_nonneg_left (hM α β) hc
      simp only [X]; nlinarith
    by_cases h1 : W₁ α <;> by_cases h2 : W₂ β
    · simp only [h1, h2, ite_true, add_zero]
      have hw := mul_le_mul_of_nonneg_left (hMw α β h1 h2) hc
      have hag := mul_le_mul_of_nonneg_left (two_mul_le_add_sq (a α y) (a β y))
        (mul_nonneg (mul_nonneg hθ (hP₁ α)) (hP₂ β))
      nlinarith
    · simp only [h1, h2, ite_true, ite_false]; linarith
    · simp only [h1, h2, ite_true, ite_false, add_zero]; linarith
    · simp only [h1, h2, ite_false]; linarith [hX0 α β]
  -- the three sums
  have hq₁0 : 0 ≤ q₁ := le_trans (Finset.sum_nonneg fun α _ => by
    have := hP₁ α; positivity) (hq₁ y)
  have hq₂0 : 0 ≤ q₂ := le_trans (Finset.sum_nonneg fun α _ => by
    have := hP₂ α; positivity) (hq₂ y)
  have hG₁ : ∀ x, ∑ α, P₁ α * (a α x * a α y) ≤ q₁ := fun x => by
    simpa using UywKernel_amgm_sum P₁ a (fun _ => False) hP₁ (o := q₁) (by simpa using hq₁) x y
  have hG₂ : ∀ x, ∑ α, P₂ α * (a α x * a α y) ≤ q₂ := fun x => by
    simpa using UywKernel_amgm_sum P₂ a (fun _ => False) hP₂ (o := q₂) (by simpa using hq₂) x y
  have hG₁0 : ∀ x, 0 ≤ ∑ α, P₁ α * (a α x * a α y) := fun x =>
    Finset.sum_nonneg fun α _ => mul_nonneg (hP₁ α) (mul_nonneg (ha α x) (ha α y))
  have hG₂0 : ∀ x, 0 ≤ ∑ α, P₂ α * (a α x * a α y) := fun x =>
    Finset.sum_nonneg fun α _ => mul_nonneg (hP₂ α) (mul_nonneg (ha α x) (ha α y))
  have hS1 : ∑ α, ∑ β, θ / 2 * (P₁ α * a α y ^ 2 * P₂ β + P₁ α * (P₂ β * a β y ^ 2)) ≤
      θ / 2 * (q₁ * S₂ + S₁ * q₂) := by
    have e : ∑ α, ∑ β, θ / 2 * (P₁ α * a α y ^ 2 * P₂ β + P₁ α * (P₂ β * a β y ^ 2)) =
        θ / 2 * ((∑ α, P₁ α * a α y ^ 2) * (∑ β, P₂ β) +
          (∑ α, P₁ α) * ∑ β, P₂ β * a β y ^ 2) := by
      rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
    rw [e]
    have hP₂s : 0 ≤ ∑ β, P₂ β := Finset.sum_nonneg fun β _ => hP₂ β
    have hP₁s : 0 ≤ ∑ α, P₁ α := Finset.sum_nonneg fun α _ => hP₁ α
    have hQ₂0 : 0 ≤ ∑ β, P₂ β * a β y ^ 2 := Finset.sum_nonneg fun β _ => by
      have := hP₂ β; positivity
    have hS₁0 : 0 ≤ S₁ := hP₁s.trans hS₁
    gcongr
    · exact hq₁ y
    · exact hq₂ y
  have hS2 : ∑ α, ∑ β, (if W₁ α then 0 else X α β) ≤ 2 * Nn * (o₁ * q₂) := by
    rw [UywKernel_rest_eq P₁ P₂ a s y Nn W₁]
    have hF : ∀ x, ∑ α, (if W₁ α then 0 else P₁ α * (a α x * a α y)) ≤ o₁ :=
      fun x => UywKernel_amgm_sum P₁ a W₁ hP₁ ho₁ x y
    have hF0 : ∀ x, 0 ≤ ∑ α, (if W₁ α then 0 else P₁ α * (a α x * a α y)) :=
      fun x => UywKernel_sum_ite_nonneg P₁ a W₁ hP₁ ha x y
    have ho₁0 : 0 ≤ o₁ := (hF0 y).trans (hF y)
    calc Nn * ∑ x, s x * ((∑ α, (if W₁ α then 0 else P₁ α * (a α x * a α y))) *
          ∑ β, P₂ β * (a β x * a β y)) ≤ Nn * ∑ x, s x * (o₁ * q₂) := by
          gcongr with x
          all_goals first | exact hs x | exact hF x | exact hG₂ x | exact hG₂0 x
      _ = Nn * (∑ x, s x) * (o₁ * q₂) := by rw [← Finset.sum_mul, mul_assoc]
      _ ≤ Nn * 2 * (o₁ * q₂) := by gcongr
      _ = _ := by ring
  have hS3 : ∑ α, ∑ β, (if W₂ β then 0 else X α β) ≤ 2 * Nn * (q₁ * o₂) := by
    have e : ∀ α β, (if W₂ β then 0 else X α β) = (if W₂ β then 0 else
        P₂ β * P₁ α * (Nn * ∑ x, s x * (a β x * a α x)) * (a β y * a α y)) := by
      intro α β
      simp only [X]
      rw [show ∑ x, s x * (a β x * a α x) = ∑ x, s x * (a α x * a β x) from
        Finset.sum_congr rfl fun x _ => by ring]
      split_ifs <;> ring
    simp_rw [e]
    rw [Finset.sum_comm, UywKernel_rest_eq P₂ P₁ a s y Nn W₂]
    have hF : ∀ x, ∑ α, (if W₂ α then 0 else P₂ α * (a α x * a α y)) ≤ o₂ :=
      fun x => UywKernel_amgm_sum P₂ a W₂ hP₂ ho₂ x y
    have hF0 : ∀ x, 0 ≤ ∑ α, (if W₂ α then 0 else P₂ α * (a α x * a α y)) :=
      fun x => UywKernel_sum_ite_nonneg P₂ a W₂ hP₂ ha x y
    have ho₂0 : 0 ≤ o₂ := (hF0 y).trans (hF y)
    calc Nn * ∑ x, s x * ((∑ α, (if W₂ α then 0 else P₂ α * (a α x * a α y))) *
          ∑ β, P₁ β * (a β x * a β y)) ≤ Nn * ∑ x, s x * (o₂ * q₁) := by
          gcongr with x
          all_goals first | exact hs x | exact hF x | exact hG₁ x | exact hG₁0 x
      _ = Nn * (∑ x, s x) * (o₂ * q₁) := by rw [← Finset.sum_mul, mul_assoc]
      _ ≤ Nn * 2 * (o₂ * q₁) := by gcongr
      _ = _ := by ring
  calc _ ≤ ∑ α, ∑ β, (θ / 2 * (P₁ α * a α y ^ 2 * P₂ β + P₁ α * (P₂ β * a β y ^ 2)) +
        (if W₁ α then 0 else X α β) + (if W₂ β then 0 else X α β)) :=
        Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ => hpt α β
    _ = ∑ α, ∑ β, θ / 2 * (P₁ α * a α y ^ 2 * P₂ β + P₁ α * (P₂ β * a β y ^ 2)) +
        ∑ α, ∑ β, (if W₁ α then 0 else X α β) + ∑ α, ∑ β, (if W₂ β then 0 else X α β) := by
        simp only [Finset.sum_add_distrib]
    _ ≤ _ := by linarith

end Pair

/-! ## 5. The variance profile -/

section Aux

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem UywKernel_N_pos : (0 : ℝ) < (((W * L) ^ d : ℕ) : ℝ) := by
  exact_mod_cast pow_pos (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne W))
    (Nat.pos_of_ne_zero (NeZero.ne L))) d

/-- Column sums of the variance profile: `∑_x S_{xy} = 1` for `3 ≤ L`, every `lam` (copy of the private
`JakSpectral_sum_svarF_col`, `JakSpectral.lean:445`; replaces RBM2D `JakKernel_sum_norm_Spaper` `:642`). -/
private theorem UywKernel_sum_svarF_col (hL : 3 ≤ L) (lam : ℝ) (y : Idx d L W) :
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

private theorem UywKernel_scirc_norm_le (lam : ℝ) (x y : Idx d L W) :
    ‖scirc d L W lam x y‖ ≤ svarF d L W lam x y + (((W * L) ^ d : ℕ) : ℝ)⁻¹ := by
  unfold scirc
  calc ‖((svarF d L W lam x y : ℝ) : ℂ) - ((((W * L) ^ d : ℕ) : ℂ))⁻¹‖
      ≤ ‖((svarF d L W lam x y : ℝ) : ℂ)‖ + ‖((((W * L) ^ d : ℕ) : ℂ))⁻¹‖ := norm_sub_le _ _
    _ = _ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (svarF_nonneg d L W lam x y),
          norm_inv, Complex.norm_natCast]

/-- The weight sum: `∑_x (S_{xy} + N⁻¹) = 2` (the constant `2` of RBM2D `:661`; copy of the private
`JakSpectral_profile_weight_sum`, `JakSpectral.lean:496`). -/
private theorem UywKernel_profile_weight_sum (hL : 3 ≤ L) (lam : ℝ) (y : Idx d L W) :
    ∑ x : Idx d L W, (svarF d L W lam x y + (((W * L) ^ d : ℕ) : ℝ)⁻¹) = 2 := by
  rw [Finset.sum_add_distrib, UywKernel_sum_svarF_col hL lam y]
  have hN : (((W * L) ^ d : ℕ) : ℝ) ≠ 0 := ne_of_gt UywKernel_N_pos
  have hconst : ∑ _x : Idx d L W, (((W * L) ^ d : ℕ) : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, card_Idx, nsmul_eq_mul]
    field_simp
  rw [hconst]
  norm_num

end Aux

/-! ## 6. The pair moment `M_{a₀,α,β}` (`2d + 1` weights) -/

/-- The pair moment `M_{a₀,α,β}` (`d ≥ 3` form of RBM2D `blockM2` `:760`): the `S^{(B)}(lam)`-weighted average
(weights `SBR d L lam b a₀`, sum `1`, support `≤ 2d + 1` blocks) of the pair block QUE quantities
`(N/W^d) ∑_{x∈[b]} conj ψ_β(x) ψ_α(x) - δ_{αβ}` (the overlap of the merged `queBadMat` at `i = β`, `j = α`).
At `α = β` it is the merged `blockM` (`blockM2_self`). -/
noncomputable def blockM2 (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (a0 : Zd d L) (α β : Idx d L W) : ℂ :=
  ∑ b : Zd d L, ((SBR d L lam b a0 : ℝ) : ℂ) *
    ((((W * L) ^ d : ℕ) : ℂ) / (W : ℂ) ^ d *
        (∑ x ∈ Iblk d L W b, star (hH.eigenvectorBasis β x) * hH.eigenvectorBasis α x) -
      (if α = β then 1 else 0))

/-- Target 1a: `blockM2` on the diagonal is the merged `blockM` (RBM2D `blockM2_self` `:769`, there `rfl`). -/
theorem blockM2_self {d L W : ℕ} [NeZero L] [NeZero W] (lam : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (a0 : Zd d L) (α : Idx d L W) :
    blockM2 d L W lam hH a0 α α = blockM d L W lam hH a0 α := by
  simp [blockM2, blockM]

section Block

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- Grouping a sum over the fine lattice by blocks, against the variance profile at a site `y`:
`∑_x f(x) S_{xy} = W^{-d} ∑_b SBR(b, [y]) ∑_{x∈[b]} f(x)` (the `hgroup` step of `unMy_eq`,
`Pins.lean:1171`, for a complex-valued `f`). -/
private theorem UywKernel_sum_svarF_group (lam : ℝ) (y : Idx d L W) (f : Idx d L W → ℂ) :
    ∑ x, f x * ((svarF d L W lam x y : ℝ) : ℂ) =
      ((W : ℂ) ^ d)⁻¹ * ∑ b : Zd d L, ((SBR d L lam b (siteBlock d L W y) : ℝ) : ℂ) *
        ∑ x ∈ Iblk d L W b, f x := by
  rw [← Finset.sum_fiberwise Finset.univ (fun x => (split d L W x).1)
    (fun x => f x * ((svarF d L W lam x y : ℝ) : ℂ)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxb : (split d L W x).1 = b := (Finset.mem_filter.mp hx).2
  simp only [svarF, siteBlock, hxb]
  push_cast
  ring

/-- Target 1b: `M_{y,α,β} = N ∑_x ψ_α(x) conj ψ_β(x) S°_{xy}` (RBM2D `blockM2_eq` `:800`; the `SBR` form:
`S_{xy} = W^{-d} SBR([x],[y])`, the block partition of `∑_x`, `∑_b SBR(b,[y]) = 1`, and the orthonormality
`∑_x conj ψ_β ψ_α = δ_{αβ}` cancelling the `-N⁻¹` part of `S°`); needs `3 ≤ L` for the row sum. -/
theorem blockM2_eq (hL : 3 ≤ L) (lam : ℝ) {H : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hH : H.IsHermitian) (y α β : Idx d L W) :
    blockM2 d L W lam hH (siteBlock d L W y) α β =
      (((W * L) ^ d : ℕ) : ℂ) *
        ∑ x, (hH.eigenvectorBasis α x * star (hH.eigenvectorBasis β x)) * scirc d L W lam x y := by
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have hWd : (W : ℂ) ^ d ≠ 0 := pow_ne_zero d hW
  have hN : (((W * L) ^ d : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero d (Nat.mul_ne_zero (NeZero.ne W) (NeZero.ne L)))
  set a : Zd d L := siteBlock d L W y with ha
  set N : ℂ := (((W * L) ^ d : ℕ) : ℂ) with hNdef
  have hrow : ∑ b : Zd d L, ((SBR d L lam b a : ℝ) : ℂ) = 1 := by
    have h : ∑ b : Zd d L, SBR d L lam b a = 1 := by
      simp_rw [SBR_comm _ a]
      exact sum_SBR_row hL a
    exact_mod_cast h
  have horth : ∑ x, hH.eigenvectorBasis α x * star (hH.eigenvectorBasis β x) =
      if α = β then 1 else 0 := by
    have h := (isOrthoEigenbasis_eigenvectorBasis hH).1 β α
    simp only [dotProduct, Pi.star_apply] at h
    rw [show (if α = β then (1 : ℂ) else 0) = if β = α then 1 else 0 by simp only [eq_comm]]
    rw [← h]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  have hT : ∀ b : Zd d L, ∑ x ∈ Iblk d L W b, star (hH.eigenvectorBasis β x) *
      hH.eigenvectorBasis α x = ∑ x ∈ Iblk d L W b, hH.eigenvectorBasis α x *
        star (hH.eigenvectorBasis β x) := fun b => Finset.sum_congr rfl fun x _ => mul_comm _ _
  have hg := UywKernel_sum_svarF_group lam y (fun x => hH.eigenvectorBasis α x *
    star (hH.eigenvectorBasis β x))
  set T : Zd d L → ℂ := fun b => ∑ x ∈ Iblk d L W b, hH.eigenvectorBasis α x *
    star (hH.eigenvectorBasis β x) with hTdef
  have e1 : blockM2 d L W lam hH a α β =
      N / (W : ℂ) ^ d * ∑ b : Zd d L, ((SBR d L lam b a : ℝ) : ℂ) * T b -
        (if α = β then 1 else 0) := by
    unfold blockM2
    have : ∀ b : Zd d L, ((SBR d L lam b a : ℝ) : ℂ) *
        (N / (W : ℂ) ^ d * (∑ x ∈ Iblk d L W b, star (hH.eigenvectorBasis β x) *
          hH.eigenvectorBasis α x) - (if α = β then 1 else 0)) =
        N / (W : ℂ) ^ d * (((SBR d L lam b a : ℝ) : ℂ) * T b) -
          ((SBR d L lam b a : ℝ) : ℂ) * (if α = β then 1 else 0) := by
      intro b
      rw [hT b]
      ring
    rw [Finset.sum_congr rfl fun b _ => this b, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, hrow, one_mul]
  have e2 : ∑ x, (hH.eigenvectorBasis α x * star (hH.eigenvectorBasis β x)) * scirc d L W lam x y =
      ((W : ℂ) ^ d)⁻¹ * ∑ b : Zd d L, ((SBR d L lam b a : ℝ) : ℂ) * T b -
        N⁻¹ * (if α = β then 1 else 0) := by
    unfold scirc
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib, hg, ← Finset.sum_mul, horth, ← ha]
    simp only [hTdef]
    ring
  rw [e1, e2]
  field_simp

end Block

/-! ## 7. The exact spectral expansion of the `y`-term -/

section BlockGreen

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- Exact eigenbasis expansion of the `y`-term before substituting `blockM2_eq` (RBM2D `:840`). -/
private theorem UywKernel_sum_variance2 (lam : ℝ) {Hm : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hH : Hm.IsHermitian) (y : Idx d L W) (z₁ z₂ : ℂ) (hη₁ : 0 < z₁.im) (hη₂ : 0 < z₂.im)
    (σ₁ σ₂ : Bool) :
    (∑ x : Idx d L W, (Gres Hm z₁ σ₁ * Gres Hm z₁ σ₁) x y * scirc d L W lam x y *
        (Gres Hm z₂ σ₂ * Gres Hm z₂ σ₂) y x) =
      ∑ α : Idx d L W, ∑ β : Idx d L W,
        (spectralGsigPole hH z₁ σ₁ α * spectralGsigPole hH z₁ σ₁ α) *
          (spectralGsigPole hH z₂ σ₂ β * spectralGsigPole hH z₂ σ₂ β) *
          (star (hH.eigenvectorBasis α y) * hH.eigenvectorBasis β y) *
          ∑ x : Idx d L W, (hH.eigenvectorBasis α x * star (hH.eigenvectorBasis β x)) *
            scirc d L W lam x y := by
  set S0 : Idx d L W → ℂ := fun x => scirc d L W lam x y with hS0
  set A : Idx d L W → Idx d L W → ℂ := fun γ x => hH.eigenvectorBasis γ x with hA
  calc
    (∑ x : Idx d L W, (Gres Hm z₁ σ₁ * Gres Hm z₁ σ₁) x y * S0 x *
        (Gres Hm z₂ σ₂ * Gres Hm z₂ σ₂) y x) =
        ∑ x : Idx d L W, (∑ α : Idx d L W, spectralGsigPole hH z₁ σ₁ α * spectralGsigPole hH z₁ σ₁ α *
            (A α x * star (A α y))) * S0 x *
          ∑ β : Idx d L W, spectralGsigPole hH z₂ σ₂ β * spectralGsigPole hH z₂ σ₂ β *
            (A β y * star (A β x)) := by
          congr 1
          funext x
          rw [UywKernel_Gsig_sq_apply hH hη₁ σ₁ x y, UywKernel_Gsig_sq_apply hH hη₂ σ₂ y x]
    _ = ∑ α : Idx d L W, ∑ β : Idx d L W,
          (spectralGsigPole hH z₁ σ₁ α * spectralGsigPole hH z₁ σ₁ α) *
            (spectralGsigPole hH z₂ σ₂ β * spectralGsigPole hH z₂ σ₂ β) *
            (star (A α y) * A β y) *
            ∑ x : Idx d L W, (A α x * star (A β x)) * S0 x := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun β _ => ?_
        refine Finset.sum_congr rfl fun x _ => ?_
        ring

/-- Target 2: the exact spectral expansion of the `y`-term of `L₂` (the integrand of the pin `UNUyw`,
`Pins.lean:712-716`), with `M_{y,α,β}` substituted from `blockM2_eq` (RBM2D `:877`;
`Gsig H z σ ^ 2` ↦ `Gres H z σ * Gres H z σ`, `spectralGsigPole … ^ 2` ↦ `p * p` as the merged
`green_spectral_identity_blockM`). -/
theorem green_spectral_identity_blockM2 (hL : 3 ≤ L) (lam : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (y : Idx d L W) (z₁ z₂ : ℂ)
    (hη₁ : 0 < z₁.im) (hη₂ : 0 < z₂.im) (σ₁ σ₂ : Bool) :
    (∑ x : Idx d L W, (Gres H z₁ σ₁ * Gres H z₁ σ₁) x y * scirc d L W lam x y *
        (Gres H z₂ σ₂ * Gres H z₂ σ₂) y x) =
      ((((W * L) ^ d : ℕ) : ℂ))⁻¹ * ∑ α : Idx d L W, ∑ β : Idx d L W,
        spectralGsigPole hH z₁ σ₁ α * spectralGsigPole hH z₁ σ₁ α *
          (spectralGsigPole hH z₂ σ₂ β * spectralGsigPole hH z₂ σ₂ β) *
            blockM2 d L W lam hH (siteBlock d L W y) α β *
              star (hH.eigenvectorBasis α y) * hH.eigenvectorBasis β y := by
  have hN : (((W * L) ^ d : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero d (Nat.mul_ne_zero (NeZero.ne W) (NeZero.ne L)))
  rw [UywKernel_sum_variance2 lam hH y z₁ z₂ hη₁ hη₂ σ₁ σ₂, eq_inv_mul_iff_mul_eq₀ hN,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [blockM2_eq hL lam hH y α β]
  ring

end BlockGreen

/-! ## 8. The pair bad event is rare: the union bound from `queBadMat` -/

section Que

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The pair analogue of `unBadY_subset` (`Pins.lean:1205`): if two eigenvalues are in the window
`|λ - E| ≤ N⁻¹ W^{𝔡/3}` and the weighted average `M_{a₀,α,β}` has modulus `≥ W^{-𝔡/6}`, then some block `b` of
positive weight carries a `queBadMat` failure at `(i, j) = (β, α)` (`(ε₀, c) = (𝔡/3, 𝔡/6)`; the weights
`SBR b a₀ ≥ 0` sum to `1`; the window is inside `𝓘_E(𝔡/3)` by `un_window_sub`, which needs `(eq:WO)`). -/
private theorem UywKernel_bad2_subset (hL : 3 ≤ L) {lam 𝔡 E : ℝ} (hW : 1 ≤ (W : ℝ)) (h𝔡 : 0 < 𝔡)
    (hlam : (W : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ lam) (a0 : Zd d L)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) (α β : Idx d L W)
    (hα : |hM.eigenvalues α - E| ≤ (((W * L) ^ d : ℕ) : ℝ)⁻¹ * (W : ℝ) ^ (𝔡 / 3))
    (hβ : |hM.eigenvalues β - E| ≤ (((W * L) ^ d : ℕ) : ℝ)⁻¹ * (W : ℝ) ^ (𝔡 / 3))
    (hθ : (W : ℝ) ^ (-(𝔡 / 6)) ≤ ‖blockM2 d L W lam hM a0 α β‖) :
    ∃ b : Zd d L, SBR d L lam b a0 ≠ 0 ∧ queBadMat d L W lam (𝔡 / 3) (𝔡 / 6) E b M := by
  have hW0 : (0 : ℝ) < (W : ℝ) := lt_of_lt_of_le one_pos hW
  have hN : (0 : ℝ) < (((W * L) ^ d : ℕ) : ℝ) := UywKernel_N_pos
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := by positivity
  set N : ℝ := (((W * L) ^ d : ℕ) : ℝ) with hNdef
  set u : Zd d L → ℂ := fun b => (((W * L) ^ d : ℕ) : ℂ) / (W : ℂ) ^ d *
    (∑ x ∈ Iblk d L W b, star (hM.eigenvectorBasis β x) * hM.eigenvectorBasis α x) -
      (if α = β then 1 else 0) with hu
  have hrow : ∑ b : Zd d L, SBR d L lam b a0 = 1 := by
    simp_rw [SBR_comm _ a0]
    exact sum_SBR_row hL a0
  have hwnn : ∀ b, 0 ≤ SBR d L lam b a0 := fun b => sbKernelR_nonneg d L lam _
  have hMu : blockM2 d L W lam hM a0 α β = ∑ b, ((SBR d L lam b a0 : ℝ) : ℂ) * u b := rfl
  by_contra hcon
  push Not at hcon
  -- every block of positive weight has `‖u b‖ < θ`
  have hlt : ∀ b, SBR d L lam b a0 ≠ 0 → ‖u b‖ < (W : ℝ) ^ (-(𝔡 / 6)) := by
    intro b hb0
    by_contra hge
    push Not at hge
    refine hcon b hb0 ⟨hM.eigenvalues, fun k x => hM.eigenvectorBasis k x,
      isOrthoEigenbasis_eigenvectorBasis hM, β, α, ?_, ?_, ?_⟩
    · exact hβ.trans (un_window_sub (d := d) hW hN h𝔡 hlam)
    · exact hα.trans (un_window_sub (d := d) hW hN h𝔡 hlam)
    · -- the block quantity: `u b = (N/W^d) (S_b - (W^d/N) δ)`
      have hrel : u b = (((W * L) ^ d : ℕ) : ℂ) / (W : ℂ) ^ d *
          ((∑ x ∈ Iblk d L W b, star (hM.eigenvectorBasis β x) * hM.eigenvectorBasis α x) -
            (W : ℂ) ^ d / (((W * L) ^ d : ℕ) : ℂ) * (if β = α then 1 else 0)) := by
        have hWdc : (W : ℂ) ^ d ≠ 0 := pow_ne_zero d (Nat.cast_ne_zero.mpr (NeZero.ne W))
        have hNc : (((W * L) ^ d : ℕ) : ℂ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (pow_ne_zero d (Nat.mul_ne_zero (NeZero.ne W) (NeZero.ne L)))
        have hite : (if α = β then (1 : ℂ) else 0) = if β = α then 1 else 0 := by
          simp only [eq_comm]
        simp only [hu, mul_sub, hite]
        congr 1
        field_simp
      have hnorm : ‖u b‖ = N / (W : ℝ) ^ d *
          ‖(∑ x ∈ Iblk d L W b, star (hM.eigenvectorBasis β x) * hM.eigenvectorBasis α x) -
            (W : ℂ) ^ d / (((W * L) ^ d : ℕ) : ℂ) * (if β = α then 1 else 0)‖ := by
        rw [hrel, norm_mul, norm_div, Complex.norm_natCast, norm_pow, Complex.norm_natCast]
      have hWc : (W : ℝ) ^ ((d : ℝ) - 𝔡 / 6) = (W : ℝ) ^ d * (W : ℝ) ^ (-(𝔡 / 6)) := by
        rw [sub_eq_add_neg, Real.rpow_add hW0, Real.rpow_natCast]
      rw [hWc]
      have hq : (W : ℝ) ^ (-(𝔡 / 6)) ≤ N / (W : ℝ) ^ d *
          ‖(∑ x ∈ Iblk d L W b, star (hM.eigenvectorBasis β x) * hM.eigenvectorBasis α x) -
            (W : ℂ) ^ d / (((W * L) ^ d : ℕ) : ℂ) * (if β = α then 1 else 0)‖ := hnorm ▸ hge
      rw [div_le_iff₀ hN]
      have h2 := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ (W : ℝ) ^ d / N)
      have h3 : (W : ℝ) ^ d / N * (N / (W : ℝ) ^ d) = 1 := by field_simp
      calc (W : ℝ) ^ d * (W : ℝ) ^ (-(𝔡 / 6))
          = (W : ℝ) ^ d / N * (W : ℝ) ^ (-(𝔡 / 6)) * N := by field_simp
        _ ≤ (W : ℝ) ^ d / N * (N / (W : ℝ) ^ d *
            ‖(∑ x ∈ Iblk d L W b, star (hM.eigenvectorBasis β x) * hM.eigenvectorBasis α x) -
              (W : ℂ) ^ d / (((W * L) ^ d : ℕ) : ℂ) * (if β = α then 1 else 0)‖) * N := by
            gcongr
        _ = ‖(∑ x ∈ Iblk d L W b, star (hM.eigenvectorBasis β x) * hM.eigenvectorBasis α x) -
              (W : ℂ) ^ d / (((W * L) ^ d : ℕ) : ℂ) * (if β = α then 1 else 0)‖ * N := by
            rw [← mul_assoc, h3, one_mul]
  -- contradiction with `θ ≤ ‖∑ w u‖`
  obtain ⟨b₀, hb₀⟩ : ∃ b₀, SBR d L lam b₀ a0 ≠ 0 := by
    by_contra h0; push Not at h0
    simp [h0] at hrow
  have hsum : ∑ b, SBR d L lam b a0 * ‖u b‖ < ∑ b, SBR d L lam b a0 * (W : ℝ) ^ (-(𝔡 / 6)) := by
    refine Finset.sum_lt_sum (fun b _ => ?_) ⟨b₀, Finset.mem_univ _, ?_⟩
    · by_cases hz : SBR d L lam b a0 = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (hlt b hz).le (hwnn b)
    · exact mul_lt_mul_of_pos_left (hlt b₀ hb₀) (lt_of_le_of_ne (hwnn b₀) (Ne.symm hb₀))
  have habs : ‖∑ b, ((SBR d L lam b a0 : ℝ) : ℂ) * u b‖ ≤ ∑ b, SBR d L lam b a0 * ‖u b‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hwnn b)]
  rw [hMu] at hθ
  rw [← Finset.sum_mul, hrow, one_mul] at hsum
  linarith

/-- Target 3: **the pair bad event of `(uywy7723r3rf)` is rare, from QUE** (RBM2D `measure_bad2_le_of_queBadMat`
`:909`; the `d ≥ 3` data of the merged `measure_bad_le_of_queBadMat`, `JakSpectral.lean:559`): if the failure event
`queBadMat` of `(Meq:QUE)` at `(ε₀, c) = (𝔡/3, 𝔡/6)` and energy `E` has probability `≤ p` for each block `b`, then
`P(∃ α β, |λ_α - E| ≤ N⁻¹W^{𝔡/3}, |λ_β - E| ≤ N⁻¹W^{𝔡/3}, |M_{a₀,α,β}| ≥ W^{-𝔡/6}) ≤ (2d + 1) p` (union
over the at most `2d + 1` blocks `b` with `SBR b a₀ ≠ 0`; `queBadMat` already quantifies the pair `i, j`).
`3 ≤ L` and `(eq:WO)` `W^{-d/2+𝔡} ≤ lam` are the hypotheses of the merged one-index form. -/
theorem measure_bad2_le_of_queBadMat {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hL : 3 ≤ L) {lam 𝔡 E : ℝ} (hW : 1 ≤ (W : ℝ)) (h𝔡 : 0 < 𝔡)
    (hlam : (W : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ lam) (a0 : Zd d L)
    {Hr : Ω → Matrix (Idx d L W) (Idx d L W) ℂ} (hH : ∀ ω, (Hr ω).IsHermitian) (p : ℝ≥0∞)
    (hp : ∀ b : Zd d L, P {ω | queBadMat d L W lam (𝔡 / 3) (𝔡 / 6) E b (Hr ω)} ≤ p) :
    P {ω | ∃ α β, |(hH ω).eigenvalues α - E| ≤ (((W * L) ^ d : ℕ) : ℝ)⁻¹ * (W : ℝ) ^ (𝔡 / 3) ∧
        |(hH ω).eigenvalues β - E| ≤ (((W * L) ^ d : ℕ) : ℝ)⁻¹ * (W : ℝ) ^ (𝔡 / 3) ∧
        (W : ℝ) ^ (-(𝔡 / 6)) ≤ ‖blockM2 d L W lam (hH ω) a0 α β‖} ≤
      ((2 * d + 1 : ℕ) : ℝ≥0∞) * p := by
  classical
  set s := Finset.univ.filter fun b : Zd d L => SBR d L lam b a0 ≠ 0 with hs
  have hsub : {ω | ∃ α β, |(hH ω).eigenvalues α - E| ≤
        (((W * L) ^ d : ℕ) : ℝ)⁻¹ * (W : ℝ) ^ (𝔡 / 3) ∧
        |(hH ω).eigenvalues β - E| ≤ (((W * L) ^ d : ℕ) : ℝ)⁻¹ * (W : ℝ) ^ (𝔡 / 3) ∧
        (W : ℝ) ^ (-(𝔡 / 6)) ≤ ‖blockM2 d L W lam (hH ω) a0 α β‖} ⊆
      ⋃ b ∈ s, {ω | queBadMat d L W lam (𝔡 / 3) (𝔡 / 6) E b (Hr ω)} := by
    rintro ω ⟨α, β, hα, hβ, hM⟩
    obtain ⟨b, hb0, hb⟩ := UywKernel_bad2_subset hL hW h𝔡 hlam a0 (hH ω) α β hα hβ hM
    exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb0⟩) hb
  calc _ ≤ P (⋃ b ∈ s, {ω | queBadMat d L W lam (𝔡 / 3) (𝔡 / 6) E b (Hr ω)}) := measure_mono hsub
    _ ≤ ∑ b ∈ s, P {ω | queBadMat d L W lam (𝔡 / 3) (𝔡 / 6) E b (Hr ω)} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _b ∈ s, p := Finset.sum_le_sum fun b _ => hp b
    _ = (s.card : ℝ≥0∞) * p := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 * d + 1 : ℕ) : ℝ≥0∞) * p := by
        gcongr
        exact_mod_cast unBadY_card_le hL lam a0

end Que

/-! ## 9. The `A_y` row and the pointwise bounds of the weighted `y`-term -/

section Pointwise

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `|M_{y,α,β}| ≤ N ∑_x (S_{xy} + N⁻¹) |ψ_α(x)| |ψ_β(x)|` (RBM2D `UywKernel_norm_blockM2_le` `:973`;
`‖Spaper‖ ↦ svarF`). -/
private theorem UywKernel_norm_blockM2_le (hL : 3 ≤ L) (lam : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (y α β : Idx d L W) :
    ‖blockM2 d L W lam hH (siteBlock d L W y) α β‖ ≤ (((W * L) ^ d : ℕ) : ℝ) *
      ∑ x : Idx d L W, (svarF d L W lam x y + (((W * L) ^ d : ℕ) : ℝ)⁻¹) *
        (‖hH.eigenvectorBasis α x‖ * ‖hH.eigenvectorBasis β x‖) := by
  rw [blockM2_eq hL lam hH y α β, norm_mul, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
  refine Finset.sum_le_sum fun x _ => ?_
  rw [norm_mul, norm_mul, norm_star]
  calc ‖hH.eigenvectorBasis α x‖ * ‖hH.eigenvectorBasis β x‖ * ‖scirc d L W lam x y‖
      ≤ ‖hH.eigenvectorBasis α x‖ * ‖hH.eigenvectorBasis β x‖ *
          (svarF d L W lam x y + (((W * L) ^ d : ℕ) : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (UywKernel_scirc_norm_le lam x y) (by positivity)
    _ = _ := by ring

private theorem UywKernel_ite_abs_neg_one (x t : ℝ) : (if |x| ≤ -1 then (0 : ℝ) else t) = t := by
  have h : ¬ |x| ≤ -1 := by linarith [abs_nonneg x]
  simp [h]

/-- **The `A_y` row.** For a window radius `w'` (take `w' < 0` for no window), with window pairs
bounded by `θ`: `A_y ≤ (θ/2)(q₁ N q₂ + N q₁ q₂) + 2N(o₁q₂ + q₁o₂)`, with
`A_y = ∑_{α,β} |p₁α|²|p₂β|²|M_{y,α,β}||ψ_α(y)||ψ_β(y)|` (RBM2D `UywKernel_A_le` `:996`). -/
private theorem UywKernel_A_le (hL : 3 ≤ L) (lam : ℝ) {H : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hH : H.IsHermitian) (u₁ u₂ : ℂ) (y : Idx d L W) {θ q₁ q₂ o₁ o₂ w' : ℝ} (hθ : 0 ≤ θ)
    (hMw : ∀ α β, |hH.eigenvalues α - u₁.re| ≤ w' → |hH.eigenvalues β - u₂.re| ≤ w' →
      ‖blockM2 d L W lam hH (siteBlock d L W y) α β‖ ≤ θ)
    (hq₁ : ∀ z, ∑ α, ‖spectralPole hH u₁ α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2 ≤ q₁)
    (hq₂ : ∀ z, ∑ α, ‖spectralPole hH u₂ α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2 ≤ q₂)
    (ho₁ : ∀ z, ∑ α, (if |hH.eigenvalues α - u₁.re| ≤ w' then 0 else
      ‖spectralPole hH u₁ α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2) ≤ o₁)
    (ho₂ : ∀ z, ∑ α, (if |hH.eigenvalues α - u₂.re| ≤ w' then 0 else
      ‖spectralPole hH u₂ α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2) ≤ o₂) :
    ∑ α, ∑ β, ‖spectralPole hH u₁ α‖ ^ 2 * ‖spectralPole hH u₂ β‖ ^ 2 *
        ‖blockM2 d L W lam hH (siteBlock d L W y) α β‖ *
          (‖hH.eigenvectorBasis α y‖ * ‖hH.eigenvectorBasis β y‖) ≤
      θ / 2 * (q₁ * ((((W * L) ^ d : ℕ) : ℝ) * q₂) + ((((W * L) ^ d : ℕ) : ℝ) * q₁) * q₂) +
        2 * (((W * L) ^ d : ℕ) : ℝ) * (o₁ * q₂ + q₁ * o₂) := by
  have hS : ∀ (u : ℂ) (q : ℝ),
      (∀ z, ∑ α, ‖spectralPole hH u α‖ ^ 2 * ‖hH.eigenvectorBasis α z‖ ^ 2 ≤ q) →
      ∑ α, ‖spectralPole hH u α‖ ^ 2 ≤ (((W * L) ^ d : ℕ) : ℝ) * q := by
    intro u q hq
    rw [UywKernel_sum_pole_sq_eq hH u]
    calc _ ≤ ∑ _z : Idx d L W, q := Finset.sum_le_sum fun z _ => hq z
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_Idx]
  refine UywKernel_pair_abstract (fun α => ‖spectralPole hH u₁ α‖ ^ 2)
    (fun α => ‖spectralPole hH u₂ α‖ ^ 2) (fun γ x => ‖hH.eigenvectorBasis γ x‖)
    (fun α β => ‖blockM2 d L W lam hH (siteBlock d L W y) α β‖)
    (fun x => svarF d L W lam x y + (((W * L) ^ d : ℕ) : ℝ)⁻¹) y
    (fun α => |hH.eigenvalues α - u₁.re| ≤ w') (fun β => |hH.eigenvalues β - u₂.re| ≤ w')
    (fun α => by positivity) (fun α => by positivity) (fun α x => norm_nonneg _)
    (fun x => add_nonneg (svarF_nonneg d L W lam x y)
      (by have := UywKernel_N_pos (d := d) (L := L) (W := W); positivity))
    (le_of_eq (UywKernel_profile_weight_sum hL lam y))
    (by have := UywKernel_N_pos (d := d) (L := L) (W := W); positivity) hθ
    (fun α β => UywKernel_norm_blockM2_le hL lam hH y α β) (fun α β h1 h2 => hMw α β h1 h2)
    hq₁ hq₂ ho₁ ho₂ (hS u₁ q₁ hq₁) (hS u₂ q₂ hq₂)

/-- The triangle bound for the exact expansion: `‖y-term‖ ≤ N⁻¹ A_y` (target 2 together with
`spectralGsigPole_norm_eq_spectralPole`; RBM2D `UywKernel_norm_yterm_le` `:1033`). -/
private theorem UywKernel_norm_yterm_le (hL : 3 ≤ L) (lam : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (y : Idx d L W) {z₁ z₂ : ℂ}
    (hη₁ : 0 < z₁.im) (hη₂ : 0 < z₂.im) (σ₁ σ₂ : Bool) :
    ‖∑ x : Idx d L W, (Gres H z₁ σ₁ * Gres H z₁ σ₁) x y * scirc d L W lam x y *
        (Gres H z₂ σ₂ * Gres H z₂ σ₂) y x‖ ≤
      (((W * L) ^ d : ℕ) : ℝ)⁻¹ * ∑ α, ∑ β, ‖spectralPole hH z₁ α‖ ^ 2 *
        ‖spectralPole hH z₂ β‖ ^ 2 * ‖blockM2 d L W lam hH (siteBlock d L W y) α β‖ *
          (‖hH.eigenvectorBasis α y‖ * ‖hH.eigenvectorBasis β y‖) := by
  rw [green_spectral_identity_blockM2 hL lam hH y z₁ z₂ hη₁ hη₂ σ₁ σ₂, norm_mul, norm_inv,
    Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
  refine Finset.sum_le_sum fun α _ => (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun β _ => ?_
  simp only [norm_mul, norm_star, spectralGsigPole_norm_eq_spectralPole]
  ring

/-- Target 4a: **pointwise bound on the good event** (RBM2D `uyw_pointwise_good` `:1055`, `d ≥ 3`, per site `y`).
On the single-scale grid event, with the window bound `|M_{y,α,β}| ≤ θ` off the blocks flagged `Bad`, the
weighted `y`-term of `L₂` (the integrand of the pin `UNUyw`, `Pins.lean:712-716`, token for token at
`H = ouMat … t ω`, `lam = sz.lam n`) is at most the product of the `Im m` rows times
`N⁻¹ (Ag + 1_{Bad} Ab)`; `N = (W L)^d`, constants of RBM2D shape (`d` does not enter them). -/
theorem uyw_pointwise_good (hL : 3 ≤ L) (lam : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (m : ℕ) (s : Finset (Fin m))
    (w : Fin m → ℂ) (u₁ u₂ : ℂ) (ηt Cb w' θ Ag Ab : ℝ)
    (hη₁ : 0 < u₁.im) (hη₁' : u₁.im ≤ ηt) (hη₂ : 0 < u₂.im) (hη₂' : u₂.im ≤ ηt)
    (hηw : ∀ j, 0 < (w j).im) (hηw' : ∀ j, (w j).im ≤ ηt) (hCb : 0 ≤ Cb) (hw' : 0 < w')
    (hθ : 0 ≤ θ) (K' : ℕ)
    (hG1 : ∀ k ≤ K', jakGridGood H ηt Cb u₁.re (2 ^ k * w'))
    (hG2 : ∀ k ≤ K', jakGridGood H ηt Cb u₂.re (2 ^ k * w'))
    (hG3 : jakGridGood H ηt Cb u₁.re 0) (hG4 : jakGridGood H ηt Cb u₂.re 0)
    (hG5 : ∀ j, jakGridGood H ηt Cb (w j).re 0)
    (Bad : Zd d L → Prop) [DecidablePred Bad]
    (hBad : ∀ a0, ¬ Bad a0 → ∀ α β, |hH.eigenvalues α - u₁.re| ≤ w' →
      |hH.eigenvalues β - u₂.re| ≤ w' → ‖blockM2 d L W lam hH a0 α β‖ ≤ θ)
    (hAg : θ / 2 * ((ηt / u₁.im ^ 2 * Cb) * ((((W * L) ^ d : ℕ) : ℝ) * (ηt / u₂.im ^ 2 * Cb)) +
        ((((W * L) ^ d : ℕ) : ℝ) * (ηt / u₁.im ^ 2 * Cb)) * (ηt / u₂.im ^ 2 * Cb)) +
      2 * (((W * L) ^ d : ℕ) : ℝ) *
        ((Cb * (8 / w' + 8 * ηt / w' ^ 2) + ((2 ^ K' * w') ^ 2)⁻¹) * (ηt / u₂.im ^ 2 * Cb) +
          (ηt / u₁.im ^ 2 * Cb) * (Cb * (8 / w' + 8 * ηt / w' ^ 2) + ((2 ^ K' * w') ^ 2)⁻¹)) ≤
      Ag)
    (hAb : 4 * (((W * L) ^ d : ℕ) : ℝ) * ((ηt / u₁.im ^ 2 * Cb) * (ηt / u₂.im ^ 2 * Cb)) ≤ Ab)
    (y : Idx d L W) (σ₁ σ₂ : Bool) :
    (∏ j ∈ s, (stieltjesN H (w j)).im) *
        ‖∑ x, (Gres H u₁ σ₁ * Gres H u₁ σ₁) x y * scirc d L W lam x y *
          (Gres H u₂ σ₂ * Gres H u₂ σ₂) y x‖ ≤
      (∏ j ∈ s, (ηt / (w j).im * Cb)) *
        ((((W * L) ^ d : ℕ) : ℝ)⁻¹ *
          (Ag + (if Bad (siteBlock d L W y) then Ab else 0))) := by
  have hηt : 0 < ηt := lt_of_lt_of_le hη₁ hη₁'
  have hN : (0 : ℝ) < (((W * L) ^ d : ℕ) : ℝ) := UywKernel_N_pos
  have hP : (∏ j ∈ s, (stieltjesN H (w j)).im) ≤ ∏ j ∈ s, (ηt / (w j).im * Cb) := by
    refine Finset.prod_le_prod₀
      (fun j _ => (UywKernel_stieltjesN_im_nonneg_le hH (hηw j)).1)
      fun j _ => UywKernel_stieltjesN_im_le_of_grid hH (hηw j) (hηw' j) (hG5 j)
  have hP0 : 0 ≤ ∏ j ∈ s, (ηt / (w j).im * Cb) :=
    Finset.prod_nonneg fun j _ => mul_nonneg (div_nonneg hηt.le (hηw j).le) hCb
  have hq₁ := UywKernel_sum_pole_sq_mass_le_of_grid hH hη₁ hη₁' hG3
  have hq₂ := UywKernel_sum_pole_sq_mass_le_of_grid hH hη₂ hη₂' hG4
  have ho₁ := UywKernel_sum_pole_sq_mass_out_le hH hηt hCb hw' K' hG1
  have ho₂ := UywKernel_sum_pole_sq_mass_out_le hH hηt hCb hw' K' hG2
  have hq₁0 : 0 ≤ ηt / u₁.im ^ 2 * Cb := by positivity
  have hq₂0 : 0 ≤ ηt / u₂.im ^ 2 * Cb := by positivity
  have hAb0 : 0 ≤ Ab := le_trans (by positivity) hAb
  have hA : ∑ α, ∑ β, ‖spectralPole hH u₁ α‖ ^ 2 * ‖spectralPole hH u₂ β‖ ^ 2 *
      ‖blockM2 d L W lam hH (siteBlock d L W y) α β‖ *
        (‖hH.eigenvectorBasis α y‖ * ‖hH.eigenvectorBasis β y‖) ≤
        Ag + (if Bad (siteBlock d L W y) then Ab else 0) := by
    by_cases hb : Bad (siteBlock d L W y)
    · simp only [hb, ite_true]
      -- no window: `w' = -1`
      have h := UywKernel_A_le hL lam hH u₁ u₂ y (θ := 0) (w' := -1) le_rfl
        (fun α β h1 _ => absurd h1 (by linarith [abs_nonneg (hH.eigenvalues α - u₁.re)]))
        hq₁ hq₂ (o₁ := ηt / u₁.im ^ 2 * Cb) (o₂ := ηt / u₂.im ^ 2 * Cb)
        (fun z => by simp_rw [UywKernel_ite_abs_neg_one]; exact hq₁ z)
        (fun z => by simp_rw [UywKernel_ite_abs_neg_one]; exact hq₂ z)
      have hAg0 : 0 ≤ Ag := le_trans (by positivity) hAg
      nlinarith
    · simp only [hb, ite_false, add_zero]
      exact (UywKernel_A_le hL lam hH u₁ u₂ y hθ (hBad _ hb) hq₁ hq₂ ho₁ ho₂).trans hAg
  have hK := UywKernel_norm_yterm_le hL lam hH y hη₁ hη₂ σ₁ σ₂
  have hK' : ‖∑ x, (Gres H u₁ σ₁ * Gres H u₁ σ₁) x y * scirc d L W lam x y *
        (Gres H u₂ σ₂ * Gres H u₂ σ₂) y x‖ ≤
      (((W * L) ^ d : ℕ) : ℝ)⁻¹ * (Ag + (if Bad (siteBlock d L W y) then Ab else 0)) :=
    hK.trans (mul_le_mul_of_nonneg_left hA (by positivity))
  calc (∏ j ∈ s, (stieltjesN H (w j)).im) *
        ‖∑ x, (Gres H u₁ σ₁ * Gres H u₁ σ₁) x y * scirc d L W lam x y *
          (Gres H u₂ σ₂ * Gres H u₂ σ₂) y x‖
      ≤ (∏ j ∈ s, (ηt / (w j).im * Cb)) *
        ‖∑ x, (Gres H u₁ σ₁ * Gres H u₁ σ₁) x y * scirc d L W lam x y *
          (Gres H u₂ σ₂ * Gres H u₂ σ₂) y x‖ :=
        mul_le_mul_of_nonneg_right hP (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hK' hP0

/-- Target 4b: **crude pointwise bound** (RBM2D `uyw_pointwise_crude` `:1127`, `d ≥ 3`, per site `y`), valid for
every Hermitian matrix: `∏ Im m(w_j) · |y-term| ≤ ∏ (Im w_j)⁻¹ · 4 (Im u₁)⁻² (Im u₂)⁻²` (from
`A_y ≤ 4N (Im u₁)⁻²(Im u₂)⁻²`). -/
theorem uyw_pointwise_crude (hL : 3 ≤ L) (lam : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (m : ℕ) (s : Finset (Fin m))
    (w : Fin m → ℂ) (u₁ u₂ : ℂ) (hη₁ : 0 < u₁.im) (hη₂ : 0 < u₂.im)
    (hηw : ∀ j, 0 < (w j).im) (y : Idx d L W) (σ₁ σ₂ : Bool) :
    (∏ j ∈ s, (stieltjesN H (w j)).im) *
        ‖∑ x, (Gres H u₁ σ₁ * Gres H u₁ σ₁) x y * scirc d L W lam x y *
          (Gres H u₂ σ₂ * Gres H u₂ σ₂) y x‖ ≤
      (∏ j ∈ s, (w j).im⁻¹) * (4 * ((u₁.im⁻¹) ^ 2 * (u₂.im⁻¹) ^ 2)) := by
  have hN : (0 : ℝ) < (((W * L) ^ d : ℕ) : ℝ) := UywKernel_N_pos
  have hP : (∏ j ∈ s, (stieltjesN H (w j)).im) ≤ ∏ j ∈ s, (w j).im⁻¹ :=
    Finset.prod_le_prod₀ (fun j _ => (UywKernel_stieltjesN_im_nonneg_le hH (hηw j)).1)
      fun j _ => (UywKernel_stieltjesN_im_nonneg_le hH (hηw j)).2
  have hP0 : 0 ≤ ∏ j ∈ s, (w j).im⁻¹ := Finset.prod_nonneg fun j _ => (inv_pos.2 (hηw j)).le
  have hq₁ := UywKernel_sum_pole_sq_mass_le_crude hH hη₁
  have hq₂ := UywKernel_sum_pole_sq_mass_le_crude hH hη₂
  have hA : ∑ α, ∑ β, ‖spectralPole hH u₁ α‖ ^ 2 * ‖spectralPole hH u₂ β‖ ^ 2 *
      ‖blockM2 d L W lam hH (siteBlock d L W y) α β‖ *
        (‖hH.eigenvectorBasis α y‖ * ‖hH.eigenvectorBasis β y‖) ≤
        4 * (((W * L) ^ d : ℕ) : ℝ) * ((u₁.im⁻¹) ^ 2 * (u₂.im⁻¹) ^ 2) := by
    have h := UywKernel_A_le hL lam hH u₁ u₂ y (θ := 0) (w' := -1) le_rfl
      (fun α β h1 _ => absurd h1 (by linarith [abs_nonneg (hH.eigenvalues α - u₁.re)]))
      hq₁ hq₂ (o₁ := (u₁.im⁻¹) ^ 2) (o₂ := (u₂.im⁻¹) ^ 2)
      (fun z => by simp_rw [UywKernel_ite_abs_neg_one]; exact hq₁ z)
      (fun z => by simp_rw [UywKernel_ite_abs_neg_one]; exact hq₂ z)
    nlinarith
  have hK : ‖∑ x, (Gres H u₁ σ₁ * Gres H u₁ σ₁) x y * scirc d L W lam x y *
        (Gres H u₂ σ₂ * Gres H u₂ σ₂) y x‖ ≤
      4 * ((u₁.im⁻¹) ^ 2 * (u₂.im⁻¹) ^ 2) := by
    refine (UywKernel_norm_yterm_le hL lam hH y hη₁ hη₂ σ₁ σ₂).trans ?_
    calc _ ≤ (((W * L) ^ d : ℕ) : ℝ)⁻¹ *
          (4 * (((W * L) ^ d : ℕ) : ℝ) * ((u₁.im⁻¹) ^ 2 * (u₂.im⁻¹) ^ 2)) :=
          mul_le_mul_of_nonneg_left hA (by positivity)
      _ = 4 * ((u₁.im⁻¹) ^ 2 * (u₂.im⁻¹) ^ 2) := by field_simp
  calc _ ≤ (∏ j ∈ s, (w j).im⁻¹) *
          ‖∑ x, (Gres H u₁ σ₁ * Gres H u₁ σ₁) x y * scirc d L W lam x y *
            (Gres H u₂ σ₂ * Gres H u₂ σ₂) y x‖ :=
        mul_le_mul_of_nonneg_right hP (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hK hP0

end Pointwise

/-! ## 10. Compiled nonempty instances (`d = 3`, `L = 3`, `W = 2`, `N = 216`) -/

/-! At the scale `η = 1` one has `Im G_xx ≤ η⁻¹ = 1` at every energy for every Hermitian matrix, so the grid
event holds with `Cb = 1`, `ηt = 1` for every centre and radius (`JakKernelInst.gridGood_one`).  The data:
`H = 1` (the `216 × 216` identity), `y = y0 = 0`, `u₁ = u₂ = w 0 = I`, `ηt = Cb = w' = 1`, `K' = 1`,
`Bad ≡ False`, `θ = 2N = 432` (`blockM2_le_432`), `Ag = 107352 = 432·216 + 432·(65/2)`, `Ab = 864 = 4·216`,
`lam = 1/2`; target 3 at `Measure.dirac ()`, `𝔡 = 1/10`, `lam = 1`, `E = 0`, `a₀ = 0`, `p = 1`. -/

/-- A Hermitian matrix has entries of eigenvectors of modulus `≤ 1` (RBM2D `UywKernel_norm_eigvec_le_one`
`:1191`). -/
private theorem UywKernel_norm_eigvec_le_one {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) (α x : n) : ‖hH.eigenvectorBasis α x‖ ≤ 1 := by
  have h1 : ‖hH.eigenvectorBasis α x‖ ^ 2 ≤ ∑ l, ‖hH.eigenvectorBasis l x‖ ^ 2 :=
    Finset.single_le_sum (f := fun l => ‖hH.eigenvectorBasis l x‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ α)
  rw [UywKernel_sum_sq_norm_row hH x] at h1
  nlinarith [norm_nonneg (hH.eigenvectorBasis α x)]

namespace UywKernelInst

/-- The `216 × 216` identity matrix, a Hermitian matrix on `Idx 3 3 2`. -/
noncomputable abbrev H1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ := 1

def y0 : Idx 3 3 2 := 0

def y1 : Idx 3 3 2 := 1

theorem H1_herm : H1.IsHermitian := Matrix.isHermitian_one

private theorem I_im_pos : 0 < Complex.I.im := by simp

/-- The pair block bound `|M_{a₀,α,β}| ≤ 2N = 432`, for every Hermitian matrix on `Idx 3 3 2`, every `lam`
(from `UywKernel_norm_blockM2_le`, `|ψ| ≤ 1`, and the row sum `∑_x (S_{xy} + N⁻¹) = 2`; RBM2D `blockM2_le_72`
`:1201`; template `JakKernelInst.blockM_le_432`, `JakKernel.lean:1012`). -/
theorem blockM2_le_432 {H : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ} (hH : H.IsHermitian) (lam : ℝ)
    (a0 : Zd 3 3) (α β : Idx 3 3 2) : ‖blockM2 3 3 2 lam hH a0 α β‖ ≤ 432 := by
  obtain ⟨y, hy⟩ : ∃ y : Idx 3 3 2, siteBlock 3 3 2 y = a0 := by
    obtain ⟨y, hy⟩ := (split_bijective 3 3 2).2
      (a0, ⟨0, pow_pos (Nat.pos_of_ne_zero (NeZero.ne 2)) 3⟩)
    exact ⟨y, by simp [siteBlock, hy]⟩
  subst hy
  have h := UywKernel_norm_blockM2_le (by norm_num : 3 ≤ 3) lam hH y α β
  have hsum := UywKernel_profile_weight_sum (d := 3) (L := 3) (W := 2) (by norm_num) lam y
  have hN : (0 : ℝ) < (((2 * 3) ^ 3 : ℕ) : ℝ) := UywKernel_N_pos
  have hle : ∑ x : Idx 3 3 2, (svarF 3 3 2 lam x y + (((2 * 3) ^ 3 : ℕ) : ℝ)⁻¹) *
      (‖hH.eigenvectorBasis α x‖ * ‖hH.eigenvectorBasis β x‖) ≤
      ∑ x : Idx 3 3 2, (svarF 3 3 2 lam x y + (((2 * 3) ^ 3 : ℕ) : ℝ)⁻¹) * 1 := by
    refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_
      (add_nonneg (svarF_nonneg 3 3 2 lam x y) (by positivity))
    calc ‖hH.eigenvectorBasis α x‖ * ‖hH.eigenvectorBasis β x‖ ≤ 1 * 1 :=
          mul_le_mul (UywKernel_norm_eigvec_le_one hH α x) (UywKernel_norm_eigvec_le_one hH β x)
            (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  simp only [mul_one, hsum] at hle
  have hmul := mul_le_mul_of_nonneg_left hle hN.le
  norm_num at h hmul ⊢
  linarith

/-- `inst_self` (target 1a at `H = 1`, `lam = 1/2`, `a₀ = 0`, `α = y0`). -/
theorem inst_self :
    ∀ hH : H1.IsHermitian,
    blockM2 3 3 2 (1 / 2) hH 0 y0 y0 = blockM 3 3 2 (1 / 2) hH 0 y0 :=
  fun hH => blockM2_self (1 / 2) hH 0 y0

/-- `inst_eq` (target 1b at `H = 1`, `lam = 1/2`, `y = y0`, `α = y0 ≠ β = y1`; extra to the pinned list). -/
theorem inst_eq :
    ∀ hH : H1.IsHermitian,
    blockM2 3 3 2 (1 / 2) hH (siteBlock 3 3 2 y0) y0 y1 =
      (((2 * 3) ^ 3 : ℕ) : ℂ) *
        ∑ x, (hH.eigenvectorBasis y0 x * star (hH.eigenvectorBasis y1 x)) * scirc 3 3 2 (1 / 2) x y0 :=
  fun hH => blockM2_eq (by norm_num) (1 / 2) hH y0 y0 y1

/-- `inst_identity2` (target 2 at `H = 1`, `lam = 1/2`, `y = y0`, `z₁ = z₂ = I`, `σ₁ = true`, `σ₂ = false`;
extra to the pinned list). -/
theorem inst_identity2 :
    ∀ hH : H1.IsHermitian,
    (∑ x, (Gres H1 Complex.I true * Gres H1 Complex.I true) x y0 * scirc 3 3 2 (1 / 2) x y0 *
        (Gres H1 Complex.I false * Gres H1 Complex.I false) y0 x) =
      ((((2 * 3) ^ 3 : ℕ) : ℂ))⁻¹ * ∑ α, ∑ β,
        spectralGsigPole hH Complex.I true α * spectralGsigPole hH Complex.I true α *
          (spectralGsigPole hH Complex.I false β * spectralGsigPole hH Complex.I false β) *
            blockM2 3 3 2 (1 / 2) hH (siteBlock 3 3 2 y0) α β *
              star (hH.eigenvectorBasis α y0) * hH.eigenvectorBasis β y0 :=
  fun hH => green_spectral_identity_blockM2 (by norm_num) (1 / 2) hH y0 Complex.I Complex.I
    I_im_pos I_im_pos true false

/-- `inst_bad2` (target 3 at `Ω = Unit`, `P = δ_()`, `Hr ≡ 1`, `lam = 1`, `𝔡 = 1/10`, `E = 0`, `a₀ = 0`,
`p = 1`; every hypothesis discharged: `3 ≤ 3`, `1 ≤ 2`, `0 < 1/10`, `2^{-3/2 + 1/10} ≤ 1`, `δ(·) ≤ 1`). -/
theorem inst_bad2 :
    ∀ hH : ∀ _ω : Unit, H1.IsHermitian,
    (Measure.dirac ()) {ω : Unit | ∃ α β,
        |(hH ω).eigenvalues α - 0| ≤ (((2 * 3) ^ 3 : ℕ) : ℝ)⁻¹ * ((2 : ℕ) : ℝ) ^ ((1 / 10 : ℝ) / 3) ∧
        |(hH ω).eigenvalues β - 0| ≤ (((2 * 3) ^ 3 : ℕ) : ℝ)⁻¹ * ((2 : ℕ) : ℝ) ^ ((1 / 10 : ℝ) / 3) ∧
        ((2 : ℕ) : ℝ) ^ (-((1 / 10 : ℝ) / 6)) ≤ ‖blockM2 3 3 2 1 (hH ω) 0 α β‖} ≤
      ((2 * 3 + 1 : ℕ) : ℝ≥0∞) * 1 := by
  intro hH
  refine measure_bad2_le_of_queBadMat (Measure.dirac ()) (by norm_num)
    (lam := 1) (𝔡 := 1 / 10) (E := 0) (by norm_num) (by norm_num) ?_ 0 hH 1
    (fun b => prob_le_one)
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)

/-- `inst_good` (target 4a at the data above, every `y`, `σ₁`, `σ₂`; RBM2D `:1290`). -/
theorem inst_good (y : Idx 3 3 2) (σ₁ σ₂ : Bool) :
    (∏ _j ∈ ({0} : Finset (Fin 1)), (stieltjesN H1 Complex.I).im) *
        ‖∑ x, (Gres H1 Complex.I σ₁ * Gres H1 Complex.I σ₁) x y *
          scirc 3 3 2 (1 / 2) x y * (Gres H1 Complex.I σ₂ * Gres H1 Complex.I σ₂) y x‖ ≤
      (∏ _j ∈ ({0} : Finset (Fin 1)), (1 / Complex.I.im * 1)) *
        ((((2 * 3) ^ 3 : ℕ) : ℝ)⁻¹ * (107352 + (if False then (864 : ℝ) else 0))) :=
  uyw_pointwise_good (d := 3) (L := 3) (W := 2) (by norm_num) (1 / 2) H1_herm 1
    ({0} : Finset (Fin 1)) (fun _ => Complex.I) Complex.I Complex.I 1 1 1 432 107352 864
    (by simp) (by simp) (by simp) (by simp) (fun _ => by simp) (fun _ => by simp) zero_le_one
    one_pos (by norm_num) 1
    (fun k _ => JakKernelInst.gridGood_one H1_herm _ _)
    (fun k _ => JakKernelInst.gridGood_one H1_herm _ _)
    (JakKernelInst.gridGood_one H1_herm _ _) (JakKernelInst.gridGood_one H1_herm _ _)
    (fun _ => JakKernelInst.gridGood_one H1_herm _ _) (fun _ : Zd 3 3 => False)
    (fun a0 _ α β _ _ => blockM2_le_432 H1_herm _ a0 α β) (by norm_num) (by norm_num) y σ₁ σ₂

/-- `inst_crude` (target 4b at `H = 1`, `s = {0}`, `w 0 = u₁ = u₂ = I`, `y = y0`, every `σ₁`, `σ₂`; RBM2D
`:1345`). -/
theorem inst_crude (σ₁ σ₂ : Bool) :
    (∏ _j ∈ ({0} : Finset (Fin 1)), (stieltjesN H1 Complex.I).im) *
        ‖∑ x, (Gres H1 Complex.I σ₁ * Gres H1 Complex.I σ₁) x y0 *
          scirc 3 3 2 (1 / 2) x y0 *
            (Gres H1 Complex.I σ₂ * Gres H1 Complex.I σ₂) y0 x‖ ≤
      (∏ _j ∈ ({0} : Finset (Fin 1)), Complex.I.im⁻¹) *
        (4 * ((Complex.I.im⁻¹) ^ 2 * (Complex.I.im⁻¹) ^ 2)) :=
  uyw_pointwise_crude (d := 3) (L := 3) (W := 2) (by norm_num) (1 / 2) H1_herm 1
    ({0} : Finset (Fin 1)) (fun _ => Complex.I) Complex.I Complex.I (by simp) (by simp)
    (fun _ => by simp) y0 σ₁ σ₂

/-- A non-scalar Hermitian matrix on `Idx 3 3 2`: `diag(x₀.val)` (RBM2D `H2` `:1185`). -/
noncomputable abbrev H2 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ :=
  Matrix.diagonal (fun x : Idx 3 3 2 => ((((x 0).val : ℕ) : ℝ) : ℂ))

theorem H2_herm : H2.IsHermitian :=
  Matrix.isHermitian_diagonal_iff.mpr (fun i => by simp [IsSelfAdjoint])

/-- Target 4a at the non-scalar `H2`: `u₁ = 1/2 + i`, `u₂ = -1 + i`, `w 0 = -1 + i`, `s = {0}`,
`ηt = Cb = w' = 1`, `K' = 1`, `Bad a₀ ↔ a₀ = 0`, `θ = 432`, the same constants, any `y`, `σ₁`, `σ₂`
(RBM2D `:1323`). -/
example (y : Idx 3 3 2) (σ₁ σ₂ : Bool) :=
  uyw_pointwise_good (d := 3) (L := 3) (W := 2) (by norm_num) (1 / 2) H2_herm 1
    ({0} : Finset (Fin 1)) (fun _ => (⟨-1, 1⟩ : ℂ)) (⟨1 / 2, 1⟩ : ℂ) (⟨-1, 1⟩ : ℂ) 1 1 1 432
    107352 864 (by simp) (by simp) (by simp) (by simp) (fun _ => by simp) (fun _ => by simp)
    zero_le_one one_pos (by norm_num) 1
    (fun _ _ => JakKernelInst.gridGood_one H2_herm _ _)
    (fun _ _ => JakKernelInst.gridGood_one H2_herm _ _)
    (JakKernelInst.gridGood_one H2_herm _ _) (JakKernelInst.gridGood_one H2_herm _ _)
    (fun _ => JakKernelInst.gridGood_one H2_herm _ _) (fun a : Zd 3 3 => a = 0)
    (fun a0 _ α β _ _ => blockM2_le_432 H2_herm _ a0 α β) (by norm_num) (by norm_num) y σ₁ σ₂

/-- Target 4b at the non-scalar `H2`: `u₁ = 1/2 + i`, `u₂ = -1 + i`, `s = {0}`, `w 0 = -1 + i`, any `y`
(RBM2D `:1358`). -/
example (y : Idx 3 3 2) (σ₁ σ₂ : Bool) :=
  uyw_pointwise_crude (d := 3) (L := 3) (W := 2) (by norm_num) (1 / 2) H2_herm 1
    ({0} : Finset (Fin 1)) (fun _ => (⟨-1, 1⟩ : ℂ)) (⟨1 / 2, 1⟩ : ℂ) (⟨-1, 1⟩ : ℂ) (by simp)
    (by simp) (fun _ => by simp) y σ₁ σ₂

end UywKernelInst

#print axioms RBM.Univ.blockM2_self
#print axioms RBM.Univ.blockM2_eq
#print axioms RBM.Univ.green_spectral_identity_blockM2
#print axioms RBM.Univ.measure_bad2_le_of_queBadMat
#print axioms RBM.Univ.uyw_pointwise_good
#print axioms RBM.Univ.uyw_pointwise_crude
#print axioms RBM.Univ.UywKernelInst.blockM2_le_432
#print axioms RBM.Univ.UywKernelInst.inst_self
#print axioms RBM.Univ.UywKernelInst.inst_eq
#print axioms RBM.Univ.UywKernelInst.inst_identity2
#print axioms RBM.Univ.UywKernelInst.inst_bad2
#print axioms RBM.Univ.UywKernelInst.inst_good
#print axioms RBM.Univ.UywKernelInst.inst_crude

end RBM.Univ
