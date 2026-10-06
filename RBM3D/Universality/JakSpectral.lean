/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.Pins
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.MeasureTheory.OuterMeasure.Basic

/-!
# `RBM3D.Universality.JakSpectral` (UN-19): the deterministic spectral layer of `(jaklsdufowe)`

Paper: arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex` (cited `1_2:line`), the proof of
`Thm: B_Univ` `1_2:566-581`, the `y`-term of the pin `UNJak`.
Port of RBM2D `Universality/JakSpectral.lean` (commit `c9a24cf`, 720 lines) to `Idx d L W`,
`scirc d L W lam`, `N = (W L)^d`, the merged resolvent `Gres`, and the `2d + 1` weights
`SBR d L lam` of `S^(B)` in place of RBM2D's five equal weights `1/5`.

For a Hermitian matrix with orthonormal eigenbasis `ψ_α` (Mathlib's `eigenvectorBasis`):
the eigenbasis expansion of `Gres` and `Gres * Gres` on the diagonal; the block quantity `blockM`
and its bridges to `N ∑_x |ψ_α(x)|² S°_{xy}` (`blockM_eq`) and to the merged `unMy`
(`blockM_eq_unMy`); the exact spectral expansion of the `UNJak` integrand and its triangle bound;
the mass bound `∑_α |M_{a₀,α}| ≤ 2N`; and the union bound through the merged `UNBadY`.
No pin is proved or stated; the file is `lam`-generic (band data `sz.lam n`, model-generic data
`K.lamV sz n`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Matrix
open RBM RBM.Gauss
open scoped ENNReal

namespace RBM.Univ

/-! ## 1. Eigenbasis expansion of the resolvent (any finite index type) -/

section Generic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The eigenvalue coefficient of the resolvent with spectral parameter `w`
(RBM2D `JakSpectral.lean:57`). -/
def spectralPole {H : Matrix n n ℂ} (hH : H.IsHermitian) (w : ℂ) (α : n) : ℂ :=
  ((hH.eigenvalues α : ℂ) - w)⁻¹

/-- The eigenvalue coefficient of `Gres H z σ`: the sign `σ = false` uses `z̄` (RBM2D `:62`; the
spectral parameter is the one of the merged `Gres`, `Loop/GLoopFlow.lean:74`). -/
def spectralGsigPole {H : Matrix n n ℂ} (hH : H.IsHermitian) (z : ℂ) (σ : Bool) (α : n) : ℂ :=
  spectralPole hH (if σ then z else (starRingEnd ℂ) z) α

private theorem JakSpectral_eigenvalues_ne_of_im_ne {H : Matrix n n ℂ} (hH : H.IsHermitian)
    {w : ℂ} (hw : w.im ≠ 0) : ∀ α, (hH.eigenvalues α : ℂ) ≠ w := by
  intro α h
  have him := congrArg Complex.im h
  simp at him
  exact hw him.symm

private theorem JakSpectral_im_gsig_ne {z : ℂ} (hη : 0 < z.im) (σ : Bool) :
    (if σ then z else (starRingEnd ℂ) z).im ≠ 0 := by
  cases σ <;> simp [hη.ne']

/-- Mathlib's eigenbasis is an orthonormal eigenbasis in the sense of `IsOrthoEigenbasis`
(RBM2D `:146`). -/
theorem isOrthoEigenbasis_eigenvectorBasis {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    IsOrthoEigenbasis H hH.eigenvalues (fun k x => hH.eigenvectorBasis k x) := by
  refine ⟨fun k k' => ?_, fun k => ?_⟩
  · have h := orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal k k'
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
    exact h
  · rw [hH.mulVec_eigenvectorBasis k]
    ext x
    simp [RCLike.real_smul_eq_coe_smul (K := ℂ)]

/-- `U* U = 1` for the matrix `U x α = ψ_α(x)` of an orthonormal family. -/
private theorem JakSpectral_star_mul_self {H : Matrix n n ℂ} {μ : n → ℝ} {ψ : n → n → ℂ}
    (hψ : IsOrthoEigenbasis H μ ψ) :
    star (Matrix.of fun y l => ψ l y) * (Matrix.of fun y l => ψ l y) = 1 := by
  ext k k'
  have h := hψ.1 k k'
  simp only [dotProduct, Pi.star_apply] at h
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply]
  exact h

/-- The spectral decomposition `Gres H w true = U diag((μ_α - w)⁻¹) U*`, `U x α = ψ_α(x)`
(template `Main/FixedZ.lean:552-600`, `RBM.Endpoints.Gres_apply_self`, the `hinv` step; RBM2D
`Delocalization.lean:47`, `green_eq_spectral`). -/
private theorem JakSpectral_Gres_eq_spectral {H : Matrix n n ℂ} {μ : n → ℝ} {ψ : n → n → ℂ}
    (hψ : IsOrthoEigenbasis H μ ψ) {w : ℂ} (hz : ∀ l, (μ l : ℂ) ≠ w) :
    Gres H w true = (Matrix.of fun y l => ψ l y) * diagonal (fun l => ((μ l : ℂ) - w)⁻¹) *
      star (Matrix.of fun y l => ψ l y) := by
  set U : Matrix n n ℂ := Matrix.of fun y l => ψ l y with hU
  have hUU : star U * U = 1 := JakSpectral_star_mul_self hψ
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

/-- Diagonal entries of the squared resolvent, including the square on the spectral pole
(RBM2D `green_sq_apply_self` `:78`; `green H w ^ 2` ↦ `Gres H w true * Gres H w true`). -/
theorem Gres_sq_apply_self {H : Matrix n n ℂ} (hH : H.IsHermitian) {w : ℂ}
    (hw : ∀ α, (hH.eigenvalues α : ℂ) ≠ w) (x : n) :
    (Gres H w true * Gres H w true) x x =
      ∑ α, spectralPole hH w α * spectralPole hH w α *
        (Complex.normSq (hH.eigenvectorBasis α x) : ℂ) := by
  have hψ := isOrthoEigenbasis_eigenvectorBasis hH
  set U : Matrix n n ℂ := Matrix.of fun y l => hH.eigenvectorBasis l y with hU
  let d : n → ℂ := fun α => spectralPole hH w α
  have hUU : star U * U = 1 := JakSpectral_star_mul_self hψ
  have hG : Gres H w true = U * diagonal d * star U := by
    simpa [U, d, spectralPole] using JakSpectral_Gres_eq_spectral hψ hw
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
  rw [Complex.normSq_eq_conj_mul_self]
  ring

/-- Diagonal entries of `Gres H z σ` in the eigenbasis (RBM2D `Gsig_apply_self_spectral` `:110`). -/
theorem Gres_apply_self_spectral {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hη : 0 < z.im) (σ : Bool) (y : n) :
    Gres H z σ y y =
      ∑ β, spectralGsigPole hH z σ β *
        (Complex.normSq (hH.eigenvectorBasis β y) : ℂ) := by
  have heig := JakSpectral_eigenvalues_ne_of_im_ne hH (JakSpectral_im_gsig_ne hη σ)
  have hψ := isOrthoEigenbasis_eigenvectorBasis hH
  have hG : Gres H z σ = Gres H (if σ then z else (starRingEnd ℂ) z) true := by
    cases σ <;> simp [Gres]
  rw [hG, JakSpectral_Gres_eq_spectral hψ heig, mul_apply]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [mul_diagonal, star_apply]
  simp only [Matrix.of_apply, RCLike.star_def, spectralGsigPole, spectralPole]
  rw [Complex.normSq_eq_conj_mul_self]
  ring

/-- Diagonal entries of `Gres H z σ * Gres H z σ` in the eigenbasis (RBM2D
`Gsig_sq_apply_self_spectral` `:122`). -/
theorem Gres_sq_apply_self_spectral {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hη : 0 < z.im) (σ : Bool) (x : n) :
    (Gres H z σ * Gres H z σ) x x =
      ∑ α, spectralGsigPole hH z σ α * spectralGsigPole hH z σ α *
        (Complex.normSq (hH.eigenvectorBasis α x) : ℂ) := by
  have heig := JakSpectral_eigenvalues_ne_of_im_ne hH (JakSpectral_im_gsig_ne hη σ)
  have hG : Gres H z σ = Gres H (if σ then z else (starRingEnd ℂ) z) true := by
    cases σ <;> simp [Gres]
  rw [hG]
  exact Gres_sq_apply_self hH heig x

/-- Both resolvent signs have the same pole norm for a Hermitian matrix (RBM2D `:132`). -/
theorem spectralGsigPole_norm_eq_spectralPole {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (z : ℂ) (σ : Bool) (α : n) :
    ‖spectralGsigPole hH z σ α‖ = ‖spectralPole hH z α‖ := by
  cases σ
  · change ‖(((hH.eigenvalues α : ℂ) - (starRingEnd ℂ) z)⁻¹)‖ =
      ‖(((hH.eigenvalues α : ℂ) - z)⁻¹)‖
    rw [norm_inv, norm_inv]
    have hconj : ((hH.eigenvalues α : ℂ) - (starRingEnd ℂ) z) =
        star ((hH.eigenvalues α : ℂ) - z) := by simp
    rw [hconj, norm_star]
  · rfl

/-- The rows of the eigenvector matrix are unit vectors: `∑_l |ψ_l(x)|² = 1` (RBM2D `:158`). -/
private theorem JakSpectral_sum_sq_norm {H : Matrix n n ℂ} (hH : H.IsHermitian) (x : n) :
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

end Generic

/-! ## 2. The block quantity `M_{y,α}` with the `2d + 1` weights -/

section Block

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- The block `a ∈ Z_L^d` of a site `y` (RBM2D `:180`; `Z2 L` ↦ `Zd d L`). -/
def siteBlock (y : Idx d L W) : Zd d L := (split d L W y).1

/-- `M_{y,α}` for `y ∈ [a₀]`, `d ≥ 3` form: the `S^{(B)}(lam)`-weighted average (weights `SBR d L lam b a₀`,
sum `1`, support `≤ 2d + 1` blocks) of the block QUE quantities `(N/W^d) ∑_{x∈[b]} |ψ_α(x)|² - 1`, written
with the overlap of the merged `queBadMat` (`Pins.lean:392`).  RBM2D `:185` is the equal-weight `1/5`
average over `a₀ + sbSupport L`; `blockM_eq` identifies it with `N ∑_x |ψ_α(x)|² S°_{xy}`,
`blockM_eq_unMy` with the merged `unMy`. -/
def blockM (lam : ℝ) {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian)
    (a0 : Zd d L) (α : Idx d L W) : ℂ :=
  ∑ b : Zd d L, ((SBR d L lam b a0 : ℝ) : ℂ) *
    ((((W * L) ^ d : ℕ) : ℂ) / (W : ℂ) ^ d *
        (∑ x ∈ Iblk d L W b, star (hH.eigenvectorBasis α x) * hH.eigenvectorBasis α x) - 1)

end Block

/-- An eigenvector of `H` is a unit vector (from `IsOrthoEigenbasis`, as `Pins.lean:1215-1224`). -/
private theorem JakSpectral_unit_norm {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (α : n) : ∑ x, ‖hH.eigenvectorBasis α x‖ ^ 2 = 1 := by
  have h1 := (isOrthoEigenbasis_eigenvectorBasis hH).1 α α
  simp only [ite_true, dotProduct] at h1
  have h2 : ∑ x, ((‖hH.eigenvectorBasis α x‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h1]
    refine Finset.sum_congr rfl fun x _ => ?_
    change ((‖hH.eigenvectorBasis α x‖ ^ 2 : ℝ) : ℂ) =
      star (hH.eigenvectorBasis α x) * hH.eigenvectorBasis α x
    rw [Complex.star_def, Complex.conj_mul']
    push_cast; ring
  exact_mod_cast h2

/-- `M_{y,α}` is the merged `unMy` of the eigenvector `ψ_α` (the bridge to `UNBadY`, `Pins.lean:1147`);
needs `3 ≤ L` through `unMy_eq`. -/
theorem blockM_eq_unMy {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) (lam : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (y α : Idx d L W) :
    blockM d L W lam hH (siteBlock d L W y) α =
      ((unMy d L W lam (fun x => hH.eigenvectorBasis α x) y : ℝ) : ℂ) := by
  rw [unMy_eq hL lam _ (JakSpectral_unit_norm hH α) y]
  have hsq : ∀ x, star (hH.eigenvectorBasis α x) * hH.eigenvectorBasis α x =
      ((‖hH.eigenvectorBasis α x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [Complex.star_def, Complex.conj_mul']
    push_cast; ring
  unfold blockM siteBlock
  simp only [hsq]
  push_cast
  rfl

/-- `M_{y,α} = N ∑_x |ψ_α(x)|² S°_{xy}` (the definition of `M_{y,α}` at `yw982823`; RBM2D `:226`);
needs `3 ≤ L` through `blockM_eq_unMy`. -/
theorem blockM_eq {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) (lam : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (y α : Idx d L W) :
    blockM d L W lam hH (siteBlock d L W y) α =
      (((W * L) ^ d : ℕ) : ℂ) *
        ∑ x, ((‖hH.eigenvectorBasis α x‖ ^ 2 : ℝ) : ℂ) * scirc d L W lam x y := by
  rw [blockM_eq_unMy hL lam hH y α]
  unfold unMy scirc
  push_cast
  rfl

/-! ## 3. The exact spectral expansion of the `y`-term of `UNJak` -/

/-- Exact eigenbasis expansion of the `y`-term before substituting `blockM_eq`. -/
private theorem JakSpectral_sum_variance {d L W : ℕ} [NeZero L] [NeZero W] (lam : ℝ)
    {Hm : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : Hm.IsHermitian) (y : Idx d L W) {z : ℂ}
    (hη : 0 < z.im) (σ₁ σ₂ : Bool) :
    (∑ x : Idx d L W, (Gres Hm z σ₁ * Gres Hm z σ₁) x x * scirc d L W lam x y *
        Gres Hm z σ₂ y y) =
      ∑ α : Idx d L W, ∑ γ : Idx d L W,
        spectralGsigPole hH z σ₁ α * spectralGsigPole hH z σ₁ α *
          spectralGsigPole hH z σ₂ γ *
          (Complex.normSq (hH.eigenvectorBasis γ y) : ℂ) *
          ∑ x : Idx d L W,
            (Complex.normSq (hH.eigenvectorBasis α x) : ℂ) * scirc d L W lam x y := by
  let S0 : Idx d L W → ℂ := fun x => scirc d L W lam x y
  let A : Idx d L W → Idx d L W → ℂ := fun α x =>
    (Complex.normSq (hH.eigenvectorBasis α x) : ℂ)
  let P : Idx d L W → ℂ := fun α =>
    spectralGsigPole hH z σ₁ α * spectralGsigPole hH z σ₁ α
  let B : Idx d L W → ℂ := fun γ =>
    spectralGsigPole hH z σ₂ γ *
      (Complex.normSq (hH.eigenvectorBasis γ y) : ℂ)
  calc
    (∑ x : Idx d L W, (Gres Hm z σ₁ * Gres Hm z σ₁) x x * S0 x * Gres Hm z σ₂ y y) =
        ∑ x : Idx d L W, (∑ α : Idx d L W, P α * A α x) * S0 x * ∑ γ : Idx d L W, B γ := by
            congr 1
            funext x
            rw [Gres_sq_apply_self_spectral hH hη σ₁, Gres_apply_self_spectral hH hη σ₂]
    _ = ∑ α : Idx d L W, ∑ γ : Idx d L W, P α * B γ * ∑ x : Idx d L W, A α x * S0 x := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        calc
          _ = ∑ α : Idx d L W, ∑ x : Idx d L W, ∑ γ : Idx d L W,
                P α * A α x * S0 x * B γ := by rw [Finset.sum_comm]
          _ = ∑ α : Idx d L W, ∑ γ : Idx d L W, ∑ x : Idx d L W,
                P α * A α x * S0 x * B γ := by
                  congr 1
                  funext α
                  rw [Finset.sum_comm]
          _ = ∑ α : Idx d L W, ∑ γ : Idx d L W, ∑ x : Idx d L W,
                P α * B γ * (A α x * S0 x) := by
                  refine Finset.sum_congr rfl fun α _ => ?_
                  refine Finset.sum_congr rfl fun γ _ => ?_
                  refine Finset.sum_congr rfl fun x _ => ?_
                  ring
          _ = _ := rfl
  simp [S0, A, P, B, mul_assoc]

/-- The averaged variance-profile factor in the spectral expansion is exactly `N⁻¹ M_{y,α}`. -/
private theorem JakSpectral_blockM_eq_variance_sum {d L W : ℕ} [NeZero L] [NeZero W]
    (hL : 3 ≤ L) (lam : ℝ) {Hm : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : Hm.IsHermitian)
    (y α : Idx d L W) :
    (((W * L) ^ d : ℕ) : ℂ)⁻¹ * blockM d L W lam hH (siteBlock d L W y) α =
      ∑ x : Idx d L W, (Complex.normSq (hH.eigenvectorBasis α x) : ℂ) * scirc d L W lam x y := by
  rw [blockM_eq hL lam hH y α]
  have hN : (((W * L) ^ d : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero d (Nat.mul_ne_zero (NeZero.ne W) (NeZero.ne L)))
  field_simp [hN]
  simp_rw [Complex.normSq_eq_norm_sq]

/-- Exact spectral expansion of the `y`-term of `(jaklsdufowe)` (the integrand of `UNJak`,
`Pins.lean:700-703`, token for token), with `N⁻¹ M_{y,α}` substituted from `blockM_eq` (RBM2D `:322`). -/
theorem green_spectral_identity_blockM {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L)
    (lam : ℝ) {Hm : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : Hm.IsHermitian) (y : Idx d L W)
    {z : ℂ} (hη : 0 < z.im) (σ₁ σ₂ : Bool) :
    (∑ x : Idx d L W, (Gres Hm z σ₁ * Gres Hm z σ₁) x x * scirc d L W lam x y *
        Gres Hm z σ₂ y y) =
      ((((W * L) ^ d : ℕ) : ℂ))⁻¹ * ∑ α : Idx d L W, ∑ γ : Idx d L W,
        spectralGsigPole hH z σ₁ α * spectralGsigPole hH z σ₁ α *
          spectralGsigPole hH z σ₂ γ * blockM d L W lam hH (siteBlock d L W y) α *
          (Complex.normSq (hH.eigenvectorBasis γ y) : ℂ) := by
  rw [JakSpectral_sum_variance lam hH y hη σ₁ σ₂]
  simp_rw [← JakSpectral_blockM_eq_variance_sum hL lam hH y]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  refine Finset.sum_congr rfl fun γ _ => ?_
  ring

/-- Triangle bound for the exact expansion (RBM2D `:339`).  The `γ`-sum remains weighted by the actual
eigenvector masses at `y`; no uniform eigenvector bound is assumed. -/
theorem norm_green_spectral_identity_blockM_le {d L W : ℕ} [NeZero L] [NeZero W]
    (hL : 3 ≤ L) (lam : ℝ) {Hm : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : Hm.IsHermitian)
    (y : Idx d L W) {z : ℂ} (hη : 0 < z.im) (σ₁ σ₂ : Bool) :
    ‖∑ x : Idx d L W, (Gres Hm z σ₁ * Gres Hm z σ₁) x x * scirc d L W lam x y *
        Gres Hm z σ₂ y y‖ ≤
      ((((W * L) ^ d : ℕ) : ℝ))⁻¹ *
        (∑ α : Idx d L W, ‖spectralGsigPole hH z σ₁ α‖ ^ 2 *
          ‖blockM d L W lam hH (siteBlock d L W y) α‖) *
        (∑ γ : Idx d L W, ‖spectralGsigPole hH z σ₂ γ‖ *
          Complex.normSq (hH.eigenvectorBasis γ y)) := by
  rw [green_spectral_identity_blockM hL lam hH y hη σ₁ σ₂]
  let P : Idx d L W → ℂ := fun α => spectralGsigPole hH z σ₁ α
  let Q : Idx d L W → ℂ := fun γ => spectralGsigPole hH z σ₂ γ
  let M : Idx d L W → ℂ := fun α => blockM d L W lam hH (siteBlock d L W y) α
  let w : Idx d L W → ℝ := fun γ => Complex.normSq (hH.eigenvectorBasis γ y)
  have hw (γ : Idx d L W) : 0 ≤ w γ := by
    simp only [w, Complex.normSq_eq_norm_sq]
    positivity
  have hnormw (γ : Idx d L W) : ‖(w γ : ℂ)‖ = w γ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw γ)]
  have hterm (α γ : Idx d L W) :
      ‖P α * P α * Q γ * M α * (w γ : ℂ)‖ ≤
        ‖P α‖ ^ 2 * ‖M α‖ * (‖Q γ‖ * w γ) := by
    calc
      ‖P α * P α * Q γ * M α * (w γ : ℂ)‖ =
          ‖P α‖ ^ 2 * ‖M α‖ * (‖Q γ‖ * w γ) := by
            simp only [norm_mul, hnormw]
            ring
      _ ≤ _ := le_rfl
  have htriangle :
      ‖∑ α : Idx d L W, ∑ γ : Idx d L W,
          P α * P α * Q γ * M α * (w γ : ℂ)‖ ≤
        ∑ α : Idx d L W, ∑ γ : Idx d L W,
          ‖P α * P α * Q γ * M α * (w γ : ℂ)‖ := by
    calc
      ‖∑ α : Idx d L W, ∑ γ : Idx d L W,
          P α * P α * Q γ * M α * (w γ : ℂ)‖ ≤
          ∑ α : Idx d L W, ‖∑ γ : Idx d L W,
            P α * P α * Q γ * M α * (w γ : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ α : Idx d L W, ∑ γ : Idx d L W,
            ‖P α * P α * Q γ * M α * (w γ : ℂ)‖ := by
          exact Finset.sum_le_sum fun α _ => norm_sum_le _ _
  have htermSum :
      ∑ α : Idx d L W, ∑ γ : Idx d L W,
          ‖P α * P α * Q γ * M α * (w γ : ℂ)‖ ≤
        ∑ α : Idx d L W, ∑ γ : Idx d L W, ‖P α‖ ^ 2 * ‖M α‖ * (‖Q γ‖ * w γ) := by
    exact Finset.sum_le_sum fun α _ =>
      Finset.sum_le_sum fun γ _ => hterm α γ
  have hfactor :
      ∑ α : Idx d L W, ∑ γ : Idx d L W, ‖P α‖ ^ 2 * ‖M α‖ * (‖Q γ‖ * w γ) =
        (∑ α : Idx d L W, ‖P α‖ ^ 2 * ‖M α‖) *
          (∑ γ : Idx d L W, ‖Q γ‖ * w γ) := by
    calc
      _ = ∑ α : Idx d L W, (‖P α‖ ^ 2 * ‖M α‖) *
            ∑ γ : Idx d L W, ‖Q γ‖ * w γ := by
              refine Finset.sum_congr rfl fun α _ => ?_
              rw [Finset.mul_sum]
      _ = _ := by rw [Finset.sum_mul]
  calc
    ‖(((W * L) ^ d : ℕ) : ℂ)⁻¹ * ∑ α : Idx d L W, ∑ γ : Idx d L W,
        P α * P α * Q γ * M α * (w γ : ℂ)‖ =
        ((((W * L) ^ d : ℕ) : ℝ))⁻¹ *
          ‖∑ α : Idx d L W, ∑ γ : Idx d L W,
            P α * P α * Q γ * M α * (w γ : ℂ)‖ := by
          rw [norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ ((((W * L) ^ d : ℕ) : ℝ))⁻¹ *
          (∑ α : Idx d L W, ∑ γ : Idx d L W,
            ‖P α * P α * Q γ * M α * (w γ : ℂ)‖) := by
          exact mul_le_mul_of_nonneg_left htriangle (by positivity)
    _ ≤ ((((W * L) ^ d : ℕ) : ℝ))⁻¹ *
          (∑ α : Idx d L W, ∑ γ : Idx d L W,
            ‖P α‖ ^ 2 * ‖M α‖ * (‖Q γ‖ * w γ)) := by
          exact mul_le_mul_of_nonneg_left htermSum (by positivity)
    _ = (((((W * L) ^ d : ℕ) : ℝ))⁻¹ *
          (∑ α : Idx d L W, ‖P α‖ ^ 2 * ‖M α‖)) *
            (∑ γ : Idx d L W, ‖Q γ‖ * w γ) := by
          rw [hfactor]
          ring

/-! ## 4. The mass bound `∑_α |M_{a₀,α}| ≤ 2N` -/

private theorem JakSpectral_N_pos {d L W : ℕ} [NeZero L] [NeZero W] :
    (0 : ℝ) < (((W * L) ^ d : ℕ) : ℝ) := by
  exact_mod_cast pow_pos (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne W))
    (Nat.pos_of_ne_zero (NeZero.ne L))) d

/-- Column sums of the variance profile: `∑_x S_{xy} = 1` for `3 ≤ L`, every `lam`
(`card_Iblk`, `sum_SBR_row`, `SBR_comm`; template `unMy_eq`'s `hgroup`, `Pins.lean:1171-1180`). -/
private theorem JakSpectral_sum_svarF_col {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L)
    (lam : ℝ) (y : Idx d L W) : ∑ x : Idx d L W, svarF d L W lam x y = 1 := by
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

private theorem JakSpectral_scirc_norm_le {d L W : ℕ} [NeZero L] [NeZero W] (lam : ℝ)
    (x y : Idx d L W) :
    ‖scirc d L W lam x y‖ ≤ svarF d L W lam x y + (((W * L) ^ d : ℕ) : ℝ)⁻¹ := by
  unfold scirc
  calc ‖((svarF d L W lam x y : ℝ) : ℂ) - ((((W * L) ^ d : ℕ) : ℂ))⁻¹‖
      ≤ ‖((svarF d L W lam x y : ℝ) : ℂ)‖ + ‖((((W * L) ^ d : ℕ) : ℂ))⁻¹‖ := norm_sub_le _ _
    _ = _ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (svarF_nonneg d L W lam x y),
          norm_inv, Complex.norm_natCast]

/-- `|M_{y,α}| ≤ N ∑_x |ψ_α(x)|² (S_{xy} + N⁻¹)`. -/
private theorem JakSpectral_norm_blockM_le {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L)
    (lam : ℝ) {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (y α : Idx d L W) :
    ‖blockM d L W lam hH (siteBlock d L W y) α‖ ≤ (((W * L) ^ d : ℕ) : ℝ) *
      ∑ x : Idx d L W, ‖hH.eigenvectorBasis α x‖ ^ 2 *
        (svarF d L W lam x y + (((W * L) ^ d : ℕ) : ℝ)⁻¹) := by
  rw [blockM_eq hL lam hH y α, norm_mul, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_))
    (by positivity)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left (JakSpectral_scirc_norm_le lam x y) (sq_nonneg _)

private theorem JakSpectral_profile_weight_sum {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L)
    (lam : ℝ) (y : Idx d L W) :
    ∑ x : Idx d L W, (svarF d L W lam x y + (((W * L) ^ d : ℕ) : ℝ)⁻¹) = 2 := by
  rw [Finset.sum_add_distrib, JakSpectral_sum_svarF_col hL lam y]
  have hN : (((W * L) ^ d : ℕ) : ℝ) ≠ 0 := ne_of_gt JakSpectral_N_pos
  have hconst : ∑ _x : Idx d L W, (((W * L) ^ d : ℕ) : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, card_Idx, nsmul_eq_mul]
    field_simp
  rw [hconst]
  norm_num

/-- Full-spectrum aggregate of the block profile: `∑_α |M_{a₀,α}| ≤ 2N` (RBM2D `:490`).  Eigenbasis
completeness (`∑_α |ψ_α(x)|² = 1`) and the column sum `∑_x S_{xy} = 1` at a site `y` of the block `a₀`. -/
theorem sum_norm_blockM_le {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) (lam : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (a0 : Zd d L) :
    ∑ α : Idx d L W, ‖blockM d L W lam hH a0 α‖ ≤ 2 * (((W * L) ^ d : ℕ) : ℝ) := by
  obtain ⟨y, hy⟩ : ∃ y : Idx d L W, siteBlock d L W y = a0 := by
    obtain ⟨y, hy⟩ := (split_bijective d L W).2
      (a0, ⟨0, pow_pos (Nat.pos_of_ne_zero (NeZero.ne W)) d⟩)
    exact ⟨y, by simp [siteBlock, hy]⟩
  subst hy
  have hN : 0 ≤ (((W * L) ^ d : ℕ) : ℝ) := by positivity
  calc
    ∑ α : Idx d L W, ‖blockM d L W lam hH (siteBlock d L W y) α‖ ≤
        ∑ α : Idx d L W, (((W * L) ^ d : ℕ) : ℝ) *
          ∑ x : Idx d L W, ‖hH.eigenvectorBasis α x‖ ^ 2 *
            (svarF d L W lam x y + (((W * L) ^ d : ℕ) : ℝ)⁻¹) :=
      Finset.sum_le_sum fun α _ => JakSpectral_norm_blockM_le hL lam hH y α
    _ = (((W * L) ^ d : ℕ) : ℝ) *
        ∑ x : Idx d L W, (∑ α : Idx d L W, ‖hH.eigenvectorBasis α x‖ ^ 2) *
          (svarF d L W lam x y + (((W * L) ^ d : ℕ) : ℝ)⁻¹) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_mul]
    _ = (((W * L) ^ d : ℕ) : ℝ) *
        ∑ x : Idx d L W, (svarF d L W lam x y + (((W * L) ^ d : ℕ) : ℝ)⁻¹) := by
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [JakSpectral_sum_sq_norm hH x, one_mul]
    _ = 2 * (((W * L) ^ d : ℕ) : ℝ) := by
      rw [JakSpectral_profile_weight_sum hL lam y]
      ring

/-! ## 5. The bad event through the merged `UNBadY` and `unBadY_measure_le` -/

/-- The eigenbasis event of RBM2D `measure_bad_le_of_queBadMat` at the window and threshold of the merged
`UNBadY` (`Pins.lean:1147-1150`) is contained in `UNBadY`. -/
theorem unBadY_of_blockM {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L)
    {lam 𝔡 E : ℝ} {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : M.IsHermitian)
    (y α : Idx d L W)
    (h1 : |hH.eigenvalues α - E| ≤ (((W * L) ^ d : ℕ) : ℝ)⁻¹ * (W : ℝ) ^ (𝔡 / 3))
    (h2 : (W : ℝ) ^ (-(𝔡 / 6)) ≤ ‖blockM d L W lam hH (siteBlock d L W y) α‖) :
    UNBadY d L W lam 𝔡 E y M := by
  refine ⟨hH.eigenvalues, fun k x => hH.eigenvectorBasis k x,
    isOrthoEigenbasis_eigenvectorBasis hH, α, h1, ?_⟩
  rw [blockM_eq_unMy hL lam hH y α, Complex.norm_real, Real.norm_eq_abs] at h2
  exact h2

/-- RBM2D `measure_bad_le_of_queBadMat` (`:537`) restated at the `d ≥ 3` data: the merged `queBadMat` at
`(ε₀, c) = (𝔡/3, 𝔡/6)` (`1_2:575-577`) and `2d + 1` blocks instead of `5`; a corollary of
`unBadY_of_blockM` and the merged `unBadY_measure_le` (`Pins.lean:1320`) with the same hypotheses. -/
theorem measure_bad_le_of_queBadMat {d L W : ℕ} [NeZero L] [NeZero W] {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (hL : 3 ≤ L) {lam 𝔡 E : ℝ} (hW : 1 ≤ (W : ℝ))
    (h𝔡 : 0 < 𝔡) (hlam : (W : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ lam) (y : Idx d L W)
    {Hr : Ω → Matrix (Idx d L W) (Idx d L W) ℂ} (hH : ∀ ω, (Hr ω).IsHermitian) (p : ℝ≥0∞)
    (hp : ∀ b : Zd d L, P {ω | queBadMat d L W lam (𝔡 / 3) (𝔡 / 6) E b (Hr ω)} ≤ p) :
    P {ω | ∃ α, |(hH ω).eigenvalues α - E| ≤ (((W * L) ^ d : ℕ) : ℝ)⁻¹ * (W : ℝ) ^ (𝔡 / 3) ∧
        (W : ℝ) ^ (-(𝔡 / 6)) ≤ ‖blockM d L W lam (hH ω) (siteBlock d L W y) α‖} ≤
      ((2 * d + 1 : ℕ) : ℝ≥0∞) * p := by
  refine le_trans (measure_mono ?_) (unBadY_measure_le P hL hW h𝔡 hlam y Hr p hp)
  rintro ω ⟨α, h1, h2⟩
  exact unBadY_of_blockM hL (hH ω) y α h1 h2

/-! ## 6. Compiled nonempty instances (`d = 3`, `L = 3`, `W = 2`, `N = 216`) -/

namespace JakSpectralInst

/-- The `216 × 216` identity matrix, a Hermitian matrix on `Idx 3 3 2`. -/
noncomputable abbrev H1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ := 1

def y0 : Idx 3 3 2 := 0

def a0 : Zd 3 3 := 0

private theorem I_im_ne : Complex.I.im ≠ 0 := by simp

private theorem I_im_pos : 0 < Complex.I.im := by simp

/-- `inst_spectral` (targets 1a-1e at the data; RBM2D `:607-631`). -/
theorem inst_spectral :
    ∀ hH : H1.IsHermitian,
    (Gres H1 Complex.I true * Gres H1 Complex.I true) y0 y0 =
        ∑ α, spectralPole hH Complex.I α * spectralPole hH Complex.I α *
          (Complex.normSq (hH.eigenvectorBasis α y0) : ℂ) ∧
      Gres H1 Complex.I false y0 y0 =
        ∑ β, spectralGsigPole hH Complex.I false β *
          (Complex.normSq (hH.eigenvectorBasis β y0) : ℂ) ∧
      (Gres H1 Complex.I false * Gres H1 Complex.I false) y0 y0 =
        ∑ α, spectralGsigPole hH Complex.I false α * spectralGsigPole hH Complex.I false α *
          (Complex.normSq (hH.eigenvectorBasis α y0) : ℂ) ∧
      ‖spectralGsigPole hH Complex.I false y0‖ = ‖spectralPole hH Complex.I y0‖ ∧
      IsOrthoEigenbasis H1 hH.eigenvalues (fun k x => hH.eigenvectorBasis k x) :=
  fun hH => ⟨Gres_sq_apply_self hH (JakSpectral_eigenvalues_ne_of_im_ne hH I_im_ne) y0,
    Gres_apply_self_spectral hH I_im_pos false y0,
    Gres_sq_apply_self_spectral hH I_im_pos false y0,
    spectralGsigPole_norm_eq_spectralPole hH Complex.I false y0,
    isOrthoEigenbasis_eigenvectorBasis hH⟩

/-- `inst_block` (targets 2a, 2b at `lam = 1/2`; RBM2D `:633`). -/
theorem inst_block :
    ∀ hH : H1.IsHermitian,
    blockM 3 3 2 (1 / 2) hH (siteBlock 3 3 2 y0) y0 =
        (((2 * 3) ^ 3 : ℕ) : ℂ) *
          ∑ x, ((‖hH.eigenvectorBasis y0 x‖ ^ 2 : ℝ) : ℂ) * scirc 3 3 2 (1 / 2) x y0 ∧
      blockM 3 3 2 (1 / 2) hH (siteBlock 3 3 2 y0) y0 =
        ((unMy 3 3 2 (1 / 2) (fun x => hH.eigenvectorBasis y0 x) y0 : ℝ) : ℂ) :=
  fun hH => ⟨blockM_eq (by norm_num) _ hH y0 y0, blockM_eq_unMy (by norm_num) _ hH y0 y0⟩

/-- `inst_identity` (targets 3a, 3b at `z = I`, `σ₁ = true`, `σ₂ = false`; RBM2D `:639-660`). -/
theorem inst_identity :
    ∀ hH : H1.IsHermitian,
    (∑ x, (Gres H1 Complex.I true * Gres H1 Complex.I true) x x *
          scirc 3 3 2 (1 / 2) x y0 * Gres H1 Complex.I false y0 y0) =
        ((((2 * 3) ^ 3 : ℕ) : ℂ))⁻¹ * ∑ α, ∑ γ,
          spectralGsigPole hH Complex.I true α * spectralGsigPole hH Complex.I true α *
            spectralGsigPole hH Complex.I false γ *
            blockM 3 3 2 (1 / 2) hH (siteBlock 3 3 2 y0) α *
            (Complex.normSq (hH.eigenvectorBasis γ y0) : ℂ) ∧
      ‖∑ x, (Gres H1 Complex.I true * Gres H1 Complex.I true) x x *
          scirc 3 3 2 (1 / 2) x y0 * Gres H1 Complex.I false y0 y0‖ ≤
        ((((2 * 3) ^ 3 : ℕ) : ℝ))⁻¹ *
          (∑ α, ‖spectralGsigPole hH Complex.I true α‖ ^ 2 *
            ‖blockM 3 3 2 (1 / 2) hH (siteBlock 3 3 2 y0) α‖) *
          (∑ γ, ‖spectralGsigPole hH Complex.I false γ‖ *
            Complex.normSq (hH.eigenvectorBasis γ y0)) :=
  fun hH => ⟨green_spectral_identity_blockM (by norm_num) _ hH y0 I_im_pos true false,
    norm_green_spectral_identity_blockM_le (by norm_num) _ hH y0 I_im_pos true false⟩

/-- `inst_mass` (target 4 at `a₀ = 0`; RBM2D `:661`). -/
theorem inst_mass :
    ∀ hH : H1.IsHermitian,
    ∑ α, ‖blockM 3 3 2 (1 / 2) hH a0 α‖ ≤ 2 * (((2 * 3) ^ 3 : ℕ) : ℝ) :=
  fun hH => sum_norm_blockM_le (by norm_num) _ hH a0

/-- `inst_bad` (target 5b at `Ω = Unit`, `P = δ_()`, `Hr ≡ 1`, `lam = 1`, `𝔡 = 1/10`, `E = 1`, `p = 1`;
every hypothesis discharged: `3 ≤ 3`, `1 ≤ 2`, `0 < 1/10`, `2^{-3/2 + 1/10} ≤ 1`, `δ(·) ≤ 1`). -/
theorem inst_bad :
    ∀ hH : ∀ _ω : Unit, H1.IsHermitian,
    (MeasureTheory.Measure.dirac ()) {ω : Unit | ∃ α, |(hH ω).eigenvalues α - 1| ≤
        (((2 * 3) ^ 3 : ℕ) : ℝ)⁻¹ * ((2 : ℕ) : ℝ) ^ ((1 / 10 : ℝ) / 3) ∧
      ((2 : ℕ) : ℝ) ^ (-((1 / 10 : ℝ) / 6)) ≤ ‖blockM 3 3 2 1 (hH ω) (siteBlock 3 3 2 y0) α‖} ≤
      ((2 * 3 + 1 : ℕ) : ℝ≥0∞) * 1 := by
  intro hH
  refine measure_bad_le_of_queBadMat (MeasureTheory.Measure.dirac ()) (by norm_num)
    (lam := 1) (𝔡 := 1 / 10) (E := 1) (by norm_num) (by norm_num) ?_ y0 hH 1 (fun b => prob_le_one)
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)

end JakSpectralInst

#print axioms RBM.Univ.Gres_sq_apply_self
#print axioms RBM.Univ.Gres_apply_self_spectral
#print axioms RBM.Univ.Gres_sq_apply_self_spectral
#print axioms RBM.Univ.spectralGsigPole_norm_eq_spectralPole
#print axioms RBM.Univ.isOrthoEigenbasis_eigenvectorBasis
#print axioms RBM.Univ.blockM_eq
#print axioms RBM.Univ.blockM_eq_unMy
#print axioms RBM.Univ.green_spectral_identity_blockM
#print axioms RBM.Univ.norm_green_spectral_identity_blockM_le
#print axioms RBM.Univ.sum_norm_blockM_le
#print axioms RBM.Univ.unBadY_of_blockM
#print axioms RBM.Univ.measure_bad_le_of_queBadMat
#print axioms RBM.Univ.JakSpectralInst.inst_spectral
#print axioms RBM.Univ.JakSpectralInst.inst_block
#print axioms RBM.Univ.JakSpectralInst.inst_identity
#print axioms RBM.Univ.JakSpectralInst.inst_mass
#print axioms RBM.Univ.JakSpectralInst.inst_bad

end RBM.Univ
