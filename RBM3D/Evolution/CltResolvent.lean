/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Evolution.CltSwap
import RBM3D.Gauss.FlowCalculus
import RBM3D.Green.EntryCore

/-!
# Deterministic resolvent bounds for the replacement step

On the fine model of `RBM3D/Gauss/FineModel.lean`.  Paper: (5.36) `eq:bound_isolated` of Lemma 5.1
(which cites [DYYY25, (7.39)]); the argument is the replacement step, see
`RBM3D/Induction/Step5Pins.lean` (`STCltIsoConcl`).  The vocabulary:

* `Zd d L` is the block lattice, `zdistInf d L` the distance (the paper's `|x|_L`,
  `Defs/Sizes.lean`), `Idx d L W` the fine lattice, `CoordF d L W` the coordinates, `gvarF d L W g`
  their variances (the variance parameter `g` is explicit), `coordinateMatrix d L W` the matrix
  directions, `zt` the spectral path, `N = (W L)^d = card (Idx d L W)`, and the support
  `{0} ∪ {zdistD = 1}` of `sbKernelR` (`Defs/Block.lean`; `2 d + 1` points).
* `gEntry E s M σ x y := Gres M (zt E s) σ x y` (`Loop/GLoopFlow.lean`), the entry of the
  `σ`-resolvent used by `loopFine`.
* `LocalForm.Local ρ` takes the locality radius `ρ` as a parameter.
* The label count `k` of `LocalForm` is general: `STcltB`/`STcltX` (`Induction/Step5Pins.lean`) use
  two.  Every statement that mentions the labels has the form with `b : Fin k → Zd d L` (names with
  the suffix Multi).
* **Re-scaled geometry.**  `CltFarGeomNear` has a locality radius `ρ` and a separation `R`: `x`
  within `ρ` of `b`, `a` at distance `≥ R/2` from `b` give `|x - a|_∞, |x - a'|_∞ ≥ R/2 - ρ - 1`,
  for all real `ρ`, `R` (triangle inequality).  `3 ≤ L` of `CltCoordAdj` is not needed (the support
  of `sbKernelR` is read directly).

The private helpers `cltres_*` are elementary.  Everything here is deterministic.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Evol

open Matrix RBM RBM.Gauss

/-! ## 1. The vocabulary -/

section Vocab

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- `G_s(σ)_{xy}` at the matrix `M` on the fine lattice: the
`(x, y)` entry of the `σ`-resolvent `Gres M (zt E s) σ` of `Loop/GLoopFlow.lean` (`G(+) = (M -
z_s)⁻¹`, `G(-) = (M - \bar z_s)⁻¹`). -/
def gEntry (E s : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (σ : Bool) (x y : Idx d L W) : ℂ :=
  Gres M (zt E s) σ x y

/-- `G_s(σ)_{xy}` at the spectral value `m`: `z_s = ztOf m E s = E + (1 - s) m`.  The band
`gEntry` is `gEntryOf d L W (mE E)`, by `rfl`. -/
def gEntryOf (m : ℂ) (E s : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (σ : Bool) (x y : Idx d L W) : ℂ :=
  Gres M (ztOf m E s) σ x y

end Vocab

/-- The deterministic coefficients of the local form: a polynomial of degree `≤ K`
in the entries `G_s(σ_i)_{x_i y_i}`; `coef b j q` is the coefficient of the monomial
`∏_{i<j} G_s(q_i.2.2)_{q_i.1, q_i.2.1}`, with `k` labels `b : Fin k → Zd d L`. -/
structure LocalForm (d L W k K : ℕ) where
  coef : (Fin k → Zd d L) → (j : Fin (K + 1)) → (Fin j → Idx d L W × Idx d L W × Bool) → ℂ

namespace LocalForm

variable {d L W k K : ℕ} [NeZero L] [NeZero W]

/-- The tensor `𝒜_b` of the local form at the matrix `M`. -/
def eval (F : LocalForm d L W k K) (E s : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (b : Fin k → Zd d L) : ℂ :=
  ∑ j : Fin (K + 1), ∑ q : Fin j → Idx d L W × Idx d L W × Bool,
    F.coef b j q * ∏ i : Fin j, gEntry d L W E s M (q i).2.2 (q i).1 (q i).2.1

/-- `𝒜_b` of (`a-local-form`) at the spectral value `m` (band `eval` is `evalOf (mE E)`, `rfl`). -/
def evalOf (F : LocalForm d L W k K) (m : ℂ) (E s : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (b : Fin k → Zd d L) : ℂ :=
  ∑ j : Fin (K + 1), ∑ q : Fin j → Idx d L W × Idx d L W × Bool,
    F.coef b j q * ∏ i : Fin j, gEntryOf d L W m E s M (q i).2.2 (q i).1 (q i).2.1

/-- The locality condition of the local form with the radius `ρ` as a parameter: a non-zero
coefficient has every entry `(x_i, y_i)` within `ρ` of some label `b_m` (blocks
`[x] = (split d L W x).1`, distance `zdistInf`). -/
def Local (F : LocalForm d L W k K) (ρ : ℝ) : Prop :=
  ∀ b j q, F.coef b j q ≠ 0 → ∀ i, ∃ m : Fin k,
    ((zdistInf d L ((split d L W (q i).1).1 - b m) +
        zdistInf d L ((split d L W (q i).2.1).1 - b m) : ℕ) : ℝ) < ρ

end LocalForm

/-! ## 2. The statements -/

section Det

/-- A one-coordinate direction with support `{(a₀,b₀),(b₀,a₀)}` and entries of modulus `≤ 1`.
`√u • coordinateMatrix d L W c` is one for `0 ≤ u ≤ 1` (by `CltCoordAdj`, `c = (a₀, b₀, β)`). -/
def cltCoordDir {ι : Type*} (A : Matrix ι ι ℂ) (a₀ b₀ : ι) : Prop :=
  A.IsHermitian ∧ (∀ a b, ‖A a b‖ ≤ 1) ∧
    ∀ a b, A a b ≠ 0 → (a = a₀ ∧ b = b₀) ∨ (a = b₀ ∧ b = a₀)

/-- **Entrywise bound of the perturbed resolvent** (deterministic part).
If `|G_{xy}| ≤ g` for all entries and `4|t| g ≤ 1`, then `|(G_t)_{xy}| ≤ 2g`, where
`G_t = (M + tA - z)⁻¹`. Consumers: `CltPathBoundMulti`. -/
def CltPertMaxLe (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (M A : Matrix ι ι ℂ) (a₀ b₀ : ι) (z : ℂ) (t g : ℝ), M.IsHermitian → cltCoordDir A a₀ b₀ →
    z.im ≠ 0 → (∀ x y, ‖green M z x y‖ ≤ g) → 4 * |t| * g ≤ 1 →
    ∀ x y, ‖green (M + (t : ℂ) • A) z x y‖ ≤ 2 * g

/-- **The perturbation difference.**  `G_t - G = -t G A G_t = -t G_t A G` bounded entrywise.
Consumers: `CltPathBoundMulti` (far entries along the path). -/
def CltPertSubLe (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (M A : Matrix ι ι ℂ) (a₀ b₀ : ι) (z : ℂ) (t gt : ℝ), M.IsHermitian → cltCoordDir A a₀ b₀ →
    z.im ≠ 0 → (∀ x y, ‖green (M + (t : ℂ) • A) z x y‖ ≤ gt) →
    ∀ x y,
      ‖green (M + (t : ℂ) • A) z x y - green M z x y‖ ≤
          2 * |t| * gt * max ‖green M z x a₀‖ ‖green M z x b₀‖ ∧
        ‖green (M + (t : ℂ) • A) z x y - green M z x y‖ ≤
          2 * |t| * gt * max ‖green M z a₀ y‖ ‖green M z b₀ y‖

/-- **The derivative of an entry** (`∂_{H_ij}(G_s)_{xy} = -(G_s)_{xi}(G_s)_{jy}`).
The derivative of `s ↦ (G_s)_{xy}` along the direction `A`, and its entrywise bounds.  Applied
with `z` and with `conj z` (the two values of `σ` in `gEntry`).  Consumers: `CltDerivEvalMultiOf`.
Input: `hasDerivAt_green_moving` (`Gauss/FlowCalculus.lean`). -/
def CltDerivEntry (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (M A : Matrix ι ι ℂ) (a₀ b₀ : ι) (z : ℂ) (t : ℝ), M.IsHermitian → cltCoordDir A a₀ b₀ →
    z.im ≠ 0 → ∀ x y,
      HasDerivAt (fun s : ℝ => green (M + (s : ℂ) • A) z x y)
        (-(green (M + (t : ℂ) • A) z * A * green (M + (t : ℂ) • A) z) x y) t ∧
      ∀ g : ℝ, (∀ x' y', ‖green (M + (t : ℂ) • A) z x' y'‖ ≤ g) →
        ‖(green (M + (t : ℂ) • A) z * A * green (M + (t : ℂ) • A) z) x y‖ ≤
            2 * g * max ‖green (M + (t : ℂ) • A) z x a₀‖ ‖green (M + (t : ℂ) • A) z x b₀‖ ∧
          ‖(green (M + (t : ℂ) • A) z * A * green (M + (t : ℂ) • A) z) x y‖ ≤
            2 * g * max ‖green (M + (t : ℂ) • A) z a₀ y‖ ‖green (M + (t : ℂ) • A) z b₀ y‖

/-- **The derivative of the local form** at the spectral value `m`, `k` labels: the premise is
`(ztOf m E u).im ≠ 0`. -/
def CltDerivEvalMultiOf (d L W k : ℕ) [NeZero L] [NeZero W] : Prop :=
  ∀ (K : ℕ) (F : LocalForm d L W k K) (m : ℂ) (E u : ℝ) (M A : Matrix (Idx d L W) (Idx d L W) ℂ)
    (a₀ b₀ : Idx d L W) (t g φ : ℝ) (b : Fin k → Zd d L),
    M.IsHermitian → cltCoordDir A a₀ b₀ → (ztOf m E u).im ≠ 0 →
    (∀ σ x y, ‖gEntryOf d L W m E u (M + (t : ℂ) • A) σ x y‖ ≤ g) →
    (∀ (j : Fin (K + 1)) (q : Fin j → Idx d L W × Idx d L W × Bool),
      F.coef b j q ≠ 0 → ∀ (i : Fin j) (σ : Bool),
        ‖gEntryOf d L W m E u (M + (t : ℂ) • A) σ (q i).1 a₀‖ ≤ φ ∧
          ‖gEntryOf d L W m E u (M + (t : ℂ) • A) σ (q i).1 b₀‖ ≤ φ) →
    ∃ D : ℂ, HasDerivAt (fun s : ℝ => F.evalOf m E u (M + (s : ℂ) • A) b) D t ∧
      ‖D‖ ≤ 2 * ∑ j : Fin (K + 1), ∑ q : Fin j → Idx d L W × Idx d L W × Bool,
        ‖F.coef b j q‖ * (j : ℝ) * g ^ (j : ℕ) * φ

/-- `c_κ = √(κ(4-κ))/2`, the lower bound of `Im m(E)` for `|E| ≤ 2 - κ`. -/
def cltCk (κ : ℝ) : ℝ := Real.sqrt (κ * (4 - κ)) / 2

/-- **Lower bound on `Im z_u`**: `κ ≤ Im m` and `N^{-1+δ} ≤ 1 - u` give `κ / N ≤ Im z_u`,
`z_u = ztOf m E u`; no `|E| ≤ 2 - κ`, no `‖m‖ = 1`. -/
def CltEtaLowerOf (d L W : ℕ) : Prop :=
  ∀ (κ δ : ℝ) (m : ℂ) (E u : ℝ), 0 < κ → 0 < δ → κ ≤ m.im →
    ((((W * L) ^ d : ℕ) : ℝ)) ^ (-1 + δ) ≤ 1 - u →
    κ / (((W * L) ^ d : ℕ) : ℝ) ≤ (ztOf m E u).im

/-- **Deterministic bound of the local form** at the spectral value `m`, `k` labels: base `2N³/κ`;
the premise is `κ ≤ 1` (base `≥ 1`). -/
def CltEvalDetLeMultiOf (d L W k : ℕ) [NeZero L] [NeZero W] : Prop :=
  ∀ (κ δ : ℝ) (m : ℂ) (E u : ℝ) (K : ℕ) (F : LocalForm d L W k K) (C' : ℝ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (b : Fin k → Zd d L),
    0 < κ → 0 < δ → κ ≤ m.im → κ ≤ 1 →
    ((((W * L) ^ d : ℕ) : ℝ)) ^ (-1 + δ) ≤ 1 - u →
    (∀ b' j q, ‖F.coef b' j q‖ ≤ ((((W * L) ^ d : ℕ) : ℝ)) ^ C') → M.IsHermitian →
    ‖F.evalOf m E u M b‖ ≤ ((K : ℝ) + 1) * ((((W * L) ^ d : ℕ) : ℝ)) ^ C' *
      (2 * ((((W * L) ^ d : ℕ) : ℝ)) ^ 3 / κ) ^ K

/-- **The dichotomy, half-separation form** (no condition on `W`).  If
`R ≤ |b_i - b_k|_∞` for all `k ≠ i`, then every block `a` has `R/2 ≤ |a - b_i|_∞` or
`R/2 ≤ |a - b_k|_∞` for all `k ≠ i`.  Consumers: `CltStep` (the case split of the replacement
step). -/
def CltFarGeomHalf : Prop :=
  ∀ (d L : ℕ) [NeZero L] (m : ℕ) (b : Fin m → Zd d L) (i : Fin m) (R : ℝ) (a : Zd d L),
    (∀ k, k ≠ i → R ≤ (zdistInf d L (b i - b k) : ℝ)) →
    R / 2 ≤ (zdistInf d L (a - b i) : ℝ) ∨ ∀ k, k ≠ i → R / 2 ≤ (zdistInf d L (a - b k) : ℝ)

/-- **The near geometry, re-scaled**. With a locality radius `ρ` and a separation `R`, both
arbitrary reals:
if the block `a` is at distance `≥ R/2` from the label `b`, `a'` is adjacent to `a`, and
`|x - b|_∞ < ρ` (a block of a monomial local to `b`), then `x` is at distance `≥ R/2 - ρ - 1` from
`a` and from `a'`. At `ρ = (log W)^3 ℓ_s`, `R = 10 (log W)^3 ℓ_s` this is `≥ 4 (log W)^3 ℓ_s - 1`,
above the far threshold `c (log W)^3 ℓ_s` of the log-scale far decay. Consumers: `CltPathBoundMulti`. -/
def CltFarGeomNear : Prop :=
  ∀ (d L : ℕ) [NeZero L] (ρ R : ℝ) (a a' b x : Zd d L),
    R / 2 ≤ (zdistInf d L (a - b) : ℝ) → zdistInf d L (a' - a) ≤ 1 →
    (zdistInf d L (x - b) : ℝ) < ρ →
    R / 2 - ρ - 1 ≤ (zdistInf d L (x - a) : ℝ) ∧ R / 2 - ρ - 1 ≤ (zdistInf d L (x - a') : ℝ)

/-- **Adjacency of a coordinate** (the restriction to `S_ij ≠ 0`).  For a coordinate `c = (x, y, β)`: if
`gvarF c ≠ 0` the blocks of `x` and `y` are adjacent (`|[x] - [y]|_∞ ≤ 1`: the support of
`sbKernelR` is `{0} ∪ {zdistD = 1}`, contained in the `∞`-ball of radius `1`); `coordinateMatrix c`
is supported on `{(x,y),(y,x)}` with entries of modulus `≤ 1`.  No condition on `L` or `g`.
Consumers: `CltStep`, `CltPathBoundMulti` (for `√u • coordinateMatrix c`). -/
def CltCoordAdj : Prop :=
  ∀ (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W] (c : CoordF d L W),
    (gvarF d L W g c ≠ 0 →
      zdistInf d L ((split d L W c.1).1 - (split d L W c.2.1).1) ≤ 1) ∧
    (∀ i j, coordinateMatrix d L W c i j ≠ 0 → (i = c.1 ∧ j = c.2.1) ∨ (i = c.2.1 ∧ j = c.1)) ∧
    (∀ i j, ‖coordinateMatrix d L W c i j‖ ≤ 1)

end Det

/-! ## 3. Perturbation of `G` in one direction -/

section Perturb

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- A real multiple of a Hermitian matrix added to a Hermitian matrix is Hermitian. -/
private theorem cltres_herm_add {M A : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (hA : A.IsHermitian) (s : ℝ) : (M + (s : ℂ) • A).IsHermitian := by
  refine hM.add ?_
  change Matrix.conjTranspose ((s : ℂ) • A) = (s : ℂ) • A
  rw [Matrix.conjTranspose_smul, hA, Complex.star_def, Complex.conj_ofReal]

/-- The first resolvent identity: `G - G_t = t G A G_t` for `G = (M - z)⁻¹`, `G_t = (M + tA - z)⁻¹`. -/
private theorem cltres_R1 {M A : Matrix ι ι ℂ} (hM : M.IsHermitian) (hA : A.IsHermitian)
    (t : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    green M z - green (M + (t : ℂ) • A) z =
      (t : ℂ) • (green M z * A * green (M + (t : ℂ) • A) z) := by
  have hX : IsUnit (M - z • (1 : Matrix ι ι ℂ)) :=
    RBM.isUnit_sub_smul_of_isHermitian hM hz
  have hY : IsUnit (M + (t : ℂ) • A - z • (1 : Matrix ι ι ℂ)) :=
    RBM.isUnit_sub_smul_of_isHermitian (cltres_herm_add hM hA t) hz
  have h := Matrix.inv_sub_inv (A := M - z • (1 : Matrix ι ι ℂ))
    (B := M + (t : ℂ) • A - z • (1 : Matrix ι ι ℂ)) ⟨fun _ => hY, fun _ => hX⟩
  have hd : (M + (t : ℂ) • A - z • (1 : Matrix ι ι ℂ)) - (M - z • (1 : Matrix ι ι ℂ))
      = (t : ℂ) • A := by abel
  rw [hd] at h
  unfold green
  rw [h, Matrix.mul_smul, Matrix.smul_mul]

/-- The second resolvent identity: `G_t - G = -t G_t A G`. -/
private theorem cltres_R2 {M A : Matrix ι ι ℂ} (hM : M.IsHermitian) (hA : A.IsHermitian)
    (t : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    green (M + (t : ℂ) • A) z - green M z =
      -((t : ℂ) • (green (M + (t : ℂ) • A) z * A * green M z)) := by
  have hX : IsUnit (M - z • (1 : Matrix ι ι ℂ)) :=
    RBM.isUnit_sub_smul_of_isHermitian hM hz
  have hY : IsUnit (M + (t : ℂ) • A - z • (1 : Matrix ι ι ℂ)) :=
    RBM.isUnit_sub_smul_of_isHermitian (cltres_herm_add hM hA t) hz
  have h := Matrix.inv_sub_inv (A := M + (t : ℂ) • A - z • (1 : Matrix ι ι ℂ))
    (B := M - z • (1 : Matrix ι ι ℂ)) ⟨fun _ => hX, fun _ => hY⟩
  have hd : (M - z • (1 : Matrix ι ι ℂ)) - (M + (t : ℂ) • A - z • (1 : Matrix ι ι ℂ))
      = -((t : ℂ) • A) := by abel
  rw [hd] at h
  unfold green
  rw [h, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul]

set_option linter.unusedDecidableInType false in
/-- The support fact: `|(P A Q)_{xy}| ≤ |P_{x a₀}||Q_{b₀ y}| + |P_{x b₀}||Q_{a₀ y}|`. -/
private theorem cltres_PAQ_le {A : Matrix ι ι ℂ} {a₀ b₀ : ι} (hA : cltCoordDir A a₀ b₀)
    (P Q : Matrix ι ι ℂ) (x y : ι) :
    ‖(P * A * Q) x y‖ ≤ ‖P x a₀‖ * ‖Q b₀ y‖ + ‖P x b₀‖ * ‖Q a₀ y‖ := by
  obtain ⟨-, hA1, hAs⟩ := hA
  have hterm : ∀ a k : ι, ‖P x a * A a k * Q k y‖ ≤
      (if a = a₀ ∧ k = b₀ then ‖P x a₀‖ * ‖Q b₀ y‖ else 0) +
      (if a = b₀ ∧ k = a₀ then ‖P x b₀‖ * ‖Q a₀ y‖ else 0) := by
    intro a k
    by_cases h0 : A a k = 0
    · rw [h0]
      simp only [mul_zero, zero_mul, norm_zero]
      split_ifs <;> positivity
    · rcases hAs a k h0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hc : a = a₀ ∧ k = b₀ := ⟨h1, h2⟩
        rw [ite_eq_left hc]
        refine le_add_of_le_of_nonneg ?_ (by split_ifs <;> positivity)
        rw [h1, h2, norm_mul, norm_mul]
        calc ‖P x a₀‖ * ‖A a₀ b₀‖ * ‖Q b₀ y‖ ≤ ‖P x a₀‖ * 1 * ‖Q b₀ y‖ := by
              gcongr; exact hA1 _ _
          _ = _ := by ring
      · have hc : a = b₀ ∧ k = a₀ := ⟨h1, h2⟩
        rw [ite_eq_left hc]
        refine le_add_of_nonneg_of_le (by split_ifs <;> positivity) ?_
        rw [h1, h2, norm_mul, norm_mul]
        calc ‖P x b₀‖ * ‖A b₀ a₀‖ * ‖Q a₀ y‖ ≤ ‖P x b₀‖ * 1 * ‖Q a₀ y‖ := by
              gcongr; exact hA1 _ _
          _ = _ := by ring
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun k _ => hterm a k)).trans (le_of_eq ?_)
  simp only [Finset.sum_add_distrib, ite_and]
  simp

end Perturb

section PerturbThms

/-- The statement `CltPertMaxLe`. -/
theorem cltPert_max_le (ι : Type*) [Fintype ι] [DecidableEq ι] : CltPertMaxLe ι := by
  intro M A a₀ b₀ z t g hM hA hz hg ht x y
  set Gt := green (M + (t : ℂ) • A) z with hGt
  set G := green M z with hG
  have hR1 : ∀ x y, Gt x y = G x y - (t : ℂ) * (G * A * Gt) x y := by
    intro x y
    have h := congrFun (congrFun (cltres_R1 hM hA.1 t hz) x) y
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
    rw [← h]; ring
  have hne : Nonempty (ι × ι) := ⟨(x, y)⟩
  obtain ⟨p, hp⟩ := Finite.exists_max (fun p : ι × ι => ‖Gt p.1 p.2‖)
  have hm0 : 0 ≤ ‖Gt p.1 p.2‖ := norm_nonneg _
  have hg0 : 0 ≤ g := (norm_nonneg _).trans (hg p.1 p.2)
  have hpm := hR1 p.1 p.2
  have hS := cltres_PAQ_le hA G Gt p.1 p.2
  have h1 : ‖G p.1 a₀‖ * ‖Gt b₀ p.2‖ ≤ g * ‖Gt p.1 p.2‖ :=
    mul_le_mul (hg _ _) (hp (b₀, p.2)) (norm_nonneg _) hg0
  have h2 : ‖G p.1 b₀‖ * ‖Gt a₀ p.2‖ ≤ g * ‖Gt p.1 p.2‖ :=
    mul_le_mul (hg _ _) (hp (a₀, p.2)) (norm_nonneg _) hg0
  have hbound : ‖Gt p.1 p.2‖ ≤ g + |t| * (g * ‖Gt p.1 p.2‖ + g * ‖Gt p.1 p.2‖) := by
    calc ‖Gt p.1 p.2‖ = ‖G p.1 p.2 - (t : ℂ) * (G * A * Gt) p.1 p.2‖ := by rw [← hpm]
      _ ≤ ‖G p.1 p.2‖ + ‖(t : ℂ) * (G * A * Gt) p.1 p.2‖ := norm_sub_le _ _
      _ = ‖G p.1 p.2‖ + |t| * ‖(G * A * Gt) p.1 p.2‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ g + |t| * (g * ‖Gt p.1 p.2‖ + g * ‖Gt p.1 p.2‖) := by
          gcongr
          · exact hg _ _
          · exact hS.trans (add_le_add h1 h2)
  have hkey : ‖Gt p.1 p.2‖ ≤ 2 * g := by
    nlinarith [mul_nonneg (sub_nonneg.2 ht) hm0]
  exact (hp (x, y)).trans hkey

/-- The statement `CltPertSubLe`. -/
theorem cltPert_sub_le (ι : Type*) [Fintype ι] [DecidableEq ι] : CltPertSubLe ι := by
  intro M A a₀ b₀ z t gt hM hA hz hgt x y
  set Gt := green (M + (t : ℂ) • A) z with hGt
  set G := green M z with hG
  have hgt0 : 0 ≤ gt := (norm_nonneg _).trans (hgt x y)
  constructor
  · have h := congrFun (congrFun (cltres_R1 hM hA.1 t hz) x) y
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
    have hS := cltres_PAQ_le hA G Gt x y
    set mx := max ‖G x a₀‖ ‖G x b₀‖ with hmx
    have hmx0 : 0 ≤ mx := (norm_nonneg _).trans (le_max_left _ _)
    have h1 : ‖G x a₀‖ * ‖Gt b₀ y‖ ≤ mx * gt :=
      mul_le_mul (le_max_left _ _) (hgt _ _) (norm_nonneg _) hmx0
    have h2 : ‖G x b₀‖ * ‖Gt a₀ y‖ ≤ mx * gt :=
      mul_le_mul (le_max_right _ _) (hgt _ _) (norm_nonneg _) hmx0
    have hd : Gt x y - G x y = -((t : ℂ) * (G * A * Gt) x y) := by rw [← h]; ring
    rw [hd, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |t| * ‖(G * A * Gt) x y‖ ≤ |t| * (mx * gt + mx * gt) := by
          gcongr; exact hS.trans (add_le_add h1 h2)
      _ = 2 * |t| * gt * mx := by ring
  · have h := congrFun (congrFun (cltres_R2 hM hA.1 t hz) x) y
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul] at h
    have hS := cltres_PAQ_le hA Gt G x y
    set my := max ‖G a₀ y‖ ‖G b₀ y‖ with hmy
    have hmy0 : 0 ≤ my := (norm_nonneg _).trans (le_max_left _ _)
    have h1 : ‖Gt x a₀‖ * ‖G b₀ y‖ ≤ gt * my :=
      mul_le_mul (hgt _ _) (le_max_right _ _) (norm_nonneg _) hgt0
    have h2 : ‖Gt x b₀‖ * ‖G a₀ y‖ ≤ gt * my :=
      mul_le_mul (hgt _ _) (le_max_left _ _) (norm_nonneg _) hgt0
    rw [h, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |t| * ‖(Gt * A * G) x y‖ ≤ |t| * (gt * my + gt * my) := by
          gcongr; exact hS.trans (add_le_add h1 h2)
      _ = 2 * |t| * gt * my := by ring

end PerturbThms

section Deriv

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Matrix.Norms.L2Operator in
/-- The resolvent along a Hermitian line has derivative `-G A G` (matrix-valued; the ambient norm
is the `L²` operator norm of `hasDerivAt_green_moving`,
with the matrix path `s ↦ M + sA` and the constant spectral parameter `z`). -/
private theorem cltres_hasDerivAt_green {M A : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => green (M + (s : ℂ) • A) z)
      (-(green (M + (t : ℂ) • A) z * A * green (M + (t : ℂ) • A) z)) t := by
  have hline : HasDerivAt (fun s : ℝ => M + (s : ℂ) • A) A t := by
    have h : HasDerivAt (fun s : ℝ => (s : ℂ) • A) A t := by
      simpa using (hasDerivAt_id t).smul_const A
    simpa using h.const_add M
  have h := hasDerivAt_green_moving (H := fun s : ℝ => M + (s : ℂ) • A) (z := fun _ => z)
    (H' := A) (z' := 0) hline (hasDerivAt_const t z) (cltres_herm_add hM hA t) hz
  have hG : ∀ N : Matrix ι ι ℂ, Gres N z true = green N z := fun N => by
    simp [Gres, green, Matrix.nonsing_inv_eq_ringInverse]
  simpa only [zero_smul, sub_zero, hG] using h

open scoped Matrix.Norms.L2Operator in
/-- The entry `(x, y)` of the resolvent along a Hermitian line has derivative
`-(G A G)_{xy}`. -/
private theorem cltres_hasDerivAt_entry {M A : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) (x y : ι) :
    HasDerivAt (fun s : ℝ => green (M + (s : ℂ) • A) z x y)
      (-(green (M + (t : ℂ) • A) z * A * green (M + (t : ℂ) • A) z) x y) t := by
  have h := cltres_hasDerivAt_green hM hA hz t
  have hl := (LinearMap.toContinuousLinearMap
    (Matrix.entryLinearMap ℝ ℂ x y : Matrix ι ι ℂ →ₗ[ℝ] ℂ)).hasFDerivAt.comp_hasDerivAt t h
  simpa [Function.comp_def] using hl

/-- The statement `CltDerivEntry`. -/
theorem cltDeriv_entry (ι : Type*) [Fintype ι] [DecidableEq ι] : CltDerivEntry ι := by
  intro M A a₀ b₀ z t hM hA hz x y
  refine ⟨cltres_hasDerivAt_entry hM hA.1 hz t x y, fun g hg => ?_⟩
  set Gt := green (M + (t : ℂ) • A) z with hGt
  have hg0 : 0 ≤ g := (norm_nonneg _).trans (hg x y)
  have hS := cltres_PAQ_le hA Gt Gt x y
  constructor
  · set mx := max ‖Gt x a₀‖ ‖Gt x b₀‖ with hmx
    have hmx0 : 0 ≤ mx := (norm_nonneg _).trans (le_max_left _ _)
    have h1 : ‖Gt x a₀‖ * ‖Gt b₀ y‖ ≤ mx * g :=
      mul_le_mul (le_max_left _ _) (hg _ _) (norm_nonneg _) hmx0
    have h2 : ‖Gt x b₀‖ * ‖Gt a₀ y‖ ≤ mx * g :=
      mul_le_mul (le_max_right _ _) (hg _ _) (norm_nonneg _) hmx0
    calc ‖(Gt * A * Gt) x y‖ ≤ mx * g + mx * g := hS.trans (add_le_add h1 h2)
      _ = 2 * g * mx := by ring
  · set my := max ‖Gt a₀ y‖ ‖Gt b₀ y‖ with hmy
    have hmy0 : 0 ≤ my := (norm_nonneg _).trans (le_max_left _ _)
    have h1 : ‖Gt x a₀‖ * ‖Gt b₀ y‖ ≤ g * my :=
      mul_le_mul (hg _ _) (le_max_right _ _) (norm_nonneg _) hg0
    have h2 : ‖Gt x b₀‖ * ‖Gt a₀ y‖ ≤ g * my :=
      mul_le_mul (hg _ _) (le_max_left _ _) (norm_nonneg _) hg0
    calc ‖(Gt * A * Gt) x y‖ ≤ g * my + g * my := hS.trans (add_le_add h1 h2)
      _ = 2 * g * my := by ring

end Deriv

section EvalDeriv

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The spectral parameter of the `σ`-resolvent in `gEntryOf`. -/
private def cltres_zs (m : ℂ) (E u : ℝ) (σ : Bool) : ℂ :=
  if σ then ztOf m E u else (starRingEnd ℂ) (ztOf m E u)

private theorem cltres_zs_im {m : ℂ} {E u : ℝ} (hz : (ztOf m E u).im ≠ 0) (σ : Bool) :
    (cltres_zs m E u σ).im ≠ 0 := by
  cases σ <;> simpa [cltres_zs] using hz

/-- `gEntryOf` is the entry of `Gres` at the `σ`-parameter. -/
private theorem cltres_gEntry_eq (m : ℂ) (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (σ : Bool)
    (x y : Idx d L W) : gEntryOf d L W m E u M σ x y = green M (cltres_zs m E u σ) x y := by
  simp only [gEntryOf, Gres, green, cltres_zs, Matrix.nonsing_inv_eq_ringInverse]

/-- The statement `CltDerivEvalMultiOf` (first order, `k` labels, at the spectral value `m`). -/
theorem cltDeriv_evalMulti_leOf (d L W k : ℕ) [NeZero L] [NeZero W] : CltDerivEvalMultiOf d L W k := by
  intro K F m E u M A a₀ b₀ t g φ b hM hA hz hg hφ
  have hg0 : 0 ≤ g := (norm_nonneg _).trans (hg true 0 0)
  set Gs : Bool → Matrix (Idx d L W) (Idx d L W) ℂ := fun σ =>
    green (M + (t : ℂ) • A) (cltres_zs m E u σ) with hGs
  let Dm : ∀ (j : Fin (K + 1)) (_ : Fin j → Idx d L W × Idx d L W × Bool), ℂ := fun j q =>
    F.coef b j q * ∑ i : Fin j,
      (∏ k ∈ Finset.univ.erase i,
        gEntryOf d L W m E u (M + (t : ℂ) • A) (q k).2.2 (q k).1 (q k).2.1) •
        (-(Gs (q i).2.2 * A * Gs (q i).2.2) (q i).1 (q i).2.1)
  refine ⟨∑ j : Fin (K + 1), ∑ q : Fin j → Idx d L W × Idx d L W × Bool, Dm j q, ?_, ?_⟩
  · unfold LocalForm.evalOf
    refine HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun q _ => ?_
    have hprod := HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin j)))
      (f := fun (i : Fin j) (s : ℝ) =>
        gEntryOf d L W m E u (M + (s : ℂ) • A) (q i).2.2 (q i).1 (q i).2.1)
      (f' := fun i => -(Gs (q i).2.2 * A * Gs (q i).2.2) (q i).1 (q i).2.1) (x := t)
      (fun i _ => by
        have h := cltres_hasDerivAt_entry hM hA.1 (cltres_zs_im hz (q i).2.2) t (q i).1 (q i).2.1
        refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
        exact cltres_gEntry_eq m E u _ _ _ _)
    exact hprod.const_mul (F.coef b j q)
  · have hterm : ∀ (j : Fin (K + 1)) (q : Fin j → Idx d L W × Idx d L W × Bool),
        ‖Dm j q‖ ≤ 2 * (‖F.coef b j q‖ * (j : ℝ) * g ^ (j : ℕ) * φ) := by
      intro j q
      by_cases hc : F.coef b j q = 0
      · simp [Dm, hc]
      rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | hpos
      · have hE : IsEmpty (Fin (j : ℕ)) := ⟨fun i => by have := i.2; omega⟩
        simp [Dm, h0]
      · have hφ' := hφ j q hc
        have hφ0 : 0 ≤ φ := (norm_nonneg _).trans (hφ' ⟨0, hpos⟩ true).1
        have hpow : g ^ (j : ℕ) = g ^ ((j : ℕ) - 1) * g := by
          rw [← pow_succ]; congr 1; omega
        have hi : ∀ i : Fin j,
            ‖(∏ k ∈ Finset.univ.erase i,
              gEntryOf d L W m E u (M + (t : ℂ) • A) (q k).2.2 (q k).1 (q k).2.1) •
              (-(Gs (q i).2.2 * A * Gs (q i).2.2) (q i).1 (q i).2.1)‖
              ≤ g ^ ((j : ℕ) - 1) * (2 * g * φ) := by
          intro i
          rw [smul_eq_mul, norm_mul, norm_neg]
          have hprod : ‖∏ k ∈ Finset.univ.erase i,
              gEntryOf d L W m E u (M + (t : ℂ) • A) (q k).2.2 (q k).1 (q k).2.1‖
              ≤ g ^ ((j : ℕ) - 1) := by
            rw [norm_prod]
            calc ∏ k ∈ Finset.univ.erase i,
                  ‖gEntryOf d L W m E u (M + (t : ℂ) • A) (q k).2.2 (q k).1 (q k).2.1‖
                ≤ ∏ _k ∈ Finset.univ.erase i, g :=
                  Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun k _ => hg _ _ _
              _ = g ^ ((j : ℕ) - 1) := by
                  rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
                    Finset.card_univ, Fintype.card_fin]
          have hentry : ‖(Gs (q i).2.2 * A * Gs (q i).2.2) (q i).1 (q i).2.1‖ ≤ 2 * g * φ := by
            have h := ((cltDeriv_entry (Idx d L W)) M A a₀ b₀ (cltres_zs m E u (q i).2.2) t hM hA
              (cltres_zs_im hz (q i).2.2) (q i).1 (q i).2.1).2 g
              (fun x' y' => by rw [← cltres_gEntry_eq]; exact hg (q i).2.2 x' y') |>.1
            refine h.trans ?_
            have hm : max ‖Gs (q i).2.2 (q i).1 a₀‖ ‖Gs (q i).2.2 (q i).1 b₀‖ ≤ φ :=
              max_le (by rw [hGs]; simp only; rw [← cltres_gEntry_eq]; exact (hφ' i (q i).2.2).1)
                (by rw [hGs]; simp only; rw [← cltres_gEntry_eq]; exact (hφ' i (q i).2.2).2)
            have := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ 2 * g)
            exact this
          exact mul_le_mul hprod hentry (norm_nonneg _) (by positivity)
        have hsum : ‖∑ i : Fin j,
            (∏ k ∈ Finset.univ.erase i,
              gEntryOf d L W m E u (M + (t : ℂ) • A) (q k).2.2 (q k).1 (q k).2.1) •
              (-(Gs (q i).2.2 * A * Gs (q i).2.2) (q i).1 (q i).2.1)‖
            ≤ (j : ℝ) * (g ^ ((j : ℕ) - 1) * (2 * g * φ)) := by
          refine (norm_sum_le _ _).trans ?_
          refine (Finset.sum_le_sum fun i _ => hi i).trans (le_of_eq ?_)
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        calc ‖Dm j q‖ = ‖F.coef b j q‖ * ‖∑ i : Fin j,
              (∏ k ∈ Finset.univ.erase i,
                gEntryOf d L W m E u (M + (t : ℂ) • A) (q k).2.2 (q k).1 (q k).2.1) •
                (-(Gs (q i).2.2 * A * Gs (q i).2.2) (q i).1 (q i).2.1)‖ := norm_mul _ _
          _ ≤ ‖F.coef b j q‖ * ((j : ℝ) * (g ^ ((j : ℕ) - 1) * (2 * g * φ))) :=
              mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
          _ = 2 * (‖F.coef b j q‖ * (j : ℝ) * g ^ (j : ℕ) * φ) := by
              rw [hpow]; ring
    calc ‖∑ j : Fin (K + 1), ∑ q : Fin j → Idx d L W × Idx d L W × Bool, Dm j q‖
        ≤ ∑ j : Fin (K + 1), ∑ q : Fin j → Idx d L W × Idx d L W × Bool, ‖Dm j q‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
      _ ≤ ∑ j : Fin (K + 1), ∑ q : Fin j → Idx d L W × Idx d L W × Bool,
            2 * (‖F.coef b j q‖ * (j : ℝ) * g ^ (j : ℕ) * φ) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun q _ => hterm j q
      _ = 2 * ∑ j : Fin (K + 1), ∑ q : Fin j → Idx d L W × Idx d L W × Bool,
            ‖F.coef b j q‖ * (j : ℝ) * g ^ (j : ℕ) * φ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]

end EvalDeriv

/-! ## 4. The lower bound on `Im z_u` and the deterministic bound of the local form -/

section EtaEval

private theorem cltres_ck_le_im {κ E : ℝ} (hE : |E| ≤ 2 - κ) : cltCk κ ≤ (mE E).im := by
  rw [mE_im, cltCk]
  have hE0 : 0 ≤ |E| := abs_nonneg E
  have hsq : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ hE0 hE 2
  have : κ * (4 - κ) ≤ 4 - E ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt this
  linarith

private theorem cltres_ck_pos {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) : 0 < cltCk κ := by
  have h1 : κ ≤ 2 := by have := abs_nonneg E; linarith
  unfold cltCk
  have : 0 < κ * (4 - κ) := mul_pos hκ (by linarith)
  positivity

private theorem cltres_ck_le_one {κ : ℝ} : cltCk κ ≤ 1 := by
  unfold cltCk
  have h : κ * (4 - κ) ≤ 2 ^ 2 := by nlinarith [sq_nonneg (κ - 2)]
  have := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq (by norm_num)] at this
  linarith

/-- The statement `CltEtaLowerOf`: `κ / N ≤ Im z_u` for `N = (W L)^d`, `z_u = ztOf m E u`, from
`κ ≤ Im m`.  Only `N ≥ 1` is used (`N^{-1+δ} ≥ N^{-1}`); the case `N = 0` (`W L = 0`) is the trivial one
`x / 0 = 0`.  No `|E| ≤ 2 - κ`, no `‖m‖ = 1`. -/
theorem cltEta_lowerOf (d L W : ℕ) : CltEtaLowerOf d L W := by
  intro κ δ m E u hκ hδ hκm hR
  rw [ztOf_im]
  unfold etaOf
  have hmim : 0 < m.im := lt_of_lt_of_le hκ hκm
  have h1u : 0 ≤ 1 - u := (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans hR
  rcases Nat.eq_zero_or_pos ((W * L) ^ d) with h0 | hpos
  · rw [h0, Nat.cast_zero, div_zero]; exact mul_nonneg h1u hmim.le
  · have hN1 : (1 : ℝ) ≤ (((W * L) ^ d : ℕ) : ℝ) := by exact_mod_cast hpos
    have h1 := Real.rpow_le_rpow_of_exponent_le hN1 (show (-1 : ℝ) ≤ -1 + δ by linarith)
    rw [Real.rpow_neg_one] at h1
    rw [div_eq_mul_inv]
    nlinarith [mul_le_mul_of_nonneg_left (h1.trans hR) hκ.le, mul_le_mul_of_nonneg_left hκm h1u]
/-- **The band margin** `c_κ`: for `0 < κ`, `|E| ≤ 2 - κ`, `0 < c_κ ≤ Im m(E)` and `c_κ ≤ 1`: the premises of the generic
`CltEtaLowerOf`, `CltEvalDetLeMultiOf` at `m = mE E`, `κ ↦ cltCk κ`. -/
theorem cltCk_facts {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    0 < cltCk κ ∧ cltCk κ ≤ (mE E).im ∧ cltCk κ ≤ 1 :=
  ⟨cltres_ck_pos hκ hE, cltres_ck_le_im hE, cltres_ck_le_one⟩

variable {d L W k : ℕ} [NeZero L] [NeZero W]

open scoped Matrix.Norms.L2Operator in
private theorem cltres_gEntry_le (m : ℂ) (E s : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (hH : M.IsHermitian) (σ : Bool) (x y : Idx d L W) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |(ztOf m E s).im|) : ‖gEntryOf d L W m E s M σ x y‖ ≤ η⁻¹ :=
  (norm_matrix_entry_le_opNorm (Gres M (ztOf m E s) σ) x y).trans
    (norm_Gsig_le_inv_eta hH hη hz σ)

private theorem cltres_card_idx :
    (Fintype.card (Idx d L W) : ℝ) = ((((W * L) ^ d : ℕ)) : ℝ) := by
  rw [card_Idx]

/-- Private re-proof of the bound of `eval` for any Hermitian matrix, with `k` labels. -/
private theorem cltres_eval_le {K : ℕ} (F : LocalForm d L W k K) (m : ℂ) (E s : ℝ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (hH : M.IsHermitian) {η C : ℝ} (hη : 0 < η)
    (hz : η ≤ |(ztOf m E s).im|) (hC : ∀ b j q, ‖F.coef b j q‖ ≤ C)
    (hΘ : 1 ≤ 2 * (Fintype.card (Idx d L W) : ℝ) ^ 2 * η⁻¹) (b : Fin k → Zd d L) :
    ‖F.evalOf m E s M b‖ ≤ (K + 1) * C * (2 * (Fintype.card (Idx d L W) : ℝ) ^ 2 * η⁻¹) ^ K := by
  set N : ℝ := (Fintype.card (Idx d L W) : ℝ) with hN
  set Θ : ℝ := 2 * N ^ 2 * η⁻¹ with hΘdef
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC b 0 (fun i => i.elim0))
  have hterm : ∀ j : Fin (K + 1), ‖∑ q : Fin j → Idx d L W × Idx d L W × Bool,
      F.coef b j q * ∏ i : Fin j, gEntryOf d L W m E s M (q i).2.2 (q i).1 (q i).2.1‖
      ≤ C * Θ ^ (j : ℕ) := by
    intro j
    calc ‖∑ q : Fin j → Idx d L W × Idx d L W × Bool,
          F.coef b j q * ∏ i : Fin j, gEntryOf d L W m E s M (q i).2.2 (q i).1 (q i).2.1‖
        ≤ ∑ q : Fin j → Idx d L W × Idx d L W × Bool, C * (η⁻¹) ^ (j : ℕ) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
          rw [norm_mul, norm_prod]
          refine mul_le_mul (hC _ _ _) ?_ (Finset.prod_nonneg fun i _ => norm_nonneg _) hC0
          calc ∏ i : Fin j, ‖gEntryOf d L W m E s M (q i).2.2 (q i).1 (q i).2.1‖
              ≤ ∏ _i : Fin j, η⁻¹ :=
                Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ =>
                  cltres_gEntry_le m E s M hH _ _ _ hη hz
            _ = (η⁻¹) ^ (j : ℕ) := by simp
      _ = (Fintype.card (Fin j → Idx d L W × Idx d L W × Bool) : ℝ) * (C * (η⁻¹) ^ (j : ℕ)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = C * Θ ^ (j : ℕ) := by
          have hcard : (Fintype.card (Fin j → Idx d L W × Idx d L W × Bool) : ℝ)
              = (2 * N ^ 2) ^ (j : ℕ) := by
            rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod (Idx d L W) (Idx d L W × Bool),
              Fintype.card_prod (Idx d L W) Bool, Fintype.card_bool]
            push_cast
            rw [hN]; ring
          rw [hcard, hΘdef, mul_pow]; ring
  unfold LocalForm.evalOf
  calc ‖∑ j : Fin (K + 1), ∑ q : Fin j → Idx d L W × Idx d L W × Bool,
        F.coef b j q * ∏ i : Fin j, gEntryOf d L W m E s M (q i).2.2 (q i).1 (q i).2.1‖
      ≤ ∑ j : Fin (K + 1), C * Θ ^ (j : ℕ) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm j)
    _ ≤ ∑ _j : Fin (K + 1), C * Θ ^ K :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hΘ (by have := j.2; omega)) hC0
    _ = (K + 1) * C * Θ ^ K := by simp; ring

/-- The statement `CltEvalDetLeMultiOf` (`k` labels, at the spectral value `m`), in powers of
`N = (W L)^d`: `κ ≤ Im m` and `κ ≤ 1` replace `|E| ≤ 2 - κ` and `cltCk κ ≤ 1` (the step `1 ≤ 2 N² η⁻¹`). -/
theorem cltEval_detMulti_leOf (d L W k : ℕ) [NeZero L] [NeZero W] : CltEvalDetLeMultiOf d L W k := by
  intro κ δ m E u K F C' M b hκ hδ hκm hκ1 hR hcoef hH
  set N : ℝ := ((((W * L) ^ d : ℕ) : ℝ)) with hN
  have hN1 : 1 ≤ N := by
    have : 0 < (W * L) ^ d := pow_pos (Nat.mul_pos (NeZero.pos W) (NeZero.pos L)) d
    rw [hN]; exact_mod_cast this
  have hN0 : 0 < N := by linarith
  set η : ℝ := κ / N with hη
  have hη0 : 0 < η := by positivity
  have hlow : η ≤ (ztOf m E u).im := cltEta_lowerOf d L W κ δ m E u hκ hδ hκm hR
  have him : η ≤ |(ztOf m E u).im| := hlow.trans (le_abs_self _)
  have hΘ : 1 ≤ 2 * (Fintype.card (Idx d L W) : ℝ) ^ 2 * η⁻¹ := by
    rw [cltres_card_idx, ← hN, hη, inv_div]
    have : 1 ≤ N / κ := by rw [le_div_iff₀ hκ]; linarith
    nlinarith [sq_nonneg N]
  have := cltres_eval_le F m E u M hH hη0 him (C := N ^ C') hcoef hΘ b
  rw [cltres_card_idx, ← hN, hη, inv_div] at this
  refine this.trans (le_of_eq ?_)
  congr 2
  ring

end EtaEval

/-! ## 5. The far/near geometry and the adjacency of a coordinate -/

section Geom

variable (d L : ℕ) [NeZero L]

private theorem cltres_zdistInf_neg (x : Zd d L) : zdistInf d L (-x) = zdistInf d L x := by
  simp only [zdistInf, Pi.neg_apply, zdist_neg]

private theorem cltres_zdistInf_zero : zdistInf d L 0 = 0 := by
  simp [zdistInf]

private theorem cltres_zdistInf_add_le (x y : Zd d L) :
    zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y := by
  refine Finset.sup_le fun i _ => ?_
  calc zdist L ((x + y) i) = zdist L (x i + y i) := rfl
    _ ≤ zdist L (x i) + zdist L (y i) := zdist_add_le L _ _
    _ ≤ _ := add_le_add (Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i))
          (Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i))

/-- The statement `CltFarGeomHalf` (the dichotomy, half-separation form). -/
theorem cltFarGeomHalf : CltFarGeomHalf := by
  intro d L _ m b i R a hsep
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, k, hki, h2⟩ := hcon
  have htri := cltres_zdistInf_add_le d L (b i - a) (a - b k)
  rw [show b i - a + (a - b k) = b i - b k by abel] at htri
  have hs : zdistInf d L (b i - a) = zdistInf d L (a - b i) := by
    rw [← neg_sub, cltres_zdistInf_neg]
  rw [hs] at htri
  have h3 := hsep k hki
  have h4 : (zdistInf d L (b i - b k) : ℝ) ≤
      (zdistInf d L (a - b i) : ℝ) + (zdistInf d L (a - b k) : ℝ) := by
    exact_mod_cast htri
  linarith

/-- The statement `CltFarGeomNear` (re-scaled): pure triangle inequality, no hypothesis on
`ρ`, `R`. -/
theorem cltFarGeomNear : CltFarGeomNear := by
  intro d L _ ρ R a a' b x hab ha' hxb
  have t1 := cltres_zdistInf_add_le d L (a - x) (x - b)
  rw [show a - x + (x - b) = a - b by abel] at t1
  have s1 : zdistInf d L (a - x) = zdistInf d L (x - a) := by
    rw [← neg_sub, cltres_zdistInf_neg]
  rw [s1] at t1
  have t2 := cltres_zdistInf_add_le d L (x - a') (a' - a)
  rw [show x - a' + (a' - a) = x - a by abel] at t2
  have t1' : (zdistInf d L (a - b) : ℝ) ≤ (zdistInf d L (x - a) : ℝ) + (zdistInf d L (x - b) : ℝ) := by
    exact_mod_cast t1
  have t2' : (zdistInf d L (x - a) : ℝ) ≤ (zdistInf d L (x - a') : ℝ) + (zdistInf d L (a' - a) : ℝ) := by
    exact_mod_cast t2
  have ha'' : (zdistInf d L (a' - a) : ℝ) ≤ 1 := by exact_mod_cast ha'
  constructor <;> linarith

end Geom

section Adj

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem cltres_single_val (c e : CoordF d L W) :
    ((Pi.single c (1 : ℝ) : CoordF d L W → ℝ) e : ℝ) = if e = c then 1 else 0 := by
  by_cases h : e = c
  · subst h; simp
  · simp [h]

/-- Entries of `coordinateMatrix c`: modulus `≤ 1`, supported on `{(x,y),(y,x)}`. -/
private theorem cltres_coordEntry (c : CoordF d L W) (i j : Idx d L W) :
    ‖coordinateMatrix d L W c i j‖ ≤ 1 ∧
      (coordinateMatrix d L W c i j ≠ 0 →
        (i = c.1 ∧ j = c.2.1) ∨ (i = c.2.1 ∧ j = c.1)) := by
  obtain ⟨x, y, β⟩ := c
  change ‖Xentry d L W (Pi.single (x, y, β) 1) i j‖ ≤ 1 ∧
    (Xentry d L W (Pi.single (x, y, β) 1) i j ≠ 0 → _)
  unfold Xentry
  simp only [cltres_single_val]
  split_ifs <;> simp_all

/-- The statement `CltCoordAdj` (the restriction to `S_ij ≠ 0`). -/
theorem cltCoord_adj : CltCoordAdj := by
  intro d L W g _ _ c
  refine ⟨fun hg => ?_, fun i j h => (cltres_coordEntry c i j).2 h,
    fun i j => (cltres_coordEntry c i j).1⟩
  have hsv : svarF d L W g c.1 c.2.1 ≠ 0 := by
    intro h0
    apply hg
    apply NNReal.eq
    simp only [gvarF, NNReal.coe_zero]
    split_ifs <;> simp [h0] <;> rfl
  have hsbr : sbKernelR d L g ((split d L W c.1).1 - (split d L W c.2.1).1) ≠ 0 := by
    intro h0
    apply hsv
    simp only [svarF, SBR, Matrix.of_apply]
    rw [h0, mul_zero]
  by_contra hcon
  have hx0 : (split d L W c.1).1 - (split d L W c.2.1).1 ≠ 0 := by
    intro h
    apply hcon
    rw [h, cltres_zdistInf_zero]
    exact Nat.zero_le _
  have hD : zdistD d L ((split d L W c.1).1 - (split d L W c.2.1).1) ≠ 1 := by
    intro h
    apply hcon
    exact (zdistInf_le_zdistD d L _).trans h.le
  apply hsbr
  simp only [sbKernelR, hx0, hD, ite_false, add_zero]

end Adj

end RBM.Evol
