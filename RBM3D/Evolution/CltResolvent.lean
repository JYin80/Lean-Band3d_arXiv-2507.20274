/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Evolution.CltSwap
import RBM3D.Gauss.FlowCalculus
import RBM3D.Green.EntryCore

/-!
# Deterministic resolvent bounds for the replacement step (ticket T2144, row S5-18, part 1)

Port of `RBM2D/Evolution/CltResolvent.lean` (977 lines)
and of the vocabulary `LocalForm` (`RBM2D/Induction/Defs.lean:141-175`) and `cltY`
(`RBM2D/Evolution/Case3Defs.lean:63`), all at commit `c9a24cf`, onto the fine model of
`RBM3D/Gauss/FineModel.lean`.  Paper: `paper/tex/3_5_Loop_Hierarchy.tex:2245` (`eq:bound_isolated`,
which cites [DYYY25, (7.39)]); the route is the replacement step of RBM2D `CltStep`, see
`RBM3D/Induction/Step5Pins.lean` (`STCltIsoConcl`).  The labels `clt-gij-bound`, `clt-gij-decay`,
`clt-f-total`, ... and the line numbers `7:513`, ... below are those of the RBM2D paper
(`../RBM2D/paper/tex/7_Evolution_kernel_estimates.tex`), not of this paper.  Dictionary:

* `Z2 L ↦ Zd d L`, `zdist2 ↦ zdistInf d L` (the paper's `|x|_L`, `Defs/Sizes.lean:115`),
  `Idx L W ↦ Idx d L W`, `Coord ↦ CoordF d L W`, `gvar ↦ gvarF d L W g` (the variance parameter
  `g` is explicit), `coordinateMatrix ↦ coordinateMatrix d L W` (`FineModel.lean:384`),
  `spectralZ ↦ zt`, `N = (W L)² ↦ N = (W L)^d = card (Idx d L W)`, the five-point `sbSupport`
  `↦` the support `{0} ∪ {zdistD = 1}` of `sbKernelR` (`Defs/Block.lean:74`; `2 d + 1` points).
* `gEntry E s M σ x y := Gres M (zt E s) σ x y` (`Loop/GLoopFlow.lean:74`), the entry of the
  `σ`-resolvent used by `loopFine`; RBM2D's `gEntry` is `(M - z_σ)⁻¹ x y`, the same function.
* `LocalForm.Local ρ` takes the locality radius `ρ` as a parameter (RBM2D: `ellT L s * W^τ`).
* The label count `k` of `LocalForm` is kept general: RBM2D uses one label (`cltY`, `k = 1`),
  `STcltB`/`STcltX` (`Step5Pins.lean:399`) use two.  Every statement that mentions the labels has
  the one-label form of RBM2D (names as in RBM2D) and the form with `b : Fin k → Zd d L`
  (suffix `Multi`), the former a corollary of the latter.
* **Re-scaled geometry.**  `CltFarGeomNear` has a locality radius `ρ` and a separation `R`
  (RBM2D: `w ≥ 6`, `ρ = ℓ w`, `R = w² ℓ`): `x` within `ρ` of `b`, `a` at distance `≥ R/2` from
  `b` give `|x - a|_∞, |x - a'|_∞ ≥ R/2 - ρ - 1`, for all real `ρ`, `R` (triangle inequality).
  `3 ≤ L` of `CltCoordAdj` is not needed (the support of `sbKernelR` is read directly).

The private helpers `cltres_*` are the helpers of the RBM2D file under the same names.
Everything here is deterministic.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Evol

open Matrix RBM RBM.Gauss

/-! ## 1. The vocabulary -/

section Vocab

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- `G_s(σ)_{xy}` at the matrix `M` on the fine lattice (entries in (`a-local-form`), `3_5`):
the `(x, y)` entry of the `σ`-resolvent `Gres M (zt E s) σ` of `Loop/GLoopFlow.lean:74`
(`G(+) = (M - z_s)⁻¹`, `G(-) = (M - \bar z_s)⁻¹`).  RBM2D `Induction/Defs.lean:141`. -/
def gEntry (E s : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (σ : Bool) (x y : Idx d L W) : ℂ :=
  Gres M (zt E s) σ x y

end Vocab

/-- The deterministic coefficients of the local form (`a-local-form`): a polynomial of degree
`≤ K` in the entries `G_s(σ_i)_{x_i y_i}`; `coef b j q` is the coefficient of the monomial
`∏_{i<j} G_s(q_i.2.2)_{q_i.1, q_i.2.1}`, with `k` labels `b : Fin k → Zd d L`.
RBM2D `Induction/Defs.lean:151` (`LocalForm L W k K`, labels in `Z2 L`). -/
structure LocalForm (d L W k K : ℕ) where
  coef : (Fin k → Zd d L) → (j : Fin (K + 1)) → (Fin j → Idx d L W × Idx d L W × Bool) → ℂ

namespace LocalForm

variable {d L W k K : ℕ} [NeZero L] [NeZero W]

/-- The tensor `𝒜_b` of (`a-local-form`) at the matrix `M`.  RBM2D `Induction/Defs.lean:159`. -/
def eval (F : LocalForm d L W k K) (E s : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (b : Fin k → Zd d L) : ℂ :=
  ∑ j : Fin (K + 1), ∑ q : Fin j → Idx d L W × Idx d L W × Bool,
    F.coef b j q * ∏ i : Fin j, gEntry d L W E s M (q i).2.2 (q i).1 (q i).2.1

/-- The locality condition of (`a-local-form`) with the radius `ρ` as a parameter: a non-zero
coefficient has every entry `(x_i, y_i)` within `ρ` of some label `b_m` (blocks
`[x] = (split d L W x).1`, distance `zdistInf`).  RBM2D `Induction/Defs.lean:166` (`Local τ s`,
`ρ = ellT L s * W^τ`, distance `zdist2`). -/
def Local (F : LocalForm d L W k K) (ρ : ℝ) : Prop :=
  ∀ b j q, F.coef b j q ≠ 0 → ∀ i, ∃ m : Fin k,
    ((zdistInf d L ((split d L W (q i).1).1 - b m) +
        zdistInf d L ((split d L W (q i).2.1).1 - b m) : ℕ) : ℝ) < ρ

end LocalForm

/-- The scalar field `Y_{s,b}` of (`clt-yform`): a local form with one label.
RBM2D `Evolution/Case3Defs.lean:63`. -/
def cltY {d L W K : ℕ} [NeZero L] [NeZero W] (F : LocalForm d L W 1 K) (E s : ℝ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (b : Zd d L) : ℂ :=
  F.eval E s M (fun _ => b)

/-! ## 2. The statements -/

section Det

/-- A one-coordinate direction with support `{(a₀,b₀),(b₀,a₀)}` and entries of modulus `≤ 1`.
`√u • coordinateMatrix d L W c` is one for `0 ≤ u ≤ 1` (by `CltCoordAdj`, `c = (a₀, b₀, β)`). -/
def cltCoordDir {ι : Type*} (A : Matrix ι ι ℂ) (a₀ b₀ : ι) : Prop :=
  A.IsHermitian ∧ (∀ a b, ‖A a b‖ ≤ 1) ∧
    ∀ a b, A a b ≠ 0 → (a = a₀ ∧ b = b₀) ∨ (a = b₀ ∧ b = a₀)

/-- **Pin M1** (`clt-gij-bound`, `7:513` of the RBM2D paper's evolution section, deterministic
part).  If `|G_{xy}| ≤ g` for all entries and `4|t| g ≤ 1`, then `|(G_t)_{xy}| ≤ 2g`, where
`G_t = green (M + tA) z`.  Consumers: `CltPathBound`. -/
def CltPertMaxLe (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (M A : Matrix ι ι ℂ) (a₀ b₀ : ι) (z : ℂ) (t g : ℝ), M.IsHermitian → cltCoordDir A a₀ b₀ →
    z.im ≠ 0 → (∀ x y, ‖green M z x y‖ ≤ g) → 4 * |t| * g ≤ 1 →
    ∀ x y, ‖green (M + (t : ℂ) • A) z x y‖ ≤ 2 * g

/-- **Pin M2** (`clt-gij-decay`).  `G_t - G = -t G A G_t = -t G_t A G` bounded entrywise.
Consumers: `CltPathBound` (far entries along the path). -/
def CltPertSubLe (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (M A : Matrix ι ι ℂ) (a₀ b₀ : ι) (z : ℂ) (t gt : ℝ), M.IsHermitian → cltCoordDir A a₀ b₀ →
    z.im ≠ 0 → (∀ x y, ‖green (M + (t : ℂ) • A) z x y‖ ≤ gt) →
    ∀ x y,
      ‖green (M + (t : ℂ) • A) z x y - green M z x y‖ ≤
          2 * |t| * gt * max ‖green M z x a₀‖ ‖green M z x b₀‖ ∧
        ‖green (M + (t : ℂ) • A) z x y - green M z x y‖ ≤
          2 * |t| * gt * max ‖green M z a₀ y‖ ‖green M z b₀ y‖

/-- **Pin M3** (first-order case of `clt-f-total`; "`∂_{H_ij}(G_s)_{xy} = -(G_s)_{xi}(G_s)_{jy}`").
The derivative of `s ↦ (G_s)_{xy}` along the direction `A`, and its entrywise bounds.  Applied
with `z` and with `conj z` (the two values of `σ` in `gEntry`).  Consumers: `CltDerivEval`.
Merged input: `hasDerivAt_green_moving` (`Gauss/FlowCalculus.lean:374`). -/
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

/-- **Pin M4**, `k` labels (`clt-f-total-bound-1`, first order).  The derivative of the local
form `F.eval E u (M + sA) b` in `s` exists and is bounded by
`2 Σ_{j,q} |coef| · j · g^j · φ`, where `g` bounds all entries of `G_t(±)` and `φ` bounds the
entries `G_t(σ)_{x a₀}`, `G_t(σ)_{x b₀}` for every left index `x` of a monomial with non-zero
coefficient.  Consumers: `CltPathBoundMulti`. -/
def CltDerivEvalMulti (d L W k : ℕ) [NeZero L] [NeZero W] : Prop :=
  ∀ (K : ℕ) (F : LocalForm d L W k K) (E u : ℝ) (M A : Matrix (Idx d L W) (Idx d L W) ℂ)
    (a₀ b₀ : Idx d L W) (t g φ : ℝ) (b : Fin k → Zd d L),
    M.IsHermitian → cltCoordDir A a₀ b₀ → (zt E u).im ≠ 0 →
    (∀ σ x y, ‖gEntry d L W E u (M + (t : ℂ) • A) σ x y‖ ≤ g) →
    (∀ (j : Fin (K + 1)) (q : Fin j → Idx d L W × Idx d L W × Bool),
      F.coef b j q ≠ 0 → ∀ (i : Fin j) (σ : Bool),
        ‖gEntry d L W E u (M + (t : ℂ) • A) σ (q i).1 a₀‖ ≤ φ ∧
          ‖gEntry d L W E u (M + (t : ℂ) • A) σ (q i).1 b₀‖ ≤ φ) →
    ∃ D : ℂ, HasDerivAt (fun s : ℝ => F.eval E u (M + (s : ℂ) • A) b) D t ∧
      ‖D‖ ≤ 2 * ∑ j : Fin (K + 1), ∑ q : Fin j → Idx d L W × Idx d L W × Bool,
        ‖F.coef b j q‖ * (j : ℝ) * g ^ (j : ℕ) * φ

/-- **Pin M4**, one label (RBM2D `CltDerivEval`): `CltDerivEvalMulti` at `k = 1`, `cltY`. -/
def CltDerivEval (d L W : ℕ) [NeZero L] [NeZero W] : Prop :=
  ∀ (K : ℕ) (F : LocalForm d L W 1 K) (E u : ℝ) (M A : Matrix (Idx d L W) (Idx d L W) ℂ)
    (a₀ b₀ : Idx d L W) (t g φ : ℝ) (b : Zd d L),
    M.IsHermitian → cltCoordDir A a₀ b₀ → (zt E u).im ≠ 0 →
    (∀ σ x y, ‖gEntry d L W E u (M + (t : ℂ) • A) σ x y‖ ≤ g) →
    (∀ (j : Fin (K + 1)) (q : Fin j → Idx d L W × Idx d L W × Bool),
      F.coef (fun _ => b) j q ≠ 0 → ∀ (i : Fin j) (σ : Bool),
        ‖gEntry d L W E u (M + (t : ℂ) • A) σ (q i).1 a₀‖ ≤ φ ∧
          ‖gEntry d L W E u (M + (t : ℂ) • A) σ (q i).1 b₀‖ ≤ φ) →
    ∃ D : ℂ, HasDerivAt (fun s : ℝ => cltY F E u (M + (s : ℂ) • A) b) D t ∧
      ‖D‖ ≤ 2 * ∑ j : Fin (K + 1), ∑ q : Fin j → Idx d L W × Idx d L W × Bool,
        ‖F.coef (fun _ => b) j q‖ * (j : ℝ) * g ^ (j : ℕ) * φ

/-- `c_κ = √(κ(4-κ))/2`, the lower bound of `Im m(E)` for `|E| ≤ 2 - κ`. -/
def cltCk (κ : ℝ) : ℝ := Real.sqrt (κ * (4 - κ)) / 2

/-- **Pin E4** (the spectral-parameter lower bound behind `clt-f-total-bound-2`):
`c_κ / N ≤ Im z_u` with `N = (W L)^d` (RBM2D: `(W L)²`).  With `norm_Gsig_le_inv_eta` this gives
`‖G_u(±)‖ ≤ N / c_κ` for every Hermitian matrix.  Consumers: `CltEvalDetLe`, `CltStep`. -/
def CltEtaLower (d L W : ℕ) : Prop :=
  ∀ (κ δ E u : ℝ), 0 < κ → 0 < δ → |E| ≤ 2 - κ →
    ((((W * L) ^ d : ℕ) : ℝ)) ^ (-1 + δ) ≤ 1 - u →
    cltCk κ / (((W * L) ^ d : ℕ) : ℝ) ≤ (zt E u).im

/-- **Pin M5**, `k` labels (`clt-f-total-bound-2`; `clt-ibp-bound2`, `clt-ibp-bound4`), in powers
of `N = (W L)^d`.  For every Hermitian `M`:
`‖F.eval E u M b‖ ≤ (K+1) N^{C'} (2N³/c_κ)^K`.  Consumers: `CltStep` (the factors on the bad
event). -/
def CltEvalDetLeMulti (d L W k : ℕ) [NeZero L] [NeZero W] : Prop :=
  ∀ (κ δ E u : ℝ) (K : ℕ) (F : LocalForm d L W k K) (C' : ℝ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (b : Fin k → Zd d L),
    0 < κ → 0 < δ → |E| ≤ 2 - κ →
    ((((W * L) ^ d : ℕ) : ℝ)) ^ (-1 + δ) ≤ 1 - u →
    (∀ b' j q, ‖F.coef b' j q‖ ≤ ((((W * L) ^ d : ℕ) : ℝ)) ^ C') → M.IsHermitian →
    ‖F.eval E u M b‖ ≤ ((K : ℝ) + 1) * ((((W * L) ^ d : ℕ) : ℝ)) ^ C' *
      (2 * ((((W * L) ^ d : ℕ) : ℝ)) ^ 3 / cltCk κ) ^ K

/-- **Pin M5**, one label (RBM2D `CltEvalDetLe`): `CltEvalDetLeMulti` at `k = 1`, `cltY`. -/
def CltEvalDetLe (d L W : ℕ) [NeZero L] [NeZero W] : Prop :=
  ∀ (κ δ E u : ℝ) (K : ℕ) (F : LocalForm d L W 1 K) (C' : ℝ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (b : Zd d L),
    0 < κ → 0 < δ → |E| ≤ 2 - κ →
    ((((W * L) ^ d : ℕ) : ℝ)) ^ (-1 + δ) ≤ 1 - u →
    (∀ b' j q, ‖F.coef b' j q‖ ≤ ((((W * L) ^ d : ℕ) : ℝ)) ^ C') → M.IsHermitian →
    ‖cltY F E u M b‖ ≤ ((K : ℝ) + 1) * ((((W * L) ^ d : ℕ) : ℝ)) ^ C' *
      (2 * ((((W * L) ^ d : ℕ) : ℝ)) ^ 3 / cltCk κ) ^ K

/-- **Pin G1(a)** (the dichotomy, half-separation form; no condition on `W`).  If
`R ≤ |b_i - b_k|_∞` for all `k ≠ i`, then every block `a` has `R/2 ≤ |a - b_i|_∞` or
`R/2 ≤ |a - b_k|_∞` for all `k ≠ i`.  Consumers: `CltStep` (case split A/B). -/
def CltFarGeomHalf : Prop :=
  ∀ (d L : ℕ) [NeZero L] (m : ℕ) (b : Fin m → Zd d L) (i : Fin m) (R : ℝ) (a : Zd d L),
    (∀ k, k ≠ i → R ≤ (zdistInf d L (b i - b k) : ℝ)) →
    R / 2 ≤ (zdistInf d L (a - b i) : ℝ) ∨ ∀ k, k ≠ i → R / 2 ≤ (zdistInf d L (a - b k) : ℝ)

/-- **Pin G1(b), re-scaled** (RBM2D: `w ≥ 6`, `ℓ ≥ 1`, `R = w²ℓ`, `ρ = ℓ w`, conclusion
`ℓ w ≤ …`).  With a locality radius `ρ` and a separation `R`, both arbitrary reals: if the block
`a` is at distance `≥ R/2` from the label `b`, `a'` is adjacent to `a`, and `|x - b|_∞ < ρ` (a
block of a monomial local to `b`), then `x` is at distance `≥ R/2 - ρ - 1` from `a` and from `a'`.
At `ρ = (log W)^3 ℓ_s`, `R = 10 (log W)^3 ℓ_s` this is `≥ 4 (log W)^3 ℓ_s - 1`, above the far
threshold `c (log W)^3 ℓ_s` of `STFarEntryAtLog`.  Consumers: `CltPathBound`. -/
def CltFarGeomNear : Prop :=
  ∀ (d L : ℕ) [NeZero L] (ρ R : ℝ) (a a' b x : Zd d L),
    R / 2 ≤ (zdistInf d L (a - b) : ℝ) → zdistInf d L (a' - a) ≤ 1 →
    (zdistInf d L (x - b) : ℝ) < ρ →
    R / 2 - ρ - 1 ≤ (zdistInf d L (x - a) : ℝ) ∧ R / 2 - ρ - 1 ≤ (zdistInf d L (x - a') : ℝ)

/-- **Pin G2** (the restriction to `S_ij ≠ 0`).  For a coordinate `c = (x, y, β)`: if
`gvarF c ≠ 0` the blocks of `x` and `y` are adjacent (`|[x] - [y]|_∞ ≤ 1`: the support of
`sbKernelR` is `{0} ∪ {zdistD = 1}`, contained in the `∞`-ball of radius `1`); `coordinateMatrix c`
is supported on `{(x,y),(y,x)}` with entries of modulus `≤ 1`.  No condition on `L` or `g`.
Consumers: `CltStep`, `CltPathBound` (`cltCoordDir` for `√u • coordinateMatrix c`). -/
def CltCoordAdj : Prop :=
  ∀ (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W] (c : CoordF d L W),
    (gvarF d L W g c ≠ 0 →
      zdistInf d L ((split d L W c.1).1 - (split d L W c.2.1).1) ≤ 1) ∧
    (∀ i j, coordinateMatrix d L W c i j ≠ 0 → (i = c.1 ∧ j = c.2.1) ∨ (i = c.2.1 ∧ j = c.1)) ∧
    (∀ i j, ‖coordinateMatrix d L W c i j‖ ≤ 1)

end Det

/-! ## 3. Perturbation of `G` in one direction (M1, M2, M3) -/

section Perturb

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- A real multiple of a Hermitian matrix added to a Hermitian matrix is Hermitian. -/
private theorem cltres_herm_add {M A : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (hA : A.IsHermitian) (s : ℝ) : (M + (s : ℂ) • A).IsHermitian := by
  refine hM.add ?_
  change Matrix.conjTranspose ((s : ℂ) • A) = (s : ℂ) • A
  rw [Matrix.conjTranspose_smul, hA, Complex.star_def, Complex.conj_ofReal]

/-- `(R1)`: `G - G_t = t G A G_t` for `G = green M z`, `G_t = green (M + tA) z`. -/
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

/-- `(R2)`: `G_t - G = -t G_t A G`. -/
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
/-- The support fact (S): `|(P A Q)_{xy}| ≤ |P_{x a₀}||Q_{b₀ y}| + |P_{x b₀}||Q_{a₀ y}|`. -/
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

/-- **M1** (`clt-gij-bound`, deterministic part), the pin `CltPertMaxLe`. -/
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

/-- **M2** (`clt-gij-decay`), the pin `CltPertSubLe`. -/
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
is the `L²` operator norm of `RBM.Gauss.hasDerivAt_green_moving`, `Gauss/FlowCalculus.lean:374`,
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

/-- **M3** (first-order case of `clt-f-total`), the pin `CltDerivEntry`. -/
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

/-- The spectral parameter of the `σ`-resolvent in `gEntry`. -/
private def cltres_zs (E u : ℝ) (σ : Bool) : ℂ :=
  if σ then zt E u else (starRingEnd ℂ) (zt E u)

private theorem cltres_zs_im {E u : ℝ} (hz : (zt E u).im ≠ 0) (σ : Bool) :
    (cltres_zs E u σ).im ≠ 0 := by
  cases σ <;> simpa [cltres_zs] using hz

/-- `gEntry` is the entry of `green` at the `σ`-parameter. -/
private theorem cltres_gEntry_eq (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (σ : Bool)
    (x y : Idx d L W) : gEntry d L W E u M σ x y = green M (cltres_zs E u σ) x y := by
  simp only [gEntry, Gres, green, cltres_zs, Matrix.nonsing_inv_eq_ringInverse]

/-- **M4**, `k` labels (`clt-f-total-bound-1`, first order), the pin `CltDerivEvalMulti`. -/
theorem cltDeriv_evalMulti_le (d L W k : ℕ) [NeZero L] [NeZero W] : CltDerivEvalMulti d L W k := by
  intro K F E u M A a₀ b₀ t g φ b hM hA hz hg hφ
  have hg0 : 0 ≤ g := (norm_nonneg _).trans (hg true 0 0)
  set Gs : Bool → Matrix (Idx d L W) (Idx d L W) ℂ := fun σ =>
    green (M + (t : ℂ) • A) (cltres_zs E u σ) with hGs
  let Dm : ∀ (j : Fin (K + 1)) (_ : Fin j → Idx d L W × Idx d L W × Bool), ℂ := fun j q =>
    F.coef b j q * ∑ i : Fin j,
      (∏ k ∈ Finset.univ.erase i,
        gEntry d L W E u (M + (t : ℂ) • A) (q k).2.2 (q k).1 (q k).2.1) •
        (-(Gs (q i).2.2 * A * Gs (q i).2.2) (q i).1 (q i).2.1)
  refine ⟨∑ j : Fin (K + 1), ∑ q : Fin j → Idx d L W × Idx d L W × Bool, Dm j q, ?_, ?_⟩
  · unfold LocalForm.eval
    refine HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun q _ => ?_
    have hprod := HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin j)))
      (f := fun (i : Fin j) (s : ℝ) =>
        gEntry d L W E u (M + (s : ℂ) • A) (q i).2.2 (q i).1 (q i).2.1)
      (f' := fun i => -(Gs (q i).2.2 * A * Gs (q i).2.2) (q i).1 (q i).2.1) (x := t)
      (fun i _ => by
        have h := cltres_hasDerivAt_entry hM hA.1 (cltres_zs_im hz (q i).2.2) t (q i).1 (q i).2.1
        refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
        exact cltres_gEntry_eq E u _ _ _ _)
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
              gEntry d L W E u (M + (t : ℂ) • A) (q k).2.2 (q k).1 (q k).2.1) •
              (-(Gs (q i).2.2 * A * Gs (q i).2.2) (q i).1 (q i).2.1)‖
              ≤ g ^ ((j : ℕ) - 1) * (2 * g * φ) := by
          intro i
          rw [smul_eq_mul, norm_mul, norm_neg]
          have hprod : ‖∏ k ∈ Finset.univ.erase i,
              gEntry d L W E u (M + (t : ℂ) • A) (q k).2.2 (q k).1 (q k).2.1‖
              ≤ g ^ ((j : ℕ) - 1) := by
            rw [norm_prod]
            calc ∏ k ∈ Finset.univ.erase i,
                  ‖gEntry d L W E u (M + (t : ℂ) • A) (q k).2.2 (q k).1 (q k).2.1‖
                ≤ ∏ _k ∈ Finset.univ.erase i, g :=
                  Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun k _ => hg _ _ _
              _ = g ^ ((j : ℕ) - 1) := by
                  rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
                    Finset.card_univ, Fintype.card_fin]
          have hentry : ‖(Gs (q i).2.2 * A * Gs (q i).2.2) (q i).1 (q i).2.1‖ ≤ 2 * g * φ := by
            have h := ((cltDeriv_entry (Idx d L W)) M A a₀ b₀ (cltres_zs E u (q i).2.2) t hM hA
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
              gEntry d L W E u (M + (t : ℂ) • A) (q k).2.2 (q k).1 (q k).2.1) •
              (-(Gs (q i).2.2 * A * Gs (q i).2.2) (q i).1 (q i).2.1)‖
            ≤ (j : ℝ) * (g ^ ((j : ℕ) - 1) * (2 * g * φ)) := by
          refine (norm_sum_le _ _).trans ?_
          refine (Finset.sum_le_sum fun i _ => hi i).trans (le_of_eq ?_)
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        calc ‖Dm j q‖ = ‖F.coef b j q‖ * ‖∑ i : Fin j,
              (∏ k ∈ Finset.univ.erase i,
                gEntry d L W E u (M + (t : ℂ) • A) (q k).2.2 (q k).1 (q k).2.1) •
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

/-- **M4**, one label (`clt-f-total-bound-1`, first order), the pin `CltDerivEval`: the case
`k = 1` of `cltDeriv_evalMulti_le`. -/
theorem cltDeriv_eval_le (d L W : ℕ) [NeZero L] [NeZero W] : CltDerivEval d L W :=
  fun K F E u M A a₀ b₀ t g φ b =>
    cltDeriv_evalMulti_le d L W 1 K F E u M A a₀ b₀ t g φ (fun _ => b)

end EvalDeriv

/-! ## 4. The lower bound on `Im z_u` and the deterministic bound of the local form (E4, M5) -/

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

/-- **E4** (the spectral-parameter lower bound behind `clt-f-total-bound-2`), the pin
`CltEtaLower`: `c_κ / N ≤ Im z_u` for `N = (W L)^d`.  Only `N ≥ 1` is used (`N^{-1+δ} ≥ N^{-1}`);
the case `N = 0` (`W L = 0`) is the trivial one `x / 0 = 0`. -/
theorem cltEta_lower (d L W : ℕ) : CltEtaLower d L W := by
  intro κ δ E u hκ hδ hE hR
  set N : ℝ := ((((W * L) ^ d : ℕ) : ℝ)) with hN
  have hRe : cltCk κ ≤ (mE E).im := cltres_ck_le_im hE
  have hck : 0 < cltCk κ := cltres_ck_pos hκ hE
  rw [zt_im]
  rcases Nat.eq_zero_or_pos ((W * L) ^ d) with h0 | hpos
  · have hN0 : N = 0 := by rw [hN, h0]; simp
    have h1u : 0 ≤ 1 - u := by
      have := Real.rpow_nonneg (le_refl (0 : ℝ)) (-1 + δ)
      rw [hN0] at hR
      linarith
    rw [hN0, div_zero]
    exact mul_nonneg h1u (hck.le.trans hRe)
  · have hN1 : 1 ≤ N := by
      rw [hN]; exact_mod_cast hpos
    have hN0 : 0 < N := by linarith
    have h1 : N⁻¹ ≤ 1 - u := by
      have h2 : N ^ (-1 : ℝ) ≤ N ^ (-1 + δ) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      rw [Real.rpow_neg_one] at h2
      linarith
    calc cltCk κ / N = N⁻¹ * cltCk κ := by ring
      _ ≤ (1 - u) * (mE E).im := mul_le_mul h1 hRe hck.le (by have := inv_pos.2 hN0; linarith)

variable {d L W k : ℕ} [NeZero L] [NeZero W]

open scoped Matrix.Norms.L2Operator in
private theorem cltres_gEntry_le (E s : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (hH : M.IsHermitian) (σ : Bool) (x y : Idx d L W) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |(zt E s).im|) : ‖gEntry d L W E s M σ x y‖ ≤ η⁻¹ :=
  (norm_matrix_entry_le_opNorm (Gres M (zt E s) σ) x y).trans
    (norm_Gsig_le_inv_eta hH hη hz σ)

private theorem cltres_card_idx :
    (Fintype.card (Idx d L W) : ℝ) = ((((W * L) ^ d : ℕ)) : ℝ) := by
  rw [card_Idx]

/-- Private re-proof of the bound of `cltY` for any Hermitian matrix, with `k` labels. -/
private theorem cltres_eval_le {K : ℕ} (F : LocalForm d L W k K) (E s : ℝ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (hH : M.IsHermitian) {η C : ℝ} (hη : 0 < η)
    (hz : η ≤ |(zt E s).im|) (hC : ∀ b j q, ‖F.coef b j q‖ ≤ C)
    (hΘ : 1 ≤ 2 * (Fintype.card (Idx d L W) : ℝ) ^ 2 * η⁻¹) (b : Fin k → Zd d L) :
    ‖F.eval E s M b‖ ≤ (K + 1) * C * (2 * (Fintype.card (Idx d L W) : ℝ) ^ 2 * η⁻¹) ^ K := by
  set N : ℝ := (Fintype.card (Idx d L W) : ℝ) with hN
  set Θ : ℝ := 2 * N ^ 2 * η⁻¹ with hΘdef
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC b 0 (fun i => i.elim0))
  have hterm : ∀ j : Fin (K + 1), ‖∑ q : Fin j → Idx d L W × Idx d L W × Bool,
      F.coef b j q * ∏ i : Fin j, gEntry d L W E s M (q i).2.2 (q i).1 (q i).2.1‖
      ≤ C * Θ ^ (j : ℕ) := by
    intro j
    calc ‖∑ q : Fin j → Idx d L W × Idx d L W × Bool,
          F.coef b j q * ∏ i : Fin j, gEntry d L W E s M (q i).2.2 (q i).1 (q i).2.1‖
        ≤ ∑ q : Fin j → Idx d L W × Idx d L W × Bool, C * (η⁻¹) ^ (j : ℕ) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
          rw [norm_mul, norm_prod]
          refine mul_le_mul (hC _ _ _) ?_ (Finset.prod_nonneg fun i _ => norm_nonneg _) hC0
          calc ∏ i : Fin j, ‖gEntry d L W E s M (q i).2.2 (q i).1 (q i).2.1‖
              ≤ ∏ _i : Fin j, η⁻¹ :=
                Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ =>
                  cltres_gEntry_le E s M hH _ _ _ hη hz
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
  unfold LocalForm.eval
  calc ‖∑ j : Fin (K + 1), ∑ q : Fin j → Idx d L W × Idx d L W × Bool,
        F.coef b j q * ∏ i : Fin j, gEntry d L W E s M (q i).2.2 (q i).1 (q i).2.1‖
      ≤ ∑ j : Fin (K + 1), C * Θ ^ (j : ℕ) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm j)
    _ ≤ ∑ _j : Fin (K + 1), C * Θ ^ K :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hΘ (by have := j.2; omega)) hC0
    _ = (K + 1) * C * Θ ^ K := by simp; ring

/-- **M5**, `k` labels (`clt-f-total-bound-2`), the pin `CltEvalDetLeMulti`, in powers of
`N = (W L)^d`. -/
theorem cltEval_detMulti_le (d L W k : ℕ) [NeZero L] [NeZero W] : CltEvalDetLeMulti d L W k := by
  intro κ δ E u K F C' M b hκ hδ hE hR hcoef hH
  set N : ℝ := ((((W * L) ^ d : ℕ) : ℝ)) with hN
  have hN1 : 1 ≤ N := by
    have : 0 < (W * L) ^ d := pow_pos (Nat.mul_pos (NeZero.pos W) (NeZero.pos L)) d
    rw [hN]; exact_mod_cast this
  have hN0 : 0 < N := by linarith
  have hck := cltres_ck_pos hκ hE
  have hck1 : cltCk κ ≤ 1 := cltres_ck_le_one
  set η : ℝ := cltCk κ / N with hη
  have hη0 : 0 < η := by positivity
  have hlow : η ≤ (zt E u).im := cltEta_lower d L W κ δ E u hκ hδ hE hR
  have him : η ≤ |(zt E u).im| := hlow.trans (le_abs_self _)
  have hΘ : 1 ≤ 2 * (Fintype.card (Idx d L W) : ℝ) ^ 2 * η⁻¹ := by
    rw [cltres_card_idx, ← hN, hη, inv_div]
    have : 1 ≤ N / cltCk κ := by rw [le_div_iff₀ hck]; linarith
    nlinarith [sq_nonneg N]
  have := cltres_eval_le F E u M hH hη0 him (C := N ^ C') hcoef hΘ b
  rw [cltres_card_idx, ← hN, hη, inv_div] at this
  refine this.trans (le_of_eq ?_)
  congr 2
  ring

/-- **M5**, one label (`clt-f-total-bound-2`), the pin `CltEvalDetLe`: the case `k = 1` of
`cltEval_detMulti_le`. -/
theorem cltEval_det_le (d L W : ℕ) [NeZero L] [NeZero W] : CltEvalDetLe d L W :=
  fun κ δ E u K F C' M b =>
    cltEval_detMulti_le d L W 1 κ δ E u K F C' M (fun _ => b)

end EtaEval

/-! ## 5. The far/near geometry and the adjacency of a coordinate (G1, G2) -/

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

/-- **G1(a)** (the dichotomy, half-separation form), the pin `CltFarGeomHalf`. -/
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

/-- **G1(b)**, re-scaled, the pin `CltFarGeomNear`: pure triangle inequality, no hypothesis on
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

/-- **G2** (the restriction to `S_ij ≠ 0`), the pin `CltCoordAdj`. -/
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


/-! ## 6. Compiled instances: every endpoint at `d = 3`, `L = 3`, `W = 1`, `g = 1/2`

`N = (W L)^d = 27`, `M = 0`, `E = 0`, `u = 1/2` (`z_u = i/2`, `Im z_u = 1/2`), `t = 1/8`,
`κ = 1`, `δ = 1/2`.  The directions are the `2 · 27² = 1458` coordinates `c = (x, y, β)` of
`CoordF 3 3 1` (`27²` oriented pairs, two real parts); the instance below takes one with
`gvarF c ≠ 0`, `c.1 ≠ c.2.1` and `coordinateMatrix c c.1 c.2.1 = 1`.  The geometry is checked
on `Z_7^3` and `Z_61^3`.  No hypothesis is left open. -/

section Checks

private theorem cltres_chk_z_im : (zt 0 (1 / 2)).im = 1 / 2 := by
  rw [zt_im, mE_im, show (4 : ℝ) - 0 ^ 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

private theorem cltres_chk_z_ne : (zt 0 (1 / 2)).im ≠ 0 := by
  rw [cltres_chk_z_im]; norm_num

/-- Every `coordinateMatrix c` is a `cltCoordDir` (`CltCoordAdj`, last two conjuncts). -/
private theorem cltres_chk_dir (c : CoordF 3 3 1) :
    cltCoordDir (coordinateMatrix 3 3 1 c) c.1 c.2.1 :=
  ⟨coordinateMatrix_isHermitian 3 3 1 c, (cltCoord_adj 3 3 1 (1 / 2) c).2.2,
    (cltCoord_adj 3 3 1 (1 / 2) c).2.1⟩

/-- Every entry of the resolvent at `z = zt 0 (1/2)` (`Im z = 1/2`) of a Hermitian matrix is
at most `2`. -/
private theorem cltres_chk_g (M : Matrix (Idx 3 3 1) (Idx 3 3 1) ℂ) (hM : M.IsHermitian)
    (σ : Bool) (x y : Idx 3 3 1) : ‖gEntry 3 3 1 0 (1 / 2) M σ x y‖ ≤ 2 := by
  have h := cltres_gEntry_le (d := 3) (L := 3) (W := 1) 0 (1 / 2) M hM σ x y (η := 1 / 2)
    (by norm_num) (by rw [cltres_chk_z_im, abs_of_pos (by norm_num)])
  rw [show ((1 / 2 : ℝ))⁻¹ = 2 by norm_num] at h
  exact h

private theorem cltres_chk_gr (M : Matrix (Idx 3 3 1) (Idx 3 3 1) ℂ) (hM : M.IsHermitian)
    (x y : Idx 3 3 1) : ‖green M (zt 0 (1 / 2)) x y‖ ≤ 2 := by
  have h := cltres_chk_g M hM true x y
  rw [cltres_gEntry_eq] at h
  exact h

private theorem cltres_chk_herm (c : CoordF 3 3 1) :
    (0 + (((1 / 8 : ℝ)) : ℂ) • coordinateMatrix 3 3 1 c).IsHermitian :=
  cltres_herm_add Matrix.isHermitian_zero (coordinateMatrix_isHermitian 3 3 1 c) _

/-- The entry `(a, b)` of `coordinateMatrix (a, b, true)` is `1` when `idxKey a < idxKey b`. -/
private theorem cltres_chk_entry {d L W : ℕ} [NeZero L] [NeZero W] (a b : Idx d L W)
    (h : idxKey d L W a < idxKey d L W b) : coordinateMatrix d L W (a, b, true) a b = 1 := by
  change Xentry d L W (Pi.single (a, b, true) 1) a b = 1
  simp [Xentry, h]

private theorem cltres_chk_gvar (a b : Idx 3 3 1) (hab : a ≠ b)
    (hc : sbKernelR 3 3 (1 / 2) ((split 3 3 1 a).1 - (split 3 3 1 b).1) ≠ 0) :
    gvarF 3 3 1 (1 / 2) (a, b, true) ≠ 0 := by
  intro h0
  have h1 : ((gvarF 3 3 1 (1 / 2) (a, b, true) : NNReal) : ℝ) = 0 := by
    rw [h0]; exact NNReal.coe_zero
  have hs : svarF 3 3 1 (1 / 2) a b ≠ 0 := by
    simp only [svarF, SBR, Matrix.of_apply]
    exact mul_ne_zero (by positivity) hc
  have hg : ((gvarF 3 3 1 (1 / 2) (a, b, true) : NNReal) : ℝ) = svarF 3 3 1 (1 / 2) a b / 2 := by
    change (if a = b then svarF 3 3 1 (1 / 2) a b else svarF 3 3 1 (1 / 2) a b / 2 : ℝ) = _
    rw [ite_eq_right_iff.mpr (fun h => absurd h hab)]
  rw [hg] at h1
  exact hs (by linarith)

/-- A coordinate with `gvarF ≠ 0`, `x ≠ y` (blocks `0` and `e₀`), entry `(x,y) = 1`. -/
private theorem cltres_chk_offdiag :
    ∃ c : CoordF 3 3 1, gvarF 3 3 1 (1 / 2) c ≠ 0 ∧ c.1 ≠ c.2.1 ∧
      coordinateMatrix 3 3 1 c c.1 c.2.1 = 1 := by
  set a : Idx 3 3 1 := 0 with ha
  set b : Idx 3 3 1 := Pi.single 0 1 with hb
  have hab : a ≠ b := by decide
  have hz1 : zdistD 3 3 ((split 3 3 1 a).1 - (split 3 3 1 b).1) = 1 := by decide
  have hz2 : zdistD 3 3 ((split 3 3 1 b).1 - (split 3 3 1 a).1) = 1 := by decide
  have hx1 : (split 3 3 1 a).1 - (split 3 3 1 b).1 ≠ 0 := by decide
  have hx2 : (split 3 3 1 b).1 - (split 3 3 1 a).1 ≠ 0 := by decide
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ 2 * (1 + 2 * ((3 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ 2)⁻¹ := by
    positivity
  have hc1 : sbKernelR 3 3 (1 / 2) ((split 3 3 1 a).1 - (split 3 3 1 b).1) ≠ 0 := by
    simp only [sbKernelR, hx1, hz1, ite_false, ite_true, zero_add]
    exact hpos.ne'
  have hc2 : sbKernelR 3 3 (1 / 2) ((split 3 3 1 b).1 - (split 3 3 1 a).1) ≠ 0 := by
    simp only [sbKernelR, hx2, hz2, ite_false, ite_true, zero_add]
    exact hpos.ne'
  rcases idxKey_lt_or_eq_or_lt 3 3 1 a b with h | h | h
  · exact ⟨(a, b, true), cltres_chk_gvar a b hab hc1, hab, cltres_chk_entry _ _ h⟩
  · exact absurd h hab
  · exact ⟨(b, a, true), cltres_chk_gvar b a hab.symm hc2, hab.symm, cltres_chk_entry _ _ h⟩

/-- M1 at `M = 0`, `t = 1/8`, `g = 2` (`4|t|g = 1`): `|(G_t)_{xy}| ≤ 4`. -/
private theorem cltres_chk_M1 (c : CoordF 3 3 1) (x y : Idx 3 3 1) :
    ‖green (0 + (((1 / 8 : ℝ)) : ℂ) • coordinateMatrix 3 3 1 c) (zt 0 (1 / 2)) x y‖ ≤ 2 * 2 :=
  cltPert_max_le (Idx 3 3 1) 0 (coordinateMatrix 3 3 1 c) c.1 c.2.1 (zt 0 (1 / 2)) (1 / 8) 2
    Matrix.isHermitian_zero (cltres_chk_dir c) cltres_chk_z_ne
    (fun x y => cltres_chk_gr 0 Matrix.isHermitian_zero x y) (by norm_num) x y

/-- M2 at the same data with `g_t = 2 * 2`. -/
private theorem cltres_chk_M2 (c : CoordF 3 3 1) (x y : Idx 3 3 1) :
    ‖green (0 + (((1 / 8 : ℝ)) : ℂ) • coordinateMatrix 3 3 1 c) (zt 0 (1 / 2)) x y -
        green 0 (zt 0 (1 / 2)) x y‖ ≤
      2 * |(1 / 8 : ℝ)| * (2 * 2) *
        max ‖green 0 (zt 0 (1 / 2)) x c.1‖ ‖green 0 (zt 0 (1 / 2)) x c.2.1‖ ∧
    ‖green (0 + (((1 / 8 : ℝ)) : ℂ) • coordinateMatrix 3 3 1 c) (zt 0 (1 / 2)) x y -
        green 0 (zt 0 (1 / 2)) x y‖ ≤
      2 * |(1 / 8 : ℝ)| * (2 * 2) *
        max ‖green 0 (zt 0 (1 / 2)) c.1 y‖ ‖green 0 (zt 0 (1 / 2)) c.2.1 y‖ :=
  cltPert_sub_le (Idx 3 3 1) 0 (coordinateMatrix 3 3 1 c) c.1 c.2.1 (zt 0 (1 / 2)) (1 / 8)
    (2 * 2) Matrix.isHermitian_zero (cltres_chk_dir c) cltres_chk_z_ne
    (fun x y => cltres_chk_M1 c x y) x y

/-- The resolvent at `M = 0 + (1/8) A`, `z = zt 0 (1/2)`. -/
private noncomputable abbrev cltres_chkG (c : CoordF 3 3 1) : Matrix (Idx 3 3 1) (Idx 3 3 1) ℂ :=
  green (0 + (((1 / 8 : ℝ)) : ℂ) • coordinateMatrix 3 3 1 c) (zt 0 (1 / 2))

/-- M3 at `M = 0`, `t = 1/8`: the derivative of the entry, and its bound with `g = 2 * 2`. -/
private theorem cltres_chk_M3 (c : CoordF 3 3 1) (x y : Idx 3 3 1) :
    HasDerivAt (fun s : ℝ => green (0 + (s : ℂ) • coordinateMatrix 3 3 1 c) (zt 0 (1 / 2)) x y)
      (-(cltres_chkG c * coordinateMatrix 3 3 1 c * cltres_chkG c) x y) (1 / 8) ∧
    ‖(cltres_chkG c * coordinateMatrix 3 3 1 c * cltres_chkG c) x y‖ ≤
      2 * (2 * 2) * max ‖cltres_chkG c x c.1‖ ‖cltres_chkG c x c.2.1‖ := by
  have h := cltDeriv_entry (Idx 3 3 1) 0 (coordinateMatrix 3 3 1 c) c.1 c.2.1 (zt 0 (1 / 2))
    (1 / 8) Matrix.isHermitian_zero (cltres_chk_dir c) cltres_chk_z_ne x y
  exact ⟨h.1, (h.2 (2 * 2) (fun x' y' => cltres_chk_M1 c x' y')).1⟩

/-- The one-monomial form `G_{a₀ b₀}` (`K = 1`) with `k` labels, supported on the label `b₂`. -/
private def cltres_chkForm (k : ℕ) (b₂ : Fin k → Zd 3 3) (a₀ b₀ : Idx 3 3 1) :
    LocalForm 3 3 1 k 1 where
  coef := fun b' j q =>
    if h : (j : ℕ) = 1 then
      (if b' = b₂ ∧ q ⟨0, by omega⟩ = (a₀, b₀, true) then 1 else 0) else 0

private theorem cltres_chkForm_ne (k : ℕ) (b₂ : Fin k → Zd 3 3) (a₀ b₀ : Idx 3 3 1) :
    (cltres_chkForm k b₂ a₀ b₀).coef b₂ 1 (fun _ => (a₀, b₀, true)) = 1 := by
  simp [cltres_chkForm]

private theorem cltres_chkForm_le (k : ℕ) (b₂ : Fin k → Zd 3 3) (a₀ b₀ : Idx 3 3 1)
    (b' : Fin k → Zd 3 3) (j : Fin (1 + 1)) (q : Fin j → Idx 3 3 1 × Idx 3 3 1 × Bool) :
    ‖(cltres_chkForm k b₂ a₀ b₀).coef b' j q‖ ≤ ((((1 * 3) ^ 3 : ℕ) : ℝ)) ^ (0 : ℝ) := by
  simp only [cltres_chkForm, Real.rpow_zero]
  split_ifs <;> simp

/-- M4, one label, at `K = 1`, `g = φ = 2`, label `b = 0`. -/
private theorem cltres_chk_M4 (c : CoordF 3 3 1) (b : Zd 3 3) :
    ∃ D : ℂ, HasDerivAt (fun s : ℝ => cltY (cltres_chkForm 1 (fun _ => b) c.1 c.2.1) 0 (1 / 2)
        (0 + (s : ℂ) • coordinateMatrix 3 3 1 c) b) D (1 / 8) ∧
      ‖D‖ ≤ 2 * ∑ j : Fin (1 + 1), ∑ q : Fin j → Idx 3 3 1 × Idx 3 3 1 × Bool,
        ‖(cltres_chkForm 1 (fun _ => b) c.1 c.2.1).coef (fun _ => b) j q‖ * (j : ℝ) *
          2 ^ (j : ℕ) * 2 :=
  cltDeriv_eval_le 3 3 1 1 (cltres_chkForm 1 (fun _ => b) c.1 c.2.1) 0 (1 / 2) 0
    (coordinateMatrix 3 3 1 c) c.1 c.2.1 (1 / 8) 2 2 b Matrix.isHermitian_zero (cltres_chk_dir c)
    cltres_chk_z_ne (fun σ x y => cltres_chk_g _ (cltres_chk_herm c) σ x y)
    (fun _ _ _ _ σ => ⟨cltres_chk_g _ (cltres_chk_herm c) σ _ _,
      cltres_chk_g _ (cltres_chk_herm c) σ _ _⟩)

/-- M4 with two labels (the shape of `STcltB`), at the labels `b₂ = (0, e₀)`. -/
private theorem cltres_chk_M4Multi (c : CoordF 3 3 1) (b₂ : Fin 2 → Zd 3 3) :
    ∃ D : ℂ, HasDerivAt (fun s : ℝ => (cltres_chkForm 2 b₂ c.1 c.2.1).eval 0 (1 / 2)
        (0 + (s : ℂ) • coordinateMatrix 3 3 1 c) b₂) D (1 / 8) ∧
      ‖D‖ ≤ 2 * ∑ j : Fin (1 + 1), ∑ q : Fin j → Idx 3 3 1 × Idx 3 3 1 × Bool,
        ‖(cltres_chkForm 2 b₂ c.1 c.2.1).coef b₂ j q‖ * (j : ℝ) * 2 ^ (j : ℕ) * 2 :=
  cltDeriv_evalMulti_le 3 3 1 2 1 (cltres_chkForm 2 b₂ c.1 c.2.1) 0 (1 / 2) 0
    (coordinateMatrix 3 3 1 c) c.1 c.2.1 (1 / 8) 2 2 b₂ Matrix.isHermitian_zero (cltres_chk_dir c)
    cltres_chk_z_ne (fun σ x y => cltres_chk_g _ (cltres_chk_herm c) σ x y)
    (fun _ _ _ _ σ => ⟨cltres_chk_g _ (cltres_chk_herm c) σ _ _,
      cltres_chk_g _ (cltres_chk_herm c) σ _ _⟩)

private theorem cltres_chk_R :
    ((((1 * 3) ^ 3 : ℕ) : ℝ)) ^ (-1 + 1 / 2 : ℝ) ≤ 1 - 1 / 2 := by
  have h27 : ((((1 * 3) ^ 3 : ℕ) : ℝ)) = 27 := by norm_num
  rw [h27, show (-1 + 1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg (by positivity),
    ← Real.sqrt_eq_rpow]
  have h2 : (2 : ℝ) ≤ Real.sqrt 27 := Real.le_sqrt_of_sq_le (by norm_num)
  calc (Real.sqrt 27)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) h2
    _ = 1 - 1 / 2 := by norm_num

/-- E4 at `d = 3`, `L = 3`, `W = 1`, `κ = 1`, `δ = 1/2`, `E = 0`, `u = 1/2`. -/
private theorem cltres_chk_E4 :
    cltCk 1 / ((((1 * 3) ^ 3 : ℕ) : ℝ)) ≤ (zt 0 (1 / 2)).im :=
  cltEta_lower 3 3 1 1 (1 / 2) 0 (1 / 2) one_pos (by norm_num) (by norm_num) cltres_chk_R

/-- M5, one label, at the same parameters, `K = 1`, `C' = 0`, `M = 0`. -/
private theorem cltres_chk_M5 (a₀ b₀ : Idx 3 3 1) (b : Zd 3 3) :
    ‖cltY (cltres_chkForm 1 (fun _ => b) a₀ b₀) 0 (1 / 2)
        (0 : Matrix (Idx 3 3 1) (Idx 3 3 1) ℂ) b‖ ≤
      (((1 : ℕ) : ℝ) + 1) * ((((1 * 3) ^ 3 : ℕ) : ℝ)) ^ (0 : ℝ) *
        (2 * ((((1 * 3) ^ 3 : ℕ) : ℝ)) ^ 3 / cltCk 1) ^ 1 :=
  cltEval_det_le 3 3 1 1 (1 / 2) 0 (1 / 2) 1 (cltres_chkForm 1 (fun _ => b) a₀ b₀) 0 0 b one_pos
    (by norm_num) (by norm_num) cltres_chk_R
    (fun b' j q => cltres_chkForm_le 1 (fun _ => b) a₀ b₀ b' j q) Matrix.isHermitian_zero

/-- M5 with two labels. -/
private theorem cltres_chk_M5Multi (a₀ b₀ : Idx 3 3 1) (b₂ : Fin 2 → Zd 3 3) :
    ‖(cltres_chkForm 2 b₂ a₀ b₀).eval 0 (1 / 2) (0 : Matrix (Idx 3 3 1) (Idx 3 3 1) ℂ) b₂‖ ≤
      (((1 : ℕ) : ℝ) + 1) * ((((1 * 3) ^ 3 : ℕ) : ℝ)) ^ (0 : ℝ) *
        (2 * ((((1 * 3) ^ 3 : ℕ) : ℝ)) ^ 3 / cltCk 1) ^ 1 :=
  cltEval_detMulti_le 3 3 1 2 1 (1 / 2) 0 (1 / 2) 1 (cltres_chkForm 2 b₂ a₀ b₀) 0 0 b₂ one_pos
    (by norm_num) (by norm_num) cltres_chk_R
    (fun b' j q => cltres_chkForm_le 2 b₂ a₀ b₀ b' j q) Matrix.isHermitian_zero

/-- G1(a) at `d = 3`, `L = 7`, `m = 2`, `b = (e₀·0, e₀·3)`, `i = 0`, `R = 3`, `a = e₀`: the first
disjunct is false and the second holds. -/
private theorem cltres_chk_half :
    ¬ ((3 : ℝ) / 2 ≤ (zdistInf 3 7 ((![1, 0, 0] : Zd 3 7) -
        (![![0, 0, 0], ![3, 0, 0]] : Fin 2 → Zd 3 7) 0) : ℝ)) ∧
      ∀ k : Fin 2, k ≠ 0 →
        (3 : ℝ) / 2 ≤ (zdistInf 3 7 ((![1, 0, 0] : Zd 3 7) -
          (![![0, 0, 0], ![3, 0, 0]] : Fin 2 → Zd 3 7) k) : ℝ) := by
  have h1 : zdistInf 3 7 ((![1, 0, 0] : Zd 3 7) -
      (![![0, 0, 0], ![3, 0, 0]] : Fin 2 → Zd 3 7) 0) = 1 := by decide
  have h2 : zdistInf 3 7 ((![1, 0, 0] : Zd 3 7) -
      (![![0, 0, 0], ![3, 0, 0]] : Fin 2 → Zd 3 7) 1) = 2 := by decide
  have h3 : zdistInf 3 7 ((![![0, 0, 0], ![3, 0, 0]] : Fin 2 → Zd 3 7) 0 -
      (![![0, 0, 0], ![3, 0, 0]] : Fin 2 → Zd 3 7) 1) = 3 := by decide
  have hsep : ∀ k : Fin 2, k ≠ 0 →
      (3 : ℝ) ≤ (zdistInf 3 7 ((![![0, 0, 0], ![3, 0, 0]] : Fin 2 → Zd 3 7) 0 -
        (![![0, 0, 0], ![3, 0, 0]] : Fin 2 → Zd 3 7) k) : ℝ) := by
    intro k hk
    have hk1 : k = 1 := by omega
    subst hk1
    rw [h3]; norm_num
  have hres := cltFarGeomHalf 3 7 2 (![![0, 0, 0], ![3, 0, 0]] : Fin 2 → Zd 3 7) 0 3 ![1, 0, 0] hsep
  refine ⟨?_, ?_⟩
  · rw [h1]; norm_num
  · exact hres.resolve_left (by rw [h1]; norm_num)

/-- G1(b), re-scaled, at `d = 3`, `L = 61`, `ρ = 1`, `R = 16`, `b = 0`, `a = (10,0,0)`,
`a' = (11,0,0)`, `x = 0`: all hypotheses hold and the conclusion is `6 ≤ |x - a|, |x - a'|`. -/
private theorem cltres_chk_near :
    (16 : ℝ) / 2 - 1 - 1 ≤ (zdistInf 3 61 ((![0, 0, 0] : Zd 3 61) - ![10, 0, 0]) : ℝ) ∧
      (16 : ℝ) / 2 - 1 - 1 ≤ (zdistInf 3 61 ((![0, 0, 0] : Zd 3 61) - ![11, 0, 0]) : ℝ) := by
  have h1 : zdistInf 3 61 ((![10, 0, 0] : Zd 3 61) - ![0, 0, 0]) = 10 := by decide
  have h2 : zdistInf 3 61 ((![11, 0, 0] : Zd 3 61) - ![10, 0, 0]) = 1 := by decide
  have h3 : zdistInf 3 61 ((![0, 0, 0] : Zd 3 61) - ![0, 0, 0]) = 0 := by decide
  exact cltFarGeomNear 3 61 1 16 ![10, 0, 0] ![11, 0, 0] ![0, 0, 0] ![0, 0, 0]
    (by rw [h1]; norm_num) (by rw [h2]) (by rw [h3]; norm_num)

/-- G2 at `d = 3`, `L = 3`, `W = 1`, `g = 1/2`: a direction with `gvarF ≠ 0`, blocks adjacent,
entry `1`. -/
private theorem cltres_chk_adj :
    ∃ c : CoordF 3 3 1, gvarF 3 3 1 (1 / 2) c ≠ 0 ∧
      zdistInf 3 3 ((split 3 3 1 c.1).1 - (split 3 3 1 c.2.1).1) ≤ 1 ∧
      coordinateMatrix 3 3 1 c c.1 c.2.1 = 1 := by
  obtain ⟨c, hg, -, h1⟩ := cltres_chk_offdiag
  exact ⟨c, hg, (cltCoord_adj 3 3 1 (1 / 2) c).1 hg, h1⟩

/-- One nondegenerate direction at which the instances M1, M3, M4 hold at once: `gvarF c ≠ 0`,
`c.1 ≠ c.2.1`, `A_{c.1 c.2.1} = 1`, the entry bound of M1, the derivative of the entry
`(c.1, c.2.1)` of `G_t` (M3) and the derivative bound of the local form `G_{c.1 c.2.1}` (M4). -/
private theorem cltres_chk_witness :
    ∃ c : CoordF 3 3 1, gvarF 3 3 1 (1 / 2) c ≠ 0 ∧ c.1 ≠ c.2.1 ∧
      coordinateMatrix 3 3 1 c c.1 c.2.1 = 1 ∧
      (∀ x y, ‖green (0 + (((1 / 8 : ℝ)) : ℂ) • coordinateMatrix 3 3 1 c) (zt 0 (1 / 2)) x y‖ ≤
        2 * 2) ∧
      HasDerivAt (fun s : ℝ => green (0 + (s : ℂ) • coordinateMatrix 3 3 1 c) (zt 0 (1 / 2))
          c.1 c.2.1)
        (-(cltres_chkG c * coordinateMatrix 3 3 1 c * cltres_chkG c) c.1 c.2.1) (1 / 8) ∧
      ∃ D : ℂ, HasDerivAt (fun s : ℝ => cltY (cltres_chkForm 1 (fun _ => (0 : Zd 3 3)) c.1 c.2.1)
          0 (1 / 2) (0 + (s : ℂ) • coordinateMatrix 3 3 1 c) 0) D (1 / 8) ∧
        ‖D‖ ≤ 2 * ∑ j : Fin (1 + 1), ∑ q : Fin j → Idx 3 3 1 × Idx 3 3 1 × Bool,
          ‖(cltres_chkForm 1 (fun _ => (0 : Zd 3 3)) c.1 c.2.1).coef (fun _ => 0) j q‖ * (j : ℝ) *
            2 ^ (j : ℕ) * 2 := by
  obtain ⟨c, hg, hne, h1⟩ := cltres_chk_offdiag
  exact ⟨c, hg, hne, h1, fun x y => cltres_chk_M1 c x y, (cltres_chk_M3 c c.1 c.2.1).1,
    cltres_chk_M4 c 0⟩

end Checks

/-! ## Axioms of the declarations of this file -/

#print axioms cltPert_max_le
#print axioms cltPert_sub_le
#print axioms cltDeriv_entry
#print axioms cltDeriv_eval_le
#print axioms cltDeriv_evalMulti_le
#print axioms cltEta_lower
#print axioms cltEval_det_le
#print axioms cltEval_detMulti_le
#print axioms cltFarGeomHalf
#print axioms cltFarGeomNear
#print axioms cltCoord_adj
#print axioms cltres_chk_witness
#print axioms cltres_chk_near
#print axioms cltres_chk_half

end RBM.Evol
