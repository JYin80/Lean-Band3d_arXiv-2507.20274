/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.TwistGrid
import RBM3D.Path.Kernel

/-!
# The twisted loop hierarchy at the path level: the grid decomposition and the grid martingale statements

Paper: the Duhamel identity (8.28) (`eq:Duhamel_twist`) for the twisted loops of (8.4) (`eq:TL2_BA`) at the block Anderson model.  Everything here lives on
`PathΩ`: the grid walk of `baStep2Mat sz lam0 E` (`Pp = pathP (sz.withLam 0)`, `Hpath = g₀ Ψ +
pathH`), with the matrix-level objects of `BA/TwistGrid` evaluated at `(u_k, H_k)`.

* The path vocabulary: `twAk` (`A_k(a) = Z_{u_k}(H_k)(a)`, a vector in `a`), `twMartInc`
  (`ξ_{j+1}`), `twDriftk`, `twEEk`, `twEEUk` (the drift, the QV and the
  `Ũ`-weighted QV at the grid state), and the canonical `twMart`, `twRem`.

* The decomposition clause `baTwistGrid_decomp` (pathwise, every `ω`), `baTwistGrid_decomp_ae`
  (the shape of the first conjunct of `BATwistGridRem`): `A_k = A_0 + Δ Σ_{j<k} Drift_j + Rem_k
  + Mart_k` with the canonical `twMart`, `twRem`.

* The six statements `BATwistGridMartAt`,
  `BATwistGridMart`, `BATwistGridRem`, `BATwistGridTail`, `BATwistGridWTail`,
  `BATwistGridAssemble`.  The three parts are `BATwistGridRem` (clauses (i)-(ii)),
  `BATwistGridTail` (iii), `BATwistGridWTail` (iv); they are proved in `BA/TwistGridRem`,
  `BA/TwistGridTail`, `BA/TwistGridWTail`.  `baTwistGridAssemble_holds` proves `BATwistGridAssemble` (the analogue of
  `stGridMartAt_of_parts2`, `Path/DifREP1`).

Every statement is for every `d` (no `3 ≤ d`).  Every helper is `private`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter
open scoped Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

section Path
variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

/-- `A_k(a) = Z_{u_k}(H_k)(a) = L̃_{u_k}(H_k)(a) - K̃_{u_k}(a)`, `H_k = Hpath k ω`; a vector in `a`, so that `Ũ` acts by `*ᵥ`. -/
def twAk (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) : Zd d (sz.L n) → ℂ := fun a =>
  twL2M sz lam0 E n (gridTime s t K n k) ((baStep2Mat sz lam0 E).Hpath s t K n k ω) σ a c₁ c₂ - twK (baFM sz lam0 E) n (gridTime s t K n k) σ a c₁ c₂
/-- `ξ_{j+1} = A_{j+1} - 𝔼[A_{j+1} | F_j]`. -/
def twMartInc (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) (j : ℕ) (ω : PathΩ sz) : Zd d (sz.L n) → ℂ := fun a =>
  twAk sz lam0 E s t K n σ c₁ c₂ (j + 1) ω a - ((baStep2Mat sz lam0 E).Pp)[fun ω' => twAk sz lam0 E s t K n σ c₁ c₂ (j + 1) ω' a | filt (sz.withLam 0) j] ω
/-- The drift, the QV and the `Ũ`-weighted QV at the grid state `(u_k, H_k)`. -/
def twDriftk (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) : ℂ :=
  twDriftM sz lam0 E n (gridTime s t K n k) ((baStep2Mat sz lam0 E).Hpath s t K n k ω) σ a c₁ c₂
def twEEk (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) : ℂ :=
  twEEM sz lam0 E n (gridTime s t K n k) ((baStep2Mat sz lam0 E).Hpath s t K n k ω) σ a a c₁ c₂
def twEEUk (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) (j k : ℕ) (ω : PathΩ sz) : ℂ :=
  twEEUM sz lam0 E n (gridTime s t K n j) (gridTime s t K n k) ((baStep2Mat sz lam0 E).Hpath s t K n j ω) σ a c₁ c₂

/-- The canonical `Mart_k = Σ_{j<k} ξ_{j+1}` and `Rem_k = Σ_{j<k} (𝔼[A_{j+1}|F_j] - A_j - Δ Drift_j)` (the analogues of `difRepMartN`, `difRepRemN` of `Path/DifREP1`). -/
def twMart (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) : ℂ :=
  ∑ j ∈ Finset.range k, twMartInc sz lam0 E s t K n σ c₁ c₂ j ω a
def twRem (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) : ℂ :=
  ∑ j ∈ Finset.range k, (((baStep2Mat sz lam0 E).Pp)[fun ω' => twAk sz lam0 E s t K n σ c₁ c₂ (j + 1) ω' a | filt (sz.withLam 0) j] ω -
    twAk sz lam0 E s t K n σ c₁ c₂ j ω a - ((gridStep s t K n : ℝ) : ℂ) * twDriftk sz lam0 E s t K n σ a c₁ c₂ j ω)

end Path

/-- The decomposition clause, pathwise: with the canonical `Mart_k = Σ_{j<k} ξ_{j+1}` and
`Rem_k = Σ_{j<k} (𝔼[A_{j+1}|F_j] - A_j - Δ Drift_j)`, `A_k = A_0 + Δ Σ_{j<k} Drift_j + Rem_k + Mart_k` (the conditional expectation
cancels; no measurability, no hypothesis on the data). -/
theorem baTwistGrid_decomp {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) :
    twAk sz lam0 E s t K n σ c₁ c₂ k ω a = twAk sz lam0 E s t K n σ c₁ c₂ 0 ω a +
      ((gridStep s t K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k, twDriftk sz lam0 E s t K n σ a c₁ c₂ j ω +
      twRem sz lam0 E s t K n σ a c₁ c₂ k ω + twMart sz lam0 E s t K n σ a c₁ c₂ k ω := by
  induction k with
  | zero => simp [twRem, twMart]
  | succ k ih =>
      simp only [twRem, twMart, twMartInc, Finset.sum_range_succ, mul_add] at ih ⊢
      linear_combination ih

/-- The decomposition clause in the shape of the first conjunct of `BATwistGridRem`: for every grid, size index and label,
almost surely in the grid walk, for all `k ≤ K n` (it holds at every `ω`: `baTwistGrid_decomp`). -/
theorem baTwistGrid_decomp_ae {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (i : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) :
    ∀ᵐ ω ∂((baStep2Mat sz lam0 E).Pp), ∀ k, k ≤ K n →
      twAk sz lam0 E s t K n i.1 i.2.2.1 i.2.2.2 k ω i.2.1 =
        twAk sz lam0 E s t K n i.1 i.2.2.1 i.2.2.2 0 ω i.2.1 + ((gridStep s t K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k,
          twDriftk sz lam0 E s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 j ω +
        twRem sz lam0 E s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 k ω + twMart sz lam0 E s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 k ω :=
  Filter.Eventually.of_forall fun ω k _ => baTwistGrid_decomp sz lam0 E s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 k ω

/-! ## The grid martingale statement `BATwistGridMartAt` and its three parts (statements; the parts are proved in `BA/TwistGridRem`, `BA/TwistGridTail`, `BA/TwistGridWTail`) -/

/-- `BATwistGridMartAt` (the shape of `STGridMartAtgL`, `Chain/Step2Gen`, with the fourth clause of `STGridRepNAtgL`): (i) the decomposition with the drift `twDriftk`,
(ii) `‖Rem‖ ≤ N^{C₀} √Δ`, (iii) the martingale tail with the QV `(Ẽ⊗Ẽ)(a,a)`, (iv) the `Ũ`-weighted tail with `((Ũ⊗Ũ)∘(Ẽ⊗Ẽ))(a,a)`. -/
def BATwistGridMartAt (d : ℕ) (C₀ : ℝ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
        ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) →
          ∃ Mart Rem : ∀ n, ((Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) → ℕ → PathΩ sz → ℂ,
            (∀ n (i : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)), ∀ᵐ ω ∂((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Pp), ∀ k, k ≤ K n →
              twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.2.1 i.2.2.2 k ω i.2.1 =
                twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.2.1 i.2.2.2 0 ω i.2.1 +
                  ((gridStep s t K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k,
                    twDriftk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 j ω +
                  Rem n i k ω + Mart n i k ω) ∧
            (∀ᶠ n in atTop, ∀ (i : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)), ∀ᵐ ω ∂((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Pp), ∀ k, k ≤ K n →
              ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s t K n)) ∧
            (∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ (i : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)),
              ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Pp) {ω | ∃ k, k ≤ K n ∧
                ((sz.size n : ℕ) : ℝ) ^ ε' * (∑ j ∈ Finset.range k, gridStep s t K n *
                  ‖twEEk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 j ω‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) <
                  ‖Mart n i k ω‖} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))) ∧
            (∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ (i : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)),
              ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Pp) {ω | ∃ k, k ≤ K n ∧
                ((sz.size n : ℕ) : ℝ) ^ ε' * (∑ j ∈ Finset.range k, gridStep s t K n *
                  ‖twEEUk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 j k ω‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) <
                  ‖(∑ j ∈ Finset.range k, twU sz (BAflowLam0 sz z) (BAflowEs sz z) n i.1 (gridTime s t K n j) (gridTime s t K n k) *ᵥ
                    (fun b => Mart n (i.1, b, i.2.2.1, i.2.2.2) (j + 1) ω - Mart n (i.1, b, i.2.2.1, i.2.2.2) j ω)) i.2.1‖} ≤
                ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)))

/-- `∃ C₀ ≥ 0` in front, as `STGridMartgL` (`Chain/Step2Gen`). -/
def BATwistGridMart (d : ℕ) : Prop := ∃ C₀ : ℝ, 0 ≤ C₀ ∧ BATwistGridMartAt d C₀

/-! ### The split of `BATwistGridMartAt` as `GridRepRemNAt`, `GridRepTailNAt`, `GridRepWTailNAt` (`Path/DifREP1`): clauses (i)-(ii) with the canonical `Mart`, `Rem`; (iii); (iv). -/

def BATwistGridRem (d : ℕ) (C₀ : ℝ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∃ CK : ℝ, 0 ≤ CK ∧
      ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) →
        (∀ n (i : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)), ∀ᵐ ω ∂((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Pp), ∀ k, k ≤ K n →
          twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.2.1 i.2.2.2 k ω i.2.1 =
            twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.2.1 i.2.2.2 0 ω i.2.1 + ((gridStep s t K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k,
              twDriftk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 j ω +
            twRem sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 k ω + twMart sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 k ω) ∧
        (∀ᶠ n in atTop, ∀ (i : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)), ∀ᵐ ω ∂((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Pp), ∀ k, k ≤ K n →
          ‖twRem sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s t K n))

def BATwistGridTail (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
      ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) → ∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ (i : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)),
        ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Pp) {ω | ∃ k, k ≤ K n ∧
          ((sz.size n : ℕ) : ℝ) ^ ε' * (∑ j ∈ Finset.range k, gridStep s t K n *
            ‖twEEk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 j ω‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) <
          ‖twMart sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 k ω‖} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

def BATwistGridWTail (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
      ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) → ∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ (i : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)),
        ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Pp) {ω | ∃ k, k ≤ K n ∧
          ((sz.size n : ℕ) : ℝ) ^ ε' * (∑ j ∈ Finset.range k, gridStep s t K n *
            ‖twEEUk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 j k ω‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) <
          ‖(∑ j ∈ Finset.range k, twU sz (BAflowLam0 sz z) (BAflowEs sz z) n i.1 (gridTime s t K n j) (gridTime s t K n k) *ᵥ
            (fun b => twMart sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 b i.2.2.1 i.2.2.2 (j + 1) ω -
              twMart sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 b i.2.2.1 i.2.2.2 j ω)) i.2.1‖} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

/-- The assembly of the three parts into `BATwistGridMartAt` (the analogue of `stGridMartAt_of_parts2`, `Path/DifREP1`: `CK := max`, `∃ Mart Rem := twMart, twRem`, `N^{CK} ≤ K` by monotonicity). -/
def BATwistGridAssemble : Prop :=
  ∀ (d : ℕ) (C₀ : ℝ), 0 ≤ C₀ → BATwistGridRem d C₀ → BATwistGridTail d → BATwistGridWTail d → BATwistGridMartAt d C₀

/-- `BATwistGridAssemble` (the analogue of `stGridMartAt_of_parts2`, `Path/DifREP1`): the three parts give `BATwistGridMartAt` with `Mart := twMart`, `Rem := twRem`,
`CK := max` of the three constants, and `N^{CK_i} ≤ N^{CK}` (`N ≥ 1`). -/
theorem baTwistGridAssemble_holds : BATwistGridAssemble := by
  intro d C₀ hC₀ hRem hTail hWTail κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT D hD
  obtain ⟨CKr, hCKr, hr⟩ := hRem κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT
  obtain ⟨CKt, hCKt, ht⟩ := hTail κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT D hD
  obtain ⟨CKw, hCKw, hw⟩ := hWTail κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT D hD
  refine ⟨max CKr (max CKt CKw), le_max_of_le_left hCKr, fun K hK0 hKN => ?_⟩
  have hmono : ∀ C : ℝ, C ≤ max CKr (max CKt CKw) → ∀ n : ℕ,
      ((sz.size n : ℕ) : ℝ) ^ (max CKr (max CKt CKw)) ≤ K n → ((sz.size n : ℕ) : ℝ) ^ C ≤ K n :=
    fun C hC n hn => (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast sz.one_le_size n) hC).trans hn
  have hKr : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CKr ≤ K n := hKN.mono fun n hn => hmono _ (le_max_left _ _) n hn
  have hKt : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CKt ≤ K n :=
    hKN.mono fun n hn => hmono _ ((le_max_left _ _).trans (le_max_right _ _)) n hn
  have hKw : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CKw ≤ K n :=
    hKN.mono fun n hn => hmono _ ((le_max_right _ _).trans (le_max_right _ _)) n hn
  obtain ⟨hid, hrem⟩ := hr K hK0 hKr
  exact ⟨fun n i k ω => twMart sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 k ω,
    fun n i k ω => twRem sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 k ω, hid, hrem,
    fun ε' hε' => ht K hK0 hKt ε' hε', fun ε' hε' => hw K hK0 hKw ε' hε'⟩

end RBM.BA
