/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.TwistGrid
import RBM3D.Path.Kernel

/-!
# BA stage TL, row TL2a (T2428), path level: the grid Duhamel identity and the grid martingale pins

Ticket `docs/tickets/T2428.md` with Amend 1 (`docs/tickets/T2428-amend-1.md`); probe
`RBM3D/Probe/T2428Pins.lean` at `f6c3866` (branch `t/T2428`, never merged); proofs
`docs/tickets/T2398-TL-proofs.md` T.9, (D.5); paper arXiv:2507.20274.  Everything here lives on
`PathΩ`: the grid walk of `baStep2Mat sz lam0 E` (`Pp = pathP (sz.withLam 0)`, `Hpath = g₀ Ψ +
pathH`), with the matrix-level objects of `RBM3D/BA/TwistGrid.lean` evaluated at `(u_k, H_k)`.

* **The path vocabulary**: `twAk` (`A_k(a) = Z_{u_k}(H_k)(a)`, a vector in `a`), `twMartInc`
  (`ξ_{j+1}`), `twPredInc` (`P_j`), `twDriftk`, `twEEk`, `twEEUk` (the drift, the QV and the
  `Ũ`-weighted QV at the grid state), and the canonical `twMart`, `twRem`.

* **4 (a)** `BATwistDuhamel`, `BATwistDuhamel_holds` (twin of `StoppedDuhamelN`,
  `Induction/GridDuhamelN.lean:293`): pathwise, `A_{j∧τ} = Ũ_{u₀,u_{j∧τ}} A₀ + Σ_{i<j∧τ}
  Ũ_{u_{i+1},u_{j∧τ}} (P_i + ξ_{i+1})`, from the semigroup law `BAuKer_self`, `BAuKer_comp` and
  the abstract telescope `duhamel_telescope` (`Path/Kernel.lean`); `TwistGrid2_twAk_step` and
  `TwistGrid2_twAk_duhamel` are the one-size-index forms.

* **Clause (i) of 4 (b)** `baTwistGrid_decomp` (pathwise, every `ω`), `baTwistGrid_decomp_ae`
  (the shape of the first conjunct of `BATwistGridRem`): `A_k = A_0 + Δ Σ_{j<k} Drift_j + Rem_k
  + Mart_k` with the canonical `twMart`, `twRem`.

* **The six pins**, verbatim from the probe at `f6c3866`: `BATwistGridMartAt`,
  `BATwistGridMart`, `BATwistGridRem`, `BATwistGridTail`, `BATwistGridWTail`,
  `BATwistGridAssemble`.  The three parts are `BATwistGridRem` (clauses (i)-(ii)),
  `BATwistGridTail` (iii), `BATwistGridWTail` (iv); their proofs are the successor rows TL2a2,
  TL2a3, TL2a4 (not here).  `baTwistGridAssemble_holds` proves `BATwistGridAssemble` (twin of
  `stGridMartAt_of_parts2`, `Path/DifREP1.lean:1276`).

Every statement is for every `d` (no `3 ≤ d`).  Every other helper is `private` or prefixed
`TwistGrid2_`.
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
/-- `P_j = 𝔼[A_{j+1} | F_j] - Ũ_{u_j,u_{j+1}} A_j`. -/
def twPredInc (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) (j : ℕ) (ω : PathΩ sz) : Zd d (sz.L n) → ℂ := fun a =>
  ((baStep2Mat sz lam0 E).Pp)[fun ω' => twAk sz lam0 E s t K n σ c₁ c₂ (j + 1) ω' a | filt (sz.withLam 0) j] ω -
    (twU sz lam0 E n σ (gridTime s t K n j) (gridTime s t K n (j + 1)) *ᵥ twAk sz lam0 E s t K n σ c₁ c₂ j ω) a
/-- The drift (target 3), the QV (target 1) and the `Ũ`-weighted QV at the grid state `(u_k, H_k)`. -/
def twDriftk (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) : ℂ :=
  twDriftM sz lam0 E n (gridTime s t K n k) ((baStep2Mat sz lam0 E).Hpath s t K n k ω) σ a c₁ c₂
def twEEk (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) : ℂ :=
  twEEM sz lam0 E n (gridTime s t K n k) ((baStep2Mat sz lam0 E).Hpath s t K n k ω) σ a a c₁ c₂
def twEEUk (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) (j k : ℕ) (ω : PathΩ sz) : ℂ :=
  twEEUM sz lam0 E n (gridTime s t K n j) (gridTime s t K n k) ((baStep2Mat sz lam0 E).Hpath s t K n j ω) σ a c₁ c₂

/-- The canonical `Mart_k = Σ_{j<k} ξ_{j+1}` and `Rem_k = Σ_{j<k} (𝔼[A_{j+1}|F_j] - A_j - Δ Drift_j)` (twins of `difRepMartN` `:58`, `difRepRemN` `:64` of `Path/DifREP1.lean`). -/
def twMart (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) : ℂ :=
  ∑ j ∈ Finset.range k, twMartInc sz lam0 E s t K n σ c₁ c₂ j ω a
def twRem (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) : ℂ :=
  ∑ j ∈ Finset.range k, (((baStep2Mat sz lam0 E).Pp)[fun ω' => twAk sz lam0 E s t K n σ c₁ c₂ (j + 1) ω' a | filt (sz.withLam 0) j] ω -
    twAk sz lam0 E s t K n σ c₁ c₂ j ω a - ((gridStep s t K n : ℝ) : ℂ) * twDriftk sz lam0 E s t K n σ a c₁ c₂ j ω)

end Path

section Duhamel
variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

/-- The one-step identity `A_{j+1} - Ũ_{u_j,u_{j+1}} A_j = P_j + ξ_{j+1}` (the conditional expectation cancels). -/
theorem TwistGrid2_twAk_step (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) (j : ℕ) (ω : PathΩ sz) :
    twAk sz lam0 E s t K n σ c₁ c₂ (j + 1) ω - twU sz lam0 E n σ (gridTime s t K n j) (gridTime s t K n (j + 1)) *ᵥ twAk sz lam0 E s t K n σ c₁ c₂ j ω =
      twPredInc sz lam0 E s t K n σ c₁ c₂ j ω + twMartInc sz lam0 E s t K n σ c₁ c₂ j ω := by
  funext a
  simp only [Pi.sub_apply, Pi.add_apply, twPredInc, twMartInc]
  ring

/-- **The stopped grid Duhamel identity, at one size index** (twin of `stoppedDuhamelN_at`, `Induction/GridDuhamelN.lean:310`), pathwise:
`A_m = Ũ_{u₀,u_m} A₀ + Σ_{i<m} Ũ_{u_{i+1},u_m} (P_i + ξ_{i+1})` for `m ≤ K n`, from the semigroup law of `BAuKer`. -/
theorem TwistGrid2_twAk_duhamel {κ : ℝ} (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n))
    (hu0 : ∀ k, k ≤ K n → 0 ≤ gridTime s t K n k) (hu1 : ∀ k, k ≤ K n → gridTime s t K n k < 1)
    (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) {m : ℕ} (hm : m ≤ K n) (ω : PathΩ sz) :
    twAk sz lam0 E s t K n σ c₁ c₂ m ω =
      twU sz lam0 E n σ (gridTime s t K n 0) (gridTime s t K n m) *ᵥ twAk sz lam0 E s t K n σ c₁ c₂ 0 ω +
        ∑ i ∈ Finset.range m, twU sz lam0 E n σ (gridTime s t K n (i + 1)) (gridTime s t K n m) *ᵥ
          (twPredInc sz lam0 E s t K n σ c₁ c₂ i ω + twMartInc sz lam0 E s t K n σ c₁ c₂ i ω) := by
  set uc : ℕ → ℝ := fun i => gridTime s t K n (min i m) with huc
  have hc0 : ∀ i, 0 ≤ uc i := fun i => hu0 _ ((min_le_right i m).trans hm)
  have hc1 : ∀ i, uc i < 1 := fun i => hu1 _ ((min_le_right i m).trans hm)
  let U : ℕ → ℕ → (Zd d (sz.L n) → ℂ) →+ (Zd d (sz.L n) → ℂ) := fun i j =>
    AddMonoidHom.mk' (fun x => twU sz lam0 E n σ (uc i) (uc j) *ᵥ x) (fun x y => Matrix.mulVec_add _ x y)
  have hself : ∀ k, U k k = AddMonoidHom.id _ := by
    intro k
    apply AddMonoidHom.ext
    intro x
    simp only [U, AddMonoidHom.mk'_apply, AddMonoidHom.id_apply]
    rw [show twU sz lam0 E n σ (uc k) (uc k) = 1 from BAuKer_self hr (hc0 k) (hc1 k) (σ 0) (σ 1), Matrix.one_mulVec]
  have hcomp : ∀ i j k, i ≤ j → j ≤ k → (U j k).comp (U i j) = U i k := by
    intro i j k _ _
    apply AddMonoidHom.ext
    intro x
    simp only [U, AddMonoidHom.comp_apply, AddMonoidHom.mk'_apply]
    rw [Matrix.mulVec_mulVec, show twU sz lam0 E n σ (uc j) (uc k) * twU sz lam0 E n σ (uc i) (uc j) = twU sz lam0 E n σ (uc i) (uc k) from
      BAuKer_comp hr (hc0 j) (hc1 j) (hc0 k) (hc1 k) (σ 0) (σ 1)]
  have htel := duhamel_telescope U hself hcomp (fun i => twAk sz lam0 E s t K n σ c₁ c₂ i ω) m
  simp only [U, AddMonoidHom.mk'_apply, huc, Nat.zero_min, min_self] at htel
  refine eq_add_of_sub_eq' (htel.trans (Finset.sum_congr rfl fun j hj => ?_))
  have hj1 : j + 1 ≤ m := Finset.mem_range.mp hj
  simp only [min_eq_left hj1, min_eq_left (Nat.le_of_succ_le hj1)]
  rw [TwistGrid2_twAk_step]

end Duhamel

/-- **4 (a)** (twin of `StoppedDuhamelN`, `Induction/GridDuhamelN.lean:293`): pathwise, `A_{j∧τ} = Ũ_{u₀,u_{j∧τ}} A₀ + Σ_{i<j∧τ} Ũ_{u_{i+1},u_{j∧τ}} (P_i + ξ_{i+1})`. -/
def BATwistDuhamel (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
      ∀ (n : ℕ) (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) (τ : PathΩ sz → ℕ) (j : ℕ) (ω : PathΩ sz), min j (τ ω) ≤ K n →
        twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ c₁ c₂ (min j (τ ω)) ω =
          twU sz (BAflowLam0 sz z) (BAflowEs sz z) n σ (gridTime s t K n 0) (gridTime s t K n (min j (τ ω))) *ᵥ
              twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ c₁ c₂ 0 ω +
            ∑ i ∈ Finset.range (min j (τ ω)), twU sz (BAflowLam0 sz z) (BAflowEs sz z) n σ (gridTime s t K n (i + 1)) (gridTime s t K n (min j (τ ω))) *ᵥ
              (twPredInc sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ c₁ c₂ i ω + twMartInc sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ c₁ c₂ i ω)

theorem BATwistDuhamel_holds (d : ℕ) : BATwistDuhamel d := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT K hK n σ c₁ c₂ τ j ω hjτ
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hz n
  have hT1 : BAflowT0 sz z n < 1 := (baStep2Data sz z).flowOK_T hκ hz n
  have hΔ : 0 ≤ gridStep s t K n := div_nonneg (sub_nonneg.2 (hst n)) (Nat.cast_nonneg _)
  have hmono : ∀ {i i' : ℕ}, i ≤ i' → gridTime s t K n i ≤ gridTime s t K n i' := by
    intro i i' h
    unfold gridTime
    have : (i : ℝ) ≤ (i' : ℝ) := Nat.cast_le.2 h
    nlinarith
  have hu0 : ∀ k, k ≤ K n → 0 ≤ gridTime s t K n k := by
    intro k _
    have h := hmono (Nat.zero_le k)
    have h0 : gridTime s t K n 0 = s n := by simp [gridTime]
    rw [h0] at h
    linarith [hs n]
  have hu1 : ∀ k, k ≤ K n → gridTime s t K n k < 1 := by
    intro k hk
    have h := hmono hk
    rw [gridTime_last s t K n (hK n)] at h
    linarith [htT n]
  exact TwistGrid2_twAk_duhamel sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n hr hu0 hu1 σ c₁ c₂ hjτ ω

/-- **Clause (i) of 4 (b)**, pathwise: with the canonical `Mart_k = Σ_{j<k} ξ_{j+1}` and
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

/-- **Clause (i) of 4 (b)** in the shape of the first conjunct of `BATwistGridRem`: for every grid, size index and label,
almost surely in the grid walk, for all `k ≤ K n` (it holds at every `ω`: `baTwistGrid_decomp`). -/
theorem baTwistGrid_decomp_ae {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (i : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) :
    ∀ᵐ ω ∂((baStep2Mat sz lam0 E).Pp), ∀ k, k ≤ K n →
      twAk sz lam0 E s t K n i.1 i.2.2.1 i.2.2.2 k ω i.2.1 =
        twAk sz lam0 E s t K n i.1 i.2.2.1 i.2.2.2 0 ω i.2.1 + ((gridStep s t K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k,
          twDriftk sz lam0 E s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 j ω +
        twRem sz lam0 E s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 k ω + twMart sz lam0 E s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 k ω :=
  Filter.Eventually.of_forall fun ω k _ => baTwistGrid_decomp sz lam0 E s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 k ω

/-! ## The grid martingale pin of 4 (b) and its three parts (statements; the proofs of the parts are the successor rows TL2a2-TL2a4) -/

/-- **4 (b)** (the shape of `STGridMartAtgL`, `Chain/Step2Gen.lean:857`, with the fourth clause of `STGridRepNAtgL`, `:994`): (i) the decomposition with the drift of target 3,
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

/-- `∃ C₀ ≥ 0` in front, as `STGridMartgL` (`Chain/Step2Gen.lean:882`). -/
def BATwistGridMart (d : ℕ) : Prop := ∃ C₀ : ℝ, 0 ≤ C₀ ∧ BATwistGridMartAt d C₀

/-! ### The split of 4 (b) (item (v)), as `GridRepRemNAt`, `GridRepTailNAt`, `GridRepWTailNAt` (`Path/DifREP1.lean:74, 95, 112`): clauses (i)-(ii) with the canonical `Mart`, `Rem`; (iii); (iv). -/

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

/-- The assembly of the three parts into 4 (b) (twin of `stGridMartAt_of_parts2`, `Path/DifREP1.lean:1276`: `CK := max`, `∃ Mart Rem := twMart, twRem`, `N^{CK} ≤ K` by monotonicity). -/
def BATwistGridAssemble : Prop :=
  ∀ (d : ℕ) (C₀ : ℝ), 0 ≤ C₀ → BATwistGridRem d C₀ → BATwistGridTail d → BATwistGridWTail d → BATwistGridMartAt d C₀

/-- `BATwistGridAssemble` (twin of `stGridMartAt_of_parts2`, `Path/DifREP1.lean:1276`): the three parts give 4 (b) with `Mart := twMart`, `Rem := twRem`,
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

/-! ## Compiled nonempty instances (`d = 3`, `sz0`: `L = 4`, `W = 32`, `lam = 1/64`; flow `flow_sz0` at `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, `z = zSeq`; `n = 0`;
`σ = (false, true)`, `c₁ = 0`, `c₂ = (1,0,0)`; the window `s ≡ 1/2 < t ≡ 2/3 ≤ BAflowT0` by `t0_sz0`; the grid `K ≡ 4`, `Δ = 1/24`).  Every deterministic hypothesis is
discharged; the three part pins of 4 (b) stay hypotheses (the successor rows TL2a2-TL2a4). -/

section Inst
open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst RBM.BA.EKPinsInst

/-- 4 (a) at the instance: a three-step stopped Duhamel sum (`τ ≡ 3`, `j = 3`, `K ≡ 4`). -/
example (ω : PathΩ sz0) :
    twAk sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => 4) 0 ![false, true] 0 ![1, 0, 0] (min 3 ((fun _ => 3 : PathΩ sz0 → ℕ) ω)) ω =
      twU sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0 ![false, true] (gridTime (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => 4) 0 0)
          (gridTime (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => 4) 0 (min 3 ((fun _ => 3 : PathΩ sz0 → ℕ) ω))) *ᵥ
        twAk sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => 4) 0 ![false, true] 0 ![1, 0, 0] 0 ω +
      ∑ i ∈ Finset.range (min 3 ((fun _ => 3 : PathΩ sz0 → ℕ) ω)),
        twU sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0 ![false, true] (gridTime (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => 4) 0 (i + 1))
            (gridTime (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => 4) 0 (min 3 ((fun _ => 3 : PathΩ sz0 → ℕ) ω))) *ᵥ
          (twPredInc sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => 4) 0 ![false, true] 0 ![1, 0, 0] i ω +
            twMartInc sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => 4) 0 ![false, true] 0 ![1, 0, 0] i ω) :=
  BATwistDuhamel_holds 3 (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => 2 / 3)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun n => t0_sz0 n) (fun _ => 4) (fun _ => by norm_num) 0 ![false, true] 0 ![1, 0, 0]
    (fun _ => 3) 3 ω (by norm_num)

/-- The step identity `A_{j+1} - Ũ A_j = P_j + ξ_{j+1}` and clause (i) at the instance (`k = 3`). -/
example (ω : PathΩ sz0) :
    twAk sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => 4) 0 ![false, true] 0 ![1, 0, 0] 3 ω 0 =
      twAk sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => 4) 0 ![false, true] 0 ![1, 0, 0] 0 ω 0 +
        ((gridStep (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => 4) 0 : ℝ) : ℂ) * ∑ j ∈ Finset.range 3,
          twDriftk sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => 4) 0 ![false, true] 0 0 ![1, 0, 0] j ω +
        twRem sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => 4) 0 ![false, true] 0 0 ![1, 0, 0] 3 ω +
        twMart sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => 4) 0 ![false, true] 0 0 ![1, 0, 0] 3 ω :=
  baTwistGrid_decomp sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => 4) 0 ![false, true] 0 0 ![1, 0, 0] 3 ω

example :=
  baTwistGrid_decomp_ae sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => 4) 0 (![false, true], 0, 0, ![1, 0, 0])

/-- `baTwistGridAssemble_holds` at `d = 3`, `C₀ = 11 ≥ 0`: the three part pins are hypotheses; the conclusion is the pin `BATwistGridMartAt 3 11`. -/
example (hRem : BATwistGridRem 3 11) (hTail : BATwistGridTail 3) (hW : BATwistGridWTail 3) : BATwistGridMartAt 3 11 :=
  baTwistGridAssemble_holds 3 11 (by norm_num) hRem hTail hW

/-- The assembled pin applied at the BA datum `(sz0, zSeq, flow_sz0)`, any `D > 0`, the grid `K_n = ⌈N_n^{CK}⌉ + 1` (`≠ 0`, eventually `≥ N^{CK}`): the conclusion is
`∃ Mart Rem, (i)-(iv)`. -/
example (hRem : BATwistGridRem 3 11) (hTail : BATwistGridTail 3) (hW : BATwistGridWTail 3) {D : ℝ} (hD : 0 < D) : True := by
  have H := baTwistGridAssemble_holds 3 11 (by norm_num) hRem hTail hW
  obtain ⟨CK, hCK, H2⟩ := H (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => 2 / 3)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun n => t0_sz0 n) D hD
  have := H2 (fun n => ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1) (fun n => Nat.succ_ne_zero _)
    (Eventually.of_forall fun n => (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ _))
  trivial

end Inst

end RBM.BA
