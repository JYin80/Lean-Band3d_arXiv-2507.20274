/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Propagator.Props4

/-!
# The evolution kernel `U^(n)` and `lem:sum_Ndecay`

`\Cref{DefTHUST}` (Section 3) defines, for tensors `𝒜 : (Z_L^d)^n → ℂ` and
`σ = (σ₁, …, σₙ) ∈ {+,-}^n` with the cyclic convention `σ_{n+1} = σ₁`,

* `(def:op_thn)` `(Θ^(n)_{t,σ} ∘ 𝒜)_a = Σ_i Σ_{b_i} (M S / (1 - t M S))_{a_i b_i} 𝒜_{a^(i)(b_i)}`,
* `(def_Ustz)` `(U^(n)_{s,t,σ} ∘ 𝒜)_a = Σ_b ∏_i ((1 - s M S) / (1 - t M S))_{a_i b_i} 𝒜_b`,

with `M = M^(σ_i,σ_{i+1})`.  For the random band matrix model
`M^(σ_i,σ_{i+1}) = m(σ_i) m(σ_{i+1}) I`, so with `μ_i := m(σ_i) m(σ_{i+1})` (`RBM.cycProd`)
the one-index kernels are `μ_i S^(B) Θ_{t μ_i}` and `(1 - s μ_i S^(B)) Θ_{t μ_i}`, built on
`RBM.Theta`.  The signs enter only through `m : Fin n → ℂ`, `m i = m(σ_i)`, `‖m i‖ = 1`.

`lem:sum_Ndecay` (proved in Appendix A.2): for `0 ≤ s ≤ t < 1`,

  `‖U^(n)_{s,t,σ} ∘ 𝒜‖_∞ ≤ ((1-s)/(1-t))^n ‖𝒜‖_∞`.

The proof follows the paper: `(eq:decompUalt)` writes the one-index kernel as `1 + Ξ`
with `Ξ = (t-s) μ S Θ_t`; `(Xi_infint)` bounds `‖Ξ‖_{∞→∞} ≤ (t-s)/(1-t)` using property 4
(`RBM.norm_Theta_le`); so each factor has `(∞→∞)`-norm at most `(1-s)/(1-t)`.  The product
over the `n` indices is `∏_i Σ_{c} |K_i(a_i, c)| = Σ_b ∏_i |K_i(a_i, b_i)|`
(`Finset.prod_univ_sum`), with no induction on `n`.

`‖𝒜‖_∞ = max_a |𝒜_a|` is Mathlib's sup norm on the function type `(Fin n → Zd d L) → ℂ`,
and `‖·‖_{∞→∞}` is the `ℓ^∞` operator norm `Matrix.Norms.Operator`, which is
`max_a Σ_b |·_{ab}|` by definition.  The paper assumes `n ≥ 2`; the bound holds for all `n`.
-/

namespace RBM

open Matrix
open scoped NNReal Matrix.Norms.Operator

variable (d L : ℕ) [NeZero L] (g : ℝ)

section Defs

/-- `μ_i = m(σ_i) m(σ_{i+1})` with the cyclic convention `σ_{n+1} = σ₁`. -/
def cycProd {n : ℕ} (m : Fin n → ℂ) (i : Fin n) : ℂ := m i * m (finRotate n i)

/-- The one-index kernel of `(def:op_thn)`: `M S / (1 - t M S) = μ S^(B) Θ_{tμ}`. -/
noncomputable def thetaKer (μ : ℂ) (t : ℝ) : Matrix (Zd d L) (Zd d L) ℂ :=
  (μ • SB d L g) * Theta d L g ((t : ℂ) * μ)

/-- The one-index kernel of `(def_Ustz)`: `(1 - s M S) / (1 - t M S) = (1 - s μ S^(B)) Θ_{tμ}`. -/
noncomputable def uKer (μ : ℂ) (s t : ℝ) : Matrix (Zd d L) (Zd d L) ℂ :=
  (1 - ((s : ℂ) * μ) • SB d L g) * Theta d L g ((t : ℂ) * μ)

/-- `(def:op_thn)`: the operator `Θ^(n)_{t,σ}` on `n`-index tensors. -/
noncomputable def ThetaN {n : ℕ} (m : Fin n → ℂ) (t : ℝ) (A : (Fin n → Zd d L) → ℂ) :
    (Fin n → Zd d L) → ℂ :=
  fun a => ∑ i, ∑ b, thetaKer d L g (cycProd m i) t (a i) b * A (Function.update a i b)

/-- `(def_Ustz)`: the evolution kernel `U^(n)_{s,t,σ}` on `n`-index tensors. -/
noncomputable def UN {n : ℕ} (m : Fin n → ℂ) (s t : ℝ) (A : (Fin n → Zd d L) → ℂ) :
    (Fin n → Zd d L) → ℂ :=
  fun a => ∑ b : Fin n → Zd d L, (∏ i, uKer d L g (cycProd m i) s t (a i) (b i)) * A b

end Defs

variable {d L g}

theorem norm_cycProd {n : ℕ} {m : Fin n → ℂ} (hm : ∀ i, ‖m i‖ = 1) (i : Fin n) :
    ‖cycProd m i‖ = 1 := by
  rw [cycProd, norm_mul, hm, hm, one_mul]

/-- A row sum of a matrix is at most its `ℓ^∞` operator norm. -/
theorem sum_norm_row_le {n : Type*} [Fintype n] (A : Matrix n n ℂ) (a : n) :
    ∑ b, ‖A a b‖ ≤ ‖A‖ := by
  have h := Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ a)
  have h2 := NNReal.coe_le_coe.mpr h
  rw [Matrix.linfty_opNorm_def]
  simpa [NNReal.coe_sum] using h2

section OneIndex

variable {μ : ℂ} {s t : ℝ}

/-- `(eq:decompUalt)`: `(1 - s M S)/(1 - t M S) = 1 + Ξ` with `Ξ = (t - s) M S Θ_t`. -/
theorem uKer_eq_one_add (hL : 3 ≤ L) (hξ : ‖(t : ℂ) * μ‖ < 1) :
    uKer d L g μ s t = 1 + (((t : ℂ) - s) * μ) • (SB d L g * Theta d L g ((t : ℂ) * μ)) := by
  have h := mul_Theta_of_three_le (d := d) (g := g) hL hξ
  have hsplit : (1 - ((s : ℂ) * μ) • SB d L g)
      = (1 - ((t : ℂ) * μ) • SB d L g) + (((t : ℂ) - s) * μ) • SB d L g := by
    rw [sub_mul, sub_smul]; abel
  rw [uKer, hsplit, add_mul, h, smul_mul_assoc]

/-- `(Xi_infint)`: `‖Ξ‖_{∞→∞} ≤ (t - s) ‖Θ_t‖_{∞→∞} ≤ (t - s)/(1 - t)`. -/
theorem norm_Xi_le (hL : 3 ≤ L) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) (hμ : ‖μ‖ = 1) :
    ‖(((t : ℂ) - s) * μ) • (SB d L g * Theta d L g ((t : ℂ) * μ))‖ ≤ (t - s) / (1 - t) := by
  have ht0 : 0 ≤ t := hs.trans hst
  have hΘ := norm_Theta_le (d := d) (g := g) hL ht0 ht hμ
  have hc : ‖((t : ℂ) - s) * μ‖ = t - s := by
    rw [norm_mul, hμ, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  calc ‖(((t : ℂ) - s) * μ) • (SB d L g * Theta d L g ((t : ℂ) * μ))‖
      ≤ ‖((t : ℂ) - s) * μ‖ * (‖SB d L g‖ * ‖Theta d L g ((t : ℂ) * μ)‖) :=
        (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
    _ = (t - s) * ‖Theta d L g ((t : ℂ) * μ)‖ := by rw [hc, norm_SB d L g hL, one_mul]
    _ ≤ (t - s) * (1 - t)⁻¹ := mul_le_mul_of_nonneg_left hΘ (by linarith)
    _ = (t - s) / (1 - t) := by rw [div_eq_mul_inv]

/-- Each one-index factor of `U^(n)` has `(∞→∞)`-norm at most `(1 - s)/(1 - t)`. -/
theorem norm_uKer_le (hL : 3 ≤ L) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) (hμ : ‖μ‖ = 1) :
    ‖uKer d L g μ s t‖ ≤ (1 - s) / (1 - t) := by
  have ht0 : 0 ≤ t := hs.trans hst
  have hξ : ‖(t : ℂ) * μ‖ < 1 := norm_t_mul_lt_one ht0 ht hμ
  rw [uKer_eq_one_add hL hξ]
  have h1t : 0 < 1 - t := by linarith
  calc ‖(1 : Matrix (Zd d L) (Zd d L) ℂ)
        + (((t : ℂ) - s) * μ) • (SB d L g * Theta d L g ((t : ℂ) * μ))‖
      ≤ ‖(1 : Matrix (Zd d L) (Zd d L) ℂ)‖
        + ‖(((t : ℂ) - s) * μ) • (SB d L g * Theta d L g ((t : ℂ) * μ))‖ := norm_add_le _ _
    _ ≤ 1 + (t - s) / (1 - t) := by
        rw [norm_one]; exact add_le_add_right (norm_Xi_le hL hs hst ht hμ) 1
    _ = (1 - s) / (1 - t) := by field_simp; ring

end OneIndex

/-- `lem:sum_Ndecay`, pointwise form. -/
theorem norm_UN_apply_le (hL : 3 ≤ L) {n : ℕ} {m : Fin n → ℂ} (hm : ∀ i, ‖m i‖ = 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) (A : (Fin n → Zd d L) → ℂ)
    (a : Fin n → Zd d L) :
    ‖UN d L g m s t A a‖ ≤ ((1 - s) / (1 - t)) ^ n * ‖A‖ := by
  set K : Fin n → Matrix (Zd d L) (Zd d L) ℂ := fun i => uKer d L g (cycProd m i) s t
  have hrow : ∀ i, ∑ c, ‖K i (a i) c‖ ≤ (1 - s) / (1 - t) := fun i =>
    (sum_norm_row_le (K i) (a i)).trans (norm_uKer_le hL hs hst ht (norm_cycProd hm i))
  calc ‖UN d L g m s t A a‖
      ≤ ∑ b : Fin n → Zd d L, ‖(∏ i, K i (a i) (b i)) * A b‖ := norm_sum_le _ _
    _ ≤ ∑ b : Fin n → Zd d L, (∏ i, ‖K i (a i) (b i)‖) * ‖A‖ := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul, norm_prod]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm A b)
          (Finset.prod_nonneg fun i _ => norm_nonneg _)
    _ = (∏ i, ∑ c, ‖K i (a i) c‖) * ‖A‖ := by
        rw [← Finset.sum_mul, Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ ≤ ((1 - s) / (1 - t)) ^ n * ‖A‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        calc ∏ i, ∑ c, ‖K i (a i) c‖ ≤ ∏ _i : Fin n, (1 - s) / (1 - t) :=
              Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun c _ => norm_nonneg _)
                fun i _ => hrow i
          _ = ((1 - s) / (1 - t)) ^ n := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **`lem:sum_Ndecay`, `(sum_res_Ndecay)`**: for `0 ≤ s ≤ t < 1`,
`‖U^(n)_{s,t,σ} ∘ 𝒜‖_∞ ≤ ((1-s)/(1-t))^n ‖𝒜‖_∞`. -/
theorem norm_UN_le (hL : 3 ≤ L) {n : ℕ} {m : Fin n → ℂ} (hm : ∀ i, ‖m i‖ = 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) (A : (Fin n → Zd d L) → ℂ) :
    ‖UN d L g m s t A‖ ≤ ((1 - s) / (1 - t)) ^ n * ‖A‖ := by
  have hpos : 0 ≤ ((1 - s) / (1 - t)) ^ n * ‖A‖ :=
    mul_nonneg (pow_nonneg (div_nonneg (by linarith) (by linarith)) n) (norm_nonneg _)
  exact (pi_norm_le_iff_of_nonneg hpos).mpr fun a => norm_UN_apply_le hL hm hs hst ht A a

end RBM
