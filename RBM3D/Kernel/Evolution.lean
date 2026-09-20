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

/-! ### Tensor kernels, and the zero-mode-removing operators `P^(i)`, `Q^(i)`, `Q^(A)`

`(def_Ustz)` builds `U^(n)` out of one one-index kernel per index.  `RBM.tensorKer` is
that construction for an arbitrary family of kernels, and `RBM.UN_eq_tensorKer` says
`U^(n)` is an instance of it.  `\Cref{def;zero_mode_remove}` defines the partial
averaging operator `P^(i)`, the zero-mode-removing `Q^(i) = I - P^(i)` and
`Q^(A) = ∏_{i ∈ A} Q^(i)`.

The structural fact behind `lem:sum_decay_nonzero` is that `Q^(i)` passes through a
tensor kernel by left-multiplying the `i`-th kernel with `I - L^{-d} J`
(`RBM.zeroModeOp_tensorKer`), so `Q^(A) ∘ U^(n)` is again a tensor kernel
(`RBM.zeroModeSet_tensorKer`) -- with the `(∞→∞)`-norm of each factor to be estimated
one index at a time. -/

section TensorKernel

variable (d L : ℕ) [NeZero L] {n : ℕ}

/-- The tensor product of `n` one-index kernels, acting on `n`-index tensors:
`(K ∘ 𝒜)_a = Σ_b ∏_i K_i(a_i, b_i) 𝒜_b`.  `(def_Ustz)` is the case
`K_i = (1 - s μ_i S^(B)) Θ_{t μ_i}`. -/
noncomputable def tensorKer (K : Fin n → Matrix (Zd d L) (Zd d L) ℂ)
    (A : (Fin n → Zd d L) → ℂ) : (Fin n → Zd d L) → ℂ :=
  fun a => ∑ b : Fin n → Zd d L, (∏ i, K i (a i) (b i)) * A b

/-- `P^(i)`: averaging over the `i`-th index, `\Cref{def;zero_mode_remove}`. -/
noncomputable def avgOp (i : Fin n) (A : (Fin n → Zd d L) → ℂ) : (Fin n → Zd d L) → ℂ :=
  fun a => ((L : ℂ) ^ d)⁻¹ * ∑ c : Zd d L, A (Function.update a i c)

/-- `Q^(i) = I - P^(i)`, the zero-mode-removing operator on the `i`-th index. -/
noncomputable def zeroModeOp (i : Fin n) (A : (Fin n → Zd d L) → ℂ) : (Fin n → Zd d L) → ℂ :=
  fun a => A a - avgOp d L i A a

/-- `Q^(A) = ∏_{i ∈ A} Q^(i)`; the factors commute, so the order in `A.toList` is
immaterial (and `Q^(i)` is idempotent, so even repetitions would be). -/
noncomputable def zeroModeSet (A : Finset (Fin n)) (T : (Fin n → Zd d L) → ℂ) :
    (Fin n → Zd d L) → ℂ :=
  A.toList.foldr (fun i f => zeroModeOp d L i f) T

/-- The one-index matrix of `Q^(i)`: `I - L^{-d} J`, i.e. `Proj_{e^⊥}` for the constant
vector `e`. -/
noncomputable def projMat : Matrix (Zd d L) (Zd d L) ℂ :=
  1 - Matrix.of fun _ _ : Zd d L => ((L : ℂ) ^ d)⁻¹

variable {d L}

theorem UN_eq_tensorKer (m : Fin n → ℂ) (s t : ℝ) :
    UN d L g m s t = tensorKer d L (fun i => uKer d L g (cycProd m i) s t) := rfl

theorem sum_one_complex : ∑ _c : Zd d L, (1 : ℂ) = ((L : ℂ) ^ d) := by
  simp [Finset.card_univ, ZMod.card]

/-- `I - L^{-d} J` is idempotent: it is the projection `Proj_{e^⊥}`. -/
theorem projMat_mul_self : projMat d L * projMat d L = projMat d L := by
  have hJ : (Matrix.of fun _ _ : Zd d L => ((L : ℂ) ^ d)⁻¹)
      * (Matrix.of fun _ _ : Zd d L => ((L : ℂ) ^ d)⁻¹)
      = Matrix.of fun _ _ : Zd d L => ((L : ℂ) ^ d)⁻¹ := by
    ext a b
    have hL : ((L : ℂ) ^ d) ≠ 0 := by
      have : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
      positivity
    have hcard : (Fintype.card (Zd d L) : ℂ) = (L : ℂ) ^ d := by
      simp [ZMod.card]
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    rw [hcard]
    field_simp
  simp only [projMat, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hJ]
  abel

/-- **`Q^(i)` passes through a tensor kernel**, left-multiplying the `i`-th kernel by
`I - L^{-d} J`. -/
theorem zeroModeOp_tensorKer (i : Fin n) (K : Fin n → Matrix (Zd d L) (Zd d L) ℂ)
    (A : (Fin n → Zd d L) → ℂ) :
    zeroModeOp d L i (tensorKer d L K A)
      = tensorKer d L (Function.update K i (projMat d L * K i)) A := by
  funext a
  have hsplit : ∀ F : Fin n → ℂ, ∏ j, F j = F i * ∏ j ∈ Finset.univ.erase i, F j := fun F => by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hfac : ∀ b : Fin n → Zd d L,
      (∏ j, Function.update K i (projMat d L * K i) j (a j) (b j))
        = (∏ j, K j (a j) (b j))
          - ((L : ℂ) ^ d)⁻¹ * ∑ c : Zd d L, ∏ j, K j (Function.update a i c j) (b j) := by
    intro b
    have h1 : ∏ j, Function.update K i (projMat d L * K i) j (a j) (b j)
        = (projMat d L * K i) (a i) (b i) * ∏ j ∈ Finset.univ.erase i, K j (a j) (b j) := by
      rw [hsplit fun j => Function.update K i (projMat d L * K i) j (a j) (b j)]
      simp only [Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    have h2 : ∀ c : Zd d L, ∏ j, K j (Function.update a i c j) (b j)
        = K i c (b i) * ∏ j ∈ Finset.univ.erase i, K j (a j) (b j) := by
      intro c
      rw [hsplit fun j => K j (Function.update a i c j) (b j)]
      simp only [Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    have h3 : (projMat d L * K i) (a i) (b i)
        = K i (a i) (b i) - ((L : ℂ) ^ d)⁻¹ * ∑ c : Zd d L, K i c (b i) := by
      simp only [projMat, Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply,
        sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true, Finset.mul_sum]
    rw [h1, h3, hsplit fun j => K j (a j) (b j)]
    simp only [h2, ← Finset.sum_mul]
    ring
  simp only [tensorKer, zeroModeOp, avgOp, hfac, sub_mul, Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.sum_mul]
  refine congrArg₂ (· - ·) rfl ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring

/-- The list form of `Q^(A)`: folding `Q^(i)` over a list of indices left-multiplies the
kernels at those indices by `I - L^{-d} J`. -/
theorem zeroModeList_tensorKer (l : List (Fin n)) (K : Fin n → Matrix (Zd d L) (Zd d L) ℂ)
    (T : (Fin n → Zd d L) → ℂ) :
    l.foldr (fun i f => zeroModeOp d L i f) (tensorKer d L K T)
      = tensorKer d L (fun i => if i ∈ l then projMat d L * K i else K i) T := by
  induction l generalizing K with
  | nil => simp
  | cons j l ih =>
    rw [List.foldr_cons, ih, zeroModeOp_tensorKer]
    congr 1
    funext i
    by_cases hij : i = j
    · subst hij
      by_cases hil : i ∈ l <;>
        simp [Function.update_self, hil, ← Matrix.mul_assoc, projMat_mul_self]
    · simp [hij]

/-- **`Q^(A) ∘ (tensor kernel)` is again a tensor kernel**, with the kernels at the
indices of `A` left-multiplied by `I - L^{-d} J`.  This is the structural half of
`lem:sum_decay_nonzero`. -/
theorem zeroModeSet_tensorKer (A : Finset (Fin n)) (K : Fin n → Matrix (Zd d L) (Zd d L) ℂ)
    (T : (Fin n → Zd d L) → ℂ) :
    zeroModeSet d L A (tensorKer d L K T)
      = tensorKer d L (fun i => if i ∈ A then projMat d L * K i else K i) T := by
  rw [zeroModeSet, zeroModeList_tensorKer]
  exact congrArg (tensorKer d L · T) (funext fun i => by simp [Finset.mem_toList])

/-- For a translation-invariant matrix, every row sum equals the row sum at `0`, so the
`(∞→∞)`-norm is controlled by the entries in one row. -/
theorem norm_le_sum_row_zero (M : Matrix (Zd d L) (Zd d L) ℂ)
    (h : ∀ a b c : Zd d L, M (a + c) (b + c) = M a b) :
    ‖M‖ ≤ ∑ b : Zd d L, ‖M 0 b‖ := by
  have key : ∀ a : Zd d L, ∑ b : Zd d L, ‖M a b‖ = ∑ b : Zd d L, ‖M 0 b‖ := by
    intro a
    have hrow : ∀ b : Zd d L, M a b = M 0 (b - a) := by
      intro b
      have := h 0 (b - a) a
      simpa using this
    calc ∑ b : Zd d L, ‖M a b‖ = ∑ b : Zd d L, ‖M 0 (b - a)‖ :=
          Finset.sum_congr rfl fun b _ => by rw [hrow b]
      _ = ∑ b : Zd d L, ‖M 0 b‖ := Fintype.sum_equiv (Equiv.subRight a) _ _ fun b => rfl
  have hnn : 0 ≤ ∑ b : Zd d L, ‖M 0 b‖ :=
    Finset.sum_nonneg fun b _ => norm_nonneg _
  have hsup : (Finset.univ.sup fun a => ∑ b, ‖M a b‖₊)
      ≤ (⟨∑ b : Zd d L, ‖M 0 b‖, hnn⟩ : ℝ≥0) := by
    refine Finset.sup_le fun a _ => ?_
    have h2 : ((∑ b, ‖M a b‖₊ : ℝ≥0) : ℝ) ≤ ∑ b : Zd d L, ‖M 0 b‖ := by
      simpa [NNReal.coe_sum] using (key a).le
    exact NNReal.coe_le_coe.mp h2
  rw [Matrix.linfty_opNorm_def]
  exact le_of_le_of_eq (NNReal.coe_le_coe.mpr hsup) rfl

/-- `‖I - L^{-d} J‖_{∞→∞} ≤ 2`. -/
theorem norm_projMat_le : ‖projMat d L‖ ≤ 2 := by
  have hJ : ‖(Matrix.of fun _ _ : Zd d L => ((L : ℂ) ^ d)⁻¹)‖ ≤ 1 := by
    have hinv : ∀ a b c : Zd d L,
        (Matrix.of fun _ _ : Zd d L => ((L : ℂ) ^ d)⁻¹) (a + c) (b + c)
          = (Matrix.of fun _ _ : Zd d L => ((L : ℂ) ^ d)⁻¹) a b := fun _ _ _ => rfl
    refine (norm_le_sum_row_zero _ hinv).trans ?_
    have hL0 : (0 : ℝ) < (L : ℝ) ^ d := by
      have : (0 : ℝ) < (L : ℝ) := by
        have := NeZero.ne L
        have : 0 < L := Nat.pos_of_ne_zero this
        exact_mod_cast this
      positivity
    simp only [Matrix.of_apply, norm_inv, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [show ((Fintype.card (Zd d L) : ℝ)) = (L : ℝ) ^ d by simp [ZMod.card],
      show ‖((L : ℂ) ^ d)‖ = (L : ℝ) ^ d by simp]
    rw [mul_inv_cancel₀ hL0.ne']
  calc ‖projMat d L‖ ≤ ‖(1 : Matrix (Zd d L) (Zd d L) ℂ)‖
        + ‖(Matrix.of fun _ _ : Zd d L => ((L : ℂ) ^ d)⁻¹)‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := by rw [norm_one]; linarith
    _ = 2 := by norm_num

/-- The columns of `S^(B)(g)` sum to `1`. -/
theorem sum_SB_col (hL : 3 ≤ L) (b : Zd d L) : ∑ c : Zd d L, SB d L g c b = 1 := by
  rw [← sum_sbKernel d L g hL]
  exact Fintype.sum_equiv (Equiv.subRight b) _ _ fun c => by rw [SB_apply]; rfl

/-- `I - L^{-d} J` commutes with `S^(B)(g)`: the paper's remark that
`Proj_{e^⊥}` commutes with the translation-invariant `M^(σ₁,σ₂) S^(B)`. -/
theorem projMat_mul_SB_comm (hL : 3 ≤ L) :
    projMat d L * SB d L g = SB d L g * projMat d L := by
  ext a b
  have hcol : ∑ c : Zd d L, SB d L g c b = 1 := sum_SB_col hL b
  have hrow : ∑ c : Zd d L, SB d L g a c = 1 := sum_SB_row d L g hL a
  simp only [projMat, Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply,
    sub_mul, mul_sub, Finset.sum_sub_distrib, ite_mul, mul_ite, one_mul, mul_one, zero_mul,
    mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ← Finset.sum_mul, ← Finset.mul_sum]
  rw [hcol, hrow]
  ring

/-- **`Proj_{e^⊥} Θ_ξ = Θ̊_ξ`**: left-multiplying the propagator by `I - L^{-d} J` is
exactly the zero-mode removal `(def_Thxi0)`. -/
theorem projMat_mul_Theta (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    projMat d L * Theta d L g ξ = Theta0 d L g ξ := by
  have hL0 : ((L : ℂ) ^ d) ≠ 0 := by
    have hne : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
    positivity
  have hsym : ∀ x y : Zd d L, Theta d L g ξ x y = Theta d L g ξ y x := by
    intro x y
    have hT := Theta_transpose_of_three_le (d := d) (g := g) hL hξ
    calc Theta d L g ξ x y = (Theta d L g ξ)ᵀ y x := rfl
      _ = Theta d L g ξ y x := by rw [hT]
  have hrowsum : ∀ x : Zd d L, ∑ y : Zd d L, Theta d L g ξ x y = (1 - ξ)⁻¹ :=
    fun x => sum_Theta_row_of_three_le hL hξ x
  ext a b
  have hcol : ∑ c : Zd d L, Theta d L g ξ c b = (1 - ξ)⁻¹ := by
    rw [Finset.sum_congr rfl fun c _ => hsym c b]
    exact hrowsum b
  have hdouble : ∑ a' : Zd d L, ∑ b' : Zd d L, Theta d L g ξ a' b'
      = (L : ℂ) ^ d * (1 - ξ)⁻¹ := by
    rw [Finset.sum_congr rfl fun a' _ => hrowsum a', Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    congr 1
    simp [ZMod.card]
  simp only [projMat, Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply,
    Theta0_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.mul_sum]
  rw [hcol, hdouble, two_mul, pow_add]
  field_simp

/-- `‖K ∘ 𝒜‖_∞ ≤ (∏_i ‖K_i‖_{∞→∞}) ‖𝒜‖_∞`, pointwise form. -/
theorem norm_tensorKer_apply_le (K : Fin n → Matrix (Zd d L) (Zd d L) ℂ)
    (A : (Fin n → Zd d L) → ℂ) (a : Fin n → Zd d L) :
    ‖tensorKer d L K A a‖ ≤ (∏ i, ‖K i‖) * ‖A‖ := by
  calc ‖tensorKer d L K A a‖
      ≤ ∑ b : Fin n → Zd d L, ‖(∏ i, K i (a i) (b i)) * A b‖ := norm_sum_le _ _
    _ ≤ ∑ b : Fin n → Zd d L, (∏ i, ‖K i (a i) (b i)‖) * ‖A‖ := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul, norm_prod]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm A b)
          (Finset.prod_nonneg fun i _ => norm_nonneg _)
    _ = (∏ i, ∑ c, ‖K i (a i) c‖) * ‖A‖ := by
        rw [← Finset.sum_mul, Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ ≤ (∏ i, ‖K i‖) * ‖A‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun c _ => norm_nonneg _)
          fun i _ => sum_norm_row_le (K i) (a i)

/-- `‖K ∘ 𝒜‖_∞ ≤ (∏_i ‖K_i‖_{∞→∞}) ‖𝒜‖_∞`. -/
theorem norm_tensorKer_le (K : Fin n → Matrix (Zd d L) (Zd d L) ℂ)
    (A : (Fin n → Zd d L) → ℂ) : ‖tensorKer d L K A‖ ≤ (∏ i, ‖K i‖) * ‖A‖ := by
  have hpos : 0 ≤ (∏ i, ‖K i‖) * ‖A‖ :=
    mul_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _) (norm_nonneg _)
  exact (pi_norm_le_iff_of_nonneg hpos).mpr fun a => norm_tensorKer_apply_le K A a

end TensorKernel

end RBM
