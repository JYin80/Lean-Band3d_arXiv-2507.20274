/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Loop.TreeRep
import RBM3D.Propagator.Interface
import RBM3D.Kernel.SumDecay

/-!
# `lem_pureloop`: exponential decay of pure `K`-loops

`\Cref{lem_pureloop}` (`res_pureKes`): when all the charges agree,
`σ_1 = σ_2 = … = σ_n`, there are `c_n, C_n > 0` with

  `|K^(n)_{t,σ,a}| ≤ C_n W^{-d(n-1)} exp(-c_n max_{i,j} |a_i - a_j|)`.

The paper derives this from the `M`-loop tree representation `(eq:tree_rep2)`, in which
every term consists of `M`-edges and *short* unlabeled edges, together with the strong
decay `(prop:ThfadC_short)` -- which holds precisely because the charges are equal, the
case `RBM.ThetaDecayShort` is stated for (`docs/paper-deltas.md`, D11).

## What is proved here

* `RBM.Loop.norm_Theta_same_le_exp` : `(prop:ThfadC_short)` in the form it is used,
  `|Θ^(σ,σ)_t(0,a)| ≤ C e^{-c|a|}` -- the indicator `1_{a=0}` is absorbed because
  `e^{-c|a|} = 1` at `a = 0`;
* `RBM.Loop.sum_exp_decay_conv` : `Σ_y e^{-c|x-y|} e^{-c|y-z|} ≤ C e^{-(c/2)|x-z|}`, the
  convolution of two exponentials on the torus, uniform in `L`.  Half the decay is spent
  on the triangle inequality and half on summing over `y`;
* `RBM.Loop.pureLoop_two` : `res_pureKes` at `n = 2`, from the two-loop formula
  `(Kn2sol)` and the two lemmas above.

## What is assumed, and what is left

`(Kn2sol)` -- `K^(2)_{t,σ,a} = W^{-d} m(σ_1) m(σ_2) Θ_{t m(σ_1) m(σ_2)}(a_1,a_2)` -- is one
of the formulas the paper takes from `[YY_25]`, `[RBSO1D]`; it is carried here as the
hypothesis `RBM.Loop.KTwoFormula`, in the repository's usual form.

The general `n` is not proved.  It needs an induction through the tree values of
`Loop/Partition.lean`: every edge of a pure loop carries `Θ^(σ,σ)` (external) or
`Θ^(σ,σ) - I` (internal), both exponentially decaying, and each split sums over an internal
vertex, which is where `sum_exp_decay_conv` and a constant loss in `c` come in.  That is
its own ticket (`docs/QUEUE.md`, Q25).
-/

namespace RBM.Loop

open Finset Real

variable {d L : ℕ} [NeZero L] {W : ℕ} {g : ℝ}

/-! ### `(prop:ThfadC_short)` as a clean exponential bound -/

/-- `(prop:ThfadC_short)` in the form the pure-loop estimate uses: at equal charges the
propagator decays exponentially, `|Θ_{t m²}(0,a)| ≤ C e^{-c|a|}`, with the indicator
absorbed into the constant. -/
theorem norm_Theta_same_le_exp {k : ℕ} {m : ℂ} (hd : 3 ≤ k + 2) (hg : 0 < g)
    (hm : ‖m‖ = 1) (hmi : 0 < m.im) (hshort : ThetaDecayShort (k + 2) g m) :
    ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∀ (L : ℕ) (_ : 3 ≤ L) (t : ℝ), 0 ≤ t → t < 1 →
      ∀ a : Zd (k + 2) L,
        haveI : NeZero L := ⟨by omega⟩
        ‖Theta (k + 2) L g ((t : ℂ) * (m * m)) 0 a‖
          ≤ C * Real.exp (-(c * (zdistD (k + 2) L a : ℝ))) := by
  obtain ⟨Cκ, hCκ, cκ, hcκ, hbd⟩ := hshort hd hg hm hmi
  refine ⟨Cκ * (1 + g ^ 2), by positivity, cκ, hcκ, ?_⟩
  intro L hL t ht0 ht1 a
  have : NeZero L := ⟨by omega⟩
  have hb := hbd L hL t ht0 ht1 a
  have hexp : (0 : ℝ) < Real.exp (-(cκ * (zdistD (k + 2) L a : ℝ))) := Real.exp_pos _
  have hind : (if a = 0 then (1 : ℝ) else 0) ≤ Real.exp (-(cκ * (zdistD (k + 2) L a : ℝ))) := by
    by_cases ha : a = 0
    · subst ha
      simp
    · simp only [ha, ite_false]
      exact hexp.le
  have hg2 : (0 : ℝ) ≤ g ^ 2 := by positivity
  calc ‖Theta (k + 2) L g ((t : ℂ) * (m * m)) 0 a‖
      ≤ Cκ * ((if a = 0 then 1 else 0)
          + g ^ 2 * Real.exp (-cκ * (zdistD (k + 2) L a : ℝ))) := hb
    _ = Cκ * ((if a = 0 then 1 else 0)
          + g ^ 2 * Real.exp (-(cκ * (zdistD (k + 2) L a : ℝ)))) := by ring_nf
    _ ≤ Cκ * (Real.exp (-(cκ * (zdistD (k + 2) L a : ℝ)))
          + g ^ 2 * Real.exp (-(cκ * (zdistD (k + 2) L a : ℝ)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hCκ.le
        linarith
    _ = Cκ * (1 + g ^ 2) * Real.exp (-(cκ * (zdistD (k + 2) L a : ℝ))) := by ring

/-! ### Convolution of two exponentials -/

/-- `Σ_y e^{-c|x-y|} e^{-c|y-z|} ≤ C(c,d) e^{-(c/2)|x-z|}`, uniformly in `L`: half of the
decay pays for the triangle inequality, the other half for the sum over `y`. -/
theorem sum_exp_decay_conv (k : ℕ) {c : ℝ} (hc : 0 < c) (x z : Zd (k + 2) L) :
    ∑ y : Zd (k + 2) L,
        Real.exp (-(c * (zdistD (k + 2) L (x - y) : ℝ)))
          * Real.exp (-(c * (zdistD (k + 2) L (y - z) : ℝ)))
      ≤ expC k (c / 2) * Real.exp (-(c / 2 * (zdistD (k + 2) L (x - z) : ℝ))) := by
  have hc2 : 0 < c / 2 := by linarith
  have hpt : ∀ y : Zd (k + 2) L,
      Real.exp (-(c * (zdistD (k + 2) L (x - y) : ℝ)))
          * Real.exp (-(c * (zdistD (k + 2) L (y - z) : ℝ)))
        ≤ Real.exp (-(c / 2 * (zdistD (k + 2) L (x - z) : ℝ)))
          * Real.exp (-(c / 2 * (zdistD (k + 2) L (x - y) : ℝ))) := by
    intro y
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have htri : zdistD (k + 2) L (x - z) ≤ zdistD (k + 2) L (x - y) + zdistD (k + 2) L (y - z) := by
      have h := zdistD_add_le (k + 2) L (x - y) (y - z)
      rwa [sub_add_sub_cancel] at h
    have htri' : ((zdistD (k + 2) L (x - z) : ℕ) : ℝ)
        ≤ (zdistD (k + 2) L (x - y) : ℝ) + (zdistD (k + 2) L (y - z) : ℝ) := by
      exact_mod_cast htri
    have h1 : (0 : ℝ) ≤ (zdistD (k + 2) L (y - z) : ℝ) := Nat.cast_nonneg _
    nlinarith
  calc ∑ y : Zd (k + 2) L,
        Real.exp (-(c * (zdistD (k + 2) L (x - y) : ℝ)))
          * Real.exp (-(c * (zdistD (k + 2) L (y - z) : ℝ)))
      ≤ ∑ y : Zd (k + 2) L, Real.exp (-(c / 2 * (zdistD (k + 2) L (x - z) : ℝ)))
          * Real.exp (-(c / 2 * (zdistD (k + 2) L (x - y) : ℝ))) :=
        Finset.sum_le_sum fun y _ => hpt y
    _ = Real.exp (-(c / 2 * (zdistD (k + 2) L (x - z) : ℝ)))
          * ∑ y : Zd (k + 2) L, Real.exp (-(c / 2 * (zdistD (k + 2) L (x - y) : ℝ))) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (-(c / 2 * (zdistD (k + 2) L (x - z) : ℝ))) * expC k (c / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        rw [show ∑ y : Zd (k + 2) L, Real.exp (-(c / 2 * (zdistD (k + 2) L (x - y) : ℝ)))
            = ∑ u : Zd (k + 2) L, Real.exp (-(c / 2 * (zdistD (k + 2) L u : ℝ))) from
          Fintype.sum_equiv (Equiv.subLeft x) _ _ fun y => rfl]
        exact sum_radial_exp_decay_le k hc2
    _ = expC k (c / 2) * Real.exp (-(c / 2 * (zdistD (k + 2) L (x - z) : ℝ))) := by ring

/-! ### The star tree at any `n`

The canonical partition with no diagonals contributes `Σ_b Π_i Θ(a_i, b)`.  For a pure
loop every factor decays exponentially, and the sum is controlled uniformly in `L` by the
same split as in `sum_exp_decay_conv`: half of the total decay `Σ_i |a_i - b|` pays for the
triangle inequality between any two labels, the other half for the sum over the centre `b`.

This is the `n`-fold analogue of `sum_exp_decay_conv`, and it is what `res_pureKes` needs
on the star; the trees with diagonals are `docs/QUEUE.md`, Q33.
-/

/-- `Σ_b e^{-c|x-b|} ≤ C(c,d)`, uniformly in `L` and in the centre `x`. -/
theorem sum_exp_decay_centre (k : ℕ) {c : ℝ} (hc : 0 < c) (x : Zd (k + 2) L) :
    ∑ b : Zd (k + 2) L, Real.exp (-(c * (zdistD (k + 2) L (x - b) : ℝ))) ≤ expC k c := by
  rw [sum_shift (k + 2) x (fun r : ℕ => Real.exp (-(c * (r : ℝ))))]
  exact sum_radial_exp_decay_le k hc

/-- **The star of a pure loop decays exponentially.**  If every entry satisfies
`‖E x y‖ ≤ C e^{-c|x-y|}`, then for all labels `a : Fin n → Z_L^d` and every pair of
indices `p, q`,
`‖Σ_b Π_i E (a i) b‖ ≤ C^n C(c/2,d) e^{-(c/2)|a_p - a_q|}`.

Taking the maximum over `p, q` gives the form of `res_pureKes`: the star decays in the
diameter of the label set. -/
theorem norm_sum_prod_le (k : ℕ) {n : ℕ} (E : Zd (k + 2) L → Zd (k + 2) L → ℂ)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hE : ∀ x y : Zd (k + 2) L,
      ‖E x y‖ ≤ C * Real.exp (-(c * (zdistD (k + 2) L (x - y) : ℝ))))
    (a : Fin n → Zd (k + 2) L) (p q : Fin n) :
    ‖∑ b : Zd (k + 2) L, ∏ i : Fin n, E (a i) b‖
      ≤ C ^ n * expC k (c / 2)
        * Real.exp (-(c / 2 * (zdistD (k + 2) L (a p - a q) : ℝ))) := by
  have hc2 : 0 < c / 2 := by linarith
  set D : Zd (k + 2) L → ℝ := fun b => ∑ i : Fin n, (zdistD (k + 2) L (a i - b) : ℝ) with hD
  have hD0 : ∀ b, 0 ≤ D b := fun b =>
    Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  -- the diameter is paid for by two of the terms
  have hpair : ∀ b : Zd (k + 2) L,
      ((zdistD (k + 2) L (a p - a q) : ℕ) : ℝ) ≤ D b := by
    intro b
    rcases eq_or_ne p q with rfl | hpq
    · simpa [hD] using hD0 b
    · have htri : (zdistD (k + 2) L (a p - a q) : ℕ)
          ≤ zdistD (k + 2) L (a p - b) + zdistD (k + 2) L (a q - b) := by
        have h := zdistD_add_le (k + 2) L (a p - b) (b - a q)
        rw [sub_add_sub_cancel] at h
        have hneg : zdistD (k + 2) L (b - a q) = zdistD (k + 2) L (a q - b) := by
          rw [← zdistD_neg (k + 2) L (a q - b), neg_sub]
        rw [hneg] at h
        exact h
      have hsub : ({p, q} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
      have hle : ∑ i ∈ ({p, q} : Finset (Fin n)), ((zdistD (k + 2) L (a i - b) : ℕ) : ℝ)
          ≤ D b :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => Nat.cast_nonneg _
      rw [Finset.sum_pair hpq] at hle
      have : ((zdistD (k + 2) L (a p - a q) : ℕ) : ℝ)
          ≤ ((zdistD (k + 2) L (a p - b) : ℕ) : ℝ)
            + ((zdistD (k + 2) L (a q - b) : ℕ) : ℝ) := by exact_mod_cast htri
      linarith
  -- and one more term pays for the sum over the centre
  have hone : ∀ b : Zd (k + 2) L, ((zdistD (k + 2) L (a p - b) : ℕ) : ℝ) ≤ D b := fun b =>
    Finset.single_le_sum (f := fun i => ((zdistD (k + 2) L (a i - b) : ℕ) : ℝ))
      (fun i _ => Nat.cast_nonneg _) (Finset.mem_univ p)
  have hterm : ∀ b : Zd (k + 2) L, ‖∏ i : Fin n, E (a i) b‖
      ≤ C ^ n * (Real.exp (-(c / 2 * (zdistD (k + 2) L (a p - a q) : ℝ)))
        * Real.exp (-(c / 2 * (zdistD (k + 2) L (a p - b) : ℝ)))) := by
    intro b
    have hprod : ‖∏ i : Fin n, E (a i) b‖
        ≤ ∏ i : Fin n, (C * Real.exp (-(c * (zdistD (k + 2) L (a i - b) : ℝ)))) := by
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hE (a i) b)
    have hsplit : ∏ i : Fin n, (C * Real.exp (-(c * (zdistD (k + 2) L (a i - b) : ℝ))))
        = C ^ n * Real.exp (-(c * D b)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      congr 1
      rw [hD, Finset.mul_sum, ← Real.exp_sum]
      congr 1
      rw [← Finset.sum_neg_distrib]
    have hexp : Real.exp (-(c * D b))
        ≤ Real.exp (-(c / 2 * (zdistD (k + 2) L (a p - a q) : ℝ)))
          * Real.exp (-(c / 2 * (zdistD (k + 2) L (a p - b) : ℝ))) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have h1 := hpair b
      have h2 := hone b
      nlinarith
    calc ‖∏ i : Fin n, E (a i) b‖
        ≤ C ^ n * Real.exp (-(c * D b)) := hsplit ▸ hprod
      _ ≤ C ^ n * (Real.exp (-(c / 2 * (zdistD (k + 2) L (a p - a q) : ℝ)))
            * Real.exp (-(c / 2 * (zdistD (k + 2) L (a p - b) : ℝ)))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
  calc ‖∑ b : Zd (k + 2) L, ∏ i : Fin n, E (a i) b‖
      ≤ ∑ b : Zd (k + 2) L, ‖∏ i : Fin n, E (a i) b‖ := norm_sum_le _ _
    _ ≤ ∑ b : Zd (k + 2) L, C ^ n
          * (Real.exp (-(c / 2 * (zdistD (k + 2) L (a p - a q) : ℝ)))
            * Real.exp (-(c / 2 * (zdistD (k + 2) L (a p - b) : ℝ)))) :=
        Finset.sum_le_sum fun b _ => hterm b
    _ = C ^ n * Real.exp (-(c / 2 * (zdistD (k + 2) L (a p - a q) : ℝ)))
          * ∑ b : Zd (k + 2) L, Real.exp (-(c / 2 * (zdistD (k + 2) L (a p - b) : ℝ))) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring
    _ ≤ C ^ n * Real.exp (-(c / 2 * (zdistD (k + 2) L (a p - a q) : ℝ))) * expC k (c / 2) := by
        refine mul_le_mul_of_nonneg_left (sum_exp_decay_centre k hc2 (a p)) (by positivity)
    _ = C ^ n * expC k (c / 2)
          * Real.exp (-(c / 2 * (zdistD (k + 2) L (a p - a q) : ℝ))) := by ring

/-! ### The two-loop formula and `res_pureKes` at `n = 2` -/

variable (d L W g)

/-- `(Kn2sol)`: `K^(2)_{t,σ,a} = W^{-d} m(σ_1) m(σ_2) Θ_{t m(σ_1)m(σ_2)}(a_1, a_2)`.  The
paper takes this from `[YY_25]`, `[RBSO1D]`; it is carried as a hypothesis. -/
def KTwoFormula (m : Bool → ℂ) (K : ℝ → LoopIdx (Zd d L) → ℂ) : Prop :=
  ∀ (t : ℝ), 0 ≤ t → t < 1 → ∀ (σ₁ σ₂ : Bool) (a₁ a₂ : Zd d L),
    K t ⟨[σ₁, σ₂], [a₁, a₂]⟩
      = ((W : ℂ) ^ d)⁻¹ * (m σ₁ * m σ₂)
        * Theta d L g ((t : ℂ) * (m σ₁ * m σ₂)) a₁ a₂

variable {d L W g}

/-- **`res_pureKes` at `n = 2`**: for a pure loop `σ₁ = σ₂ = σ`,
`|K^(2)_{t,σ,a}| ≤ C W^{-d} e^{-c |a₁ - a₂|}`. -/
theorem pureLoop_two {k : ℕ} {m : Bool → ℂ} {K : ℝ → LoopIdx (Zd (k + 2) L) → ℂ}
    (hd : 3 ≤ k + 2) (hg : 0 < g) (hL : 3 ≤ L) {σ : Bool}
    (hm : ‖m σ‖ = 1) (hmi : 0 < (m σ).im)
    (hshort : ThetaDecayShort (k + 2) g (m σ))
    (hK : KTwoFormula (k + 2) L W g m K) :
    ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∀ (t : ℝ), 0 ≤ t → t < 1 → ∀ a₁ a₂ : Zd (k + 2) L,
      ‖K t ⟨[σ, σ], [a₁, a₂]⟩‖
        ≤ C * ‖((W : ℂ) ^ (k + 2))⁻¹‖
          * Real.exp (-(c * (zdistD (k + 2) L (a₁ - a₂) : ℝ))) := by
  obtain ⟨C, hC, c, hc, hbd⟩ := norm_Theta_same_le_exp (g := g) hd hg hm hmi hshort
  refine ⟨C, hC, c, hc, ?_⟩
  intro t ht0 ht1 a₁ a₂
  -- translation invariance moves the estimate at `0` to the pair `(a₁, a₂)`
  have hmm : ‖m σ * m σ‖ = 1 := by rw [norm_mul, hm, mul_one]
  have hξ : ‖(t : ℂ) * (m σ * m σ)‖ < 1 := norm_t_mul_lt_one ht0 ht1 hmm
  have htrans : Theta (k + 2) L g ((t : ℂ) * (m σ * m σ)) a₁ a₂
      = Theta (k + 2) L g ((t : ℂ) * (m σ * m σ)) 0 (a₂ - a₁) := by
    have h := Theta_apply_add_right_of_three_le (g := g) hL hξ 0 (a₂ - a₁) a₁
    simpa using h
  have hdist : zdistD (k + 2) L (a₂ - a₁) = zdistD (k + 2) L (a₁ - a₂) := by
    rw [← zdistD_neg (k + 2) L (a₁ - a₂), neg_sub]
  rw [hK t ht0 ht1 σ σ a₁ a₂, htrans]
  have hTheta := hbd L hL t ht0 ht1 (a₂ - a₁)
  rw [hdist] at hTheta
  calc ‖((W : ℂ) ^ (k + 2))⁻¹ * (m σ * m σ)
        * Theta (k + 2) L g ((t : ℂ) * (m σ * m σ)) 0 (a₂ - a₁)‖
      = ‖((W : ℂ) ^ (k + 2))⁻¹‖ * ‖m σ * m σ‖
        * ‖Theta (k + 2) L g ((t : ℂ) * (m σ * m σ)) 0 (a₂ - a₁)‖ := by
        rw [norm_mul, norm_mul]
    _ = ‖((W : ℂ) ^ (k + 2))⁻¹‖
        * ‖Theta (k + 2) L g ((t : ℂ) * (m σ * m σ)) 0 (a₂ - a₁)‖ := by rw [hmm, mul_one]
    _ ≤ ‖((W : ℂ) ^ (k + 2))⁻¹‖ * (C * Real.exp (-(c * (zdistD (k + 2) L (a₁ - a₂) : ℝ)))) :=
        mul_le_mul_of_nonneg_left hTheta (norm_nonneg _)
    _ = C * ‖((W : ℂ) ^ (k + 2))⁻¹‖
        * Real.exp (-(c * (zdistD (k + 2) L (a₁ - a₂) : ℝ))) := by ring

end RBM.Loop
