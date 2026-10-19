/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Evolution.XiPins
import RBM3D.Propagator.Prop5Hold

/-!
# Evolution kernel: `(sum_res_2_NAL)` of `lem:sum_decay`, every `n ≥ 2`

The proof `ekSumDecayNAL_holds : EKSumDecayNAL d n Λ κ` of a statement of
`RBM3D/Evolution/Pins.lean`, for all `n` and `d ≥ 3`, uniform in `g ∈ (0, Λ]`.

Proof outline: triangle inequality first; the tensor `A` is split by an *anchor* index
`k` into the window `{b : ∀ i ≠ k, |b_k - b_i| < W^ε ℓ_s}` and its complement, where
`(deccA0)` gives `|A_b| ≤ W^{-D}`.  On the window the sum factorises over the indices
(`ek_anchor_sum_le`): the anchor row costs `R_k` (the same-sign bound `C_s` of `ekSameRow_holds`),
and each of the `n - 1` other indices costs the window sum `1 + C_X ρ² r` of `ekXiBall_holds`,
`ρ = W^ε`, `r = (g²+|1-s|)/(g²+|1-t|)`.  The tail costs `R_k P^{n-1}`, `P = (1-s)/(1-t)`.  The
constants are absorbed into `W^{Cε}` using `4 ≤ W^ε` (`ek_arith_nal`).  `ek_anchor_sum_le` is the
windowed analogue of the anchored product sum of the two-dimensional formalization, for an
arbitrary finite type.
-/

set_option linter.style.longLine false

namespace RBM

open Matrix
open scoped Matrix.Norms.Operator

/-! ### The anchored product sum (any finite type) -/

section Anchor

variable {X : Type*} [Fintype X]

/-- **Anchored product sum.**  Window `{b : ∀ i ≠ k, near (b k) (b i)}`: the anchor row sum
`≤ Rk`, every other index has window sums `≤ S`; the total is `≤ Rk S^{n-1}`. -/
theorem ek_anchor_sum_le {n : ℕ} (k : Fin n) (near : X → X → Prop)
    [∀ x y, Decidable (near x y)] (K : Fin n → X → ℝ) (hK : ∀ i x, 0 ≤ K i x) {S Rk : ℝ}
    (hS0 : 0 ≤ S) (hS : ∀ i, i ≠ k → ∀ x, ∑ y ∈ Finset.univ.filter (near x), K i y ≤ S)
    (hR : ∑ x, K k x ≤ Rk) :
    ∑ b : Fin n → X, (if ∀ i, i ≠ k → near (b k) (b i) then ∏ i, K i (b i) else 0)
      ≤ Rk * S ^ (n - 1) := by
  classical
  set T : X → ∀ _ : Fin n, Finset X :=
    fun x i => if i = k then {x} else Finset.univ.filter (near x) with hT
  have h1 : ∑ b : Fin n → X, (if ∀ i, i ≠ k → near (b k) (b i) then ∏ i, K i (b i) else 0)
      = ∑ x : X, ∑ b ∈ Fintype.piFinset (T x), ∏ i, K i (b i) := by
    rw [← Finset.sum_fiberwise Finset.univ (fun b : Fin n → X => b k)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_filter, Finset.filter_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, hT]
    constructor
    · rintro ⟨hb, hW⟩ i
      by_cases hi : i = k
      · subst hi; simp [hb]
      · simp only [hi, ite_false, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← hb]; exact hW i hi
    · intro h
      have hk : b k = x := by simpa using h k
      refine ⟨hk, fun i hi => ?_⟩
      have := h i
      simp only [hi, ite_false, Finset.mem_filter, Finset.mem_univ, true_and] at this
      rwa [hk]
  have h2 : ∀ x : X, ∑ b ∈ Fintype.piFinset (T x), ∏ i, K i (b i) ≤ K k x * S ^ (n - 1) := by
    intro x
    rw [← Finset.prod_univ_sum, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
    have hk : ∑ y ∈ T x k, K k y = K k x := by simp [hT]
    rw [hk]
    refine mul_le_mul_of_nonneg_left ?_ (hK k x)
    calc ∏ i ∈ Finset.univ.erase k, ∑ y ∈ T x i, K i y
        ≤ ∏ _i ∈ Finset.univ.erase k, S := by
          refine Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun y _ => hK i y) ?_
          intro i hi
          have hik : i ≠ k := Finset.ne_of_mem_erase hi
          simpa [hT, hik] using hS i hik x
      _ = S ^ (n - 1) := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
            Fintype.card_fin]
  rw [h1]
  calc ∑ x : X, ∑ b ∈ Fintype.piFinset (T x), ∏ i, K i (b i)
      ≤ ∑ x : X, K k x * S ^ (n - 1) := Finset.sum_le_sum fun x _ => h2 x
    _ = (∑ x : X, K k x) * S ^ (n - 1) := by rw [Finset.sum_mul]
    _ ≤ Rk * S ^ (n - 1) := mul_le_mul_of_nonneg_right hR (pow_nonneg hS0 _)

/-- The whole sum of a product of non-negative factors with anchor row sum `≤ Rk`, others `≤ P`. -/
theorem ek_prod_sum_le {n : ℕ} (k : Fin n) (K : Fin n → X → ℝ) (hK : ∀ i x, 0 ≤ K i x)
    {P Rk : ℝ} (hP : ∀ i, i ≠ k → ∑ y, K i y ≤ P) (hR : ∑ x, K k x ≤ Rk) :
    ∑ b : Fin n → X, ∏ i, K i (b i) ≤ Rk * P ^ (n - 1) := by
  have h1 : ∑ b : Fin n → X, ∏ i, K i (b i) = ∏ i, ∑ y, K i y := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [h1, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  refine mul_le_mul hR ?_ (Finset.prod_nonneg fun i _ => Finset.sum_nonneg fun y _ => hK i y)
    ((Finset.sum_nonneg fun y _ => hK k y).trans hR)
  calc ∏ i ∈ Finset.univ.erase k, ∑ y, K i y ≤ ∏ _i ∈ Finset.univ.erase k, P :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun y _ => hK i y)
          fun i hi => hP i (Finset.ne_of_mem_erase hi)
    _ = P ^ (n - 1) := by
        rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
          Fintype.card_fin]

/-- **Window / tail split at an anchor index.**  `|A_b| ≤ M` everywhere and `|A_b| ≤ δ` off the
window; the kernel factors `κ i` have anchor row sum `≤ Rk`, other row sums `≤ P` and other window
sums `≤ S`.  Then `‖∑_b (∏_i κ_i(b_i)) A_b‖ ≤ M Rk S^{n-1} + δ Rk P^{n-1}`. -/
theorem ek_core_bound {n : ℕ} (k : Fin n) (near : X → X → Prop) [∀ x y, Decidable (near x y)]
    (κ : Fin n → X → ℂ) (A : (Fin n → X) → ℂ) {M δ S P Rk : ℝ} (hM0 : 0 ≤ M) (hδ : 0 ≤ δ)
    (hM : ∀ b, ‖A b‖ ≤ M) (hfar : ∀ b, ¬ (∀ i, i ≠ k → near (b k) (b i)) → ‖A b‖ ≤ δ)
    (hS0 : 0 ≤ S) (hS : ∀ i, i ≠ k → ∀ x, ∑ y ∈ Finset.univ.filter (near x), ‖κ i y‖ ≤ S)
    (hP : ∀ i, i ≠ k → ∑ y, ‖κ i y‖ ≤ P) (hRk : ∑ x, ‖κ k x‖ ≤ Rk) :
    ‖∑ b : Fin n → X, (∏ i, κ i (b i)) * A b‖ ≤
      M * (Rk * S ^ (n - 1)) + δ * (Rk * P ^ (n - 1)) := by
  classical
  have hK : ∀ (i : Fin n) (x : X), 0 ≤ (fun i x => ‖κ i x‖) i x := fun i x => norm_nonneg _
  have hpt : ∀ b : Fin n → X, ‖(∏ i, κ i (b i)) * A b‖ ≤
      M * (if ∀ i, i ≠ k → near (b k) (b i) then ∏ i, ‖κ i (b i)‖ else 0)
        + δ * ∏ i, ‖κ i (b i)‖ := by
    intro b
    rw [norm_mul, norm_prod]
    have hp0 : 0 ≤ ∏ i, ‖κ i (b i)‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
    split_ifs with h
    · have := mul_le_mul_of_nonneg_left (hM b) hp0
      nlinarith [mul_nonneg hδ hp0]
    · have := mul_le_mul_of_nonneg_left (hfar b h) hp0
      nlinarith
  calc ‖∑ b : Fin n → X, (∏ i, κ i (b i)) * A b‖
      ≤ ∑ b : Fin n → X, ‖(∏ i, κ i (b i)) * A b‖ := norm_sum_le _ _
    _ ≤ ∑ b : Fin n → X, (M * (if ∀ i, i ≠ k → near (b k) (b i) then ∏ i, ‖κ i (b i)‖ else 0)
          + δ * ∏ i, ‖κ i (b i)‖) := Finset.sum_le_sum fun b _ => hpt b
    _ = M * ∑ b : Fin n → X, (if ∀ i, i ≠ k → near (b k) (b i) then ∏ i, ‖κ i (b i)‖ else 0)
          + δ * ∑ b : Fin n → X, ∏ i, ‖κ i (b i)‖ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ M * (Rk * S ^ (n - 1)) + δ * (Rk * P ^ (n - 1)) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (ek_anchor_sum_le k near (fun i x => ‖κ i x‖) hK hS0 hS hRk)
            hM0)
          (mul_le_mul_of_nonneg_left (ek_prod_sum_le k (fun i x => ‖κ i x‖) hK hP hRk) hδ)

end Anchor

/-! ### Constants -/

theorem ek_arith_nal {Cb Cs ρ r : ℝ} {m' e : ℕ} (hCb : 0 ≤ Cb) (hCs : 0 ≤ Cs) (hρ : 4 ≤ ρ)
    (hr : 1 ≤ r) (hm : Cs * (1 + Cb) ^ e < 4 ^ m') :
    Cs * (1 + Cb * ρ ^ 2 * r) ^ e ≤ ρ ^ (m' + 2 * e) * r ^ e := by
  have hr0 : 0 ≤ r := by linarith
  have hρ0 : 0 ≤ ρ := by linarith
  have hρ2 : 1 ≤ ρ ^ 2 * r := by
    have : (16 : ℝ) ≤ ρ ^ 2 := by nlinarith
    nlinarith
  have hS : 1 + Cb * ρ ^ 2 * r ≤ (1 + Cb) * (ρ ^ 2 * r) := by nlinarith
  have hSe : (1 + Cb * ρ ^ 2 * r) ^ e ≤ ((1 + Cb) * (ρ ^ 2 * r)) ^ e :=
    pow_le_pow_left₀ (by positivity) hS e
  have hρm : (4 : ℝ) ^ m' ≤ ρ ^ m' := pow_le_pow_left₀ (by norm_num) hρ m'
  have h2 : Cs * (1 + Cb) ^ e ≤ ρ ^ m' := hm.le.trans hρm
  calc Cs * (1 + Cb * ρ ^ 2 * r) ^ e ≤ Cs * ((1 + Cb) * (ρ ^ 2 * r)) ^ e :=
        mul_le_mul_of_nonneg_left hSe hCs
    _ = (Cs * (1 + Cb) ^ e) * (ρ ^ 2) ^ e * r ^ e := by
        rw [mul_pow, mul_pow]; ring
    _ ≤ ρ ^ m' * (ρ ^ 2) ^ e * r ^ e := by gcongr
    _ = ρ ^ (m' + 2 * e) * r ^ e := by ring

/-! ### The anchored bound for `U^{(n)}` -/

/-- The bound of `U^{(n)}_{s,t,σ} ∘ A` at a point `a` from the window sums of `Ξ`: with anchor `k`,
anchor row sum `Rk`, `ρ = W^ε`, `r = (g²+|1-s|)/(g²+|1-t|)`, `P = (1-s)/(1-t)`,
`‖UN A a‖ ≤ ‖A‖ Rk (1 + C_X ρ² r)^{n-1} + W^{-D} Rk P^{n-1}`.  The ball sums of `Ξ` enter as the
hypothesis `hX` (`ekXiBall_holds`). -/
theorem ek_UN_anchor_bound {d L n : ℕ} [NeZero L] (hL : 3 ≤ L) {g : ℝ}
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) {W ε D : ℝ} (hρ : 1 ≤ W ^ ε)
    (m : ℂ) (hm : ‖m‖ = 1) (σ : Fin n → Bool) (A : (Fin n → Zd d L) → ℂ)
    (hA : EKFastDecay g s W ε D A) (hD : 0 ≤ W ^ (-D)) (k : Fin n)
    {CX Rk : ℝ} (hCX : 0 ≤ CX)
    (hX : ∀ μ : ℂ, ‖μ‖ = 1 → ∀ Λ' : ℝ, 1 ≤ Λ' → ∀ R : ℝ, 1 ≤ R → R ≤ Λ' * ellT L g s →
      ∀ (a ctr : Zd d L) (D : Finset (Zd d L)), (∀ b ∈ D, (zdistD d L (ctr - b) : ℝ) ≤ R) →
        ∑ b ∈ D, ‖XiKer d L g μ s t a b‖
          ≤ CX * Λ' ^ 2 * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)))
    (a : Fin n → Zd d L)
    (hRk : ∑ y, ‖uKer d L g (cycProd (EKsgn m σ) k) s t (a k) y‖ ≤ Rk) :
    ‖UN d L g (EKsgn m σ) s t A a‖ ≤
      ‖A‖ * (Rk * (1 + CX * (W ^ ε) ^ 2 * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|))) ^ (n - 1))
        + W ^ (-D) * (Rk * ((1 - s) / (1 - t)) ^ (n - 1)) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_of_lt (by omega : 1 < L)
  have ht0 : 0 ≤ t := hs.trans hst
  have hu : (0 : ℝ) < 1 - t := by linarith
  have hv : (0 : ℝ) < 1 - s := by linarith
  set μ : Fin n → ℂ := fun i => cycProd (EKsgn m σ) i with hμdef
  have hμ : ∀ i, ‖μ i‖ = 1 := fun i => norm_cycProd (fun j => ek_norm_spin hm (σ j)) i
  set r : ℝ := (g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|) with hr
  have hr0 : 0 ≤ r := by positivity
  set ρ : ℝ := W ^ ε with hρdef
  have hℓs : 1 ≤ ellT L g s := one_le_ellT hL1
  set R : ℝ := ρ * ellT L g s with hR
  have hR1 : 1 ≤ R := by nlinarith
  have hS0 : 0 ≤ 1 + CX * ρ ^ 2 * r := by positivity
  -- window sums of the one-index kernels
  have hwin : ∀ (i : Fin n) (x ctr : Zd d L) (E : Finset (Zd d L)),
      (∀ b ∈ E, ((zdistD d L (ctr - b) : ℕ) : ℝ) ≤ R) →
      ∑ y ∈ E, ‖uKer d L g (μ i) s t x y‖ ≤ 1 + CX * ρ ^ 2 * r := by
    intro i x ctr E hE
    have hξ : ‖(t : ℂ) * μ i‖ < 1 := norm_t_mul_lt_one ht0 ht (hμ i)
    have hdec : ∀ y, ‖uKer d L g (μ i) s t x y‖
        ≤ (if x = y then (1 : ℝ) else 0) + ‖XiKer d L g (μ i) s t x y‖ := by
      intro y
      rw [uKer_eq_one_add_XiKer hL hξ, Matrix.add_apply, Matrix.one_apply]
      refine (norm_add_le _ _).trans ?_
      by_cases h : x = y <;> simp [h]
    have h1 : ∑ y ∈ E, (if x = y then (1 : ℝ) else 0) ≤ 1 := by
      rw [Finset.sum_ite_eq]; split_ifs <;> norm_num
    have h2 := hX (μ i) (hμ i) ρ hρ R hR1 le_rfl x ctr E hE
    calc ∑ y ∈ E, ‖uKer d L g (μ i) s t x y‖
        ≤ ∑ y ∈ E, ((if x = y then (1 : ℝ) else 0) + ‖XiKer d L g (μ i) s t x y‖) :=
          Finset.sum_le_sum fun y _ => hdec y
      _ = ∑ y ∈ E, (if x = y then (1 : ℝ) else 0) + ∑ y ∈ E, ‖XiKer d L g (μ i) s t x y‖ :=
          Finset.sum_add_distrib
      _ ≤ 1 + CX * ρ ^ 2 * r := by linarith
  have hrow : ∀ i : Fin n, ∑ y, ‖uKer d L g (μ i) s t (a i) y‖ ≤ (1 - s) / (1 - t) := fun i =>
    (sum_norm_row_le _ (a i)).trans (norm_uKer_le hL hs hst ht (hμ i))
  refine le_trans (ek_core_bound (X := Zd d L) k (fun x y => (zdistD d L (x - y) : ℝ) < R)
    (fun i y => uKer d L g (μ i) s t (a i) y) A (M := ‖A‖) (δ := W ^ (-D))
    (norm_nonneg _) hD (fun b => norm_le_pi_norm A b) ?_ hS0 ?_ (fun i _ => hrow i) hRk) le_rfl
  · intro b hb
    push Not at hb
    obtain ⟨i, hik, hi⟩ := hb
    exact hA b ⟨k, i, hi⟩
  · intro i hik x
    refine hwin i (a i) x _ ?_
    intro b hb
    exact le_of_lt (Finset.mem_filter.mp hb).2

/-! ### The statements -/

/-- **`(sum_res_2_NAL)` of `lem:sum_decay`** for every `n ≥ 2`, `d ≥ 3`, uniform in `g ∈ (0, Λ]`: the
statement `EKSumDecayNAL`.  The anchor is an index `k` with `σ_k = σ_{k+1}`, whose one-index row sum is
bounded by `C_s` of `ekSameRow_holds` instead of `P`; this removes one factor `r` and the factor
`ℓ_t²/ℓ_s²`.  The constant is `C = m'' + 2n - 2` with `m''` least with
`C_s (1 + C_X)^{n-1} < 4^{m''}`.  (`Prop5Short` is the antecedent of the statement; `ekSameRow_holds`
does not use it, `prop5Short_holds` being proved.) -/
theorem ekSumDecayNAL_holds (d n : ℕ) (Λ κ : ℝ) : EKSumDecayNAL d n Λ κ := by
  intro h5 _h5s hd hn hΛ hκ
  obtain ⟨CX, hCX, hX⟩ := ekXiBall_holds d Λ h5 hd hΛ
  obtain ⟨Cs, hCs, hS⟩ := ekSameRow_holds d Λ κ hd hΛ hκ
  obtain ⟨m', hm'⟩ := pow_unbounded_of_one_lt (Cs * (1 + CX) ^ (n - 1)) (by norm_num : (1 : ℝ) < 4)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hm'0 : (0 : ℝ) ≤ m' := Nat.cast_nonneg m'
  refine ⟨(m' : ℝ) + 2 * n - 2, by linarith, ?_⟩
  intro L hL g hg hgΛ W ε D hW1 hε0 hε1 hD hρ s t hs hst ht hWt m hm hκm σ hσ A
  obtain ⟨k, hk⟩ := hσ
  have : NeZero L := ⟨by omega⟩
  intro hA
  have hW0 : 0 < W := by linarith
  have hLge : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hL0 : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
  have hgt : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t := by linarith
  have ht1 : t < 1 := by
    have : 0 < g ^ 2 / (L : ℝ) ^ 2 := by positivity
    linarith
  have hs1 : s < 1 := lt_of_le_of_lt hst ht1
  have hu : (0 : ℝ) < 1 - t := by linarith
  have hv : (0 : ℝ) < 1 - s := by linarith
  set r : ℝ := (g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|) with hr
  set P : ℝ := (1 - s) / (1 - t) with hP
  set ρ : ℝ := W ^ ε with hρdef
  have hρ4 : 4 ≤ ρ := hρ
  have hr1 : 1 ≤ r := by
    rw [hr, abs_of_pos hu, abs_of_pos hv, le_div_iff₀ (by positivity)]
    linarith
  have hP0 : 0 ≤ P := div_nonneg hv.le hu.le
  have hPW : P ≤ W := by
    have h1 : ((1 - t) / (1 - s))⁻¹ ≤ W := inv_le_of_inv_le₀ hW0 hWt
    rwa [inv_div] at h1
  have hW4 : 4 ≤ W := by
    have h1 : W ^ ε ≤ W ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hW1.le hε1.le
    rw [Real.rpow_one] at h1
    linarith
  have hWD : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW0.le _
  have hW1' : (1 : ℝ) ≤ W := hW1.le
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hr0 : 0 ≤ r := by linarith
  have hAn : 0 ≤ ‖A‖ := norm_nonneg _
  -- the one-index factor at the anchor `k`: same sign
  have hcyc : cycProd (EKsgn m σ) k = PropSpin m (σ k) * PropSpin m (σ k) := by
    simp only [cycProd, EKsgn]
    rw [← hk]
  have hrowk : ∀ a : Fin n → Zd d L,
      ∑ y, ‖uKer d L g (cycProd (EKsgn m σ) k) s t (a k) y‖ ≤ Cs := by
    intro a
    refine (sum_norm_row_le _ (a k)).trans ?_
    rw [hcyc]
    exact hS L hL g hg hgΛ m hm hκm (σ k) s t hs hst ht1
  -- (c) the absorption of the constants into `W^{Cε}`
  have habs1 : ρ ^ (m' + 2 * (n - 1)) ≤ W ^ (((m' : ℝ) + 2 * n - 2) * ε) := by
    have h1 : ρ ^ (m' + 2 * (n - 1)) = W ^ (ε * ((m' + 2 * (n - 1) : ℕ) : ℝ)) := by
      rw [hρdef, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
    rw [h1]
    refine Real.rpow_le_rpow_of_exponent_le hW1' ?_
    push_cast
    rw [hcast]
    nlinarith
  have hCs4 : Cs ≤ W ^ m' := by
    have h1 : (1 : ℝ) ≤ (1 + CX) ^ (n - 1) := one_le_pow₀ (by linarith)
    have h2 : Cs ≤ Cs * (1 + CX) ^ (n - 1) := by nlinarith
    exact (h2.trans hm'.le).trans (pow_le_pow_left₀ (by norm_num) hW4 m')
  have habs2 : W ^ (-D) * (Cs * W ^ (n - 1)) ≤ W ^ (-D + ((m' : ℝ) + 2 * n - 2)) := by
    have h1 : W ^ m' * W ^ (n - 1) ≤ W ^ ((m' : ℝ) + 2 * n - 2) := by
      rw [← pow_add, ← Real.rpow_natCast]
      refine Real.rpow_le_rpow_of_exponent_le hW1' ?_
      push_cast
      rw [hcast]
      linarith
    calc W ^ (-D) * (Cs * W ^ (n - 1)) ≤ W ^ (-D) * (W ^ m' * W ^ (n - 1)) := by
          gcongr
      _ ≤ W ^ (-D) * W ^ ((m' : ℝ) + 2 * n - 2) := mul_le_mul_of_nonneg_left h1 hWD
      _ = W ^ (-D + ((m' : ℝ) + 2 * n - 2)) := (Real.rpow_add hW0 _ _).symm
  have hpos : 0 ≤ W ^ (((m' : ℝ) + 2 * n - 2) * ε) * r ^ (n - 1) * ‖A‖
      + W ^ (-D + ((m' : ℝ) + 2 * n - 2)) := by
    positivity
  refine (pi_norm_le_iff_of_nonneg hpos).mpr fun a => ?_
  have hcore := ek_UN_anchor_bound (d := d) (n := n) hL hs hst ht1 (by linarith : 1 ≤ ρ) m hm σ A
    hA hWD k (CX := CX) (Rk := Cs) hCX.le
    (fun μ hμ Λ' hΛ' R hR hRℓ a ctr E hE =>
      hX L hL g hg hgΛ μ hμ s t hs hst ht1 hgt Λ' hΛ' R hR hRℓ a ctr E hE)
    a (hrowk a)
  have hclaim : Cs * (1 + CX * ρ ^ 2 * r) ^ (n - 1) ≤ ρ ^ (m' + 2 * (n - 1)) * r ^ (n - 1) :=
    ek_arith_nal hCX.le hCs.le hρ4 hr1 hm'
  have hPP : P ^ (n - 1) ≤ W ^ (n - 1) := pow_le_pow_left₀ hP0 hPW _
  calc ‖UN d L g (EKsgn m σ) s t A a‖
      ≤ ‖A‖ * (Cs * (1 + CX * ρ ^ 2 * r) ^ (n - 1)) + W ^ (-D) * (Cs * P ^ (n - 1)) := hcore
    _ ≤ ‖A‖ * (ρ ^ (m' + 2 * (n - 1)) * r ^ (n - 1)) + W ^ (-D) * (Cs * W ^ (n - 1)) := by
        gcongr
    _ ≤ ‖A‖ * (W ^ (((m' : ℝ) + 2 * n - 2) * ε) * r ^ (n - 1))
          + W ^ (-D + ((m' : ℝ) + 2 * n - 2)) := by
        gcongr
    _ = W ^ (((m' : ℝ) + 2 * n - 2) * ε) * r ^ (n - 1) * ‖A‖
          + W ^ (-D + ((m' : ℝ) + 2 * n - 2)) := by ring

end RBM
