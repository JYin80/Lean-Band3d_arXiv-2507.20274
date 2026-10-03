/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Evolution.XiPins
import RBM3D.Propagator.Prop5Hold

/-!
# Evolution kernel EK-3: `(sum_res_1)` and `(sum_res_2_NAL)` of `lem:sum_decay`, every `n ≥ 2`

Proofs `ekSumDecay1_holds : EKSumDecay1 d n Λ` and `ekSumDecayNAL_holds : EKSumDecayNAL d n Λ κ`
of the two pins of `RBM3D/Evolution/Pins.lean`, for all `n` and `d ≥ 3`, uniform in `g ∈ (0, Λ]`.

Route (design T2016 b8): triangle inequality first; the tensor `A` is split by an *anchor* index
`k` into the window `{b : ∀ i ≠ k, |b_k - b_i| < W^ε ℓ_s}` and its complement, where
`(deccA0)` gives `|A_b| ≤ W^{-D}`.  On the window the sum factorises over the indices
(`ek_anchor_sum_le`): the anchor row costs `R_k` (`P = (1-s)/(1-t)` for `(sum_res_1)`, the
same-sign bound `C_s` of `ekSameRow_holds` for `(sum_res_2_NAL)`), and each of the `n - 1` other
indices costs the window sum `1 + C_X ρ² r` of `ekXiBall_holds`, `ρ = W^ε`,
`r = (g²+|1-s|)/(g²+|1-t|)`.  The tail costs `R_k P^{n-1}`.  The constants are absorbed into
`W^{Cε}` using `4 ≤ W^ε` (`ek_arith_res1`, `ek_arith_nal`, generalising the probe's
`ek_arith_claim`).
`ek_ellT_sq_ge`, `ek_ratio_le` (`P ≤ 2 (ℓ_t²/ℓ_s²) r`) are copied from the T2016 probe
`c961e62:RBM3D/Probe/T2016Pins.lean` lines 451-505.  `ek_anchor_sum_le` is the windowed analogue of
RBM2D `Evolution/KernelExpand.lean` `sum_prod_anchor_le` (`c9a24cf`, line 93; its statement was
read, the proof here is independent), for an arbitrary finite type.  Registry (DECISIONS §20):
`EKFastDecay`, a hypothesis of `ek_UN_anchor_bound`, is listed in `structuralProps` of
`RBM3D/Test/Axioms.lean`.
-/

set_option linter.style.longLine false

namespace RBM

open Matrix
open scoped Matrix.Norms.Operator

/-! ### Real-variable steps (copied from the T2016 probe) -/

theorem ek_ellT_sq_ge {L : ℕ} {g t : ℝ} (hL : 1 ≤ (L : ℝ)) (hg : 0 ≤ g) (ht : t < 1)
    (hgL : g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t)) :
    g ^ 2 + (1 - t) ≤ 2 * (1 - t) * ellT L g t ^ 2 := by
  have hu : (0 : ℝ) < 1 - t := by linarith
  have hx0 : 0 ≤ g / √|1 - t| := div_nonneg hg (Real.sqrt_nonneg _)
  have hsq : (g / √|1 - t|) ^ 2 = g ^ 2 / (1 - t) := by
    rw [div_pow, Real.sq_sqrt (abs_nonneg _), abs_of_pos hu]
  have hxL : g / √|1 - t| ≤ L := by
    have h2 : (g / √|1 - t|) ^ 2 ≤ (L : ℝ) ^ 2 := by
      rw [hsq, div_le_iff₀ hu]; linarith
    exact le_of_sq_le_sq h2 (by linarith)
  have hmax : max (g / √|1 - t|) 1 ≤ L := max_le hxL hL
  have hell : ellT L g t = max (g / √|1 - t|) 1 := by
    unfold ellT; exact min_eq_left hmax
  have h1 : 1 ≤ ellT L g t ^ 2 := by
    have := one_le_ellT (L := L) (g := g) (t := t) hL
    nlinarith
  have h2 : g ^ 2 / (1 - t) ≤ ellT L g t ^ 2 := by
    rw [← hsq]
    have : g / √|1 - t| ≤ ellT L g t := by rw [hell]; exact le_max_left _ _
    exact pow_le_pow_left₀ hx0 this 2
  have h3 : g ^ 2 ≤ (1 - t) * ellT L g t ^ 2 := by
    rw [div_le_iff₀ hu] at h2; linarith
  nlinarith

/-- `(1-s)/(1-t) ≤ 2 (ℓ_t²/ℓ_s²) (g²+|1-s|)/(g²+|1-t|)` for `s ≤ t ≤ 1 - g²/L²`. -/
theorem ek_ratio_le {L : ℕ} {g s t : ℝ} (hL : 1 ≤ (L : ℝ)) (hg : 0 ≤ g) (hst : s ≤ t)
    (ht : t < 1) (hgL : g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t)) :
    (1 - s) / (1 - t) ≤
      2 * (ellT L g t ^ 2 / ellT L g s ^ 2) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) := by
  have hu : (0 : ℝ) < 1 - t := by linarith
  have hv : (0 : ℝ) < 1 - s := by linarith
  have hs1 : s < 1 := by linarith
  have hls : 0 < ellT L g s := ellT_pos hL
  have h1 := one_sub_mul_ellT_sq_le (L := L) (g := g) (s := s) hg hs1
  rw [abs_of_pos hv] at h1
  have h2 := ek_ellT_sq_ge hL hg ht hgL
  rw [abs_of_pos hu, abs_of_pos hv]
  have hg2 : 0 ≤ g ^ 2 := sq_nonneg g
  rw [div_le_iff₀ hu]
  have key : (1 - s) * (ellT L g s ^ 2 * (g ^ 2 + (1 - t))) ≤
      2 * (1 - t) * ellT L g t ^ 2 * (g ^ 2 + (1 - s)) := by
    nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ g ^ 2 + (1 - t)),
      mul_le_mul_of_nonneg_right h2 (by linarith : (0 : ℝ) ≤ g ^ 2 + (1 - s))]
  have hlsq : 0 < ellT L g s ^ 2 := by positivity
  have hgt : 0 < g ^ 2 + (1 - t) := by linarith
  calc 1 - s = ((1 - s) * (ellT L g s ^ 2 * (g ^ 2 + (1 - t)))) /
          (ellT L g s ^ 2 * (g ^ 2 + (1 - t))) := by field_simp
    _ ≤ (2 * (1 - t) * ellT L g t ^ 2 * (g ^ 2 + (1 - s))) /
          (ellT L g s ^ 2 * (g ^ 2 + (1 - t))) :=
        div_le_div_of_nonneg_right key (by positivity)
    _ = 2 * (ellT L g t ^ 2 / ellT L g s ^ 2) * ((g ^ 2 + (1 - s)) / (g ^ 2 + (1 - t)))
          * (1 - t) := by
        field_simp

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

theorem ek_arith_res1 {Cb ρ q r P : ℝ} {m' e : ℕ} (hCb : 0 ≤ Cb) (hρ : 4 ≤ ρ) (hq : 1 ≤ q)
    (hr : 1 ≤ r) (hP : P ≤ 2 * q * r) (hm' : 2 * (1 + Cb) ^ e < 4 ^ m') :
    P * (1 + Cb * ρ ^ 2 * r) ^ e ≤ ρ ^ (m' + 2 * e) * q * r ^ (e + 1) := by
  have hr0 : 0 ≤ r := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hρ0 : 0 ≤ ρ := by linarith
  have hρ2 : 1 ≤ ρ ^ 2 * r := by
    have : (16 : ℝ) ≤ ρ ^ 2 := by nlinarith
    nlinarith
  have hS : 1 + Cb * ρ ^ 2 * r ≤ (1 + Cb) * (ρ ^ 2 * r) := by nlinarith
  have hSe : (1 + Cb * ρ ^ 2 * r) ^ e ≤ ((1 + Cb) * (ρ ^ 2 * r)) ^ e :=
    pow_le_pow_left₀ (by positivity) hS e
  have hρm : (4 : ℝ) ^ m' ≤ ρ ^ m' := pow_le_pow_left₀ (by norm_num) hρ m'
  have h2 : 2 * (1 + Cb) ^ e ≤ ρ ^ m' := hm'.le.trans hρm
  calc P * (1 + Cb * ρ ^ 2 * r) ^ e ≤ (2 * q * r) * ((1 + Cb) * (ρ ^ 2 * r)) ^ e :=
        mul_le_mul hP hSe (by positivity) (by positivity)
    _ = (2 * (1 + Cb) ^ e) * (ρ ^ 2) ^ e * q * r ^ (e + 1) := by
        rw [mul_pow, mul_pow]; ring
    _ ≤ ρ ^ m' * (ρ ^ 2) ^ e * q * r ^ (e + 1) := by gcongr
    _ = ρ ^ (m' + 2 * e) * q * r ^ (e + 1) := by ring

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

/-! ### The pins -/

/-- **`(sum_res_1)` of `lem:sum_decay`** for every `n ≥ 2`, `d ≥ 3`, uniform in `g ∈ (0, Λ]`: the pin
`EKSumDecay1`, from `Prop5Decay` (through `ekXiBall_holds`).  The constant is
`C = m' + 2n` with `m'` least with `2 (1 + C_X)^{n-1} < 4^{m'}`, `C_X` the constant of
`ekXiBall_holds`. -/
theorem ekSumDecay1_holds (d n : ℕ) (Λ : ℝ) : EKSumDecay1 d n Λ := by
  intro h5 hd hn hΛ
  obtain ⟨CX, hCX, hX⟩ := ekXiBall_holds d Λ h5 hd hΛ
  obtain ⟨m', hm'⟩ := pow_unbounded_of_one_lt (2 * (1 + CX) ^ (n - 1)) (by norm_num : (1 : ℝ) < 4)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hm'0 : (0 : ℝ) ≤ m' := Nat.cast_nonneg m'
  refine ⟨(m' : ℝ) + 2 * n, by linarith, ?_⟩
  intro L hL g hg hgΛ W ε D hW1 hε0 hε1 hD hρ s t hs hst ht hWt m hm σ A
  have : NeZero L := ⟨by omega⟩
  intro hA
  have hW0 : 0 < W := by linarith
  have hLge : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hL0 : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
  have hgt : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t := by linarith
  have hgL : g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t) := by
    rw [div_le_iff₀ hL0] at hgt; linarith
  have ht1 : t < 1 := by
    have : 0 < g ^ 2 / (L : ℝ) ^ 2 := by positivity
    linarith
  have hs1 : s < 1 := lt_of_le_of_lt hst ht1
  have hu : (0 : ℝ) < 1 - t := by linarith
  have hv : (0 : ℝ) < 1 - s := by linarith
  set r : ℝ := (g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|) with hr
  set q : ℝ := ellT L g t ^ 2 / ellT L g s ^ 2 with hq
  set P : ℝ := (1 - s) / (1 - t) with hP
  set ρ : ℝ := W ^ ε with hρdef
  have hρ4 : 4 ≤ ρ := hρ
  have hℓs : 1 ≤ ellT L g s := one_le_ellT hLge
  have hℓt : ellT L g s ≤ ellT L g t := ellT_mono hg.le hst ht1
  have hℓs0 : 0 < ellT L g s := by linarith
  have hr1 : 1 ≤ r := by
    rw [hr, abs_of_pos hu, abs_of_pos hv, le_div_iff₀ (by positivity)]
    linarith
  have hq1 : 1 ≤ q := by
    rw [hq, le_div_iff₀ (by positivity)]
    have := pow_le_pow_left₀ hℓs0.le hℓt 2
    linarith
  have hP0 : 0 ≤ P := div_nonneg hv.le hu.le
  have hPW : P ≤ W := by
    have h1 : ((1 - t) / (1 - s))⁻¹ ≤ W := inv_le_of_inv_le₀ hW0 hWt
    rwa [inv_div] at h1
  have hP2 : P ≤ 2 * q * r := ek_ratio_le hLge hg.le hst ht1 hgL
  have hWD : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW0.le _
  have hAn : 0 ≤ ‖A‖ := norm_nonneg _
  have hW1' : (1 : ℝ) ≤ W := hW1.le
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  -- (c) the absorption of the constants into `W^{Cε}`
  have habs1 : ρ ^ (m' + 2 * (n - 1)) ≤ W ^ (((m' : ℝ) + 2 * n) * ε) := by
    have h1 : ρ ^ (m' + 2 * (n - 1)) = W ^ (ε * ((m' + 2 * (n - 1) : ℕ) : ℝ)) := by
      rw [hρdef, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
    rw [h1]
    refine Real.rpow_le_rpow_of_exponent_le hW1' ?_
    push_cast
    rw [hcast]
    nlinarith
  have habs2 : W ^ (-D) * W ^ n ≤ W ^ (-D + ((m' : ℝ) + 2 * n)) := by
    have h1 : W ^ n ≤ W ^ ((m' : ℝ) + 2 * n) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hW1' (by linarith)
    calc W ^ (-D) * W ^ n ≤ W ^ (-D) * W ^ ((m' : ℝ) + 2 * n) :=
          mul_le_mul_of_nonneg_left h1 hWD
      _ = W ^ (-D + ((m' : ℝ) + 2 * n)) := (Real.rpow_add hW0 _ _).symm
  have hq0 : 0 ≤ q := by linarith
  have hr0 : 0 ≤ r := by linarith
  have hpos : 0 ≤ W ^ (((m' : ℝ) + 2 * n) * ε) * q * r ^ n * ‖A‖ + W ^ (-D + ((m' : ℝ) + 2 * n)) := by
    positivity
  refine (pi_norm_le_iff_of_nonneg hpos).mpr fun a => ?_
  have hcore := ek_UN_anchor_bound (d := d) (n := n) hL hs hst ht1 (by linarith : 1 ≤ ρ) m hm σ A
    hA hWD ⟨0, by omega⟩ (CX := CX) (Rk := P) hCX.le
    (fun μ hμ Λ' hΛ' R hR hRℓ a ctr E hE =>
      hX L hL g hg hgΛ μ hμ s t hs hst ht1 hgt Λ' hΛ' R hR hRℓ a ctr E hE)
    a ((sum_norm_row_le _ (a _)).trans
      (norm_uKer_le hL hs hst ht1 (norm_cycProd (fun j => ek_norm_spin hm (σ j)) _)))
  have hclaim : P * (1 + CX * ρ ^ 2 * r) ^ (n - 1) ≤ ρ ^ (m' + 2 * (n - 1)) * q * r ^ n := by
    have := ek_arith_res1 hCX.le hρ4 hq1 hr1 hP2 hm'
    rwa [hn1] at this
  have hPP : P * P ^ (n - 1) ≤ W ^ n := by
    rw [← pow_succ', hn1]
    exact pow_le_pow_left₀ hP0 hPW n
  calc ‖UN d L g (EKsgn m σ) s t A a‖
      ≤ ‖A‖ * (P * (1 + CX * ρ ^ 2 * r) ^ (n - 1)) + W ^ (-D) * (P * P ^ (n - 1)) := hcore
    _ ≤ ‖A‖ * (ρ ^ (m' + 2 * (n - 1)) * q * r ^ n) + W ^ (-D) * W ^ n := by
        gcongr
    _ ≤ ‖A‖ * (W ^ (((m' : ℝ) + 2 * n) * ε) * q * r ^ n) + W ^ (-D + ((m' : ℝ) + 2 * n)) := by
        gcongr
    _ = W ^ (((m' : ℝ) + 2 * n) * ε) * q * r ^ n * ‖A‖ + W ^ (-D + ((m' : ℝ) + 2 * n)) := by ring

/-- **`(sum_res_2_NAL)` of `lem:sum_decay`** for every `n ≥ 2`, `d ≥ 3`, uniform in `g ∈ (0, Λ]`: the
pin `EKSumDecayNAL`.  The anchor is an index `k` with `σ_k = σ_{k+1}`, whose one-index row sum is
bounded by `C_s` of `ekSameRow_holds` instead of `P`; this removes one factor `r` and the factor
`ℓ_t²/ℓ_s²`.  The constant is `C = m'' + 2n - 2` with `m''` least with
`C_s (1 + C_X)^{n-1} < 4^{m''}`.  (`Prop5Short` is the antecedent of the pin; `ekSameRow_holds`
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

/-! ### Compiled nonempty instances

`d = 3`, `L = 5`, `g = 1/2`, `Λ = 1`, `κ = 1/2`, `m = i` (`‖m‖ = 1`, `Im m = 1 ≥ κ`),
`s = 1/2`, `t = 9/10` (`g²/L² = 1/100 ≤ 1 - t = 1/10`), `W = 25`, `ε = 1/2` (`W^ε = 5 ≥ 4`; the
window radius `W^ε ℓ_s = 5` is below the torus diameter `6`), `D = 2` (`W⁻¹ = 1/25 ≤ (1-t)/(1-s) = 1/5`),
`A = δ_0` on `(Z_5^3)^n`.  `Prop5Decay` and `Prop5Short` are supplied by the proved
`prop5Decay_holds`, `prop5Short_holds`: no hypothesis of the pins is left open. -/

section Instances

/-- the tensor `δ_0` on `(Z_5^3)^n` -/
private noncomputable def ekSDdelta0 (n : ℕ) : (Fin n → Zd 3 5) → ℂ :=
  fun b => if b = 0 then 1 else 0

private theorem ekSD_sqrt25 : (25 : ℝ) ^ ((1 : ℝ) / 2) = 5 := by
  rw [← Real.sqrt_eq_rpow, show (25 : ℝ) = 5 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- `δ_0` satisfies `(deccA0)` at the instance data: a far pair of indices forces `b ≠ 0`, where
`δ_0` vanishes. -/
private theorem ekSD_fastDecay (n : ℕ) :
    EKFastDecay (1 / 2 : ℝ) (1 / 2) 25 (1 / 2) 2 (ekSDdelta0 n) := by
  intro a ⟨i, j, hij⟩
  by_cases ha : a = 0
  · exfalso
    subst ha
    have hℓ : 1 ≤ ellT 5 (1 / 2 : ℝ) (1 / 2) := one_le_ellT (by norm_num)
    rw [ekSD_sqrt25] at hij
    simp at hij
    linarith
  · simp only [ekSDdelta0, ha, ↓reduceIte, norm_zero]
    positivity

private theorem ekSD_ellT_s : ellT 5 (1 / 2 : ℝ) (1 / 2) = 1 := by
  unfold ellT
  have hs : (1 / 2 : ℝ) ≤ Real.sqrt |1 - 1 / 2| := by
    rw [show |(1 : ℝ) - 1 / 2| = 1 / 2 by rw [abs_of_pos (by norm_num)]; norm_num]
    have h4 : (1 / 2 : ℝ) = Real.sqrt (1 / 4) := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
      exact (Real.sqrt_sq (by norm_num)).symm
    calc (1 / 2 : ℝ) = Real.sqrt (1 / 4) := h4
      _ ≤ Real.sqrt (1 / 2) := Real.sqrt_le_sqrt (by norm_num)
  have h : (1 / 2 : ℝ) / Real.sqrt |1 - 1 / 2| ≤ 1 := by
    rw [div_le_one (lt_of_lt_of_le (by norm_num) hs)]
    exact hs
  rw [max_eq_right h]
  norm_num

private theorem ekSD_zdistD_far : zdistD 3 5 (![2, 2, 1] : Zd 3 5) = 5 := by
  unfold zdistD
  simp only [Fin.sum_univ_three, zdist]
  decide

/-- `δ_0` is a nonzero tensor: `‖δ_0‖ = 1`. -/
example (n : ℕ) : ‖ekSDdelta0 n‖ = 1 := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).mpr fun b => ?_) ?_
  · unfold ekSDdelta0
    split_ifs <;> simp
  · have := norm_le_pi_norm (ekSDdelta0 n) 0
    simpa [ekSDdelta0] using this

/-- the far premise of `(deccA0)` is not vacuous at the instance data, for every `n ≥ 2`: two
indices at `ℓ¹` distance `5 = W^ε ℓ_s`. -/
example (n : ℕ) (hn : 2 ≤ n) :
    ∃ a : Fin n → Zd 3 5, ∃ i j, (25 : ℝ) ^ ((1 : ℝ) / 2) * ellT 5 (1 / 2 : ℝ) (1 / 2)
      ≤ (zdistD 3 5 (a i - a j) : ℝ) := by
  refine ⟨fun i => if i.val = 0 then 0 else ![2, 2, 1], ⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
  rw [ekSD_sqrt25, ekSD_ellT_s]
  simp only [↓reduceIte, one_ne_zero, zero_sub, zdistD_neg, ekSD_zdistD_far]
  norm_num

/-- instance of `ekSumDecay1_holds` at `n = 2`, `σ = (+,-)`. -/
example : ∃ C : ℝ, 0 < C ∧
    ‖UN 3 5 (1 / 2 : ℝ) (EKsgn Complex.I ![true, false]) (1 / 2) (9 / 10) (ekSDdelta0 2)‖ ≤
      (25 : ℝ) ^ (C * (1 / 2)) * (ellT 5 (1 / 2 : ℝ) (9 / 10) ^ 2 / ellT 5 (1 / 2 : ℝ) (1 / 2) ^ 2)
          * (((1 / 2 : ℝ) ^ 2 + |1 - 1 / 2|) / ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)) ^ 2
          * ‖ekSDdelta0 2‖ + (25 : ℝ) ^ (-2 + C) := by
  obtain ⟨C, hC, H⟩ := ekSumDecay1_holds 3 2 1 (prop5Decay_holds 3 1) le_rfl le_rfl one_pos
  exact ⟨C, hC, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 25 (1 / 2) 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by rw [ekSD_sqrt25]; norm_num)
    (1 / 2) (9 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) Complex.I
    Complex.norm_I ![true, false] (ekSDdelta0 2) (ekSD_fastDecay 2)⟩

/-- instance of `ekSumDecay1_holds` at `n = 3`, `σ = (+,-,+)`. -/
example : ∃ C : ℝ, 0 < C ∧
    ‖UN 3 5 (1 / 2 : ℝ) (EKsgn Complex.I ![true, false, true]) (1 / 2) (9 / 10) (ekSDdelta0 3)‖ ≤
      (25 : ℝ) ^ (C * (1 / 2)) * (ellT 5 (1 / 2 : ℝ) (9 / 10) ^ 2 / ellT 5 (1 / 2 : ℝ) (1 / 2) ^ 2)
          * (((1 / 2 : ℝ) ^ 2 + |1 - 1 / 2|) / ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)) ^ 3
          * ‖ekSDdelta0 3‖ + (25 : ℝ) ^ (-2 + C) := by
  obtain ⟨C, hC, H⟩ := ekSumDecay1_holds 3 3 1 (prop5Decay_holds 3 1) le_rfl (by norm_num) one_pos
  exact ⟨C, hC, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 25 (1 / 2) 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by rw [ekSD_sqrt25]; norm_num)
    (1 / 2) (9 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) Complex.I
    Complex.norm_I ![true, false, true] (ekSDdelta0 3) (ekSD_fastDecay 3)⟩

/-- instance of `ekSumDecayNAL_holds` at `n = 3`, `σ = (+,+,-)` (`σ_0 = σ_1`), `κ = 1/2`. -/
example : ∃ C : ℝ, 0 < C ∧
    ‖UN 3 5 (1 / 2 : ℝ) (EKsgn Complex.I ![true, true, false]) (1 / 2) (9 / 10) (ekSDdelta0 3)‖ ≤
      (25 : ℝ) ^ (C * (1 / 2))
          * (((1 / 2 : ℝ) ^ 2 + |1 - 1 / 2|) / ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)) ^ (3 - 1)
          * ‖ekSDdelta0 3‖ + (25 : ℝ) ^ (-2 + C) := by
  obtain ⟨C, hC, H⟩ := ekSumDecayNAL_holds 3 3 1 (1 / 2) (prop5Decay_holds 3 1)
    (prop5Short_holds 3 1 (1 / 2)) le_rfl (by norm_num) one_pos (by norm_num)
  exact ⟨C, hC, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 25 (1 / 2) 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by rw [ekSD_sqrt25]; norm_num)
    (1 / 2) (9 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) Complex.I
    Complex.norm_I (by norm_num [Complex.I_im]) ![true, true, false] ⟨0, by decide⟩
    (ekSDdelta0 3) (ekSD_fastDecay 3)⟩

end Instances

end RBM
