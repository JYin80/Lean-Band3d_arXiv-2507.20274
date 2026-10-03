/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Evolution.XiPins
import RBM3D.Propagator.Prop5Hold

/-!
# Evolution kernel EK-5: `lem:sum_decay_nonzero` without loss

`ekSumDecayNonzero_holds : EKSumDecayNonzero d n Λ κ` for all `d n Λ κ`: the pin
`(sum_res_Ndecay_nonzero)`, `‖Q^(A) U^(n)_{s,t,σ} 𝒜‖_∞ ≤ C ‖𝒜‖_∞` for `1 - g²/L² ≤ s ≤ t < 1`,
`A ⊇ I_diff(σ)`, with `C` depending on `(d, n, Λ, κ)` only (no `L^{nτ}`).

The proof ports `norm_zeroModeSet_UN_le` (`RBM3D/Kernel/Evolution.lean:520-683`):
* `i ∉ A`: `σ_i = σ_{i+1}`, so the factor is bounded by `ekSameRow_holds` (EK-2);
* `i ∈ A`: `Proj · (1 - sμS) Θ_{tμ} = Proj + (t-s) μ S Θ̊_{tμ}`, and the row sum of `Θ̊` is
  bounded by pin 8 (`Prop8ZeroMode`) and the radial sum `sum_radial_pow_le`;
  `(1-s) L² ≤ g²` removes `L²`.
The antecedent `Prop5Short` of the pin is not used (it is only needed through `ekSameRow_holds`,
which proves it itself).
-/

set_option linter.style.longLine false

namespace RBM

open Matrix
open scoped NNReal Matrix.Norms.Operator

/-- the constant of the radial sum `Σ_b (|b|+1)^{-k} ≤ E L²` -/
private noncomputable def ekE (k : ℕ) : ℝ :=
  Real.exp (Real.sqrt ((k : ℝ) + 2)) * (2 ^ (k + 2) * radC 1)

private theorem ekE_pos (k : ℕ) : 0 < ekE k := by
  unfold ekE
  have := radC_pos (one_pos : (0 : ℝ) < 1)
  have := Real.exp_pos (Real.sqrt ((k : ℝ) + 2))
  positivity

private theorem ek_norm_PropSpin {m : ℂ} (hm : ‖m‖ = 1) (b : Bool) : ‖PropSpin m b‖ = 1 := by
  unfold PropSpin
  split_ifs
  · exact hm
  · simpa using hm

private theorem ek_norm_spin_mul {m : ℂ} (hm : ‖m‖ = 1) (b c : Bool) :
    ‖PropSpin m b * PropSpin m c‖ = 1 := by
  rw [norm_mul, ek_norm_PropSpin hm, ek_norm_PropSpin hm, one_mul]

/-- `(eq:diffcolor)` without loss: at an index carrying `Proj_{e^⊥}` the one-index factor is bounded
by `2 + C₀ E`, given `1 - s ≤ g²/L²` and the bound of pin 8 with constant `C₀`. -/
private theorem ek_norm_projMat_mul_uKer_le {k : ℕ} {Λ κ C₀ : ℝ} (hC₀ : 0 < C₀)
    (hbd : ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ₁ σ₂ : Bool, ∀ a : Zd (k + 2) L,
        haveI : NeZero L := ⟨by omega⟩
        ‖Theta0 (k + 2) L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖
          ≤ C₀ * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD (k + 2) L a : ℝ) + 1) ^ (k + 2 - 2))⁻¹)
    (L : ℕ) (hL : 3 ≤ L) (g : ℝ) (hg : 0 < g) (hgΛ : g ≤ Λ) (s t : ℝ) (hs : 0 ≤ s)
    (hsg : 1 - g ^ 2 / (L : ℝ) ^ 2 ≤ s) (hst : s ≤ t) (ht : t < 1) (m : ℂ) (hm : ‖m‖ = 1)
    (hκm : κ ≤ m.im) (σ₁ σ₂ : Bool) :
    haveI : NeZero L := ⟨by omega⟩
    ‖projMat (k + 2) L * uKer (k + 2) L g (PropSpin m σ₁ * PropSpin m σ₂) s t‖
      ≤ 2 + C₀ * ekE k := by
  have : NeZero L := ⟨by omega⟩
  set μ : ℂ := PropSpin m σ₁ * PropSpin m σ₂ with hμdef
  have hμ : ‖μ‖ = 1 := ek_norm_spin_mul hm σ₁ σ₂
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_of_lt (by omega : 1 < L)
  have ht0 : 0 ≤ t := hs.trans hst
  have hξ : ‖(t : ℂ) * μ‖ < 1 := norm_t_mul_lt_one ht0 ht hμ
  have hE0 := ekE_pos k
  -- the zero-mode-removed propagator: pin 8 plus the radial sum
  have hTheta0 : ‖Theta0 (k + 2) L g ((t : ℂ) * μ)‖
      ≤ C₀ * (g ^ 2 + |1 - t|)⁻¹ * (ekE k * (L : ℝ) ^ 2) := by
    have htrans : ∀ a b c : Zd (k + 2) L,
        Theta0 (k + 2) L g ((t : ℂ) * μ) (a + c) (b + c)
          = Theta0 (k + 2) L g ((t : ℂ) * μ) a b :=
      fun a b c => Theta0_apply_add_right hL hξ a b c
    refine (norm_le_sum_row_zero _ htrans).trans ?_
    calc ∑ b : Zd (k + 2) L, ‖Theta0 (k + 2) L g ((t : ℂ) * μ) 0 b‖
        ≤ ∑ b : Zd (k + 2) L, C₀ * (g ^ 2 + |1 - t|)⁻¹
            * (((zdistD (k + 2) L b : ℝ) + 1) ^ (k + 2 - 2))⁻¹ :=
          Finset.sum_le_sum fun b _ => hbd L hL g hg hgΛ t ht0 ht m hm hκm σ₁ σ₂ b
      _ = C₀ * (g ^ 2 + |1 - t|)⁻¹
            * ∑ b : Zd (k + 2) L, (((zdistD (k + 2) L b : ℝ) + 1) ^ k)⁻¹ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => by norm_num
      _ ≤ C₀ * (g ^ 2 + |1 - t|)⁻¹ * (ekE k * (L : ℝ) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := sum_radial_pow_le (L := L) k hL1
          unfold ekE
          rw [mul_assoc]
          exact this
  -- `1 - s ≤ g²/L²` removes the factor `L²`
  have hcoef : (t - s) * ((g ^ 2 + |1 - t|)⁻¹ * (L : ℝ) ^ 2) ≤ 1 := by
    have hg2 : (0 : ℝ) < g ^ 2 := by positivity
    have h1 : (g ^ 2 + |1 - t|)⁻¹ ≤ (g ^ 2)⁻¹ :=
      inv_anti₀ hg2 (by have := abs_nonneg (1 - t); linarith)
    have h2 : t - s ≤ 1 - s := by linarith
    have hs2 : (1 - s) * (L : ℝ) ^ 2 ≤ g ^ 2 := by
      have hsg' : 1 - s ≤ g ^ 2 / (L : ℝ) ^ 2 := by linarith
      rw [le_div_iff₀ (by positivity)] at hsg'; linarith
    have h3 : (g ^ 2 + |1 - t|)⁻¹ * (L : ℝ) ^ 2 ≤ (g ^ 2)⁻¹ * (L : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    calc (t - s) * ((g ^ 2 + |1 - t|)⁻¹ * (L : ℝ) ^ 2)
        ≤ (1 - s) * ((g ^ 2)⁻¹ * (L : ℝ) ^ 2) :=
          mul_le_mul h2 h3 (by positivity) (by linarith)
      _ = ((1 - s) * (L : ℝ) ^ 2) / g ^ 2 := by field_simp
      _ ≤ 1 := by rw [div_le_one hg2]; exact hs2
  -- `projMat * uKer = projMat + (t-s) μ • (S Θ̊)`
  have hsplit : projMat (k + 2) L * uKer (k + 2) L g μ s t
      = projMat (k + 2) L
        + (((t : ℂ) - s) * μ) • (SB (k + 2) L g * Theta0 (k + 2) L g ((t : ℂ) * μ)) := by
    rw [uKer_eq_one_add hL hξ, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
      ← Matrix.mul_assoc, projMat_mul_SB_comm hL, Matrix.mul_assoc,
      projMat_mul_Theta hL hξ]
  rw [hsplit]
  have hsmul := norm_smul_le (((t : ℂ) - s) * μ)
    (SB (k + 2) L g * Theta0 (k + 2) L g ((t : ℂ) * μ))
  have hmul := norm_mul_le (SB (k + 2) L g) (Theta0 (k + 2) L g ((t : ℂ) * μ))
  rw [norm_SB (k + 2) L g hL, one_mul] at hmul
  have hc : ‖((t : ℂ) - s) * μ‖ = t - s := by
    rw [norm_mul, hμ, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have hterm : ‖(((t : ℂ) - s) * μ) • (SB (k + 2) L g * Theta0 (k + 2) L g ((t : ℂ) * μ))‖
      ≤ C₀ * ekE k := by
    calc ‖(((t : ℂ) - s) * μ) • (SB (k + 2) L g * Theta0 (k + 2) L g ((t : ℂ) * μ))‖
        ≤ (t - s) * ‖Theta0 (k + 2) L g ((t : ℂ) * μ)‖ := by
          rw [← hc]
          exact hsmul.trans (mul_le_mul_of_nonneg_left hmul (norm_nonneg _))
      _ ≤ (t - s) * (C₀ * (g ^ 2 + |1 - t|)⁻¹ * (ekE k * (L : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hTheta0 (by linarith)
      _ = (C₀ * ekE k) * ((t - s) * ((g ^ 2 + |1 - t|)⁻¹ * (L : ℝ) ^ 2)) := by ring
      _ ≤ (C₀ * ekE k) * 1 :=
          mul_le_mul_of_nonneg_left hcoef (by positivity)
      _ = C₀ * ekE k := mul_one _
  calc ‖projMat (k + 2) L
        + (((t : ℂ) - s) * μ) • (SB (k + 2) L g * Theta0 (k + 2) L g ((t : ℂ) * μ))‖
      ≤ ‖projMat (k + 2) L‖
        + ‖(((t : ℂ) - s) * μ) • (SB (k + 2) L g * Theta0 (k + 2) L g ((t : ℂ) * μ))‖ :=
        norm_add_le _ _
    _ ≤ 2 + C₀ * ekE k := add_le_add norm_projMat_le hterm

/-- **`lem:sum_decay_nonzero`, `(sum_res_Ndecay_nonzero)`**, loss-free: the pin `EKSumDecayNonzero`. -/
theorem ekSumDecayNonzero_holds (d n : ℕ) (Λ κ : ℝ) : EKSumDecayNonzero d n Λ κ := by
  intro _h5 h8 hd _hn hΛ hκ
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  obtain ⟨Cs, hCs, hsame⟩ := ekSameRow_holds (k + 2) Λ κ hd hΛ hκ
  obtain ⟨C₀, hC₀, hbd⟩ := h8 hd hΛ hκ
  have hE0 := ekE_pos k
  set Ci : ℝ := max Cs (2 + C₀ * ekE k) with hCi
  have hCi0 : 0 < Ci := lt_of_lt_of_le hCs (le_max_left _ _)
  refine ⟨Ci ^ n, pow_pos hCi0 n, ?_⟩
  intro L hL g hg hgΛ s t hs hsg hst ht m hm hκm σ A hA 𝒜
  have : NeZero L := ⟨by omega⟩
  -- the bound of the one-index factor at each `i`
  have key : ∀ i : Fin n,
      ‖(if i ∈ A then projMat (k + 2) L * uKer (k + 2) L g (cycProd (EKsgn m σ) i) s t
          else uKer (k + 2) L g (cycProd (EKsgn m σ) i) s t)‖ ≤ Ci := by
    intro i
    by_cases hi : i ∈ A
    · simp only [hi, ite_true]
      exact (ek_norm_projMat_mul_uKer_le hC₀ hbd L hL g hg hgΛ s t hs hsg hst ht m hm hκm
        (σ i) (σ (finRotate n i))).trans (le_max_right _ _)
    · have hσ : σ i = σ (finRotate n i) := by
        by_contra hne
        exact hi (hA i hne)
      simp only [hi, ite_false]
      have hcyc : cycProd (EKsgn m σ) i = PropSpin m (σ i) * PropSpin m (σ i) := by
        simp only [cycProd, EKsgn]
        rw [← hσ]
      rw [hcyc]
      exact (hsame L hL g hg hgΛ m hm hκm (σ i) s t hs hst ht).trans (le_max_left _ _)
  rw [UN_eq_tensorKer, zeroModeSet_tensorKer]
  calc ‖tensorKer (k + 2) L
        (fun i => if i ∈ A then projMat (k + 2) L * uKer (k + 2) L g (cycProd (EKsgn m σ) i) s t
          else uKer (k + 2) L g (cycProd (EKsgn m σ) i) s t) 𝒜‖
      ≤ (∏ i, ‖(if i ∈ A then projMat (k + 2) L * uKer (k + 2) L g (cycProd (EKsgn m σ) i) s t
          else uKer (k + 2) L g (cycProd (EKsgn m σ) i) s t)‖) * ‖𝒜‖ := norm_tensorKer_le _ _
    _ ≤ (∏ _i : Fin n, Ci) * ‖𝒜‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => key i
    _ = Ci ^ n * ‖𝒜‖ := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ### Instances (nonempty application of `ekSumDecayNonzero_holds`) -/

section Instances

/-- the point mass `δ₀` on `n`-index tensors -/
noncomputable def ekDelta0 (n d L : ℕ) : (Fin n → Zd d L) → ℂ := fun a => if a = 0 then 1 else 0

/-- `d = 3`, `n = 2`, `Λ = 1`, `κ = 1/2`, `L = 5`, `g = 1/2`, `s = 995/1000 ≥ 1 - g²/L² = 99/100`,
`t = 999/1000`, `m = i`, `σ = (+,-)`, `A = univ`, `𝒜 = δ₀`; both pins are discharged by their proofs. -/
example :
    haveI : NeZero 5 := ⟨by norm_num⟩
    ∃ C : ℝ, 0 < C ∧ ekDelta0 2 3 5 0 ≠ 0 ∧
      ‖zeroModeSet 3 5 (Finset.univ : Finset (Fin 2))
          (UN 3 5 (1 / 2 : ℝ) (EKsgn Complex.I ![true, false]) (995 / 1000) (999 / 1000)
            (ekDelta0 2 3 5))‖ ≤ C * ‖ekDelta0 2 3 5‖ := by
  obtain ⟨C, hC, H⟩ := ekSumDecayNonzero_holds 3 2 1 (1 / 2) (prop5Short_holds 3 1 (1 / 2))
    (prop8ZeroMode_holds 3 1 (1 / 2)) le_rfl le_rfl one_pos (by norm_num)
  refine ⟨C, hC, by simp [ekDelta0], ?_⟩
  exact H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (995 / 1000) (999 / 1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) Complex.I Complex.norm_I
    (by rw [Complex.I_im]; norm_num) ![true, false] Finset.univ (fun i _ => Finset.mem_univ i)
    (ekDelta0 2 3 5)

/-- `n = 3`, `σ = (+,+,-)`, `A = {1, 2}` the two sign-change indices (index `0` is same-sign). -/
example :
    haveI : NeZero 5 := ⟨by norm_num⟩
    ∃ C : ℝ, 0 < C ∧ ekDelta0 3 3 5 0 ≠ 0 ∧
      ‖zeroModeSet 3 5 ({1, 2} : Finset (Fin 3))
          (UN 3 5 (1 / 2 : ℝ) (EKsgn Complex.I ![true, true, false]) (995 / 1000) (999 / 1000)
            (ekDelta0 3 3 5))‖ ≤ C * ‖ekDelta0 3 3 5‖ := by
  obtain ⟨C, hC, H⟩ := ekSumDecayNonzero_holds 3 3 1 (1 / 2) (prop5Short_holds 3 1 (1 / 2))
    (prop8ZeroMode_holds 3 1 (1 / 2)) le_rfl (by norm_num) one_pos (by norm_num)
  refine ⟨C, hC, by simp [ekDelta0], ?_⟩
  exact H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (995 / 1000) (999 / 1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) Complex.I Complex.norm_I
    (by rw [Complex.I_im]; norm_num) ![true, true, false] ({1, 2} : Finset (Fin 3))
    (by decide) (ekDelta0 3 3 5)

end Instances

end RBM
