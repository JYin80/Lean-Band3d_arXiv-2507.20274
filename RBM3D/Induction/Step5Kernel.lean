/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step5Pins
import RBM3D.Induction.TailtoTail
import RBM3D.Kernel.Evolution
import RBM3D.Propagator.Props4
import RBM3D.Propagator.Prop5Hold
import RBM3D.Evolution.PropTInf
import RBM3D.Defs.Tail

/-!
# S5-14 (ST-4): the kernel facts of the Duhamel step of Step 5 (`3_5:1983-2065`)

Deterministic facts on `Θ^{(+,-)}_t = Theta d L g t` and the profile `W^{-d} 𝒯̃^L_{u,D}`
(`STprof`, `tailW` with `ℓ = L`, the `L^∞` distance `zdistInf`), the inputs of S5-15, S5-16,
S5-26, S5-27.  The paper writes `≺` and `≲`; here the constants are explicit.

* `(eq:decompU)` (`3_5:1983`): `step5Kernel_decompU`, `step5Kernel_UN_decompU`;
* `(eq:THETAinftinf)`: merged `RBM.norm_Theta_le` (`Propagator/Props4.lean`) and its row-sum form
  `RBM.sum_norm_Theta_row_le`; nothing is restated (`step5Kernel_row_sum_inst`);
* `(uwp2-92kj)` (`3_5:2048-2053`): `step5Kernel_profile_explicit_holds` (the two terms kept
  explicitly) and `step5Kernel_profile_holds` (the floor `(1-u)/(1-t) W^{-D}` absorbed under
  `(1-u)/(1-t) ≤ W^θ`, `D ↦ D - θ`; the paper's `D - 1` is `θ = 1`);
* `step5Kernel_profile_not_unconditional`: the floor hypothesis cannot be dropped (compiled
  negative statement, `d = 3`, `g = 1/2`, `W = 2`, `D = 2`, `u = 0`, `t = 1 - 1/(4L²)`);
* `(uwftgwesj)` (`3_5:2055-2058`): `step5Kernel_calA` (`(eq:def_calA5)`, `3_5:2010-2015`),
  `step5Kernel_calA_holds` (under `(1-s)/(1-t) ≤ W^θ`, `D ↦ D - 2θ`),
  `step5Kernel_calA_explicit_holds` (no such hypothesis) and `step5Kernel_calA_sup_holds` (the
  maximum over `u ∈ [s,t]` as a `sSup`).

## Differences from the paper (paper-delta candidates, see the report)

* the constants of `(uwp2-92kj)`, `(uwftgwesj)` depend on `(d, Λ)`, `0 < g ≤ Λ`
  (`prop5Decay_holds`), not on `d` alone;
* `(TTT2)` (`ekPropTInf_holds`) needs `g²/L² ≤ 1 - t ∨ 1 - u ≤ g²/L²`, a hypothesis here;
* the floor term `(1-u)/(1-t) W^{-D}` is `≤ 𝒯̃_{t,D-1}` only if `(1-u)/(1-t) ≤ W`; this is a
  hypothesis `(1-u)/(1-t) ≤ W^θ` (resp. `(1-s)/(1-t) ≤ W^θ`), with `D - θ`, `D - 2θ`.
-/

set_option linter.style.longLine false

namespace RBM

open Matrix

/-! ### 1. `(eq:decompU)` -/

section Decomp

variable {d L : ℕ} [NeZero L] {g : ℝ}

/-- **`(eq:decompU)`** (`3_5:1983`): `(1 - s μ S)/(1 - t μ S) = s/t + ((t-s)/t) Θ_t`, as an identity
of one-index kernels (`μ = m(σ₁) m(σ₂)`, `‖μ‖ = 1`, `Θ_t = Theta (t μ)`); `s` is free. -/
theorem step5Kernel_decompU (hL : 3 ≤ L) {μ : ℂ} (hμ : ‖μ‖ = 1) {s t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) :
    uKer d L g μ s t = ((s / t : ℝ) : ℂ) • (1 : Matrix (Zd d L) (Zd d L) ℂ)
      + (((t - s) / t : ℝ) : ℂ) • Theta d L g ((t : ℂ) * μ) := by
  have hξ : ‖(t : ℂ) * μ‖ < 1 := norm_t_mul_lt_one ht0.le ht1 hμ
  have h := mul_Theta_of_three_le (d := d) (g := g) hL hξ
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  have hsplit : (1 - ((s : ℂ) * μ) • SB d L g)
      = ((s / t : ℝ) : ℂ) • (1 - ((t : ℂ) * μ) • SB d L g)
        + (((t - s) / t : ℝ) : ℂ) • (1 : Matrix (Zd d L) (Zd d L) ℂ) := by
    push_cast
    match_scalars <;> field_simp
    ring
  rw [uKer, hsplit, add_mul, smul_mul_assoc, h, smul_mul_assoc, one_mul]

/-- `(eq:decompU)` inside the merged `UN` (`(def_Ustz)`): every index factor of `𝒰^{(n)}_{s,t,σ}` is
`s/t + ((t-s)/t) Θ_{t μ_i}`. -/
theorem step5Kernel_UN_decompU (hL : 3 ≤ L) {n : ℕ} {m : Fin n → ℂ} (hm : ∀ i, ‖m i‖ = 1)
    {s t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (A : (Fin n → Zd d L) → ℂ) (a : Fin n → Zd d L) :
    UN d L g m s t A a
      = ∑ b : Fin n → Zd d L, (∏ i, ((((s / t : ℝ) : ℂ) • (1 : Matrix (Zd d L) (Zd d L) ℂ)
          + (((t - s) / t : ℝ) : ℂ) • Theta d L g ((t : ℂ) * cycProd m i)) (a i) (b i))) * A b := by
  unfold UN
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [step5Kernel_decompU hL (norm_cycProd hm i) ht0 ht1]

end Decomp

/-! ### 2. Helpers: the `L^∞` distance, the profile, the decay of `Θ` -/

section Profile

variable {d L : ℕ} [NeZero L] {g : ℝ}

private theorem step5Ker_zdistInf_neg (x : Zd d L) :
    Gauss.zdistInf d L (-x) = Gauss.zdistInf d L x := by
  unfold Gauss.zdistInf
  exact Finset.sup_congr rfl fun i _ => by simp [zdist_neg]

private theorem step5Ker_zdistInf_sub_comm (a b : Zd d L) :
    Gauss.zdistInf d L (a - b) = Gauss.zdistInf d L (b - a) := by
  rw [← neg_sub, step5Ker_zdistInf_neg]

omit [NeZero L] in
private theorem step5Ker_zdistInf_le_L (x : Zd d L) : ((Gauss.zdistInf d L x : ℕ) : ℝ) ≤ L := by
  have : Gauss.zdistInf d L x ≤ L := Finset.sup_le fun i _ => zdist_le_L (x i)
  exact_mod_cast this

omit [NeZero L] in
/-- `𝒯̃^L_{t,D}(|x|_∞) = max(𝒯_t(|x|_∞), W^{-D})`: `|x|_∞ ≤ L`, so `r ∧ L = r`. -/
private theorem step5Ker_tailW_eq (g t W D : ℝ) (x : Zd d L) :
    tailW d L g t (L : ℝ) W D (Gauss.zdistInf d L x : ℕ)
      = max (tailT d L g t (Gauss.zdistInf d L x : ℕ)) (W ^ (-D)) := by
  unfold tailW
  rw [min_eq_left (step5Ker_zdistInf_le_L x)]

/-- `Θ^{(+,-)}_{t,ab}` is real and `≥ 0`, so its norm is its real part. -/
theorem step5Kernel_norm_Theta_eq_re (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (a b : Zd d L) :
    ‖Theta d L g (t : ℂ) a b‖ = (Theta d L g (t : ℂ) a b).re := by
  have h := Theta_real_eq (g := g) hL ht0 ht1 a b
  have h0 := Theta_real_nonneg (g := g) hL ht0 ht1 a b
  conv_lhs => rw [h]
  rw [Complex.norm_real, Real.norm_of_nonneg h0]

private theorem step5Ker_sq_aux {c : ℝ} (hc : 0 < c) (s : ℝ) : s ≤ c * s ^ 2 + 1 / (4 * c) := by
  have h4 : 0 < 4 * c := by positivity
  rw [← sub_nonneg]
  have e : c * s ^ 2 + 1 / (4 * c) - s = (2 * c * s - 1) ^ 2 / (4 * c) := by
    field_simp
    ring
  rw [e]
  positivity

/-- `(prop:ThfadC)` in the `L^∞` form: `|Θ_{t,ab}| ≤ C₆ 𝒯_t(|b-a|_∞)`, `C₆ = C₆(d, Λ)`,
`0 < g ≤ Λ` (`prop5Decay_holds`, then `zdistInf ≤ zdistD` and `e^{-c x} ≤ e^{1/(4c)} e^{-√x}`). -/
theorem step5Kernel_theta_decay (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g t : ℝ, 0 < g → g ≤ Λ → 0 ≤ t → t < 1 →
      ∀ a b : Zd d L,
        ‖Theta d L g (t : ℂ) a b‖ ≤ C * tailT d L g t (Gauss.zdistInf d L (b - a) : ℕ) := by
  obtain ⟨C₅, hC₅, c₅, hc₅, H⟩ := prop5Decay_holds d Λ hd hΛ
  refine ⟨C₅ * Real.exp (1 / (4 * c₅)), by positivity, ?_⟩
  intro L _ hL g t hg hgΛ ht0 ht1 a b
  have hξ : ‖(t : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_of_nonneg ht0]
  have hshift : Theta d L g (t : ℂ) a b = Theta d L g (t : ℂ) 0 (b - a) := by
    have := Theta_apply_add_right_of_three_le (d := d) (g := g) hL hξ 0 (b - a) a
    rwa [zero_add, sub_add_cancel] at this
  have hP := H L hL g hg hgΛ t ht0 ht1 1 (by simp) true false (b - a)
  have hspin : PropSpin (1 : ℂ) true * PropSpin (1 : ℂ) false = 1 := by simp [PropSpin]
  rw [hspin, mul_one] at hP
  rw [hshift]
  refine hP.trans ?_
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hℓ : 0 < ellT L g t := ellT_pos hL1
  generalize b - a = x
  have hρD : ((Gauss.zdistInf d L x : ℕ) : ℝ) ≤ (zdistD d L x : ℕ) := by
    exact_mod_cast Gauss.zdistInf_le_zdistD d L x
  have hB : Bparam d L g t (zdistD d L x)
      ≤ BparamR d L g t ((Gauss.zdistInf d L x : ℕ) : ℝ) := by
    rw [← BparamR_natCast]
    exact BparamR_antitone (Nat.cast_nonneg _) hρD
  have hy0 : 0 ≤ ((Gauss.zdistInf d L x : ℕ) : ℝ) / ellT L g t :=
    div_nonneg (Nat.cast_nonneg _) hℓ.le
  have hexp1 : -c₅ * ((zdistD d L x : ℕ) : ℝ) / ellT L g t
      ≤ -(c₅ * (((Gauss.zdistInf d L x : ℕ) : ℝ) / ellT L g t)) := by
    have h1 : c₅ * (((Gauss.zdistInf d L x : ℕ) : ℝ) / ellT L g t)
        ≤ c₅ * ((zdistD d L x : ℕ) : ℝ) / ellT L g t := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hρD hc₅.le) hℓ.le
    have e : -c₅ * ((zdistD d L x : ℕ) : ℝ) / ellT L g t
        = -(c₅ * ((zdistD d L x : ℕ) : ℝ) / ellT L g t) := by ring
    linarith
  have hsq := step5Ker_sq_aux hc₅ (Real.sqrt (((Gauss.zdistInf d L x : ℕ) : ℝ) / ellT L g t))
  rw [Real.sq_sqrt hy0] at hsq
  have hexp : Real.exp (-c₅ * ((zdistD d L x : ℕ) : ℝ) / ellT L g t)
      ≤ Real.exp (1 / (4 * c₅)) *
        Real.exp (-Real.sqrt (((Gauss.zdistInf d L x : ℕ) : ℝ) / ellT L g t)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hT : tailT d L g t ((Gauss.zdistInf d L x : ℕ) : ℝ)
      = BparamR d L g t ((Gauss.zdistInf d L x : ℕ) : ℝ) *
        Real.exp (-Real.sqrt (((Gauss.zdistInf d L x : ℕ) : ℝ) / ellT L g t)) := rfl
  rw [hT]
  calc C₅ * Bparam d L g t (zdistD d L x) * Real.exp (-c₅ * ((zdistD d L x : ℕ) : ℝ) / ellT L g t)
      ≤ C₅ * BparamR d L g t ((Gauss.zdistInf d L x : ℕ) : ℝ) *
          (Real.exp (1 / (4 * c₅)) *
            Real.exp (-Real.sqrt (((Gauss.zdistInf d L x : ℕ) : ℝ) / ellT L g t))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hB hC₅.le) hexp (Real.exp_pos _).le
          (mul_nonneg hC₅.le (BparamR_nonneg (Nat.cast_nonneg _)))
    _ = C₅ * Real.exp (1 / (4 * c₅)) *
          (BparamR d L g t ((Gauss.zdistInf d L x : ℕ) : ℝ) *
            Real.exp (-Real.sqrt (((Gauss.zdistInf d L x : ℕ) : ℝ) / ellT L g t))) := by ring

/-! ### 3. `(uwp2-92kj)` -/

/-- **`(uwp2-92kj)`, explicit form** (`3_5:2048-2053`): for `0 ≤ u ≤ t < 1`, `0 < g ≤ Λ`, `3 ≤ d`,
`3 ≤ L`, `g²/L² ≤ 1-t ∨ 1-u ≤ g²/L²` (the hypothesis of `(TTT2)`), `W > 0`:
`(1-u) Σ_b |Θ^{(+,-)}_{t,a₁b}| 𝒯̃^L_{u,D}(|b-a₂|) ≤ C 𝒯_t(|a₁-a₂|) + (1-u)/(1-t) W^{-D}`,
`C = C(d, Λ)`.  The floor term is the row sum `Σ_b |Θ_{a₁b}| ≤ (1-t)⁻¹` (`(eq:THETAinftinf)`) times
`(1-u) W^{-D}`; the first term is `(prop:ThfadC)` and `(TTT2)`. -/
theorem step5Kernel_profile_explicit_holds (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g W D u t : ℝ, 0 < g → g ≤ Λ → 0 < W → 0 ≤ u → u ≤ t →
        t < 1 → (g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t ∨ 1 - u ≤ g ^ 2 / (L : ℝ) ^ 2) →
        ∀ a₁ a₂ : Zd d L,
          (1 - u) * ∑ b : Zd d L, ‖Theta d L g (t : ℂ) a₁ b‖ *
              tailW d L g u (L : ℝ) W D (Gauss.zdistInf d L (b - a₂) : ℕ)
            ≤ C * tailT d L g t (Gauss.zdistInf d L (a₁ - a₂) : ℕ)
              + (1 - u) / (1 - t) * W ^ (-D) := by
  obtain ⟨C₆, hC₆, hΘ⟩ := step5Kernel_theta_decay d Λ hd hΛ
  obtain ⟨CT, hCT, hT⟩ := ekPropTInf_holds d hd
  refine ⟨C₆ * CT, mul_pos hC₆ hCT, ?_⟩
  intro L _ hL g W D u t hg hgΛ hW hu hut ht hreg a₁ a₂
  have hv : 0 < 1 - u := by linarith
  have hw : 0 < 1 - t := by linarith
  have ht0 : 0 ≤ t := hu.trans hut
  have hWD : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  have hrow : ∑ b : Zd d L, ‖Theta d L g (t : ℂ) a₁ b‖ ≤ (1 - t)⁻¹ := by
    have := sum_norm_Theta_row_le (g := g) hL ht0 ht (m := (1 : ℂ)) (by simp) a₁
    simpa using this
  have hpt : ∀ b : Zd d L, ‖Theta d L g (t : ℂ) a₁ b‖ *
        tailW d L g u (L : ℝ) W D (Gauss.zdistInf d L (b - a₂) : ℕ)
      ≤ C₆ * (tailT d L g u (Gauss.zdistInf d L (a₂ - b) : ℕ) *
          tailT d L g t (Gauss.zdistInf d L (b - a₁) : ℕ)) + W ^ (-D) * ‖Theta d L g (t : ℂ) a₁ b‖ := by
    intro b
    have hTu0 : 0 ≤ tailT d L g u (Gauss.zdistInf d L (a₂ - b) : ℕ) :=
      tailT_nonneg (Nat.cast_nonneg _)
    have hmax : tailW d L g u (L : ℝ) W D (Gauss.zdistInf d L (b - a₂) : ℕ)
        ≤ tailT d L g u (Gauss.zdistInf d L (a₂ - b) : ℕ) + W ^ (-D) := by
      rw [step5Ker_tailW_eq, step5Ker_zdistInf_sub_comm b a₂]
      exact max_le (le_add_of_nonneg_right hWD) (le_add_of_nonneg_left hTu0)
    have hθ := hΘ L hL g t hg hgΛ ht0 ht a₁ b
    calc ‖Theta d L g (t : ℂ) a₁ b‖ *
          tailW d L g u (L : ℝ) W D (Gauss.zdistInf d L (b - a₂) : ℕ)
        ≤ ‖Theta d L g (t : ℂ) a₁ b‖ *
          (tailT d L g u (Gauss.zdistInf d L (a₂ - b) : ℕ) + W ^ (-D)) :=
          mul_le_mul_of_nonneg_left hmax (norm_nonneg _)
      _ = ‖Theta d L g (t : ℂ) a₁ b‖ * tailT d L g u (Gauss.zdistInf d L (a₂ - b) : ℕ)
          + W ^ (-D) * ‖Theta d L g (t : ℂ) a₁ b‖ := by ring
      _ ≤ C₆ * tailT d L g t (Gauss.zdistInf d L (b - a₁) : ℕ) *
            tailT d L g u (Gauss.zdistInf d L (a₂ - b) : ℕ)
          + W ^ (-D) * ‖Theta d L g (t : ℂ) a₁ b‖ :=
          add_le_add_left (mul_le_mul_of_nonneg_right hθ hTu0) _
      _ = _ := by ring
  have hsum : ∑ b : Zd d L, ‖Theta d L g (t : ℂ) a₁ b‖ *
        tailW d L g u (L : ℝ) W D (Gauss.zdistInf d L (b - a₂) : ℕ)
      ≤ C₆ * ∑ b : Zd d L, tailT d L g u (Gauss.zdistInf d L (a₂ - b) : ℕ) *
          tailT d L g t (Gauss.zdistInf d L (b - a₁) : ℕ)
        + W ^ (-D) * ∑ b : Zd d L, ‖Theta d L g (t : ℂ) a₁ b‖ := by
    calc _ ≤ ∑ b : Zd d L, (C₆ * (tailT d L g u (Gauss.zdistInf d L (a₂ - b) : ℕ) *
          tailT d L g t (Gauss.zdistInf d L (b - a₁) : ℕ))
          + W ^ (-D) * ‖Theta d L g (t : ℂ) a₁ b‖) := Finset.sum_le_sum fun b _ => hpt b
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hS := hT L g u t hg hu hut ht hreg a₂ a₁
  rw [step5Ker_zdistInf_sub_comm a₂ a₁] at hS
  have hS' : (1 - u) * ∑ b : Zd d L, tailT d L g u (Gauss.zdistInf d L (a₂ - b) : ℕ) *
          tailT d L g t (Gauss.zdistInf d L (b - a₁) : ℕ)
      ≤ CT * tailT d L g t (Gauss.zdistInf d L (a₁ - a₂) : ℕ) := by
    calc _ ≤ (1 - u) * (CT / (1 - u) * tailT d L g t (Gauss.zdistInf d L (a₁ - a₂) : ℕ)) :=
          mul_le_mul_of_nonneg_left hS hv.le
      _ = _ := by field_simp
  calc (1 - u) * ∑ b : Zd d L, ‖Theta d L g (t : ℂ) a₁ b‖ *
          tailW d L g u (L : ℝ) W D (Gauss.zdistInf d L (b - a₂) : ℕ)
      ≤ (1 - u) * (C₆ * ∑ b : Zd d L, tailT d L g u (Gauss.zdistInf d L (a₂ - b) : ℕ) *
            tailT d L g t (Gauss.zdistInf d L (b - a₁) : ℕ)
          + W ^ (-D) * ∑ b : Zd d L, ‖Theta d L g (t : ℂ) a₁ b‖) :=
        mul_le_mul_of_nonneg_left hsum hv.le
    _ = C₆ * ((1 - u) * ∑ b : Zd d L, tailT d L g u (Gauss.zdistInf d L (a₂ - b) : ℕ) *
            tailT d L g t (Gauss.zdistInf d L (b - a₁) : ℕ))
          + (1 - u) * (W ^ (-D) * ∑ b : Zd d L, ‖Theta d L g (t : ℂ) a₁ b‖) := by ring
    _ ≤ C₆ * (CT * tailT d L g t (Gauss.zdistInf d L (a₁ - a₂) : ℕ))
          + (1 - u) * (W ^ (-D) * (1 - t)⁻¹) :=
        add_le_add (mul_le_mul_of_nonneg_left hS' hC₆.le)
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrow hWD) hv.le)
    _ = C₆ * CT * tailT d L g t (Gauss.zdistInf d L (a₁ - a₂) : ℕ)
          + (1 - u) / (1 - t) * W ^ (-D) := by
        rw [div_eq_mul_inv]; ring

/-- **`(uwp2-92kj)`** (`3_5:2048-2053`), the paper's last `≲` made explicit: under
`(1-u)/(1-t) ≤ W^θ` (the paper's `(1-u)/(1-t) W^{-D} ≤ W^{-(D-1)}` is `θ = 1`),
`(1-u) Σ_b |Θ^{(+,-)}_{t,a₁b}| 𝒯̃^L_{u,D}(|b-a₂|) ≤ C 𝒯̃^L_{t,D-θ}(|a₁-a₂|)`, `C = C(d, Λ)`,
`0 < g ≤ Λ`, `0 ≤ u ≤ t < 1`, `g²/L² ≤ 1-t ∨ 1-u ≤ g²/L²`.  Without a hypothesis of this kind the
claim fails (`(1-u)/(1-t) W^{-D}` is not `≲ 𝒯̃_{t,D-1}` when `(1-t) W ≪ 1`). -/
theorem step5Kernel_profile_holds (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g W D θ u t : ℝ, 0 < g → g ≤ Λ → 0 < W → 0 ≤ u → u ≤ t →
        t < 1 → (g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t ∨ 1 - u ≤ g ^ 2 / (L : ℝ) ^ 2) →
        (1 - u) / (1 - t) ≤ W ^ θ → ∀ a₁ a₂ : Zd d L,
          (1 - u) * ∑ b : Zd d L, ‖Theta d L g (t : ℂ) a₁ b‖ *
              tailW d L g u (L : ℝ) W D (Gauss.zdistInf d L (b - a₂) : ℕ)
            ≤ C * tailW d L g t (L : ℝ) W (D - θ) (Gauss.zdistInf d L (a₁ - a₂) : ℕ) := by
  obtain ⟨C, hC, H⟩ := step5Kernel_profile_explicit_holds d Λ hd hΛ
  refine ⟨C + 1, by linarith, ?_⟩
  intro L _ hL g W D θ u t hg hgΛ hW hu hut ht hreg hfl a₁ a₂
  have h1 := H L hL g W D u t hg hgΛ hW hu hut ht hreg a₁ a₂
  have hWD : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  have hX : tailT d L g t (Gauss.zdistInf d L (a₁ - a₂) : ℕ)
      ≤ tailW d L g t (L : ℝ) W (D - θ) (Gauss.zdistInf d L (a₁ - a₂) : ℕ) := by
    rw [step5Ker_tailW_eq]; exact le_max_left _ _
  have hF : (1 - u) / (1 - t) * W ^ (-D)
      ≤ tailW d L g t (L : ℝ) W (D - θ) (Gauss.zdistInf d L (a₁ - a₂) : ℕ) := by
    rw [step5Ker_tailW_eq]
    refine le_trans ?_ (le_max_right _ _)
    calc (1 - u) / (1 - t) * W ^ (-D) ≤ W ^ θ * W ^ (-D) :=
          mul_le_mul_of_nonneg_right hfl hWD
      _ = W ^ (-(D - θ)) := by
          rw [← Real.rpow_add hW]; congr 1; ring
  calc _ ≤ _ := h1
    _ ≤ C * tailW d L g t (L : ℝ) W (D - θ) (Gauss.zdistInf d L (a₁ - a₂) : ℕ)
          + tailW d L g t (L : ℝ) W (D - θ) (Gauss.zdistInf d L (a₁ - a₂) : ℕ) :=
        add_le_add (mul_le_mul_of_nonneg_left hX hC.le) hF
    _ = _ := by ring

omit [NeZero L] in
/-- `𝒯_u(r) ≤ 𝒯_t(r)` for `u ≤ t < 1`, `r ≥ 0`: `B_{u,r} ≤ B_{t,r}` and `ℓ_u ≤ ℓ_t`. -/
private theorem step5Ker_tailT_mono (hg : 0 ≤ g) (hL1 : (1 : ℝ) ≤ L) {u t : ℝ} (hut : u ≤ t)
    (ht : t < 1) {r : ℝ} (hr : 0 ≤ r) : tailT d L g u r ≤ tailT d L g t r := by
  unfold tailT BparamR
  have hv : 0 < 1 - u := by linarith
  have hw : 0 < 1 - t := by linarith
  rw [abs_of_pos hv, abs_of_pos hw]
  have hℓ : ellT L g u ≤ ellT L g t := ellT_mono hg hut ht
  have hℓu : 0 < ellT L g u := ellT_pos hL1
  have hL0 : (0 : ℝ) < L := by linarith
  have hA : (g ^ 2 + (1 - u))⁻¹ ≤ (g ^ 2 + (1 - t))⁻¹ := inv_anti₀ (by positivity) (by linarith)
  have hZ : ((L : ℝ) ^ d * (1 - u))⁻¹ ≤ ((L : ℝ) ^ d * (1 - t))⁻¹ :=
    inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have hP : 0 ≤ ((r + 1) ^ (d - 2))⁻¹ := by positivity
  have hE : Real.exp (-Real.sqrt (r / ellT L g u)) ≤ Real.exp (-Real.sqrt (r / ellT L g t)) :=
    Real.exp_le_exp.mpr (neg_le_neg (Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hr hℓu hℓ)))
  have hB : (g ^ 2 + (1 - u))⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - u))⁻¹
      ≤ (g ^ 2 + (1 - t))⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - t))⁻¹ :=
    add_le_add (mul_le_mul_of_nonneg_right hA hP) hZ
  have hBt : 0 ≤ (g ^ 2 + (1 - t))⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - t))⁻¹ := by
    positivity
  exact mul_le_mul hB hE (Real.exp_pos _).le hBt

omit [NeZero L] in
/-- `𝒯̃^L_{u,D}(r) ≤ 𝒯̃^L_{t,D}(r)` for `u ≤ t < 1`, `r ≥ 0`. -/
private theorem step5Ker_tailW_mono_time (hg : 0 ≤ g) (hL1 : (1 : ℝ) ≤ L) {u t W D : ℝ}
    (hut : u ≤ t) (ht : t < 1) {r : ℝ} (hr : 0 ≤ r) :
    tailW d L g u (L : ℝ) W D r ≤ tailW d L g t (L : ℝ) W D r :=
  max_le_max (step5Ker_tailT_mono hg hL1 hut ht (le_min hr (by linarith))) le_rfl

omit [NeZero L] in
/-- `W^{-D} ≤ W^{-(D-θ)}` when `W^θ ≥ 1`: `𝒯̃_{t,D} ≤ 𝒯̃_{t,D-θ}`. -/
private theorem step5Ker_tailW_sub {g t ℓ W D θ r : ℝ} (hW : 0 < W) (hθ : 1 ≤ W ^ θ) :
    tailW d L g t ℓ W D r ≤ tailW d L g t ℓ W (D - θ) r := by
  refine max_le_max le_rfl ?_
  calc W ^ (-D) = W ^ (-D) * 1 := (mul_one _).symm
    _ ≤ W ^ (-D) * W ^ θ := mul_le_mul_of_nonneg_left hθ (Real.rpow_nonneg hW.le _)
    _ = W ^ (-(D - θ)) := by rw [← Real.rpow_add hW]; congr 1; ring

/-- **The floor hypothesis of `step5Kernel_profile_holds` cannot be dropped** (the paper's last `≲` of
`(uwp2-92kj)`, with `D - 1` and a constant independent of `L`, is false): at `d = 3`, `g = 1/2`
(`Λ = 1/2`), `W = 2`, `D = 2`, `u = 0`, `t = 1 - 1/(4L²)` (so `g²/L² = 1 - t`, `(TTT2)` case (i)),
`a₁ = a₂ = 0`, every hypothesis of `step5Kernel_profile_holds` holds except
`(1-u)/(1-t) = 4L² ≤ W^θ = 2`, and for every `C` the inequality
`(1-u) Σ_b |Θ_{t,a₁b}| 𝒯̃^L_{u,D}(|b-a₂|) ≤ C 𝒯̃^L_{t,D-1}(|a₁-a₂|)` fails for some `L`
(left side `≥ L²`, right side `≤ 8 |C|`). -/
theorem step5Kernel_profile_not_unconditional (C : ℝ) :
    ∃ L : ℕ, ∃ _ : NeZero L, 3 ≤ L ∧
      (0 ≤ 1 - 1 / (4 * (L : ℝ) ^ 2) ∧ 1 - 1 / (4 * (L : ℝ) ^ 2) < 1 ∧
        (1 / 2 : ℝ) ^ 2 / (L : ℝ) ^ 2 ≤ 1 - (1 - 1 / (4 * (L : ℝ) ^ 2)) ∧
        (2 : ℝ) ^ (1 : ℝ) < (1 - 0 : ℝ) / (1 - (1 - 1 / (4 * (L : ℝ) ^ 2)))) ∧
      C * tailW 3 L (1 / 2 : ℝ) (1 - 1 / (4 * (L : ℝ) ^ 2)) (L : ℝ) (2 : ℝ) (2 - 1 : ℝ)
          (Gauss.zdistInf 3 L ((0 : Zd 3 L) - 0) : ℕ)
        < (1 - 0 : ℝ) * ∑ b : Zd 3 L,
            ‖Theta 3 L (1 / 2 : ℝ) (((1 - 1 / (4 * (L : ℝ) ^ 2) : ℝ)) : ℂ) 0 b‖ *
              tailW 3 L (1 / 2 : ℝ) 0 (L : ℝ) (2 : ℝ) (2 : ℝ) (Gauss.zdistInf 3 L (b - 0) : ℕ) := by
  obtain ⟨L, hL3, hLC⟩ : ∃ L : ℕ, 3 ≤ L ∧ 8 * |C| + 1 ≤ (L : ℝ) :=
    ⟨max 3 ⌈8 * |C| + 1⌉₊, le_max_left _ _,
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 3 ⌈8 * |C| + 1⌉₊)⟩
  have hNZ : NeZero L := ⟨by omega⟩
  refine ⟨L, hNZ, hL3, ?_⟩
  have hL3r : (3 : ℝ) ≤ L := by exact_mod_cast hL3
  have hL0 : (0 : ℝ) < L := by linarith
  have hLL : (0 : ℝ) < 4 * (L : ℝ) ^ 2 := by positivity
  set t : ℝ := 1 - 1 / (4 * (L : ℝ) ^ 2) with htdef
  have hε : 1 - t = 1 / (4 * (L : ℝ) ^ 2) := by rw [htdef]; ring
  have hε0 : 0 < 1 - t := by rw [hε]; positivity
  have hεle : 1 / (4 * (L : ℝ) ^ 2) ≤ 1 := by
    rw [div_le_one hLL]; nlinarith
  have ht0 : 0 ≤ t := by rw [htdef]; linarith
  have ht1 : t < 1 := by linarith
  have hg2 : (1 / 2 : ℝ) ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t := by
    rw [hε]; apply le_of_eq; field_simp; norm_num
  have hfl : (2 : ℝ) ^ (1 : ℝ) < (1 - 0 : ℝ) / (1 - t) := by
    rw [Real.rpow_one, sub_zero, hε, one_div_one_div]
    nlinarith
  refine ⟨⟨ht0, ht1, hg2, hfl⟩, ?_⟩
  -- left side: at least `L²`
  have hrow : ∑ b : Zd 3 L, ‖Theta 3 L (1 / 2 : ℝ) (t : ℂ) 0 b‖ = (1 - t)⁻¹ := by
    rw [← sum_Theta_real_row (g := 1 / 2) hL3 ht0 ht1 0]
    exact Finset.sum_congr rfl fun b _ => step5Kernel_norm_Theta_eq_re hL3 ht0 ht1 0 b
  have hq : (2 : ℝ) ^ (-(2 : ℝ)) = 1 / 4 := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_two]; norm_num
  have hlow : (1 / 4 : ℝ) * (1 - t)⁻¹
      ≤ ∑ b : Zd 3 L, ‖Theta 3 L (1 / 2 : ℝ) (t : ℂ) 0 b‖ *
          tailW 3 L (1 / 2 : ℝ) 0 (L : ℝ) (2 : ℝ) (2 : ℝ) (Gauss.zdistInf 3 L (b - 0) : ℕ) := by
    calc (1 / 4 : ℝ) * (1 - t)⁻¹
        = ∑ b : Zd 3 L, ‖Theta 3 L (1 / 2 : ℝ) (t : ℂ) 0 b‖ * (1 / 4 : ℝ) := by
          rw [← Finset.sum_mul, hrow]; ring
      _ ≤ _ := Finset.sum_le_sum fun b _ => by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [← hq]
          exact rpow_neg_le_tailW _
  have hLsq : (L : ℝ) ^ 2 = (1 / 4 : ℝ) * (1 - t)⁻¹ := by
    rw [hε]; field_simp
  -- right side: at most `8`
  have hzero : Gauss.zdistInf 3 L ((0 : Zd 3 L) - 0) = 0 := by
    simp [Gauss.zdistInf]
  have hB : tailT 3 L (1 / 2 : ℝ) t 0 ≤ 8 := by
    rw [tailT_zero]
    unfold Bparam
    rw [abs_of_pos hε0, hε]
    have h1 : ((1 / 2 : ℝ) ^ 2 + 1 / (4 * (L : ℝ) ^ 2))⁻¹ ≤ 4 := by
      have hpos : (0 : ℝ) < 1 / (4 * (L : ℝ) ^ 2) := by positivity
      calc ((1 / 2 : ℝ) ^ 2 + 1 / (4 * (L : ℝ) ^ 2))⁻¹ ≤ ((1 / 2 : ℝ) ^ 2)⁻¹ :=
            inv_anti₀ (by norm_num) (by linarith)
        _ = 4 := by norm_num
    have h2 : ((L : ℝ) ^ 3 * (1 / (4 * (L : ℝ) ^ 2)))⁻¹ ≤ 4 := by
      have h3 : ((L : ℝ) ^ 3 * (1 / (4 * (L : ℝ) ^ 2)))⁻¹ = 4 / (L : ℝ) := by
        field_simp
      rw [h3, div_le_iff₀ hL0]; linarith
    norm_num at h1 h2 ⊢
    linarith
  have hR : tailW 3 L (1 / 2 : ℝ) t (L : ℝ) (2 : ℝ) (2 - 1 : ℝ) 0 ≤ 8 := by
    unfold tailW
    refine max_le ?_ ?_
    · rw [min_eq_left (by exact_mod_cast Nat.zero_le L)]; exact hB
    · norm_num [Real.rpow_neg]
  have hR0 : 0 ≤ tailW 3 L (1 / 2 : ℝ) t (L : ℝ) (2 : ℝ) (2 - 1 : ℝ) 0 :=
    (tailW_pos (by norm_num) _).le
  rw [hzero, Nat.cast_zero, sub_zero, one_mul]
  calc C * tailW 3 L (1 / 2 : ℝ) t (L : ℝ) (2 : ℝ) (2 - 1 : ℝ) 0
      ≤ |C| * tailW 3 L (1 / 2 : ℝ) t (L : ℝ) (2 : ℝ) (2 - 1 : ℝ) 0 :=
        mul_le_mul_of_nonneg_right (le_abs_self C) hR0
    _ ≤ |C| * 8 := mul_le_mul_of_nonneg_left hR (abs_nonneg C)
    _ < (L : ℝ) ^ 2 := by nlinarith [abs_nonneg C]
    _ = (1 / 4 : ℝ) * (1 - t)⁻¹ := hLsq
    _ ≤ _ := hlow

end Profile

/-! ### 4. `(eq:def_calA5)` and `(uwftgwesj)` -/

namespace Gauss.Sizes

open RBM.Gauss

section CalA

variable {d : ℕ} (sz : Sizes d)

/-- `Θ^{(+,-)}_{t,ab}` at size index `n`, as a real number (it is real and `≥ 0`,
`step5Kernel_norm_Theta_eq_re`): `Theta d L g t` with `L = sz.L n`, `g = sz.lam n`. -/
noncomputable def step5Kernel_Th (n : ℕ) (t : ℝ) (a b : Zd d (sz.L n)) : ℝ :=
  (Theta d (sz.L n) (sz.lam n) (t : ℂ) a b).re

/-- **`𝒜_{u,t,a}`** of `(eq:def_calA5)` (`3_5:2010-2015`), `a = (a₁, a₂)`, with the profile
`W^{-d} 𝒯̃^L_{u,D}(|b-c|) = STprof sz n u D L b c` (`ℓ = L`, the `L^∞` distance):
`𝒜 = P_u(a₁,a₂) + (t-u) Σ_b [Θ_{a₁b} P_u(b,a₂) + P_u(a₁,b) Θ_{ba₂}]
  + (t-u)² Σ_{b₁b₂} Θ_{a₁b₁} P_u(b₁,b₂) Θ_{b₂a₂}`. -/
noncomputable def step5Kernel_calA (n : ℕ) (D u t : ℝ) (a : Fin 2 → Zd d (sz.L n)) : ℝ :=
  STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1)
    + (t - u) * ∑ b : Zd d (sz.L n),
        (step5Kernel_Th sz n t (a 0) b * STprof sz n u D ((sz.L n : ℕ) : ℝ) b (a 1)
          + STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) b * step5Kernel_Th sz n t b (a 1))
    + (t - u) ^ 2 * ∑ b₁ : Zd d (sz.L n), ∑ b₂ : Zd d (sz.L n),
        step5Kernel_Th sz n t (a 0) b₁ * STprof sz n u D ((sz.L n : ℕ) : ℝ) b₁ b₂ * step5Kernel_Th sz n t b₂ (a 1)

/-- `𝒯̃^L_{u,D}(|x|_∞)` at size index `n`. -/
private noncomputable def step5Ker_tw (n : ℕ) (u D : ℝ) (x : Zd d (sz.L n)) : ℝ :=
  tailW d (sz.L n) (sz.lam n) u ((sz.L n : ℕ) : ℝ) ((sz.W n : ℕ) : ℝ) D
    (zdistInf d (sz.L n) x : ℕ)

private theorem step5Ker_STprof_eq (n : ℕ) (u D : ℝ) (b c : Zd d (sz.L n)) :
    STprof sz n u D ((sz.L n : ℕ) : ℝ) b c
      = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * step5Ker_tw sz n u D (b - c) := rfl

private theorem step5Ker_tw_pos (n : ℕ) (u D : ℝ) (x : Zd d (sz.L n)) :
    0 < step5Ker_tw sz n u D x :=
  tailW_pos (by exact_mod_cast sz.W_pos n) _

private theorem step5Ker_tw_comm (n : ℕ) (u D : ℝ) (x y : Zd d (sz.L n)) :
    step5Ker_tw sz n u D (x - y) = step5Ker_tw sz n u D (y - x) := by
  unfold step5Ker_tw
  rw [step5Ker_zdistInf_sub_comm x y]

private theorem step5Ker_tw_mono_time (n : ℕ) {u t : ℝ} (D : ℝ) (hg : 0 ≤ sz.lam n) (hut : u ≤ t)
    (ht : t < 1) (x : Zd d (sz.L n)) :
    step5Ker_tw sz n u D x ≤ step5Ker_tw sz n t D x :=
  step5Ker_tailW_mono_time hg (by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n))
    hut ht (Nat.cast_nonneg _)

private theorem step5Ker_tw_sub (n : ℕ) (t D θ : ℝ) (hθ : 1 ≤ ((sz.W n : ℕ) : ℝ) ^ θ)
    (x : Zd d (sz.L n)) :
    step5Ker_tw sz n t D x ≤ step5Ker_tw sz n t (D - θ) x :=
  step5Ker_tailW_sub (by exact_mod_cast sz.W_pos n) hθ

private theorem step5Ker_Th_eq_norm (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 1)
    (x y : Zd d (sz.L n)) :
    step5Kernel_Th sz n t x y = ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) x y‖ :=
  (step5Kernel_norm_Theta_eq_re (sz.three_le_L n) ht0 ht x y).symm

private theorem step5Ker_Th_nonneg (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 1)
    (x y : Zd d (sz.L n)) : 0 ≤ step5Kernel_Th sz n t x y := by
  rw [step5Ker_Th_eq_norm sz n ht0 ht]
  exact norm_nonneg _

private theorem step5Ker_Th_symm (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 1)
    (x y : Zd d (sz.L n)) : step5Kernel_Th sz n t x y = step5Kernel_Th sz n t y x := by
  have hξ : ‖(t : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_of_nonneg ht0]
  have h := Theta_transpose_of_three_le (d := d) (g := sz.lam n) (sz.three_le_L n) hξ
  have h2 := congrFun (congrFun h x) y
  simp only [Matrix.transpose_apply] at h2
  unfold step5Kernel_Th
  rw [h2]

private theorem step5Ker_STprof_symm (n : ℕ) (u D : ℝ) (x y : Zd d (sz.L n)) :
    STprof sz n u D ((sz.L n : ℕ) : ℝ) x y = STprof sz n u D ((sz.L n : ℕ) : ℝ) y x := by
  rw [step5Ker_STprof_eq, step5Ker_STprof_eq, step5Ker_tw_comm]

/-- **`(uwftgwesj)`** (`3_5:2055-2058`): for `3 ≤ d`, `0 < g ≤ Λ` (`g = sz.lam n`),
`0 ≤ s ≤ u ≤ t < 1`, `g²/L² ≤ 1-t ∨ 1-s ≤ g²/L²` (the hypothesis of `(TTT2)` for every `u ∈ [s,t]`)
and `(1-s)/(1-t) ≤ W^θ` (the paper's `D-2` is `θ = 1`):
`𝒜_{u,t,a} ≤ C (1-s)/(1-t) · W^{-d} 𝒯̃^L_{t,D-2θ}(|a₁-a₂|)`, `C = (1 + C₃)²`, `C₃ = C₃(d, Λ)` the
constant of `step5Kernel_profile_holds`; for every `u ∈ [s,t]`, i.e. for the maximum over `[s,t]`
(`step5Kernel_calA_sup_holds`). -/
theorem step5Kernel_calA_holds (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (n : ℕ) (D θ s u t : ℝ), 0 < sz.lam n → sz.lam n ≤ Λ →
      0 ≤ s → s ≤ u → u ≤ t → t < 1 →
      (sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t
        ∨ 1 - s ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) →
      (1 - s) / (1 - t) ≤ ((sz.W n : ℕ) : ℝ) ^ θ →
      ∀ a : Fin 2 → Zd d (sz.L n),
        step5Kernel_calA sz n D u t a ≤ C * ((1 - s) / (1 - t)) *
          STprof sz n t (D - 2 * θ) ((sz.L n : ℕ) : ℝ) (a 0) (a 1) := by
  obtain ⟨C₃, hC₃, H3⟩ := step5Kernel_profile_holds d Λ hd hΛ
  refine ⟨(1 + C₃) ^ 2, by positivity, ?_⟩
  intro sz n D θ s u t hg hgΛ hs hsu hut ht hreg hfl a
  have hL : 3 ≤ sz.L n := sz.three_le_L n
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hu0 : 0 ≤ u := hs.trans hsu
  have ht0 : 0 ≤ t := hu0.trans hut
  have hv : 0 < 1 - u := by linarith
  have hw : 0 < 1 - t := by linarith
  have hρ1 : 1 ≤ (1 - s) / (1 - t) := (one_le_div hw).mpr (by linarith)
  have hWθ : 1 ≤ ((sz.W n : ℕ) : ℝ) ^ θ := hρ1.trans hfl
  have hu_fl : (1 - u) / (1 - t) ≤ ((sz.W n : ℕ) : ℝ) ^ θ :=
    (div_le_div_of_nonneg_right (by linarith) hw.le).trans hfl
  have hreg_u : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t
      ∨ 1 - u ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := hreg.imp_right fun h => by linarith
  have hreg_t : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t
      ∨ 1 - t ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := le_total _ _
  have hfl_t : (1 - t) / (1 - t) ≤ ((sz.W n : ℕ) : ℝ) ^ θ := by
    rw [div_self hw.ne']; exact hWθ
  have H3u : ∀ x y : Zd d (sz.L n), (1 - u) * ∑ b : Zd d (sz.L n),
        ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) x b‖ * step5Ker_tw sz n u D (b - y)
      ≤ C₃ * step5Ker_tw sz n t (D - θ) (x - y) := fun x y =>
    H3 (sz.L n) hL (sz.lam n) ((sz.W n : ℕ) : ℝ) D θ u t hg hgΛ hW hu0 hut ht hreg_u hu_fl x y
  have H3t : ∀ x y : Zd d (sz.L n), (1 - t) * ∑ b : Zd d (sz.L n),
        ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) x b‖ * step5Ker_tw sz n t (D - θ) (b - y)
      ≤ C₃ * step5Ker_tw sz n t (D - θ - θ) (x - y) := fun x y =>
    H3 (sz.L n) hL (sz.lam n) ((sz.W n : ℕ) : ℝ) (D - θ) θ t t hg hgΛ hW ht0 le_rfl ht hreg_t
      hfl_t x y
  have hTh := step5Ker_Th_eq_norm sz n ht0 ht
  have hTh0 := step5Ker_Th_nonneg sz n ht0 ht
  have hThs := step5Ker_Th_symm sz n ht0 ht
  have hPs := step5Ker_STprof_symm sz n
  have hWd : 0 < (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  -- one application of `(uwp2-92kj)` followed by the constant `W^{-d}`
  have hA2 : ∀ x y : Zd d (sz.L n),
      (t - u) * ∑ b : Zd d (sz.L n),
          step5Kernel_Th sz n t x b * STprof sz n u D ((sz.L n : ℕ) : ℝ) b y
        ≤ C₃ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * step5Ker_tw sz n t (D - θ) (x - y) := by
    intro x y
    have hS0 : 0 ≤ ∑ b : Zd d (sz.L n),
        ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) x b‖ * step5Ker_tw sz n u D (b - y) :=
      Finset.sum_nonneg fun b _ => mul_nonneg (norm_nonneg _) (step5Ker_tw_pos sz n u D _).le
    have hconv : ∑ b : Zd d (sz.L n), step5Kernel_Th sz n t x b * STprof sz n u D ((sz.L n : ℕ) : ℝ) b y
        = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ∑ b : Zd d (sz.L n),
            ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) x b‖ * step5Ker_tw sz n u D (b - y) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hTh, step5Ker_STprof_eq]
      ring
    rw [hconv]
    calc (t - u) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ∑ b : Zd d (sz.L n),
            ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) x b‖ * step5Ker_tw sz n u D (b - y))
        = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((t - u) * ∑ b : Zd d (sz.L n),
            ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) x b‖ * step5Ker_tw sz n u D (b - y)) := by ring
      _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((1 - u) * ∑ b : Zd d (sz.L n),
            ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) x b‖ * step5Ker_tw sz n u D (b - y)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hS0) hWd.le
      _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (C₃ * step5Ker_tw sz n t (D - θ) (x - y)) :=
          mul_le_mul_of_nonneg_left (H3u x y) hWd.le
      _ = _ := by ring
  -- the three terms of `𝒜`
  have hTT0 : 0 < step5Ker_tw sz n t (D - 2 * θ) (a 0 - a 1) := step5Ker_tw_pos sz n _ _ _
  have hX : step5Ker_tw sz n t (D - θ) (a 0 - a 1) ≤ step5Ker_tw sz n t (D - 2 * θ) (a 0 - a 1) := by
    have h := step5Ker_tw_sub sz n t (D - θ) θ hWθ (a 0 - a 1)
    rwa [show D - θ - θ = D - 2 * θ by ring] at h
  have hP1 : STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1)
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * step5Ker_tw sz n t (D - 2 * θ) (a 0 - a 1) := by
    rw [step5Ker_STprof_eq]
    refine mul_le_mul_of_nonneg_left ?_ hWd.le
    have h1 := step5Ker_tw_mono_time sz n D hg.le hut ht (a 0 - a 1)
    have h2 := step5Ker_tw_sub sz n t D θ hWθ (a 0 - a 1)
    have h3 := step5Ker_tw_sub sz n t (D - θ) θ hWθ (a 0 - a 1)
    rw [show D - θ - θ = D - 2 * θ by ring] at h3
    exact h1.trans (h2.trans h3)
  have hB2a := hA2 (a 0) (a 1)
  have hB2b : (t - u) * ∑ b : Zd d (sz.L n),
        STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) b * step5Kernel_Th sz n t b (a 1)
      ≤ C₃ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * step5Ker_tw sz n t (D - θ) (a 0 - a 1) := by
    have hsw : ∑ b : Zd d (sz.L n), STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) b * step5Kernel_Th sz n t b (a 1)
        = ∑ b : Zd d (sz.L n), step5Kernel_Th sz n t (a 1) b * STprof sz n u D ((sz.L n : ℕ) : ℝ) b (a 0) := by
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hPs u D (a 0) b, hThs b (a 1), mul_comm]
    rw [hsw]
    have h := hA2 (a 1) (a 0)
    rwa [step5Ker_tw_comm sz n t (D - θ) (a 1) (a 0)] at h
  have hB3 : (t - u) ^ 2 * ∑ b₁ : Zd d (sz.L n), ∑ b₂ : Zd d (sz.L n),
        step5Kernel_Th sz n t (a 0) b₁ * STprof sz n u D ((sz.L n : ℕ) : ℝ) b₁ b₂ * step5Kernel_Th sz n t b₂ (a 1)
      ≤ C₃ * C₃ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((1 - s) / (1 - t))
          * step5Ker_tw sz n t (D - 2 * θ) (a 0 - a 1) := by
    obtain ⟨F, hF⟩ : ∃ F : Zd d (sz.L n) → ℝ, ∀ b₂, F b₂ = ∑ b₁ : Zd d (sz.L n),
        step5Kernel_Th sz n t (a 0) b₁ * STprof sz n u D ((sz.L n : ℕ) : ℝ) b₁ b₂ := ⟨_, fun _ => rfl⟩
    have hform : ∑ b₁ : Zd d (sz.L n), ∑ b₂ : Zd d (sz.L n),
        step5Kernel_Th sz n t (a 0) b₁ * STprof sz n u D ((sz.L n : ℕ) : ℝ) b₁ b₂ * step5Kernel_Th sz n t b₂ (a 1)
        = ∑ b₂ : Zd d (sz.L n), F b₂ * step5Kernel_Th sz n t b₂ (a 1) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b₂ _ => ?_
      rw [hF, Finset.sum_mul]
    rw [hform]
    have hFb : ∀ b₂, (t - u) * F b₂
        ≤ C₃ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * step5Ker_tw sz n t (D - θ) (a 0 - b₂) := fun b₂ => by
      rw [hF]; exact hA2 (a 0) b₂
    have h1 : (t - u) * ∑ b₂ : Zd d (sz.L n), F b₂ * step5Kernel_Th sz n t b₂ (a 1)
        ≤ ∑ b₂ : Zd d (sz.L n), (C₃ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹
            * step5Ker_tw sz n t (D - θ) (a 0 - b₂)) * step5Kernel_Th sz n t b₂ (a 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun b₂ _ => ?_
      calc (t - u) * (F b₂ * step5Kernel_Th sz n t b₂ (a 1))
          = ((t - u) * F b₂) * step5Kernel_Th sz n t b₂ (a 1) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hFb b₂) (hTh0 _ _)
    have h2 : ∑ b₂ : Zd d (sz.L n), (C₃ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹
            * step5Ker_tw sz n t (D - θ) (a 0 - b₂)) * step5Kernel_Th sz n t b₂ (a 1)
        = C₃ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ∑ b₂ : Zd d (sz.L n),
            ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) (a 1) b₂‖ * step5Ker_tw sz n t (D - θ) (b₂ - a 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b₂ _ => ?_
      rw [hThs b₂ (a 1), hTh, step5Ker_tw_comm sz n t (D - θ) (a 0) b₂]
      ring
    have h3 : (1 - t) * ∑ b₂ : Zd d (sz.L n),
          ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) (a 1) b₂‖ * step5Ker_tw sz n t (D - θ) (b₂ - a 0)
        ≤ C₃ * step5Ker_tw sz n t (D - 2 * θ) (a 0 - a 1) := by
      have h := H3t (a 1) (a 0)
      rwa [show D - θ - θ = D - 2 * θ by ring, step5Ker_tw_comm sz n t (D - 2 * θ) (a 1) (a 0)] at h
    have hSig : ∑ b₂ : Zd d (sz.L n),
          ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) (a 1) b₂‖ * step5Ker_tw sz n t (D - θ) (b₂ - a 0)
        ≤ C₃ * step5Ker_tw sz n t (D - 2 * θ) (a 0 - a 1) / (1 - t) := by
      rw [le_div_iff₀ hw]; linarith
    have htu : (t - u) / (1 - t) ≤ (1 - s) / (1 - t) :=
      div_le_div_of_nonneg_right (by linarith) hw.le
    have hcc : 0 ≤ C₃ * C₃ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * step5Ker_tw sz n t (D - 2 * θ) (a 0 - a 1) := by
      positivity
    calc (t - u) ^ 2 * ∑ b₂ : Zd d (sz.L n), F b₂ * step5Kernel_Th sz n t b₂ (a 1)
        = (t - u) * ((t - u) * ∑ b₂ : Zd d (sz.L n), F b₂ * step5Kernel_Th sz n t b₂ (a 1)) := by ring
      _ ≤ (t - u) * (C₃ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ∑ b₂ : Zd d (sz.L n),
            ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) (a 1) b₂‖ * step5Ker_tw sz n t (D - θ) (b₂ - a 0)) :=
          mul_le_mul_of_nonneg_left (h1.trans h2.le) (by linarith)
      _ ≤ (t - u) * (C₃ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹
            * (C₃ * step5Ker_tw sz n t (D - 2 * θ) (a 0 - a 1) / (1 - t))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSig (by positivity)) (by linarith)
      _ = C₃ * C₃ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * step5Ker_tw sz n t (D - 2 * θ) (a 0 - a 1)
            * ((t - u) / (1 - t)) := by
          field_simp
      _ ≤ C₃ * C₃ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * step5Ker_tw sz n t (D - 2 * θ) (a 0 - a 1)
            * ((1 - s) / (1 - t)) := mul_le_mul_of_nonneg_left htu hcc
      _ = _ := by ring
  -- assembly
  unfold step5Kernel_calA
  rw [Finset.sum_add_distrib, mul_add, step5Ker_STprof_eq sz n t (D - 2 * θ) (a 0) (a 1)]
  set TT := step5Ker_tw sz n t (D - 2 * θ) (a 0 - a 1) with hTT
  set Wd := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ with hWdd
  set ρ := (1 - s) / (1 - t) with hρ
  have hQ : 0 ≤ Wd * TT := by positivity
  have hQ1 : Wd * TT ≤ ρ * (Wd * TT) := le_mul_of_one_le_left hQ hρ1
  have hXa : C₃ * Wd * step5Ker_tw sz n t (D - θ) (a 0 - a 1) ≤ C₃ * (ρ * (Wd * TT)) := by
    calc C₃ * Wd * step5Ker_tw sz n t (D - θ) (a 0 - a 1) ≤ C₃ * Wd * TT :=
          mul_le_mul_of_nonneg_left hX (by positivity)
      _ = C₃ * (Wd * TT) := by ring
      _ ≤ C₃ * (ρ * (Wd * TT)) := mul_le_mul_of_nonneg_left hQ1 hC₃.le
  calc _ ≤ Wd * TT + (C₃ * (ρ * (Wd * TT)) + C₃ * (ρ * (Wd * TT)))
        + C₃ * C₃ * Wd * ρ * TT := by linarith
    _ ≤ ρ * (Wd * TT) + (C₃ * (ρ * (Wd * TT)) + C₃ * (ρ * (Wd * TT)))
        + C₃ * C₃ * Wd * ρ * TT := by linarith
    _ = (1 + C₃) ^ 2 * ρ * (Wd * TT) := by ring

/-- `𝒯_t(|x|_∞)` at size index `n`. -/
private noncomputable def step5Ker_tT (n : ℕ) (t : ℝ) (x : Zd d (sz.L n)) : ℝ :=
  tailT d (sz.L n) (sz.lam n) t (zdistInf d (sz.L n) x : ℕ)

private theorem step5Ker_tT_nonneg (n : ℕ) (t : ℝ) (x : Zd d (sz.L n)) :
    0 ≤ step5Ker_tT sz n t x :=
  tailT_nonneg (Nat.cast_nonneg _)

private theorem step5Ker_tT_comm (n : ℕ) (t : ℝ) (x y : Zd d (sz.L n)) :
    step5Ker_tT sz n t (x - y) = step5Ker_tT sz n t (y - x) := by
  unfold step5Ker_tT
  rw [step5Ker_zdistInf_sub_comm x y]

private theorem step5Ker_tT_mono_time (n : ℕ) {u t : ℝ} (hg : 0 ≤ sz.lam n) (hut : u ≤ t)
    (ht : t < 1) (x : Zd d (sz.L n)) :
    step5Ker_tT sz n u x ≤ step5Ker_tT sz n t x :=
  step5Ker_tailT_mono hg (by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n))
    hut ht (Nat.cast_nonneg _)

private theorem step5Ker_tw_le_add (n : ℕ) (u D : ℝ) (x : Zd d (sz.L n)) :
    step5Ker_tw sz n u D x ≤ step5Ker_tT sz n u x + ((sz.W n : ℕ) : ℝ) ^ (-D) := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  unfold step5Ker_tw step5Ker_tT
  rw [step5Ker_tailW_eq]
  exact max_le (le_add_of_nonneg_right (Real.rpow_nonneg hW.le _))
    (le_add_of_nonneg_left (tailT_nonneg (Nat.cast_nonneg _)))

private theorem step5Ker_tT_le_tw (n : ℕ) (u D : ℝ) (x : Zd d (sz.L n)) :
    step5Ker_tT sz n u x ≤ step5Ker_tw sz n u D x := by
  unfold step5Ker_tw step5Ker_tT
  rw [step5Ker_tailW_eq]
  exact le_max_left _ _

/-- **`(uwftgwesj)`, explicit form** (no hypothesis on `(1-t) W`): for `3 ≤ d`, `0 < g ≤ Λ`,
`0 ≤ s ≤ u ≤ t < 1`, `g²/L² ≤ 1-t ∨ 1-s ≤ g²/L²`, with `R = (1-s)/(1-t)`:
`𝒜_{u,t,a} ≤ C R · W^{-d} [𝒯_t(|a₁-a₂|) + R W^{-D}]`, `C = (1 + C₃)² + C₃ + 4`.  Under
`R ≤ W^θ` it implies the form of `step5Kernel_calA_holds` with the constant doubled
(`R W^{-D} ≤ W^{-(D-θ)} ≤ W^{-(D-2θ)}`, `𝒯_t ≤ 𝒯̃_{t,D-2θ}`). -/
theorem step5Kernel_calA_explicit_holds (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (n : ℕ) (D s u t : ℝ), 0 < sz.lam n → sz.lam n ≤ Λ →
      0 ≤ s → s ≤ u → u ≤ t → t < 1 →
      (sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t
        ∨ 1 - s ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) →
      ∀ a : Fin 2 → Zd d (sz.L n),
        step5Kernel_calA sz n D u t a ≤ C * ((1 - s) / (1 - t)) *
          ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
            (tailT d (sz.L n) (sz.lam n) t ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)
              + (1 - s) / (1 - t) * ((sz.W n : ℕ) : ℝ) ^ (-D))) := by
  obtain ⟨C₃, hC₃, H3⟩ := step5Kernel_profile_explicit_holds d Λ hd hΛ
  refine ⟨(1 + C₃) ^ 2 + C₃ + 4, by positivity, ?_⟩
  intro sz n D s u t hg hgΛ hs hsu hut ht hreg a
  have hL : 3 ≤ sz.L n := sz.three_le_L n
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hu0 : 0 ≤ u := hs.trans hsu
  have ht0 : 0 ≤ t := hu0.trans hut
  have hv : 0 < 1 - u := by linarith
  have hw : 0 < 1 - t := by linarith
  have hρ1 : 1 ≤ (1 - s) / (1 - t) := (one_le_div hw).mpr (by linarith)
  have hu_R : (1 - u) / (1 - t) ≤ (1 - s) / (1 - t) :=
    div_le_div_of_nonneg_right (by linarith) hw.le
  have hreg_u : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t
      ∨ 1 - u ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := hreg.imp_right fun h => by linarith
  have hreg_t : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t
      ∨ 1 - t ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := le_total _ _
  have hF0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW.le _
  have hWd : 0 < (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  have H3u : ∀ x y : Zd d (sz.L n), (1 - u) * ∑ b : Zd d (sz.L n),
        ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) x b‖ * step5Ker_tw sz n u D (b - y)
      ≤ C₃ * step5Ker_tT sz n t (x - y) + (1 - u) / (1 - t) * ((sz.W n : ℕ) : ℝ) ^ (-D) :=
    fun x y => H3 (sz.L n) hL (sz.lam n) ((sz.W n : ℕ) : ℝ) D u t hg hgΛ hW hu0 hut ht hreg_u x y
  have H3t : ∀ x y : Zd d (sz.L n), (1 - t) * ∑ b : Zd d (sz.L n),
        ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) x b‖ * step5Ker_tw sz n t D (b - y)
      ≤ C₃ * step5Ker_tT sz n t (x - y) + (1 - t) / (1 - t) * ((sz.W n : ℕ) : ℝ) ^ (-D) :=
    fun x y => H3 (sz.L n) hL (sz.lam n) ((sz.W n : ℕ) : ℝ) D t t hg hgΛ hW ht0 le_rfl ht hreg_t
      x y
  have hTh := step5Ker_Th_eq_norm sz n ht0 ht
  have hTh0 := step5Ker_Th_nonneg sz n ht0 ht
  have hThs := step5Ker_Th_symm sz n ht0 ht
  have hPs := step5Ker_STprof_symm sz n
  have hrow : ∀ x : Zd d (sz.L n),
      ∑ b : Zd d (sz.L n), ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) x b‖ ≤ (1 - t)⁻¹ := fun x => by
    have := sum_norm_Theta_row_le (d := d) (L := sz.L n) (g := sz.lam n) hL ht0 ht
      (m := (1 : ℂ)) (by simp) x
    simpa using this
  -- one application of `(uwp2-92kj)` (explicit form) followed by the constant `W^{-d}`
  have hA2 : ∀ x y : Zd d (sz.L n),
      (t - u) * ∑ b : Zd d (sz.L n),
          step5Kernel_Th sz n t x b * STprof sz n u D ((sz.L n : ℕ) : ℝ) b y
        ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (C₃ * step5Ker_tT sz n t (x - y)
            + (1 - s) / (1 - t) * ((sz.W n : ℕ) : ℝ) ^ (-D)) := by
    intro x y
    have hS0 : 0 ≤ ∑ b : Zd d (sz.L n),
        ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) x b‖ * step5Ker_tw sz n u D (b - y) :=
      Finset.sum_nonneg fun b _ => mul_nonneg (norm_nonneg _) (step5Ker_tw_pos sz n u D _).le
    have hconv : ∑ b : Zd d (sz.L n), step5Kernel_Th sz n t x b * STprof sz n u D ((sz.L n : ℕ) : ℝ) b y
        = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ∑ b : Zd d (sz.L n),
            ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) x b‖ * step5Ker_tw sz n u D (b - y) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hTh, step5Ker_STprof_eq]
      ring
    rw [hconv]
    calc (t - u) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ∑ b : Zd d (sz.L n),
            ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) x b‖ * step5Ker_tw sz n u D (b - y))
        = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((t - u) * ∑ b : Zd d (sz.L n),
            ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) x b‖ * step5Ker_tw sz n u D (b - y)) := by ring
      _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((1 - u) * ∑ b : Zd d (sz.L n),
            ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) x b‖ * step5Ker_tw sz n u D (b - y)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hS0) hWd.le
      _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (C₃ * step5Ker_tT sz n t (x - y)
            + (1 - u) / (1 - t) * ((sz.W n : ℕ) : ℝ) ^ (-D)) :=
          mul_le_mul_of_nonneg_left (H3u x y) hWd.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl
          (mul_le_mul_of_nonneg_right hu_R hF0)) hWd.le
  -- the three terms of `𝒜`
  have hP1 : STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1)
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (step5Ker_tT sz n t (a 0 - a 1)
          + ((sz.W n : ℕ) : ℝ) ^ (-D)) := by
    rw [step5Ker_STprof_eq]
    refine mul_le_mul_of_nonneg_left ?_ hWd.le
    have h1 := step5Ker_tw_le_add sz n u D (a 0 - a 1)
    have h2 := step5Ker_tT_mono_time sz n hg.le hut ht (a 0 - a 1)
    linarith
  have hB2a := hA2 (a 0) (a 1)
  have hB2b : (t - u) * ∑ b : Zd d (sz.L n),
        STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) b * step5Kernel_Th sz n t b (a 1)
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (C₃ * step5Ker_tT sz n t (a 0 - a 1)
            + (1 - s) / (1 - t) * ((sz.W n : ℕ) : ℝ) ^ (-D)) := by
    have hsw : ∑ b : Zd d (sz.L n), STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) b * step5Kernel_Th sz n t b (a 1)
        = ∑ b : Zd d (sz.L n), step5Kernel_Th sz n t (a 1) b * STprof sz n u D ((sz.L n : ℕ) : ℝ) b (a 0) := by
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hPs u D (a 0) b, hThs b (a 1), mul_comm]
    rw [hsw]
    have h := hA2 (a 1) (a 0)
    rwa [step5Ker_tT_comm sz n t (a 1) (a 0)] at h
  have hB3 : (t - u) ^ 2 * ∑ b₁ : Zd d (sz.L n), ∑ b₂ : Zd d (sz.L n),
        step5Kernel_Th sz n t (a 0) b₁ * STprof sz n u D ((sz.L n : ℕ) : ℝ) b₁ b₂ * step5Kernel_Th sz n t b₂ (a 1)
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((1 - s) / (1 - t)) * (C₃ * (C₃ * step5Ker_tT sz n t (a 0 - a 1)
            + ((sz.W n : ℕ) : ℝ) ^ (-D)) + (1 - s) / (1 - t) * ((sz.W n : ℕ) : ℝ) ^ (-D)) := by
    obtain ⟨F, hF⟩ : ∃ F : Zd d (sz.L n) → ℝ, ∀ b₂, F b₂ = ∑ b₁ : Zd d (sz.L n),
        step5Kernel_Th sz n t (a 0) b₁ * STprof sz n u D ((sz.L n : ℕ) : ℝ) b₁ b₂ := ⟨_, fun _ => rfl⟩
    have hform : ∑ b₁ : Zd d (sz.L n), ∑ b₂ : Zd d (sz.L n),
        step5Kernel_Th sz n t (a 0) b₁ * STprof sz n u D ((sz.L n : ℕ) : ℝ) b₁ b₂ * step5Kernel_Th sz n t b₂ (a 1)
        = ∑ b₂ : Zd d (sz.L n), F b₂ * step5Kernel_Th sz n t b₂ (a 1) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b₂ _ => ?_
      rw [hF, Finset.sum_mul]
    rw [hform]
    have hFb : ∀ b₂, (t - u) * F b₂
        ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (C₃ * step5Ker_tT sz n t (a 0 - b₂)
            + (1 - s) / (1 - t) * ((sz.W n : ℕ) : ℝ) ^ (-D)) := fun b₂ => by
      rw [hF]; exact hA2 (a 0) b₂
    have h1 : (t - u) * ∑ b₂ : Zd d (sz.L n), F b₂ * step5Kernel_Th sz n t b₂ (a 1)
        ≤ ∑ b₂ : Zd d (sz.L n), ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (C₃ * step5Ker_tT sz n t (a 0 - b₂)
            + (1 - s) / (1 - t) * ((sz.W n : ℕ) : ℝ) ^ (-D))) * step5Kernel_Th sz n t b₂ (a 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun b₂ _ => ?_
      calc (t - u) * (F b₂ * step5Kernel_Th sz n t b₂ (a 1))
          = ((t - u) * F b₂) * step5Kernel_Th sz n t b₂ (a 1) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hFb b₂) (hTh0 _ _)
    have h2 : ∑ b₂ : Zd d (sz.L n), ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (C₃ * step5Ker_tT sz n t (a 0 - b₂)
            + (1 - s) / (1 - t) * ((sz.W n : ℕ) : ℝ) ^ (-D))) * step5Kernel_Th sz n t b₂ (a 1)
        = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * C₃ * ∑ b₂ : Zd d (sz.L n),
            ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) (a 1) b₂‖ * step5Ker_tT sz n t (b₂ - a 0)
          + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((1 - s) / (1 - t) * ((sz.W n : ℕ) : ℝ) ^ (-D))
            * ∑ b₂ : Zd d (sz.L n), ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) (a 1) b₂‖ := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b₂ _ => ?_
      rw [hThs b₂ (a 1), hTh, step5Ker_tT_comm sz n t (a 0) b₂]
      ring
    have hS1 : ∑ b₂ : Zd d (sz.L n),
          ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) (a 1) b₂‖ * step5Ker_tT sz n t (b₂ - a 0)
        ≤ (C₃ * step5Ker_tT sz n t (a 0 - a 1) + ((sz.W n : ℕ) : ℝ) ^ (-D)) / (1 - t) := by
      rw [le_div_iff₀ hw]
      have h := H3t (a 1) (a 0)
      rw [div_self hw.ne', one_mul, step5Ker_tT_comm sz n t (a 1) (a 0)] at h
      calc (∑ b₂ : Zd d (sz.L n),
            ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) (a 1) b₂‖ * step5Ker_tT sz n t (b₂ - a 0)) * (1 - t)
          = (1 - t) * ∑ b₂ : Zd d (sz.L n),
            ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) (a 1) b₂‖ * step5Ker_tT sz n t (b₂ - a 0) := by ring
        _ ≤ (1 - t) * ∑ b₂ : Zd d (sz.L n),
            ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) (a 1) b₂‖ * step5Ker_tw sz n t D (b₂ - a 0) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b₂ _ =>
            mul_le_mul_of_nonneg_left (step5Ker_tT_le_tw sz n t D _) (norm_nonneg _)) hw.le
        _ ≤ _ := h
    have hS0 := hrow (a 1)
    have hT0 := step5Ker_tT_nonneg sz n t (a 0 - a 1)
    have hRF : 0 ≤ (1 - s) / (1 - t) * ((sz.W n : ℕ) : ℝ) ^ (-D) :=
      mul_nonneg (by linarith) hF0
    have htu : (t - u) / (1 - t) ≤ (1 - s) / (1 - t) :=
      div_le_div_of_nonneg_right (by linarith) hw.le
    have hX : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (C₃ * (C₃ * step5Ker_tT sz n t (a 0 - a 1)
            + ((sz.W n : ℕ) : ℝ) ^ (-D)) + (1 - s) / (1 - t) * ((sz.W n : ℕ) : ℝ) ^ (-D)) := by
      positivity
    calc (t - u) ^ 2 * ∑ b₂ : Zd d (sz.L n), F b₂ * step5Kernel_Th sz n t b₂ (a 1)
        = (t - u) * ((t - u) * ∑ b₂ : Zd d (sz.L n), F b₂ * step5Kernel_Th sz n t b₂ (a 1)) := by ring
      _ ≤ (t - u) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * C₃ * ∑ b₂ : Zd d (sz.L n),
            ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) (a 1) b₂‖ * step5Ker_tT sz n t (b₂ - a 0)
          + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((1 - s) / (1 - t) * ((sz.W n : ℕ) : ℝ) ^ (-D))
            * ∑ b₂ : Zd d (sz.L n), ‖Theta d (sz.L n) (sz.lam n) (t : ℂ) (a 1) b₂‖) :=
          mul_le_mul_of_nonneg_left (h1.trans h2.le) (by linarith)
      _ ≤ (t - u) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * C₃
            * ((C₃ * step5Ker_tT sz n t (a 0 - a 1) + ((sz.W n : ℕ) : ℝ) ^ (-D)) / (1 - t))
          + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((1 - s) / (1 - t) * ((sz.W n : ℕ) : ℝ) ^ (-D))
            * (1 - t)⁻¹) :=
          mul_le_mul_of_nonneg_left (add_le_add
            (mul_le_mul_of_nonneg_left hS1 (by positivity))
            (mul_le_mul_of_nonneg_left hS0 (by positivity))) (by linarith)
      _ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (C₃ * (C₃ * step5Ker_tT sz n t (a 0 - a 1)
            + ((sz.W n : ℕ) : ℝ) ^ (-D)) + (1 - s) / (1 - t) * ((sz.W n : ℕ) : ℝ) ^ (-D))
            * ((t - u) / (1 - t)) := by
          field_simp
      _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (C₃ * (C₃ * step5Ker_tT sz n t (a 0 - a 1)
            + ((sz.W n : ℕ) : ℝ) ^ (-D)) + (1 - s) / (1 - t) * ((sz.W n : ℕ) : ℝ) ^ (-D))
            * ((1 - s) / (1 - t)) := mul_le_mul_of_nonneg_left htu hX
      _ = _ := by ring
  -- assembly
  unfold step5Kernel_calA
  rw [Finset.sum_add_distrib, mul_add]
  set T := step5Ker_tT sz n t (a 0 - a 1) with hT
  set Wd := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ with hWdd
  set R := (1 - s) / (1 - t) with hR
  set F := ((sz.W n : ℕ) : ℝ) ^ (-D) with hFdef
  have hT0 : 0 ≤ T := step5Ker_tT_nonneg sz n t _
  have hWT : 0 ≤ Wd * T := by positivity
  have hWF : 0 ≤ Wd * F := by positivity
  have e1 : 1 + 2 * C₃ + R * C₃ ^ 2 ≤ ((1 + C₃) ^ 2 + C₃ + 4) * R := by
    nlinarith [mul_le_mul_of_nonneg_left hρ1 (by positivity : (0 : ℝ) ≤ 5 + 3 * C₃)]
  have e2 : 1 + 2 * R + R * C₃ + R ^ 2 ≤ ((1 + C₃) ^ 2 + C₃ + 4) * R ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hρ1 (by positivity : (0 : ℝ) ≤ C₃), sq_nonneg C₃,
      mul_nonneg hC₃.le (sq_nonneg R), mul_nonneg hC₃.le (mul_nonneg hC₃.le (sq_nonneg R)),
      mul_le_mul hρ1 hρ1 zero_le_one (by linarith : (0 : ℝ) ≤ R)]
  calc _ ≤ Wd * (T + F) + (Wd * (C₃ * T + R * F) + Wd * (C₃ * T + R * F))
        + Wd * R * (C₃ * (C₃ * T + F) + R * F) := by linarith
    _ = Wd * T * (1 + 2 * C₃ + R * C₃ ^ 2) + Wd * F * (1 + 2 * R + R * C₃ + R ^ 2) := by ring
    _ ≤ Wd * T * (((1 + C₃) ^ 2 + C₃ + 4) * R) + Wd * F * (((1 + C₃) ^ 2 + C₃ + 4) * R ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left e1 hWT) (mul_le_mul_of_nonneg_left e2 hWF)
    _ = ((1 + C₃) ^ 2 + C₃ + 4) * R * (Wd * (T + R * F)) := by ring

/-- `(uwftgwesj)` for the maximum over `u ∈ [s,t]` of the paper: the supremum of
`u ↦ 𝒜_{u,t,a}` over `Set.Icc s t` is `≤ C (1-s)/(1-t) · W^{-d} 𝒯̃^L_{t,D-2θ}(|a₁-a₂|)`, with the
constant and the hypotheses of `step5Kernel_calA_holds` (`s ≤ t`). -/
theorem step5Kernel_calA_sup_holds (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (n : ℕ) (D θ s t : ℝ), 0 < sz.lam n → sz.lam n ≤ Λ →
      0 ≤ s → s ≤ t → t < 1 →
      (sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t
        ∨ 1 - s ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) →
      (1 - s) / (1 - t) ≤ ((sz.W n : ℕ) : ℝ) ^ θ →
      ∀ a : Fin 2 → Zd d (sz.L n),
        sSup ((fun u => step5Kernel_calA sz n D u t a) '' Set.Icc s t) ≤ C * ((1 - s) / (1 - t)) *
          STprof sz n t (D - 2 * θ) ((sz.L n : ℕ) : ℝ) (a 0) (a 1) := by
  obtain ⟨C, hC, H⟩ := step5Kernel_calA_holds d Λ hd hΛ
  refine ⟨C, hC, ?_⟩
  intro sz n D θ s t hg hgΛ hs hst ht hreg hfl a
  refine csSup_le ⟨_, Set.mem_image_of_mem _ (Set.left_mem_Icc.mpr hst)⟩ ?_
  rintro _ ⟨u, ⟨hsu, hut⟩, rfl⟩
  exact H sz n D θ s u t hg hgΛ hs hsu hut ht hreg hfl a

end CalA

end Gauss.Sizes

/-! ### 5. Compiled nonempty instances (CLAUDE.md §4 step 2)

`d = 3`, `L = 3`, `g = 1/2`, `W = 2`, `D = 2`, `θ = 1`, `Λ = 1/2`, `s = 0`, `u = 1/4`, `t = 1/2`.
Torus `Z_3^3` (27 points), `a = (0, e₁)`, `|a₁ - a₂|_∞ = 1`.  `g²/L² = 1/36 ≤ 1/2 = 1 - t`
(`(TTT2)` case (i)); `(1-u)/(1-t) = 3/2 ≤ 2 = W^1`; `(1-s)/(1-t) = 2 = W^1`. -/

section Instances

/-- The sizes of the instances: `L = 3`, `W = 2`, `ilambda = 1/2` for every `n`. -/
noncomputable def step5Kernel_instSz : Gauss.Sizes 3 where
  L := fun _ => 3
  W := fun _ => 2
  lam := fun _ => 1 / 2
  three_le_L := fun _ => le_rfl
  W_pos := fun _ => by norm_num

/-- Item 1, `(eq:decompU)`, at `μ = i` (`|μ| = 1`), `s = 1/4`, `t = 1/2`. -/
theorem step5Kernel_decompU_inst :
    uKer 3 3 (1 / 2 : ℝ) Complex.I (1 / 4 : ℝ) (1 / 2 : ℝ)
      = (((1 / 4 : ℝ) / (1 / 2 : ℝ) : ℝ) : ℂ) • (1 : Matrix (Zd 3 3) (Zd 3 3) ℂ)
        + ((((1 / 2 : ℝ) - (1 / 4 : ℝ)) / (1 / 2 : ℝ) : ℝ) : ℂ)
          • Theta 3 3 (1 / 2 : ℝ) (((1 / 2 : ℝ) : ℂ) * Complex.I) :=
  step5Kernel_decompU (by norm_num) Complex.norm_I (by norm_num) (by norm_num)

/-- Item 1 inside `UN`: `n = 2`, `m = (m(+), m(-)) = (i, ī)`, `s = 0`, `t = 1/2`, the tensor `A = 1`. -/
theorem step5Kernel_UN_decompU_inst :
    UN 3 3 (1 / 2 : ℝ) ![Complex.I, (starRingEnd ℂ) Complex.I] (0 : ℝ) (1 / 2 : ℝ)
        (fun _ : Fin 2 → Zd 3 3 => (1 : ℂ)) ![0, ![1, 0, 0]]
      = ∑ b : Fin 2 → Zd 3 3, (∏ i, ((((0 / (1 / 2) : ℝ) : ℂ) • (1 : Matrix (Zd 3 3) (Zd 3 3) ℂ)
          + ((((1 / 2 : ℝ) - 0) / (1 / 2) : ℝ) : ℂ) • Theta 3 3 (1 / 2 : ℝ)
            (((1 / 2 : ℝ) : ℂ) * cycProd ![Complex.I, (starRingEnd ℂ) Complex.I] i))
              (![0, ![1, 0, 0]] i) (b i))) * 1 :=
  step5Kernel_UN_decompU (by norm_num)
    (fun i => by fin_cases i <;> simp) (by norm_num) (by norm_num)
    (fun _ : Fin 2 → Zd 3 3 => (1 : ℂ)) ![0, ![1, 0, 0]]

open scoped Matrix.Norms.Operator in
/-- Item 2, `(eq:THETAinftinf)`, at the instance (merged `sum_norm_Theta_row_le`, `norm_Theta_le`):
the row sum of `Θ^{(σ)}_{1/2}` is `≤ (1 - 1/2)⁻¹ = 2`, for `μ = 1` and `μ = i`. -/
theorem step5Kernel_row_sum_inst :
    (∑ b : Zd 3 3, ‖Theta 3 3 (1 / 2 : ℝ) (((1 / 2 : ℝ) : ℂ) * 1) 0 b‖ ≤ (1 - 1 / 2 : ℝ)⁻¹)
    ∧ (∑ b : Zd 3 3, ‖Theta 3 3 (1 / 2 : ℝ) (((1 / 2 : ℝ) : ℂ) * Complex.I) 0 b‖
        ≤ (1 - 1 / 2 : ℝ)⁻¹)
    ∧ ‖Theta 3 3 (1 / 2 : ℝ) (((1 / 2 : ℝ) : ℂ) * Complex.I)‖ ≤ (1 - 1 / 2 : ℝ)⁻¹ :=
  ⟨sum_norm_Theta_row_le (by norm_num) (by norm_num) (by norm_num) (by simp) 0,
    sum_norm_Theta_row_le (by norm_num) (by norm_num) (by norm_num) Complex.norm_I 0,
    norm_Theta_le (by norm_num) (by norm_num) (by norm_num) Complex.norm_I⟩

/-- Item 3, `(uwp2-92kj)` with the floor absorbed (`D - θ = 1`), at `u = 1/4`, `t = 1/2`,
`a = (0, e₁)`. -/
theorem step5Kernel_profile_inst :
    ∃ C : ℝ, 0 < C ∧
      (1 - 1 / 4 : ℝ) * ∑ b : Zd 3 3, ‖Theta 3 3 (1 / 2 : ℝ) (((1 / 2 : ℝ)) : ℂ) 0 b‖ *
          tailW 3 3 (1 / 2 : ℝ) (1 / 4 : ℝ) ((3 : ℕ) : ℝ) (2 : ℝ) (2 : ℝ)
            (Gauss.zdistInf 3 3 (b - ![1, 0, 0]) : ℕ)
        ≤ C * tailW 3 3 (1 / 2 : ℝ) (1 / 2 : ℝ) ((3 : ℕ) : ℝ) (2 : ℝ) (2 - 1 : ℝ)
            (Gauss.zdistInf 3 3 ((0 : Zd 3 3) - ![1, 0, 0]) : ℕ) := by
  obtain ⟨C, hC, H⟩ := step5Kernel_profile_holds 3 (1 / 2) le_rfl (by norm_num)
  exact ⟨C, hC, H 3 (by norm_num) (1 / 2) 2 2 1 (1 / 4) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
    (by norm_num) 0 ![1, 0, 0]⟩

/-- Item 3, explicit-factor form, at the same data. -/
theorem step5Kernel_profile_explicit_inst :
    ∃ C : ℝ, 0 < C ∧
      (1 - 1 / 4 : ℝ) * ∑ b : Zd 3 3, ‖Theta 3 3 (1 / 2 : ℝ) (((1 / 2 : ℝ)) : ℂ) 0 b‖ *
          tailW 3 3 (1 / 2 : ℝ) (1 / 4 : ℝ) ((3 : ℕ) : ℝ) (2 : ℝ) (2 : ℝ)
            (Gauss.zdistInf 3 3 (b - ![1, 0, 0]) : ℕ)
        ≤ C * tailT 3 3 (1 / 2 : ℝ) (1 / 2 : ℝ)
            (Gauss.zdistInf 3 3 ((0 : Zd 3 3) - ![1, 0, 0]) : ℕ)
          + (1 - 1 / 4 : ℝ) / (1 - 1 / 2) * (2 : ℝ) ^ (-(2 : ℝ)) := by
  obtain ⟨C, hC, H⟩ := step5Kernel_profile_explicit_holds 3 (1 / 2) le_rfl (by norm_num)
  exact ⟨C, hC, H 3 (by norm_num) (1 / 2) 2 2 (1 / 4) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num)) 0 ![1, 0, 0]⟩

/-- Item 4, `(uwftgwesj)`, at `s = 0`, `u = 1/4`, `t = 1/2`, `a = (0, e₁)`; `sz = step5Kernel_instSz`. -/
theorem step5Kernel_calA_inst :
    ∃ C : ℝ, 0 < C ∧
      Gauss.Sizes.step5Kernel_calA step5Kernel_instSz 0 2 (1 / 4) (1 / 2) ![0, ![1, 0, 0]]
        ≤ C * ((1 - 0 : ℝ) / (1 - 1 / 2)) *
          Gauss.Sizes.STprof step5Kernel_instSz 0 (1 / 2) (2 - 2 * 1) ((step5Kernel_instSz.L 0 : ℕ) : ℝ)
            ((![0, ![1, 0, 0]] : Fin 2 → Zd 3 (step5Kernel_instSz.L 0)) 0)
            ((![0, ![1, 0, 0]] : Fin 2 → Zd 3 (step5Kernel_instSz.L 0)) 1) := by
  obtain ⟨C, hC, H⟩ := Gauss.Sizes.step5Kernel_calA_holds 3 (1 / 2) le_rfl (by norm_num)
  exact ⟨C, hC, H step5Kernel_instSz 0 2 1 0 (1 / 4) (1 / 2) (by norm_num [step5Kernel_instSz])
    (by norm_num [step5Kernel_instSz]) le_rfl (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by norm_num [step5Kernel_instSz])) (by norm_num [step5Kernel_instSz]) ![0, ![1, 0, 0]]⟩

/-- Item 4, explicit form (no hypothesis `(1-s)/(1-t) ≤ W^θ`), at the same data. -/
theorem step5Kernel_calA_explicit_inst :
    ∃ C : ℝ, 0 < C ∧
      Gauss.Sizes.step5Kernel_calA step5Kernel_instSz 0 2 (1 / 4) (1 / 2) ![0, ![1, 0, 0]]
        ≤ C * ((1 - 0 : ℝ) / (1 - 1 / 2)) *
          ((((step5Kernel_instSz.W 0 : ℕ) : ℝ) ^ 3)⁻¹ *
            (tailT 3 (step5Kernel_instSz.L 0) (step5Kernel_instSz.lam 0) (1 / 2)
                (Gauss.zdistInf 3 (step5Kernel_instSz.L 0)
                  (((![0, ![1, 0, 0]] : Fin 2 → Zd 3 (step5Kernel_instSz.L 0)) 0)
                    - ((![0, ![1, 0, 0]] : Fin 2 → Zd 3 (step5Kernel_instSz.L 0)) 1)) : ℕ)
              + (1 - 0 : ℝ) / (1 - 1 / 2) * ((step5Kernel_instSz.W 0 : ℕ) : ℝ) ^ (-(2 : ℝ)))) := by
  obtain ⟨C, hC, H⟩ := Gauss.Sizes.step5Kernel_calA_explicit_holds 3 (1 / 2) le_rfl (by norm_num)
  exact ⟨C, hC, H step5Kernel_instSz 0 2 0 (1 / 4) (1 / 2) (by norm_num [step5Kernel_instSz])
    (by norm_num [step5Kernel_instSz]) le_rfl (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by norm_num [step5Kernel_instSz])) ![0, ![1, 0, 0]]⟩

/-- Item 4, supremum form, at the same data (`u` ranges over `[0, 1/2]`). -/
theorem step5Kernel_calA_sup_inst :
    ∃ C : ℝ, 0 < C ∧
      sSup ((fun u => Gauss.Sizes.step5Kernel_calA step5Kernel_instSz 0 2 u (1 / 2) ![0, ![1, 0, 0]]) ''
          Set.Icc (0 : ℝ) (1 / 2))
        ≤ C * ((1 - 0 : ℝ) / (1 - 1 / 2)) *
          Gauss.Sizes.STprof step5Kernel_instSz 0 (1 / 2) (2 - 2 * 1) ((step5Kernel_instSz.L 0 : ℕ) : ℝ)
            ((![0, ![1, 0, 0]] : Fin 2 → Zd 3 (step5Kernel_instSz.L 0)) 0)
            ((![0, ![1, 0, 0]] : Fin 2 → Zd 3 (step5Kernel_instSz.L 0)) 1) := by
  obtain ⟨C, hC, H⟩ := Gauss.Sizes.step5Kernel_calA_sup_holds 3 (1 / 2) le_rfl (by norm_num)
  exact ⟨C, hC, H step5Kernel_instSz 0 2 1 0 (1 / 2) (by norm_num [step5Kernel_instSz])
    (by norm_num [step5Kernel_instSz]) le_rfl (by norm_num) (by norm_num)
    (Or.inl (by norm_num [step5Kernel_instSz])) (by norm_num [step5Kernel_instSz]) ![0, ![1, 0, 0]]⟩

end Instances

end RBM
