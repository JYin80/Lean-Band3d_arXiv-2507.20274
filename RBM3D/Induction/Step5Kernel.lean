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

end Profile

/-! ### 4. `(eq:def_calA5)` and `(uwftgwesj)` -/

/-! ### 5. Compiled nonempty instances (CLAUDE.md §4 step 2)

`d = 3`, `L = 3`, `g = 1/2`, `W = 2`, `D = 2`, `θ = 1`, `Λ = 1/2`, `s = 0`, `u = 1/4`, `t = 1/2`.
Torus `Z_3^3` (27 points), `a = (0, e₁)`, `|a₁ - a₂|_∞ = 1`.  `g²/L² = 1/36 ≤ 1/2 = 1 - t`
(`(TTT2)` case (i)); `(1-u)/(1-t) = 3/2 ≤ 2 = W^1`; `(1-s)/(1-t) = 2 = W^1`. -/

end RBM
