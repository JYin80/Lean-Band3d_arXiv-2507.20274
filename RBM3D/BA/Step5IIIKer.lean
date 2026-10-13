/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step5Gen
import RBM3D.Chain.Step2Kern
import RBM3D.BA.Step2BA
import RBM3D.BA.EKPins
import RBM3D.BA.KKernel
import RBM3D.BA.Prop5Short
import RBM3D.BA.Prop6Path
import RBM3D.BA.GreenSchur
import RBM3D.BA.GreenStab
import RBM3D.BA.EMn2BA
import RBM3D.BA.TwistStep2

/-!
# U5a, part 1: the kernel of Step 5, case (iii), at the block Anderson model (ticket T2481)

Paper: `(neiwuj)` `3_5:2344-2362` (`TailtoTail`; proof hint `3_5:2364`: `(sum_res_Ndecay)`,
`(prop:ThfadC)` and a basic calculus fact); BA: `7_8:2101` (omitted details, paper-delta T2459a).
Design `docs/reports/T2459-design.md` U5-1; probe `t/T2459:RBM3D/Probe/T2459Pins.lean`
(`:58`, `:84-91`, `:240-276`; never merged), copied under the stems `Step5IIIKer_`, `baStep5III_`.
No port from `../RBM1D` or `../RBM2D`.

1. `baStep5III_lam0_le_lam` (target 1): where `g₀ = BAflowLam0 > 0`, `g₀ ≤ g = sz.lam`
   (`TwistStep2_lam0_sq`).
2. `Step5IIIKer_uKer_weighted`: the weighted row sum of the one-index kernel
   `uKer = (1 - sM) Θ_t`, `Σ_x |u_{s,t}(a,x)| e^{k √|a-x|_∞} ≤ W_k (1-s)/(1-t)`, from
   `baProp5_holds` (`(prop:ThfadC)`, `Prop6Path:850`) with `ellT = 1` in the regime
   `g² ≤ 1 - t`, and `uKer = (s/t) 1 + (1 - s/t) Θ_t` (`BAuKer_convex`).  This is route (b) of
   the ticket: no weighted `K`-row sum (target 2 of the ticket is dropped).
3. `BAStep5IIIKernel`, `baStep5IIIKernel_holds`, `baStep5IIIKernel_at_flow` (target 3):
   `TailtoTail` on the one kernel `Step2Gen_UN` at `baFM`, `Cc = W_1²`, and its reading at the flow.
4. `baStep5III_Theta_far` (target 4 (a)): the Θ-level far field at mixed charges, from
   `baEMn2ExpHK`.
5. `baStep5III_uKer_far` (target 4 (b)): the `uKer`-level far field, all four charge pairs,
   beyond `ℓ* = (log W)^{3/2}`.
6. Compiled nonempty instances at `d = 3`, `sz0`, `zSeq`, `flow_sz0`.

Helpers carry the stem `Step5IIIKer_`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Matrix

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Lattice and real-analysis helpers -/

section Helpers

/-- `zdistInf (-x) = zdistInf x` (copy of the private `zdistInf_neg_eq`, `Induction/EMn2Poly.lean:446`). -/
theorem Step5IIIKer_zdistInf_neg (d L : ℕ) [NeZero L] (x : Zd d L) : zdistInf d L (-x) = zdistInf d L x := by
  unfold zdistInf
  exact Finset.sup_congr rfl fun i _ => by simp [zdist_neg]

theorem Step5IIIKer_zdistInf_add_le (d L : ℕ) [NeZero L] (x y : Zd d L) :
    zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y := by
  unfold zdistInf
  refine Finset.sup_le fun i _ => ?_
  exact (zdist_add_le L (x i) (y i)).trans (add_le_add
    (Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i))
    (Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i)))

/-- The triangle inequality for the periodic `L^∞` distance. -/
theorem Step5IIIKer_zdistInf_tri (d L : ℕ) [NeZero L] (x y w : Zd d L) :
    zdistInf d L (x - w) ≤ zdistInf d L (x - y) + zdistInf d L (y - w) := by
  have : x - w = (x - y) + (y - w) := by abel
  rw [this]; exact Step5IIIKer_zdistInf_add_le d L _ _

theorem Step5IIIKer_zdistInf_sub_comm (d L : ℕ) [NeZero L] (x y : Zd d L) :
    zdistInf d L (x - y) = zdistInf d L (y - x) := by
  rw [← neg_sub, Step5IIIKer_zdistInf_neg]

theorem Step5IIIKer_zdistInf_zero (d L : ℕ) : zdistInf d L (0 : Zd d L) = 0 := by
  unfold zdistInf
  exact Nat.eq_zero_of_le_zero (Finset.sup_le fun i _ => by simp)

/-- `√(x + y) ≤ √x + √y`. -/
theorem Step5IIIKer_sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sqrt_nonneg x, Real.sqrt_nonneg y, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

/-- The product of sums over two slots: `Σ_b Π_i f_i(b_i) = Π_i Σ_x f_i(x)`. -/
theorem Step5IIIKer_sum_prod {Z : Type*} [Fintype Z] (f : Fin 2 → Z → ℝ) :
    ∑ b : Fin 2 → Z, ∏ i, f i (b i) = ∏ i, ∑ x, f i x := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- `k √r ≤ (c/2) r + k²/(2c)` (AM-GM). -/
theorem Step5IIIKer_amgm {c k r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) :
    k * Real.sqrt r ≤ c / 2 * r + k ^ 2 / (2 * c) := by
  have h := Real.sq_sqrt hr
  have h0 : 0 ≤ c / 2 * (Real.sqrt r - k / c) ^ 2 := by positivity
  have e : c / 2 * (Real.sqrt r - k / c) ^ 2 = c / 2 * (Real.sqrt r) ^ 2 - k * Real.sqrt r + k ^ 2 / (2 * c) := by
    field_simp
    ring
  rw [h] at e
  linarith

end Helpers

/-! ## 2. The weighted row sums of `Θ_t` and of `uKer` (route (b): `(prop:ThfadC)` with `ℓ_t = 1`) -/

section Weighted

/-- In the regime `g² ≤ 1 - t` the effective range is `ℓ_t = 1` (`(eq:ellt)`). -/
theorem Step5IIIKer_ellT_eq_one {L : ℕ} {g t : ℝ} (hL : 1 ≤ L) (hg : 0 ≤ g) (ht : t < 1) (h : g ^ 2 ≤ 1 - t) :
    ellT L g t = 1 := by
  have h1t : 0 < 1 - t := by linarith
  have hs : g ≤ Real.sqrt |1 - t| := by
    rw [abs_of_pos h1t]
    exact Real.le_sqrt_of_sq_le h
  have hs0 : 0 < Real.sqrt |1 - t| := Real.sqrt_pos.mpr (abs_pos.mpr h1t.ne')
  have hdiv : g / Real.sqrt |1 - t| ≤ 1 := (div_le_one hs0).mpr hs
  unfold ellT
  rw [max_eq_right hdiv]
  exact min_eq_left (by exact_mod_cast hL)

/-- `B_{t,K} ≤ 2/(1 - t)` (both terms of `(eq_B_param)` are at most `(1-t)⁻¹`). -/
theorem Step5IIIKer_Bparam_le {d L : ℕ} (hL : 1 ≤ L) {g t : ℝ} (ht : t < 1) (K : ℕ) :
    Bparam d L g t K ≤ 2 / (1 - t) := by
  have h1t : 0 < 1 - t := by linarith
  have hab : |1 - t| = 1 - t := abs_of_pos h1t
  unfold Bparam
  rw [hab]
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hL)
  have hK1 : (1 : ℝ) ≤ ((K : ℝ) + 1) ^ (d - 2) := one_le_pow₀ (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)])
  have h1 : (g ^ 2 + (1 - t))⁻¹ * (((K : ℝ) + 1) ^ (d - 2))⁻¹ ≤ (1 - t)⁻¹ := by
    have a1 : (g ^ 2 + (1 - t))⁻¹ ≤ (1 - t)⁻¹ := inv_anti₀ h1t (by nlinarith [sq_nonneg g])
    have a2 : (((K : ℝ) + 1) ^ (d - 2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK1
    calc _ ≤ (1 - t)⁻¹ * 1 := mul_le_mul a1 a2 (by positivity) (by positivity)
      _ = _ := mul_one _
  have h2 : ((L : ℝ) ^ d * (1 - t))⁻¹ ≤ (1 - t)⁻¹ := by
    apply inv_anti₀ h1t
    nlinarith
  calc _ ≤ (1 - t)⁻¹ + (1 - t)⁻¹ := add_le_add h1 h2
    _ = 2 / (1 - t) := by ring

/-- **Entrywise decay of `Θ_t`** (`(prop:ThfadC)` = `baProp5_holds`, `Prop6Path:850`, with `ℓ_t = 1` in the regime `g² ≤ 1 - t` and
`B_{t,K} ≤ 2/(1 - t)`): `|Θ_t(a,x)| ≤ 2C (1-t)⁻¹ e^{-c |a-x|_1}`, `C, c` depending on `(d, Λ, κ)` only, every charge pair. -/
theorem Step5IIIKer_theta_entry (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
      haveI : NeZero L := ⟨by omega⟩
      BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → g ^ 2 ≤ 1 - t → ∀ σ₁ σ₂ : Bool, ∀ a x : Zd d L,
        ‖BATheta d L g E m t σ₁ σ₂ a x‖ ≤ 2 * C / (1 - t) * Real.exp (-(c * (zdistD d L (a - x) : ℝ))) := by
  obtain ⟨C, hC, c, hc, H⟩ := baProp5_holds d Λ κ hd hΛ hκ
  refine ⟨C, c, hC, hc, ?_⟩
  intro L hL g hg hgΛ E m hr t ht0 ht1 hgt σ₁ σ₂ a x
  have : NeZero L := ⟨by omega⟩
  have hell := Step5IIIKer_ellT_eq_one (L := L) (by omega) hg.le ht1 hgt
  have hshift : BATheta d L g E m t σ₁ σ₂ a x = BATheta d L g E m t σ₁ σ₂ 0 (x - a) := by
    have := baP8_BATheta_shift (d := d) (L := L) g E m t σ₁ σ₂ a x (-a)
    rw [add_neg_cancel, ← sub_eq_add_neg] at this
    exact this.symm
  have hdist : zdistD d L (x - a) = zdistD d L (a - x) := by rw [← neg_sub, zdistD_neg]
  have h5 := H L hL g hg hgΛ E m hr t ht0 ht1 σ₁ σ₂ (x - a)
  rw [hdist, hell, div_one] at h5
  rw [hshift]
  have hB0 : 0 ≤ Bparam d L g t (zdistD d L (a - x)) := by unfold Bparam; positivity
  have hBle := Step5IIIKer_Bparam_le (d := d) (L := L) (g := g) (by omega) ht1 (zdistD d L (a - x))
  calc _ ≤ C * Bparam d L g t (zdistD d L (a - x)) * Real.exp (-c * (zdistD d L (a - x) : ℝ)) := h5
    _ ≤ C * (2 / (1 - t)) * Real.exp (-c * (zdistD d L (a - x) : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBle hC.le) (Real.exp_pos _).le
    _ = 2 * C / (1 - t) * Real.exp (-(c * (zdistD d L (a - x) : ℝ))) := by rw [neg_mul]; ring

/-- **Weighted row sum of `Θ_t`**: for `g² ≤ 1 - t`, `Σ_x |Θ_t(a,x)| e^{k √|a-x|_∞} ≤ V_k (1-t)⁻¹`, `V_k = V_k(d, Λ, κ)`. -/
theorem Step5IIIKer_theta_weighted (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) (k : ℝ) (hk : 0 ≤ k) :
    ∃ V : ℝ, 0 < V ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
      haveI : NeZero L := ⟨by omega⟩
      BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → g ^ 2 ≤ 1 - t → ∀ σ₁ σ₂ : Bool, ∀ a : Zd d L,
        ∑ x, ‖BATheta d L g E m t σ₁ σ₂ a x‖ * Real.exp (k * Real.sqrt (zdistInf d L (a - x))) ≤ V * (1 - t)⁻¹ := by
  obtain ⟨C, c, hC, hc, H⟩ := Step5IIIKer_theta_entry d hd Λ κ hΛ hκ
  have hc2 : 0 < c / 2 := by positivity
  have hS : 0 < RBM.expC (d - 2) (c / 2) := by
    unfold RBM.expC
    positivity
  refine ⟨2 * C * Real.exp (k ^ 2 / (2 * c)) * RBM.expC (d - 2) (c / 2), by positivity, ?_⟩
  intro L hL g hg hgΛ E m hr t ht0 ht1 hgt σ₁ σ₂ a
  have : NeZero L := ⟨by omega⟩
  have h1t : 0 < 1 - t := by linarith
  have hterm : ∀ x : Zd d L, ‖BATheta d L g E m t σ₁ σ₂ a x‖ * Real.exp (k * Real.sqrt (zdistInf d L (a - x))) ≤
      2 * C / (1 - t) * Real.exp (k ^ 2 / (2 * c)) * Real.exp (-((c / 2) * (zdistD d L (a - x) : ℝ))) := by
    intro x
    have h5 := H L hL g hg hgΛ E m hr t ht0 ht1 hgt σ₁ σ₂ a x
    set r : ℝ := (zdistD d L (a - x) : ℝ) with hr_def
    have hr0 : 0 ≤ r := Nat.cast_nonneg _
    have hinf : (zdistInf d L (a - x) : ℝ) ≤ r := by rw [hr_def]; exact_mod_cast zdistInf_le_zdistD d L (a - x)
    have hexp1 : Real.exp (k * Real.sqrt (zdistInf d L (a - x))) ≤ Real.exp (k * Real.sqrt r) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hinf) hk)
    have hamgm := Step5IIIKer_amgm (c := c) (k := k) (r := r) hc hr0
    have hexp2 : Real.exp (-(c * r)) * Real.exp (k * Real.sqrt r) ≤ Real.exp (k ^ 2 / (2 * c)) * Real.exp (-((c / 2) * r)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    calc ‖BATheta d L g E m t σ₁ σ₂ a x‖ * Real.exp (k * Real.sqrt (zdistInf d L (a - x)))
        ≤ (2 * C / (1 - t) * Real.exp (-(c * r))) * Real.exp (k * Real.sqrt r) :=
          mul_le_mul h5 hexp1 (Real.exp_pos _).le (by positivity)
      _ = 2 * C / (1 - t) * (Real.exp (-(c * r)) * Real.exp (k * Real.sqrt r)) := by ring
      _ ≤ 2 * C / (1 - t) * (Real.exp (k ^ 2 / (2 * c)) * Real.exp (-((c / 2) * r))) :=
          mul_le_mul_of_nonneg_left hexp2 (by positivity)
      _ = 2 * C / (1 - t) * Real.exp (k ^ 2 / (2 * c)) * Real.exp (-((c / 2) * r)) := by ring
  calc ∑ x, ‖BATheta d L g E m t σ₁ σ₂ a x‖ * Real.exp (k * Real.sqrt (zdistInf d L (a - x)))
      ≤ ∑ x : Zd d L, 2 * C / (1 - t) * Real.exp (k ^ 2 / (2 * c)) * Real.exp (-((c / 2) * (zdistD d L (a - x) : ℝ))) :=
        Finset.sum_le_sum fun x _ => hterm x
    _ = 2 * C / (1 - t) * Real.exp (k ^ 2 / (2 * c)) * ∑ x : Zd d L, Real.exp (-((c / 2) * (zdistD d L (a - x) : ℝ))) := by
        rw [← Finset.mul_sum]
    _ ≤ 2 * C / (1 - t) * Real.exp (k ^ 2 / (2 * c)) * RBM.expC (d - 2) (c / 2) := by
        apply mul_le_mul_of_nonneg_left (BAsum_exp_decay_le d L (by omega) (c / 2) hc2 a) (by positivity)
    _ = 2 * C * Real.exp (k ^ 2 / (2 * c)) * RBM.expC (d - 2) (c / 2) * (1 - t)⁻¹ := by
        field_simp

/-- The one-index kernel has row sums at most `(1-s)/(1-t)` (`EKPins_norm_uKer_le`, `(Xi_infint)`). -/
theorem Step5IIIKer_uKer_row_le {d L : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) (σ₁ σ₂ : Bool) (a : Zd d L) :
    ∑ x, ‖BAuKer d L g E m s t σ₁ σ₂ a x‖ ≤ (1 - s) / (1 - t) :=
  (sum_norm_row_le _ a).trans (EKPins_norm_uKer_le hr hs hst ht σ₁ σ₂)

/-- **Weighted row sum of `uKer`**: for `g² ≤ 1 - t`, `0 ≤ s ≤ t < 1`,
`Σ_x |u_{s,t}(a,x)| e^{k √|a-x|_∞} ≤ W_k (1-s)/(1-t)`, `W_k = W_k(d, Λ, κ) ≥ 1`, every charge pair. -/
theorem Step5IIIKer_uKer_weighted (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) (k : ℝ) (hk : 0 ≤ k) :
    ∃ W : ℝ, 1 ≤ W ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
      haveI : NeZero L := ⟨by omega⟩
      BAReal d L g κ E m → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → g ^ 2 ≤ 1 - t → ∀ σ₁ σ₂ : Bool, ∀ a : Zd d L,
        ∑ x, ‖BAuKer d L g E m s t σ₁ σ₂ a x‖ * Real.exp (k * Real.sqrt (zdistInf d L (a - x))) ≤
          W * ((1 - s) / (1 - t)) := by
  obtain ⟨V, hV, H⟩ := Step5IIIKer_theta_weighted d hd Λ κ hΛ hκ k hk
  refine ⟨max 1 V, le_max_left _ _, ?_⟩
  intro L hL g hg hgΛ E m hr s t hs hst ht1 hgt σ₁ σ₂ a
  have : NeZero L := ⟨by omega⟩
  have ht0 : 0 ≤ t := hs.trans hst
  have h1t : 0 < 1 - t := by linarith
  have hW1 : (1 : ℝ) ≤ max 1 V := le_max_left _ _
  have hWV : V ≤ max 1 V := le_max_right _ _
  have hρ : 1 ≤ (1 - s) / (1 - t) := by
    rw [le_div_iff₀ h1t]; linarith
  -- the diagonal term
  have hdiag : ∑ x : Zd d L, ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) a x‖ * Real.exp (k * Real.sqrt (zdistInf d L (a - x))) = 1 := by
    have hx : ∀ x : Zd d L, ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) a x‖ * Real.exp (k * Real.sqrt (zdistInf d L (a - x))) =
        if a = x then 1 else 0 := by
      intro x
      by_cases h : a = x
      · subst h; simp [Step5IIIKer_zdistInf_zero]
      · simp [h]
    rw [Finset.sum_congr rfl fun x _ => hx x]
    simp
  rcases ht0.eq_or_lt with h0 | hpos
  · -- `t = 0`, hence `s = 0` and `u = 1`
    obtain rfl : t = 0 := h0.symm
    obtain rfl : s = 0 := le_antisymm hst hs
    have hu := BAuKer_eq_one_add hr ht0 ht1 σ₁ σ₂ (s := 0)
    simp only [Complex.ofReal_zero, sub_self, zero_smul, add_zero] at hu
    rw [hu, hdiag]
    norm_num
  · have hconv := BAuKer_convex hr hpos ht1 σ₁ σ₂ (s := s)
    have hsl : 0 ≤ s / t := div_nonneg hs ht0
    have hsl1 : s / t ≤ 1 := (div_le_one hpos).mpr hst
    have hpt : ∀ x : Zd d L, ‖BAuKer d L g E m s t σ₁ σ₂ a x‖ ≤
        s / t * ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) a x‖ + (1 - s / t) * ‖BATheta d L g E m t σ₁ σ₂ a x‖ := by
      intro x
      rw [hconv, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have e1 : ‖((s : ℂ) / t)‖ = s / t := by
        rw [← Complex.ofReal_div, Complex.norm_real, Real.norm_of_nonneg hsl]
      have e2 : ‖(1 - (s : ℂ) / t)‖ = 1 - s / t := by
        have : (1 - (s : ℂ) / t) = ((1 - s / t : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      rw [e1, e2]
    calc ∑ x, ‖BAuKer d L g E m s t σ₁ σ₂ a x‖ * Real.exp (k * Real.sqrt (zdistInf d L (a - x)))
        ≤ ∑ x, (s / t * ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) a x‖ * Real.exp (k * Real.sqrt (zdistInf d L (a - x))) +
            (1 - s / t) * (‖BATheta d L g E m t σ₁ σ₂ a x‖ * Real.exp (k * Real.sqrt (zdistInf d L (a - x))))) :=
          Finset.sum_le_sum fun x _ => by
            have := mul_le_mul_of_nonneg_right (hpt x) (Real.exp_pos (k * Real.sqrt (zdistInf d L (a - x)))).le
            linarith
      _ = s / t * ∑ x : Zd d L, ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) a x‖ * Real.exp (k * Real.sqrt (zdistInf d L (a - x))) +
            (1 - s / t) * ∑ x, ‖BATheta d L g E m t σ₁ σ₂ a x‖ * Real.exp (k * Real.sqrt (zdistInf d L (a - x))) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun x _ => by ring
      _ ≤ s / t * 1 + (1 - s / t) * (V * (1 - t)⁻¹) := by
          rw [hdiag]
          have h3 := mul_le_mul_of_nonneg_left (H L hL g hg hgΛ E m hr t ht0 ht1 hgt σ₁ σ₂ a)
            (show 0 ≤ 1 - s / t by linarith)
          linarith
      _ ≤ max 1 V * (s / t + (1 - s / t) * (1 - t)⁻¹) := by
          have h2 : V * (1 - t)⁻¹ ≤ max 1 V * (1 - t)⁻¹ := by gcongr
          nlinarith [mul_le_mul_of_nonneg_left h2 (show 0 ≤ 1 - s / t by linarith)]
      _ = max 1 V * ((1 - s) / (1 - t)) := by
          congr 1
          field_simp
          ring

end Weighted

/-! ## 3. Two slots: the weighted sum of a profile against the product of two row kernels -/

section TwoSlot

/-- The exponential triangle inequality for the tail profile: `|b₀-b₁| ≥ |a₀-a₁| - |a₀-b₀| - |a₁-b₁|` under `√`. -/
theorem Step5IIIKer_exp_tri (d L : ℕ) [NeZero L] (a b : Fin 2 → Zd d L) {c : ℝ} (hc : 0 ≤ c) :
    Real.exp (-(c * Real.sqrt (zdistInf d L (b 0 - b 1)))) ≤
      Real.exp (-(c * Real.sqrt (zdistInf d L (a 0 - a 1)))) *
        ∏ i, Real.exp (c * Real.sqrt (zdistInf d L (a i - b i))) := by
  have h1 : zdistInf d L (a 0 - a 1) ≤ zdistInf d L (a 0 - b 0) + zdistInf d L (b 0 - b 1) + zdistInf d L (a 1 - b 1) := by
    have e1 := Step5IIIKer_zdistInf_tri d L (a 0) (b 0) (a 1)
    have e2 := Step5IIIKer_zdistInf_tri d L (b 0) (b 1) (a 1)
    have e3 := Step5IIIKer_zdistInf_sub_comm d L (b 1) (a 1)
    have e4 := Step5IIIKer_zdistInf_sub_comm d L (b 1) (a 1)
    omega
  have h2 : Real.sqrt (zdistInf d L (a 0 - a 1)) ≤ Real.sqrt (zdistInf d L (a 0 - b 0)) +
      Real.sqrt (zdistInf d L (b 0 - b 1)) + Real.sqrt (zdistInf d L (a 1 - b 1)) := by
    have h1' : ((zdistInf d L (a 0 - a 1) : ℕ) : ℝ) ≤ (zdistInf d L (a 0 - b 0) : ℝ) + (zdistInf d L (b 0 - b 1) : ℝ) +
        (zdistInf d L (a 1 - b 1) : ℝ) := by exact_mod_cast h1
    refine (Real.sqrt_le_sqrt h1').trans ?_
    refine (Step5IIIKer_sqrt_add_le (by positivity) (by positivity)).trans ?_
    gcongr
    exact Step5IIIKer_sqrt_add_le (by positivity) (by positivity)
  rw [Fin.prod_univ_two, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left h2 hc]

theorem Step5IIIKer_sum_mul_le {Z : Type*} [Fintype Z] (P f e : Z → ℝ) {amp D0 : ℝ} (hP : ∀ z, 0 ≤ P z)
    (hf : ∀ z, f z ≤ amp * e z + D0) :
    ∑ z, P z * f z ≤ amp * ∑ z, P z * e z + D0 * ∑ z, P z := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun z _ => ?_
  have := mul_le_mul_of_nonneg_left (hf z) (hP z)
  linarith

/-- The row sums multiply: `Σ_b Π_i |U_i(a_i,b_i)| ≤ ρ²`. -/
theorem Step5IIIKer_prod_sum_le {d L : ℕ} [NeZero L] (U : Fin 2 → Matrix (Zd d L) (Zd d L) ℂ) {ρ : ℝ}
    (hrow : ∀ i a, ∑ x, ‖U i a x‖ ≤ ρ) (a : Fin 2 → Zd d L) :
    ∑ b : Fin 2 → Zd d L, ∏ i, ‖U i (a i) (b i)‖ ≤ ρ ^ 2 := by
  rw [Step5IIIKer_sum_prod (fun i x => ‖U i (a i) x‖)]
  calc ∏ i : Fin 2, ∑ x, ‖U i (a i) x‖ ≤ ∏ _i : Fin 2, ρ :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun x _ => norm_nonneg _) fun i _ => hrow i (a i)
    _ = ρ ^ 2 := by simp

/-- **Two-slot bound**: for row kernels `U_i` with row sums `≤ ρ` and `c`-weighted row sums `≤ W_c ρ`, and a profile `f` below
`amp e^{-c √|b₀-b₁|} + D₀`, `Σ_b Π_i |U_i(a_i,b_i)| f(b) ≤ amp W_c² ρ² e^{-c√|a₀-a₁|} + D₀ ρ²`. -/
theorem Step5IIIKer_two_slot {d L : ℕ} [NeZero L] (U : Fin 2 → Matrix (Zd d L) (Zd d L) ℂ) {c ρ Wc amp D0 : ℝ}
    (hc : 0 ≤ c) (hρ : 0 ≤ ρ) (hamp : 0 ≤ amp) (hD0 : 0 ≤ D0)
    (hrow : ∀ i a, ∑ x, ‖U i a x‖ ≤ ρ)
    (hw : ∀ i a, ∑ x, ‖U i a x‖ * Real.exp (c * Real.sqrt (zdistInf d L (a - x))) ≤ Wc * ρ)
    (f : (Fin 2 → Zd d L) → ℝ)
    (hf : ∀ b, f b ≤ amp * Real.exp (-(c * Real.sqrt (zdistInf d L (b 0 - b 1)))) + D0) (a : Fin 2 → Zd d L) :
    ∑ b, (∏ i, ‖U i (a i) (b i)‖) * f b ≤
      amp * Wc ^ 2 * ρ ^ 2 * Real.exp (-(c * Real.sqrt (zdistInf d L (a 0 - a 1)))) + D0 * ρ ^ 2 := by
  have hP : ∀ b : Fin 2 → Zd d L, 0 ≤ ∏ i, ‖U i (a i) (b i)‖ := fun b => Finset.prod_nonneg fun i _ => norm_nonneg _
  have hs1 := Step5IIIKer_prod_sum_le U hrow a
  have hs2 : ∑ b : Fin 2 → Zd d L, (∏ i, ‖U i (a i) (b i)‖) *
      Real.exp (-(c * Real.sqrt (zdistInf d L (b 0 - b 1)))) ≤
      Real.exp (-(c * Real.sqrt (zdistInf d L (a 0 - a 1)))) * (Wc * ρ) ^ 2 := by
    calc _ ≤ ∑ b : Fin 2 → Zd d L, Real.exp (-(c * Real.sqrt (zdistInf d L (a 0 - a 1)))) *
          ∏ i, (‖U i (a i) (b i)‖ * Real.exp (c * Real.sqrt (zdistInf d L (a i - b i)))) := by
          refine Finset.sum_le_sum fun b _ => ?_
          have h := mul_le_mul_of_nonneg_left (Step5IIIKer_exp_tri d L a b hc) (hP b)
          have e : ∏ i, (‖U i (a i) (b i)‖ * Real.exp (c * Real.sqrt (zdistInf d L (a i - b i)))) =
              (∏ i, ‖U i (a i) (b i)‖) * ∏ i, Real.exp (c * Real.sqrt (zdistInf d L (a i - b i))) :=
            Finset.prod_mul_distrib
          rw [e]
          linarith
      _ = Real.exp (-(c * Real.sqrt (zdistInf d L (a 0 - a 1)))) *
            ∏ i : Fin 2, ∑ x, ‖U i (a i) x‖ * Real.exp (c * Real.sqrt (zdistInf d L (a i - x))) := by
          rw [← Finset.mul_sum, Step5IIIKer_sum_prod (fun i x => ‖U i (a i) x‖ * Real.exp (c * Real.sqrt (zdistInf d L (a i - x))))]
      _ ≤ Real.exp (-(c * Real.sqrt (zdistInf d L (a 0 - a 1)))) * (Wc * ρ) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          calc ∏ i : Fin 2, ∑ x, ‖U i (a i) x‖ * Real.exp (c * Real.sqrt (zdistInf d L (a i - x)))
              ≤ ∏ _i : Fin 2, (Wc * ρ) :=
                Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun x _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
                  fun i _ => hw i (a i)
            _ = (Wc * ρ) ^ 2 := by simp
  have hfin := Step5IIIKer_sum_mul_le (fun b => ∏ i, ‖U i (a i) (b i)‖) f
    (fun b => Real.exp (-(c * Real.sqrt (zdistInf d L (b 0 - b 1))))) hP hf
  have h3 := mul_le_mul_of_nonneg_left hs2 hamp
  have h4 := mul_le_mul_of_nonneg_left hs1 hD0
  refine hfin.trans ?_
  have e : amp * Wc ^ 2 * ρ ^ 2 * Real.exp (-(c * Real.sqrt (zdistInf d L (a 0 - a 1)))) =
      amp * (Real.exp (-(c * Real.sqrt (zdistInf d L (a 0 - a 1)))) * (Wc * ρ) ^ 2) := by ring
  rw [e]
  exact add_le_add h3 h4

end TwoSlot

/-! ## 4. Targets 1 and 3 -/

/-- **Target 1** (the probe's `T2459_lam0_le_lam`, `:58`; UBA-C1 at BA, guarded): where `g₀ = BAflowLam0 > 0`, `g₀ ≤ g = sz.lam`
(`TwistStep2_lam0_sq`, `BA/TwistStep2.lean:740`). -/
theorem baStep5III_lam0_le_lam {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {sz : Sizes d} {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z)
    (n : ℕ) (hpos : 0 < BAflowLam0 sz z n) : BAflowLam0 sz z n ≤ sz.lam n := by
  have h := (TwistStep2_lam0_sq hκ hflow n).1
  have hl : 0 < sz.lam n := by
    by_contra hneg
    have : BAflowLam0 sz z n ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) (not_lt.mp hneg)
    linarith
  exact (pow_le_pow_iff_left₀ hpos.le hl.le two_ne_zero).1 h

/-- **Target 3** (the probe's `T2459_BAKernel`, `:78`): `(neiwuj)` (`3_5:2344-2362`) on the one kernel `Step2Gen_UN` at `baFM`,
`Cc = Cc(d, 𝔡⁻¹, κ)`; `lam0 ≤ sz.lam` replaces `‖m‖ = 1`; the conclusion is U6's `STTailtoTailConclgL` (`Chain/Step5Gen.lean:169`). -/
def BAStep5IIIKernel (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ Cc : ℝ, 0 < Cc ∧ ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (D s t : ℝ),
    BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n) → 0 < lam0 n → lam0 n ≤ 𝔡⁻¹ → lam0 n ≤ sz.lam n →
    0 ≤ s → s ≤ t → t < 1 → sz.lam n ^ 2 ≤ 1 - t → STTailtoTailConclgL (baFM sz lam0 E) n Cc D s t

/-- `Im (E + m) ≠ 0` from `κ ≤ Im m`. -/
theorem Step5IIIKer_hIm {d : ℕ} {sz : Sizes d} {lam0 E : ℕ → ℝ} {κ : ℝ} (hκ : 0 < κ) {n : ℕ}
    (hreal : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) :
    (((E n : ℝ) : ℂ) + BAmF sz lam0 E n).im ≠ 0 := by
  have h := hreal.2
  rw [Complex.add_im, Complex.ofReal_im, zero_add]
  exact (lt_of_lt_of_le hκ h).ne'

/-- The product kernel `Step2Gen_UN` at `baFM`, two slots, as the sum of products of `BAuKer`. -/
theorem Step5IIIKer_UN_eq {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)
    (hIm : (((E n : ℝ) : ℂ) + BAmF sz lam0 E n).im ≠ 0) (σ : Fin 2 → Bool) (s t : ℝ) (A : (Fin 2 → Zd d (sz.L n)) → ℂ)
    (a : Fin 2 → Zd d (sz.L n)) :
    Step2Gen_UN (baFM sz lam0 E) n σ s t A a =
      ∑ b : Fin 2 → Zd d (sz.L n), (∏ i, BAuKer d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) s t (σ i) (σ (finRotate 2 i)) (a i) (b i)) * A b := by
  rw [Step2Kern_UN_BA sz lam0 E n hIm 2 σ s t A]
  rfl

/-- `lam0 ≤ lam` and `lam² ≤ 1 - t` give `lam0² ≤ 1 - t`. -/
theorem Step5IIIKer_sq_le {l0 l t : ℝ} (hpos : 0 < l0) (hle : l0 ≤ l) (hreg : l ^ 2 ≤ 1 - t) : l0 ^ 2 ≤ 1 - t :=
  (pow_le_pow_left₀ hpos.le hle 2).trans hreg

theorem baStep5IIIKernel_holds (d : ℕ) : BAStep5IIIKernel d := by
  intro hd κ 𝔡 hκ h𝔡
  obtain ⟨Wk, hWk1, HW⟩ := Step5IIIKer_uKer_weighted d hd 𝔡⁻¹ κ (inv_pos.mpr h𝔡) hκ 1 zero_le_one
  refine ⟨Wk ^ 2, by positivity, ?_⟩
  intro sz lam0 E n D s t hreal hpos hΛ hle hs hst ht hreg σ A hA a
  have hIm := Step5IIIKer_hIm hκ hreal
  have hg2 := Step5IIIKer_sq_le hpos hle hreg
  have h1t : 0 < 1 - t := by linarith
  have h1s : 0 < 1 - s := by linarith
  have hρ : 0 ≤ (1 - s) / (1 - t) := div_nonneg h1s.le h1t.le
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  rw [Step5IIIKer_UN_eq sz lam0 E n hIm σ s t A a]
  have hn : ‖∑ b : Fin 2 → Zd d (sz.L n), (∏ i, BAuKer d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) s t (σ i) (σ (finRotate 2 i)) (a i) (b i)) * A b‖ ≤
      ∑ b : Fin 2 → Zd d (sz.L n), (∏ i, ‖BAuKer d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) s t (σ i) (σ (finRotate 2 i)) (a i) (b i)‖) * ‖A b‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_mul, norm_prod]
  refine hn.trans ?_
  have hmain := Step5IIIKer_two_slot (fun i => BAuKer d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) s t (σ i) (σ (finRotate 2 i)))
    (c := 1) (ρ := (1 - s) / (1 - t)) (Wc := Wk) (amp := ((((sz.W n : ℕ) : ℝ) ^ d * |1 - s|)⁻¹) ^ 2)
    (D0 := ((sz.W n : ℕ) : ℝ) ^ (-D)) zero_le_one hρ (by positivity) (Real.rpow_nonneg hW0.le _)
    (fun i x => Step5IIIKer_uKer_row_le hreal hs hst ht _ _ x)
    (fun i x => HW (sz.L n) (sz.three_le_L n) (lam0 n) hpos hΛ (E n) _ hreal s t hs hst ht hg2 _ _ x)
    (fun b => ‖A b‖) (fun b => by
      have := hA b
      unfold tailTD at this
      simpa only [one_mul] using this) a
  refine hmain.trans ?_
  set Wn : ℝ := ((sz.W n : ℕ) : ℝ) with hWn
  have hs' : |1 - s| = 1 - s := abs_of_pos h1s
  have ht' : |1 - t| = 1 - t := abs_of_pos h1t
  have hWd : 0 < Wn ^ d := pow_pos hW0 d
  have hkey : ((Wn ^ d * |1 - s|)⁻¹) ^ 2 * Wk ^ 2 * ((1 - s) / (1 - t)) ^ 2 =
      Wk ^ 2 * ((Wn ^ d * |1 - t|)⁻¹) ^ 2 := by
    rw [hs', ht']
    field_simp
  have hD : 0 ≤ Wn ^ (-D) := Real.rpow_nonneg hW0.le _
  unfold tailTD
  rw [hkey, one_mul]
  have : 0 ≤ Wk ^ 2 * Wn ^ (-D) := by positivity
  nlinarith

/-- **Target 3, at the flow** (the conclusion of the probe's `T2459_kernel_at_flow`, `:84-91`, hypothesis discharged by
`baStep5IIIKernel_holds`; every `d ≥ 3`, `ε 𝔠` after `∃ Cc`): `g₀ = BAflowLam0`, eventually in `n` (`BAflow_lam0_window`,
`BAflow_real`, target 1); the regime reads `g = sz.lam` (UBA-C1). -/
theorem baStep5IIIKernel_at_flow (d : ℕ) : 3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ Cc : ℝ, 0 < Cc ∧
    ∀ (ε 𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ᶠ n in atTop, ∀ D s t : ℝ, 0 ≤ s → s ≤ t → t < 1 →
      sz.lam n ^ 2 ≤ 1 - t → STTailtoTailConclgL (baFMz sz z) n Cc D s t := by
  intro hd κ 𝔡 hκ h𝔡
  obtain ⟨Cc, hCc, H⟩ := baStep5IIIKernel_holds d hd κ 𝔡 hκ h𝔡
  refine ⟨Cc, hCc, fun ε 𝔠 sz z hflow => ?_⟩
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow] with n hn D s t hs hst ht1 hreg
  exact H sz (BAflowLam0 sz z) (BAflowEs sz z) n D s t (BAflow_real κ ε 𝔠 𝔡 sz z hflow n) hn.1 hn.2
    (baStep5III_lam0_le_lam hκ hflow n hn.1) hs hst ht1 hreg

/-! ## 5. The far fields -/

/-- **Target 4 (a)**: the Θ-level far field from the K-level `emn2ExpHK` (the probe's `T2459_Theta_far`, `:242-276`, copied; paper-delta
T2459e): for `x ≠ x'`, `Θ_{xx'} = t (Θ M)_{xx'}` (`BATheta_resolvent`, `BA/KBase.lean:330`) and `𝒦^{(2)} = W^{-d}(Θ M)`
(`EMn2BA_K_two`, `BA/EMn2BA.lean:624`), so `baEMn2ExpHK` (`:637`) at `D + d` gives `|Θ_{xx'}| ≤ W^{-D}` beyond `ℓ*_t`. -/
theorem baStep5III_Theta_far {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {sz : Sizes d} {z : ℕ → ℂ}
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (htT : ∀ n, t n ≤ BAflowT0 sz z n) {D : ℝ} (hD : 0 < D) :
    ∀ᶠ n in atTop, ∀ (x x' : Zd d (sz.L n)) (s : Bool), x ≠ x' → emn2ExpEllStar sz n (t n) ≤ (zdistInf d (sz.L n) (x - x') : ℝ) →
      ‖BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (t n) s (!s) x x'‖ ≤
        ((sz.W n : ℕ) : ℝ) ^ (-D) := by
  have hK := baEMn2ExpHK hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT D hD
  filter_upwards [hK, BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow] with n hn hg x x' s hne hfar
  have hT1 : t n < 1 := (htT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  have hKeq := EMn2BA_K_two hκ sz hflow n hg.1 ⟨ht0 n, hT1⟩ s x x'
  have hres := (BATheta_resolvent d (sz.L n) _ κ _ _ (BAflow_real κ ε 𝔠 𝔡 sz z hflow n) (t n) (ht0 n) hT1 s (!s)).2
  have hoff := congrFun (congrFun hres x) x'
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hne, zero_add, smul_eq_mul] at hoff
  have hkn := hn x x' s hfar
  have hW : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  rw [hoff]
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  have hWd : (0 : ℝ) < W ^ d := pow_pos hW0 d
  have hY : ‖(BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (t n) s (!s) *
      BAMss d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) ((BAflowEs sz z n : ℝ) : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) s (!s)) x x'‖ =
      W ^ d * ‖(baFMz sz z).K n (t n) ![s, !s] ![x, x']‖ := by
    rw [hKeq, norm_mul, norm_inv, norm_pow, Complex.norm_natCast, ← hWdef]
    field_simp
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ht0 n), hY]
  have h1 : W ^ d * ‖(baFMz sz z).K n (t n) ![s, !s] ![x, x']‖ ≤ W ^ (-(D + (d : ℝ))) :=
    calc W ^ d * ‖(baFMz sz z).K n (t n) ![s, !s] ![x, x']‖ ≤ W ^ d * ((W ^ d)⁻¹ * W ^ (-(D + (d : ℝ)))) :=
          mul_le_mul_of_nonneg_left hkn hWd.le
      _ = W ^ (-(D + (d : ℝ))) := by field_simp
  have h2 : W ^ (-(D + (d : ℝ))) ≤ W ^ (-D) :=
    Real.rpow_le_rpow_of_exponent_le hW (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
  calc t n * (W ^ d * ‖(baFMz sz z).K n (t n) ![s, !s] ![x, x']‖) ≤ 1 * (W ^ d * ‖(baFMz sz z).K n (t n) ![s, !s] ![x, x']‖) :=
        mul_le_mul_of_nonneg_right hT1.le (by positivity)
    _ ≤ W ^ (-D) := by rw [one_mul]; exact h1.trans h2

/-- `W_n → ∞` from `Admissible` (`Bandwidth` and `SizeTendsto`; the twin of `step34Gen_W_tendsto`, `Chain/Step34Gen.lean:610`). -/
theorem Step5IIIKer_W_tendsto {d : ℕ} {sz : Sizes d} {𝔠 𝔡 : ℝ} (h : sz.Admissible 𝔠 𝔡) :
    Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := by
  obtain ⟨h𝔠, -, hsize, hbw, -⟩ := h
  exact tendsto_atTop_mono' _ hbw ((tendsto_rpow_atTop h𝔠).comp hsize)

/-- `A x^m ≤ exp (c (log x)^{3/2})` for large `x` (`(log x)^{3/2}` beats `m log x + log A`). -/
theorem Step5IIIKer_poly_le_exp {A c m : ℝ} (hA : 0 < A) (hc : 0 < c) (hm : 0 ≤ m) :
    ∀ᶠ x : ℝ in atTop, A * x ^ m ≤ Real.exp (c * Real.log x ^ (3 / 2 : ℝ)) := by
  set K : ℝ := (m + |Real.log A| + 1) / c with hK
  have hK0 : 0 ≤ K := by positivity
  filter_upwards [eventually_ge_atTop (Real.exp (max 1 (K ^ 2)))] with x hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hy1 : max 1 (K ^ 2) ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hx
  set y := Real.log x with hy
  have hy1' : 1 ≤ y := (le_max_left _ _).trans hy1
  have hy0 : 0 ≤ y := by linarith
  have hsq : K ≤ Real.sqrt y := Real.le_sqrt_of_sq_le ((le_max_right _ _).trans hy1)
  have h32 : y ^ (3 / 2 : ℝ) = y * Real.sqrt y := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hy0 (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hxm : x ^ m = Real.exp (y * m) := Real.rpow_def_of_pos hxpos m
  have hcK : c * K = m + |Real.log A| + 1 := by rw [hK]; field_simp
  calc A * x ^ m = Real.exp (Real.log A + y * m) := by rw [Real.exp_add, Real.exp_log hA, hxm]
    _ ≤ Real.exp (c * y ^ (3 / 2 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        rw [h32]
        have h1 : c * (y * K) ≤ c * (y * Real.sqrt y) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hy0) hc.le
        have h2 : c * (y * K) = (m + |Real.log A| + 1) * y := by rw [← hcK]; ring
        have h3 := le_abs_self (Real.log A)
        nlinarith [abs_nonneg (Real.log A)]

/-- **Target 4 (b)**: the `uKer`-level far field at the flow, all four charge pairs `(τ, τ')`, uniformly in `0 ≤ v ≤ w ≤ t₀` with
`sz.lam² ≤ 1 - w`, beyond `ℓ* = (log W)^{3/2}`; premise (H3) of `baStep5IIITailSq` at the flow.  Route (i): `u_{v,w}(x,y) = (1 - v/w) Θ_w(x,y)`
off the diagonal (`BAuKer_convex`), `baProp5_holds` with `ℓ_w = 1`, `B ≤ 2/(1-w) ≤ 2 W^d` (`lam_sq_mul_pow_ge`), and `2C W^{d+D} ≤ e^{c ℓ*}`
eventually. -/
theorem baStep5III_uKer_far (d : ℕ) : 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ D : ℝ, 0 < D →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, ∀ v w : ℝ, 0 ≤ v → v ≤ w → w ≤ BAflowT0 sz z n → sz.lam n ^ 2 ≤ 1 - w →
        ∀ (τ τ' : Bool) (x y : Zd d (sz.L n)),
          Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (x - y) : ℝ) →
          ‖Step2Gen_uKer (baFMz sz z) n τ τ' v w x y‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := by
  intro hd κ ε 𝔡 hκ hε h𝔡 D hD 𝔠 sz z hflow
  obtain ⟨C, c, hC, hc, H⟩ := Step5IIIKer_theta_entry d hd 𝔡⁻¹ κ (inv_pos.mpr h𝔡) hκ
  have hWt := Step5IIIKer_W_tendsto hflow.1
  have hpoly := Step5IIIKer_poly_le_exp (A := 2 * C) (c := c) (m := (d : ℝ) + D) (by positivity) hc (by positivity)
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow, hWt.eventually hpoly, hWt.eventually_gt_atTop 1,
    hflow.1.2.2.2.2] with n hn hpn hW1 hWO v w hv hvw hwT hreg τ τ' x y hfar
  have hle := baStep5III_lam0_le_lam hκ hflow n hn.1
  have hg2 := Step5IIIKer_sq_le hn.1 hle hreg
  have hreal := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hIm := Step5IIIKer_hIm hκ hreal
  have hw1 : w < 1 := hwT.trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  have h1w : 0 < 1 - w := by linarith
  set Wn : ℝ := ((sz.W n : ℕ) : ℝ) with hWn
  have hW0 : 0 < Wn := by linarith
  set ell : ℝ := Real.log Wn ^ (3 / 2 : ℝ) with hell
  have hell0 : 0 < ell := Real.rpow_pos_of_pos (Real.log_pos hW1) _
  have hne : x ≠ y := by
    intro h
    rw [h, sub_self, Step5IIIKer_zdistInf_zero] at hfar
    simp only [Nat.cast_zero] at hfar
    linarith
  have hu : Step2Gen_uKer (baFMz sz z) n τ τ' v w =
      BAuKer d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) v w τ τ' :=
    Step2Kern_uKer_BA sz (BAflowLam0 sz z) (BAflowEs sz z) n hIm τ τ' v w
  rw [hu]
  have hWpos : 0 ≤ Wn ^ (-D) := Real.rpow_nonneg hW0.le _
  rcases hv.trans hvw |>.eq_or_lt with hw0 | hwpos
  · -- `w = 0`: `u = 1`
    have he := BAuKer_eq_one_add hreal (hv.trans hvw) hw1 τ τ' (s := v)
    have hv0 : v = 0 := le_antisymm (hw0 ▸ hvw) hv
    rw [← hw0, hv0] at he ⊢
    simp only [Complex.ofReal_zero, sub_self, zero_smul, add_zero] at he
    rw [he, Matrix.one_apply_ne hne, norm_zero]
    exact hWpos
  · -- `w > 0`: `u x y = (1 - v/w) Θ_w x y`
    have hconv := BAuKer_convex hreal hwpos hw1 τ τ' (s := v)
    have hvw1 : v / w ≤ 1 := (div_le_one hwpos).mpr hvw
    have hv0 : 0 ≤ v / w := div_nonneg hv hwpos.le
    have hent : ‖BAuKer d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) v w τ τ' x y‖ ≤
        ‖BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) w τ τ' x y‖ := by
      rw [hconv, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply_ne hne, smul_zero, zero_add, smul_eq_mul,
        norm_mul]
      have e2 : ‖(1 - (v : ℂ) / w)‖ = 1 - v / w := by
        have : (1 - (v : ℂ) / w) = ((1 - v / w : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      rw [e2]
      calc _ ≤ 1 * ‖BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) w τ τ' x y‖ :=
            mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
        _ = _ := one_mul _
    have hΘ := H (sz.L n) (sz.three_le_L n) (BAflowLam0 sz z n) hn.1 hn.2 (BAflowEs sz z n) _ hreal w hwpos.le hw1 hg2 τ τ' x y
    -- `(1 - w)⁻¹ ≤ W^d`
    have hlam0 : 0 < sz.lam n := hn.1.trans_le hle
    have hlw := lam_sq_mul_pow_ge sz n hWO.1
    have hWr1 : 1 ≤ Wn ^ (2 * 𝔡) := Real.one_le_rpow hW1.le (by linarith)
    have hWdpos : 0 < Wn ^ d := pow_pos hW0 d
    have hinv : (1 - w)⁻¹ ≤ Wn ^ d := by
      rw [inv_eq_one_div, div_le_iff₀ h1w]
      have h1 : 1 ≤ sz.lam n ^ 2 * Wn ^ d := hWr1.trans hlw
      nlinarith
    have hdist : ell ≤ (zdistD d (sz.L n) (x - y) : ℝ) :=
      hfar.trans (by exact_mod_cast zdistInf_le_zdistD d (sz.L n) (x - y))
    have hexp : Real.exp (-(c * (zdistD d (sz.L n) (x - y) : ℝ))) ≤ Real.exp (-(c * ell)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hmain : 2 * C * Wn ^ d * Real.exp (-(c * ell)) ≤ Wn ^ (-D) := by
      rw [Real.rpow_neg hW0.le, ← one_div, le_div_iff₀ (Real.rpow_pos_of_pos hW0 D)]
      have e : 2 * C * Wn ^ d * Real.exp (-(c * ell)) * Wn ^ D = 2 * C * Wn ^ ((d : ℝ) + D) * Real.exp (-(c * ell)) := by
        rw [Real.rpow_add hW0, Real.rpow_natCast]; ring
      rw [e]
      calc 2 * C * Wn ^ ((d : ℝ) + D) * Real.exp (-(c * ell)) ≤ Real.exp (c * ell) * Real.exp (-(c * ell)) :=
            mul_le_mul_of_nonneg_right hpn (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    calc _ ≤ _ := hent
      _ ≤ _ := hΘ
      _ ≤ 2 * C * Wn ^ d * Real.exp (-(c * ell)) := by
          have h2 : 2 * C / (1 - w) ≤ 2 * C * Wn ^ d := by
            rw [div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_left hinv (by positivity)
          exact mul_le_mul h2 hexp (Real.exp_pos _).le (by positivity)
      _ ≤ _ := hmain

/-! ## 6. Compiled nonempty instances at `d = 3`, `sz0`, `zSeq`, `flow_sz0`

`(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, `s ≡ 1/10 < t ≡ 1/2 < t₀` (`half_lt_t0`); the regime `sz0.lam² ≤ 1 - t` holds from
`sz0.lam ≤ 1/64`.  Every deterministic hypothesis is discharged. -/

section Instances

/-- `sz0.lam n ≤ 1/64` (copy of `T2459_sz0_lam_le`, probe `:94`). -/
theorem Step5IIIKer_sz0_lam_le (n : ℕ) : SizesInst.sz0.lam n ≤ 1 / 64 := by
  have h2 : (2 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h : (64 : ℝ) ≤ (2 * ((n : ℝ) + 1)) ^ 6 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 6
    norm_num at this
    exact this
  change ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ ≤ 1 / 64
  rw [one_div]
  exact inv_anti₀ (by norm_num) h

/-- The regime `sz0.lam² ≤ 1 - t` for every `t ≤ 1/2`. -/
theorem Step5IIIKer_sz0_reg (n : ℕ) {t : ℝ} (ht : t ≤ 1 / 2) : SizesInst.sz0.lam n ^ 2 ≤ 1 - t := by
  have h := Step5IIIKer_sz0_lam_le n
  have h0 := FlowPinsInst.sz0_lam_pos n
  nlinarith

/-- **Instance of target 1**: at `flow_sz0`, eventually `0 < g₀ ≤ sz0.lam`. -/
example : ∀ᶠ n in atTop, 0 < BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq n ∧
    BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq n ≤ SizesInst.sz0.lam n := by
  filter_upwards [BAflow_lam0_window (1 / 2) (1 / 10) (1 / 6) (1 / 10) SizesInst.sz0 FlowPinsInst.zSeq FlowPinsInst.flow_sz0] with n hn
  exact ⟨hn.1, baStep5III_lam0_le_lam (by norm_num) FlowPinsInst.flow_sz0 n hn.1⟩

/-- **Instance of target 3**: `s ≡ 1/10 < t ≡ 1/2`, every `D`. -/
example : ∃ Cc : ℝ, 0 < Cc ∧ ∀ᶠ n in atTop, ∀ D : ℝ,
    STTailtoTailConclgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) n Cc D (1 / 10) (1 / 2) := by
  obtain ⟨Cc, hCc, H⟩ := baStep5IIIKernel_at_flow 3 le_rfl (1 / 2) (1 / 10) (by norm_num) (by norm_num)
  refine ⟨Cc, hCc, ?_⟩
  filter_upwards [H (1 / 10) (1 / 6) SizesInst.sz0 FlowPinsInst.zSeq FlowPinsInst.flow_sz0] with n hn D
  exact hn D (1 / 10) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (Step5IIIKer_sz0_reg n le_rfl)

/-- **Instance of target 4 (a)**: `t ≡ 1/2`, `D = 1`. -/
example : ∀ᶠ n in atTop, ∀ (x x' : Zd 3 (SizesInst.sz0.L n)) (s : Bool), x ≠ x' →
    emn2ExpEllStar SizesInst.sz0 n (1 / 2) ≤ (zdistInf 3 (SizesInst.sz0.L n) (x - x') : ℝ) →
    ‖BATheta 3 (SizesInst.sz0.L n) (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq n) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq n)
      (BAmF SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq) n)
      (1 / 2) s (!s) x x'‖ ≤ ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) :=
  baStep5III_Theta_far (d := 3) le_rfl (κ := 1 / 2) (ε := 1 / 10) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (by norm_num) (by norm_num) (by norm_num)
    FlowPinsInst.flow_sz0 (t := fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (FlowPinsInst.half_lt_t0 n).le) one_pos

/-- **Instance of target 4 (b)**: `v = 1/10`, `w = 1/2`, `D = 1`, every charge pair. -/
example : ∀ᶠ n in atTop, ∀ (τ τ' : Bool) (x y : Zd 3 (SizesInst.sz0.L n)),
    Real.log ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf 3 (SizesInst.sz0.L n) (x - y) : ℝ) →
    ‖Step2Gen_uKer (baFMz SizesInst.sz0 FlowPinsInst.zSeq) n τ τ' (1 / 10) (1 / 2) x y‖ ≤ ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) := by
  filter_upwards [baStep5III_uKer_far 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 1 one_pos (1 / 6)
    SizesInst.sz0 FlowPinsInst.zSeq FlowPinsInst.flow_sz0] with n hn τ τ' x y hfar
  exact hn (1 / 10) (1 / 2) (by norm_num) (by norm_num) (FlowPinsInst.half_lt_t0 n).le (Step5IIIKer_sz0_reg n le_rfl) τ τ' x y hfar

end Instances

end RBM.BA

end
