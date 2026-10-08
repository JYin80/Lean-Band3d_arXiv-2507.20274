/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.DuhamelI
import RBM3D.Induction.WardII
import RBM3D.Induction.IniTermII

/-!
# S5-26 (ticket T2339): the integrated hierarchy with `Q^{(1)}`, case (ii) of Step 5

`stDuhamelII_holds : ∀ d, STDuhamelII d` (`3_5:2251-2283`, `(zYU2)`): for `σ₁ ≠ σ₂` the
zero-mode removed loop `Q^{(1)} ∘ (𝓛-𝒦)^{(2)}` (`Q^{(1)} = zeroModeSet {0}`), for `σ₁ = σ₂`
no zero-mode removal (`stDuhamelConcl_engine`, `hTTT` through `Or.inr`).  The public engine of
the mixed conjunct is `stDuhamelConcl_engineQ1` (any sign class `P`; `Q = {0}`).

Route (the preflight route F1, paper-delta candidate `T2339a`): instead of the paper's `Θ̊`
kernel estimates `(ThetaBcirc_infint)`, `(uwp2-92kj00)`, `Q^{(1)}` is applied to the pathwise
remainder `R = (𝓛-𝒦)_{tt} - 𝒰_{s,tt} (𝓛-𝒦)_s` of the grid Duhamel form.  `R` is controlled at
every label by the drift and martingale terms of section 3 of `DuhamelI.lean`
(`duhamelII_path_rem`: `duhamelI_path` without the initial term), `Q^{(1)} 𝒰 (𝓛-𝒦)_s` is the
hypothesis, and `‖Q^{(1)} R_a‖ ≤ ‖R_a‖ + L^{-d} Σ_c ‖R_{(c,a₂)}‖`, the average of the profile
being controlled by the zero mode of `𝒯_t` in the regime `1-t ≤ ilambda²/L²`
(`duhamelII_prof_avg`).  The private helpers of `DuhamelI.lean` are reached with `open private`
(Batteries) instead of being copied, as in `Induction/EMn2Exp2.lean`.

Imports: those of the ticket's check file, `ZeroModeCalc` being transitive through `DuhamelI`;
`WardII` and `IniTermII` (the case (ii) siblings S5-28, S5-27) are imported without using a
declaration of theirs.

Sections: 1 `Q^{(1)}` on the first index; 2 the average of the profile; 3 the pathwise
remainder; 4 Hölder continuity of `Q^{(1)}(𝓛-𝒦)_u`; 5 the per-section statement; 6 the engine,
the pin and the compiled instances at `d = 3`.
-/

set_option linter.style.longLine false

open private duhamelI_drift duhamelI_mart duhamelI_grid duhamelI_tailW_eq duhamelI_rpow_quarter
  duhamelI_absorb duhamelI_whp_sec duhamelI_ELKLK_meas duhamelI_cardK duhamelI_measure_le
  from RBM3D.Induction.DuhamelI
open private emn2Exp2_exists_CR from RBM3D.Induction.EMn2Exp2

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ## 1. `Q^{(1)}` on the first index -/

section Zero

variable {d L : ℕ} [NeZero L]

/-- `Q^{(1)} = zeroModeSet {0}` removes the average over the first index. -/
private theorem duhamelII_Q_apply (T : (Fin 2 → Zd d L) → ℂ) (a : Fin 2 → Zd d L) :
    zeroModeSet d L {0} T a = T a - ((L : ℂ) ^ d)⁻¹ * ∑ c : Zd d L, T (Function.update a 0 c) := by
  simp [zeroModeSet, Finset.toList_singleton, zeroModeOp, avgOp]

/-- `‖Q^{(1)}X_a - Q^{(1)}I_a‖ ≤ ‖X_a - I_a‖ + L^{-d} Σ_c ‖X_{(c,a₂)} - I_{(c,a₂)}‖`. -/
private theorem duhamelII_Q_sub_le (X I : (Fin 2 → Zd d L) → ℂ) (a : Fin 2 → Zd d L) :
    ‖zeroModeSet d L {0} X a - zeroModeSet d L {0} I a‖ ≤
      ‖X a - I a‖ + ((L : ℝ) ^ d)⁻¹ *
        ∑ c : Zd d L, ‖X (Function.update a 0 c) - I (Function.update a 0 c)‖ := by
  rw [duhamelII_Q_apply, duhamelII_Q_apply]
  have e : (X a - ((L : ℂ) ^ d)⁻¹ * ∑ c, X (Function.update a 0 c)) -
      (I a - ((L : ℂ) ^ d)⁻¹ * ∑ c, I (Function.update a 0 c)) =
      (X a - I a) - ((L : ℂ) ^ d)⁻¹ * ∑ c, (X (Function.update a 0 c) - I (Function.update a 0 c)) := by
    simp only [Finset.sum_sub_distrib]; ring
  rw [e]
  refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
  rw [norm_mul]
  have hinv : ‖((L : ℂ) ^ d)⁻¹‖ = ((L : ℝ) ^ d)⁻¹ := by simp
  rw [hinv]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

omit [NeZero L] in
/-- `(update a 0 c) 0 = c`, `(update a 0 c) 1 = a 1`. -/
private theorem duhamelII_update_apply (a : Fin 2 → Zd d L) (c : Zd d L) :
    (Function.update a 0 c) 0 = c ∧ (Function.update a 0 c) 1 = a 1 :=
  ⟨Function.update_self .., Function.update_of_ne (by decide) _ _⟩

end Zero

/-- `Q^{(1)} ∘ 𝒰_{v,w} (𝓛-𝒦)_u` is a measurable function of the matrix. -/
private theorem duhamelII_QUgen_meas {d : ℕ} (sz : Sizes d) (n : ℕ) (E u v w : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      ‖zeroModeSet d (sz.L n) {0}
        (RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ v w (fun b => STLKM sz n E u H σ b)) a‖ := by
  have hU : ∀ b, Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ v w (fun b' => STLKM sz n E u H σ b') b := fun b => by
    unfold RBM.Ind.Ugen UN
    exact Finset.measurable_sum _ fun b' _ => measurable_const.mul (STLKM_measurable sz n E u σ b')
  simp only [duhamelII_Q_apply]
  exact ((hU a).sub (measurable_const.mul (Finset.measurable_sum _ fun c _ => hU _))).norm

/-! ## 2. The profile averaged over the first index (the zero mode of `𝒯_t`, `1-t ≤ ilambda²/L²`) -/

section Averaging

variable {d : ℕ}

/-- **The average of the profile**: for `1 - u ≤ ilambda²/L²` the profile `P_u(x,y) = W^{-d} max(𝒯_u(|x-y|_∞), W^{-D})`
has `L^{-d} Σ_c P_u(c,y) ≤ C P_u(x,y)` for all `x, y`, `C = 3 C_rad + 1` depending on `d` only: the radial sum
`Σ_c 𝒯_u(|c-y|_∞) ≤ C_rad/(1-u)` (`emn2Exp2_exists_CR`) against the zero mode of `𝒯_u` (`ℓ_u = L`, so
`exp(-√(r/ℓ_u)) ≥ e⁻¹` for `r ≤ L`, and `B_{u,r} ≥ (L^d(1-u))⁻¹`). -/
private theorem duhamelII_prof_avg (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (n : ℕ) (D u : ℝ), 0 ≤ sz.lam n → u < 1 →
      1 - u ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 → ∀ x y : Zd d (sz.L n),
        (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * ∑ c : Zd d (sz.L n), STprof sz n u D ((sz.L n : ℕ) : ℝ) c y ≤
          C * STprof sz n u D ((sz.L n : ℕ) : ℝ) x y := by
  obtain ⟨CR, hCR, hsum⟩ := emn2Exp2_exists_CR d hd
  refine ⟨3 * CR + 1, by positivity, ?_⟩
  intro sz n D u hg hu1 hreg x y
  have hL3 := sz.three_le_L n
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ sz.L n)
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by linarith
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := by positivity
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have h1u : 0 < 1 - u := by linarith
  set Wd := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ with hWd
  set Wm := ((sz.W n : ℕ) : ℝ) ^ (-D) with hWm
  have hWd0 : 0 ≤ Wd := by positivity
  have hWm0 : 0 ≤ Wm := Real.rpow_nonneg hW.le _
  have hprof : ∀ a b : Zd d (sz.L n), STprof sz n u D ((sz.L n : ℕ) : ℝ) a b =
      Wd * max (tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a - b) : ℕ)) Wm := fun a b => by
    unfold STprof; rw [duhamelI_tailW_eq]
  have hT0 : ∀ a b : Zd d (sz.L n), 0 ≤ tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a - b) : ℕ) :=
    fun a b => tailT_nonneg (Nat.cast_nonneg _)
  -- the sum of the profile
  have hup : ∑ c : Zd d (sz.L n), STprof sz n u D ((sz.L n : ℕ) : ℝ) c y ≤
      Wd * (CR / (1 - u) + ((sz.L n : ℕ) : ℝ) ^ d * Wm) := by
    calc ∑ c : Zd d (sz.L n), STprof sz n u D ((sz.L n : ℕ) : ℝ) c y
        = ∑ c : Zd d (sz.L n), Wd * max (tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (c - y) : ℕ)) Wm :=
          Finset.sum_congr rfl fun c _ => hprof c y
      _ ≤ ∑ c : Zd d (sz.L n), Wd * (tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (c - y) : ℕ) + Wm) :=
          Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left
            (max_le (le_add_of_nonneg_right hWm0) (le_add_of_nonneg_left (hT0 c y))) hWd0
      _ = Wd * (∑ c : Zd d (sz.L n), tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (c - y) : ℕ) +
            ((sz.L n : ℕ) : ℝ) ^ d * Wm) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            card_Zd]
          push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (hsum (sz.L n) (sz.lam n) u hg hu1 y) le_rfl) hWd0
  -- the zero mode of the profile at `(x, y)`
  have hrL : ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    have : zdistInf d (sz.L n) (x - y) ≤ sz.L n := Finset.sup_le fun i _ => zdist_le_L _
    exact_mod_cast this
  have hlow : Real.exp (-1) * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ≤
      tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (x - y) : ℕ) := by
    unfold tailT BparamR
    have hexp := exp_tail_ge hg hu1 hL1 hreg hrL
    have hB : (((sz.L n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ≤
        (sz.lam n ^ 2 + |1 - u|)⁻¹ * ((((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ +
          (((sz.L n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ := by
      have : 0 ≤ (sz.lam n ^ 2 + |1 - u|)⁻¹ * ((((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ :=
        mul_nonneg (inv_nonneg.2 (by positivity)) (inv_nonneg.2 (by positivity))
      linarith
    rw [abs_of_pos h1u] at hB ⊢
    calc Real.exp (-1) * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ =
          (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ * Real.exp (-1) := mul_comm _ _
      _ ≤ _ := mul_le_mul hB hexp (Real.exp_pos _).le (by
          have : 0 ≤ (sz.lam n ^ 2 + (1 - u))⁻¹ * ((((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ :=
            mul_nonneg (inv_nonneg.2 (by positivity)) (inv_nonneg.2 (by positivity))
          have : 0 ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := inv_nonneg.2 (by positivity)
          positivity)
  have he3 : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
  have hZ : (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ≤ 3 * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (x - y) : ℕ) := by
    have h1 : (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ = Real.exp 1 * (Real.exp (-1) * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) := by
      rw [← mul_assoc, ← Real.exp_add]; simp
    rw [h1]
    calc Real.exp 1 * (Real.exp (-1) * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹)
        ≤ Real.exp 1 * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (x - y) : ℕ) :=
          mul_le_mul_of_nonneg_left hlow (Real.exp_pos _).le
      _ ≤ 3 * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (x - y) : ℕ) :=
          mul_le_mul_of_nonneg_right he3 (hT0 x y)
  -- conclusion
  set Tx := tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (x - y) : ℕ) with hTx
  have hTx0 : 0 ≤ Tx := hT0 x y
  rw [hprof x y]
  have e1 : (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * (Wd * (CR / (1 - u) + ((sz.L n : ℕ) : ℝ) ^ d * Wm)) =
      Wd * (CR * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ + Wm) := by
    rw [mul_inv]; field_simp
  calc (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * ∑ c : Zd d (sz.L n), STprof sz n u D ((sz.L n : ℕ) : ℝ) c y
      ≤ (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * (Wd * (CR / (1 - u) + ((sz.L n : ℕ) : ℝ) ^ d * Wm)) :=
        mul_le_mul_of_nonneg_left hup (inv_nonneg.2 hLd.le)
    _ = Wd * (CR * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ + Wm) := e1
    _ ≤ Wd * (CR * (3 * Tx) + Wm) := by gcongr
    _ ≤ (3 * CR + 1) * (Wd * max Tx Wm) := by
        have h1 : Tx ≤ max Tx Wm := le_max_left _ _
        have h2 : Wm ≤ max Tx Wm := le_max_right _ _
        have h3 : 0 ≤ max Tx Wm := le_trans hTx0 h1
        nlinarith [mul_le_mul_of_nonneg_left h1 hWd0, mul_le_mul_of_nonneg_left h2 hWd0,
          mul_nonneg hWd0 (sub_nonneg.2 h1), mul_nonneg hCR.le (mul_nonneg hWd0 (sub_nonneg.2 h1))]

end Averaging

/-! ## 3. The pathwise remainder at one size index -/

section Path

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
-- the remainder combines the drift, martingale and floor estimates of `duhamelI_path`: 200000 is not enough
/-- **The pathwise remainder at one size index** (`duhamelI_path` without the initial term): on a sample `ω` of the grid walk of
`[s, tt]` at which the decomposition of `STGridMartAt`, the three error terms at every grid time and the martingale tail hold,
`‖(𝓛-𝒦)^{(2)}_{tt,σ,a} - [𝒰_{s,tt} (𝓛-𝒦)_s]_a‖ ≤ κ Λ² ρ³ A^{-1/4} W^{-d}𝒯̃^L_{tt,D}(|a₁-a₂|) + W^{-D}`,
`ρ = (1-s)/(1-tt)`, `κ = 4C/c₀ + 8C(2/c₀+1)`.  The hypotheses are uniform in the label `(σ, a)`, so the bound holds at every label
of the same sample (`duhamelII_section` applies it at `(σ, (c, a₂))` for every `c`). -/
theorem duhamelII_path_rem (sz : Sizes d) (n : ℕ) (E s tt : ℕ → ℝ) (K : ℕ → ℕ) (ω : PathΩ sz)
    (Mart Rem : STLab sz n → ℕ → PathΩ sz → ℂ) {Λ D DE Dm M R C c₀ : ℝ} (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n))
    (hs0 : 0 ≤ s n) (hstt : s n < tt n) (htt1 : tt n < 1) (hK : K n ≠ 0) (hE : |E n| ≤ 2)
    (hlam : 0 < sz.lam n) (hΛ : 1 ≤ Λ) (hA : 1 ≤ STAI sz n) (hc₀ : 0 < c₀) (hc : c₀ ≤ (mE (E n)).im)
    (hC : 0 ≤ C)
    (hΦ : ∀ (D' v w : ℝ), s n ≤ v → v ≤ w → w ≤ tt n → ∀ a : Fin 2 → Zd d (sz.L n),
      duhamelI_Phi (fun x y => ‖Theta d (sz.L n) (sz.lam n) (w : ℂ) x y‖) (2 * (1 - v))
          (fun x y => STprof sz n v D' ((sz.L n : ℕ) : ℝ) x y) a ≤
        C * ((1 - v) / (1 - w)) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
          (tailT d (sz.L n) (sz.lam n) w ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) +
            (1 - v) / (1 - w) * ((sz.W n : ℕ) : ℝ) ^ (-D'))))
    (hDE : (1 - s n) / (1 - tt n) * ((sz.W n : ℕ) : ℝ) ^ (-DE) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D))
    (hid : ∀ i : STLab sz n, ∀ k, k ≤ K n → STgA sz s tt K n (E n) i.1 i.2 k ω =
      STgA sz s tt K n (E n) i.1 i.2 0 ω + ((gridStep s tt K n : ℝ) : ℂ) *
        ∑ j ∈ Finset.range k, STgDrift sz s tt K n (E n) i.1 i.2 j ω + Rem i k ω + Mart i k ω)
    (hRem : ∀ i : STLab sz n, ∀ k, k ≤ K n → ‖Rem i k ω‖ ≤ R)
    (hM : ∀ i : STLab sz n, ∀ k, k ≤ K n → ‖STgA sz s tt K n (E n) i.1 i.2 k ω‖ ≤ M)
    (hMart : ∀ i : STLab sz n, ∀ k, k ≤ K n → ‖Mart i k ω‖ ≤ Λ * Real.sqrt (∑ j ∈ Finset.range k,
      gridStep s tt K n * ‖STEEM sz n (E n) (gridTime s tt K n j) (pathH sz s tt K n j ω) i.1 i.2‖ +
        ((sz.size n : ℕ) : ℝ) ^ (-Dm)))
    (hELK : ∀ j, j ≤ K n → ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)),
      ‖STELKLKM sz n (E n) (gridTime s tt K n j) (pathH sz s tt K n j ω) σ b‖ ≤
        Λ * ((STAI sz n) ^ (-(1 / 3) : ℝ) * (etaT (E n) (gridTime s tt K n j))⁻¹ *
          STprof sz n (gridTime s tt K n j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1)))
    (hEGt : ∀ j, j ≤ K n → ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)),
      ‖STEGtM sz n (E n) (gridTime s tt K n j) (pathH sz s tt K n j ω) σ b‖ ≤
        Λ * ((STAI sz n) ^ (-(1 / 2) : ℝ) * (etaT (E n) (gridTime s tt K n j))⁻¹ *
          STprof sz n (gridTime s tt K n j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1)))
    (hEEk : ∀ j, j ≤ K n → ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)) (k : Fin 2),
      ‖STEEkM sz n (E n) (gridTime s tt K n j) (pathH sz s tt K n j ω) k σ b‖ ≤
        Λ * ((STAI sz n) ^ (-(1 / 2) : ℝ) * (etaT (E n) (gridTime s tt K n j))⁻¹ *
          STprof sz n (gridTime s tt K n j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1) ^ 2))
    (hfloor : 36 * ((1 - s n) / (1 - tt n)) ^ 2 * (Λ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm))) +
        64 * ((1 - tt n)⁻¹) ^ 7 * (R + gridStep s tt K n * M) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)) :
    ‖STgA sz s tt K n (E n) σ a (K n) ω - RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ (s n) (tt n)
        (fun b => STgA sz s tt K n (E n) σ b 0 ω) a‖ ≤
      (4 * C / c₀ + 8 * C * (2 / c₀ + 1)) * (Λ ^ 2 * (((1 - s n) / (1 - tt n)) ^ 3 * STAI sz n ^ (-(1 / 4) : ℝ))) *
          STprof sz n (tt n) D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) + ((sz.W n : ℕ) : ℝ) ^ (-D) := by
  obtain ⟨hΔ, hu1, hu0, huK, hKΔ, hmem, hmono⟩ := duhamelI_grid s tt K n hstt.le hK
  have hLn : 3 ≤ sz.L n := sz.three_le_L n
  have hw0 : 0 < tt n := lt_of_le_of_lt hs0 hstt
  have h1w : 0 < 1 - tt n := by linarith
  have hK1 : 1 ≤ K n := Nat.one_le_iff_ne_zero.2 hK
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  set ρ : ℝ := (1 - s n) / (1 - tt n) with hρdef
  have hρ1 : 1 ≤ ρ := by rw [hρdef, le_div_iff₀ h1w]; linarith
  set A := STAI sz n with hAdef
  obtain ⟨ha₄0, ha₄1, ha₂, ha₃⟩ := duhamelI_rpow_quarter hA
  set a₄ := A ^ (-(1 / 4) : ℝ) with ha₄def
  set Wd := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ with hWd
  have hWd0 : 0 < Wd := by positivity
  set T : ℝ := tailT d (sz.L n) (sz.lam n) (tt n) ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) with hT
  set P : ℝ := STprof sz n (tt n) D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) with hP
  set WmE : ℝ := ((sz.W n : ℕ) : ℝ) ^ (-DE) with hWmE
  set WmD : ℝ := ((sz.W n : ℕ) : ℝ) ^ (-D) with hWmD
  have hT0 : 0 ≤ T := tailT_nonneg (Nat.cast_nonneg _)
  have hWmE0 : 0 ≤ WmE := Real.rpow_nonneg hW.le _
  have hWmD0 : 0 ≤ WmD := Real.rpow_nonneg hW.le _
  have hZP : Wd * (T + ρ * WmE) ≤ 2 * P := by
    have hP' : P = Wd * max T WmD := by
      rw [hP]; unfold STprof; rw [duhamelI_tailW_eq]
    rw [hP']
    calc Wd * (T + ρ * WmE) ≤ Wd * (T + WmD) := mul_le_mul_of_nonneg_left (by linarith [hDE]) hWd0.le
      _ ≤ Wd * (2 * max T WmD) :=
          mul_le_mul_of_nonneg_left (by linarith [le_max_left T WmD, le_max_right T WmD]) hWd0.le
      _ = 2 * (Wd * max T WmD) := by ring
  have hZP' : Wd * (T + WmE) ≤ 2 * P := le_trans (mul_le_mul_of_nonneg_left (by nlinarith) hWd0.le) hZP
  -- the grid
  set u : ℕ → ℝ := gridTime s tt K n with hu
  set Δ : ℝ := gridStep s tt K n with hΔdef
  have hu_s : ∀ j ≤ K n, s n ≤ u j := fun j hj => (hmem j hj).1
  have hu_w : ∀ j ≤ K n, u j ≤ tt n := fun j hj => (hmem j hj).2
  have hmono' : ∀ j < K n, u j ≤ u (j + 1) := hmono
  -- the Duhamel formula on the grid
  have hdu := pfStep5Grid_duhamel d (sz.L n) hLn (sz.lam n) (E n) Δ M R σ (K n) u
    (fun j b => STgA sz s tt K n (E n) σ b j ω)
    (fun j b => STELKLKM sz n (E n) (u j) (pathH sz s tt K n j ω) σ b +
      STEGtM sz n (E n) (u j) (pathH sz s tt K n j ω) σ b)
    (fun j b => Rem (σ, b) j ω) (fun j b => Mart (σ, b) j ω) hE hΔ (by rw [hu0]; exact hs0) hu1
    (by rw [huK]; exact htt1) (fun j hj b => hM (σ, b) j hj) (fun j hj b => hRem (σ, b) j hj)
    (fun j hj b => by
      have h := hid (σ, b) j hj
      have e : ∀ i, STgDrift sz s tt K n (E n) σ b i ω =
          ThetaN d (sz.L n) (sz.lam n) (fun i' => mSigma (E n) (σ i')) (u i)
            (fun b' => STgA sz s tt K n (E n) σ b' i ω) b +
          (STELKLKM sz n (E n) (u i) (pathH sz s tt K n i ω) σ b +
            STEGtM sz n (E n) (u i) (pathH sz s tt K n i ω) σ b) := by
        intro i
        unfold STgDrift
        rw [STthetaOp_eq_ThetaN, add_assoc]
        rfl
      simp only [e] at h
      exact h) a
  rw [hu0, huK] at hdu
  set Fj : ℕ → (Fin 2 → Zd d (sz.L n)) → ℂ := fun j b =>
    STELKLKM sz n (E n) (u j) (pathH sz s tt K n j ω) σ b +
      STEGtM sz n (E n) (u j) (pathH sz s tt K n j ω) σ b with hFj
  set Iv : ℂ := RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ (s n) (tt n)
    (fun b => STgA sz s tt K n (E n) σ b 0 ω) a with hIv
  set Dr : ℂ := ∑ j ∈ Finset.range (K n), (Δ : ℂ) *
    RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ (u j) (tt n) (Fj j) a with hDr
  set Mr : ℂ := ∑ j ∈ Finset.range (K n), RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ (u j) (tt n)
    (fun b => Mart (σ, b) (j + 1) ω - Mart (σ, b) j ω) a with hMr
  have hsplit : ‖STgA sz s tt K n (E n) σ a (K n) ω - Iv‖ ≤
      ‖Dr‖ + ‖Mr‖ + 64 * ((1 - tt n)⁻¹) ^ 7 * (R + Δ * M) := by
    set X := STgA sz s tt K n (E n) σ a (K n) ω with hX
    have e : X - Iv = (X - Iv - Dr - Mr) + Dr + Mr := by ring
    have h1 := norm_add_le (X - Iv - Dr - Mr + Dr) Mr
    have h2 := norm_add_le (X - Iv - Dr - Mr) Dr
    have hdu' : ‖X - Iv - Dr - Mr‖ ≤ 64 * ((1 - tt n)⁻¹) ^ 7 * (R + Δ * M) := hdu
    rw [e]
    linarith
  -- the drift
  have hF : ∀ j ≤ K n, ∀ b : Fin 2 → Zd d (sz.L n), ‖Fj j b‖ ≤
      (Λ * (2 * a₄) * (etaT (E n) (u j))⁻¹) * STprof sz n (u j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1) := by
    intro j hj b
    have hu_lt : u j < 1 := (hu_w j hj).trans_lt htt1
    have hη0 : 0 ≤ (etaT (E n) (u j))⁻¹ := inv_nonneg.2 (by
      unfold etaT; exact (mul_pos (by linarith) (lt_of_lt_of_le hc₀ hc)).le)
    have hp0 := (ST_STprof_pos sz n (u j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1)).le
    have h1 := hELK j hj σ b
    have h2 := hEGt j hj σ b
    have h3 : A ^ (-(1 / 2) : ℝ) ≤ a₄ := by rw [ha₂]; nlinarith
    refine (norm_add_le _ _).trans ?_
    calc _ ≤ Λ * (A ^ (-(1 / 3) : ℝ) * (etaT (E n) (u j))⁻¹ *
          STprof sz n (u j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1)) +
        Λ * (A ^ (-(1 / 2) : ℝ) * (etaT (E n) (u j))⁻¹ *
          STprof sz n (u j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1)) := add_le_add h1 h2
      _ ≤ Λ * (a₄ * (etaT (E n) (u j))⁻¹ * STprof sz n (u j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1)) +
        Λ * (a₄ * (etaT (E n) (u j))⁻¹ * STprof sz n (u j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1)) := by
          gcongr
      _ = _ := by ring
  have hDr_le := duhamelI_drift sz n (E := E n) (s := s n) (w := tt n) (Λ := Λ) (DE := DE) (C := C) (c₀ := c₀)
    (e₀ := 2 * a₄) (Δ := Δ) (K := K n) u Fj σ a hs0 hstt htt1 hE (by linarith) hC (by linarith) hc₀ hc hΔ hKΔ
    hu_s hu_w hΦ hF
  have hMart' : ∀ (b : Fin 2 → Zd d (sz.L n)) (j : ℕ), j ≤ K n →
      ‖Mart (σ, b) j ω‖ ≤ Λ * Real.sqrt (∑ i ∈ Finset.range j, Δ * ‖STEEM sz n (E n) (u i)
        (pathH sz s tt K n i ω) σ b‖ + ((sz.size n : ℕ) : ℝ) ^ (-Dm)) := fun b j hj => hMart (σ, b) j hj
  have hMr_le := duhamelI_mart sz n (E := E n) (s := s n) (w := tt n) (Λ := Λ) (DE := DE) (Dm := Dm) (C := C)
    (c₀ := c₀) (Δ := Δ) (K := K n) u (fun j b => Mart (σ, b) j ω)
    (fun j b => ‖STEEM sz n (E n) (u j) (pathH sz s tt K n j ω) σ b‖) σ a hK1 hs0 hstt htt1 hE hlam hΛ hA hc₀ hc
    hΔ hKΔ hu0 hu_s hu_w hmono' hΦ (fun j b => norm_nonneg _)
    (fun j hj b => by
      have h3 : STEEM sz n (E n) (u j) (pathH sz s tt K n j ω) σ b =
          STEEkM sz n (E n) (u j) (pathH sz s tt K n j ω) 0 σ b +
            STEEkM sz n (E n) (u j) (pathH sz s tt K n j ω) 1 σ b := rfl
      rw [h3]
      have := add_le_add (hEEk j hj σ b 0) (hEEk j hj σ b 1)
      refine (norm_add_le _ _).trans (this.trans (le_of_eq ?_))
      ring) hMart'
  have hP0 : 0 ≤ P := (ST_STprof_pos sz n _ _ _ _ _).le
  clear hELK hEGt hEEk hMart hMart' hid hRem hM hF hdu
  have hDr2 : ‖Dr‖ ≤ (4 * C / c₀) * (Λ ^ 2 * (ρ ^ 3 * a₄)) * P := by
    refine hDr_le.trans ?_
    have h1 : Λ * (2 * a₄) * (ρ / c₀) * (C * ρ * (Wd * (T + ρ * WmE))) ≤
        Λ * (2 * a₄) * (ρ / c₀) * (C * ρ * (2 * P)) := by gcongr
    refine h1.trans ?_
    have e : Λ * (2 * a₄) * (ρ / c₀) * (C * ρ * (2 * P)) = (4 * C / c₀) * (Λ * ρ ^ 2 * a₄) * P := by ring
    rw [e]
    have h2 : Λ * ρ ^ 2 * a₄ ≤ Λ ^ 2 * (ρ ^ 3 * a₄) := by
      have : Λ * ρ ^ 2 ≤ Λ ^ 2 * ρ ^ 3 := mul_le_mul (by nlinarith) (by nlinarith) (by positivity) (by positivity)
      nlinarith
    gcongr
  have hMr2 : ‖Mr‖ ≤ (8 * C * (2 / c₀ + 1)) * (Λ ^ 2 * (ρ ^ 3 * a₄)) * P +
      36 * ρ ^ 2 * (Λ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm))) := by
    refine hMr_le.trans ?_
    have h1 : 4 * ((Λ * (Λ * ρ * (2 / c₀ + 1) * a₄)) * (ρ ^ 2 * (C * (Wd * (T + WmE)))) +
        (Λ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm))) * (9 * ρ ^ 2)) ≤
        4 * ((Λ * (Λ * ρ * (2 / c₀ + 1) * a₄)) * (ρ ^ 2 * (C * (2 * P))) +
        (Λ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm))) * (9 * ρ ^ 2)) := by gcongr
    refine h1.trans (le_of_eq ?_)
    ring
  have e : (4 * C / c₀ + 8 * C * (2 / c₀ + 1)) * (Λ ^ 2 * (ρ ^ 3 * a₄)) * P =
      (4 * C / c₀) * (Λ ^ 2 * (ρ ^ 3 * a₄)) * P + (8 * C * (2 / c₀ + 1)) * (Λ ^ 2 * (ρ ^ 3 * a₄)) * P := by ring
  rw [e]
  linarith

end Path

/-! ## 4. Hölder continuity of `Q^{(1)}(𝓛-𝒦)_u` in `u` -/

section Holder

open RBM.Ind.ContinuityNet

variable {d : ℕ}

/-- `u ↦ ‖Q^{(1)}(𝓛-𝒦)^{(2)}_{u,σ,a}‖` is Hölder-1/2 on `contGood`, constant `N^{12}`: `LemDecCalELip_LK_sub` (the norm of the
difference of the loops, not the difference of the norms) at the labels `a` and `(c, a₂)`, and `‖Q X‖ ≤ ‖X_a‖ + L^{-d} Σ_c ‖X_{(c,a₂)}‖`. -/
private theorem duhamelII_holder (sz : Sizes d) (E s t : ℕ → ℝ) (κ : ℝ) (hsize : sz.SizeTendsto) (hκ : 0 < κ)
    (hE : ∀ n, |E n| ≤ 2 - κ) (hs : ∀ n, 0 ≤ s n) (ht : ∀ n, t n < 1)
    (htN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ contGood sz n, ∀ (u u' : TimeIcc s t n) (σ : Fin 2 → Bool)
      (a : Fin 2 → Zd d (sz.L n)),
      |‖zeroModeSet d (sz.L n) {0} (fun a' => STLKM sz n (E n) (u : ℝ) (sz.seqHflow n (u : ℝ) ω) σ a') a‖ -
          ‖zeroModeSet d (sz.L n) {0} (fun a' => STLKM sz n (E n) (u' : ℝ) (sz.seqHflow n (u' : ℝ) ω) σ a') a‖| ≤
        ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)| := by
  refine ⟨((12 : ℕ) : ℝ), Nat.cast_nonneg _, ?_⟩
  filter_upwards [LemDecCalELip_env sz E t κ hκ hE hsize htN 14] with n hn ω hω u u' σ a
  obtain ⟨h14, h1, hE2, hQ, hN1⟩ := hn
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  set x : ℝ := Real.sqrt |(u : ℝ) - (u' : ℝ)| with hx
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hb : ∀ b : Fin 2 → Zd d (sz.L n),
      ‖STLKM sz n (E n) (u : ℝ) (sz.seqHflow n (u : ℝ) ω) σ b -
        STLKM sz n (E n) (u' : ℝ) (sz.seqHflow n (u' : ℝ) ω) σ b‖ ≤ 7 * N ^ 11 * x := fun b =>
    LemDecCalELip_LK_sub sz n (E n) ω (N := N) rfl h1 hE2 (ht n) ((hs n).trans u.2.1) u.2.2 ((hs n).trans u'.2.1)
      u'.2.2 hQ (fun c => hω c) hN1 σ b
  refine (abs_norm_sub_norm_le _ _).trans ((duhamelII_Q_sub_le _ _ a).trans ?_)
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := by
    have := sz.three_le_L n
    have : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < sz.L n)
    positivity
  have hsum : (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * ∑ c : Zd d (sz.L n),
      ‖STLKM sz n (E n) (u : ℝ) (sz.seqHflow n (u : ℝ) ω) σ (Function.update a 0 c) -
        STLKM sz n (E n) (u' : ℝ) (sz.seqHflow n (u' : ℝ) ω) σ (Function.update a 0 c)‖ ≤ 7 * N ^ 11 * x := by
    calc _ ≤ (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * ∑ _c : Zd d (sz.L n), 7 * N ^ 11 * x :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => hb _) (inv_nonneg.2 hL0.le)
      _ = 7 * N ^ 11 * x := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_Zd]
          push_cast
          field_simp
  have h11 : 14 * N ^ 11 ≤ N ^ 12 := by
    have : 0 ≤ N ^ 11 := by positivity
    calc 14 * N ^ 11 ≤ N * N ^ 11 := mul_le_mul_of_nonneg_right h14 this
      _ = N ^ 12 := by ring
  rw [Real.rpow_natCast]
  nlinarith [hb a, hsum, mul_le_mul_of_nonneg_right h11 hx0]

end Holder

/-! ## 5. The per-section statement with `Q^{(1)}` -/

section Prob

variable {d : ℕ}

/-- `Q^{(1)}(𝓛-𝒦)_u` is a measurable function of the matrix. -/
private theorem duhamelII_QLK_meas (sz : Sizes d) (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      ‖zeroModeSet d (sz.L n) {0} (fun a' => STLKM sz n E u H σ a') a‖ := by
  simp only [duhamelII_Q_apply]
  exact ((STLKM_measurable sz n E u σ a).sub (measurable_const.mul
    (Finset.measurable_sum _ fun c _ => STLKM_measurable sz n E u σ _))).norm

/-- `1 - s ≤ ilambda²/L²` gives `1 - s ≤ ilambda²` (`L ≥ 1`). -/
private theorem duhamelII_mid (sz : Sizes d) (n : ℕ) {s : ℝ} (h : 1 - s ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) :
    1 - s ≤ sz.lam n ^ 2 := by
  have hL : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  exact h.trans (div_le_self (sq_nonneg _) (one_le_pow₀ hL))

/-- The chain `‖Q X‖ ≤ ‖Q I‖ + ‖Q X - Q I‖`, `‖Q X - Q I‖ ≤ R₀ + R_s` and the bounds of the three terms (plain arithmetic, a small context). -/
private theorem duhamelII_chain {QX QI QD R0 Rs Λ F Bk CA P Wm : ℝ} (hins : QX ≤ QI + QD) (hQ : QD ≤ R0 + Rs)
    (hI : QI ≤ Λ * F) (hR0 : R0 ≤ Bk * P + Wm) (hsum : Rs ≤ Bk * (CA * P) + Wm) :
    QX ≤ Λ * F + (Bk * P + Bk * (CA * P)) + 2 * Wm := by
  linarith

/-- The exponent closure with the doubled floor (`duhamelI_absorb` at `W_m = 2 W^{-D}`):
`Y ≤ Λ F + Λ² κ ρ³ A^{-1/4} P + 2 W^{-D}` gives `Y ≤ N^τ (F + A^{-1/5} P + W^{-D})` if `2 (2κ+1) Λ² ≤ N^τ`. -/
private theorem duhamelII_close {Λ κ F P Wm A ρ Nτ Y : ℝ} (hΛ : 1 ≤ Λ) (hκ : 0 ≤ κ) (hF : 0 ≤ F) (hP : 0 ≤ P)
    (hWm : 0 ≤ Wm) (hA : 1 ≤ A) (hρ1 : 1 ≤ ρ) (hρ : ρ ≤ (2 * A) ^ (1 / 100 : ℝ))
    (hN : 2 * ((2 * κ + 1) * Λ ^ 2) ≤ Nτ) (hY : Y ≤ Λ * F + Λ ^ 2 * κ * (ρ ^ 3 * A ^ (-(1 / 4) : ℝ)) * P + 2 * Wm) :
    Y ≤ Nτ * (F + A ^ (-(1 / 5) : ℝ) * P + Wm) := by
  have habs := duhamelI_absorb (Λ := Λ) (κ := κ) (F := F) (P := P) (Wm := 2 * Wm) (A := A) (ρ := ρ)
    (Nτ := (2 * κ + 1) * Λ ^ 2) hΛ hκ hF hP (by linarith) hA hρ1 hρ le_rfl
  have hA5 : 0 ≤ A ^ (-(1 / 5) : ℝ) := Real.rpow_nonneg (by linarith) _
  have hX0 : 0 ≤ F + A ^ (-(1 / 5) : ℝ) * P := add_nonneg hF (mul_nonneg hA5 hP)
  have hc : 0 ≤ (2 * κ + 1) * Λ ^ 2 := by positivity
  have h2c : (2 * κ + 1) * Λ ^ 2 * (F + A ^ (-(1 / 5) : ℝ) * P + 2 * Wm) ≤
      2 * ((2 * κ + 1) * Λ ^ 2) * (F + A ^ (-(1 / 5) : ℝ) * P + Wm) := by
    nlinarith [mul_nonneg hc hX0, mul_nonneg hc hWm]
  have h3c : 2 * ((2 * κ + 1) * Λ ^ 2) * (F + A ^ (-(1 / 5) : ℝ) * P + Wm) ≤ Nτ * (F + A ^ (-(1 / 5) : ℝ) * P + Wm) :=
    mul_le_mul_of_nonneg_right hN (by linarith)
  linarith

/-- **The per-section statement with `Q^{(1)}`**: at a section `tt n ∈ [s_n, t_n]` the family `‖Q^{(1)}(𝓛-𝒦)^{(2)}_{tt,σ,a}‖` is
dominated by `F + A^{-1/5} W^{-d}𝒯̃^L_{tt,D} + W^{-D}` on the model, given `‖Q^{(1)} 𝒰_{s,tt}(𝓛-𝒦)_s‖ ≺ F`,
`STEtermsMidConcl` and `(con_st_ind)`, in the regime `ilambda²/L^d ≤ 1-t ≤ 1-s ≤ ilambda²/L²`.  The grid and the six events are those of
`duhamelI_section` (the events at the grid times are over all labels); the initial-term event is the `Q^{(1)}`-form, and at the
end `Q^{(1)}` is applied to the remainder at the labels `(σ, (c, a₂))`, `c ∈ Z_L^d` (`duhamelII_path_rem`, `duhamelII_prof_avg`). -/
private theorem duhamelII_section (hd : 3 ≤ d) {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (sz : Sizes d)
    {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (htz : ∀ n, t n ≤ lemT (z n)) (hReg : STReg5II sz s t)
    (hCon : STConStInd sz (1 / 100) s t) (hE : STEtermsMidConcl sz (STflowE z) s t)
    {D : ℝ} (hD : 0 < D) (P : (Fin 2 → Bool) → Prop) (F : ∀ n, STIdx2P sz P s t n → ℝ)
    (hF0 : ∀ n p, 0 ≤ F n p)
    (hini : sz.Prec (U := STIdx2P sz P s t) (fun n p ω => ‖zeroModeSet d (sz.L n) {0} (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n)
      p.2.1.1 (s n) (p.1 : ℝ) (fun b => STLKM sz n (STflowE z n) (s n) (sz.seqHflow n (s n) ω) p.2.1.1 b)) p.2.2‖) (fun n p _ => F n p))
    (tt : ∀ n, TimeIcc s t n) :
    sz.Prec (U := fun n => {σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n)))
      (fun n v ω => ‖zeroModeSet d (sz.L n) {0}
        (fun a' => STLKM sz n (STflowE z n) (tt n : ℝ) (sz.seqHflow n (tt n : ℝ) ω) v.1.1 a') v.2‖)
      (fun n v _ => F n (tt n, v) + STAI sz n ^ (-(1 / 5) : ℝ) *
        STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D)) := by
  classical
  by_cases hP : ∃ σ, P σ
  swap
  · exact st5_prec_of_isEmpty sz (fun n => ⟨fun v => hP ⟨v.1.1, v.1.2⟩⟩)
  have : ∀ n, Nonempty ({σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n))) :=
    fun n => ⟨(⟨hP.choose, hP.choose_spec⟩, fun _ => 0)⟩
  obtain ⟨hAdm, hEn, ht1, -⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow htz
  have hsN := tendsto_size sz hAdm.2.2.1
  intro τ hτ D' hD'
  obtain ⟨C, hC, hΦC⟩ := duhamelI_Phi_STprof hd (Λ := 𝔡⁻¹) (inv_pos.2 h𝔡)
  obtain ⟨CA, hCA, hAvg⟩ := duhamelII_prof_avg hd
  have hmid : ∀ n, 1 - s n ≤ sz.lam n ^ 2 := fun n => duhamelII_mid sz n (hReg n).2
  set c₀ : ℝ := Real.sqrt κ / 2 with hc₀def
  have hc₀ : 0 < c₀ := by positivity
  set κs : ℝ := 4 * C / c₀ + 8 * C * (2 / c₀ + 1) with hκs
  set κq : ℝ := κs * (1 + CA) with hκq
  have hκs0 : 0 ≤ κs := by rw [hκs]; positivity
  have hκq0 : 0 ≤ κq := by rw [hκq]; positivity
  obtain ⟨C₀, hC₀, hAt⟩ := ST_gridMart_of_repN (RBM.Ind.stGridRepN_holds d hd)
  set DE : ℝ := D + d + 2 with hDE
  set Dm : ℝ := 2 * (D + D' + 6 + τ) with hDm
  obtain ⟨CK, hCK0, hK⟩ := hAt κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s (fun n => (tt n : ℝ)) hs (fun n => (tt n).2.1)
    (fun n => (tt n).2.2.trans (htz n)) Dm (by positivity)
  set x₀ : ℝ := max CK (2 * (C₀ + D + 12)) with hx₀
  set m : ℕ := ⌈x₀⌉₊ with hm
  set K : ℕ → ℕ := fun n => (sz.size n) ^ m with hKdef
  have hKne : ∀ n, K n ≠ 0 := fun n => pow_ne_zero _ (by have := sz.one_le_size n; omega)
  have hKbig : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n := by
    filter_upwards [hsN.eventually (eventually_ge_atTop 1)] with n hn
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hn
    have h1 : CK ≤ (m : ℝ) := (le_max_left _ _).trans (Nat.le_ceil x₀)
    calc ((sz.size n : ℕ) : ℝ) ^ CK ≤ ((sz.size n : ℕ) : ℝ) ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 h1
      _ = K n := by rw [Real.rpow_natCast]; simp [hKdef]
  obtain ⟨Mart, Rem, hid, hrem, hmart⟩ := hK K hKne hKbig
  set τ₁ : ℝ := τ / 4 with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  obtain ⟨hE1, hE2, hE3⟩ := hE DE (by positivity)
  -- card bounds
  have hcardV : ∀ᶠ n in atTop, (Fintype.card ({σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n))) : ℝ) ≤
      ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) := by
    filter_upwards [hsN.eventually (eventually_ge_atTop 4)] with n hn
    exact duhamelI_card_le sz P n hn
  have hcardK : ∀ (c : ℕ → ℕ), (∀ᶠ n in atTop, (c n : ℝ) ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ)) →
      ∀ᶠ n in atTop, (((K n + 1) * c n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (((m + 5 : ℕ) : ℝ)) := fun c hc => by
    filter_upwards [hc, hsN.eventually (eventually_ge_atTop 4)] with n h1 h2
    exact duhamelI_cardK (sz.size n) m (c n) h2 h1
  -- E1: the initial term at the grid index `0`
  have hΞ1 := ST_grid_whp_zero sz (V := fun n => {σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n))) s
    (fun n => (tt n : ℝ)) K hs (fun n => (tt n).2.1) hKne (C := 3) (by norm_num) hcardV
    (fun n v u H => ‖zeroModeSet d (sz.L n) {0} (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) v.1.1 (s n) (tt n : ℝ)
      (fun b => STLKM sz n (STflowE z n) u H v.1.1 b)) v.2‖) (fun n v u H => F n (tt n, v))
    (fun n v u => duhamelII_QUgen_meas sz n _ u _ _ _ v.2) (fun n v u => measurable_const) τ₁ hτ₁0
    (StochDomAt.precomp_param hini (fun n v => (tt n, v)))
  -- E2, E3, E4: the three error terms at every grid index
  have hcardL : ∀ᶠ n in atTop, (Fintype.card (sz.STLab n) : ℝ) ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) := by
    filter_upwards [hsN.eventually (eventually_ge_atTop 4)] with n hn
    have := ST_card_lab_le sz n hn
    have h0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith
  have hcardL2 : ∀ᶠ n in atTop, (Fintype.card (sz.STLab n × Fin 2) : ℝ) ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) := by
    filter_upwards [hsN.eventually (eventually_ge_atTop 4)] with n hn
    have := ST_card_lab_le sz n hn
    rw [Fintype.card_prod, Fintype.card_fin]; push_cast
    linarith
  have hΞ2 := duhamelI_whp_sec (V := fun n => sz.STLab n) sz tt K hs hKne (C := ((m + 5 : ℕ) : ℝ)) (by positivity)
    (hcardK _ hcardL)
    (fun n v u H => ‖STELKLKM sz n (STflowE z n) u H v.1 v.2‖)
    (fun n v u H => STAI sz n ^ (-(1 / 3) : ℝ) * (etaT (STflowE z n) u)⁻¹ *
      STprof sz n u DE ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1))
    (fun n v u => (duhamelI_ELKLK_meas sz n _ u v.1 v.2).norm) (fun n v u => measurable_const) hτ₁0 hE1
  have hΞ3 := duhamelI_whp_sec (V := fun n => sz.STLab n) sz tt K hs hKne (C := ((m + 5 : ℕ) : ℝ)) (by positivity)
    (hcardK _ hcardL)
    (fun n v u H => ‖STEGtM sz n (STflowE z n) u H v.1 v.2‖)
    (fun n v u H => STAI sz n ^ (-(1 / 2) : ℝ) * (etaT (STflowE z n) u)⁻¹ *
      STprof sz n u DE ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1))
    (fun n v u => (STEGtM_measurable sz n _ u v.1 v.2).norm) (fun n v u => measurable_const) hτ₁0 hE2
  have hΞ4 := duhamelI_whp_sec (V := fun n => sz.STLab n × Fin 2) sz tt K hs hKne (C := ((m + 5 : ℕ) : ℝ)) (by positivity)
    (hcardK _ hcardL2)
    (fun n v u H => ‖STEEkM sz n (STflowE z n) u H v.2 v.1.1 v.1.2‖)
    (fun n v u H => STAI sz n ^ (-(1 / 2) : ℝ) * (etaT (STflowE z n) u)⁻¹ *
      STprof sz n u DE ((sz.L n : ℕ) : ℝ) (v.1.2 0) (v.1.2 1) ^ 2)
    (fun n v u => (STEEkM_measurable sz n _ u v.2 v.1.1 v.1.2).norm) (fun n v u => measurable_const) hτ₁0
    (StochDomAt.precomp_param hE3 (fun n (p : TimeIcc s t n × (sz.STLab n × Fin 2)) =>
      (((p.1, p.2.1), p.2.2) : sz.STIdx2 s t n × Fin 2)))
  have hΞ := hΞ1.inter hsN (hΞ2.inter hsN (hΞ3.inter hsN hΞ4))
  -- E5: the martingale tails of all labels
  have hmartE : ∀ᶠ n in atTop, pathP sz (⋃ i : sz.STLab n, {ω | ∃ k, k ≤ K n ∧
      ((sz.size n : ℕ) : ℝ) ^ τ₁ * (∑ j ∈ Finset.range k, gridStep s (fun m => (tt m : ℝ)) K n *
        ‖STEEM sz n (STflowE z n) (gridTime s (fun m => (tt m : ℝ)) K n j)
          (pathH sz s (fun m => (tt m : ℝ)) K n j ω) i.1 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-Dm)) ^ (1 / 2 : ℝ) <
        ‖Mart n i k ω‖}) ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D' + 1))) := by
    filter_upwards [hmart τ₁ hτ₁0, hsN.eventually (eventually_ge_atTop 4)] with n hn h4
    exact ST_union_prob (pathP sz) _ (by exact_mod_cast (by omega : 1 ≤ sz.size n)) (ST_card_lab_le sz n h4)
      (by rw [hDm]; nlinarith) hn
  -- E6: the almost sure identities
  have hae : ∀ᶠ n in atTop, ∀ᵐ ω ∂(pathP sz), ∀ i : sz.STLab n,
      (∀ k, k ≤ K n → STgA sz s (fun m => (tt m : ℝ)) K n (STflowE z n) i.1 i.2 k ω =
        STgA sz s (fun m => (tt m : ℝ)) K n (STflowE z n) i.1 i.2 0 ω +
          ((gridStep s (fun m => (tt m : ℝ)) K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k,
            STgDrift sz s (fun m => (tt m : ℝ)) K n (STflowE z n) i.1 i.2 j ω + Rem n i k ω + Mart n i k ω) ∧
      (∀ k, k ≤ K n → ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s (fun m => (tt m : ℝ)) K n)) := by
    filter_upwards [hrem] with n hn
    exact ae_all_iff.2 fun i => (hid n i).and (hn i)
  -- numerical facts
  have hWO := hAdm.2.2.2.2
  have hev := st5_eventually_A_ge_one sz h𝔡 hWO
  have hWbig : ∀ᶠ n in atTop, 2 * 𝔡⁻¹ ^ 2 ≤ ((sz.W n : ℕ) : ℝ) := by
    filter_upwards [hAdm.2.2.2.1, hsN.eventually (eventually_le_rpow (2 * 𝔡⁻¹ ^ 2) hAdm.1)] with n h1 h2
    exact h2.trans h1
  have hNc : ∀ᶠ n in atTop, c₀⁻¹ ^ 2 ≤ ((sz.size n : ℕ) : ℝ) := hAdm.2.2.1.eventually (eventually_ge_atTop _)
  have hNτ : ∀ᶠ n in atTop, 2 * (2 * κq + 1) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    hsN.eventually (eventually_le_rpow _ (half_pos hτ))
  have hiniE := StochDomAt.precomp_param hini (fun n v => (tt n, v))
  filter_upwards [hiniE τ hτ D' hD', hev, hWO, hWbig, hNc, hNτ, hCon, hmartE, hae, hΞ (D' + 1) (by linarith),
    hsN.eventually (eventually_ge_atTop 256)] with n hini1 hAn hWOn hWb hNcn hNτn hCon1 hmartn haen hΞn h256
  obtain ⟨hlam, hA1⟩ := hAn
  have hlamle : sz.lam n ≤ 𝔡⁻¹ := hWOn.2
  have hE2 : |STflowE z n| ≤ 2 := ((hEn n).le).trans (by linarith)
  have htt1 : (tt n : ℝ) < 1 := (tt n).2.2.trans_lt (ht1 n)
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hN256 : (256 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast h256
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
  have hΛ : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ := Real.one_le_rpow hN1 hτ₁0.le
  by_cases hsn : s n < (tt n : ℝ)
  swap
  · -- the section is the initial time: `𝒰_{s,s} = 1`
    have hts : (tt n : ℝ) = s n := le_antisymm (not_lt.1 hsn) (tt n).2.1
    refine le_trans (measure_mono ?_) hini1
    rintro ω ⟨v, hv⟩
    refine ⟨v, ?_⟩
    have hs1 : s n < 1 := (hst n).trans (ht1 n)
    have hU := RBM.Ind.GridDuhamelN_Ugen_self (g := sz.lam n) (sz.three_le_L n) hE2 v.1.1 (hs n) hs1
      (fun b => STLKM sz n (STflowE z n) (s n) (sz.seqHflow n (s n) ω) v.1.1 b)
    have hF1 : 0 ≤ STAI sz n ^ (-(1 / 5) : ℝ) * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1) +
        ((sz.W n : ℕ) : ℝ) ^ (-D) := add_nonneg (mul_nonneg (Real.rpow_nonneg (by unfold STAI; positivity) _)
          (ST_STprof_pos sz n _ _ _ _ _).le) (Real.rpow_nonneg hW0.le _)
    simp only [hts] at hv hF1 ⊢
    rw [hU]
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by linarith) _)) hv
    linarith [hF0 n (tt n, v)]
  -- the main case: `s n < tt n`
  have hs1 : s n < 1 := (hst n).trans (ht1 n)
  have h1tt : 0 < 1 - (tt n : ℝ) := by linarith
  have htN : (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := duhamelI_htN sz n hlam hA1 (hReg n).1
  have hTi : (1 - (tt n : ℝ))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) :=
    (inv_anti₀ (by linarith [ht1 n]) (by linarith [(tt n).2.2])).trans htN
  have hρA := duhamelI_rho sz n hlam (tt n).2.1 (tt n).2.2 (ht1 n) (by linarith [hmid n, (hst n)]) hCon1.1
  set ρ : ℝ := (1 - s n) / (1 - (tt n : ℝ)) with hρdef
  have hρ1 : 1 ≤ ρ := by rw [hρdef, le_div_iff₀ h1tt]; linarith
  have hρN : ρ ≤ ((sz.size n : ℕ) : ℝ) :=
    ((div_le_div_of_nonneg_right (by linarith [hs n]) h1tt.le).trans_eq (one_div _)).trans hTi
  have hx₀m : x₀ ≤ (m : ℝ) := Nat.le_ceil x₀
  have hKx : ((sz.size n : ℕ) : ℝ) ^ x₀ ≤ K n := by
    calc ((sz.size n : ℕ) : ℝ) ^ x₀ ≤ ((sz.size n : ℕ) : ℝ) ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hx₀m
      _ = K n := by rw [Real.rpow_natCast]; simp [hKdef]
  have hΔ : gridStep s (fun m => (tt m : ℝ)) K n ≤ ((sz.size n : ℕ) : ℝ) ^ (-x₀) := by
    have hKpos : (0 : ℝ) < K n := by exact_mod_cast Nat.pos_of_ne_zero (hKne n)
    have hNx : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) ^ x₀ := Real.rpow_pos_of_pos (by linarith) _
    unfold gridStep
    calc ((tt n : ℝ) - s n) / K n ≤ 1 / K n := div_le_div_of_nonneg_right (by linarith [(tt n).2.2, ht1 n, hs n]) hKpos.le
      _ ≤ 1 / ((sz.size n : ℕ) : ℝ) ^ x₀ := one_div_le_one_div_of_le hNx hKx
      _ = _ := by rw [Real.rpow_neg (by linarith), one_div]
  have hWN := duhamelI_W_le_size sz (by omega : d ≠ 0) n
  have hWm : ((sz.size n : ℕ) : ℝ) ^ (-D) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) :=
    Real.rpow_le_rpow_of_nonpos hW0 hWN (neg_nonpos.2 hD.le)
  have hfloor := duhamelI_floor (Δ := gridStep s (fun m => (tt m : ℝ)) K n) (Wm := ((sz.W n : ℕ) : ℝ) ^ (-D))
    (C₀ := C₀) (c₀ := c₀) (D := D) (τ := τ) (Dm := Dm) (x := x₀) (ρ := ρ) (Ti := (1 - (tt n : ℝ))⁻¹) hN256 hNcn hτ hD hC₀
    (by linarith) hρN (inv_nonneg.2 h1tt.le) hTi (div_nonneg (by linarith [(tt n).2.1]) (by exact_mod_cast Nat.zero_le _)) hΔ hWm
    (by rw [hDm]; linarith) (le_max_right _ _)
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hDEn : ρ * ((sz.W n : ℕ) : ℝ) ^ (-DE) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := by
    have h2A : (1 : ℝ) ≤ 2 * STAI sz n := by linarith
    have hρ2 : ρ ≤ 2 * STAI sz n := hρA.trans (by
      calc (2 * STAI sz n) ^ (1 / 100 : ℝ) ≤ (2 * STAI sz n) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h2A (by norm_num)
        _ = 2 * STAI sz n := Real.rpow_one _)
    have hA2 : 2 * STAI sz n ≤ ((sz.W n : ℕ) : ℝ) ^ (d + 1) := by
      unfold STAI
      calc 2 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ≤ 2 * (𝔡⁻¹ ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) := by
            gcongr
        _ = (2 * 𝔡⁻¹ ^ 2) * ((sz.W n : ℕ) : ℝ) ^ d := by ring
        _ ≤ ((sz.W n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ d := mul_le_mul_of_nonneg_right hWb (by positivity)
        _ = _ := by ring
    calc ρ * ((sz.W n : ℕ) : ℝ) ^ (-DE) ≤ ((sz.W n : ℕ) : ℝ) ^ (d + 1) * ((sz.W n : ℕ) : ℝ) ^ (-DE) :=
          mul_le_mul_of_nonneg_right (hρ2.trans hA2) (Real.rpow_nonneg hW0.le _)
      _ = ((sz.W n : ℕ) : ℝ) ^ (-D - 1) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hW0]; congr 1; push_cast; rw [hDE]; ring
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hNτ' : 2 * ((2 * κq + 1) * (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
    have e1 : (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 = ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; congr 1; rw [hτ₁]; push_cast; ring
    have e2 : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) = ((sz.size n : ℕ) : ℝ) ^ τ := by
      rw [← Real.rpow_add (by linarith)]; congr 1; ring
    rw [e1, ← e2, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hNτn (Real.rpow_nonneg (by linarith) _)
  have hΦn : ∀ (D'' v w : ℝ), s n ≤ v → v ≤ w → w ≤ (tt n : ℝ) → ∀ a : Fin 2 → Zd d (sz.L n),
      duhamelI_Phi (fun x y => ‖Theta d (sz.L n) (sz.lam n) (w : ℂ) x y‖) (2 * (1 - v))
          (fun x y => STprof sz n v D'' ((sz.L n : ℕ) : ℝ) x y) a ≤
        C * ((1 - v) / (1 - w)) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
          (tailT d (sz.L n) (sz.lam n) w ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) +
            (1 - v) / (1 - w) * ((sz.W n : ℕ) : ℝ) ^ (-D''))) := by
    intro D'' v w hv hvw hw a
    refine hΦC sz n D'' v w hlam hlamle ((hs n).trans hv) hvw (hw.trans_lt htt1) ?_ a
    exact Or.inr (by linarith [(hReg n).2])
  -- the bad event at the section, as a measurable set of matrices
  set ζ : ({σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n))) → ℝ := fun v => F n (tt n, v) +
    STAI sz n ^ (-(1 / 5) : ℝ) * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1) +
      ((sz.W n : ℕ) : ℝ) ^ (-D) with hζ
  set Sset : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
    ⋃ v, {H | ((sz.size n : ℕ) : ℝ) ^ τ * ζ v <
      ‖zeroModeSet d (sz.L n) {0} (fun a' => STLKM sz n (STflowE z n) (tt n : ℝ) H v.1.1 a') v.2‖} with hSset
  have hSm : MeasurableSet Sset := MeasurableSet.iUnion fun v =>
    measurableSet_lt measurable_const (duhamelII_QLK_meas sz n _ _ _ _)
  have heq := ST_pathP_eq_seqP sz s (fun m => (tt m : ℝ)) K n (K n) (hs n) (tt n).2.1 (hKne n) hSm
  rw [gridTime_last s (fun m => (tt m : ℝ)) K n (hKne n)] at heq
  have hbad : badSetAt sz.size (fun n v ω => ‖zeroModeSet d (sz.L n) {0}
        (fun a' => STLKM sz n (STflowE z n) (tt n : ℝ) (sz.seqHflow n (tt n : ℝ) ω) v.1.1 a') v.2‖)
      (fun n v _ => F n (tt n, v) + STAI sz n ^ (-(1 / 5) : ℝ) * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1) +
        ((sz.W n : ℕ) : ℝ) ^ (-D)) τ n = {ω | sz.seqHflow n (tt n : ℝ) ω ∈ Sset} := by
    ext ω; simp [badSetAt, hSset, hζ]
  rw [hbad, ← heq]
  set Gset : Set (PathΩ sz) := {ω | ∀ i : sz.STLab n,
      (∀ k, k ≤ K n → STgA sz s (fun m => (tt m : ℝ)) K n (STflowE z n) i.1 i.2 k ω =
        STgA sz s (fun m => (tt m : ℝ)) K n (STflowE z n) i.1 i.2 0 ω +
          ((gridStep s (fun m => (tt m : ℝ)) K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k,
            STgDrift sz s (fun m => (tt m : ℝ)) K n (STflowE z n) i.1 i.2 j ω + Rem n i k ω + Mart n i k ω) ∧
      (∀ k, k ≤ K n → ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s (fun m => (tt m : ℝ)) K n))}
    with hGset
  have hG : pathP sz Gsetᶜ = 0 := ae_iff.1 haen
  refine duhamelI_measure_le (pathP sz) (G := Gset) (by linarith) ?_ hΞn hmartn hG
  intro ω hω
  by_contra hcon
  simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hcon
  obtain ⟨⟨hA, hB⟩, hGω⟩ := hcon
  obtain ⟨h1, h2, h3, h4⟩ := hA
  obtain ⟨v, hv⟩ := Set.mem_iUnion.1 hω
  have hv' : ((sz.size n : ℕ) : ℝ) ^ τ * ζ v < ‖zeroModeSet d (sz.L n) {0}
      (fun a' => STLKM sz n (STflowE z n) (tt n : ℝ) (pathH sz s (fun m => (tt m : ℝ)) K n (K n) ω) v.1.1 a') v.2‖ := hv
  have hc : c₀ ≤ (mE (STflowE z n)).im := duhamelI_imag hκ (hEn n).le
  have hMa : ∀ i : sz.STLab n, ∀ k, k ≤ K n → ‖STgA sz s (fun m => (tt m : ℝ)) K n (STflowE z n) i.1 i.2 k ω‖ ≤
      (((sz.size n : ℕ) : ℝ) / c₀) ^ 2 + ((sz.size n : ℕ) : ℝ) := by
    intro i k hk
    have hmem := ST_gridTime_mem s (fun m => (tt m : ℝ)) K n k (tt n).2.1 (hKne n) hk
    exact duhamelI_apriori sz n (lt_of_lt_of_le (hEn n) (by linarith)) ((hs n).trans hmem.1) hmem.2 htt1 hTi hc₀ hc
      (pathH_isHermitian sz s (fun m => (tt m : ℝ)) K n k ω) i.1 i.2
  have hMart' : ∀ i : sz.STLab n, ∀ k, k ≤ K n → ‖Mart n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ *
      Real.sqrt (∑ j ∈ Finset.range k, gridStep s (fun m => (tt m : ℝ)) K n *
        ‖STEEM sz n (STflowE z n) (gridTime s (fun m => (tt m : ℝ)) K n j)
          (pathH sz s (fun m => (tt m : ℝ)) K n j ω) i.1 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-Dm)) := by
    intro i k hk
    by_contra hlt
    rw [not_le, Real.sqrt_eq_rpow] at hlt
    exact hB (Set.mem_iUnion.2 ⟨i, k, hk, hlt⟩)
  have hrem : ∀ b : Fin 2 → Zd d (sz.L n),
      ‖STgA sz s (fun m => (tt m : ℝ)) K n (STflowE z n) v.1.1 b (K n) ω -
          RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) v.1.1 (s n) (tt n : ℝ)
            (fun b' => STgA sz s (fun m => (tt m : ℝ)) K n (STflowE z n) v.1.1 b' 0 ω) b‖ ≤
        κs * ((((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 * (ρ ^ 3 * STAI sz n ^ (-(1 / 4) : ℝ))) *
            STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (b 0) (b 1) + ((sz.W n : ℕ) : ℝ) ^ (-D) := fun b =>
    duhamelII_path_rem sz n (STflowE z) s (fun m => (tt m : ℝ)) K ω (Mart n) (Rem n)
      (Λ := ((sz.size n : ℕ) : ℝ) ^ τ₁) (D := D) (DE := DE) (Dm := Dm)
      (M := (((sz.size n : ℕ) : ℝ) / c₀) ^ 2 + ((sz.size n : ℕ) : ℝ))
      (R := ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s (fun m => (tt m : ℝ)) K n)) (C := C) (c₀ := c₀)
      v.1.1 b (hs n) hsn htt1 (hKne n) hE2 hlam hΛ hA1 hc₀ hc hC.le hΦn hDEn
      (fun i k hk => (hGω i).1 k hk) (fun i k hk => (hGω i).2 k hk) hMa hMart'
      (fun j hj σ b => h2 j (Finset.mem_range.2 (Nat.lt_succ_of_le hj)) (σ, b))
      (fun j hj σ b => h3 j (Finset.mem_range.2 (Nat.lt_succ_of_le hj)) (σ, b))
      (fun j hj σ b k => h4 j (Finset.mem_range.2 (Nat.lt_succ_of_le hj)) ((σ, b), k)) hfloor
  have hSTgA : ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)),
      STgA sz s (fun m => (tt m : ℝ)) K n (STflowE z n) σ b (K n) ω =
        STLKM sz n (STflowE z n) (tt n : ℝ) (pathH sz s (fun m => (tt m : ℝ)) K n (K n) ω) σ b := by
    intro σ b; unfold STgA; rw [gridTime_last s (fun m => (tt m : ℝ)) K n (hKne n)]
  have hXeq : (fun a' => STLKM sz n (STflowE z n) (tt n : ℝ) (pathH sz s (fun m => (tt m : ℝ)) K n (K n) ω) v.1.1 a') =
      fun b => STgA sz s (fun m => (tt m : ℝ)) K n (STflowE z n) v.1.1 b (K n) ω := by
    funext b; exact (hSTgA v.1.1 b).symm
  rw [hXeq] at hv'
  -- `Q^{(1)}` of the initial term (the event E1) and of the remainder (`duhamelII_path_rem` at every label)
  have hI := h1 v
  have hQ := duhamelII_Q_sub_le (fun b => STgA sz s (fun m => (tt m : ℝ)) K n (STflowE z n) v.1.1 b (K n) ω)
    (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) v.1.1 (s n) (tt n : ℝ)
      (fun b' => STgA sz s (fun m => (tt m : ℝ)) K n (STflowE z n) v.1.1 b' 0 ω)) v.2
  have hins := norm_le_insert'
    (zeroModeSet d (sz.L n) {0} (fun b => STgA sz s (fun m => (tt m : ℝ)) K n (STflowE z n) v.1.1 b (K n) ω) v.2)
    (zeroModeSet d (sz.L n) {0} (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) v.1.1 (s n) (tt n : ℝ)
      (fun b' => STgA sz s (fun m => (tt m : ℝ)) K n (STflowE z n) v.1.1 b' 0 ω)) v.2)
  have hR0 := hrem v.2
  have hRc : ∀ c : Zd d (sz.L n),
      ‖STgA sz s (fun m => (tt m : ℝ)) K n (STflowE z n) v.1.1 (Function.update v.2 0 c) (K n) ω -
          RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) v.1.1 (s n) (tt n : ℝ)
            (fun b' => STgA sz s (fun m => (tt m : ℝ)) K n (STflowE z n) v.1.1 b' 0 ω) (Function.update v.2 0 c)‖ ≤
        κs * ((((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 * (ρ ^ 3 * STAI sz n ^ (-(1 / 4) : ℝ))) *
            STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) c (v.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D) := fun c => by
    have := hrem (Function.update v.2 0 c)
    rwa [(duhamelII_update_apply v.2 c).1, (duhamelII_update_apply v.2 c).2] at this
  have hreg2 : 1 - (tt n : ℝ) ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by
    linarith [(hReg n).2, (tt n).2.1]
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
    positivity
  have hBk0 : 0 ≤ κs * ((((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 * (ρ ^ 3 * STAI sz n ^ (-(1 / 4) : ℝ))) := by positivity
  have hsum : (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * ∑ c : Zd d (sz.L n),
      ‖STgA sz s (fun m => (tt m : ℝ)) K n (STflowE z n) v.1.1 (Function.update v.2 0 c) (K n) ω -
          RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) v.1.1 (s n) (tt n : ℝ)
            (fun b' => STgA sz s (fun m => (tt m : ℝ)) K n (STflowE z n) v.1.1 b' 0 ω) (Function.update v.2 0 c)‖ ≤
      κs * ((((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 * (ρ ^ 3 * STAI sz n ^ (-(1 / 4) : ℝ))) *
          (CA * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1)) + ((sz.W n : ℕ) : ℝ) ^ (-D) := by
    have havg := hAvg sz n D (tt n : ℝ) hlam.le htt1 hreg2 (v.2 0) (v.2 1)
    calc _ ≤ (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * ∑ c : Zd d (sz.L n),
          (κs * ((((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 * (ρ ^ 3 * STAI sz n ^ (-(1 / 4) : ℝ))) *
            STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) c (v.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => hRc c) (inv_nonneg.2 hLd.le)
      _ = κs * ((((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 * (ρ ^ 3 * STAI sz n ^ (-(1 / 4) : ℝ))) *
            ((((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * ∑ c : Zd d (sz.L n), STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) c (v.2 1)) +
          ((sz.W n : ℕ) : ℝ) ^ (-D) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_Zd]
          push_cast
          field_simp
      _ ≤ _ := by gcongr
  -- the exponent closure
  have hP0 : 0 ≤ STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1) := (ST_STprof_pos sz n _ _ _ _ _).le
  have hWm0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  have hchain := duhamelII_chain hins hQ hI hR0 hsum
  have e : κs * ((((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 * (ρ ^ 3 * STAI sz n ^ (-(1 / 4) : ℝ))) *
        STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1) +
      κs * ((((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 * (ρ ^ 3 * STAI sz n ^ (-(1 / 4) : ℝ))) *
        (CA * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1)) =
      (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 * κq * (ρ ^ 3 * STAI sz n ^ (-(1 / 4) : ℝ)) *
        STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1) := by
    rw [hκq]; ring
  rw [e] at hchain
  have hfin := duhamelII_close hΛ hκq0 (hF0 n (tt n, v)) hP0 hWm0 hA1 hρ1 hρA hNτ' hchain
  exact absurd hfin (not_le.2 hv')

end Prob

/-! ## 6. The engine and the pin -/

section Main

variable {d : ℕ}

/-- `STReg5II` is `STReg5Mid` with the second bound strengthened (`ilambda²/L² ≤ ilambda²`). -/
private theorem duhamelII_reg5II_mid {sz : Sizes d} {s t : ℕ → ℝ} (h : STReg5II sz s t) : STReg5Mid sz s t :=
  fun n => ⟨(h n).1, duhamelII_mid sz n (h n).2⟩

/-- **The engine of `STDuhamelII`, mixed conjunct** (`(zYU2)`, `3_5:2263-2277`), zero-mode set `Q = {0}` (`Q^{(1)}`), any sign class `P`
(the argument does not use the signs): if `‖Q^{(1)} 𝒰_{s,u}(𝓛-𝒦)^{(2)}_{s,σ}‖_a ≺ F`, then
`‖Q^{(1)}(𝓛-𝒦)^{(2)}_{u,σ}‖_a ≺ F + A^{-1/5} W^{-d}𝒯̃^L_{u,D} + W^{-D}` uniformly in `u ∈ [s,t]`, `σ ∈ P`.  Hypotheses: the flow;
the window `STReg5II` (`ilambda²/L^d ≤ 1-t ≤ 1-s ≤ ilambda²/L²`: the second half is `(TTT2)` through `Or.inr` and the saturation
`ℓ_u = L` of the profile); `(con_st_ind)` at `𝔠_d = 1/100`; `hE`, the body of `STEtermsMidConcl` written out (as in
`stDuhamelConcl_engine`, so that the registry scan sees only `Prec`).  The proof applies `Q^{(1)}` to the pathwise remainder of the
grid Duhamel form (`duhamelII_path_rem`) instead of the paper's `Θ̊`-weighted kernel estimates (paper-delta candidate `T2339a`). -/
theorem stDuhamelConcl_engineQ1 (hd : 3 ≤ d) {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (sz : Sizes d)
    {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (htz : ∀ n, t n ≤ lemT (z n)) (hReg : STReg5II sz s t)
    (hCon : STConStInd sz (1 / 100) s t)
    (hE : ∀ D : ℝ, 0 < D →
      sz.Prec (U := STIdx2 sz s t) (fun n p ω => ‖STELKLK sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => (STAI sz n) ^ (-(1 / 3) : ℝ) * (etaT (STflowE z n) (p.1 : ℝ))⁻¹ *
          STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) ∧
      sz.Prec (U := STIdx2 sz s t) (fun n p ω => ‖STEGt sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => (STAI sz n) ^ (-(1 / 2) : ℝ) * (etaT (STflowE z n) (p.1 : ℝ))⁻¹ *
          STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) ∧
      sz.Prec (U := fun n => STIdx2 sz s t n × Fin 2)
        (fun n p ω => ‖STEEk sz n (STflowE z n) (p.1.1 : ℝ) p.2 p.1.2.1 p.1.2.2 ω‖)
        (fun n p _ => (STAI sz n) ^ (-(1 / 2) : ℝ) * (etaT (STflowE z n) (p.1.1 : ℝ))⁻¹ *
          STprof sz n (p.1.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.1.2.2 0) (p.1.2.2 1) ^ 2))
    (P : (Fin 2 → Bool) → Prop) :
    STDuhamelConcl sz {0} P (STflowE z) s t := by
  classical
  intro D hD F hF0 hini
  obtain ⟨hAdm, hEn, ht1, -⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow htz
  have hsize : sz.SizeTendsto := hAdm.2.2.1
  have hsN := tendsto_size sz hsize
  by_cases hP : ∃ σ, P σ
  swap
  · exact st5_prec_of_isEmpty sz (fun n => ⟨fun p => hP ⟨p.2.1.1, p.2.1.2⟩⟩)
  have hne : ∀ n, Nonempty ({σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n))) :=
    fun n => ⟨(⟨hP.choose, hP.choose_spec⟩, fun _ => 0)⟩
  have hlen : ∀ n, t n - s n ≤ 1 := fun n => by linarith [ht1 n, hs n]
  have hev := st5_eventually_A_ge_one sz h𝔡 hAdm.2.2.2.2
  have htN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
    filter_upwards [hev] with n hn
    exact duhamelI_htN sz n hn.1 hn.2 (hReg n).1
  obtain ⟨CH, hCH0, hCH⟩ := duhamelII_holder sz (STflowE z) s t (κ / 2) hsize (by linarith)
    (fun n => (hEn n).le) hs ht1 htN
  refine duhamelI_lift sz hsize (fun n => (hst n).le) hlen
    (V := fun n => {σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n))) (Cv := 3) (CR := D) (by norm_num) hD.le ?_
    (fun n p ω => ‖zeroModeSet d (sz.L n) {0}
      (fun a' => STLKM sz n (STflowE z n) (p.1 : ℝ) (sz.seqHflow n (p.1 : ℝ) ω) p.2.1.1 a') p.2.2‖)
    (fun n p => F n p + STAI sz n ^ (-(1 / 5) : ℝ) *
      STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D)) ?_ ?_ ?_ ⟨CH, hCH0, ?_⟩
  · filter_upwards [hsN.eventually (eventually_ge_atTop 4)] with n hn
    exact duhamelI_card_le sz P n hn
  · intro n p
    exact add_nonneg (add_nonneg (hF0 n p) (mul_nonneg (Real.rpow_nonneg (by unfold STAI; positivity) _)
      (ST_STprof_pos sz n _ _ _ _ _).le)) (Real.rpow_nonneg (by positivity) _)
  · exact ST_PT_of_sections sz (fun n => (hst n).le) _ _ fun tt =>
      duhamelII_section hd hκ hε h𝔡 sz hflow hs hst htz hReg hCon hE hD P F hF0 hini tt
  · filter_upwards with n p
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hWm : ((sz.size n : ℕ) : ℝ) ^ (-D) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) :=
      Real.rpow_le_rpow_of_nonpos hW0 (duhamelI_W_le_size sz (by omega) n) (neg_nonpos.2 hD.le)
    have := mul_nonneg (Real.rpow_nonneg (by unfold STAI; positivity) (-(1 / 5) : ℝ) : (0 : ℝ) ≤ STAI sz n ^ (-(1 / 5) : ℝ))
      (ST_STprof_pos sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)).le
    linarith [hF0 n p]
  · filter_upwards [hCH] with n hn ω hω u u' v
    exact hn ω hω u u' v.1.1 v.2

/-- **`STDuhamelII`** (case (ii), the integrated hierarchy: `Q^{(1)}` for `σ₁ ≠ σ₂`, no zero-mode removal for `σ₁ = σ₂`): the mixed
conjunct is `stDuhamelConcl_engineQ1`, the equal-sign conjunct is `stDuhamelConcl_engine` (`Q = ∅`) with `(TTT2)` through
`Or.inr`; `𝔠_d = 1/100`. -/
theorem stDuhamelII_holds (d : ℕ) : STDuhamelII d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs hst htz hReg _ _ _ _ _ hCon _ _ _ _ hE
  exact ⟨stDuhamelConcl_engineQ1 hd hκ hε h𝔡 sz hflow hs hst htz hReg hCon hE STSigMixed,
    stDuhamelConcl_engine hd hκ hε h𝔡 sz hflow hs hst htz (duhamelII_reg5II_mid hReg)
      (fun n => Or.inr (hReg n).2) hCon hE STSigSame⟩

end Main

end RBM.Gauss.Sizes

/-! ## Compiled nonempty instances at `d = 3` -/

namespace RBM.Gauss.Step5Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst RBM.Path Filter

/-- `stDuhamelII_holds` at `(szB, zB, 15/16, 31/32)` (the data of `inst_duhamelII`). -/
theorem inst_duhamelII_proved (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STEtermsMidConcl sz E s t →
      STDuhamelConcl sz {0} STSigMixed E s t ∧ STDuhamelConcl sz ∅ STSigSame E s t) szB zB
      (fun _ => 15 / 16) (fun _ => 31 / 32) Cd :=
  inst_duhamelII (stDuhamelII_holds 3) Cd hCd

/-- `stDuhamelConcl_engineQ1` at the same data, mixed signs (`σ = (+,-)` is in the class); `STEtermsMidConcl` is the proved pin of
another gate (a hypothesis of the example), every deterministic hypothesis is discharged. -/
example (hE : STEtermsMidConcl szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32)) :
    STDuhamelConcl szB {0} STSigMixed (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  stDuhamelConcl_engineQ1 (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10)
    (by norm_num : (0 : ℝ) < 1 / 10) szB flow_zB (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) szB_reg5II
    (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num)) hE STSigMixed

/-- The same at strictly interior data `(szB, zB, 19/20, 31/32)`: `ilambda²/L^d = 1/64 ≤ 1-t = 1/32 ≤ 1-s = 1/20 < 1/16 = ilambda²/L²`
(`inst_duhamelII_proved` has `1-s = ilambda²/L²`, the closed end of the regime). -/
example (hE : STEtermsMidConcl szB (STflowE zB) (fun _ => 19 / 20) (fun _ => 31 / 32)) :
    STDuhamelConcl szB {0} STSigMixed (STflowE zB) (fun _ => 19 / 20) (fun _ => 31 / 32) :=
  stDuhamelConcl_engineQ1 (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10)
    (by norm_num : (0 : ℝ) < 1 / 10) szB flow_zB (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) (fun n => ⟨by simp [szB]; norm_num, by simp [szB]; norm_num⟩)
    (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num)) hE STSigMixed

/-- `stDuhamelII_holds` at the same strictly interior data. -/
example (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STEtermsMidConcl sz E s t →
      STDuhamelConcl sz {0} STSigMixed E s t ∧ STDuhamelConcl sz ∅ STSigSame E s t) szB zB
      (fun _ => 19 / 20) (fun _ => 31 / 32) Cd :=
  inst_ing5 STReg5II _ (stDuhamelII_holds 3) szB zB flow_zB (fun _ => 19 / 20) (fun _ => 31 / 32)
    (fun _ => by norm_num) (fun _ => by norm_num) (szB_flow_ht (by norm_num))
    (fun n => ⟨by simp [szB]; norm_num, by simp [szB]; norm_num⟩)
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) Cd hCd

end RBM.Gauss.Step5Inst
