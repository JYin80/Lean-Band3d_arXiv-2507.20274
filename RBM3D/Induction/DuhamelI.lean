/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.EtermsMid
import RBM3D.Induction.Step5Kernel
import RBM3D.Induction.PfStep5Grid
import RBM3D.Path.DifREP3

/-!
# S5-15 (ticket T2333): the integrated hierarchy at `n = 2`, case (i) of Step 5

`stDuhamelI_holds : ∀ d, STDuhamelI d` (`3_5:1941-2069`: `(int_K-LcalE_n=2)`,
`(jymwons)`..`(iois-mtx2)`) and the engine `stDuhamelConcl_engine` (zero-mode set `∅`, every
sign class `P`; the general `Q` is not done, see the report).

Route.  Sections 1-4: the weights `α = v/w`, `β = (w-v)/w` of `(eq:decompU)` and the operator `Φ`
that sums the three terms of `𝒰 = α + β Θ` slot by slot; `Φ` is estimated by the kernel bound
`(uwp2-92kj)` (`step5Kernel_profile_explicit_holds`).  Section 5: the pathwise bound at one size
index from the grid Duhamel form `pfStep5Grid_duhamel` (drift term; martingale term of
`STGridMartAt` by Abel summation).  Section 6: the numerical facts (`ρ ≤ (2A)^{1/100}`, floors).
Section 7: the per-section statement `duhamelI_section` (grid events, `ST_pathP_eq_seqP`).
Section 8: the net lift to `u ∈ [s,t]` for an arbitrary deterministic initial control
(`duhamelI_lift`).  Sections 9-10: the engine, the pin, the instances.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ## 1. Scalar facts: the weights of `(eq:decompU)` and summation by parts -/

/-- `(w - v)/w ≤ 2 (1 - v)` for `0 ≤ v ≤ w < 1`: `2(1-v)w - (w-v) = w(1-v) + v(1-w) ≥ 0`. -/
private theorem duhamelI_beta_le {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) (hw0 : 0 < w) (hw1 : w < 1) :
    (w - v) / w ≤ 2 * (1 - v) := by
  rw [div_le_iff₀ hw0]
  nlinarith [mul_nonneg hw0.le (sub_nonneg.2 (hvw.trans hw1.le)), mul_nonneg hv (sub_nonneg.2 hw1.le)]

/-- **Summation by parts** (`Finset.sum_range_by_parts`): `|Σ_{j<K} c_j (M_{j+1} - M_j)| ≤ 2B (γ + τ)` if
`|c_{K-1}| ≤ γ`, the total variation of `c` is `≤ τ` and `|M_j| ≤ B` for `j ≤ K`. -/
private theorem duhamelI_abel (c : ℕ → ℝ) (M : ℕ → ℂ) (K : ℕ) {γ τ B : ℝ}
    (hc : |c (K - 1)| ≤ γ) (htv : ∑ i ∈ Finset.range (K - 1), |c (i + 1) - c i| ≤ τ)
    (hB : ∀ j ≤ K, ‖M j‖ ≤ B) :
    ‖∑ j ∈ Finset.range K, c j • (M (j + 1) - M j)‖ ≤ 2 * B * (γ + τ) := by
  rw [Finset.sum_range_by_parts c (fun j => M (j + 1) - M j) K]
  simp only [Finset.sum_range_sub]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _))
  have hγ0 : 0 ≤ γ := (abs_nonneg _).trans hc
  have hMM : ∀ j ≤ K, ‖M j - M 0‖ ≤ 2 * B := fun j hj =>
    (norm_sub_le _ _).trans (by linarith [hB j hj, hB 0 (Nat.zero_le _)])
  have h1 : ‖c (K - 1) • (M K - M 0)‖ ≤ γ * (2 * B) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hc (hMM K le_rfl) (norm_nonneg _) hγ0
  have h2 : ‖∑ i ∈ Finset.range (K - 1), (c (i + 1) - c i) • (M (i + 1) - M 0)‖ ≤ τ * (2 * B) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ Finset.range (K - 1), ‖(c (i + 1) - c i) • (M (i + 1) - M 0)‖
        ≤ ∑ i ∈ Finset.range (K - 1), |c (i + 1) - c i| * (2 * B) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hMM (i + 1) (by have := Finset.mem_range.1 hi; omega)) (abs_nonneg _)
      _ = (∑ i ∈ Finset.range (K - 1), |c (i + 1) - c i|) * (2 * B) := by rw [Finset.sum_mul]
      _ ≤ τ * (2 * B) := mul_le_mul_of_nonneg_right htv (by linarith)
  calc _ ≤ ‖c (K - 1) • (M K - M 0)‖ + ‖∑ i ∈ Finset.range (K - 1), (c (i + 1) - c i) • (M (i + 1) - M 0)‖ :=
        norm_sub_le _ _
    _ ≤ γ * (2 * B) + τ * (2 * B) := add_le_add h1 h2
    _ = 2 * B * (γ + τ) := by ring

private theorem duhamelI_tv_up (f : ℕ → ℝ) (m : ℕ) (h : ∀ i < m, f i ≤ f (i + 1)) :
    ∑ i ∈ Finset.range m, |f (i + 1) - f i| = f m - f 0 := by
  rw [← Finset.sum_range_sub]
  exact Finset.sum_congr rfl fun i hi => abs_of_nonneg (sub_nonneg.2 (h i (Finset.mem_range.1 hi)))

private theorem duhamelI_tv_down (f : ℕ → ℝ) (m : ℕ) (h : ∀ i < m, f (i + 1) ≤ f i) :
    ∑ i ∈ Finset.range m, |f (i + 1) - f i| = f 0 - f m := by
  rw [← Finset.sum_range_sub']
  exact Finset.sum_congr rfl fun i hi => by
    rw [abs_sub_comm]; exact abs_of_nonneg (sub_nonneg.2 (h i (Finset.mem_range.1 hi)))

/-- **The three weights of the martingale term** `α²`, `αβ`, `β²` (`α = v/w` increasing from `a 0` to `a (K-1)`,
`β = 1 - α`): the Abel sums are bounded by `4B`, `4B β₀`, `4B β₀²`, `β₀ = 1 - a 0`. -/
private theorem duhamelI_weights (a : ℕ → ℝ) (K : ℕ) (hK : 1 ≤ K) (ha0 : ∀ j ≤ K, 0 ≤ a j)
    (ha1 : ∀ j ≤ K, a j ≤ 1) (hmono : ∀ j < K, a j ≤ a (j + 1)) (M : ℕ → ℂ) {B : ℝ}
    (hB : ∀ j ≤ K, ‖M j‖ ≤ B) :
    ‖∑ j ∈ Finset.range K, (a j) ^ 2 • (M (j + 1) - M j)‖ ≤ 4 * B ∧
    ‖∑ j ∈ Finset.range K, (a j * (1 - a j)) • (M (j + 1) - M j)‖ ≤ 4 * B * (1 - a 0) ∧
    ‖∑ j ∈ Finset.range K, (1 - a j) ^ 2 • (M (j + 1) - M j)‖ ≤ 4 * B * (1 - a 0) ^ 2 := by
  have hK1 : K - 1 + 1 = K := Nat.sub_add_cancel hK
  have hKm : ∀ i < K - 1, i + 1 ≤ K := fun i hi => by omega
  have hmono' : ∀ i < K - 1, a i ≤ a (i + 1) := fun i hi => hmono i (by omega)
  have hmax : a (K - 1) ≤ 1 := ha1 _ (by omega)
  have hamin : a 0 ≤ a (K - 1) := by
    have : ∀ m ≤ K - 1, a 0 ≤ a m := by
      intro m
      induction m with
      | zero => exact fun _ => le_rfl
      | succ m ih => exact fun hm => (ih (by omega)).trans (hmono' m (by omega))
    exact this _ le_rfl
  have h0 := ha0 0 (Nat.zero_le _)
  have hKK := ha0 (K - 1) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · have := duhamelI_abel (fun j => (a j) ^ 2) M K (γ := 1) (τ := 1)
      (by rw [abs_of_nonneg (sq_nonneg _)]; nlinarith)
      (by
        rw [duhamelI_tv_up (fun j => (a j) ^ 2) (K - 1) (fun i hi => by
          have := ha0 i (by omega); have := hmono' i hi; nlinarith)]
        nlinarith [sq_nonneg (a 0)]) hB
    simpa [smul_eq_mul] using this.trans (by linarith)
  · have := duhamelI_abel (fun j => a j * (1 - a j)) M K (γ := 1 - a 0) (τ := 1 - a 0)
      (by
        rw [abs_of_nonneg (mul_nonneg hKK (sub_nonneg.2 hmax))]
        nlinarith)
      (by
        calc ∑ i ∈ Finset.range (K - 1), |a (i + 1) * (1 - a (i + 1)) - a i * (1 - a i)|
            ≤ ∑ i ∈ Finset.range (K - 1), (a (i + 1) - a i) := by
              refine Finset.sum_le_sum fun i hi => ?_
              have hi' := Finset.mem_range.1 hi
              have h1 := ha0 i (by omega)
              have h2 := hmono' i hi'
              have h3 := ha1 (i + 1) (by omega)
              have e : a (i + 1) * (1 - a (i + 1)) - a i * (1 - a i) = (a (i + 1) - a i) * (1 - a i - a (i + 1)) := by ring
              rw [e, abs_mul, abs_of_nonneg (sub_nonneg.2 h2)]
              have : |1 - a i - a (i + 1)| ≤ 1 := by
                rw [abs_le]; constructor <;> nlinarith
              nlinarith [sub_nonneg.2 h2]
          _ = a (K - 1) - a 0 := Finset.sum_range_sub a (K - 1)
          _ ≤ 1 - a 0 := by linarith) hB
    simpa [smul_eq_mul] using this.trans (by linarith)
  · have := duhamelI_abel (fun j => (1 - a j) ^ 2) M K (γ := (1 - a 0) ^ 2) (τ := (1 - a 0) ^ 2)
      (by
        rw [abs_of_nonneg (sq_nonneg _)]
        nlinarith)
      (by
        rw [duhamelI_tv_down (fun j => (1 - a j) ^ 2) (K - 1) (fun i hi => by
          have := ha1 (i + 1) (by omega); have := hmono' i hi; have := ha0 i (by omega); nlinarith)]
        nlinarith [sq_nonneg (1 - a (K - 1))]) hB
    simpa [smul_eq_mul] using this.trans (by nlinarith [sq_nonneg (1 - a 0)])



private theorem duhamelI_sum2 {X : Type*} [Fintype X] {R : Type*} [AddCommMonoid R] (f : X → X → R) :
    ∑ b : Fin 2 → X, f (b 0) (b 1) = ∑ x, ∑ y, f x y := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (finTwoArrowEquiv X) _ _ (fun b => rfl)

/-! ## 2. The operator `Φ` of `(eq:decompU)` -/

/-- The Φ operator. -/
def duhamelI_Phi {X : Type*} [Fintype X] (T : X → X → ℝ) (h : ℝ) (q : X → X → ℝ) (a : Fin 2 → X) : ℝ :=
  q (a 0) (a 1) + h * (∑ y, T (a 1) y * q (a 0) y + ∑ x, T (a 0) x * q x (a 1)) +
    h ^ 2 * ∑ x, ∑ y, T (a 0) x * T (a 1) y * q x y

theorem duhamelI_Phi_mono {X : Type*} [Fintype X] {T : X → X → ℝ} {h : ℝ} {q q' : X → X → ℝ}
    (hT : ∀ x y, 0 ≤ T x y) (hh : 0 ≤ h) (hq : ∀ x y, q x y ≤ q' x y) (a : Fin 2 → X) :
    duhamelI_Phi T h q a ≤ duhamelI_Phi T h q' a := by
  unfold duhamelI_Phi
  have h1 : ∑ y, T (a 1) y * q (a 0) y ≤ ∑ y, T (a 1) y * q' (a 0) y :=
    Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hq _ _) (hT _ _)
  have h2 : ∑ x, T (a 0) x * q x (a 1) ≤ ∑ x, T (a 0) x * q' x (a 1) :=
    Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hq _ _) (hT _ _)
  have h3 : ∑ x, ∑ y, T (a 0) x * T (a 1) y * q x y ≤ ∑ x, ∑ y, T (a 0) x * T (a 1) y * q' x y :=
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
      mul_le_mul_of_nonneg_left (hq _ _) (mul_nonneg (hT _ _) (hT _ _))
  nlinarith [hq (a 0) (a 1), mul_le_mul_of_nonneg_left (add_le_add h1 h2) hh,
    mul_le_mul_of_nonneg_left h3 (sq_nonneg h)]

theorem duhamelI_Phi_lin {X : Type*} [Fintype X] (T : X → X → ℝ) (h c₁ c₂ : ℝ) (q₁ q₂ : X → X → ℝ)
    (a : Fin 2 → X) :
    duhamelI_Phi T h (fun x y => c₁ * q₁ x y + c₂ * q₂ x y) a =
      c₁ * duhamelI_Phi T h q₁ a + c₂ * duhamelI_Phi T h q₂ a := by
  unfold duhamelI_Phi
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, mul_left_comm _ c₁, mul_left_comm _ c₂]
  ring

theorem duhamelI_Phi_smul {X : Type*} [Fintype X] (T : X → X → ℝ) (h c : ℝ) (q : X → X → ℝ) (a : Fin 2 → X) :
    duhamelI_Phi T h (fun x y => c * q x y) a = c * duhamelI_Phi T h q a := by
  have := duhamelI_Phi_lin T h c 0 q q a
  simpa using this

theorem duhamelI_Phi_one {X : Type*} [Fintype X] {T : X → X → ℝ} {h R : ℝ} (hT : ∀ x y, 0 ≤ T x y)
    (hh : 0 ≤ h) (hR : ∀ x, ∑ y, T x y ≤ R) (a : Fin 2 → X) :
    duhamelI_Phi T h (fun _ _ => 1) a ≤ 1 + 2 * h * R + h ^ 2 * R ^ 2 := by
  unfold duhamelI_Phi
  have hR0 : 0 ≤ R := (Finset.sum_nonneg fun y _ => hT (a 0) y).trans (hR (a 0))
  have h2 : ∑ x, ∑ y, T (a 0) x * T (a 1) y = (∑ x, T (a 0) x) * ∑ y, T (a 1) y := by
    rw [Finset.sum_mul_sum]
  simp only [mul_one]
  rw [h2]
  have e1 := hR (a 1)
  have e2 := hR (a 0)
  have e3 : (∑ x, T (a 0) x) * ∑ y, T (a 1) y ≤ R * R :=
    mul_le_mul e2 e1 (Finset.sum_nonneg fun y _ => hT _ _) hR0
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add e1 e2) hh, mul_le_mul_of_nonneg_left e3 (sq_nonneg h)]

theorem duhamelI_Phi_scale {X : Type*} [Fintype X] {T : X → X → ℝ} {h ρ : ℝ} {q : X → X → ℝ}
    (hT : ∀ x y, 0 ≤ T x y) (hq : ∀ x y, 0 ≤ q x y) (hh : 0 ≤ h) (hρ : 1 ≤ ρ) (a : Fin 2 → X) :
    duhamelI_Phi T (ρ * h) q a ≤ ρ ^ 2 * duhamelI_Phi T h q a := by
  unfold duhamelI_Phi
  have s1 : 0 ≤ ∑ y, T (a 1) y * q (a 0) y := Finset.sum_nonneg fun y _ => mul_nonneg (hT _ _) (hq _ _)
  have s2 : 0 ≤ ∑ x, T (a 0) x * q x (a 1) := Finset.sum_nonneg fun x _ => mul_nonneg (hT _ _) (hq _ _)
  have s3 : 0 ≤ ∑ x, ∑ y, T (a 0) x * T (a 1) y * q x y :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => mul_nonneg (mul_nonneg (hT _ _) (hT _ _)) (hq _ _)
  have q0 := hq (a 0) (a 1)
  have hρ0 : 0 ≤ ρ := by linarith
  have hρ2 : ρ ≤ ρ ^ 2 := by nlinarith
  have hρ3 : 1 ≤ ρ ^ 2 := by nlinarith
  have hs := add_nonneg s1 s2
  nlinarith [mul_nonneg hh hs, mul_nonneg (mul_nonneg hh hs) (sub_nonneg.2 hρ2), mul_nonneg (sq_nonneg h) s3,
    mul_nonneg (mul_nonneg (sq_nonneg h) s3) (sub_nonneg.2 hρ3), mul_nonneg q0 (sub_nonneg.2 hρ3), mul_nonneg hρ0 hs,
    mul_nonneg (mul_nonneg hh hs) (sub_nonneg.2 hρ)]

/-- The kernel estimate (uwp2-92kj) turned into a bound on `Φ` of a profile. -/
theorem duhamelI_Phi_prof {X : Type*} [Fintype X] (T q tT : X → X → ℝ) {v w C₃ Wd ρ Wm : ℝ}
    (hv : v < 1) (hw : w < 1) (hvw : v ≤ w) (hρ : ρ = (1 - v) / (1 - w)) (hC₃ : 0 ≤ C₃)
    (hWd : 0 ≤ Wd) (hWm : 0 ≤ Wm) (hT : ∀ x y, 0 ≤ T x y) (hrow : ∀ x, ∑ y, T x y ≤ (1 - w)⁻¹)
    (htT0 : ∀ x y, 0 ≤ tT x y) (htTs : ∀ x y, tT x y = tT y x) (hqs : ∀ x y, q x y = q y x)
    (hq0 : ∀ x y, q x y ≤ Wd * (tT x y + Wm))
    (hU : ∀ x y, (1 - v) * ∑ b, T x b * q b y ≤ Wd * (C₃ * tT x y + ρ * Wm))
    (hV : ∀ x y, (1 - w) * ∑ b, T x b * tT b y ≤ C₃ * tT x y + Wm) (a : Fin 2 → X) :
    duhamelI_Phi T (2 * (1 - v)) q a ≤
      ((1 + 2 * C₃) ^ 2 + 9 + 4 * C₃) * ρ * (Wd * (tT (a 0) (a 1) + ρ * Wm)) := by
  have h1w : 0 < 1 - w := by linarith
  have h1v : 0 < 1 - v := by linarith
  have hρ1 : 1 ≤ ρ := by rw [hρ, le_div_iff₀ h1w]; linarith
  have hρe : 1 - v = ρ * (1 - w) := by rw [hρ]; field_simp
  set P := tT (a 0) (a 1) with hP
  have hP1 : tT (a 1) (a 0) = P := htTs _ _
  have hP0 : 0 ≤ P := htT0 _ _
  -- the single-slot terms
  have S1a : (1 - v) * ∑ x, T (a 0) x * q x (a 1) ≤ Wd * (C₃ * P + ρ * Wm) := hU (a 0) (a 1)
  have S1b : (1 - v) * ∑ y, T (a 1) y * q (a 0) y ≤ Wd * (C₃ * P + ρ * Wm) := by
    have h := hU (a 1) (a 0)
    rw [hP1] at h
    simpa only [hqs (a 0)] using h
  -- the double-slot term
  have hrowv : (1 - v) * ∑ y, T (a 1) y ≤ ρ := by
    calc (1 - v) * ∑ y, T (a 1) y ≤ (1 - v) * (1 - w)⁻¹ := mul_le_mul_of_nonneg_left (hrow _) h1v.le
      _ = ρ := by rw [hρ]; field_simp
  have hV' : (1 - v) * ∑ y, T (a 1) y * tT y (a 0) ≤ ρ * (C₃ * P + Wm) := by
    have h := hV (a 1) (a 0)
    rw [hP1] at h
    rw [hρe]
    calc ρ * (1 - w) * ∑ y, T (a 1) y * tT y (a 0) = ρ * ((1 - w) * ∑ y, T (a 1) y * tT y (a 0)) := by ring
      _ ≤ ρ * (C₃ * P + Wm) := mul_le_mul_of_nonneg_left h (by linarith)
  have S2 : (1 - v) ^ 2 * ∑ x, ∑ y, T (a 0) x * T (a 1) y * q x y ≤
      Wd * C₃ * ρ * (C₃ * P + Wm) + Wd * ρ ^ 2 * Wm := by
    have e : ∑ x, ∑ y, T (a 0) x * T (a 1) y * q x y = ∑ y, T (a 1) y * ∑ x, T (a 0) x * q x y := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [e]
    calc (1 - v) ^ 2 * ∑ y, T (a 1) y * ∑ x, T (a 0) x * q x y
        = (1 - v) * ∑ y, T (a 1) y * ((1 - v) * ∑ x, T (a 0) x * q x y) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
      _ ≤ (1 - v) * ∑ y, T (a 1) y * (Wd * (C₃ * tT (a 0) y + ρ * Wm)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (hU (a 0) y) (hT _ _)) h1v.le
      _ = Wd * C₃ * ((1 - v) * ∑ y, T (a 1) y * tT y (a 0)) + Wd * ρ * Wm * ((1 - v) * ∑ y, T (a 1) y) := by
          simp only [Finset.mul_sum]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [htTs (a 0) y]
          ring
      _ ≤ Wd * C₃ * (ρ * (C₃ * P + Wm)) + Wd * ρ * Wm * ρ :=
          add_le_add (mul_le_mul_of_nonneg_left hV' (mul_nonneg hWd hC₃))
            (mul_le_mul_of_nonneg_left hrowv (mul_nonneg (mul_nonneg hWd (by linarith)) hWm))
      _ = _ := by ring
  have Q0 := hq0 (a 0) (a 1)
  unfold duhamelI_Phi
  have hsq : (2 * (1 - v)) ^ 2 = 4 * (1 - v) ^ 2 := by ring
  rw [hsq]
  set u := Wd * P with hu
  set m := Wd * Wm with hm
  have hu0 : 0 ≤ u := mul_nonneg hWd hP0
  have hm0 : 0 ≤ m := mul_nonneg hWd hWm
  have hρ2 : ρ ≤ ρ ^ 2 := by nlinarith
  have hQ : q (a 0) (a 1) ≤ u + m := by rw [hu, hm]; nlinarith
  have hS1 : 2 * (1 - v) * (∑ y, T (a 1) y * q (a 0) y + ∑ x, T (a 0) x * q x (a 1)) ≤
      4 * (C₃ * u + ρ * m) := by
    have := add_le_add S1a S1b
    have e : 2 * (1 - v) * (∑ y, T (a 1) y * q (a 0) y + ∑ x, T (a 0) x * q x (a 1)) =
        2 * ((1 - v) * ∑ x, T (a 0) x * q x (a 1) + (1 - v) * ∑ y, T (a 1) y * q (a 0) y) := by ring
    rw [e]
    nlinarith
  have hS2 : 4 * (1 - v) ^ 2 * ∑ x, ∑ y, T (a 0) x * T (a 1) y * q x y ≤
      4 * (C₃ * ρ * (C₃ * u + m) + ρ ^ 2 * m) := by
    nlinarith [S2]
  have e1 : (1 + 2 * C₃) ^ 2 + 9 + 4 * C₃ = 10 + 8 * C₃ + 4 * C₃ ^ 2 := by ring
  have goal : ((1 + 2 * C₃) ^ 2 + 9 + 4 * C₃) * ρ * (Wd * (P + ρ * Wm)) =
      (10 + 8 * C₃ + 4 * C₃ ^ 2) * ρ * (u + ρ * m) := by rw [e1, hu, hm]; ring
  rw [goal]
  nlinarith [mul_nonneg hu0 (sub_nonneg.2 hρ1), mul_nonneg hm0 (sub_nonneg.2 hρ1), mul_nonneg hm0 (sub_nonneg.2 hρ2),
    mul_nonneg hC₃ hu0, mul_nonneg hC₃ hm0, mul_nonneg (mul_nonneg hC₃ hC₃) hu0, mul_nonneg (mul_nonneg hC₃ hu0) (sub_nonneg.2 hρ1),
    mul_nonneg (mul_nonneg hC₃ hm0) (sub_nonneg.2 hρ1), mul_nonneg (mul_nonneg (mul_nonneg hC₃ hC₃) hu0) (sub_nonneg.2 hρ1),
    mul_nonneg (mul_nonneg hC₃ hm0) (sub_nonneg.2 hρ2), mul_nonneg (mul_nonneg hC₃ hm0) (sq_nonneg ρ)]

private theorem duhamelI_expand {X : Type*} [Fintype X] [DecidableEq X] (α β : ℂ) (K : Fin 2 → Matrix X X ℂ)
    (Y : (Fin 2 → X) → ℂ) (a : Fin 2 → X) :
    ∑ b : Fin 2 → X, (∏ i, (α • (1 : Matrix X X ℂ) + β • K i) (a i) (b i)) * Y b =
      α ^ 2 * Y a + α * β * (∑ y, K 1 (a 1) y * Y ![a 0, y] + ∑ x, K 0 (a 0) x * Y ![x, a 1]) +
        β ^ 2 * ∑ x, ∑ y, K 0 (a 0) x * K 1 (a 1) y * Y ![x, y] := by
  have eta : ∀ b : Fin 2 → X, ![b 0, b 1] = b := fun b => by ext i; fin_cases i <;> rfl
  have ha : a = ![a 0, a 1] := (eta a).symm
  calc ∑ b : Fin 2 → X, (∏ i, (α • (1 : Matrix X X ℂ) + β • K i) (a i) (b i)) * Y b
      = ∑ b : Fin 2 → X, ((α * (if a 0 = b 0 then 1 else 0) + β * K 0 (a 0) (b 0)) *
          (α * (if a 1 = b 1 then 1 else 0) + β * K 1 (a 1) (b 1))) * Y ![b 0, b 1] := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Fin.prod_univ_two, eta]
        simp [Matrix.one_apply]
    _ = ∑ x, ∑ y, ((α * (if a 0 = x then 1 else 0) + β * K 0 (a 0) x) *
          (α * (if a 1 = y then 1 else 0) + β * K 1 (a 1) y)) * Y ![x, y] :=
        duhamelI_sum2 (fun x y => ((α * (if a 0 = x then 1 else 0) + β * K 0 (a 0) x) *
          (α * (if a 1 = y then 1 else 0) + β * K 1 (a 1) y)) * Y ![x, y])
    _ = _ := by
        have e : ∀ x y, ((α * (if a 0 = x then 1 else 0) + β * K 0 (a 0) x) *
          (α * (if a 1 = y then 1 else 0) + β * K 1 (a 1) y)) * Y ![x, y] =
            α ^ 2 * ((if a 0 = x then 1 else 0) * ((if a 1 = y then 1 else 0) * Y ![x, y])) +
            α * β * ((if a 0 = x then 1 else 0) * (K 1 (a 1) y * Y ![x, y])) +
            α * β * (K 0 (a 0) x * ((if a 1 = y then 1 else 0) * Y ![x, y])) +
            β ^ 2 * (K 0 (a 0) x * (K 1 (a 1) y * Y ![x, y])) := fun x y => by ring
        simp_rw [e]
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Fin.isValue, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, ← ha]
        have e2 : ∑ i, K 0 (a 0) i * ∑ i_1, K 1 (a 1) i_1 * Y ![i, i_1] =
            ∑ x, ∑ x_1, K 0 (a 0) x * (K 1 (a 1) x_1 * Y ![x, x_1]) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
        rw [e2]
        ring_nf


/-- The norm of the expanded kernel is at most `Φ` of the entrywise norm. -/
private theorem duhamelI_UN_abs {X : Type*} [Fintype X] [DecidableEq X] (T : X → X → ℝ) {α β h : ℝ}
    (K : Fin 2 → Matrix X X ℂ) (hK : ∀ i x y, ‖K i x y‖ ≤ T x y) (hT : ∀ x y, 0 ≤ T x y)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β) (hαβ : α * β ≤ h) (hβ2 : β ^ 2 ≤ h ^ 2)
    (Y : (Fin 2 → X) → ℂ) (a : Fin 2 → X) :
    ‖∑ b : Fin 2 → X, (∏ i, (((α : ℝ) : ℂ) • (1 : Matrix X X ℂ) + ((β : ℝ) : ℂ) • K i) (a i) (b i)) * Y b‖ ≤
      duhamelI_Phi T h (fun x y => ‖Y ![x, y]‖) a := by
  rw [duhamelI_expand]
  have hYa : a = ![a 0, a 1] := by ext i; fin_cases i <;> rfl
  have s1 : ‖∑ y, K 1 (a 1) y * Y ![a 0, y]‖ ≤ ∑ y, T (a 1) y * ‖Y ![a 0, y]‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hK _ _ _) (norm_nonneg _))
  have s2 : ‖∑ x, K 0 (a 0) x * Y ![x, a 1]‖ ≤ ∑ x, T (a 0) x * ‖Y ![x, a 1]‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hK _ _ _) (norm_nonneg _))
  have s3 : ‖∑ x, ∑ y, K 0 (a 0) x * K 1 (a 1) y * Y ![x, y]‖ ≤
      ∑ x, ∑ y, T (a 0) x * T (a 1) y * ‖Y ![x, y]‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun y _ => by
        rw [norm_mul, norm_mul]
        exact mul_le_mul_of_nonneg_right (mul_le_mul (hK _ _ _) (hK _ _ _) (norm_nonneg _) (hT _ _))
          (norm_nonneg _)))
  have hs12 : 0 ≤ ∑ y, T (a 1) y * ‖Y ![a 0, y]‖ + ∑ x, T (a 0) x * ‖Y ![x, a 1]‖ :=
    add_nonneg (Finset.sum_nonneg fun y _ => mul_nonneg (hT _ _) (norm_nonneg _))
      (Finset.sum_nonneg fun x _ => mul_nonneg (hT _ _) (norm_nonneg _))
  have hh0 : 0 ≤ h := (mul_nonneg hα0 hβ0).trans hαβ
  have n1 : ‖((α : ℝ) : ℂ) ^ 2 * Y a‖ ≤ ‖Y ![a 0, a 1]‖ := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hα0, ← hYa]
    have : α ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this (norm_nonneg (Y a))]
  have n2 : ‖((α : ℝ) : ℂ) * ((β : ℝ) : ℂ) * (∑ y, K 1 (a 1) y * Y ![a 0, y] + ∑ x, K 0 (a 0) x * Y ![x, a 1])‖ ≤
      h * (∑ y, T (a 1) y * ‖Y ![a 0, y]‖ + ∑ x, T (a 0) x * ‖Y ![x, a 1]‖) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hα0, Real.norm_of_nonneg hβ0]
    exact mul_le_mul hαβ ((norm_add_le _ _).trans (add_le_add s1 s2)) (norm_nonneg _) hh0
  have n3 : ‖((β : ℝ) : ℂ) ^ 2 * ∑ x, ∑ y, K 0 (a 0) x * K 1 (a 1) y * Y ![x, y]‖ ≤
      h ^ 2 * ∑ x, ∑ y, T (a 0) x * T (a 1) y * ‖Y ![x, y]‖ := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hβ0]
    exact mul_le_mul hβ2 s3 (norm_nonneg _) (sq_nonneg h)
  refine norm_add₃_le.trans ?_
  unfold duhamelI_Phi
  linarith


theorem duhamelI_Phi_mono_h {X : Type*} [Fintype X] {T : X → X → ℝ} {h h' : ℝ} {q : X → X → ℝ}
    (hT : ∀ x y, 0 ≤ T x y) (hq : ∀ x y, 0 ≤ q x y) (hh : 0 ≤ h) (hhh : h ≤ h') (a : Fin 2 → X) :
    duhamelI_Phi T h q a ≤ duhamelI_Phi T h' q a := by
  unfold duhamelI_Phi
  have s1 : 0 ≤ ∑ y, T (a 1) y * q (a 0) y := Finset.sum_nonneg fun y _ => mul_nonneg (hT _ _) (hq _ _)
  have s2 : 0 ≤ ∑ x, T (a 0) x * q x (a 1) := Finset.sum_nonneg fun x _ => mul_nonneg (hT _ _) (hq _ _)
  have s3 : 0 ≤ ∑ x, ∑ y, T (a 0) x * T (a 1) y * q x y :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => mul_nonneg (mul_nonneg (hT _ _) (hT _ _)) (hq _ _)
  have hs := add_nonneg s1 s2
  nlinarith [mul_le_mul_of_nonneg_right hhh hs, mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hh hhh 2) s3]

/-- **The martingale term, generic form.** -/
private theorem duhamelI_mart_gen {X : Type*} [Fintype X] [DecidableEq X] (T : X → X → ℝ)
    (K : Fin 2 → Matrix X X ℂ) (hK : ∀ i x y, ‖K i x y‖ ≤ T x y) (hT : ∀ x y, 0 ≤ T x y)
    (α : ℕ → ℝ) (Kn : ℕ) (hK1 : 1 ≤ Kn) (ha0 : ∀ j ≤ Kn, 0 ≤ α j) (ha1 : ∀ j ≤ Kn, α j ≤ 1)
    (hmono : ∀ j < Kn, α j ≤ α (j + 1)) (Mt : ℕ → (Fin 2 → X) → ℂ) (B : (Fin 2 → X) → ℝ)
    (hB : ∀ b j, j ≤ Kn → ‖Mt j b‖ ≤ B b) (a : Fin 2 → X) :
    ‖∑ j ∈ Finset.range Kn, ∑ b : Fin 2 → X,
        (∏ i, (((α j : ℝ) : ℂ) • (1 : Matrix X X ℂ) + (((1 - α j : ℝ)) : ℂ) • K i) (a i) (b i)) *
          (Mt (j + 1) b - Mt j b)‖ ≤
      4 * duhamelI_Phi T (1 - α 0) (fun x y => B ![x, y]) a := by
  have hB0 : ∀ b, 0 ≤ B b := fun b => (norm_nonneg _).trans (hB b 0 (Nat.zero_le _))
  have hexp : ∀ j, ∑ b : Fin 2 → X, (∏ i, (((α j : ℝ) : ℂ) • (1 : Matrix X X ℂ) + (((1 - α j : ℝ)) : ℂ) • K i) (a i) (b i)) *
          (Mt (j + 1) b - Mt j b) =
      ((α j ^ 2 : ℝ) : ℂ) * (Mt (j + 1) a - Mt j a) +
        ((α j * (1 - α j) : ℝ) : ℂ) * (∑ y, K 1 (a 1) y * (Mt (j + 1) ![a 0, y] - Mt j ![a 0, y]) +
          ∑ x, K 0 (a 0) x * (Mt (j + 1) ![x, a 1] - Mt j ![x, a 1])) +
        (((1 - α j) ^ 2 : ℝ) : ℂ) * ∑ x, ∑ y, K 0 (a 0) x * K 1 (a 1) y * (Mt (j + 1) ![x, y] - Mt j ![x, y]) := by
    intro j
    rw [duhamelI_expand]
    push_cast
    ring
  simp_rw [hexp]
  have hYa : a = ![a 0, a 1] := by ext i; fin_cases i <;> rfl
  have hw := fun b => duhamelI_weights α Kn hK1 ha0 ha1 hmono (fun j => Mt j b) (hB b)
  -- the three reorganised sums
  have P1 : ∑ j ∈ Finset.range Kn, ((α j * (1 - α j) : ℝ) : ℂ) * ∑ y, K 1 (a 1) y * (Mt (j + 1) ![a 0, y] - Mt j ![a 0, y]) =
      ∑ y, K 1 (a 1) y * ∑ j ∈ Finset.range Kn, ((α j * (1 - α j) : ℝ) : ℂ) * (Mt (j + 1) ![a 0, y] - Mt j ![a 0, y]) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun j _ => by ring
  have P2 : ∑ j ∈ Finset.range Kn, ((α j * (1 - α j) : ℝ) : ℂ) * ∑ x, K 0 (a 0) x * (Mt (j + 1) ![x, a 1] - Mt j ![x, a 1]) =
      ∑ x, K 0 (a 0) x * ∑ j ∈ Finset.range Kn, ((α j * (1 - α j) : ℝ) : ℂ) * (Mt (j + 1) ![x, a 1] - Mt j ![x, a 1]) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun j _ => by ring
  have P3 : ∑ j ∈ Finset.range Kn, (((1 - α j) ^ 2 : ℝ) : ℂ) * ∑ x, ∑ y, K 0 (a 0) x * K 1 (a 1) y * (Mt (j + 1) ![x, y] - Mt j ![x, y]) =
      ∑ x, ∑ y, K 0 (a 0) x * K 1 (a 1) y * ∑ j ∈ Finset.range Kn, (((1 - α j) ^ 2 : ℝ) : ℂ) * (Mt (j + 1) ![x, y] - Mt j ![x, y]) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun j _ => by ring
  have hsum : ∑ j ∈ Finset.range Kn, (((α j ^ 2 : ℝ) : ℂ) * (Mt (j + 1) a - Mt j a) +
        ((α j * (1 - α j) : ℝ) : ℂ) * (∑ y, K 1 (a 1) y * (Mt (j + 1) ![a 0, y] - Mt j ![a 0, y]) +
          ∑ x, K 0 (a 0) x * (Mt (j + 1) ![x, a 1] - Mt j ![x, a 1])) +
        (((1 - α j) ^ 2 : ℝ) : ℂ) * ∑ x, ∑ y, K 0 (a 0) x * K 1 (a 1) y * (Mt (j + 1) ![x, y] - Mt j ![x, y])) =
      (∑ j ∈ Finset.range Kn, ((α j ^ 2 : ℝ) : ℂ) * (Mt (j + 1) a - Mt j a)) +
        (∑ y, K 1 (a 1) y * ∑ j ∈ Finset.range Kn, ((α j * (1 - α j) : ℝ) : ℂ) * (Mt (j + 1) ![a 0, y] - Mt j ![a 0, y]) +
          ∑ x, K 0 (a 0) x * ∑ j ∈ Finset.range Kn, ((α j * (1 - α j) : ℝ) : ℂ) * (Mt (j + 1) ![x, a 1] - Mt j ![x, a 1])) +
        ∑ x, ∑ y, K 0 (a 0) x * K 1 (a 1) y * ∑ j ∈ Finset.range Kn, (((1 - α j) ^ 2 : ℝ) : ℂ) * (Mt (j + 1) ![x, y] - Mt j ![x, y]) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← P1, ← P2, ← P3, ← Finset.sum_add_distrib]
    simp only [mul_add, Finset.sum_add_distrib]
  rw [hsum]
  -- norms
  have n0 : ‖∑ j ∈ Finset.range Kn, ((α j ^ 2 : ℝ) : ℂ) * (Mt (j + 1) a - Mt j a)‖ ≤ 4 * B a := by
    have := (hw a).1
    simpa [Complex.real_smul] using this
  have n1 : ∀ x : Fin 2 → X, ‖∑ j ∈ Finset.range Kn, ((α j * (1 - α j) : ℝ) : ℂ) * (Mt (j + 1) x - Mt j x)‖ ≤ 4 * B x * (1 - α 0) := by
    intro x
    have := (hw x).2.1
    simpa [Complex.real_smul] using this
  have n2 : ∀ x : Fin 2 → X, ‖∑ j ∈ Finset.range Kn, (((1 - α j) ^ 2 : ℝ) : ℂ) * (Mt (j + 1) x - Mt j x)‖ ≤ 4 * B x * (1 - α 0) ^ 2 := by
    intro x
    have := (hw x).2.2
    simpa [Complex.real_smul] using this
  have m1 : ‖∑ y, K 1 (a 1) y * ∑ j ∈ Finset.range Kn, ((α j * (1 - α j) : ℝ) : ℂ) * (Mt (j + 1) ![a 0, y] - Mt j ![a 0, y])‖ ≤
      ∑ y, T (a 1) y * (4 * B ![a 0, y] * (1 - α 0)) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => by
      rw [norm_mul]; exact mul_le_mul (hK _ _ _) (n1 _) (norm_nonneg _) (hT _ _))
  have m2 : ‖∑ x, K 0 (a 0) x * ∑ j ∈ Finset.range Kn, ((α j * (1 - α j) : ℝ) : ℂ) * (Mt (j + 1) ![x, a 1] - Mt j ![x, a 1])‖ ≤
      ∑ x, T (a 0) x * (4 * B ![x, a 1] * (1 - α 0)) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => by
      rw [norm_mul]; exact mul_le_mul (hK _ _ _) (n1 _) (norm_nonneg _) (hT _ _))
  have m3 : ‖∑ x, ∑ y, K 0 (a 0) x * K 1 (a 1) y * ∑ j ∈ Finset.range Kn, (((1 - α j) ^ 2 : ℝ) : ℂ) * (Mt (j + 1) ![x, y] - Mt j ![x, y])‖ ≤
      ∑ x, ∑ y, T (a 0) x * T (a 1) y * (4 * B ![x, y] * (1 - α 0) ^ 2) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => by
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul (hK _ _ _) (hK _ _ _) (norm_nonneg _) (hT _ _)) (n2 _) (norm_nonneg _)
        (mul_nonneg (hT _ _) (hT _ _))))
  refine norm_add₃_le.trans ?_
  have e1 : ∑ y, T (a 1) y * (4 * B ![a 0, y] * (1 - α 0)) = 4 * (1 - α 0) * ∑ y, T (a 1) y * B ![a 0, y] := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
  have e2 : ∑ x, T (a 0) x * (4 * B ![x, a 1] * (1 - α 0)) = 4 * (1 - α 0) * ∑ x, T (a 0) x * B ![x, a 1] := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
  have e3 : ∑ x, ∑ y, T (a 0) x * T (a 1) y * (4 * B ![x, y] * (1 - α 0) ^ 2) =
      4 * (1 - α 0) ^ 2 * ∑ x, ∑ y, T (a 0) x * T (a 1) y * B ![x, y] := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
  unfold duhamelI_Phi
  have hBa : B ![a 0, a 1] = B a := by rw [← hYa]
  simp only [hBa]
  refine (add_le_add (add_le_add n0 ((norm_add_le _ _).trans (add_le_add m1 m2))) m3).trans ?_
  rw [e1, e2, e3]
  exact le_of_eq (by ring)


/-! ## 3. The model-level facts -/

section ModelKernel

variable {d : ℕ}

private theorem duhamelI_zdistInf_sub_comm {L : ℕ} [NeZero L] (a b : Zd d L) :
    zdistInf d L (a - b) = zdistInf d L (b - a) := by
  unfold zdistInf
  refine Finset.sup_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply]
  rw [← neg_sub (a i) (b i), zdist_neg]

private theorem duhamelI_tailW_eq {L : ℕ} [NeZero L] (g t W D : ℝ) (x : Zd d L) :
    tailW d L g t (L : ℝ) W D (zdistInf d L x : ℕ) =
      max (tailT d L g t (zdistInf d L x : ℕ)) (W ^ (-D)) := by
  unfold tailW
  rw [min_eq_left]
  have : zdistInf d L x ≤ L := Finset.sup_le fun i _ => zdist_le_L (x i)
  exact_mod_cast this

/-- **`Φ` of a profile** (`(uwp2-92kj)` in the explicit form `step5Kernel_profile_explicit_holds`, applied at `(v, w)` and at
`(w, w)`): for `0 ≤ v ≤ w < 1`, in the window `(TTT2)`,
`Φ_{2(1-v)}(W^{-d}𝒯̃^L_{v,D}) ≤ C ρ W^{-d} (𝒯_w(|a₁-a₂|) + ρ W^{-D})`, `ρ = (1-v)/(1-w)`, `C = C(d, Λ)`. -/
theorem duhamelI_Phi_STprof (hd : 3 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (n : ℕ) (D v w : ℝ), 0 < sz.lam n → sz.lam n ≤ Λ → 0 ≤ v → v ≤ w →
      w < 1 → (sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - w ∨ 1 - v ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) →
      ∀ a : Fin 2 → Zd d (sz.L n),
        duhamelI_Phi (fun x y => ‖Theta d (sz.L n) (sz.lam n) (w : ℂ) x y‖) (2 * (1 - v))
            (fun x y => STprof sz n v D ((sz.L n : ℕ) : ℝ) x y) a ≤
          C * ((1 - v) / (1 - w)) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
            (tailT d (sz.L n) (sz.lam n) w ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) +
              (1 - v) / (1 - w) * ((sz.W n : ℕ) : ℝ) ^ (-D))) := by
  obtain ⟨C₃, hC₃, H3⟩ := step5Kernel_profile_explicit_holds d Λ hd hΛ
  refine ⟨(1 + 2 * C₃) ^ 2 + 9 + 4 * C₃, by positivity, ?_⟩
  intro sz n D v w hg hgΛ hv hvw hw hreg a
  have hL := sz.three_le_L n
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hw0 : 0 ≤ w := hv.trans hvw
  have hv1 : v < 1 := hvw.trans_lt hw
  have h1w : 0 < 1 - w := by linarith
  set Wm := ((sz.W n : ℕ) : ℝ) ^ (-D) with hWm
  set Wd := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ with hWd
  have hWd0 : 0 ≤ Wd := by positivity
  have hWm0 : 0 ≤ Wm := Real.rpow_nonneg hW.le _
  have hprof : ∀ x y : Zd d (sz.L n), STprof sz n v D ((sz.L n : ℕ) : ℝ) x y =
      Wd * tailW d (sz.L n) (sz.lam n) v ((sz.L n : ℕ) : ℝ) ((sz.W n : ℕ) : ℝ) D (zdistInf d (sz.L n) (x - y) : ℕ) :=
    fun x y => rfl
  refine duhamelI_Phi_prof (fun x y => ‖Theta d (sz.L n) (sz.lam n) (w : ℂ) x y‖)
    (fun x y => STprof sz n v D ((sz.L n : ℕ) : ℝ) x y)
    (fun x y => tailT d (sz.L n) (sz.lam n) w (zdistInf d (sz.L n) (x - y) : ℕ)) hv1 hw hvw rfl hC₃.le hWd0 hWm0
    (fun x y => norm_nonneg _) ?_ (fun x y => tailT_nonneg (Nat.cast_nonneg _)) ?_ ?_ ?_ ?_ ?_ a
  · intro x
    simpa using sum_norm_Theta_row_le (g := sz.lam n) hL hw0 hw (m := (1 : ℂ)) (by simp) x
  · intro x y
    simp only [duhamelI_zdistInf_sub_comm x y]
  · intro x y
    simp only [hprof, duhamelI_zdistInf_sub_comm x y]
  · intro x y
    rw [hprof, duhamelI_tailW_eq]
    refine mul_le_mul_of_nonneg_left (max_le ?_ ?_) hWd0
    · have := ST_tailT_mono_time (d := d) (L := sz.L n) (g := sz.lam n) (u := v) (v := w)
        (r := (zdistInf d (sz.L n) (x - y) : ℕ)) (by exact_mod_cast (by omega : 1 ≤ sz.L n)) hg.le hvw hw (Nat.cast_nonneg _)
      linarith [hWm0]
    · have := tailT_nonneg (d := d) (L := sz.L n) (g := sz.lam n) (t := w) (r := (zdistInf d (sz.L n) (x - y) : ℕ)) (Nat.cast_nonneg _)
      linarith
  · intro x y
    have h := H3 (sz.L n) hL (sz.lam n) ((sz.W n : ℕ) : ℝ) D v w hg hgΛ hW hv hvw hw hreg x y
    have e : (1 - v) * ∑ b, ‖Theta d (sz.L n) (sz.lam n) (w : ℂ) x b‖ *
        STprof sz n v D ((sz.L n : ℕ) : ℝ) b y =
        Wd * ((1 - v) * ∑ b, ‖Theta d (sz.L n) (sz.lam n) (w : ℂ) x b‖ *
          tailW d (sz.L n) (sz.lam n) v ((sz.L n : ℕ) : ℝ) ((sz.W n : ℕ) : ℝ) D (zdistInf d (sz.L n) (b - y) : ℕ)) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by rw [hprof]; ring
    change (1 - v) * ∑ b, ‖Theta d (sz.L n) (sz.lam n) (w : ℂ) x b‖ * STprof sz n v D ((sz.L n : ℕ) : ℝ) b y ≤ _
    rw [e]
    exact mul_le_mul_of_nonneg_left h hWd0
  · intro x y
    have h := H3 (sz.L n) hL (sz.lam n) ((sz.W n : ℕ) : ℝ) D w w hg hgΛ hW hw0 le_rfl hw (le_total _ _) x y
    rw [div_self h1w.ne', one_mul] at h
    have hle : (1 - w) * ∑ b, ‖Theta d (sz.L n) (sz.lam n) (w : ℂ) x b‖ *
          tailT d (sz.L n) (sz.lam n) w (zdistInf d (sz.L n) (b - y) : ℕ) ≤
        (1 - w) * ∑ b, ‖Theta d (sz.L n) (sz.lam n) (w : ℂ) x b‖ *
          tailW d (sz.L n) (sz.lam n) w ((sz.L n : ℕ) : ℝ) ((sz.W n : ℕ) : ℝ) D (zdistInf d (sz.L n) (b - y) : ℕ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (by
        rw [duhamelI_tailW_eq]; exact le_max_left _ _) (norm_nonneg _)) h1w.le
    exact hle.trans h

end ModelKernel

/-! ## 4. The kernel `𝒰` through `Φ` -/

section UgenPhi

variable {d L : ℕ} [NeZero L] {g E : ℝ}

private theorem duhamelI_theta_le (hL : 3 ≤ L) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) {μ : ℂ} (hμ : ‖μ‖ = 1)
    (x y : Zd d L) :
    ‖Theta d L g ((w : ℂ) * μ) x y‖ ≤ ‖Theta d L g (w : ℂ) x y‖ :=
  (norm_Theta_apply_le hL hw0 hw1 hμ x y).trans (step5Kernel_norm_Theta_eq_re hL hw0 hw1 x y).ge

/-- `‖(𝒰_{v,w} ∘ Y)_a‖ ≤ Φ_{2(1-v)}(|Y|)` (`(eq:decompU)`, `α = v/w`, `β = (w-v)/w ≤ 2(1-v)`). -/
theorem duhamelI_Ugen_le (hL : 3 ≤ L) (hE : |E| ≤ 2) (σ : Fin 2 → Bool) {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w)
    (hw0 : 0 < w) (hw1 : w < 1) (Y : (Fin 2 → Zd d L) → ℂ) (a : Fin 2 → Zd d L) :
    ‖RBM.Ind.Ugen d L g E σ v w Y a‖ ≤
      duhamelI_Phi (fun x y => ‖Theta d L g (w : ℂ) x y‖) (2 * (1 - v)) (fun x y => ‖Y ![x, y]‖) a := by
  have hm : ∀ i, ‖mSigma E (σ i)‖ = 1 := fun i => norm_mSigma hE (σ i)
  unfold RBM.Ind.Ugen
  rw [step5Kernel_UN_decompU hL hm hw0 hw1]
  have hα1 : v / w ≤ 1 := (div_le_one hw0).2 hvw
  have hβ : (w - v) / w ≤ 2 * (1 - v) := duhamelI_beta_le hv hvw hw0 hw1
  have hβ0 : 0 ≤ (w - v) / w := div_nonneg (by linarith) hw0.le
  have hα0 : 0 ≤ v / w := div_nonneg hv hw0.le
  refine duhamelI_UN_abs (fun x y => ‖Theta d L g (w : ℂ) x y‖) (α := v / w) (β := (w - v) / w) (h := 2 * (1 - v))
    (fun i => Theta d L g ((w : ℂ) * cycProd (fun i => mSigma E (σ i)) i))
    (fun i x y => duhamelI_theta_le hL hw0.le hw1 (norm_cycProd hm i) x y) (fun x y => norm_nonneg _) hα0 hα1 hβ0
    ?_ ?_ Y a
  · calc v / w * ((w - v) / w) ≤ 1 * ((w - v) / w) := mul_le_mul_of_nonneg_right hα1 hβ0
      _ ≤ 2 * (1 - v) := by linarith
  · exact pow_le_pow_left₀ hβ0 hβ 2

/-- **The martingale term through `Φ`**: `‖Σ_{j<K} (𝒰_{u_j,w} ∘ ΔM_j)_a‖ ≤ 4 Φ_{2(1-u_0)}(B)` if `|M_j(b)| ≤ B(b)`
for `j ≤ K` (`(uuwmskiow)`: Abel summation of the weights `α², αβ, β²`). -/
theorem duhamelI_mart_Ugen (hL : 3 ≤ L) (hE : |E| ≤ 2) (σ : Fin 2 → Bool) (u : ℕ → ℝ) (Kn : ℕ) (hK1 : 1 ≤ Kn)
    {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hu0 : ∀ j ≤ Kn, 0 ≤ u j) (huw : ∀ j ≤ Kn, u j ≤ w)
    (hmono : ∀ j < Kn, u j ≤ u (j + 1)) (Mt : ℕ → (Fin 2 → Zd d L) → ℂ) (B : (Fin 2 → Zd d L) → ℝ)
    (hB : ∀ b j, j ≤ Kn → ‖Mt j b‖ ≤ B b) (a : Fin 2 → Zd d L) :
    ‖∑ j ∈ Finset.range Kn, RBM.Ind.Ugen d L g E σ (u j) w (fun b => Mt (j + 1) b - Mt j b) a‖ ≤
      4 * duhamelI_Phi (fun x y => ‖Theta d L g (w : ℂ) x y‖) (2 * (1 - u 0)) (fun x y => B ![x, y]) a := by
  have hm : ∀ i, ‖mSigma E (σ i)‖ = 1 := fun i => norm_mSigma hE (σ i)
  have e : ∀ j, RBM.Ind.Ugen d L g E σ (u j) w (fun b => Mt (j + 1) b - Mt j b) a =
      ∑ b : Fin 2 → Zd d L, (∏ i, (((u j / w : ℝ) : ℂ) • (1 : Matrix (Zd d L) (Zd d L) ℂ) +
        (((1 - u j / w : ℝ)) : ℂ) • Theta d L g ((w : ℂ) * cycProd (fun i => mSigma E (σ i)) i)) (a i) (b i)) *
          (Mt (j + 1) b - Mt j b) := by
    intro j
    unfold RBM.Ind.Ugen
    rw [step5Kernel_UN_decompU hL hm hw0 hw1]
    have : (w - u j) / w = 1 - u j / w := by field_simp
    rw [this]
  simp_rw [e]
  have h := duhamelI_mart_gen (fun x y => ‖Theta d L g (w : ℂ) x y‖)
    (fun i => Theta d L g ((w : ℂ) * cycProd (fun i => mSigma E (σ i)) i))
    (fun i x y => duhamelI_theta_le hL hw0.le hw1 (norm_cycProd hm i) x y) (fun x y => norm_nonneg _)
    (fun j => u j / w) Kn hK1 (fun j hj => div_nonneg (hu0 j hj) hw0.le)
    (fun j hj => (div_le_one hw0).2 (huw j hj)) (fun j hj => div_le_div_of_nonneg_right (hmono j hj) hw0.le)
    Mt B hB a
  refine h.trans ?_
  have hB0 : ∀ x y, 0 ≤ B ![x, y] := fun x y => (norm_nonneg _).trans (hB _ 0 (Nat.zero_le _))
  have hβ : 1 - u 0 / w ≤ 2 * (1 - u 0) := by
    have := duhamelI_beta_le (hu0 0 (Nat.zero_le _)) (huw 0 (Nat.zero_le _)) hw0 hw1
    have e2 : (w - u 0) / w = 1 - u 0 / w := by field_simp
    linarith
  have hβ0 : 0 ≤ 1 - u 0 / w := by
    have := (div_le_one hw0).2 (huw 0 (Nat.zero_le _))
    linarith
  exact mul_le_mul_of_nonneg_left (duhamelI_Phi_mono_h (fun x y => norm_nonneg _) hB0 hβ0 hβ a) (by norm_num)

end UgenPhi

/-! ## 5. The pathwise bound at one size index -/

section Path

variable {d : ℕ}

private theorem duhamelI_grid (s tt : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hst : s n ≤ tt n) (hK : K n ≠ 0) :
    0 ≤ gridStep s tt K n ∧ (∀ j, gridTime s tt K n (j + 1) = gridTime s tt K n j + gridStep s tt K n) ∧
      gridTime s tt K n 0 = s n ∧ gridTime s tt K n (K n) = tt n ∧
      (K n : ℝ) * gridStep s tt K n = tt n - s n ∧
      (∀ j ≤ K n, s n ≤ gridTime s tt K n j ∧ gridTime s tt K n j ≤ tt n) ∧
      (∀ j < K n, gridTime s tt K n j ≤ gridTime s tt K n (j + 1)) := by
  have hKpos : (0 : ℝ) < K n := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hΔ : 0 ≤ gridStep s tt K n := div_nonneg (by linarith) hKpos.le
  refine ⟨hΔ, fun j => ?_, ST_gridTime_zero s tt K n, gridTime_last s tt K n hK, ?_,
    fun j hj => ST_gridTime_mem s tt K n j hst hK hj, fun j _ => ?_⟩
  · unfold gridTime; push_cast; ring
  · unfold gridStep; field_simp
  · unfold gridTime; push_cast; nlinarith [hΔ]

/-- The crude Riemann sum `Σ_{j<K} Δ η_{u_j}⁻¹ ≤ ρ / Im m` (`η_u = (1-u) Im m`, `u_j ≤ w`, `KΔ = w - s ≤ 1 - s`). -/
private theorem duhamelI_riemann (E : ℝ) (u : ℕ → ℝ) (Δ s w : ℝ) (K : ℕ) (hΔ : 0 ≤ Δ)
    (hKΔ : (K : ℝ) * Δ = w - s) (hw : w < 1) (hu : ∀ j < K, u j ≤ w) (hc : 0 < (mE E).im) :
    ∑ j ∈ Finset.range K, Δ * (etaT E (u j))⁻¹ ≤ ((1 - s) / (1 - w)) / (mE E).im := by
  have h1w : 0 < 1 - w := by linarith
  have hterm : ∀ j ∈ Finset.range K, Δ * (etaT E (u j))⁻¹ ≤ Δ * ((1 - w) * (mE E).im)⁻¹ := by
    intro j hj
    refine mul_le_mul_of_nonneg_left ?_ hΔ
    unfold etaT
    exact inv_anti₀ (mul_pos h1w hc)
      (mul_le_mul_of_nonneg_right (by linarith [hu j (Finset.mem_range.1 hj)]) hc.le)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc (K : ℝ) * (Δ * ((1 - w) * (mE E).im)⁻¹) = ((K : ℝ) * Δ) * ((1 - w) * (mE E).im)⁻¹ := by ring
    _ = (w - s) * ((1 - w) * (mE E).im)⁻¹ := by rw [hKΔ]
    _ ≤ (1 - s) * ((1 - w) * (mE E).im)⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith [hKΔ, mul_nonneg (Nat.cast_nonneg K : (0 : ℝ) ≤ K) hΔ])
          (by positivity)
    _ = ((1 - s) / (1 - w)) / (mE E).im := by field_simp

/-- `W^{-d} 𝒯̃^L_{u,D}` is nondecreasing in the time. -/
private theorem duhamelI_prof_mono (sz : Sizes d) (n : ℕ) {u v D : ℝ} (hg : 0 ≤ sz.lam n) (huv : u ≤ v)
    (hv : v < 1) (x y : Zd d (sz.L n)) :
    STprof sz n u D ((sz.L n : ℕ) : ℝ) x y ≤ STprof sz n v D ((sz.L n : ℕ) : ℝ) x y := by
  unfold STprof
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  unfold tailW
  exact max_le_max (ST_tailT_mono_time (by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n))
    hg huv hv (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _))) le_rfl

private theorem duhamelI_sqrt_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

private theorem duhamelI_sqrt_aux {Λ ρ c₀ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 1 ≤ ρ) (hc₀ : 0 < c₀) :
    Real.sqrt (2 * Λ * ρ / c₀) ≤ Λ * ρ * (2 / c₀ + 1) := by
  have h1 : 2 * Λ * ρ / c₀ = (Λ * ρ) * (2 / c₀) := by ring
  rw [h1, Real.sqrt_mul (by positivity)]
  have hΛρ : 1 ≤ Λ * ρ := by nlinarith
  have hx : Real.sqrt (Λ * ρ) ≤ Λ * ρ := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hy : Real.sqrt (2 / c₀) ≤ 2 / c₀ + 1 := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith [sq_nonneg (2 / c₀)]
  exact mul_le_mul hx hy (Real.sqrt_nonneg _) (by positivity)

private theorem duhamelI_rpow_quarter {A : ℝ} (hA : 1 ≤ A) :
    0 < A ^ (-(1 / 4) : ℝ) ∧ A ^ (-(1 / 4) : ℝ) ≤ 1 ∧ A ^ (-(1 / 2) : ℝ) = (A ^ (-(1 / 4) : ℝ)) ^ 2 ∧
      A ^ (-(1 / 3) : ℝ) ≤ A ^ (-(1 / 4) : ℝ) := by
  have hA0 : 0 < A := by linarith
  refine ⟨Real.rpow_pos_of_pos hA0 _, Real.rpow_le_one_of_one_le_of_nonpos hA (by norm_num), ?_,
    Real.rpow_le_rpow_of_exponent_le hA (by norm_num)⟩
  rw [← Real.rpow_natCast, ← Real.rpow_mul hA0.le]; norm_num

private theorem duhamelI_absorb {Λ κ F P Wm A ρ Nτ : ℝ} (hΛ : 1 ≤ Λ) (hκ : 0 ≤ κ) (hF : 0 ≤ F) (hP : 0 ≤ P)
    (hWm : 0 ≤ Wm) (hA : 1 ≤ A) (hρ1 : 1 ≤ ρ) (hρ : ρ ≤ (2 * A) ^ (1 / 100 : ℝ))
    (hN : (2 * κ + 1) * Λ ^ 2 ≤ Nτ) :
    Λ * F + Λ ^ 2 * κ * (ρ ^ 3 * A ^ (-(1 / 4) : ℝ)) * P + Wm ≤ Nτ * (F + A ^ (-(1 / 5) : ℝ) * P + Wm) := by
  have hA0 : 0 < A := by linarith
  have h2A : (0 : ℝ) < 2 * A := by linarith
  have hρ3 : ρ ^ 3 ≤ 2 * A ^ (3 / 100 : ℝ) := by
    have h1 : ρ ^ 3 ≤ ((2 * A) ^ (1 / 100 : ℝ)) ^ 3 := pow_le_pow_left₀ (by linarith) hρ 3
    have h2 : ((2 * A) ^ (1 / 100 : ℝ)) ^ 3 = (2 * A) ^ (3 / 100 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h2A.le]; norm_num
    have h3 : (2 * A) ^ (3 / 100 : ℝ) = 2 ^ (3 / 100 : ℝ) * A ^ (3 / 100 : ℝ) := Real.mul_rpow (by norm_num) hA0.le
    have h4 : (2 : ℝ) ^ (3 / 100 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (3 / 100 : ℝ) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    rw [h2, h3] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hA0.le _))
  have hexp : A ^ (3 / 100 : ℝ) * A ^ (-(1 / 4) : ℝ) ≤ A ^ (-(1 / 5) : ℝ) := by
    rw [← Real.rpow_add hA0]
    exact Real.rpow_le_rpow_of_exponent_le hA (by norm_num)
  have h5 : ρ ^ 3 * A ^ (-(1 / 4) : ℝ) ≤ 2 * A ^ (-(1 / 5) : ℝ) := by
    have := mul_le_mul_of_nonneg_right hρ3 (Real.rpow_nonneg hA0.le (-(1 / 4) : ℝ))
    nlinarith
  have hA5 : 0 ≤ A ^ (-(1 / 5) : ℝ) := Real.rpow_nonneg hA0.le _
  have hΛ2 : Λ ≤ Λ ^ 2 := by nlinarith
  have hΛ0 : 0 ≤ Λ ^ 2 := sq_nonneg Λ
  have s1 : Λ ^ 2 * κ * (ρ ^ 3 * A ^ (-(1 / 4) : ℝ)) * P ≤ Λ ^ 2 * κ * (2 * A ^ (-(1 / 5) : ℝ)) * P :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 (mul_nonneg hΛ0 hκ)) hP
  have s2 : Λ * F ≤ Λ ^ 2 * F := mul_le_mul_of_nonneg_right hΛ2 hF
  have hX : 0 ≤ A ^ (-(1 / 5) : ℝ) * P := mul_nonneg hA5 hP
  have hN0 : 0 ≤ Nτ := le_trans (by positivity) hN
  have hΛ1 : 1 ≤ Λ ^ 2 := by nlinarith
  nlinarith [mul_nonneg (mul_nonneg hκ hΛ0) hX, mul_nonneg hΛ0 hF, mul_nonneg hΛ0 hWm, mul_nonneg (mul_nonneg hκ hΛ0) hF,
    mul_nonneg (mul_nonneg hκ hΛ0) hWm, mul_le_mul_of_nonneg_right hN (add_nonneg (add_nonneg hF hX) hWm)]

/-- The crude Riemann bound in the form used below: `Σ_{j<K} Δ η_{u_j}⁻¹ ≤ ρ / c₀` for `c₀ ≤ Im m`. -/
private theorem duhamelI_riemann' (E : ℝ) (u : ℕ → ℝ) (Δ s w c₀ : ℝ) (K : ℕ) (hΔ : 0 ≤ Δ)
    (hKΔ : (K : ℝ) * Δ = w - s) (hsw : s ≤ w) (hw : w < 1) (hu : ∀ j < K, u j ≤ w) (hc₀ : 0 < c₀)
    (hc : c₀ ≤ (mE E).im) :
    ∑ j ∈ Finset.range K, Δ * (etaT E (u j))⁻¹ ≤ ((1 - s) / (1 - w)) / c₀ :=
  (duhamelI_riemann E u Δ s w K hΔ hKΔ hw hu (lt_of_lt_of_le hc₀ hc)).trans
    (div_le_div_of_nonneg_left (div_nonneg (by linarith) (by linarith)) hc₀ hc)

/-- **The drift term** (`(jymwons-L-K)`, `(jymwons-Gc)`): if `|F_j(b)| ≤ Λ e₀ η_{u_j}⁻¹ W^{-d}𝒯̃^L_{u_j,D}`, then
`|Δ Σ_{j<K} (𝒰_{u_j,w} ∘ F_j)_a| ≤ Λ e₀ (ρ/c₀) C ρ W^{-d}(𝒯_w + ρ W^{-D})`, `ρ = (1-s)/(1-w)`. -/
private theorem duhamelI_drift (sz : Sizes d) (n : ℕ) {E s w Λ DE C c₀ e₀ Δ : ℝ} {K : ℕ} (u : ℕ → ℝ)
    (Fj : ℕ → (Fin 2 → Zd d (sz.L n)) → ℂ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (hs0 : 0 ≤ s) (hsw : s < w) (hw1 : w < 1) (hE : |E| ≤ 2) (hΛ : 0 ≤ Λ)
    (hC : 0 ≤ C) (he₀ : 0 ≤ e₀) (hc₀ : 0 < c₀) (hc : c₀ ≤ (mE E).im) (hΔ : 0 ≤ Δ)
    (hKΔ : (K : ℝ) * Δ = w - s) (hu_s : ∀ j ≤ K, s ≤ u j) (hu_w : ∀ j ≤ K, u j ≤ w)
    (hΦ : ∀ (D' v w' : ℝ), s ≤ v → v ≤ w' → w' ≤ w → ∀ a : Fin 2 → Zd d (sz.L n),
      duhamelI_Phi (fun x y => ‖Theta d (sz.L n) (sz.lam n) (w' : ℂ) x y‖) (2 * (1 - v))
          (fun x y => STprof sz n v D' ((sz.L n : ℕ) : ℝ) x y) a ≤
        C * ((1 - v) / (1 - w')) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
          (tailT d (sz.L n) (sz.lam n) w' ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) +
            (1 - v) / (1 - w') * ((sz.W n : ℕ) : ℝ) ^ (-D'))))
    (hF : ∀ j ≤ K, ∀ b : Fin 2 → Zd d (sz.L n), ‖Fj j b‖ ≤ (Λ * e₀ * (etaT E (u j))⁻¹) *
      STprof sz n (u j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1)) :
    ‖∑ j ∈ Finset.range K, (Δ : ℂ) * RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ (u j) w (Fj j) a‖ ≤
      Λ * e₀ * (((1 - s) / (1 - w)) / c₀) * (C * ((1 - s) / (1 - w)) *
        ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (tailT d (sz.L n) (sz.lam n) w
          ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) + (1 - s) / (1 - w) * ((sz.W n : ℕ) : ℝ) ^ (-DE)))) := by
  have hLn : 3 ≤ sz.L n := sz.three_le_L n
  have hw0 : 0 < w := lt_of_le_of_lt hs0 hsw
  have h1w : 0 < 1 - w := by linarith
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hc0 : 0 < (mE E).im := lt_of_lt_of_le hc₀ hc
  set ρ : ℝ := (1 - s) / (1 - w) with hρdef
  have hρ1 : 1 ≤ ρ := by rw [hρdef, le_div_iff₀ h1w]; linarith
  set Wd := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ with hWd
  have hWd0 : 0 < Wd := by positivity
  set T : ℝ := tailT d (sz.L n) (sz.lam n) w ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) with hT
  set WmE : ℝ := ((sz.W n : ℕ) : ℝ) ^ (-DE) with hWmE
  have hT0 : 0 ≤ T := tailT_nonneg (Nat.cast_nonneg _)
  have hWmE0 : 0 ≤ WmE := Real.rpow_nonneg hW.le _
  have hu_lt : ∀ j ≤ K, u j < 1 := fun j hj => (hu_w j hj).trans_lt hw1
  have hη : ∀ j ≤ K, 0 < etaT E (u j) := fun j hj => by
    unfold etaT; exact mul_pos (by linarith [hu_lt j hj]) hc0
  have hriem' := duhamelI_riemann' E u Δ s w c₀ K hΔ hKΔ hsw.le hw1 (fun j hj => hu_w j hj.le) hc₀ hc
  have hR0 : 0 ≤ C * ρ * (Wd * (T + ρ * WmE)) := by positivity
  have hterm : ∀ j ∈ Finset.range K, ‖(Δ : ℂ) * RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ (u j) w (Fj j) a‖ ≤
      Δ * ((Λ * e₀ * (etaT E (u j))⁻¹) * (C * ρ * (Wd * (T + ρ * WmE)))) := by
    intro j hj
    have hjK : j ≤ K := (Finset.mem_range.1 hj).le
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hΔ]
    refine mul_le_mul_of_nonneg_left ?_ hΔ
    have hej : 0 ≤ Λ * e₀ * (etaT E (u j))⁻¹ := by
      have := (hη j hjK).le; positivity
    have h1 := duhamelI_Ugen_le (g := sz.lam n) hLn hE σ (hs0.trans (hu_s j hjK)) (hu_w j hjK) hw0 hw1 (Fj j) a
    have h2 := duhamelI_Phi_mono (T := fun x y => ‖Theta d (sz.L n) (sz.lam n) (w : ℂ) x y‖)
      (h := 2 * (1 - u j)) (q := fun x y => ‖Fj j ![x, y]‖)
      (q' := fun x y => (Λ * e₀ * (etaT E (u j))⁻¹) * STprof sz n (u j) DE ((sz.L n : ℕ) : ℝ) x y)
      (fun x y => norm_nonneg _) (by linarith [hu_lt j hjK]) (fun x y => hF j hjK ![x, y]) a
    rw [duhamelI_Phi_smul] at h2
    have h4 := hΦ DE (u j) w (hu_s j hjK) (hu_w j hjK) le_rfl a
    have hρj : (1 - u j) / (1 - w) ≤ ρ := div_le_div_of_nonneg_right (by linarith [hu_s j hjK]) h1w.le
    have hρj0 : 0 ≤ (1 - u j) / (1 - w) := div_nonneg (by linarith [hu_lt j hjK]) h1w.le
    have h5 : C * ((1 - u j) / (1 - w)) * (Wd * (T + (1 - u j) / (1 - w) * WmE)) ≤
        C * ρ * (Wd * (T + ρ * WmE)) := by gcongr
    exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left (h4.trans h5) hej))
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  calc ∑ j ∈ Finset.range K, Δ * ((Λ * e₀ * (etaT E (u j))⁻¹) * (C * ρ * (Wd * (T + ρ * WmE))))
      = (Λ * e₀ * (C * ρ * (Wd * (T + ρ * WmE)))) * ∑ j ∈ Finset.range K, Δ * (etaT E (u j))⁻¹ := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ (Λ * e₀ * (C * ρ * (Wd * (T + ρ * WmE)))) * (ρ / c₀) :=
        mul_le_mul_of_nonneg_left hriem' (by positivity)
    _ = _ := by ring

/-- **The martingale term** (`(uuwmskiow)`): if `|M_j(b)| ≤ Λ (Σ_{i<j} Δ Q_i(b) + N^{-D_m})^{1/2}` and
`Q_i(b) ≤ 2Λ A^{-1/2} η_{u_i}⁻¹ (W^{-d}𝒯̃^L_{u_i,D})²`, then `|Σ_{j<K} (𝒰_{u_j,w} ∘ ΔM_j)_a|` is at most
`4 (Λ² ρ (2/c₀+1) A^{-1/4} ρ² C W^{-d}(𝒯_w + W^{-D}) + Λ N^{-D_m/2} 9 ρ²)`, `ρ = (1-s)/(1-w)`. -/
private theorem duhamelI_mart (sz : Sizes d) (n : ℕ) {E s w Λ DE Dm C c₀ Δ : ℝ} {K : ℕ} (u : ℕ → ℝ)
    (Mt : ℕ → (Fin 2 → Zd d (sz.L n)) → ℂ) (Q : ℕ → (Fin 2 → Zd d (sz.L n)) → ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (hK1 : 1 ≤ K) (hs0 : 0 ≤ s) (hsw : s < w) (hw1 : w < 1) (hE : |E| ≤ 2)
    (hlam : 0 < sz.lam n) (hΛ : 1 ≤ Λ) (hA : 1 ≤ STAI sz n) (hc₀ : 0 < c₀) (hc : c₀ ≤ (mE E).im)
    (hΔ : 0 ≤ Δ) (hKΔ : (K : ℝ) * Δ = w - s) (hu0 : u 0 = s) (hu_s : ∀ j ≤ K, s ≤ u j)
    (hu_w : ∀ j ≤ K, u j ≤ w) (hmono : ∀ j < K, u j ≤ u (j + 1))
    (hΦ : ∀ (D' v w' : ℝ), s ≤ v → v ≤ w' → w' ≤ w → ∀ a : Fin 2 → Zd d (sz.L n),
      duhamelI_Phi (fun x y => ‖Theta d (sz.L n) (sz.lam n) (w' : ℂ) x y‖) (2 * (1 - v))
          (fun x y => STprof sz n v D' ((sz.L n : ℕ) : ℝ) x y) a ≤
        C * ((1 - v) / (1 - w')) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
          (tailT d (sz.L n) (sz.lam n) w' ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) +
            (1 - v) / (1 - w') * ((sz.W n : ℕ) : ℝ) ^ (-D'))))
    (hQ0 : ∀ j b, 0 ≤ Q j b)
    (hQ : ∀ j ≤ K, ∀ b : Fin 2 → Zd d (sz.L n), Q j b ≤ 2 * (Λ * (STAI sz n ^ (-(1 / 2) : ℝ) *
      (etaT E (u j))⁻¹ * STprof sz n (u j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1) ^ 2)))
    (hMart : ∀ (b : Fin 2 → Zd d (sz.L n)) (j : ℕ), j ≤ K → ‖Mt j b‖ ≤ Λ * Real.sqrt (∑ i ∈ Finset.range j,
      Δ * Q i b + ((sz.size n : ℕ) : ℝ) ^ (-Dm))) :
    ‖∑ j ∈ Finset.range K, RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ (u j) w
        (fun b => Mt (j + 1) b - Mt j b) a‖ ≤
      4 * ((Λ * (Λ * ((1 - s) / (1 - w)) * (2 / c₀ + 1) * STAI sz n ^ (-(1 / 4) : ℝ))) *
          (((1 - s) / (1 - w)) ^ 2 * (C * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
            (tailT d (sz.L n) (sz.lam n) w ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) +
              ((sz.W n : ℕ) : ℝ) ^ (-DE))))) +
        (Λ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm))) * (9 * ((1 - s) / (1 - w)) ^ 2)) := by
  have hLn : 3 ≤ sz.L n := sz.three_le_L n
  have hw0 : 0 < w := lt_of_le_of_lt hs0 hsw
  have h1w : 0 < 1 - w := by linarith
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hc0 : 0 < (mE E).im := lt_of_lt_of_le hc₀ hc
  set ρ : ℝ := (1 - s) / (1 - w) with hρdef
  have hρ1 : 1 ≤ ρ := by rw [hρdef, le_div_iff₀ h1w]; linarith
  have hρe : 1 - s = ρ * (1 - w) := by rw [hρdef]; field_simp
  set A := STAI sz n with hAdef
  obtain ⟨ha₄0, ha₄1, ha₂, -⟩ := duhamelI_rpow_quarter hA
  set a₄ := A ^ (-(1 / 4) : ℝ) with ha₄def
  set Wd := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ with hWd
  have hWd0 : 0 < Wd := by positivity
  set T : ℝ := tailT d (sz.L n) (sz.lam n) w ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) with hT
  set WmE : ℝ := ((sz.W n : ℕ) : ℝ) ^ (-DE) with hWmE
  have hT0 : 0 ≤ T := tailT_nonneg (Nat.cast_nonneg _)
  have hWmE0 : 0 ≤ WmE := Real.rpow_nonneg hW.le _
  have hu_lt : ∀ j ≤ K, u j < 1 := fun j hj => (hu_w j hj).trans_lt hw1
  have hu_nn : ∀ j ≤ K, 0 ≤ u j := fun j hj => hs0.trans (hu_s j hj)
  have hη : ∀ j ≤ K, 0 < etaT E (u j) := fun j hj => by
    unfold etaT; exact mul_pos (by linarith [hu_lt j hj]) hc0
  have hriem' := duhamelI_riemann' E u Δ s w c₀ K hΔ hKΔ hsw.le hw1 (fun j hj => hu_w j hj.le) hc₀ hc
  have hN0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-Dm) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  set Bf : (Fin 2 → Zd d (sz.L n)) → ℝ := fun b => Λ * Real.sqrt (∑ j ∈ Finset.range K, Δ * Q j b +
    ((sz.size n : ℕ) : ℝ) ^ (-Dm)) with hBf
  have hB : ∀ b j, j ≤ K → ‖Mt j b‖ ≤ Bf b := by
    intro b j hj
    refine (hMart b j hj).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (add_le_add_left ?_ _)) (by linarith)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj)
      (fun i _ _ => mul_nonneg hΔ (hQ0 _ _))
  have hMr_le := duhamelI_mart_Ugen (g := sz.lam n) hLn hE σ u K hK1 hw0 hw1 hu_nn hu_w hmono Mt Bf hB a
  have hBb : ∀ b : Fin 2 → Zd d (sz.L n), Bf b ≤
      (Λ * (Λ * ρ * (2 / c₀ + 1) * a₄)) * STprof sz n w DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1) +
        Λ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm)) := by
    intro b
    set Pb := STprof sz n w DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1) with hPb
    have hPb0 : 0 ≤ Pb := (ST_STprof_pos sz n _ _ _ _ _).le
    have hterm' : ∀ j ∈ Finset.range K, Δ * Q j b ≤ Δ * ((2 * Λ * a₄ ^ 2 * Pb ^ 2) * (etaT E (u j))⁻¹) := by
      intro j hj
      have hjK := (Finset.mem_range.1 hj).le
      refine mul_le_mul_of_nonneg_left ?_ hΔ
      have hη0 : 0 ≤ (etaT E (u j))⁻¹ := inv_nonneg.2 (hη j hjK).le
      have hpj : STprof sz n (u j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1) ≤ Pb :=
        duhamelI_prof_mono sz n hlam.le (hu_w j hjK) hw1 _ _
      have hpj0 := (ST_STprof_pos sz n (u j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1)).le
      refine (hQ j hjK b).trans ?_
      rw [ha₂]
      calc 2 * (Λ * (a₄ ^ 2 * (etaT E (u j))⁻¹ * STprof sz n (u j) DE ((sz.L n : ℕ) : ℝ) (b 0) (b 1) ^ 2))
          ≤ 2 * (Λ * (a₄ ^ 2 * (etaT E (u j))⁻¹ * Pb ^ 2)) := by gcongr
        _ = _ := by ring
    have hQV : ∑ j ∈ Finset.range K, Δ * Q j b ≤ (2 * Λ * ρ / c₀) * (a₄ * Pb) ^ 2 := by
      refine (Finset.sum_le_sum hterm').trans ?_
      calc ∑ j ∈ Finset.range K, Δ * ((2 * Λ * a₄ ^ 2 * Pb ^ 2) * (etaT E (u j))⁻¹)
          = (2 * Λ * a₄ ^ 2 * Pb ^ 2) * ∑ j ∈ Finset.range K, Δ * (etaT E (u j))⁻¹ := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ ≤ (2 * Λ * a₄ ^ 2 * Pb ^ 2) * (ρ / c₀) := mul_le_mul_of_nonneg_left hriem' (by positivity)
        _ = (2 * Λ * ρ / c₀) * (a₄ * Pb) ^ 2 := by ring
    have hS0 : 0 ≤ ∑ j ∈ Finset.range K, Δ * Q j b := Finset.sum_nonneg fun j _ => mul_nonneg hΔ (hQ0 _ _)
    have hsq := duhamelI_sqrt_aux hΛ hρ1 hc₀
    calc Bf b = Λ * Real.sqrt (∑ j ∈ Finset.range K, Δ * Q j b + ((sz.size n : ℕ) : ℝ) ^ (-Dm)) := rfl
      _ ≤ Λ * (Real.sqrt (∑ j ∈ Finset.range K, Δ * Q j b) + Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm))) :=
          mul_le_mul_of_nonneg_left (duhamelI_sqrt_add hS0 hN0) (by linarith)
      _ ≤ Λ * (Real.sqrt ((2 * Λ * ρ / c₀) * (a₄ * Pb) ^ 2) + Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm))) := by
          gcongr
      _ = Λ * (Real.sqrt (2 * Λ * ρ / c₀) * (a₄ * Pb) + Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm))) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      _ ≤ Λ * ((Λ * ρ * (2 / c₀ + 1)) * (a₄ * Pb) + Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm))) := by
          gcongr
      _ = _ := by ring
  -- `Φ` of the bound
  set Tk : Zd d (sz.L n) → Zd d (sz.L n) → ℝ := fun x y => ‖Theta d (sz.L n) (sz.lam n) (w : ℂ) x y‖ with hTk
  have hTk0 : ∀ x y, 0 ≤ Tk x y := fun x y => norm_nonneg _
  have hh0 : 2 * (1 - u 0) = ρ * (2 * (1 - w)) := by rw [hu0, hρe]; ring
  have hΦ1 := duhamelI_Phi_mono (T := Tk) (h := 2 * (1 - u 0))
    (q := fun x y => Bf ![x, y])
    (q' := fun x y => (Λ * (Λ * ρ * (2 / c₀ + 1) * a₄)) * STprof sz n w DE ((sz.L n : ℕ) : ℝ) x y +
      (Λ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm))) * 1) hTk0
    (by rw [hu0]; linarith) (fun x y => by simpa using hBb ![x, y]) a
  rw [duhamelI_Phi_lin] at hΦ1
  have hΦp : duhamelI_Phi Tk (2 * (1 - u 0)) (fun x y => STprof sz n w DE ((sz.L n : ℕ) : ℝ) x y) a ≤
      ρ ^ 2 * (C * (Wd * (T + WmE))) := by
    rw [hh0]
    refine (duhamelI_Phi_scale hTk0 (fun x y => (ST_STprof_pos sz n _ _ _ _ _).le) (by linarith) hρ1 a).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg ρ)
    have := hΦ DE w w hsw.le le_rfl le_rfl a
    rw [div_self h1w.ne'] at this
    simpa using this
  have hΦo : duhamelI_Phi Tk (2 * (1 - u 0)) (fun _ _ => 1) a ≤ ρ ^ 2 * 9 := by
    rw [hh0]
    refine (duhamelI_Phi_scale hTk0 (fun _ _ => zero_le_one) (by linarith) hρ1 a).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg ρ)
    have hrow : ∀ x : Zd d (sz.L n), ∑ y, Tk x y ≤ (1 - w)⁻¹ := fun x => by
      simpa using sum_norm_Theta_row_le (g := sz.lam n) hLn hw0.le hw1 (m := (1 : ℂ)) (by simp) x
    refine (duhamelI_Phi_one hTk0 (by linarith) hrow a).trans (le_of_eq ?_)
    field_simp
    ring
  have hc1 : 0 ≤ Λ * (Λ * ρ * (2 / c₀ + 1) * a₄) := by positivity
  have hc2 : 0 ≤ Λ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm)) := by positivity
  refine hMr_le.trans ?_
  refine mul_le_mul_of_nonneg_left (hΦ1.trans ?_) (by norm_num)
  calc _ ≤ (Λ * (Λ * ρ * (2 / c₀ + 1) * a₄)) * (ρ ^ 2 * (C * (Wd * (T + WmE)))) +
        (Λ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm))) * (ρ ^ 2 * 9) :=
        add_le_add (mul_le_mul_of_nonneg_left hΦp hc1) (mul_le_mul_of_nonneg_left hΦo hc2)
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
-- the pathwise bound combines the drift, martingale, initial and floor estimates: 200000 is not enough
/-- **The pathwise bound at one size index** (the deterministic core of `(iois-mtx)`..`(iois-mtx2)`, `3_5:2046-2069`).
On a sample `ω` of the grid walk of `[s, tt]` at which the decomposition of `STGridMartAt`, the initial term, the three error
terms at every grid time and the martingale tail hold, `(𝓛-𝒦)^{(2)}_{tt,σ,a}` is at most
`Λ F + Λ² κ ρ³ A^{-1/4} W^{-d}𝒯̃^L_{tt,D} + W^{-D}`, `ρ = (1-s)/(1-tt)`, `κ = 4C/c₀ + 8C(2/c₀+1)`.  The grid Duhamel form is
`pfStep5Grid_duhamel`; the drift and the martingale term are `duhamelI_drift`, `duhamelI_mart`. -/
theorem duhamelI_path (sz : Sizes d) (n : ℕ) (E s tt : ℕ → ℝ) (K : ℕ → ℕ) (ω : PathΩ sz)
    (Mart Rem : STLab sz n → ℕ → PathΩ sz → ℂ) {Λ D DE Dm M R C c₀ : ℝ} (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) {Fv : ℝ}
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
    (hini : ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ (s n) (tt n)
        (fun b => STgA sz s tt K n (E n) σ b 0 ω) a‖ ≤ Λ * Fv)
    (hfloor : 36 * ((1 - s n) / (1 - tt n)) ^ 2 * (Λ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-Dm))) +
        64 * ((1 - tt n)⁻¹) ^ 7 * (R + gridStep s tt K n * M) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D))
    (hρA : (1 - s n) / (1 - tt n) ≤ (2 * STAI sz n) ^ (1 / 100 : ℝ))
    (hFv : 0 ≤ Fv) {Nτ : ℝ} (hNτ : (2 * (4 * C / c₀ + 8 * C * (2 / c₀ + 1)) + 1) * Λ ^ 2 ≤ Nτ) :
    ‖STgA sz s tt K n (E n) σ a (K n) ω‖ ≤ Nτ * (Fv + STAI sz n ^ (-(1 / 5) : ℝ) *
          STprof sz n (tt n) D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) + ((sz.W n : ℕ) : ℝ) ^ (-D)) := by
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
  have hsplit : ‖STgA sz s tt K n (E n) σ a (K n) ω‖ ≤
      ‖Iv‖ + ‖Dr‖ + ‖Mr‖ + 64 * ((1 - tt n)⁻¹) ^ 7 * (R + Δ * M) := by
    set X := STgA sz s tt K n (E n) σ a (K n) ω with hX
    have e : X = (X - Iv - Dr - Mr) + Iv + Dr + Mr := by ring
    have h1 := norm_add_le (X - Iv - Dr - Mr + Iv + Dr) Mr
    have h2 := norm_add_le (X - Iv - Dr - Mr + Iv) Dr
    have h3 := norm_add_le (X - Iv - Dr - Mr) Iv
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
  have hIv_le : ‖Iv‖ ≤ Λ * Fv := hini
  have hP0 : 0 ≤ P := (ST_STprof_pos sz n _ _ _ _ _).le
  clear hELK hEGt hEEk hMart hMart' hid hRem hM hini hF hdu
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
  refine le_trans (by linarith) (duhamelI_absorb hΛ (by positivity) hFv hP0 hWmD0 hA hρ1 hρA hNτ)

end Path


/-! ## 6. Numerical facts of the flow and of the choice of constants -/

section Numerics
variable {d : ℕ}

/-- `√κ/2 ≤ Im m(E)` for `|E| ≤ 2 - κ/2`, `0 < κ`. -/
theorem duhamelI_imag {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ / 2) : Real.sqrt κ / 2 ≤ (mE E).im := by
  rw [mE_im]
  refine div_le_div_of_nonneg_right (Real.sqrt_le_sqrt ?_) (by norm_num)
  have h0 := abs_nonneg E
  have hsq : E ^ 2 ≤ (2 - κ / 2) ^ 2 := by
    rw [← sq_abs E]; exact pow_le_pow_left₀ h0 hE 2
  nlinarith

/-- `(1-t)⁻¹ ≤ N` in the window (`1 - t ≥ ilambda²/L^d`, `ilambda² W^d ≥ 1`); `etermsMid_htN`, private there. -/
theorem duhamelI_htN (sz : Sizes d) (n : ℕ) {t : ℝ} (hl : 0 < sz.lam n) (hA : 1 ≤ STAI sz n)
    (hRegt : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t) : (1 - t)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    have := sz.three_le_L n
    exact_mod_cast (by omega : 0 < sz.L n)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := pow_pos hL d
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
  have hg2 : 0 < sz.lam n ^ 2 := by positivity
  have hsz : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    unfold Sizes.size; push_cast; ring
  have h1 : (1 - t)⁻¹ ≤ (sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d)⁻¹ := inv_anti₀ (div_pos hg2 hLd) hRegt
  refine h1.trans ?_
  rw [inv_div, hsz]
  have hA' : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d := hA
  rw [div_le_iff₀ hg2]
  nlinarith [mul_pos hWd hLd]

/-- `ρ = (1-s)/(1-tt) ≤ (2A)^{1/100}` from `(con_st_ind)` at the end time `t ≥ tt` and `W^{-d}B_{t,0} ≥ (2A)⁻¹`. -/
theorem duhamelI_rho (sz : Sizes d) (n : ℕ) {s tt t : ℝ} (hl : 0 < sz.lam n) (hs : s ≤ tt) (htt : tt ≤ t)
    (ht1 : t < 1) (hx : 1 - t ≤ sz.lam n ^ 2) (hcon : (sz.Bctl n t) ^ (1 / 100 : ℝ) ≤ (1 - t) / (1 - s)) :
    (1 - s) / (1 - tt) ≤ (2 * STAI sz n) ^ (1 / 100 : ℝ) := by
  have h1t : 0 < 1 - t := by linarith
  have h1s : 0 < 1 - s := by linarith
  have h1tt : 0 < 1 - tt := by linarith
  have hB := st5_Bctl_ge sz n hl ht1 hx
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hA0 : 0 < 2 * STAI sz n := by unfold STAI; positivity
  have h2 : ((2 * STAI sz n)⁻¹) ^ (1 / 100 : ℝ) ≤ (sz.Bctl n t) ^ (1 / 100 : ℝ) :=
    Real.rpow_le_rpow (inv_nonneg.2 hA0.le) hB (by norm_num)
  have h3 : ((2 * STAI sz n)⁻¹) ^ (1 / 100 : ℝ) = ((2 * STAI sz n) ^ (1 / 100 : ℝ))⁻¹ := Real.inv_rpow hA0.le _
  have h4 : ((2 * STAI sz n) ^ (1 / 100 : ℝ))⁻¹ ≤ (1 - t) / (1 - s) := by rw [← h3]; exact h2.trans hcon
  have h5 : (1 - s) / (1 - t) ≤ (2 * STAI sz n) ^ (1 / 100 : ℝ) := by
    have hp : 0 < (2 * STAI sz n) ^ (1 / 100 : ℝ) := Real.rpow_pos_of_pos hA0 _
    rw [div_le_iff₀ h1t]
    rw [inv_le_iff_one_le_mul₀ hp, div_mul_eq_mul_div, le_div_iff₀ h1s] at h4
    nlinarith
  exact (div_le_div_of_nonneg_left h1s.le h1t (by linarith)).trans h5

/-- The a priori bound: `‖(𝓛-𝒦)^{(2)}_{u,σ,a}(H)‖ ≤ (N/c₀)² + N` for Hermitian `H`, `0 ≤ u ≤ tt < 1`, `(1-tt)⁻¹ ≤ N`, `c₀ ≤ Im m`. -/
theorem duhamelI_apriori (sz : Sizes d) (n : ℕ) {E u tt c₀ : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hut : u ≤ tt)
    (htt : tt < 1) (hN : (1 - tt)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) (hc₀ : 0 < c₀) (hc : c₀ ≤ (mE E).im)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ‖STLKM sz n E u H σ a‖ ≤ (((sz.size n : ℕ) : ℝ) / c₀) ^ 2 + ((sz.size n : ℕ) : ℝ) := by
  have hu1 : u < 1 := hut.trans_lt htt
  have h1 := RBM.Ind.norm_loopFine_crudeN sz n hE hH hu1 (by norm_num : 1 ≤ 2) σ a
  have hη : (etaT E u)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) / c₀ := by
    have h1t : 0 < 1 - tt := by linarith
    have hη0 : 0 < etaT E u := etaT_pos hE hu1
    rw [inv_le_iff_one_le_mul₀ hη0]
    have hη1 : (1 - tt) * c₀ ≤ etaT E u := by
      unfold etaT; exact mul_le_mul (by linarith) hc hc₀.le (by linarith)
    have h2 : 1 ≤ ((sz.size n : ℕ) : ℝ) * (1 - tt) := by
      rw [inv_le_iff_one_le_mul₀ h1t] at hN; exact hN
    have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
    calc 1 ≤ ((sz.size n : ℕ) : ℝ) * (1 - tt) := h2
      _ = (((sz.size n : ℕ) : ℝ) / c₀) * ((1 - tt) * c₀) := by field_simp
      _ ≤ (((sz.size n : ℕ) : ℝ) / c₀) * etaT E u := mul_le_mul_of_nonneg_left hη1 (by positivity)
  have h2 : ‖STKloop sz n E u σ a‖ ≤ ((sz.size n : ℕ) : ℝ) :=
    LemDecCalELip_STKloop_two_norm sz n hE.le htt hu0 hut hN σ a
  unfold STLKM STLM
  calc _ ≤ ‖loopFine d (sz.L n) (sz.W n) H (zt E u) σ a‖ + ‖STKloop sz n E u σ a‖ := norm_sub_le _ _
    _ ≤ (((sz.size n : ℕ) : ℝ) / c₀) ^ 2 + ((sz.size n : ℕ) : ℝ) :=
        add_le_add (h1.trans (pow_le_pow_left₀ (inv_nonneg.2 (etaT_pos hE hu1).le) hη 2)) h2


theorem duhamelI_rp {N e D : ℝ} {k : ℕ} (hN : 256 ≤ N) (he : e + D ≤ -(k : ℝ)) :
    N ^ e ≤ N ^ (-D) * (N⁻¹) ^ k := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have h1 : N ^ e = N ^ (-D) * N ^ (e + D) := by rw [← Real.rpow_add hN0]; congr 1; ring
  have h2 : N ^ (e + D) ≤ N ^ (-(k : ℝ)) := Real.rpow_le_rpow_of_exponent_le hN1 he
  have h3 : N ^ (-(k : ℝ)) = (N⁻¹) ^ k := by
    rw [Real.rpow_neg hN0.le, Real.rpow_natCast, inv_pow]
  rw [h1]
  exact mul_le_mul_of_nonneg_left (h2.trans_eq h3) (Real.rpow_nonneg hN0.le _)

/-- The floor `36ρ²Λ N^{-D_m/2} + 64(1-tt)^{-7}(N^{C₀}√Δ + ΔM) ≤ W^{-D}`. -/
theorem duhamelI_floor {N ρ Ti Δ Wm C₀ c₀ D τ Dm x : ℝ} (hN : 256 ≤ N) (hc₀ : c₀⁻¹ ^ 2 ≤ N)
    (hτ : 0 < τ) (hD : 0 < D) (hC₀ : 0 ≤ C₀) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ N) (hTi0 : 0 ≤ Ti) (hTi : Ti ≤ N)
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ N ^ (-x)) (hWm : N ^ (-D) ≤ Wm) (hDm : 2 * (D + 6 + τ) ≤ Dm)
    (hx : 2 * (C₀ + D + 12) ≤ x) :
    36 * ρ ^ 2 * (N ^ (τ / 4) * Real.sqrt (N ^ (-Dm))) +
      64 * Ti ^ 7 * (N ^ C₀ * Real.sqrt Δ + Δ * ((N / c₀) ^ 2 + N)) ≤ Wm := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hq0 : 0 ≤ N ^ (-D) := Real.rpow_nonneg hN0.le _
  have hsq : ∀ y : ℝ, Real.sqrt (N ^ y) = N ^ (y / 2) := fun y => by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]; congr 1; ring
  -- term 1
  have t1 : 36 * ρ ^ 2 * (N ^ (τ / 4) * Real.sqrt (N ^ (-Dm))) ≤ N ^ (-D) * (36 * (N⁻¹) ^ 4) := by
    have e1 : N ^ (τ / 4) * Real.sqrt (N ^ (-Dm)) = N ^ (τ / 4 + -Dm / 2) := by
      rw [hsq, ← Real.rpow_add hN0]
    have e2 : ρ ^ 2 ≤ N ^ (2 : ℝ) := by
      rw [Real.rpow_two]; exact pow_le_pow_left₀ hρ0 hρ 2
    have e3 : N ^ (2 : ℝ) * N ^ (τ / 4 + -Dm / 2) = N ^ (2 + (τ / 4 + -Dm / 2)) := (Real.rpow_add hN0 _ _).symm
    have e4 := duhamelI_rp (k := 4) hN (e := 2 + (τ / 4 + -Dm / 2)) (D := D) (by push_cast; linarith)
    rw [e1]
    calc 36 * ρ ^ 2 * N ^ (τ / 4 + -Dm / 2) ≤ 36 * N ^ (2 : ℝ) * N ^ (τ / 4 + -Dm / 2) := by
          gcongr
      _ = 36 * N ^ (2 + (τ / 4 + -Dm / 2)) := by rw [mul_assoc, e3]
      _ ≤ 36 * (N ^ (-D) * (N⁻¹) ^ 4) := mul_le_mul_of_nonneg_left e4 (by norm_num)
      _ = _ := by ring
  -- term 2
  have hTi7 : Ti ^ 7 ≤ N ^ (7 : ℝ) := by
    have := Real.rpow_natCast N 7
    simp only [Nat.cast_ofNat] at this
    rw [this]; exact pow_le_pow_left₀ hTi0 hTi 7
  have hsΔ : Real.sqrt Δ ≤ N ^ (-x / 2) := by
    exact (Real.sqrt_le_sqrt hΔ).trans (le_of_eq (hsq (-x)))
  have t2 : 64 * Ti ^ 7 * (N ^ C₀ * Real.sqrt Δ) ≤ N ^ (-D) * (64 * (N⁻¹) ^ 5) := by
    have e1 : N ^ (7 : ℝ) * (N ^ C₀ * N ^ (-x / 2)) = N ^ (7 + (C₀ + -x / 2)) := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
    have e4 := duhamelI_rp (k := 5) hN (e := 7 + (C₀ + -x / 2)) (D := D) (by push_cast; linarith)
    calc 64 * Ti ^ 7 * (N ^ C₀ * Real.sqrt Δ) ≤ 64 * N ^ (7 : ℝ) * (N ^ C₀ * N ^ (-x / 2)) := by
          gcongr
      _ = 64 * N ^ (7 + (C₀ + -x / 2)) := by rw [mul_assoc, e1]
      _ ≤ 64 * (N ^ (-D) * (N⁻¹) ^ 5) := mul_le_mul_of_nonneg_left e4 (by norm_num)
      _ = _ := by ring
  have t3 : 64 * Ti ^ 7 * (Δ * ((N / c₀) ^ 2 + N)) ≤ N ^ (-D) * (128 * (N⁻¹) ^ 14) := by
    have hM : (N / c₀) ^ 2 + N ≤ 2 * N ^ (3 : ℝ) := by
      have : (N / c₀) ^ 2 = N ^ 2 * c₀⁻¹ ^ 2 := by rw [div_eq_mul_inv, mul_pow]
      rw [this, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have h1 : N ^ 2 * c₀⁻¹ ^ 2 ≤ N ^ 2 * N := mul_le_mul_of_nonneg_left hc₀ (by positivity)
      nlinarith [pow_le_pow_right₀ hN1 (by norm_num : 1 ≤ 3), pow_le_pow_right₀ hN1 (by norm_num : 2 ≤ 3)]
    have e1 : N ^ (7 : ℝ) * (N ^ (-x) * N ^ (3 : ℝ)) = N ^ (7 + (-x + 3)) := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
    have e4 := duhamelI_rp (k := 14) hN (e := 7 + (-x + 3)) (D := D) (by push_cast; linarith)
    calc 64 * Ti ^ 7 * (Δ * ((N / c₀) ^ 2 + N)) ≤ 64 * N ^ (7 : ℝ) * (N ^ (-x) * (2 * N ^ (3 : ℝ))) := by
          gcongr
      _ = 128 * N ^ (7 + (-x + 3)) := by rw [← e1]; ring
      _ ≤ 128 * (N ^ (-D) * (N⁻¹) ^ 14) := mul_le_mul_of_nonneg_left e4 (by norm_num)
      _ = _ := by ring
  have hNi : N⁻¹ ≤ 1 / 256 := by rw [one_div]; exact inv_anti₀ (by norm_num) hN
  have hNi0 : 0 ≤ N⁻¹ := inv_nonneg.2 hN0.le
  have h4 : (N⁻¹) ^ 4 ≤ (1 / 256) ^ 4 := pow_le_pow_left₀ hNi0 hNi 4
  have h5 : (N⁻¹) ^ 5 ≤ (1 / 256) ^ 5 := pow_le_pow_left₀ hNi0 hNi 5
  have h14 : (N⁻¹) ^ 14 ≤ (1 / 256) ^ 14 := pow_le_pow_left₀ hNi0 hNi 14
  have hsum : 36 * (N⁻¹) ^ 4 + 64 * (N⁻¹) ^ 5 + 128 * (N⁻¹) ^ 14 ≤ 1 := by
    have : (36 : ℝ) * (1 / 256) ^ 4 + 64 * (1 / 256) ^ 5 + 128 * (1 / 256) ^ 14 ≤ 1 := by norm_num
    nlinarith
  calc _ ≤ N ^ (-D) * (36 * (N⁻¹) ^ 4) + N ^ (-D) * (64 * (N⁻¹) ^ 5) + N ^ (-D) * (128 * (N⁻¹) ^ 14) := by
        rw [mul_add]; linarith
    _ = N ^ (-D) * (36 * (N⁻¹) ^ 4 + 64 * (N⁻¹) ^ 5 + 128 * (N⁻¹) ^ 14) := by ring
    _ ≤ N ^ (-D) * 1 := mul_le_mul_of_nonneg_left hsum hq0
    _ ≤ Wm := by linarith

end Numerics


/-! ## 7. The per-section statement (the grid events and the pathwise bound) -/

section Prob

variable {d : ℕ}

/-- The label set `{σ // P σ} × (Z_L^d)²` has at most `N³` elements (`N ≥ 4`). -/
theorem duhamelI_card_le (sz : Sizes d) (P : (Fin 2 → Bool) → Prop)
    [∀ n, Fintype ({σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n)))] (n : ℕ) (hn : 4 ≤ sz.size n) :
    (Fintype.card ({σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n))) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) := by
  have h1 : Fintype.card ({σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n))) ≤ Fintype.card (sz.STLab n) :=
    Fintype.card_le_of_injective (fun v => ((v.1.1, v.2) : sz.STLab n)) (fun v w h => by
      have := Prod.mk.inj h
      exact Prod.ext (Subtype.ext this.1) this.2)
  exact (Nat.cast_le.2 h1).trans (ST_card_lab_le sz n hn)

/-- `W ≤ N = (W L)^d` (`d ≥ 1`). -/
theorem duhamelI_W_le_size (sz : Sizes d) (hd : d ≠ 0) (n : ℕ) : ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  exact (le_self_pow₀ hW1 hd).trans (ST_Wpow_le_size sz n)

/-- measurability of `‖STELKLKM‖` in the matrix -/
private theorem duhamelI_ELKLK_meas (sz : Sizes d) (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => STELKLKM sz n E u H σ a := by
  unfold STELKLKM
  refine measurable_const.mul (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ => ?_)
  exact ((STLKM_measurable sz n E u _ _).mul measurable_const).mul (STLKM_measurable sz n E u _ _)

/-- the grid events at the sections of `[s, tt]` from a per-section `≺` on `[s, t]` -/
private theorem duhamelI_whp_sec {V : ℕ → Type} [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)] (sz : Sizes d) {s t : ℕ → ℝ}
    (tt : ∀ n, TimeIcc s t n) (K : ℕ → ℕ) (hs : ∀ n, 0 ≤ s n) (hKne : ∀ n, K n ≠ 0) {C : ℝ} (hC0 : 0 ≤ C)
    (hcard : ∀ᶠ n in atTop, (((K n + 1) * Fintype.card (V n) : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C)
    (F Z : ∀ n, V n → ℝ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℝ)
    (hF : ∀ n v u, Measurable (F n v u)) (hZ : ∀ n v u, Measurable (Z n v u)) {τ : ℝ} (hτ : 0 < τ)
    (h : sz.Prec (U := fun n => TimeIcc s t n × V n) (fun n p ω => F n p.2 (p.1 : ℝ) (sz.seqHflow n (p.1 : ℝ) ω))
      (fun n p ω => Z n p.2 (p.1 : ℝ) (sz.seqHflow n (p.1 : ℝ) ω))) :
    HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ j ∈ Finset.range (K n + 1), ∀ v : V n,
      F n v (gridTime s (fun m => (tt m : ℝ)) K n j) (pathH sz s (fun m => (tt m : ℝ)) K n j ω) ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * Z n v (gridTime s (fun m => (tt m : ℝ)) K n j)
          (pathH sz s (fun m => (tt m : ℝ)) K n j ω)}) := by
  refine ST_grid_whp_of_sections sz s (fun m => (tt m : ℝ)) K hs (fun n => (tt n).2.1) hKne hC0 hcard F Z hF hZ τ hτ
    fun tt' => ?_
  exact StochDomAt.precomp_param h (fun n v => (⟨(tt' n : ℝ), (tt' n).2.1, (tt' n).2.2.trans (tt n).2.2⟩, v))


private theorem duhamelI_Ugen_meas (sz : Sizes d) (n : ℕ) (E u v w : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ v w (fun b => STLKM sz n E u H σ b) a‖ := by
  unfold RBM.Ind.Ugen UN
  exact (Finset.measurable_sum _ fun b _ => measurable_const.mul (STLKM_measurable sz n E u σ b)).norm

private theorem duhamelI_cardK (N m c : ℕ) (hN : 4 ≤ N) (hc : (c : ℝ) ≤ 2 * (N : ℝ) ^ (3 : ℝ)) :
    (((N ^ m + 1) * c : ℕ) : ℝ) ≤ (N : ℝ) ^ (((m + 5 : ℕ) : ℝ)) := by
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have h3 : (N : ℝ) ^ (3 : ℝ) = (N : ℝ) ^ 3 := by simp
  have h5 : (N : ℝ) ^ (((m + 5 : ℕ) : ℝ)) = (N : ℝ) ^ m * (N : ℝ) ^ 5 := by
    rw [Real.rpow_natCast, pow_add]
  rw [h3] at hc
  rw [h5]; push_cast
  have hm1 : (1 : ℝ) ≤ (N : ℝ) ^ m := one_le_pow₀ (by linarith)
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  calc ((N : ℝ) ^ m + 1) * c ≤ (2 * (N : ℝ) ^ m) * (2 * (N : ℝ) ^ 3) :=
        mul_le_mul (by linarith) hc hc0 (by positivity)
    _ = 4 * (N : ℝ) ^ m * (N : ℝ) ^ 3 := by ring
    _ ≤ (N : ℝ) ^ m * (N : ℝ) ^ 5 := by
        have h2 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
        have : 4 * (N : ℝ) ^ 3 ≤ (N : ℝ) ^ 5 := by
          calc 4 * (N : ℝ) ^ 3 ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ 3 := mul_le_mul_of_nonneg_right h2 (by positivity)
            _ = (N : ℝ) ^ 5 := by ring
        nlinarith [pow_pos hN0 m]

private theorem duhamelI_measure_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {A B G S : Set Ω} {N a : ℝ}
    (hN : 3 ≤ N) (hS : S ⊆ Aᶜ ∪ B ∪ Gᶜ) (hA : μ Aᶜ ≤ ENNReal.ofReal (N ^ (-(a + 1))))
    (hB : μ B ≤ ENNReal.ofReal (N ^ (-(a + 1)))) (hG : μ Gᶜ = 0) : μ S ≤ ENNReal.ofReal (N ^ (-a)) := by
  have hN0 : 0 < N := by linarith
  have hp : (0 : ℝ) ≤ N ^ (-(a + 1)) := Real.rpow_nonneg hN0.le _
  calc μ S ≤ μ (Aᶜ ∪ B ∪ Gᶜ) := measure_mono hS
    _ ≤ μ (Aᶜ ∪ B) + μ Gᶜ := measure_union_le _ _
    _ ≤ (μ Aᶜ + μ B) + μ Gᶜ := add_le_add (measure_union_le _ _) le_rfl
    _ ≤ (ENNReal.ofReal (N ^ (-(a + 1))) + ENNReal.ofReal (N ^ (-(a + 1)))) + 0 := by
        rw [hG]; exact add_le_add (add_le_add hA hB) le_rfl
    _ = ENNReal.ofReal (2 * N ^ (-(a + 1))) := by
        rw [add_zero, ← ENNReal.ofReal_add hp hp]; ring_nf
    _ ≤ ENNReal.ofReal (N ^ (-a)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : N ^ (-(a + 1)) = N ^ (-a) * N⁻¹ := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hN0]; congr 1; ring
        rw [this]
        have h2 : 0 ≤ N ^ (-a) := Real.rpow_nonneg hN0.le _
        have h3 : 2 * N⁻¹ ≤ 1 := by rw [← div_eq_mul_inv, div_le_one hN0]; linarith
        nlinarith

set_option maxHeartbeats 1000000 in
-- the six grid events and the pathwise case analysis elaborate a long `have` list: 200000 is not enough
/-- **The per-section statement**: at a section `tt n ∈ [s_n, t_n]` the family `‖(𝓛-𝒦)^{(2)}_{tt,σ,a}‖` is dominated by
`F + A^{-1/5} W^{-d}𝒯̃^L_{tt,D} + W^{-D}` on the model, given the initial term `≺ F`, `STEtermsMidConcl` and `(con_st_ind)`.
The grid has `K_n = N^m` steps; the six events (initial term, three error terms, martingale tails, identities) are at the
grid times, the section being the last grid time of `[s, tt]` (`ST_pathP_eq_seqP`). -/
private theorem duhamelI_section (hd : 3 ≤ d) {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (sz : Sizes d)
    {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (htz : ∀ n, t n ≤ lemT (z n)) (hReg : STReg5Mid sz s t)
    (hTTT : ∀ n, sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t n ∨ 1 - s n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hCon : STConStInd sz (1 / 100) s t) (hE : STEtermsMidConcl sz (STflowE z) s t)
    {D : ℝ} (hD : 0 < D) (P : (Fin 2 → Bool) → Prop) (F : ∀ n, STIdx2P sz P s t n → ℝ)
    (hF0 : ∀ n p, 0 ≤ F n p)
    (hini : sz.Prec (U := STIdx2P sz P s t) (fun n p ω => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) p.2.1.1
      (s n) (p.1 : ℝ) (fun b => STLKM sz n (STflowE z n) (s n) (sz.seqHflow n (s n) ω) p.2.1.1 b) p.2.2‖) (fun n p _ => F n p))
    (tt : ∀ n, TimeIcc s t n) :
    sz.Prec (U := fun n => {σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n)))
      (fun n v ω => ‖STLKM sz n (STflowE z n) (tt n : ℝ) (sz.seqHflow n (tt n : ℝ) ω) v.1.1 v.2‖)
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
  set c₀ : ℝ := Real.sqrt κ / 2 with hc₀def
  have hc₀ : 0 < c₀ := by positivity
  set κs : ℝ := 4 * C / c₀ + 8 * C * (2 / c₀ + 1) with hκs
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
    (fun n v u H => ‖RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) v.1.1 (s n) (tt n : ℝ)
      (fun b => STLKM sz n (STflowE z n) u H v.1.1 b) v.2‖) (fun n v u H => F n (tt n, v))
    (fun n v u => duhamelI_Ugen_meas sz n _ u _ _ _ v.2) (fun n v u => measurable_const) τ₁ hτ₁0
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
  have hNτ : ∀ᶠ n in atTop, 2 * κs + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
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
  have hρA := duhamelI_rho sz n hlam (tt n).2.1 (tt n).2.2 (ht1 n) (by linarith [(hReg n).2, (hst n)]) hCon1.1
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
  have hNτ' : (2 * (4 * C / c₀ + 8 * C * (2 / c₀ + 1)) + 1) * (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 ≤
      ((sz.size n : ℕ) : ℝ) ^ τ := by
    have e1 : (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 = ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; congr 1; rw [hτ₁]; push_cast; ring
    have e2 : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) = ((sz.size n : ℕ) : ℝ) ^ τ := by
      rw [← Real.rpow_add (by linarith)]; congr 1; ring
    rw [e1, ← e2]
    exact mul_le_mul_of_nonneg_right hNτn (Real.rpow_nonneg (by linarith) _)
  have hΦn : ∀ (D'' v w : ℝ), s n ≤ v → v ≤ w → w ≤ (tt n : ℝ) → ∀ a : Fin 2 → Zd d (sz.L n),
      duhamelI_Phi (fun x y => ‖Theta d (sz.L n) (sz.lam n) (w : ℂ) x y‖) (2 * (1 - v))
          (fun x y => STprof sz n v D'' ((sz.L n : ℕ) : ℝ) x y) a ≤
        C * ((1 - v) / (1 - w)) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
          (tailT d (sz.L n) (sz.lam n) w ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) +
            (1 - v) / (1 - w) * ((sz.W n : ℕ) : ℝ) ^ (-D''))) := by
    intro D'' v w hv hvw hw a
    refine hΦC sz n D'' v w hlam hlamle ((hs n).trans hv) hvw (hw.trans_lt htt1) ?_ a
    exact (hTTT n).imp (fun h => h.trans (by linarith [(tt n).2.2])) (fun h => by linarith)
  -- the bad event at the section, as a measurable set of matrices
  set ζ : ({σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n))) → ℝ := fun v => F n (tt n, v) +
    STAI sz n ^ (-(1 / 5) : ℝ) * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (v.2 0) (v.2 1) +
      ((sz.W n : ℕ) : ℝ) ^ (-D) with hζ
  set Sset : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
    ⋃ v, {H | ((sz.size n : ℕ) : ℝ) ^ τ * ζ v < ‖STLKM sz n (STflowE z n) (tt n : ℝ) H v.1.1 v.2‖} with hSset
  have hSm : MeasurableSet Sset := MeasurableSet.iUnion fun v =>
    measurableSet_lt measurable_const (STLKM_measurable sz n _ _ _ _).norm
  have heq := ST_pathP_eq_seqP sz s (fun m => (tt m : ℝ)) K n (K n) (hs n) (tt n).2.1 (hKne n) hSm
  rw [gridTime_last s (fun m => (tt m : ℝ)) K n (hKne n)] at heq
  have hbad : badSetAt sz.size (fun n v ω => ‖STLKM sz n (STflowE z n) (tt n : ℝ) (sz.seqHflow n (tt n : ℝ) ω) v.1.1 v.2‖)
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
  have hv' : ((sz.size n : ℕ) : ℝ) ^ τ * ζ v < ‖STLKM sz n (STflowE z n) (tt n : ℝ)
      (pathH sz s (fun m => (tt m : ℝ)) K n (K n) ω) v.1.1 v.2‖ := hv
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
  have hmain := duhamelI_path sz n (STflowE z) s (fun m => (tt m : ℝ)) K ω (Mart n) (Rem n)
    (Λ := ((sz.size n : ℕ) : ℝ) ^ τ₁) (D := D) (DE := DE) (Dm := Dm)
    (M := (((sz.size n : ℕ) : ℝ) / c₀) ^ 2 + ((sz.size n : ℕ) : ℝ))
    (R := ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s (fun m => (tt m : ℝ)) K n)) (C := C) (c₀ := c₀)
    v.1.1 v.2 (Fv := F n (tt n, v)) (hs n) hsn htt1 (hKne n) hE2 hlam hΛ hA1 hc₀ hc hC.le hΦn hDEn
    (fun i k hk => (hGω i).1 k hk) (fun i k hk => (hGω i).2 k hk) hMa hMart'
    (fun j hj σ b => h2 j (Finset.mem_range.2 (Nat.lt_succ_of_le hj)) (σ, b))
    (fun j hj σ b => h3 j (Finset.mem_range.2 (Nat.lt_succ_of_le hj)) (σ, b))
    (fun j hj σ b k => h4 j (Finset.mem_range.2 (Nat.lt_succ_of_le hj)) ((σ, b), k))
    (h1 v) hfloor hρA (hF0 n _) hNτ'
  have hSTgA : STgA sz s (fun m => (tt m : ℝ)) K n (STflowE z n) v.1.1 v.2 (K n) ω =
      STLKM sz n (STflowE z n) (tt n : ℝ) (pathH sz s (fun m => (tt m : ℝ)) K n (K n) ω) v.1.1 v.2 := by
    unfold STgA; rw [gridTime_last s (fun m => (tt m : ℝ)) K n (hKne n)]
  rw [hSTgA] at hmain
  exact absurd hmain (not_le.2 hv')

end Prob

/-! ## 8. The net lift from the sections to `u ∈ [s,t]` -/

section Lift

open RBM.Ind.ContinuityNet

variable {d : ℕ}

/-- The union bound of `cont_stochDomAt_of_subset` (`RBM3D/Induction/ContinuityNet.lean:76`, private there), copied. -/
private theorem duhamelI_stoch_of_subset {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}
    (hsize : Tendsto size atTop atTop) {U V : ℕ → Type*}
    {ξ ζ : ∀ l, U l → Ω → ℝ} {ξ' ζ' : ∀ l, V l → Ω → ℝ} {Ξ : ℕ → Set Ω}
    (h : StochDomAt P size ξ' ζ') (hΞ : HighProbAt P size Ξ)
    (hsub : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop,
      badSetAt size ξ ζ τ l ∩ Ξ l ⊆ badSetAt size ξ' ζ' τ' l) :
    StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := hsub τ hτ
  filter_upwards [hs, h τ' hτ' (D + 1) (by linarith), hΞ (D + 1) (by linarith),
    hsize.eventually (eventually_two_mul_rpow_le D)] with l h0 h1 h2 h3
  have hp : (0 : ℝ) ≤ (size l : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hcover : badSetAt size ξ ζ τ l ⊆ (badSetAt size ξ ζ τ l ∩ Ξ l) ∪ (Ξ l)ᶜ := by
    intro ω hω
    by_cases hΞω : ω ∈ Ξ l
    · exact Or.inl ⟨hω, hΞω⟩
    · exact Or.inr hΞω
  calc P (badSetAt size ξ ζ τ l) ≤ P ((badSetAt size ξ ζ τ l ∩ Ξ l) ∪ (Ξ l)ᶜ) :=
        measure_mono hcover
    _ ≤ P (badSetAt size ξ ζ τ l ∩ Ξ l) + P (Ξ l)ᶜ := measure_union_le _ _
    _ ≤ P (badSetAt size ξ' ζ' τ' l) + P (Ξ l)ᶜ := add_le_add (measure_mono h0) le_rfl
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-(D + 1))) +
          ENNReal.ofReal ((size l : ℝ) ^ (-(D + 1))) := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * (size l : ℝ) ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add hp hp]; ring_nf
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal h3

/-- **The net lift with an arbitrary deterministic control** (`1_2:1400`): a per-time `≺` with the control `ζ ≥ N^{-C_R}`,
for a family that is Hölder-`1/2` on `contGood`, is uniform in `u ∈ [s,t]`.  The control is not assumed to vary slowly: at
every net cell and label the section is taken at a near-minimizer of `ζ` over the cell (`ζ(θ) ≤ ζ(u) + N^{-C_R} ≤ 2ζ(u)`). -/
theorem duhamelI_lift (sz : Sizes d) (hsz : sz.SizeTendsto) {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n)
    (hlen : ∀ n, t n - s n ≤ 1) {V : ℕ → Type} [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)] {Cv CR : ℝ}
    (hCv : 0 ≤ Cv) (hCR : 0 ≤ CR)
    (hcard : ∀ᶠ n in atTop, (Fintype.card (V n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ Cv)
    (ξ : ∀ n, TimeIcc s t n × V n → sz.SeqΩ → ℝ) (ζ : ∀ n, TimeIcc s t n × V n → ℝ) (hζ0 : ∀ n p, 0 ≤ ζ n p)
    (hPT : sz.PrecPT ξ (fun n p _ => ζ n p))
    (hlow : ∀ᶠ n in atTop, ∀ p, ((sz.size n : ℕ) : ℝ) ^ (-CR) ≤ ζ n p)
    (hH : ∃ CH : ℝ, 0 ≤ CH ∧ ∀ᶠ n in atTop, ∀ ω ∈ contGood sz n, ∀ (u u' : TimeIcc s t n) (v : V n),
      |ξ n (u, v) ω - ξ n (u', v) ω| ≤ ((sz.size n : ℕ) : ℝ) ^ CH * Real.sqrt |(u : ℝ) - (u' : ℝ)|) :
    sz.Prec ξ (fun n p _ => ζ n p) := by
  obtain ⟨CH, hCH0, hH'⟩ := hH
  have hsN := tendsto_size sz hsz
  set A : ℝ := 2 * (CH + CR) + 6 with hAdef
  have hA0 : 0 ≤ A := by linarith
  set M : ℕ → ℕ := fun n => netSize (A + 1) (sz.size n) with hM
  set cell : ∀ n, Fin (M n + 1) → ℝ := fun n k => min (t n) (s n + netPt 1 (A + 1) (sz.size n) k) with hcell
  have hcellmem : ∀ n k, cell n k ∈ Set.Icc (s n) (t n) := fun n k => by
    refine ⟨le_min (hst n) ?_, min_le_left _ _⟩
    have := (netPt_mem_Icc zero_le_one (A + 1) (sz.size n) k).1
    linarith
  have hexists : ∀ n (u : TimeIcc s t n), ∃ k : Fin (M n + 1), |(u : ℝ) - cell n k| ≤ 1 / (M n : ℝ) := by
    intro n u
    have hmem : (u : ℝ) - s n ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [u.2.1], by linarith [u.2.2, hlen n]⟩
    obtain ⟨k, hk⟩ := exists_netPt_close one_pos (A + 1) (sz.size n) hmem
    refine ⟨k, ?_⟩
    have hkq : |(u : ℝ) - (s n + netPt 1 (A + 1) (sz.size n) k)| ≤ 1 / (M n : ℝ) := by
      have h : (u : ℝ) - (s n + netPt 1 (A + 1) (sz.size n) k) = u - s n - netPt 1 (A + 1) (sz.size n) k := by ring
      rw [h]; exact hk
    simp only [hcell]
    rcases le_or_gt (s n + netPt 1 (A + 1) (sz.size n) k) (t n) with h | h
    · rwa [min_eq_right h]
    · rw [min_eq_left h.le]
      refine le_trans ?_ hkq
      rw [abs_of_nonpos (by linarith [u.2.2]), abs_of_nonpos (by linarith [u.2.2])]
      linarith
  have hθ : ∀ n (k : Fin (M n + 1)) (v : V n), ∃ θ : TimeIcc s t n, |(θ : ℝ) - cell n k| ≤ 1 / (M n : ℝ) ∧
      ∀ u : TimeIcc s t n, |(u : ℝ) - cell n k| ≤ 1 / (M n : ℝ) →
        ζ n (θ, v) ≤ ζ n (u, v) + ((sz.size n : ℕ) : ℝ) ^ (-CR) := by
    intro n k v
    have hMpos : (0 : ℝ) < (M n : ℝ) := by exact_mod_cast netSize_pos _ _
    let T : Set (TimeIcc s t n) := {u | |(u : ℝ) - cell n k| ≤ 1 / (M n : ℝ)}
    have hT : (⟨cell n k, hcellmem n k⟩ : TimeIcc s t n) ∈ T := by
      change |((cell n k : ℝ)) - cell n k| ≤ 1 / (M n : ℝ)
      rw [sub_self, abs_zero]; positivity
    have hε : 0 < ((sz.size n : ℕ) : ℝ) ^ (-CR) :=
      Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _
    obtain ⟨_, ⟨θ, hθT, rfl⟩, hlt⟩ := Real.lt_sInf_add_pos (s := (fun u => ζ n (u, v)) '' T)
      ⟨_, ⟨_, hT, rfl⟩⟩ hε
    refine ⟨θ, hθT, fun u hu => ?_⟩
    have : sInf ((fun u => ζ n (u, v)) '' T) ≤ ζ n (u, v) :=
      csInf_le ⟨0, by rintro _ ⟨w, -, rfl⟩; exact hζ0 n _⟩ ⟨u, hu, rfl⟩
    linarith
  choose θ hθ1 hθ2 using hθ
  have hA1 : (0 : ℝ) ≤ A + 1 := by linarith
  let ξ' : ∀ n, (Fin (M n + 1) × V n) → sz.SeqΩ → ℝ := fun n p ω => ξ n (θ n p.1 p.2, p.2) ω
  let ζ' : ∀ n, (Fin (M n + 1) × V n) → sz.SeqΩ → ℝ := fun n p _ => ζ n (θ n p.1 p.2, p.2)
  have hpt' : PerTimeDomAt (seqP sz) sz.size ξ' ζ' := by
    intro τ hτ D hD
    filter_upwards [hPT τ hτ D hD] with l hl p
    exact hl (θ l p.1 p.2, p.2)
  have hcard' : ∀ᶠ n : ℕ in atTop, (Fintype.card (Fin (M n + 1) × V n) : ℝ) ≤
      ((sz.size n : ℕ) : ℝ) ^ (A + 1 + 1 + Cv) := by
    filter_upwards [hcard, hsN.eventually (card_net_le hA1), hsN.eventually (eventually_ge_atTop 1)] with n h1 h2 h3
    have hpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast h3
    rw [Fintype.card_prod, Nat.cast_mul, Real.rpow_add hpos]
    exact mul_le_mul h2 h1 (Nat.cast_nonneg _) (Real.rpow_nonneg hpos.le _)
  have hnet : StochDomAt (seqP sz) sz.size ξ' ζ' :=
    stochDomAt_of_perTimeDomAt (seqP sz) sz.size (C := A + 1 + 1 + Cv) (by linarith) hcard' hpt'
  refine duhamelI_stoch_of_subset hsN hnet (cont_highProbAt_good sz hsN) fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  have hτ2 : 0 < τ / 2 := half_pos hτ
  filter_upwards [hH', hlow, hsN.eventually (eventually_ge_atTop 2), hsN.eventually (eventually_le_rpow 3 hτ2)] with
    n hHn hlowN hN2 hN3
  rintro ω ⟨⟨⟨u, v⟩, hbad⟩, hωΞ⟩
  have hN2' : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hmge : ((sz.size n : ℕ) : ℝ) ^ (A + 1) ≤ (M n : ℝ) := rpow_le_netSize _ _
  have hNA1 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) ^ (A + 1) := Real.rpow_pos_of_pos hNpos _
  obtain ⟨k, hk⟩ := hexists n u
  -- the distance from `u` to the near-minimizer
  have hdist : |(u : ℝ) - ((θ n k v : TimeIcc s t n) : ℝ)| ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (-(A + 1)) := by
    have h1 : 1 / (M n : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(A + 1)) := by
      rw [Real.rpow_neg hNpos.le, ← one_div]
      gcongr
    have h2 := hθ1 n k v
    calc |(u : ℝ) - ((θ n k v : TimeIcc s t n) : ℝ)|
        = |((u : ℝ) - cell n k) + (cell n k - ((θ n k v : TimeIcc s t n) : ℝ))| := by ring_nf
      _ ≤ |(u : ℝ) - cell n k| + |cell n k - ((θ n k v : TimeIcc s t n) : ℝ)| := abs_add_le _ _
      _ ≤ 1 / (M n : ℝ) + 1 / (M n : ℝ) := by
          rw [abs_sub_comm (cell n k)]
          exact add_le_add hk h2
      _ ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (-(A + 1)) := by linarith
  have hdist' : |(u : ℝ) - ((θ n k v : TimeIcc s t n) : ℝ)| ≤ ((sz.size n : ℕ) : ℝ) ^ (-A) := by
    refine hdist.trans ?_
    have hmul : ((sz.size n : ℕ) : ℝ) ^ (-(A + 1)) = ((sz.size n : ℕ) : ℝ) ^ (-A) * (((sz.size n : ℕ) : ℝ))⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hNpos]; congr 1; ring
    rw [hmul]
    have h0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-A) := Real.rpow_nonneg hNpos.le _
    have h3 : 2 * (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hNpos]; linarith
    nlinarith
  -- Hölder: `ξ u ≤ ξ θ + N^{-CR}`
  have hsq : Real.sqrt |(u : ℝ) - ((θ n k v : TimeIcc s t n) : ℝ)| ≤
      ((sz.size n : ℕ) : ℝ) ^ (-A / 2) := cont_sqrt_abs_le hNpos.le hdist'
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
  have hhol : ξ n (u, v) ω ≤ ξ n (θ n k v, v) ω + ((sz.size n : ℕ) : ℝ) ^ (-CR) := by
    have h1 := (abs_le.1 (hHn ω hωΞ u (θ n k v) v)).2
    have h2 : ((sz.size n : ℕ) : ℝ) ^ CH * Real.sqrt |(u : ℝ) - ((θ n k v : TimeIcc s t n) : ℝ)| ≤
        ((sz.size n : ℕ) : ℝ) ^ (-CR) := by
      calc ((sz.size n : ℕ) : ℝ) ^ CH * Real.sqrt |(u : ℝ) - ((θ n k v : TimeIcc s t n) : ℝ)|
          ≤ ((sz.size n : ℕ) : ℝ) ^ CH * ((sz.size n : ℕ) : ℝ) ^ (-A / 2) :=
            mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hNpos.le _)
        _ = ((sz.size n : ℕ) : ℝ) ^ (CH + -A / 2) := (Real.rpow_add hNpos _ _).symm
        _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-CR) := Real.rpow_le_rpow_of_exponent_le hN1' (by rw [hAdef]; linarith)
    linarith
  have hzlow : ((sz.size n : ℕ) : ℝ) ^ (-CR) ≤ ζ n (u, v) := hlowN (u, v)
  have hζθ : ζ n (θ n k v, v) ≤ 2 * ζ n (u, v) := by
    have := hθ2 n k v u hk
    linarith
  have hz0 : (0 : ℝ) ≤ ζ n (u, v) := hζ0 n _
  have hhalf : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) = ((sz.size n : ℕ) : ℝ) ^ τ := by
    rw [← Real.rpow_add hNpos]; ring_nf
  have hbig : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ - 2 * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) - 1 := by
    nlinarith [hhalf, hN3]
  have hprod : (0 : ℝ) ≤ (((sz.size n : ℕ) : ℝ) ^ τ - 2 * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) - 1) * ζ n (u, v) :=
    mul_nonneg hbig hz0
  have hhalf0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg hNpos.le _
  have hz'le : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζ n (θ n k v, v) ≤
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (2 * ζ n (u, v)) := mul_le_mul_of_nonneg_left hζθ hhalf0
  refine ⟨(k, v), ?_⟩
  change ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζ n (θ n k v, v) < ξ n (θ n k v, v) ω
  have hbad' : ((sz.size n : ℕ) : ℝ) ^ τ * ζ n (u, v) < ξ n (u, v) ω := hbad
  nlinarith [hbad', hhol, hprod, hzlow, hz'le]

end Lift

/-! ## 9. The engine and the pin -/

section Main

variable {d : ℕ}

/-- **The engine of `STDuhamelI`** (`(int_K-LcalE_n=2)`, `3_5:1941-2069`), zero-mode set `Q = ∅`, any sign class `P`: if the
initial term at `s` obeys `F`, then `‖(𝓛-𝒦)^{(2)}_{u,σ,a}‖ ≺ F + A^{-1/5} W^{-d}𝒯̃^L_{u,D} + W^{-D}` uniformly in
`u ∈ [s,t]`, `σ ∈ P`.  Hypotheses: the flow; the window `STReg5Mid`; `(TTT2)` in the form "`1-t ≥ ilambda²/L²` or
`1-s ≤ ilambda²/L²`" (case (i) or case (ii)); `(con_st_ind)` at `𝔠_d = 1/100`; `hE`, the body of `STEtermsMidConcl`
written out (`STEtermsMidConcl sz (STflowE z) s t` is accepted as `hE`; written out so that the registry scan of
`RBM3D/Test/Axioms.lean`, which flags a Prop-valued definition that no theorem proves, sees only `Prec`). -/
theorem stDuhamelConcl_engine (hd : 3 ≤ d) {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (sz : Sizes d)
    {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (htz : ∀ n, t n ≤ lemT (z n)) (hReg : STReg5Mid sz s t)
    (hTTT : ∀ n, sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t n ∨ 1 - s n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
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
    STDuhamelConcl sz ∅ P (STflowE z) s t := by
  classical
  intro D hD F hF0 hini
  simp only [st5_zeroModeSet_empty] at hini ⊢
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
  obtain ⟨CH, hCH0, hCH⟩ := LemDecCalELip_LK2 sz (STflowE z) s t (κ / 2) hd hsize (by linarith)
    (fun n => (hEn n).le) hs ht1 htN
  refine duhamelI_lift sz hsize (fun n => (hst n).le) hlen
    (V := fun n => {σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n))) (Cv := 3) (CR := D) (by norm_num) hD.le ?_
    (fun n p ω => ‖STLKM sz n (STflowE z n) (p.1 : ℝ) (sz.seqHflow n (p.1 : ℝ) ω) p.2.1.1 p.2.2‖)
    (fun n p => F n p + STAI sz n ^ (-(1 / 5) : ℝ) *
      STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D)) ?_ ?_ ?_ ⟨CH, hCH0, ?_⟩
  · filter_upwards [hsN.eventually (eventually_ge_atTop 4)] with n hn
    exact duhamelI_card_le sz P n hn
  · intro n p
    exact add_nonneg (add_nonneg (hF0 n p) (mul_nonneg (Real.rpow_nonneg (by unfold STAI; positivity) _)
      (ST_STprof_pos sz n _ _ _ _ _).le)) (Real.rpow_nonneg (by positivity) _)
  · exact ST_PT_of_sections sz (fun n => (hst n).le) _ _ fun tt =>
      duhamelI_section hd hκ hε h𝔡 sz hflow hs hst htz hReg hTTT hCon hE hD P F hF0 hini tt
  · filter_upwards with n p
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hWm : ((sz.size n : ℕ) : ℝ) ^ (-D) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) :=
      Real.rpow_le_rpow_of_nonpos hW0 (duhamelI_W_le_size sz (by omega) n) (neg_nonpos.2 hD.le)
    have := mul_nonneg (Real.rpow_nonneg (by unfold STAI; positivity) (-(1 / 5) : ℝ) : (0 : ℝ) ≤ STAI sz n ^ (-(1 / 5) : ℝ))
      (ST_STprof_pos sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)).le
    linarith [hF0 n p]
  · filter_upwards [hCH] with n hn ω hω u u' v
    exact hn ω hω u u' v.1.1 v.2

/-- **`STDuhamelI`** (case (i), the integrated hierarchy without zero-mode removal, all signs). -/
theorem stDuhamelI_holds (d : ℕ) : STDuhamelI d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs hst htz hReg _ _ _ _ _ hCon _ _ _ _ hE
  exact stDuhamelConcl_engine hd hκ hε h𝔡 sz hflow hs hst htz (st5_reg5I_mid (by omega) hReg)
    (fun n => Or.inl (hReg n).1) hCon hE STSigAll

end Main
end RBM.Gauss.Sizes

/-! ## Compiled nonempty instances at `d = 3` -/

namespace RBM.Gauss.Step5Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst RBM.Path Filter

/-- `stDuhamelI_holds` at `(szB, zB, 7/8, 15/16)` (the data of `inst_duhamelI`). -/
theorem inst_duhamelI_proved (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STEtermsMidConcl sz E s t → STDuhamelConcl sz ∅ STSigAll E s t) szB zB
      (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
  inst_duhamelI (stDuhamelI_holds 3) Cd hCd

/-- `stDuhamelConcl_engine` at the same data, for all signs; `STEtermsMidConcl` is the proved pin of another gate. -/
example (hE : STEtermsMidConcl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
    STDuhamelConcl szB ∅ STSigAll (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  stDuhamelConcl_engine (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10)
    (by norm_num : (0 : ℝ) < 1 / 10) szB flow_zB (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) (st5_reg5I_mid (by norm_num) szB_reg5I) (fun n => Or.inl (szB_reg5I n).1)
    (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num)) hE STSigAll

/-- The same at the data of case (ii), `(szB, zB, 15/16, 31/32)`, equal signs (`(TTT2)` through `1-s ≤ ilambda²/L²`). -/
example (hE : STEtermsMidConcl szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32)) :
    STDuhamelConcl szB ∅ STSigSame (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  stDuhamelConcl_engine (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10)
    (by norm_num : (0 : ℝ) < 1 / 10) szB flow_zB (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) (fun n => ⟨(szB_reg5II n).1, by simp [szB]; norm_num⟩)
    (fun n => Or.inr (szB_reg5II n).2) (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num))
    hE STSigSame

/-- The exponent closure (5) at concrete numbers (`duhamelI_absorb`): `A = 2^99`, so that `(2A)^{1/100} = 2 = ρ`; `Λ = 2`,
`κ = 3`, `F = P = W^{-D} = 1`, `N^τ = (2κ+1)Λ² = 28`. -/
example : (2 : ℝ) * 1 + 2 ^ 2 * 3 * (2 ^ 3 * ((2 : ℝ) ^ 99) ^ (-(1 / 4) : ℝ)) * 1 + 1 ≤
    28 * (1 + ((2 : ℝ) ^ 99) ^ (-(1 / 5) : ℝ) * 1 + 1) :=
  duhamelI_absorb (Λ := 2) (κ := 3) (F := 1) (P := 1) (Wm := 1) (A := 2 ^ 99) (ρ := 2) (Nτ := 28) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h1 : (2 * (2 : ℝ) ^ 99) = 2 ^ 100 := by norm_num
      have h2 : ((1 : ℝ) / 100) = ((100 : ℕ) : ℝ)⁻¹ := by norm_num
      rw [h1, h2, Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)])
    (by norm_num)

end RBM.Gauss.Step5Inst
