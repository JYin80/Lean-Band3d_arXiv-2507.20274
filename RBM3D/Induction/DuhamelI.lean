/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.EtermsMid
import RBM3D.Induction.Step5Kernel
import RBM3D.Path.DifREP3
import RBM3D.Chain.Step5KerGen
import RBM3D.Chain.IniTermIIGen

/-!
# S5-15 (T2333; T2496, U4s3b): the integrated hierarchy at `n = 2`, case (i), kernel part

`stDuhamelI_holds : ∀ d, STDuhamelI d` (`3_5:1941-2069`: `(int_K-LcalE_n=2)`,
`(jymwons)`..`(iois-mtx2)`) and the engine are proved over a carrier `(Cm : Step2Mat sz, μ)` in
the sibling `Induction/DuhamelI2` (`stDuhamelConclgL_engine`, `stDuhamelIgL_of`); this file is the
kernel and numerics part, in place (T2496, `docs/tickets/T2496.md`, Amend 2).

Sections 1-2: the weights `α = v/w`, `β = (w-v)/w` of `(eq:decompU)`, summation by parts and the
operator `Φ` that sums the three terms of `𝒰 = α + β Θ` slot by slot (model-free, unchanged).
Section 3: `Φ` of a profile at the carrier kernel `Step2Gen_thetaKer` (the decay
`Step5KerGen_ThDecay` at the coupling `gK`, the one comparison R1 of UBA-C1 inside
`step5KerGen_profile_holds`).  Section 4: `𝒰 = 1 + (w-v) θ_w` (`Step5KerGen_UN_decomp`) through
`Φ`, and the martingale term by Abel summation.  Section 6: the numerical facts (`ρ ≤
(2A)^{1/100}`, floors) and the a priori bound `duhamelIG_apriori` from `norm_loopFine_crudeNg`.
Section 8: the net lift at a law `μ` and an event `G` (`duhamelIG_lift`).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

open private Step5KerGen_cmp_pos from RBM3D.Chain.Step5KerGen

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.BA

/-! ## 1. Scalar facts: the weights of `(eq:decompU)` and summation by parts -/

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

private theorem duhamelI_tv_down (f : ℕ → ℝ) (m : ℕ) (h : ∀ i < m, f (i + 1) ≤ f i) :
    ∑ i ∈ Finset.range m, |f (i + 1) - f i| = f 0 - f m := by
  rw [← Finset.sum_range_sub']
  exact Finset.sum_congr rfl fun i hi => by
    rw [abs_sub_comm]; exact abs_of_nonneg (sub_nonneg.2 (h i (Finset.mem_range.1 hi)))




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

/-- **`Φ` of a profile at the carrier kernel** (`(uwp2-92kj)`; band `duhamelI_Phi_STprof`): for `0 ≤ v ≤ w < 1` in the window `(TTT2)`, given the decay
`Step5KerGen_ThDecay` of `θ` at the coupling `gK` and the comparison R1 `gK² ≤ lam² ≤ A gK²` (inside `step5KerGen_profile_holds`),
`Φ_{2(1-v)}(‖θ_w‖, W^{-d}𝒯̃^L_{v,D}) ≤ C ρ W^{-d}(𝒯_w(|a₁-a₂|) + ρ W^{-D})`, `ρ = (1-v)/(1-w)`, `C = C(d, Λ, C₆, A)`. -/
theorem duhamelIG_Phi_STprof (hd : 3 ≤ d) {Λ C₆ A : ℝ} (hΛ : 0 < Λ) (hC₆ : 0 < C₆) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (Ck : FlowFM sz) (gK : ℕ → ℝ), Step5KerGen_ThDecay Ck gK Λ C₆ →
      (∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2) →
      ∀ (n : ℕ) (σ σ' : Bool) (D v w : ℝ), 0 < gK n → gK n ≤ Λ → 0 ≤ v → v ≤ w → w < 1 →
        (∀ x, ∑ y, ‖Step2Gen_thetaKer Ck n σ σ' w x y‖ ≤ (1 - w)⁻¹) →
        (sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - w ∨ 1 - v ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) →
        ∀ a : Fin 2 → Zd d (sz.L n),
          duhamelI_Phi (fun x y => ‖Step2Gen_thetaKer Ck n σ σ' w x y‖) (2 * (1 - v))
              (fun x y => STprof sz n v D ((sz.L n : ℕ) : ℝ) x y) a ≤
            C * ((1 - v) / (1 - w)) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
              (tailT d (sz.L n) (sz.lam n) w ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) +
                (1 - v) / (1 - w) * ((sz.W n : ℕ) : ℝ) ^ (-D))) := by
  obtain ⟨Cp, hCp, H3⟩ := step5KerGen_profile_holds d hd Λ C₆ A hΛ hC₆ hA
  set C₃ : ℝ := max Cp 1 with hC₃def
  have hC₃1 : 1 ≤ C₃ := le_max_right _ _
  have hC₃0 : 0 < C₃ := by linarith
  refine ⟨((1 + 2 * C₃) ^ 2 + 9 + 4 * C₃) * C₃, by positivity, ?_⟩
  intro sz Ck gK hdec hcmp n σ σ' D v w hg0 hgΛ hv hvw hw hrow hreg a
  obtain ⟨hlam, hgl⟩ := Step5KerGen_cmp_pos (hcmp n) hg0
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
  have hT0 : ∀ x y, 0 ≤ ‖Step2Gen_thetaKer Ck n σ σ' w x y‖ := fun x y => norm_nonneg _
  refine duhamelI_Phi_prof (fun x y => ‖Step2Gen_thetaKer Ck n σ σ' w x y‖)
    (fun x y => STprof sz n v D ((sz.L n : ℕ) : ℝ) x y)
    (fun x y => tailT d (sz.L n) (sz.lam n) w (zdistInf d (sz.L n) (x - y) : ℕ)) hv1 hw hvw rfl hC₃0.le hWd0
    (mul_nonneg hC₃0.le hWm0) hT0 hrow (fun x y => tailT_nonneg (Nat.cast_nonneg _)) ?_ ?_ ?_ ?_ ?_ a |>.trans ?_
  · intro x y
    simp only [duhamelI_zdistInf_sub_comm x y]
  · intro x y
    simp only [hprof, duhamelI_zdistInf_sub_comm x y]
  · intro x y
    rw [hprof, duhamelI_tailW_eq]
    refine mul_le_mul_of_nonneg_left (max_le ?_ ?_) hWd0
    · have := ST_tailT_mono_time (d := d) (L := sz.L n) (g := sz.lam n) (u := v) (v := w)
        (r := (zdistInf d (sz.L n) (x - y) : ℕ)) (by exact_mod_cast (by omega : 1 ≤ sz.L n)) hlam.le hvw hw (Nat.cast_nonneg _)
      have := mul_nonneg hC₃0.le hWm0
      linarith
    · have := tailT_nonneg (d := d) (L := sz.L n) (g := sz.lam n) (t := w) (r := (zdistInf d (sz.L n) (x - y) : ℕ)) (Nat.cast_nonneg _)
      have := mul_le_mul_of_nonneg_right hC₃1 hWm0
      linarith
  · intro x y
    have h := H3 sz Ck gK hdec hcmp n σ σ' ((sz.W n : ℕ) : ℝ) D v w hg0 hgΛ hW hv hvw hw hreg x y
    have e : (1 - v) * ∑ b, ‖Step2Gen_thetaKer Ck n σ σ' w x b‖ * STprof sz n v D ((sz.L n : ℕ) : ℝ) b y =
        Wd * ((1 - v) * ∑ b, ‖Step2Gen_thetaKer Ck n σ σ' w x b‖ *
          tailW d (sz.L n) (sz.lam n) v ((sz.L n : ℕ) : ℝ) ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (b - y) : ℕ) : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by rw [hprof]; ring
    change (1 - v) * ∑ b, ‖Step2Gen_thetaKer Ck n σ σ' w x b‖ * STprof sz n v D ((sz.L n : ℕ) : ℝ) b y ≤ _
    rw [e]
    refine mul_le_mul_of_nonneg_left (h.trans ?_) hWd0
    have h1 : Cp * tailT d (sz.L n) (sz.lam n) w ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) ≤
        C₃ * tailT d (sz.L n) (sz.lam n) w ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (tailT_nonneg (Nat.cast_nonneg _))
    have h2 : Cp * ((1 - v) / (1 - w) * Wm) ≤ (1 - v) / (1 - w) * (C₃ * Wm) := by
      have : 0 ≤ (1 - v) / (1 - w) * Wm := mul_nonneg (div_nonneg (by linarith) h1w.le) hWm0
      calc Cp * ((1 - v) / (1 - w) * Wm) ≤ C₃ * ((1 - v) / (1 - w) * Wm) := mul_le_mul_of_nonneg_right (le_max_left _ _) this
        _ = _ := by ring
    linarith
  · intro x y
    have h := H3 sz Ck gK hdec hcmp n σ σ' ((sz.W n : ℕ) : ℝ) D w w hg0 hgΛ hW hw0 le_rfl hw (le_total _ _) x y
    rw [div_self h1w.ne', one_mul] at h
    have hle : (1 - w) * ∑ b, ‖Step2Gen_thetaKer Ck n σ σ' w x b‖ *
          tailT d (sz.L n) (sz.lam n) w (zdistInf d (sz.L n) (b - y) : ℕ) ≤
        (1 - w) * ∑ b, ‖Step2Gen_thetaKer Ck n σ σ' w x b‖ *
          tailW d (sz.L n) (sz.lam n) w ((sz.L n : ℕ) : ℝ) ((sz.W n : ℕ) : ℝ) D (zdistInf d (sz.L n) (b - y) : ℕ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (by
        rw [duhamelI_tailW_eq]; exact le_max_left _ _) (norm_nonneg _)) h1w.le
    have h1 : Cp * tailT d (sz.L n) (sz.lam n) w ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) ≤
        C₃ * tailT d (sz.L n) (sz.lam n) w ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (tailT_nonneg (Nat.cast_nonneg _))
    have h2 : Cp * Wm ≤ C₃ * Wm := mul_le_mul_of_nonneg_right (le_max_left _ _) hWm0
    linarith
  · set T := tailT d (sz.L n) (sz.lam n) w ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) with hTdef
    set ρ := (1 - v) / (1 - w) with hρdef
    have hρ : 0 ≤ ρ := div_nonneg (by linarith) h1w.le
    have hT : 0 ≤ T := tailT_nonneg (Nat.cast_nonneg _)
    have hTC : T ≤ C₃ * T := le_mul_of_one_le_left hT hC₃1
    have hK0 : 0 ≤ ((1 + 2 * C₃) ^ 2 + 9 + 4 * C₃) * ρ * Wd := by positivity
    calc ((1 + 2 * C₃) ^ 2 + 9 + 4 * C₃) * ρ * (Wd * (T + ρ * (C₃ * Wm)))
        ≤ ((1 + 2 * C₃) ^ 2 + 9 + 4 * C₃) * ρ * (Wd * (C₃ * T + ρ * (C₃ * Wm))) := by gcongr
      _ = _ := by ring



/-- The comparison R1 at one index (UBA-C1 guard (g), the converse of `Step5KerGen_cmp_pos`): `0 < l` gives `0 < g` and `g ≤ l`. -/
private theorem duhamelIG_cmp_pos' {g l A : ℝ} (h : 0 ≤ g * l ∧ g ^ 2 ≤ l ^ 2 ∧ l ^ 2 ≤ A * g ^ 2) (hl : 0 < l) :
    0 < g ∧ g ≤ l := by
  obtain ⟨h1, h2, h3⟩ := h
  have hg : 0 < g := by
    rcases lt_trichotomy g 0 with hg | hg | hg
    · nlinarith [mul_pos hl (neg_pos.2 hg)]
    · subst hg; nlinarith
    · exact hg
  exact ⟨hg, (sq_le_sq₀ hg.le hl.le).1 h2⟩

/-- **`Φ` of a profile at the carrier kernel, indexed by the model coupling** (`duhamelIG_Phi_STprof` with `0 < sz.lam n` in place of `0 < gK n`, by the
guard (g)): the hypothesis `0 < gK n ∧ gK n ≤ Λ` is derived from `0 < sz.lam n ≤ Λ` and the comparison R1 `0 ≤ gK lam`, `gK² ≤ lam² ≤ A gK²`. -/
theorem duhamelIG_Phi_lam (hd : 3 ≤ d) {Λ C₆ A : ℝ} (hΛ : 0 < Λ) (hC₆ : 0 < C₆) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (Ck : FlowFM sz) (gK : ℕ → ℝ), Step5KerGen_ThDecay Ck gK Λ C₆ →
      (∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2) →
      ∀ (n : ℕ) (σ σ' : Bool) (D v w : ℝ), 0 < sz.lam n → sz.lam n ≤ Λ → 0 ≤ v → v ≤ w → w < 1 →
        (∀ x, ∑ y, ‖Step2Gen_thetaKer Ck n σ σ' w x y‖ ≤ (1 - w)⁻¹) →
        (sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - w ∨ 1 - v ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) →
        ∀ a : Fin 2 → Zd d (sz.L n),
          duhamelI_Phi (fun x y => ‖Step2Gen_thetaKer Ck n σ σ' w x y‖) (2 * (1 - v))
              (fun x y => STprof sz n v D ((sz.L n : ℕ) : ℝ) x y) a ≤
            C * ((1 - v) / (1 - w)) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
              (tailT d (sz.L n) (sz.lam n) w ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) +
                (1 - v) / (1 - w) * ((sz.W n : ℕ) : ℝ) ^ (-D))) := by
  obtain ⟨C, hC, H⟩ := duhamelIG_Phi_STprof hd hΛ hC₆ hA
  refine ⟨C, hC, fun sz Ck gK hdec hcmp n σ σ' D v w hl hlΛ hv hvw hw hrow hreg a => ?_⟩
  obtain ⟨hg, hgl⟩ := duhamelIG_cmp_pos' (hcmp n) hl
  exact H sz Ck gK hdec hcmp n σ σ' D v w hg (hgl.trans hlΛ) hv hvw hw hrow hreg a

end ModelKernel

/-! ## 4. The kernel `𝒰` through `Φ` -/

section UgenPhi

variable {d : ℕ}

/-- **The three weights of the martingale term at the kernel `1 + c θ`** (`c` nonincreasing, nonnegative): the Abel sums of
`1`, `c_j`, `c_j²` are bounded by `2B`, `2B c₀`, `2B c₀²` (`γ + τ = c₀`). -/
private theorem duhamelI_weights' (c : ℕ → ℝ) (K : ℕ) (hK : 1 ≤ K) (hc0 : ∀ j ≤ K, 0 ≤ c j)
    (hanti : ∀ j < K, c (j + 1) ≤ c j) (M : ℕ → ℂ) {B : ℝ} (hB : ∀ j ≤ K, ‖M j‖ ≤ B) :
    ‖∑ j ∈ Finset.range K, (1 : ℝ) • (M (j + 1) - M j)‖ ≤ 2 * B ∧
    ‖∑ j ∈ Finset.range K, c j • (M (j + 1) - M j)‖ ≤ 2 * B * c 0 ∧
    ‖∑ j ∈ Finset.range K, (c j) ^ 2 • (M (j + 1) - M j)‖ ≤ 2 * B * c 0 ^ 2 := by
  have hK1 : K - 1 ≤ K := Nat.sub_le _ _
  have hanti' : ∀ i < K - 1, c (i + 1) ≤ c i := fun i hi => hanti i (by omega)
  refine ⟨?_, ?_, ?_⟩
  · simp only [one_smul]
    rw [Finset.sum_range_sub (fun j => M j) K]
    refine (norm_sub_le _ _).trans ?_
    linarith [hB K le_rfl, hB 0 (Nat.zero_le _)]
  · have h := duhamelI_abel c M K (γ := c (K - 1)) (τ := c 0 - c (K - 1))
      (by rw [abs_of_nonneg (hc0 _ hK1)])
      (by rw [duhamelI_tv_down c (K - 1) hanti']) hB
    refine h.trans (le_of_eq ?_)
    ring
  · have h := duhamelI_abel (fun j => (c j) ^ 2) M K (γ := (c (K - 1)) ^ 2) (τ := (c 0) ^ 2 - (c (K - 1)) ^ 2)
      (by rw [abs_of_nonneg (sq_nonneg _)])
      (by
        rw [duhamelI_tv_down (fun j => (c j) ^ 2) (K - 1) (fun i hi =>
          pow_le_pow_left₀ (hc0 _ (by omega)) (hanti' i hi) 2)]) hB
    refine h.trans (le_of_eq ?_)
    ring

private theorem duhamelI_mart_gen' {X : Type*} [Fintype X] [DecidableEq X] (T : X → X → ℝ)
    (K : Fin 2 → Matrix X X ℂ) (hK : ∀ i x y, ‖K i x y‖ ≤ T x y) (hT : ∀ x y, 0 ≤ T x y)
    (c : ℕ → ℝ) (Kn : ℕ) (hK1 : 1 ≤ Kn) (hc0 : ∀ j ≤ Kn, 0 ≤ c j)
    (hanti : ∀ j < Kn, c (j + 1) ≤ c j) (Mt : ℕ → (Fin 2 → X) → ℂ) (B : (Fin 2 → X) → ℝ)
    (hB : ∀ b j, j ≤ Kn → ‖Mt j b‖ ≤ B b) (a : Fin 2 → X) :
    ‖∑ j ∈ Finset.range Kn, ∑ b : Fin 2 → X,
        (∏ i, (((1 : ℝ) : ℂ) • (1 : Matrix X X ℂ) + ((c j : ℝ) : ℂ) • K i) (a i) (b i)) *
          (Mt (j + 1) b - Mt j b)‖ ≤
      2 * duhamelI_Phi T (c 0) (fun x y => B ![x, y]) a := by
  have hB0 : ∀ b, 0 ≤ B b := fun b => (norm_nonneg _).trans (hB b 0 (Nat.zero_le _))
  have hexp : ∀ j, ∑ b : Fin 2 → X, (∏ i, (((1 : ℝ) : ℂ) • (1 : Matrix X X ℂ) + ((c j : ℝ) : ℂ) • K i) (a i) (b i)) *
          (Mt (j + 1) b - Mt j b) =
      ((1 : ℝ) : ℂ) * (Mt (j + 1) a - Mt j a) +
        ((c j : ℝ) : ℂ) * (∑ y, K 1 (a 1) y * (Mt (j + 1) ![a 0, y] - Mt j ![a 0, y]) +
          ∑ x, K 0 (a 0) x * (Mt (j + 1) ![x, a 1] - Mt j ![x, a 1])) +
        ((c j ^ 2 : ℝ) : ℂ) * ∑ x, ∑ y, K 0 (a 0) x * K 1 (a 1) y * (Mt (j + 1) ![x, y] - Mt j ![x, y]) := by
    intro j
    rw [duhamelI_expand]
    push_cast
    ring
  simp_rw [hexp]
  have hYa : a = ![a 0, a 1] := by ext i; fin_cases i <;> rfl
  have hw := fun b => duhamelI_weights' c Kn hK1 hc0 hanti (fun j => Mt j b) (hB b)
  -- the three reorganised sums
  have P1 : ∑ j ∈ Finset.range Kn, ((c j : ℝ) : ℂ) * ∑ y, K 1 (a 1) y * (Mt (j + 1) ![a 0, y] - Mt j ![a 0, y]) =
      ∑ y, K 1 (a 1) y * ∑ j ∈ Finset.range Kn, ((c j : ℝ) : ℂ) * (Mt (j + 1) ![a 0, y] - Mt j ![a 0, y]) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun j _ => by ring
  have P2 : ∑ j ∈ Finset.range Kn, ((c j : ℝ) : ℂ) * ∑ x, K 0 (a 0) x * (Mt (j + 1) ![x, a 1] - Mt j ![x, a 1]) =
      ∑ x, K 0 (a 0) x * ∑ j ∈ Finset.range Kn, ((c j : ℝ) : ℂ) * (Mt (j + 1) ![x, a 1] - Mt j ![x, a 1]) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun j _ => by ring
  have P3 : ∑ j ∈ Finset.range Kn, ((c j ^ 2 : ℝ) : ℂ) * ∑ x, ∑ y, K 0 (a 0) x * K 1 (a 1) y * (Mt (j + 1) ![x, y] - Mt j ![x, y]) =
      ∑ x, ∑ y, K 0 (a 0) x * K 1 (a 1) y * ∑ j ∈ Finset.range Kn, ((c j ^ 2 : ℝ) : ℂ) * (Mt (j + 1) ![x, y] - Mt j ![x, y]) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun j _ => by ring
  have hsum : ∑ j ∈ Finset.range Kn, (((1 : ℝ) : ℂ) * (Mt (j + 1) a - Mt j a) +
        ((c j : ℝ) : ℂ) * (∑ y, K 1 (a 1) y * (Mt (j + 1) ![a 0, y] - Mt j ![a 0, y]) +
          ∑ x, K 0 (a 0) x * (Mt (j + 1) ![x, a 1] - Mt j ![x, a 1])) +
        ((c j ^ 2 : ℝ) : ℂ) * ∑ x, ∑ y, K 0 (a 0) x * K 1 (a 1) y * (Mt (j + 1) ![x, y] - Mt j ![x, y])) =
      (∑ j ∈ Finset.range Kn, ((1 : ℝ) : ℂ) * (Mt (j + 1) a - Mt j a)) +
        (∑ y, K 1 (a 1) y * ∑ j ∈ Finset.range Kn, ((c j : ℝ) : ℂ) * (Mt (j + 1) ![a 0, y] - Mt j ![a 0, y]) +
          ∑ x, K 0 (a 0) x * ∑ j ∈ Finset.range Kn, ((c j : ℝ) : ℂ) * (Mt (j + 1) ![x, a 1] - Mt j ![x, a 1])) +
        ∑ x, ∑ y, K 0 (a 0) x * K 1 (a 1) y * ∑ j ∈ Finset.range Kn, ((c j ^ 2 : ℝ) : ℂ) * (Mt (j + 1) ![x, y] - Mt j ![x, y]) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← P1, ← P2, ← P3, ← Finset.sum_add_distrib]
    simp only [mul_add, Finset.sum_add_distrib]
  rw [hsum]
  -- norms
  have n0 : ‖∑ j ∈ Finset.range Kn, ((1 : ℝ) : ℂ) * (Mt (j + 1) a - Mt j a)‖ ≤ 2 * B a := by
    have := (hw a).1
    simpa [Complex.real_smul] using this
  have n1 : ∀ x : Fin 2 → X, ‖∑ j ∈ Finset.range Kn, ((c j : ℝ) : ℂ) * (Mt (j + 1) x - Mt j x)‖ ≤ 2 * B x * c 0 := by
    intro x
    have := (hw x).2.1
    simpa [Complex.real_smul] using this
  have n2 : ∀ x : Fin 2 → X, ‖∑ j ∈ Finset.range Kn, ((c j ^ 2 : ℝ) : ℂ) * (Mt (j + 1) x - Mt j x)‖ ≤ 2 * B x * c 0 ^ 2 := by
    intro x
    have := (hw x).2.2
    simpa [Complex.real_smul] using this
  have m1 : ‖∑ y, K 1 (a 1) y * ∑ j ∈ Finset.range Kn, ((c j : ℝ) : ℂ) * (Mt (j + 1) ![a 0, y] - Mt j ![a 0, y])‖ ≤
      ∑ y, T (a 1) y * (2 * B ![a 0, y] * c 0) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => by
      rw [norm_mul]; exact mul_le_mul (hK _ _ _) (n1 _) (norm_nonneg _) (hT _ _))
  have m2 : ‖∑ x, K 0 (a 0) x * ∑ j ∈ Finset.range Kn, ((c j : ℝ) : ℂ) * (Mt (j + 1) ![x, a 1] - Mt j ![x, a 1])‖ ≤
      ∑ x, T (a 0) x * (2 * B ![x, a 1] * c 0) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => by
      rw [norm_mul]; exact mul_le_mul (hK _ _ _) (n1 _) (norm_nonneg _) (hT _ _))
  have m3 : ‖∑ x, ∑ y, K 0 (a 0) x * K 1 (a 1) y * ∑ j ∈ Finset.range Kn, ((c j ^ 2 : ℝ) : ℂ) * (Mt (j + 1) ![x, y] - Mt j ![x, y])‖ ≤
      ∑ x, ∑ y, T (a 0) x * T (a 1) y * (2 * B ![x, y] * c 0 ^ 2) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => by
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul (hK _ _ _) (hK _ _ _) (norm_nonneg _) (hT _ _)) (n2 _) (norm_nonneg _)
        (mul_nonneg (hT _ _) (hT _ _))))
  refine norm_add₃_le.trans ?_
  have e1 : ∑ y, T (a 1) y * (2 * B ![a 0, y] * c 0) = 2 * c 0 * ∑ y, T (a 1) y * B ![a 0, y] := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
  have e2 : ∑ x, T (a 0) x * (2 * B ![x, a 1] * c 0) = 2 * c 0 * ∑ x, T (a 0) x * B ![x, a 1] := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
  have e3 : ∑ x, ∑ y, T (a 0) x * T (a 1) y * (2 * B ![x, y] * c 0 ^ 2) =
      2 * c 0 ^ 2 * ∑ x, ∑ y, T (a 0) x * T (a 1) y * B ![x, y] := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
  unfold duhamelI_Phi
  have hBa : B ![a 0, a 1] = B a := by rw [← hYa]
  simp only [hBa]
  refine (add_le_add (add_le_add n0 ((norm_add_le _ _).trans (add_le_add m1 m2))) m3).trans ?_
  rw [e1, e2, e3]
  exact le_of_eq (by ring)



section UgenG

variable {sz : Sizes d} {Ck : FlowFM sz} {n : ℕ}

/-- The slot kernels of `𝒰^{(2)}_σ` agree entrywise in norm with the first one, if `θ^{(σ₁σ₀)} = θ^{(σ₀σ₁)}` (the swap E1). -/
private theorem duhamelIG_slot_le (σ : Fin 2 → Bool) (w : ℝ)
    (hpair : Step2Gen_thetaKer Ck n (σ 1) (σ 0) w = Step2Gen_thetaKer Ck n (σ 0) (σ 1) w) (i : Fin 2) (x y : Zd d (sz.L n)) :
    ‖Step2Gen_thetaKer Ck n (σ i) (σ (finRotate 2 i)) w x y‖ ≤ ‖Step2Gen_thetaKer Ck n (σ 0) (σ 1) w x y‖ := by
  fin_cases i
  · exact le_of_eq rfl
  · exact le_of_eq (by simp [hpair])

/-- `‖(𝒰_{v,w} ∘ Y)_a‖ ≤ Φ_{2(1-v)}(‖θ_w‖, |Y|)` (`(eq:decompUalt)`: `𝒰_{v,w} = 1 + (w - v) θ_w` at each slot; band `duhamelI_Ugen_le`). -/
theorem duhamelIG_Ugen_le (hU : Step2Gen_USemigroup Ck n) (σ : Fin 2 → Bool)
    (hpair : ∀ w : ℝ, 0 < w → w < 1 → Step2Gen_thetaKer Ck n (σ 1) (σ 0) w = Step2Gen_thetaKer Ck n (σ 0) (σ 1) w)
    {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) (hw0 : 0 < w) (hw1 : w < 1) (Y : (Fin 2 → Zd d (sz.L n)) → ℂ)
    (a : Fin 2 → Zd d (sz.L n)) :
    ‖Step2Gen_UN Ck n σ v w Y a‖ ≤
      duhamelI_Phi (fun x y => ‖Step2Gen_thetaKer Ck n (σ 0) (σ 1) w x y‖) (2 * (1 - v)) (fun x y => ‖Y ![x, y]‖) a := by
  rw [Step5KerGen_UN_decomp Ck n hU σ v w hw0.le hw1 Y a]
  have e : ∀ i : Fin 2, (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) +
      ((w - v : ℝ) : ℂ) • Step2Gen_thetaKer Ck n (σ i) (σ (finRotate 2 i)) w =
      ((1 : ℝ) : ℂ) • (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) +
        ((w - v : ℝ) : ℂ) • Step2Gen_thetaKer Ck n (σ i) (σ (finRotate 2 i)) w := fun i => by simp
  simp only [e]
  have hβ0 : 0 ≤ w - v := by linarith
  have hh : 0 ≤ 2 * (1 - v) := by linarith
  refine duhamelI_UN_abs (fun x y => ‖Step2Gen_thetaKer Ck n (σ 0) (σ 1) w x y‖) (α := 1) (β := w - v) (h := 2 * (1 - v))
    (fun i => Step2Gen_thetaKer Ck n (σ i) (σ (finRotate 2 i)) w)
    (fun i x y => duhamelIG_slot_le σ w (hpair w hw0 hw1) i x y) (fun x y => norm_nonneg _) zero_le_one le_rfl hβ0
    (by linarith) (by nlinarith) Y a

private theorem duhamelIG_Phi_nonneg {X : Type*} [Fintype X] {T : X → X → ℝ} {h : ℝ} {q : X → X → ℝ}
    (hT : ∀ x y, 0 ≤ T x y) (hq : ∀ x y, 0 ≤ q x y) (hh : 0 ≤ h) (a : Fin 2 → X) : 0 ≤ duhamelI_Phi T h q a := by
  unfold duhamelI_Phi
  have s1 : 0 ≤ ∑ y, T (a 1) y * q (a 0) y := Finset.sum_nonneg fun y _ => mul_nonneg (hT _ _) (hq _ _)
  have s2 : 0 ≤ ∑ x, T (a 0) x * q x (a 1) := Finset.sum_nonneg fun x _ => mul_nonneg (hT _ _) (hq _ _)
  have s3 : 0 ≤ ∑ x, ∑ y, T (a 0) x * T (a 1) y * q x y :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => mul_nonneg (mul_nonneg (hT _ _) (hT _ _)) (hq _ _)
  have := hq (a 0) (a 1)
  positivity

/-- **The martingale term through `Φ`**: `‖Σ_{j<K} (𝒰_{u_j,w} ∘ ΔM_j)_a‖ ≤ 4 Φ_{2(1-u_0)}(‖θ_w‖, B)` if `|M_j(b)| ≤ B(b)`
for `j ≤ K` (`(uuwmskiow)`: Abel summation of the weights `1, w - u_j, (w - u_j)²`; band `duhamelI_mart_Ugen`). -/
theorem duhamelIG_mart_Ugen (hU : Step2Gen_USemigroup Ck n) (σ : Fin 2 → Bool)
    (hpair : ∀ w : ℝ, 0 < w → w < 1 → Step2Gen_thetaKer Ck n (σ 1) (σ 0) w = Step2Gen_thetaKer Ck n (σ 0) (σ 1) w)
    (u : ℕ → ℝ) (Kn : ℕ) (hK1 : 1 ≤ Kn) {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hu0 : ∀ j ≤ Kn, 0 ≤ u j)
    (huw : ∀ j ≤ Kn, u j ≤ w) (hmono : ∀ j < Kn, u j ≤ u (j + 1)) (Mt : ℕ → (Fin 2 → Zd d (sz.L n)) → ℂ)
    (B : (Fin 2 → Zd d (sz.L n)) → ℝ) (hB : ∀ b j, j ≤ Kn → ‖Mt j b‖ ≤ B b) (a : Fin 2 → Zd d (sz.L n)) :
    ‖∑ j ∈ Finset.range Kn, Step2Gen_UN Ck n σ (u j) w (fun b => Mt (j + 1) b - Mt j b) a‖ ≤
      4 * duhamelI_Phi (fun x y => ‖Step2Gen_thetaKer Ck n (σ 0) (σ 1) w x y‖) (2 * (1 - u 0)) (fun x y => B ![x, y]) a := by
  have e : ∀ j, j ∈ Finset.range Kn → Step2Gen_UN Ck n σ (u j) w (fun b => Mt (j + 1) b - Mt j b) a =
      ∑ b : Fin 2 → Zd d (sz.L n), (∏ i, (((1 : ℝ) : ℂ) • (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) +
        ((w - u j : ℝ) : ℂ) • Step2Gen_thetaKer Ck n (σ i) (σ (finRotate 2 i)) w) (a i) (b i)) *
          (Mt (j + 1) b - Mt j b) := fun j hj => by
    have hj' : j ≤ Kn := (Finset.mem_range.1 hj).le
    rw [Step5KerGen_UN_decomp Ck n hU σ (u j) w hw0.le hw1 _ a]
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp
  rw [Finset.sum_congr rfl e]
  have hB0 : ∀ b, 0 ≤ B b := fun b => (norm_nonneg _).trans (hB b 0 (Nat.zero_le _))
  have hT0 : ∀ x y : Zd d (sz.L n), 0 ≤ ‖Step2Gen_thetaKer Ck n (σ 0) (σ 1) w x y‖ := fun x y => norm_nonneg _
  have h := duhamelI_mart_gen' (fun x y => ‖Step2Gen_thetaKer Ck n (σ 0) (σ 1) w x y‖)
    (fun i => Step2Gen_thetaKer Ck n (σ i) (σ (finRotate 2 i)) w)
    (fun i x y => duhamelIG_slot_le σ w (hpair w hw0 hw1) i x y) hT0 (fun j => w - u j) Kn hK1
    (fun j hj => by linarith [huw j hj]) (fun j hj => by linarith [hmono j hj]) Mt B hB a
  refine h.trans ?_
  have hh0 : 0 ≤ w - u 0 := by linarith [huw 0 (Nat.zero_le _)]
  have hmono' := duhamelI_Phi_mono_h (T := fun x y => ‖Step2Gen_thetaKer Ck n (σ 0) (σ 1) w x y‖) (q := fun x y => B ![x, y])
    hT0 (fun x y => hB0 _) hh0 (show w - u 0 ≤ 2 * (1 - u 0) by linarith [hu0 0 (Nat.zero_le _)]) a
  have hnn := duhamelIG_Phi_nonneg hT0 (q := fun x y => B ![x, y]) (fun x y => hB0 _) (by linarith [hu0 0 (Nat.zero_le _)] : 0 ≤ 2 * (1 - u 0)) a
  linarith

end UgenG

end UgenPhi

/-! ## 6. Numerical facts of the flow and of the choice of constants -/

section Numerics
variable {d : ℕ}

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

/-- The a priori bound over a carrier (band `duhamelI_apriori`): for Hermitian `H`, `u ≤ tt < 1`, `(1-tt)⁻¹ ≤ N`, `c₀ ≤ Im m` and
`‖𝒦^{(2)}_{u,σ,a}‖ ≤ N`, `‖(𝓛-𝒦)^{(2)}_{u,σ,a}(H)‖ ≤ (N/c₀)² + N` (`norm_loopFine_crudeNg` at `ℓ = 2`). -/
theorem duhamelIG_apriori {sz : Sizes d} {Cm : Step2Mat sz} {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) {u tt c₀ : ℝ}
    (hη : ∀ v : ℝ, Cm.eta n v = (1 - v) * (Cm.m n).im) (hut : u ≤ tt) (htt : tt < 1)
    (hN : (1 - tt)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) (hc₀ : 0 < c₀) (hc : c₀ ≤ (Cm.m n).im)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (hK : ‖Cm.K n u σ a‖ ≤ ((sz.size n : ℕ) : ℝ)) :
    ‖STLKMg Cm n u H σ a‖ ≤ (((sz.size n : ℕ) : ℝ) / c₀) ^ 2 + ((sz.size n : ℕ) : ℝ) := by
  have hu1 : u < 1 := hut.trans_lt htt
  have h1 := norm_loopFine_crudeNg hL hH hu1 (by norm_num : 1 ≤ 2) σ a
  have hη' : (Cm.eta n u)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) / c₀ := by
    have h1t : 0 < 1 - tt := by linarith
    have hη0 : 0 < Cm.eta n u := by rw [hη]; exact mul_pos (by linarith) (lt_of_lt_of_le hc₀ hc)
    rw [inv_le_iff_one_le_mul₀ hη0]
    have hη1 : (1 - tt) * c₀ ≤ Cm.eta n u := by
      rw [hη]; exact mul_le_mul (by linarith) hc hc₀.le (by linarith)
    have h2 : 1 ≤ ((sz.size n : ℕ) : ℝ) * (1 - tt) := by
      rw [inv_le_iff_one_le_mul₀ h1t] at hN; exact hN
    have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
    calc 1 ≤ ((sz.size n : ℕ) : ℝ) * (1 - tt) := h2
      _ = (((sz.size n : ℕ) : ℝ) / c₀) * ((1 - tt) * c₀) := by field_simp
      _ ≤ (((sz.size n : ℕ) : ℝ) / c₀) * Cm.eta n u := mul_le_mul_of_nonneg_left hη1 (by positivity)
  unfold STLKMg STLMg
  calc _ ≤ ‖Cm.LM n u H σ a‖ + ‖Cm.K n u σ a‖ := norm_sub_le _ _
    _ ≤ (((sz.size n : ℕ) : ℝ) / c₀) ^ 2 + ((sz.size n : ℕ) : ℝ) :=
        add_le_add (h1.trans (pow_le_pow_left₀ (inv_nonneg.2 (by rw [hη]; exact mul_nonneg (by linarith) (by linarith))) hη' 2)) hK


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

/-! ## 7. Counting and probability helpers of the per-section statement (used in `DuhamelI2`, `DuhamelII`) -/

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

/-- **The net lift with an arbitrary deterministic control over a law** (`1_2:1400`; band `duhamelI_lift`): a per-time `≺` at the law `μ` with the
control `ζ ≥ N^{-C_R}`, for a family that is Hölder-`1/2` on a high-probability event `G` of `μ` (D2), is uniform in `u ∈ [s,t]`.  The control is not assumed to vary slowly: at
every net cell and label the section is taken at a near-minimizer of `ζ` over the cell (`ζ(θ) ≤ ζ(u) + N^{-C_R} ≤ 2ζ(u)`). -/
theorem duhamelIG_lift (sz : Sizes d) (μ : Measure sz.SeqΩ) (G : ℕ → Set sz.SeqΩ) (hG : HighProbAt μ sz.size G)
    (hsz : sz.SizeTendsto) {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n)
    (hlen : ∀ n, t n - s n ≤ 1) {V : ℕ → Type} [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)] {Cv CR : ℝ}
    (hCv : 0 ≤ Cv) (hCR : 0 ≤ CR)
    (hcard : ∀ᶠ n in atTop, (Fintype.card (V n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ Cv)
    (ξ : ∀ n, TimeIcc s t n × V n → sz.SeqΩ → ℝ) (ζ : ∀ n, TimeIcc s t n × V n → ℝ) (hζ0 : ∀ n p, 0 ≤ ζ n p)
    (hPT : PrecPTL sz μ ξ (fun n p _ => ζ n p))
    (hlow : ∀ᶠ n in atTop, ∀ p, ((sz.size n : ℕ) : ℝ) ^ (-CR) ≤ ζ n p)
    (hH : ∃ CH : ℝ, 0 ≤ CH ∧ ∀ᶠ n in atTop, ∀ ω ∈ G n, ∀ (u u' : TimeIcc s t n) (v : V n),
      |ξ n (u, v) ω - ξ n (u', v) ω| ≤ ((sz.size n : ℕ) : ℝ) ^ CH * Real.sqrt |(u : ℝ) - (u' : ℝ)|) :
    PrecL sz μ ξ (fun n p _ => ζ n p) := by
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
  have hpt' : PerTimeDomAt μ sz.size ξ' ζ' := by
    intro τ hτ D hD
    filter_upwards [hPT τ hτ D hD] with l hl p
    exact hl (θ l p.1 p.2, p.2)
  have hcard' : ∀ᶠ n : ℕ in atTop, (Fintype.card (Fin (M n + 1) × V n) : ℝ) ≤
      ((sz.size n : ℕ) : ℝ) ^ (A + 1 + 1 + Cv) := by
    filter_upwards [hcard, hsN.eventually (card_net_le hA1), hsN.eventually (eventually_ge_atTop 1)] with n h1 h2 h3
    have hpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast h3
    rw [Fintype.card_prod, Nat.cast_mul, Real.rpow_add hpos]
    exact mul_le_mul h2 h1 (Nat.cast_nonneg _) (Real.rpow_nonneg hpos.le _)
  have hnet : StochDomAt μ sz.size ξ' ζ' :=
    stochDomAt_of_perTimeDomAt μ sz.size (C := A + 1 + 1 + Cv) (by linarith) hcard' hpt'
  refine duhamelI_stoch_of_subset hsN hnet hG fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
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

end RBM.Gauss.Sizes
