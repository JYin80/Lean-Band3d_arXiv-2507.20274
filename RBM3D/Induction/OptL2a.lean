/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step2Iterate
import RBM3D.Induction.EMn2Poly
import RBM3D.Induction.NewKLK

set_option linter.style.longLine false

/-!
# ST2-14 (ticket T2110): `(eq:opt_L2)`, part 1: the Grönwall inequality `(eq:Gronwall_2L_max)` on the grid

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): `(lokis2)` `3_5:466`,
`(eq:opt_L2)` `3_5:470`, `(l>0EQ)` `3_5:474`, `(eq:Gronwall_2L_max)` `3_5:481`.  New; no port.

Targets (section 7), all for a time window `[s, T]` (`T` is the end of the grid; ST2-15 takes
`T = u` for each section `u ∈ [s,t]`, runs the linear Grönwall step `ST_gronwall`, chooses `𝔠₀`, and
proves `STOptL2`):
* `stOptL2a_drift` (Target 1, `(l>0EQ)`): w.h.p. on the grid, drift of `(𝓛-𝒦)^{(2)}` `≤ C₀ (1-u_j)⁻¹ J_j
  + N^τ η_{u_j}⁻¹ λ^{3/2}`, from `lem:newKLK` at `ℓ = 0` (`stNewKLK_holds`, deterministic form
  `OptL2a_drift_matrix`, `OptL2a_drift_grid`) and the light-weight term (pin `STLWB`);
* `stOptL2a_martingale` (Target 2): `|Mart_k| ≤ N^τ λ^{5/4}` w.h.p., from `stEMn2Poly_holds` and the pin
  `STGridMart` (its Markov step `3_5:476–478`);
* `stOptL2a_gronwall` (Target 3, `(eq:Gronwall_2L_max)`): `J_k ≤ N^τ (B_s² + λ^{5/4}) + Δ Σ_{j<k} (C₀/(1-u_j)) J_j`
  w.h.p. for all `k ≤ K_n`, in the form that `ST_gronwall` consumes.

`λ = ((1-s)/(1-T)) W^{-d}B_{T,0}` (`OptL2alam`) is the paper's `W^{-c₀}` of `(lokis2)`; the control of the
pins is `Ψ = min(√λ, W^{-ε₀})` (`OptL2aPsi`), equal to `√λ` for large `n`.  Of `(con_st_ind)` only the first
conjunct `B_T^{𝔠_d} ≤ (1-T)/(1-s)` with `𝔠_d ≤ 1/2` is used.  The final section holds one compiled `example` per
target at `d = 3` (`sz0`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. The drift bound of `(l>0EQ)` (deterministic), Target 1 -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Drift

variable {d : ℕ} (sz : Sizes d)

/-- `J = max_{σ,a} |(𝓛-𝒦)^{(2)}_{u,σ,a}|` of a fine matrix `H`. -/
def OptL2aJ (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ :=
  Finset.univ.sup' ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
    (fun i : STLab sz n => ‖STLKM sz n E u H i.1 i.2‖)

theorem OptL2aJ_ge (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (i : STLab sz n) :
    ‖STLKM sz n E u H i.1 i.2‖ ≤ OptL2aJ sz n E u H :=
  Finset.le_sup' (fun i : STLab sz n => ‖STLKM sz n E u H i.1 i.2‖) (Finset.mem_univ i)

theorem OptL2aJ_nonneg (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : 0 ≤ OptL2aJ sz n E u H :=
  (norm_nonneg _).trans (OptL2aJ_ge sz n E u H ((fun _ => true), (fun _ => 0)))

theorem OptL2aJ_le (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {B : ℝ}
    (h : ∀ i : STLab sz n, ‖STLKM sz n E u H i.1 i.2‖ ≤ B) : OptL2aJ sz n E u H ≤ B :=
  Finset.sup'_le _ _ fun i _ => h i

/-- At `ℓ = 0` the profile `W^{-d} 𝒯̃^0_{u,D}(|a-b|)` does not depend on `(a, b)`. -/
theorem OptL2a_prof_zero (n : ℕ) (u D : ℝ) (a b a' b' : Zd d (sz.L n)) :
    STprof sz n u D 0 a b = STprof sz n u D 0 a' b' := by
  have h : ∀ x y : Zd d (sz.L n),
      tailW d (sz.L n) (sz.lam n) u 0 ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (x - y) : ℕ) : ℝ) =
        tailW d (sz.L n) (sz.lam n) u 0 ((sz.W n : ℕ) : ℝ) D 0 := by
    intro x y
    unfold tailW
    rw [min_eq_right (Nat.cast_nonneg _), min_self]
  unfold STprof
  rw [h, h]

/-- `Ĵ^0_{u,D} · W^{-d} 𝒯̃^0_{u,D} ≤ J`: at `ℓ = 0` the random control times the (constant) profile
is at most the maximum `J`. -/
theorem OptL2a_Jhat_mul_le (n : ℕ) (E D u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (a : Fin 2 → Zd d (sz.L n)) :
    STJhatM sz n E D 0 u H * STprof sz n u D 0 (a 0) (a 1) ≤ OptL2aJ sz n E u H := by
  have hP := ST_STprof_pos sz n u D 0 (a 0) (a 1)
  rw [← le_div_iff₀ hP]
  unfold STJhatM
  refine Finset.sup'_le _ _ fun p _ => ?_
  rw [OptL2a_prof_zero sz n u D (p.2 0) (p.2 1) (a 0) (a 1)]
  exact div_le_div_of_nonneg_right (OptL2aJ_ge sz n E u H p) hP.le

/-- **Target 1, matrix level (`(l>0EQ)`, `3_5:474`)**: `lem:newKLK` at `ℓ = 0` bounds the two
terms `Θ^{(2)}_{u,σ} ∘ (𝓛-𝒦)^{(2)}` and `𝓔^{(𝓛-𝓚)×(𝓛-𝓚)}` of the drift of `(𝓛-𝒦)^{(2)}`
by `2C (1-u)⁻¹ J`; the quadratic term of `lem:newKLK` is absent at `ℓ = 0`. -/
theorem OptL2a_drift_matrix {κ 𝔡 C δ₀ : ℝ} (hC : 0 ≤ C) (hnew : STNewKLKAt d κ 𝔡 C δ₀) (n : ℕ)
    (E u : ℝ) (hlam : 0 < sz.lam n) (hlam' : sz.lam n ≤ 𝔡⁻¹) (hE : |E| ≤ 2 - κ) (hu0 : 0 ≤ u)
    (hu1 : u < 1) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hH : H.IsHermitian) (hweak : ∀ x y, ‖STGMM sz n E u H x y‖ ≤ δ₀) (i : STLab sz n) :
    ‖STthetaOp sz n E u i.1 (STLKM sz n E u H i.1) i.2‖ + ‖STELKLKM sz n E u H i.1 i.2‖ ≤
      2 * C / (1 - u) * OptL2aJ sz n E u H := by
  have hL : (0 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := Nat.cast_nonneg _
  obtain ⟨h1, h2⟩ := hnew sz n E u 1 0 hlam hlam' hE hu0 hu1 (by norm_num) le_rfl hL H hH hweak
    i.1 i.2
  have hv : 0 < 1 - u := by linarith
  have hJ := OptL2a_Jhat_mul_le sz n E 1 u H i.2
  have hc : 0 ≤ C / (1 - u) := div_nonneg hC hv.le
  have e1 : ‖STthetaOp sz n E u i.1 (STLKM sz n E u H i.1) i.2‖ ≤ C / (1 - u) * OptL2aJ sz n E u H := by
    refine h1.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hJ hc
  have e2 : ‖STELKLKM sz n E u H i.1 i.2‖ ≤ C / (1 - u) * OptL2aJ sz n E u H := by
    refine h2.trans ?_
    have h0 : ¬ ((1 : ℝ) ≤ 0) := by norm_num
    simp only [h0, ite_false, mul_zero, add_zero]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hJ hc
  calc _ ≤ C / (1 - u) * OptL2aJ sz n E u H + C / (1 - u) * OptL2aJ sz n E u H := add_le_add e1 e2
    _ = 2 * C / (1 - u) * OptL2aJ sz n E u H := by ring

/-- **Target 1, grid level**: the drift of `(𝓛-𝒦)^{(2)}` at the grid state `j` is at most
`C₀ (1-u_j)⁻¹ J_j + |𝓔^{G̃}|` with `C₀ = 2C`, whenever the weak law holds at the grid state. -/
theorem OptL2a_drift_grid {κ 𝔡 C δ₀ : ℝ} (hC : 0 ≤ C) (hnew : STNewKLKAt d κ 𝔡 C δ₀)
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (E : ℝ) (hlam : 0 < sz.lam n) (hlam' : sz.lam n ≤ 𝔡⁻¹)
    (hE : |E| ≤ 2 - κ) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0)
    (ω : PathΩ sz) (j : ℕ) (hj : j ≤ K n)
    (hweak : ∀ x y, ‖STGMM sz n E (gridTime s t K n j) (pathH sz s t K n j ω) x y‖ ≤ δ₀)
    (i : STLab sz n) :
    ‖STgDrift sz s t K n E i.1 i.2 j ω‖ ≤
      2 * C / (1 - gridTime s t K n j) * OptL2aJ sz n E (gridTime s t K n j) (pathH sz s t K n j ω) +
        ‖STEGtM sz n E (gridTime s t K n j) (pathH sz s t K n j ω) i.1 i.2‖ := by
  have hmem := ST_gridTime_mem s t K n j hst hK hj
  have hu0 : 0 ≤ gridTime s t K n j := hs0.trans hmem.1
  have hu1 : gridTime s t K n j < 1 := lt_of_le_of_lt hmem.2 ht1
  have h := OptL2a_drift_matrix sz hC hnew n E (gridTime s t K n j) hlam hlam' hE hu0 hu1
    (pathH sz s t K n j ω) (pathH_isHermitian sz s t K n j ω) hweak i
  unfold STgDrift
  calc _ ≤ ‖STthetaOp sz n E (gridTime s t K n j) i.1
          (STLKM sz n E (gridTime s t K n j) (pathH sz s t K n j ω) i.1) i.2‖ +
        ‖STELKLKM sz n E (gridTime s t K n j) (pathH sz s t K n j ω) i.1 i.2‖ +
        ‖STEGtM sz n E (gridTime s t K n j) (pathH sz s t K n j ω) i.1 i.2‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ _ := add_le_add h le_rfl

end Drift

end RBM.Gauss.Sizes

/-! ## 2. The control `Ψ` of the light-weight and martingale pins at a time section -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Sections

variable {d : ℕ} (sz : Sizes d)

/-- `λ_n = ((1-s)/(1-T)) W^{-d}B_{T,0}`: the paper's `W^{-c₀}` of `(lokis2)` (`3_5:466`) at the end
`T` of the time window. -/
def OptL2alam (s T : ℕ → ℝ) (n : ℕ) : ℝ := (1 - s n) / (1 - T n) * sz.Bctl n (T n)

/-- The deterministic control of `lem:LWterm` and `lem: EMn2_N`: `Ψ_n = min(√λ_n, W^{-ε₀})`, the same
for all distances (equal to `√λ_n` for large `n`, `STPsiClass` asks `Ψ ≤ W^{-ε₀}` for every `n`). -/
def OptL2aPsi (ε₀ : ℝ) (s T : ℕ → ℝ) (n : ℕ) : ℝ :=
  min (Real.sqrt (OptL2alam sz s T n)) (((sz.W n : ℕ) : ℝ) ^ (-ε₀))

/-- A profile that does not depend on the distance is in the class `(eq:Psi)` of `STPsiClass`. -/
theorem OptL2a_psiClass_const {ε₀ : ℝ} (Ψ0 : ℕ → ℝ) (hpos : ∀ n, 0 < Ψ0 n)
    (hle : ∀ n, Ψ0 n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) {c0 : ℝ} (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hwin : ∀ᶠ n in atTop, c0 * ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ0 n) :
    STPsiClass sz ε₀ (fun n _ => Ψ0 n) := by
  refine ⟨fun n r => ⟨hpos n, hle n⟩, fun n r r' _ => le_refl _, fun C => ⟨c0, hc0, ?_⟩,
    ⟨2, 2, by norm_num, by norm_num, ?_⟩⟩
  · filter_upwards [hwin] with n hn
    refine ⟨(le_inv_mul_iff₀ hc0).2 hn, fun r _ => ?_⟩
    exact mul_le_of_le_one_left (hpos n).le hc01
  · intro n r₁ r₂ h1 h12
    have hr1 : (0 : ℝ) < r₁ := by exact_mod_cast h1
    have hr12 : (1 : ℝ) ≤ (r₂ : ℝ) / r₁ := by
      rw [le_div_iff₀ hr1]; simpa using (by exact_mod_cast h12 : (r₁ : ℝ) ≤ r₂)
    rw [div_self (hpos n).ne']
    have := Real.one_le_rpow hr12 (by norm_num : (0 : ℝ) ≤ 2)
    linarith

/-- `ρ B ≤ B^{1/2}` from `B^{𝔠_d} ≤ (1-T)/(1-s)`, `0 < B ≤ 1` and `𝔠_d ≤ 1/2` (the first conjunct of
`(con_st_ind)`). -/
theorem OptL2a_lam_le_sqrt {s T B 𝔠d : ℝ} (hB0 : 0 < B) (hB1 : B ≤ 1)
    (h𝔠d : 𝔠d ≤ 1 / 2) (hcon : B ^ 𝔠d ≤ (1 - T) / (1 - s)) :
    (1 - s) / (1 - T) * B ≤ B ^ (1 / 2 : ℝ) := by
  have h1 : (1 - s) / (1 - T) ≤ B ^ (-𝔠d) := by
    calc (1 - s) / (1 - T) = ((1 - T) / (1 - s))⁻¹ := (inv_div _ _).symm
      _ ≤ (B ^ 𝔠d)⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hB0 _) hcon
      _ = B ^ (-𝔠d) := (Real.rpow_neg hB0.le _).symm
  calc (1 - s) / (1 - T) * B ≤ B ^ (-𝔠d) * B := mul_le_mul_of_nonneg_right h1 hB0.le
    _ = B ^ (-𝔠d + 1) := by rw [Real.rpow_add hB0, Real.rpow_one]
    _ ≤ B ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hB0 hB1 (by linarith)

end Sections

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Sections2

variable {d : ℕ} (sz : Sizes d)

/-- **The size of `λ`**: for large `n`, `λ_n ≤ B_T^{1/2}` and `√λ_n ≤ W^{-ε₀}`, `ε₀ = d c/4`
(from `B_T ≤ N^{-c}` and `B_T^{𝔠_d} ≤ (1-T)/(1-s)`, `𝔠_d ≤ 1/2`). -/
theorem OptL2a_lam_facts {s T : ℕ → ℝ} {c 𝔠d ε₀ : ℝ} (hc : 0 < c) (hε₀ : ε₀ = (d : ℝ) * c / 4)
    (h𝔠d : 𝔠d ≤ 1 / 2) (hT1 : ∀ n, T n < 1)
    (hbd : ∀ᶠ n in atTop, sz.Bctl n (T n) ≤ ((sz.size n : ℕ) : ℝ) ^ (-c))
    (hcon : ∀ᶠ n in atTop, (sz.Bctl n (T n)) ^ 𝔠d ≤ (1 - T n) / (1 - s n)) :
    ∀ᶠ n in atTop, OptL2alam sz s T n ≤ (sz.Bctl n (T n)) ^ (1 / 2 : ℝ) ∧
      Real.sqrt (OptL2alam sz s T n) ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀) := by
  filter_upwards [hbd, hcon] with n hn hc'
  have hBT : 0 < sz.Bctl n (T n) := STBctl_pos sz n (hT1 n)
  have hB1 : sz.Bctl n (T n) ≤ 1 :=
    hn.trans (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast sz.one_le_size n)
      (by linarith))
  have h1 := OptL2a_lam_le_sqrt (s := s n) (T := T n) hBT hB1 h𝔠d hc'
  refine ⟨h1, ?_⟩
  have h2 : Real.sqrt (OptL2alam sz s T n) ≤ (sz.Bctl n (T n)) ^ (1 / 4 : ℝ) := by
    calc Real.sqrt (OptL2alam sz s T n) ≤ Real.sqrt ((sz.Bctl n (T n)) ^ (1 / 2 : ℝ)) :=
          Real.sqrt_le_sqrt h1
      _ = (sz.Bctl n (T n)) ^ (1 / 4 : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hBT.le]; norm_num
  have h3 := ST_quarter_le sz n hBT.le hc.le hn
  rw [hε₀]
  exact h2.trans h3

/-- `N^{-m} ≤ λ^p` from `λ ≥ c_B N⁻¹` and `N^{-(m-p)} ≤ c_B^p` (`0 < p ≤ m`). -/
theorem OptL2a_floor {lam cB N p m : ℝ} (hcB : 0 < cB) (hN : 1 ≤ N) (hlam : cB * N⁻¹ ≤ lam)
    (hp : 0 < p) (hsm : N ^ (-(m - p)) ≤ cB ^ p) : N ^ (-m) ≤ lam ^ p := by
  have hN0 : 0 < N := by linarith
  have h0 : 0 ≤ cB * N⁻¹ := by positivity
  calc N ^ (-m) = N ^ (-(m - p)) * N ^ (-p) := by rw [← Real.rpow_add hN0]; congr 1; ring
    _ ≤ cB ^ p * N ^ (-p) := mul_le_mul_of_nonneg_right hsm (Real.rpow_nonneg hN0.le _)
    _ = (cB * N⁻¹) ^ p := by rw [Real.mul_rpow hcB.le (inv_nonneg.mpr hN0.le), Real.inv_rpow hN0.le,
          Real.rpow_neg hN0.le]
    _ ≤ lam ^ p := Real.rpow_le_rpow h0 hlam hp.le

/-- `ρ ≤ B^{-1/2}` from the first conjunct of `(con_st_ind)`. -/
theorem OptL2a_rho_le {s T B 𝔠d : ℝ} (hB0 : 0 < B) (hB1 : B ≤ 1) (h𝔠d : 𝔠d ≤ 1 / 2)
    (hcon : B ^ 𝔠d ≤ (1 - T) / (1 - s)) : (1 - s) / (1 - T) ≤ B ^ (-(1 / 2 : ℝ)) := by
  calc (1 - s) / (1 - T) = ((1 - T) / (1 - s))⁻¹ := (inv_div _ _).symm
    _ ≤ (B ^ 𝔠d)⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hB0 _) hcon
    _ = B ^ (-𝔠d) := (Real.rpow_neg hB0.le _).symm
    _ ≤ B ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_ge hB0 hB1 (by linarith)

/-- `λ = w⁴`, `w = λ^{1/4}`: `w² = √λ`, `w⁵ = λ^{5/4}`, `w^{10} = λ^{5/2}`, `w⁶ = λ^{3/2}`. -/
theorem OptL2a_w_pow {lam : ℝ} (h : 0 < lam) :
    (lam ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt lam ∧ (lam ^ (1 / 4 : ℝ)) ^ 5 = lam ^ (5 / 4 : ℝ) ∧
      (lam ^ (1 / 4 : ℝ)) ^ 10 = lam ^ (5 / 2 : ℝ) ∧ (lam ^ (1 / 4 : ℝ)) ^ 6 = lam ^ (3 / 2 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul h.le, Real.sqrt_eq_rpow]; norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul h.le]; norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul h.le]; norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul h.le]; norm_num

/-- `(lokis2)` in Lean: `((1-s)/(1-u))^{k-1} (W^{-d}B_{s,0})^{k-1} ≤ λ` at `k = 2`, `u ∈ [s,T]`. -/
theorem OptL2a_loop_ctl (n : ℕ) {s T : ℕ → ℝ} {u : ℝ} (hsu : s n ≤ u) (huT : u ≤ T n) (hT1 : T n < 1) :
    ((1 - s n) / (1 - u)) ^ (2 - 1) * (sz.Bctl n (s n)) ^ (2 - 1) ≤ OptL2alam sz s T n := by
  norm_num only [pow_one]
  unfold OptL2alam
  have hs1 : s n < 1 := by linarith
  have h1 : (1 - s n) / (1 - u) ≤ (1 - s n) / (1 - T n) :=
    div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
  have h2 := STBctl_mono sz n (hsu.trans huT) hT1
  have hb0 := (STBctl_pos sz n hs1).le
  exact mul_le_mul h1 h2 hb0 (div_nonneg (by linarith) (by linarith))

/-- **The premises of `lem:LWterm` and `lem: EMn2_N` at a time section `tt_n ∈ [s_n, T_n]`**, with the
control `Ψ = min(√λ, W^{-ε₀})`: `(eq:Psi)` (`OptL2a_psiClass_const`); `(initialGT2)`: the weak law of
Step 1 (`ε₀ = d c/4`) and `(lokis2)` (`STStep1Loop` at `k = 2`, `((1-s)/(1-u)) B_s ≤ λ`);
`(eq:LW_assm)`: `(lokis2)`.  `STConStInd` enters through its first conjunct
`B_T^{𝔠_d} ≤ (1-T)/(1-s)` only (it gives `√λ ≤ W^{-ε₀}` for large `n`). -/
theorem OptL2a_premises (hd0 : 0 < d)
    {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s T : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hsT : ∀ n, s n ≤ T n)
    (hTT : ∀ n, T n ≤ lemT (z n))
    (hS1L : STStep1Loop sz (STflowE z) s T) (hS1W : STStep1Weak sz (STflowE z) s T)
    {cB c 𝔠d ε₀ : ℝ} (hcB : 0 < cB) (hc : 0 < c) (hc1 : c ≤ 1) (hε₀ : ε₀ = (d : ℝ) * c / 4)
    (hBd : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ T n →
      cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c))
    (h𝔠d : 𝔠d ≤ 1 / 2)
    (hcon : ∀ᶠ n in atTop, (sz.Bctl n (T n)) ^ 𝔠d ≤ (1 - T n) / (1 - s n))
    (tt : ∀ n, TimeIcc s T n) :
    STPsiClass sz ε₀ (fun n _ => OptL2aPsi sz ε₀ s T n) ∧
      STInitialGT2 sz (STflowE z) (fun n => (tt n : ℝ)) ε₀ (fun n => OptL2aPsi sz ε₀ s T n) ∧
      STLWassm sz (STflowE z) (fun n => (tt n : ℝ)) (fun n _ => OptL2aPsi sz ε₀ s T n) := by
  classical
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hWt := ST_W_tendsto sz hsz hflow.1.1 hflow.1.2.2.2.1
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd0
  have hε₀pos : 0 < ε₀ := by rw [hε₀]; positivity
  have hε₀d : ε₀ ≤ (d : ℝ) / 2 := by rw [hε₀]; nlinarith
  have hT1 : ∀ n, T n < 1 := fun n =>
    lt_of_le_of_lt (hTT n) (lemT_lt_one (ST_flow_im_pos sz hflow n))
  have hs1 : ∀ n, s n < 1 := fun n => lt_of_le_of_lt (hsT n) (hT1 n)
  have hBT : ∀ n, 0 < sz.Bctl n (T n) := fun n => STBctl_pos sz n (hT1 n)
  have hlam : ∀ n, 0 < OptL2alam sz s T n := fun n =>
    mul_pos (div_pos (by linarith [hs1 n]) (by linarith [hT1 n])) (hBT n)
  have hρ1 : ∀ n, 1 ≤ (1 - s n) / (1 - T n) := fun n => by
    rw [le_div_iff₀ (by linarith [hT1 n])]; linarith [hsT n]
  have hWpos : ∀ n, (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.W_pos n
  have hΨpos : ∀ n, 0 < OptL2aPsi sz ε₀ s T n := fun n =>
    lt_min (Real.sqrt_pos.2 (hlam n)) (Real.rpow_pos_of_pos (hWpos n) _)
  have hΨle : ∀ n, OptL2aPsi sz ε₀ s T n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀) := fun n => min_le_right _ _
  have hbd : ∀ᶠ n in atTop, cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n (T n) ∧
      sz.Bctl n (T n) ≤ ((sz.size n : ℕ) : ℝ) ^ (-c) := by
    filter_upwards [hBd] with n hn using hn (T n) ((hs n).trans (hsT n)) le_rfl
  have hsq : ∀ᶠ n in atTop, Real.sqrt (OptL2alam sz s T n) ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀) :=
    (OptL2a_lam_facts sz hc hε₀ h𝔠d hT1 (hbd.mono fun n hn => hn.2) hcon).mono fun n hn => hn.2
  have hΨeq : ∀ᶠ n in atTop, OptL2aPsi sz ε₀ s T n = Real.sqrt (OptL2alam sz s T n) := by
    filter_upwards [hsq] with n hn using min_eq_left hn
  have hΨsq : ∀ᶠ n in atTop, (OptL2aPsi sz ε₀ s T n) ^ 2 = OptL2alam sz s T n := by
    filter_upwards [hΨeq] with n hn
    rw [hn, Real.sq_sqrt (hlam n).le]
  -- the window `W^{-d/2} ≲ Ψ`
  have hwin : ∀ᶠ n in atTop, min 1 (Real.sqrt cB) * ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤
      OptL2aPsi sz ε₀ s T n := by
    filter_upwards [hbd, hWt.eventually (eventually_ge_atTop 1)] with n hn hW1
    have hW := hWpos n
    have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
    have hc0 : 0 ≤ min 1 (Real.sqrt cB) := (lt_min one_pos (Real.sqrt_pos.2 hcB)).le
    have hn0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg hW.le _
    refine le_min ?_ ?_
    · rw [ST_rpow_neg_half hW.le]
      calc min 1 (Real.sqrt cB) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ)
          ≤ Real.sqrt cB * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ) := by
            refine mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg (by positivity) _)
        _ = Real.sqrt (cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) := by
            rw [Real.sqrt_mul hcB.le, Real.sqrt_eq_rpow (((sz.W n : ℕ) : ℝ) ^ d)⁻¹]
        _ ≤ Real.sqrt (OptL2alam sz s T n) := by
            refine Real.sqrt_le_sqrt ?_
            calc cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n (T n) := hn.1
              _ = 1 * sz.Bctl n (T n) := (one_mul _).symm
              _ ≤ OptL2alam sz s T n := mul_le_mul_of_nonneg_right (hρ1 n) (hBT n).le
    · calc min 1 (Real.sqrt cB) * ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)
          ≤ 1 * ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hn0
        _ = ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) := one_mul _
        _ ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀) :=
            Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hPsi : STPsiClass sz ε₀ (fun n _ => OptL2aPsi sz ε₀ s T n) :=
    OptL2a_psiClass_const sz _ hΨpos hΨle (c0 := min 1 (Real.sqrt cB))
      (lt_min one_pos (Real.sqrt_pos.2 hcB)) (min_le_left _ _) hwin
  -- the size data at the section
  have hbdtt : ∀ᶠ n in atTop, cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n (tt n : ℝ) ∧
      sz.Bctl n (tt n : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-c) := by
    filter_upwards [hBd] with n hn
    exact hn (tt n : ℝ) ((hs n).trans (tt n).2.1) (tt n).2.2
  have hbpos : ∀ n, 0 ≤ sz.Bctl n (tt n : ℝ) := fun n =>
    (STBctl_pos sz n (lt_of_le_of_lt (tt n).2.2 (hT1 n))).le
  -- `(initialGT2)` at the section
  have hInit1 : sz.Prec (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖STGM sz n (STflowE z n) (tt n : ℝ) ω p.1 p.2‖)
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) := by
    have h1 := StochDomAt.precomp_param
      (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) hS1W
      (fun n p => (tt n, p.1, p.2))
    refine ST_prec_mono_eventually sz ?_ h1
    filter_upwards [hbdtt] with n hn u ω
    have := ST_quarter_le sz n (hbpos n) hc.le hn.2
    rw [hε₀]
    exact this
  have hInit2 : sz.Prec (U := fun _ => Unit)
      (fun n _ ω => STmaxLoop2 sz n (STflowE z n) (tt n : ℝ) ω)
      (fun n _ _ => (OptL2aPsi sz ε₀ s T n) ^ 2) := by
    have h1 := hS1L 2 (by norm_num)
    have h2 := StochDomAt.precomp_param (V := fun n => Zd d (sz.L n) × Zd d (sz.L n)) h1
      (fun n p => (tt n, ![false, true], ![p.1, p.2]))
    have h3 : sz.Prec (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
        (fun n p ω => ‖Lloop sz n (STflowE z n) (tt n : ℝ) ![false, true] ![p.1, p.2] ω‖)
        (fun n _ _ => (OptL2aPsi sz ε₀ s T n) ^ 2) := by
      refine ST_prec_mono_eventually sz ?_ h2
      filter_upwards [hΨsq] with n hn u ω
      show ((1 - s n) / (1 - (tt n : ℝ))) ^ (2 - 1) * (sz.Bctl n (s n)) ^ (2 - 1) ≤ _
      rw [hn]
      exact OptL2a_loop_ctl sz n (tt n).2.1 (tt n).2.2 (hT1 n)
    exact ST_prec_sup sz _ _ h3
  have hinit : STInitialGT2 sz (STflowE z) (fun n => (tt n : ℝ)) ε₀ (fun n => OptL2aPsi sz ε₀ s T n) :=
    ⟨hInit1, hInit2⟩
  have hassm : STLWassm sz (STflowE z) (fun n => (tt n : ℝ)) (fun n _ => OptL2aPsi sz ε₀ s T n) := by
    have h1 := hS1L 2 (by norm_num)
    have h2 := StochDomAt.precomp_param
      (V := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n))) h1
      (fun n p => (tt n, p.1.1, p.2))
    refine ST_prec_mono_eventually sz ?_ h2
    filter_upwards [hΨsq] with n hn u ω
    show ((1 - s n) / (1 - (tt n : ℝ))) ^ (2 - 1) * (sz.Bctl n (s n)) ^ (2 - 1) ≤ _
    rw [hn]
    exact OptL2a_loop_ctl sz n (tt n).2.1 (tt n).2.2 (hT1 n)
  exact ⟨hPsi, hinit, hassm⟩

/-- **`lem:LWterm` at a time section** (conclusion of `STLWB` at the premises `OptL2a_premises`):
`𝓔^{G̃,(2)}_{tt,σ,a} ≺ η⁻¹ Ψ³`. -/
theorem OptL2a_sections_lw (hd0 : 0 < d) (hLWB : STLWB d)
    {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s T : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hsT : ∀ n, s n ≤ T n)
    (hTT : ∀ n, T n ≤ lemT (z n))
    (hS1L : STStep1Loop sz (STflowE z) s T) (hS1W : STStep1Weak sz (STflowE z) s T)
    {cB c 𝔠d ε₀ : ℝ} (hcB : 0 < cB) (hc : 0 < c) (hc1 : c ≤ 1) (hε₀ : ε₀ = (d : ℝ) * c / 4)
    (hBd : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ T n →
      cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c))
    (h𝔠d : 𝔠d ≤ 1 / 2)
    (hcon : ∀ᶠ n in atTop, (sz.Bctl n (T n)) ^ 𝔠d ≤ (1 - T n) / (1 - s n))
    (tt : ∀ n, TimeIcc s T n) :
    sz.Prec (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
        (fun n p ω => ‖STEGt sz n (STflowE z n) (tt n : ℝ) p.1 p.2 ω‖)
        (fun n _ _ => (etaT (STflowE z n) (tt n : ℝ))⁻¹ * OptL2aPsi sz ε₀ s T n *
          (OptL2aPsi sz ε₀ s T n) ^ 2) := by
  obtain ⟨hPsi, hinit, hassm⟩ := OptL2a_premises sz hd0 hκ hε h𝔡 hflow hs hsT hTT hS1L hS1W hcB hc hc1
    hε₀ hBd h𝔠d hcon tt
  have hε₀pos : 0 < ε₀ := by
    have : (0 : ℝ) < d := by exact_mod_cast hd0
    rw [hε₀]; positivity
  exact hLWB κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow (fun n => (tt n : ℝ)) (fun n => (hs n).trans (tt n).2.1)
    (fun n => (tt n).2.2.trans (hTT n)) ε₀ hε₀pos (fun n _ => OptL2aPsi sz ε₀ s T n) hPsi hinit hassm

/-- **`lem: EMn2_N`, first estimate `(eq:MG_conclusion)`, at a time section** (`stEMn2Poly_holds` at the
premises `OptL2a_premises`): `(𝓔⊗𝓔)^{M,(2;k)}_{tt,σ,a,a} ≺ η⁻¹ Ψ⁵`.  No light-weight pin is used. -/
theorem OptL2a_sections_mg (hd0 : 0 < d)
    {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s T : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hsT : ∀ n, s n ≤ T n)
    (hTT : ∀ n, T n ≤ lemT (z n))
    (hS1L : STStep1Loop sz (STflowE z) s T) (hS1W : STStep1Weak sz (STflowE z) s T)
    {cB c 𝔠d ε₀ : ℝ} (hcB : 0 < cB) (hc : 0 < c) (hc1 : c ≤ 1) (hε₀ : ε₀ = (d : ℝ) * c / 4)
    (hBd : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ T n →
      cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c))
    (h𝔠d : 𝔠d ≤ 1 / 2)
    (hcon : ∀ᶠ n in atTop, (sz.Bctl n (T n)) ^ 𝔠d ≤ (1 - T n) / (1 - s n))
    (tt : ∀ n, TimeIcc s T n) :
    sz.Prec (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
        (fun n p ω => ‖STEEk sz n (STflowE z n) (tt n : ℝ) p.1 p.2.1 p.2.2 ω‖)
        (fun n _ _ => (etaT (STflowE z n) (tt n : ℝ))⁻¹ * OptL2aPsi sz ε₀ s T n *
          (OptL2aPsi sz ε₀ s T n) ^ 4) := by
  obtain ⟨hPsi, hinit, hassm⟩ := OptL2a_premises sz hd0 hκ hε h𝔡 hflow hs hsT hTT hS1L hS1W hcB hc hc1
    hε₀ hBd h𝔠d hcon tt
  have hε₀pos : 0 < ε₀ := by
    have : (0 : ℝ) < d := by exact_mod_cast hd0
    rw [hε₀]; positivity
  exact stEMn2Poly_holds d κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow (fun n => (tt n : ℝ))
    (fun n => (hs n).trans (tt n).2.1) (fun n => (tt n).2.2.trans (hTT n)) ε₀ hε₀pos
    (fun n _ => OptL2aPsi sz ε₀ s T n) hPsi hinit hassm

end Sections2

end RBM.Gauss.Sizes

/-! ## 3. The `w.h.p.` events on the grid -/

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

section Events2

variable {d : ℕ} (sz : Sizes d)

/-- **The light-weight term on the grid** (`lem:LWterm` at every grid time, `(l>0EQ)`, `3_5:474`):
`|𝓔^{G̃,(2)}_{u_j,σ,a}| ≤ N^{ε₁} η_{u_j}⁻¹ Ψ³` for all `j ≤ K_n` and all labels, w.h.p. -/
theorem OptL2a_event_lw (hd0 : 0 < d) (hLWB : STLWB d)
    {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s T : ℕ → ℝ} (K : ℕ → ℕ) (hs : ∀ n, 0 ≤ s n)
    (hsT : ∀ n, s n ≤ T n) (hK : ∀ n, K n ≠ 0) (hTT : ∀ n, T n ≤ lemT (z n))
    (hS1L : STStep1Loop sz (STflowE z) s T) (hS1W : STStep1Weak sz (STflowE z) s T)
    {cB c 𝔠d ε₀ : ℝ} (hcB : 0 < cB) (hc : 0 < c) (hc1 : c ≤ 1) (hε₀ : ε₀ = (d : ℝ) * c / 4)
    (hBd : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ T n →
      cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c))
    (h𝔠d : 𝔠d ≤ 1 / 2)
    (hcon : ∀ᶠ n in atTop, (sz.Bctl n (T n)) ^ 𝔠d ≤ (1 - T n) / (1 - s n))
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hcard : ∀ᶠ n in atTop, ((((K n + 1) * Fintype.card (STLab sz n) : ℕ)) : ℝ) ≤
      ((sz.size n : ℕ) : ℝ) ^ C₁)
    {ε₁ : ℝ} (hε₁ : 0 < ε₁) :
    Gauss.HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ j, j ≤ K n → ∀ i : STLab sz n,
      ‖STEGtM sz n (STflowE z n) (gridTime s T K n j) (pathH sz s T K n j ω) i.1 i.2‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₁ * ((etaT (STflowE z n) (gridTime s T K n j))⁻¹ *
          OptL2aPsi sz ε₀ s T n * (OptL2aPsi sz ε₀ s T n) ^ 2)}) := by
  have hmain := ST_grid_whp_of_sections sz (V := fun n => STLab sz n) s T K hs hsT hK hC₁ hcard
    (fun n v u H => ‖STEGtM sz n (STflowE z n) u H v.1 v.2‖)
    (fun n v u H => (etaT (STflowE z n) u)⁻¹ * OptL2aPsi sz ε₀ s T n * (OptL2aPsi sz ε₀ s T n) ^ 2)
    (fun n v u => (STEGtM_measurable sz n (STflowE z n) u v.1 v.2).norm)
    (fun n v u => measurable_const) ε₁ hε₁ (fun tt =>
      (OptL2a_sections_lw sz hd0 hLWB hκ hε h𝔡 hflow hs hsT hTT hS1L hS1W hcB hc hc1 hε₀ hBd h𝔠d hcon
        tt))
  refine hmain.mono (Eventually.of_forall fun n => ?_)
  intro ω hω j hj i
  exact hω j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) i

/-- **The quadratic variation on the grid** (`lem: EMn2_N`, first estimate `(eq:MG_conclusion)`, at
every grid time): `|(𝓔⊗𝓔)^{M,(2)}_{u_j,σ,a}| ≤ 2 N^{ε₁} η_{u_j}⁻¹ Ψ⁵` for all `j ≤ K_n` and all labels,
w.h.p. (`(𝓔⊗𝓔)^{M,(2)}` is the sum of the two cuts `k = 1, 2`). -/
theorem OptL2a_event_mg (hd0 : 0 < d)
    {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s T : ℕ → ℝ} (K : ℕ → ℕ) (hs : ∀ n, 0 ≤ s n)
    (hsT : ∀ n, s n ≤ T n) (hK : ∀ n, K n ≠ 0) (hTT : ∀ n, T n ≤ lemT (z n))
    (hS1L : STStep1Loop sz (STflowE z) s T) (hS1W : STStep1Weak sz (STflowE z) s T)
    {cB c 𝔠d ε₀ : ℝ} (hcB : 0 < cB) (hc : 0 < c) (hc1 : c ≤ 1) (hε₀ : ε₀ = (d : ℝ) * c / 4)
    (hBd : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ T n →
      cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c))
    (h𝔠d : 𝔠d ≤ 1 / 2)
    (hcon : ∀ᶠ n in atTop, (sz.Bctl n (T n)) ^ 𝔠d ≤ (1 - T n) / (1 - s n))
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hcard : ∀ᶠ n in atTop, ((((K n + 1) * Fintype.card (Fin 2 × STLab sz n) : ℕ)) : ℝ) ≤
      ((sz.size n : ℕ) : ℝ) ^ C₁)
    {ε₁ : ℝ} (hε₁ : 0 < ε₁) :
    Gauss.HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ j, j ≤ K n → ∀ i : STLab sz n,
      ‖STEEM sz n (STflowE z n) (gridTime s T K n j) (pathH sz s T K n j ω) i.1 i.2‖ ≤
        2 * ((sz.size n : ℕ) : ℝ) ^ ε₁ * ((etaT (STflowE z n) (gridTime s T K n j))⁻¹ *
          OptL2aPsi sz ε₀ s T n * (OptL2aPsi sz ε₀ s T n) ^ 4)}) := by
  have hmain := ST_grid_whp_of_sections sz (V := fun n => Fin 2 × STLab sz n) s T K hs hsT hK hC₁
    hcard
    (fun n v u H => ‖STEEkM sz n (STflowE z n) u H v.1 v.2.1 v.2.2‖)
    (fun n v u H => (etaT (STflowE z n) u)⁻¹ * OptL2aPsi sz ε₀ s T n * (OptL2aPsi sz ε₀ s T n) ^ 4)
    (fun n v u => (STEEkM_measurable sz n (STflowE z n) u v.1 v.2.1 v.2.2).norm)
    (fun n v u => measurable_const) ε₁ hε₁ (fun tt =>
      (OptL2a_sections_mg sz hd0 hκ hε h𝔡 hflow hs hsT hTT hS1L hS1W hcB hc hc1 hε₀ hBd h𝔠d hcon
        tt))
  refine hmain.mono (Eventually.of_forall fun n => ?_)
  intro ω hω j hj i
  have hj' := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have h0 := hω j hj' (0, i)
  have h1 := hω j hj' (1, i)
  calc ‖STEEM sz n (STflowE z n) (gridTime s T K n j) (pathH sz s T K n j ω) i.1 i.2‖
      ≤ ‖STEEkM sz n (STflowE z n) (gridTime s T K n j) (pathH sz s T K n j ω) 0 i.1 i.2‖ +
        ‖STEEkM sz n (STflowE z n) (gridTime s T K n j) (pathH sz s T K n j ω) 1 i.1 i.2‖ :=
        norm_add_le _ _
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ * ((etaT (STflowE z n) (gridTime s T K n j))⁻¹ *
          OptL2aPsi sz ε₀ s T n * (OptL2aPsi sz ε₀ s T n) ^ 4) +
        ((sz.size n : ℕ) : ℝ) ^ ε₁ * ((etaT (STflowE z n) (gridTime s T K n j))⁻¹ *
          OptL2aPsi sz ε₀ s T n * (OptL2aPsi sz ε₀ s T n) ^ 4) := add_le_add h0 h1
    _ = _ := by ring

end Events2

end RBM.Gauss.Sizes

/-! ## 4. The probability bookkeeping and the real arithmetic of the final comparison -/

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

section Arith2

/-- **The failure probability of the good event**: a `w.h.p.` event `Ξ`, the union of the
martingale tail events `B n v` (probability `N^{-D_m}` each, at most `N^3` labels), and a null set. -/
theorem OptL2a_prob_combine {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (size : ℕ → ℕ)
    (hsize : Tendsto size atTop atTop) {V : ℕ → Type} [∀ n, Fintype (V n)]
    (Ξ : ℕ → Set Ω) (hΞ : Gauss.HighProbAt P size Ξ) (B : ∀ n, V n → Set Ω) (Nl : ℕ → Set Ω)
    {D' Dm : ℝ} (hD' : 0 < D') (hDm : D' + 1 + 3 ≤ Dm)
    (hB : ∀ᶠ n in atTop, ∀ v, P (B n v) ≤ ENNReal.ofReal ((size n : ℝ) ^ (-Dm)))
    (hcard : ∀ᶠ n in atTop, (Fintype.card (V n) : ℝ) ≤ (size n : ℝ) ^ (3 : ℝ))
    (hNl : ∀ᶠ n in atTop, P (Nl n) = 0) (S : ℕ → Set Ω)
    (hS : ∀ᶠ n in atTop, S n ⊆ ((Ξ n)ᶜ ∪ ⋃ v, B n v) ∪ Nl n) :
    ∀ᶠ n in atTop, P (S n) ≤ ENNReal.ofReal ((size n : ℝ) ^ (-D')) := by
  filter_upwards [hΞ (D' + 1) (by linarith), hB, hcard,
    hsize.eventually (eventually_two_mul_rpow_le D'), hsize.eventually (eventually_ge_atTop 1),
    hNl, hS] with n h1 hBn hcn h2 hN1 hNln hSn
  have hN1' : (1 : ℝ) ≤ (size n : ℝ) := by exact_mod_cast hN1
  have hU := ST_union_prob P (B n) hN1' hcn (a := D' + 1) hDm hBn
  have hp : (0 : ℝ) ≤ (size n : ℝ) ^ (-(D' + 1)) := Real.rpow_nonneg (by positivity) _
  calc P (S n) ≤ P (((Ξ n)ᶜ ∪ ⋃ v, B n v) ∪ Nl n) := measure_mono hSn
    _ ≤ P ((Ξ n)ᶜ ∪ ⋃ v, B n v) + P (Nl n) := measure_union_le _ _
    _ = P ((Ξ n)ᶜ ∪ ⋃ v, B n v) := by rw [hNln, add_zero]
    _ ≤ P (Ξ n)ᶜ + P (⋃ v, B n v) := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((size n : ℝ) ^ (-(D' + 1))) + ENNReal.ofReal ((size n : ℝ) ^ (-(D' + 1))) :=
        add_le_add h1 hU
    _ = ENNReal.ofReal (2 * (size n : ℝ) ^ (-(D' + 1))) := by
        rw [← ENNReal.ofReal_add hp hp]; congr 1; ring
    _ ≤ ENNReal.ofReal ((size n : ℝ) ^ (-D')) := ENNReal.ofReal_le_ofReal h2

/-- The martingale term: `M (2MΨ⁵x + N^{-D_m})^{1/2} ≤ 2 M² w⁵` for `Ψ ≤ w²`, `N^{-D_m} ≤ w^{10}`,
`x ≤ M` (`w = λ^{1/4}`; `(Σ_j Δ W^{-5c₀/2}/η_{u_j})^{1/2} ≺ W^{-5c₀/4}`, `3_5:476-478`). -/
theorem OptL2a_mart_arith {M w Ψ x Nm : ℝ} (hM : 1 ≤ M) (hw0 : 0 < w) (hΨ0 : 0 < Ψ)
    (hΨw : Ψ ≤ w ^ 2) (hx0 : 0 ≤ x) (hxM : x ≤ M) (hNm0 : 0 ≤ Nm) (hNm : Nm ≤ w ^ 10) :
    M * (2 * M * Ψ ^ 5 * x + Nm) ^ (1 / 2 : ℝ) ≤ 2 * M ^ 2 * w ^ 5 := by
  have hM0 : 0 < M := by linarith
  have hΨ5 : Ψ ^ 5 ≤ w ^ 10 := by
    calc Ψ ^ 5 ≤ (w ^ 2) ^ 5 := pow_le_pow_left₀ hΨ0.le hΨw 5
      _ = w ^ 10 := by ring
  have hy : 2 * M * Ψ ^ 5 * x + Nm ≤ (2 * M * w ^ 5) ^ 2 := by
    have h1 : 2 * M * Ψ ^ 5 * x ≤ 2 * M * w ^ 10 * M :=
      mul_le_mul (mul_le_mul_of_nonneg_left hΨ5 (by positivity)) hxM hx0 (by positivity)
    have h2 : (2 * M * w ^ 5) ^ 2 = 4 * M ^ 2 * w ^ 10 := by ring
    rw [h2]
    have h3 : 0 ≤ w ^ 10 := by positivity
    nlinarith [mul_nonneg h3 (by nlinarith : (0 : ℝ) ≤ M ^ 2 - 1)]
  have hy0 : 0 ≤ 2 * M * Ψ ^ 5 * x + Nm := by positivity
  have hT4 : (2 * M * Ψ ^ 5 * x + Nm) ^ (1 / 2 : ℝ) ≤ 2 * M * w ^ 5 := by
    rw [← Real.sqrt_eq_rpow]
    calc Real.sqrt (2 * M * Ψ ^ 5 * x + Nm) ≤ Real.sqrt ((2 * M * w ^ 5) ^ 2) :=
          Real.sqrt_le_sqrt hy
      _ = 2 * M * w ^ 5 := Real.sqrt_sq (by positivity)
  calc M * (2 * M * Ψ ^ 5 * x + Nm) ^ (1 / 2 : ℝ) ≤ M * (2 * M * w ^ 5) :=
        mul_le_mul_of_nonneg_left hT4 hM0.le
    _ = 2 * M ^ 2 * w ^ 5 := by ring

/-- `2 M² ≤ M⁸` for `M ≥ 2`. -/
theorem OptL2a_two_sq_le {M : ℝ} (hM : 2 ≤ M) : 2 * M ^ 2 ≤ M ^ 8 := by
  have h6 : (4 : ℝ) ≤ M ^ 6 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hM 6]
  have : M ^ 8 = M ^ 6 * M ^ 2 := by ring
  rw [this]; nlinarith [sq_nonneg M]

/-- The final comparison of `(eq:L-K2max)`'s `α`: the initial value `M B²`, the remainder
`r ≤ w⁵`, the light-weight sum `M Y x` (`Y ≤ w⁵`, `x ≤ M`) and the martingale `M_b ≤ M⁴ w⁵` are at
most `M⁸ (B² + w⁵)` for `M ≥ 2`. -/
theorem OptL2a_alpha_arith {M B2 w Y x r Mb : ℝ} (hM : 2 ≤ M) (hB2 : 0 ≤ B2) (hw0 : 0 < w)
    (hY : Y ≤ w ^ 5) (hx0 : 0 ≤ x) (hxM : x ≤ M) (hr : r ≤ w ^ 5)
    (hMb : Mb ≤ M ^ 4 * w ^ 5) :
    M * B2 + r + M * Y * x + Mb ≤ M ^ 8 * (B2 + w ^ 5) := by
  have hM0 : 0 < M := by linarith
  have hw5 : 0 ≤ w ^ 5 := by positivity
  have hT2 : M * Y * x ≤ M * w ^ 5 * M :=
    mul_le_mul (mul_le_mul_of_nonneg_left hY hM0.le) hxM hx0 (by positivity)
  have hM8 : M ≤ M ^ 8 := by
    have : M ^ 1 ≤ M ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
    simpa using this
  have hM4 : (16 : ℝ) ≤ M ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hM 4]
  have hM2 : (4 : ℝ) ≤ M ^ 2 := by nlinarith
  have hM42 : M ^ 2 ≤ M ^ 4 := by nlinarith
  have hA : r ≤ M ^ 4 * w ^ 5 := hr.trans (le_mul_of_one_le_left hw5 (by linarith))
  have hB : M * w ^ 5 * M ≤ M ^ 4 * w ^ 5 := by
    have : M * w ^ 5 * M = M ^ 2 * w ^ 5 := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hM42 hw5
  have hC : 3 * M ^ 4 ≤ M ^ 8 := by
    have : M ^ 8 = M ^ 4 * M ^ 4 := by ring
    rw [this]; nlinarith
  calc M * B2 + r + M * Y * x + Mb ≤ M * B2 + 3 * (M ^ 4 * w ^ 5) := by linarith
    _ ≤ M ^ 8 * B2 + M ^ 8 * w ^ 5 := by
        nlinarith [mul_le_mul_of_nonneg_right hM8 hB2, mul_le_mul_of_nonneg_right hC hw5]
    _ = M ^ 8 * (B2 + w ^ 5) := by ring

/-- `q log ρ ≤ N^{2ε'}`: `1 ≤ ρ ≤ B^{-1/2}`, `B ≥ c_B W^{-d}`, `W^d ≤ N` (the logarithmic time sum
`Δ Σ_j (1-u_j)⁻¹ ≤ log ρ` costs only a power `N^{ε}`). -/
theorem OptL2a_q_log_le {q ρ B cB Wd N ε' : ℝ} (hq : 0 ≤ q) (hε' : 0 < ε') (hcB : 0 < cB)
    (hN : 1 ≤ N) (hWd : 0 < Wd) (hWdN : Wd ≤ N)
    (hBlow : cB * Wd⁻¹ ≤ B) (hρ1 : 1 ≤ ρ) (hρB : ρ ≤ B ^ (-(1 / 2 : ℝ)))
    (hbig : q / 2 * (cB ^ (-ε') / ε') ≤ N ^ ε') :
    q * Real.log ρ ≤ N ^ (2 * ε') := by
  have hN0 : 0 < N := by linarith
  have hx0 : 0 < cB * Wd⁻¹ := mul_pos hcB (inv_pos.mpr hWd)
  have h1 : B ^ (-(1 / 2 : ℝ)) ≤ (N / cB) ^ (1 / 2 : ℝ) := by
    calc B ^ (-(1 / 2 : ℝ)) ≤ (cB * Wd⁻¹) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hx0 hBlow (by norm_num)
      _ = (Wd / cB) ^ (1 / 2 : ℝ) := by
          rw [Real.rpow_neg hx0.le, ← Real.inv_rpow hx0.le]
          congr 1; field_simp
      _ ≤ (N / cB) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hWdN hcB.le) (by norm_num)
  have hρ0 : 0 < ρ := by linarith
  have hNc : 0 < N / cB := div_pos hN0 hcB
  have h2 : Real.log ρ ≤ 1 / 2 * Real.log (N / cB) := by
    calc Real.log ρ ≤ Real.log ((N / cB) ^ (1 / 2 : ℝ)) :=
          Real.log_le_log hρ0 (hρB.trans h1)
      _ = 1 / 2 * Real.log (N / cB) := Real.log_rpow hNc _
  have h3 := Real.log_le_rpow_div hNc.le hε'
  have h4 : (N / cB) ^ ε' = N ^ ε' * cB ^ (-ε') := by
    rw [Real.div_rpow hN0.le hcB.le, Real.rpow_neg hcB.le, div_eq_mul_inv]
  have hNe : N ^ (2 * ε') = N ^ ε' * N ^ ε' := by
    rw [two_mul, Real.rpow_add hN0]
  calc q * Real.log ρ ≤ q * (1 / 2 * ((N / cB) ^ ε' / ε')) :=
        mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 (by norm_num))) hq
    _ = (q / 2 * (cB ^ (-ε') / ε')) * N ^ ε' := by rw [h4]; ring
    _ ≤ N ^ ε' * N ^ ε' :=
        mul_le_mul_of_nonneg_right hbig (Real.rpow_nonneg hN0.le _)
    _ = N ^ (2 * ε') := hNe.symm

end Arith2

end RBM.Gauss.Sizes

/-! ## 5. Size data, grid cardinalities -/

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

section SizeData

variable {d : ℕ} (sz : Sizes d)

/-- The size data `c_B W^{-d} ≤ W^{-d}B_{u,0} ≤ N^{-c}` of `ST_Bdata_holds` with `c ≤ 1`
(`c_B` free of the bandwidth exponent `𝔠`; `c` may be decreased). -/
theorem OptL2a_sizedata (hd0 : 0 < d) {κ ε 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) :
    ∃ cB : ℝ, 0 < cB ∧ ∀ 𝔠 : ℝ, ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z → ∀ T : ℕ → ℝ, (∀ n, 0 ≤ T n) →
        (∀ n, T n ≤ lemT (z n)) → ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ T n →
          cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧
            sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c) := by
  obtain ⟨cB, hcB, hcBd⟩ := ST_Bdata_holds hd0 κ ε 𝔡 hκ hε h𝔡
  refine ⟨cB, hcB, fun 𝔠 => ?_⟩
  obtain ⟨c0, hc0, hBd0⟩ := hcBd 𝔠
  refine ⟨min c0 1, lt_min hc0 one_pos, min_le_right _ _, fun sz z hflow T hT0 hTT => ?_⟩
  filter_upwards [hBd0 sz z hflow T hT0 hTT,
    (tendsto_size sz hflow.1.2.2.1).eventually (eventually_ge_atTop 1)] with n hn hN1 u hu0 huT
  refine ⟨(hn u hu0 huT).1, (hn u hu0 huT).2.trans ?_⟩
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith [min_le_left c0 1])

/-- The grid `K_n = ⌈N^{CK}⌉` is nonempty and at least `N^{CK}`. -/
theorem OptL2a_grid {CK : ℝ} (K : ℕ → ℕ) (hK : ∀ n, K n = ⌈((sz.size n : ℕ) : ℝ) ^ CK⌉₊) :
    (∀ n, K n ≠ 0) ∧ ∀ n, ((sz.size n : ℕ) : ℝ) ^ CK ≤ (K n : ℝ) := by
  refine ⟨fun n => ?_, fun n => ?_⟩
  · rw [hK n]
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    exact (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hN0 _)).ne'
  · rw [hK n]; exact Nat.le_ceil _

/-- The label sets of the grid events have polynomially many elements. -/
theorem OptL2a_cards (hsize : Tendsto sz.size atTop atTop) {CK : ℝ} (hCK : 0 ≤ CK) (K : ℕ → ℕ)
    (hK : ∀ n, K n = ⌈((sz.size n : ℕ) : ℝ) ^ CK⌉₊) :
    (∀ᶠ n in atTop, ((((K n + 1) *
      Fintype.card (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) : ℕ)) : ℝ) ≤
        ((sz.size n : ℕ) : ℝ) ^ (CK + 5)) ∧
    (∀ᶠ n in atTop, (Fintype.card (STLab sz n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ)) ∧
    (∀ᶠ n in atTop, ((((K n + 1) * Fintype.card (STLab sz n) : ℕ)) : ℝ) ≤
        ((sz.size n : ℕ) : ℝ) ^ (CK + 5)) ∧
    (∀ᶠ n in atTop, ((((K n + 1) * Fintype.card (Fin 2 × STLab sz n) : ℕ)) : ℝ) ≤
        ((sz.size n : ℕ) : ℝ) ^ (CK + 5)) := by
  have hN4 : ∀ᶠ n in atTop, 4 ≤ sz.size n := hsize.eventually (eventually_ge_atTop 4)
  have hLab3 : ∀ᶠ n in atTop,
      (Fintype.card (STLab sz n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) := by
    filter_upwards [hN4] with n hn using ST_card_lab_le sz n hn
  refine ⟨ST_hcard sz (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) hsize hCK
    K hK (by filter_upwards [hN4] with n hn
             exact ST_card_idx_prod_le sz n (by omega)), hLab3,
    ST_hcard sz (V := fun n => STLab sz n) hsize hCK K hK (by
      filter_upwards [hLab3, hN4] with n hn hN
      refine hn.trans (Real.rpow_le_rpow_of_exponent_le ?_ (by norm_num))
      exact_mod_cast (by omega : 1 ≤ sz.size n)),
    ST_hcard sz (V := fun n => Fin 2 × STLab sz n) hsize hCK K hK (by
      filter_upwards [hN4] with n hn using ST_card_fin2_lab_le sz n hn)⟩

end SizeData

end RBM.Gauss.Sizes

/-! ## 6. The pathwise Grönwall inequality on one sample -/

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

section Pathwise

variable {d : ℕ} (sz : Sizes d)

/-- `Δ Σ_{j<k} η_{u_j}⁻¹ ≤ q log((1-s)/(1-T))` along the grid (`Im m(E) ≥ q⁻¹`; the logarithmic time
sum `ST_logsum`, `3_5:481`). -/
theorem OptL2a_eta_sum {s T : ℕ → ℝ} (K : ℕ → ℕ) (n : ℕ) {E q : ℝ} (hsT : s n ≤ T n) (hT1 : T n < 1)
    (hK : K n ≠ 0) (hE2 : |E| < 2) (hq : ((mE E).im)⁻¹ ≤ q) {k : ℕ} (hk : k ≤ K n) :
    gridStep s T K n * ∑ j ∈ Finset.range k, (etaT E (gridTime s T K n j))⁻¹ ≤
      q * Real.log ((1 - s n) / (1 - T n)) := by
  have hΔ := ST_gridStep_nonneg s T K n hsT
  have hmemk := ST_gridTime_mem s T K n k hsT hK hk
  have hk1 : s n + (k : ℝ) * gridStep s T K n < 1 := by
    have := hmemk.2; unfold gridTime at this; linarith
  have hlog := ST_logsum hΔ k hk1
  have hmI : 0 < (mE E).im := mE_im_pos hE2
  have hq0 : 0 ≤ q := (inv_nonneg.mpr hmI.le).trans hq
  have hterm : ∀ j ∈ Finset.range k, (etaT E (gridTime s T K n j))⁻¹ ≤
      q * (1 - (s n + (j : ℝ) * gridStep s T K n))⁻¹ := by
    intro j hj
    have hjk : j ≤ K n := (Finset.mem_range.mp hj).le.trans hk
    have hmj := ST_gridTime_mem s T K n j hsT hK hjk
    have hu1 : gridTime s T K n j < 1 := lt_of_le_of_lt hmj.2 hT1
    have hpos : 0 < 1 - (s n + (j : ℝ) * gridStep s T K n) := by unfold gridTime at hu1; linarith
    unfold etaT gridTime
    rw [mul_inv]
    calc (1 - (s n + (j : ℝ) * gridStep s T K n))⁻¹ * ((mE E).im)⁻¹
        ≤ (1 - (s n + (j : ℝ) * gridStep s T K n))⁻¹ * q :=
          mul_le_mul_of_nonneg_left hq (inv_nonneg.mpr hpos.le)
      _ = q * (1 - (s n + (j : ℝ) * gridStep s T K n))⁻¹ := mul_comm _ _
  have hsk : s n + (k : ℝ) * gridStep s T K n ≤ T n := by
    have := hmemk.2; unfold gridTime at this; linarith
  have hs1 : 0 < 1 - s n := by linarith
  have hA : 0 < 1 - (s n + (k : ℝ) * gridStep s T K n) := by linarith
  calc gridStep s T K n * ∑ j ∈ Finset.range k, (etaT E (gridTime s T K n j))⁻¹
      ≤ gridStep s T K n * ∑ j ∈ Finset.range k, q * (1 - (s n + (j : ℝ) * gridStep s T K n))⁻¹ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) hΔ
    _ = q * (gridStep s T K n * ∑ j ∈ Finset.range k, (1 - (s n + (j : ℝ) * gridStep s T K n))⁻¹) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ q * Real.log ((1 - s n) / (1 - (s n + (k : ℝ) * gridStep s T K n))) :=
        mul_le_mul_of_nonneg_left hlog hq0
    _ ≤ q * Real.log ((1 - s n) / (1 - T n)) := by
        refine mul_le_mul_of_nonneg_left (Real.log_le_log (div_pos hs1 hA) ?_) hq0
        exact div_le_div_of_nonneg_left hs1.le (by linarith) (by linarith)

/-- `Σ_{j<k} Δ (a η_{u_j}⁻¹) ≤ a q Lg`, `Lg ≥ log((1-s)/(1-T))`. -/
theorem OptL2a_eta_sum_mul {s T : ℕ → ℝ} (K : ℕ → ℕ) (n : ℕ) {E q Lg a : ℝ} (hsT : s n ≤ T n)
    (hT1 : T n < 1) (hK : K n ≠ 0) (hE2 : |E| < 2) (hq : ((mE E).im)⁻¹ ≤ q)
    (hLg : Real.log ((1 - s n) / (1 - T n)) ≤ Lg) (ha : 0 ≤ a) {k : ℕ} (hk : k ≤ K n) :
    ∑ j ∈ Finset.range k, gridStep s T K n * (a * (etaT E (gridTime s T K n j))⁻¹) ≤
      a * (q * Lg) := by
  have hq0 : 0 ≤ q := (inv_nonneg.mpr (mE_im_pos hE2).le).trans hq
  have h := OptL2a_eta_sum K n hsT hT1 hK hE2 hq hk
  have h2 : q * Real.log ((1 - s n) / (1 - T n)) ≤ q * Lg := mul_le_mul_of_nonneg_left hLg hq0
  have hrew : ∑ j ∈ Finset.range k, gridStep s T K n * (a * (etaT E (gridTime s T K n j))⁻¹) =
      a * (gridStep s T K n * ∑ j ∈ Finset.range k, (etaT E (gridTime s T K n j))⁻¹) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hrew]
  exact mul_le_mul_of_nonneg_left (h.trans h2) ha

/-- **Targets 1-3 on one sample**: on the sample where the drift bound (Target 1), the initial value,
the martingale bound (Target 2), the remainder and the grid decomposition hold,
`J_k ≤ α + Δ Σ_{j<k} (C₀/(1-u_j)) J_j` for all `k ≤ K_n` (`(eq:Gronwall_2L_max)`, `3_5:481`). -/
theorem OptL2a_pathwise {κ C₀ : ℝ} (hκ : 0 < κ) (hC₀ : 0 ≤ C₀)
    (s T : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (E : ℝ) (hE : |E| ≤ 2 - κ) (hsT : s n ≤ T n)
    (hT1 : T n < 1) (hK : K n ≠ 0)
    (Mart Rem : STLab sz n → ℕ → PathΩ sz → ℂ) (ω : PathΩ sz)
    {a₀ r₀ Mx Y q Lg Mb α : ℝ} (ha₀ : 0 ≤ a₀) (hr₀ : 0 ≤ r₀) (hMx : 0 ≤ Mx) (hY : 0 ≤ Y)
    (hq : ((mE E).im)⁻¹ ≤ q) (hLg : Real.log ((1 - s n) / (1 - T n)) ≤ Lg)
    (hα : a₀ + r₀ + Mx * Y * (q * Lg) + Mb ≤ α)
    (hdrift : ∀ j, j ≤ K n → ∀ i : STLab sz n,
      ‖STgDrift sz s T K n E i.1 i.2 j ω‖ ≤ C₀ / (1 - gridTime s T K n j) *
          OptL2aJ sz n E (gridTime s T K n j) (pathH sz s T K n j ω) +
        Mx * ((etaT E (gridTime s T K n j))⁻¹ * Y))
    (hinit : ∀ i : STLab sz n, ‖STgA sz s T K n E i.1 i.2 0 ω‖ ≤ a₀)
    (hmart : ∀ i : STLab sz n, ∀ k, k ≤ K n → ‖Mart i k ω‖ ≤ Mb)
    (hrem : ∀ i : STLab sz n, ∀ k, k ≤ K n → ‖Rem i k ω‖ ≤ r₀)
    (hident : ∀ i : STLab sz n, ∀ k, k ≤ K n →
      STgA sz s T K n E i.1 i.2 k ω =
        STgA sz s T K n E i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDrift sz s T K n E i.1 i.2 j ω + Rem i k ω + Mart i k ω) :
    ∀ k, k ≤ K n →
      OptL2aJ sz n E (gridTime s T K n k) (pathH sz s T K n k ω) ≤
        α + gridStep s T K n * ∑ j ∈ Finset.range k, C₀ / (1 - gridTime s T K n j) *
          OptL2aJ sz n E (gridTime s T K n j) (pathH sz s T K n j ω) := by
  classical
  have hΔ := ST_gridStep_nonneg s T K n hsT
  have hE2 : |E| < 2 := by linarith
  have hmem : ∀ j, j ≤ K n → s n ≤ gridTime s T K n j ∧ gridTime s T K n j ≤ T n := fun j hj =>
    ST_gridTime_mem s T K n j hsT hK hj
  have hu1 : ∀ j, j ≤ K n → gridTime s T K n j < 1 := fun j hj =>
    lt_of_le_of_lt (hmem j hj).2 hT1
  have hηpos : ∀ j, j ≤ K n → 0 < etaT E (gridTime s T K n j) := fun j hj =>
    etaT_pos hE2 (hu1 j hj)
  have hdec : ∀ (i : STLab sz n) (k : ℕ), k ≤ K n → k ≤ K n →
      ‖STgA sz s T K n E i.1 i.2 k ω‖ ≤ ‖STgA sz s T K n E i.1 i.2 0 ω‖ +
        gridStep s T K n * ∑ j ∈ Finset.range k, ‖STgDrift sz s T K n E i.1 i.2 j ω‖ +
        ‖Rem i k ω‖ + ‖Mart i k ω‖ := by
    intro i k hk _
    have hid := hident i k hk
    have hsum' : ‖((gridStep s T K n : ℝ) : ℂ) *
        ∑ j ∈ Finset.range k, STgDrift sz s T K n E i.1 i.2 j ω‖ ≤
        gridStep s T K n * ∑ j ∈ Finset.range k, ‖STgDrift sz s T K n E i.1 i.2 j ω‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hΔ]
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) hΔ
    rw [hid]
    calc ‖STgA sz s T K n E i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDrift sz s T K n E i.1 i.2 j ω + Rem i k ω + Mart i k ω‖
        ≤ ‖STgA sz s T K n E i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDrift sz s T K n E i.1 i.2 j ω + Rem i k ω‖ +
          ‖Mart i k ω‖ := norm_add_le _ _
      _ ≤ (‖STgA sz s T K n E i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDrift sz s T K n E i.1 i.2 j ω‖ + ‖Rem i k ω‖) +
          ‖Mart i k ω‖ := add_le_add_left (norm_add_le _ _) _
      _ ≤ ((‖STgA sz s T K n E i.1 i.2 0 ω‖ + ‖((gridStep s T K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDrift sz s T K n E i.1 i.2 j ω‖) + ‖Rem i k ω‖) +
          ‖Mart i k ω‖ := by gcongr; exact norm_add_le _ _
      _ ≤ _ := by gcongr
  have key := ST_pathwise_ineq (ι := STLab sz n) (K := K n) (τ := K n) (Δ := gridStep s T K n)
    (a₀ := a₀) (r₀ := r₀)
    (x := fun k i => ‖STgA sz s T K n E i.1 i.2 k ω‖)
    (dr := fun j i => ‖STgDrift sz s T K n E i.1 i.2 j ω‖)
    (mart := fun k i => ‖Mart i k ω‖) (P := fun _ _ => (1 : ℝ))
    (remk := fun k i => ‖Rem i k ω‖)
    (Jh := fun j => OptL2aJ sz n E (gridTime s T K n j) (pathH sz s T K n j ω))
    (β := fun j => C₀ / (1 - gridTime s T K n j))
    (e := fun j => Mx * ((etaT E (gridTime s T K n j))⁻¹ * Y))
    (m := fun _ => Mb)
    hΔ ha₀ hr₀ (fun j _ => OptL2aJ_nonneg sz n E _ _)
    (fun k B _ h => OptL2aJ_le sz n E _ _ (fun i => by have := h i; rw [div_one] at this; exact this))
    (fun _ _ _ => one_pos) (fun _ _ _ _ _ _ => le_refl _)
    (fun j hj => div_nonneg hC₀ (by linarith [hu1 j hj.le]))
    (fun j hj => mul_nonneg hMx (mul_nonneg (inv_nonneg.mpr (hηpos j hj.le).le) hY))
    hdec (fun i => by simpa using hinit i)
    (fun i j hj => by simpa using hdrift j hj.le i)
    (fun i k hk => by simpa using hrem i k hk)
    (fun i k hk => by simpa using hmart i k hk)
  intro k hk
  have hk' := key k hk hk
  have hE_sum : gridStep s T K n * ∑ j ∈ Finset.range k,
      Mx * ((etaT E (gridTime s T K n j))⁻¹ * Y) ≤ Mx * Y * (q * Lg) := by
    have h := OptL2a_eta_sum_mul K n hsT hT1 hK hE2 hq hLg (mul_nonneg hMx hY) hk
    have hrew : gridStep s T K n * ∑ j ∈ Finset.range k,
        Mx * ((etaT E (gridTime s T K n j))⁻¹ * Y) =
        ∑ j ∈ Finset.range k, gridStep s T K n *
          (Mx * Y * (etaT E (gridTime s T K n j))⁻¹) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hrew]; exact h
  linarith

end Pathwise

end RBM.Gauss.Sizes

/-! ## 7. The three targets of ST2-14 -/

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

section Numbers

variable {d : ℕ} (sz : Sizes d)

/-- The elementary facts on `λ_n` at one `n`: `0 < λ ≤ 1`, `λ ≥ c_B N⁻¹`, `Ψ = (λ^{1/4})²`. -/
theorem OptL2a_lam_basic (n : ℕ) {s T : ℕ → ℝ} {cB c ε₀ : ℝ} (hcB : 0 < cB) (hs1 : s n < 1)
    (hT1 : T n < 1) (hsT : s n ≤ T n) (hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ))
    (hbd : cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n (T n) ∧
      sz.Bctl n (T n) ≤ ((sz.size n : ℕ) : ℝ) ^ (-c))
    (hlf : OptL2alam sz s T n ≤ (sz.Bctl n (T n)) ^ (1 / 2 : ℝ) ∧
      Real.sqrt (OptL2alam sz s T n) ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) (hc : 0 ≤ c) :
    0 < OptL2alam sz s T n ∧ OptL2alam sz s T n ≤ 1 ∧
      cB * ((sz.size n : ℕ) : ℝ)⁻¹ ≤ OptL2alam sz s T n ∧
      OptL2aPsi sz ε₀ s T n = (OptL2alam sz s T n ^ (1 / 4 : ℝ)) ^ 2 := by
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hBT : 0 < sz.Bctl n (T n) := STBctl_pos sz n hT1
  have hB1 : sz.Bctl n (T n) ≤ 1 :=
    hbd.2.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith))
  have hρ1 : 1 ≤ (1 - s n) / (1 - T n) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hlampos : 0 < OptL2alam sz s T n :=
    mul_pos (div_pos (by linarith) (by linarith)) hBT
  refine ⟨hlampos, hlf.1.trans (Real.rpow_le_one hBT.le hB1 (by norm_num)), ?_, ?_⟩
  · have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hWpos d
    calc cB * ((sz.size n : ℕ) : ℝ)⁻¹ ≤ cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ hWd (ST_Wpow_le_size sz n)) hcB.le
      _ ≤ sz.Bctl n (T n) := hbd.1
      _ = 1 * sz.Bctl n (T n) := (one_mul _).symm
      _ ≤ OptL2alam sz s T n := mul_le_mul_of_nonneg_right hρ1 hBT.le
  · rw [(OptL2a_w_pow hlampos).1]
    exact min_eq_left hlf.2

/-- `q log ρ ≤ N^{ε₁}` for the time ratio `ρ = (1-s)/(1-T)` (`log ρ` costs a power of `N`). -/
theorem OptL2a_x_le (n : ℕ) {s T : ℕ → ℝ} {cB c 𝔠d q ε₁ : ℝ} (hq0 : 0 ≤ q) (hε₁ : 0 < ε₁)
    (hcB : 0 < cB) (hT1 : T n < 1) (hsT : s n ≤ T n)
    (hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ))
    (hbd : cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n (T n) ∧
      sz.Bctl n (T n) ≤ ((sz.size n : ℕ) : ℝ) ^ (-c)) (hc : 0 ≤ c)
    (h𝔠d : 𝔠d ≤ 1 / 2) (hcon : (sz.Bctl n (T n)) ^ 𝔠d ≤ (1 - T n) / (1 - s n))
    (hbig : q / 2 * (cB ^ (-(ε₁ / 2)) / (ε₁ / 2)) ≤ ((sz.size n : ℕ) : ℝ) ^ (ε₁ / 2)) :
    q * Real.log ((1 - s n) / (1 - T n)) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ := by
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hBT : 0 < sz.Bctl n (T n) := STBctl_pos sz n hT1
  have hB1 : sz.Bctl n (T n) ≤ 1 :=
    hbd.2.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith))
  have hρ1 : 1 ≤ (1 - s n) / (1 - T n) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have h := OptL2a_q_log_le (q := q) (ρ := (1 - s n) / (1 - T n)) (B := sz.Bctl n (T n)) (cB := cB)
    (Wd := ((sz.W n : ℕ) : ℝ) ^ d) (N := ((sz.size n : ℕ) : ℝ)) (ε' := ε₁ / 2) hq0
    (by positivity) hcB hN1 (pow_pos hWpos d) (ST_Wpow_le_size sz n) hbd.1 hρ1
    (OptL2a_rho_le hBT hB1 h𝔠d hcon) hbig
  rwa [show 2 * (ε₁ / 2) = ε₁ by ring] at h

end Numbers

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-- **Target 1: the drift bound of `(l>0EQ)`** (`3_5:474`).  For `κ, ε, 𝔡 > 0` there is `C₀ > 0`
(`C₀ = 2C`, `C` of `lem:newKLK`, depending only on `d, κ, 𝔡`) such that, along a flow `z` and for
times `0 ≤ s ≤ T ≤ lemT z` with the first conjunct of `(con_st_ind)` (`B_T^{𝔠_d} ≤ (1-T)/(1-s)`,
`𝔠_d ≤ 1/2`) and Step 1 on `[s,T]`, for every `τ > 0` and every grid `K_n = ⌈N^{CK}⌉` from `s` to `T`, w.h.p.,
for all `j ≤ K_n` and all labels `(σ,a)`: the drift of `(𝓛-𝒦)^{(2)}` at `u_j` is at most
`C₀ (1-u_j)⁻¹ J_j + N^τ η_{u_j}⁻¹ λ^{3/2}`, `J_j = max_{σ,a} |(𝓛-𝒦)^{(2)}_{u_j,σ,a}|`,
`λ = ((1-s)/(1-T)) W^{-d}B_{T,0}` (the paper's `W^{-c₀}`; `λ^{3/2} = W^{-3c₀/2}`).  The light-weight
term enters through the pin `STLWB`; `lem:newKLK` (`stNewKLK_holds`) at `ℓ = 0` is proved. -/
theorem stOptL2a_drift {d : ℕ} (hd : 3 ≤ d) (hLWB : STLWB d)
    (κ ε 𝔡 : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s T : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ T n) → (∀ n, T n ≤ lemT (z n)) →
        ∀ 𝔠d : ℝ, 𝔠d ≤ 1 / 2 →
          (∀ᶠ n in atTop, (sz.Bctl n (T n)) ^ 𝔠d ≤ (1 - T n) / (1 - s n)) →
          STStep1Loop sz (STflowE z) s T → STStep1Weak sz (STflowE z) s T →
          ∀ τ : ℝ, 0 < τ → ∀ CK : ℝ, 0 ≤ CK → ∀ K : ℕ → ℕ,
            (∀ n, K n = ⌈((sz.size n : ℕ) : ℝ) ^ CK⌉₊) →
              Gauss.HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ j, j ≤ K n → ∀ i : STLab sz n,
                ‖STgDrift sz s T K n (STflowE z n) i.1 i.2 j ω‖ ≤
                  C₀ / (1 - gridTime s T K n j) *
                      OptL2aJ sz n (STflowE z n) (gridTime s T K n j) (pathH sz s T K n j ω) +
                    ((sz.size n : ℕ) : ℝ) ^ τ * ((etaT (STflowE z n) (gridTime s T K n j))⁻¹ *
                      (OptL2alam sz s T n) ^ (3 / 2 : ℝ))}) := by
  classical
  obtain ⟨C, δ₀, hC, hδ₀, hnew⟩ := stNewKLK_holds d hd κ 𝔡 hκ h𝔡
  have hd0 : 0 < d := by omega
  obtain ⟨cB, hcB, hcd⟩ := OptL2a_sizedata hd0 hκ hε h𝔡
  refine ⟨2 * C, by positivity, ?_⟩
  intro 𝔠 sz z hflow s T hs hsT hTT 𝔠d h𝔠d hcon hS1L hS1W τ hτ CK hCK K hKn
  have hsize := tendsto_size sz hflow.1.2.2.1
  have hWO : sz.WO 𝔡 := hflow.1.2.2.2.2
  have hT0 : ∀ n, 0 ≤ T n := fun n => (hs n).trans (hsT n)
  have hT1 : ∀ n, T n < 1 := fun n =>
    lt_of_le_of_lt (hTT n) (lemT_lt_one (ST_flow_im_pos sz hflow n))
  obtain ⟨c, hc, hc1, hBd0⟩ := hcd 𝔠
  have hBd := hBd0 sz z hflow T hT0 hTT
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : ℝ, ε₀ = (d : ℝ) * c / 4 := ⟨_, rfl⟩
  obtain ⟨hK0, -⟩ := OptL2a_grid sz K hKn
  obtain ⟨hcardIdx, -, hcardLab, -⟩ := OptL2a_cards sz hsize hCK K hKn
  -- (E1) the weak law
  have hsmallE1 : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ T n →
      ((sz.size n : ℕ) : ℝ) ^ (c / 8) * (sz.Bctl n u) ^ (1 / 4 : ℝ) ≤ δ₀ := by
    filter_upwards [hBd, ST_size_pow_small sz hsize (a := c / 8 - c / 4) (δ := δ₀)
      (by linarith) hδ₀] with n hn hsm u hsu huT
    have hb := (hn u ((hs n).trans hsu) huT).2
    have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hb0 : 0 ≤ sz.Bctl n u := (mul_nonneg hcB.le (inv_nonneg.mpr (pow_nonneg
      (Nat.cast_nonneg _) d))).trans (hn u ((hs n).trans hsu) huT).1
    calc ((sz.size n : ℕ) : ℝ) ^ (c / 8) * (sz.Bctl n u) ^ (1 / 4 : ℝ)
        ≤ ((sz.size n : ℕ) : ℝ) ^ (c / 8) * (((sz.size n : ℕ) : ℝ) ^ (-c)) ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hb0 hb (by norm_num)) (Real.rpow_nonneg hN0 _)
      _ = ((sz.size n : ℕ) : ℝ) ^ (c / 8 - c / 4) := by
          rw [← Real.rpow_mul hN0, ← Real.rpow_add' hN0 (by linarith)]; congr 1; ring
      _ ≤ δ₀ := hsm
  have hE1 := ST_event_weak sz (κ := κ) (ε := ε) (𝔡 := 𝔡) (𝔠 := 𝔠) (z := z) (s := s) (t := T)
    (T := T) K hs hsT (fun n => le_refl _) hK0 (by linarith : (0 : ℝ) ≤ CK + 5) hcardIdx hS1W
    (ε₁ := c / 8) (by positivity) hsmallE1
  -- (E3) the light-weight term
  have hE3 := OptL2a_event_lw sz hd0 hLWB hκ hε h𝔡 hflow K hs hsT hK0 hTT hS1L hS1W hcB hc hc1 hε₀
    hBd h𝔠d hcon (C₁ := CK + 5) (by linarith) hcardLab hτ
  have hlf := OptL2a_lam_facts sz hc hε₀ h𝔠d hT1
    (hBd.mono fun n hn => (hn (T n) (hT0 n) le_rfl).2) hcon
  refine (Gauss.HighProbAt.inter hsize hE1 hE3).mono ?_
  filter_upwards [hWO, hlf, hBd, hcon, hsize.eventually (eventually_ge_atTop 1)] with n hwon hlfn
    hbdn hconn hN1
  rintro ω ⟨hw, hl⟩ j hj i
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have him := ST_flow_im_pos sz hflow n
  have hE : |STflowE z n| ≤ 2 - κ := (abs_lemE_le him).trans (hflow.2 n).1
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hlamn : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hwon.1
  have hs1 : s n < 1 := lt_of_le_of_lt (hsT n) (hT1 n)
  obtain ⟨hlampos, -, -, hΨeq⟩ := OptL2a_lam_basic sz n hcB hs1 (hT1 n) (hsT n) hN1'
    (hbdn (T n) (hT0 n) le_rfl) hlfn hc.le
  obtain ⟨hw2, -, -, hw6⟩ := OptL2a_w_pow hlampos
  have hdr := OptL2a_drift_grid sz (by positivity : (0 : ℝ) ≤ C) hnew s T K n (STflowE z n) hlamn
    hwon.2 hE (hs n) (hsT n) (hT1 n) (hK0 n) ω j hj (hw j hj) i
  have hel := hl j hj i
  have hΨ3 : OptL2aPsi sz ε₀ s T n * OptL2aPsi sz ε₀ s T n ^ 2 = OptL2alam sz s T n ^ (3 / 2 : ℝ) := by
    rw [← hw6, hΨeq]; ring
  have hrew : ((sz.size n : ℕ) : ℝ) ^ τ * ((etaT (STflowE z n) (gridTime s T K n j))⁻¹ *
      OptL2aPsi sz ε₀ s T n * OptL2aPsi sz ε₀ s T n ^ 2) =
      ((sz.size n : ℕ) : ℝ) ^ τ * ((etaT (STflowE z n) (gridTime s T K n j))⁻¹ *
        OptL2alam sz s T n ^ (3 / 2 : ℝ)) := by
    rw [← hΨ3]; ring
  rw [hrew] at hel
  exact hdr.trans (add_le_add le_rfl hel)

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-- **Target 2: the martingale bound** (`3_5:476-478`).  Under the hypotheses of Target 1 (without
`STLWB`), for every
`τ, D > 0` there is a grid exponent `CK` such that on every grid `K_n = ⌈N^{CK}⌉` from `s` to `T` the
grid decomposition of `STGridMart` (`Sol_CalL`, `lem:DIfREP`) holds with a remainder `|Rem| ≤ N^{-2}`
and a martingale part with `|Mart_k| ≤ N^τ λ^{5/4}` for all `k ≤ K_n` and all labels, with
probability `≥ 1 - N^{-D}` (`λ^{5/4} = W^{-5c₀/4}`).  Inputs: `(eq:MG_conclusion)` of
`stEMn2Poly_holds` with `Ψ = √λ` (the quadratic variation `|(𝓔⊗𝓔)^{M,(2)}_{u_j}| ≤ N^{ε} η_{u_j}⁻¹ λ^{5/2}`,
`ΔΣ_j η_{u_j}⁻¹ ≤ q log ρ`) and the Markov step of the pin `STGridMart`; no light-weight pin is used
(`3 ≤ d` is not needed here: only `0 < d`). -/
theorem stOptL2a_martingale {d : ℕ} (hd0 : 0 < d) (hGM : STGridMart d)
    (κ ε 𝔡 : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) :
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s T : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ T n) → (∀ n, T n ≤ lemT (z n)) →
        ∀ 𝔠d : ℝ, 𝔠d ≤ 1 / 2 →
          (∀ᶠ n in atTop, (sz.Bctl n (T n)) ^ 𝔠d ≤ (1 - T n) / (1 - s n)) →
          STStep1Loop sz (STflowE z) s T → STStep1Weak sz (STflowE z) s T →
          ∀ τ : ℝ, 0 < τ → ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
            ∀ K : ℕ → ℕ, (∀ n, K n = ⌈((sz.size n : ℕ) : ℝ) ^ CK⌉₊) →
              ∃ Mart Rem : ∀ n, ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) → ℕ → PathΩ sz → ℂ,
                (∀ n i, ∀ᵐ ω ∂(pathP sz), ∀ k, k ≤ K n →
                  STgA sz s T K n (STflowE z n) i.1 i.2 k ω =
                    STgA sz s T K n (STflowE z n) i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
                      ∑ j ∈ Finset.range k, STgDrift sz s T K n (STflowE z n) i.1 i.2 j ω +
                        Rem n i k ω + Mart n i k ω) ∧
                (∀ᶠ n in atTop, ∀ i, ∀ᵐ ω ∂(pathP sz), ∀ k, k ≤ K n →
                  ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (-2 : ℝ)) ∧
                (∀ᶠ n in atTop, pathP sz {ω | ∃ i : STLab sz n, ∃ k, k ≤ K n ∧
                  ((sz.size n : ℕ) : ℝ) ^ τ * (OptL2alam sz s T n) ^ (5 / 4 : ℝ) <
                    ‖Mart n i k ω‖} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))) := by
  classical
  obtain ⟨CM, hCM0, hCM⟩ := hGM
  obtain ⟨cB, hcB, hcd⟩ := OptL2a_sizedata hd0 hκ hε h𝔡
  intro 𝔠 sz z hflow s T hs hsT hTT 𝔠d h𝔠d hcon hS1L hS1W τ hτ D hD
  have hsize := tendsto_size sz hflow.1.2.2.1
  have hT0 : ∀ n, 0 ≤ T n := fun n => (hs n).trans (hsT n)
  have hT1 : ∀ n, T n < 1 := fun n =>
    lt_of_le_of_lt (hTT n) (lemT_lt_one (ST_flow_im_pos sz hflow n))
  have hs1 : ∀ n, s n < 1 := fun n => lt_of_le_of_lt (hsT n) (hT1 n)
  obtain ⟨c, hc, hc1, hBd0⟩ := hcd 𝔠
  have hBd := hBd0 sz z hflow T hT0 hTT
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : ℝ, ε₀ = (d : ℝ) * c / 4 := ⟨_, rfl⟩
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = τ / 8 := ⟨_, rfl⟩
  have hε₁ : 0 < ε₁ := by rw [hε₁def]; positivity
  obtain ⟨Dm, hDmdef⟩ : ∃ Dm : ℝ, Dm = D + 4 := ⟨_, rfl⟩
  have hDmpos : 0 < Dm := by rw [hDmdef]; linarith
  obtain ⟨CK0, hCK0, hCK⟩ := hCM κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s T hs hsT hTT Dm hDmpos
  obtain ⟨CK', hCK'def⟩ : ∃ CK' : ℝ, CK' = max CK0 (2 * (CM + 2)) := ⟨_, rfl⟩
  have hCK'0 : 0 ≤ CK' := by rw [hCK'def]; exact hCK0.trans (le_max_left _ _)
  have hCK'1 : CK0 ≤ CK' := by rw [hCK'def]; exact le_max_left _ _
  have hCK'2 : 2 * (CM + 2) ≤ CK' := by rw [hCK'def]; exact le_max_right _ _
  refine ⟨CK', hCK'0, ?_⟩
  intro K hKn
  obtain ⟨hK0, hKbig'⟩ := OptL2a_grid sz K hKn
  have hKbig : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK0 ≤ (K n : ℝ) := by
    filter_upwards [hsize.eventually (eventually_ge_atTop 1)] with n hn
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hn
    exact (Real.rpow_le_rpow_of_exponent_le hN1 hCK'1).trans (hKbig' n)
  obtain ⟨Mart, Rem, hident, hrem0, hmart0⟩ := hCK K hK0 hKbig
  obtain ⟨-, hcardLab3, -, hcardF2⟩ := OptL2a_cards sz hsize hCK'0 K hKn
  refine ⟨Mart, Rem, hident, ?_, ?_⟩
  · -- the remainder
    filter_upwards [hrem0, hsize.eventually (eventually_ge_atTop 1)] with n hr hN1 i
    have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    refine (hr i).mono fun ω hω k hk => (hω k hk).trans ?_
    have hts : T n - s n ≤ 1 := by linarith [hT1 n, hs n]
    have hsq := ST_sqrt_gridStep_le s T K n hN1' hts (hKbig' n)
    calc ((sz.size n : ℕ) : ℝ) ^ CM * Real.sqrt (gridStep s T K n)
        ≤ ((sz.size n : ℕ) : ℝ) ^ CM * ((sz.size n : ℕ) : ℝ) ^ (-CK' / 2) :=
          mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hN0.le _)
      _ = ((sz.size n : ℕ) : ℝ) ^ (CM + -CK' / 2) := (Real.rpow_add hN0 _ _).symm
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  · -- the martingale
    obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = (Real.sqrt κ / 2)⁻¹ := ⟨_, rfl⟩
    have hsqκ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
    have hq0 : 0 ≤ q := by rw [hqdef]; positivity
    have hbigE : ∀ᶠ n in atTop, q / 2 * (cB ^ (-(ε₁ / 2)) / (ε₁ / 2)) ≤
        ((sz.size n : ℕ) : ℝ) ^ (ε₁ / 2) :=
      ST_size_pow_big sz hsize (a := ε₁ / 2) (M := q / 2 * (cB ^ (-(ε₁ / 2)) / (ε₁ / 2)))
        (by positivity)
    have hMge : ∀ᶠ n in atTop, 2 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ :=
      ST_size_pow_big sz hsize (a := ε₁) (M := 2) hε₁
    have hfm : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-(4 - 5 / 2 : ℝ)) ≤ cB ^ (5 / 2 : ℝ) :=
      ST_size_pow_small sz hsize (by norm_num) (Real.rpow_pos_of_pos hcB _)
    have hlf := OptL2a_lam_facts sz hc hε₀ h𝔠d hT1
      (hBd.mono fun n hn => (hn (T n) (hT0 n) le_rfl).2) hcon
    have hE4 := OptL2a_event_mg sz hd0 hκ hε h𝔡 hflow K hs hsT hK0 hTT hS1L hS1W hcB hc hc1 hε₀
      hBd h𝔠d hcon (C₁ := CK' + 5) (by linarith) hcardF2 hε₁
    refine OptL2a_prob_combine (pathP sz) sz.size hsize _ hE4
      (fun n i => {ω | ∃ k, k ≤ K n ∧ ((sz.size n : ℕ) : ℝ) ^ ε₁ *
        (∑ j ∈ Finset.range k, gridStep s T K n *
          ‖STEEM sz n (STflowE z n) (gridTime s T K n j) (pathH sz s T K n j ω) i.1 i.2‖ +
          ((sz.size n : ℕ) : ℝ) ^ (-Dm)) ^ (1 / 2 : ℝ) < ‖Mart n i k ω‖})
      (fun n => ∅) hD (Dm := Dm) (by rw [hDmdef]; linarith) (hmart0 ε₁ hε₁) hcardLab3
      (Eventually.of_forall fun n => measure_empty) _ ?_
    filter_upwards [hsize.eventually (eventually_ge_atTop 1), hBd, hlf, hcon, hMge, hbigE, hfm]
      with n hN1 hbdn hlfn hconn hM hbig hfmn
    intro ω hω
    by_contra hcon'
    have hΞω := fun h => hcon' (Or.inl (Or.inl h))
    have hm := not_not.1 hΞω
    have hΔ0 := ST_gridStep_nonneg s T K n (hsT n)
    have hnB : ∀ i, ω ∉ ({ω | ∃ k, k ≤ K n ∧ ((sz.size n : ℕ) : ℝ) ^ ε₁ *
        (∑ j ∈ Finset.range k, gridStep s T K n *
          ‖STEEM sz n (STflowE z n) (gridTime s T K n j) (pathH sz s T K n j ω) i.1 i.2‖ +
          ((sz.size n : ℕ) : ℝ) ^ (-Dm)) ^ (1 / 2 : ℝ) < ‖Mart n i k ω‖} : Set (PathΩ sz)) :=
      fun i hB => hcon' (Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, hB⟩)))
    obtain ⟨i, k, hk, hlt⟩ := hω
    -- the numbers at `n`
    have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have him := ST_flow_im_pos sz hflow n
    have hE : |STflowE z n| ≤ 2 - κ := (abs_lemE_le him).trans (hflow.2 n).1
    have hE2 : |STflowE z n| < 2 := by linarith
    obtain ⟨hlampos, -, hlamge, hΨeq⟩ := OptL2a_lam_basic sz n hcB (hs1 n) (hT1 n) (hsT n) hN1'
      (hbdn (T n) (hT0 n) le_rfl) hlfn hc.le
    obtain ⟨hw2, hw5, hw10, -⟩ := OptL2a_w_pow hlampos
    have hw0 : 0 < OptL2alam sz s T n ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hlampos _
    have hΨ0 : 0 < OptL2aPsi sz ε₀ s T n := by rw [hΨeq]; positivity
    have hΨw : OptL2aPsi sz ε₀ s T n ≤ (OptL2alam sz s T n ^ (1 / 4 : ℝ)) ^ 2 := hΨeq.le
    have hNmfl : ((sz.size n : ℕ) : ℝ) ^ (-Dm) ≤ (OptL2alam sz s T n ^ (1 / 4 : ℝ)) ^ 10 := by
      calc ((sz.size n : ℕ) : ℝ) ^ (-Dm) ≤ ((sz.size n : ℕ) : ℝ) ^ (-4 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1' (by rw [hDmdef]; linarith)
        _ ≤ OptL2alam sz s T n ^ (5 / 2 : ℝ) :=
            OptL2a_floor hcB hN1' hlamge (by norm_num) hfmn
        _ = (OptL2alam sz s T n ^ (1 / 4 : ℝ)) ^ 10 := hw10.symm
    have hxM := OptL2a_x_le sz n hq0 hε₁ hcB (hT1 n) (hsT n) hN1' (hbdn (T n) (hT0 n) le_rfl)
      hc.le h𝔠d hconn hbig
    have hρ1 : 1 ≤ (1 - s n) / (1 - T n) := by
      rw [le_div_iff₀ (by linarith [hT1 n])]; linarith [hsT n]
    have hx0 : 0 ≤ q * Real.log ((1 - s n) / (1 - T n)) := mul_nonneg hq0 (Real.log_nonneg hρ1)
    have hNm0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-Dm) := Real.rpow_nonneg hN0.le _
    have hqim : ((mE (STflowE z n)).im)⁻¹ ≤ q := by
      rw [hqdef]; exact inv_anti₀ (by positivity) (ST_mE_im_ge hκ hE)
    -- the quadratic variation sum
    have hmgn : ∀ j, j ≤ K n →
        ‖STEEM sz n (STflowE z n) (gridTime s T K n j) (pathH sz s T K n j ω) i.1 i.2‖ ≤
          (2 * ((sz.size n : ℕ) : ℝ) ^ ε₁ * OptL2aPsi sz ε₀ s T n ^ 5) *
            (etaT (STflowE z n) (gridTime s T K n j))⁻¹ := fun j hj => by
      refine (hm j hj i).trans (le_of_eq ?_)
      ring
    have ha : 0 ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ ε₁ * OptL2aPsi sz ε₀ s T n ^ 5 :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hN0.le _)) (pow_nonneg hΨ0.le 5)
    have hetaS := OptL2a_eta_sum_mul K n (hsT n) (hT1 n) (hK0 n) hE2 hqim (le_refl _) ha hk
    have hsumE : ∑ j ∈ Finset.range k, gridStep s T K n *
        ‖STEEM sz n (STflowE z n) (gridTime s T K n j) (pathH sz s T K n j ω) i.1 i.2‖ ≤
        (2 * ((sz.size n : ℕ) : ℝ) ^ ε₁ * OptL2aPsi sz ε₀ s T n ^ 5) *
          (q * Real.log ((1 - s n) / (1 - T n))) :=
      le_trans (Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
        (hmgn j ((Finset.mem_range.mp hj).le.trans hk)) hΔ0) hetaS
    have hmartn := not_lt.1 fun h => hnB i ⟨k, hk, h⟩
    have h1 : ((sz.size n : ℕ) : ℝ) ^ ε₁ * (∑ j ∈ Finset.range k, gridStep s T K n *
        ‖STEEM sz n (STflowE z n) (gridTime s T K n j) (pathH sz s T K n j ω) i.1 i.2‖ +
        ((sz.size n : ℕ) : ℝ) ^ (-Dm)) ^ (1 / 2 : ℝ) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₁ * (2 * ((sz.size n : ℕ) : ℝ) ^ ε₁ * OptL2aPsi sz ε₀ s T n ^ 5 *
          (q * Real.log ((1 - s n) / (1 - T n))) + ((sz.size n : ℕ) : ℝ) ^ (-Dm)) ^ (1 / 2 : ℝ) := by
      refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) ?_ (by norm_num))
        (Real.rpow_nonneg hN0.le _)
      linarith
    have h2 := OptL2a_mart_arith (M := ((sz.size n : ℕ) : ℝ) ^ ε₁) (w := OptL2alam sz s T n ^ (1 / 4 : ℝ))
      (Ψ := OptL2aPsi sz ε₀ s T n) (x := q * Real.log ((1 - s n) / (1 - T n)))
      (Nm := ((sz.size n : ℕ) : ℝ) ^ (-Dm)) (by linarith) hw0 hΨ0 hΨw hx0 hxM hNm0 hNmfl
    have hM8 : (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 8 = ((sz.size n : ℕ) : ℝ) ^ τ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; rw [hε₁def]; push_cast; ring
    have h3 : 2 * (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2 ≤ (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 8 :=
      OptL2a_two_sq_le hM
    have hw5' : 0 ≤ (OptL2alam sz s T n ^ (1 / 4 : ℝ)) ^ 5 := by positivity
    have h4 : 2 * (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2 * (OptL2alam sz s T n ^ (1 / 4 : ℝ)) ^ 5 ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * OptL2alam sz s T n ^ (5 / 4 : ℝ) := by
      rw [← hw5, ← hM8]; exact mul_le_mul_of_nonneg_right h3 hw5'
    exact absurd (hlt.trans_le (hmartn.trans (h1.trans (h2.trans h4)))) (lt_irrefl _)

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-- **Target 3: `(eq:Gronwall_2L_max)` on the grid, in the form `ST_gronwall` consumes**
(`3_5:466–481`, the first part of the proof of `(eq:opt_L2)`).  For `κ, ε, 𝔡 > 0` there is `C₀ > 0`
(`C₀ = 2C`, depending only on `d, κ, 𝔡`) such that for a flow `z`, times `0 ≤ s ≤ T ≤ lemT z`, under
`(Eq:L-KGt+IND)` at `s` (`STLK`), the first conjunct `B_T^{𝔠_d} ≤ (1-T)/(1-s)` of `(con_st_ind)`
(`𝔠_d ≤ 1/2`) and Step 1 (`STStep1Loop`, `STStep1Weak` on `[s,T]`), for every `τ, D > 0` there is a
grid exponent `CK` such that on the grid `K_n = ⌈N^{CK}⌉` from `s` to `T`, with probability `≥ 1 - N^{-D}`,
for all `k ≤ K_n`
`J_k ≤ N^τ ((W^{-d}B_{s,0})² + λ^{5/4}) + Δ Σ_{j<k} (C₀/(1-u_j)) J_j`,
`J_k = max_{σ,a} |(𝓛-𝒦)^{(2)}_{u_k,σ,a}|` of the grid walk, `λ = ((1-s)/(1-T)) W^{-d}B_{T,0}` (the
paper's `W^{-c₀}`).  The right side has the form of `ST_gronwall` (`α` constant, `β_j = C₀/(1-u_j)`).
It combines Target 1 (`stOptL2a_drift`) and Target 2 (`stOptL2a_martingale`) with the initial value
`J_0 ≺ B_s²` (`STLK`, `ST_grid_whp_zero`).  The two owed pins enter as `STLWB`, `STGridMart`. -/
theorem stOptL2a_gronwall {d : ℕ} (hd : 3 ≤ d) (hLWB : STLWB d) (hGM : STGridMart d)
    (κ ε 𝔡 : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s T : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ T n) → (∀ n, T n ≤ lemT (z n)) →
        STLK sz (STflowE z) s → ∀ 𝔠d : ℝ, 𝔠d ≤ 1 / 2 →
          (∀ᶠ n in atTop, (sz.Bctl n (T n)) ^ 𝔠d ≤ (1 - T n) / (1 - s n)) →
          STStep1Loop sz (STflowE z) s T → STStep1Weak sz (STflowE z) s T →
          ∀ τ : ℝ, 0 < τ → ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
            ∀ K : ℕ → ℕ, (∀ n, K n = ⌈((sz.size n : ℕ) : ℝ) ^ CK⌉₊) →
              ∀ᶠ n in atTop, pathP sz {ω | ¬ ∀ k, k ≤ K n →
                OptL2aJ sz n (STflowE z n) (gridTime s T K n k) (pathH sz s T K n k ω) ≤
                  ((sz.size n : ℕ) : ℝ) ^ τ *
                      ((sz.Bctl n (s n)) ^ 2 + (OptL2alam sz s T n) ^ (5 / 4 : ℝ)) +
                    gridStep s T K n * ∑ j ∈ Finset.range k, C₀ / (1 - gridTime s T K n j) *
                      OptL2aJ sz n (STflowE z n) (gridTime s T K n j) (pathH sz s T K n j ω)} ≤
                ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
  classical
  obtain ⟨C₀, hC₀, hDrift⟩ := stOptL2a_drift hd hLWB κ ε 𝔡 hκ hε h𝔡
  refine ⟨C₀, hC₀, ?_⟩
  intro 𝔠 sz z hflow s T hs hsT hTT hSTLK 𝔠d h𝔠d hcon hS1L hS1W τ hτ D hD
  have hd0 : 0 < d := by omega
  have hsize := tendsto_size sz hflow.1.2.2.1
  have hT0 : ∀ n, 0 ≤ T n := fun n => (hs n).trans (hsT n)
  have hT1 : ∀ n, T n < 1 := fun n =>
    lt_of_le_of_lt (hTT n) (lemT_lt_one (ST_flow_im_pos sz hflow n))
  have hs1 : ∀ n, s n < 1 := fun n => lt_of_le_of_lt (hsT n) (hT1 n)
  obtain ⟨cB, hcB, hcd⟩ := OptL2a_sizedata hd0 hκ hε h𝔡
  obtain ⟨c, hc, hc1, hBd0⟩ := hcd 𝔠
  have hBd := hBd0 sz z hflow T hT0 hTT
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : ℝ, ε₀ = (d : ℝ) * c / 4 := ⟨_, rfl⟩
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = τ / 8 := ⟨_, rfl⟩
  have hε₁ : 0 < ε₁ := by rw [hε₁def]; positivity
  obtain ⟨CK, hCK0, hCK⟩ := stOptL2a_martingale hd0 hGM κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s T hs hsT
    hTT 𝔠d h𝔠d hcon hS1L hS1W (τ / 2) (by positivity) (D + 4) (by positivity)
  refine ⟨CK, hCK0, fun K hKn => ?_⟩
  obtain ⟨Mart, Rem, hident, hrem, hmartP⟩ := hCK K hKn
  obtain ⟨hK0, -⟩ := OptL2a_grid sz K hKn
  obtain ⟨-, hcardLab3, -, -⟩ := OptL2a_cards sz hsize hCK0 K hKn
  have hE1 := hDrift 𝔠 sz z hflow s T hs hsT hTT 𝔠d h𝔠d hcon hS1L hS1W ε₁ hε₁ CK hCK0 K hKn
  have hE2 := ST_grid_whp_zero sz (V := fun n => STLab sz n) s T K hs hsT hK0 (C := 3)
    (by norm_num) hcardLab3
    (fun n v u H => ‖STLKM sz n (STflowE z n) u H v.1 v.2‖)
    (fun n v u H => (sz.Bctl n (s n)) ^ 2)
    (fun n v u => (STLKM_measurable sz n (STflowE z n) u v.1 v.2).norm)
    (fun n v u => measurable_const) ε₁ hε₁ (hSTLK 2 (by norm_num))
  have hΞ := Gauss.HighProbAt.inter hsize hE1 hE2
  -- the null set
  have hNl : ∀ᶠ n in atTop, pathP sz {ω | ¬ ∀ i : STLab sz n, ∀ k, k ≤ K n →
      (STgA sz s T K n (STflowE z n) i.1 i.2 k ω =
        STgA sz s T K n (STflowE z n) i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDrift sz s T K n (STflowE z n) i.1 i.2 j ω +
            Rem n i k ω + Mart n i k ω) ∧
      ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (-2 : ℝ)} = 0 := by
    filter_upwards [hrem] with n hr
    have h1 : ∀ᵐ ω ∂(pathP sz), ∀ i : STLab sz n, ∀ k, k ≤ K n →
        STgA sz s T K n (STflowE z n) i.1 i.2 k ω =
          STgA sz s T K n (STflowE z n) i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
            ∑ j ∈ Finset.range k, STgDrift sz s T K n (STflowE z n) i.1 i.2 j ω +
              Rem n i k ω + Mart n i k ω := ae_all_iff.2 fun i => hident n i
    have h2 : ∀ᵐ ω ∂(pathP sz), ∀ i : STLab sz n, ∀ k, k ≤ K n →
        ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (-2 : ℝ) := ae_all_iff.2 fun i => hr i
    have hae : ∀ᵐ ω ∂(pathP sz), ∀ i : STLab sz n, ∀ k, k ≤ K n →
        (STgA sz s T K n (STflowE z n) i.1 i.2 k ω =
          STgA sz s T K n (STflowE z n) i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
            ∑ j ∈ Finset.range k, STgDrift sz s T K n (STflowE z n) i.1 i.2 j ω +
              Rem n i k ω + Mart n i k ω) ∧
        ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (-2 : ℝ) := by
      filter_upwards [h1, h2] with ω a b i k hk
      exact ⟨a i k hk, b i k hk⟩
    exact ae_iff.1 hae
  -- the constants of the final comparison
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = (Real.sqrt κ / 2)⁻¹ := ⟨_, rfl⟩
  have hsqκ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  have hbigE : ∀ᶠ n in atTop, q / 2 * (cB ^ (-(ε₁ / 2)) / (ε₁ / 2)) ≤
      ((sz.size n : ℕ) : ℝ) ^ (ε₁ / 2) :=
    ST_size_pow_big sz hsize (a := ε₁ / 2) (M := q / 2 * (cB ^ (-(ε₁ / 2)) / (ε₁ / 2)))
      (by positivity)
  have hMge : ∀ᶠ n in atTop, 2 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ :=
    ST_size_pow_big sz hsize (a := ε₁) (M := 2) hε₁
  have hfr : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-(2 - 5 / 4 : ℝ)) ≤ cB ^ (5 / 4 : ℝ) :=
    ST_size_pow_small sz hsize (by norm_num) (Real.rpow_pos_of_pos hcB _)
  have hlf := OptL2a_lam_facts sz hc hε₀ h𝔠d hT1
    (hBd.mono fun n hn => (hn (T n) (hT0 n) le_rfl).2) hcon
  refine OptL2a_prob_combine (pathP sz) sz.size hsize _ hΞ (V := fun _ : ℕ => Unit)
    (fun n _ => {ω | ∃ i : STLab sz n, ∃ k, k ≤ K n ∧
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (OptL2alam sz s T n) ^ (5 / 4 : ℝ) < ‖Mart n i k ω‖})
    (fun n => {ω | ¬ ∀ i : STLab sz n, ∀ k, k ≤ K n →
      (STgA sz s T K n (STflowE z n) i.1 i.2 k ω =
        STgA sz s T K n (STflowE z n) i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDrift sz s T K n (STflowE z n) i.1 i.2 j ω +
            Rem n i k ω + Mart n i k ω) ∧
      ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (-2 : ℝ)})
    hD (Dm := D + 4) (by linarith) (by filter_upwards [hmartP] with n hn _ using hn) ?_ hNl _ ?_
  · filter_upwards [hsize.eventually (eventually_ge_atTop 1)] with n hn
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hn
    simpa using Real.one_le_rpow hN1 (by norm_num : (0 : ℝ) ≤ 3)
  filter_upwards [hsize.eventually (eventually_ge_atTop 1), hBd, hlf, hcon, hMge, hbigE, hfr]
    with n hN1 hbdn hlfn hconn hM hbig hfrn
  intro ω hω
  by_contra hcon'
  have hΞω := fun h => hcon' (Or.inl (Or.inl h))
  obtain ⟨hdr, hi⟩ := not_not.1 hΞω
  have hnB : ω ∉ ({ω | ∃ i : STLab sz n, ∃ k, k ≤ K n ∧
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (OptL2alam sz s T n) ^ (5 / 4 : ℝ) < ‖Mart n i k ω‖} :
        Set (PathΩ sz)) := fun hB => hcon' (Or.inl (Or.inr (Set.mem_iUnion.2 ⟨(), hB⟩)))
  have hnN := fun h => hcon' (Or.inr h)
  have hQ : ∀ i : STLab sz n, ∀ k, k ≤ K n →
      (STgA sz s T K n (STflowE z n) i.1 i.2 k ω =
        STgA sz s T K n (STflowE z n) i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDrift sz s T K n (STflowE z n) i.1 i.2 j ω +
            Rem n i k ω + Mart n i k ω) ∧
      ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (-2 : ℝ) := by
    by_contra h
    exact hnN h
  -- the numbers at `n`
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have him := ST_flow_im_pos sz hflow n
  have hE : |STflowE z n| ≤ 2 - κ := (abs_lemE_le him).trans (hflow.2 n).1
  obtain ⟨hlampos, hlam1, hlamge, -⟩ := OptL2a_lam_basic sz n hcB (hs1 n) (hT1 n) (hsT n) hN1'
    (hbdn (T n) (hT0 n) le_rfl) hlfn hc.le
  obtain ⟨-, hw5, -, hw6⟩ := OptL2a_w_pow hlampos
  have hw0 : 0 < OptL2alam sz s T n ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hlampos _
  have hw1 : OptL2alam sz s T n ^ (1 / 4 : ℝ) ≤ 1 :=
    Real.rpow_le_one hlampos.le hlam1 (by norm_num)
  have hrfl : ((sz.size n : ℕ) : ℝ) ^ (-2 : ℝ) ≤ (OptL2alam sz s T n ^ (1 / 4 : ℝ)) ^ 5 := by
    rw [hw5]; exact OptL2a_floor hcB hN1' hlamge (by norm_num) hfrn
  have hxM := OptL2a_x_le sz n hq0 hε₁ hcB (hT1 n) (hsT n) hN1' (hbdn (T n) (hT0 n) le_rfl)
    hc.le h𝔠d hconn hbig
  have hρ1 : 1 ≤ (1 - s n) / (1 - T n) := by
    rw [le_div_iff₀ (by linarith [hT1 n])]; linarith [hsT n]
  have hx0 : 0 ≤ q * Real.log ((1 - s n) / (1 - T n)) := mul_nonneg hq0 (Real.log_nonneg hρ1)
  have hqim : ((mE (STflowE z n)).im)⁻¹ ≤ q := by
    rw [hqdef]; exact inv_anti₀ (by positivity) (ST_mE_im_ge hκ hE)
  have hY : OptL2alam sz s T n ^ (3 / 2 : ℝ) ≤ (OptL2alam sz s T n ^ (1 / 4 : ℝ)) ^ 5 := by
    rw [← hw6]; exact pow_le_pow_of_le_one hw0.le hw1 (by norm_num)
  have hM4 : (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 4 = ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; rw [hε₁def]; push_cast; ring
  have hM8 : (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 8 = ((sz.size n : ℕ) : ℝ) ^ τ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; rw [hε₁def]; push_cast; ring
  have hα := OptL2a_alpha_arith (M := ((sz.size n : ℕ) : ℝ) ^ ε₁) (B2 := (sz.Bctl n (s n)) ^ 2)
    (w := OptL2alam sz s T n ^ (1 / 4 : ℝ)) (Y := OptL2alam sz s T n ^ (3 / 2 : ℝ))
    (x := q * Real.log ((1 - s n) / (1 - T n))) (r := ((sz.size n : ℕ) : ℝ) ^ (-2 : ℝ))
    (Mb := ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * OptL2alam sz s T n ^ (5 / 4 : ℝ)) hM (sq_nonneg _) hw0
    hY hx0 hxM hrfl (by rw [hM4, hw5])
  rw [hM8, hw5] at hα
  have hM0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ := Real.rpow_nonneg hN0.le _
  refine hω (OptL2a_pathwise sz hκ hC₀.le s T K n (STflowE z n) hE (hsT n) (hT1 n) (hK0 n) (Mart n)
    (Rem n) ω (a₀ := ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ 2)
    (r₀ := ((sz.size n : ℕ) : ℝ) ^ (-2 : ℝ)) (Mx := ((sz.size n : ℕ) : ℝ) ^ ε₁)
    (Y := OptL2alam sz s T n ^ (3 / 2 : ℝ)) (q := q) (Lg := Real.log ((1 - s n) / (1 - T n)))
    (Mb := ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * OptL2alam sz s T n ^ (5 / 4 : ℝ))
    (α := ((sz.size n : ℕ) : ℝ) ^ τ * ((sz.Bctl n (s n)) ^ 2 + OptL2alam sz s T n ^ (5 / 4 : ℝ)))
    (mul_nonneg hM0 (sq_nonneg _)) (Real.rpow_nonneg hN0.le _) hM0 (Real.rpow_nonneg hlampos.le _)
    hqim le_rfl (by linarith) hdr (fun i => hi i)
    (fun i k hk => not_lt.1 fun h => hnB ⟨i, k, hk, h⟩)
    (fun i k hk => (hQ i k hk).2) (fun i k hk => (hQ i k hk).1))

end RBM.Gauss.Sizes

/-! ## Instances (new): every endpoint theorem at `d = 3`

The data are the merged `RBM.Gauss.SizesInst.sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`,
`lam_n = (2(n+1))^{-6}`, `N_n = (W_n L_n)^3`), the flow `z0` (`flow_z0`, `κ = ε = 𝔡 = 1/10`,
`𝔠 = 1/6`, `Im z_n = N_n^{-4/5}`), the times `s ≡ 0`, `T ≡ 1/16 ≤ lemT z_n`, `𝔠_d = 1/26`, `τ = D = 1`.
Discharged in every example: `STFlow`, the time ranges, `𝔠_d ≤ 1/2`, and the first conjunct of
`(con_st_ind)` (`conStInd_inst`).  What stays a hypothesis of an example is a pin of another gate
(`STLWB`, `STGridMart`) or a stochastic premise of Step 1 / the induction (`STLK`, `STStep1Loop`,
`STStep1Weak`). -/

namespace RBM.Gauss.OptL2aInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst
  RBM.Gauss.Step2IterateInst RBM.Path Filter

private theorem OptL2a_hcon :
    ∀ᶠ n in atTop, (sz0.Bctl n (tInst n)) ^ (1 / 26 : ℝ) ≤ (1 - tInst n) / (1 - sInst n) :=
  (conStInd_inst (by norm_num : (0 : ℝ) < 1 / 26)).mono fun n hn => hn.1

/-- **Target 1 at the data**: the drift bound on the grid `K_n = ⌈N_n⌉` from `0` to `1/16`. -/
example (hLWB : STLWB 3) (hS1L : STStep1Loop sz0 (STflowE z0) sInst tInst)
    (hS1W : STStep1Weak sz0 (STflowE z0) sInst tInst) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ K : ℕ → ℕ, (∀ n, K n = ⌈((sz0.size n : ℕ) : ℝ) ^ (1 : ℝ)⌉₊) →
      Gauss.HighProbAt (pathP sz0) sz0.size (fun n => {ω | ∀ j, j ≤ K n → ∀ i : STLab sz0 n,
        ‖STgDrift sz0 sInst tInst K n (STflowE z0 n) i.1 i.2 j ω‖ ≤
          C₀ / (1 - gridTime sInst tInst K n j) *
              OptL2aJ sz0 n (STflowE z0 n) (gridTime sInst tInst K n j)
                (pathH sz0 sInst tInst K n j ω) +
            ((sz0.size n : ℕ) : ℝ) ^ (1 : ℝ) *
              ((etaT (STflowE z0 n) (gridTime sInst tInst K n j))⁻¹ *
                (OptL2alam sz0 sInst tInst n) ^ (3 / 2 : ℝ))}) := by
  obtain ⟨C₀, hC₀, h⟩ := stOptL2a_drift (d := 3) le_rfl hLWB (1 / 10) (1 / 10) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨C₀, hC₀, fun K hK => h (1 / 6) sz0 z0 flow_z0 sInst tInst hs0 hst htT (1 / 26)
    (by norm_num) OptL2a_hcon hS1L hS1W 1 one_pos 1 zero_le_one K hK⟩

/-- **Target 2 at the data**: the grid decomposition of `STGridMart` with `|Rem| ≤ N^{-2}` and
`|Mart_k| ≤ N λ^{5/4}` w.h.p. -/
example (hGM : STGridMart 3) (hS1L : STStep1Loop sz0 (STflowE z0) sInst tInst)
    (hS1W : STStep1Weak sz0 (STflowE z0) sInst tInst) :=
  stOptL2a_martingale (d := 3) (by norm_num) hGM (1 / 10) (1 / 10) (1 / 10) (by norm_num)
    (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0 sInst tInst hs0 hst htT (1 / 26)
    (by norm_num) OptL2a_hcon hS1L hS1W 1 one_pos 1 one_pos

/-- **Target 3 at the data**: `(eq:Gronwall_2L_max)` on the grid from `0` to `1/16`. -/
example (hLWB : STLWB 3) (hGM : STGridMart 3) (hLK : STLK sz0 (STflowE z0) sInst)
    (hS1L : STStep1Loop sz0 (STflowE z0) sInst tInst)
    (hS1W : STStep1Weak sz0 (STflowE z0) sInst tInst) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ CK : ℝ, 0 ≤ CK ∧ ∀ K : ℕ → ℕ,
      (∀ n, K n = ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊) →
        ∀ᶠ n in atTop, pathP sz0 {ω | ¬ ∀ k, k ≤ K n →
          OptL2aJ sz0 n (STflowE z0 n) (gridTime sInst tInst K n k) (pathH sz0 sInst tInst K n k ω) ≤
            ((sz0.size n : ℕ) : ℝ) ^ (1 : ℝ) *
                ((sz0.Bctl n (sInst n)) ^ 2 + (OptL2alam sz0 sInst tInst n) ^ (5 / 4 : ℝ)) +
              gridStep sInst tInst K n * ∑ j ∈ Finset.range k,
                C₀ / (1 - gridTime sInst tInst K n j) *
                  OptL2aJ sz0 n (STflowE z0 n) (gridTime sInst tInst K n j)
                    (pathH sz0 sInst tInst K n j ω)} ≤
          ENNReal.ofReal (((sz0.size n : ℕ) : ℝ) ^ (-1 : ℝ)) := by
  obtain ⟨C₀, hC₀, h⟩ := stOptL2a_gronwall (d := 3) le_rfl hLWB hGM (1 / 10) (1 / 10) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨CK, hCK0, h'⟩ := h (1 / 6) sz0 z0 flow_z0 sInst tInst hs0 hst htT hLK (1 / 26)
    (by norm_num) OptL2a_hcon hS1L hS1W 1 one_pos 1 one_pos
  exact ⟨C₀, hC₀, CK, hCK0, h'⟩

end RBM.Gauss.OptL2aInst
