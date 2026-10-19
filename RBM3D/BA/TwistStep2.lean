/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.TwistStep
import RBM3D.BA.TwistKer
import RBM3D.BA.TwistChain
import RBM3D.BA.TwistAvgB
import RBM3D.BA.Step1Fam
import RBM3D.BA.GreenSchur
import RBM3D.Induction.Step34Pins

/-!
# The per-time bound for the twisted 2-loop, part 2: the assembly, the charge cases, the regimes

Part 1 is `BA/TwistStep` (the statement `BATwistStepFixed`, the pathwise estimate of the grid walk at the last grid point, its six events, the
deterministic core, the transport back to the model).  Here:

1. the eventual arithmetic facts along the scale `N = size n`;
2. the label function of the final bound;
3. `TwistStep2_main`: the assembly of the probability bounds (six events, the remainder and `Ũ`-weighted tail clauses of `BATwistGridMartAt`,
   deterministic core, transport) for a family `Pr` of projections;
4. `TwistStep2_pin`: `BATwistStepFixed d R` from the regime input `TwistStep2_Ker d R` (the bounds on the sources `BATwistSrc1` to `BATwistSrc5`,
   the decomposition `Z = Pr Z + (1 - Pr) Z`);
5. the kernel losses of the three charge cases: `TwistStep2_kerA` (`σ₁ = σ₂`, `BAEKSameRow`), `TwistStep2_kerB` (`σ₁ ≠ σ₂` in
   `STCaseI`, external anchor, `BATwKerFar`), `TwistStep2_kerC` (`σ₁ ≠ σ₂` in `STCaseII`, `BATwKerZero`);
6. regime I: `TwistStep2_ker_caseI`, `baTwistStepFixed_caseI`;
7. regime II: the zero mode of `Z_τ` (the Ward identities of `L̃` and of `K̃`, `baTwistZeroMode_holds`, and Lemma 8.6 (`lem:TL1_BA`) at `τ`),
   `TwistStep2_ker_caseII`, `baTwistStepFixed_caseII`.

Private helpers carry the stem `TwistStep2_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.show false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open MeasureTheory Filter
open scoped Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## 1. Eventual arithmetic facts along the scale `N = size n` -/

open private TwistKer2_Bctl_ge_inv TwistKer2_Wd_Ld_le from RBM3D.BA.TwistKer2
open private TwistStep_Good from RBM3D.BA.TwistStep

section FA

variable {d : ℕ} (sz : Sizes d)

/-- Eventually `A ≤ N^c` along the scale `N = size n`. -/
theorem TwistStep2_ev_ge (hN : Tendsto sz.size atTop atTop) {c : ℝ} (hc : 0 < c) (A : ℝ) :
    ∀ᶠ n in atTop, A ≤ ((sz.size n : ℕ) : ℝ) ^ c := by
  have h1 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  exact ((tendsto_rpow_atTop hc).comp h1).eventually_ge_atTop A

/-- `W_n ≤ N_n` (`W^d ≤ N`, `d ≥ 1`). -/
theorem TwistStep2_W_le_N (hd : 1 ≤ d) (n : ℕ) : ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  have h := (TwistKer2_Wd_Ld_le (sz := sz) n).1
  have hW : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  exact le_trans (le_self_pow₀ hW (by omega)) h

/-- `N^{-3/2} ≤ B^{3/2}` and `N^{-5/3} ≤ B^{5/3}` for `0 ≤ u < 1`. -/
theorem TwistStep2_beta_ge (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ((sz.size n : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) ≤ sz.Bctl n u ^ (3 / 2 : ℝ) ∧ ((sz.size n : ℕ) : ℝ) ^ (-(5 / 3 : ℝ)) ≤ sz.Bctl n u ^ (5 / 3 : ℝ) := by
  have hB := TwistKer2_Bctl_ge_inv sz n hu0 hu1
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have e : ∀ c : ℝ, ((sz.size n : ℕ) : ℝ) ^ (-c) = (((sz.size n : ℕ) : ℝ)⁻¹) ^ c := fun c => by
    rw [Real.rpow_neg hN.le, Real.inv_rpow hN.le]
  refine ⟨?_, ?_⟩
  · rw [e]; exact Real.rpow_le_rpow (inv_nonneg.2 hN.le) hB (by norm_num)
  · rw [e]; exact Real.rpow_le_rpow (inv_nonneg.2 hN.le) hB (by norm_num)

/-- `Λ₀ W^{2ε'} ≤ N^δ` eventually (`2ε' < δ`). -/
theorem TwistStep2_ev_lam (hN : Tendsto sz.size atTop atTop) (hd : 1 ≤ d) {Λ₀ δ ε' : ℝ} (hε' : 0 ≤ ε') (hδ : 2 * ε' < δ) :
    ∀ᶠ n in atTop, Λ₀ * ((sz.W n : ℕ) : ℝ) ^ (2 * ε') ≤ ((sz.size n : ℕ) : ℝ) ^ δ := by
  filter_upwards [TwistStep2_ev_ge sz hN (by linarith : 0 < δ - 2 * ε') Λ₀] with n hn
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  calc Λ₀ * ((sz.W n : ℕ) : ℝ) ^ (2 * ε') ≤ ((sz.size n : ℕ) : ℝ) ^ (δ - 2 * ε') * ((sz.size n : ℕ) : ℝ) ^ (2 * ε') :=
        mul_le_mul hn (Real.rpow_le_rpow hW0 (TwistStep2_W_le_N sz hd n) (by linarith)) (Real.rpow_nonneg hW0 _) (Real.rpow_nonneg (by linarith) _)
    _ = ((sz.size n : ℕ) : ℝ) ^ δ := by rw [← Real.rpow_add (by linarith)]; ring_nf

/-- `40 (N^{τ'/4})³ ≤ N^{τ'}` eventually. -/
theorem TwistStep2_ev_Ntau (hN : Tendsto sz.size atTop atTop) {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ n in atTop, 40 * (((sz.size n : ℕ) : ℝ) ^ (τ' / 4)) ^ 3 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' := by
  filter_upwards [TwistStep2_ev_ge sz hN (by linarith : 0 < τ' / 4) 40] with n hn
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have h1 : (((sz.size n : ℕ) : ℝ) ^ (τ' / 4)) ^ 3 * ((sz.size n : ℕ) : ℝ) ^ (τ' / 4) = ((sz.size n : ℕ) : ℝ) ^ τ' := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), ← Real.rpow_add (by linarith)]; ring_nf
  have h2 : 0 ≤ (((sz.size n : ℕ) : ℝ) ^ (τ' / 4)) ^ 3 := by positivity
  calc 40 * (((sz.size n : ℕ) : ℝ) ^ (τ' / 4)) ^ 3 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ' / 4) * (((sz.size n : ℕ) : ℝ) ^ (τ' / 4)) ^ 3 :=
        by nlinarith
    _ = _ := by rw [mul_comm]; exact h1

/-- `16 W^{1-D_d} ≤ B^{3/2}` eventually, `D_d = 2 + 2/𝔠`, `W ≥ N^𝔠`. -/
theorem TwistStep2_ev_theta (hN : Tendsto sz.size atTop atTop) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hband : sz.Bandwidth 𝔠) {τ : ℕ → ℝ}
    (hτ0 : ∀ n, 0 ≤ τ n) (hτ1 : ∀ n, τ n < 1) :
    ∀ᶠ n in atTop, 16 * ((sz.W n : ℕ) : ℝ) ^ (-(2 + 2 / 𝔠) + 1) ≤ sz.Bctl n (τ n) ^ (3 / 2 : ℝ) := by
  filter_upwards [hband, TwistStep2_ev_ge sz hN (by linarith : 0 < 𝔠 + 1 / 2) 16] with n hb hn
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := zero_lt_one.trans_le hN1
  have h1 := (TwistStep2_beta_ge sz n (hτ0 n) (hτ1 n)).1
  have hNc : 0 < ((sz.size n : ℕ) : ℝ) ^ 𝔠 := Real.rpow_pos_of_pos hNpos _
  have hneg : -(2 + 2 / 𝔠) + 1 ≤ 0 := by
    have : 0 < 2 / 𝔠 := by positivity
    linarith
  have h2 : ((sz.W n : ℕ) : ℝ) ^ (-(2 + 2 / 𝔠) + 1) ≤ (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (-(2 + 2 / 𝔠) + 1) :=
    Real.rpow_le_rpow_of_nonpos hNc hb hneg
  have h3 : (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (-(2 + 2 / 𝔠) + 1) = ((sz.size n : ℕ) : ℝ) ^ (-𝔠 - 2) := by
    rw [← Real.rpow_mul hNpos.le]; congr 1; field_simp; ring
  have h4 : 16 * ((sz.size n : ℕ) : ℝ) ^ (-𝔠 - 2) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
    have e : ((sz.size n : ℕ) : ℝ) ^ (-𝔠 - 2) * ((sz.size n : ℕ) : ℝ) ^ (𝔠 + 1 / 2) = ((sz.size n : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_add hNpos]; ring_nf
    have hp : 0 < ((sz.size n : ℕ) : ℝ) ^ (-𝔠 - 2) := Real.rpow_pos_of_pos hNpos _
    calc 16 * ((sz.size n : ℕ) : ℝ) ^ (-𝔠 - 2) = ((sz.size n : ℕ) : ℝ) ^ (-𝔠 - 2) * 16 := mul_comm _ _
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-𝔠 - 2) * ((sz.size n : ℕ) : ℝ) ^ (𝔠 + 1 / 2) := mul_le_mul_of_nonneg_left hn hp.le
      _ = _ := e
  calc 16 * ((sz.W n : ℕ) : ℝ) ^ (-(2 + 2 / 𝔠) + 1) ≤ 16 * ((sz.size n : ℕ) : ℝ) ^ (-𝔠 - 2) := by
        rw [← h3]; exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ ≤ _ := h4.trans h1

/-- `16 N^δ √(N^{-D₂}) ≤ B^{3/2}` eventually (`2δ + 5 ≤ D₂`). -/
theorem TwistStep2_ev_Np (hN : Tendsto sz.size atTop atTop) {δ D₂ : ℝ} (hD₂ : 2 * δ + 5 ≤ D₂) {τ : ℕ → ℝ} (hτ0 : ∀ n, 0 ≤ τ n) (hτ1 : ∀ n, τ n < 1) :
    ∀ᶠ n in atTop, 16 * ((sz.size n : ℕ) : ℝ) ^ δ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-D₂)) ≤ sz.Bctl n (τ n) ^ (3 / 2 : ℝ) := by
  filter_upwards [TwistStep2_ev_ge sz hN (by norm_num : (0 : ℝ) < 1) 16] with n hn
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := zero_lt_one.trans_le hN1
  have h1 := (TwistStep2_beta_ge sz n (hτ0 n) (hτ1 n)).1
  have hn' : 16 ≤ ((sz.size n : ℕ) : ℝ) := by simpa using hn
  have e1 : Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-D₂)) = ((sz.size n : ℕ) : ℝ) ^ (-D₂ / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le]; ring_nf
  have e2 : ((sz.size n : ℕ) : ℝ) ^ δ * ((sz.size n : ℕ) : ℝ) ^ (-D₂ / 2) = ((sz.size n : ℕ) : ℝ) ^ (δ - D₂ / 2) := by
    rw [← Real.rpow_add hNpos]; ring_nf
  have h3 : ((sz.size n : ℕ) : ℝ) ^ (δ - D₂ / 2) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have e3 : ((sz.size n : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) = ((sz.size n : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * ((sz.size n : ℕ) : ℝ)⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hNpos]; ring_nf
  have hinv : 16 * ((sz.size n : ℕ) : ℝ)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hNpos]; exact hn'
  have hp : 0 < ((sz.size n : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos hNpos _
  calc 16 * ((sz.size n : ℕ) : ℝ) ^ δ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-D₂)) = 16 * (((sz.size n : ℕ) : ℝ) ^ δ * ((sz.size n : ℕ) : ℝ) ^ (-D₂ / 2)) := by
        rw [e1]; ring
    _ = 16 * ((sz.size n : ℕ) : ℝ) ^ (δ - D₂ / 2) := by rw [e2]
    _ ≤ 16 * (((sz.size n : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * ((sz.size n : ℕ) : ℝ)⁻¹) := by rw [← e3]; exact mul_le_mul_of_nonneg_left h3 (by norm_num)
    _ = ((sz.size n : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * (16 * ((sz.size n : ℕ) : ℝ)⁻¹) := by ring
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * 1 := mul_le_mul_of_nonneg_left hinv hp.le
    _ ≤ _ := by rw [mul_one]; exact h1

/-- `N^δ (3 W^{-D_a}) ≤ W^{-D_d}` eventually, `D_a = D_d + δ/𝔠 + 1`, `W ≥ N^𝔠`. -/
theorem TwistStep2_ev_decay (hN : Tendsto sz.size atTop atTop) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hband : sz.Bandwidth 𝔠) {δ Dd : ℝ} (hδ : 0 ≤ δ) :
    ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ δ * (3 * ((sz.W n : ℕ) : ℝ) ^ (-(Dd + δ / 𝔠 + 1))) ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dd) := by
  filter_upwards [hband, TwistStep2_ev_ge sz hN h𝔠 3] with n hb h3
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := zero_lt_one.trans_le hN1
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW3 : 3 ≤ ((sz.W n : ℕ) : ℝ) := h3.trans hb
  have hNW : ((sz.size n : ℕ) : ℝ) ^ δ ≤ ((sz.W n : ℕ) : ℝ) ^ (δ / 𝔠) := by
    have : ((sz.size n : ℕ) : ℝ) ^ δ = (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (δ / 𝔠) := by
      rw [← Real.rpow_mul hNpos.le]; congr 1; field_simp
    rw [this]; exact Real.rpow_le_rpow (Real.rpow_nonneg hNpos.le _) hb (by positivity)
  have e : ((sz.W n : ℕ) : ℝ) ^ (δ / 𝔠) * ((sz.W n : ℕ) : ℝ) ^ (-(Dd + δ / 𝔠 + 1)) = ((sz.W n : ℕ) : ℝ) ^ (-Dd - 1) := by
    rw [← Real.rpow_add hWpos]; ring_nf
  have e' : ((sz.W n : ℕ) : ℝ) ^ (-Dd - 1) = ((sz.W n : ℕ) : ℝ) ^ (-Dd) * ((sz.W n : ℕ) : ℝ)⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hWpos]; ring_nf
  have hp : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-(Dd + δ / 𝔠 + 1)) := Real.rpow_nonneg hWpos.le _
  have hp' : 0 < ((sz.W n : ℕ) : ℝ) ^ (-Dd) := Real.rpow_pos_of_pos hWpos _
  calc ((sz.size n : ℕ) : ℝ) ^ δ * (3 * ((sz.W n : ℕ) : ℝ) ^ (-(Dd + δ / 𝔠 + 1))) ≤ ((sz.W n : ℕ) : ℝ) ^ (δ / 𝔠) * (3 * ((sz.W n : ℕ) : ℝ) ^ (-(Dd + δ / 𝔠 + 1))) :=
        mul_le_mul_of_nonneg_right hNW (by positivity)
    _ = 3 * (((sz.W n : ℕ) : ℝ) ^ (δ / 𝔠) * ((sz.W n : ℕ) : ℝ) ^ (-(Dd + δ / 𝔠 + 1))) := by ring
    _ = 3 * (((sz.W n : ℕ) : ℝ) ^ (-Dd) * ((sz.W n : ℕ) : ℝ)⁻¹) := by rw [e, e']
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dd) := by
        have : 3 * ((sz.W n : ℕ) : ℝ)⁻¹ ≤ 1 := by rw [← div_eq_mul_inv, div_le_one hWpos]; exact hW3
        nlinarith

/-- `(K_n + 1) · #V ≤ N^{C+4}` (`#V` the number of labels) for `K_n = ⌈N^C⌉ + 1`, eventually. -/
theorem TwistStep2_ev_card (hN : Tendsto sz.size atTop atTop) {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ n in atTop, (((⌈((sz.size n : ℕ) : ℝ) ^ C⌉₊ + 1 + 1) * Fintype.card ((Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) : ℕ) : ℝ) ≤
      ((sz.size n : ℕ) : ℝ) ^ (C + 4) := by
  filter_upwards [TwistStep2_ev_ge sz hN (by norm_num : (0 : ℝ) < 1) 16] with n hn
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := zero_lt_one.trans_le hN1
  have hn' : 16 ≤ ((sz.size n : ℕ) : ℝ) := by simpa using hn
  have hNC : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C := Real.one_le_rpow hN1 hC
  have hcard := TwistStep_card_V sz n
  have hceil : (⌈((sz.size n : ℕ) : ℝ) ^ C⌉₊ : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  push_cast
  have h1 : ((⌈((sz.size n : ℕ) : ℝ) ^ C⌉₊ : ℝ) + 1 + 1) ≤ 4 * ((sz.size n : ℕ) : ℝ) ^ C := by linarith
  have e : ((sz.size n : ℕ) : ℝ) ^ (C + 4) = ((sz.size n : ℕ) : ℝ) ^ C * ((sz.size n : ℕ) : ℝ) ^ 3 * ((sz.size n : ℕ) : ℝ) := by
    rw [Real.rpow_add hNpos, show (4 : ℝ) = ((3 : ℕ) : ℝ) + 1 by norm_num, Real.rpow_add hNpos, Real.rpow_natCast, Real.rpow_one]
    ring
  rw [e]
  calc ((⌈((sz.size n : ℕ) : ℝ) ^ C⌉₊ : ℝ) + 1 + 1) * (Fintype.card ((Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) : ℝ) ≤
        (4 * ((sz.size n : ℕ) : ℝ) ^ C) * (4 * ((sz.size n : ℕ) : ℝ) ^ 3) := mul_le_mul h1 hcard (by positivity) (by positivity)
    _ = 16 * (((sz.size n : ℕ) : ℝ) ^ C * ((sz.size n : ℕ) : ℝ) ^ 3) := by ring
    _ ≤ ((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) ^ C * ((sz.size n : ℕ) : ℝ) ^ 3) := by
        exact mul_le_mul_of_nonneg_right hn' (by positivity)
    _ = _ := by ring

/-- `(Im m)⁻¹ log R ≤ N^δ` eventually (`1 ≤ R ≤ (2/κ) N`, `Im m ≥ κ`; `log N ≤ N^{δ/2}/(δ/2)`). -/
theorem TwistStep2_ev_im (hN : Tendsto sz.size atTop atTop) {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) {im R : ℕ → ℝ} (him : ∀ n, κ ≤ im n) (hR1 : ∀ n, 1 ≤ R n)
    (hRY : ∀ n, R n ≤ (2 / κ) * ((sz.size n : ℕ) : ℝ)) :
    ∀ᶠ n in atTop, (im n)⁻¹ * Real.log (R n) ≤ ((sz.size n : ℕ) : ℝ) ^ δ := by
  filter_upwards [TwistStep2_ev_ge sz hN hδ (2 * κ⁻¹ * |Real.log (2 / κ)|), TwistStep2_ev_ge sz hN (half_pos hδ) (4 * κ⁻¹ / δ)] with n h1 h2
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := zero_lt_one.trans_le hN1
  have hRpos : 0 < R n := zero_lt_one.trans_le (hR1 n)
  have himpos : 0 < im n := hκ.trans_le (him n)
  have hlog : Real.log (R n) ≤ |Real.log (2 / κ)| + ((sz.size n : ℕ) : ℝ) ^ (δ / 2) / (δ / 2) := by
    calc Real.log (R n) ≤ Real.log ((2 / κ) * ((sz.size n : ℕ) : ℝ)) := Real.log_le_log hRpos (hRY n)
      _ = Real.log (2 / κ) + Real.log ((sz.size n : ℕ) : ℝ) := Real.log_mul (by positivity) hNpos.ne'
      _ ≤ |Real.log (2 / κ)| + ((sz.size n : ℕ) : ℝ) ^ (δ / 2) / (δ / 2) :=
          add_le_add (le_abs_self _) (Real.log_le_rpow_div hNpos.le (half_pos hδ))
  have hinv : (im n)⁻¹ ≤ κ⁻¹ := inv_anti₀ hκ (him n)
  have hℓ0 : 0 ≤ Real.log (R n) := Real.log_nonneg (hR1 n)
  have hNδ : ((sz.size n : ℕ) : ℝ) ^ δ = ((sz.size n : ℕ) : ℝ) ^ (δ / 2) * ((sz.size n : ℕ) : ℝ) ^ (δ / 2) := by
    rw [← Real.rpow_add hNpos]; ring_nf
  have hp : 0 < ((sz.size n : ℕ) : ℝ) ^ (δ / 2) := Real.rpow_pos_of_pos hNpos _
  calc (im n)⁻¹ * Real.log (R n) ≤ κ⁻¹ * (|Real.log (2 / κ)| + ((sz.size n : ℕ) : ℝ) ^ (δ / 2) / (δ / 2)) :=
        mul_le_mul hinv hlog hℓ0 (by positivity)
    _ = κ⁻¹ * |Real.log (2 / κ)| + κ⁻¹ * (2 / δ) * ((sz.size n : ℕ) : ℝ) ^ (δ / 2) := by field_simp
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ δ / 2 + ((sz.size n : ℕ) : ℝ) ^ δ / 2 := by
        refine add_le_add (by nlinarith [h1]) ?_
        have : 2 * (κ⁻¹ * (2 / δ)) ≤ ((sz.size n : ℕ) : ℝ) ^ (δ / 2) := by
          calc 2 * (κ⁻¹ * (2 / δ)) = 4 * κ⁻¹ / δ := by field_simp; ring
            _ ≤ _ := h2
        rw [hNδ]
        nlinarith [mul_le_mul_of_nonneg_right this hp.le]
    _ = _ := by ring

/-- The terms of order `Δ` are smaller than the control: `16 · 18 √Δ N^{C₀} Y³ N (1 + Ξ) ≤ B^{3/2} + B^{5/3} Ξ` eventually, if `Δ ≤ N^{-CK}`, `CK ≥ 2 C₀ + 14`. -/
theorem TwistStep2_ev_small (hN : Tendsto sz.size atTop atTop) {κ C₀ CK : ℝ} (hκ : 0 < κ) (hCK : 2 * C₀ + 14 ≤ CK) {τ : ℕ → ℝ}
    (hτ0 : ∀ n, 0 ≤ τ n) (hτ1 : ∀ n, τ n < 1) {Δ : ℕ → ℝ} (hΔ : ∀ n, Δ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-CK)) (Ξ : ℕ → ℝ) (hΞ : ∀ n, 1 ≤ Ξ n) :
    ∀ᶠ n in atTop, 16 * (18 * Real.sqrt (Δ n) * ((sz.size n : ℕ) : ℝ) ^ C₀ * ((2 / κ) * ((sz.size n : ℕ) : ℝ)) ^ 3 * ((sz.size n : ℕ) : ℝ) * (1 + Ξ n)) ≤
      sz.Bctl n (τ n) ^ (3 / 2 : ℝ) + sz.Bctl n (τ n) ^ (5 / 3 : ℝ) * Ξ n := by
  filter_upwards [TwistStep2_ev_ge sz hN (by norm_num : (0 : ℝ) < 1) (288 * (2 / κ) ^ 3)] with n hn
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := zero_lt_one.trans_le hN1
  have hn' : 288 * (2 / κ) ^ 3 ≤ ((sz.size n : ℕ) : ℝ) := by simpa using hn
  obtain ⟨hb1, hb2⟩ := TwistStep2_beta_ge sz n (hτ0 n) (hτ1 n)
  have hΞ1 := hΞ n
  have hsq : Real.sqrt (Δ n) ≤ ((sz.size n : ℕ) : ℝ) ^ (-CK / 2) := by
    calc Real.sqrt (Δ n) ≤ Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-CK)) := Real.sqrt_le_sqrt (hΔ n)
      _ = _ := by rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le]; ring_nf
  have hN2 : ((sz.size n : ℕ) : ℝ) ^ (-(2 : ℝ)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hN2' : ((sz.size n : ℕ) : ℝ) ^ (-(2 : ℝ)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(5 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hrhs : ((sz.size n : ℕ) : ℝ) ^ (-(2 : ℝ)) * (1 + Ξ n) ≤ sz.Bctl n (τ n) ^ (3 / 2 : ℝ) + sz.Bctl n (τ n) ^ (5 / 3 : ℝ) * Ξ n := by
    have hp : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-(2 : ℝ)) := Real.rpow_nonneg hNpos.le _
    nlinarith [mul_le_mul_of_nonneg_right (hN2.trans hb1) (by linarith : (0 : ℝ) ≤ 1), mul_le_mul_of_nonneg_right (hN2'.trans hb2) (by linarith : (0 : ℝ) ≤ Ξ n)]
  refine le_trans ?_ hrhs
  -- the left side
  have hY : ((2 / κ) * ((sz.size n : ℕ) : ℝ)) ^ 3 = (2 / κ) ^ 3 * ((sz.size n : ℕ) : ℝ) ^ 3 := by ring
  have e1 : ((sz.size n : ℕ) : ℝ) ^ (-CK / 2) * ((sz.size n : ℕ) : ℝ) ^ C₀ * ((sz.size n : ℕ) : ℝ) ^ (3 : ℕ) * ((sz.size n : ℕ) : ℝ) =
      ((sz.size n : ℕ) : ℝ) ^ (-CK / 2 + C₀ + 4) := by
    rw [Real.rpow_add hNpos, Real.rpow_add hNpos, show (4 : ℝ) = ((3 : ℕ) : ℝ) + 1 by norm_num, Real.rpow_add hNpos, Real.rpow_natCast, Real.rpow_one]
    ring
  have h3 : ((sz.size n : ℕ) : ℝ) ^ (-CK / 2 + C₀ + 4) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have e3 : ((sz.size n : ℕ) : ℝ) ^ (-(3 : ℝ)) = ((sz.size n : ℕ) : ℝ) ^ (-(2 : ℝ)) * ((sz.size n : ℕ) : ℝ)⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hNpos]; ring_nf
  have hc : 288 * (2 / κ) ^ 3 * ((sz.size n : ℕ) : ℝ)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hNpos]; exact hn'
  have hp2 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-(2 : ℝ)) := Real.rpow_nonneg hNpos.le _
  have hq : 0 ≤ 1 + Ξ n := by linarith
  calc 16 * (18 * Real.sqrt (Δ n) * ((sz.size n : ℕ) : ℝ) ^ C₀ * ((2 / κ) * ((sz.size n : ℕ) : ℝ)) ^ 3 * ((sz.size n : ℕ) : ℝ) * (1 + Ξ n))
      = (288 * (2 / κ) ^ 3) * (Real.sqrt (Δ n) * ((sz.size n : ℕ) : ℝ) ^ C₀ * ((sz.size n : ℕ) : ℝ) ^ (3 : ℕ) * ((sz.size n : ℕ) : ℝ)) * (1 + Ξ n) := by
        rw [hY]; ring
    _ ≤ (288 * (2 / κ) ^ 3) * (((sz.size n : ℕ) : ℝ) ^ (-CK / 2) * ((sz.size n : ℕ) : ℝ) ^ C₀ * ((sz.size n : ℕ) : ℝ) ^ (3 : ℕ) * ((sz.size n : ℕ) : ℝ)) * (1 + Ξ n) := by
        gcongr
    _ = (288 * (2 / κ) ^ 3) * ((sz.size n : ℕ) : ℝ) ^ (-CK / 2 + C₀ + 4) * (1 + Ξ n) := by rw [e1]
    _ ≤ (288 * (2 / κ) ^ 3) * (((sz.size n : ℕ) : ℝ) ^ (-(2 : ℝ)) * ((sz.size n : ℕ) : ℝ)⁻¹) * (1 + Ξ n) := by
        rw [← e3]; gcongr
    _ = (288 * (2 / κ) ^ 3 * ((sz.size n : ℕ) : ℝ)⁻¹) * (((sz.size n : ℕ) : ℝ) ^ (-(2 : ℝ)) * (1 + Ξ n)) := by ring
    _ ≤ 1 * (((sz.size n : ℕ) : ℝ) ^ (-(2 : ℝ)) * (1 + Ξ n)) := by
        exact mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := one_mul _

end FA


/-- The final probability arithmetic: `N^{-(D+1)} + c N^{-D₂} ≤ N^{-D}` for `c ≤ 4 N³`, `D₂ = D + δ + 8`, `N ≥ 2`, `2 N^{-(D+1)} ≤ N^{-D}`. -/
theorem TwistStep2_prob_arith {N δ D D₂ c : ℝ} (hN2 : 2 ≤ N) (hδ : 0 ≤ δ) (hD₂ : D₂ = D + δ + 8) (hc : c ≤ 4 * N ^ 3)
    (h2N : 2 * N ^ (-(D + 1)) ≤ N ^ (-D)) : N ^ (-(D + 1)) + c * N ^ (-D₂) ≤ N ^ (-D) := by
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hN4 : (16 : ℝ) ≤ N ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN2 4
    norm_num at this
    exact this
  have e1 : N ^ 3 * N ^ (-D₂) = N ^ (-(D + 1)) * N ^ (-(δ + 4)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    congr 1
    rw [hD₂]; push_cast; ring
  have h4 : N ^ (-(δ + 4)) ≤ N ^ (-(4 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have h5 : N ^ (-(4 : ℝ)) ≤ 1 / 16 := by
    rw [Real.rpow_neg hNpos.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) hN4
  have hp1 : 0 < N ^ (-(D + 1)) := Real.rpow_pos_of_pos hNpos _
  have hp2 : 0 ≤ N ^ (-D₂) := Real.rpow_nonneg hNpos.le _
  have h6 : c * N ^ (-D₂) ≤ (4 * N ^ 3) * N ^ (-D₂) := mul_le_mul_of_nonneg_right hc hp2
  have h7 : (4 * N ^ 3) * N ^ (-D₂) = 4 * (N ^ (-(D + 1)) * N ^ (-(δ + 4))) := by rw [mul_assoc, e1]
  have h8 : N ^ (-(D + 1)) * N ^ (-(δ + 4)) ≤ N ^ (-(D + 1)) * (1 / 16) := mul_le_mul_of_nonneg_left (h4.trans h5) hp1.le
  linarith

/-! ## 2. The label function of the final bound, `R` along the flow -/

open private TwistKer2_conU TwistKer2_eta_inv_le from RBM3D.BA.TwistKer2
open private TwistGridTail_measurable_twL2M from RBM3D.BA.TwistGridTail

section Labels

variable {d : ℕ}

/-- The label function of the final bound: `‖(Pr Z_u(H))(a)‖` of the flow matrix `λ₀ Ψ + H`. -/
def TwistStep2_Zlab (sz : Sizes d) (z : ℕ → ℂ) (Pr : ∀ n, (Fin 2 → Bool) → Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) (n : ℕ)
    (v : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) (u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ :=
  ‖(Pr n v.1 *ᵥ fun b => twL2M sz (BAflowLam0 sz z) (BAflowEs sz z) n u ((BAflowLam0 sz z n : ℂ) • PsiI d (sz.L n) (sz.W n) + H) v.1 b v.2.2.1 v.2.2.2 -
    twK (baFM sz (BAflowLam0 sz z) (BAflowEs sz z)) n u v.1 b v.2.2.1 v.2.2.2) v.2.1‖

theorem TwistStep2_measurable_Zlab (sz : Sizes d) (z : ℕ → ℂ) (Pr : ∀ n, (Fin 2 → Bool) → Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) (n : ℕ)
    (v : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) (u : ℝ) : Measurable (TwistStep2_Zlab sz z Pr n v u) := by
  unfold TwistStep2_Zlab
  refine Measurable.norm ?_
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.measurable_sum _ fun b _ => measurable_const.mul ?_
  exact ((TwistGridTail_measurable_twL2M sz (BAflowLam0 sz z) (BAflowEs sz z) n u v.1 b v.2.2.1 v.2.2.2).comp
    (TwistStep_measurable_shift sz n _)).sub_const _

/-- `1 ≤ (1-s)/(1-τ) ≤ (2/κ) N` along the flow. -/
theorem TwistStep2_R_bounds {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {sz : Sizes d} {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {s τ : ℕ → ℝ} (n : ℕ)
    (hs : 0 ≤ s n) (hsτ : s n ≤ τ n) (hτT : τ n ≤ BAflowT0 sz z n) :
    1 ≤ (1 - s n) / (1 - τ n) ∧ (1 - s n) / (1 - τ n) ≤ (2 / κ) * ((sz.size n : ℕ) : ℝ) := by
  have hτ1 : τ n < 1 := hτT.trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  have h1τ : 0 < 1 - τ n := by linarith
  have hm := EMn2BA_mF_data sz hflow n
  have him0 : 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := lt_of_lt_of_le hκ hm.1
  refine ⟨by rw [le_div_iff₀ h1τ]; linarith, ?_⟩
  have hη := TwistKer2_eta_inv_le hκ hε hflow n (hs.trans hsτ) hτT
  have hη' : (((1 - τ n) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im)⁻¹) ≤ (2 / κ) * ((sz.size n : ℕ) : ℝ) := hη
  refine le_trans ?_ (le_trans (inv_anti₀ (mul_pos h1τ him0) (mul_le_of_le_one_right h1τ.le hm.2)) hη')
  rw [div_eq_mul_inv]
  exact mul_le_of_le_one_left (inv_nonneg.2 h1τ.le) (by linarith)

/-- The label function at the last grid state is the component of `Pr A_K`. -/
theorem TwistStep2_Zlab_eq (sz : Sizes d) (z : ℕ → ℂ) (Pr : ∀ n, (Fin 2 → Bool) → Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) (s τ : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (hK : K n ≠ 0) (ω : PathΩ (sz.withLam 0)) (v : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) :
    TwistStep2_Zlab sz z Pr n v (τ n) (pathH (sz.withLam 0) s τ K n (K n) ω) =
      ‖(Pr n v.1 *ᵥ twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s τ K n v.1 v.2.2.1 v.2.2.2 (K n) ω) v.2.1‖ := by
  have hlast : gridTime s τ K n (K n) = τ n := gridTime_last s τ K n hK
  have h : twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s τ K n v.1 v.2.2.1 v.2.2.2 (K n) ω =
      fun b => twL2M sz (BAflowLam0 sz z) (BAflowEs sz z) n (τ n) ((BAflowLam0 sz z n : ℂ) • PsiI d (sz.L n) (sz.W n) +
          (show Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ from pathH (sz.withLam 0) s τ K n (K n) ω)) v.1 b v.2.2.1 v.2.2.2 -
        twK (baFM sz (BAflowLam0 sz z) (BAflowEs sz z)) n (τ n) v.1 b v.2.2.1 v.2.2.2 := by
    unfold twAk
    rw [hlast]
    rfl
  rw [h]
  rfl

end Labels

/-! ## 3. The assembly of the probability bounds -/

section Main

variable {d : ℕ}

/-- **The assembly of the probability bounds**: for every `τ' > 0`, `D > 0`, the grid walk over `[s, τ]` with `K_n = ⌈N^{CK}⌉ + 1` gives `‖(Pr Z_τ)(a)‖ ≺ B^{3/2} (1 + B^{1/6} Ξ)` at the model:
the six events (`TwistStep_events_hp`), the remainder (clause (ii) of `BATwistGridMartAt`) and the `Ũ`-weighted tail (clause (iv)), the deterministic core `TwistStep_det_n`, the transport `TwistStep_model_le`. -/
theorem TwistStep2_main (hd : 3 ≤ d) {κ ε 𝔠 𝔡 𝔠d : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (h𝔠d : 0 < 𝔠d) (h𝔠d8 : 𝔠d ≤ 1 / 8)
    {sz : Sizes d} {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {s t τ : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (hsτ : ∀ n, s n ≤ τ n) (hτt : ∀ n, τ n ≤ t n) (htT : ∀ n, t n ≤ BAflowT0 sz z n) (hcon : sz.STConStInd 𝔠d s t)
    (Ξ : ℕ → ℝ) (hΞ : ∀ n, 1 ≤ Ξ n)
    (Pr : ∀ n, (Fin 2 → Bool) → Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) (hPr : ∀ n σ (x : Zd d (sz.L n) → ℂ), ‖Pr n σ *ᵥ x‖ ≤ 2 * ‖x‖)
    (hL0 : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n v ω => TwistStep_Fz sz (BAflowLam0 sz z) (BAflowEs sz z) n v (s n) ((sz.withLam 0).seqHflow n (s n) ω)) (fun n _ _ => sz.Bctl n (s n) ^ (3 / 2 : ℝ)))
    (hZ : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => TimeIcc s t n × ((Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)))
      (fun n p ω => TwistStep_Fz sz (BAflowLam0 sz z) (BAflowEs sz z) n p.2 (p.1 : ℝ) ((sz.withLam 0).seqHflow n (p.1 : ℝ) ω))
      (fun n p _ => Ξ n * sz.Bctl n (p.1 : ℝ) ^ (3 / 2 : ℝ)))
    (hS : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => TimeIcc s t n × ((Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)))
      (fun n p ω => TwistStep_Fs sz (BAflowLam0 sz z) (BAflowEs sz z) n p.2 (p.1 : ℝ) ((sz.withLam 0).seqHflow n (p.1 : ℝ) ω))
      (fun n p _ => ((1 - (p.1 : ℝ)) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im)⁻¹ *
        (2 * sz.Bctl n (p.1 : ℝ) ^ 2 + Ξ n * sz.Bctl n (p.1 : ℝ) ^ (5 / 3 : ℝ))))
    (hQ : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => TimeIcc s t n × ((Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)))
      (fun n p ω => TwistStep_Fq sz (BAflowLam0 sz z) (BAflowEs sz z) n p.2 (p.1 : ℝ) ((sz.withLam 0).seqHflow n (p.1 : ℝ) ω))
      (fun n p _ => ((1 - (p.1 : ℝ)) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im)⁻¹ * sz.Bctl n (p.1 : ℝ) ^ (13 / 4 : ℝ)))
    (hD0 : ∀ ε' Da : ℝ, 0 < ε' → 0 < Da → PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n v ω => TwistStep_Fzd sz (BAflowLam0 sz z) (BAflowEs sz z) n ε' v (s n) ((sz.withLam 0).seqHflow n (s n) ω))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-Da)))
    (hDS : ∀ ε' Da : ℝ, 0 < ε' → 0 < Da → PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => TimeIcc s t n × ((Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)))
      (fun n p ω => TwistStep_Fsd sz (BAflowLam0 sz z) (BAflowEs sz z) n ε' p.2 (p.1 : ℝ) ((sz.withLam 0).seqHflow n (p.1 : ℝ) ω))
      (fun n p _ => 3 * ((sz.W n : ℕ) : ℝ) ^ (-Da)))
    (hKL : ∀ ε' Dd : ℝ, 0 < ε' → ε' < 1 / 4 → 1 < Dd → ∃ Λ₀ : ℝ, 0 ≤ Λ₀ ∧ ∀ᶠ n in atTop, ∀ (σ : Fin 2 → Bool) (c₁ : Zd d (sz.L n)) (v : ℝ), s n ≤ v → v ≤ τ n →
      ∀ x : Zd d (sz.L n) → ℂ, (∀ b, 3 * ((sz.W n : ℕ) : ℝ) ^ ε' * ellT (sz.L n) (sz.lam n) v ≤ (zdistInf d (sz.L n) (b - c₁) : ℝ) → ‖x b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dd)) →
      ‖Pr n σ *ᵥ (twU sz (BAflowLam0 sz z) (BAflowEs sz z) n σ v (τ n) *ᵥ x)‖ ≤
        Λ₀ * ((sz.W n : ℕ) : ℝ) ^ (4 * ε') * (sz.Bctl n (τ n) / sz.Bctl n v) * ‖x‖ + ((sz.W n : ℕ) : ℝ) ^ (-Dd + 1)) :
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p ω => ‖(Pr n p.1 *ᵥ fun b => twL2' (baFMz sz z) n (τ n) ω p.1 b p.2.2.1 p.2.2.2 - twK (baFMz sz z) n (τ n) p.1 b p.2.2.1 p.2.2.2) p.2.1‖)
      (fun n _ _ => sz.Bctl n (τ n) ^ (3 / 2 : ℝ) * (1 + sz.Bctl n (τ n) ^ (1 / 6 : ℝ) * Ξ n)) := by
  classical
  have hsize : Tendsto sz.size atTop atTop := tendsto_size sz hflow.1.2.2.1
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hband : sz.Bandwidth 𝔠 := hflow.1.2.2.2.1
  have hτT : ∀ n, τ n ≤ BAflowT0 sz z n := fun n => (hτt n).trans (htT n)
  have hτ1 : ∀ n, τ n < 1 := fun n => (hτT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  have hτ0 : ∀ n, 0 ≤ τ n := fun n => (hs n).trans (hsτ n)
  -- the case `τ' ≤ 1`
  have key : ∀ τ' : ℝ, 0 < τ' → τ' ≤ 1 → ∀ D : ℝ, 0 < D → ∀ᶠ n in atTop,
      Sizes.seqP (sz.withLam 0) (badSetAt sz.size (fun n (p : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) ω =>
        ‖(Pr n p.1 *ᵥ fun b => twL2' (baFMz sz z) n (τ n) ω p.1 b p.2.2.1 p.2.2.2 - twK (baFMz sz z) n (τ n) p.1 b p.2.2.1 p.2.2.2) p.2.1‖)
        (fun n _ _ => sz.Bctl n (τ n) ^ (3 / 2 : ℝ) * (1 + sz.Bctl n (τ n) ^ (1 / 6 : ℝ) * Ξ n)) τ' n) ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
    intro τ' hτ' hτ'1 D hD
    set δ : ℝ := τ' / 4 with hδdef
    have hδ : 0 < δ := by positivity
    have hδ1 : δ ≤ 1 / 4 := by linarith
    set ε' : ℝ := δ / 8 with hε'def
    have hε' : 0 < ε' := by positivity
    set Dd : ℝ := 2 + 2 / 𝔠 with hDddef
    have hDd1 : 1 < Dd := by
      have : 0 < 2 / 𝔠 := by positivity
      linarith
    set Da : ℝ := Dd + δ / 𝔠 + 1 with hDadef
    have hDa : 0 < Da := by
      have : 0 < δ / 𝔠 := by positivity
      linarith
    set D₂ : ℝ := D + δ + 8 with hD₂def
    --     -- the grid martingale clauses (ii) and (iv)
    obtain ⟨C₀, hC₀, hRemP⟩ := baTwistGridRem_holds d
    obtain ⟨CKr, hCKr, hRemK⟩ := hRemP κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s τ hs hsτ hτT
    obtain ⟨CKw, hCKw, hWK⟩ := baTwistGridWTail_holds d κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s τ hs hsτ hτT D₂ (by positivity)
    set CK : ℝ := max CKr (max CKw (2 * C₀ + 14)) with hCKdef
    have hCK0 : 0 ≤ CK := le_max_of_le_left hCKr
    set Kf : ℕ → ℕ := fun n => ⌈((sz.size n : ℕ) : ℝ) ^ CK⌉₊ + 1 with hKf
    have hK0 : ∀ n, Kf n ≠ 0 := fun n => Nat.succ_ne_zero _
    have hKN : ∀ n, ((sz.size n : ℕ) : ℝ) ^ CK ≤ Kf n := fun n => by
      have := Nat.le_ceil (((sz.size n : ℕ) : ℝ) ^ CK)
      simp only [hKf]; push_cast; linarith
    have hKmono : ∀ C : ℝ, C ≤ CK → ∀ n, ((sz.size n : ℕ) : ℝ) ^ C ≤ Kf n := fun C hC n =>
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast sz.one_le_size n) hC).trans (hKN n)
    have hRem := (hRemK Kf hK0 (Eventually.of_forall (hKmono CKr (le_max_left _ _)))).2
    have hWT := hWK Kf hK0 (Eventually.of_forall (hKmono CKw ((le_max_left _ _).trans (le_max_right _ _)))) δ hδ
    obtain ⟨Λ₀, hΛ₀, hKLev⟩ := hKL ε' Dd hε' (by linarith) hDd1
    -- the six events and the eventual arithmetic
    have hβ1ev : ∀ᶠ n in atTop, sz.Bctl n (τ n) ≤ 1 := by
      filter_upwards [hcon] with n hn
      exact (TwistKer2_conU sz n h𝔠d hn (hτt n) ((htT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n))).2.1
    have hHP := TwistStep_events_hp sz z s τ Kf hκ hflow hs hsτ hτt htT hK0 (C := CK + 4) (by linarith) (TwistStep2_ev_card sz hsize hCK0) Ξ hΞ hδ hβ1ev
      (TwistStep2_ev_decay sz hsize h𝔠 hband hδ.le) hL0 hZ hS hQ (hD0 ε' Da hε' hDa) (hDS ε' Da hε' hDa)
    have hΔ : ∀ n, gridStep s τ Kf n ≤ ((sz.size n : ℕ) : ℝ) ^ (-CK) := by
      intro n
      have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
      have hNC : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ CK := Real.one_le_rpow hN1 hCK0
      have hKpos : (0 : ℝ) < (Kf n : ℝ) := lt_of_lt_of_le (by linarith) (hKN n)
      have h1 : τ n - s n ≤ 1 := by linarith [hτ1 n, hs n]
      calc gridStep s τ Kf n = (τ n - s n) / (Kf n : ℝ) := rfl
        _ ≤ 1 / (Kf n : ℝ) := div_le_div_of_nonneg_right h1 hKpos.le
        _ ≤ 1 / ((sz.size n : ℕ) : ℝ) ^ CK := one_div_le_one_div_of_le (by linarith) (hKN n)
        _ = ((sz.size n : ℕ) : ℝ) ^ (-CK) := by rw [Real.rpow_neg (by linarith), one_div]
    have hlam0ev : ∀ᶠ n in atTop, 0 ≤ sz.lam n := by
      filter_upwards [hflow.1.2.2.2.2] with n hn
      exact (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans hn.1
    have a2 := TwistStep2_ev_lam sz hsize (by omega : 1 ≤ d) (Λ₀ := Λ₀) (ε' := 2 * ε') (by linarith) (by linarith : 2 * (2 * ε') < δ)
    have e4 : 2 * (2 * ε') = 4 * ε' := by ring
    rw [e4] at a2
    have a3 := TwistStep2_ev_Ntau sz hsize hτ'
    have a4 := TwistStep2_ev_im sz hsize hκ hδ (im := fun n => (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im) (R := fun n => (1 - s n) / (1 - τ n))
      (fun n => (EMn2BA_mF_data sz hflow n).1) (fun n => (TwistStep2_R_bounds hκ hε hflow n (hs n) (hsτ n) (hτT n)).1)
      (fun n => (TwistStep2_R_bounds hκ hε hflow n (hs n) (hsτ n) (hτT n)).2)
    have a5 := TwistStep2_ev_theta sz hsize h𝔠 hband hτ0 hτ1
    have a6 := TwistStep2_ev_Np sz hsize (δ := δ) (D₂ := D₂) (by linarith) hτ0 hτ1
    have a7 := TwistStep2_ev_small sz hsize (κ := κ) (C₀ := C₀) (CK := CK) hκ (le_max_of_le_right (le_max_right _ _)) hτ0 hτ1 (Δ := fun n => gridStep s τ Kf n) hΔ Ξ hΞ
    have hD1 := hHP (D + 1) (by linarith)
    filter_upwards [hD1, hRem, hWT, hKLev, hcon, hlam0ev, a2, a3, a4, a5, a6, a7, hsize.eventually (eventually_two_mul_rpow_le D), hsize.eventually (eventually_ge_atTop 2)] with n h1 hrem hwt hkl hconn hlam a2 a3 a4 a5 a6 a7 h2N hN2
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := zero_lt_one.trans_le hN1
    have hNδ1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ δ := Real.one_le_rpow hN1 hδ.le
    have hNδN : ((sz.size n : ℕ) : ℝ) ^ δ ≤ ((sz.size n : ℕ) : ℝ) :=
      calc ((sz.size n : ℕ) : ℝ) ^ δ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
        _ = _ := Real.rpow_one _
    have hΛ0 : 0 ≤ Λ₀ * ((sz.W n : ℕ) : ℝ) ^ (4 * ε') := mul_nonneg hΛ₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hθ0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dd + 1) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hNp0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₂) := Real.rpow_nonneg hNpos.le _
    have hdet := TwistStep_det_n sz z s τ Kf n hκ hε hflow h𝔠d h𝔠d8 (hs n) (hsτ n) (hτt n) (htT n) (hK0 n) hlam hconn (Pr n) (hPr n)
      (Ξ := Ξ n) (Nδ := ((sz.size n : ℕ) : ℝ) ^ δ) (Nτ := ((sz.size n : ℕ) : ℝ) ^ τ') (Λ := Λ₀ * ((sz.W n : ℕ) : ℝ) ^ (4 * ε')) (θ := ((sz.W n : ℕ) : ℝ) ^ (-Dd + 1))
      (Np := ((sz.size n : ℕ) : ℝ) ^ (-D₂)) (ρ := ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s τ Kf n)) (ε' := ε') (Dd := Dd) (C₀ := C₀)
      (hΞ n) hNδ1 hNδN a2 hNp0 a3 a4 a5 a6 rfl hC₀ a7 hkl hΛ0 hθ0
    have hlast : gridTime s τ Kf n (Kf n) = τ n := gridTime_last s τ Kf n (hK0 n)
    set Good1set : Set (PathΩ (sz.withLam 0)) := {ω | TwistStep_Good1 sz z s τ Kf n (Ξ n) (((sz.size n : ℕ) : ℝ) ^ δ) ε' Dd ω} with hG1def
    set W8 : ((Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) → Set (PathΩ (sz.withLam 0)) := fun i =>
      {ω | ∃ k ≤ Kf n, ((sz.size n : ℕ) : ℝ) ^ δ * (∑ j ∈ Finset.range k, gridStep s τ Kf n *
        ‖twEEUk sz (BAflowLam0 sz z) (BAflowEs sz z) s τ Kf n i.1 i.2.1 i.2.2.1 i.2.2.2 j k ω‖ + ((sz.size n : ℕ) : ℝ) ^ (-D₂)) ^ (1 / 2 : ℝ) <
        ‖(∑ j ∈ Finset.range k, twU sz (BAflowLam0 sz z) (BAflowEs sz z) n i.1 (gridTime s τ Kf n j) (gridTime s τ Kf n k) *ᵥ
          fun b => twMart sz (BAflowLam0 sz z) (BAflowEs sz z) s τ Kf n i.1 b i.2.2.1 i.2.2.2 (j + 1) ω -
            twMart sz (BAflowLam0 sz z) (BAflowEs sz z) s τ Kf n i.1 b i.2.2.1 i.2.2.2 j ω) i.2.1‖} with hW8
    set N9 : Set (PathΩ (sz.withLam 0)) := {ω | ¬ ∀ i : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n), ∀ k ≤ Kf n,
      ‖twRem sz (BAflowLam0 sz z) (BAflowEs sz z) s τ Kf n i.1 i.2.1 i.2.2.1 i.2.2.2 k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s τ Kf n)} with hN9
    -- the complement of the good set
    have hcompl : {ω | TwistStep_Good sz z s τ Kf n (Ξ n) (((sz.size n : ℕ) : ℝ) ^ δ) (((sz.size n : ℕ) : ℝ) ^ (-D₂))
        (((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s τ Kf n)) ε' Dd ω}ᶜ ⊆ Good1setᶜ ∪ ((⋃ i, W8 i) ∪ N9) := by
      intro ω hω
      by_contra hno
      simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not, Set.mem_iUnion, not_exists] at hno
      obtain ⟨hG1, hW, hR9⟩ := hno
      refine hω ⟨hG1, ?_, ?_⟩
      · intro σ c₁ c₂ a
        have h := hW (σ, a, c₁, c₂)
        simp only [hW8, Set.mem_ofPred_eq, not_exists, not_and, not_lt] at h
        have h' := h (Kf n) le_rfl
        rw [hlast] at h'
        exact h'
      · intro σ c₁ c₂ k hk
        refine (pi_norm_le_iff_of_nonneg (mul_nonneg (Real.rpow_nonneg hNpos.le _) (Real.sqrt_nonneg _))).2 fun a => ?_
        have h9 : ¬ ¬ ∀ i : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n), ∀ k ≤ Kf n,
            ‖twRem sz (BAflowLam0 sz z) (BAflowEs sz z) s τ Kf n i.1 i.2.1 i.2.2.1 i.2.2.2 k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s τ Kf n) := hR9
        exact (not_not.1 h9) (σ, a, c₁, c₂) k hk
    -- the probabilities
    have hP2 : pathP (sz.withLam 0) (⋃ i, W8 i) ≤ ENNReal.ofReal ((Fintype.card ((Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) : ℝ) *
        ((sz.size n : ℕ) : ℝ) ^ (-D₂)) := by
      refine (measure_iUnion_fintype_le _ _).trans ?_
      calc ∑ i, pathP (sz.withLam 0) (W8 i) ≤ ∑ _i : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n), ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₂)) :=
            Finset.sum_le_sum fun i _ => hwt i
        _ = ENNReal.ofReal ((Fintype.card ((Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-D₂)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    have hP3 : pathP (sz.withLam 0) N9 = 0 := ae_iff.1 (ae_all_iff.2 hrem)
    have hreal : ((sz.size n : ℕ) : ℝ) ^ (-(D + 1)) + (Fintype.card ((Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-D₂) ≤
        ((sz.size n : ℕ) : ℝ) ^ (-D) :=
      TwistStep2_prob_arith (by exact_mod_cast hN2) hδ.le rfl (TwistStep_card_V sz n) h2N
    have hfinal : pathP (sz.withLam 0) (Good1setᶜ ∪ ((⋃ i, W8 i) ∪ N9)) ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
      calc pathP (sz.withLam 0) (Good1setᶜ ∪ ((⋃ i, W8 i) ∪ N9)) ≤ pathP (sz.withLam 0) Good1setᶜ + (pathP (sz.withLam 0) (⋃ i, W8 i) + pathP (sz.withLam 0) N9) :=
            (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
        _ ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D + 1))) + (ENNReal.ofReal ((Fintype.card ((Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) : ℝ) *
            ((sz.size n : ℕ) : ℝ) ^ (-D₂)) + 0) := add_le_add h1 (add_le_add hP2 hP3.le)
        _ = ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D + 1)) + (Fintype.card ((Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-D₂)) := by
            rw [add_zero, ENNReal.ofReal_add (Real.rpow_nonneg hNpos.le _) (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hNpos.le _))]
        _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
    -- the good set gives the bound for every label, the model probability is bounded through the grid walk
    have hgood : ∀ ω ∈ {ω | TwistStep_Good sz z s τ Kf n (Ξ n) (((sz.size n : ℕ) : ℝ) ^ δ) (((sz.size n : ℕ) : ℝ) ^ (-D₂))
        (((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s τ Kf n)) ε' Dd ω}, ∀ v : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n),
        TwistStep2_Zlab sz z Pr n v (τ n) (pathH (sz.withLam 0) s τ Kf n (Kf n) ω) ≤ ((sz.size n : ℕ) : ℝ) ^ τ' *
          (sz.Bctl n (τ n) ^ (3 / 2 : ℝ) * (1 + sz.Bctl n (τ n) ^ (1 / 6 : ℝ) * Ξ n)) := by
      intro ω hω v
      have h := hdet ω hω v.1 v.2.2.1 v.2.2.2
      rw [TwistStep2_Zlab_eq sz z Pr s τ Kf n (hK0 n) ω v]
      exact (norm_le_pi_norm _ _).trans h
    have hmodel := TwistStep_model_le (sz.withLam 0) s τ Kf hs hsτ hK0 n (V := fun n => (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
      (TwistStep2_Zlab sz z Pr) (TwistStep2_measurable_Zlab sz z Pr) τ' (sz.Bctl n (τ n) ^ (3 / 2 : ℝ) * (1 + sz.Bctl n (τ n) ^ (1 / 6 : ℝ) * Ξ n))
      {ω | TwistStep_Good sz z s τ Kf n (Ξ n) (((sz.size n : ℕ) : ℝ) ^ δ) (((sz.size n : ℕ) : ℝ) ^ (-D₂)) (((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s τ Kf n)) ε' Dd ω} hgood
    calc _ ≤ Sizes.seqP (sz.withLam 0) {ω | ∃ v : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n), ((sz.size n : ℕ) : ℝ) ^ τ' *
          (sz.Bctl n (τ n) ^ (3 / 2 : ℝ) * (1 + sz.Bctl n (τ n) ^ (1 / 6 : ℝ) * Ξ n)) < TwistStep2_Zlab sz z Pr n v (τ n) ((sz.withLam 0).seqHflow n (τ n) ω)} :=
          measure_mono (fun ω hω => hω)
      _ ≤ _ := hmodel
      _ ≤ _ := measure_mono hcompl
      _ ≤ _ := hfinal
  -- all `τ' > 0`: `badSetAt τ' ⊆ badSetAt (min τ' 1)`
  intro τ' hτ' D hD
  filter_upwards [key (min τ' 1) (lt_min hτ' one_pos) (min_le_right _ _) D hD] with n hn
  refine le_trans (measure_mono ?_) hn
  rintro ω ⟨u, hu⟩
  refine ⟨u, lt_of_le_of_lt ?_ hu⟩
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hβ0 : 0 < sz.Bctl n (τ n) := st_Bctl_pos sz (hτ1 n)
  have hξ0 : 0 ≤ sz.Bctl n (τ n) ^ (3 / 2 : ℝ) * (1 + sz.Bctl n (τ n) ^ (1 / 6 : ℝ) * Ξ n) := by
    have := hΞ n
    positivity
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN1 (min_le_left _ _)) hξ0

end Main

/-! ## 4. `BATwistStepFixed` from the regime input: the grid-walk clauses, the sources, the decomposition `Z = Pr Z + (1 - Pr) Z` -/

section Pin

variable {d : ℕ}

/-- `Z_u(·)(σ, c₁, c₂) = L̃ - K̃` as a vector in `a`. -/
def TwistStep2_Zvec (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) : Zd d (sz.L n) → ℂ :=
  fun b => twL2' (baFMz sz z) n u ω σ b c₁ c₂ - twK (baFMz sz z) n u σ b c₁ c₂

/-- **The regime-dependent input of `BATwistStepFixed`** (the kernel losses of the three charge cases): at the frame data and a time sequence `τ ∈ [s, t]` there is a family of
projections `Pr` (`‖Pr x‖ ≤ 2‖x‖`) such that (1) `Ũ_{v,τ}` followed by `Pr` loses at most `Λ₀ W^{4ε'} B_τ/B_v` on vectors with the decay `twDec` of the sources (`hKL`) and (2) the part `(1 - Pr) Z_τ` (the zero mode) is `≺ B_τ^{3/2}`. -/
def TwistStep2_Ker (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 𝔠d : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → 0 < 𝔠d → (d : ℝ) * 𝔠d < 1 →
    ∀ s t τ : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, s n ≤ τ n) → (∀ n, τ n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → R sz s t →
      sz.STConStInd 𝔠d s t → ∀ Cd : ℝ, twSteps (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd →
      ∃ Pr : ∀ n, (Fin 2 → Bool) → Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ,
        (∀ n σ (x : Zd d (sz.L n) → ℂ), ‖Pr n σ *ᵥ x‖ ≤ 2 * ‖x‖) ∧
        (∀ ε' Dd : ℝ, 0 < ε' → ε' < 1 / 4 → 1 < Dd → ∃ Λ₀ : ℝ, 0 ≤ Λ₀ ∧ ∀ᶠ n in atTop, ∀ (σ : Fin 2 → Bool) (c₁ : Zd d (sz.L n)) (v : ℝ), s n ≤ v → v ≤ τ n →
          ∀ x : Zd d (sz.L n) → ℂ, (∀ b, 3 * ((sz.W n : ℕ) : ℝ) ^ ε' * ellT (sz.L n) (sz.lam n) v ≤ (zdistInf d (sz.L n) (b - c₁) : ℝ) → ‖x b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dd)) →
            ‖Pr n σ *ᵥ (twU sz (BAflowLam0 sz z) (BAflowEs sz z) n σ v (τ n) *ᵥ x)‖ ≤
              Λ₀ * ((sz.W n : ℕ) : ℝ) ^ (4 * ε') * (sz.Bctl n (τ n) / sz.Bctl n v) * ‖x‖ + ((sz.W n : ℕ) : ℝ) ^ (-Dd + 1)) ∧
        PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
          (fun n p ω => ‖((1 - Pr n p.1) *ᵥ TwistStep2_Zvec sz z n (τ n) ω p.1 p.2.2.1 p.2.2.2) p.2.1‖) (fun n _ _ => sz.Bctl n (τ n) ^ (3 / 2 : ℝ))

/-- `≺` is monotone: a smaller left side and a larger control (pointwise). -/
theorem TwistStep2_prec_mono {sz : Sizes d} {μ : Measure sz.SeqΩ} {U : ℕ → Type*} {ξ ξ' ζ ζ' : ∀ n, U n → sz.SeqΩ → ℝ}
    (hξ : ∀ n u ω, ξ' n u ω ≤ ξ n u ω) (hζ : ∀ n u ω, ζ n u ω ≤ ζ' n u ω) (h : PrecL sz μ ξ ζ) : PrecL sz μ ξ' ζ' :=
  StochDomAt.of_subset h fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω ⟨u, hu⟩ => ⟨u, lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (hζ n u ω) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (lt_of_lt_of_le hu (hξ n u ω))⟩⟩

theorem TwistStep2_prec_add3 {sz : Sizes d} {μ : Measure sz.SeqΩ} {U : ℕ → Type*} {ξ₁ ξ₂ ξ₃ ζ₁ ζ₂ ζ₃ : ∀ n, U n → sz.SeqΩ → ℝ}
    (hsize : Tendsto sz.size atTop atTop) (h₁ : PrecL sz μ ξ₁ ζ₁) (h₂ : PrecL sz μ ξ₂ ζ₂) (h₃ : PrecL sz μ ξ₃ ζ₃) :
    PrecL sz μ (fun n u ω => ξ₁ n u ω + ξ₂ n u ω + ξ₃ n u ω) (fun n u ω => ζ₁ n u ω + ζ₂ n u ω + ζ₃ n u ω) :=
  (StochDomAt.add hsize h₁ h₂).add hsize h₃

/-- The definitional bridges: the three-term source family of the grid walk is the sum of the model sources at `H = seqHflow`. -/
theorem TwistStep2_Fs_eq (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (v : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) (u : ℝ) (ω : sz.SeqΩ) :
    TwistStep_Fs sz (BAflowLam0 sz z) (BAflowEs sz z) n v u ((sz.withLam 0).seqHflow n u ω) =
      ‖twB1 (baFMz sz z) n u ω v.1 v.2.1 v.2.2.1 v.2.2.2‖ + ‖twB2 (baFMz sz z) n u ω v.1 v.2.1 v.2.2.1 v.2.2.2‖ +
        ‖twEG (baFMz sz z) n u ω v.1 v.2.1 v.2.2.1 v.2.2.2‖ := rfl

theorem TwistStep2_Fq_eq (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (v : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) (u : ℝ) (ω : sz.SeqΩ) :
    TwistStep_Fq sz (BAflowLam0 sz z) (BAflowEs sz z) n v u ((sz.withLam 0).seqHflow n u ω) =
      ‖twEE (baFMz sz z) n u ω v.1 v.2.1 v.2.1 v.2.2.1 v.2.2.2‖ := rfl

theorem TwistStep2_eta_eq (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (u : ℝ) :
    (baFMz sz z).eta n u = (1 - u) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := rfl

/-- **`BATwistStepFixed` from the regime input**: `BATwistStepFixed d R` for every regime `R` whose kernel input `TwistStep2_Ker d R` is given (the assembly `TwistStep2_main`, the five bounds `BATwistSrc1` to `BATwistSrc5` on the sources, the decomposition `Z = Pr Z + (1 - Pr) Z`). -/
theorem TwistStep2_pin (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (hK : TwistStep2_Ker d R) : BATwistStepFixed d R := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := baTwistSrc1_holds d R hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₂, hc₂, hc₂', H₂⟩ := baTwistSrc2_holds d R hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₃, hc₃, hc₃', H₃⟩ := baTwistSrc3_holds d R hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₄, hc₄, hc₄', H₄⟩ := baTwistSrc4_holds d R hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₅, hc₅, hc₅', H₅⟩ := baTwistSrc5_holds d R hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have h2d : 0 < 1 / (2 * (d : ℝ)) := by positivity
  have h𝔠dpos : 0 < min c₁ (min c₂ (min c₃ (min c₄ (min c₅ (1 / (2 * (d : ℝ))))))) :=
    lt_min hc₁ (lt_min hc₂ (lt_min hc₃ (lt_min hc₄ (lt_min hc₅ h2d))))
  refine ⟨min c₁ (min c₂ (min c₃ (min c₄ (min c₅ (1 / (2 * (d : ℝ))))))), h𝔠dpos, (min_le_left _ _).trans hc₁', ?_⟩
  intro 𝔠 sz z hflow s t hs hst htT hR hcon hsteps hloop Ξ hΞ hΞb τ hsτ hτt
  have hsize := tendsto_size sz hflow.1.2.2.1
  set 𝔠d := min c₁ (min c₂ (min c₃ (min c₄ (min c₅ (1 / (2 * (d : ℝ))))))) with h𝔠ddef
  have hle : 𝔠d ≤ c₁ ∧ 𝔠d ≤ c₂ ∧ 𝔠d ≤ c₃ ∧ 𝔠d ≤ c₄ ∧ 𝔠d ≤ c₅ ∧ 𝔠d ≤ 1 / (2 * (d : ℝ)) := by
    simp [h𝔠ddef]
  have hd𝔠 : (d : ℝ) * 𝔠d < 1 := by
    have h1 : (d : ℝ) * 𝔠d ≤ (d : ℝ) * (1 / (2 * (d : ℝ))) := mul_le_mul_of_nonneg_left hle.2.2.2.2.2 hd0.le
    have h2 : (d : ℝ) * (1 / (2 * (d : ℝ))) = 1 / 2 := by field_simp
    linarith
  have h𝔠d8 : 𝔠d ≤ 1 / 8 := by linarith [hle.1, hc₁']
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  have hmono : ∀ c : ℝ, 𝔠d ≤ c → sz.STConStInd c s t := fun c hc => st5_conStInd_mono sz hcon ht1 h𝔠dpos hc
  have E1 := H₁ 𝔠 sz z hflow s t hs hst htT hR (hmono c₁ hle.1) hsteps
  have E2 := H₂ 𝔠 sz z hflow s t hs hst htT hR (hmono c₂ hle.2.1) hsteps
  have E3 := H₃ 𝔠 sz z hflow s t hs hst htT hR (hmono c₃ hle.2.2.1) hsteps
  have E4 := H₄ 𝔠 sz z hflow s t hs hst htT hR (hmono c₄ hle.2.2.2.1) hsteps
  have E5 := H₅ 𝔠 sz z hflow s t hs hst htT hR (hmono c₅ hle.2.2.2.2.1) hsteps
  obtain ⟨Pr, hPr, hKL, hPZ⟩ := hK hd κ ε 𝔡 hκ hε h𝔡 𝔠 𝔠d sz z hflow h𝔠dpos hd𝔠 s t τ hs hst hsτ hτt htT hR hcon Cd hsteps
  have hmain : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p ω => ‖(Pr n p.1 *ᵥ TwistStep2_Zvec sz z n (τ n) ω p.1 p.2.2.1 p.2.2.2) p.2.1‖)
      (fun n _ _ => sz.Bctl n (τ n) ^ (3 / 2 : ℝ) * (1 + sz.Bctl n (τ n) ^ (1 / 6 : ℝ) * Ξ n)) := by
    refine TwistStep2_main hd hκ hε h𝔡 h𝔠dpos h𝔠d8 hflow hs hsτ hτt htT hcon Ξ hΞ Pr hPr ?_ ?_ ?_ ?_ ?_ ?_ hKL
    · exact hloop
    · exact hΞb
    · -- the sources `B̃₁ + B̃₂ + Ẽ^{G̊}`
      have E4' := TwistStep_src4_det hκ hε hflow hs htT E4 Ξ hΞ hΞb
      refine TwistStep2_prec_mono (fun n p ω => le_of_eq (TwistStep2_Fs_eq sz z n p.2 (p.1 : ℝ) ω)) (fun n p ω => ?_) (TwistStep2_prec_add3 hsize E1 E4' E2)
      have e32 : (3 / 2 + 1 / 6 : ℝ) = 5 / 3 := by norm_num
      simp only [e32, Real.rpow_two, TwistStep2_eta_eq]
      exact le_of_eq (by ring)
    · -- the quadratic variation
      have E3' := E3.1 2 2 (by norm_num) (by norm_num)
      refine TwistStep2_prec_mono (fun n p ω => le_of_eq (TwistStep2_Fq_eq sz z n p.2 (p.1 : ℝ) ω)) (fun n p ω => ?_) E3'
      have e : (4 - 1 / (2 * ((2 : ℕ) : ℝ)) - 1 / ((2 : ℕ) : ℝ) : ℝ) = 13 / 4 := by norm_num
      simp only [e, TwistStep2_eta_eq]
      exact le_of_eq (by ring)
    · -- the decay of `Z` at the initial time
      intro ε' Da hε' hDa
      exact (E5.2.2.2.1 ε' Da hε' hDa).precomp_param (fun n v => (⟨s n, le_rfl, (hst n).le⟩, v))
    · -- the decay of the sources
      intro ε' Da hε' hDa
      have hD3 := TwistStep2_prec_add3 hsize (E5.1 ε' Da hε' hDa) (E5.2.1 ε' Da hε' hDa) (E5.2.2.1 ε' Da hε' hDa)
      refine TwistStep2_prec_mono (fun n p ω => ?_) (fun n p ω => ?_) hD3
      · simp only [TwistStep_Fsd, TwistStep2_Fs_eq]
        exact le_of_eq (by ring)
      · exact le_of_eq (by ring)
  -- the decomposition `Z = Pr Z + (1 - Pr) Z` and the absorption of the constant
  have hβ1 : ∀ n, 0 < sz.Bctl n (τ n) := fun n => st_Bctl_pos sz ((hτt n).trans_lt (ht1 n))
  have hβnn : ∀ n (p : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) (ω : sz.SeqΩ),
      0 ≤ sz.Bctl n (τ n) ^ (3 / 2 : ℝ) * (1 + sz.Bctl n (τ n) ^ (1 / 6 : ℝ) * Ξ n) := fun n p ω => by
    have := hβ1 n
    have := hΞ n
    positivity
  have h2 : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p ω => sz.Bctl n (τ n) ^ (3 / 2 : ℝ) * (1 + sz.Bctl n (τ n) ^ (1 / 6 : ℝ) * Ξ n) + sz.Bctl n (τ n) ^ (3 / 2 : ℝ))
      (fun n _ _ => sz.Bctl n (τ n) ^ (3 / 2 : ℝ) * (1 + sz.Bctl n (τ n) ^ (1 / 6 : ℝ) * Ξ n)) := by
    refine StochDomAt.of_le_left (fun n p ω => ?_) (StochDomAt.const_mul_left (c := 2) hsize (by norm_num) hβnn (StochDomAt.refl hsize hβnn))
    have h0 : 0 ≤ sz.Bctl n (τ n) ^ (1 / 6 : ℝ) * Ξ n := by
      have := hβ1 n
      have := hΞ n
      positivity
    have h1 : 0 ≤ sz.Bctl n (τ n) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (hβ1 n).le _
    nlinarith [mul_nonneg h1 h0]
  refine StochDomAt.trans hsize (StochDomAt.of_le_left (fun n p ω => ?_) (StochDomAt.add hsize hmain hPZ)) h2
  show ‖twL2' (baFMz sz z) n (τ n) ω p.1 p.2.1 p.2.2.1 p.2.2.2 - twK (baFMz sz z) n (τ n) p.1 p.2.1 p.2.2.1 p.2.2.2‖ ≤
    ‖(Pr n p.1 *ᵥ TwistStep2_Zvec sz z n (τ n) ω p.1 p.2.2.1 p.2.2.2) p.2.1‖ + ‖((1 - Pr n p.1) *ᵥ TwistStep2_Zvec sz z n (τ n) ω p.1 p.2.2.1 p.2.2.2) p.2.1‖
  have e : (Pr n p.1 *ᵥ TwistStep2_Zvec sz z n (τ n) ω p.1 p.2.2.1 p.2.2.2) p.2.1 + ((1 - Pr n p.1) *ᵥ TwistStep2_Zvec sz z n (τ n) ω p.1 p.2.2.1 p.2.2.2) p.2.1 =
      twL2' (baFMz sz z) n (τ n) ω p.1 p.2.1 p.2.2.1 p.2.2.2 - twK (baFMz sz z) n (τ n) p.1 p.2.1 p.2.2.1 p.2.2.2 := by
    rw [← Pi.add_apply, ← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
    rfl
  rw [← e]
  exact norm_add_le _ _

end Pin

/-! ## 5. The kernel losses of the three charge cases (`BAEKSameRow`, `BATwKerFar`, `BATwKerZero`)

(A) `σ₁ = σ₂`: `TwistStep2_kerA`; (B) `σ₁ ≠ σ₂` in `STCaseI`: `TwistStep2_kerB`; (C) `σ₁ ≠ σ₂` in `STCaseII`: `TwistStep2_kerC`. -/

section Ker

variable {d : ℕ}

/-- `κ/(κ+1) ≤ t₀_n` along the flow (`t₀ = Im m/(Im m + Im z)`, `Im m ≥ κ`, `Im z ≤ 1`). -/
theorem TwistStep2_T0_ge {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {sz : Sizes d} {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) : κ / (κ + 1) ≤ BAflowT0 sz z n := by
  obtain ⟨h1, -, h3⟩ := hflow.2 n
  have hz := EMn2BA_zim_pos sz hflow n
  have hm : 0 < (BAm d (sz.L n) (sz.lam n) (z n)).im := lt_of_lt_of_le hκ h1
  show κ / (κ + 1) ≤ (BAm d (sz.L n) (sz.lam n) (z n)).im / ((BAm d (sz.L n) (sz.lam n) (z n)).im + (z n).im)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- `g₀² = t₀ g²`, so `g₀² ≤ g²` and `g² ≤ ((κ+1)/κ) g₀²`. -/
theorem TwistStep2_lam0_sq {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {sz : Sizes d} {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
    BAflowLam0 sz z n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ (κ + 1) / κ * BAflowLam0 sz z n ^ 2 := by
  have hT0 := TwistStep2_T0_ge hκ hflow n
  have hT1 := EMn2BA_T0_lt_one hκ sz hflow n
  have hT0' : 0 < κ / (κ + 1) := by positivity
  have e : BAflowLam0 sz z n ^ 2 = BAflowT0 sz z n * sz.lam n ^ 2 := by
    show (Real.sqrt (BAflowT0 sz z n) * sz.lam n) ^ 2 = _
    rw [mul_pow, Real.sq_sqrt (hT0'.trans_le hT0).le]
  rw [e]
  refine ⟨?_, ?_⟩
  · nlinarith [sq_nonneg (sz.lam n)]
  · have h1 : κ / (κ + 1) * sz.lam n ^ 2 ≤ BAflowT0 sz z n * sz.lam n ^ 2 := mul_le_mul_of_nonneg_right hT0 (sq_nonneg _)
    have h2 : sz.lam n ^ 2 = (κ + 1) / κ * (κ / (κ + 1) * sz.lam n ^ 2) := by field_simp
    calc sz.lam n ^ 2 = (κ + 1) / κ * (κ / (κ + 1) * sz.lam n ^ 2) := h2
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)

open scoped Matrix.Norms.Operator in
/-- **Case (A)** (`σ₁ = σ₂`, either regime): the loss-free bound `‖Ũ_{v,τ} x‖ ≤ C ‖x‖` (`BAEKSameRow`, `baEKSameRow_holds`). -/
theorem TwistStep2_kerA (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) {sz : Sizes d} {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {s τ : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (hτT : ∀ n, τ n ≤ BAflowT0 sz z n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool, σ 0 = σ 1 → ∀ v : ℝ, s n ≤ v → v ≤ τ n → ∀ x : Zd d (sz.L n) → ℂ,
      ‖twU sz (BAflowLam0 sz z) (BAflowEs sz z) n σ v (τ n) *ᵥ x‖ ≤ C * ‖x‖ := by
  obtain ⟨C, hC, H⟩ := baEKSameRow_holds d 𝔡⁻¹ κ hd (inv_pos.2 h𝔡) hκ
  refine ⟨C, hC.le, ?_⟩
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow] with n hn σ hσ v hv hvτ x
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hτ1 : τ n < 1 := (hτT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  have h := H (sz.L n) (sz.three_le_L n) _ hn.1 hn.2 _ _ hr (σ 0) v (τ n) ((hs n).trans hv) hvτ hτ1
  have e : twU sz (BAflowLam0 sz z) (BAflowEs sz z) n σ v (τ n) = BAuKer d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) v (τ n) (σ 0) (σ 0) := by
    show BAuKer d (sz.L n) _ _ _ v (τ n) (σ 0) (σ 1) = _
    rw [← hσ]
  rw [e]
  exact (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))

open scoped Matrix.Norms.Operator in
/-- **Case (C)** (`σ₁ ≠ σ₂`, `STCaseII`): `‖Q Ũ_{v,τ} x‖ ≤ C ‖x‖` for `Q = projMat` (`BATwKerZero`, `baTwKerZero_holds` at `A = (κ+1)/κ`, `1 - v ≤ 1 - s ≤ g²/L² ≤ A g₀²/L²`). -/
theorem TwistStep2_kerC (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) {sz : Sizes d} {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {s t τ : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (hτT : ∀ n, τ n ≤ BAflowT0 sz z n) (hcase : STCaseII sz s t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool, ∀ v : ℝ, s n ≤ v → v ≤ τ n → ∀ x : Zd d (sz.L n) → ℂ,
      ‖projMat d (sz.L n) *ᵥ (twU sz (BAflowLam0 sz z) (BAflowEs sz z) n σ v (τ n) *ᵥ x)‖ ≤ C * ‖x‖ := by
  obtain ⟨C, hC, H⟩ := baTwKerZero_holds d 𝔡⁻¹ κ hd (inv_pos.2 h𝔡) hκ ((κ + 1) / κ) (by positivity)
  refine ⟨C, hC.le, ?_⟩
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow] with n hn σ v hv hvτ x
  have : NeZero (sz.L n) := ⟨by have := sz.three_le_L n; omega⟩
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hτ1 : τ n < 1 := (hτT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ 2 := by
    have : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
    positivity
  have hreg : (1 - v) * ((sz.L n : ℕ) : ℝ) ^ 2 ≤ (κ + 1) / κ * BAflowLam0 sz z n ^ 2 := by
    have h1 : 1 - v ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by linarith [hcase n, hv]
    have h2 : (1 - v) * ((sz.L n : ℕ) : ℝ) ^ 2 ≤ sz.lam n ^ 2 := by
      rw [le_div_iff₀ hL0] at h1; exact h1
    exact h2.trans (TwistStep2_lam0_sq hκ hflow n).2
  have h := H (sz.L n) (sz.three_le_L n) _ hn.1 hn.2 _ _ hr (σ 0) (σ 1) v (τ n) ((hs n).trans hv) hreg hvτ hτ1
  rw [Matrix.mulVec_mulVec]
  refine (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact h


/-- Eventually `A ≤ W^c` (`W ≥ N^𝔠`). -/
theorem TwistStep2_ev_W (sz : Sizes d) (hsize : Tendsto sz.size atTop atTop) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hband : sz.Bandwidth 𝔠) {c : ℝ} (hc : 0 < c) (A : ℝ) :
    ∀ᶠ n in atTop, A ≤ ((sz.W n : ℕ) : ℝ) ^ c := by
  filter_upwards [hband, TwistStep2_ev_ge sz hsize (mul_pos h𝔠 hc) A] with n hb hn
  have hN : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  calc A ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * c) := hn
    _ = (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ c := by rw [Real.rpow_mul hN]
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ c := Real.rpow_le_rpow (Real.rpow_nonneg hN _) hb hc.le

/-- `(W^d)⁻¹ (1 + 𝔡⁻²)⁻¹ ≤ W^{-d} B_{u,0}` for `0 ≤ u < 1`, `0 ≤ lam ≤ 𝔡⁻¹`. -/
theorem TwistStep2_Bctl_ge_W (sz : Sizes d) (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) {𝔡 : ℝ} (hlam : sz.lam n ≤ 𝔡⁻¹) (hlam0 : 0 ≤ sz.lam n) :
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 + (𝔡⁻¹) ^ 2)⁻¹ ≤ sz.Bctl n u := by
  unfold Sizes.Bctl Bparam
  have hx : 0 < 1 - u := by linarith
  rw [abs_of_pos hx]
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 : (1 + (𝔡⁻¹) ^ 2)⁻¹ ≤ (sz.lam n ^ 2 + (1 - u))⁻¹ := by
    refine inv_anti₀ (by positivity) ?_
    nlinarith [pow_le_pow_left₀ hlam0 hlam 2]
  have h2 : 0 ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by positivity
  simp only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one]
  linarith


open scoped Matrix.Norms.Operator in
/-- **Case (B)** (`STCaseI`, external anchor): `‖Ũ_{v,τ} x‖ ≤ Λ₀ W^{4ε'} (B_τ/B_v) ‖x‖ + W^{-D+1}` for `x` with the decay `twDec` at the scale `3 W^{ε'} ℓ_v(lam)`
(`BATwKerFar`, `baTwKerFar_holds` at `ε = 2ε'`; `ℓ_v(g₀) ≥ √t₀ ℓ_v(lam)`, `zdistD ≤ d zdistInf`; the side conditions from `STCaseI`, `STConStInd`, `d 𝔠d < 1`; the loss factor by `TwistStep_ratio_le`). -/
theorem TwistStep2_kerB (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) {sz : Sizes d} {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {s t τ : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (hsτ : ∀ n, s n ≤ τ n) (hτt : ∀ n, τ n ≤ t n) (htT : ∀ n, t n ≤ BAflowT0 sz z n) (hcase : STCaseI sz s t)
    {𝔠d : ℝ} (hd𝔠 : (d : ℝ) * 𝔠d < 1) (h𝔠d : 0 < 𝔠d) (hcon : sz.STConStInd 𝔠d s t) {ε' Dd : ℝ} (hε' : 0 < ε') (hε'1 : ε' < 1 / 4) (hDd : 1 < Dd) :
    ∃ Λ₀ : ℝ, 0 ≤ Λ₀ ∧ ∀ᶠ n in atTop, ∀ (σ : Fin 2 → Bool) (c₁ : Zd d (sz.L n)) (v : ℝ), s n ≤ v → v ≤ τ n →
      ∀ x : Zd d (sz.L n) → ℂ, (∀ b, 3 * ((sz.W n : ℕ) : ℝ) ^ ε' * ellT (sz.L n) (sz.lam n) v ≤ (zdistInf d (sz.L n) (b - c₁) : ℝ) → ‖x b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dd)) →
        ‖twU sz (BAflowLam0 sz z) (BAflowEs sz z) n σ v (τ n) *ᵥ x‖ ≤
          Λ₀ * ((sz.W n : ℕ) : ℝ) ^ (4 * ε') * (sz.Bctl n (τ n) / sz.Bctl n v) * ‖x‖ + ((sz.W n : ℕ) : ℝ) ^ (-Dd + 1) := by
  obtain ⟨C₁, hC₁, H⟩ := baTwKerFar_holds d 𝔡⁻¹ κ hd (inv_pos.2 h𝔡) hκ
  set A : ℝ := (κ + 1) / κ with hAdef
  have hA1 : 1 ≤ A := by rw [hAdef, le_div_iff₀ hκ]; linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  refine ⟨1 + 2 * A * C₁, by positivity, ?_⟩
  have hsize := tendsto_size sz hflow.1.2.2.1
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hband := hflow.1.2.2.2.1
  set K : ℝ := 1 + (𝔡⁻¹) ^ 2 with hK
  have hK0 : 0 < K := by positivity
  have h1d : 0 < 1 - (d : ℝ) * 𝔠d := by linarith
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow, hflow.1.2.2.2.2, TwistStep2_ev_W sz hsize h𝔠 hband hε' (3 * d * A),
    TwistStep2_ev_W sz hsize h𝔠 hband (by norm_num : (0 : ℝ) < 1) 2, TwistStep2_ev_W sz hsize h𝔠 hband h1d (K ^ 𝔠d), hcon]
    with n hwin hWO hW3 hW2 hWK hconn σ c₁ v hv hvτ x hx
  have hL3 := sz.three_le_L n
  have : NeZero (sz.L n) := ⟨by omega⟩
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  have hW2' : (2 : ℝ) ≤ W := by simpa using hW2
  have hW1 : 1 < W := lt_of_lt_of_le one_lt_two hW2'
  have hW0 : 0 < W := zero_lt_one.trans hW1
  have hlam0 : 0 ≤ sz.lam n := (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans hWO.1
  have hlamd : sz.lam n ≤ 𝔡⁻¹ := hWO.2
  have hg := TwistStep2_lam0_sq hκ hflow n
  have hτ1 : τ n < 1 := ((hτt n).trans (htT n)).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hv0 : 0 ≤ v := (hs n).trans hv
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ 2 := by
    have : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < sz.L n)
    positivity
  -- the regime `lam² ≤ L² (1 - τ)`
  have hlu : sz.lam n ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ 2 * (1 - τ n) := by
    have h1 : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - τ n := by linarith [hcase n, hτt n]
    rw [div_le_iff₀ hL0] at h1; linarith
  have hu_le : τ n ≤ 1 - BAflowLam0 sz z n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by
    have h1 : BAflowLam0 sz z n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hg.1 hL0.le
    linarith [hcase n, hτt n]
  -- `W⁻¹ ≤ (1 - τ)/(1 - v)`
  have hWu : W⁻¹ ≤ (1 - τ n) / (1 - v) := by
    have ht0 : 0 ≤ t n := (hs n).trans ((hsτ n).trans (hτt n))
    have ht1 : t n < 1 := (htT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
    have hlow := TwistStep2_Bctl_ge_W sz n ht0 ht1 hlamd hlam0
    have hc0 : 0 ≤ 𝔠d := h𝔠d.le
    have h1 : ((W ^ d)⁻¹ * K⁻¹) ^ 𝔠d ≤ sz.Bctl n (t n) ^ 𝔠d := Real.rpow_le_rpow (by positivity) hlow hc0
    have h2 : ((W ^ d)⁻¹ * K⁻¹) ^ 𝔠d = (W ^ (d * 𝔠d) * K ^ 𝔠d)⁻¹ := by
      rw [← mul_inv, Real.inv_rpow (by positivity), Real.mul_rpow (by positivity) hK0.le, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
    have h3 : W ^ (d * 𝔠d) * K ^ 𝔠d ≤ W := by
      calc W ^ (d * 𝔠d) * K ^ 𝔠d ≤ W ^ (d * 𝔠d) * W ^ (1 - d * 𝔠d) := mul_le_mul_of_nonneg_left hWK (by positivity)
        _ = W := by rw [← Real.rpow_add hW0]; simp
    have h4 : W⁻¹ ≤ (W ^ (d * 𝔠d) * K ^ 𝔠d)⁻¹ := inv_anti₀ (by positivity) h3
    have h5 : (1 - t n) / (1 - s n) ≤ (1 - τ n) / (1 - v) := by
      have h1v : 0 < 1 - v := by linarith [hτ1]
      exact div_le_div₀ (by linarith [hτt n]) (by linarith [hτt n]) h1v (by linarith)
    calc W⁻¹ ≤ (W ^ (d * 𝔠d) * K ^ 𝔠d)⁻¹ := h4
      _ = ((W ^ d)⁻¹ * K⁻¹) ^ 𝔠d := h2.symm
      _ ≤ sz.Bctl n (t n) ^ 𝔠d := h1
      _ ≤ (1 - t n) / (1 - s n) := hconn.1
      _ ≤ _ := h5
  -- the support: `W^{2ε'} ℓ_v(g₀) ≤ zdistD` gives `3 W^{ε'} ℓ_v(lam) ≤ zdistInf`
  have hA : ∀ b, W ^ (2 * ε') * ellT (sz.L n) (BAflowLam0 sz z n) v ≤ (zdistD d (sz.L n) (b - c₁) : ℝ) → ‖x b‖ ≤ W ^ (-Dd) := by
    intro b hb
    refine hx b ?_
    have hT0 := TwistStep2_T0_ge hκ hflow n
    have hT1 := EMn2BA_T0_lt_one hκ sz hflow n
    have hT0' : 0 < κ / (κ + 1) := by positivity
    have hsq : 1 / A ≤ Real.sqrt (BAflowT0 sz z n) := by
      have h1 : 1 / A = κ / (κ + 1) := by rw [hAdef]; field_simp
      rw [h1]
      refine le_trans hT0 (Real.le_sqrt_of_sq_le ?_)
      nlinarith [hT0'.trans_le hT0]
    have hsc := TwistStep_ellT_scale (sz.L n) (g := sz.lam n) (v := v) (Real.sqrt_nonneg (BAflowT0 sz z n)) (Real.sqrt_le_one.2 hT1.le)
    have hE0 : 0 ≤ ellT (sz.L n) (sz.lam n) v := le_trans zero_le_one (one_le_ellT (by exact_mod_cast (by omega : 1 ≤ sz.L n)))
    have hell : 1 / A * ellT (sz.L n) (sz.lam n) v ≤ ellT (sz.L n) (BAflowLam0 sz z n) v :=
      (mul_le_mul_of_nonneg_right hsq hE0).trans hsc
    have hzd := zdistD_le_mul_zdistInf d (sz.L n) (b - c₁)
    set R := W ^ ε' with hR
    set E := ellT (sz.L n) (sz.lam n) v with hE
    have hR0 : 0 ≤ R := Real.rpow_nonneg hW0.le _
    have hRR : W ^ (2 * ε') = R * R := by
      rw [hR, ← Real.rpow_add hW0]; ring_nf
    rw [hRR] at hb
    have hzi0 : (0 : ℝ) ≤ (zdistInf d (sz.L n) (b - c₁) : ℝ) := Nat.cast_nonneg _
    have hdA : (0 : ℝ) < A * d := by positivity
    have h1 : R * R * (1 / A * E) ≤ d * (zdistInf d (sz.L n) (b - c₁) : ℝ) := by
      calc R * R * (1 / A * E) ≤ R * R * ellT (sz.L n) (BAflowLam0 sz z n) v := mul_le_mul_of_nonneg_left hell (by positivity)
        _ ≤ (zdistD d (sz.L n) (b - c₁) : ℝ) := hb
        _ ≤ d * (zdistInf d (sz.L n) (b - c₁) : ℝ) := by exact_mod_cast hzd
    have h2 : (A * d) * (3 * R * E) ≤ (A * d) * (zdistInf d (sz.L n) (b - c₁) : ℝ) := by
      have h3 : 3 * d * A * (R * E) ≤ R * (R * E) := mul_le_mul_of_nonneg_right hW3 (by positivity)
      have h4 : R * R * E ≤ A * (d * (zdistInf d (sz.L n) (b - c₁) : ℝ)) := by
        have := mul_le_mul_of_nonneg_left h1 (zero_le_one.trans hA1)
        calc R * R * E = A * (R * R * (1 / A * E)) := by field_simp
          _ ≤ _ := this
      calc (A * d) * (3 * R * E) = 3 * d * A * (R * E) := by ring
        _ ≤ R * (R * E) := h3
        _ = R * R * E := by ring
        _ ≤ A * (d * (zdistInf d (sz.L n) (b - c₁) : ℝ)) := h4
        _ = (A * d) * (zdistInf d (sz.L n) (b - c₁) : ℝ) := by ring
    have := le_of_mul_le_mul_left h2 hdA
    linarith
  have hmain := H (sz.L n) hL3 (BAflowLam0 sz z n) hwin.1 hwin.2 W (2 * ε') Dd hW1 (by positivity) (by linarith) hDd v (τ n) hv0 hvτ hu_le hWu
    (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) hr (σ 0) (σ 1) c₁ x hA
  -- the loss factor
  have hratio := TwistStep_ratio_le (d := d) (L := sz.L n) hd hL3 hA1 hg.1 hg.2 hvτ hτ1 hlu
  have hBe : sz.Bctl n (τ n) / sz.Bctl n v = Bparam d (sz.L n) (sz.lam n) (τ n) 0 / Bparam d (sz.L n) (sz.lam n) v 0 := by
    unfold Sizes.Bctl
    rw [mul_div_mul_left _ _ (by positivity)]
  have hBv0 : 0 < sz.Bctl n v := st_Bctl_pos sz (by linarith)
  have hBvτ : sz.Bctl n v ≤ sz.Bctl n (τ n) := STBctl_mono sz n hvτ hτ1
  have hq1 : 1 ≤ sz.Bctl n (τ n) / sz.Bctl n v := by rw [le_div_iff₀ hBv0]; linarith
  have hW4 : 1 ≤ W ^ (4 * ε') := Real.one_le_rpow hW1.le (by linarith)
  have hW22 : W ^ (2 * (2 * ε')) = W ^ (4 * ε') := by ring_nf
  rw [hW22] at hmain
  rw [← hBe] at hratio
  set q := sz.Bctl n (τ n) / sz.Bctl n v with hq
  have hWq : 1 ≤ W ^ (4 * ε') * q := one_le_mul_of_one_le_of_one_le hW4 hq1
  have hcoef : 1 + C₁ * W ^ (4 * ε') * ((BAflowLam0 sz z n ^ 2 + |1 - v|) / (BAflowLam0 sz z n ^ 2 + |1 - τ n|)) ≤ (1 + 2 * A * C₁) * W ^ (4 * ε') * q := by
    have h1 := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ C₁ * W ^ (4 * ε'))
    generalize (BAflowLam0 sz z n ^ 2 + |1 - v|) / (BAflowLam0 sz z n ^ 2 + |1 - τ n|) = ρ at h1 ⊢
    generalize W ^ (4 * ε') = Y at h1 hWq ⊢
    linarith
  calc ‖twU sz (BAflowLam0 sz z) (BAflowEs sz z) n σ v (τ n) *ᵥ x‖ ≤ (1 + C₁ * W ^ (4 * ε') * ((BAflowLam0 sz z n ^ 2 + |1 - v|) / (BAflowLam0 sz z n ^ 2 + |1 - τ n|))) * ‖x‖ + W ^ (-Dd + 1) := hmain
    _ ≤ (1 + 2 * A * C₁) * W ^ (4 * ε') * q * ‖x‖ + W ^ (-Dd + 1) := by
        have := mul_le_mul_of_nonneg_right hcoef (norm_nonneg x)
        linarith

end Ker

/-! ## 6. Regime I: `Pr = 1`, the loss of `Ũ` is `TwistStep2_kerA` for `σ₁ = σ₂` and `TwistStep2_kerB` for `σ₁ ≠ σ₂`; the theorem `baTwistStepFixed_caseI` -/

section CaseI

variable {d : ℕ}

/-- `0 ≤ ζ` and `ξ ≤ 0` give `ξ ≺ ζ`. -/
theorem TwistStep2_prec_zero {sz : Sizes d} {μ : Measure sz.SeqΩ} {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (hξ : ∀ n u ω, ξ n u ω ≤ 0) (hζ : ∀ n u ω, 0 ≤ ζ n u ω) : PrecL sz μ ξ ζ :=
  StochDomAt.of_eventually_empty fun τ hτ => Eventually.of_forall fun n => by
    ext ω
    simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
    intro u
    exact (hξ n u ω).trans (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hζ n u ω))

/-- `1 ≤ W^{4ε'} · B_τ/B_v` for `v ≤ τ < 1`. -/
theorem TwistStep2_loss_ge (sz : Sizes d) (n : ℕ) {v τ : ℝ} (hvτ : v ≤ τ) (hτ1 : τ < 1) {ε' : ℝ} (hε' : 0 ≤ ε') :
    1 ≤ ((sz.W n : ℕ) : ℝ) ^ (4 * ε') * (sz.Bctl n τ / sz.Bctl n v) := by
  have hBv0 : 0 < sz.Bctl n v := st_Bctl_pos sz (by linarith)
  have hq1 : 1 ≤ sz.Bctl n τ / sz.Bctl n v := by
    rw [le_div_iff₀ hBv0]; linarith [STBctl_mono sz n hvτ hτ1]
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hW1 (by linarith)) hq1

/-- A loss-free bound `C ‖x‖` is dominated by the lossy form `Λ W^{4ε'} (B_τ/B_v) ‖x‖ + W^{-D+1}` if `0 ≤ C ≤ Λ`. -/
theorem TwistStep2_loss_dom (sz : Sizes d) (n : ℕ) {v τ : ℝ} (hvτ : v ≤ τ) (hτ1 : τ < 1) {ε' Dd C Λ : ℝ} (hε' : 0 ≤ ε') (hC : C ≤ Λ) (hC0 : 0 ≤ C)
    (x : Zd d (sz.L n) → ℂ) :
    C * ‖x‖ ≤ Λ * ((sz.W n : ℕ) : ℝ) ^ (4 * ε') * (sz.Bctl n τ / sz.Bctl n v) * ‖x‖ + ((sz.W n : ℕ) : ℝ) ^ (-Dd + 1) := by
  have hloss := TwistStep2_loss_ge sz n hvτ hτ1 hε'
  have hW0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dd + 1) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h1 : C * ‖x‖ ≤ Λ * (((sz.W n : ℕ) : ℝ) ^ (4 * ε') * (sz.Bctl n τ / sz.Bctl n v)) * ‖x‖ := by
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg x)
    calc C ≤ Λ := hC
      _ = Λ * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hloss (hC0.trans hC)
  calc C * ‖x‖ ≤ _ := h1
    _ = Λ * ((sz.W n : ℕ) : ℝ) ^ (4 * ε') * (sz.Bctl n τ / sz.Bctl n v) * ‖x‖ := by ring
    _ ≤ _ := le_add_of_nonneg_right hW0

/-- Monotonicity of the lossy form in the constant `Λ`. -/
theorem TwistStep2_loss_mono (sz : Sizes d) (n : ℕ) {v τ : ℝ} (hvτ : v ≤ τ) (hτ1 : τ < 1) {ε' Dd Λ Λ' : ℝ} (hΛ : Λ ≤ Λ') (x : Zd d (sz.L n) → ℂ) :
    Λ * ((sz.W n : ℕ) : ℝ) ^ (4 * ε') * (sz.Bctl n τ / sz.Bctl n v) * ‖x‖ + ((sz.W n : ℕ) : ℝ) ^ (-Dd + 1) ≤
      Λ' * ((sz.W n : ℕ) : ℝ) ^ (4 * ε') * (sz.Bctl n τ / sz.Bctl n v) * ‖x‖ + ((sz.W n : ℕ) : ℝ) ^ (-Dd + 1) := by
  have hBv0 : 0 < sz.Bctl n v := st_Bctl_pos sz (by linarith)
  have hBτ0 : 0 < sz.Bctl n τ := st_Bctl_pos sz hτ1
  have hq0 : 0 ≤ sz.Bctl n τ / sz.Bctl n v := by positivity
  have hW0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (4 * ε') := Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hΛ hW0) hq0) (norm_nonneg x)) le_rfl

/-- **The kernel input of regime I** (`STCaseI`): `Pr = 1`; the loss of `Ũ` is `TwistStep2_kerA` for `σ₁ = σ₂` and `TwistStep2_kerB` for `σ₁ ≠ σ₂`; no zero mode. -/
theorem TwistStep2_ker_caseI (d : ℕ) : TwistStep2_Ker d STCaseI := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 𝔠d sz z hflow h𝔠d hd𝔠 s t τ hs hst hsτ hτt htT hR hcon Cd hsteps
  refine ⟨fun _ _ => 1, ?_, ?_, ?_⟩
  · intro n σ x
    rw [Matrix.one_mulVec]
    have := norm_nonneg x
    linarith
  · intro ε' Dd hε' hε'1 hDd
    obtain ⟨CA, hCA, HA⟩ := TwistStep2_kerA hd hκ h𝔡 hflow hs (fun n => (hτt n).trans (htT n))
    obtain ⟨Λ₀, hΛ₀, H⟩ := TwistStep2_kerB hd hκ h𝔡 hflow hs hsτ hτt htT hR hd𝔠 h𝔠d hcon hε' hε'1 hDd
    refine ⟨max CA Λ₀, le_max_of_le_left hCA, ?_⟩
    filter_upwards [HA, H] with n hA hB σ c₁ v hv hvτ x hx
    have hτ1 : τ n < 1 := ((hτt n).trans (htT n)).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
    rw [Matrix.one_mulVec]
    by_cases h : σ 0 = σ 1
    · exact (hA σ h v hv hvτ x).trans (TwistStep2_loss_dom sz n hvτ hτ1 hε'.le (le_max_left _ _) hCA x)
    · exact (hB σ c₁ v hv hvτ x hx).trans (TwistStep2_loss_mono sz n hvτ hτ1 (le_max_right _ _) x)
  · refine TwistStep2_prec_zero (fun n p ω => ?_) (fun n p ω => ?_)
    · simp
    · exact Real.rpow_nonneg (st_Bctl_pos sz ((hτt n).trans_lt ((htT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)))).le _

/-- **The regime `STCaseI`**: `BATwistStepFixed d STCaseI`. -/
theorem baTwistStepFixed_caseI (d : ℕ) : BATwistStepFixed d STCaseI := TwistStep2_pin d STCaseI (TwistStep2_ker_caseI d)

end CaseI

open private TwistKer_Gres_sub TwistKer_Gres_conjTranspose from RBM3D.BA.TwistKer
open private TwistKer2_hermitian TwistKer2_carrier from RBM3D.BA.TwistKer2
open private TwistPins_sum_twist from RBM3D.BA.TwistPins
open private TwistChain_Off TwistChain_trP_offset from RBM3D.BA.TwistChain

/-! ## 7. Regime II: the zero mode of `Z_τ` (the random identity, the bound by the twisted one-loops of Lemma 8.6), `TwistStep2_ker_caseII`, the theorem `baTwistStepFixed_caseII` -/

section Zero

variable {d : ℕ}

/-- `Tr(X(−) P_{c₁c₂}) = conj Tr(X P_{c₂c₁})`: the reindexing `w ↦ (c₁, o_w)` of the blocks. -/
theorem TwistStep2_trP_conj {sz : Sizes d} (n : ℕ) (X : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) (c₁ c₂ : Zd d (sz.L n)) :
    twTrP n (twChg X false) c₁ c₂ = (starRingEnd ℂ) (twTrP n X c₂ c₁) := by
  unfold twTrP
  rw [map_mul, map_sum]
  have h := TwistPins_sum_twist (sz := sz) n c₁ c₂ (fun y w => (starRingEnd ℂ) (X w y))
  have hW : (starRingEnd ℂ) ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ := by simp
  rw [hW]
  congr 1
  simp only [twChg, Bool.false_eq_true, ↓reduceIte]
  exact h.symm

/-- `Tr((X + Y) P) = Tr(X P) + Tr(Y P)` (pointwise sum of the matrices). -/
theorem TwistStep2_trP_add {sz : Sizes d} (n : ℕ) (X Y : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) (c₁ c₂ : Zd d (sz.L n)) :
    twTrP n (fun x y => X x y + Y x y) c₁ c₂ = twTrP n X c₁ c₂ + twTrP n Y c₁ c₂ := by
  unfold twTrP
  rw [← mul_add, ← Finset.sum_add_distrib]

/-- **The zero mode of `Z_τ` at the random level** (`σ₁ ≠ σ₂`): `Σ_a Z_τ(a) = (2i W^d η_τ)⁻¹ (T̃_{c₂c₁} - conj T̃_{c₁c₂})`, `T̃ = twTr`.
The Ward identity of `L̃` (`twWard_holds` at `G = Gres H ζ`) and the exact cancellation `D_τ = 0` (`baTwistZeroMode_holds`): the `M`-parts cancel. -/
theorem TwistStep2_zero_sum (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {sz : Sizes d} {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z)
    {τ : ℕ → ℝ} (hτ0 : ∀ n, 0 ≤ τ n) (hτT : ∀ n, τ n ≤ BAflowT0 sz z n) (n : ℕ) (ω : sz.SeqΩ) (σ : Fin 2 → Bool) (hσ : σ 0 ≠ σ 1) (c₁ c₂ : Zd d (sz.L n)) :
    ∑ b, TwistStep2_Zvec sz z n (τ n) ω σ c₁ c₂ b =
      (2 * Complex.I * (((sz.W n : ℕ) : ℂ) ^ d) * (((baFMz sz z).eta n (τ n) : ℝ) : ℂ))⁻¹ *
        (twTr (baFMz sz z) n (τ n) ω c₂ c₁ - (starRingEnd ℂ) (twTr (baFMz sz z) n (τ n) ω c₁ c₂)) := by
  have hmF : 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := lt_of_lt_of_le hκ (EMn2BA_mF_data sz hflow n).1
  have hτ1 : τ n < 1 := (hτT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  have hηpos : 0 < (baFMz sz z).eta n (τ n) := mul_pos (by linarith) hmF
  obtain ⟨hGeq, -, hzim⟩ := TwistKer2_carrier sz z n (τ n) ω
  set H := sz.seqHflowBA (BAflowLam0 sz z) n (τ n) ω with hH
  set zt := ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) (τ n) with hzt
  set η := (baFMz sz z).eta n (τ n) with hηdef
  have hHerm : H.IsHermitian := TwistKer2_hermitian sz z n (τ n) ω
  have hzim0 : zt.im ≠ 0 := by rw [hzim]; exact hηpos.ne'
  obtain ⟨h1, h2⟩ := TwistKer_Gres_sub hHerm hzim0
  have hcj : (Gres H zt true)ᴴ = Gres H zt false := TwistKer_Gres_conjTranspose hHerm zt true
  have hz2 : zt - (starRingEnd ℂ) zt = 2 * (η : ℂ) * Complex.I := by
    rw [Complex.sub_conj, ← hzim]; push_cast; ring
  rw [hz2, ← hcj] at h1 h2
  -- the Ward identity of `L̃`
  have hward := twWard_holds sz n (Gres H zt true) η hηpos.ne' h1 h2
  have hsig : σ 1 = !σ 0 := by
    cases h0 : σ 0 <;> cases h1' : σ 1 <;> simp_all
  have hL : ∀ b, twL2' (baFMz sz z) n (τ n) ω σ b c₁ c₂ = twLoopX n (twChg (Gres H zt true) (σ 0)) (twChg (Gres H zt true) (!σ 0)) b c₁ c₂ := by
    intro b
    rw [← hsig]
    show twLoopX n (twChg ((baFMz sz z).G n (τ n) ω) (σ 0)) (twChg ((baFMz sz z).G n (τ n) ω) (σ 1)) b c₁ c₂ = _
    rw [hGeq]
  have hK := baTwistZeroMode_holds d hd κ ε 𝔡 𝔠 hκ hε h𝔡 sz z hflow τ hτ0 hτT n σ hσ c₁ c₂
  have hZ : ∑ b, TwistStep2_Zvec sz z n (τ n) ω σ c₁ c₂ b =
      ∑ b, twLoopX n (twChg (Gres H zt true) (σ 0)) (twChg (Gres H zt true) (!σ 0)) b c₁ c₂ - ∑ b, twK (baFMz sz z) n (τ n) σ b c₁ c₂ := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by simp only [TwistStep2_Zvec, hL b]
  rw [hZ, hward (σ 0) c₁ c₂, hK]
  -- the traces
  have hMoff : TwistChain_Off n ((baFMz sz z).M n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) := by
    intro x y
    exact BAMfine_eq sz (BAflowLam0 sz z) (BAflowEs sz z) n hmF x y
  have hG : ∀ x y, Gres H zt true x y = (baFMz sz z).GM n (τ n) ω x y + (baFMz sz z).M n x y := by
    intro x y
    show (baFMz sz z).G n (τ n) ω x y = _
    unfold FlowFM.GM
    ring
  have hS1 : twTrP n (twChg (Gres H zt true) true) c₁ c₂ = twTr (baFMz sz z) n (τ n) ω c₂ c₁ + BAMsigma d (sz.L n) (twMB (baFMz sz z) n) true c₂ c₁ := by
    have e : twTrP n (twChg (Gres H zt true) true) c₁ c₂ = twTrP n (fun x y => (baFMz sz z).GM n (τ n) ω x y + (baFMz sz z).M n x y) c₁ c₂ := by
      unfold twTrP
      refine congrArg _ (Finset.sum_congr rfl fun w _ => ?_)
      simp only [twChg, ↓reduceIte]
      exact hG _ _
    rw [e, TwistStep2_trP_add, TwistChain_trP_offset n _ _ hMoff c₁ c₂, twMB_ba z n hmF]
    rfl
  have hS2 : twTrP n (twChg (Gres H zt true) false) c₁ c₂ = (starRingEnd ℂ) (twTr (baFMz sz z) n (τ n) ω c₁ c₂) + BAMsigma d (sz.L n) (twMB (baFMz sz z) n) false c₂ c₁ := by
    refine (TwistStep2_trP_conj n (Gres H zt true) c₁ c₂).trans ?_
    have e : twTrP n (Gres H zt true) c₂ c₁ = twTrP n (fun x y => (baFMz sz z).GM n (τ n) ω x y + (baFMz sz z).M n x y) c₂ c₁ := by
      unfold twTrP
      refine congrArg _ (Finset.sum_congr rfl fun w _ => ?_)
      exact hG _ _
    rw [e, TwistStep2_trP_add, TwistChain_trP_offset n _ _ hMoff c₂ c₁, map_add, twMB_ba z n hmF]
    simp [BAMsigma, Matrix.conjTranspose_apply, twTr_eq]
  rw [hS1, hS2]
  ring


/-- **Lemma 8.6 (`lem:TL1_BA`) at `τ ∈ [s, t]`** from the parts of `twSteps` (`hA` = `STAvgUgL`, `twSteps.1.2.1`; `hL` = the second conjunct `twSteps.2.1`): the inputs of `baTwistAvgProd_holds`, `LWAvgLawgL` is `hA` restricted to
`τ` with `𝒦^{(1)} = m` (`baKsol_one`) and `STLmaxgL` is `hL` restricted to `τ`. -/
theorem TwistStep2_tl1 (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {sz : Sizes d} {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {s t τ : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (ht : ∀ n, t n ≤ BAflowT0 sz z n)
    (hA : StochDomAt (Sizes.seqP (sz.withLam 0)) sz.size (U := fun n => TimeIcc s t n × (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n)))
      (fun n p ω => ‖(baFMz sz z).L n (p.1 : ℝ) p.2.1 p.2.2 ω - (baFMz sz z).K n (p.1 : ℝ) p.2.1 p.2.2‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ 1))
    (hL : ∀ k : ℕ, 1 ≤ k → StochDomAt (Sizes.seqP (sz.withLam 0)) sz.size (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖(baFMz sz z).L n (p.1 : ℝ) p.2.1 p.2.2 ω‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (k - 1)))
    (h1 : ∀ n, s n ≤ τ n) (h2 : ∀ n, τ n ≤ t n) :
    BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) τ := by
  refine baTwistAvgProd_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow τ (fun n => (hs n).trans (h1 n)) (fun n => (h2 n).trans (ht n)) ?_ ?_
  · have hB := StochDomAt.precomp_param hA (fun n (a : Zd d (sz.L n)) =>
      ((⟨τ n, h1 n, h2 n⟩ : TimeIcc s t n), (fun _ => true : Fin 1 → Bool), (fun _ => a : Fin 1 → Zd d (sz.L n))))
    have hpos : ∀ᶠ n in atTop, 0 < BAflowLam0 sz z n := by
      filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow] with n hn
      exact hn.1
    refine StochDomAt.of_subset hB (fun τ' hτ' => ⟨τ', hτ', ?_⟩)
    filter_upwards [hpos] with n hn
    intro ω hω
    obtain ⟨a, ha⟩ := hω
    refine ⟨a, ?_⟩
    have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
    have hT1 : BAflowT0 sz z n < 1 := EMn2BA_T0_lt_one hκ sz hflow n
    have hK : (baFMz sz z).K n (τ n) (fun _ : Fin 1 => true) (fun _ => a) = (baFMz sz z).m n := by
      have := baKsol_one d hκ hn (sz.three_le_L n) (sz.W n) hr (t := τ n) ⟨(hs n).trans (h1 n), lt_of_le_of_lt ((h2 n).trans (ht n)) hT1⟩
        (fun _ : Fin 1 => true) (fun _ => a)
      exact this.trans (by simp [PropSpin, baFMz, baFM])
    simpa [hK, pow_one] using ha
  · intro k hk
    exact StochDomAt.precomp_param (hL k hk) (fun n (v : (Fin k → Bool) × (Fin k → Zd d (sz.L n))) => ((⟨τ n, h1 n, h2 n⟩ : TimeIcc s t n), v.1, v.2))

/-- The regime-II projections: `Pr = 1` for `σ₁ = σ₂`, `Pr = Q^{(1)} = projMat` for `σ₁ ≠ σ₂`. -/
def TwistStep2_Pr (sz : Sizes d) (n : ℕ) (σ : Fin 2 → Bool) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  haveI : NeZero (sz.L n) := ⟨by have := sz.three_le_L n; omega⟩
  if σ 0 = σ 1 then 1 else projMat d (sz.L n)

theorem TwistStep2_Pr_same (sz : Sizes d) (n : ℕ) {σ : Fin 2 → Bool} (h : σ 0 = σ 1) : TwistStep2_Pr sz n σ = 1 := by
  simp [TwistStep2_Pr, h]

theorem TwistStep2_Pr_diff (sz : Sizes d) (n : ℕ) {σ : Fin 2 → Bool} (h : σ 0 ≠ σ 1) [NeZero (sz.L n)] : TwistStep2_Pr sz n σ = projMat d (sz.L n) := by
  simp [TwistStep2_Pr, h]

open scoped Matrix.Norms.Operator in
theorem TwistStep2_Pr_norm (sz : Sizes d) (n : ℕ) (σ : Fin 2 → Bool) (x : Zd d (sz.L n) → ℂ) : ‖TwistStep2_Pr sz n σ *ᵥ x‖ ≤ 2 * ‖x‖ := by
  by_cases h : σ 0 = σ 1
  · rw [TwistStep2_Pr_same sz n h, Matrix.one_mulVec]
    have := norm_nonneg x
    linarith
  · have : NeZero (sz.L n) := ⟨by have := sz.three_le_L n; omega⟩
    rw [TwistStep2_Pr_diff sz n h]
    exact (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_right norm_projMat_le (norm_nonneg _))


/-- `(N (1 - u))⁻¹ ≤ W^{-d} B_{u,0}`, `N = (W L)^d`. -/
theorem TwistStep2_Bctl_ge_N (sz : Sizes d) (n : ℕ) {u : ℝ} (hu1 : u < 1) :
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ≤ sz.Bctl n u := by
  unfold Sizes.Bctl Bparam
  have hx : 0 < 1 - u := by linarith
  rw [abs_of_pos hx]
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h2 : 0 ≤ (sz.lam n ^ 2 + (1 - u))⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
  linarith

/-- Monotonicity of `≺`: a smaller left side pointwise and a larger control eventually. -/
theorem TwistStep2_prec_mono_ev {sz : Sizes d} {μ : Measure sz.SeqΩ} {U : ℕ → Type*} {ξ ξ' ζ ζ' : ∀ n, U n → sz.SeqΩ → ℝ}
    (hξ : ∀ n u ω, ξ' n u ω ≤ ξ n u ω) (hζ : ∀ᶠ n in atTop, ∀ u ω, ζ n u ω ≤ ζ' n u ω) (h : PrecL sz μ ξ ζ) : PrecL sz μ ξ' ζ' :=
  StochDomAt.of_subset h fun τ hτ => ⟨τ, hτ, by
    filter_upwards [hζ] with n hn ω ⟨u, hu⟩
    exact ⟨u, lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hn u ω) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (lt_of_lt_of_le hu (hξ n u ω))⟩⟩

/-- **The zero mode bounded pointwise**: `|((1 - Pr) Z_τ)(a)| ≤ κ⁻¹ B_τ (|T̃_{c₂c₁}| + |T̃_{c₁c₂}|)` (zero for `σ₁ = σ₂`; for `σ₁ ≠ σ₂`: `TwistStep2_zero_sum`, `(N η)⁻¹ ≤ κ⁻¹ (N (1-τ))⁻¹ ≤ κ⁻¹ B_τ`). -/
theorem TwistStep2_zero_pt (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {sz : Sizes d} {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z)
    {τ : ℕ → ℝ} (hτ0 : ∀ n, 0 ≤ τ n) (hτT : ∀ n, τ n ≤ BAflowT0 sz z n) (n : ℕ) (ω : sz.SeqΩ) (σ : Fin 2 → Bool) (c₁ c₂ a : Zd d (sz.L n)) :
    ‖((1 - TwistStep2_Pr sz n σ) *ᵥ TwistStep2_Zvec sz z n (τ n) ω σ c₁ c₂) a‖ ≤
      κ⁻¹ * sz.Bctl n (τ n) * (‖twTr (baFMz sz z) n (τ n) ω c₂ c₁‖ + ‖twTr (baFMz sz z) n (τ n) ω c₁ c₂‖) := by
  have hτ1 : τ n < 1 := (hτT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  have hBpos : 0 < sz.Bctl n (τ n) := st_Bctl_pos sz hτ1
  have hnn : 0 ≤ κ⁻¹ * sz.Bctl n (τ n) * (‖twTr (baFMz sz z) n (τ n) ω c₂ c₁‖ + ‖twTr (baFMz sz z) n (τ n) ω c₁ c₂‖) := by positivity
  by_cases hσ : σ 0 = σ 1
  · rw [TwistStep2_Pr_same sz n hσ]
    simpa using hnn
  · have : NeZero (sz.L n) := ⟨by have := sz.three_le_L n; omega⟩
    rw [TwistStep2_Pr_diff sz n hσ]
    have hmF : 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := lt_of_lt_of_le hκ (EMn2BA_mF_data sz hflow n).1
    have hmF' := (EMn2BA_mF_data sz hflow n).1
    have hη : (baFMz sz z).eta n (τ n) = (1 - τ n) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := rfl
    have h1τ : 0 < 1 - τ n := by linarith
    have hηpos : 0 < (baFMz sz z).eta n (τ n) := by rw [hη]; positivity
    have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
      exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
    -- `1 - projMat` is the averaging matrix
    have hJ : ∀ x : Zd d (sz.L n) → ℂ, ((1 - projMat d (sz.L n)) *ᵥ x) a = (((sz.L n : ℕ) : ℂ) ^ d)⁻¹ * ∑ b, x b := by
      intro x
      simp only [projMat, sub_sub_cancel, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
    rw [hJ, TwistStep2_zero_sum hd hκ hε h𝔡 hflow hτ0 hτT n ω σ hσ c₁ c₂]
    set T₁ := twTr (baFMz sz z) n (τ n) ω c₂ c₁
    set T₂ := twTr (baFMz sz z) n (τ n) ω c₁ c₂
    set η := (baFMz sz z).eta n (τ n) with hηd
    have n1 : ‖(((sz.L n : ℕ) : ℂ) ^ d)⁻¹‖ = (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ := by simp
    have n2 : ‖(2 * Complex.I * (((sz.W n : ℕ) : ℂ) ^ d) * (η : ℂ))⁻¹‖ = (2 * ((sz.W n : ℕ) : ℝ) ^ d * η)⁻¹ := by simp [abs_of_pos hηpos]
    have n3 : ‖T₁ - (starRingEnd ℂ) T₂‖ ≤ ‖T₁‖ + ‖T₂‖ := by
      have := norm_sub_le T₁ ((starRingEnd ℂ) T₂)
      rwa [Complex.norm_conj] at this
    have hnorm : ‖(((sz.L n : ℕ) : ℂ) ^ d)⁻¹ * ((2 * Complex.I * (((sz.W n : ℕ) : ℂ) ^ d) * (η : ℂ))⁻¹ * (T₁ - (starRingEnd ℂ) T₂))‖ ≤
        (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * (2 * ((sz.W n : ℕ) : ℝ) ^ d * η)⁻¹ * (‖T₁‖ + ‖T₂‖) := by
      rw [norm_mul, norm_mul, n1, n2]
      calc _ ≤ (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * ((2 * ((sz.W n : ℕ) : ℝ) ^ d * η)⁻¹ * (‖T₁‖ + ‖T₂‖)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left n3 (by positivity)) (by positivity)
        _ = _ := by ring
    refine hnorm.trans ?_
    -- the coefficient
    have hcoef : (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * (2 * ((sz.W n : ℕ) : ℝ) ^ d * η)⁻¹ ≤ κ⁻¹ * sz.Bctl n (τ n) := by
      have hB := TwistStep2_Bctl_ge_N sz n hτ1
      have hP : 0 < ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ d := by positivity
      have e : (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ * (2 * ((sz.W n : ℕ) : ℝ) ^ d * η)⁻¹ = (2 * (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ d) * η)⁻¹ := by
        field_simp
      rw [e]
      have h1 : (2 * (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ d) * η)⁻¹ ≤ (2 * (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ d) * ((1 - τ n) * κ))⁻¹ := by
        refine inv_anti₀ (by positivity) ?_
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [hη]
        exact mul_le_mul_of_nonneg_left hmF' h1τ.le
      refine h1.trans ?_
      have e2 : (2 * (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ d) * ((1 - τ n) * κ))⁻¹ = (2 * κ)⁻¹ * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * (1 - τ n))⁻¹) := by
        field_simp
      rw [e2]
      exact mul_le_mul (inv_anti₀ hκ (by linarith)) hB (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right hcoef (by positivity)

/-- **The zero mode in regime II** (`σ₁ ≠ σ₂`; the Ward identities with Lemma 8.6 at `τ`): `|((1 - Pr) Z_τ)(a)| ≺ B_τ^{3/2}`. -/
theorem TwistStep2_zero (hd : 3 ≤ d) {κ ε 𝔠 𝔡 𝔠d : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (h𝔠d : 0 < 𝔠d) {sz : Sizes d} {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z)
    {s t τ : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hsτ : ∀ n, s n ≤ τ n) (hτt : ∀ n, τ n ≤ t n) (htT : ∀ n, t n ≤ BAflowT0 sz z n) (hcon : sz.STConStInd 𝔠d s t)
    (hA : StochDomAt (Sizes.seqP (sz.withLam 0)) sz.size (U := fun n => TimeIcc s t n × (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n)))
      (fun n p ω => ‖(baFMz sz z).L n (p.1 : ℝ) p.2.1 p.2.2 ω - (baFMz sz z).K n (p.1 : ℝ) p.2.1 p.2.2‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ 1))
    (hL : ∀ k : ℕ, 1 ≤ k → StochDomAt (Sizes.seqP (sz.withLam 0)) sz.size (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖(baFMz sz z).L n (p.1 : ℝ) p.2.1 p.2.2 ω‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (k - 1))) :
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p ω => ‖((1 - TwistStep2_Pr sz n p.1) *ᵥ TwistStep2_Zvec sz z n (τ n) ω p.1 p.2.2.1 p.2.2.2) p.2.1‖) (fun n _ _ => sz.Bctl n (τ n) ^ (3 / 2 : ℝ)) := by
  have hsize := tendsto_size sz hflow.1.2.2.1
  have hτ0 : ∀ n, 0 ≤ τ n := fun n => (hs n).trans (hsτ n)
  have hτT : ∀ n, τ n ≤ BAflowT0 sz z n := fun n => (hτt n).trans (htT n)
  have hτ1 : ∀ n, τ n < 1 := fun n => (hτT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  have hBpos : ∀ n, 0 < sz.Bctl n (τ n) := fun n => st_Bctl_pos sz (hτ1 n)
  have hAvg := TwistStep2_tl1 hd hκ hε h𝔡 hflow hs htT hA hL hsτ hτt
  have hT1 := StochDomAt.precomp_param hAvg (fun n (p : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) =>
    ((p.2.2.2, p.2.2.1) : Zd d (sz.L n) × Zd d (sz.L n)))
  have hT2 := StochDomAt.precomp_param hAvg (fun n (p : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) =>
    ((p.2.2.1, p.2.2.2) : Zd d (sz.L n) × Zd d (sz.L n)))
  have hT := StochDomAt.add hsize hT1 hT2
  have hζ0 : ∀ (n : ℕ) (p : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) (ω : sz.SeqΩ), 0 ≤ sz.Bctl n (τ n) ^ (3 / 2 : ℝ) :=
    fun n p ω => Real.rpow_nonneg (hBpos n).le _
  have hF : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n _ _ => κ⁻¹ * sz.Bctl n (τ n)) (fun n _ _ => κ⁻¹ * sz.Bctl n (τ n)) :=
    StochDomAt.refl hsize (fun n _ _ => by have := hBpos n; positivity)
  have hM := StochDomAt.mul hsize (fun n p ω => add_nonneg (norm_nonneg _) (norm_nonneg _)) (fun n _ _ => by have := hBpos n; positivity) hF hT
  have hB1 : ∀ᶠ n in atTop, sz.Bctl n (τ n) ≤ 1 := by
    filter_upwards [hcon] with n hn
    exact (TwistKer2_conU sz n h𝔠d hn (hτt n) ((htT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n))).2.1
  have h2 := StochDomAt.const_mul_left (P := Sizes.seqP (sz.withLam 0)) hsize (c := 2 * κ⁻¹) (by positivity) hζ0 (StochDomAt.refl hsize hζ0)
  refine StochDomAt.trans hsize ?_ h2
  refine TwistStep2_prec_mono_ev (fun n p ω => ?_) ?_ hM
  · exact TwistStep2_zero_pt hd hκ hε h𝔡 hflow hτ0 hτT n ω p.1 p.2.2.1 p.2.2.2 p.2.1
  · filter_upwards [hB1] with n hn u ω
    have hb0 := hBpos n
    have hb32 : sz.Bctl n (τ n) ^ 2 ≤ sz.Bctl n (τ n) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge hb0 hn (by norm_num)
    show κ⁻¹ * sz.Bctl n (τ n) * (sz.Bctl n (τ n) + sz.Bctl n (τ n)) ≤ 2 * κ⁻¹ * sz.Bctl n (τ n) ^ (3 / 2 : ℝ)
    have hk : 0 ≤ κ⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hb32 hk]


/-- **The kernel input of regime II** (`STCaseII`): `Pr = 1` for `σ₁ = σ₂` (`TwistStep2_kerA`), `Pr = Q^{(1)}` for `σ₁ ≠ σ₂` (`TwistStep2_kerC`); the zero mode is `TwistStep2_zero`. -/
theorem TwistStep2_ker_caseII (d : ℕ) : TwistStep2_Ker d STCaseII := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 𝔠d sz z hflow h𝔠d hd𝔠 s t τ hs hst hsτ hτt htT hR hcon Cd hsteps
  refine ⟨TwistStep2_Pr sz, fun n σ x => TwistStep2_Pr_norm sz n σ x, ?_, ?_⟩
  · intro ε' Dd hε' hε'1 hDd
    obtain ⟨CA, hCA, HA⟩ := TwistStep2_kerA hd hκ h𝔡 hflow hs (fun n => (hτt n).trans (htT n))
    obtain ⟨CC, hCC, HC⟩ := TwistStep2_kerC hd hκ h𝔡 hflow hs (fun n => (hτt n).trans (htT n)) hR
    refine ⟨max CA CC, le_max_of_le_left hCA, ?_⟩
    filter_upwards [HA, HC] with n hA hC σ c₁ v hv hvτ x hx
    have hτ1 : τ n < 1 := ((hτt n).trans (htT n)).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
    by_cases h : σ 0 = σ 1
    · rw [TwistStep2_Pr_same sz n h, Matrix.one_mulVec]
      exact (hA σ h v hv hvτ x).trans (TwistStep2_loss_dom sz n hvτ hτ1 hε'.le (le_max_left _ _) hCA x)
    · have : NeZero (sz.L n) := ⟨by have := sz.three_le_L n; omega⟩
      rw [TwistStep2_Pr_diff sz n h]
      exact (hC σ v hv hvτ x).trans (TwistStep2_loss_dom sz n hvτ hτ1 hε'.le (le_max_right _ _) hCC x)
  · exact TwistStep2_zero hd hκ hε h𝔡 h𝔠d hflow hs hsτ hτt htT hcon hsteps.1.2.1 hsteps.2.1

/-- **The regime `STCaseII`**: `BATwistStepFixed d STCaseII`. -/
theorem baTwistStepFixed_caseII (d : ℕ) : BATwistStepFixed d STCaseII := TwistStep2_pin d STCaseII (TwistStep2_ker_caseII d)

end Zero

end RBM.BA

end
