/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.Jak
import RBM3D.Universality.UywKernel

/-!
# `RBM3D.Universality.Uyw` (UN-23): the `Uyw` half of the row `UNJakUywRow`

Paper: arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex` (cited `1_2:line`), the display
`(uywy7723r3rf)` (`1_2:566-581`) in the proof of `Thm: B_Univ`, with the two `𝐇_t` claims of the proof.
Port of RBM2D `Universality/Uyw.lean` (commit `c9a24cf`) to the merged band pins at `d ≥ 3`, by the redo
that `Jak.lean` (UN-21) did for `UNJak`.

Main results (namespace `RBM.Univ`): `unUyw_of_ouClaims` (the pin `UNUyw` at `C = 3 nf + 16`,
`c' = 𝔠𝔡/30` from `UNOUQUE`, `UNOUDiag` at one `τ_U ∈ (0, 1/4]`), `uywRow` (the row form: the `Uyw` half of
`UNJakUywRow`, `Pins.lean:805-809`), `jakUywRow` (the row `UNJakUywRow`).

Differences from RBM2D (the exponent redo of the design UN-D1 = T2162):
* the scale is `N = (W L)^d`, the index `Idx d L W`, the profile `scirc d L W lam`, the resolvent `Gres`
  (the integrand of `UNUyw` is the left side of `uyw_pointwise_good` token for token, so `gSel`, `Gsig` and
  the integrand identity are dropped);
* the parameters of RBM2D `Uyw_fixed_time` take the values `c := 2𝔠𝔡`: grid scale `η̃ = N^{-1+2τ}`,
  `C_b = N^δ` (`δ = τ/(nf+5)`), window `w' = N^{-1+𝔠𝔡/3}/2`, good-event threshold `θ = N^{-𝔠𝔡/18}`;
  the window of the pair bad event is the fixed window of the merged `measure_bad2_le_of_queBadMat`
  (`N⁻¹ W^{𝔡/3}`, threshold `W^{-𝔡/6}`), so `w' + C₀/N ≤ N⁻¹ W^{𝔡/3}` is `Bandwidth`;
* the bad block has probability `≤ (2d+1) W^{-𝔡/30} ≤ (2d+1) N^{-𝔠𝔡/30}` (`UNOUQUE` at `τ_Q = 𝔡/30`):
  `ℙ(𝓑)` binds (`𝔠𝔡/30 < 𝔠𝔡/18`), the pin exponent is `c' = 𝔠𝔡/30` (RBM2D `𝔠/36`), and the constant
  `20 = 4·5` of RBM2D becomes `4(2d+1)`; `Uyw_o_le` needs `c ≤ 1` only (`c = 2𝔠𝔡 ≤ 1`, `un_cd_le_half`);
* the row `jakUywRow` takes the common `C = 3 nf + 16`, `τ₀ = min τ₁ (1/4)` of `jakRow` and `uywRow`
  (no monotonicity lemma).

Proof, per site `y` (no average over `y`, no moment bound, no Markov step): §1 the real arithmetic of the
exponents; §2 the majorant integration, the union bound over the covering grids; §3 the pointwise bound on
the good event; §4 the bound at one size and one time (`f ≤ A₀ + c_B 1_B + C_r 1_T`); §5 the eventual
conditions, `unUyw_of_ouClaims`, `uywRow`, `jakUywRow`; §6 compiled nonempty instances at `sz0` (`d = 3`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology ProbabilityTheory
open RBM RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal

/-! ## §1 Exponent bookkeeping (pure real arithmetic) -/

private theorem Uyw_rpow_mul {X : ℝ} (hX : 0 < X) (a b : ℝ) : X ^ a * X ^ b = X ^ (a + b) :=
  (Real.rpow_add hX a b).symm

private theorem Uyw_exists_dyadic {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ K : ℕ, 2 ^ K * a ≤ b ∧ b < 2 ^ (K + 1) * a := by
  classical
  have hex : ∃ K : ℕ, b < 2 ^ (K + 1) * a := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (b / a) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ ha] at hn
    have : (2 : ℝ) ^ n ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)
    nlinarith
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases h : Nat.find hex with _ | k
  · simpa using hab
  · have hk : k < Nat.find hex := by omega
    have := Nat.find_min hex hk
    push Not at this
    exact this

/-- The factor `Q_i`: `(η̃/η²) N^δ ≤ N^{1+4τ+δ}`. -/
private theorem Uyw_q_le {X τ δ η ηt : ℝ} (hX : 1 ≤ X) (hηt : ηt = X ^ (-1 + 2 * τ))
    (hη : X ^ (-1 - τ) ≤ η) : ηt / η ^ 2 * X ^ δ ≤ X ^ (1 + 4 * τ + δ) := by
  have hX0 : 0 < X := by linarith
  have hηt0 : 0 < ηt := by rw [hηt]; positivity
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hη
  have hq : ηt / η ^ 2 ≤ X ^ (1 + 4 * τ) := by
    have hsq : X ^ (-1 - τ) * X ^ (-1 - τ) ≤ η ^ 2 := by
      rw [sq]; exact mul_le_mul hη hη (by positivity) hη0.le
    calc ηt / η ^ 2 ≤ ηt / (X ^ (-1 - τ) * X ^ (-1 - τ)) :=
          div_le_div_of_nonneg_left hηt0.le (by positivity) hsq
      _ = X ^ (1 + 4 * τ) := by
          rw [Uyw_rpow_mul hX0, hηt, ← Real.rpow_sub hX0]; congr 1; ring
  calc ηt / η ^ 2 * X ^ δ ≤ X ^ (1 + 4 * τ) * X ^ δ := by gcongr
    _ = X ^ (1 + 4 * τ + δ) := Uyw_rpow_mul hX0 _ _

/-- The factor `Q_i^out`: `N^δ(8/w' + 8η̃/w'²) + (2^{K'}w')⁻² ≤ (48 + 64/κ²) N^{1-c/6+2τ+δ}`. -/
private theorem Uyw_o_le {X c τ δ κ ηt w' : ℝ} {K' : ℕ} (hX : 1 ≤ X) (hc : 0 < c)
    (hc2 : c ≤ 1) (hτ : 0 < τ) (hδ : 0 ≤ δ) (hκ : 0 < κ)
    (hηt : ηt = X ^ (-1 + 2 * τ)) (hw' : w' = (2 * X ^ (1 - c / 6))⁻¹)
    (hK2 : κ / 4 < 2 ^ (K' + 1) * w') :
    X ^ δ * (8 / w' + 8 * ηt / w' ^ 2) + ((2 ^ K' * w') ^ 2)⁻¹ ≤
      (48 + 64 / κ ^ 2) * X ^ (1 - c / 6 + 2 * τ + δ) := by
  have hX0 : 0 < X := by linarith
  set E₁ : ℝ := 1 - c / 6 + 2 * τ + δ with hE₁
  have hw0 : 0 < w' := by rw [hw']; positivity
  have hwi : 8 / w' = 16 * X ^ (1 - c / 6) := by rw [hw']; field_simp; ring
  have hwi2 : 8 * ηt / w' ^ 2 = 32 * X ^ (1 + 2 * τ - c / 3) := by
    rw [hw', hηt]
    have : X ^ (1 + 2 * τ - c / 3) = X ^ (-1 + 2 * τ) * (X ^ (1 - c / 6) * X ^ (1 - c / 6)) := by
      rw [Uyw_rpow_mul hX0, Uyw_rpow_mul hX0]; congr 1; ring
    rw [this]; field_simp; ring
  have ht1 : X ^ δ * (8 / w' + 8 * ηt / w' ^ 2) ≤ 48 * X ^ E₁ := by
    rw [hwi, hwi2]
    have e1 : X ^ δ * (16 * X ^ (1 - c / 6) + 32 * X ^ (1 + 2 * τ - c / 3)) =
        16 * X ^ (δ + (1 - c / 6)) + 32 * X ^ (δ + (1 + 2 * τ - c / 3)) := by
      rw [← Uyw_rpow_mul hX0, ← Uyw_rpow_mul hX0]; ring
    rw [e1]
    have f1 : X ^ (δ + (1 - c / 6)) ≤ X ^ E₁ :=
      Real.rpow_le_rpow_of_exponent_le hX (by rw [hE₁]; linarith)
    have f2 : X ^ (δ + (1 + 2 * τ - c / 3)) ≤ X ^ E₁ :=
      Real.rpow_le_rpow_of_exponent_le hX (by rw [hE₁]; linarith)
    linarith
  have ht2 : ((2 ^ K' * w') ^ 2)⁻¹ ≤ 64 / κ ^ 2 * X ^ E₁ := by
    have hb : κ / 8 < 2 ^ K' * w' := by rw [pow_succ] at hK2; linarith
    have hb2 : ((2 ^ K' * w') ^ 2)⁻¹ ≤ 64 / κ ^ 2 := by
      rw [inv_le_comm₀ (by positivity) (by positivity)]
      rw [show (64 / κ ^ 2)⁻¹ = (κ / 8) ^ 2 by field_simp; norm_num]
      exact pow_le_pow_left₀ (by positivity) hb.le 2
    have hXE : (1 : ℝ) ≤ X ^ E₁ := Real.one_le_rpow hX (by rw [hE₁]; linarith)
    calc _ ≤ 64 / κ ^ 2 := hb2
      _ ≤ 64 / κ ^ 2 * X ^ E₁ := le_mul_of_one_le_right (by positivity) hXE
  linarith

/-- The factor `A_y`, good block: `θ N q₁ q₂ + 2N(o q₂ + q₁ o) ≤ (193 + 256/κ²) N^{3-c/36+8τ+2δ}`.
-/
private theorem Uyw_Ag_le {X c τ δ κ θ q₁ q₂ o : ℝ} (hX : 1 ≤ X) (hc : 0 < c) (hτ : 0 < τ)
    (hκ : 0 < κ) (hθ : θ = X ^ (-(c / 36)))
    (hq₁ : q₁ ≤ X ^ (1 + 4 * τ + δ)) (hq₂0 : 0 ≤ q₂)
    (hq₂ : q₂ ≤ X ^ (1 + 4 * τ + δ)) (ho0 : 0 ≤ o)
    (ho : o ≤ (48 + 64 / κ ^ 2) * X ^ (1 - c / 6 + 2 * τ + δ)) :
    θ / 2 * (q₁ * (X * q₂) + (X * q₁) * q₂) + 2 * X * (o * q₂ + q₁ * o) ≤
      (193 + 256 / κ ^ 2) * X ^ (3 - c / 36 + 8 * τ + 2 * δ) := by
  have hX0 : 0 < X := by linarith
  set E₁ : ℝ := 3 - c / 36 + 8 * τ + 2 * δ with hE₁
  set R : ℝ := X ^ (1 + 4 * τ + δ)
  set Co : ℝ := 48 + 64 / κ ^ 2
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hq12 : q₁ * q₂ ≤ R * R := mul_le_mul hq₁ hq₂ hq₂0 (by positivity)
  have hoq₂ : o * q₂ ≤ Co * X ^ (1 - c / 6 + 2 * τ + δ) * R :=
    mul_le_mul ho hq₂ hq₂0 (by positivity)
  have hq₁o : q₁ * o ≤ R * (Co * X ^ (1 - c / 6 + 2 * τ + δ)) :=
    mul_le_mul hq₁ ho ho0 (by positivity)
  have e1 : θ / 2 * (q₁ * (X * q₂) + (X * q₁) * q₂) = θ * X * (q₁ * q₂) := by ring
  have f1 : θ * X * (R * R) ≤ X ^ E₁ := by
    rw [hθ]
    have : X ^ (-(c / 36)) * X * (R * R) =
        X ^ (-(c / 36) + 1 + (1 + 4 * τ + δ) + (1 + 4 * τ + δ)) := by
      simp only [R, ← Uyw_rpow_mul hX0, Real.rpow_one]; ring
    rw [this]
    exact le_of_eq (by congr 1; rw [hE₁]; ring)
  have f2 : 2 * X * (Co * X ^ (1 - c / 6 + 2 * τ + δ) * R + R * (Co * X ^ (1 - c / 6 + 2 * τ + δ)))
      ≤ 4 * Co * X ^ E₁ := by
    have : 2 * X * (Co * X ^ (1 - c / 6 + 2 * τ + δ) * R + R * (Co * X ^ (1 - c / 6 + 2 * τ + δ)))
        = 4 * Co * X ^ ((1 : ℝ) + (1 - c / 6 + 2 * τ + δ) + (1 + 4 * τ + δ)) := by
      simp only [R, ← Uyw_rpow_mul hX0, Real.rpow_one]; ring
    rw [this]
    have hCo : 0 ≤ Co := by positivity
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX (by rw [hE₁]; linarith)) (by positivity)
  have g1 : θ * X * (q₁ * q₂) ≤ θ * X * (R * R) :=
    mul_le_mul_of_nonneg_left hq12 (by positivity)
  have g2 : 2 * X * (o * q₂ + q₁ * o) ≤
      2 * X * (Co * X ^ (1 - c / 6 + 2 * τ + δ) * R + R * (Co * X ^ (1 - c / 6 + 2 * τ + δ))) := by
    gcongr
  rw [e1]
  have : (193 + 256 / κ ^ 2) * X ^ E₁ = X ^ E₁ + 4 * Co * X ^ E₁ := by simp only [Co]; ring
  linarith

/-- The factor `A_y`, bad block: `4N q₁ q₂ ≤ 4 N^{3+8τ+2δ}`. -/
private theorem Uyw_Ab_le {X τ δ q₁ q₂ : ℝ} (hX : 1 ≤ X)
    (hq₁ : q₁ ≤ X ^ (1 + 4 * τ + δ)) (hq₂0 : 0 ≤ q₂) (hq₂ : q₂ ≤ X ^ (1 + 4 * τ + δ)) :
    4 * X * (q₁ * q₂) ≤ 4 * X ^ (3 + 8 * τ + 2 * δ) := by
  have hX0 : 0 < X := by linarith
  have h := mul_le_mul hq₁ hq₂ hq₂0 (by positivity)
  calc 4 * X * (q₁ * q₂) ≤ 4 * X * (X ^ (1 + 4 * τ + δ) * X ^ (1 + 4 * τ + δ)) := by gcongr
    _ = 4 * X ^ ((1 : ℝ) + (1 + 4 * τ + δ) + (1 + 4 * τ + δ)) := by
        simp only [← Uyw_rpow_mul hX0, Real.rpow_one]; ring
    _ = 4 * X ^ (3 + 8 * τ + 2 * δ) := by congr 2; ring

/-- **Assembly of the good and bad parts**: with `P̄ = N^{(3τ+δ)|s|}`,
`P̄ N⁻¹ A_good + P̄ N⁻¹ A_bad · K N^{-c'} ≤ ½ N^{2 - c' + (3|s|+16)τ}` once `c' ≤ c/36` and
`2 (C₁ + 4K) ≤ N^{6τ}` (`K = 2d+1`; RBM2D `5 N^{-c/18}` and `2 (C₁ + 20)`); here `(m+3)δ ≤ τ` is the
normalization of `δ`. -/
private theorem Uyw_good_total_le {X c c' τ δ C₁ K : ℝ} {sc m : ℕ} (hX : 1 ≤ X)
    (hcc : c' ≤ c / 36) (hτ : 0 < τ) (hδ : 0 ≤ δ) (hC₁ : 0 ≤ C₁) (hK : 0 ≤ K)
    (hsc : sc ≤ m) (hmδ : ((m : ℝ) + 3) * δ ≤ τ) (hslack : 2 * (C₁ + 4 * K) ≤ X ^ (6 * τ)) :
    X ^ ((3 * τ + δ) * (sc : ℝ)) * (X⁻¹ * (C₁ * X ^ (3 - c / 36 + 8 * τ + 2 * δ))) +
        X ^ ((3 * τ + δ) * (sc : ℝ)) * (X⁻¹ * (4 * X ^ (3 + 8 * τ + 2 * δ))) *
          (K * X ^ (-c')) ≤
      1 / 2 * X ^ (2 - c' + (3 * (sc : ℝ) + 16) * τ) := by
  have hX0 : 0 < X := by linarith
  set T : ℝ := 2 - c' + (3 * (sc : ℝ) + 16) * τ with hT
  have hsc' : (sc : ℝ) ≤ m := by exact_mod_cast hsc
  set a : ℝ := (3 * τ + δ) * (sc : ℝ)
  set e : ℝ := 3 - c / 36 + 8 * τ + 2 * δ
  set f : ℝ := 3 + 8 * τ + 2 * δ
  set g : ℝ := -c'
  have r1 : X ^ (a + e - 1) = X ^ a * X ^ e / X := by
    rw [Real.rpow_sub hX0, Real.rpow_add hX0 a e, Real.rpow_one]
  have r2 : X ^ (a + f + g - 1) = X ^ a * X ^ f * X ^ g / X := by
    rw [Real.rpow_sub hX0, Real.rpow_add hX0 (a + f) g, Real.rpow_add hX0 a f, Real.rpow_one]
  have e1 : X ^ a * (X⁻¹ * (C₁ * X ^ e)) = C₁ * X ^ (a + e - 1) := by
    rw [r1]
    generalize X ^ a = A
    generalize X ^ e = Ee
    field_simp
  have e2 : X ^ a * (X⁻¹ * (4 * X ^ f)) * (K * X ^ g) = 4 * K * X ^ (a + f + g - 1) := by
    rw [r2]
    generalize X ^ a = A
    generalize X ^ f = F
    generalize X ^ g = G
    field_simp
  rw [e1, e2]
  have hsd : (sc + 3 : ℝ) * δ ≤ τ := le_trans (by gcongr) hmδ
  have f1 : X ^ (a + e - 1) ≤ X ^ (T - 6 * τ) := by
    refine Real.rpow_le_rpow_of_exponent_le hX ?_
    simp only [a, e, hT]
    nlinarith
  have f2 : X ^ (a + f + g - 1) ≤ X ^ (T - 6 * τ) := by
    refine Real.rpow_le_rpow_of_exponent_le hX ?_
    simp only [a, f, g, hT]
    nlinarith
  have hsplit : X ^ T = X ^ (T - 6 * τ) * X ^ (6 * τ) := by
    rw [Uyw_rpow_mul hX0]; congr 1; ring
  have hpos : 0 ≤ X ^ (T - 6 * τ) := by positivity
  calc C₁ * X ^ (a + e - 1) + 4 * K * X ^ (a + f + g - 1)
      ≤ C₁ * X ^ (T - 6 * τ) + 4 * K * X ^ (T - 6 * τ) := by gcongr
    _ = 1 / 2 * (2 * (C₁ + 4 * K)) * X ^ (T - 6 * τ) := by ring
    _ ≤ 1 / 2 * X ^ (6 * τ) * X ^ (T - 6 * τ) := by gcongr
    _ = 1 / 2 * X ^ T := by rw [hsplit]; ring

/-- **Assembly of the crude part**: with `D ≥ (1+τ)(m+4) + 3` and `c' ≤ 2`,
`4 N^{(1+τ)(|s|+4)} · (4+m) N · 2N · N^{-D} ≤ 8(4+m) N⁻¹ ≤ ½ N^{2 - c' + (3|s|+16)τ}`. -/
private theorem Uyw_crude_total_le {X c' τ D : ℝ} {sc m : ℕ} (hX : 1 ≤ X) (hτ : 0 < τ)
    (hc : c' ≤ 2) (hsc : sc ≤ m) (hD : (1 + τ) * ((m : ℝ) + 4) + 3 ≤ D)
    (hXm : 16 * (4 + (m : ℝ)) ≤ X) :
    4 * X ^ ((1 + τ) * ((sc : ℝ) + 4)) *
        (((4 + (m : ℝ)) * X) * ((2 * X) * X ^ (-D))) ≤
      1 / 2 * X ^ (2 - c' + (3 * (sc : ℝ) + 16) * τ) := by
  have hX0 : 0 < X := by linarith
  have hsc' : (sc : ℝ) ≤ m := by exact_mod_cast hsc
  set a : ℝ := (1 + τ) * ((sc : ℝ) + 4)
  have r : X ^ (a + 1 + 1 + -D) = X ^ a * X * X * X ^ (-D) := by
    rw [Real.rpow_add hX0 (a + 1 + 1) (-D), Real.rpow_add hX0 (a + 1) 1, Real.rpow_add hX0 a 1,
      Real.rpow_one]
  have e : 4 * X ^ a * (((4 + (m : ℝ)) * X) * ((2 * X) * X ^ (-D))) =
      8 * (4 + (m : ℝ)) * X ^ (a + 1 + 1 + -D) := by
    rw [r]
    ring
  rw [e]
  have f : X ^ (a + 1 + 1 + -D) ≤ X ^ (-1 : ℝ) := by
    refine Real.rpow_le_rpow_of_exponent_le hX ?_
    simp only [a]
    nlinarith
  have hT : (1 : ℝ) ≤ X ^ (2 - c' + (3 * (sc : ℝ) + 16) * τ) :=
    Real.one_le_rpow hX (by
      have : (0 : ℝ) ≤ (3 * (sc : ℝ) + 16) * τ := by positivity
      linarith)
  rw [Real.rpow_neg_one] at f
  have h2 : 8 * (4 + (m : ℝ)) * X⁻¹ ≤ 1 / 2 := by
    rw [mul_inv_le_iff₀ hX0]; linarith
  calc 8 * (4 + (m : ℝ)) * X ^ (a + 1 + 1 + -D)
      ≤ 8 * (4 + (m : ℝ)) * X⁻¹ := by gcongr
    _ ≤ 1 / 2 := h2
    _ ≤ _ := by linarith

/-- The factors `Im m_t(w_j)`, product form: `∏_{j∈s} (η̃/Im w_j) N^δ ≤ N^{(3τ+δ)|s|}`. -/
private theorem Uyw_prod_row_le {X τ δ ηt : ℝ} (hX : 1 ≤ X) (hηt : ηt = X ^ (-1 + 2 * τ))
    {m : ℕ} (s : Finset (Fin m)) (w : Fin m → ℂ) (hw : ∀ j, X ^ (-1 - τ) ≤ (w j).im) :
    ∏ j ∈ s, (ηt / (w j).im * X ^ δ) ≤ X ^ ((3 * τ + δ) * (s.card : ℝ)) := by
  have hX0 : 0 < X := by linarith
  have hηt0 : 0 < ηt := by rw [hηt]; positivity
  have hwj : ∀ j, 0 < (w j).im := fun j => lt_of_lt_of_le (by positivity) (hw j)
  calc ∏ j ∈ s, (ηt / (w j).im * X ^ δ) ≤ ∏ _j ∈ s, X ^ (3 * τ + δ) := by
        refine Finset.prod_le_prod₀ (fun j _ => ?_) (fun j _ => ?_)
        · have := hwj j
          positivity
        · have h1 : ηt / (w j).im ≤ X ^ (3 * τ) := by
            calc ηt / (w j).im ≤ ηt / X ^ (-1 - τ) :=
                  div_le_div_of_nonneg_left hηt0.le (by positivity) (hw j)
              _ = X ^ (3 * τ) := by rw [hηt, ← Real.rpow_sub hX0]; congr 1; ring
          calc ηt / (w j).im * X ^ δ ≤ X ^ (3 * τ) * X ^ δ := by gcongr
            _ = X ^ (3 * τ + δ) := (Real.rpow_add hX0 _ _).symm
    _ = X ^ ((3 * τ + δ) * (s.card : ℝ)) := by
        rw [Finset.prod_const, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]

/-- On `Ξᶜ`, crude weight: `∏_{j∈s} (Im w_j)⁻¹ · 4 (Im u₁)⁻²(Im u₂)⁻² ≤ 4 N^{(1+τ)(|s|+4)}`. -/
private theorem Uyw_prod_crude_le {X τ : ℝ} (hX : 1 ≤ X) {m : ℕ} (s : Finset (Fin m))
    (w : Fin m → ℂ) (u₁ u₂ : ℂ) (hw : ∀ j, X ^ (-1 - τ) ≤ (w j).im)
    (hu₁ : X ^ (-1 - τ) ≤ u₁.im) (hu₂ : X ^ (-1 - τ) ≤ u₂.im) :
    (∏ j ∈ s, (w j).im⁻¹) * (4 * ((u₁.im⁻¹) ^ 2 * (u₂.im⁻¹) ^ 2)) ≤
      4 * X ^ ((1 + τ) * ((s.card : ℝ) + 4)) := by
  have hX0 : 0 < X := by linarith
  have hinv : ∀ {y : ℝ}, X ^ (-1 - τ) ≤ y → y⁻¹ ≤ X ^ (1 + τ) := by
    intro y hy
    calc y⁻¹ ≤ (X ^ (-1 - τ))⁻¹ := inv_anti₀ (by positivity) hy
      _ = X ^ (1 + τ) := by rw [← Real.rpow_neg hX0.le]; congr 1; ring
  have hP : ∏ j ∈ s, (w j).im⁻¹ ≤ X ^ ((1 + τ) * (s.card : ℝ)) := by
    calc _ ≤ ∏ _j ∈ s, X ^ (1 + τ) :=
          Finset.prod_le_prod₀ (fun j _ => inv_nonneg.2 (le_trans (by positivity) (hw j)))
            (fun j _ => hinv (hw j))
      _ = _ := by rw [Finset.prod_const, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
  have hU : ∀ {y : ℝ}, X ^ (-1 - τ) ≤ y → (y⁻¹) ^ 2 ≤ X ^ ((1 + τ) * 2) := by
    intro y hy
    calc (y⁻¹) ^ 2 ≤ (X ^ (1 + τ)) ^ 2 :=
          pow_le_pow_left₀ (inv_nonneg.2 (le_trans (by positivity) hy)) (hinv hy) 2
      _ = X ^ ((1 + τ) * 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  have hP0 : 0 ≤ ∏ j ∈ s, (w j).im⁻¹ :=
    Finset.prod_nonneg fun j _ => inv_nonneg.2 (le_trans (by positivity) (hw j))
  have hUU : (u₁.im⁻¹) ^ 2 * (u₂.im⁻¹) ^ 2 ≤ X ^ ((1 + τ) * 2) * X ^ ((1 + τ) * 2) :=
    mul_le_mul (hU hu₁) (hU hu₂) (by positivity) (by positivity)
  calc _ ≤ X ^ ((1 + τ) * (s.card : ℝ)) *
        (4 * (X ^ ((1 + τ) * 2) * X ^ ((1 + τ) * 2))) :=
        mul_le_mul hP (by linarith) (by positivity) (by positivity)
    _ = 4 * X ^ ((1 + τ) * ((s.card : ℝ) + 4)) := by
        rw [show (4 : ℝ) * X ^ ((1 + τ) * ((s.card : ℝ) + 4)) =
          4 * (X ^ ((1 + τ) * (s.card : ℝ)) * (X ^ ((1 + τ) * 2) * X ^ ((1 + τ) * 2))) by
          rw [Uyw_rpow_mul hX0, Uyw_rpow_mul hX0]; congr 2; ring]
        ring

/-- Grid energies stay in the local-law domain: a centre within `C` of `E`, a radius `r ≤ κ/4`
and `C + 2η̃ < κ/4` give `|E₀ - r + 2η̃j| < 2 - κ/2` for `j ≤ ⌈r/η̃⌉₊`. -/
private theorem Uyw_grid_energy_lt {E E₀ κ C r ηt : ℝ} {j : ℕ} (hηt : 0 < ηt)
    (hE : |E| ≤ 2 - κ) (hE₀ : |E₀ - E| ≤ C) (hr : 0 ≤ r) (hrκ : r ≤ κ / 4)
    (hC : C + 2 * ηt < κ / 4) (hj : j ∈ Finset.range (⌈r / ηt⌉₊ + 1)) :
    |E₀ - r + 2 * ηt * j| < 2 - κ / 2 := by
  have hj' : (j : ℝ) < r / ηt + 1 := by
    have h1 := Finset.mem_range.1 hj
    have h2 : (j : ℝ) ≤ ⌈r / ηt⌉₊ := by exact_mod_cast Nat.lt_succ_iff.1 h1
    linarith [Nat.ceil_lt_add_one (div_nonneg hr hηt.le)]
  have hj2 : 2 * ηt * j < 2 * r + 2 * ηt := by
    have h := mul_lt_mul_of_pos_left hj' (by positivity : (0 : ℝ) < 2 * ηt)
    have he : 2 * ηt * (r / ηt + 1) = 2 * r + 2 * ηt := by field_simp
    linarith
  have hj0 : 0 ≤ 2 * ηt * j := by positivity
  rw [abs_le] at hE hE₀
  rw [abs_lt]
  constructor <;> linarith

/-! ## §2 Measure-theoretic and deterministic helpers -/

/-- Integration of a simple majorant: `f ≤ A₀ + c_B 1_B + C_r 1_T` (measurable `B`, `T`,
nonnegative constants) gives `∫ f ≤ A₀ + c_B P(B) + C_r P(T)`.  No integrability or
measurability of `f` is needed (if `f` is not integrable its integral is `0`). -/
private theorem Uyw_integral_le_of_majorant {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} {B T : Set Ω} (hB : MeasurableSet B)
    (hT : MeasurableSet T) {A0 cB Cr : ℝ} (hA0 : 0 ≤ A0) (hcB : 0 ≤ cB) (hCr : 0 ≤ Cr)
    (hfg : ∀ ω, f ω ≤ A0 + cB * B.indicator 1 ω + Cr * T.indicator 1 ω) :
    ∫ ω, f ω ∂μ ≤ A0 + cB * μ.real B + Cr * μ.real T := by
  have hint1 : ∀ A : Set Ω, MeasurableSet A → Integrable (A.indicator (1 : Ω → ℝ)) μ :=
    fun A hA => (integrable_const (1 : ℝ)).indicator hA
  have hI1 : Integrable (fun ω => A0 + cB * B.indicator (1 : Ω → ℝ) ω) μ :=
    (integrable_const A0).add ((hint1 B hB).const_mul cB)
  have hI2 : Integrable (fun ω => Cr * T.indicator (1 : Ω → ℝ) ω) μ :=
    (hint1 T hT).const_mul Cr
  have hgi : Integrable (fun ω => A0 + cB * B.indicator (1 : Ω → ℝ) ω +
      Cr * T.indicator 1 ω) μ := hI1.add hI2
  have hval : ∫ ω, (A0 + cB * B.indicator (1 : Ω → ℝ) ω + Cr * T.indicator 1 ω) ∂μ =
      A0 + cB * μ.real B + Cr * μ.real T := by
    rw [integral_add hI1 hI2, integral_add (integrable_const A0) ((hint1 B hB).const_mul cB),
      integral_const, integral_const_mul, integral_const_mul, integral_indicator_one hB,
      integral_indicator_one hT]
    simp
  rw [← hval]
  by_cases hf : Integrable f μ
  · exact integral_mono hf hgi hfg
  · rw [integral_undef hf]
    refine integral_nonneg fun ω => ?_
    have h1 : 0 ≤ B.indicator (1 : Ω → ℝ) ω := Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    have h2 : 0 ≤ T.indicator (1 : Ω → ℝ) ω := Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    positivity

/-- Union bound over a finite family `S` of covering grids `(centre, radius)`: if for every grid
of `S` and every energy `e` of it the event `∃ x, Cb < ‖G_xx(e + iη̃)‖` has probability at most
`p`, then the failure of `jakGridGood` on some grid of `S` has probability at most `|S| · G · p`,
where `G` bounds the number of energies per grid. -/
private theorem Uyw_measure_grid_fail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Hr : Ω → Matrix ι ι ℂ) {ηt Cb : ℝ}
    (S : Finset (ℝ × ℝ)) (G : ℕ) (hG : ∀ q ∈ S, ⌈q.2 / ηt⌉₊ + 1 ≤ G) {p : ENNReal}
    (hp : ∀ q ∈ S, ∀ j ∈ Finset.range (⌈q.2 / ηt⌉₊ + 1),
      μ {ω | ∃ x : ι, Cb <
        ‖Gres (Hr ω) (((q.1 - q.2 + 2 * ηt * j : ℝ) : ℂ) + ηt * Complex.I) true x x‖} ≤ p) :
    μ {ω | ¬ ∀ q ∈ S, jakGridGood (Hr ω) ηt Cb q.1 q.2} ≤
      (S.card : ENNReal) * ((G : ENNReal) * p) := by
  have hsub : {ω | ¬ ∀ q ∈ S, jakGridGood (Hr ω) ηt Cb q.1 q.2} ⊆
      ⋃ q ∈ S, ⋃ j ∈ Finset.range (⌈q.2 / ηt⌉₊ + 1), {ω | ∃ x : ι, Cb <
        ‖Gres (Hr ω) (((q.1 - q.2 + 2 * ηt * j : ℝ) : ℂ) + ηt * Complex.I) true x x‖} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, not_forall] at hω
    obtain ⟨q, hq, hn⟩ := hω
    simp only [jakGridGood, not_forall, not_le] at hn
    obtain ⟨j, hj, x, hx⟩ := hn
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨q, hq, j, hj, x, hx.trans_le (Complex.im_le_norm _)⟩
  calc μ _ ≤ μ (⋃ q ∈ S, ⋃ j ∈ Finset.range (⌈q.2 / ηt⌉₊ + 1), {ω | ∃ x : ι, Cb <
        ‖Gres (Hr ω) (((q.1 - q.2 + 2 * ηt * j : ℝ) : ℂ) + ηt * Complex.I) true x x‖}) :=
        measure_mono hsub
    _ ≤ ∑ q ∈ S, μ (⋃ j ∈ Finset.range (⌈q.2 / ηt⌉₊ + 1), {ω | ∃ x : ι, Cb <
        ‖Gres (Hr ω) (((q.1 - q.2 + 2 * ηt * j : ℝ) : ℂ) + ηt * Complex.I) true x x‖}) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ S, ∑ j ∈ Finset.range (⌈q.2 / ηt⌉₊ + 1), μ {ω | ∃ x : ι, Cb <
        ‖Gres (Hr ω) (((q.1 - q.2 + 2 * ηt * j : ℝ) : ℂ) + ηt * Complex.I) true x x‖} :=
        Finset.sum_le_sum fun q _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ S, ∑ _j ∈ Finset.range (⌈q.2 / ηt⌉₊ + 1), p :=
        Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun j hj => hp q hq j hj
    _ = ∑ q ∈ S, ((⌈q.2 / ηt⌉₊ + 1 : ℕ) : ENNReal) * p := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ∑ _q ∈ S, (G : ENNReal) * p := by
        refine Finset.sum_le_sum fun q hq => ?_
        gcongr
        exact_mod_cast hG q hq
    _ = (S.card : ENNReal) * ((G : ENNReal) * p) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- `queBound` at `(ε₀, c, τ_Q) = (𝔡/3, 𝔡/6, 𝔡/30)` is `W^{-𝔡/30}` (`un_que_exponent`: `-𝔡/15 + 𝔡/30`). -/
private theorem Uyw_queBound_eq (W : ℕ) {𝔡 : ℝ} (h𝔡 : 0 < 𝔡) :
    queBound W 𝔡 (𝔡 / 3) (𝔡 / 6) (𝔡 / 30) = ENNReal.ofReal ((W : ℝ) ^ (-(𝔡 / 30))) := by
  unfold queBound
  rw [un_que_exponent h𝔡]
  congr 2
  ring

/-! ## §3 The normalized pointwise bound on the good event -/

/-- **Good-event pointwise bound, normalized** (factors `Im m_t(w_j)`, `Q_i`, `Q_i^out`, `A_y` off/on `B_y`,
with `η̃ = N^{-1+2τ}`, `C_b = N^δ`, `w' = N^{-1+c/6}/2`, `θ = N^{-c/36}`), the `uyw_pointwise_good` of the
`UywKernel` layer with the explicit constants; `c` is a free parameter `0 < c ≤ 1` (`c = 2𝔠𝔡` in the use). -/
private theorem Uyw_pointwise_good_norm {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) (lam : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) {m : ℕ} (s : Finset (Fin m))
    (w : Fin m → ℂ) (u₁ u₂ : ℂ) {X c τ δ κ ηt w' θ : ℝ} {K' : ℕ}
    (hX : (((W * L) ^ d : ℕ) : ℝ) = X) (hX1 : 1 ≤ X) (hc : 0 < c) (hc2 : c ≤ 1)
    (hτ : 0 < τ) (hδ : 0 ≤ δ) (hκ : 0 < κ)
    (hηt : ηt = X ^ (-1 + 2 * τ)) (hw' : w' = (2 * X ^ (1 - c / 6))⁻¹)
    (hθ : θ = X ^ (-(c / 36)))
    (hηu₁ : X ^ (-1 - τ) ≤ u₁.im) (hηu₁' : u₁.im ≤ ηt)
    (hηu₂ : X ^ (-1 - τ) ≤ u₂.im) (hηu₂' : u₂.im ≤ ηt)
    (hηw1 : ∀ j, X ^ (-1 - τ) ≤ (w j).im) (hηw' : ∀ j, (w j).im ≤ ηt)
    (hK2' : κ / 4 < 2 ^ (K' + 1) * w')
    (hG1 : ∀ k ≤ K', jakGridGood H ηt (X ^ δ) u₁.re (2 ^ k * w'))
    (hG2 : ∀ k ≤ K', jakGridGood H ηt (X ^ δ) u₂.re (2 ^ k * w'))
    (hG3 : jakGridGood H ηt (X ^ δ) u₁.re 0) (hG4 : jakGridGood H ηt (X ^ δ) u₂.re 0)
    (hG5 : ∀ j, jakGridGood H ηt (X ^ δ) (w j).re 0)
    (Bad : Zd d L → Prop) [DecidablePred Bad]
    (hBad : ∀ a0, ¬ Bad a0 → ∀ α β, |hH.eigenvalues α - u₁.re| ≤ w' →
      |hH.eigenvalues β - u₂.re| ≤ w' → ‖blockM2 d L W lam hH a0 α β‖ ≤ θ)
    (y : Idx d L W) (σ₁ σ₂ : Bool) :
    (∏ j ∈ s, (stieltjesN H (w j)).im) *
        ‖∑ x, (Gres H u₁ σ₁ * Gres H u₁ σ₁) x y * scirc d L W lam x y *
          (Gres H u₂ σ₂ * Gres H u₂ σ₂) y x‖ ≤
      X ^ ((3 * τ + δ) * (s.card : ℝ)) *
        (X⁻¹ * ((193 + 256 / κ ^ 2) * X ^ (3 - c / 36 + 8 * τ + 2 * δ) +
          (if Bad (siteBlock d L W y) then 4 * X ^ (3 + 8 * τ + 2 * δ) else 0))) := by
  have hX0 : 0 < X := by linarith
  have hηt0 : 0 < ηt := by rw [hηt]; positivity
  have hu₁0 : 0 < u₁.im := lt_of_lt_of_le (by positivity) hηu₁
  have hu₂0 : 0 < u₂.im := lt_of_lt_of_le (by positivity) hηu₂
  have hηw : ∀ j, 0 < (w j).im := fun j => lt_of_lt_of_le (by positivity) (hηw1 j)
  have hw'0 : 0 < w' := by rw [hw']; positivity
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hCb : 0 ≤ X ^ δ := by positivity
  have hq₁ := Uyw_q_le (δ := δ) hX1 hηt hηu₁
  have hq₂ := Uyw_q_le (δ := δ) hX1 hηt hηu₂
  have hq₁0 : 0 ≤ ηt / u₁.im ^ 2 * X ^ δ := by positivity
  have hq₂0 : 0 ≤ ηt / u₂.im ^ 2 * X ^ δ := by positivity
  have ho := Uyw_o_le (K' := K') (δ := δ) hX1 hc hc2 hτ hδ hκ hηt hw' hK2'
  have ho0 : 0 ≤ X ^ δ * (8 / w' + 8 * ηt / w' ^ 2) + ((2 ^ K' * w') ^ 2)⁻¹ := by positivity
  have hAg := Uyw_Ag_le hX1 hc hτ hκ hθ hq₁ hq₂0 hq₂ ho0 ho
  have hAb := Uyw_Ab_le hX1 hq₁ hq₂0 hq₂
  have hgood := uyw_pointwise_good hL lam hH m s w u₁ u₂ ηt (X ^ δ) w' θ
    ((193 + 256 / κ ^ 2) * X ^ (3 - c / 36 + 8 * τ + 2 * δ)) (4 * X ^ (3 + 8 * τ + 2 * δ))
    hu₁0 hηu₁' hu₂0 hηu₂' hηw hηw' hCb hw'0 hθ0 K' hG1 hG2 hG3 hG4 hG5 Bad hBad
    (by rw [hX]; exact hAg) (by rw [hX]; exact hAb) y σ₁ σ₂
  rw [hX] at hgood
  refine hgood.trans ?_
  have hP := Uyw_prod_row_le (δ := δ) hX1 hηt s w hηw1
  refine mul_le_mul_of_nonneg_right hP ?_
  have h0 : 0 ≤ (if Bad (siteBlock d L W y) then 4 * X ^ (3 + 8 * τ + 2 * δ) else 0) := by
    split_ifs <;> positivity
  positivity

/-! ## §4 The bound at one size and one time -/

set_option maxHeartbeats 400000 in
-- one declaration assembles the grid, bad-block and crude parts and runs many `positivity`/`gcongr` calls
/-- **Fixed-time assembly** of `(uywy7723r3rf)` at one size `(L, W)`, one random matrix `Hr` on a probability
space, and one choice of `s, w, u₁, u₂, y, b₁, b₂`: all eventual conditions are passed as explicit numeric
hypotheses, and the two `𝐇_t` claims enter as the probability bounds `hdiag` (`UNOUDiag` at the grid
energies) and `hque` (`UNOUQUE` at `τ_Q = 𝔡/30`).  The parameter `c = 2𝔠𝔡` of RBM2D `Uyw_fixed_time`
(`Uyw.lean:553`, d = 2, per site `y`) is `hcdef`; `X = N = (W L)^d`.  The conclusion exponent is the pin
exponent `c' = 𝔠𝔡/30`. -/
private theorem Uyw_fixed_time {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) (lam : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Hr : Ω → Matrix (Idx d L W) (Idx d L W) ℂ) (hH : ∀ ω, (Hr ω).IsHermitian)
    {X 𝔠 𝔡 c κ τ δ C₀ E D : ℝ} {m : ℕ}
    (hX : (((W * L) ^ d : ℕ) : ℝ) = X) (hWc : X ^ 𝔠 ≤ (W : ℝ))
    (h𝔠 : 0 < 𝔠) (h𝔡 : 0 < 𝔡) (hcdef : c = 2 * (𝔠 * 𝔡)) (hcd : 𝔠 * 𝔡 ≤ 1 / 2)
    (hlam : (W : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ lam)
    (hκ : 0 < κ) (hκ2 : κ ≤ 2) (hτ : 0 < τ) (hδ : 0 < δ)
    (hmδ : ((m : ℝ) + 3) * δ ≤ τ) (hD : (1 + τ) * ((m : ℝ) + 4) + 3 ≤ D)
    (hE : |E| ≤ 2 - κ) (h1 : 16 * (4 + (m : ℝ)) ≤ X) (h2 : 2 * C₀ ≤ X ^ (c / 6))
    (h3 : C₀ / X + 2 * X ^ (-1 + 2 * τ) < κ / 4) (h4 : X ^ (-1 + c / 6) < κ / 2)
    (h5 : 2 * ((193 + 256 / κ ^ 2) + 4 * ((2 * d + 1 : ℕ) : ℝ)) ≤ X ^ (6 * τ))
    (hdiag : ∀ e : ℝ, |e| < 2 - κ / 2 →
      P {ω | ∃ x : Idx d L W, X ^ δ <
        ‖Gres (Hr ω) ((e : ℂ) + ((X ^ (-1 + 2 * τ) : ℝ) : ℂ) * Complex.I) true x x‖} ≤
        ENNReal.ofReal (X ^ (-D)))
    (hque : ∀ b : Zd d L,
      P {ω | queBadMat d L W lam (𝔡 / 3) (𝔡 / 6) E b (Hr ω)} ≤
        ENNReal.ofReal ((W : ℝ) ^ (-(𝔡 / 30))))
    (s : Finset (Fin m)) (w : Fin m → ℂ) (u₁ u₂ : ℂ)
    (hw : ∀ i, |(w i).re - E| ≤ C₀ / X ∧ X ^ (-1 - τ) ≤ (w i).im ∧ (w i).im ≤ X ^ (-1 + τ))
    (hu₁ : |u₁.re - E| ≤ C₀ / X ∧ X ^ (-1 - τ) ≤ u₁.im ∧ u₁.im ≤ X ^ (-1 + τ))
    (hu₂ : |u₂.re - E| ≤ C₀ / X ∧ X ^ (-1 - τ) ≤ u₂.im ∧ u₂.im ≤ X ^ (-1 + τ))
    (y : Idx d L W) (b₁ b₂ : Bool) :
    ∫ ω, (∏ j ∈ s, (stieltjesN (Hr ω) (w j)).im) *
        ‖∑ x, (Gres (Hr ω) u₁ b₁ * Gres (Hr ω) u₁ b₁) x y * scirc d L W lam x y *
            (Gres (Hr ω) u₂ b₂ * Gres (Hr ω) u₂ b₂) y x‖ ∂P ≤
      X ^ (2 - 𝔠 * 𝔡 / 30 + (3 * (s.card : ℝ) + 16) * τ) := by
  classical
  have hcd0 : 0 < 𝔠 * 𝔡 := mul_pos h𝔠 h𝔡
  have hc : 0 < c := by rw [hcdef]; linarith
  have hc1 : c ≤ 1 := by rw [hcdef]; linarith
  have hX1 : 1 ≤ X := by have : (0 : ℝ) ≤ m := m.cast_nonneg; linarith
  have hX0 : 0 < X := by linarith
  obtain ⟨ηt, hηt⟩ : ∃ ηt : ℝ, ηt = X ^ (-1 + 2 * τ) := ⟨_, rfl⟩
  obtain ⟨w', hw'def⟩ : ∃ w' : ℝ, w' = X ^ (-1 + c / 6) / 2 := ⟨_, rfl⟩
  have hηt0 : 0 < ηt := by rw [hηt]; positivity
  have hCb0 : 0 < X ^ δ := by positivity
  have hw'0 : 0 < w' := by rw [hw'def]; positivity
  have hC₀n : 0 ≤ C₀ / X := le_trans (abs_nonneg _) hu₁.1
  have hηtκ : ηt ≤ κ / 4 := by rw [hηt]; linarith
  have hw'κ : w' ≤ κ / 4 := by rw [hw'def]; linarith
  have hw'eq : w' = (2 * X ^ (1 - c / 6))⁻¹ := by
    rw [hw'def, mul_inv, show -1 + c / 6 = -(1 - c / 6) by ring, Real.rpow_neg hX0.le]
    ring
  obtain ⟨K', hK1', hK2'⟩ := Uyw_exists_dyadic hw'0 hw'κ
  have hure₁ : |u₁.re - E| ≤ C₀ / X := hu₁.1
  have hure₂ : |u₂.re - E| ≤ C₀ / X := hu₂.1
  have hηu₁1 : X ^ (-1 - τ) ≤ u₁.im := hu₁.2.1
  have hηu₂1 : X ^ (-1 - τ) ≤ u₂.im := hu₂.2.1
  have hηu₁ : 0 < u₁.im := lt_of_lt_of_le (by positivity) hηu₁1
  have hηu₂ : 0 < u₂.im := lt_of_lt_of_le (by positivity) hηu₂1
  have hle_ηt : ∀ {y : ℝ}, y ≤ X ^ (-1 + τ) → y ≤ ηt := fun hy =>
    hy.trans (by rw [hηt]; exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith))
  have hηu₁' : u₁.im ≤ ηt := hle_ηt hu₁.2.2
  have hηu₂' : u₂.im ≤ ηt := hle_ηt hu₂.2.2
  have hηw1 : ∀ j, X ^ (-1 - τ) ≤ (w j).im := fun j => (hw j).2.1
  have hηw : ∀ j, 0 < (w j).im := fun j => lt_of_lt_of_le (by positivity) (hηw1 j)
  have hηw' : ∀ j, (w j).im ≤ ηt := fun j => hle_ηt (hw j).2.2
  -- the finite family of covering grids (centre, radius)
  obtain ⟨S, hSdef⟩ : ∃ S : Finset (ℝ × ℝ), S =
      ((Finset.range (K' + 1)).image fun k => (u₁.re, (2 : ℝ) ^ k * w')) ∪
        ((Finset.range (K' + 1)).image fun k => (u₂.re, (2 : ℝ) ^ k * w')) ∪
        {(u₁.re, 0)} ∪ {(u₂.re, 0)} ∪ (Finset.univ.image fun j => ((w j).re, (0 : ℝ))) :=
    ⟨_, rfl⟩
  have hrad : ∀ k ∈ Finset.range (K' + 1), (2 : ℝ) ^ k * w' ≤ κ / 4 := fun k hk =>
    le_trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) (by have := Finset.mem_range.1 hk; omega)) hw'0.le) hK1'
  have hS : ∀ q ∈ S, |q.1 - E| ≤ C₀ / X ∧ 0 ≤ q.2 ∧ q.2 ≤ κ / 4 := by
    intro q hq
    simp only [hSdef, Finset.mem_union, Finset.mem_image,
      Finset.mem_singleton, Finset.mem_univ, true_and] at hq
    rcases hq with (((⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) | rfl) | rfl) | ⟨j, rfl⟩
    · exact ⟨hure₁, by positivity, hrad k hk⟩
    · exact ⟨hure₂, by positivity, hrad k hk⟩
    · exact ⟨hure₁, le_rfl, by positivity⟩
    · exact ⟨hure₂, le_rfl, by positivity⟩
    · exact ⟨(hw j).1, le_rfl, by positivity⟩
  have hSmem1 : ∀ k ≤ K', (u₁.re, (2 : ℝ) ^ k * w') ∈ S := fun k hk => by
    rw [hSdef]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range]
    exact Or.inl (Or.inl (Or.inl (Or.inl ⟨k, by omega, rfl⟩)))
  have hSmem2 : ∀ k ≤ K', (u₂.re, (2 : ℝ) ^ k * w') ∈ S := fun k hk => by
    rw [hSdef]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨k, by omega, rfl⟩)))
  have hSmem3 : (u₁.re, (0 : ℝ)) ∈ S := by rw [hSdef]; simp
  have hSmem4 : (u₂.re, (0 : ℝ)) ∈ S := by rw [hSdef]; simp
  have hSmem5 : ∀ j, ((w j).re, (0 : ℝ)) ∈ S := fun j => by
    rw [hSdef]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr ⟨j, rfl⟩
  -- sizes: `2^{K'} ≤ X`, `#S ≤ (4+m) X`, grid size `≤ G ≤ 2X`
  have hηtinv : ηt⁻¹ ≤ X := by
    rw [hηt, ← Real.rpow_neg hX0.le]
    calc X ^ (-(-1 + 2 * τ)) ≤ X ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ = X := Real.rpow_one X
  have h2K' : (2 : ℝ) ^ K' ≤ X := by
    have hinv : (2 * w')⁻¹ ≤ X := by
      rw [hw'eq, mul_inv, inv_inv, ← mul_assoc, show (2 : ℝ)⁻¹ * 2 = 1 by norm_num, one_mul]
      calc X ^ (1 - c / 6) ≤ X ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
        _ = X := Real.rpow_one X
    calc (2 : ℝ) ^ K' ≤ 1 / (2 * w') := (le_div_iff₀ (by positivity)).2 (by linarith)
      _ = (2 * w')⁻¹ := one_div _
      _ ≤ X := hinv
  have hScard : (S.card : ℝ) ≤ (4 + m) * X := by
    have hc1 : S.card ≤ (K' + 1) + (K' + 1) + 1 + 1 + m := by
      rw [hSdef]
      refine (Finset.card_union_le _ _).trans ?_
      refine Nat.add_le_add ((Finset.card_union_le _ _).trans ?_) ?_
      · refine Nat.add_le_add ((Finset.card_union_le _ _).trans ?_) (by simp)
        refine Nat.add_le_add ((Finset.card_union_le _ _).trans ?_) (by simp)
        refine Nat.add_le_add ?_ ?_
        · exact (Finset.card_image_le).trans (by simp)
        · exact (Finset.card_image_le).trans (by simp)
      · exact (Finset.card_image_le).trans (by simp)
    have hK' : (K' : ℝ) + 1 ≤ X := by
      have : K' + 1 ≤ 2 ^ K' := Nat.lt_two_pow_self
      have h' : ((K' + 1 : ℕ) : ℝ) ≤ ((2 ^ K' : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h'
      linarith
    have hc1' : (S.card : ℝ) ≤ (K' + 1) + (K' + 1) + 1 + 1 + m := by exact_mod_cast hc1
    have : (0 : ℝ) ≤ m := m.cast_nonneg
    nlinarith
  have hGS : ∀ q ∈ S, ⌈q.2 / ηt⌉₊ + 1 ≤ ⌈X⌉₊ + 1 := by
    intro q hq
    obtain ⟨-, hq0, hqκ⟩ := hS q hq
    have : q.2 / ηt ≤ X := by
      rw [div_eq_mul_inv]
      calc q.2 * ηt⁻¹ ≤ 1 * X := mul_le_mul (by linarith) hηtinv (by positivity) zero_le_one
        _ = X := one_mul X
    exact Nat.add_le_add_right (Nat.ceil_mono this) 1
  have hG : ((⌈X⌉₊ + 1 : ℕ) : ℝ) ≤ 2 * X := by
    have : (0 : ℝ) ≤ m := m.cast_nonneg
    push_cast; linarith [Nat.ceil_lt_add_one hX0.le]
  -- the event `T`: failure of a covering grid, with its probability from `UNOUDiag`
  obtain ⟨T, hTdef⟩ : ∃ T : Set Ω, T = toMeasurable P
      {ω | ¬ ∀ q ∈ S, jakGridGood (Hr ω) ηt (X ^ δ) q.1 q.2} := ⟨_, rfl⟩
  have hTm : MeasurableSet T := by rw [hTdef]; exact measurableSet_toMeasurable _ _
  have hTprob : P.real T ≤ ((4 + (m : ℝ)) * X) * ((2 * X) * X ^ (-D)) := by
    have hgrid := Uyw_measure_grid_fail (μ := P) Hr (ηt := ηt)
      (Cb := X ^ δ) S (⌈X⌉₊ + 1) hGS (p := ENNReal.ofReal (X ^ (-D))) (by
        intro q hq j hj
        obtain ⟨hq1, hq0, hqκ⟩ := hS q hq
        have he := Uyw_grid_energy_lt hηt0 hE hq1 hq0 hqκ (by rw [hηt]; exact h3) hj
        have := hdiag _ he
        rw [← hηt] at this
        exact this)
    have hne : ((S.card : ENNReal) * (((⌈X⌉₊ + 1 : ℕ) : ENNReal) *
        ENNReal.ofReal (X ^ (-D)))) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top)
    have hX0D : 0 ≤ X ^ (-D) := by positivity
    calc P.real T
        = (P {ω | ¬ ∀ q ∈ S, jakGridGood (Hr ω) ηt (X ^ δ) q.1 q.2}).toReal := by
          rw [hTdef, Measure.real, measure_toMeasurable]
      _ ≤ ((S.card : ENNReal) * (((⌈X⌉₊ + 1 : ℕ) : ENNReal) *
            ENNReal.ofReal (X ^ (-D)))).toReal := ENNReal.toReal_mono hne hgrid
      _ = (S.card : ℝ) * (((⌈X⌉₊ + 1 : ℕ) : ℝ) * X ^ (-D)) := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hX0D,
            ENNReal.toReal_natCast, ENNReal.toReal_natCast]
      _ ≤ ((4 + (m : ℝ)) * X) * ((2 * X) * X ^ (-D)) := by gcongr
  -- the bad block of `y`: the pair event of the merged `measure_bad2_le_of_queBadMat`
  have hW0 : (0 : ℝ) < (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hW1 : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  obtain ⟨Bs, hBsdef⟩ : ∃ Bs : Set Ω, Bs = {ω | ∃ α β,
      |(hH ω).eigenvalues α - E| ≤ (((W * L) ^ d : ℕ) : ℝ)⁻¹ * (W : ℝ) ^ (𝔡 / 3) ∧
        |(hH ω).eigenvalues β - E| ≤ (((W * L) ^ d : ℕ) : ℝ)⁻¹ * (W : ℝ) ^ (𝔡 / 3) ∧
        (W : ℝ) ^ (-(𝔡 / 6)) ≤ ‖blockM2 d L W lam (hH ω) (siteBlock d L W y) α β‖} := ⟨_, rfl⟩
  obtain ⟨Bm, hBmdef⟩ : ∃ Bm : Set Ω, Bm = toMeasurable P Bs := ⟨_, rfl⟩
  have hBmm : MeasurableSet Bm := by rw [hBmdef]; exact measurableSet_toMeasurable _ _
  have hBprob : P.real Bm ≤ ((2 * d + 1 : ℕ) : ℝ) * X ^ (-(𝔠 * 𝔡 / 30)) := by
    have h := measure_bad2_le_of_queBadMat P hL hW1 h𝔡 hlam (siteBlock d L W y) hH _ hque
    have h' : P Bs ≤ ENNReal.ofReal (((2 * d + 1 : ℕ) : ℝ) * (W : ℝ) ^ (-(𝔡 / 30))) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, hBsdef]
      exact h
    have hWX := un_W_neg_le (N := X) (W := (W : ℝ)) (𝔠 := 𝔠) (x := 𝔡 / 30) hX0 hW0
      (by positivity) hWc
    rw [Measure.real, hBmdef, measure_toMeasurable]
    calc (P Bs).toReal ≤ ((2 * d + 1 : ℕ) : ℝ) * (W : ℝ) ^ (-(𝔡 / 30)) :=
          ENNReal.toReal_le_of_le_ofReal (by positivity) h'
      _ ≤ ((2 * d + 1 : ℕ) : ℝ) * X ^ (-(𝔠 * (𝔡 / 30))) := by gcongr
      _ = _ := by congr 2; ring
  -- the majorant constants
  have hsc : s.card ≤ m := by simpa using Finset.card_le_univ s
  obtain ⟨Pw, hPw⟩ : ∃ Pw : ℝ, Pw = X ^ ((3 * τ + δ) * (s.card : ℝ)) := ⟨_, rfl⟩
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = 193 + 256 / κ ^ 2 := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hPw0 : 0 ≤ Pw := by rw [hPw]; positivity
  have hA0 : 0 ≤ Pw * (X⁻¹ * (C₁ * X ^ (3 - c / 36 + 8 * τ + 2 * δ))) := by positivity
  have hcB0 : 0 ≤ Pw * (X⁻¹ * (4 * X ^ (3 + 8 * τ + 2 * δ))) := by positivity
  have hCr0 : 0 ≤ 4 * X ^ ((1 + τ) * ((s.card : ℝ) + 4)) := by positivity
  -- the two `w'`-windows lie in the window of the bad event
  have hwin : ∀ (γ : ℝ) (v : ℂ), |v.re - E| ≤ C₀ / X → |γ - v.re| ≤ w' →
      |γ - E| ≤ (((W * L) ^ d : ℕ) : ℝ)⁻¹ * (W : ℝ) ^ (𝔡 / 3) := by
    intro γ v hv hγ
    have hsplit : X ^ (-1 + c / 6) = X ^ (c / 6) * X⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hX0]; congr 1; ring
    have hC : C₀ / X ≤ X ^ (-1 + c / 6) / 2 := by
      rw [hsplit, div_eq_mul_inv]
      have := mul_le_mul_of_nonneg_right h2 (inv_nonneg.2 hX0.le)
      linarith
    have hXc : X ^ (c / 6) ≤ (W : ℝ) ^ (𝔡 / 3) := by
      calc X ^ (c / 6) = (X ^ 𝔠) ^ (𝔡 / 3) := by
            rw [← Real.rpow_mul hX0.le]; congr 1; rw [hcdef]; ring
        _ ≤ (W : ℝ) ^ (𝔡 / 3) := Real.rpow_le_rpow (by positivity) hWc (by positivity)
    calc |γ - E| ≤ |γ - v.re| + |v.re - E| := abs_sub_le _ _ _
      _ ≤ w' + C₀ / X := add_le_add hγ hv
      _ ≤ X ^ (-1 + c / 6) := by rw [hw'def]; linarith
      _ = X⁻¹ * X ^ (c / 6) := by rw [hsplit]; ring
      _ ≤ X⁻¹ * (W : ℝ) ^ (𝔡 / 3) := by gcongr
      _ = _ := by rw [hX]
  -- pointwise domination
  have hfg : ∀ ω, (∏ j ∈ s, (stieltjesN (Hr ω) (w j)).im) *
      ‖∑ x, (Gres (Hr ω) u₁ b₁ * Gres (Hr ω) u₁ b₁) x y * scirc d L W lam x y *
          (Gres (Hr ω) u₂ b₂ * Gres (Hr ω) u₂ b₂) y x‖ ≤
      Pw * (X⁻¹ * (C₁ * X ^ (3 - c / 36 + 8 * τ + 2 * δ))) +
        (Pw * (X⁻¹ * (4 * X ^ (3 + 8 * τ + 2 * δ)))) * Bm.indicator 1 ω +
        (4 * X ^ ((1 + τ) * ((s.card : ℝ) + 4))) * T.indicator 1 ω := by
    intro ω
    have hHω := hH ω
    have hind : ∀ (A : Set Ω), 0 ≤ A.indicator (1 : Ω → ℝ) ω :=
      fun A => Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    by_cases hωT : ω ∈ T
    · -- crude row
      have hc1 := uyw_pointwise_crude hL lam hHω m s w u₁ u₂ hηu₁ hηu₂ hηw y b₁ b₂
      have hc2 := Uyw_prod_crude_le hX1 s w u₁ u₂ hηw1 hηu₁1 hηu₂1
      have hTi : T.indicator (1 : Ω → ℝ) ω = 1 := by
        simp [Set.indicator_of_mem hωT]
      rw [hTi, mul_one]
      have := mul_nonneg hcB0 (hind Bm)
      linarith [hc1.trans hc2]
    · -- good event
      have hΞ : ∀ q ∈ S, jakGridGood (Hr ω) ηt (X ^ δ) q.1 q.2 := by
        by_contra hn'
        apply hωT
        rw [hTdef]
        exact subset_toMeasurable _ _ hn'
      have hBad : ∀ a0, ¬ (a0 ≠ siteBlock d L W y ∨ ω ∈ Bm) → ∀ α β,
          |hHω.eigenvalues α - u₁.re| ≤ w' → |hHω.eigenvalues β - u₂.re| ≤ w' →
          ‖blockM2 d L W lam hHω a0 α β‖ ≤ X ^ (-(c / 36)) := by
        intro a0 hna α β hα hβ
        push Not at hna
        obtain ⟨rfl, hnb⟩ := hna
        have hnb' : ω ∉ Bs := fun hb => hnb (by rw [hBmdef]; exact subset_toMeasurable _ _ hb)
        rw [hBsdef] at hnb'
        simp only [Set.mem_ofPred_eq, not_exists, not_and, not_le] at hnb'
        have hlt := hnb' α β (hwin _ u₁ hure₁ hα) (hwin _ u₂ hure₂ hβ)
        have hWX := un_W_neg_le (N := X) (W := (W : ℝ)) (𝔠 := 𝔠) (x := 𝔡 / 6) hX0 hW0
          (by positivity) hWc
        calc ‖blockM2 d L W lam hHω (siteBlock d L W y) α β‖ ≤ (W : ℝ) ^ (-(𝔡 / 6)) := hlt.le
          _ ≤ X ^ (-(𝔠 * (𝔡 / 6))) := hWX
          _ ≤ X ^ (-(c / 36)) :=
              Real.rpow_le_rpow_of_exponent_le hX1 (by rw [hcdef]; linarith)
      have hgood := Uyw_pointwise_good_norm hL lam hHω s w u₁ u₂ (δ := δ) (θ := X ^ (-(c / 36)))
        hX hX1 hc hc1 hτ hδ.le hκ hηt hw'eq rfl hηu₁1 hηu₁' hηu₂1 hηu₂' hηw1 hηw' hK2'
        (fun k hk => hΞ (u₁.re, (2 : ℝ) ^ k * w') (hSmem1 k hk))
        (fun k hk => hΞ (u₂.re, (2 : ℝ) ^ k * w') (hSmem2 k hk)) (hΞ (u₁.re, 0) hSmem3)
        (hΞ (u₂.re, 0) hSmem4) (fun j => hΞ ((w j).re, 0) (hSmem5 j))
        (fun a0 => a0 ≠ siteBlock d L W y ∨ ω ∈ Bm) hBad y b₁ b₂
      rw [← hPw, ← hC₁] at hgood
      have hTi : T.indicator (1 : Ω → ℝ) ω = 0 := Set.indicator_of_notMem hωT _
      rw [hTi, mul_zero, add_zero]
      by_cases hb : ω ∈ Bm
      · simp only [ne_eq, not_true_eq_false, false_or, hb, ↓reduceIte] at hgood
        rw [Set.indicator_of_mem hb, Pi.one_apply]
        calc _ ≤ _ := hgood
          _ = _ := by ring
      · simp only [ne_eq, not_true_eq_false, false_or, hb, ↓reduceIte] at hgood
        rw [Set.indicator_of_notMem hb]
        calc _ ≤ _ := hgood
          _ = _ := by ring
  have hint := Uyw_integral_le_of_majorant (μ := P) hBmm hTm hA0 hcB0 hCr0 hfg
  -- final normalisation: good part, bad part and crude part
  have hgoodT := Uyw_good_total_le (X := X) (c := c) (c' := 𝔠 * 𝔡 / 30) (δ := δ) (C₁ := C₁)
    (K := ((2 * d + 1 : ℕ) : ℝ)) (sc := s.card) (m := m) hX1
    (by rw [hcdef]; linarith) hτ hδ.le hC₁0 (Nat.cast_nonneg _) hsc hmδ (by rw [hC₁]; exact h5)
  have hcrudeT := Uyw_crude_total_le (X := X) (c' := 𝔠 * 𝔡 / 30) (τ := τ) (D := D)
    (sc := s.card) (m := m) hX1 hτ (by linarith) hsc hD h1
  rw [← hPw] at hgoodT
  have hB2 := mul_le_mul_of_nonneg_left hBprob hcB0
  have hT2 := mul_le_mul_of_nonneg_left hTprob hCr0
  have hXT : 0 ≤ X ^ (2 - 𝔠 * 𝔡 / 30 + (3 * (s.card : ℝ) + 16) * τ) := by positivity
  refine hint.trans ?_
  linarith

/-! ## §5 The eventual statement and the rows `uywRow`, `jakUywRow` -/

/-- **`UNUyw` at `c' = 𝔠𝔡/30` and `C = 3 nf + 16`**, for one small `τ_U`, from the two `𝐇_t` claims
(RBM2D private `Uyw_main` `:831`; `1_2:566-581`).  The weights `∏ Im m_t(z_k)` and the grid event come
from `UNOUDiag` (at `κ/2`, `ε := δ = τ_U/(nf+5)`, `D := (1+τ_U)(nf+4)+3`), the bad block from `UNOUQUE`
(at `κ`, `τ_Q = 𝔡/30`) through `measure_bad2_le_of_queBadMat`; the parameter of RBM2D `Uyw_fixed_time` is
`c = 2𝔠𝔡`.  The eventual conditions are `ev1`-`ev5`, `Bandwidth` and `WO` (`Admissible`), the two claims.
The index `i ≠ j` of the pin is not used. -/
theorem unUyw_of_ouClaims : ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ nf : ℕ, ∀ τU : ℝ, 0 < τU → τU ≤ 1 / 4 →
      UNOUQUE sz 𝔡 τU → UNOUDiag sz τU →
        UNUyw sz E nf τU (3 * (nf : ℝ) + 16) (𝔠 * 𝔡 / 30) := by
  intro d hd 𝔠 𝔡 sz hadm κ hκ E hE nf τU hτ hτ4 hQUE hDiag C₀ ε hC₀ hε
  have hcd : 𝔠 * 𝔡 ≤ 1 / 2 := un_cd_le_half d (by omega) 𝔠 𝔡 sz hadm
  obtain ⟨h𝔠, h𝔡, hsize', hband, hWO⟩ := hadm
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hcd0 : 0 < 𝔠 * 𝔡 := mul_pos h𝔠 h𝔡
  -- parameters fixed before `n`: `c = 2𝔠𝔡`, `δ = τU/(nf+5)` and the exponent `D` of `UNOUDiag`
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = 2 * (𝔠 * 𝔡) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; linarith
  have hc1 : c ≤ 1 := by rw [hcdef]; linarith
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = τU / (nf + 5) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hmδ : ((nf : ℝ) + 3) * δ ≤ τU := by
    rw [hδdef, mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = (1 + τU) * ((nf : ℝ) + 4) + 3 := ⟨_, rfl⟩
  have hD0 : 0 < D := by rw [hDdef]; positivity
  have hsize : Tendsto (fun n => Nsz sz n) atTop atTop := hsize'
  -- the eventual conditions on `n` (finitely many, uniform in `t, s, z, i, j, y, b₁, b₂`)
  have ev1 : ∀ᶠ n in atTop, 16 * (4 + (nf : ℝ)) ≤ Nsz sz n :=
    hsize.eventually_ge_atTop _
  have ev2 : ∀ᶠ n in atTop, 2 * C₀ ≤ Nsz sz n ^ (c / 6) :=
    ((tendsto_rpow_atTop (by positivity)).comp hsize).eventually_ge_atTop _
  have ev3 : ∀ᶠ n in atTop, C₀ / Nsz sz n + 2 * Nsz sz n ^ (-1 + 2 * τU) < κ / 4 := by
    have h1 : Tendsto (fun n => C₀ / Nsz sz n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hsize
    have h2 : Tendsto (fun n => Nsz sz n ^ (-1 + 2 * τU)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := 1 - 2 * τU) (by linarith)).comp hsize
      refine this.congr fun n => ?_
      simp only [Function.comp]; congr 1; ring
    have h3 := h1.add (h2.const_mul 2)
    simp only [mul_zero, add_zero] at h3
    exact h3.eventually_lt_const (by positivity)
  have ev4 : ∀ᶠ n in atTop, Nsz sz n ^ (-1 + c / 6) < κ / 2 := by
    have h2 : Tendsto (fun n => Nsz sz n ^ (-1 + c / 6)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := 1 - c / 6) (by linarith)).comp hsize
      refine this.congr fun n => ?_
      simp only [Function.comp]; congr 1; ring
    exact h2.eventually_lt_const (by positivity)
  have ev5 : ∀ᶠ n in atTop,
      2 * ((193 + 256 / κ ^ 2) + 4 * ((2 * d + 1 : ℕ) : ℝ)) ≤ Nsz sz n ^ (6 * τU) :=
    ((tendsto_rpow_atTop (by positivity)).comp hsize).eventually_ge_atTop _
  have evD := hDiag (κ / 2) δ D (half_pos hκ) hδ hD0
  have evQ := hQUE κ (𝔡 / 30) hκ (by positivity)
  filter_upwards [hband, hWO, ev1, ev2, ev3, ev4, ev5, evD, evQ] with
    n hWn hWOn h1 h2 h3 h4 h5 hDn hQn
  intro z hz t ht0 htT s i j _hij y b₁ b₂
  have hX1 : (1 : ℝ) ≤ Nsz sz n := by
    have : (0 : ℝ) ≤ nf := nf.cast_nonneg
    linarith
  have hsc : s.card ≤ nf := by simpa using Finset.card_le_univ s
  have hfix := Uyw_fixed_time (sz.three_le_L n) (sz.lam n) (ouP (UNModel.band sz) n)
    (ouMat (UNModel.band sz) n t) (ouMat_isHermitian (UNModel.band sz) n t) (X := Nsz sz n)
    (𝔠 := 𝔠) (𝔡 := 𝔡) (c := c) (κ := κ) (τ := τU) (δ := δ) (C₀ := C₀) (E := E) (D := D)
    (m := nf) rfl hWn h𝔠 h𝔡 hcdef hcd hWOn.1 hκ hκ2 hτ hδ hmδ (by rw [hDdef]) hE h1 h2 h3 h4 h5
    (fun e he => hDn t ht0 htT e he.le)
    (fun b => (hQn t ht0 htT E hE b).trans (Uyw_queBound_eq _ h𝔡).le) s z (z i) (z j)
    (fun k => hz k) (hz i) (hz j) y b₁ b₂
  refine hfix.trans ?_
  calc Nsz sz n ^ (2 - 𝔠 * 𝔡 / 30 + (3 * (s.card : ℝ) + 16) * τU)
      ≤ Nsz sz n ^ (2 - 𝔠 * 𝔡 / 30 + (3 * (nf : ℝ) + 16) * τU) := by
        refine Real.rpow_le_rpow_of_exponent_le hX1 ?_
        have : (s.card : ℝ) ≤ nf := by exact_mod_cast hsc
        nlinarith
    _ = 1 * Nsz sz n ^ (2 - 𝔠 * 𝔡 / 30 + (3 * (nf : ℝ) + 16) * τU) := (one_mul _).symm
    _ ≤ Nsz sz n ^ ε * Nsz sz n ^ (2 - 𝔠 * 𝔡 / 30 + (3 * (nf : ℝ) + 16) * τU) := by
        gcongr
        exact Real.one_le_rpow hX1 hε.le

/-- **The `Uyw` half of the row `UNJakUywRow`** (RBM2D `uywRow` `:898`): the weighted `(uywy7723r3rf)`
(`1_2:566-581`) at `c' = 𝔠𝔡/30` and `C = 3 nf + 16`, from the `𝐇_t` claims, with `τ₀ = min τ₁ (1/4)`.
`UNLocAvgBand` is the first hypothesis of the row and is not used.  Same hypotheses and quantifiers as
`jakRow` (`Jak.lean:931`). -/
theorem uywRow :
    UNLocAvgBand → UNOUClaims → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ nf : ℕ, ∃ C τ₀ : ℝ, 0 < τ₀ ∧
        ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → UNUyw sz E nf τU C (𝔠 * 𝔡 / 30) := by
  intro _hloc hclaims d hd 𝔠 𝔡 sz hadm κ hκ E hE nf
  obtain ⟨τ₁, hτ₁, hτ⟩ := hclaims d hd 𝔠 𝔡 sz hadm
  refine ⟨3 * (nf : ℝ) + 16, min τ₁ (1 / 4), lt_min hτ₁ (by norm_num), ?_⟩
  intro τU hτU hτle
  obtain ⟨hQ, hD⟩ := hτ τU hτU (le_min_iff.1 hτle).1
  exact unUyw_of_ouClaims d hd 𝔠 𝔡 sz hadm κ hκ E hE nf τU hτU (le_min_iff.1 hτle).2 hQ hD

/-- **The row `UNJakUywRow`** (RBM2D `jakUywRow` `:951`): `jakRow` and `uywRow` have the common constant
`C = 3 nf + 16` and the common range `τ₀ = min τ₁ (1/4)`, so no monotonicity lemma is needed. -/
theorem jakUywRow : UNJakUywRow := by
  intro hloc hclaims d hd 𝔠 𝔡 sz hadm κ hκ E hE nf
  obtain ⟨τ₁, hτ₁, hτ⟩ := hclaims d hd 𝔠 𝔡 sz hadm
  refine ⟨3 * (nf : ℝ) + 16, min τ₁ (1 / 4), lt_min hτ₁ (by norm_num), ?_⟩
  intro τU hτU hτle
  obtain ⟨hQ, hD⟩ := hτ τU hτU (le_min_iff.1 hτle).1
  exact ⟨unJak_of_ouClaims d hd 𝔠 𝔡 sz hadm κ hκ E hE nf τU hτU (le_min_iff.1 hτle).2 hQ hD,
    unUyw_of_ouClaims d hd 𝔠 𝔡 sz hadm κ hκ E hE nf τU hτU (le_min_iff.1 hτle).2 hQ hD⟩

/-! ## §6 Compiled nonempty instances (namespace `RBM.Univ.UywInst`)

The targets at the preflight size sequence `sz0` (`d = 3`, `L_n = 4(n+1)`, `W_n = (2(n+1))^5`,
`Admissible (1/6) (1/10)`: `UNInst.sz0_adm`), `κ = 1/2`, `E = 1` (`|E| = 1 ≤ 3/2 = 2 - κ`), `nf = 2`.
`UNLocAvgBand` and `UNOUClaims` are pins of other gates and stay hypotheses of `inst_row`/`inst_uywRow`;
`UNOUQUE` and `UNOUDiag` stay hypotheses of `inst_unUyw`; every deterministic hypothesis is discharged.
`inst_window` shows that the premises of `UNUyw` at these data are satisfiable at every size: two distinct
window points `z 0 = 1 + i N⁻¹`, `z 1 = 1 + N⁻¹ + i N⁻¹` lie in `InWindow sz0 1 1 τ_U n` (`i ≠ j` of the pin is
`(0 : Fin 2) ≠ 1`) and `t = 0 ≤ t*`. -/

namespace UywInst

theorem inst_row :
    UNLocAvgBand → UNOUClaims →
      ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
        UNJak SizesInst.sz0 1 2 τU C ((1 / 6 : ℝ) * (1 / 10) / 30) ∧
          UNUyw SizesInst.sz0 1 2 τU C ((1 / 6 : ℝ) * (1 / 10) / 30) :=
  fun hloc hOU =>
    jakUywRow hloc hOU 3 le_rfl (1 / 6) (1 / 10) SizesInst.sz0 UNInst.sz0_adm (1 / 2) (by norm_num) 1
      (by norm_num) 2

theorem inst_uywRow :
    UNLocAvgBand → UNOUClaims →
      ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
        UNUyw SizesInst.sz0 1 2 τU C ((1 / 6 : ℝ) * (1 / 10) / 30) :=
  fun hloc hOU =>
    uywRow hloc hOU 3 le_rfl (1 / 6) (1 / 10) SizesInst.sz0 UNInst.sz0_adm (1 / 2) (by norm_num) 1
      (by norm_num) 2

/-- `unUyw_of_ouClaims` at `sz0`, `κ = 1/2`, `E = 1`, `nf = 2`, any `τ_U ∈ (0, 1/4]`; the two `𝐇_t` claims
at `τ_U` are hypotheses (pins of other gates). -/
theorem inst_unUyw :
    ∀ τU : ℝ, 0 < τU → τU ≤ 1 / 4 →
      UNOUQUE SizesInst.sz0 (1 / 10) τU → UNOUDiag SizesInst.sz0 τU →
        UNUyw SizesInst.sz0 1 2 τU (3 * ((2 : ℕ) : ℝ) + 16) ((1 / 6 : ℝ) * (1 / 10) / 30) :=
  fun τU hτ hτ4 hQUE hDiag =>
    unUyw_of_ouClaims 3 le_rfl (1 / 6) (1 / 10) SizesInst.sz0 UNInst.sz0_adm (1 / 2) (by norm_num) 1
      (by norm_num) 2 τU hτ hτ4 hQUE hDiag

theorem inst_window :
    ∀ (n : ℕ) (τU : ℝ), 0 < τU →
      ∃ z : Fin 2 → ℂ, (∀ i, InWindow SizesInst.sz0 1 1 τU n (z i)) ∧ z 0 ≠ z 1 ∧
        (0 : Fin 2) ≠ 1 ∧ 0 ≤ ouTStar SizesInst.sz0 τU n := by
  intro n τU hτU
  have hN : (1 : ℝ) ≤ Nsz SizesInst.sz0 n := by
    have : 1 ≤ SizesInst.sz0.size n := by
      simp only [Sizes.size, SizesInst.sz0]
      exact Nat.one_le_pow _ _ (by positivity)
    exact_mod_cast this
  have hN0 : (0 : ℝ) < Nsz SizesInst.sz0 n := by linarith
  have hlo : Nsz SizesInst.sz0 n ^ (-1 - τU) ≤ (Nsz SizesInst.sz0 n)⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hhi : (Nsz SizesInst.sz0 n)⁻¹ ≤ Nsz SizesInst.sz0 n ^ (-1 + τU) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  refine ⟨![(⟨1, (Nsz SizesInst.sz0 n)⁻¹⟩ : ℂ), (⟨1 + (Nsz SizesInst.sz0 n)⁻¹, (Nsz SizesInst.sz0 n)⁻¹⟩ : ℂ)],
    ?_, ?_, by decide, by unfold ouTStar; positivity⟩
  · intro i
    fin_cases i
    · exact ⟨by simp, hlo, hhi⟩
    · refine ⟨?_, hlo, hhi⟩
      change |1 + (Nsz SizesInst.sz0 n)⁻¹ - 1| ≤ 1 / Nsz SizesInst.sz0 n
      simp
  · intro h
    have h' : (1 : ℝ) = 1 + (Nsz SizesInst.sz0 n)⁻¹ := congrArg Complex.re h
    exact inv_ne_zero hN0.ne' (by linarith)

end UywInst

#print axioms RBM.Univ.unUyw_of_ouClaims
#print axioms RBM.Univ.uywRow
#print axioms RBM.Univ.jakUywRow
#print axioms RBM.Univ.UywInst.inst_row
#print axioms RBM.Univ.UywInst.inst_uywRow
#print axioms RBM.Univ.UywInst.inst_unUyw
#print axioms RBM.Univ.UywInst.inst_window

end RBM.Univ
