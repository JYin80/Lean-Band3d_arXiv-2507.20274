/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.NewKLKGen
import RBM3D.Chain.Step2Kern
import RBM3D.BA.Step1Fam
import RBM3D.BA.Step2BA
import RBM3D.BA.EMn2BA
import RBM3D.BA.KSolve
import RBM3D.BA.KTreeRep
import RBM3D.BA.Prop6Path
import RBM3D.BA.Ward
import RBM3D.BA.EKPins

/-!
# `lem:newKLK` and the `𝒦^{(2)}` decay at the block Anderson carrier (BA-T row T3-BA, ticket T2424)

Design `docs/reports/T2379-design.md` §2 (row T3); supervisor `docs/supervisor/2026-10-11-0853.md` (BAT-F1, BAT-F2).
The generic theorem `stNewKLKgL'_of` (`Chain/NewKLKGen.lean:617`) needs `NewKLKGenHyp` (F5-F9); this file proves them at the BA
family `baStep2Fam` (`BA/Step2BA.lean:157`, `S = 1`, `m = BAmF`), so the primed pins hold at BA.

* `baNewKLKGenHyp` (target 1): F5-F9 at `fun sz E => baStep2Fam sz E`, for `3 ≤ d`, `κ, 𝔡 > 0`.
* `baSTNewKLKgL'` (target 2): `STNewKLKgL' d (fun sz E => baStep2Fam sz E)`.
* `baSTK2decaygL'` (target 3, BAT-F2): `STK2decaygL' d (fun sz E => baStep2Fam sz E)`.

F7 (BAT-F1) is the real BA `Θ`-convolution: `thetaKer = Θ_BA M^{(σσ')}` (`Step2Kern_thetaKer_BA`), whose entries decay as
`‖(Θ M^{(σσ')})_{ab}‖ ≤ Q₀ 𝒯_u(|a-b|_∞)` for every `0 ≤ u < 1` (`NewKLKBA_tail`: `u ≥ 1/2` from the resolvent identity and
`BAProp5`; `u < 1/2` from `baComp_holds`), with the row sum `(1-u)⁻¹` of `baComp_row_le`; then the convolution estimate against
`tailW` is a copy of `nkl_conv_P` (`Induction/NewKLK.lean:334`) for a generic kernel.  `𝒦^{(2)} = W^{-d} Θ M^{(σσ')}` is `(Kn2sol)` of
`baKsolve` (`baK_unique`).  All constants depend on `(d, κ, 𝔡)` only; `κ ≤ Im m` is the premise; no scalar `m`.

Ports: copies of `nkl_conv_P` (`Induction/NewKLK.lean:334`) and `k2d_theta_tail` (`Induction/Step2K2.lean:78`) in this repository
(no RBM1D/RBM2D text).
-/

set_option linter.style.longLine false

open private nkl_Cs_ge_one nkl_tailT_le_tailW nkl_tailW_eq_of_near nkl_tailW_far nkl_tailT_shift
  from RBM3D.Induction.NewKLK
open private k2d_sqrt_le k2d_zdistInf_neg from RBM3D.Induction.Step2K2

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The convolution estimate for a generic kernel (copy of `nkl_conv_P`) -/

section Conv

variable {d L : ℕ} [NeZero L] {g t : ℝ} {ℓ W D : ℝ}

/-- **Bound 1 core for a generic kernel `X`** (copy of `nkl_conv_P`, `Induction/NewKLK.lean:334`, with `S Θ` replaced by `X`):
`‖X_{ab}‖ ≤ Q 𝒯_t(|a-b|_∞)`, row sums `≤ c`, `(TTT2)` with `C_T` give
`Σ_b ‖X_{ab}‖ 𝒯̃(|b-a'|) ≤ (Q C_T + C_s c) 𝒯̃(|a-a'|)`. -/
private theorem NewKLKBA_conv_P (hW : 0 < W) (hℓ : 0 ≤ ℓ) {X : Matrix (Zd d L) (Zd d L) ℂ} {Q CT c : ℝ}
    (hQ : 0 ≤ Q) (hCT : 0 ≤ CT)
    (hTail : ∀ a b : Zd d L, ‖X a b‖ ≤ Q * tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ))
    (hRow : ∀ a : Zd d L, ∑ b, ‖X a b‖ ≤ c)
    (hTTT : ∀ a b : Zd d L, ∑ x : Zd d L, tailT d L g t ((zdistInf d L (a - x) : ℕ) : ℝ) *
        tailT d L g t ((zdistInf d L (x - b) : ℕ) : ℝ) ≤
      CT * tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ)) (a a' : Zd d L) :
    ∑ b, ‖X a b‖ * tailW d L g t ℓ W D ((zdistInf d L (b - a') : ℕ) : ℝ) ≤
      (Q * CT + (2 ^ (d - 2) * Real.exp 1) * c) *
        tailW d L g t ℓ W D ((zdistInf d L (a - a') : ℕ) : ℝ) := by
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (NeZero.one_le (n := L))
  set P : ℝ → ℝ := tailW d L g t ℓ W D with hP
  have hdist : ∀ x : Zd d L, ((zdistInf d L x : ℕ) : ℝ) = 0 ∨ 1 ≤ ((zdistInf d L x : ℕ) : ℝ) := by
    intro x
    rcases Nat.eq_zero_or_pos (zdistInf d L x) with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  have hterm : ∀ b : Zd d L, ‖X a b‖ * P ((zdistInf d L (b - a') : ℕ) : ℝ) ≤
      Q * (tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ) *
        tailT d L g t ((zdistInf d L (b - a') : ℕ) : ℝ)) +
      (2 ^ (d - 2) * Real.exp 1) * (‖X a b‖ * P ((zdistInf d L (a - a') : ℕ) : ℝ)) := by
    intro b
    set r : ℝ := ((zdistInf d L (b - a') : ℕ) : ℝ) with hr
    have hr0 : 0 ≤ r := Nat.cast_nonneg _
    have hCs := nkl_Cs_ge_one (d := d)
    have hnorm := norm_nonneg (X a b)
    by_cases hnear : 1 ≤ ℓ ∧ r ≤ ℓ ∧ W ^ (-D) ≤ tailT d L g t r
    · rw [hP, nkl_tailW_eq_of_near hnear.2.1 hnear.2.2]
      have h1 := mul_le_mul_of_nonneg_right (hTail a b) (tailT_nonneg (d := d) (L := L) (g := g)
        (t := t) hr0)
      have h2 : 0 ≤ (2 ^ (d - 2) * Real.exp 1) * (‖X a b‖ * P ((zdistInf d L (a - a') : ℕ) : ℝ)) := by
        have := (tailW_pos (d := d) (L := L) (g := g) (t := t) (ℓ := ℓ) (D := D) hW
          ((zdistInf d L (a - a') : ℕ) : ℝ)).le
        positivity
      nlinarith
    · have hfar := nkl_tailW_far (d := d) (L := L) (g := g) (t := t) hL1 hW hℓ hr0
        (Nat.cast_nonneg (zdistInf d L (a - a'))) (hdist _) hnear
      have h1 : 0 ≤ Q * (tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ) *
          tailT d L g t ((zdistInf d L (b - a') : ℕ) : ℝ)) :=
        mul_nonneg hQ (mul_nonneg (tailT_nonneg (Nat.cast_nonneg _)) (tailT_nonneg (Nat.cast_nonneg _)))
      calc ‖X a b‖ * P r
          ≤ ‖X a b‖ * ((2 ^ (d - 2) * Real.exp 1) * P ((zdistInf d L (a - a') : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hfar hnorm
        _ = (2 ^ (d - 2) * Real.exp 1) * (‖X a b‖ * P ((zdistInf d L (a - a') : ℕ) : ℝ)) := by ring
        _ ≤ _ := le_add_of_nonneg_left h1
  have hT0 : tailT d L g t ((zdistInf d L (a - a') : ℕ) : ℝ) ≤ P ((zdistInf d L (a - a') : ℕ) : ℝ) :=
    nkl_tailT_le_tailW hℓ (Nat.cast_nonneg _)
  have hP0 : 0 ≤ P ((zdistInf d L (a - a') : ℕ) : ℝ) :=
    (tailW_pos (d := d) (L := L) (g := g) (t := t) (ℓ := ℓ) (D := D) hW _).le
  have hCs := nkl_Cs_ge_one (d := d)
  calc ∑ b, ‖X a b‖ * P ((zdistInf d L (b - a') : ℕ) : ℝ)
      ≤ ∑ b, (Q * (tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ) *
        tailT d L g t ((zdistInf d L (b - a') : ℕ) : ℝ)) +
      (2 ^ (d - 2) * Real.exp 1) * (‖X a b‖ * P ((zdistInf d L (a - a') : ℕ) : ℝ))) :=
        Finset.sum_le_sum fun b _ => hterm b
    _ = Q * ∑ b, (tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ) *
        tailT d L g t ((zdistInf d L (b - a') : ℕ) : ℝ)) +
      (2 ^ (d - 2) * Real.exp 1) * ((∑ b, ‖X a b‖) * P ((zdistInf d L (a - a') : ℕ) : ℝ)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
    _ ≤ Q * (CT * tailT d L g t ((zdistInf d L (a - a') : ℕ) : ℝ)) +
      (2 ^ (d - 2) * Real.exp 1) * (c * P ((zdistInf d L (a - a') : ℕ) : ℝ)) := by
        refine add_le_add (mul_le_mul_of_nonneg_left (hTTT a a') hQ) ?_
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hRow a) hP0) (by positivity)
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hT0 (mul_nonneg hQ hCT)
        nlinarith

end Conv

/-! ## 2. The tail of the kernel `Θ_BA M^{(σσ')}`: `‖(ΘQ)_{ab}‖ ≤ Q₀ 𝒯_u(|a-b|_∞)` -/

section Tail

/-- **The tail bound of one propagator entry** (copy of `k2d_theta_tail`, `Induction/Step2K2.lean:78`, for a generic translation
invariant `Θ`): from `‖Θ(0,x)‖ ≤ C₅ B_{t,|x|₁} e^{-c|x|₁/ℓ_t}` to `‖Θ(a,b)‖ ≤ C₅ e^{1/(4c)} 𝒯_t(|a-b|_∞)`. -/
private theorem NewKLKBA_theta_tail {d : ℕ} {C₅ c : ℝ} (hC₅ : 0 < C₅) (hc : 0 < c) {L : ℕ} [NeZero L]
    {g t : ℝ} {Th : Matrix (Zd d L) (Zd d L) ℂ} (hshift : ∀ a b : Zd d L, Th a b = Th 0 (b - a))
    (H : ∀ x : Zd d L, ‖Th 0 x‖ ≤
      C₅ * Bparam d L g t (zdistD d L x) * Real.exp (-c * (zdistD d L x : ℝ) / ellT L g t))
    (a b : Zd d L) :
    ‖Th a b‖ ≤ C₅ * Real.exp (1 / (4 * c)) * tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ) := by
  rw [hshift a b]
  refine (H (b - a)).trans ?_
  have hr : zdistInf d L (a - b) = zdistInf d L (b - a) := by
    rw [← k2d_zdistInf_neg (b - a), neg_sub]
  rw [hr]
  set x := b - a with hx
  have hrρ : ((zdistInf d L x : ℕ) : ℝ) ≤ (zdistD d L x : ℝ) := by
    exact_mod_cast zdistInf_le_zdistD d L x
  have hr0 : (0 : ℝ) ≤ ((zdistInf d L x : ℕ) : ℝ) := Nat.cast_nonneg _
  have hℓ : 0 < ellT L g t := ellT_pos (by exact_mod_cast (NeZero.one_le (n := L)))
  have hB : Bparam d L g t (zdistD d L x) ≤ BparamR d L g t ((zdistInf d L x : ℕ) : ℝ) := by
    rw [← BparamR_natCast]
    exact BparamR_antitone hr0 hrρ
  have hexp : Real.exp (-c * (zdistD d L x : ℝ) / ellT L g t) ≤
      Real.exp (1 / (4 * c)) *
        Real.exp (-Real.sqrt (((zdistInf d L x : ℕ) : ℝ) / ellT L g t)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : ((zdistInf d L x : ℕ) : ℝ) / ellT L g t ≤ (zdistD d L x : ℝ) / ellT L g t :=
      div_le_div_of_nonneg_right hrρ hℓ.le
    have h2 := mul_le_mul_of_nonneg_left h1 hc.le
    have h3 := k2d_sqrt_le hc (((zdistInf d L x : ℕ) : ℝ) / ellT L g t)
      (div_nonneg hr0 hℓ.le)
    have e : -c * (zdistD d L x : ℝ) / ellT L g t = -(c * ((zdistD d L x : ℝ) / ellT L g t)) := by
      ring
    rw [e]
    linarith
  calc C₅ * Bparam d L g t (zdistD d L x) * Real.exp (-c * (zdistD d L x : ℝ) / ellT L g t)
      ≤ C₅ * BparamR d L g t ((zdistInf d L x : ℕ) : ℝ) *
          (Real.exp (1 / (4 * c)) *
            Real.exp (-Real.sqrt (((zdistInf d L x : ℕ) : ℝ) / ellT L g t))) := by
        have hBR0 : 0 ≤ BparamR d L g t ((zdistInf d L x : ℕ) : ℝ) := BparamR_nonneg hr0
        exact mul_le_mul (mul_le_mul_of_nonneg_left hB hC₅.le) hexp (Real.exp_pos _).le
          (mul_nonneg hC₅.le hBR0)
    _ = C₅ * Real.exp (1 / (4 * c)) * tailT d L g t ((zdistInf d L x : ℕ) : ℝ) := by
        unfold tailT
        ring

/-- **A polynomial against a stretched exponential**: for `c' > 0`, `k ≥ 1` there is `C_P` with
`e^{-c' r} ≤ C_P (r+1)^{-k} e^{-√r}` for all `r ≥ 0` (`√r ≤ (c'/4) r + 1/c'`, `y^k/k! ≤ e^y` at `y = c'(r+1)/(4k)`). -/
private theorem NewKLKBA_exp_poly {c' : ℝ} (hc' : 0 < c') {k : ℕ} (hk : 1 ≤ k) :
    ∃ CP : ℝ, 0 < CP ∧ ∀ r : ℝ, 0 ≤ r →
      Real.exp (-(c' * r)) ≤ CP * (((r + 1) ^ k)⁻¹ * Real.exp (-Real.sqrt r)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  refine ⟨k.factorial * (4 * k / c') ^ k * Real.exp (1 / c' + c' / 4), by positivity, ?_⟩
  intro r hr
  have hr1 : 0 < r + 1 := by linarith
  have hrk : 0 < (r + 1) ^ k := pow_pos hr1 k
  -- `√r ≤ (c'/4) r + 1/c'`
  have h1 : Real.sqrt r ≤ c' / 4 * r + 1 / c' := by
    have := k2d_sqrt_le (show 0 < c' / 4 by positivity) r hr
    have e : 1 / (4 * (c' / 4)) = 1 / c' := by field_simp
    rw [e] at this
    exact this
  -- `(r+1)^k ≤ k! (4k/c')^k e^{(c'/(4k))(r+1)}`
  have h2 : (r + 1) ^ k ≤ k.factorial * (4 * k / c') ^ k * Real.exp (c' / (4 * k) * (r + 1)) := by
    have hx : 0 ≤ c' / (4 * k) * (r + 1) := by positivity
    have h := Real.pow_div_factorial_le_exp (c' / (4 * k) * (r + 1)) hx k
    rw [div_le_iff₀ hfac, mul_pow] at h
    have e : (c' / (4 * k)) ^ k = ((4 * k / c') ^ k)⁻¹ := by
      rw [← inv_pow]; congr 1; field_simp
    rw [e] at h
    have hq : 0 < (4 * (k : ℝ) / c') ^ k := by positivity
    calc (r + 1) ^ k = (4 * k / c') ^ k * (((4 * k / c') ^ k)⁻¹ * (r + 1) ^ k) := by
          field_simp
      _ ≤ (4 * k / c') ^ k * (Real.exp (c' / (4 * k) * (r + 1)) * k.factorial) :=
          mul_le_mul_of_nonneg_left h hq.le
      _ = _ := by ring
  have h3 : c' / (4 * k) * (r + 1) ≤ c' / 4 * (r + 1) := by
    have : c' / (4 * (k : ℝ)) ≤ c' / 4 := by
      apply div_le_div_of_nonneg_left hc'.le (by norm_num)
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    exact mul_le_mul_of_nonneg_right this hr1.le
  have h4 : (r + 1) ^ k * Real.exp (Real.sqrt r) * Real.exp (-(c' * r)) ≤
      k.factorial * (4 * k / c') ^ k * Real.exp (1 / c' + c' / 4) := by
    have hq : 0 ≤ (k.factorial : ℝ) * (4 * k / c') ^ k := by positivity
    have hA : Real.exp (c' / (4 * k) * (r + 1)) ≤ Real.exp (c' / 4 * (r + 1)) := Real.exp_le_exp.2 h3
    have hB : Real.exp (Real.sqrt r) ≤ Real.exp (c' / 4 * r + 1 / c') := Real.exp_le_exp.2 h1
    have hC : 0 ≤ Real.exp (-(c' * r)) := (Real.exp_pos _).le
    have hD : 0 ≤ Real.exp (Real.sqrt r) := (Real.exp_pos _).le
    have hrk' : (r + 1) ^ k ≤ k.factorial * (4 * k / c') ^ k * Real.exp (c' / 4 * (r + 1)) :=
      h2.trans (mul_le_mul_of_nonneg_left hA hq)
    calc (r + 1) ^ k * Real.exp (Real.sqrt r) * Real.exp (-(c' * r))
        ≤ (k.factorial * (4 * k / c') ^ k * Real.exp (c' / 4 * (r + 1))) *
            Real.exp (c' / 4 * r + 1 / c') * Real.exp (-(c' * r)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hrk' hB hD (by positivity)) hC
      _ = k.factorial * (4 * k / c') ^ k *
            Real.exp (c' / 4 * (r + 1) + (c' / 4 * r + 1 / c') + -(c' * r)) := by
          simp only [Real.exp_add]; ring
      _ ≤ k.factorial * (4 * k / c') ^ k * Real.exp (1 / c' + c' / 4) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [mul_nonneg hc'.le hr])) hq
  -- conclude
  have hE : 0 < Real.exp (Real.sqrt r) := Real.exp_pos _
  have e1 : Real.exp (-Real.sqrt r) = (Real.exp (Real.sqrt r))⁻¹ := Real.exp_neg _
  rw [e1]
  rw [show k.factorial * (4 * k / c') ^ k * Real.exp (1 / c' + c' / 4) *
      (((r + 1) ^ k)⁻¹ * (Real.exp (Real.sqrt r))⁻¹) =
      (k.factorial * (4 * k / c') ^ k * Real.exp (1 / c' + c' / 4)) /
        ((r + 1) ^ k * Real.exp (Real.sqrt r)) by field_simp]
  rw [le_div_iff₀ (by positivity)]
  calc Real.exp (-(c' * r)) * ((r + 1) ^ k * Real.exp (Real.sqrt r))
      = (r + 1) ^ k * Real.exp (Real.sqrt r) * Real.exp (-(c' * r)) := by ring
    _ ≤ _ := h4

/-- `ℓ_u ≤ 2Λ + 1` for `0 ≤ u ≤ 1/2`, `0 < g ≤ Λ` (`g/√(1-u) ≤ 2g` since `√(1-u) ≥ 1/2`). -/
private theorem NewKLKBA_ellT_le {L : ℕ} {g Λ u : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) (hu1 : u ≤ 1 / 2) :
    ellT L g u ≤ 2 * Λ + 1 := by
  have h1 : (1 / 2 : ℝ) ≤ Real.sqrt |1 - u| := by
    rw [Real.le_sqrt' (by norm_num)]
    rw [abs_of_pos (by linarith)]
    nlinarith
  have h2 : g / Real.sqrt |1 - u| ≤ 2 * Λ := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  unfold ellT
  refine (min_le_left _ _).trans (max_le ?_ ?_)
  · linarith
  · have : (0 : ℝ) ≤ Λ := hg.le.trans hgΛ
    linarith

/-- **The tail of the BA drift kernel** (the heart of F7): for `3 ≤ d`, `Λ, κ > 0` there is `Q₀` (in `(d, Λ, κ)` only) with
`‖(Θ_u M^{(σσ')})(a,b)‖ ≤ Q₀ 𝒯_u(|a-b|_∞)` for every `0 ≤ u < 1`, `0 < g ≤ Λ`, `L ≥ 3`, `BAReal d L g κ E m`, both charge pairs.
`u ≥ 1/2`: `Θ M = (Θ - 1)/u` (resolvent identity), `‖Θ_{ab}‖ ≤ C₁ 𝒯_u` (`baProp5_holds`, shift), `1 ≤ (Λ²+1) 𝒯_u(0)`.
`u < 1/2`: the third conjunct of `baComp_holds`, `ℓ_u ≤ 2Λ+1`, `|a-b|_∞ ≤ |a-b|₁`, and `e^{-c r} ≤ C_P (r+1)^{-(d-2)} e^{-√r}`. -/
private theorem NewKLKBA_tail (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
      haveI : NeZero L := ⟨by omega⟩
      BAReal d L g κ E m → ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ σ₁ σ₂ : Bool, ∀ a b : Zd d L,
        ‖(BATheta d L g E m u σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a b‖ ≤
          Q₀ * tailT d L g u ((zdistInf d L (a - b) : ℕ) : ℝ) := by
  obtain ⟨C₅, hC₅, c₅, hc₅, H5⟩ := baProp5_holds d Λ κ hd hΛ hκ
  obtain ⟨CQ, hCQ, cQ, hcQ, HQ⟩ := baComp_holds d Λ κ hd hΛ hκ
  have hℓs : 0 < 2 * Λ + 1 := by linarith
  obtain ⟨CP, hCP, hP⟩ := NewKLKBA_exp_poly (c' := cQ / (2 * Λ + 1)) (by positivity) (k := d - 2) (by omega)
  have hC₁ : 0 < C₅ * Real.exp (1 / (4 * c₅)) := by positivity
  have hΛ1 : 0 < Λ ^ 2 + 1 := by positivity
  refine ⟨max (2 * (C₅ * Real.exp (1 / (4 * c₅))) + 2 * (Λ ^ 2 + 1)) (2 * CQ * CP * (Λ ^ 2 + 1)),
    lt_max_of_lt_left (by positivity), ?_⟩
  intro L hL g hg hgΛ E m hr u hu0 hu1 σ₁ σ₂ a b
  have : NeZero L := ⟨by omega⟩
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (by omega : 1 ≤ L)
  set r : ℝ := ((zdistInf d L (a - b) : ℕ) : ℝ) with hr_def
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  have hℓ1 : 1 ≤ ellT L g u := one_le_ellT hL1
  have hℓ0 : 0 < ellT L g u := lt_of_lt_of_le one_pos hℓ1
  -- the lower bound `𝒯_u(r) ≥ (Λ²+1)⁻¹ (r+1)^{-(d-2)} e^{-√r}`
  have hgl : g ^ 2 + |1 - u| ≤ Λ ^ 2 + 1 := by
    rw [abs_of_pos (by linarith)]
    nlinarith
  have hT : (Λ ^ 2 + 1)⁻¹ * (((r + 1) ^ (d - 2))⁻¹ * Real.exp (-Real.sqrt r)) ≤ tailT d L g u r := by
    unfold tailT BparamR
    have h1 : (Λ ^ 2 + 1)⁻¹ ≤ (g ^ 2 + |1 - u|)⁻¹ :=
      inv_anti₀ (by rw [abs_of_pos (by linarith)]; nlinarith) hgl
    have h2 : Real.exp (-Real.sqrt r) ≤ Real.exp (-Real.sqrt (r / ellT L g u)) := by
      refine Real.exp_le_exp.2 (neg_le_neg (Real.sqrt_le_sqrt ?_))
      exact div_le_self hr0 hℓ1
    have h3 : 0 ≤ ((r + 1) ^ (d - 2))⁻¹ := inv_nonneg.2 (pow_nonneg (by linarith) _)
    have h4 : 0 ≤ ((L : ℝ) ^ d * |1 - u|)⁻¹ := inv_nonneg.2 (by positivity)
    calc (Λ ^ 2 + 1)⁻¹ * (((r + 1) ^ (d - 2))⁻¹ * Real.exp (-Real.sqrt r))
        ≤ ((g ^ 2 + |1 - u|)⁻¹ * ((r + 1) ^ (d - 2))⁻¹) * Real.exp (-Real.sqrt (r / ellT L g u)) := by
          rw [← mul_assoc]
          exact mul_le_mul (mul_le_mul_of_nonneg_right h1 h3) h2 (Real.exp_pos _).le
            (mul_nonneg (inv_nonneg.2 (by positivity)) h3)
      _ ≤ _ := by
          have := mul_nonneg h4 (Real.exp_pos (-Real.sqrt (r / ellT L g u))).le
          nlinarith
  have hT0 : 0 ≤ tailT d L g u r := tailT_nonneg hr0
  by_cases hu : 1 / 2 ≤ u
  · -- `u ≥ 1/2`: through the resolvent identity
    have hres := (BATheta_resolvent d L g κ E m hr u hu0 hu1 σ₁ σ₂).2
    set Th := BATheta d L g E m u σ₁ σ₂ with hTh
    set Q := BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ with hQ
    have hΘ : ∀ x y : Zd d L, ‖Th x y‖ ≤
        (C₅ * Real.exp (1 / (4 * c₅))) * tailT d L g u ((zdistInf d L (x - y) : ℕ) : ℝ) :=
      fun x y => NewKLKBA_theta_tail hC₅ hc₅ (EMn2BA_theta_shift g E m u σ₁ σ₂)
        (fun z => H5 L hL g hg hgΛ E m hr u hu0 hu1 σ₁ σ₂ z) x y
    have hentry : (u : ℂ) * (Th * Q) a b = Th a b - (1 : Matrix (Zd d L) (Zd d L) ℂ) a b := by
      have := congrFun (congrFun hres a) b
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at this
      rw [this]; ring
    have hnorm : u * ‖(Th * Q) a b‖ ≤ ‖Th a b‖ + (if a = b then 1 else 0) := by
      have h1 := congrArg norm hentry
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0] at h1
      rw [h1]
      refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
      rw [Matrix.one_apply]
      split_ifs <;> simp
    have hind : (if a = b then (1 : ℝ) else 0) ≤ (Λ ^ 2 + 1) * tailT d L g u r := by
      by_cases hab : a = b
      · subst hab
        have h0 : r = 0 := by simp [hr_def, zdistInf, zdist_zero]
        rw [h0] at hT
        simp only [zero_add, one_pow, inv_one, Real.sqrt_zero, neg_zero, Real.exp_zero,
          mul_one] at hT
        rw [h0] at hT0 ⊢
        simp only [ite_true]
        have := mul_le_mul_of_nonneg_left hT hΛ1.le
        rw [mul_inv_cancel₀ hΛ1.ne'] at this
        exact this
      · simp only [hab, ite_false]; positivity
    have hu0' : 0 < u := by linarith
    have hmain : ‖(Th * Q) a b‖ ≤ 2 * ‖Th a b‖ + 2 * (if a = b then (1 : ℝ) else 0) := by
      have : ‖(Th * Q) a b‖ * (1 / 2) ≤ ‖(Th * Q) a b‖ * u :=
        mul_le_mul_of_nonneg_left hu (norm_nonneg _)
      have h5 : (0 : ℝ) ≤ (if a = b then (1 : ℝ) else 0) := by split_ifs <;> norm_num
      nlinarith [norm_nonneg (Th a b), norm_nonneg ((Th * Q) a b)]
    calc ‖(Th * Q) a b‖ ≤ 2 * ‖Th a b‖ + 2 * (if a = b then (1 : ℝ) else 0) := hmain
      _ ≤ 2 * ((C₅ * Real.exp (1 / (4 * c₅))) * tailT d L g u r) + 2 * ((Λ ^ 2 + 1) * tailT d L g u r) := by
          have := hΘ a b
          gcongr
      _ = (2 * (C₅ * Real.exp (1 / (4 * c₅))) + 2 * (Λ ^ 2 + 1)) * tailT d L g u r := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hT0
  · -- `u < 1/2`: `baComp_holds`
    have hu2 : u < 1 / 2 := not_le.1 hu
    obtain ⟨-, -, H3⟩ := HQ L hL g hg hgΛ E m hr u hu0 hu1 σ₁ σ₂
    have h3 := H3 a b
    have hinv : (1 - u)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    have hℓ : ellT L g u ≤ 2 * Λ + 1 := NewKLKBA_ellT_le hg hgΛ hu2.le
    have hρ : r ≤ (zdistD d L (a - b) : ℝ) := by
      rw [hr_def]
      exact_mod_cast zdistInf_le_zdistD d L (a - b)
    have hexp : Real.exp (-cQ * (zdistD d L (a - b) : ℝ) / ellT L g u) ≤
        Real.exp (-(cQ / (2 * Λ + 1) * r)) := by
      refine Real.exp_le_exp.2 ?_
      have h1 : cQ * r / (2 * Λ + 1) ≤ cQ * (zdistD d L (a - b) : ℝ) / (2 * Λ + 1) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hρ hcQ.le) hℓs.le
      have h2 : cQ * (zdistD d L (a - b) : ℝ) / (2 * Λ + 1) ≤ cQ * (zdistD d L (a - b) : ℝ) / ellT L g u :=
        div_le_div_of_nonneg_left (by positivity) hℓ0 hℓ
      have e1 : -cQ * (zdistD d L (a - b) : ℝ) / ellT L g u = -(cQ * (zdistD d L (a - b) : ℝ) / ellT L g u) := by
        ring
      have e2 : cQ / (2 * Λ + 1) * r = cQ * r / (2 * Λ + 1) := by ring
      rw [e1, e2]
      linarith
    have hpoly := hP r hr0
    calc ‖(BATheta d L g E m u σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a b‖
        ≤ CQ * (1 - u)⁻¹ * Real.exp (-cQ * (zdistD d L (a - b) : ℝ) / ellT L g u) := h3
      _ ≤ CQ * 2 * (CP * (((r + 1) ^ (d - 2))⁻¹ * Real.exp (-Real.sqrt r))) := by
          have h4 : CQ * (1 - u)⁻¹ ≤ CQ * 2 := mul_le_mul_of_nonneg_left hinv hCQ.le
          exact mul_le_mul h4 (hexp.trans hpoly) (Real.exp_pos _).le (by positivity)
      _ = (2 * CQ * CP * (Λ ^ 2 + 1)) * ((Λ ^ 2 + 1)⁻¹ * (((r + 1) ^ (d - 2))⁻¹ * Real.exp (-Real.sqrt r))) := by
          field_simp
      _ ≤ (2 * CQ * CP * (Λ ^ 2 + 1)) * tailT d L g u r :=
          mul_le_mul_of_nonneg_left hT (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hT0

end Tail

/-! ## 3. The facts F5-F9 at the BA family -/

section Facts

variable {d : ℕ}

/-- The premise `κ ≤ Im m` of the primed pins is `BAReal` at the datum `(L_n, g_n, E, m)` of the family (`baStep2Fam_m`). -/
private theorem NewKLKBA_real {κ : ℝ} (hκ : 0 < κ) (sz : Sizes d) (n : ℕ) (E : ℝ)
    (hIm : κ ≤ ((baStep2Fam sz (fun _ => E)).m n).im) :
    BAReal d (sz.L n) (sz.lam n) κ E (BAm d (sz.L n) (sz.lam n) (E : ℂ)) :=
  ⟨BAm_self_of_im_pos (lt_of_lt_of_le hκ hIm), hIm⟩

/-- `Im (E + m) ≠ 0` (the hypothesis of `Step2Kern_thetaKer_BA`) from `κ ≤ Im m`. -/
private theorem NewKLKBA_hIm {κ : ℝ} (hκ : 0 < κ) (sz : Sizes d) (n : ℕ) (E : ℝ)
    (hIm : κ ≤ ((baStep2Fam sz (fun _ => E)).m n).im) :
    ((((fun _ : ℕ => E) n : ℝ) : ℂ) + BAmF sz sz.lam (fun _ => E) n).im ≠ 0 := by
  have : 0 < ((baStep2Fam sz (fun _ => E)).m n).im := lt_of_lt_of_le hκ hIm
  change 0 < (BAm d (sz.L n) (sz.lam n) (E : ℂ)).im at this
  change ((E : ℂ) + BAm d (sz.L n) (sz.lam n) (E : ℂ)).im ≠ 0
  simpa using this.ne'

/-- **`𝒦^{(2)}` at BA** (`(Kn2sol)` of `baKsolve`, uniqueness `baK_unique`): `𝒦^{(2)}_{u,σ,a} = W^{-d} (Θ_u M^{(σ₀σ₁)})(a₀, a₁)`
(`BAKloop = BAKsol`, `baKsolve` has the `(Kn2sol)` clause; the loop `KLloopOf σ a` is well formed of length `2`). -/
private theorem NewKLKBA_K_two {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) (sz : Sizes d) (n : ℕ) (E : ℝ)
    (hlam : 0 < sz.lam n) (hlamΛ : sz.lam n ≤ Λ) (hIm : κ ≤ ((baStep2Fam sz (fun _ => E)).m n).im)
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    (baStep2Fam sz (fun _ => E)).K n u σ a =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
        (BATheta d (sz.L n) (sz.lam n) E (BAm d (sz.L n) (sz.lam n) (E : ℂ)) u (σ 0) (σ 1) *
          BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) (E : ℂ) (BAm d (sz.L n) (sz.lam n) (E : ℂ))) (σ 0) (σ 1))
          (a 0) (a 1) := by
  have hr := NewKLKBA_real hκ sz n E hIm
  have hL : 3 ≤ sz.L n := sz.three_le_L n
  obtain ⟨K, hK, hK2⟩ := baKsolve d Λ κ hΛ hκ (sz.L n) hL (sz.W n) (sz.lam n) hlam hlamΛ E _ hr
  have hu : u ∈ Set.Ico (0 : ℝ) 1 := ⟨hu0, hu1⟩
  have heq := baK_unique _ _ (BAKsol_isKLoopS (baKsolve d) hΛ hκ hL hlam hlamΛ hr (W := sz.W n)) hK u hu
    (KLloopOf d (sz.L n) σ a) (by simp [LoopIdx.WF, KLloopOf])
    (by simp only [LoopIdx.length, KLloopOf, List.length_ofFn]; exact le_rfl)
  have hKL : KLloopOf d (sz.L n) σ a = ⟨[σ 0, σ 1], [a 0, a 1]⟩ := by
    simp [KLloopOf, List.ofFn_succ]
  have h1 : (baStep2Fam sz (fun _ => E)).K n u σ a = K u (KLloopOf d (sz.L n) σ a) := heq
  rw [h1, hKL]
  exact hK2 u hu (σ 0, σ 1) (a 0) (a 1)

/-- **Target 1 (`lem:newKLK` over the BA carrier, F5-F9)**: for `3 ≤ d`, `κ, 𝔡 > 0` the facts `NewKLKGenHyp` hold at the block Anderson
family `fun sz E => baStep2Fam sz E` (`S = 1`, `m = BAmF`, `M = BAMfine`), with `K_c = Q₀ C_T + C_s`, `C_K = 1`, constants in
`(d, κ, 𝔡)` only; the domain is `0 < lam ≤ 𝔡⁻¹`, `κ ≤ Im m` (no smallness of `g`, no scalar `m`).
* F5: `S = 1`; F6: `|m| ≤ 1` (`BAm_norm_le_one`);
* F7 (BAT-F1): the real `Θ_BA`-convolution: `thetaKer = Θ_BA M^{(σσ')}` (`Step2Kern_thetaKer_BA`), tail `NewKLKBA_tail`, row sum
  `baComp_row_le`, `(TTT2)` of `ekPropTInf_holds`, and `NewKLKBA_conv_P`;
* F8: `𝒦^{(2)} = W^{-d} Θ M` (`NewKLKBA_K_two`) and `baComp_col_le`, `baComp_row_le`;
* F9: `LM` is `loopFine` at `ztOf`, `Im ζ = (1-u) Im m`, and `M_{xx} = m` (`BAMB_diag_eq`). -/
theorem baNewKLKGenHyp (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) :
    NewKLKGenHyp d κ 𝔡 (fun sz E => baStep2Fam sz E) := by
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  obtain ⟨Q₀, hQ₀, HQ⟩ := NewKLKBA_tail d hd 𝔡⁻¹ κ hΛ hκ
  obtain ⟨CT, hCT, HT⟩ := ekPropTInf_holds d hd
  have hCs := nkl_Cs_ge_one (d := d)
  set Cs : ℝ := 2 ^ (d - 2) * Real.exp 1 with hCsdef
  have hCs0 : 0 < Cs := by linarith
  unfold NewKLKGenHyp
  refine ⟨Q₀ * CT + Cs, 1, by positivity, zero_le_one, ?_, ?_, ?_, ?_, ?_⟩
  · -- F5
    intro sz n E hlam hlam' hIm
    refine ⟨fun x y h => ?_, fun x => ?_, fun x y => ?_⟩
    · change (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) x y ≠ 0 at h
      rw [Matrix.one_apply] at h
      by_cases hxy : x = y
      · subst hxy
        simp [zdistInf]
      · simp [hxy] at h
    · change ∑ y, ‖(1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) x y‖ ≤ 1
      have h1 : ∀ y, ‖(1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) x y‖ = if x = y then (1 : ℝ) else 0 := fun y => by
        rw [Matrix.one_apply]; split_ifs <;> simp
      simp only [h1, Finset.sum_ite_eq, Finset.mem_univ, ite_true, le_refl]
    · change ‖(1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) x y‖ = ‖(1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) y x‖
      simp [Matrix.one_apply, eq_comm]
  · -- F6
    intro sz n E hlam hlam' hIm
    have hr := NewKLKBA_real hκ sz n E hIm
    exact BAm_norm_le_one d (sz.L n) (sz.lam n) (E : ℂ) _ (by simp) hr.1
  · -- F7
    intro sz n E u hlam hlam' hIm hu0 hu1 s s' ℓ' D' hℓ' hD' a a'
    have hr := NewKLKBA_real hκ sz n E hIm
    have hL : 3 ≤ sz.L n := sz.three_le_L n
    have hv : 0 < 1 - u := by linarith
    have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
    have hker : ∀ x y : Zd d (sz.L n),
        Step2Gen_thetaKer (baStep2Fam sz (fun _ => E)).toFlowFM n s s' u x y =
          (BATheta d (sz.L n) (sz.lam n) E (BAm d (sz.L n) (sz.lam n) (E : ℂ)) u s s' *
            BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) (E : ℂ) (BAm d (sz.L n) (sz.lam n) (E : ℂ))) s s') x y :=
      fun x y => congrFun (congrFun (Step2Kern_thetaKer_BA sz sz.lam (fun _ => E) n
        (NewKLKBA_hIm hκ sz n E hIm) s s' u) x) y
    have hconv := NewKLKBA_conv_P (d := d) (L := sz.L n) (g := sz.lam n) (t := u) (ℓ := ℓ')
      (W := ((sz.W n : ℕ) : ℝ)) (D := D') hWpos hℓ'
      (X := BATheta d (sz.L n) (sz.lam n) E (BAm d (sz.L n) (sz.lam n) (E : ℂ)) u s s' *
        BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) (E : ℂ) (BAm d (sz.L n) (sz.lam n) (E : ℂ))) s s')
      (Q := Q₀) (CT := CT / (1 - u)) (c := (1 - u)⁻¹) hQ₀.le (by positivity)
      (fun x y => HQ (sz.L n) hL (sz.lam n) hlam hlam' E _ hr u hu0 hu1 s s' x y)
      (fun x => baComp_row_le hr hu0 hu1 s s' x)
      (fun x y => HT (sz.L n) (sz.lam n) u u hlam hu0 le_rfl hu1 (le_total _ _) x y) a a'
    have e : Q₀ * (CT / (1 - u)) + Cs * (1 - u)⁻¹ = (Q₀ * CT + Cs) / (1 - u) := by
      field_simp
    rw [e] at hconv
    simp only [hker]
    exact hconv
  · -- F8
    intro sz n E u hlam hlam' hIm hu0 hu1 σ
    have hr := NewKLKBA_real hκ sz n E hIm
    have hv : 0 < 1 - u := by linarith
    have hW0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
    have hK : ∀ a : Fin 2 → Zd d (sz.L n), ‖(baStep2Fam sz (fun _ => E)).K n u σ a‖ =
        (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
          ‖(BATheta d (sz.L n) (sz.lam n) E (BAm d (sz.L n) (sz.lam n) (E : ℂ)) u (σ 0) (σ 1) *
            BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) (E : ℂ) (BAm d (sz.L n) (sz.lam n) (E : ℂ))) (σ 0) (σ 1))
            (a 0) (a 1)‖ := by
      intro a
      rw [NewKLKBA_K_two hΛ hκ sz n E hlam hlam' hIm u hu0 hu1 σ a, norm_mul, norm_inv, norm_pow,
        Complex.norm_natCast]
    refine ⟨fun a₁ => ?_, fun a₀ => ?_⟩
    · have h := baComp_col_le hr hu0 hu1 (σ 0) (σ 1) a₁
      calc ∑ x, ‖(baStep2Fam sz (fun _ => E)).K n u σ ![x, a₁]‖
          = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ∑ x, ‖(BATheta d (sz.L n) (sz.lam n) E
              (BAm d (sz.L n) (sz.lam n) (E : ℂ)) u (σ 0) (σ 1) *
              BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) (E : ℂ) (BAm d (sz.L n) (sz.lam n) (E : ℂ)))
                (σ 0) (σ 1)) x a₁‖ := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [hK]
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 - u)⁻¹ := mul_le_mul_of_nonneg_left h hW0
        _ = 1 * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 - u)⁻¹) := (one_mul _).symm
    · have h := baComp_row_le hr hu0 hu1 (σ 0) (σ 1) a₀
      calc ∑ y, ‖(baStep2Fam sz (fun _ => E)).K n u σ ![a₀, y]‖
          = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ∑ y, ‖(BATheta d (sz.L n) (sz.lam n) E
              (BAm d (sz.L n) (sz.lam n) (E : ℂ)) u (σ 0) (σ 1) *
              BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) (E : ℂ) (BAm d (sz.L n) (sz.lam n) (E : ℂ)))
                (σ 0) (σ 1)) a₀ y‖ := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [hK]
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 - u)⁻¹ := mul_le_mul_of_nonneg_left h hW0
        _ = 1 * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 - u)⁻¹) := (one_mul _).symm
  · -- F9
    intro sz n E u hlam hlam' hIm hu0 hu1
    have hr := NewKLKBA_real hκ sz n E hIm
    refine ⟨ztOf (BAmF sz sz.lam (fun _ => E) n) E u, ztOf_im _ _ _, fun H σ a => rfl, fun H x => ?_⟩
    have hM : BAMfine sz sz.lam (fun _ => E) n x x = BAmF sz sz.lam (fun _ => E) n := by
      rw [BAMfine_eq sz sz.lam (fun _ => E) n hr.1.1 x x]
      simp only [ite_true]
      exact BAMB_diag_eq d (sz.L n) (sz.lam n) (E : ℂ) _ hr.1 _
    change Gres H (ztOf (BAmF sz sz.lam (fun _ => E) n) E u) true x x - BAMfine sz sz.lam (fun _ => E) n x x = _
    rw [hM]
    rfl

end Facts

end RBM.BA
