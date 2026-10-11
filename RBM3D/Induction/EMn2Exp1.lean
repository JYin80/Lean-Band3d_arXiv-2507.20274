/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.EMn2Poly
import RBM3D.Induction.Step2Iterate
import RBM3D.Path.KellStar

/-!
# ST2-10 (ticket T2109): `lem: EMn2_N`, third estimate `(eq:MG_conclusion3)`, part 1

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): the lemma `3_5:427-444`
(`(eq:MG_conclusion3)` `3_5:438`), its proof `3_5:829-888`, the cutoff scales
`(eq:cutoff_scales)` `3_5:829-831`, the near case `3_5:833-838`, `(eq:largea-b)` `3_5:840`, the
split `(eq;S123)` `3_5:842-845`, `(eq:pointwise_loop2)` `3_5:847-852`, `(eq_S1tilde)`
`3_5:853-856`, `(eq:boundwtS_1)` `3_5:859-863`; the contraction inequality `(eq_sym_loop_bound)`,
`(eq_sym_loop_bound2)` `3_5:754`, `3_5:758`.

The pin `STEMn2Exp` (`RBM3D/Induction/Step2Defs.lean:456`) is **not** proved here: it needs the
far-case sum `S̃₃` (`3_5:871-888`, ST2-11).  This file proves everything else, in namespace
`RBM.Gauss.Sizes`:

* **the cutoff scales and the profile comparisons** (§2, §9): `emn2ExpEllStar`
  (`ℓ*_t = (log W)^{3/2} ℓ_t`, the scale written inline in `KellStarEv`; the far field of
  `kellStarEv` restated with it is `emn2Exp_kellStar_far`), `emn2ExpEllDag`
  (`ℓ†_t = (log W)^{7/4} ℓ_t`), the profile `emn2ExpPf = W^{-d} 𝒯̃^ℓ_{t,D}` (`STprof` at a real
  argument), `𝒯̃(|b - c'|) ≤ K_n 𝒯̃(|a - b|)` in the two cases of `3_5:851-853`
  (`emn2Exp_profile_shift`, `emn2Exp_profile_cmp`, `K_n = 2^{d-2} exp(2 (log W)^{3/4}) = N^{o(1)}`),
  and `Ψ_t(r)² ≍ W^{-d} 𝒯̃(r)` for `r ≤ ℓ†_t` (`emn2Exp_trunc_cmp`);
* **the near case** `|a - b| ≤ ℓ†_t` (§6, `emn2Exp_near`): `stEMn2Poly_holds`
  (`(eq:MG_conclusion)`) at the truncated profile `emn2ExpPsi`
  (`Ψ'_n(r) = min(√(W^{-d}(B_{t,r∧ℓ⁺} + W^{-D})), W^{-ε'})`), which is in `STPsiClass`, satisfies
  `STLWassm` and `STInitialGT2` from `STLWassmExp` and `STInitialGT2.1`, and obeys
  `Ψ'(r)² ≤ 2 exp((log W)^{7/8}) W^{-d} 𝒯̃(r)` for `r ≤ ℓ†_t`;
* **the far case** `|a - b| > ℓ†_t` (§3, §4, §7, §8): the three region sums `emn2ExpS1`,
  `emn2ExpS2`, `emn2ExpS3` of `(eq;S123)`, the cover `emn2Exp_cover` / `emn2Exp_EEk_cover` /
  `emn2Exp_EEk_split` (`|(𝓔⊗𝓔)^{M,(2;k)}| ≤ S̃₁ + S̃₂ + S̃₃`), the deterministic bound
  `emn2Exp_S12_le` (`S̃₁ + S̃₂ ≤ 2 · 3^d η⁻¹ K y⁵ √P(0) P(|a-b|)²`, from the contraction
  inequality `stContractPt_holds`, its partner `emn2Poly_contractPt_partner` and the 3-loop and
  4-loop bounds `emn2Poly_norm_loop3_le`, `emn2Poly_norm_loop4_alt_le` of T2102: **no entry
  bound `(GijGEX)` is used**) and its stochastic form `emn2Exp_far12`:
  `(S̃₁ + S̃₂) 1_{|a-b| > ℓ†_t} ≺ η⁻¹ (W^{-d} B_{t,0})^{1/2} (W^{-d} 𝒯̃)²` (no random control `Ĵ`);
* **the assembly** (§10): `emn2Exp_of_far3`, the body of `STEMn2Exp` from the bound of `S̃₃` on the
  far pairs (conditional, so not stated with the head `STEMn2Exp`).

For ST2-11: `S̃₃` is `emn2ExpS3M` (the `3_5:871-888` region `ℓ* < |c'-b| ≤ ℓ`,
`ℓ* < |c-a| ≤ ℓ`, the complement of `R₁ ∪ R₂`); the hypothesis `h3` of `emn2Exp_of_far3` is the
only remaining input.  The statements `emn2Exp_near`, `emn2Exp_far12` have the premises of the pin
word for word; the premises `Ψ` and its window are not used by either, `STInitialGT2` only by
`emn2Exp_near` (its first part), and the upper bound on `ℓ` by neither.

Differences from the paper's proof (paper-delta candidates in the ticket report): the 4-loop and
the 3-loop are bounded by 2-loops by block Cauchy-Schwarz (T2102), not by entry bounds; the near
case uses the truncated profile with the added `W^{-D}` and the cap `W^{-ε'}` (so that
`STPsiClass` and `STLWassm` hold for every `n`); the gap `ℓ†_t/2 ≥ ℓ*_t + 1` used in
`3_5:851-852` ("`(1 - o(1)) |a - b|`") is the hypothesis `2 (ℓ*_t + 1) ≤ ℓ†_t`, true when
`(log W)^{1/4} ≥ 4` (`emn2Exp_scale_gap`).
-/

set_option linter.style.longLine false

noncomputable section

open Matrix Finset Filter MeasureTheory

namespace RBM.Gauss.Sizes

open RBM RBM.Gauss RBM.Loop RBM.Path
open RBM.BA (FlowFM PrecL STEEg STInitialGT2gL STLWassmgL STLWassmExpgL)

/-! ## 1. The profile `𝒯_t`, `B_{t,ρ}`: ratios and shifts -/

section Profile

variable {d L : ℕ} {g t : ℝ}

/-- `𝒯_t(ρ) ≤ B_{t,ρ}` for `ρ ≥ 0`. -/
private lemma emn2Exp_tailT_le_bparamR {ρ : ℝ} (hρ : 0 ≤ ρ) :
    tailT d L g t ρ ≤ BparamR d L g t ρ := by
  unfold tailT
  have hB := BparamR_nonneg (d := d) (L := L) (g := g) (t := t) hρ
  have h1 : Real.exp (-Real.sqrt (ρ / ellT L g t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; exact neg_nonpos.mpr (Real.sqrt_nonneg _)
  nlinarith

/-- `B_{t,ρ} ≤ exp(√X) 𝒯_t(ρ)` for `0 ≤ ρ ≤ X ℓ_t`: the exponential factor of `𝒯_t`
is at least `exp(-√X)` on that range (`3_5:833-836`). -/
private lemma emn2Exp_bparamR_le_exp_tailT (hL : 1 ≤ (L : ℝ)) {ρ X : ℝ} (hρ : 0 ≤ ρ)
    (hX : ρ ≤ X * ellT L g t) :
    BparamR d L g t ρ ≤ Real.exp (Real.sqrt X) * tailT d L g t ρ := by
  have hℓ : 0 < ellT L g t := ellT_pos hL
  have h1 : ρ / ellT L g t ≤ X := (div_le_iff₀ hℓ).mpr hX
  have h2 : Real.sqrt (ρ / ellT L g t) ≤ Real.sqrt X := Real.sqrt_le_sqrt h1
  have hB := BparamR_nonneg (d := d) (L := L) (g := g) (t := t) hρ
  unfold tailT
  have h3 : 1 ≤ Real.exp (Real.sqrt X) * Real.exp (-Real.sqrt (ρ / ellT L g t)) := by
    rw [← Real.exp_add]; apply Real.one_le_exp; linarith
  nlinarith

/-- **The ratio of `B`**: `B_{t,x} ≤ q^{d-2} B_{t,y}` for `0 ≤ x ≤ y` and `y + 1 ≤ q (x + 1)`. -/
private lemma emn2Exp_bparamR_ratio {x y q : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hq : 1 ≤ q)
    (hyq : y + 1 ≤ q * (x + 1)) :
    BparamR d L g t x ≤ q ^ (d - 2) * BparamR d L g t y := by
  unfold BparamR
  have hA0 : 0 ≤ (g ^ 2 + |1 - t|)⁻¹ := inv_nonneg.mpr (by positivity)
  have hZ0 : 0 ≤ ((L : ℝ) ^ d * |1 - t|)⁻¹ := inv_nonneg.mpr (by positivity)
  have hqm : 1 ≤ q ^ (d - 2) := one_le_pow₀ hq
  have hx1 : 0 < (x + 1) ^ (d - 2) := pow_pos (by linarith) _
  have hy1 : 0 < (y + 1) ^ (d - 2) := pow_pos (by linarith) _
  have hpow : (y + 1) ^ (d - 2) ≤ q ^ (d - 2) * (x + 1) ^ (d - 2) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) hyq _
  have hinv : ((x + 1) ^ (d - 2))⁻¹ ≤ q ^ (d - 2) * ((y + 1) ^ (d - 2))⁻¹ := by
    calc ((x + 1) ^ (d - 2))⁻¹
        = (y + 1) ^ (d - 2) * ((x + 1) ^ (d - 2))⁻¹ * ((y + 1) ^ (d - 2))⁻¹ := by
          field_simp
      _ ≤ (q ^ (d - 2) * (x + 1) ^ (d - 2)) * ((x + 1) ^ (d - 2))⁻¹ * ((y + 1) ^ (d - 2))⁻¹ := by
          gcongr
      _ = q ^ (d - 2) * ((y + 1) ^ (d - 2))⁻¹ := by field_simp
  calc (g ^ 2 + |1 - t|)⁻¹ * ((x + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * |1 - t|)⁻¹
      ≤ (g ^ 2 + |1 - t|)⁻¹ * (q ^ (d - 2) * ((y + 1) ^ (d - 2))⁻¹) +
          q ^ (d - 2) * ((L : ℝ) ^ d * |1 - t|)⁻¹ := by
        gcongr
        nlinarith
    _ = q ^ (d - 2) * ((g ^ 2 + |1 - t|)⁻¹ * ((y + 1) ^ (d - 2))⁻¹ +
          ((L : ℝ) ^ d * |1 - t|)⁻¹) := by ring

/-- `√(a + b) ≤ √a + √b`. -/
private lemma emn2Exp_sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  nlinarith [mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- **The shift of `𝒯_t`**: for `0 ≤ x ≤ y ≤ x + s` and `s ≤ x + 1`,
`𝒯_t(x) ≤ 2^{d-2} exp(√(s/ℓ_t)) 𝒯_t(y)` (`3_5:851-853`, case (2)). -/
private lemma emn2Exp_tailT_shift (hL : 1 ≤ (L : ℝ)) {x y s : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hys : y ≤ x + s) (hs : 0 ≤ s) (hsx : s ≤ x + 1) :
    tailT d L g t x ≤ 2 ^ (d - 2) * Real.exp (Real.sqrt (s / ellT L g t)) * tailT d L g t y := by
  have hℓ : 0 < ellT L g t := ellT_pos hL
  have hBr := emn2Exp_bparamR_ratio (d := d) (L := L) (g := g) (t := t) hx hxy (q := 2)
    (by norm_num) (by linarith)
  have hsub : Real.sqrt (y / ellT L g t) ≤
      Real.sqrt (x / ellT L g t) + Real.sqrt (s / ellT L g t) := by
    refine le_trans (Real.sqrt_le_sqrt ?_) (emn2Exp_sqrt_add_le (by positivity) (by positivity))
    rw [← add_div]
    exact div_le_div_of_nonneg_right hys hℓ.le
  have hexp : Real.exp (-Real.sqrt (x / ellT L g t)) ≤
      Real.exp (Real.sqrt (s / ellT L g t)) * Real.exp (-Real.sqrt (y / ellT L g t)) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
  have hBy := BparamR_nonneg (d := d) (L := L) (g := g) (t := t) (hx.trans hxy)
  have hBx := BparamR_nonneg (d := d) (L := L) (g := g) (t := t) hx
  unfold tailT
  calc BparamR d L g t x * Real.exp (-Real.sqrt (x / ellT L g t))
      ≤ (2 ^ (d - 2) * BparamR d L g t y) *
          (Real.exp (Real.sqrt (s / ellT L g t)) * Real.exp (-Real.sqrt (y / ellT L g t))) := by
        apply mul_le_mul hBr hexp (Real.exp_pos _).le (by positivity)
    _ = 2 ^ (d - 2) * Real.exp (Real.sqrt (s / ellT L g t)) *
          (BparamR d L g t y * Real.exp (-Real.sqrt (y / ellT L g t))) := by ring

end Profile

/-! ## 2. The cutoff scales, the profile `P`, and the shift `P(|b - c'|) ≤ K_n P(|a - b|)` -/

section Scales

variable {d : ℕ} (sz : Sizes d)

/-- **The cutoff scale `ℓ*_t = (log W)^{3/2} ℓ_t`** (`(eq:cutoff_scales)`, `3_5:830`); the same object as
the inline scale of `KellStarEv` (`Path/KellStar.lean:60`). -/
def emn2ExpEllStar (n : ℕ) (u : ℝ) : ℝ :=
  Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (sz.lam n) u

/-- **The cutoff scale `ℓ†_t = (log W)^{7/4} ℓ_t`** (`(eq:cutoff_scales)`, `3_5:830`). -/
def emn2ExpEllDag (n : ℕ) (u : ℝ) : ℝ :=
  Real.log ((sz.W n : ℕ) : ℝ) ^ ((7 : ℝ) / 4) * ellT (sz.L n) (sz.lam n) u

/-- `W^{-d} 𝒯̃^ℓ_{u,D}(x)` at a real argument `x`; `STprof` is this at `x = |a - b|`. -/
def emn2ExpPf (n : ℕ) (u D ℓ x : ℝ) : ℝ :=
  (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) u ℓ ((sz.W n : ℕ) : ℝ) D x

/-- `STprof` is `emn2ExpPf` at the real argument `|a - b|` (definitional). -/
theorem emn2Exp_STprof_eq (n : ℕ) (u D ℓ : ℝ) (a b : Zd d (sz.L n)) :
    STprof sz n u D ℓ a b = emn2ExpPf sz n u D ℓ ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) := rfl

/-- The loss constant of the shift `P(|b - c'|) ≤ K_n P(|a - b|)`: `K_n = 2^{d-2} exp(2 (log W)^{3/4})`. -/
def emn2ExpK (d : ℕ) (W : ℝ) : ℝ := 2 ^ (d - 2) * Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4))

/-- `K_n ≥ 1` (so that `P(m) ≤ P(r)` is `≤ K_n P(r)` in case (1)). -/
theorem emn2Exp_one_le_K (d : ℕ) {W : ℝ} (hW : 1 ≤ W) : 1 ≤ emn2ExpK d W := by
  unfold emn2ExpK
  have h1 : (1 : ℝ) ≤ 2 ^ (d - 2) := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4)) := by
    apply Real.one_le_exp
    have : 0 ≤ Real.log W := Real.log_nonneg hW
    positivity
  nlinarith

/-- **`𝒯̃(|b - c'|) ≺ 𝒯̃(|a - b|)`, abstractly** (`3_5:851-853`): let `P(x) = W^{-d} 𝒯̃^ℓ_{t,D}(x)`,
`ℓ ≥ 0`, `s ≥ 0`, `2 s ≤ ℓ_†` and `r > ℓ_†`.  If `m > ℓ` (case (1): `𝒯̃(m) = 𝒯̃(ℓ) ≤ 𝒯̃(r)`) or `m ≥ r - s`
(case (2): the shift of `𝒯_t` by at most `s`), then `P(m) ≤ 2^{d-2} exp((s/ℓ_t)^{1/2}) P(r)`. -/
theorem emn2Exp_profile_shift {d L : ℕ} (hL : 1 ≤ (L : ℝ)) (g t Wr D ℓ : ℝ) (hW : 0 < Wr)
    (hℓ : 0 ≤ ℓ) {r m s ℓd : ℝ} (hs0 : 0 ≤ s) (hs : 2 * s ≤ ℓd) (hr : ℓd < r)
    (hm : ℓ < m ∨ r ≤ m + s) :
    (Wr ^ d)⁻¹ * tailW d L g t ℓ Wr D m ≤
      2 ^ (d - 2) * Real.exp (Real.sqrt (s / ellT L g t)) *
        ((Wr ^ d)⁻¹ * tailW d L g t ℓ Wr D r) := by
  have hK1 : 1 ≤ 2 ^ (d - 2) * Real.exp (Real.sqrt (s / ellT L g t)) := by
    have h1 : (1 : ℝ) ≤ 2 ^ (d - 2) := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ Real.exp (Real.sqrt (s / ellT L g t)) :=
      Real.one_le_exp (Real.sqrt_nonneg _)
    nlinarith
  set K : ℝ := 2 ^ (d - 2) * Real.exp (Real.sqrt (s / ellT L g t)) with hKdef
  have hK0 : 0 ≤ K := by linarith
  have hmin0 : ∀ x : ℝ, 0 ≤ x → 0 ≤ min x ℓ := fun x hx => le_min hx hℓ
  have hr0 : 0 ≤ r := by linarith
  have hTr0 : 0 ≤ tailT d L g t (min r ℓ) := tailT_nonneg (hmin0 r hr0)
  have hA : tailT d L g t ℓ ≤ tailT d L g t (min r ℓ) :=
    tailT_antitone (hmin0 r hr0) (min_le_right r ℓ)
  have hAK : tailT d L g t ℓ ≤ K * tailT d L g t (min r ℓ) :=
    hA.trans (le_mul_of_one_le_left hTr0 hK1)
  have hkey : tailT d L g t (min m ℓ) ≤ K * tailT d L g t (min r ℓ) := by
    by_cases hc : ℓ < m
    · rw [min_eq_right hc.le]; exact hAK
    · have hm' : r ≤ m + s := by
        rcases hm with h | h
        · exact absurd h hc
        · exact h
      by_cases hx : ℓ ≤ r - s
      · have : ℓ ≤ m := by linarith
        rw [min_eq_right this]; exact hAK
      · push Not at hx
        have hx0 : 0 ≤ r - s := by linarith
        have h1 : r - s ≤ min m ℓ := le_min (by linarith) hx.le
        have h2 : tailT d L g t (min m ℓ) ≤ tailT d L g t (r - s) := tailT_antitone hx0 h1
        have h3 : r - s ≤ min r ℓ := le_min (by linarith) hx.le
        have h4 : min r ℓ ≤ (r - s) + s := by
          have := min_le_left r ℓ; linarith
        have h5 : s ≤ (r - s) + 1 := by linarith
        have h6 := emn2Exp_tailT_shift (d := d) (L := L) (g := g) (t := t) hL hx0 h3 h4 hs0 h5
        exact h2.trans (h6.trans (mul_le_mul_of_nonneg_right (le_refl K) hTr0))
  unfold tailW
  have hwd : 0 ≤ (Wr ^ d)⁻¹ := inv_nonneg.mpr (by positivity)
  have hmax : max (tailT d L g t (min m ℓ)) (Wr ^ (-D)) ≤
      K * max (tailT d L g t (min r ℓ)) (Wr ^ (-D)) := by
    refine max_le ?_ ?_
    · exact hkey.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hK0)
    · have hw0 : 0 ≤ max (tailT d L g t (min r ℓ)) (Wr ^ (-D)) := hTr0.trans (le_max_left _ _)
      exact (le_max_right _ _).trans (le_mul_of_one_le_left hw0 hK1)
  calc (Wr ^ d)⁻¹ * max (tailT d L g t (min m ℓ)) (Wr ^ (-D))
      ≤ (Wr ^ d)⁻¹ * (K * max (tailT d L g t (min r ℓ)) (Wr ^ (-D))) :=
        mul_le_mul_of_nonneg_left hmax hwd
    _ = K * ((Wr ^ d)⁻¹ * max (tailT d L g t (min r ℓ)) (Wr ^ (-D))) := by ring

/-- **The gap between the cutoff scales**: `(log W)^{1/4} ≥ 4` gives `2 (ℓ*_t + 1) ≤ ℓ†_t`
(`ℓ†_t = (log W)^{1/4} ℓ*_t` and `ℓ*_t ≥ 1`). -/
theorem emn2Exp_scale_gap (n : ℕ) (u : ℝ) (hLg1 : 1 ≤ Real.log ((sz.W n : ℕ) : ℝ))
    (hLg4 : 4 ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ ((1 : ℝ) / 4)) :
    2 * (emn2ExpEllStar sz n u + 1) ≤ emn2ExpEllDag sz n u := by
  set Lg : ℝ := Real.log ((sz.W n : ℕ) : ℝ) with hLg
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hlt1 : 1 ≤ ellT (sz.L n) (sz.lam n) u := one_le_ellT hL1
  have hLg0 : 0 < Lg := by linarith
  have ha1one : 1 ≤ Lg ^ ((3 : ℝ) / 2) := Real.one_le_rpow hLg1 (by norm_num)
  have hdag : Lg ^ ((7 : ℝ) / 4) = Lg ^ ((3 : ℝ) / 2) * Lg ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_add hLg0]; norm_num
  unfold emn2ExpEllStar emn2ExpEllDag
  rw [hdag]
  set a1 : ℝ := Lg ^ ((3 : ℝ) / 2)
  set a2 : ℝ := Lg ^ ((1 : ℝ) / 4)
  set lt : ℝ := ellT (sz.L n) (sz.lam n) u
  have h1 : 1 ≤ a1 * lt := by nlinarith
  have h2 : 4 * (a1 * lt) ≤ a2 * (a1 * lt) := mul_le_mul_of_nonneg_right hLg4 (by positivity)
  nlinarith

/-- **`𝒯̃(|b - c'|) ≺ 𝒯̃(|a - b|)`** (`3_5:851-853`): for `r > ℓ†_t` and a distance `m` that is either
`> ℓ` (case (1)) or `≥ r - ℓ*_t - 1` (case (2)), `P(m) ≤ K_n P(r)`, `K_n = 2^{d-2} exp(2 (log W)^{3/4})
= N^{o(1)}`.  Used at `m = |c' - b|` for `S̃₁` and `m = |c - a|` for `S̃₂`.  The hypothesis
`2 (ℓ*_t + 1) ≤ ℓ†_t` (`ℓ†_t/2 ≥ ℓ*_t + 1`: the paper's "`(1 - o(1)) |a-b|`") holds eventually
(`emn2Exp_scale_gap`). -/
theorem emn2Exp_profile_cmp (n : ℕ) (u D ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (hLg1 : 1 ≤ Real.log ((sz.W n : ℕ) : ℝ))
    (hs : 2 * (emn2ExpEllStar sz n u + 1) ≤ emn2ExpEllDag sz n u)
    {r m : ℝ} (hr : emn2ExpEllDag sz n u < r)
    (hm : ℓ < m ∨ r ≤ m + emn2ExpEllStar sz n u + 1) :
    emn2ExpPf sz n u D ℓ m ≤ emn2ExpK d ((sz.W n : ℕ) : ℝ) * emn2ExpPf sz n u D ℓ r := by
  set Wr : ℝ := ((sz.W n : ℕ) : ℝ) with hWr
  set Lg : ℝ := Real.log Wr with hLg
  set lt : ℝ := ellT (sz.L n) (sz.lam n) u with hlt
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hlt1 : 1 ≤ lt := one_le_ellT hL1
  have hlt0 : 0 < lt := by linarith
  have hWpos : 0 < Wr := by rw [hWr]; exact_mod_cast sz.W_pos n
  have hW1 : (1 : ℝ) ≤ Wr := by rw [hWr]; exact_mod_cast sz.W_pos n
  have hLg0 : 0 < Lg := by linarith
  set a1 : ℝ := Lg ^ ((3 : ℝ) / 2) with ha1
  have ha1one : 1 ≤ a1 := Real.one_le_rpow hLg1 (by norm_num)
  have hstar : emn2ExpEllStar sz n u = a1 * lt := rfl
  rw [hstar] at hs hm
  have hs0 : 0 ≤ a1 * lt + 1 := by positivity
  have hshift := emn2Exp_profile_shift (d := d) (L := sz.L n) hL1 (sz.lam n) u Wr D ℓ hWpos hℓ
    (r := r) (m := m) (s := a1 * lt + 1) (ℓd := emn2ExpEllDag sz n u) hs0
    hs hr (by
      rcases hm with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith))
  -- `√((ℓ* + 1)/ℓ_t) ≤ 2 (log W)^{3/4}`
  have hsq : Real.sqrt ((a1 * lt + 1) / lt) ≤ 2 * Lg ^ ((3 : ℝ) / 4) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have e : (Lg ^ ((3 : ℝ) / 4)) ^ 2 = a1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hLg0.le, ha1]; norm_num
    have h3 : (a1 * lt + 1) / lt ≤ a1 + 1 := by
      rw [div_le_iff₀ hlt0]
      nlinarith
    calc (a1 * lt + 1) / lt ≤ a1 + 1 := h3
      _ ≤ 4 * a1 := by linarith
      _ = (2 * Lg ^ ((3 : ℝ) / 4)) ^ 2 := by rw [mul_pow, e]; ring
  have hKshift : (2 : ℝ) ^ (d - 2) * Real.exp (Real.sqrt ((a1 * lt + 1) / lt)) ≤
      emn2ExpK d Wr := by
    unfold emn2ExpK
    gcongr
  have hPf0 : 0 ≤ emn2ExpPf sz n u D ℓ r := by
    unfold emn2ExpPf
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hWpos.le d)) (tailW_pos hWpos _).le
  unfold emn2ExpPf
  exact hshift.trans (mul_le_mul_of_nonneg_right hKshift (by
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hWpos.le d)) (tailW_pos hWpos _).le))

end Scales

/-! ## 3. Lattice facts (copies of the private lemmas of `EMn2Poly.lean` §5) -/

section Lattice

private lemma emn2Exp_zdistInf_zero (d L : ℕ) : zdistInf d L (0 : Zd d L) = 0 := by
  unfold zdistInf
  exact Nat.eq_zero_of_le_zero (Finset.sup_le fun i _ => by simp)

private lemma emn2Exp_zdistInf_neg (d L : ℕ) [NeZero L] (x : Zd d L) :
    zdistInf d L (-x) = zdistInf d L x := by
  unfold zdistInf
  exact Finset.sup_congr rfl fun i _ => by simp [zdist_neg]

private lemma emn2Exp_zdistInf_add_le (d L : ℕ) [NeZero L] (x y : Zd d L) :
    zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y := by
  unfold zdistInf
  refine Finset.sup_le fun i _ => ?_
  exact (zdist_add_le L (x i) (y i)).trans (add_le_add
    (Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i))
    (Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i)))

private lemma emn2Exp_zdistInf_tri (d L : ℕ) [NeZero L] (x y w : Zd d L) :
    zdistInf d L (x - w) ≤ zdistInf d L (x - y) + zdistInf d L (y - w) := by
  have : x - w = (x - y) + (y - w) := by abel
  rw [this]; exact emn2Exp_zdistInf_add_le d L _ _

private lemma emn2Exp_zdistInf_sub_comm (d L : ℕ) [NeZero L] (x y : Zd d L) :
    zdistInf d L (x - y) = zdistInf d L (y - x) := by
  rw [← neg_sub, emn2Exp_zdistInf_neg]

private lemma emn2Exp_norm_SB_le_one (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) (c c' : Zd d L) :
    ‖SB d L g c c'‖ ≤ 1 := by
  calc ‖SB d L g c c'‖ ≤ ∑ b, ‖SB d L g c b‖ :=
        Finset.single_le_sum (f := fun b => ‖SB d L g c b‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ c')
    _ = 1 := sum_norm_SB_row d L g hL c

private lemma emn2Exp_SB_eq_zero_of_far (d L : ℕ) [NeZero L] (g : ℝ) (c c' : Zd d L)
    (h : 1 < zdistInf d L (c - c')) : SB d L g c c' = 0 := by
  rw [SB_apply, sbKernel]
  have h0 : c - c' ≠ 0 := by
    intro h0; rw [h0, emn2Exp_zdistInf_zero] at h; omega
  have h1 : zdistD d L (c - c') ≠ 1 := by
    intro h1; have := zdistInf_le_zdistD d L (c - c'); omega
  simp [h0, h1]

end Lattice

/-! ## 4. The six-loop sums of the three regions `R₁, R₂, R₃` (`(eq;S123)`, `3_5:842-845`) -/

section Regions

variable {d L W : ℕ} [NeZero L] [NeZero W] (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ)

/-- **`S̃₁`** (`3_5:842-845`, with the prefactor `W^d`): the region `|c-a| ≤ ℓ*` or `|c'-b| > ℓ`
of the `6`-loops of the cut `k = 0` of `(𝓔⊗𝓔)^{M,(2;k)}_{σ,(a,b),(a,b)}` (the paper's `k = 1`), with the
constraint `|c-c'| ≤ 1`. -/
def emn2ExpS1 (ℓs ℓ : ℝ) (σ : Fin 2 → Bool) (a b : Zd d L) : ℝ :=
  ((W : ℕ) : ℝ) ^ d * ∑ c : Zd d L, ∑ c' : Zd d L,
    if zdistInf d L (c - c') ≤ 1 ∧
        ((zdistInf d L (c - a) : ℝ) ≤ ℓs ∨ ℓ < (zdistInf d L (c' - b) : ℝ)) then
      ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
    else 0

/-- **`S̃₂`** (`3_5:842-845`, with the prefactor `W^d`): the region `|c'-b| ≤ ℓ*` or `|c-a| > ℓ`. -/
def emn2ExpS2 (ℓs ℓ : ℝ) (σ : Fin 2 → Bool) (a b : Zd d L) : ℝ :=
  ((W : ℕ) : ℝ) ^ d * ∑ c : Zd d L, ∑ c' : Zd d L,
    if zdistInf d L (c - c') ≤ 1 ∧
        ((zdistInf d L (c' - b) : ℝ) ≤ ℓs ∨ ℓ < (zdistInf d L (c - a) : ℝ)) then
      ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
    else 0

/-- **`S̃₃`** (`3_5:842-845`, with the prefactor `W^d`; bounded in ST2-11): the region `ℓ* < |c'-b| ≤ ℓ`, `ℓ* < |c-a| ≤ ℓ`. -/
def emn2ExpS3 (ℓs ℓ : ℝ) (σ : Fin 2 → Bool) (a b : Zd d L) : ℝ :=
  ((W : ℕ) : ℝ) ^ d * ∑ c : Zd d L, ∑ c' : Zd d L,
    if zdistInf d L (c - c') ≤ 1 ∧
        ((ℓs < (zdistInf d L (c' - b) : ℝ) ∧ (zdistInf d L (c' - b) : ℝ) ≤ ℓ) ∧
          (ℓs < (zdistInf d L (c - a) : ℝ) ∧ (zdistInf d L (c - a) : ℝ) ≤ ℓ)) then
      ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
    else 0

/-- **The cover** `(eq;S123)` (`3_5:842-845`): every pair `(c,c')` with `|c - c'| ≤ 1` is in one of the
three regions, so `|(𝓔⊗𝓔)^{M,(2;0)}| ≤ S̃₁ + S̃₂ + S̃₃` (`|S^{(B)}| ≤ 1`, supported on
`|c - c'| ≤ 1`; deterministic, `L ≥ 3`). -/
theorem emn2Exp_cover (hL : 3 ≤ L) (g ℓs ℓ : ℝ) (σ : Fin 2 → Bool) (a b : Zd d L) :
    ‖(((W : ℕ) : ℂ) ^ d) * ∑ c : Zd d L, ∑ c' : Zd d L, SB d L g c c' *
        loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖ ≤
      emn2ExpS1 H z ℓs ℓ σ a b + emn2ExpS2 H z ℓs ℓ σ a b + emn2ExpS3 H z ℓs ℓ σ a b := by
  have hW : (0 : ℝ) < ((W : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hWd : (0 : ℝ) < ((W : ℕ) : ℝ) ^ d := pow_pos hW d
  have hterm : ∀ c c' : Zd d L,
      ‖SB d L g c c' * loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)]
          ![a, b, c', b, a, c]‖ ≤
        (if zdistInf d L (c - c') ≤ 1 ∧
          ((zdistInf d L (c - a) : ℝ) ≤ ℓs ∨ ℓ < (zdistInf d L (c' - b) : ℝ)) then
          ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
          else 0) +
        (if zdistInf d L (c - c') ≤ 1 ∧
          ((zdistInf d L (c' - b) : ℝ) ≤ ℓs ∨ ℓ < (zdistInf d L (c - a) : ℝ)) then
          ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
          else 0) +
        (if zdistInf d L (c - c') ≤ 1 ∧
          ((ℓs < (zdistInf d L (c' - b) : ℝ) ∧ (zdistInf d L (c' - b) : ℝ) ≤ ℓ) ∧
            (ℓs < (zdistInf d L (c - a) : ℝ) ∧ (zdistInf d L (c - a) : ℝ) ≤ ℓ)) then
          ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
          else 0) := by
    intro c c'
    set X : ℝ := ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
      with hX
    have hX0 : 0 ≤ X := norm_nonneg _
    by_cases hn : zdistInf d L (c - c') ≤ 1
    · have hSB : ‖SB d L g c c' * loopFine d L W H z
          ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖ ≤ X := by
        rw [norm_mul]
        calc ‖SB d L g c c'‖ * X ≤ 1 * X :=
              mul_le_mul_of_nonneg_right (emn2Exp_norm_SB_le_one d L hL g c c') hX0
          _ = X := one_mul _
      refine hSB.trans ?_
      by_cases h1 : (zdistInf d L (c - a) : ℝ) ≤ ℓs ∨ ℓ < (zdistInf d L (c' - b) : ℝ)
      · simp only [hn, h1, and_self, ↓reduceIte, true_and]
        split_ifs <;> linarith
      · by_cases h2 : (zdistInf d L (c' - b) : ℝ) ≤ ℓs ∨ ℓ < (zdistInf d L (c - a) : ℝ)
        · simp only [hn, h1, h2, and_self, ↓reduceIte, true_and]
          split_ifs <;> linarith
        · have h3 : (ℓs < (zdistInf d L (c' - b) : ℝ) ∧ (zdistInf d L (c' - b) : ℝ) ≤ ℓ) ∧
              (ℓs < (zdistInf d L (c - a) : ℝ) ∧ (zdistInf d L (c - a) : ℝ) ≤ ℓ) := by
            push Not at h1 h2
            exact ⟨⟨h2.1, h1.2⟩, ⟨h1.1, h2.2⟩⟩
          simp only [hn, h1, h2, h3, and_self, ↓reduceIte, true_and]
          simp
    · have h0 : SB d L g c c' = 0 := emn2Exp_SB_eq_zero_of_far d L g c c' (by omega)
      rw [h0, zero_mul, norm_zero]
      simp only [hn, false_and, ↓reduceIte, add_zero, le_refl]
  unfold emn2ExpS1 emn2ExpS2 emn2ExpS3
  rw [← mul_add, ← mul_add]
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ hWd.le
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c' _ => ?_)
  exact hterm c c'


/-- **`(eq:reduce4_bdd3)`** (`3_5:821-825`) from the 2-loop control `‖𝓛²_{(s,-s),(x,x')}‖ ≤ y² P(|x-x'|)`:
`|𝓛^{(3)}_{(s,σ₂,-σ₂),(a,b,a)}| ≤ y √P(0) · y² P(|b - a|)` (the short leg `P_a G P_a` gives
`y √P(0)`, the two long legs `y² P(|a-b|)`). -/
private lemma emn2Exp_loop3_ctrl (hH : H.IsHermitian) {y : ℝ} (hy : 0 ≤ y) {Pf : ℕ → ℝ}
    (h2 : ∀ (s : Bool) (x x' : Zd d L), ‖loopFine d L W H z ![s, !s] ![x, x']‖ ≤
      y ^ 2 * Pf (zdistInf d L (x - x'))) (s s1 : Bool) (a b : Zd d L) :
    ‖loopFine d L W H z ![s, s1, !s1] ![a, b, a]‖ ≤
      y * Real.sqrt (Pf 0) * (y ^ 2 * Pf (zdistInf d L (b - a))) := by
  refine (emn2Poly_norm_loop3_le H z hH s s1 a b).trans ?_
  have h1 := h2 s a a
  rw [sub_self, emn2Exp_zdistInf_zero] at h1
  have h3 := h2 s1 b a
  have h4 : ‖loopFine d L W H z ![s, !s] ![a, a]‖ ^ (1 / 2 : ℝ) ≤ y * Real.sqrt (Pf 0) := by
    rw [← Real.sqrt_eq_rpow]
    calc Real.sqrt ‖loopFine d L W H z ![s, !s] ![a, a]‖ ≤ Real.sqrt (y ^ 2 * Pf 0) :=
          Real.sqrt_le_sqrt h1
      _ = y * Real.sqrt (Pf 0) := by
          rw [Real.sqrt_mul (sq_nonneg y), Real.sqrt_sq hy]
  exact mul_le_mul h4 h3 (norm_nonneg _) (mul_nonneg hy (Real.sqrt_nonneg _))

/-- **`S̃₁ ≺ ...`** (deterministic, `3_5:848-857`): the region `R₁` through the contraction inequality
`stContractPt_holds` with `𝒜₁ = {c' : |c' - b| > ℓ ∨ ∃ c ∼ c', |c - a| ≤ ℓ*}` and `M = y² K P(r)`;
the hypothesis `hK` is `P(|c'-b|) ≤ K P(|a-b|)` in the two cases of `3_5:851-853`. -/
private lemma emn2Exp_part1 (hH : H.IsHermitian) (hz : 0 < z.im) (σ : Fin 2 → Bool)
    (a b : Zd d L) {y K ℓs ℓ : ℝ} (hy : 0 ≤ y) (hK0 : 0 ≤ K) {Pf : ℕ → ℝ} (hPf : ∀ m, 0 ≤ Pf m)
    (h2 : ∀ (s : Bool) (x x' : Zd d L), ‖loopFine d L W H z ![s, !s] ![x, x']‖ ≤
      y ^ 2 * Pf (zdistInf d L (x - x')))
    (hK : ∀ m : ℕ, (ℓ < (m : ℝ) ∨ (zdistInf d L (a - b) : ℝ) ≤ (m : ℝ) + ℓs + 1) →
      Pf m ≤ K * Pf (zdistInf d L (a - b))) :
    ∑ c : Zd d L, ∑ c' : Zd d L,
        (if zdistInf d L (c - c') ≤ 1 ∧
          ((zdistInf d L (c - a) : ℝ) ≤ ℓs ∨ ℓ < (zdistInf d L (c' - b) : ℝ)) then
          ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
          else 0) ≤
      3 ^ d / (((W : ℕ) : ℝ) ^ d * z.im) * (y ^ 2 * K * Pf (zdistInf d L (a - b))) *
        (y * Real.sqrt (Pf 0) * (y ^ 2 * Pf (zdistInf d L (a - b)))) := by
  set 𝒜 : Finset (Zd d L) := Finset.univ.filter (fun c' : Zd d L => ∃ c : Zd d L,
    zdistInf d L (c - c') ≤ 1 ∧
      ((zdistInf d L (c - a) : ℝ) ≤ ℓs ∨ ℓ < (zdistInf d L (c' - b) : ℝ))) with h𝒜
  have hM0 : 0 ≤ y ^ 2 * K * Pf (zdistInf d L (a - b)) := by
    have := hPf (zdistInf d L (a - b)); positivity
  have hM : ∀ c' ∈ 𝒜, ‖loopFine d L W H z ![σ 0, !(σ 0), σ 0, !(σ 0)] ![c', b, c', b]‖ ^
      (1 / 2 : ℝ) ≤ y ^ 2 * K * Pf (zdistInf d L (a - b)) := by
    intro c' hc'
    obtain ⟨c, hn, hcase⟩ := (Finset.mem_filter.mp hc').2
    have hcmp : Pf (zdistInf d L (c' - b)) ≤ K * Pf (zdistInf d L (a - b)) := by
      refine hK _ ?_
      rcases hcase with h | h
      · right
        have t1 := emn2Exp_zdistInf_tri d L a c b
        have t2 := emn2Exp_zdistInf_tri d L c c' b
        have t3 := emn2Exp_zdistInf_sub_comm d L a c
        have : zdistInf d L (a - b) ≤ zdistInf d L (c - a) + 1 + zdistInf d L (c' - b) := by omega
        have h' : ((zdistInf d L (a - b) : ℕ) : ℝ) ≤
            (zdistInf d L (c - a) : ℝ) + 1 + (zdistInf d L (c' - b) : ℝ) := by exact_mod_cast this
        linarith
      · left; exact h
    calc ‖loopFine d L W H z ![σ 0, !(σ 0), σ 0, !(σ 0)] ![c', b, c', b]‖ ^ (1 / 2 : ℝ)
        ≤ ‖loopFine d L W H z ![σ 0, !(σ 0)] ![c', b]‖ := emn2Poly_norm_loop4_alt_le H z hH (σ 0) b c'
      _ ≤ y ^ 2 * Pf (zdistInf d L (c' - b)) := h2 (σ 0) c' b
      _ ≤ y ^ 2 * (K * Pf (zdistInf d L (a - b))) :=
          mul_le_mul_of_nonneg_left hcmp (sq_nonneg y)
      _ = y ^ 2 * K * Pf (zdistInf d L (a - b)) := by ring
  have hpin := stContractPt_holds d L W H z hH hz σ a b 𝒜 _ hM0 hM
  have hmax : max ‖loopFine d L W H z ![true, σ 1, !(σ 1)] ![a, b, a]‖
      ‖loopFine d L W H z ![false, σ 1, !(σ 1)] ![a, b, a]‖ ≤
      y * Real.sqrt (Pf 0) * (y ^ 2 * Pf (zdistInf d L (a - b))) := by
    have e : zdistInf d L (b - a) = zdistInf d L (a - b) := emn2Exp_zdistInf_sub_comm d L b a
    have h3 := emn2Exp_loop3_ctrl H z hH hy h2
    refine max_le ?_ ?_
    · have := h3 true (σ 1) a b; rwa [e] at this
    · have := h3 false (σ 1) a b; rwa [e] at this
  have hK' : 0 ≤ 3 ^ d / (((W : ℕ) : ℝ) ^ d * z.im) * (y ^ 2 * K * Pf (zdistInf d L (a - b))) := by
    have : (0 : ℝ) < ((W : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
    positivity
  -- rearrange the double sum onto `c' ∈ 𝒜`, `c ∈ filter`
  have hrearr : ∑ c : Zd d L, ∑ c' : Zd d L,
        (if zdistInf d L (c - c') ≤ 1 ∧
          ((zdistInf d L (c - a) : ℝ) ≤ ℓs ∨ ℓ < (zdistInf d L (c' - b) : ℝ)) then
          ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
          else 0) ≤
      ∑ c' ∈ 𝒜, ∑ c ∈ Finset.univ.filter (fun c : Zd d L => zdistInf d L (c - c') ≤ 1),
        ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖ := by
    rw [Finset.sum_comm]
    have hz0 : ∀ c' ∉ 𝒜, ∑ c : Zd d L,
        (if zdistInf d L (c - c') ≤ 1 ∧
          ((zdistInf d L (c - a) : ℝ) ≤ ℓs ∨ ℓ < (zdistInf d L (c' - b) : ℝ)) then
          ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
          else 0) = 0 := by
      intro c' hc'
      refine Finset.sum_eq_zero fun c _ => ?_
      have hn : ¬ (zdistInf d L (c - c') ≤ 1 ∧
          ((zdistInf d L (c - a) : ℝ) ≤ ℓs ∨ ℓ < (zdistInf d L (c' - b) : ℝ))) := fun hn =>
        hc' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, c, hn.1, hn.2⟩)
      simp only [hn, ↓reduceIte]
    calc ∑ c' : Zd d L, ∑ c : Zd d L,
          (if zdistInf d L (c - c') ≤ 1 ∧
            ((zdistInf d L (c - a) : ℝ) ≤ ℓs ∨ ℓ < (zdistInf d L (c' - b) : ℝ)) then
            ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
            else 0)
        = ∑ c' ∈ 𝒜, ∑ c : Zd d L,
          (if zdistInf d L (c - c') ≤ 1 ∧
            ((zdistInf d L (c - a) : ℝ) ≤ ℓs ∨ ℓ < (zdistInf d L (c' - b) : ℝ)) then
            ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
            else 0) := by
          symm
          exact Finset.sum_subset (Finset.filter_subset _ _) fun c' _ hc' => hz0 c' hc'
      _ ≤ _ := by
          refine Finset.sum_le_sum fun c' _ => ?_
          rw [← Finset.sum_filter]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)
          intro c hc
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hc).2.1⟩
  calc _ ≤ _ := hrearr
    _ ≤ _ := hpin
    _ ≤ _ := mul_le_mul_of_nonneg_left hmax hK'


/-- **`S̃₂ ≺ ...`** (deterministic): the region `R₂` through the partner
`emn2Poly_contractPt_partner` with `𝒜₂ = {c : |c - a| > ℓ ∨ ∃ c' ∼ c, |c' - b| ≤ ℓ*}`. -/
private lemma emn2Exp_part2 (hH : H.IsHermitian) (hz : 0 < z.im) (σ : Fin 2 → Bool)
    (a b : Zd d L) {y K ℓs ℓ : ℝ} (hy : 0 ≤ y) (hK0 : 0 ≤ K) {Pf : ℕ → ℝ} (hPf : ∀ m, 0 ≤ Pf m)
    (h2 : ∀ (s : Bool) (x x' : Zd d L), ‖loopFine d L W H z ![s, !s] ![x, x']‖ ≤
      y ^ 2 * Pf (zdistInf d L (x - x')))
    (hK : ∀ m : ℕ, (ℓ < (m : ℝ) ∨ (zdistInf d L (a - b) : ℝ) ≤ (m : ℝ) + ℓs + 1) →
      Pf m ≤ K * Pf (zdistInf d L (a - b))) :
    ∑ c : Zd d L, ∑ c' : Zd d L,
        (if zdistInf d L (c - c') ≤ 1 ∧
          ((zdistInf d L (c' - b) : ℝ) ≤ ℓs ∨ ℓ < (zdistInf d L (c - a) : ℝ)) then
          ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
          else 0) ≤
      3 ^ d / (((W : ℕ) : ℝ) ^ d * z.im) * (y ^ 2 * K * Pf (zdistInf d L (a - b))) *
        (y * Real.sqrt (Pf 0) * (y ^ 2 * Pf (zdistInf d L (a - b)))) := by
  set 𝒜 : Finset (Zd d L) := Finset.univ.filter (fun c : Zd d L => ∃ c' : Zd d L,
    zdistInf d L (c - c') ≤ 1 ∧
      ((zdistInf d L (c' - b) : ℝ) ≤ ℓs ∨ ℓ < (zdistInf d L (c - a) : ℝ))) with h𝒜
  have hM0 : 0 ≤ y ^ 2 * K * Pf (zdistInf d L (a - b)) := by
    have := hPf (zdistInf d L (a - b)); positivity
  have h4 : ∀ c ∈ 𝒜, ‖loopFine d L W H z ![!(σ 0), σ 0, !(σ 0), σ 0] ![c, a, c, a]‖ ^
      (1 / 2 : ℝ) ≤ y ^ 2 * K * Pf (zdistInf d L (a - b)) := by
    intro c hc
    obtain ⟨c', hn, hcase⟩ := (Finset.mem_filter.mp hc).2
    have hcmp : Pf (zdistInf d L (c - a)) ≤ K * Pf (zdistInf d L (a - b)) := by
      refine hK _ ?_
      rcases hcase with h | h
      · right
        have t1 := emn2Exp_zdistInf_tri d L a c b
        have t2 := emn2Exp_zdistInf_tri d L c c' b
        have t3 := emn2Exp_zdistInf_sub_comm d L a c
        have : zdistInf d L (a - b) ≤ zdistInf d L (c - a) + 1 + zdistInf d L (c' - b) := by omega
        have h' : ((zdistInf d L (a - b) : ℕ) : ℝ) ≤
            (zdistInf d L (c - a) : ℝ) + 1 + (zdistInf d L (c' - b) : ℝ) := by exact_mod_cast this
        linarith
      · left; exact h
    have h5 := emn2Poly_norm_loop4_alt_le H z hH (!(σ 0)) a c
    have h6 := h2 (!(σ 0)) c a
    simp only [Bool.not_not] at h5 h6
    calc ‖loopFine d L W H z ![!(σ 0), σ 0, !(σ 0), σ 0] ![c, a, c, a]‖ ^ (1 / 2 : ℝ)
        ≤ ‖loopFine d L W H z ![!(σ 0), σ 0] ![c, a]‖ := h5
      _ ≤ y ^ 2 * Pf (zdistInf d L (c - a)) := h6
      _ ≤ y ^ 2 * (K * Pf (zdistInf d L (a - b))) :=
          mul_le_mul_of_nonneg_left hcmp (sq_nonneg y)
      _ = y ^ 2 * K * Pf (zdistInf d L (a - b)) := by ring
  have hpin := emn2Poly_contractPt_partner H z hH hz (σ 0) (σ 1) a b 𝒜 _ hM0 h4
  have hmax : max ‖loopFine d L W H z ![true, !(σ 1), σ 1] ![b, a, b]‖
      ‖loopFine d L W H z ![false, !(σ 1), σ 1] ![b, a, b]‖ ≤
      y * Real.sqrt (Pf 0) * (y ^ 2 * Pf (zdistInf d L (a - b))) := by
    have h3 := emn2Exp_loop3_ctrl H z hH hy h2
    refine max_le ?_ ?_
    · have := h3 true (!(σ 1)) b a; simpa only [Bool.not_not] using this
    · have := h3 false (!(σ 1)) b a; simpa only [Bool.not_not] using this
  have hK' : 0 ≤ 3 ^ d / (((W : ℕ) : ℝ) ^ d * z.im) * (y ^ 2 * K * Pf (zdistInf d L (a - b))) := by
    have : (0 : ℝ) < ((W : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
    positivity
  have hrearr : ∑ c : Zd d L, ∑ c' : Zd d L,
        (if zdistInf d L (c - c') ≤ 1 ∧
          ((zdistInf d L (c' - b) : ℝ) ≤ ℓs ∨ ℓ < (zdistInf d L (c - a) : ℝ)) then
          ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
          else 0) ≤
      ∑ c ∈ 𝒜, ∑ c' ∈ Finset.univ.filter (fun c' : Zd d L => zdistInf d L (c' - c) ≤ 1),
        ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖ := by
    have hz0 : ∀ c ∉ 𝒜, ∑ c' : Zd d L,
        (if zdistInf d L (c - c') ≤ 1 ∧
          ((zdistInf d L (c' - b) : ℝ) ≤ ℓs ∨ ℓ < (zdistInf d L (c - a) : ℝ)) then
          ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
          else 0) = 0 := by
      intro c hc
      refine Finset.sum_eq_zero fun c' _ => ?_
      have hn : ¬ (zdistInf d L (c - c') ≤ 1 ∧
          ((zdistInf d L (c' - b) : ℝ) ≤ ℓs ∨ ℓ < (zdistInf d L (c - a) : ℝ))) := fun hn =>
        hc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, c', hn.1, hn.2⟩)
      simp only [hn, ↓reduceIte]
    calc ∑ c : Zd d L, ∑ c' : Zd d L,
          (if zdistInf d L (c - c') ≤ 1 ∧
            ((zdistInf d L (c' - b) : ℝ) ≤ ℓs ∨ ℓ < (zdistInf d L (c - a) : ℝ)) then
            ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
            else 0)
        = ∑ c ∈ 𝒜, ∑ c' : Zd d L,
          (if zdistInf d L (c - c') ≤ 1 ∧
            ((zdistInf d L (c' - b) : ℝ) ≤ ℓs ∨ ℓ < (zdistInf d L (c - a) : ℝ)) then
            ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
            else 0) := by
          symm
          exact Finset.sum_subset (Finset.filter_subset _ _) fun c hc hc' => hz0 c hc'
      _ ≤ _ := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [← Finset.sum_filter]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)
          intro c' hc'
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rw [emn2Exp_zdistInf_sub_comm d L c' c]
          exact (Finset.mem_filter.mp hc').2.1
  calc _ ≤ _ := hrearr
    _ ≤ _ := hpin
    _ ≤ _ := mul_le_mul_of_nonneg_left hmax hK'

/-- **`S̃₁ + S̃₂`, deterministically** (`(eq:pointwise_loop2)`, `(eq_S1tilde)`, `(eq:boundwtS_1)`,
`3_5:848-863`): for every Hermitian `H` and `Im z > 0`, if every 2-loop of the pattern `(s,-s)` is at
most `y² P(|x - x'|)` and `P(|b - c'|) ≤ K P(|a-b|)` in the two cases of `3_5:851-853`, then
`S̃₁ + S̃₂ ≤ 2 · 3^d η⁻¹ K y⁵ √P(0) P(|a-b|)²` (`η = Im z`).  No entry bound `(GijGEX)` is used. -/
theorem emn2Exp_S12_le (hH : H.IsHermitian) (hz : 0 < z.im) (σ : Fin 2 → Bool)
    (a b : Zd d L) {y K ℓs ℓ : ℝ} (hy : 0 ≤ y) (hK0 : 0 ≤ K) {Pf : ℕ → ℝ} (hPf : ∀ m, 0 ≤ Pf m)
    (h2 : ∀ (s : Bool) (x x' : Zd d L), ‖loopFine d L W H z ![s, !s] ![x, x']‖ ≤
      y ^ 2 * Pf (zdistInf d L (x - x')))
    (hK : ∀ m : ℕ, (ℓ < (m : ℝ) ∨ (zdistInf d L (a - b) : ℝ) ≤ (m : ℝ) + ℓs + 1) →
      Pf m ≤ K * Pf (zdistInf d L (a - b))) :
    emn2ExpS1 H z ℓs ℓ σ a b + emn2ExpS2 H z ℓs ℓ σ a b ≤
      2 * 3 ^ d / z.im * K * y ^ 5 * Real.sqrt (Pf 0) * Pf (zdistInf d L (a - b)) ^ 2 := by
  have hW : (0 : ℝ) < ((W : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hWd : (0 : ℝ) < ((W : ℕ) : ℝ) ^ d := pow_pos hW d
  have hp1 := emn2Exp_part1 H z hH hz σ a b hy hK0 hPf h2 hK
  have hp2 := emn2Exp_part2 H z hH hz σ a b hy hK0 hPf h2 hK
  unfold emn2ExpS1 emn2ExpS2
  rw [← mul_add]
  calc ((W : ℕ) : ℝ) ^ d * (_ + _)
      ≤ ((W : ℕ) : ℝ) ^ d * (3 ^ d / (((W : ℕ) : ℝ) ^ d * z.im) *
          (y ^ 2 * K * Pf (zdistInf d L (a - b))) *
          (y * Real.sqrt (Pf 0) * (y ^ 2 * Pf (zdistInf d L (a - b)))) +
        3 ^ d / (((W : ℕ) : ℝ) ^ d * z.im) * (y ^ 2 * K * Pf (zdistInf d L (a - b))) *
          (y * Real.sqrt (Pf 0) * (y ^ 2 * Pf (zdistInf d L (a - b))))) :=
        mul_le_mul_of_nonneg_left (add_le_add hp1 hp2) hWd.le
    _ = _ := by
        field_simp
        ring

end Regions

/-! ## 5. Eventual size facts -/

section Eventually

variable {d : ℕ} (sz : Sizes d)

/-- `N → ∞` forces `d ≥ 1` (for `d = 0`, `N = (W L)^0 = 1`). -/
private theorem emn2Exp_d_pos (h : sz.SizeTendsto) : 0 < d := by
  by_contra h0
  have hd : d = 0 := by omega
  subst hd
  have h1 : ∀ n, ((sz.size n : ℕ) : ℝ) = 1 := fun n => by simp [Sizes.size]
  have h2 := h.eventually (eventually_ge_atTop (2 : ℝ))
  obtain ⟨n, hn⟩ := h2.exists
  rw [h1 n] at hn
  norm_num at hn

/-- `W ≤ N`. -/
private theorem emn2Exp_W_le_size (hd : 0 < d) (n : ℕ) :
    ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  exact (le_self_pow₀ hW1 hd.ne').trans (ST_Wpow_le_size sz n)

/-- `C e^{c u^a} ≤ e^{δ u}` for large `u` (`0 ≤ a < 1`). -/
private theorem emn2Exp_exp_pow_le {c a δ : ℝ} (ha1 : a < 1)
    (hδ : 0 < δ) (C : ℝ) :
    ∀ᶠ u : ℝ in atTop, C * Real.exp (c * u ^ a) ≤ Real.exp (δ * u) := by
  have h1 : ∀ᶠ u : ℝ in atTop, (2 * c / δ) ≤ u ^ (1 - a) :=
    (tendsto_rpow_atTop (by linarith : 0 < 1 - a)).eventually_ge_atTop _
  have h2 : ∀ᶠ u : ℝ in atTop, Real.log (max C 1) ≤ δ / 2 * u :=
    (tendsto_id.const_mul_atTop (by positivity : 0 < δ / 2)).eventually_ge_atTop _
  filter_upwards [h1, h2, eventually_gt_atTop (0 : ℝ)] with u hu1 hu2 hu0
  have hua : 0 ≤ u ^ a := Real.rpow_nonneg hu0.le _
  have e : u = u ^ a * u ^ (1 - a) := by
    rw [← Real.rpow_add hu0]; simp
  have hc' : c ≤ δ / 2 * u ^ (1 - a) := by
    have h := mul_le_mul_of_nonneg_left hu1 (by positivity : 0 ≤ δ / 2)
    calc c = δ / 2 * (2 * c / δ) := by field_simp
      _ ≤ _ := h
  have h3 : c * u ^ a ≤ δ / 2 * u := by
    calc c * u ^ a ≤ (δ / 2 * u ^ (1 - a)) * u ^ a := mul_le_mul_of_nonneg_right hc' hua
      _ = δ / 2 * (u ^ a * u ^ (1 - a)) := by ring
      _ = δ / 2 * u := by rw [← e]
  have hC : C ≤ Real.exp (Real.log (max C 1)) := by
    rw [Real.exp_log (by positivity)]; exact le_max_left _ _
  calc C * Real.exp (c * u ^ a) ≤ Real.exp (Real.log (max C 1)) * Real.exp (c * u ^ a) :=
        mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le
    _ = Real.exp (Real.log (max C 1) + c * u ^ a) := by rw [← Real.exp_add]
    _ ≤ Real.exp (δ * u) := Real.exp_le_exp.mpr (by linarith)

/-- **`C e^{c (log W)^a} ≤ N^δ` eventually** (`C ≥ 0`, `0 ≤ a < 1`, `δ > 0`): `W ≤ N` and
`log N → ∞`. -/
theorem emn2Exp_ev_exp_pow (hd : 0 < d) (hsize : sz.SizeTendsto) {c a δ : ℝ} (hc : 0 ≤ c)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hδ : 0 < δ) {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ n in atTop, C * Real.exp (c * Real.log ((sz.W n : ℕ) : ℝ) ^ a) ≤
      ((sz.size n : ℕ) : ℝ) ^ δ := by
  have hlog : Tendsto (fun n => Real.log ((sz.size n : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hsize
  filter_upwards [hlog.eventually (emn2Exp_exp_pow_le ha1 hδ C)] with n hn
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hWN := emn2Exp_W_le_size sz hd n
  have hl : Real.log ((sz.W n : ℕ) : ℝ) ≤ Real.log ((sz.size n : ℕ) : ℝ) :=
    Real.log_le_log hW0 hWN
  have hl0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := by
    apply Real.log_nonneg; exact_mod_cast sz.W_pos n
  have hpow : Real.log ((sz.W n : ℕ) : ℝ) ^ a ≤ Real.log ((sz.size n : ℕ) : ℝ) ^ a :=
    Real.rpow_le_rpow hl0 hl ha0
  have hexp : Real.exp (c * Real.log ((sz.W n : ℕ) : ℝ) ^ a) ≤
      Real.exp (c * Real.log ((sz.size n : ℕ) : ℝ) ^ a) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpow hc)
  calc C * Real.exp (c * Real.log ((sz.W n : ℕ) : ℝ) ^ a)
      ≤ C * Real.exp (c * Real.log ((sz.size n : ℕ) : ℝ) ^ a) := mul_le_mul_of_nonneg_left hexp hC
    _ ≤ Real.exp (δ * Real.log ((sz.size n : ℕ) : ℝ)) := hn
    _ = ((sz.size n : ℕ) : ℝ) ^ δ := by
        rw [Real.rpow_def_of_pos hN0, mul_comm]

end Eventually

/-! ## 5b. The model facts of the third estimate over the carrier, and the premise block (T2404) -/

section CarrierFacts

/-- **The facts the third estimate reads from the model** (`lem: EMn2_N`, `3_5:829-888`): over the carrier
`mk sz z` and the realization `(Hf, ζf)` of its loops, the facts of the first estimate (`emn2PolyFacts`) and, for every
`Flow`, for `0 ≤ u ≤ T0`: (T) `T0 < 1`; (E) `η_u ≤ 1 - u`; (B) the size data `cB W^{-d} ≤ W^{-d} B_{u,0} ≤ N^{-c}`
(`STBdata`, `ST_Bdata_holds`). -/
def emn2ExpFacts (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (u : ℝ), sz.SeqΩ →
      Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (ζf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (u : ℝ), ℂ) : Prop :=
  emn2PolyFacts d Flow mk T0 Hf ζf ∧
    ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
        (∀ n, T0 sz z n < 1) ∧
        (∀ (n : ℕ) (u : ℝ), 0 ≤ u → u ≤ T0 sz z n → (mk sz z).eta n u ≤ 1 - u) ∧
        ∃ cB c : ℝ, 0 < cB ∧ 0 < c ∧ ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ T0 sz z n →
          cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c)

/-- **The premise block of `STEMn2ExpgL`** (`Chain/Step2Gen.lean:483`) up to the choice of `D`, with the conclusion
`Q` at `(sz, z, t, ℓ, D)`: the near case, `S̃₁ + S̃₂` and `S̃₃` below have the premises of the pin word for word. -/
def emn2ExpPrem (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Q : ∀ (sz : Sizes d) (z : ℕ → ℂ) (t ℓ : ℕ → ℝ) (D : ℝ), Prop) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
        ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℝ,
          (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n ∧
            Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
          STInitialGT2gL (mk sz z) (law sz) t ε₀ Ψ →
          ∀ ℓ : ℕ → ℝ, (∀ᶠ n in atTop, 0 ≤ ℓ n ∧ ℓ n ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 *
              ellT (sz.L n) (sz.lam n) (t n)) →
            (∀ D : ℝ, 0 < D → STLWassmExpgL (mk sz z) (law sz) t D ℓ) →
            ∀ D : ℝ, 0 < D → Q sz z t ℓ D

/-- **The facts of the third estimate at the band**: `mk = bandFM ∘ STflowE`, `Hf = seqHflow`, `ζf = zt`. -/
theorem emn2Exp_bandFacts (d : ℕ) :
    emn2ExpFacts d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => RBM.BA.bandFM sz (STflowE z)) (fun _ z n => lemT (z n))
      (fun sz _ n u ω => sz.seqHflow n u ω) (fun _ z n u => zt (STflowE z n) u) := by
  refine ⟨emn2Poly_bandFacts d, fun κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow => ?_⟩
  have hzim : ∀ n, 0 < (z n).im := fun n => ST_flow_im_pos sz hflow n
  refine ⟨fun n => lemT_lt_one (hzim n), fun n u _ huT => ?_, ?_⟩
  · have h1 : 0 ≤ 1 - u := by linarith [huT.trans_lt (lemT_lt_one (hzim n))]
    have hm1 : (mE (STflowE z n)).im ≤ 1 :=
      (Complex.im_le_norm _).trans (norm_mE (abs_lemE_lt_two (hzim n)).le).le
    exact mul_le_of_le_one_right h1 hm1
  · obtain ⟨cB, hcB, hBd⟩ := ST_Bdata_holds (emn2Exp_d_pos sz hflow.1.2.2.1) κ ε 𝔡 hκ hε h𝔡
    obtain ⟨c, hc, hbd⟩ := hBd 𝔠
    exact ⟨cB, c, hcB, hc, hbd sz z hflow (fun n => lemT (z n)) (fun n => by unfold lemT; positivity)
      (fun n => le_rfl)⟩

/-- `Prec`-monotonicity in the control at an arbitrary law (`ST_prec_mono_eventually`, `Step2Events.lean:49`, at `μ`). -/
private theorem emn2Exp_precL_mono {d : ℕ} (sz : Sizes d) (μ : Measure sz.SeqΩ) {U : ℕ → Type*}
    {ξ ζ ζ' : ∀ n, U n → sz.SeqΩ → ℝ} (hle : ∀ᶠ n in atTop, ∀ u ω, ζ n u ω ≤ ζ' n u ω)
    (h : PrecL sz μ ξ ζ) : PrecL sz μ ξ ζ' :=
  StochDomAt.of_subset h fun τ hτ => ⟨τ, hτ, hle.mono fun n hn ω ⟨u, hu⟩ =>
    ⟨u, lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hn u ω)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hu⟩⟩

/-- The supremum over a finite family of labels (`ST_prec_sup`, `Step2Events.lean:76`, at `μ`). -/
private theorem emn2Exp_precL_sup {d : ℕ} (sz : Sizes d) (μ : Measure sz.SeqΩ) {V : ℕ → Type}
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)] (ξ : ∀ n, V n → sz.SeqΩ → ℝ) (ζ : ℕ → ℝ)
    (h : PrecL sz μ (U := V) ξ (fun n _ _ => ζ n)) :
    PrecL sz μ (U := fun _ => Unit)
      (fun n _ ω => Finset.univ.sup' Finset.univ_nonempty (fun v : V n => ξ n v ω))
      (fun n _ _ => ζ n) := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with n hn
  refine le_trans (measure_mono ?_) hn
  rintro ω ⟨_, hu⟩
  obtain ⟨v, -, hv⟩ := (Finset.lt_sup'_iff Finset.univ_nonempty).1 hu
  exact ⟨v, hv⟩

end CarrierFacts

/-! ## 6. The near case `|a - b| ≤ ℓ†_t`: the first estimate with the truncated profile -/

section Near

variable {d : ℕ} (sz : Sizes d)

/-- `Ψ'_n(r)²` before the cap: `W^{-d}(B_{t, r ∧ ℓ⁺} + W^{-D})` (`3_5:833-836`: the truncated profile
`(W^{-d} B_{t, r ∧ ℓ})^{1/2}`, with `+ W^{-D}` so that `W^{-d} 𝒯̃^ℓ_{t,D}(r) ≤ Ψ'(r)²` holds for every
`r`, and `ℓ⁺ = max (ℓ, 0)` so that the profile is defined for every `n`). -/
def emn2ExpPsiSq (t ℓ : ℕ → ℝ) (D : ℝ) (n r : ℕ) : ℝ :=
  (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
    (BparamR d (sz.L n) (sz.lam n) (t n) (min (r : ℝ) (max (ℓ n) 0)) + ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **The truncated profile** `Ψ'_n(r) = min(√(W^{-d}(B_{t,r∧ℓ⁺} + W^{-D})), W^{-ε'})`: the cap
`W^{-ε'}` makes the clauses of `STPsiClass` that hold for every `n` true (it is eventually
inactive). -/
def emn2ExpPsi (t ℓ : ℕ → ℝ) (D ε' : ℝ) (n r : ℕ) : ℝ :=
  min (Real.sqrt (emn2ExpPsiSq sz t ℓ D n r)) (((sz.W n : ℕ) : ℝ) ^ (-ε'))

private theorem emn2Exp_psiSq_pos (t ℓ : ℕ → ℝ) {D : ℝ} (n r : ℕ) :
    0 < emn2ExpPsiSq sz t ℓ D n r := by
  unfold emn2ExpPsiSq
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hB := BparamR_nonneg (d := d) (L := sz.L n) (g := sz.lam n) (t := t n)
    (le_min (Nat.cast_nonneg r) (le_max_right (ℓ n) 0))
  have : 0 < ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_pos_of_pos hW _
  positivity

private theorem emn2Exp_psiSq_anti (t ℓ : ℕ → ℝ) {D : ℝ} (n : ℕ) {r r' : ℕ} (h : r ≤ r') :
    emn2ExpPsiSq sz t ℓ D n r' ≤ emn2ExpPsiSq sz t ℓ D n r := by
  unfold emn2ExpPsiSq
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hr : 0 ≤ min (r : ℝ) (max (ℓ n) 0) := le_min (Nat.cast_nonneg r) (le_max_right (ℓ n) 0)
  have hle : min (r : ℝ) (max (ℓ n) 0) ≤ min (r' : ℝ) (max (ℓ n) 0) :=
    min_le_min_right _ (by exact_mod_cast h)
  have h1 := BparamR_antitone (d := d) (L := sz.L n) (g := sz.lam n) (t := t n) hr hle
  have hWd : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := inv_nonneg.mpr (by positivity)
  exact mul_le_mul_of_nonneg_left (by linarith) hWd

private theorem emn2Exp_psiSq_ratio (t ℓ : ℕ → ℝ) {D : ℝ} (n : ℕ) {r₁ r₂ : ℕ} (h1 : 1 ≤ r₁)
    (h12 : r₁ ≤ r₂) :
    emn2ExpPsiSq sz t ℓ D n r₁ ≤ ((r₂ : ℝ) / r₁) ^ (d - 2) * emn2ExpPsiSq sz t ℓ D n r₂ := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := inv_nonneg.mpr (by positivity)
  have hr1 : (1 : ℝ) ≤ r₁ := by exact_mod_cast h1
  have hr12 : (r₁ : ℝ) ≤ r₂ := by exact_mod_cast h12
  have hq : 1 ≤ (r₂ : ℝ) / r₁ := by rw [le_div_iff₀ (by linarith)]; linarith
  set q : ℝ := (r₂ : ℝ) / r₁ with hqdef
  have hqr : q * r₁ = r₂ := by rw [hqdef]; field_simp
  set ℓp : ℝ := max (ℓ n) 0 with hℓp
  have hℓp0 : 0 ≤ ℓp := le_max_right _ _
  have hρ1 : 0 ≤ min (r₁ : ℝ) ℓp := le_min (by linarith) hℓp0
  have hρ12 : min (r₁ : ℝ) ℓp ≤ min (r₂ : ℝ) ℓp := min_le_min_right _ hr12
  have hyq : min (r₂ : ℝ) ℓp + 1 ≤ q * (min (r₁ : ℝ) ℓp + 1) := by
    by_cases hc : (r₁ : ℝ) ≤ ℓp
    · rw [min_eq_left hc]
      have : min (r₂ : ℝ) ℓp ≤ r₂ := min_le_left _ _
      nlinarith
    · push Not at hc
      rw [min_eq_right hc.le]
      have : min (r₂ : ℝ) ℓp ≤ ℓp := min_le_right _ _
      nlinarith
  have hB := emn2Exp_bparamR_ratio (d := d) (L := sz.L n) (g := sz.lam n) (t := t n) hρ1 hρ12 hq hyq
  have hqm : 1 ≤ q ^ (d - 2) := one_le_pow₀ hq
  have hw : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW.le _
  unfold emn2ExpPsiSq
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (BparamR d (sz.L n) (sz.lam n) (t n) (min (r₁ : ℝ) ℓp) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (q ^ (d - 2) * (BparamR d (sz.L n) (sz.lam n) (t n)
          (min (r₂ : ℝ) ℓp) + ((sz.W n : ℕ) : ℝ) ^ (-D))) := by
        apply mul_le_mul_of_nonneg_left _ hWd
        nlinarith
    _ = _ := by ring

private theorem emn2Exp_psiSq_zero_le (t ℓ : ℕ → ℝ) {D : ℝ} (n : ℕ) {r C : ℕ} (hr : r ≤ C) :
    emn2ExpPsiSq sz t ℓ D n 0 ≤ ((C : ℝ) + 1) ^ (d - 2) * emn2ExpPsiSq sz t ℓ D n r := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := inv_nonneg.mpr (by positivity)
  set ℓp : ℝ := max (ℓ n) 0 with hℓp
  have hℓp0 : 0 ≤ ℓp := le_max_right _ _
  have hρ : 0 ≤ min (r : ℝ) ℓp := le_min (Nat.cast_nonneg r) hℓp0
  have hρC : min (r : ℝ) ℓp ≤ C := (min_le_left _ _).trans (by exact_mod_cast hr)
  have hB := emn2Exp_bparamR_ratio (d := d) (L := sz.L n) (g := sz.lam n) (t := t n) (x := 0)
    (y := min (r : ℝ) ℓp) (q := min (r : ℝ) ℓp + 1) le_rfl hρ (by linarith) (by linarith)
  have hqC : (min (r : ℝ) ℓp + 1) ^ (d - 2) ≤ ((C : ℝ) + 1) ^ (d - 2) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hqm : 1 ≤ ((C : ℝ) + 1) ^ (d - 2) := one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) C; linarith)
  have hBr := BparamR_nonneg (d := d) (L := sz.L n) (g := sz.lam n) (t := t n) hρ
  have hw : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW.le _
  have e0 : min (((0 : ℕ) : ℝ)) ℓp = 0 := by simp [hℓp0]
  unfold emn2ExpPsiSq
  rw [e0]
  have hB' : BparamR d (sz.L n) (sz.lam n) (t n) 0 ≤
      ((C : ℝ) + 1) ^ (d - 2) * BparamR d (sz.L n) (sz.lam n) (t n) (min (r : ℝ) ℓp) :=
    hB.trans (mul_le_mul_of_nonneg_right hqC hBr)
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (BparamR d (sz.L n) (sz.lam n) (t n) 0 +
        ((sz.W n : ℕ) : ℝ) ^ (-D))
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((C : ℝ) + 1) ^ (d - 2) *
          (BparamR d (sz.L n) (sz.lam n) (t n) (min (r : ℝ) ℓp) +
            ((sz.W n : ℕ) : ℝ) ^ (-D))) := by
        apply mul_le_mul_of_nonneg_left _ hWd
        nlinarith
    _ = _ := by ring

/-- `Ψ'_n(0)² ≥ W^{-d} B_{t,0} = Bctl` (the `+ W^{-D}` only adds). -/
private theorem emn2Exp_psiSq_zero_ge (t ℓ : ℕ → ℝ) {D : ℝ} (n : ℕ) :
    sz.Bctl n (t n) ≤ emn2ExpPsiSq sz t ℓ D n 0 := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hw : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW.le _
  have hWd : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := inv_nonneg.mpr (by positivity)
  have e0 : min (((0 : ℕ) : ℝ)) (max (ℓ n) 0) = 0 := by simp
  unfold emn2ExpPsiSq Sizes.Bctl
  rw [e0]
  have : BparamR d (sz.L n) (sz.lam n) (t n) 0 = Bparam d (sz.L n) (sz.lam n) (t n) 0 := by
    have := BparamR_natCast (d := d) (L := sz.L n) (g := sz.lam n) (t := t n) 0
    simpa using this
  rw [this]
  exact mul_le_mul_of_nonneg_left (by linarith) hWd

/-- **The truncated profile is in the class `STPsiClass`** of `(eq:Psi)` (`3_5:385-393`) at the
exponent `ε' ≤ d/2`: the four clauses (positivity and the cap, monotonicity, the window with
`W^{-d/2} ≲ Ψ'(0) ≍ Ψ'(r)` for `r ≤ C`, the ratio with `C₁ = 2`, `C₂ = d + 2`).  The window uses
`cB W^{-d} ≤ W^{-d} B_{t,0}` (eventually). -/
private theorem emn2Exp_psiClass (t ℓ : ℕ → ℝ) {D ε' cB : ℝ} (hcB : 0 < cB) (hε'd : ε' ≤ (d : ℝ) / 2)
    (hB : ∀ᶠ n in atTop, cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n (t n)) :
    STPsiClass sz ε' (emn2ExpPsi sz t ℓ D ε') := by
  have hWpos : ∀ n, (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.W_pos n
  have hW1 : ∀ n, (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.W_pos n
  refine ⟨fun n r => ⟨?_, ?_⟩, fun n r r' hrr => ?_, fun C => ?_, ?_⟩
  · unfold emn2ExpPsi
    exact lt_min (Real.sqrt_pos.mpr (emn2Exp_psiSq_pos sz t ℓ n r))
      (Real.rpow_pos_of_pos (hWpos n) _)
  · exact min_le_right _ _
  · unfold emn2ExpPsi
    exact min_le_min (Real.sqrt_le_sqrt (emn2Exp_psiSq_anti sz t ℓ n hrr)) le_rfl
  · -- the window
    have hCp : (0 : ℝ) < ((C : ℝ) + 1) ^ (d - 2) := pow_pos (by positivity) _
    set c : ℝ := min 1 (min cB (((C : ℝ) + 1) ^ (d - 2))⁻¹) with hc
    have hc0 : 0 < c := lt_min one_pos (lt_min hcB (inv_pos.mpr hCp))
    have hc1 : c ≤ 1 := min_le_left _ _
    have hcB' : c ≤ cB := (min_le_right _ _).trans (min_le_left _ _)
    have hcC : c ≤ (((C : ℝ) + 1) ^ (d - 2))⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨c, hc0, ?_⟩
    filter_upwards [hB] with n hBn
    have hW := hWpos n
    have hWd : 0 < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
    have hc2 : c ^ 2 ≤ c := by nlinarith
    constructor
    · have h1 : c * ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ emn2ExpPsi sz t ℓ D ε' n 0 := by
        unfold emn2ExpPsi
        refine le_min ?_ ?_
        · have h0 : 0 ≤ c * ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) := by
            have := Real.rpow_nonneg hW.le (-(d : ℝ) / 2); positivity
          have hsq : (c * ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 =
              c ^ 2 * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
            rw [mul_pow, ST_rpow_neg_half hW.le, ← Real.sqrt_eq_rpow,
              Real.sq_sqrt (inv_nonneg.mpr hWd.le)]
          have hle : c ^ 2 * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ emn2ExpPsiSq sz t ℓ D n 0 := by
            calc c ^ 2 * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
                  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hWd.le); linarith
              _ ≤ sz.Bctl n (t n) := hBn
              _ ≤ _ := emn2Exp_psiSq_zero_ge sz t ℓ n
          calc c * ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)
              = Real.sqrt ((c * ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) ^ 2) :=
                (Real.sqrt_sq h0).symm
            _ ≤ Real.sqrt (emn2ExpPsiSq sz t ℓ D n 0) := Real.sqrt_le_sqrt (hsq ▸ hle)
        · have h1 : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε') :=
            Real.rpow_le_rpow_of_exponent_le (hW1 n) (by linarith)
          have h2 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg hW.le _
          nlinarith
      calc ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)
          = c⁻¹ * (c * ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) := by field_simp
        _ ≤ c⁻¹ * emn2ExpPsi sz t ℓ D ε' n 0 :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hc0.le)
    · intro r hr
      unfold emn2ExpPsi
      refine le_min ?_ ?_
      · have h0 : 0 ≤ c * Real.sqrt (emn2ExpPsiSq sz t ℓ D n 0) := by positivity
        have h2 : c ^ 2 * emn2ExpPsiSq sz t ℓ D n 0 ≤ emn2ExpPsiSq sz t ℓ D n r := by
          have h3 := emn2Exp_psiSq_zero_le sz t ℓ (D := D) n hr
          have h4 : c ^ 2 * (((C : ℝ) + 1) ^ (d - 2)) ≤ 1 := by
            calc c ^ 2 * (((C : ℝ) + 1) ^ (d - 2)) ≤ c * (((C : ℝ) + 1) ^ (d - 2)) := by
                  nlinarith
              _ ≤ (((C : ℝ) + 1) ^ (d - 2))⁻¹ * (((C : ℝ) + 1) ^ (d - 2)) :=
                  mul_le_mul_of_nonneg_right hcC hCp.le
              _ = 1 := inv_mul_cancel₀ hCp.ne'
          have hpos := emn2Exp_psiSq_pos sz t ℓ (D := D) n r
          calc c ^ 2 * emn2ExpPsiSq sz t ℓ D n 0
              ≤ c ^ 2 * (((C : ℝ) + 1) ^ (d - 2) * emn2ExpPsiSq sz t ℓ D n r) :=
                mul_le_mul_of_nonneg_left h3 (sq_nonneg c)
            _ = (c ^ 2 * (((C : ℝ) + 1) ^ (d - 2))) * emn2ExpPsiSq sz t ℓ D n r := by ring
            _ ≤ 1 * emn2ExpPsiSq sz t ℓ D n r := mul_le_mul_of_nonneg_right h4 hpos.le
            _ = _ := one_mul _
        calc c * min (Real.sqrt (emn2ExpPsiSq sz t ℓ D n 0)) (((sz.W n : ℕ) : ℝ) ^ (-ε'))
            ≤ c * Real.sqrt (emn2ExpPsiSq sz t ℓ D n 0) :=
              mul_le_mul_of_nonneg_left (min_le_left _ _) hc0.le
          _ = Real.sqrt (c ^ 2 * emn2ExpPsiSq sz t ℓ D n 0) := by
              rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc0.le]
          _ ≤ Real.sqrt (emn2ExpPsiSq sz t ℓ D n r) := Real.sqrt_le_sqrt h2
      · have hw : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε') := Real.rpow_nonneg hW.le _
        calc c * min (Real.sqrt (emn2ExpPsiSq sz t ℓ D n 0)) (((sz.W n : ℕ) : ℝ) ^ (-ε'))
            ≤ c * ((sz.W n : ℕ) : ℝ) ^ (-ε') :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) hc0.le
          _ ≤ 1 * ((sz.W n : ℕ) : ℝ) ^ (-ε') := mul_le_mul_of_nonneg_right hc1 hw
          _ = _ := one_mul _
  · -- the ratio
    refine ⟨2, (d : ℝ) + 2, by norm_num, by have := Nat.cast_nonneg (α := ℝ) d; linarith,
      fun n r₁ r₂ h1 h12 => ?_⟩
    have hr1 : (1 : ℝ) ≤ r₁ := by exact_mod_cast h1
    have hr12 : (r₁ : ℝ) ≤ r₂ := by exact_mod_cast h12
    have hq1 : 1 ≤ (r₂ : ℝ) / r₁ := by rw [le_div_iff₀ (by linarith)]; linarith
    set q : ℝ := ((r₂ : ℝ) / r₁) ^ (d - 2) with hq
    have hq1' : 1 ≤ q := one_le_pow₀ hq1
    have hsq1 : 1 ≤ Real.sqrt q := by
      calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt q := Real.sqrt_le_sqrt hq1'
    have hΨ2 : 0 < emn2ExpPsi sz t ℓ D ε' n r₂ := by
      unfold emn2ExpPsi
      exact lt_min (Real.sqrt_pos.mpr (emn2Exp_psiSq_pos sz t ℓ n r₂))
        (Real.rpow_pos_of_pos (hWpos n) _)
    have ha : emn2ExpPsiSq sz t ℓ D n r₁ ≤ q * emn2ExpPsiSq sz t ℓ D n r₂ :=
      emn2Exp_psiSq_ratio sz t ℓ n h1 h12
    have ha' : emn2ExpPsiSq sz t ℓ D n r₂ ≤ emn2ExpPsiSq sz t ℓ D n r₁ :=
      emn2Exp_psiSq_anti sz t ℓ n h12
    have hmain : emn2ExpPsi sz t ℓ D ε' n r₁ ≤ Real.sqrt q * emn2ExpPsi sz t ℓ D ε' n r₂ := by
      unfold emn2ExpPsi
      by_cases hc : Real.sqrt (emn2ExpPsiSq sz t ℓ D n r₂) ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε')
      · rw [min_eq_left hc]
        calc min (Real.sqrt (emn2ExpPsiSq sz t ℓ D n r₁)) (((sz.W n : ℕ) : ℝ) ^ (-ε'))
            ≤ Real.sqrt (emn2ExpPsiSq sz t ℓ D n r₁) := min_le_left _ _
          _ ≤ Real.sqrt (q * emn2ExpPsiSq sz t ℓ D n r₂) := Real.sqrt_le_sqrt ha
          _ = Real.sqrt q * Real.sqrt (emn2ExpPsiSq sz t ℓ D n r₂) :=
              Real.sqrt_mul (by linarith) _
      · push Not at hc
        have hc1 : ((sz.W n : ℕ) : ℝ) ^ (-ε') ≤ Real.sqrt (emn2ExpPsiSq sz t ℓ D n r₁) :=
          hc.le.trans (Real.sqrt_le_sqrt ha')
        rw [min_eq_right hc.le, min_eq_right hc1]
        have hw : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε') := Real.rpow_nonneg (hWpos n).le _
        nlinarith
    have hq2 : q ≤ ((r₂ : ℝ) / r₁) ^ ((d : ℝ) + 2) := by
      rw [hq, ← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le hq1
      have : ((d - 2 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.sub_le d 2
      linarith
    have hpow1 : 1 ≤ ((r₂ : ℝ) / r₁) ^ ((d : ℝ) + 2) := Real.one_le_rpow hq1 (by positivity)
    have hsqq : Real.sqrt q ≤ q := by
      rw [Real.sqrt_le_iff]; exact ⟨by linarith, by nlinarith⟩
    rw [div_le_iff₀ hΨ2]
    calc emn2ExpPsi sz t ℓ D ε' n r₁ ≤ Real.sqrt q * emn2ExpPsi sz t ℓ D ε' n r₂ := hmain
      _ ≤ (2 * ((r₂ : ℝ) / r₁) ^ ((d : ℝ) + 2)) * emn2ExpPsi sz t ℓ D ε' n r₂ := by
          apply mul_le_mul_of_nonneg_right _ hΨ2.le
          linarith

/-- **`W^{-d} 𝒯̃^ℓ_{t,D}(r) ≤ Ψ'(r)²`** (`3_5:833-836`, second fact, for every `r`): from `𝒯 ≤ B`, the
`+ W^{-D}` of `Ψ'` and the cap `W^{-2ε'}` (`ST_prof_le_Bctl`, `Bctl ≤ N^{-c} ≤ W^{-dc}`). -/
private theorem emn2Exp_prof_le_psi (n : ℕ) (t ℓ : ℕ → ℝ) {D ε' cB c : ℝ} (hcB : 0 < cB) (hD : 0 < D)
    (hε' : ε' ≤ (d : ℝ) * c / 4) (hc : 0 ≤ c) (hℓn : 0 ≤ ℓ n)
    (hb : cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n (t n))
    (hbN : sz.Bctl n (t n) ≤ ((sz.size n : ℕ) : ℝ) ^ (-c))
    (hWbig : 1 + cB⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) * c / 2)) (a b : Zd d (sz.L n)) :
    STprof sz n (t n) D (ℓ n) a b ≤
      (emn2ExpPsi sz t ℓ D ε' n (zdistInf d (sz.L n) (a - b))) ^ 2 := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : 0 < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
  set r : ℕ := zdistInf d (sz.L n) (a - b) with hr
  have hP0 : 0 ≤ STprof sz n (t n) D (ℓ n) a b := (ST_STprof_pos sz n _ _ _ a b).le
  -- `P ≤ Ψ'²` before the cap
  have h1 : STprof sz n (t n) D (ℓ n) a b ≤ emn2ExpPsiSq sz t ℓ D n r := by
    unfold STprof emn2ExpPsiSq tailW
    rw [max_eq_left hℓn]
    have hρ : 0 ≤ min (r : ℝ) (ℓ n) := le_min (Nat.cast_nonneg r) hℓn
    have hT := emn2Exp_tailT_le_bparamR (d := d) (L := sz.L n) (g := sz.lam n) (t := t n) hρ
    have hBr := BparamR_nonneg (d := d) (L := sz.L n) (g := sz.lam n) (t := t n) hρ
    have hw : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW.le _
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hWd.le)
    exact max_le (by linarith) (by linarith)
  -- `P ≤ W^{-2ε'}`
  have h2 : STprof sz n (t n) D (ℓ n) a b ≤ (((sz.W n : ℕ) : ℝ) ^ (-ε')) ^ 2 := by
    have h3 := ST_prof_le_Bctl sz n hcB hℓn hD hb a b
    have hBpos : 0 ≤ sz.Bctl n (t n) := (mul_nonneg hcB.le (inv_nonneg.mpr hWd.le)).trans hb
    have h4 : sz.Bctl n (t n) ≤ ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c)) :=
      hbN.trans (ST_size_rpow_neg_le sz n hc)
    have h5 : (1 + cB⁻¹) * sz.Bctl n (t n) ≤ ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c / 2)) := by
      calc (1 + cB⁻¹) * sz.Bctl n (t n)
          ≤ ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) * c / 2) * ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c)) :=
            mul_le_mul hWbig h4 hBpos (Real.rpow_nonneg hW.le _)
        _ = ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c / 2)) := by
            rw [← Real.rpow_add hW]; congr 1; ring
    have h6 : ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c / 2)) ≤ ((sz.W n : ℕ) : ℝ) ^ (2 * (-ε')) :=
      Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
    rw [ST_rpow_sq hW.le]
    exact h3.trans (h5.trans h6)
  have hs1 : Real.sqrt (STprof sz n (t n) D (ℓ n) a b) ≤ Real.sqrt (emn2ExpPsiSq sz t ℓ D n r) :=
    Real.sqrt_le_sqrt h1
  have hs2 : Real.sqrt (STprof sz n (t n) D (ℓ n) a b) ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε') := by
    calc Real.sqrt (STprof sz n (t n) D (ℓ n) a b)
        ≤ Real.sqrt ((((sz.W n : ℕ) : ℝ) ^ (-ε')) ^ 2) := Real.sqrt_le_sqrt h2
      _ = ((sz.W n : ℕ) : ℝ) ^ (-ε') := Real.sqrt_sq (Real.rpow_nonneg hW.le _)
  have hs : Real.sqrt (STprof sz n (t n) D (ℓ n) a b) ≤ emn2ExpPsi sz t ℓ D ε' n r := le_min hs1 hs2
  calc STprof sz n (t n) D (ℓ n) a b = (Real.sqrt (STprof sz n (t n) D (ℓ n) a b)) ^ 2 :=
        (Real.sq_sqrt hP0).symm
    _ ≤ (emn2ExpPsi sz t ℓ D ε' n r) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2

/-- **`Ψ'(r)² ≤ 2 exp((log W)^{7/8}) W^{-d} 𝒯̃^ℓ_{t,D}(r)` for `r ≤ ℓ†_t`** (`3_5:833-836`, first fact):
`B_{t,ρ} = 𝒯_t(ρ) exp((ρ/ℓ_t)^{1/2})` and `(ρ/ℓ_t)^{1/2} ≤ (log W)^{7/8}` for `ρ ≤ ℓ†_t`. -/
private theorem emn2Exp_psi_sq_le (n : ℕ) (t ℓ : ℕ → ℝ) {D ε' : ℝ} (hℓn : 0 ≤ ℓ n) {r : ℕ}
    (hr : (r : ℝ) ≤ emn2ExpEllDag sz n (t n)) :
    (emn2ExpPsi sz t ℓ D ε' n r) ^ 2 ≤
      2 * Real.exp (Real.sqrt (Real.log ((sz.W n : ℕ) : ℝ) ^ ((7 : ℝ) / 4))) *
        emn2ExpPf sz n (t n) D (ℓ n) r := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : 0 < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  set e : ℝ := Real.exp (Real.sqrt (Real.log ((sz.W n : ℕ) : ℝ) ^ ((7 : ℝ) / 4))) with he
  have he1 : 1 ≤ e := Real.one_le_exp (Real.sqrt_nonneg _)
  have hw : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW.le _
  have h0 : (emn2ExpPsi sz t ℓ D ε' n r) ^ 2 ≤ emn2ExpPsiSq sz t ℓ D n r := by
    calc (emn2ExpPsi sz t ℓ D ε' n r) ^ 2 ≤ (Real.sqrt (emn2ExpPsiSq sz t ℓ D n r)) ^ 2 :=
          pow_le_pow_left₀ (le_min (Real.sqrt_nonneg _) (Real.rpow_nonneg hW.le _))
            (min_le_left _ _) 2
      _ = _ := Real.sq_sqrt (emn2Exp_psiSq_pos sz t ℓ n r).le
  refine h0.trans ?_
  unfold emn2ExpPsiSq emn2ExpPf tailW
  rw [max_eq_left hℓn]
  have hρ : 0 ≤ min (r : ℝ) (ℓ n) := le_min (Nat.cast_nonneg r) hℓn
  have hX : min (r : ℝ) (ℓ n) ≤
      Real.log ((sz.W n : ℕ) : ℝ) ^ ((7 : ℝ) / 4) * ellT (sz.L n) (sz.lam n) (t n) :=
    (min_le_left _ _).trans hr
  have hB := emn2Exp_bparamR_le_exp_tailT (d := d) (L := sz.L n) (g := sz.lam n) (t := t n) hL1
    hρ hX
  have hT0 := tailT_nonneg (d := d) (L := sz.L n) (g := sz.lam n) (t := t n) hρ
  have hmax : e * (tailT d (sz.L n) (sz.lam n) (t n) (min (r : ℝ) (ℓ n)) + ((sz.W n : ℕ) : ℝ) ^ (-D)) ≤
      2 * e * max (tailT d (sz.L n) (sz.lam n) (t n) (min (r : ℝ) (ℓ n))) (((sz.W n : ℕ) : ℝ) ^ (-D)) := by
    have : tailT d (sz.L n) (sz.lam n) (t n) (min (r : ℝ) (ℓ n)) + ((sz.W n : ℕ) : ℝ) ^ (-D) ≤
        2 * max (tailT d (sz.L n) (sz.lam n) (t n) (min (r : ℝ) (ℓ n))) (((sz.W n : ℕ) : ℝ) ^ (-D)) := by
      have := le_max_left (tailT d (sz.L n) (sz.lam n) (t n) (min (r : ℝ) (ℓ n))) (((sz.W n : ℕ) : ℝ) ^ (-D))
      have := le_max_right (tailT d (sz.L n) (sz.lam n) (t n) (min (r : ℝ) (ℓ n))) (((sz.W n : ℕ) : ℝ) ^ (-D))
      linarith
    calc e * (tailT d (sz.L n) (sz.lam n) (t n) (min (r : ℝ) (ℓ n)) + ((sz.W n : ℕ) : ℝ) ^ (-D))
        ≤ e * (2 * max (tailT d (sz.L n) (sz.lam n) (t n) (min (r : ℝ) (ℓ n))) (((sz.W n : ℕ) : ℝ) ^ (-D))) :=
          mul_le_mul_of_nonneg_left this (by linarith)
      _ = _ := by ring
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (BparamR d (sz.L n) (sz.lam n) (t n) (min (r : ℝ) (ℓ n)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (e * (tailT d (sz.L n) (sz.lam n) (t n) (min (r : ℝ) (ℓ n)) +
          ((sz.W n : ℕ) : ℝ) ^ (-D))) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hWd.le)
        nlinarith
    _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (2 * e * max (tailT d (sz.L n) (sz.lam n) (t n) (min (r : ℝ) (ℓ n)))
          (((sz.W n : ℕ) : ℝ) ^ (-D))) := mul_le_mul_of_nonneg_left hmax (inv_nonneg.mpr hWd.le)
    _ = 2 * e * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * max (tailT d (sz.L n) (sz.lam n) (t n) (min (r : ℝ) (ℓ n)))
          (((sz.W n : ℕ) : ℝ) ^ (-D))) := by ring

/-- `Ψ'(0)² ≤ (1 + cB⁻¹) W^{-d} B_{t,0}`. -/
private theorem emn2Exp_psi0_le (n : ℕ) (t ℓ : ℕ → ℝ) {D ε' cB : ℝ} (hcB : 0 < cB) (hD : 0 < D)
    (hb : cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n (t n)) :
    (emn2ExpPsi sz t ℓ D ε' n 0) ^ 2 ≤ (1 + cB⁻¹) * sz.Bctl n (t n) := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : 0 < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
  have h0 : (emn2ExpPsi sz t ℓ D ε' n 0) ^ 2 ≤ emn2ExpPsiSq sz t ℓ D n 0 := by
    calc (emn2ExpPsi sz t ℓ D ε' n 0) ^ 2 ≤ (Real.sqrt (emn2ExpPsiSq sz t ℓ D n 0)) ^ 2 :=
          pow_le_pow_left₀ (le_min (Real.sqrt_nonneg _) (Real.rpow_nonneg hW.le _))
            (min_le_left _ _) 2
      _ = _ := Real.sq_sqrt (emn2Exp_psiSq_pos sz t ℓ n 0).le
  refine h0.trans ?_
  have e0 : min (((0 : ℕ) : ℝ)) (max (ℓ n) 0) = 0 := by simp
  have hB0 : BparamR d (sz.L n) (sz.lam n) (t n) 0 = Bparam d (sz.L n) (sz.lam n) (t n) 0 := by
    have := BparamR_natCast (d := d) (L := sz.L n) (g := sz.lam n) (t := t n) 0
    simpa using this
  have hwD : ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  unfold emn2ExpPsiSq
  rw [e0, hB0]
  have hbB : sz.Bctl n (t n) = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) (t n) 0 := rfl
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (Bparam d (sz.L n) (sz.lam n) (t n) 0 + ((sz.W n : ℕ) : ℝ) ^ (-D))
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (Bparam d (sz.L n) (sz.lam n) (t n) 0 + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hWd.le)
    _ = sz.Bctl n (t n) + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by rw [hbB]; ring
    _ ≤ sz.Bctl n (t n) + cB⁻¹ * sz.Bctl n (t n) := by
        have h1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ cB⁻¹ * sz.Bctl n (t n) := by
          rw [inv_mul_eq_div, le_div_iff₀ hcB]
          linarith
        linarith
    _ = (1 + cB⁻¹) * sz.Bctl n (t n) := by ring

/-- `√(x^{7/4}) = x^{7/8}` for `x ≥ 0`. -/
private theorem emn2Exp_sqrt_rpow {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (x ^ ((7 : ℝ) / 4)) = x ^ ((7 : ℝ) / 8) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]; norm_num

variable (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
  {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop}
  {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz} {T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ}
  {Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (u : ℝ), sz.SeqΩ →
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
  {ζf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (u : ℝ), ℂ}

/-- **The near case of `(eq:MG_conclusion3)` over a carrier** (`3_5:829-836`, first case `|a - b| ≤ ℓ†_t`): under the
premises of `STEMn2ExpgL` the quadratic variation loop satisfies, on the pairs with `|a - b| ≤ ℓ†_t`,
`(𝓔⊗𝓔)^{M,(2;k)}_{t,σ,a,a} ≺ η_t^{-1} (W^{-d} B_{t,0})^{1/2} (W^{-d} 𝒯̃^ℓ_{t,D}(|a-b|))²`.
Proof: `stEMn2PolygL_of` (`(eq:MG_conclusion)`) at the truncated profile `emn2ExpPsi`, which is in the
class `STPsiClass` (`emn2Exp_psiClass`), satisfies `STLWassm` and `STInitialGT2` (from
`STLWassmExp` at the same `D`, `STInitialGT2.1`) and is comparable to `W^{-d} 𝒯̃` for `r ≤ ℓ†_t`
(`emn2Exp_psi_sq_le`: the loss is `exp(2 (log W)^{7/8}) = N^{o(1)}`).  The premises `Ψ` and its window
are not used. -/
theorem emn2Exp_nearg (hF : emn2ExpFacts d Flow mk T0 Hf ζf) :
    emn2ExpPrem d law Flow mk T0 (fun sz z t ℓ D =>
      PrecL sz (law sz) (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
        (fun n p ω => if (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℝ) ≤
            emn2ExpEllDag sz n (t n) then
          ‖STEEg (mk sz z) n (t n) p.1 p.2.1 p.2.2 ω‖ else 0)
        (fun n p _ => ((mk sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
          (STprof sz n (t n) D (ℓ n) (p.2.2 0) (p.2.2 1)) ^ 2)) := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ Ψ _hΨ hI ℓ hℓ hA D hD
  classical
  obtain ⟨hadm, hR, -⟩ := hF.1 κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow
  obtain ⟨-, -, cB, c, hcB, hc, hbd⟩ := hF.2 κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hd : 0 < d := emn2Exp_d_pos sz hsz
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hWt := ST_W_tendsto sz hsz hadm.1 hadm.2.2.2.1
  have hη : ∀ n, 0 < (mk sz z).eta n (t n) := by
    intro n
    obtain ⟨-, h1, h2, -⟩ := hR n (t n) (ht0 n) (htT n)
    rw [← h2]; exact h1
  have hW1 : ∀ n, (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.W_pos n
  have hWpos : ∀ n, (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.W_pos n
  -- the size data `cB W^{-d} ≤ W^{-d} B_{t,0} ≤ N^{-c}`
  have hBt : ∀ᶠ n in atTop, cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n (t n) ∧
      sz.Bctl n (t n) ≤ ((sz.size n : ℕ) : ℝ) ^ (-c) :=
    hbd.mono fun n hn => hn (t n) (ht0 n) (htT n)
  -- the exponent `ε'`
  obtain ⟨ε', hε'def⟩ : ∃ ε' : ℝ, ε' = min ε₀ (min ((d : ℝ) * c / 4) ((d : ℝ) / 2)) := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by
    rw [hε'def]; exact lt_min hε₀ (lt_min (by positivity) (by positivity))
  have hε'1 : ε' ≤ ε₀ := by rw [hε'def]; exact min_le_left _ _
  have hε'2 : ε' ≤ (d : ℝ) * c / 4 := by
    rw [hε'def]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hε'3 : ε' ≤ (d : ℝ) / 2 := by
    rw [hε'def]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hWbig : ∀ᶠ n in atTop, 1 + cB⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) * c / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < (d : ℝ) * c / 2)).comp hWt).eventually
      (eventually_ge_atTop _)
  -- the truncated profile
  have hcls : STPsiClass sz ε' (emn2ExpPsi sz t ℓ D ε') :=
    emn2Exp_psiClass sz t ℓ hcB hε'3 (hBt.mono fun n hn => hn.1)
  have hPle : ∀ᶠ n in atTop, ∀ a b : Zd d (sz.L n), STprof sz n (t n) D (ℓ n) a b ≤
      (emn2ExpPsi sz t ℓ D ε' n (zdistInf d (sz.L n) (a - b))) ^ 2 := by
    filter_upwards [hℓ, hBt, hWbig] with n hℓn hBn hWb a b
    exact emn2Exp_prof_le_psi sz n t ℓ hcB hD hε'2 hc.le hℓn.1 hBn.1 hBn.2 hWb a b
  have hPos : ∀ n r, 0 < emn2ExpPsi sz t ℓ D ε' n r := fun n r => (hcls.1 n r).1
  -- `STLWassm`
  have hA' : STLWassmgL (mk sz z) (law sz) t (emn2ExpPsi sz t ℓ D ε') := by
    refine emn2Exp_precL_mono sz (law sz) ?_ (hA D hD)
    filter_upwards [hPle] with n hn u ω
    exact hn _ _
  -- `STInitialGT2`
  have hI1 : PrecL sz (law sz) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖(mk sz z).GM n (t n) ω p.1 p.2‖)
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε')) := by
    refine emn2Exp_precL_mono sz (law sz) ?_ hI.1
    exact Eventually.of_forall fun n u ω =>
      Real.rpow_le_rpow_of_exponent_le (hW1 n) (by linarith)
  have hI2 : PrecL sz (law sz) (U := fun _ => Unit)
      (fun n _ ω => RBM.BA.STmaxLoop2g (mk sz z) n (t n) ω)
      (fun n _ _ => (emn2ExpPsi sz t ℓ D ε' n 0) ^ 2) := by
    have h1 := hA D hD
    have h2 := StochDomAt.precomp_param (V := fun n => Zd d (sz.L n) × Zd d (sz.L n)) h1
      (fun n p => ((⟨![false, true], by simp⟩ : {σ : Fin 2 → Bool // σ 0 ≠ σ 1}), ![p.1, p.2]))
    have h3 : PrecL sz (law sz) (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
        (fun n p ω => ‖(mk sz z).L n (t n) ![false, true] ![p.1, p.2] ω‖)
        (fun n _ _ => (emn2ExpPsi sz t ℓ D ε' n 0) ^ 2) := by
      refine emn2Exp_precL_mono sz (law sz) ?_ h2
      filter_upwards [hPle] with n hn u ω
      refine (hn _ _).trans ?_
      exact pow_le_pow_left₀ (hPos n _).le (hcls.2.1 n 0 _ (Nat.zero_le _)) 2
    exact emn2Exp_precL_sup sz (law sz) _ _ h3
  have hI' : STInitialGT2gL (mk sz z) (law sz) t ε' (fun n => emn2ExpPsi sz t ℓ D ε' n 0) := ⟨hI1, hI2⟩
  have hMain := stEMn2PolygL_of law hF.1 κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε' hε'0
    (emn2ExpPsi sz t ℓ D ε') hcls hI' hA'
  -- the conversion to the near region
  refine StochDomAt.of_subset hMain ?_
  intro τ hτ
  refine ⟨τ / 2, by positivity, ?_⟩
  have hQ := emn2Exp_ev_exp_pow sz hd hsz (c := 2) (a := (7 : ℝ) / 8) (δ := τ / 2) (by norm_num)
    (by norm_num) (by norm_num) (by positivity) (C := 4 * Real.sqrt (1 + cB⁻¹)) (by positivity)
  filter_upwards [hℓ, hBt, hQ] with n hℓn hBn hQn
  intro ω hω
  obtain ⟨p, hp⟩ := hω
  obtain ⟨k, σ, a⟩ := p
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hBpos : 0 ≤ sz.Bctl n (t n) :=
    (mul_nonneg hcB.le (inv_nonneg.mpr (pow_nonneg (hWpos n).le d))).trans hBn.1
  have hηn := hη n
  by_cases hnear : (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤ emn2ExpEllDag sz n (t n)
  · simp only [hnear, ↓reduceIte] at hp
    refine ⟨(k, σ, a), lt_of_le_of_lt ?_ hp⟩
    set r : ℕ := zdistInf d (sz.L n) (a 0 - a 1) with hr
    set A : ℝ := emn2ExpPsi sz t ℓ D ε' n 0 with hAdef
    set B : ℝ := emn2ExpPsi sz t ℓ D ε' n r with hBdef
    set P : ℝ := STprof sz n (t n) D (ℓ n) (a 0) (a 1) with hPdef
    set e : ℝ := Real.exp (Real.sqrt (Real.log ((sz.W n : ℕ) : ℝ) ^ ((7 : ℝ) / 4))) with he
    set s : ℝ := Real.sqrt (1 + cB⁻¹) with hs
    have hA0 : 0 < A := hPos n 0
    have hB0 : 0 < B := hPos n r
    have hP0 : 0 < P := ST_STprof_pos sz n _ _ _ _ _
    have he0 : 0 < e := Real.exp_pos _
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have h1 : B ^ 2 ≤ 2 * e * P := emn2Exp_psi_sq_le sz n t ℓ (D := D) (ε' := ε') hℓn.1 hnear
    have h0 := emn2Exp_psi0_le sz n t ℓ (D := D) (ε' := ε') hcB hD hBn.1
    have hbb : Real.sqrt (sz.Bctl n (t n)) = (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) :=
      Real.sqrt_eq_rpow _
    have hA' : A ≤ s * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) := by
      have h2 : A ^ 2 ≤ (s * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [mul_pow, hs, Real.sq_sqrt (by positivity), ← hbb, Real.sq_sqrt hBpos]
        exact h0
      exact le_of_sq_le_sq (by simpa using h2) (by positivity)
    have hB4 : B ^ 4 ≤ (2 * e * P) ^ 2 := by
      calc B ^ 4 = (B ^ 2) ^ 2 := by ring
        _ ≤ (2 * e * P) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have he2 : e ^ 2 = Real.exp (2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((7 : ℝ) / 8)) := by
      rw [he, ← Real.exp_nat_mul, emn2Exp_sqrt_rpow (Real.log_nonneg (hW1 n))]
      push_cast; ring_nf
    have hζ0 : 0 ≤ ((mk sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) * P ^ 2 := by
      positivity
    have hkey : ((mk sz z).eta n (t n))⁻¹ * A * B ^ 4 ≤
        (4 * s * Real.exp (2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((7 : ℝ) / 8))) *
          (((mk sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) * P ^ 2) := by
      rw [← he2]
      have hη0 : 0 ≤ ((mk sz z).eta n (t n))⁻¹ := inv_nonneg.mpr hηn.le
      calc ((mk sz z).eta n (t n))⁻¹ * A * B ^ 4
          ≤ ((mk sz z).eta n (t n))⁻¹ * (s * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ)) * (2 * e * P) ^ 2 := by
            apply mul_le_mul _ hB4 (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left hA' hη0
        _ = _ := by ring
    calc ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (((mk sz z).eta n (t n))⁻¹ * A * B ^ 4)
        ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
          ((((sz.size n : ℕ) : ℝ) ^ (τ / 2)) *
            (((mk sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) * P ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hNpos.le _)
          exact hkey.trans (mul_le_mul_of_nonneg_right hQn hζ0)
      _ = ((sz.size n : ℕ) : ℝ) ^ τ *
          (((mk sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) * P ^ 2) := by
          rw [← mul_assoc, ← Real.rpow_add hNpos]; congr 2; ring
  · exfalso
    simp only [hnear, ↓reduceIte] at hp
    have : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (((mk sz z).eta n (t n))⁻¹ *
        (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
        (STprof sz n (t n) D (ℓ n) (a 0) (a 1)) ^ 2) := by positivity
    linarith

/-- **The near case** at the band carrier: `emn2Exp_nearg` at `law = seqP`, `Flow = STFlow`,
`mk = bandFM ∘ STflowE`, `T0 = lemT` (`emn2Exp_bandFacts`), under its old name and statement. -/
theorem emn2Exp_near (d : ℕ) :
    ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℝ,
          (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n ∧
            Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
          STInitialGT2 sz (STflowE z) t ε₀ Ψ →
          ∀ ℓ : ℕ → ℝ, (∀ᶠ n in atTop, 0 ≤ ℓ n ∧ ℓ n ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 *
              ellT (sz.L n) (sz.lam n) (t n)) →
            (∀ D : ℝ, 0 < D → STLWassmExp sz (STflowE z) t D ℓ) →
            ∀ D : ℝ, 0 < D →
              Prec sz (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
                (fun n p ω => if (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℝ) ≤
                    emn2ExpEllDag sz n (t n) then
                  ‖STEEk sz n (STflowE z n) (t n) p.1 p.2.1 p.2.2 ω‖ else 0)
                (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
                  (STprof sz n (t n) D (ℓ n) (p.2.2 0) (p.2.2 1)) ^ 2) := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ Ψ hΨ hI ℓ hℓ hA D hD
  exact emn2Exp_nearg (fun sz => Sizes.seqP sz) (emn2Exp_bandFacts d) κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ Ψ hΨ hI ℓ hℓ hA D hD

end Near

/-! ## 7. The model-level six-loop sums and the cover for the cut `k` -/

section ModelSums

variable {d : ℕ} (sz : Sizes d)

/-- The cut `k = 1` is the cut `k = 0` with the two edges exchanged (`def:CALE`, `3_5:169-190`):
`emn2ExpSw 0 x = x`, `emn2ExpSw 1 x = (x₂, x₁)`. -/
def emn2ExpSw {α : Type*} (k : Fin 2) (x : Fin 2 → α) : Fin 2 → α :=
  if k = 0 then x else ![x 1, x 0]

/-- **`S̃₁`** at the model matrix (`(eq;S123)`, `3_5:842-845`), for the cut `k`, with the cutoff scale
`ℓ*_t` of `emn2ExpEllStar` and the scale `ℓ` of `(eq:LW_assm_exp)`. -/
def emn2ExpS1M (n : ℕ) (E u ℓ : ℝ) (k : Fin 2) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (ω : sz.SeqΩ) : ℝ :=
  emn2ExpS1 (sz.seqHflow n u ω) (zt E u) (emn2ExpEllStar sz n u) ℓ (emn2ExpSw k σ)
    (emn2ExpSw k a 0) (emn2ExpSw k a 1)

/-- **`S̃₂`** at the model matrix. -/
def emn2ExpS2M (n : ℕ) (E u ℓ : ℝ) (k : Fin 2) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (ω : sz.SeqΩ) : ℝ :=
  emn2ExpS2 (sz.seqHflow n u ω) (zt E u) (emn2ExpEllStar sz n u) ℓ (emn2ExpSw k σ)
    (emn2ExpSw k a 0) (emn2ExpSw k a 1)

/-- **`S̃₃`** at the model matrix (bounded in ST2-11). -/
def emn2ExpS3M (n : ℕ) (E u ℓ : ℝ) (k : Fin 2) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (ω : sz.SeqΩ) : ℝ :=
  emn2ExpS3 (sz.seqHflow n u ω) (zt E u) (emn2ExpEllStar sz n u) ℓ (emn2ExpSw k σ)
    (emn2ExpSw k a 0) (emn2ExpSw k a 1)

/-- **`S̃₁`** of a realization `(H, ζ)` of the loops (`emn2ExpS1` at the cut `k` and the scale `ℓ*_u`):
`emn2ExpS1M` is the case `H = seqHflow`, `ζ = zt`. -/
def emn2ExpS1g (n : ℕ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (ζ : ℂ)
    (u ℓ : ℝ) (k : Fin 2) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℝ :=
  emn2ExpS1 H ζ (emn2ExpEllStar sz n u) ℓ (emn2ExpSw k σ) (emn2ExpSw k a 0) (emn2ExpSw k a 1)

/-- **`S̃₂`** of a realization `(H, ζ)` of the loops. -/
def emn2ExpS2g (n : ℕ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (ζ : ℂ)
    (u ℓ : ℝ) (k : Fin 2) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℝ :=
  emn2ExpS2 H ζ (emn2ExpEllStar sz n u) ℓ (emn2ExpSw k σ) (emn2ExpSw k a 0) (emn2ExpSw k a 1)

/-- **`S̃₃`** of a realization `(H, ζ)` of the loops. -/
def emn2ExpS3g (n : ℕ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (ζ : ℂ)
    (u ℓ : ℝ) (k : Fin 2) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℝ :=
  emn2ExpS3 H ζ (emn2ExpEllStar sz n u) ℓ (emn2ExpSw k σ) (emn2ExpSw k a 0) (emn2ExpSw k a 1)

private lemma emn2Exp_STEEkM_zero_eq (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STEEkM sz n E u H 0 σ a = (((sz.W n : ℕ) : ℂ) ^ d) *
      ∑ c : Zd d (sz.L n), ∑ c' : Zd d (sz.L n), SB d (sz.L n) (sz.lam n) c c' *
        loopFine d (sz.L n) (sz.W n) H (zt E u)
          ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a 0, a 1, c', a 1, a 0, c] := by
  simp [STEEkM, STLM]

private lemma emn2Exp_STEEkM_one_eq (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STEEkM sz n E u H 1 σ a = STEEkM sz n E u H 0 ![σ 1, σ 0] ![a 1, a 0] := by
  simp [STEEkM, STLM]

/-- **The cover at the model level**: for both cuts `k`, `|(𝓔⊗𝓔)^{M,(2;k)}_{t,σ,a,a}| ≤ S̃₁ + S̃₂ + S̃₃`
(deterministic: `emn2Exp_cover` at the labels of the cut). -/
theorem emn2Exp_EEk_cover (n : ℕ) (E u ℓ : ℝ) (k : Fin 2) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    ‖STEEk sz n E u k σ a ω‖ ≤ emn2ExpS1M sz n E u ℓ k σ a ω + emn2ExpS2M sz n E u ℓ k σ a ω +
      emn2ExpS3M sz n E u ℓ k σ a ω := by
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  unfold emn2ExpS1M emn2ExpS2M emn2ExpS3M STEEk
  fin_cases k
  · simp only [Fin.zero_eta, emn2ExpSw, ite_true]
    rw [emn2Exp_STEEkM_zero_eq]
    exact emn2Exp_cover (sz.seqHflow n u ω) (zt E u) hL3 (sz.lam n) _ _ σ (a 0) (a 1)
  · have h10 : ¬ ((1 : Fin 2) = 0) := by decide
    simp only [Fin.mk_one, emn2ExpSw, h10, ite_false]
    rw [emn2Exp_STEEkM_one_eq, emn2Exp_STEEkM_zero_eq]
    simpa using emn2Exp_cover (sz.seqHflow n u ω) (zt E u) hL3 (sz.lam n) (emn2ExpEllStar sz n u) ℓ
      ![σ 1, σ 0] (a 1) (a 0)

end ModelSums


/-! ## 8. The far case `|a - b| > ℓ†_t`: `S̃₁ + S̃₂` -/

section Far12

/-- A failure event eventually contained in the failure event of another domination, over a
different parameter type (copy of the private `stochDomAt_of_subset'` of `EMn2Poly.lean:797`). -/
private theorem emn2Exp_stochDomAt_of_subset {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {size : ℕ → ℕ} {U U₁ : ℕ → Type*} {ξ ζ : ∀ l, U l → Ω → ℝ} {ξ₁ ζ₁ : ∀ l, U₁ l → Ω → ℝ}
    (h : StochDomAt P size ξ₁ ζ₁)
    (hsub : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop,
      badSetAt size ξ ζ τ l ⊆ badSetAt size ξ₁ ζ₁ τ' l) : StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := hsub τ hτ
  filter_upwards [hs, h τ' hτ' D hD] with l h1 h2
  exact (measure_mono h1).trans h2

variable {d : ℕ} (sz : Sizes d)

private lemma emn2Exp_sw_dist (n : ℕ) (k : Fin 2) (a : Fin 2 → Zd d (sz.L n)) :
    zdistInf d (sz.L n) (emn2ExpSw k a 0 - emn2ExpSw k a 1) = zdistInf d (sz.L n) (a 0 - a 1) := by
  fin_cases k
  · simp [emn2ExpSw]
  · have h10 : ¬ ((1 : Fin 2) = 0) := by decide
    simp only [Fin.mk_one, emn2ExpSw, h10, ite_false]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact emn2Exp_zdistInf_sub_comm d (sz.L n) _ _

variable (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
  {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop}
  {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz} {T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ}
  {Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (u : ℝ), sz.SeqΩ →
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
  {ζf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (u : ℝ), ℂ}

/-- **`S̃₁ + S̃₂` in the far case** (`3_5:848-863`, `(eq:pointwise_loop2)`, `(eq_S1tilde)`,
`(eq:boundwtS_1)`): under the premises of `STEMn2Exp`, on the pairs with `|a - b| > ℓ†_t`,
`(S̃₁ + S̃₂)_{t,σ,a} ≺ η_t^{-1} (W^{-d} B_{t,0})^{1/2} (W^{-d} 𝒯̃^ℓ_{t,D}(|a-b|))²`
(no random control `Ĵ` is needed).  Proof: on the good event of `(eq:LW_assm_exp)` at the exponent
`τ/5` every 2-loop of the pattern `(σ,-σ)` is `≤ N^{τ/5} W^{-d} 𝒯̃`, and `emn2Exp_S12_le` (contraction
inequality, 3-loop bound; no entry bound `(GijGEX)`) applies with `K_n = emn2ExpK`, whose hypothesis
`𝒯̃(|b-c'|) ≤ K_n 𝒯̃(|a-b|)` is `emn2Exp_profile_cmp`; the loss `2 · 3^d K_n √(1 + cB⁻¹) N^{τ/2}` is `≤ N^τ`
eventually.  The premises `Ψ`, its window, `STInitialGT2` and the upper bound on `ℓ` are not used. -/
theorem emn2Exp_far12g (hF : emn2ExpFacts d Flow mk T0 Hf ζf) :
    emn2ExpPrem d law Flow mk T0 (fun sz z t ℓ D =>
      PrecL sz (law sz) (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
        (fun n p ω => if emn2ExpEllDag sz n (t n) <
            (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℝ) then
          emn2ExpS1g sz n (Hf sz z n (t n) ω) (ζf sz z n (t n)) (t n) (ℓ n) p.1 p.2.1 p.2.2 +
            emn2ExpS2g sz n (Hf sz z n (t n) ω) (ζf sz z n (t n)) (t n) (ℓ n) p.1 p.2.1 p.2.2 else 0)
        (fun n p _ => ((mk sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
          (STprof sz n (t n) D (ℓ n) (p.2.2 0) (p.2.2 1)) ^ 2)) := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ Ψ _hΨ _hI ℓ hℓ hA D hD
  classical
  obtain ⟨hadm, hR, -⟩ := hF.1 κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow
  obtain ⟨-, -, cB, c, hcB, hc, hbd⟩ := hF.2 κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hd : 0 < d := emn2Exp_d_pos sz hsz
  have hWt := ST_W_tendsto sz hsz hadm.1 hadm.2.2.2.1
  have hη : ∀ n, 0 < (mk sz z).eta n (t n) := by
    intro n
    obtain ⟨-, h1, h2, -⟩ := hR n (t n) (ht0 n) (htT n)
    rw [← h2]; exact h1
  have hW1 : ∀ n, (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.W_pos n
  have hWpos : ∀ n, (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.W_pos n
  have hBt : ∀ᶠ n in atTop, cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n (t n) :=
    hbd.mono fun n hn => (hn (t n) (ht0 n) (htT n)).1
  have hLg1 : ∀ᶠ n in atTop, 1 ≤ Real.log ((sz.W n : ℕ) : ℝ) :=
    (Real.tendsto_log_atTop.comp hWt).eventually (eventually_ge_atTop _)
  have hLg4 : ∀ᶠ n in atTop, 4 ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ ((1 : ℝ) / 4) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      (Real.tendsto_log_atTop.comp hWt)).eventually (eventually_ge_atTop _)
  refine emn2Exp_stochDomAt_of_subset (hA D hD) ?_
  intro τ hτ
  refine ⟨τ / 5, by positivity, ?_⟩
  have hQ := emn2Exp_ev_exp_pow sz hd hsz (c := 2) (a := (3 : ℝ) / 4) (δ := τ / 2) (by norm_num)
    (by norm_num) (by norm_num) (by positivity)
    (C := 2 * 3 ^ d * 2 ^ (d - 2) * Real.sqrt (1 + cB⁻¹)) (by positivity)
  filter_upwards [hℓ, hBt, hLg1, hLg4, hQ] with n hℓn hBn hLg1n hLg4n hQn
  intro ω hω
  obtain ⟨p, hp⟩ := hω
  by_contra hno
  have hgood : ∀ u' : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)),
      ‖(mk sz z).L n (t n) u'.1.1 u'.2 ω‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 5) * STprof sz n (t n) D (ℓ n) (u'.2 0) (u'.2 1) :=
    fun u' => not_lt.mp fun h => hno ⟨u', h⟩
  obtain ⟨k, σ, a⟩ := p
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hBpos : 0 ≤ sz.Bctl n (t n) :=
    (mul_nonneg hcB.le (inv_nonneg.mpr (pow_nonneg (hWpos n).le d))).trans hBn
  have hηn := hη n
  by_cases hfar : emn2ExpEllDag sz n (t n) < (zdistInf d (sz.L n) (a 0 - a 1) : ℝ)
  · simp only [hfar, ↓reduceIte] at hp
    set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
    set y : ℝ := N ^ (τ / 10) with hy
    have hy0 : 0 ≤ y := Real.rpow_nonneg hNpos.le _
    have hy2 : y ^ 2 = N ^ (τ / 5) := by
      rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      congr 1; push_cast; ring
    have hy5 : y ^ 5 = N ^ (τ / 2) := by
      rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      congr 1; push_cast; ring
    have hNτ : N ^ τ = N ^ (τ / 2) * N ^ (τ / 2) := by
      rw [← Real.rpow_add hNpos]; congr 1; ring
    -- the profile
    set Pf : ℕ → ℝ := fun m => emn2ExpPf sz n (t n) D (ℓ n) (m : ℝ) with hPfdef
    have hPf0 : ∀ m, 0 ≤ Pf m := fun m => by
      change 0 ≤ emn2ExpPf sz n (t n) D (ℓ n) (m : ℝ)
      unfold emn2ExpPf
      exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (hWpos n).le d))
        (tailW_pos (hWpos n) _).le
    obtain ⟨hH, hz', hzeta, hLoop⟩ := hR n (t n) (ht0 n) (htT n)
    have h2 : ∀ (s : Bool) (x x' : Zd d (sz.L n)),
        ‖loopFine d (sz.L n) (sz.W n) (Hf sz z n (t n) ω) (ζf sz z n (t n))
            ![s, !s] ![x, x']‖ ≤ y ^ 2 * Pf (zdistInf d (sz.L n) (x - x')) := by
      intro s x x'
      have hne : (![s, !s] : Fin 2 → Bool) 0 ≠ (![s, !s] : Fin 2 → Bool) 1 := by
        cases s <;> simp
      rw [hy2, ← hLoop ω ![s, !s] ![x, x']]
      exact hgood (⟨![s, !s], hne⟩, ![x, x'])
    have hsw := emn2Exp_sw_dist sz n k a
    have hK : ∀ m : ℕ, (ℓ n < (m : ℝ) ∨
        (zdistInf d (sz.L n) (emn2ExpSw k a 0 - emn2ExpSw k a 1) : ℝ) ≤ (m : ℝ) +
          emn2ExpEllStar sz n (t n) + 1) →
        Pf m ≤ emn2ExpK d ((sz.W n : ℕ) : ℝ) *
          Pf (zdistInf d (sz.L n) (emn2ExpSw k a 0 - emn2ExpSw k a 1)) := by
      intro m hm
      rw [hsw] at hm ⊢
      exact emn2Exp_profile_cmp sz n (t n) D (ℓ n) hℓn.1 hLg1n
        (emn2Exp_scale_gap sz n (t n) hLg1n hLg4n) hfar hm
    have hK0 : 0 ≤ emn2ExpK d ((sz.W n : ℕ) : ℝ) := by
      have := emn2Exp_one_le_K d (hW1 n); linarith
    have hS := emn2Exp_S12_le (Hf sz z n (t n) ω) (ζf sz z n (t n)) (hH ω) hz'
      (emn2ExpSw k σ) (emn2ExpSw k a 0) (emn2ExpSw k a 1) hy0 hK0 hPf0 h2 hK
    rw [hsw] at hS
    -- `Pf 0 ≤ (1 + cB⁻¹) Bctl`
    have hP0 : Pf 0 ≤ (1 + cB⁻¹) * sz.Bctl n (t n) := by
      have := ST_prof_le_Bctl sz n hcB hℓn.1 hD hBn (0 : Zd d (sz.L n)) 0
      rw [emn2Exp_STprof_eq, sub_self, emn2Exp_zdistInf_zero] at this
      simpa [hPfdef] using this
    have hsq0 : Real.sqrt (Pf 0) ≤ Real.sqrt (1 + cB⁻¹) * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt hP0
    unfold emn2ExpS1g emn2ExpS2g at hp
    refine absurd hp (not_lt.mpr (hS.trans ?_))
    rw [hzeta]
    have hPpos : 0 ≤ Pf (zdistInf d (sz.L n) (a 0 - a 1)) ^ 2 := sq_nonneg _
    have hQ' : 2 * 3 ^ d * emn2ExpK d ((sz.W n : ℕ) : ℝ) * Real.sqrt (1 + cB⁻¹) ≤ N ^ (τ / 2) := by
      have : 2 * 3 ^ d * emn2ExpK d ((sz.W n : ℕ) : ℝ) * Real.sqrt (1 + cB⁻¹) =
          2 * 3 ^ d * 2 ^ (d - 2) * Real.sqrt (1 + cB⁻¹) *
            Real.exp (2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) := by
        unfold emn2ExpK; ring
      rw [this]; exact hQn
    have hη0 : 0 ≤ ((mk sz z).eta n (t n))⁻¹ := inv_nonneg.mpr hηn.le
    have hb0 : 0 ≤ (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hBpos _
    calc 2 * 3 ^ d / (mk sz z).eta n (t n) * emn2ExpK d ((sz.W n : ℕ) : ℝ) * y ^ 5 *
          Real.sqrt (Pf 0) * Pf (zdistInf d (sz.L n) (a 0 - a 1)) ^ 2
        ≤ 2 * 3 ^ d / (mk sz z).eta n (t n) * emn2ExpK d ((sz.W n : ℕ) : ℝ) * y ^ 5 *
          (Real.sqrt (1 + cB⁻¹) * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ)) *
            Pf (zdistInf d (sz.L n) (a 0 - a 1)) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hPpos
          apply mul_le_mul_of_nonneg_left hsq0
          positivity
      _ = (2 * 3 ^ d * emn2ExpK d ((sz.W n : ℕ) : ℝ) * Real.sqrt (1 + cB⁻¹)) * y ^ 5 *
          (((mk sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
            Pf (zdistInf d (sz.L n) (a 0 - a 1)) ^ 2) := by
          field_simp
      _ ≤ N ^ (τ / 2) * N ^ (τ / 2) * (((mk sz z).eta n (t n))⁻¹ *
          (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) * Pf (zdistInf d (sz.L n) (a 0 - a 1)) ^ 2) := by
          rw [hy5]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hQ' (Real.rpow_nonneg hNpos.le _)
      _ = N ^ τ * (((mk sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
          (STprof sz n (t n) D (ℓ n) (a 0) (a 1)) ^ 2) := by
          rw [hNτ]
          rfl
  · exfalso
    simp only [hfar, ↓reduceIte] at hp
    have : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (((mk sz z).eta n (t n))⁻¹ *
        (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
        (STprof sz n (t n) D (ℓ n) (a 0) (a 1)) ^ 2) := by positivity
    linarith

/-- **`S̃₁ + S̃₂` in the far case** at the band carrier: `emn2Exp_far12g` at `law = seqP`, `Flow = STFlow`,
`mk = bandFM ∘ STflowE`, `T0 = lemT` (`emn2Exp_bandFacts`), under its old name and statement. -/
theorem emn2Exp_far12 (d : ℕ) :
    ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℝ,
          (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n ∧
            Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
          STInitialGT2 sz (STflowE z) t ε₀ Ψ →
          ∀ ℓ : ℕ → ℝ, (∀ᶠ n in atTop, 0 ≤ ℓ n ∧ ℓ n ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 *
              ellT (sz.L n) (sz.lam n) (t n)) →
            (∀ D : ℝ, 0 < D → STLWassmExp sz (STflowE z) t D ℓ) →
            ∀ D : ℝ, 0 < D →
              Prec sz (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
                (fun n p ω => if emn2ExpEllDag sz n (t n) <
                    (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℝ) then
                  emn2ExpS1M sz n (STflowE z n) (t n) (ℓ n) p.1 p.2.1 p.2.2 ω +
                    emn2ExpS2M sz n (STflowE z n) (t n) (ℓ n) p.1 p.2.1 p.2.2 ω else 0)
                (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
                  (STprof sz n (t n) D (ℓ n) (p.2.2 0) (p.2.2 1)) ^ 2) := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ Ψ hΨ hI ℓ hℓ hA D hD
  exact emn2Exp_far12g (fun sz => Sizes.seqP sz) (emn2Exp_bandFacts d) κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ Ψ hΨ hI ℓ hℓ hA D hD

end Far12

/-! ## 9. The truncated profile and the split: statements for the consumers -/

section Consumers

variable {d : ℕ} (sz : Sizes d)

/-- `ℓ*_t` is the scale written inline in `KellStarEv` (`RBM3D/Path/KellStar.lean:60`):
`(log W)^{3/2} ℓ_t`. -/
theorem emn2ExpEllStar_eq (n : ℕ) (u : ℝ) :
    emn2ExpEllStar sz n u =
      Real.log (sz.W n : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (sz.lam n) u := rfl

/-- **The far field of `KellStarEv` at the scale `ℓ*_t`** (`Path/KellStar.lean`, `kellStarEv`; the input of
`S̃₃`, `3_5:871-888`, via the exponential decay `(prop:ThfadC)`): eventually, uniformly in
`0 ≤ s ≤ u ≤ t_n`, `Θ_u(a,b)` and `(Θ_s^{-1}Θ_u)(a,b)` are at most `W^{-D}` once
`δ ℓ*_u ≤ |a - b|`, `ℓ*_u = emn2ExpEllStar`.  Here the hypothesis of `KellStarEv` is read with
`emn2ExpEllStar` (they unify, `emn2ExpEllStar_eq`). -/
theorem emn2Exp_kellStar_far (sz : Sizes d) (𝔠 Λ τ δ D : ℝ) (t : ℕ → ℝ) (hd : 3 ≤ d)
    (h𝔠 : 0 < 𝔠) (hΛ : 0 < Λ) (hτ : 0 < τ) (hδ : 0 < δ) (hsz : sz.SizeTendsto)
    (hband : sz.Bandwidth 𝔠) (hrange : sz.RangeCond τ t) (ht1 : ∀ n, t n < 1)
    (hlam : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λ) :
    ∀ᶠ n : ℕ in atTop, ∀ s u : ℝ, 0 ≤ s → s ≤ u → u ≤ t n → ∀ a b : Zd d (sz.L n),
      δ * emn2ExpEllStar sz n u ≤ (zdistInf d (sz.L n) (a - b) : ℝ) →
        ‖Theta d (sz.L n) (sz.lam n) (u : ℂ) a b‖ ≤ (sz.W n : ℝ) ^ (-D) ∧
          ‖ukerMat d (sz.L n) (sz.lam n) 1 s u a b‖ ≤ (sz.W n : ℝ) ^ (-D) :=
  kellStarEv d sz 𝔠 Λ τ δ D t hd h𝔠 hΛ hτ hδ hsz hband hrange ht1 hlam

/-- **The comparison `Ψ_t(r)² ≍ W^{-d} 𝒯̃^ℓ_{t,D}(r)` for `0 ≤ r ≤ ℓ†_t`** (`3_5:833-836`) for the literal
truncated profile `Ψ_t(r)² = W^{-d} B_{t, r ∧ ℓ}`.  (i) `Ψ_t(r)² ≤ exp((log W)^{7/8}) W^{-d} 𝒯̃^ℓ_{t,D}(r)`:
`B_{t,ρ} = 𝒯_t(ρ) exp((ρ/ℓ_t)^{1/2})` with `ρ = r ∧ ℓ ≤ ℓ†_t`, so `(ρ/ℓ_t)^{1/2} ≤ (log W)^{7/8}`.
(ii) `W^{-d} 𝒯̃^ℓ_{t,D}(r) ≤ Ψ_t(r)²` whenever `W^{-D} ≤ B_{t, r ∧ ℓ}` (the truncation `r ∧ ℓ` is what
makes the second bound hold: for the untruncated `B_{t,r}` it fails when `ℓ < r`, `3_5:836`). -/
theorem emn2Exp_trunc_cmp (n : ℕ) (u D ℓ : ℝ) (hℓ : 0 ≤ ℓ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ emn2ExpEllDag sz n u) :
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * BparamR d (sz.L n) (sz.lam n) u (min r ℓ) ≤
        Real.exp (Real.sqrt (Real.log ((sz.W n : ℕ) : ℝ) ^ ((7 : ℝ) / 4))) *
          emn2ExpPf sz n u D ℓ r ∧
      (((sz.W n : ℕ) : ℝ) ^ (-D) ≤ BparamR d (sz.L n) (sz.lam n) u (min r ℓ) →
        emn2ExpPf sz n u D ℓ r ≤
          (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * BparamR d (sz.L n) (sz.lam n) u (min r ℓ)) := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : 0 < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hρ : 0 ≤ min r ℓ := le_min hr0 hℓ
  have hX : min r ℓ ≤
      Real.log ((sz.W n : ℕ) : ℝ) ^ ((7 : ℝ) / 4) * ellT (sz.L n) (sz.lam n) u :=
    (min_le_left _ _).trans hr
  have hB := emn2Exp_bparamR_le_exp_tailT (d := d) (L := sz.L n) (g := sz.lam n) (t := u) hL1 hρ hX
  have he0 : 0 ≤ Real.exp (Real.sqrt (Real.log ((sz.W n : ℕ) : ℝ) ^ ((7 : ℝ) / 4))) :=
    (Real.exp_pos _).le
  unfold emn2ExpPf tailW
  refine ⟨?_, fun hD => ?_⟩
  · calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * BparamR d (sz.L n) (sz.lam n) u (min r ℓ)
        ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (Real.exp (Real.sqrt (Real.log ((sz.W n : ℕ) : ℝ) ^
            ((7 : ℝ) / 4))) * max (tailT d (sz.L n) (sz.lam n) u (min r ℓ)) (((sz.W n : ℕ) : ℝ) ^ (-D))) :=
          mul_le_mul_of_nonneg_left (hB.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) he0))
            (inv_nonneg.mpr hWd.le)
      _ = _ := by ring
  · exact mul_le_mul_of_nonneg_left (max_le (emn2Exp_tailT_le_bparamR hρ) hD)
      (inv_nonneg.mpr hWd.le)

/-- **The three-way split of `(𝓔⊗𝓔)^{M,(2;k)}`** (`3_5:840-845`): pointwise, `|(𝓔⊗𝓔)^{M,(2;k)}|` is at most its
value on the near pairs (`|a-b| ≤ ℓ†_t`) plus `S̃₁ + S̃₂` and `S̃₃` on the far pairs (`|a-b| > ℓ†_t`);
the three terms are the three `Prec` statements `emn2Exp_near`, `emn2Exp_far12` and ST2-11's `S̃₃`. -/
theorem emn2Exp_EEk_split (n : ℕ) (E u ℓ : ℝ) (k : Fin 2) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    ‖STEEk sz n E u k σ a ω‖ ≤
      (if (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤ emn2ExpEllDag sz n u then
        ‖STEEk sz n E u k σ a ω‖ else 0) +
      (if emn2ExpEllDag sz n u < (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) then
        emn2ExpS1M sz n E u ℓ k σ a ω + emn2ExpS2M sz n E u ℓ k σ a ω else 0) +
      (if emn2ExpEllDag sz n u < (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) then
        emn2ExpS3M sz n E u ℓ k σ a ω else 0) := by
  by_cases h : emn2ExpEllDag sz n u < (zdistInf d (sz.L n) (a 0 - a 1) : ℝ)
  · have h' : ¬ ((zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤ emn2ExpEllDag sz n u) := not_le.mpr h
    simp only [h, h', ↓reduceIte, zero_add]
    exact emn2Exp_EEk_cover sz n E u ℓ k σ a ω
  · have h' : (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤ emn2ExpEllDag sz n u := not_lt.mp h
    simp only [h, h', ↓reduceIte, add_zero]
    exact le_rfl


/-- **The three-way split of `(𝓔⊗𝓔)^{M,(2;k)}` over a carrier** (`3_5:840-845`): for the loops `C.L` realized by
`(H, ζ)` and the kernel `C.S = S^{(B)}(g)`, pointwise `|(𝓔⊗𝓔)^{M,(2;k)}|` is at most its value on the near pairs plus
`S̃₁ + S̃₂` and `S̃₃` on the far pairs (`emn2Exp_EEk_split` at the carrier). -/
theorem emn2Exp_EEg_split {C : FlowFM sz} (n : ℕ) (u ℓ : ℝ) (ω : sz.SeqΩ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (ζ : ℂ) (g : ℝ)
    (hS : C.S n = SB d (sz.L n) g)
    (hL : ∀ {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      C.L n u σ a ω = loopFine d (sz.L n) (sz.W n) H ζ σ a)
    (k : Fin 2) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ‖STEEg C n u k σ a ω‖ ≤
      (if (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤ emn2ExpEllDag sz n u then
        ‖STEEg C n u k σ a ω‖ else 0) +
      (if emn2ExpEllDag sz n u < (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) then
        emn2ExpS1g sz n H ζ u ℓ k σ a + emn2ExpS2g sz n H ζ u ℓ k σ a else 0) +
      (if emn2ExpEllDag sz n u < (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) then
        emn2ExpS3g sz n H ζ u ℓ k σ a else 0) := by
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  have hcover : ‖STEEg C n u k σ a ω‖ ≤ emn2ExpS1g sz n H ζ u ℓ k σ a +
      emn2ExpS2g sz n H ζ u ℓ k σ a + emn2ExpS3g sz n H ζ u ℓ k σ a := by
    unfold emn2ExpS1g emn2ExpS2g emn2ExpS3g
    fin_cases k
    · simp only [Fin.zero_eta, emn2ExpSw, ite_true]
      rw [emn2Poly_EEg_zero_eq C n u ω H ζ g hS hL]
      exact emn2Exp_cover H ζ hL3 g _ _ σ (a 0) (a 1)
    · have h10 : ¬ ((1 : Fin 2) = 0) := by decide
      simp only [Fin.mk_one, emn2ExpSw, h10, ite_false]
      rw [emn2Poly_EEg_one_eq, emn2Poly_EEg_zero_eq C n u ω H ζ g hS hL]
      simpa using emn2Exp_cover H ζ hL3 g (emn2ExpEllStar sz n u) ℓ ![σ 1, σ 0] (a 1) (a 0)
  by_cases h : emn2ExpEllDag sz n u < (zdistInf d (sz.L n) (a 0 - a 1) : ℝ)
  · have h' : ¬ ((zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤ emn2ExpEllDag sz n u) := not_le.mpr h
    simp only [h, h', ↓reduceIte, zero_add]
    exact hcover
  · have h' : (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤ emn2ExpEllDag sz n u := not_lt.mp h
    simp only [h, h', ↓reduceIte, add_zero]
    exact le_rfl

end Consumers

/-! ## 10. Assembly of `STEMn2Exp` from the far-case sum `S̃₃` -/

section Assembly

/-- **The assembly of `(eq:MG_conclusion3)` over a law** (the last step of `3_5:829-888`): if the quadratic variation
`ξ ≤ ξ₁ + ξ₂ + ξ₃` pointwise (the near case, `S̃₁ + S̃₂`, `S̃₃`), `ξ₁, ξ₂ ≺ η⁻¹ B P²` and `ξ₃ ≺ η⁻¹ (B + J³) P²`
with `η > 0`, `B ≥ 0`, `J ≥ 0`, then `ξ ≺ η⁻¹ (B + J³) P²`: `ξ ≺ ζ₁ + ζ₁ + ζ ≤ 3 ζ ≺ ζ`. -/
theorem emn2Exp_assemble {d : ℕ} {sz : Sizes d} (μ : Measure sz.SeqΩ)
    (hsize : Tendsto sz.size atTop atTop) (η Bq : ℕ → ℝ)
    (P : ∀ n, (Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) → ℝ) (J : ∀ n, sz.SeqΩ → ℝ)
    (hη : ∀ n, 0 < η n) (hB : ∀ n, 0 ≤ Bq n) (hJ : ∀ n ω, 0 ≤ J n ω)
    {ξ n₁ n₂ n₃ : ∀ n, (Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) → sz.SeqΩ → ℝ}
    (hξ : ∀ n p ω, ξ n p ω ≤ n₁ n p ω + n₂ n p ω + n₃ n p ω)
    (h₁ : PrecL sz μ n₁ (fun n p _ => (η n)⁻¹ * Bq n * P n p ^ 2))
    (h₂ : PrecL sz μ n₂ (fun n p _ => (η n)⁻¹ * Bq n * P n p ^ 2))
    (h₃ : PrecL sz μ n₃ (fun n p ω => (η n)⁻¹ * (Bq n + J n ω ^ 3) * P n p ^ 2)) :
    PrecL sz μ ξ (fun n p ω => (η n)⁻¹ * (Bq n + J n ω ^ 3) * P n p ^ 2) := by
  set ζ₁ : ∀ n, (Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) → sz.SeqΩ → ℝ :=
    fun n p _ => (η n)⁻¹ * Bq n * P n p ^ 2 with hζ₁
  set ζ : ∀ n, (Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) → sz.SeqΩ → ℝ :=
    fun n p ω => (η n)⁻¹ * (Bq n + J n ω ^ 3) * P n p ^ 2 with hζ
  have hζ0 : ∀ n p ω, 0 ≤ ζ n p ω := fun n p ω => by
    have := hη n; have := hB n; have := hJ n ω; positivity
  have hζ₁ζ : ∀ n p ω, ζ₁ n p ω ≤ ζ n p ω := fun n p ω => by
    have h1 : 0 ≤ (η n)⁻¹ := inv_nonneg.mpr (hη n).le
    have h3 : 0 ≤ J n ω ^ 3 := by have := hJ n ω; positivity
    simp only [hζ₁, hζ]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) h1) (sq_nonneg _)
  have h123 := StochDomAt.add hsize (StochDomAt.add hsize h₁ h₂) h₃
  have h1 : PrecL sz μ ξ (ζ₁ + ζ₁ + ζ) := StochDomAt.of_le_left (fun n p ω => hξ n p ω) h123
  have h2 : PrecL sz μ ξ (fun n p ω => 3 * ζ n p ω) := by
    refine emn2Exp_precL_mono sz μ (Eventually.of_forall fun n p ω => ?_) h1
    have := hζ₁ζ n p ω
    simp only [Pi.add_apply]
    linarith
  have h3' : StochDomAt μ sz.size (fun n p ω => 3 * ζ n p ω) ζ :=
    StochDomAt.const_mul_left hsize (by norm_num) hζ0 (StochDomAt.refl hsize hζ0)
  exact StochDomAt.trans hsize h2 h3'
/-- **`STEMn2Exp` from `S̃₃`** (the assembly of `3_5:829-888`): the pin `STEMn2Exp d` follows from
`emn2Exp_near`, `emn2Exp_far12` and the bound of the far-case sum `S̃₃` by the pin's right-hand side
(`η_t^{-1} [(W^{-d}B_{t,0})^{1/2} + Ĵ³] (W^{-d} 𝒯̃)²`, `3_5:871-888`, the part of ST2-11).  The hypothesis
`h3` has the premises of the pin and `Prec (S̃₃ · 1_{|a-b| > ℓ†_t}) ≺ η⁻¹ [Bctl^{1/2} + Ĵ³] P²`.
The conclusion is the body of `STEMn2Exp d` written out (so `STEMn2Exp d` is `emn2Exp_of_far3 d h3`
by unfolding): this conditional theorem is deliberately not stated with the head `STEMn2Exp`, which
the registry scan (`RBM.Audit.scanPremises`) would count as a proof of the owed pin. -/
theorem emn2Exp_of_far3 (d : ℕ)
    (h3 : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
          ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℝ,
            (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n ∧
              Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
            STInitialGT2 sz (STflowE z) t ε₀ Ψ →
            ∀ ℓ : ℕ → ℝ, (∀ᶠ n in atTop, 0 ≤ ℓ n ∧ ℓ n ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 *
                ellT (sz.L n) (sz.lam n) (t n)) →
              (∀ D : ℝ, 0 < D → STLWassmExp sz (STflowE z) t D ℓ) →
              ∀ D : ℝ, 0 < D →
                Prec sz (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
                  (fun n p ω => if emn2ExpEllDag sz n (t n) <
                      (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℝ) then
                    emn2ExpS3M sz n (STflowE z n) (t n) (ℓ n) p.1 p.2.1 p.2.2 ω else 0)
                  (fun n p ω => (etaT (STflowE z n) (t n))⁻¹ *
                    ((sz.Bctl n (t n)) ^ (1 / 2 : ℝ) +
                      (STJhat sz n (STflowE z n) D (ℓ n) (t n) ω) ^ 3) *
                    (STprof sz n (t n) D (ℓ n) (p.2.2 0) (p.2.2 1)) ^ 2)) :
    ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℝ,
          (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n ∧
            Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
          STInitialGT2 sz (STflowE z) t ε₀ Ψ →
          ∀ ℓ : ℕ → ℝ, (∀ᶠ n in atTop, 0 ≤ ℓ n ∧ ℓ n ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 *
              ellT (sz.L n) (sz.lam n) (t n)) →
            (∀ D : ℝ, 0 < D → STLWassmExp sz (STflowE z) t D ℓ) →
            ∀ D : ℝ, 0 < D →
              Prec sz (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
                (fun n p ω => ‖STEEk sz n (STflowE z n) (t n) p.1 p.2.1 p.2.2 ω‖)
                (fun n p ω => (etaT (STflowE z n) (t n))⁻¹ *
                  ((sz.Bctl n (t n)) ^ (1 / 2 : ℝ) +
                    (STJhat sz n (STflowE z n) D (ℓ n) (t n) ω) ^ 3) *
                  (STprof sz n (t n) D (ℓ n) (p.2.2 0) (p.2.2 1)) ^ 2) := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ Ψ hΨ hI ℓ hℓ hA D hD
  have hnear := emn2Exp_near d κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ Ψ hΨ hI ℓ hℓ hA D hD
  have hfar := emn2Exp_far12 d κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ Ψ hΨ hI ℓ hℓ hA D hD
  have hf3 := h3 κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ Ψ hΨ hI ℓ hℓ hA D hD
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hsize : Tendsto sz.size atTop atTop := tendsto_size sz hsz
  have hη : ∀ n, 0 < etaT (STflowE z n) (t n) := by
    intro n
    have hzim := ST_flow_im_pos sz hflow n
    exact etaT_pos (abs_lemE_lt_two hzim) ((htT n).trans_lt (lemT_lt_one hzim))
  have hBpos : ∀ n, 0 < sz.Bctl n (t n) := fun n =>
    STBctl_pos sz n ((htT n).trans_lt (lemT_lt_one (ST_flow_im_pos sz hflow n)))
  have hJ : ∀ n ω, 0 ≤ STJhat sz n (STflowE z n) D (ℓ n) (t n) ω := fun n ω =>
    ST_JhatM_nonneg sz n _ _ _ _ _
  exact emn2Exp_assemble (Sizes.seqP sz) hsize (fun n => etaT (STflowE z n) (t n))
    (fun n => (sz.Bctl n (t n)) ^ (1 / 2 : ℝ))
    (fun n p => STprof sz n (t n) D (ℓ n) (p.2.2 0) (p.2.2 1))
    (fun n ω => STJhat sz n (STflowE z n) D (ℓ n) (t n) ω) hη (fun n => Real.rpow_nonneg (hBpos n).le _) hJ
    (fun n p ω => emn2Exp_EEk_split sz n (STflowE z n) (t n) (ℓ n) p.1 p.2.1 p.2.2 ω) hnear hfar hf3

end Assembly

end RBM.Gauss.Sizes

/-! ## 11. Compiled nonempty instances at `d = 3`

**Matrix level** (`emn2Exp_cover`, `emn2Exp_S12_le`): `d = 3`, `L = 3`, `W = 2` (`N = 216`, `W^d = 8`
sites per block, `L^d = 27` blocks), the Hermitian matrix `H_{ij} = (i)_0 + (j)_0` (not block diagonal,
not a multiple of the identity), `z = 1/2 + i/4`, `σ = (+,-)`, `a = 0`, `b = (1,1,1)`; the control is the
deterministic envelope `|𝓛^{(2)}| ≤ η⁻²` (`norm_loopM_le`), i.e. `y = η⁻¹`, `P ≡ 1`, `K = 1`.

**Scales** (`emn2Exp_profile_shift`, `emn2Exp_scale_gap`, `emn2Exp_profile_cmp`, `emn2Exp_trunc_cmp`,
`emn2Exp_kellStar_far`): small numbers for the abstract shift lemma; the size sequence with
`W = 2^{400}` (`log W > 277`) for the gap `2(ℓ* + 1) ≤ ℓ†`, which needs `(log W)^{1/4} ≥ 4`; `sz0`
for `emn2Exp_trunc_cmp` and `emn2Exp_kellStar_far`.

**Model level** (`emn2Exp_EEk_cover`, `emn2Exp_EEk_split`, `emn2Exp_psiClass`, `emn2Exp_near`,
`emn2Exp_far12`): the merged size sequence `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`,
`ilambda_n = (2(n+1))^{-6}`), `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `z_n = 1/2 + i N_n^{-4/5}` (`flow_z0`),
`t ≡ 1/16 ≤ lemT z_n`, `ε₀ = 1/20`, `Ψ_n = W_n^{-1}`, the scale `ℓ_n = ℓ_t` (`ellT`, not the collapsed `ℓ = 0`)
and every `D > 0`.  Every deterministic hypothesis is discharged; what stays a hypothesis of the
examples is `STInitialGT2` and `STLWassmExp` (Step 1 / ST-6 chain and the LW gate, other gates'
pins; limit check in the preflight report (a)). -/

namespace RBM.Gauss.EMn2Exp1Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst
  RBM.Gauss.Step2DefsInst RBM.Path Filter

/-- The instance matrix `H_{ij} = (i)_0 + (j)_0` on `Idx 3 3 2` (copy of `EMn2PolyInst.emH`). -/
private noncomputable def exH : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ :=
  Matrix.of fun i j => (((i 0).val + (j 0).val : ℕ) : ℂ)

private theorem exH_herm : exH.IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, exH, Matrix.of_apply]
  rw [add_comm (j 0).val, star_natCast]

private def exZ : ℂ := ⟨1 / 2, 1 / 4⟩

private theorem exZ_im : 0 < exZ.im := by
  change (0 : ℝ) < 1 / 4
  norm_num

private def exB : Zd 3 3 := fun _ => 1

/-- **`emn2Exp_cover`** at the instance matrix: the cut-`0` quadratic variation loop is at most
`S̃₁ + S̃₂ + S̃₃` (`ℓ* = 1`, `ℓ = 2`). -/
example :
    ‖(((2 : ℕ) : ℂ) ^ 3) * ∑ c : Zd 3 3, ∑ c' : Zd 3 3, SB 3 3 ((1 : ℝ) / 8) c c' *
        loopFine 3 3 2 exH exZ ![true, false, true, !true, !false, !true]
          ![0, exB, c', exB, 0, c]‖ ≤
      emn2ExpS1 exH exZ 1 2 ![true, false] 0 exB + emn2ExpS2 exH exZ 1 2 ![true, false] 0 exB +
        emn2ExpS3 exH exZ 1 2 ![true, false] 0 exB := by
  simpa using emn2Exp_cover (L := 3) (W := 2) exH exZ le_rfl ((1 : ℝ) / 8) 1 2 ![true, false] 0 exB

/-- **`emn2Exp_S12_le`** at the instance matrix: every hypothesis is discharged (the 2-loops by the
envelope `‖𝓛^{(2)}‖ ≤ η⁻²`, `η = Im z = 1/4`; `P ≡ 1`, `K = 1`; `hK` is `1 ≤ 1 · 1`). -/
example :
    emn2ExpS1 exH exZ 1 2 ![true, false] 0 exB + emn2ExpS2 exH exZ 1 2 ![true, false] 0 exB ≤
      2 * 3 ^ 3 / exZ.im * 1 * (exZ.im⁻¹) ^ 5 * Real.sqrt 1 * 1 ^ 2 := by
  have hη : (0 : ℝ) < exZ.im := exZ_im
  have hb : (blockMat 3 3 2 exH).IsHermitian := exH_herm.submatrix _
  have h := emn2Exp_S12_le (L := 3) (W := 2) exH exZ exH_herm exZ_im ![true, false] 0 exB
    (y := exZ.im⁻¹) (K := 1) (ℓs := 1) (ℓ := 2) (by positivity) zero_le_one (Pf := fun _ => 1)
    (fun _ => zero_le_one) (fun s x x' => by
      have := norm_loopM_le (d := 3) (L := 3) (W := 2) (n := 1)
        hb (z := exZ) hη (by rw [abs_of_pos hη])
        ![s, !s] ![x, x']
      simpa [loopFine] using this) (fun m _ => by simp)
  simpa using h


/-- **`emn2Exp_profile_shift`** at small numbers (`d = 3`, `L = 4`, `ilambda = 1/64`, `t = 1/16`, `W = 2`,
`D = 1`, `ℓ = 1`, `r = 3`, `m = 2`, `s = 1`, `ℓ_† = 2`): case (1) `m > ℓ`. -/
example :
    ((2 : ℝ) ^ 3)⁻¹ * tailW 3 4 (1 / 64) (1 / 16) 1 2 1 2 ≤
      2 ^ (3 - 2) * Real.exp (Real.sqrt (1 / ellT 4 (1 / 64) (1 / 16))) *
        (((2 : ℝ) ^ 3)⁻¹ * tailW 3 4 (1 / 64) (1 / 16) 1 2 1 3) :=
  emn2Exp_profile_shift (d := 3) (L := 4) (by norm_num) (1 / 64) (1 / 16) 2 1 1 (by norm_num)
    (by norm_num) (r := 3) (m := 2) (s := 1) (ℓd := 2) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by norm_num))

/-- The same data, case (2) `m ≥ r - s` with `m ≤ ℓ`: `r = 3`, `m = 2 = r - s`, `ℓ = 2`. -/
example :
    ((2 : ℝ) ^ 3)⁻¹ * tailW 3 4 (1 / 64) (1 / 16) 2 2 1 2 ≤
      2 ^ (3 - 2) * Real.exp (Real.sqrt (1 / ellT 4 (1 / 64) (1 / 16))) *
        (((2 : ℝ) ^ 3)⁻¹ * tailW 3 4 (1 / 64) (1 / 16) 2 2 1 3) :=
  emn2Exp_profile_shift (d := 3) (L := 4) (by norm_num) (1 / 64) (1 / 16) 2 1 2 (by norm_num)
    (by norm_num) (r := 3) (m := 2) (s := 1) (ℓd := 2) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr (by norm_num))

/-- A size sequence with `W = 2^{400}` (`log W = 400 log 2 > 277`), `L = 4`, `ilambda = 1/64`: here
`(log W)^{1/4} ≥ 4`, so the gap `2(ℓ* + 1) ≤ ℓ†` holds. -/
private def szA : Sizes 3 where
  L := fun _ => 4
  W := fun _ => 2 ^ 400
  lam := fun _ => 1 / 64
  three_le_L := fun _ => by norm_num
  W_pos := fun _ => by positivity

private theorem szA_logW : (277 : ℝ) ≤ Real.log ((szA.W 0 : ℕ) : ℝ) := by
  change (277 : ℝ) ≤ Real.log (((2 ^ 400 : ℕ) : ℕ) : ℝ)
  rw [Nat.cast_pow, Real.log_pow]
  have := Real.log_two_gt_d9
  norm_num at this ⊢
  linarith

private theorem szA_Lg4 : (4 : ℝ) ≤ Real.log ((szA.W 0 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := by
  have h2 : (256 : ℝ) ≤ Real.log ((szA.W 0 : ℕ) : ℝ) := by linarith [szA_logW]
  have h3 : (256 : ℝ) ^ ((1 : ℝ) / 4) ≤ Real.log ((szA.W 0 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow (by norm_num) h2 (by norm_num)
  have h4 : (256 : ℝ) ^ ((1 : ℝ) / 4) = 4 := by
    rw [show (256 : ℝ) = 4 ^ (4 : ℕ) by norm_num, show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
  linarith

/-- **`emn2Exp_scale_gap`** at `szA`: `2 (ℓ* + 1) ≤ ℓ†`. -/
example : 2 * (emn2ExpEllStar szA 0 (1 / 16) + 1) ≤ emn2ExpEllDag szA 0 (1 / 16) :=
  emn2Exp_scale_gap szA 0 (1 / 16) (by linarith [szA_logW]) szA_Lg4

/-- **`emn2Exp_profile_cmp`** at `szA`, case (1): `m = 2 > ℓ = 1`, `r = ℓ† + 1`. -/
example : emn2ExpPf szA 0 (1 / 16) 1 1 2 ≤ emn2ExpK 3 ((szA.W 0 : ℕ) : ℝ) *
    emn2ExpPf szA 0 (1 / 16) 1 1 (emn2ExpEllDag szA 0 (1 / 16) + 1) :=
  emn2Exp_profile_cmp szA 0 (1 / 16) 1 1 (by norm_num) (by linarith [szA_logW])
    (emn2Exp_scale_gap szA 0 (1 / 16) (by linarith [szA_logW]) szA_Lg4) (by linarith)
    (Or.inl (by norm_num))

/-- **`emn2Exp_profile_cmp`** at `szA`, case (2): `m = r - (ℓ* + 1)`, `ℓ = 1`. -/
example : emn2ExpPf szA 0 (1 / 16) 1 1 (emn2ExpEllDag szA 0 (1 / 16) + 1 -
      (emn2ExpEllStar szA 0 (1 / 16) + 1)) ≤ emn2ExpK 3 ((szA.W 0 : ℕ) : ℝ) *
    emn2ExpPf szA 0 (1 / 16) 1 1 (emn2ExpEllDag szA 0 (1 / 16) + 1) :=
  emn2Exp_profile_cmp szA 0 (1 / 16) 1 1 (by norm_num) (by linarith [szA_logW])
    (emn2Exp_scale_gap szA 0 (1 / 16) (by linarith [szA_logW]) szA_Lg4) (by linarith)
    (Or.inr (by linarith))

private theorem sz0_logW (n : ℕ) : 1 ≤ Real.log ((sz0.W n : ℕ) : ℝ) := by
  have h32 : (32 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := by
    have : (32 : ℕ) ≤ sz0.W n := by
      change 32 ≤ (2 * (n + 1)) ^ 5
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ (2 * (n + 1)) ^ 5 := Nat.pow_le_pow_left (by omega) 5
    exact_mod_cast this
  have h1 : Real.log 32 ≤ Real.log ((sz0.W n : ℕ) : ℝ) := Real.log_le_log (by norm_num) h32
  have h2 : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_gt_d9
  linarith

/-- **`emn2Exp_trunc_cmp`** at `sz0`, `n = 0`, `t = 1/16`, `D = 1`, `ℓ = 1`, `r = 1 ≤ ℓ†`
(`ℓ† = (log 32)^{7/4} ℓ_t ≥ 1`). -/
example :
    (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ * BparamR 3 (sz0.L 0) (sz0.lam 0) (1 / 16) (min 1 1) ≤
        Real.exp (Real.sqrt (Real.log ((sz0.W 0 : ℕ) : ℝ) ^ ((7 : ℝ) / 4))) *
          emn2ExpPf sz0 0 (1 / 16) 1 1 1 ∧
      (((sz0.W 0 : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤ BparamR 3 (sz0.L 0) (sz0.lam 0) (1 / 16) (min 1 1) →
        emn2ExpPf sz0 0 (1 / 16) 1 1 1 ≤
          (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ * BparamR 3 (sz0.L 0) (sz0.lam 0) (1 / 16) (min 1 1)) :=
  emn2Exp_trunc_cmp sz0 0 (1 / 16) 1 1 (by norm_num) (r := 1) (by norm_num) (by
    unfold emn2ExpEllDag
    have hL : (1 : ℝ) ≤ ((sz0.L 0 : ℕ) : ℝ) := by
      exact_mod_cast (by have := sz0.three_le_L 0; omega : 1 ≤ sz0.L 0)
    exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (sz0_logW 0) (by norm_num))
      (one_le_ellT hL))

/-- **`emn2Exp_ev_exp_pow`** at `sz0`: eventually `exp(2 (log W)^{3/4}) ≤ N^{1/2}`. -/
example : ∀ᶠ n in atTop, 1 * Real.exp (2 * Real.log ((sz0.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) ≤
    ((sz0.size n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
  emn2Exp_ev_exp_pow sz0 (by norm_num) sz0_tendsto (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (C := 1) (by norm_num)

private theorem sz0_Bdata : ∃ cB : ℝ, 0 < cB ∧
    ∀ᶠ n in atTop, cB * (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ ≤ sz0.Bctl n (tInst n) := by
  obtain ⟨cB, hcB, hBd⟩ := ST_Bdata_holds (by norm_num : 0 < 3) (1 / 10) (1 / 10) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨c, hc, hbd⟩ := hBd (1 / 6)
  refine ⟨cB, hcB, ?_⟩
  have := hbd sz0 z0 flow_z0 tInst (fun n => by simp only [tInst]; norm_num) sixteenth_le_lemT
  exact this.mono fun n hn => (hn (tInst n) (by simp only [tInst]; norm_num) le_rfl).1

/-- **`emn2Exp_psiClass`** at `sz0`: the truncated profile at the scale `ℓ_n = ℓ_t`, `D = 1`,
`ε' = 1/20` is in the class `STPsiClass` (the size data `cB W^{-d} ≤ W^{-d} B_{t,0}` from
`ST_Bdata_holds`). -/
example : STPsiClass sz0 (1 / 20)
    (emn2ExpPsi sz0 tInst (fun n => ellT (sz0.L n) (sz0.lam n) (tInst n)) 1 (1 / 20)) := by
  obtain ⟨cB, hcB, hB⟩ := sz0_Bdata
  exact emn2Exp_psiClass sz0 tInst _ hcB (by norm_num) hB

/-- **`emn2Exp_EEk_cover`** and **`emn2Exp_EEk_split`** at `sz0`, `n = 0`, `E = 1/2`, `t = 1/16`,
`σ = (+,-)`, `a = (0, b)`, `b = (1,1,1)`, for every `ω` and both cuts. -/
example (ω : sz0.SeqΩ) (k : Fin 2) :
    ‖STEEk sz0 0 (1 / 2) (1 / 16) k ![true, false] ![0, fun _ => 1] ω‖ ≤
      emn2ExpS1M sz0 0 (1 / 2) (1 / 16) 1 k ![true, false] ![0, fun _ => 1] ω +
        emn2ExpS2M sz0 0 (1 / 2) (1 / 16) 1 k ![true, false] ![0, fun _ => 1] ω +
        emn2ExpS3M sz0 0 (1 / 2) (1 / 16) 1 k ![true, false] ![0, fun _ => 1] ω :=
  emn2Exp_EEk_cover sz0 0 (1 / 2) (1 / 16) 1 k ![true, false] ![0, fun _ => 1] ω

example (ω : sz0.SeqΩ) (k : Fin 2) :
    ‖STEEk sz0 0 (1 / 2) (1 / 16) k ![true, false] ![0, fun _ => 1] ω‖ ≤
      (if (zdistInf 3 (sz0.L 0) ((![0, fun _ => 1] : Fin 2 → Zd 3 (sz0.L 0)) 0 -
          (![0, fun _ => 1] : Fin 2 → Zd 3 (sz0.L 0)) 1) : ℝ) ≤ emn2ExpEllDag sz0 0 (1 / 16) then
        ‖STEEk sz0 0 (1 / 2) (1 / 16) k ![true, false] ![0, fun _ => 1] ω‖ else 0) +
      (if emn2ExpEllDag sz0 0 (1 / 16) < (zdistInf 3 (sz0.L 0)
          ((![0, fun _ => 1] : Fin 2 → Zd 3 (sz0.L 0)) 0 -
            (![0, fun _ => 1] : Fin 2 → Zd 3 (sz0.L 0)) 1) : ℝ) then
        emn2ExpS1M sz0 0 (1 / 2) (1 / 16) 1 k ![true, false] ![0, fun _ => 1] ω +
          emn2ExpS2M sz0 0 (1 / 2) (1 / 16) 1 k ![true, false] ![0, fun _ => 1] ω else 0) +
      (if emn2ExpEllDag sz0 0 (1 / 16) < (zdistInf 3 (sz0.L 0)
          ((![0, fun _ => 1] : Fin 2 → Zd 3 (sz0.L 0)) 0 -
            (![0, fun _ => 1] : Fin 2 → Zd 3 (sz0.L 0)) 1) : ℝ) then
        emn2ExpS3M sz0 0 (1 / 2) (1 / 16) 1 k ![true, false] ![0, fun _ => 1] ω else 0) :=
  emn2Exp_EEk_split sz0 0 (1 / 2) (1 / 16) 1 k ![true, false] ![0, fun _ => 1] ω

private theorem ℓ_range_inst : ∀ᶠ n in atTop,
    0 ≤ ellT (sz0.L n) (sz0.lam n) (tInst n) ∧
      ellT (sz0.L n) (sz0.lam n) (tInst n) ≤
        (Real.log ((sz0.W n : ℕ) : ℝ)) ^ 10 * ellT (sz0.L n) (sz0.lam n) (tInst n) :=
  Eventually.of_forall fun n => ⟨ellT_nonneg, le_mul_of_one_le_left ellT_nonneg
    (one_le_pow₀ (sz0_logW n))⟩

/-- **`emn2Exp_near`** (the near case `|a - b| ≤ ℓ†_t` of `(eq:MG_conclusion3)`) at the instance data
above, `ε₀ = 1/20`, `Ψ_n = W_n^{-1}`, `ℓ_n = ℓ_t`, every `D > 0`. -/
example
    (hI : STInitialGT2 sz0 (STflowE z0) tInst (1 / 20) (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))))
    (hA : ∀ D : ℝ, 0 < D →
      STLWassmExp sz0 (STflowE z0) tInst D (fun n => ellT (sz0.L n) (sz0.lam n) (tInst n)))
    (D : ℝ) (hD : 0 < D) :
    Prec sz0 (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => if (zdistInf 3 (sz0.L n) (p.2.2 0 - p.2.2 1) : ℝ) ≤
          emn2ExpEllDag sz0 n (tInst n) then
        ‖STEEk sz0 n (STflowE z0 n) (tInst n) p.1 p.2.1 p.2.2 ω‖ else 0)
      (fun n p _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * (sz0.Bctl n (tInst n)) ^ (1 / 2 : ℝ) *
        (STprof sz0 n (tInst n) D (ellT (sz0.L n) (sz0.lam n) (tInst n)) (p.2.2 0) (p.2.2 1)) ^ 2) :=
  emn2Exp_near 3 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 tInst (fun n => by simp only [tInst]; norm_num) sixteenth_le_lemT (1 / 20)
    (by norm_num) (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) Ψ1_window hI
    (fun n => ellT (sz0.L n) (sz0.lam n) (tInst n)) ℓ_range_inst hA D hD

/-- **`emn2Exp_far12`** (`S̃₁ + S̃₂` in the far case `|a - b| > ℓ†_t`) at the same data. -/
example
    (hI : STInitialGT2 sz0 (STflowE z0) tInst (1 / 20) (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))))
    (hA : ∀ D : ℝ, 0 < D →
      STLWassmExp sz0 (STflowE z0) tInst D (fun n => ellT (sz0.L n) (sz0.lam n) (tInst n)))
    (D : ℝ) (hD : 0 < D) :
    Prec sz0 (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => if emn2ExpEllDag sz0 n (tInst n) <
          (zdistInf 3 (sz0.L n) (p.2.2 0 - p.2.2 1) : ℝ) then
        emn2ExpS1M sz0 n (STflowE z0 n) (tInst n) (ellT (sz0.L n) (sz0.lam n) (tInst n))
            p.1 p.2.1 p.2.2 ω +
          emn2ExpS2M sz0 n (STflowE z0 n) (tInst n) (ellT (sz0.L n) (sz0.lam n) (tInst n))
            p.1 p.2.1 p.2.2 ω else 0)
      (fun n p _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * (sz0.Bctl n (tInst n)) ^ (1 / 2 : ℝ) *
        (STprof sz0 n (tInst n) D (ellT (sz0.L n) (sz0.lam n) (tInst n)) (p.2.2 0) (p.2.2 1)) ^ 2) :=
  emn2Exp_far12 3 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 tInst (fun n => by simp only [tInst]; norm_num) sixteenth_le_lemT (1 / 20)
    (by norm_num) (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) Ψ1_window hI
    (fun n => ellT (sz0.L n) (sz0.lam n) (tInst n)) ℓ_range_inst hA D hD


/-- **`emn2Exp_of_far3`** at `d = 3`: the pin `STEMn2Exp 3` follows from the bound of `S̃₃` (ST2-11, the
hypothesis `h3` of the example: another gate's pin). -/
example (h3 : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
      ∀ (𝔠 : ℝ) (sz : Sizes 3) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
          ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℝ,
            (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(3 : ℕ) / 2 : ℝ) ≤ Ψ n ∧
              Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
            STInitialGT2 sz (STflowE z) t ε₀ Ψ →
            ∀ ℓ : ℕ → ℝ, (∀ᶠ n in atTop, 0 ≤ ℓ n ∧ ℓ n ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 *
                ellT (sz.L n) (sz.lam n) (t n)) →
              (∀ D : ℝ, 0 < D → STLWassmExp sz (STflowE z) t D ℓ) →
              ∀ D : ℝ, 0 < D →
                Prec sz (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz.L n)))
                  (fun n p ω => if emn2ExpEllDag sz n (t n) <
                      (zdistInf 3 (sz.L n) (p.2.2 0 - p.2.2 1) : ℝ) then
                    emn2ExpS3M sz n (STflowE z n) (t n) (ℓ n) p.1 p.2.1 p.2.2 ω else 0)
                  (fun n p ω => (etaT (STflowE z n) (t n))⁻¹ *
                    ((sz.Bctl n (t n)) ^ (1 / 2 : ℝ) +
                      (STJhat sz n (STflowE z n) D (ℓ n) (t n) ω) ^ 3) *
                    (STprof sz n (t n) D (ℓ n) (p.2.2 0) (p.2.2 1)) ^ 2)) :
    STEMn2Exp 3 :=
  emn2Exp_of_far3 3 h3


private theorem sz0_rangeCond : sz0.RangeCond (1 / 20) tInst := by
  have h := ST_size_pow_small sz0 (a := -1 + 1 / 20) (δ := 15 / 16) (tendsto_size sz0 sz0_tendsto)
    (by norm_num) (by norm_num)
  filter_upwards [h] with n hn
  simp only [tInst]
  linarith

private theorem sz0_lam_ev : ∀ᶠ n : ℕ in atTop, 0 < sz0.lam n ∧ sz0.lam n ≤ 1 :=
  Eventually.of_forall fun n => by
    have h1 : (1 : ℝ) ≤ (2 * ((n : ℝ) + 1)) ^ 6 :=
      one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    exact ⟨by simp only [sz0]; positivity, by simp only [sz0]; exact inv_le_one_of_one_le₀ h1⟩

/-- **`emn2Exp_kellStar_far`** at `sz0`, `𝔠 = 1/6`, `Λ = 1`, `τ = 1/20`, `δ = 1/200`, `D = 1`,
`t ≡ 1/16`: every deterministic hypothesis is discharged. -/
example : ∀ᶠ n : ℕ in atTop, ∀ s u : ℝ, 0 ≤ s → s ≤ u → u ≤ tInst n → ∀ a b : Zd 3 (sz0.L n),
    (1 / 200 : ℝ) * emn2ExpEllStar sz0 n u ≤ (zdistInf 3 (sz0.L n) (a - b) : ℝ) →
      ‖Theta 3 (sz0.L n) (sz0.lam n) (u : ℂ) a b‖ ≤ (sz0.W n : ℝ) ^ (-(1 : ℝ)) ∧
        ‖ukerMat 3 (sz0.L n) (sz0.lam n) 1 s u a b‖ ≤ (sz0.W n : ℝ) ^ (-(1 : ℝ)) :=
  emn2Exp_kellStar_far sz0 (1 / 6) 1 (1 / 20) (1 / 200) 1 tInst le_rfl (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) sz0_tendsto sz0_bandwidth sz0_rangeCond
    (fun n => by simp only [tInst]; norm_num) sz0_lam_ev

/-- **`emn2Exp_one_le_K`**, **`emn2Exp_STprof_eq`**, **`emn2ExpEllStar_eq`** at `sz0`, `n = 0`: the loss
constant is `≥ 1`, `STprof` is `emn2ExpPf` at `|a - b|`, `ℓ*` is the inline scale of `KellStarEv`. -/
example : 1 ≤ emn2ExpK 3 ((sz0.W 0 : ℕ) : ℝ) := emn2Exp_one_le_K 3 (W_ge_one 0)

example (a b : Zd 3 (sz0.L 0)) : STprof sz0 0 (1 / 16) 1 1 a b =
    emn2ExpPf sz0 0 (1 / 16) 1 1 ((zdistInf 3 (sz0.L 0) (a - b) : ℕ) : ℝ) :=
  emn2Exp_STprof_eq sz0 0 (1 / 16) 1 1 a b

example : emn2ExpEllStar sz0 0 (1 / 16) =
    Real.log (sz0.W 0 : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz0.L 0) (sz0.lam 0) (1 / 16) :=
  emn2ExpEllStar_eq sz0 0 (1 / 16)

end RBM.Gauss.EMn2Exp1Inst
