/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Path.UBounds
import RBM3D.Propagator.Prop5Hold
import RBM3D.Green.Pins
import RBM3D.Defs.Sizes

/-!
# The far field `Kell*`: `Θ_u` and the `𝒰`-kernel beyond `δ ℓ*_u`

Ticket T2097 (ST2-25, part 3).  Port of `RBM2D/Path/KellStar.lean` at commit `c9a24cf` (cited
`KellStar:<line>`): the pinned `KellStarEv` (`KellStar:53`) and its proof `kellStarEv` (`:311`),
with the helpers `kellStar_uker_offdiag` (`:219`) and the closing inequality (`:109`).  Paper:
arXiv:2507.20274, `lem_propTH` property 5 (`prop:ThfadC`); the scale `ℓ*_u = (log W)^{3/2} ℓ_u`
is the one of RBM2D (`Path/Scales:52`), see the commented line `3_5_Loop_Hierarchy.tex:2313`.

**Not ported** (ticket `T2097.md`): `KpmBoundProp5`, `kpmBoundProp5` (`KellStar:39`, `:240`; the
`d = 2` form of the `𝒦^{(2)}` bound, superseded by `STK2decay`); `ThetaMaxNorm`, `thetaMaxNorm`
(`:46`, `:280`; the constant `180·40002²(1 + log L)` and `scaleM` are `d = 2` objects, and the
portmap lists only `kellStarEv` as consumed); `kellStar_Kpm_eq`, `kellStar_min_le`.

Differences from RBM2D (every one forced by `d ≥ 3`):
* the propagator input is `Prop5Decay d Λ` (`RBM3D/Propagator/Pins.lean:35`), **proved** by
  `prop5Decay_holds` (`Prop5Hold.lean:784`), instead of `norm_Theta_apply_le_prop5`; it needs
  `3 ≤ d`, `0 < Λ` and `0 < g ≤ Λ`, so `KellStarEv d` has the hypotheses `3 ≤ d`, `0 < Λ` and
  `∀ᶠ n, 0 < sz.lam n ∧ sz.lam n ≤ Λ` (absent in RBM2D, which has no coupling);
* the `d = 2` prefactor `((1-u) ℓ_u²)⁻¹ ≤ W²` and the factor `1 + log L` are gone: the amplitude is
  `B_{u,K} ≤ 2 (1-u)⁻¹ ≤ 2 N^{1-τ} ≤ 2 W^{max(1-τ,0)/𝔠}` (`Bparam`, `RangeCond`, `Bandwidth`);
* `d : Sizes` becomes `sz : Sizes d`, `Bandwidth d c` becomes `sz.Bandwidth 𝔠`, `Tendsto d.size`
  becomes `sz.SizeTendsto`, `RangeCond d τ t` becomes `sz.RangeCond τ t`;
* the distance of the far condition is `zdistInf` (stochastic side); `zdistInf ≤ zdistD`
  (`zdistInf_le_zdistD`) and property 5 is in `zdistD`, so the `zdistInf` form is the stronger
  statement;
* `ℓ*_u` is written inline as `(log W)^{3/2} * ellT L g u` (no public `ellStar`).
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Path

open Filter Matrix RBM RBM.Gauss

/-! ## Pinned definition -/

/-- **Pin E.3g (`Kell*`)**, in `∀ᶠ` form: eventually, beyond `δ ℓ*_u`, `ℓ*_u = (log W)^{3/2} ℓ_u`,
both `Θ_u` and `Θ_s^{-1} Θ_u = ukerMat 1 s u` are `≤ W^{-D}`, uniformly in `0 ≤ s ≤ u ≤ t_n`
(`KellStar:53`).  Added to RBM2D's hypotheses: `3 ≤ d`, `0 < Λ` and `0 < lam n ≤ Λ` eventually
(the coupling window of `Prop5Decay`). -/
def KellStarEv (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (𝔠 Λ τ δ D : ℝ) (t : ℕ → ℝ), 3 ≤ d → 0 < 𝔠 → 0 < Λ → 0 < τ → 0 < δ →
    sz.SizeTendsto → sz.Bandwidth 𝔠 → sz.RangeCond τ t → (∀ n, t n < 1) →
    (∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λ) →
    ∀ᶠ n : ℕ in atTop, ∀ s u : ℝ, 0 ≤ s → s ≤ u → u ≤ t n →
      ∀ a b : Zd d (sz.L n),
        δ * (Real.log (sz.W n : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (sz.lam n) u) ≤
            (zdistInf d (sz.L n) (a - b) : ℝ) →
        ‖Theta d (sz.L n) (sz.lam n) (u : ℂ) a b‖ ≤ (sz.W n : ℝ) ^ (-D) ∧
          ‖ukerMat d (sz.L n) (sz.lam n) 1 s u a b‖ ≤ (sz.W n : ℝ) ^ (-D)

/-! ## Private helpers -/

/-- `B_{u,K} ≤ 2 (1-u)⁻¹` for `u < 1`, `L ≥ 1` (both terms of `(eq_B_param)` are `≤ (1-u)⁻¹`). -/
private theorem kellStar_bparam_le (d L : ℕ) (hL : 1 ≤ L) (g : ℝ) {u : ℝ} (hu : u < 1) (n : ℕ) :
    Bparam d L g u n ≤ 2 * (1 - u)⁻¹ := by
  have hx : 0 < 1 - u := by linarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold Bparam
  rw [abs_of_pos hx]
  have hxi : 0 ≤ (1 - u)⁻¹ := inv_nonneg.mpr hx.le
  have h1 : (g ^ 2 + (1 - u))⁻¹ * (((n : ℝ) + 1) ^ (d - 2))⁻¹ ≤ (1 - u)⁻¹ := by
    have a1 : (g ^ 2 + (1 - u))⁻¹ ≤ (1 - u)⁻¹ := inv_anti₀ hx (by nlinarith [sq_nonneg g])
    have a2 : (((n : ℝ) + 1) ^ (d - 2))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    calc (g ^ 2 + (1 - u))⁻¹ * (((n : ℝ) + 1) ^ (d - 2))⁻¹ ≤ (1 - u)⁻¹ * 1 :=
          mul_le_mul a1 a2 (by positivity) hxi
      _ = (1 - u)⁻¹ := mul_one _
  have h2 : ((L : ℝ) ^ d * (1 - u))⁻¹ ≤ (1 - u)⁻¹ := by
    have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hL)
    exact inv_anti₀ hx (by nlinarith)
  linarith

/-- The closing inequality of the far field, for `x = log W ≥ 1` with
`2C + k + |D| ≤ c δ √x`: `2C e^{x k} e^{-c δ x^{3/2}} ≤ e^{-x D}`. -/
private theorem kellStar_arith {C c δ D k x : ℝ} (hC : 0 < C) (hx1 : 1 ≤ x)
    (hsq : 2 * C + k + |D| ≤ c * δ * Real.sqrt x) :
    C * (2 * Real.exp (x * k)) * Real.exp (-(c * δ * x ^ ((3 : ℝ) / 2))) ≤
      Real.exp (x * (-D)) := by
  have hx0 : 0 < x := by linarith
  have h32 : x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
    have h : (3 : ℝ) / 2 = 1 + 1 / 2 := by norm_num
    rw [h, Real.rpow_add hx0, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have h1 : 2 * C ≤ Real.exp (2 * C) := by
    have := Real.add_one_le_exp (2 * C); linarith
  have h2 : 2 * C + x * k - c * δ * x ^ ((3 : ℝ) / 2) ≤ x * (-D) := by
    rw [h32]
    have hDx : D * x ≤ |D| * x := mul_le_mul_of_nonneg_right (le_abs_self D) hx0.le
    have hCx : 2 * C ≤ 2 * C * x := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hsq hx0.le
    nlinarith
  calc C * (2 * Real.exp (x * k)) * Real.exp (-(c * δ * x ^ ((3 : ℝ) / 2)))
      = (2 * C) * Real.exp (x * k) * Real.exp (-(c * δ * x ^ ((3 : ℝ) / 2))) := by ring
    _ ≤ Real.exp (2 * C) * Real.exp (x * k) * Real.exp (-(c * δ * x ^ ((3 : ℝ) / 2))) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (2 * C + x * k - c * δ * x ^ ((3 : ℝ) / 2)) := by
        rw [← Real.exp_add, ← Real.exp_add]; rfl
    _ ≤ Real.exp (x * (-D)) := Real.exp_le_exp.mpr h2

/-- Off-diagonal entries of the `𝒰`-kernel: `u 𝒰_{s,u}(a,b) = (u - s) Θ_u(a,b)` for `a ≠ b`
(from `(1 - uS) Θ_u = 1`; `KellStar:219`). -/
private theorem kellStar_uker_offdiag (d L : ℕ) [NeZero L] (g : ℝ) (hL : 3 ≤ L) {s u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) {a b : Zd d L} (hab : a ≠ b) :
    (u : ℂ) * ukerMat d L g 1 s u a b = ((u : ℂ) - (s : ℂ)) * Theta d L g (u : ℂ) a b := by
  have hξ : ‖(u : ℂ) * 1‖ < 1 := by
    rw [mul_one, Complex.norm_real, Real.norm_of_nonneg hu0]; exact hu1
  have h := mul_Theta_of_three_le (d := d) (L := L) (g := g) hL hξ
  have h' : (u : ℂ) • ukerMat d L g 1 s u =
      ((u : ℂ) - (s : ℂ)) • Theta d L g ((u : ℂ) * 1) +
        (s : ℂ) • (1 : Matrix (Zd d L) (Zd d L) ℂ) := by
    have hs : (s : ℂ) • (1 : Matrix (Zd d L) (Zd d L) ℂ) =
        (s : ℂ) • ((1 - ((u : ℂ) * 1) • SB d L g) * Theta d L g ((u : ℂ) * 1)) := by rw [h]
    rw [hs]
    unfold ukerMat
    simp only [sub_mul, one_mul, smul_mul_assoc]
    module
  have h'' := congrFun (congrFun h' a) b
  have e : Theta d L g ((u : ℂ) * 1) = Theta d L g (u : ℂ) := by rw [mul_one]
  rw [e] at h''
  simpa [Matrix.one_apply_ne hab] using h''

open scoped Matrix.Norms.Operator in
/-- Property 5 at the real point `ξ = u ∈ [0,1)` (`m = 1`, `σ₁ = σ₂`): for the constants `C, c` of
`Prop5Decay d Λ` and `0 < g ≤ Λ`,
`‖Θ_u(a,b)‖ ≤ C B_{u,|b-a|₁} e^{-c |b-a|₁/ℓ_u}` (translation invariance `Theta_apply_add_right`). -/
private theorem kellStar_theta_le {d : ℕ} {Λ C c : ℝ}
    (hP : ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → ∀ σ₁ σ₂ : Bool, ∀ a : Zd d L,
          haveI : NeZero L := ⟨by omega⟩
          ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖
            ≤ C * Bparam d L g t (zdistD d L a)
                * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t))
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) {g : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) {u : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u < 1) (a b : Zd d L) :
    ‖Theta d L g (u : ℂ) a b‖ ≤
      C * Bparam d L g u (zdistD d L (a - b)) * Real.exp (-c * (zdistD d L (a - b) : ℝ) / ellT L g u) := by
  have hξ : ‖(u : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hu0]; exact hu1
  have htr : Theta d L g (u : ℂ) a b = Theta d L g (u : ℂ) 0 (b - a) := by
    have h := Theta_apply_add_right_of_three_le (d := d) (g := g) hL hξ 0 (b - a) a
    simpa using h
  have h5 := hP L hL g hg hgΛ u hu0 hu1 1 (by simp) true true (b - a)
  have hs : (u : ℂ) * (PropSpin (1 : ℂ) true * PropSpin (1 : ℂ) true) = (u : ℂ) := by
    simp [PropSpin]
  rw [hs] at h5
  have hd : zdistD d L (b - a) = zdistD d L (a - b) := by
    rw [← neg_sub a b, zdistD_neg]
  rw [hd] at h5
  rw [htr]
  exact h5

/-! ## The pinned theorem -/

/-- **Pin E.3g (`Kell*`)** (`KellStar:311`): eventually, beyond `δ ℓ*_u`, `Θ_u` and
`Θ_s⁻¹ Θ_u = ukerMat 1 s u` are `≤ W^{-D}`, uniformly in `0 ≤ s ≤ u ≤ t_n`.  Property 5
(`prop5Decay_holds`, proved) bounds `Θ_u`; the amplitude is `B_{u,K} ≤ 2 (1-u)⁻¹ ≤ 2 W^{A/𝔠}`,
`A = max(1-τ, 0)`, on the range `1 - t ≥ N^{-1+τ}` (`RangeCond`, `Bandwidth`), and
`(log W)^{3/2}` beats `log W` since `W → ∞` (`Bandwidth`, `SizeTendsto`). -/
theorem kellStarEv (d : ℕ) : KellStarEv d := by
  intro sz 𝔠 Λ τ δ D t hd h𝔠 hΛ hτ hδ hT hBW hRC ht hlam
  obtain ⟨C, hC, c, hc, hP⟩ := prop5Decay_holds d Λ hd hΛ
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = max (1 - τ) 0 := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; exact le_max_right _ _
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * C + A / 𝔠 + |D| := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hcδ : 0 < c * δ := mul_pos hc hδ
  have hNc : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
    (tendsto_rpow_atTop h𝔠).comp hT
  have hWtop : Tendsto (fun n => (sz.W n : ℝ)) atTop atTop :=
    tendsto_atTop_mono' _ hBW hNc
  have hxtop : Tendsto (fun n => Real.log (sz.W n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hWtop
  have hX := (tendsto_atTop.1 hxtop) (max 1 ((K / (c * δ)) ^ 2))
  filter_upwards [hBW, hRC, hlam, hX] with n hBn hRn hlamn hXn
  intro s u hs0 hsu hut a b hfar
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu1 : u < 1 := lt_of_le_of_lt hut (ht n)
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  have hW1 : 1 ≤ sz.W n := sz.W_pos n
  have hWpos : (0 : ℝ) < sz.W n := by exact_mod_cast sz.W_pos n
  have hx1 : 1 ≤ Real.log (sz.W n : ℝ) := (le_max_left _ _).trans hXn
  have hx0 : 0 < Real.log (sz.W n : ℝ) := by linarith
  have hsq : 2 * C + A / 𝔠 + |D| ≤ c * δ * Real.sqrt (Real.log (sz.W n : ℝ)) := by
    have hA' : 0 ≤ K / (c * δ) := by positivity
    have h1 : (K / (c * δ)) ^ 2 ≤ Real.log (sz.W n : ℝ) := (le_max_right _ _).trans hXn
    have h2 := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq hA', div_le_iff₀ hcδ] at h2
    rw [← hK]
    linarith
  -- the size `N ≥ 1` and the amplitude `(1-u)⁻¹ ≤ W^{A/𝔠}`
  have hNpos : 0 < sz.size n := by
    unfold Sizes.size
    exact pow_pos (Nat.mul_pos (sz.W_pos n) (by omega)) d
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hNpos
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hx : 0 < 1 - u := by linarith
  have hamp : (1 - u)⁻¹ ≤ (sz.W n : ℝ) ^ (A / 𝔠) := by
    have h1 : (((sz.size n : ℕ) : ℝ) ^ (-1 + τ))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 - τ) := by
      rw [← Real.rpow_neg hN0.le]
      exact le_of_eq (by congr 1; ring)
    have h2 : (1 - u)⁻¹ ≤ (((sz.size n : ℕ) : ℝ) ^ (-1 + τ))⁻¹ :=
      inv_anti₀ (Real.rpow_pos_of_pos hN0 _) (hRn.trans (by linarith))
    have h3 : ((sz.size n : ℕ) : ℝ) ^ (1 - τ) ≤ ((sz.size n : ℕ) : ℝ) ^ A :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by rw [hA]; exact le_max_left _ _)
    exact h2.trans (h1.trans (h3.trans (sz.size_rpow_le_W_rpow h𝔠 n hBn hA0)))
  -- the `ℓ_u`-scale and the exponential
  have hℓ : 0 < ellT (sz.L n) (sz.lam n) u := ellT_pos (by exact_mod_cast (by omega : 1 ≤ sz.L n))
  have hdist : δ * (Real.log (sz.W n : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (sz.lam n) u) ≤
      (zdistD d (sz.L n) (a - b) : ℝ) := by
    refine hfar.trans ?_
    exact_mod_cast zdistInf_le_zdistD d (sz.L n) (a - b)
  have hexp : Real.exp (-c * (zdistD d (sz.L n) (a - b) : ℝ) / ellT (sz.L n) (sz.lam n) u) ≤
      Real.exp (-(c * δ * Real.log (sz.W n : ℝ) ^ ((3 : ℝ) / 2))) := by
    apply Real.exp_le_exp.mpr
    rw [neg_mul, neg_div, neg_le_neg_iff, le_div_iff₀ hℓ]
    nlinarith
  have hΘ : ‖Theta d (sz.L n) (sz.lam n) (u : ℂ) a b‖ ≤ (sz.W n : ℝ) ^ (-D) := by
    have h5 := kellStar_theta_le hP (sz.L n) hL3 hlamn.1 hlamn.2 hu0 hu1 a b
    have hB := kellStar_bparam_le d (sz.L n) (by omega) (sz.lam n) hu1 (zdistD d (sz.L n) (a - b))
    calc ‖Theta d (sz.L n) (sz.lam n) (u : ℂ) a b‖
        ≤ C * Bparam d (sz.L n) (sz.lam n) u (zdistD d (sz.L n) (a - b)) *
          Real.exp (-c * (zdistD d (sz.L n) (a - b) : ℝ) / ellT (sz.L n) (sz.lam n) u) := h5
      _ ≤ C * (2 * (sz.W n : ℝ) ^ (A / 𝔠)) *
          Real.exp (-(c * δ * Real.log (sz.W n : ℝ) ^ ((3 : ℝ) / 2))) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (hB.trans ?_) hC.le) hexp (Real.exp_pos _).le
          (by positivity)
        linarith
      _ = C * (2 * Real.exp (Real.log (sz.W n : ℝ) * (A / 𝔠))) *
          Real.exp (-(c * δ * Real.log (sz.W n : ℝ) ^ ((3 : ℝ) / 2))) := by
        rw [Real.rpow_def_of_pos hWpos]
      _ ≤ Real.exp (Real.log (sz.W n : ℝ) * (-D)) := kellStar_arith hC hx1 hsq
      _ = (sz.W n : ℝ) ^ (-D) := (Real.rpow_def_of_pos hWpos _).symm
  refine ⟨hΘ, ?_⟩
  -- the pair is off the diagonal: `δ ℓ*_u > 0`
  have hab : a ≠ b := by
    intro hab
    have hz : (zdistInf d (sz.L n) (a - b) : ℝ) = 0 := by
      rw [hab, sub_self]
      have : zdistInf d (sz.L n) (0 : Zd d (sz.L n)) = 0 := by
        unfold zdistInf
        simp
      rw [this]; simp
    have hpos : 0 < δ * (Real.log (sz.W n : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (sz.lam n) u) := by
      have : 0 < Real.log (sz.W n : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hx0 _
      positivity
    linarith
  by_cases hu : u = 0
  · have hs : s = 0 := le_antisymm (hu ▸ hsu) hs0
    subst hu; subst hs
    have e : ukerMat d (sz.L n) (sz.lam n) 1 ((0 : ℝ)) ((0 : ℝ)) =
        Theta d (sz.L n) (sz.lam n) (((0 : ℝ)) : ℂ) := by
      simp [ukerMat]
    rw [e]
    exact hΘ
  · have hupos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
    have key := kellStar_uker_offdiag d (sz.L n) (sz.lam n) hL3 (s := s) hu0 hu1 hab
    have hn := congrArg norm key
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)] at hn
    have hle : u * ‖ukerMat d (sz.L n) (sz.lam n) 1 s u a b‖ ≤
        u * ‖Theta d (sz.L n) (sz.lam n) (u : ℂ) a b‖ := by
      rw [hn]
      exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    exact (le_of_mul_le_mul_left hle hupos).trans hΘ


/-! ## Compiled nonempty instance of `kellStarEv` (`d = 3`, the preflight sequence `sz0`)

Data: `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`, `N = (W L)^3`), `𝔠 = 1/6`
(`sz0_bandwidth`), `Λ = 1` (`0 < lam ≤ 1`), `τ = 1/2` with `t n = 3/4` (`N^{-1/2} ≤ 1/4`,
because `N ≥ 16`), `δ = 1/200`, `D = 1`; `s = 1/4`, `u = 1/2`.  Every hypothesis of `kellStarEv`
is discharged.  The far condition `δ ℓ*_u ≤ |a - b|_∞` is satisfied at every `n` by the pair
`a = (2(n+1), 2(n+1), 2(n+1))`, `b = 0` (`|a - b|_∞ = L/2`, `ℓ_u = 1`, `δ (log W)^{3/2} ≤ L/2`),
so the conclusion is applied at a genuinely far pair `a ≠ b` at the witness index. -/

end RBM.Path

end
