/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step2Defs
import RBM3D.Loop.KLTree
import RBM3D.Propagator.Pins
import RBM3D.Propagator.Prop5Hold
import RBM3D.Propagator.Props4

/-!
# ST2-06 (ticket T2093): `(eq:simpleboundK)` = `(eq:kn2sol_decay)`, the pin `STK2decay` proved

`stK2decay_holds (d : ℕ) : STK2decay d` (`Induction/Step2Defs.lean:568`): for `3 ≤ d`,
`‖𝒦^{(2)}_{u,σ,a}‖ ≤ C W^{-d} 𝒯̃^{L}_{u,D}(|a₁-a₂|)` uniformly in `D ≥ 0`, `0 ≤ u < 1`,
`|E| ≤ 2 - κ`, `0 < λ ≤ 𝔡⁻¹` (paper `3_5:457`, `3_5:518`).

Proof (all steps are merged facts).
1. `(Kn2sol)` = `KLK_two`: `𝒦^{(2)} = W^{-d} m₁ m₂ Θ_{u m₁ m₂}(a₁, a₂)`, and `‖m(σ)‖ = 1`
   (`norm_mSigma`, `|E| ≤ 2`), so `‖𝒦^{(2)}‖ = W^{-d} ‖Θ(a₁, a₂)‖`.
2. Translation invariance (`Theta_apply_add_right_of_three_le`, `‖u m₁ m₂‖ = u < 1`):
   `Θ(a₁, a₂) = Θ(0, a₂ - a₁)`.
3. `prop:ThfadC` = `Prop5Decay` (proved, `prop5Decay_holds`, constants `(d, 𝔡⁻¹)` only):
   `‖Θ(0,x)‖ ≤ C₅ B_{u,ρ} e^{-cρ/ℓ_u}` with `ρ = |x|_1` (`zdistD`).
4. With `r = |x|_∞` (`zdistInf`): `r ≤ ρ` (`zdistInf_le_zdistD`), `B` is non-increasing, and
   `√y ≤ c y + 1/(4c)` (`(2c√y - 1)² ≥ 0`), so `e^{-cρ/ℓ} ≤ e^{1/(4c)} e^{-√(r/ℓ)}`: the constant is
   `C = C₅ e^{1/(4c)}`.  Only the direction `r ≤ ρ` of the `ℓ¹`/`L^∞` comparison is used; the factor
   `d` of `zdistD ≤ d · zdistInf` and the doubling of `𝒯` (which needs an `L`-dependent constant,
   `Evolution/PropTInf.lean`) are not needed.
5. `r ≤ L` (`zdist ≤ L`), so `min r L = r` in `tailW`, and `tailW ≥ 𝒯_u(r)` (`le_max_left`):
   the floor `W^{-D}` only enlarges the profile, and `D ≥ 0` plays no role.

The statement of the pin is used exactly (it has no `λ`-lower bound, no `L^d ≤ W^K`, and `∀ n`).
The `λ > L` case needs no split: `ℓ_u = min (max (λ/√(1-u)) 1) L` is the same on both sides.

Port: the `n = 2` tree formula and the Theta bound correspond to RBM2D `Path/KellStar.lean:39`
(`KpmBoundProp5`) and `:240` (`kpmBoundProp5`) at `c9a24cf`; no text is copied (that statement is
`≤ C (1 + log L) M_u⁻¹` without decay in `|a - b|`; here the decay comes from `Prop5Decay`).
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Gauss

/-- `𝒦^{(2)}` of a loop index of length `2` (the shape of `KLK_two`). -/
private theorem k2d_KLloopOf_two {d L : ℕ} (σ : Fin 2 → Bool) (a : Fin 2 → Zd d L) :
    KLloopOf d L σ a = ⟨[σ 0, σ 1], [a 0, a 1]⟩ := by
  simp [KLloopOf, List.ofFn_succ]

/-- `zdistInf` is even. -/
private theorem k2d_zdistInf_neg {d L : ℕ} (x : Zd d L) [NeZero L] :
    zdistInf d L (-x) = zdistInf d L x := by
  simp only [zdistInf, Pi.neg_apply, zdist_neg]

/-- `zdist L u ≤ L`, so `zdistInf d L x ≤ L`. -/
private theorem k2d_zdistInf_le {d L : ℕ} (x : Zd d L) : zdistInf d L x ≤ L :=
  Finset.sup_le fun _ _ => (min_le_right _ _).trans (Nat.sub_le _ _)

/-- `√y ≤ c y + 1/(4c)` for `c > 0`: the elementary step that turns `e^{-c y}` into `e^{-√y}`. -/
private theorem k2d_sqrt_le {c : ℝ} (hc : 0 < c) (y : ℝ) (hy : 0 ≤ y) :
    Real.sqrt y ≤ c * y + 1 / (4 * c) := by
  set s := Real.sqrt y with hs
  have hy' : y = s ^ 2 := (Real.sq_sqrt hy).symm
  rw [hy', ← sub_nonneg]
  have : c * s ^ 2 + 1 / (4 * c) - s = (2 * c * s - 1) ^ 2 / (4 * c) := by
    field_simp
    ring
  rw [this]
  positivity

/-- **The tail bound of one propagator entry** from the decay of `Θ_ξ(0, ·)` in the `ℓ¹` distance:
`‖Θ_ξ(a,b)‖ ≤ C₅ e^{1/(4c)} 𝒯_t(|a-b|_∞)` (`t` enters only through `B`, `ℓ`). -/
private theorem k2d_theta_tail {d : ℕ} {C₅ c : ℝ} (hC₅ : 0 < C₅) (hc : 0 < c) {L : ℕ}
    [NeZero L] (hL : 3 ≤ L) {g t : ℝ} {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    (H : ∀ x : Zd d L, ‖Theta d L g ξ 0 x‖ ≤
      C₅ * Bparam d L g t (zdistD d L x) * Real.exp (-c * (zdistD d L x : ℝ) / ellT L g t))
    (a b : Zd d L) :
    ‖Theta d L g ξ a b‖ ≤
      C₅ * Real.exp (1 / (4 * c)) * tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ) := by
  have htr : Theta d L g ξ a b = Theta d L g ξ 0 (b - a) := by
    have h := Theta_apply_add_right_of_three_le (g := g) hL hξ 0 (b - a) a
    simpa using h
  rw [htr]
  refine (H (b - a)).trans ?_
  have hr : zdistInf d L (a - b) = zdistInf d L (b - a) := by
    rw [← k2d_zdistInf_neg (b - a), neg_sub]
  rw [hr]
  set x := b - a with hx
  have hrρ : ((zdistInf d L x : ℕ) : ℝ) ≤ (zdistD d L x : ℝ) := by
    exact_mod_cast zdistInf_le_zdistD d L x
  have hr0 : (0 : ℝ) ≤ ((zdistInf d L x : ℕ) : ℝ) := Nat.cast_nonneg _
  have hℓ : 0 < ellT L g t := ellT_pos (by exact_mod_cast (by omega : 1 ≤ L))
  have hB : Bparam d L g t (zdistD d L x) ≤ BparamR d L g t ((zdistInf d L x : ℕ) : ℝ) := by
    rw [← BparamR_natCast]
    exact BparamR_antitone hr0 hrρ
  have hB0 : 0 ≤ Bparam d L g t (zdistD d L x) := by
    rw [← BparamR_natCast]
    exact BparamR_nonneg (Nat.cast_nonneg _)
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

/-- **`(eq:simpleboundK)` = `(eq:kn2sol_decay)` (`3_5:457`, `518`): the pin `STK2decay` holds.**
Constants first (`κ, 𝔡`), then `C = C₅ e^{1/(4c)}` with `(C₅, c)` the constants of `Prop5Decay d 𝔡⁻¹`,
independent of the sizes, `n`, `E`, `u`, `D`, `σ`, `a`. -/
theorem stK2decay_holds (d : ℕ) : STK2decay d := by
  intro hd κ 𝔡 hκ h𝔡
  obtain ⟨C₅, hC₅, c, hc, H⟩ := prop5Decay_holds d 𝔡⁻¹ hd (inv_pos.2 h𝔡)
  refine ⟨C₅ * Real.exp (1 / (4 * c)), by positivity, ?_⟩
  intro sz n E u D hlam hlam' hE hu0 hu1 hD σ a
  have hE2 : |E| ≤ 2 := by linarith
  have hL : 3 ≤ sz.L n := sz.three_le_L n
  have hm : ‖mSigma E (σ 0) * mSigma E (σ 1)‖ = 1 := by
    rw [norm_mul, norm_mSigma hE2, norm_mSigma hE2, mul_one]
  have hξ : ‖(u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))‖ < 1 :=
    norm_mul_mSigma_lt_one hE2 hu0 hu1 (σ 0) (σ 1)
  have hK : STKloop sz n E u σ a =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (mSigma E (σ 0) * mSigma E (σ 1)) *
        Theta d (sz.L n) (sz.lam n) ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) (a 0) (a 1) := by
    unfold STKloop
    rw [k2d_KLloopOf_two, KLK_two]
  have hθ := k2d_theta_tail (d := d) (L := sz.L n) (g := sz.lam n) (t := u) hC₅ hc hL hξ
    (fun x => H (sz.L n) hL (sz.lam n) hlam hlam' u hu0 hu1 (mE E) (norm_mE hE2) (σ 0) (σ 1) x)
    (a 0) (a 1)
  have hr : ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast k2d_zdistInf_le (a 0 - a 1)
  have hmin : min ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ((sz.L n : ℕ) : ℝ) =
      ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) := min_eq_left hr
  have hW0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  have htail : tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤
      tailW d (sz.L n) (sz.lam n) u ((sz.L n : ℕ) : ℝ) ((sz.W n : ℕ) : ℝ) D
        ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) := by
    unfold tailW
    rw [hmin]
    exact le_max_left _ _
  have hnorm : ‖STKloop sz n E u σ a‖ =
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
        ‖Theta d (sz.L n) (sz.lam n) ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) (a 0) (a 1)‖ := by
    rw [hK, norm_mul, norm_mul, hm, mul_one, norm_inv, norm_pow, Complex.norm_natCast]
  rw [hnorm]
  unfold STprof
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
        ‖Theta d (sz.L n) (sz.lam n) ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) (a 0) (a 1)‖
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
          (C₅ * Real.exp (1 / (4 * c)) *
            tailW d (sz.L n) (sz.lam n) u ((sz.L n : ℕ) : ℝ) ((sz.W n : ℕ) : ℝ) D
              ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (hθ.trans ?_) hW0
        exact mul_le_mul_of_nonneg_left htail (by positivity)
    _ = C₅ * Real.exp (1 / (4 * c)) *
          ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
            tailW d (sz.L n) (sz.lam n) u ((sz.L n : ℕ) : ℝ) ((sz.W n : ℕ) : ℝ) D
              ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) := by ring

/-! ### Compiled nonempty instances (`d = 3`, the merged preflight sequence `sz0`)

`sz0` at `n = 0`: `L = 4`, `W = 32`, `lam = 1/64` (`N = 2097152`, `sz0_values`), and the pin's
constants `κ = 𝔡 = 1/10` (so `lam ≤ 𝔡⁻¹ = 10`).  Every deterministic hypothesis is discharged. -/

open RBM.Gauss.SizesInst in
/-- **`stK2decay_holds`, instantiated** at `d = 3`, `n = 0` (`L = 4`, `W = 32`, `lam = 1/64`),
`E = 1/2`, `u = 1/2`, `D = 5`, all four sign patterns and all `a ∈ (Z_4^3)²`. -/
example :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L 0)),
      ‖STKloop sz0 0 (1 / 2) (1 / 2) σ a‖ ≤
        C * STprof sz0 0 (1 / 2) 5 ((sz0.L 0 : ℕ) : ℝ) (a 0) (a 1) := by
  obtain ⟨C, hC, hall⟩ := stK2decay_holds 3 (by norm_num) (1 / 10) (1 / 10) (by norm_num)
    (by norm_num)
  have hlam : 0 < sz0.lam 0 := by simp [sz0]
  have hlam' : sz0.lam 0 ≤ ((1 : ℝ) / 10)⁻¹ := by
    have : sz0.lam 0 = 1 / 64 := by norm_num [sz0]
    rw [this]; norm_num
  exact ⟨C, hC, fun σ a => hall sz0 0 (1 / 2) (1 / 2) 5 hlam hlam' (by norm_num [abs_of_pos])
    (by norm_num) (by norm_num) (by norm_num) σ a⟩

open RBM.Gauss.SizesInst in
/-- The same at `n = 1` (`L = 8`, `W = 1024`, `lam = 1/4096`), `E = 0`, `u = 99/100` (near `1`),
`D = 0`, at the concrete off-diagonal pair `a = (0, e₁)` and signs `(+, -)`. -/
example :
    ∃ C : ℝ, 0 < C ∧
      ‖STKloop sz0 1 0 (99 / 100) ![true, false] ![0, Pi.single 0 1]‖ ≤
        C * STprof sz0 1 (99 / 100) 0 ((sz0.L 1 : ℕ) : ℝ) 0 (Pi.single 0 1) := by
  obtain ⟨C, hC, hall⟩ := stK2decay_holds 3 (by norm_num) (1 / 10) (1 / 10) (by norm_num)
    (by norm_num)
  have hlam : 0 < sz0.lam 1 := by simp [sz0]
  have hlam' : sz0.lam 1 ≤ ((1 : ℝ) / 10)⁻¹ := by
    have : sz0.lam 1 = 1 / 4096 := by norm_num [sz0]
    rw [this]; norm_num
  refine ⟨C, hC, ?_⟩
  have := hall sz0 1 0 (99 / 100) 0 hlam hlam' (by norm_num) (by norm_num) (by norm_num)
    le_rfl ![true, false] ![0, Pi.single 0 1]
  simpa using this

end RBM.Gauss.Sizes
