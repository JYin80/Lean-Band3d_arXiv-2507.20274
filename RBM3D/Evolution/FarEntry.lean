/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step5Pins
import RBM3D.Induction.Step34Pins
import RBM3D.Induction.KDecay
import RBM3D.Green.Pins
import RBM3D.Green.GbEXP
import RBM3D.Path.KellStar
import RBM3D.Chain.CltGen

/-!
# The far-entry decay of the resolvent at the log scale (ticket T2141, row S5-19)

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): the far-entry bound used
in the proof of `lem;CLT` / `(eq:bound_isolated)` (`3_5:2245`, which cites [DYYY25]); the inputs
are `(GijGEX)` (`3_5:24`) and `(Eq:Gdecay_w)` (`1_2:1349`).  Port of
`RBM2D/Evolution/FarEntry.lean` at commit `c9a24cf` (cited `FarEntry:<line>`: the route of
`farEntryDecayPT` `:632`; the helpers `farEntry_zdist2_tri` `:106`, `farEntry_ind_gexRHS_le` `:504`,
`farEntry_pair_bounds` `:283`, `farEntry_term_step` `:533`) with the dictionary of the ticket:
`Step2LocalPT`/`Step2DecayPT` become the uniform `STLocalEntryU`/`STGdecayW` of `STStep2Concl`
read at a time sequence `τ ∈ [s,t]` (`prec_timeIcc_section`); `GbEXPHypV3` becomes the proved
`STGbEXPij` (`stGbEXPij_of_v3 (gbEXPV3 hd)`); `kellStarEv` is the RBM3D one
(`Path/KellStar.lean`); `Z2 ↦ Zd d`, `zdist2 ↦ zdistInf`; the `5 × 5` neighbours become the
`3^d × 3^d` cube neighbours of `STgexRHS`.

**Target.**  `STFarEntryAtLog sz E τ`: for every `c, D' > 0`, both charges, over all pairs of fine
lattice points, `‖(G_τ)_{xy}‖ 1[c (log W)³ ℓ_τ ≤ |[x]-[y]|_∞] ≺ W^{-D'}`.  The log-scale threshold
is the one of the consumer `STCltIsoConcl`; the drafted `W^{τ'} ℓ_τ` threshold follows since
`W^{τ'} ≥ c (log W)³` eventually, and is not stated.  **Theorem** `stFarEntryAtLog`: from
`STFlow`, `STStep2Concl` on `[s,t]` (only `STLocalEntryU` and `STGdecayW` are used) and a time
sequence `τ ∈ [s,t]`.

Route (as RBM2D): (asGMc) at `τ` from `STLocalEntryU` (the indicator `STindMax … W^{-ε₀}` is `1`
off a small event); `(GijGEX)` from `STGbEXPij`; on the far set the term `W^{-d} 1_{|a-b|≤1}` of
`STgexRHS` vanishes and the `2·9^d` neighbouring loops `𝓛^{(2)}_{(a',b')}` remain, with
`|a'-b'|_∞ ≥ (c (log W)³ - 2) ℓ_τ`; `𝒦` by `kellStarEv` (`δ = 1`, `(log W)^{3/2} ℓ_τ ≤ |a'-b'|`;
`𝒦^{(2)}_{(+,-)} = W^{-d} Θ_τ` by `KLK_two`, `KLmSigma_mul_not`); `𝓛 - 𝒦` by `STGdecayW` at
`D = 2D'` (the loss `((1-s)/(1-τ))^{C_d}` and `B_{τ,·}` are powers of `N`, killed by
`exp(-(c (log W)³ - 2)^{1/2})`); then `|G|² ≺ W^{-2D'}` gives `|G| ≺ W^{-D'}`.  The charge
`σ = false` is the transpose of `σ = true` (`H` Hermitian).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ## 1. Generic facts -/

/-- A failure event eventually contained in the union of three failure events (each at its own
exponent `τᵢ`).  As `StochDomAt.of_subset_union` (`Defs/StochDomAt.lean:355`) with three events:
`3 N^{-(D+1)} ≤ N^{-D}` once `N ≥ 3`. -/
private theorem farEntry_union3 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}
    (hsize : Tendsto size atTop atTop) {U U₁ U₂ U₃ : ℕ → Type*}
    {ξ ζ : ∀ l, U l → Ω → ℝ} {f₁ g₁ : ∀ l, U₁ l → Ω → ℝ} {f₂ g₂ : ∀ l, U₂ l → Ω → ℝ}
    {f₃ g₃ : ∀ l, U₃ l → Ω → ℝ}
    (h₁ : StochDomAt P size f₁ g₁) (h₂ : StochDomAt P size f₂ g₂) (h₃ : StochDomAt P size f₃ g₃)
    (hsub : ∀ τ > (0 : ℝ), ∃ τ₁ > (0 : ℝ), ∃ τ₂ > (0 : ℝ), ∃ τ₃ > (0 : ℝ),
      ∀ᶠ l : ℕ in atTop, badSetAt size ξ ζ τ l ⊆
        badSetAt size f₁ g₁ τ₁ l ∪ badSetAt size f₂ g₂ τ₂ l ∪ badSetAt size f₃ g₃ τ₃ l) :
    StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ₁, hτ₁, τ₂, hτ₂, τ₃, hτ₃, hs⟩ := hsub τ hτ
  filter_upwards [hs, h₁ τ₁ hτ₁ (D + 1) (by linarith), h₂ τ₂ hτ₂ (D + 1) (by linarith),
    h₃ τ₃ hτ₃ (D + 1) (by linarith), hsize.eventually (eventually_ge_atTop 3)] with l h0 h1 h2 h3 h4
  have hN3 : (3 : ℝ) ≤ (size l : ℝ) := by exact_mod_cast h4
  have hN0 : (0 : ℝ) < (size l : ℝ) := by linarith
  have hp : (0 : ℝ) ≤ (size l : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg hN0.le _
  have h33 : 3 * (size l : ℝ) ^ (-(D + 1)) ≤ (size l : ℝ) ^ (-D) := by
    have e : (size l : ℝ) ^ (-(D + 1)) = (size l : ℝ) ^ (-D) * (size l : ℝ)⁻¹ := by
      rw [show -(D + 1) = -D + (-1) by ring, Real.rpow_add hN0, Real.rpow_neg_one]
    rw [e]
    have hD0 : 0 ≤ (size l : ℝ) ^ (-D) := Real.rpow_nonneg hN0.le _
    have h3N : 3 * (size l : ℝ)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hN0]; exact hN3
    nlinarith
  calc P (badSetAt size ξ ζ τ l)
      ≤ P (badSetAt size f₁ g₁ τ₁ l ∪ badSetAt size f₂ g₂ τ₂ l ∪ badSetAt size f₃ g₃ τ₃ l) :=
        measure_mono h0
    _ ≤ P (badSetAt size f₁ g₁ τ₁ l ∪ badSetAt size f₂ g₂ τ₂ l) + P (badSetAt size f₃ g₃ τ₃ l) :=
        measure_union_le _ _
    _ ≤ (P (badSetAt size f₁ g₁ τ₁ l) + P (badSetAt size f₂ g₂ τ₂ l)) +
          P (badSetAt size f₃ g₃ τ₃ l) := by
        gcongr; exact measure_union_le _ _
    _ ≤ (ENNReal.ofReal ((size l : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((size l : ℝ) ^ (-(D + 1)))) +
          ENNReal.ofReal ((size l : ℝ) ^ (-(D + 1))) := by gcongr
    _ = ENNReal.ofReal (3 * (size l : ℝ) ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add hp hp, ← ENNReal.ofReal_add (by positivity) hp]
        congr 1; ring
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal h33


section Lattice

variable {d L : ℕ} [NeZero L]

private theorem farEntry_zdistInf_add_le (x y : Zd d L) :
    zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y := by
  unfold zdistInf
  refine Finset.sup_le fun i _ => ?_
  calc zdist L ((x + y) i) = zdist L (x i + y i) := rfl
    _ ≤ zdist L (x i) + zdist L (y i) := zdist_add_le L (x i) (y i)
    _ ≤ _ := Nat.add_le_add
        (Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i))
        (Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i))

private theorem farEntry_zdistInf_neg (x : Zd d L) : zdistInf d L (-x) = zdistInf d L x := by
  unfold zdistInf
  exact Finset.sup_congr rfl fun i _ => by simp [zdist_neg]

omit [NeZero L] in
private theorem farEntry_zdistInf_zero : zdistInf d L (0 : Zd d L) = 0 := by
  unfold zdistInf
  simp

private theorem farEntry_zdistInf_comm (a b : Zd d L) :
    zdistInf d L (a - b) = zdistInf d L (b - a) := by
  rw [← neg_sub b a, farEntry_zdistInf_neg]

end Lattice

/-! ### The charge `σ = false` is the transpose of `σ = true` -/

section Charge

/-- `G(-) = G(+)^*`: `Gres H z false = (Gres H z true)ᴴ` for Hermitian `H` (`ST_Gres_false`,
`Induction/Step2Iterate.lean:1198`, copied). -/
private theorem farEntry_Gres_false {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (z : ℂ) : Gres H z false = (Gres H z true)ᴴ := by
  unfold Gres
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.conjTranspose_nonsing_inv]
  congr 1
  rw [Matrix.conjTranspose_sub, hH.eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  simp

end Charge


/-! ## 2. Arithmetic in `x = log W` -/

section Arith

/-- The threshold `X₀(c, K)` of `log W` beyond which the arithmetic below holds. -/
private def farEntry_X0 (c K : ℝ) : ℝ := max 1 ((K ^ 2 + 4 * K + 10) / c)

private theorem farEntry_X0_le {c K x : ℝ} (hc : 0 < c) (hx : farEntry_X0 c K ≤ x) :
    1 ≤ x ∧ K ^ 2 + 4 * K + 10 ≤ c * x := by
  refine ⟨(le_max_left _ _).trans hx, ?_⟩
  have h := (le_max_right _ _).trans hx
  rw [div_le_iff₀ hc] at h
  linarith

/-- `x^{3/2} + 2 ≤ c x³` for `x ≥ 1`, `c x ≥ 4`. -/
private theorem farEntry_log_arith {c x : ℝ} (h1 : 1 ≤ x) (h4 : 4 ≤ c * x) :
    x ^ ((3 : ℝ) / 2) + 2 ≤ c * x ^ 3 := by
  have h32 : x ^ ((3 : ℝ) / 2) ≤ x ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le h1 (show (3 : ℝ) / 2 ≤ 2 by norm_num)
    rwa [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
  have hx2 : 1 ≤ x ^ 2 := one_le_pow₀ h1
  have : 4 * x ^ 2 ≤ c * x * x ^ 2 := mul_le_mul_of_nonneg_right h4 (sq_nonneg x)
  nlinarith

/-- `4 W^K e^{-√y} ≤ 1` when `√y ≥ K log W + 2`, which holds for `y ≥ c (log W)³ - 2` and
`log W` large (`K² + 4K + 6 ≤ c log W`, `log W ≥ 1`). -/
private theorem farEntry_exp_arith {K c W y : ℝ} (hK : 0 ≤ K) (hW : 0 < W)
    (hx1 : 1 ≤ Real.log W) (hx2 : K ^ 2 + 4 * K + 6 ≤ c * Real.log W)
    (hy : c * Real.log W ^ 3 - 2 ≤ y) :
    4 * W ^ K * Real.exp (-(y ^ (1 / 2 : ℝ))) ≤ 1 := by
  set x := Real.log W with hxdef
  have hx0 : 0 ≤ x := by linarith
  have hcube : (K * x + 2) ^ 2 ≤ c * x ^ 3 - 2 := by
    have a1 : (K ^ 2 + 4 * K + 6) * x ^ 2 ≤ c * x * x ^ 2 :=
      mul_le_mul_of_nonneg_right hx2 (sq_nonneg x)
    have a2 : 0 ≤ K * (x * (x - 1)) := mul_nonneg hK (mul_nonneg hx0 (by linarith))
    have a3 : 0 ≤ x ^ 2 - 1 := by nlinarith
    nlinarith
  have hsq : K * x + 2 ≤ y ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    have h1 : (K * x + 2) ^ 2 ≤ y := by linarith
    calc K * x + 2 = Real.sqrt ((K * x + 2) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt y := Real.sqrt_le_sqrt h1
  have hWK : W ^ K = Real.exp (x * K) := Real.rpow_def_of_pos hW K
  have h2 : (4 : ℝ) ≤ Real.exp 2 := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    calc (4 : ℝ) = 2 * 2 := by norm_num
      _ ≤ Real.exp 1 * Real.exp 1 := mul_le_mul h1 h1 (by norm_num) (by positivity)
      _ = Real.exp 2 := by rw [← Real.exp_add]; norm_num
  have h3 : Real.exp (x * K) * Real.exp (-(y ^ (1 / 2 : ℝ))) ≤ Real.exp (-2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  have h4 : Real.exp (-2) * Real.exp 2 = 1 := by rw [← Real.exp_add]; norm_num
  have h5 : 0 < Real.exp (-2) := Real.exp_pos _
  calc 4 * W ^ K * Real.exp (-(y ^ (1 / 2 : ℝ)))
      = 4 * (Real.exp (x * K) * Real.exp (-(y ^ (1 / 2 : ℝ)))) := by rw [hWK]; ring
    _ ≤ 4 * Real.exp (-2) := by gcongr
    _ ≤ Real.exp 2 * Real.exp (-2) := by gcongr
    _ = 1 := by rw [mul_comm, h4]

end Arith


/-! ## 3. Deterministic bounds at one size index -/

section PerSize

variable {d : ℕ} (sz : Sizes d)

/-- `B_{u,K} ≤ 2 (1-u)⁻¹` for `u < 1`, `L ≥ 1` (`kellStar_bparam_le`, `Path/KellStar.lean:67`,
copied). -/
private theorem farEntry_bparam_le (L : ℕ) (hL : 1 ≤ L) (g : ℝ) {u : ℝ} (hu : u < 1) (K : ℕ) :
    Bparam d L g u K ≤ 2 * (1 - u)⁻¹ := by
  have hx : 0 < 1 - u := by linarith
  have hn : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  unfold Bparam
  rw [abs_of_pos hx]
  have hxi : 0 ≤ (1 - u)⁻¹ := inv_nonneg.mpr hx.le
  have h1 : (g ^ 2 + (1 - u))⁻¹ * (((K : ℝ) + 1) ^ (d - 2))⁻¹ ≤ (1 - u)⁻¹ := by
    have a1 : (g ^ 2 + (1 - u))⁻¹ ≤ (1 - u)⁻¹ := inv_anti₀ hx (by nlinarith [sq_nonneg g])
    have a2 : (((K : ℝ) + 1) ^ (d - 2))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    calc (g ^ 2 + (1 - u))⁻¹ * (((K : ℝ) + 1) ^ (d - 2))⁻¹ ≤ (1 - u)⁻¹ * 1 :=
          mul_le_mul a1 a2 (by positivity) hxi
      _ = (1 - u)⁻¹ := mul_one _
  have h2 : ((L : ℝ) ^ d * (1 - u))⁻¹ ≤ (1 - u)⁻¹ := by
    have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hL)
    exact inv_anti₀ hx (by nlinarith)
  linarith

private theorem farEntry_size_real (n : ℕ) :
    ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
  change (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) = _
  push_cast; ring

private theorem farEntry_W_le_size (hd : 1 ≤ d) (n : ℕ) :
    ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  have hL : 0 < sz.L n := by have := sz.three_le_L n; omega
  have hW : 0 < sz.W n := sz.W_pos n
  have h1 : sz.W n ≤ sz.W n * sz.L n := Nat.le_mul_of_pos_right _ hL
  have h2 : sz.W n * sz.L n ≤ (sz.W n * sz.L n) ^ d := Nat.le_self_pow (by omega) _
  exact_mod_cast h1.trans h2

/-- **`W^{-d} B_{u,K} ≤ W^{-2𝔡} + W^{-δ}`** (the control of `(Gt_bound)`): the first term of `B` is
`≤ (ilambda² W^d)⁻¹ ≤ W^{-2𝔡}` (`(eq:WO)`, `Sizes.lam_sq_mul_pow_ge`), the zero-mode term is
`(N (1-u))⁻¹ ≤ N^{-δ} ≤ W^{-δ}` on the range `1 - u ≥ N^{-1+δ}`. -/
private theorem farEntry_stwb_le (hd : 1 ≤ d) (n : ℕ) {u 𝔡 δ : ℝ} (K : ℕ) (hδ : 0 < δ)
    (hu1 : u < 1)
    (hwo : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n)
    (hrange : ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - u) :
    sz.STWB n u K ≤ ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) + ((sz.W n : ℕ) : ℝ) ^ (-δ) := by
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hx : 0 < 1 - u := by linarith
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hlam0 : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hwo
  have hN : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d :=
    farEntry_size_real sz n
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
    rw [hN]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hW1) (one_le_pow₀ hL1)
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hWN := farEntry_W_le_size sz hd n
  unfold STWB Bparam
  rw [abs_of_pos hx, mul_add]
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  -- first term
  have t1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ * (((K : ℝ) + 1) ^ (d - 2))⁻¹) ≤
      ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) := by
    have a1 : (sz.lam n ^ 2 + (1 - u))⁻¹ ≤ (sz.lam n ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (by linarith)
    have a2 : (((K : ℝ) + 1) ^ (d - 2))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    have a3 : (sz.lam n ^ 2 + (1 - u))⁻¹ * (((K : ℝ) + 1) ^ (d - 2))⁻¹ ≤ (sz.lam n ^ 2)⁻¹ * 1 :=
      mul_le_mul a1 a2 (by positivity) (by positivity)
    have a4 := Sizes.lam_sq_mul_pow_ge sz n hwo
    have a5 : (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡))⁻¹ :=
      inv_anti₀ (Real.rpow_pos_of_pos hWpos _) a4
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ * (((K : ℝ) + 1) ^ (d - 2))⁻¹)
        ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2)⁻¹ * 1) :=
          mul_le_mul_of_nonneg_left a3 (by positivity)
      _ = (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
          rw [mul_one, ← mul_inv, mul_comm]
      _ ≤ (((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡))⁻¹ := a5
      _ = ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) := (Real.rpow_neg hWpos.le _).symm
  -- second term
  have t2 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ≤
      ((sz.W n : ℕ) : ℝ) ^ (-δ) := by
    have b1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ =
        (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ := by
      rw [hN, ← mul_inv, mul_assoc]
    have b2 : ((sz.size n : ℕ) : ℝ) ^ δ ≤ ((sz.size n : ℕ) : ℝ) * (1 - u) := by
      have h := mul_le_mul_of_nonneg_left hrange hN0.le
      rw [← Real.rpow_one_add' hN0.le (by linarith : (1 : ℝ) + (-1 + δ) ≠ 0)] at h
      simpa using h
    have b3 : ((sz.W n : ℕ) : ℝ) ^ δ ≤ ((sz.size n : ℕ) : ℝ) ^ δ :=
      Real.rpow_le_rpow hWpos.le hWN hδ.le
    rw [b1, Real.rpow_neg hWpos.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hWpos _) (b3.trans b2)
  linarith


/-- On the range `1 - u ≥ N⁻¹` the loss, `W^{-d} B_{u,0}` and `W^{-d} B_{u,K}` are powers of `N`:
`((1-s)/(1-u))^{C_d} (W^{-d}B_{u,0})^{1/5} (W^{-d}B_{u,K}) ≤ 4 N^{max(C_d,0) + 2}`
(`W^{-d} ≤ 1`, `B ≤ 2 (1-u)⁻¹ ≤ 2 N`, `(1-s)/(1-u) ≤ N`; the analogue of `farEntry_pair_bounds`,
`FarEntry:283`, `hN4`, and of `B45_far_main`, `hP2n`). -/
private theorem farEntry_loss_le (n : ℕ) {s u Cd : ℝ} (K : ℕ) (hs0 : 0 ≤ s) (hsu : s ≤ u)
    (hu1 : u < 1) (hN1u : ((sz.size n : ℕ) : ℝ)⁻¹ ≤ 1 - u) :
    ((1 - s) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) * sz.STWB n u K ≤
      4 * ((sz.size n : ℕ) : ℝ) ^ (max Cd 0 + 2) := by
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL1 : 1 ≤ sz.L n := by have := sz.three_le_L n; omega
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hx : 0 < 1 - u := by linarith
  have hWd1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ hW1
  have hinv : (1 - u)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
    have := inv_anti₀ (by positivity) hN1u
    rwa [inv_inv] at this
  have hstwb : ∀ K' : ℕ, 0 ≤ sz.STWB n u K' ∧ sz.STWB n u K' ≤ 2 * ((sz.size n : ℕ) : ℝ) := by
    intro K'
    have hB0 : 0 ≤ Bparam d (sz.L n) (sz.lam n) u K' := by unfold Bparam; positivity
    have hB := farEntry_bparam_le (d := d) (sz.L n) hL1 (sz.lam n) hu1 K'
    have hWi : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hWd1
    unfold STWB
    refine ⟨by positivity, ?_⟩
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) u K'
        ≤ 1 * Bparam d (sz.L n) (sz.lam n) u K' :=
          mul_le_mul_of_nonneg_right hWi hB0
      _ ≤ 2 * (1 - u)⁻¹ := by rw [one_mul]; exact hB
      _ ≤ 2 * ((sz.size n : ℕ) : ℝ) := by linarith
  obtain ⟨hK0, hK2⟩ := hstwb K
  obtain ⟨hB0, hB2⟩ := hstwb 0
  have hBctl : sz.Bctl n u = sz.STWB n u 0 := rfl
  rw [hBctl]
  have h2N : (1 : ℝ) ≤ 2 * ((sz.size n : ℕ) : ℝ) := by linarith
  have hB5 : (sz.STWB n u 0) ^ (1 / 5 : ℝ) ≤ 2 * ((sz.size n : ℕ) : ℝ) :=
    calc (sz.STWB n u 0) ^ (1 / 5 : ℝ) ≤ (2 * ((sz.size n : ℕ) : ℝ)) ^ (1 / 5 : ℝ) :=
          Real.rpow_le_rpow hB0 hB2 (by norm_num)
      _ ≤ (2 * ((sz.size n : ℕ) : ℝ)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h2N (by norm_num)
      _ = 2 * ((sz.size n : ℕ) : ℝ) := Real.rpow_one _
  have hratio1 : 1 ≤ (1 - s) / (1 - u) := by
    rw [le_div_iff₀ hx]; linarith
  have hratioN : (1 - s) / (1 - u) ≤ ((sz.size n : ℕ) : ℝ) := by
    rw [div_le_iff₀ hx]
    have h1 := mul_le_mul_of_nonneg_left hN1u hN0.le
    rw [mul_inv_cancel₀ hN0.ne'] at h1
    linarith
  have hpow : ((1 - s) / (1 - u)) ^ Cd ≤ ((sz.size n : ℕ) : ℝ) ^ (max Cd 0) :=
    calc ((1 - s) / (1 - u)) ^ Cd ≤ ((1 - s) / (1 - u)) ^ (max Cd 0) :=
          Real.rpow_le_rpow_of_exponent_le hratio1 (le_max_left _ _)
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (max Cd 0) :=
          Real.rpow_le_rpow (by linarith) hratioN (le_max_right _ _)
  have hP0 : 0 ≤ ((1 - s) / (1 - u)) ^ Cd := Real.rpow_nonneg (by linarith) _
  have hB50 : 0 ≤ (sz.STWB n u 0) ^ (1 / 5 : ℝ) := Real.rpow_nonneg hB0 _
  have hNC : ((sz.size n : ℕ) : ℝ) ^ (max Cd 0 + 2) =
      ((sz.size n : ℕ) : ℝ) ^ (max Cd 0) * (((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ)) := by
    rw [Real.rpow_add hN0, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  calc ((1 - s) / (1 - u)) ^ Cd * (sz.STWB n u 0) ^ (1 / 5 : ℝ) * sz.STWB n u K
      ≤ ((sz.size n : ℕ) : ℝ) ^ (max Cd 0) * (2 * ((sz.size n : ℕ) : ℝ)) *
          (2 * ((sz.size n : ℕ) : ℝ)) := by
        gcongr
    _ = 4 * ((sz.size n : ℕ) : ℝ) ^ (max Cd 0 + 2) := by rw [hNC]; ring


/-- `𝒦^{(2)}_{τ,σ,(a',b')} = W^{-d} Θ_τ(a',b')` for `σ ∈ {(+,-),(-,+)}`, so `‖𝒦‖ ≤ ‖Θ_τ(a',b')‖`
(`KLK_two`, `KLmSigma_mul_not`: `m(σ) m(-σ) = 1`).  RBM2D: `farEntry_Kpm_eq`, `FarEntry:266`. -/
private theorem farEntry_K_le (n : ℕ) {E τ D : ℝ} (hE : |E| ≤ 2)
    (hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ)) (a' b' : Zd d (sz.L n)) (σ : Fin 2 → Bool)
    (hσ : σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)))
    (hTh : ‖Theta d (sz.L n) (sz.lam n) (τ : ℂ) a' b'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)) :
    ‖sz.STKloop n E τ σ ![a', b']‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := by
  have hWd : ‖((((sz.W n : ℕ) : ℂ) ^ d)⁻¹)‖ ≤ 1 := by
    rw [norm_inv, norm_pow, Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hW1)
  have key : ∀ s₁ s₂ : Bool, mSigma E s₁ * mSigma E s₂ = 1 →
      ‖KLK d (sz.L n) (sz.lam n) (sz.W n) E τ ⟨[s₁, s₂], [a', b']⟩‖ ≤
        ((sz.W n : ℕ) : ℝ) ^ (-D) := by
    intro s₁ s₂ h1
    rw [KLK_two, h1]
    simp only [mul_one]
    rw [norm_mul]
    calc ‖((((sz.W n : ℕ) : ℂ) ^ d)⁻¹)‖ * ‖Theta d (sz.L n) (sz.lam n) (τ : ℂ) a' b'‖
        ≤ 1 * ((sz.W n : ℕ) : ℝ) ^ (-D) := mul_le_mul hWd hTh (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
  rcases hσ with rfl | rfl
  · unfold STKloop
    have := key true false (KLmSigma_mul_not hE true)
    simpa [KLloopOf, List.ofFn_succ] using this
  · unfold STKloop
    have := key false true (KLmSigma_mul_not hE false)
    simpa [KLloopOf, List.ofFn_succ] using this

/-- **The scalar tail of the far neighbour bound** (`farEntry_neighbour`, `farEntry_loop_le` is its part after the geometry):
if `r ≥ (c (log W)³ - 2) ℓ_τ`, `‖K‖ ≤ W^{-2D'}` and `‖L - K‖ ≤ N^{τ₃} (loss · B^{1/5} · STWB_r · e^{-√(r/ℓ)} + W^{-2D'})`,
then `‖L‖ ≤ 3 N^{τ₃} W^{-2D'}`.  Carrier-free (any `L`, `K` values): used by the band route and by the carrier route. -/
private theorem farEntry_loop_le (n : ℕ) {s τ 𝔠 c D' Cd τ₃ : ℝ} (Lv Kv : ℂ)
    (h𝔠 : 0 < 𝔠) (hc : 0 < c) (hD' : 0 < D') (hτ₃ : 0 ≤ τ₃)
    (hs0 : 0 ≤ s) (hsτ : s ≤ τ) (hτ1 : τ < 1)
    (hN1u : ((sz.size n : ℕ) : ℝ)⁻¹ ≤ 1 - τ)
    (hbw : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ))
    (hG : farEntry_X0 c ((max Cd 0 + 2) / 𝔠 + 2 * D') ≤ Real.log ((sz.W n : ℕ) : ℝ))
    {r : ℕ} (hdist : (c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 - 2) * ellT (sz.L n) (sz.lam n) τ ≤ (r : ℝ))
    (hK : ‖Kv‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-(2 * D')))
    (hdec : ‖Lv - Kv‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ₃ *
        (((1 - s) / (1 - τ)) ^ Cd * (sz.Bctl n τ) ^ (1 / 5 : ℝ) * sz.STWB n τ r *
            Real.exp (-((r : ℝ) / ellT (sz.L n) (sz.lam n) τ) ^ (1 / 2 : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-(2 * D')))) :
    ‖Lv‖ ≤ 3 * ((sz.size n : ℕ) : ℝ) ^ τ₃ * ((sz.W n : ℕ) : ℝ) ^ (-(2 * D')) := by
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  set G : ℝ := Real.log ((sz.W n : ℕ) : ℝ) with hGdef
  set ℓ : ℝ := ellT (sz.L n) (sz.lam n) τ with hℓdef
  set K₁ : ℝ := (max Cd 0 + 2) / 𝔠 + 2 * D' with hK₁
  have hK₁0 : 0 ≤ K₁ := by
    have : 0 ≤ (max Cd 0 + 2) / 𝔠 := div_nonneg (by have := le_max_right Cd 0; linarith) h𝔠.le
    rw [hK₁]; linarith
  obtain ⟨hG1, hG2⟩ := farEntry_X0_le hc hG
  have hℓ1 : 1 ≤ ℓ := one_le_ellT hL1
  have hℓpos : 0 < ℓ := by linarith
  -- the exponential
  have hy : c * G ^ 3 - 2 ≤ (r : ℝ) / ℓ := by
    rw [le_div_iff₀ hℓpos]; exact hdist
  have hexp := farEntry_exp_arith hK₁0 hWpos hG1 (by linarith) hy
  have hexp0 : 0 ≤ Real.exp (-((r : ℝ) / ℓ) ^ (1 / 2 : ℝ)) :=
    (Real.exp_pos _).le
  have hloss := farEntry_loss_le sz n (Cd := Cd) (r) hs0 hsτ hτ1 hN1u
  have hNW : ((sz.size n : ℕ) : ℝ) ^ (max Cd 0 + 2) ≤
      ((sz.W n : ℕ) : ℝ) ^ ((max Cd 0 + 2) / 𝔠) :=
    Sizes.size_rpow_le_W_rpow sz h𝔠 n hbw (by have := le_max_right Cd 0; linarith)
  have hfirst : ((1 - s) / (1 - τ)) ^ Cd * (sz.Bctl n τ) ^ (1 / 5 : ℝ) *
        sz.STWB n τ (r) *
        Real.exp (-((r : ℝ) / ℓ) ^ (1 / 2 : ℝ)) ≤
      ((sz.W n : ℕ) : ℝ) ^ (-(2 * D')) := by
    have hWD : 0 < ((sz.W n : ℕ) : ℝ) ^ (2 * D') := Real.rpow_pos_of_pos hWpos _
    have hsplit : ((sz.W n : ℕ) : ℝ) ^ K₁ =
        ((sz.W n : ℕ) : ℝ) ^ ((max Cd 0 + 2) / 𝔠) * ((sz.W n : ℕ) : ℝ) ^ (2 * D') :=
      Real.rpow_add hWpos _ _
    rw [hsplit] at hexp
    rw [Real.rpow_neg hWpos.le]
    calc ((1 - s) / (1 - τ)) ^ Cd * (sz.Bctl n τ) ^ (1 / 5 : ℝ) *
          sz.STWB n τ (r) *
          Real.exp (-((r : ℝ) / ℓ) ^ (1 / 2 : ℝ))
        ≤ (4 * ((sz.W n : ℕ) : ℝ) ^ ((max Cd 0 + 2) / 𝔠)) *
          Real.exp (-((r : ℝ) / ℓ) ^ (1 / 2 : ℝ)) := by
          refine mul_le_mul_of_nonneg_right (hloss.trans ?_) hexp0
          linarith
      _ = (4 * (((sz.W n : ℕ) : ℝ) ^ ((max Cd 0 + 2) / 𝔠) * ((sz.W n : ℕ) : ℝ) ^ (2 * D')) *
            Real.exp (-((r : ℝ) / ℓ) ^ (1 / 2 : ℝ))) *
            (((sz.W n : ℕ) : ℝ) ^ (2 * D'))⁻¹ := by field_simp
      _ ≤ 1 * (((sz.W n : ℕ) : ℝ) ^ (2 * D'))⁻¹ := by
          gcongr
      _ = (((sz.W n : ℕ) : ℝ) ^ (2 * D'))⁻¹ := one_mul _
  have hNτ : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ₃ := Real.one_le_rpow hN1 hτ₃
  have hW2 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-(2 * D')) := Real.rpow_nonneg hWpos.le _
  calc ‖Lv‖
      = ‖Kv + (Lv -
          Kv)‖ := by rw [add_sub_cancel]
    _ ≤ ‖Kv‖ +
          ‖Lv - Kv‖ := norm_add_le _ _
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ (-(2 * D')) + ((sz.size n : ℕ) : ℝ) ^ τ₃ *
          (((sz.W n : ℕ) : ℝ) ^ (-(2 * D')) + ((sz.W n : ℕ) : ℝ) ^ (-(2 * D'))) := by
        refine add_le_add hK (hdec.trans ?_)
        exact mul_le_mul_of_nonneg_left (add_le_add hfirst le_rfl) (by linarith)
    _ ≤ 3 * ((sz.size n : ℕ) : ℝ) ^ τ₃ * ((sz.W n : ℕ) : ℝ) ^ (-(2 * D')) := by
        nlinarith


/-- **The event `Ω(τ, ε₀)` holds** (asGMc, from `STLocalEntryU` at `τ`): with `c₀ = min(2𝔡, δ)` and
`ε₀ = c₀/4`, if `‖G_τ - M‖²_{xy} ≤ N^{𝔠 c₀/4} W^{-d} B_{τ,|[x]-[y]|}` for all `x, y` (the complement
of the failure event of `STLocalEntryU` at the exponent `𝔠 c₀/4`), `N^𝔠 ≤ W`,
`W^{-d} B ≤ W^{-2𝔡} + W^{-δ}` and `W^{c₀/4} ≥ 2`, then `‖G_τ - M‖_max ≤ W^{-ε₀}`, i.e.
`STindMax … W^{-ε₀} = 1` (RBM2D: `farEntry_local_le`, `FarEntry:425`, with `ε₀ = c/2`). -/
private theorem farEntry_indMax_eq_one (C : RBM.BA.FlowFM sz) (n : ℕ) (ω : sz.SeqΩ) {τ 𝔠 𝔡 δ : ℝ} (h𝔠 : 0 < 𝔠)
    (h𝔡 : 0 < 𝔡) (hδ : 0 < δ)
    (hbw : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ))
    (hW2 : (2 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (min (2 * 𝔡) δ / 4))
    (hSTWB : ∀ K : ℕ, sz.STWB n τ K ≤
      ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) + ((sz.W n : ℕ) : ℝ) ^ (-δ))
    (hb1 : ∀ x y : Idx d (sz.L n) (sz.W n), ‖C.GM n τ ω x y‖ ^ 2 ≤
      ((sz.size n : ℕ) : ℝ) ^ (𝔠 * (min (2 * 𝔡) δ / 4)) *
        sz.STWB n τ (zdistInf d (sz.L n) (sz.STblk n x - sz.STblk n y))) :
    RBM.BA.STindMaxg C n τ (((sz.W n : ℕ) : ℝ) ^ (-(min (2 * 𝔡) δ / 4))) ω = 1 := by
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  set c₀ : ℝ := min (2 * 𝔡) δ with hc₀
  have hc₀0 : 0 < c₀ := lt_min (by linarith) hδ
  set a : ℝ := W ^ (c₀ / 4) with hadef
  have ha2 : (2 : ℝ) ≤ a := hW2
  have ha0 : 0 < a := by linarith
  have hWc : W ^ c₀ = a ^ 4 := by
    rw [hadef, ← Real.rpow_natCast, ← Real.rpow_mul hWpos.le]
    congr 1; push_cast; ring
  have hNτ : ((sz.size n : ℕ) : ℝ) ^ (𝔠 * (c₀ / 4)) ≤ a := by
    have := Sizes.size_rpow_le_W_rpow sz h𝔠 n hbw (τ := 𝔠 * (c₀ / 4)) (by positivity)
    rwa [show 𝔠 * (c₀ / 4) / 𝔠 = c₀ / 4 by field_simp] at this
  have hstwb : ∀ K : ℕ, sz.STWB n τ K ≤ 2 * (a ^ 4)⁻¹ := by
    intro K
    have h1 : W ^ (-(2 * 𝔡)) ≤ W ^ (-c₀) :=
      Real.rpow_le_rpow_of_exponent_le hW1 (neg_le_neg (min_le_left _ _))
    have h2 : W ^ (-δ) ≤ W ^ (-c₀) :=
      Real.rpow_le_rpow_of_exponent_le hW1 (neg_le_neg (min_le_right _ _))
    have h3 : W ^ (-c₀) = (a ^ 4)⁻¹ := by rw [Real.rpow_neg hWpos.le, hWc]
    have := hSTWB K
    linarith
  have hinv : W ^ (-(c₀ / 4)) = a⁻¹ := by rw [Real.rpow_neg hWpos.le]
  unfold RBM.BA.STindMaxg
  have hall : ∀ x y : Idx d (sz.L n) (sz.W n), ‖C.GM n τ ω x y‖ ≤ W ^ (-(c₀ / 4)) := by
    intro x y
    have h2 := hb1 x y
    have h3 : ‖C.GM n τ ω x y‖ ^ 2 ≤ a * (2 * (a ^ 4)⁻¹) :=
      h2.trans (mul_le_mul hNτ (hstwb _) (by
        have := hSTWB (zdistInf d (sz.L n) (sz.STblk n x - sz.STblk n y))
        unfold STWB; unfold Bparam; positivity) ha0.le)
    have h4 : a * (2 * (a ^ 4)⁻¹) ≤ (a⁻¹) ^ 2 := by
      have : a * (2 * (a ^ 4)⁻¹) = 2 / a ^ 3 := by field_simp
      rw [this, inv_pow, ← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [pow_pos ha0 2, pow_pos ha0 3]
    rw [hinv]
    refine (pow_le_pow_iff_left₀ (n := 2) (norm_nonneg _) (inv_nonneg.2 ha0.le) two_ne_zero).1 ?_
    exact h3.trans h4
  simp [hall]

end PerSize

/-! ## 4. The pin and the theorem -/

end RBM.Gauss.Sizes

/-! ## 5. The carrier route (T2455): `STFarEntryAtLoggL`

The same argument over `C : FlowFM sz` and a law `μ`: the Green input (`GijGEX`) is the pin `STGijDecgL` (loop premise for both mixed
charges), the far field of `𝒦^{(2)}` is `STKfargL`, `M` enters through the Ward row `Σ_y ‖M_{xy}‖² ≤ 1` and the far smallness
`STMfarg`, the loops are the entries of the resolvent of `H₀ n + H_u` (`CltRepg`).  Ported with the dictionary of the band route; the
two-loop in entries is `RBM3D/Green/Pins.lean:350-440` (private there, copied: `64bdfd3`). -/

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes MeasureTheory

section LoopId

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem farEntry_gres_blockMat_true (H : Matrix (Idx d L W) (Idx d L W) ℂ)
    (z : ℂ) (x y : Vtx d L W) :
    Gres (blockMat d L W H) z true x y =
      Gres H z true ((splitEquiv d L W).symm x) ((splitEquiv d L W).symm y) := by
  unfold Gres blockMat
  simp only [ite_true]
  have e1 : H.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm -
        z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
      (H - z • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)).submatrix (splitEquiv d L W).symm
        (splitEquiv d L W).symm := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply]
  rw [e1, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.inv_submatrix_equiv]
  rfl

omit [NeZero W] in
private theorem farEntry_trace_pm_formula (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a b : Zd d L) :
    ((G * Eblk d L W a) * (Gᴴ * Eblk d L W b)).trace =
      ((((W : ℝ) ^ d)⁻¹ ^ 2 * ∑ v : Vtx d L W, ∑ w : Vtx d L W,
          (if v.1 = b ∧ w.1 = a then ‖G v w‖ ^ 2 else 0) : ℝ) : ℂ) := by
  have hE : ∀ c : Zd d L, Eblk d L W c = Matrix.diagonal fun x : Vtx d L W =>
      if x.1 = c then (((W : ℂ)) ^ d)⁻¹ else 0 := fun c => rfl
  rw [hE a, hE b]
  have h1 : G * Matrix.diagonal (fun x : Vtx d L W => if x.1 = a then (((W : ℂ)) ^ d)⁻¹ else 0) =
      Matrix.of fun i j => G i j * (if j.1 = a then (((W : ℂ)) ^ d)⁻¹ else 0) := by
    ext i j; simp [Matrix.mul_diagonal]
  have h2 : Gᴴ * Matrix.diagonal (fun x : Vtx d L W => if x.1 = b then (((W : ℂ)) ^ d)⁻¹ else 0) =
      Matrix.of fun i j => star (G j i) * (if j.1 = b then (((W : ℂ)) ^ d)⁻¹ else 0) := by
    ext i j; simp [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  rw [h1, h2]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hi : i.1 = b <;> by_cases hj : j.1 = a <;> simp [hi, hj]
  have h := Complex.mul_conj' (G i j)
  linear_combination (((W : ℂ) ^ d)⁻¹) ^ 2 * h

/-- **The two-loop in entries** (`Green/Pins.lean:418`, `loopFine_pm_formula`, copied): for a Hermitian `H`,
`𝓛_{(+,-),(a,b)} = W^{-2d} Σ_{y∈[b], x∈[a]} |G_{yx}|²`. -/
private theorem farEntry_loopFine_pm (H : Matrix (Idx d L W) (Idx d L W) ℂ) (hH : H.IsHermitian)
    (z : ℂ) (a b : Zd d L) :
    loopFine d L W H z ![true, false] ![a, b] =
      ((((W : ℝ) ^ d)⁻¹ ^ 2 * ∑ y : Idx d L W, ∑ x : Idx d L W,
          (if (split d L W y).1 = b ∧ (split d L W x).1 = a then ‖Gres H z true y x‖ ^ 2
            else 0) : ℝ) : ℂ) := by
  have hHb : (blockMat d L W H).IsHermitian := hH.submatrix _
  have hv : loopFine d L W H z ![true, false] ![a, b] =
      ((((W : ℝ) ^ d)⁻¹ ^ 2 * ∑ v : Vtx d L W, ∑ w : Vtx d L W,
          (if v.1 = b ∧ w.1 = a then ‖Gres (blockMat d L W H) z true v w‖ ^ 2 else 0) : ℝ) : ℂ) := by
    unfold loopFine loopM
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ]
    rw [RBM.Gauss.Sizes.farEntry_Gres_false hHb z, farEntry_trace_pm_formula]
  rw [hv]
  congr 1
  congr 1
  have hsum : ∀ F : Vtx d L W → Vtx d L W → ℝ, ∑ v, ∑ w, F v w =
      ∑ y : Idx d L W, ∑ x : Idx d L W, F (splitEquiv d L W y) (splitEquiv d L W x) := by
    intro F
    calc ∑ v, ∑ w, F v w = ∑ y, ∑ w, F (splitEquiv d L W y) w :=
          (Equiv.sum_comp (splitEquiv d L W) (fun v => ∑ w, F v w)).symm
      _ = _ := Finset.sum_congr rfl fun y _ =>
          (Equiv.sum_comp (splitEquiv d L W) (fun w => F (splitEquiv d L W y) w)).symm
  rw [hsum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  rw [farEntry_gres_blockMat_true, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

private theorem farEntry_loopFine_mp (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) (a b : Zd d L) :
    loopFine d L W H z ![false, true] ![a, b] = loopFine d L W H z ![true, false] ![b, a] := by
  unfold loopFine loopM
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  exact Matrix.trace_mul_comm _ _

/-- A mixed-charge pair is `(+,-)` or `(-,+)`. -/
private theorem farEntry_mixed_cases (σ : Fin 2 → Bool) (h : σ 0 ≠ σ 1) :
    σ = ![true, false] ∨ σ = ![false, true] := by
  have e : σ = ![σ 0, σ 1] := by ext i; fin_cases i <;> rfl
  rcases h0 : σ 0 with _ | _ <;> rcases h1 : σ 1 with _ | _
  · exact absurd (h0.trans h1.symm) h
  · right; rw [e, h0, h1]
  · left; rw [e, h0, h1]
  · exact absurd (h0.trans h1.symm) h

/-- **The loop bound**: for a Hermitian `H`, if `‖G - M‖_max ≤ m` and `Σ_x |M_{yx}|² ≤ 1` for every `y`, then
`‖𝓛^{(2)}_{(±,∓),(a,b)}‖ ≤ 2 m² + 2 W^{-d}` (`|G|² ≤ 2|G-M|² + 2|M|²`, `|[a]| = W^d`). -/
private theorem farEntry_loop_le_of_GM (H : Matrix (Idx d L W) (Idx d L W) ℂ) (hH : H.IsHermitian) (z : ℂ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) {m : ℝ} (hm : ∀ x y, ‖Gres H z true x y - M x y‖ ≤ m)
    (hM : ∀ y, ∑ x, ‖M y x‖ ^ 2 ≤ 1) (σ : Fin 2 → Bool) (hσ : σ 0 ≠ σ 1) (a b : Zd d L) :
    ‖loopFine d L W H z σ ![a, b]‖ ≤ 2 * m ^ 2 + 2 * ((W : ℝ) ^ d)⁻¹ := by
  have hm0 : 0 ≤ m := (norm_nonneg _).trans (hm 0 0)
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)) d
  -- the general block sum
  have key : ∀ a₁ b₁ : Zd d L, ((((W : ℝ) ^ d)⁻¹ ^ 2 * ∑ y : Idx d L W, ∑ x : Idx d L W,
        (if (split d L W y).1 = b₁ ∧ (split d L W x).1 = a₁ then ‖Gres H z true y x‖ ^ 2 else 0) : ℝ)) ≤
      2 * m ^ 2 + 2 * ((W : ℝ) ^ d)⁻¹ := by
    intro a₁ b₁
    have hcard : ∀ c : Zd d L, ((Finset.univ.filter fun x : Idx d L W => (split d L W x).1 = c).card : ℝ) =
        (W : ℝ) ^ d := fun c => by
      have := card_Iblk d L W c
      simp only [Iblk] at this
      rw [this]; push_cast; rfl
    have hinner : ∀ y : Idx d L W, (∑ x : Idx d L W,
        (if (split d L W y).1 = b₁ ∧ (split d L W x).1 = a₁ then ‖Gres H z true y x‖ ^ 2 else 0)) ≤
        (if (split d L W y).1 = b₁ then 2 * m ^ 2 * (W : ℝ) ^ d + 2 else 0) := by
      intro y
      by_cases hy : (split d L W y).1 = b₁
      · simp only [hy, true_and, ite_true]
        calc (∑ x : Idx d L W, if (split d L W x).1 = a₁ then ‖Gres H z true y x‖ ^ 2 else 0)
            ≤ ∑ x : Idx d L W, ((if (split d L W x).1 = a₁ then 2 * m ^ 2 else 0) + 2 * ‖M y x‖ ^ 2) := by
              refine Finset.sum_le_sum fun x _ => ?_
              have h1 : ‖Gres H z true y x‖ ≤ ‖Gres H z true y x - M y x‖ + ‖M y x‖ := by
                have := norm_add_le (Gres H z true y x - M y x) (M y x)
                rwa [sub_add_cancel] at this
              have h2 : ‖Gres H z true y x‖ ^ 2 ≤ 2 * m ^ 2 + 2 * ‖M y x‖ ^ 2 := by
                have h3 := hm y x
                nlinarith [norm_nonneg (Gres H z true y x), norm_nonneg (M y x),
                  norm_nonneg (Gres H z true y x - M y x), sq_nonneg (‖Gres H z true y x - M y x‖ - ‖M y x‖)]
              split_ifs with hx
              · linarith
              · have := sq_nonneg ‖M y x‖
                linarith [mul_nonneg hm0 hm0]
          _ = (∑ x : Idx d L W, if (split d L W x).1 = a₁ then 2 * m ^ 2 else 0) + 2 * ∑ x, ‖M y x‖ ^ 2 := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
          _ ≤ 2 * m ^ 2 * (W : ℝ) ^ d + 2 := by
              rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcard]
              have := hM y
              nlinarith
      · simp only [hy, false_and, ite_false, Finset.sum_const_zero]
        exact le_rfl
    calc ((((W : ℝ) ^ d)⁻¹ ^ 2 * ∑ y : Idx d L W, ∑ x : Idx d L W,
          (if (split d L W y).1 = b₁ ∧ (split d L W x).1 = a₁ then ‖Gres H z true y x‖ ^ 2 else 0) : ℝ))
        ≤ ((W : ℝ) ^ d)⁻¹ ^ 2 * ∑ y : Idx d L W, (if (split d L W y).1 = b₁ then 2 * m ^ 2 * (W : ℝ) ^ d + 2 else 0) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => hinner y) (by positivity)
      _ = ((W : ℝ) ^ d)⁻¹ ^ 2 * ((W : ℝ) ^ d * (2 * m ^ 2 * (W : ℝ) ^ d + 2)) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcard]
      _ = 2 * m ^ 2 + 2 * ((W : ℝ) ^ d)⁻¹ := by field_simp
  have hnn : ∀ a₁ b₁ : Zd d L, 0 ≤ ((((W : ℝ) ^ d)⁻¹ ^ 2 * ∑ y : Idx d L W, ∑ x : Idx d L W,
        (if (split d L W y).1 = b₁ ∧ (split d L W x).1 = a₁ then ‖Gres H z true y x‖ ^ 2 else 0) : ℝ)) :=
    fun a₁ b₁ => mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun x _ => by
      split_ifs <;> positivity)
  rcases farEntry_mixed_cases σ hσ with rfl | rfl
  · rw [farEntry_loopFine_pm H hH z a b, Complex.norm_real, Real.norm_of_nonneg (hnn a b)]
    exact key a b
  · rw [farEntry_loopFine_mp, farEntry_loopFine_pm H hH z b a, Complex.norm_real,
      Real.norm_of_nonneg (hnn b a)]
    exact key b a

end LoopId

section Generic

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **`STFarEntryAtLog` over the carrier** (charge `+`; the charge `-` is the transpose, `G(-) = G(+)ᴴ` for a Hermitian matrix):
for every `c, D' > 0`, `‖(G_τ)_{xy}‖ 1[c (log W)³ ℓ_τ ≤ |[x] - [y]|_∞] ≺ W^{-D'}` under the law `μ`. -/
def STFarEntryAtLoggL (τ : ℕ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ D' : ℝ, 0 < D' →
    PrecL sz μ (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖C.G n (τ n) ω p.1 p.2‖ *
        (if c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (τ n) ≤
            ((zdistInf d (sz.L n) (STblk sz n p.1 - STblk sz n p.2) : ℕ) : ℝ) then 1 else 0))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D'))

/-- The loop scale `Φ_n(a,b)` fed to `STGijDecgL`: `W^{-ε₀}` for the pairs closer than `ρ`, `W^{-D₁}` beyond. -/
private def farEntry_Phi (sz : Sizes d) (n : ℕ) (ρ ε₀ D₁ : ℝ) (a b : Zd d (sz.L n)) : ℝ :=
  if (zdistInf d (sz.L n) (a - b) : ℝ) < ρ then ((sz.W n : ℕ) : ℝ) ^ (-ε₀) else ((sz.W n : ℕ) : ℝ) ^ (-D₁)

/-- One term of the sum in `farEntry_rhs_le`: `Φ_n(a',b') e^{-c_g(|a'-a|+|b'-b|)} ≤ e^{-κ₀ G³} + W^{-D₁}` for a far pair `(a,b)`. -/
private theorem farEntry_term_le (sz : Sizes d) (n : ℕ) {c cg ε₀ D₁ τ' : ℝ} (hc : 0 < c) (hcg : 0 < cg)
    (hε₀ : 0 ≤ ε₀) (hW2 : (2 : ℝ) ≤ ((sz.W n : ℕ) : ℝ)) (hG1 : 1 ≤ Real.log ((sz.W n : ℕ) : ℝ))
    {a b : Zd d (sz.L n)}
    (hab : c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) τ' ≤
      (zdistInf d (sz.L n) (a - b) : ℝ)) (a' b' : Zd d (sz.L n)) :
    farEntry_Phi sz n ((c / 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 - 2) * ellT (sz.L n) (sz.lam n) τ') ε₀ D₁ a' b' *
        Real.exp (-cg * ((zdistInf d (sz.L n) (a' - a) : ℝ) + (zdistInf d (sz.L n) (b' - b) : ℝ))) ≤
      Real.exp (-(cg * (c / 2) * Real.log ((sz.W n : ℕ) : ℝ) ^ 3)) + ((sz.W n : ℕ) : ℝ) ^ (-D₁) := by
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hℓ1 : 1 ≤ ellT (sz.L n) (sz.lam n) τ' := one_le_ellT hL1
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  set G : ℝ := Real.log W with hGdef
  set ℓ : ℝ := ellT (sz.L n) (sz.lam n) τ' with hℓdef
  set κ₀ : ℝ := cg * (c / 2) with hκ₀
  have hcG : 0 ≤ c / 2 * G ^ 3 := by positivity
  have hex0 : Real.exp (-cg * ((zdistInf d (sz.L n) (a' - a) : ℝ) + (zdistInf d (sz.L n) (b' - b) : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (zdistInf d (sz.L n) (a' - a) : ℝ) + (zdistInf d (sz.L n) (b' - b) : ℝ) := by positivity
    nlinarith only [this, hcg]
  unfold farEntry_Phi
  split_ifs with hlt
  · -- near
    have hW1 : W ^ (-ε₀) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (le_trans (by norm_num) hW2) (neg_nonpos.2 hε₀)
    have htri : (zdistInf d (sz.L n) (a - b) : ℝ) ≤
        (zdistInf d (sz.L n) (a' - a) : ℝ) + (zdistInf d (sz.L n) (a' - b') : ℝ) +
          (zdistInf d (sz.L n) (b' - b) : ℝ) := by
      have e : a - b = ((a - a') + (a' - b')) + (b' - b) := by abel
      have h1 := RBM.Gauss.Sizes.farEntry_zdistInf_add_le ((a - a') + (a' - b')) (b' - b)
      have h2 := RBM.Gauss.Sizes.farEntry_zdistInf_add_le (a - a') (a' - b')
      have h3 := RBM.Gauss.Sizes.farEntry_zdistInf_comm a a'
      rw [e]
      exact_mod_cast (by omega : zdistInf d (sz.L n) (((a - a') + (a' - b')) + (b' - b)) ≤
        zdistInf d (sz.L n) (a' - a) + zdistInf d (sz.L n) (a' - b') + zdistInf d (sz.L n) (b' - b))
    have hsum : c / 2 * G ^ 3 ≤ (zdistInf d (sz.L n) (a' - a) : ℝ) + (zdistInf d (sz.L n) (b' - b) : ℝ) := by
      have h1 : c * G ^ 3 * ℓ - (c / 2 * G ^ 3 - 2) * ℓ ≤
          (zdistInf d (sz.L n) (a' - a) : ℝ) + (zdistInf d (sz.L n) (b' - b) : ℝ) := by
        linarith only [hab, hlt, htri]
      have h2 : c / 2 * G ^ 3 ≤ c * G ^ 3 * ℓ - (c / 2 * G ^ 3 - 2) * ℓ := by
        have : c * G ^ 3 * ℓ - (c / 2 * G ^ 3 - 2) * ℓ = (c / 2 * G ^ 3 + 2) * ℓ := by ring
        rw [this]
        nlinarith only [hℓ1, hcG]
      linarith only [h1, h2]
    have hex : Real.exp (-cg * ((zdistInf d (sz.L n) (a' - a) : ℝ) + (zdistInf d (sz.L n) (b' - b) : ℝ))) ≤
        Real.exp (-(κ₀ * G ^ 3)) := by
      refine Real.exp_le_exp.2 ?_
      have := mul_le_mul_of_nonneg_left hsum hcg.le
      rw [hκ₀]
      nlinarith only [this]
    have hP0 : 0 ≤ W ^ (-D₁) := Real.rpow_nonneg hWpos.le _
    calc W ^ (-ε₀) * Real.exp (-cg * ((zdistInf d (sz.L n) (a' - a) : ℝ) + (zdistInf d (sz.L n) (b' - b) : ℝ)))
        ≤ 1 * Real.exp (-(κ₀ * G ^ 3)) := mul_le_mul hW1 hex (Real.exp_pos _).le (by norm_num)
      _ ≤ _ := by linarith only [hP0]
  · have hex1 := Real.exp_pos (-(κ₀ * G ^ 3))
    calc W ^ (-D₁) * Real.exp (-cg * ((zdistInf d (sz.L n) (a' - a) : ℝ) +
          (zdistInf d (sz.L n) (b' - b) : ℝ))) ≤ W ^ (-D₁) * 1 :=
          mul_le_mul_of_nonneg_left hex0 (Real.rpow_nonneg hWpos.le _)
      _ ≤ _ := by linarith only [hex1]

/-- **The right side of `STGijDecgL` at a far pair of blocks is at most `3 W^{-D'}`**: with `Φ = farEntry_Phi` at the
radius `ρ = (c/2 · (log W)³ - 2) ℓ`, `Ψ = W^{-ε₀}`, `D = D'`, `D₁ = D' + 2/𝔠 + 1 + ε₀`.  Eventual arithmetic only:
`2/𝔠 + D' + 1 ≤ c_g (c/2) (log W)²`, `W ≥ 2`, `N^𝔠 ≤ W`. -/
private theorem farEntry_rhs_le (sz : Sizes d) (n : ℕ) {c cg D' ε₀ 𝔠 τ' : ℝ} (hc : 0 < c) (hcg : 0 < cg)
    (hε₀ : 0 ≤ ε₀) (h𝔠 : 0 < 𝔠) (hbw : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ))
    (hW2 : (2 : ℝ) ≤ ((sz.W n : ℕ) : ℝ)) (hG1 : 1 ≤ Real.log ((sz.W n : ℕ) : ℝ))
    (hG : 2 / 𝔠 + D' + 1 ≤ cg * (c / 2) * Real.log ((sz.W n : ℕ) : ℝ) ^ 2)
    {a b : Zd d (sz.L n)}
    (hab : c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) τ' ≤
      (zdistInf d (sz.L n) (a - b) : ℝ)) :
    (∑ a' : Zd d (sz.L n), ∑ b' : Zd d (sz.L n),
        farEntry_Phi sz n ((c / 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 - 2) * ellT (sz.L n) (sz.lam n) τ') ε₀
            (D' + 2 / 𝔠 + 1 + ε₀) a' b' *
          Real.exp (-cg * ((zdistInf d (sz.L n) (a' - a) : ℝ) + (zdistInf d (sz.L n) (b' - b) : ℝ)))) +
      ((sz.W n : ℕ) : ℝ) ^ (-ε₀) * Real.exp (-cg * (zdistInf d (sz.L n) (a - b) : ℝ)) +
      ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ 3 * ((sz.W n : ℕ) : ℝ) ^ (-D') := by
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set G : ℝ := Real.log W with hGdef
  set ℓ : ℝ := ellT (sz.L n) (sz.lam n) τ' with hℓdef
  set κ₀ : ℝ := cg * (c / 2) with hκ₀
  have hκ0 : 0 < κ₀ := by positivity
  have hℓ1 : 1 ≤ ℓ := one_le_ellT hL1
  have hG0 : 0 ≤ G := by linarith
  have hcG : 0 ≤ c / 2 * G ^ 3 := by positivity
  -- the two exponentials
  have hexp1 : Real.exp (-(κ₀ * G ^ 3)) * W ^ (2 / 𝔠) ≤ W ^ (-(D' + 1)) := by
    rw [Real.rpow_def_of_pos hWpos, Real.rpow_def_of_pos hWpos, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : G * (2 / 𝔠) + G * (D' + 1) ≤ κ₀ * G ^ 3 := by
      have h := mul_le_mul_of_nonneg_left hG hG0
      nlinarith
    nlinarith
  have hW1D : W ^ (-(D' + 1)) ≤ W ^ (-D') / 2 := by
    have e : W ^ (-(D' + 1)) = W ^ (-D') * W⁻¹ := by
      rw [show -(D' + 1) = -D' + (-1) by ring, Real.rpow_add hWpos, Real.rpow_neg_one]
    rw [e]
    have h1 : W⁻¹ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) hW2
    have h2 : 0 ≤ W ^ (-D') := Real.rpow_nonneg hWpos.le _
    nlinarith
  -- the number of pairs
  have hN2 : N ^ (2 : ℕ) ≤ W ^ (2 / 𝔠) := by
    have h2 := Sizes.size_rpow_le_W_rpow sz h𝔠 n hbw (τ := 2) (by norm_num)
    have e : N ^ (2 : ℝ) = N ^ (2 : ℕ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [← e]
    exact h2
  have hcard : (Fintype.card (Zd d (sz.L n)) : ℝ) ≤ N := by
    rw [card_Zd]
    have h1 : (sz.L n) ^ d ≤ sz.size n := by
      change (sz.L n) ^ d ≤ (sz.W n * sz.L n) ^ d
      exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
    rw [hNdef]
    exact_mod_cast h1
  -- each term
  have hterm := farEntry_term_le sz n hc hcg hε₀ (D₁ := D' + 2 / 𝔠 + 1 + ε₀) hW2 hG1 hab
  -- T1
  have hT1 : (∑ a' : Zd d (sz.L n), ∑ b' : Zd d (sz.L n),
        farEntry_Phi sz n ((c / 2 * G ^ 3 - 2) * ℓ) ε₀ (D' + 2 / 𝔠 + 1 + ε₀) a' b' *
          Real.exp (-cg * ((zdistInf d (sz.L n) (a' - a) : ℝ) + (zdistInf d (sz.L n) (b' - b) : ℝ)))) ≤
      W ^ (-D') := by
    have hB0 : 0 ≤ Real.exp (-(κ₀ * G ^ 3)) + W ^ (-(D' + 2 / 𝔠 + 1 + ε₀)) :=
      add_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hWpos.le _)
    calc _ ≤ ∑ _a' : Zd d (sz.L n), ∑ _b' : Zd d (sz.L n),
          (Real.exp (-(κ₀ * G ^ 3)) + W ^ (-(D' + 2 / 𝔠 + 1 + ε₀))) :=
          Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun b' _ => hterm a' b'
      _ = (Fintype.card (Zd d (sz.L n)) : ℝ) ^ 2 *
            (Real.exp (-(κ₀ * G ^ 3)) + W ^ (-(D' + 2 / 𝔠 + 1 + ε₀))) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
      _ ≤ N ^ 2 * (Real.exp (-(κ₀ * G ^ 3)) + W ^ (-(D' + 2 / 𝔠 + 1 + ε₀))) := by
          gcongr
      _ ≤ W ^ (2 / 𝔠) * (Real.exp (-(κ₀ * G ^ 3)) + W ^ (-(D' + 2 / 𝔠 + 1 + ε₀))) :=
          mul_le_mul_of_nonneg_right hN2 hB0
      _ = Real.exp (-(κ₀ * G ^ 3)) * W ^ (2 / 𝔠) + W ^ (2 / 𝔠) * W ^ (-(D' + 2 / 𝔠 + 1 + ε₀)) := by ring
      _ ≤ W ^ (-(D' + 1)) + W ^ (-(D' + 1)) := by
          refine add_le_add hexp1 ?_
          rw [← Real.rpow_add hWpos]
          refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
          linarith
      _ ≤ W ^ (-D') := by linarith
  -- T2
  have hT2 : W ^ (-ε₀) * Real.exp (-cg * (zdistInf d (sz.L n) (a - b) : ℝ)) ≤ W ^ (-D') := by
    have hW1 : W ^ (-ε₀) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (le_trans (by norm_num) hW2) (neg_nonpos.2 hε₀)
    have hcG3 : 0 ≤ c * G ^ 3 := by positivity
    have h1 : κ₀ * G ^ 3 ≤ cg * (zdistInf d (sz.L n) (a - b) : ℝ) := by
      have h0 : c / 2 * G ^ 3 ≤ (zdistInf d (sz.L n) (a - b) : ℝ) := by
        have : c * G ^ 3 ≤ c * G ^ 3 * ℓ := le_mul_of_one_le_right hcG3 hℓ1
        linarith only [this, hab, hcG3]
      calc κ₀ * G ^ 3 = cg * (c / 2 * G ^ 3) := by rw [hκ₀]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h0 hcg.le
    have h2 : Real.exp (-cg * (zdistInf d (sz.L n) (a - b) : ℝ)) ≤ Real.exp (-(κ₀ * G ^ 3)) :=
      Real.exp_le_exp.2 (by linarith only [h1])
    have h3 : Real.exp (-(κ₀ * G ^ 3)) ≤ W ^ (-D') := by
      have h4 : Real.exp (-(κ₀ * G ^ 3)) * W ^ (2 / 𝔠) ≤ W ^ (-(D' + 1)) := hexp1
      have h5 : 1 ≤ W ^ (2 / 𝔠) := Real.one_le_rpow (le_trans (by norm_num) hW2) (by positivity)
      have h6 := (Real.exp_pos (-(κ₀ * G ^ 3))).le
      have h7 : Real.exp (-(κ₀ * G ^ 3)) ≤ Real.exp (-(κ₀ * G ^ 3)) * W ^ (2 / 𝔠) := le_mul_of_one_le_right h6 h5
      have h8 : 0 ≤ W ^ (-D') := Real.rpow_nonneg hWpos.le _
      linarith only [h4, h7, hW1D, h8]
    calc W ^ (-ε₀) * Real.exp (-cg * (zdistInf d (sz.L n) (a - b) : ℝ)) ≤ 1 * Real.exp (-(κ₀ * G ^ 3)) :=
          mul_le_mul hW1 h2 (Real.exp_pos _).le (by norm_num)
      _ ≤ W ^ (-D') := by linarith only [h3]
  linarith

/-- The radius of `farEntry_Phi`: `ρ_n = (c₃ (log W)³ - 2) ℓ_τ`. -/
private def farEntry_rho (sz : Sizes d) (c₃ : ℝ) (τ : ℕ → ℝ) (n : ℕ) : ℝ :=
  (c₃ * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 - 2) * ellT (sz.L n) (sz.lam n) (τ n)

private theorem farEntry_indg_cases (n : ℕ) (τ A : ℝ) (ω : sz.SeqΩ) :
    (STindMaxg C n τ A ω = 1 ∧ ∀ x y, ‖C.GM n τ ω x y‖ ≤ A) ∨ STindMaxg C n τ A ω = 0 := by
  unfold STindMaxg
  split_ifs with h
  · exact Or.inl ⟨rfl, h⟩
  · exact Or.inr rfl

private theorem farEntry_indg_of_le (n : ℕ) (τ A : ℝ) (ω : sz.SeqΩ) (h : ∀ x y, ‖C.GM n τ ω x y‖ ≤ A) :
    STindMaxg C n τ A ω = 1 := by
  unfold STindMaxg; simp [h]

/-- **The loop premise of `STGijDecgL` holds for `Φ = farEntry_Phi`**: `1_Ω ‖𝓛^{(2)}_{(±,∓),(a,b)}‖ ≺ Φ_n(a,b)²`.  Near pairs
(`|a-b| < ρ_n`) deterministically (`‖𝓛‖ ≤ 2 W^{-2ε₀} + 2 W^{-d}`, `farEntry_loop_le_of_GM`); far pairs by `STGdecayWgL`
(`D = 2 D₁`), the far field `STKfargL` and the scalar tail `farEntry_loop_le`. -/
private theorem farEntry_loopPrem {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    {g' E : ℕ → ℝ} {s t τ : ℕ → ℝ} {𝔠 δ Cd ε₀ D₁ c₃ : ℝ} (hRep : CltRepg C μ H₀ g' E)
    (hWard : ∀ n x, ∑ y, ‖C.M n x y‖ ^ 2 ≤ 1) (h𝔠 : 0 < 𝔠) (hc₃ : 0 < c₃) (hε₀ : 0 < ε₀)
    (hε₀d : 2 * ε₀ ≤ d) (hD₁ : 0 < D₁) (hδ : 0 < δ) (hs : ∀ n, 0 ≤ s n) (hsτ : ∀ n, s n ≤ τ n)
    (hτt : ∀ n, τ n ≤ t n) (ht1 : ∀ n, t n < 1)
    (hrange : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - t n)
    (hBW : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ))
    (hsize : Tendsto sz.size atTop atTop)
    (hWtend : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop)
    (hDec : STGdecayWgL C μ s t Cd) (hK : STKfargL C τ) :
    PrecL sz μ (U := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n q ω => STindMaxg C n (τ n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω * ‖C.L n (τ n) q.1.1 ![q.2.1, q.2.2] ω‖)
      (fun n q _ => (farEntry_Phi sz n (farEntry_rho sz c₃ τ n) ε₀ D₁ q.2.1 q.2.2) ^ 2) := by
  have hDecS := StochDomAt.precomp_param (hDec (2 * D₁) (by linarith))
    (fun n (q : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × Zd d (sz.L n) × Zd d (sz.L n)) =>
      ((⟨τ n, hsτ n, hτt n⟩ : TimeIcc s t n), q.1.1, ![q.2.1, q.2.2]))
  refine StochDomAt.of_subset hDecS fun τ' hτ' => ⟨τ' / 2, half_pos hτ', ?_⟩
  have hGev : ∀ᶠ n : ℕ in atTop, farEntry_X0 c₃ ((max Cd 0 + 2) / 𝔠 + 2 * D₁) ≤ Real.log ((sz.W n : ℕ) : ℝ) :=
    (Real.tendsto_log_atTop.comp hWtend).eventually_ge_atTop _
  have hNev : ∀ᶠ n : ℕ in atTop, 3 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) :=
    hsize.eventually (eventually_le_rpow 3 (half_pos hτ'))
  filter_upwards [hGev, hNev, hrange, hBW, hK (2 * D₁) (by linarith), hWtend.eventually_ge_atTop 2]
    with n hGn hN3 hrn hbw hKn hW2
  rintro ω ⟨⟨⟨σ, hσ⟩, a, b⟩, hq⟩
  refine ⟨⟨⟨σ, hσ⟩, a, b⟩, ?_⟩
  by_contra hno
  push Not at hno
  simp only at hq hno
  -- scales
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by linarith
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hqq : ((sz.size n : ℕ) : ℝ) ^ τ' = ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hNτ0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) := Real.rpow_nonneg hN0.le _
  by_cases hnear : (zdistInf d (sz.L n) (a - b) : ℝ) < farEntry_rho sz c₃ τ n
  · -- near pair
    have hΦ : farEntry_Phi sz n (farEntry_rho sz c₃ τ n) ε₀ D₁ a b = ((sz.W n : ℕ) : ℝ) ^ (-ε₀) := by
      simp only [farEntry_Phi, hnear, ↓reduceIte]
    rw [hΦ] at hq
    have hΦ2 : (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ^ 2 = ((sz.W n : ℕ) : ℝ) ^ (-(2 * ε₀)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hWpos.le]; congr 1; push_cast; ring
    have hbound : STindMaxg C n (τ n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω *
        ‖C.L n (τ n) σ ![a, b] ω‖ ≤ 4 * ((sz.W n : ℕ) : ℝ) ^ (-(2 * ε₀)) := by
      have hP : 0 < ((sz.W n : ℕ) : ℝ) ^ (-(2 * ε₀)) := Real.rpow_pos_of_pos hWpos _
      rcases farEntry_indg_cases C n (τ n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω with ⟨h1, h2⟩ | h0
      · rw [h1, one_mul]
        obtain ⟨hG, hL⟩ := (hRep.2.2 n (τ n) ω)
        have hHerm : (H₀ n + Matrix.of fun i j : Idx d (sz.L n) (sz.W n) =>
            Sizes.seqHflow (sz.withLam g') n (τ n) ω i j).IsHermitian :=
          (hRep.2.1 n).add (Sizes.seqHflow_isHermitian (sz.withLam g') n (τ n) ω)
        have hm := farEntry_loop_le_of_GM (H₀ n + Matrix.of fun i j : Idx d (sz.L n) (sz.W n) =>
            Sizes.seqHflow (sz.withLam g') n (τ n) ω i j) hHerm (ztOf (C.m n) (E n) (τ n))
          (Matrix.of fun x y => C.M n x y) (m := ((sz.W n : ℕ) : ℝ) ^ (-ε₀))
          (fun x y => by
            have := h2 x y
            simp only [FlowFM.GM, hG x y] at this
            exact this)
          (fun y => hWard n y) σ hσ a b
        rw [hL 2 σ ![a, b]] at hq ⊢
        have hW0 : ((sz.W n : ℕ) : ℝ) ^ (-ε₀) ≥ 0 := Real.rpow_nonneg hWpos.le _
        have hWd : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ (-(2 * ε₀)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_neg hWpos.le]
          exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
        have : 2 * (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ^ 2 + 2 * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤
            4 * ((sz.W n : ℕ) : ℝ) ^ (-(2 * ε₀)) := by rw [hΦ2]; linarith
        exact le_trans hm this
      · rw [h0, zero_mul]; positivity
    have h4 : 4 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' := by
      rw [hqq]; nlinarith
    have hP : 0 < ((sz.W n : ℕ) : ℝ) ^ (-(2 * ε₀)) := Real.rpow_pos_of_pos hWpos _
    rw [hΦ2] at hq
    nlinarith
  · -- far pair
    have hΦ : farEntry_Phi sz n (farEntry_rho sz c₃ τ n) ε₀ D₁ a b = ((sz.W n : ℕ) : ℝ) ^ (-D₁) := by
      simp only [farEntry_Phi, hnear, ↓reduceIte]
    rw [hΦ] at hq
    have hΦ2 : (((sz.W n : ℕ) : ℝ) ^ (-D₁)) ^ 2 = ((sz.W n : ℕ) : ℝ) ^ (-(2 * D₁)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hWpos.le]; congr 1; push_cast; ring
    rw [hΦ2] at hq
    push Not at hnear
    -- geometry and the `𝒦` bound
    obtain ⟨hG1, hG2⟩ := farEntry_X0_le hc₃ hGn
    have hK₁0 : 0 ≤ (max Cd 0 + 2) / 𝔠 + 2 * D₁ := by
      have : 0 ≤ (max Cd 0 + 2) / 𝔠 := div_nonneg (by have := le_max_right Cd 0; linarith) h𝔠.le
      linarith
    have hG4 : 4 ≤ c₃ * Real.log ((sz.W n : ℕ) : ℝ) := by
      nlinarith [sq_nonneg ((max Cd 0 + 2) / 𝔠 + 2 * D₁)]
    have hlogA := farEntry_log_arith hG1 hG4
    have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
      exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
    have hℓpos : 0 < ellT (sz.L n) (sz.lam n) (τ n) := by linarith [one_le_ellT (L := sz.L n) (g := sz.lam n) (t := τ n) hL1]
    have hKcond : Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (sz.lam n) (τ n) ≤
        (zdistInf d (sz.L n) (a - b) : ℝ) := by
      refine le_trans ?_ hnear
      unfold farEntry_rho
      exact mul_le_mul_of_nonneg_right (by linarith) hℓpos.le
    have hKb : ‖C.K n (τ n) σ ![a, b]‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-(2 * D₁)) := by
      have hK' : ∀ s₀ : Bool, ‖C.K n (τ n) ![s₀, !s₀] ![a, b]‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-(2 * D₁)) := by
        intro s₀
        refine (hKn a b s₀ hKcond).trans ?_
        have h1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hW1)
        have h2 : ((sz.W n : ℕ) : ℝ) ^ (-(2 * D₁ + (d : ℝ))) ≤ ((sz.W n : ℕ) : ℝ) ^ (-(2 * D₁)) :=
          Real.rpow_le_rpow_of_exponent_le hW1 (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
        calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-(2 * D₁ + (d : ℝ)))
            ≤ 1 * ((sz.W n : ℕ) : ℝ) ^ (-(2 * D₁)) :=
              mul_le_mul h1 h2 (Real.rpow_nonneg hWpos.le _) zero_le_one
          _ = _ := one_mul _
      rcases farEntry_mixed_cases σ hσ with rfl | rfl
      · exact hK' true
      · exact hK' false
    have hdec := hno
    have hL := farEntry_loop_le sz n (s := s n) (τ := τ n) (𝔠 := 𝔠) (c := c₃) (D' := D₁) (Cd := Cd)
      (τ₃ := τ' / 2) (C.L n (τ n) σ ![a, b] ω) (C.K n (τ n) σ ![a, b]) h𝔠 hc₃ hD₁ (half_pos hτ').le (hs n)
      (hsτ n) ((hτt n).trans_lt (ht1 n))
      (by
        have h := Real.rpow_le_rpow_of_exponent_le hN1 (show (-1 : ℝ) ≤ -1 + δ by linarith)
        rw [Real.rpow_neg_one] at h
        linarith [hrn, hτt n])
      hbw hGn (r := zdistInf d (sz.L n) (a - b)) hnear hKb
      (by simpa using hdec)
    have hind : STindMaxg C n (τ n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω ≤ 1 := by
      rcases farEntry_indg_cases C n (τ n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω with ⟨h1, -⟩ | h0
      · rw [h1]
      · rw [h0]; norm_num
    have hind0 : 0 ≤ STindMaxg C n (τ n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω := by
      rcases farEntry_indg_cases C n (τ n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω with ⟨h1, -⟩ | h0
      · rw [h1]; norm_num
      · rw [h0]
    have hP : 0 < ((sz.W n : ℕ) : ℝ) ^ (-(2 * D₁)) := Real.rpow_pos_of_pos hWpos _
    have : STindMaxg C n (τ n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω * ‖C.L n (τ n) σ ![a, b] ω‖ ≤
        ‖C.L n (τ n) σ ![a, b] ω‖ := by
      calc _ ≤ 1 * ‖C.L n (τ n) σ ![a, b] ω‖ := mul_le_mul_of_nonneg_right hind (norm_nonneg _)
        _ = _ := one_mul _
    have h3 : 3 * ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) * ((sz.W n : ℕ) : ℝ) ^ (-(2 * D₁)) ≤
        ((sz.size n : ℕ) : ℝ) ^ τ' * ((sz.W n : ℕ) : ℝ) ^ (-(2 * D₁)) := by
      rw [hqq]
      exact mul_le_mul_of_nonneg_right (by nlinarith) hP.le
    linarith

/-- **The log-scale far-entry decay of the resolvent over the carrier** (X1-C4 target 4; the generic form of `stFarEntryAtLog`).  From
`STLocalEntryUgL`, `STGdecayWgL` on `[s,t]` (Step 2), the Green input `STGijDecgL` and the far field `STKfargL` of `𝒦^{(2)}` at `τ`,
the Ward row bound and the far smallness `STMfarg` of `M`, `CltRepg`, and the flow facts: admissible sizes, `0 ≤ s ≤ τ ≤ t < 1`,
`N^{-1+δ} ≤ 1 - t`.  No `|E| ≤ 2 - κ`, no `|m| = 1`, no `Θ`. -/
theorem stFarEntryAtLoggL {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    {g' E : ℕ → ℝ} {s t τ : ℕ → ℝ} {𝔠 𝔡 δ Cd : ℝ} (hd : 3 ≤ d) (hadm : sz.Admissible 𝔠 𝔡) (hδ : 0 < δ)
    (hRep : CltRepg C μ H₀ g' E) (hWard : ∀ n x, ∑ y, ‖C.M n x y‖ ^ 2 ≤ 1)
    (hs : ∀ n, 0 ≤ s n) (hsτ : ∀ n, s n ≤ τ n) (hτt : ∀ n, τ n ≤ t n) (ht1 : ∀ n, t n < 1)
    (hrange : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - t n)
    (hLoc : STLocalEntryUgL C μ s t) (hDec : STGdecayWgL C μ s t Cd) (hGij : STGijDecgL C μ τ)
    (hK : STKfargL C τ) (hMf : STMfarg C τ) :
    STFarEntryAtLoggL C μ τ := by
  intro c hc D' hD'
  obtain ⟨h𝔠, h𝔡, hN, hBW, hWO⟩ := id hadm
  have hsize : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hN
  have hWtend : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
      (tendsto_rpow_atTop h𝔠).comp hN
    exact tendsto_atTop_mono' _ hBW h1
  set c₀ : ℝ := min (2 * 𝔡) δ with hc₀def
  have hc₀ : 0 < c₀ := lt_min (by linarith) hδ
  set ε₀ : ℝ := min (c₀ / 4) ((d : ℝ) / 2) with hε₀def
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hε₀ : 0 < ε₀ := lt_min (by positivity) (by positivity)
  have hε₀d : 2 * ε₀ ≤ d := by have := min_le_right (c₀ / 4) ((d : ℝ) / 2); linarith
  have hε₀c : ε₀ ≤ c₀ / 4 := min_le_left _ _
  set D₁ : ℝ := D' + 2 / 𝔠 + 1 + ε₀ with hD₁def
  have hD₁ : 0 < D₁ := by positivity
  have h2𝔠 : 0 ≤ 2 / 𝔠 := by positivity
  obtain ⟨cg, hcg, Hg⟩ := hGij
  have hprem := farEntry_loopPrem C μ hRep hWard h𝔠 (half_pos hc) hε₀ hε₀d hD₁ hδ hs hsτ hτt ht1 hrange hBW
    hsize hWtend hDec hK
  have hB := Hg ε₀ hε₀ D' hD'
    (fun n a b => farEntry_Phi sz n (farEntry_rho sz (c / 2) τ n) ε₀ D₁ a b)
    (fun n => ((sz.W n : ℕ) : ℝ) ^ (-ε₀))
    (by
      filter_upwards [hWtend.eventually_ge_atTop 1] with n hW1 a b
      have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
      unfold farEntry_Phi
      split_ifs
      · exact ⟨Real.rpow_pos_of_pos hWpos _, le_rfl⟩
      · exact ⟨Real.rpow_pos_of_pos hWpos _,
          Real.rpow_le_rpow_of_exponent_le hW1 (by linarith [hD₁def, hD'])⟩)
    (by
      filter_upwards [hWtend.eventually_ge_atTop 1] with n hW1
      exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith))
    (Eventually.of_forall fun n => le_rfl) hprem
  have hLocS := StochDomAt.precomp_param hLoc
    (fun n (p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) =>
      ((⟨τ n, hsτ n, hτt n⟩ : TimeIcc s t n), p.1, p.2))
  refine farEntry_union3 hsize hLocS hB hB ?_
  intro τ₀ hτ₀
  refine ⟨𝔠 * (c₀ / 4), by positivity, τ₀ / 2, by positivity, τ₀ / 2, by positivity, ?_⟩
  have hGev : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log ((sz.W n : ℕ) : ℝ) ∧
      2 / 𝔠 + D' + 1 ≤ cg * (c / 2) * Real.log ((sz.W n : ℕ) : ℝ) ^ 2 := by
    have hlog := Real.tendsto_log_atTop.comp hWtend
    have hq : Tendsto (fun n => cg * (c / 2) * Real.log ((sz.W n : ℕ) : ℝ) ^ 2) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity : 0 < cg * (c / 2))
        ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hlog)
    filter_upwards [hlog.eventually_ge_atTop 1, hq.eventually_ge_atTop (2 / 𝔠 + D' + 1)] with n h1 h2
    exact ⟨h1, h2⟩
  have hW2ev : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (c₀ / 4) :=
    ((tendsto_rpow_atTop (by positivity : 0 < c₀ / 4)).comp hWtend).eventually_ge_atTop 2
  have hNev : ∀ᶠ n : ℕ in atTop, 4 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ₀ / 2) :=
    hsize.eventually (eventually_le_rpow 4 (half_pos hτ₀))
  filter_upwards [hGev, hW2ev, hNev, hrange, hBW, hWO, hWtend.eventually_ge_atTop 2,
    hMf c D' hc hD'] with n hGn hW2n hN4 hrn hbw hwo hW2 hMn
  intro ω hω
  by_contra hnot
  simp only [Set.mem_union, not_or, badSetAt, Set.mem_ofPred_eq, not_exists, not_lt] at hnot hω
  obtain ⟨⟨hn1, hn2⟩, -⟩ := hnot
  obtain ⟨⟨x, y⟩, hp⟩ := hω
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by linarith
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hτ1 : τ n < 1 := (hτt n).trans_lt (ht1 n)
  have hrcτ : ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - τ n := hrn.trans (by linarith [hτt n])
  have hSTWB : ∀ K : ℕ, sz.STWB n (τ n) K ≤
      ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) + ((sz.W n : ℕ) : ℝ) ^ (-δ) :=
    fun K => farEntry_stwb_le sz (by omega) n K hδ hτ1 hwo.1 hrcτ
  have hind0 := farEntry_indMax_eq_one sz C n ω h𝔠 h𝔡 hδ hbw hW2n hSTWB (fun x y => hn1 (x, y))
  have hind : STindMaxg C n (τ n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω = 1 := by
    refine farEntry_indg_of_le C n (τ n) _ ω fun x y => ?_
    rcases farEntry_indg_cases C n (τ n) (((sz.W n : ℕ) : ℝ) ^ (-(min (2 * 𝔡) δ / 4))) ω with ⟨-, h⟩ | h0
    · exact (h x y).trans (Real.rpow_le_rpow_of_exponent_le hW1 (by linarith))
    · rw [hind0] at h0; norm_num at h0
  by_cases hfar : c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (τ n) ≤
      ((zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) : ℕ) : ℝ)
  swap
  · simp only [hfar, ↓reduceIte, mul_zero] at hp
    have : 0 < ((sz.size n : ℕ) : ℝ) ^ τ₀ * ((sz.W n : ℕ) : ℝ) ^ (-D') := by positivity
    linarith
  simp only [hfar, ↓reduceIte, mul_one] at hp
  have hℓ1 : 1 ≤ ellT (sz.L n) (sz.lam n) (τ n) := one_le_ellT hL1
  have hxy : x ≠ y := by
    rintro rfl
    rw [sub_self, farEntry_zdistInf_zero, Nat.cast_zero] at hfar
    have : 0 < c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (τ n) := by
      have := hGn.1; positivity
    linarith
  have hgex := hn2 ⟨(x, y), hxy⟩
  rw [hind, one_mul] at hgex
  have hrhs := farEntry_rhs_le sz n (D' := D') (ε₀ := ε₀) (τ' := τ n) hc hcg hε₀.le h𝔠 hbw hW2 hGn.1 hGn.2 hfar
  have hMb := hMn x y hfar
  have hGM : ‖C.G n (τ n) ω x y‖ ≤ ‖C.GM n (τ n) ω x y‖ + ‖C.M n x y‖ := by
    have := norm_add_le (C.GM n (τ n) ω x y) (C.M n x y)
    simpa [FlowFM.GM] using this
  have hq0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ₀ / 2) := Real.rpow_nonneg hN0.le _
  have hqq : ((sz.size n : ℕ) : ℝ) ^ τ₀ = ((sz.size n : ℕ) : ℝ) ^ (τ₀ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ₀ / 2) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hP0 : 0 < ((sz.W n : ℕ) : ℝ) ^ (-D') := Real.rpow_pos_of_pos hWpos _
  have h1 : ‖C.GM n (τ n) ω x y‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ₀ / 2) * (3 * ((sz.W n : ℕ) : ℝ) ^ (-D')) :=
    hgex.trans (mul_le_mul_of_nonneg_left hrhs hq0)
  rw [hqq] at hp
  have hqP : 4 * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.size n : ℕ) : ℝ) ^ (τ₀ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-D') :=
    mul_le_mul_of_nonneg_right hN4 hP0.le
  have hqqP := mul_le_mul_of_nonneg_right hN4 (mul_nonneg hq0 hP0.le)
  nlinarith only [hp, hGM, hMb, h1, hqP, hqqP, hP0]

private theorem farEntry_exp_lb : (1 / 8 : ℝ) ≤ Real.exp (-2) := by
  have h1' : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2' : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [Real.exp_neg, h2', le_inv_comm₀ (by norm_num) (by positivity)]
  nlinarith [Real.exp_pos 1]

private theorem farEntry_gij_arith {G2 q X Y R : ℝ} (hq : 1 ≤ q) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hG : G2 ≤ q * (2 * q * (X * X) + Y * Y)) (hXY : X + Y ≤ 8 * R) : G2 ≤ (16 * q * R) ^ 2 := by
  have hq0 : 0 ≤ q := by linarith
  have h1 : q * (2 * q * (X * X) + Y * Y) ≤ 2 * q ^ 2 * ((X + Y) * (X + Y)) := by
    have : q * (Y * Y) ≤ q * q * (Y * Y) := mul_le_mul_of_nonneg_right (by nlinarith) (mul_nonneg hY hY)
    nlinarith [mul_nonneg (mul_nonneg hq0 hq0) (mul_nonneg hX hY)]
  have h2 : (X + Y) * (X + Y) ≤ (8 * R) * (8 * R) := mul_self_le_mul_self (add_nonneg hX hY) hXY
  have h3 : 2 * q ^ 2 * ((X + Y) * (X + Y)) ≤ 2 * q ^ 2 * ((8 * R) * (8 * R)) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  nlinarith [sq_nonneg (q * R)]

/-- **`(GijGEX)` over any carrier, for every `ε₀`, gives `STGijDecgL`** (with `c = 1`): the right side of `(GijGEX)`
(`STgexRHSg`, `2 · 9^d`-neighbour loops and `W^{-d} 1_{|a-b|≤1}`) is bounded by `2 q (ΣΦ)² + Ψ² 1_{|a-b|≤1}` from the loop premise
(`‖𝓛‖ ≤ q Φ²` at `q = N^{τ/4}`), and `≤ (16 q R)²` for the right side `R` of `STGijDecgL` (`e^{-2} ≥ 1/8`, `W^{-d} ≤ Ψ²`).  The
statement of `STGijDecgL` takes the loop premise for both mixed charges, which is exactly what `STgexRHSg` sums. -/
theorem stGijDecgL_of_gex (t : ℕ → ℝ)
    (hsize : Tendsto sz.size atTop atTop) (h : ∀ ε₀ : ℝ, 0 < ε₀ → STGijGEXgL C μ t ε₀) :
    STGijDecgL C μ t := by
  refine ⟨1, one_pos, fun ε₀ hε₀ D hD Φ Ψ hΦ hΨ1 _ hL => ?_⟩
  refine StochDomAt.of_subset_union hsize (h ε₀ hε₀) hL fun τ hτ => ⟨τ / 4, by positivity, ?_⟩
  have hK : ∀ᶠ n : ℕ in atTop, (16 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (3 * τ / 4) :=
    ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < 3 * τ / 4)).comp
      (tendsto_natCast_atTop_atTop.comp hsize)).eventually_ge_atTop 16
  filter_upwards [hΦ, hΨ1, hK] with n hΦn hΨn hKn
  rintro ω ⟨p, hp⟩
  by_contra hno
  simp only [Set.mem_union, badSetAt, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno
  obtain ⟨h1, h2⟩ := hno
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.2 (sz.one_le_size n)
  have hN0 : 0 < N := by linarith
  set q : ℝ := N ^ (τ / 4) with hqdef
  have hq1 : 1 ≤ q := Real.one_le_rpow hN1 (by positivity)
  have hNq : 16 * q ≤ N ^ τ := by
    have : N ^ τ = q * N ^ (3 * τ / 4) := by rw [hqdef, ← Real.rpow_add hN0]; congr 1; ring
    rw [this]; nlinarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  set a := STblk sz n p.1.1
  set b := STblk sz n p.1.2
  set A := Finset.univ.filter (fun a' : Zd d (sz.L n) => zdistInf d (sz.L n) (a' - a) ≤ 1)
  set B := Finset.univ.filter (fun b' : Zd d (sz.L n) => zdistInf d (sz.L n) (b' - b) ≤ 1)
  set X : ℝ := ∑ a' ∈ A, ∑ b' ∈ B, Φ n a' b'
  set ind : ℝ := if zdistInf d (sz.L n) (a - b) ≤ 1 then 1 else 0
  have hΦ0 : ∀ a' b', 0 ≤ Φ n a' b' := fun a' b' => (hΦn a' b').1.le
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hΦ0 _ _
  have hΨ0 : 0 ≤ Ψ n := (Real.rpow_nonneg hW0.le _).trans hΨn
  have hind : ind = 0 ∨ ind = 1 := by by_cases hab : zdistInf d (sz.L n) (a - b) ≤ 1 <;> simp [ind, hab]
  have hind0 : 0 ≤ ind := by rcases hind with h | h <;> simp [h]
  -- the right side `R` of the conclusion is `≥ (X + Ψ ind) / 8`
  have he2 : (1 / 8 : ℝ) ≤ Real.exp (-2) := farEntry_exp_lb
  have he1 : Real.exp (-2) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by norm_num)
  set R : ℝ := (∑ a' : Zd d (sz.L n), ∑ b' : Zd d (sz.L n), Φ n a' b' *
      Real.exp (-1 * ((zdistInf d (sz.L n) (a' - a) : ℝ) + (zdistInf d (sz.L n) (b' - b) : ℝ)))) +
    Ψ n * Real.exp (-1 * (zdistInf d (sz.L n) (a - b) : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-D) with hRdef
  have hF : ∀ a' b', 0 ≤ Φ n a' b' *
      Real.exp (-1 * ((zdistInf d (sz.L n) (a' - a) : ℝ) + (zdistInf d (sz.L n) (b' - b) : ℝ))) :=
    fun a' b' => mul_nonneg (hΦ0 _ _) (Real.exp_pos _).le
  have hS1 : X / 8 ≤ ∑ a' : Zd d (sz.L n), ∑ b' : Zd d (sz.L n), Φ n a' b' *
      Real.exp (-1 * ((zdistInf d (sz.L n) (a' - a) : ℝ) + (zdistInf d (sz.L n) (b' - b) : ℝ))) := by
    have hX8 : X / 8 = ∑ a' ∈ A, ∑ b' ∈ B, Φ n a' b' / 8 := by simp only [X, Finset.sum_div]
    have h1 : X / 8 ≤ ∑ a' ∈ A, ∑ b' ∈ B, Φ n a' b' *
        Real.exp (-1 * ((zdistInf d (sz.L n) (a' - a) : ℝ) + (zdistInf d (sz.L n) (b' - b) : ℝ))) := by
      rw [hX8]
      refine Finset.sum_le_sum fun a' ha' => Finset.sum_le_sum fun b' hb' => ?_
      have h1'' : ((zdistInf d (sz.L n) (a' - a) : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (Finset.mem_filter.1 ha').2
      have h2'' : ((zdistInf d (sz.L n) (b' - b) : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (Finset.mem_filter.1 hb').2
      have hexp : (1 / 8 : ℝ) ≤ Real.exp (-1 * ((zdistInf d (sz.L n) (a' - a) : ℝ) + (zdistInf d (sz.L n) (b' - b) : ℝ))) :=
        he2.trans (Real.exp_le_exp.2 (by linarith))
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hexp (hΦ0 _ _)
    have h2 : ∑ a' ∈ A, ∑ b' ∈ B, Φ n a' b' *
        Real.exp (-1 * ((zdistInf d (sz.L n) (a' - a) : ℝ) + (zdistInf d (sz.L n) (b' - b) : ℝ))) ≤
        ∑ a' ∈ A, ∑ b' : Zd d (sz.L n), Φ n a' b' *
        Real.exp (-1 * ((zdistInf d (sz.L n) (a' - a) : ℝ) + (zdistInf d (sz.L n) (b' - b) : ℝ))) :=
      Finset.sum_le_sum fun a' _ => Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun b' _ _ => hF a' b'
    have h3 : ∑ a' ∈ A, ∑ b' : Zd d (sz.L n), Φ n a' b' *
        Real.exp (-1 * ((zdistInf d (sz.L n) (a' - a) : ℝ) + (zdistInf d (sz.L n) (b' - b) : ℝ))) ≤
        ∑ a' : Zd d (sz.L n), ∑ b' : Zd d (sz.L n), Φ n a' b' *
        Real.exp (-1 * ((zdistInf d (sz.L n) (a' - a) : ℝ) + (zdistInf d (sz.L n) (b' - b) : ℝ))) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun a' _ _ => Finset.sum_nonneg fun b' _ => hF a' b'
    exact h1.trans (h2.trans h3)
  have hS2 : Ψ n * ind / 8 ≤ Ψ n * Real.exp (-1 * (zdistInf d (sz.L n) (a - b) : ℝ)) := by
    by_cases hab : zdistInf d (sz.L n) (a - b) ≤ 1
    · have hd1 : ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hab
      have hexp : (1 / 8 : ℝ) ≤ Real.exp (-1 * (zdistInf d (sz.L n) (a - b) : ℝ)) :=
        he2.trans (Real.exp_le_exp.2 (by linarith))
      have hi : ind = 1 := by simp [ind, hab]
      rw [hi, mul_one, div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hexp hΨ0
    · have hi : ind = 0 := by simp [ind, hab]
      rw [hi, mul_zero, zero_div]; exact mul_nonneg hΨ0 (Real.exp_pos _).le
  have hR : (X + Ψ n * ind) / 8 ≤ R := by
    have : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
    rw [hRdef]; linarith
  have hR0 : 0 ≤ R := le_trans (by positivity) hR
  -- the indicator of `Ω`
  by_cases hi : ∀ x y : Idx d (sz.L n) (sz.W n), ‖C.GM n (t n) ω x y‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)
  swap
  · have hi0 : STindMaxg C n (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω = 0 := by simp [STindMaxg, hi]
    have := hp; simp only [hi0, zero_mul] at this
    have : 0 ≤ N ^ τ * R := mul_nonneg (Real.rpow_nonneg hN0.le _) hR0
    linarith
  have hi1 : STindMaxg C n (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω = 1 := by simp [STindMaxg, hi]
  have hp' := hp; simp only [hi1, one_mul] at hp'
  have hG := h1 p; simp only [hi1, one_mul] at hG
  -- the loops: `‖L_σ(a',b')‖ ≤ q Φ(a',b')²` for both mixed charges
  have hLb : ∀ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)), ∀ a' b',
      ‖C.L n (t n) σ ![a', b'] ω‖ ≤ q * Φ n a' b' ^ 2 := by
    intro σ hσ a' b'
    have hσ' : σ 0 ≠ σ 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
      rcases hσ with rfl | rfl <;> decide
    have := h2 (⟨σ, hσ'⟩, a', b'); simp only [hi1, one_mul] at this; exact this
  have hΦX : ∑ a' ∈ A, ∑ b' ∈ B, Φ n a' b' ^ 2 ≤ X * X := by
    have hle : ∀ a' ∈ A, ∀ b' ∈ B, Φ n a' b' ≤ X := fun a' ha' b' hb' =>
      (Finset.single_le_sum (f := fun b' => Φ n a' b') (fun _ _ => hΦ0 _ _) hb').trans
        (Finset.single_le_sum (f := fun a' => ∑ b' ∈ B, Φ n a' b')
          (fun _ _ => Finset.sum_nonneg fun _ _ => hΦ0 _ _) ha')
    calc ∑ a' ∈ A, ∑ b' ∈ B, Φ n a' b' ^ 2 ≤ ∑ a' ∈ A, ∑ b' ∈ B, Φ n a' b' * X :=
          Finset.sum_le_sum fun a' ha' => Finset.sum_le_sum fun b' hb' => by
            rw [sq]; exact mul_le_mul_of_nonneg_left (hle a' ha' b' hb') (hΦ0 _ _)
      _ = X * X := by simp only [X, Finset.sum_mul]
  have hloops : (∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)), ∑ a' ∈ A, ∑ b' ∈ B,
      ‖C.L n (t n) σ ![a', b'] ω‖) ≤ 2 * q * (X * X) := by
    calc _ ≤ ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)), ∑ a' ∈ A, ∑ b' ∈ B,
          q * Φ n a' b' ^ 2 := Finset.sum_le_sum fun σ hσ => Finset.sum_le_sum fun a' _ =>
            Finset.sum_le_sum fun b' _ => hLb σ hσ a' b'
      _ = 2 * (q * ∑ a' ∈ A, ∑ b' ∈ B, Φ n a' b' ^ 2) := by
          rw [Finset.sum_const, Finset.card_pair (by decide)]; simp [Finset.mul_sum]
      _ ≤ 2 * (q * (X * X)) := by gcongr
      _ = 2 * q * (X * X) := by ring
  -- `W^{-d} ≤ Ψ²`
  have hWΨ : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ Ψ n ^ 2 := by
    have e : (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le, ← Real.rpow_natCast, ← Real.rpow_neg hW0.le]
      congr 1; push_cast; ring
    rw [← e]; exact pow_le_pow_left₀ (Real.rpow_nonneg hW0.le _) hΨn 2
  have hgex : STgexRHSg C n (t n) ω a b ≤ 2 * q * (X * X) + Ψ n ^ 2 * ind := by
    unfold STgexRHSg
    have : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ind ≤ Ψ n ^ 2 * ind := mul_le_mul_of_nonneg_right hWΨ hind0
    exact add_le_add hloops this
  have hsq : ‖C.GM n (t n) ω p.1.1 p.1.2‖ ^ 2 ≤ (16 * q * R) ^ 2 := by
    have hind2 : Ψ n ^ 2 * ind = (Ψ n * ind) * (Ψ n * ind) := by
      rcases hind with h | h <;> simp [h, sq]
    have hR8 : X + Ψ n * ind ≤ 8 * R := by linarith
    refine farEntry_gij_arith hq1 hX0 (mul_nonneg hΨ0 hind0) ?_ hR8
    rw [← hind2]
    exact hG.trans (mul_le_mul_of_nonneg_left hgex (by linarith))
  have hle := (pow_le_pow_iff_left₀ (n := 2) (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
  have : 16 * q * R ≤ N ^ τ * R := mul_le_mul_of_nonneg_right hNq hR0
  linarith


/-- **The band implication** `STGbEXPij → STGijDecgL (bandFM …)` (`(GijGEX)` of `lem_GbEXP` through `bandFM_STGijGEX`). -/
theorem bandFM_STGijDecgL (hG : STGbEXPij d) {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    {z : ℕ → ℂ} (hf : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n)
    (htT : ∀ n, t n ≤ lemT (z n)) : STGijDecgL (bandFM sz (STflowE z)) (Sizes.seqP sz) t :=
  stGijDecgL_of_gex _ _ t (Sizes.tendsto_size sz hf.1.2.2.1) fun ε₀ hε₀ =>
    (bandFM_STGijGEX sz (STflowE z) t ε₀).1 (hG κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hf t ht0 htT ε₀ hε₀)

/-- Unconditional at `3 ≤ d` (`stGbEXPij_of_v3 (gbEXPV3 hd)`, `Green/GbEXP:806`). -/
theorem bandFM_STGijDecgL_of_three_le (hd : 3 ≤ d) {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    {z : ℕ → ℂ} (hf : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n)
    (htT : ∀ n, t n ≤ lemT (z n)) : STGijDecgL (bandFM sz (STflowE z)) (Sizes.seqP sz) t :=
  bandFM_STGijDecgL (RBM.Green.stGbEXPij_of_v3 (RBM.Green.gbEXPV3 hd)) hκ hε h𝔡 hf ht0 htT

/-- **The band implication** `kellStarEv → STKfargL (bandFM …)`: `𝒦^{(2)}_{(s,-s),(x,x')} = W^{-d} Θ_t(x,x')`
(`farEntry_K_le`, `KLK_two`, `m(σ) m(-σ) = 1`) and `kellStarEv` at `δ = 1`, `D + 2d`. -/
theorem bandFM_STKfargL (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ) (hε : 0 < ε)
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (htT : ∀ n, t n ≤ lemT (z n)) :
    STKfargL (bandFM sz (STflowE z)) t := by
  intro D hD
  obtain ⟨h𝔠, h𝔡, hN, hBW, hWO⟩ := id hflow.1
  obtain ⟨-, -, ht1, hRC⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow htT
  have hlam : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hWO] with n hn
    have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hn.1, hn.2⟩
  have hdpos : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hKell := RBM.Path.kellStarEv d sz 𝔠 𝔡⁻¹ (ε / 2) 1 (D + 2 * d) t hd h𝔠 (inv_pos.2 h𝔡) (half_pos hε)
    one_pos hN hBW hRC ht1 hlam
  filter_upwards [hKell] with n hKn x x' s hfar
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have him : 0 < (z n).im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) (hflow.2 n).2.1
  have hE : |STflowE z n| ≤ 2 := by
    have := (abs_lemE_le him).trans (hflow.2 n).1
    change |lemE (z n)| ≤ 2
    linarith
  have hTh := (hKn 0 (t n) le_rfl (ht0 n) le_rfl x x' (by rw [one_mul]; exact hfar)).1
  have hσ : (![s, !s] : Fin 2 → Bool) ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)) := by
    cases s <;> simp
  have hK := RBM.Gauss.Sizes.farEntry_K_le sz n hE hW1 x x' ![s, !s] hσ hTh
  change ‖sz.STKloop n (STflowE z n) (t n) ![s, !s] ![x, x']‖ ≤ _
  refine hK.trans (le_of_eq ?_)
  rw [Real.rpow_neg hWpos.le, Real.rpow_neg hWpos.le, ← Real.rpow_natCast, ← mul_inv, ← Real.rpow_add hWpos]
  congr 2
  ring

end Generic

end RBM.BA

/-! ## 5. The compiled nonempty instance

At `d = 3` on the merged `RBM.Gauss.Step5Inst.szCL` (`Induction/Step5Pins.lean:640`: `m = n + 24`,
`L_n = 2 m^5`, `W_n = 2^m`, `ilambda = 1`; flow `zCL`, `s ≡ 0`, `1 - t_n = L_n^{-2}`; `L_n ≥ 2`,
`W_n ≥ L_n`, `szCL_tendsto`, `szCL_bandwidth`): the flow `flow_zCL`, `0 ≤ s ≤ t ≤ lemT zCL`
(`lemT_zCL`) are proved, the time is `τ = s ≡ 0` (`ℓ_s = 1`), and only `STStep2Concl` (the Step 2 pins,
another gate) stays a hypothesis.  The far set `{c (log W)³ ℓ_s ≤ |[x]-[y]|_∞}` is nonempty at every `n`
for `c = 1` (`farEntry_szCL_far_nonempty`; `sz0` is not used: its far set is empty until `n ≈ 3·10^5`). -/

end
