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

/-- **The section lemma.**  A domination `≺` uniform over `u ∈ [s_n, t_n]` (the index type
`TimeIcc s t n × V n`) restricts to the section at a time sequence `τ` with `s ≤ τ ≤ t`: the
union over `u` is shrunk to the single time `τ n`.  (As `STLK_of_STLKU`, `Step34Pins.lean:291`.)
Used here for `STLocalEntryU` and `STGdecayW`. -/
theorem prec_timeIcc_section {d : ℕ} (sz : Sizes d) {s t τ : ℕ → ℝ} (hsτ : ∀ n, s n ≤ τ n)
    (hτt : ∀ n, τ n ≤ t n) {V : ℕ → Type*} {ξ ζ : ∀ n, TimeIcc s t n × V n → sz.SeqΩ → ℝ}
    (h : sz.Prec ξ ζ) :
    sz.Prec (U := V) (fun n v ω => ξ n (⟨τ n, hsτ n, hτt n⟩, v) ω)
      (fun n v ω => ζ n (⟨τ n, hsτ n, hτt n⟩, v) ω) :=
  StochDomAt.precomp_param h (fun n v => (⟨τ n, hsτ n, hτt n⟩, v))

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

/-- `|a - b|_∞ ≤ |a' - b'|_∞ + 2` when `|a' - a|_∞ ≤ 1` and `|b' - b|_∞ ≤ 1`
(`FarEntry:106`, `farEntry_zdist2_tri`, with `zdist2 ↦ zdistInf`). -/
private theorem farEntry_zdistInf_tri (a b a' b' : Zd d L) (h1 : zdistInf d L (a' - a) ≤ 1)
    (h2 : zdistInf d L (b' - b) ≤ 1) :
    zdistInf d L (a - b) ≤ zdistInf d L (a' - b') + 2 := by
  have e : a - b = ((a - a') + (a' - b')) + (b' - b) := by abel
  have hA := farEntry_zdistInf_add_le ((a - a') + (a' - b')) (b' - b)
  have hB := farEntry_zdistInf_add_le (a - a') (a' - b')
  have hC := farEntry_zdistInf_comm a a'
  rw [e]
  omega

end Lattice

/-! ### The charge `σ = false` is the transpose of `σ = true` -/

section Charge

variable {d : ℕ} (sz : Sizes d)

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

/-- `|(G^-)_{xy}| = |(G^+)_{yx}|`. -/
private theorem farEntry_norm_Gt_false (n : ℕ) (E u : ℝ) (ω : sz.SeqΩ)
    (x y : Idx d (sz.L n) (sz.W n)) :
    ‖Gt sz n E u false ω x y‖ = ‖Gt sz n E u true ω y x‖ := by
  have h : Gres (sz.seqHflow n u ω) (zt E u) false = (Gres (sz.seqHflow n u ω) (zt E u) true)ᴴ :=
    farEntry_Gres_false (Sizes.seqHflow_isHermitian sz n u ω) _
  unfold Gt
  rw [h, Matrix.conjTranspose_apply, norm_star]

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

/-- **The far neighbour bound** (`farEntry_term_step`, `FarEntry:533`, with the loss of
`STGdecayW`).  Let `(a,b)` be a far pair of blocks, `c (log W)³ ℓ_τ ≤ |a-b|_∞`, `(a',b')` a pair of
neighbours (`|a'-a|_∞, |b'-b|_∞ ≤ 1`), `σ ∈ {(+,-),(-,+)}`.  Then `|a'-b'|_∞ ≥ (c (log W)³ - 2) ℓ_τ`,
`‖𝒦_σ(a',b')‖ ≤ W^{-2D'}` (far field `hTheta`, `kellStarEv` with `δ = 1`) and the right side of
`STGdecayW` at `D = 2D'` is at most `2 W^{-2D'}` (`farEntry_loss_le`, `farEntry_exp_arith`), so that
from the failure-free bound `hdec` (`‖𝓛-𝒦‖ ≤ N^{τ₃} · (right side)`) one gets
`‖𝓛_σ(a',b')‖ ≤ 3 N^{τ₃} W^{-2D'}`.  All hypotheses are deterministic and hold eventually
in `n` for the flow. -/
private theorem farEntry_neighbour (n : ℕ) (ω : sz.SeqΩ) {E s τ 𝔠 c D' Cd τ₃ : ℝ}
    (h𝔠 : 0 < 𝔠) (hc : 0 < c) (hD' : 0 < D') (hτ₃ : 0 ≤ τ₃)
    (hE : |E| ≤ 2) (hs0 : 0 ≤ s) (hsτ : s ≤ τ) (hτ1 : τ < 1)
    (hN1u : ((sz.size n : ℕ) : ℝ)⁻¹ ≤ 1 - τ)
    (hbw : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ))
    (hG : farEntry_X0 c ((max Cd 0 + 2) / 𝔠 + 2 * D') ≤ Real.log ((sz.W n : ℕ) : ℝ))
    (hTheta : ∀ a b : Zd d (sz.L n),
      1 * (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (sz.lam n) τ) ≤
          (zdistInf d (sz.L n) (a - b) : ℝ) →
        ‖Theta d (sz.L n) (sz.lam n) (τ : ℂ) a b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-(2 * D')))
    (hdec : ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)),
      ‖sz.Lloop n E τ σ b ω - sz.STKloop n E τ σ b‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ₃ *
        (((1 - s) / (1 - τ)) ^ Cd * (sz.Bctl n τ) ^ (1 / 5 : ℝ) *
            sz.STWB n τ (zdistInf d (sz.L n) (b 0 - b 1)) *
            Real.exp (-(((zdistInf d (sz.L n) (b 0 - b 1) : ℕ) : ℝ) /
              ellT (sz.L n) (sz.lam n) τ) ^ (1 / 2 : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-(2 * D'))))
    {a b a' b' : Zd d (sz.L n)}
    (hfar : c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) τ ≤
      (zdistInf d (sz.L n) (a - b) : ℝ))
    (h1 : zdistInf d (sz.L n) (a' - a) ≤ 1) (h2 : zdistInf d (sz.L n) (b' - b) ≤ 1)
    (σ : Fin 2 → Bool) (hσ : σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool))) :
    ‖sz.Lloop n E τ σ ![a', b'] ω‖ ≤
      3 * ((sz.size n : ℕ) : ℝ) ^ τ₃ * ((sz.W n : ℕ) : ℝ) ^ (-(2 * D')) := by
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
  have hG4 : 4 ≤ c * G := by nlinarith [sq_nonneg K₁]
  have hlogA : G ^ ((3 : ℝ) / 2) + 2 ≤ c * G ^ 3 := farEntry_log_arith hG1 hG4
  have hℓ1 : 1 ≤ ℓ := one_le_ellT hL1
  have hℓpos : 0 < ℓ := by linarith
  -- geometry: `|a'-b'|_∞ ≥ (c G³ - 2) ℓ`
  have hz : (zdistInf d (sz.L n) (a - b) : ℝ) ≤ (zdistInf d (sz.L n) (a' - b') : ℝ) + 2 := by
    exact_mod_cast farEntry_zdistInf_tri a b a' b' h1 h2
  have hdist : (c * G ^ 3 - 2) * ℓ ≤ (zdistInf d (sz.L n) (a' - b') : ℝ) := by
    have : (c * G ^ 3 - 2) * ℓ = c * G ^ 3 * ℓ - 2 * ℓ := by ring
    linarith
  have hKcond : 1 * (G ^ ((3 : ℝ) / 2) * ℓ) ≤ (zdistInf d (sz.L n) (a' - b') : ℝ) := by
    rw [one_mul]
    refine le_trans ?_ hdist
    exact mul_le_mul_of_nonneg_right (by linarith) hℓpos.le
  -- the `𝒦` bound
  have hK := farEntry_K_le sz n hE hW1 a' b' σ hσ (hTheta a' b' hKcond)
  -- the exponential
  have hy : c * G ^ 3 - 2 ≤ (zdistInf d (sz.L n) (a' - b') : ℝ) / ℓ := by
    rw [le_div_iff₀ hℓpos]; exact hdist
  have hexp := farEntry_exp_arith hK₁0 hWpos hG1 (by linarith) hy
  have hexp0 : 0 ≤ Real.exp (-(((zdistInf d (sz.L n) (a' - b') : ℕ) : ℝ) / ℓ) ^ (1 / 2 : ℝ)) :=
    (Real.exp_pos _).le
  have hloss := farEntry_loss_le sz n (Cd := Cd) (zdistInf d (sz.L n) (a' - b')) hs0 hsτ hτ1 hN1u
  have hNW : ((sz.size n : ℕ) : ℝ) ^ (max Cd 0 + 2) ≤
      ((sz.W n : ℕ) : ℝ) ^ ((max Cd 0 + 2) / 𝔠) :=
    Sizes.size_rpow_le_W_rpow sz h𝔠 n hbw (by have := le_max_right Cd 0; linarith)
  have hfirst : ((1 - s) / (1 - τ)) ^ Cd * (sz.Bctl n τ) ^ (1 / 5 : ℝ) *
        sz.STWB n τ (zdistInf d (sz.L n) (a' - b')) *
        Real.exp (-(((zdistInf d (sz.L n) (a' - b') : ℕ) : ℝ) / ℓ) ^ (1 / 2 : ℝ)) ≤
      ((sz.W n : ℕ) : ℝ) ^ (-(2 * D')) := by
    have hWD : 0 < ((sz.W n : ℕ) : ℝ) ^ (2 * D') := Real.rpow_pos_of_pos hWpos _
    have hsplit : ((sz.W n : ℕ) : ℝ) ^ K₁ =
        ((sz.W n : ℕ) : ℝ) ^ ((max Cd 0 + 2) / 𝔠) * ((sz.W n : ℕ) : ℝ) ^ (2 * D') :=
      Real.rpow_add hWpos _ _
    rw [hsplit] at hexp
    rw [Real.rpow_neg hWpos.le]
    calc ((1 - s) / (1 - τ)) ^ Cd * (sz.Bctl n τ) ^ (1 / 5 : ℝ) *
          sz.STWB n τ (zdistInf d (sz.L n) (a' - b')) *
          Real.exp (-(((zdistInf d (sz.L n) (a' - b') : ℕ) : ℝ) / ℓ) ^ (1 / 2 : ℝ))
        ≤ (4 * ((sz.W n : ℕ) : ℝ) ^ ((max Cd 0 + 2) / 𝔠)) *
          Real.exp (-(((zdistInf d (sz.L n) (a' - b') : ℕ) : ℝ) / ℓ) ^ (1 / 2 : ℝ)) := by
          refine mul_le_mul_of_nonneg_right (hloss.trans ?_) hexp0
          linarith
      _ = (4 * (((sz.W n : ℕ) : ℝ) ^ ((max Cd 0 + 2) / 𝔠) * ((sz.W n : ℕ) : ℝ) ^ (2 * D')) *
            Real.exp (-(((zdistInf d (sz.L n) (a' - b') : ℕ) : ℝ) / ℓ) ^ (1 / 2 : ℝ))) *
            (((sz.W n : ℕ) : ℝ) ^ (2 * D'))⁻¹ := by field_simp
      _ ≤ 1 * (((sz.W n : ℕ) : ℝ) ^ (2 * D'))⁻¹ := by
          gcongr
      _ = (((sz.W n : ℕ) : ℝ) ^ (2 * D'))⁻¹ := one_mul _
  have hdec' := hdec σ ![a', b']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hdec'
  have hNτ : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ₃ := Real.one_le_rpow hN1 hτ₃
  have hW2 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-(2 * D')) := Real.rpow_nonneg hWpos.le _
  calc ‖sz.Lloop n E τ σ ![a', b'] ω‖
      = ‖sz.STKloop n E τ σ ![a', b'] + (sz.Lloop n E τ σ ![a', b'] ω -
          sz.STKloop n E τ σ ![a', b'])‖ := by rw [add_sub_cancel]
    _ ≤ ‖sz.STKloop n E τ σ ![a', b']‖ +
          ‖sz.Lloop n E τ σ ![a', b'] ω - sz.STKloop n E τ σ ![a', b']‖ := norm_add_le _ _
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ (-(2 * D')) + ((sz.size n : ℕ) : ℝ) ^ τ₃ *
          (((sz.W n : ℕ) : ℝ) ^ (-(2 * D')) + ((sz.W n : ℕ) : ℝ) ^ (-(2 * D'))) := by
        refine add_le_add hK (hdec'.trans ?_)
        exact mul_le_mul_of_nonneg_left (add_le_add hfirst le_rfl) (by linarith)
    _ ≤ 3 * ((sz.size n : ℕ) : ℝ) ^ τ₃ * ((sz.W n : ℕ) : ℝ) ^ (-(2 * D')) := by
        nlinarith


/-- **The far part of the right side of (`GijGEX`)** (`farEntry_ind_gexRHS_le`, `FarEntry:504`; and
`RBM.Ind.s1_gexRHS_le`, `Induction/Step1Setup.lean:1015`, whose hypotheses are on all `(σ, b)`):
on the far set `|a - b|_∞ > 1` the term `W^{-d} 1_{|a-b|≤1}` of `STgexRHS` vanishes, and the sum has
at most `2` charges and `3^d · 3^d` neighbouring pairs, so `STgexRHS ≤ 2 · 9^d B` if every loop
`‖𝓛^{(2)}_{σ,(a',b')}‖ ≤ B` at the neighbours (`RBM.Ind.s1_near_card`: the `L^∞` ball has `≤ 3^d`
points; the ticket's `(2d+1)²` is the `zdistD` ball). -/
private theorem farEntry_gexRHS_le (n : ℕ) (E u B : ℝ) (ω : sz.SeqΩ) (a b : Zd d (sz.L n))
    (hab : ¬ zdistInf d (sz.L n) (a - b) ≤ 1) (hB : 0 ≤ B)
    (hL : ∀ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
      ∀ a' b' : Zd d (sz.L n), zdistInf d (sz.L n) (a' - a) ≤ 1 → zdistInf d (sz.L n) (b' - b) ≤ 1 →
        ‖sz.Lloop n E u σ ![a', b'] ω‖ ≤ B) :
    sz.STgexRHS n E u ω a b ≤ 2 * 9 ^ d * B := by
  classical
  unfold Sizes.STgexRHS
  set Fa := Finset.univ.filter (fun a' : Zd d (sz.L n) => zdistInf d (sz.L n) (a' - a) ≤ 1)
    with hFa
  set Fb := Finset.univ.filter (fun b' : Zd d (sz.L n) => zdistInf d (sz.L n) (b' - b) ≤ 1)
    with hFb
  have hFa' : (Fa.card : ℝ) ≤ 3 ^ d := RBM.Ind.s1_near_card a
  have hFb' : (Fb.card : ℝ) ≤ 3 ^ d := RBM.Ind.s1_near_card b
  have h3d : (0 : ℝ) ≤ 3 ^ d := by positivity
  have hinner : ∀ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
      ∑ a' ∈ Fa, ∑ b' ∈ Fb, ‖sz.Lloop n E u σ ![a', b'] ω‖ ≤ 3 ^ d * (3 ^ d * B) := by
    intro σ hσ
    calc ∑ a' ∈ Fa, ∑ b' ∈ Fb, ‖sz.Lloop n E u σ ![a', b'] ω‖
        ≤ ∑ _a' ∈ Fa, ((3 : ℝ) ^ d * B) := Finset.sum_le_sum fun a' ha' => by
          calc ∑ b' ∈ Fb, ‖sz.Lloop n E u σ ![a', b'] ω‖ ≤ ∑ _b' ∈ Fb, B :=
                Finset.sum_le_sum fun b' hb' =>
                  hL σ hσ a' b' (Finset.mem_filter.1 ha').2 (Finset.mem_filter.1 hb').2
            _ = Fb.card * B := by rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ 3 ^ d * B := mul_le_mul_of_nonneg_right hFb' hB
      _ = Fa.card * ((3 : ℝ) ^ d * B) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 3 ^ d * (3 ^ d * B) := mul_le_mul_of_nonneg_right hFa' (by positivity)
  have hS : ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
      ∑ a' ∈ Fa, ∑ b' ∈ Fb, ‖sz.Lloop n E u σ ![a', b'] ω‖ ≤ 2 * (3 ^ d * (3 ^ d * B)) := by
    calc _ ≤ ∑ _σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
          ((3 : ℝ) ^ d * (3 ^ d * B)) := Finset.sum_le_sum fun σ hσ => hinner σ hσ
      _ = (({![true, false], ![false, true]} : Finset (Fin 2 → Bool)).card : ℝ) *
          (3 ^ d * (3 ^ d * B)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (3 ^ d * (3 ^ d * B)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast Finset.card_le_two
  have h2 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if zdistInf d (sz.L n) (a - b) ≤ 1 then (1 : ℝ) else 0) = 0 := by
    simp [hab]
  have h9 : 2 * ((3 : ℝ) ^ d * (3 ^ d * B)) = 2 * 9 ^ d * B := by
    rw [show (9 : ℝ) = 3 * 3 by norm_num, mul_pow]; ring
  linarith


/-- **The event `Ω(τ, ε₀)` holds** (asGMc, from `STLocalEntryU` at `τ`): with `c₀ = min(2𝔡, δ)` and
`ε₀ = c₀/4`, if `‖G_τ - M‖²_{xy} ≤ N^{𝔠 c₀/4} W^{-d} B_{τ,|[x]-[y]|}` for all `x, y` (the complement
of the failure event of `STLocalEntryU` at the exponent `𝔠 c₀/4`), `N^𝔠 ≤ W`,
`W^{-d} B ≤ W^{-2𝔡} + W^{-δ}` and `W^{c₀/4} ≥ 2`, then `‖G_τ - M‖_max ≤ W^{-ε₀}`, i.e.
`STindMax … W^{-ε₀} = 1` (RBM2D: `farEntry_local_le`, `FarEntry:425`, with `ε₀ = c/2`). -/
private theorem farEntry_indMax_eq_one (n : ℕ) (ω : sz.SeqΩ) {E τ 𝔠 𝔡 δ : ℝ} (h𝔠 : 0 < 𝔠)
    (h𝔡 : 0 < 𝔡) (hδ : 0 < δ)
    (hbw : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ))
    (hW2 : (2 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (min (2 * 𝔡) δ / 4))
    (hSTWB : ∀ K : ℕ, sz.STWB n τ K ≤
      ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) + ((sz.W n : ℕ) : ℝ) ^ (-δ))
    (hb1 : ∀ x y : Idx d (sz.L n) (sz.W n), ‖sz.STGM n E τ ω x y‖ ^ 2 ≤
      ((sz.size n : ℕ) : ℝ) ^ (𝔠 * (min (2 * 𝔡) δ / 4)) *
        sz.STWB n τ (zdistInf d (sz.L n) (sz.STblk n x - sz.STblk n y))) :
    sz.STindMax n E τ (((sz.W n : ℕ) : ℝ) ^ (-(min (2 * 𝔡) δ / 4))) ω = 1 := by
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
  unfold STindMax
  have hall : ∀ x y : Idx d (sz.L n) (sz.W n), ‖sz.STGM n E τ ω x y‖ ≤ W ^ (-(c₀ / 4)) := by
    intro x y
    have h2 := hb1 x y
    have h3 : ‖sz.STGM n E τ ω x y‖ ^ 2 ≤ a * (2 * (a ^ 4)⁻¹) :=
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

section Pin

variable {d : ℕ}

/-- **Pin `STFarEntryAtLog`** (the log-scale far-entry decay of the resolvent at the time sequence `τ`;
paper `3_5:2245` via [DYYY25]; RBM2D `7:534`, `7:541`, `7:622`): for every `c > 0` and `D' > 0`, both
charges `σ` and every pair of fine lattice points `(x, y)` (the index set of `Prec`),
`‖(G_τ(σ))_{xy}‖ · 1[c (log W)³ ℓ_τ ≤ |[x] - [y]|_∞] ≺ W^{-D'}`.  The threshold is the log scale
of the consumer `STCltIsoConcl` (isolation at `10 (log W)³ ℓ_s`); the `W^{τ'} ℓ_τ` threshold of
RBM2D follows since `W^{τ'} ≥ c (log W)³` eventually (paper-delta candidate `T2141a`). -/
def STFarEntryAtLog (sz : Sizes d) (E τ : ℕ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ D' : ℝ, 0 < D' →
    sz.Prec (U := fun n => Bool × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖Gt sz n (E n) (τ n) p.1 ω p.2.1 p.2.2‖ *
        (if c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (τ n) ≤
            ((zdistInf d (sz.L n) (STblk sz n p.2.1 - STblk sz n p.2.2) : ℕ) : ℝ) then 1 else 0))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D'))

/-- **The charge `+` core of `stFarEntryAtLog`** over the pairs of fine lattice points. -/
private theorem farEntry_core (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}
    (hκ : 0 < κ) (hε : 0 < ε) (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t τ : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (ht : ∀ n, t n ≤ lemT (z n))
    (hsτ : ∀ n, s n ≤ τ n) (hτt : ∀ n, τ n ≤ t n) {Cd : ℝ}
    (hStep2 : STStep2Concl sz (STflowE z) s t Cd) {c : ℝ} (hc : 0 < c) {D' : ℝ} (hD' : 0 < D') :
    sz.Prec (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖Gt sz n (STflowE z n) (τ n) true ω p.1 p.2‖ *
        (if c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (τ n) ≤
            ((zdistInf d (sz.L n) (STblk sz n p.1 - STblk sz n p.2) : ℕ) : ℝ) then 1 else 0))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D')) := by
  obtain ⟨h𝔠, h𝔡, hN, hBW, hWO⟩ := id hflow.1
  obtain ⟨-, -, hlt1, hRC⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow ht
  have hsize : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hN
  have hD2 : 0 < 2 * D' := by linarith
  have hδ : 0 < ε / 2 := by linarith
  have hc₀ : 0 < min (2 * 𝔡) (ε / 2) := lt_min (by linarith) hδ
  have hτ0 : ∀ n, 0 ≤ τ n := fun n => (hs n).trans (hsτ n)
  have hτl : ∀ n, τ n ≤ lemT (z n) := fun n => (hτt n).trans (ht n)
  have hij := RBM.Green.stGbEXPij_of_v3 (RBM.Green.gbEXPV3 hd) κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow τ hτ0 hτl
    (min (2 * 𝔡) (ε / 2) / 4) (by positivity)
  have hLoc := prec_timeIcc_section sz hsτ hτt hStep2.1
  have hDec := prec_timeIcc_section sz hsτ hτt (hStep2.2.2 (2 * D') hD2)
  have hWtend : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
      (tendsto_rpow_atTop h𝔠).comp hN
    exact tendsto_atTop_mono' _ hBW h1
  have hlam : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hWO] with n hn
    have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hn.1, hn.2⟩
  have hKell := RBM.Path.kellStarEv d sz 𝔠 𝔡⁻¹ (ε / 2) 1 (2 * D') t hd h𝔠 (inv_pos.2 h𝔡) hδ
    one_pos hN hBW hRC hlt1 hlam
  refine farEntry_union3 hsize hLoc hij hDec ?_
  intro τ₀ hτ₀
  refine ⟨𝔠 * (min (2 * 𝔡) (ε / 2) / 4), by positivity, τ₀ / 2, by positivity, τ₀ / 2,
    by positivity, ?_⟩
  have hGev : ∀ᶠ n : ℕ in atTop, farEntry_X0 c ((max Cd 0 + 2) / 𝔠 + 2 * D') ≤
      Real.log ((sz.W n : ℕ) : ℝ) :=
    (Real.tendsto_log_atTop.comp hWtend).eventually_ge_atTop _
  have hW2ev : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (min (2 * 𝔡) (ε / 2) / 4) :=
    ((tendsto_rpow_atTop (by positivity : 0 < min (2 * 𝔡) (ε / 2) / 4)).comp hWtend).eventually_ge_atTop 2
  have hNev : ∀ᶠ n : ℕ in atTop, 6 * 9 ^ d ≤ ((sz.size n : ℕ) : ℝ) ^ τ₀ :=
    hsize.eventually (eventually_le_rpow (6 * 9 ^ d) hτ₀)
  filter_upwards [hBW, hRC, hWO, hKell, hGev, hW2ev, hNev] with n hbw hrc hwo hke hGn hW2n hN6
  intro ω hω
  by_contra hnot
  simp only [Set.mem_union, not_or, badSetAt, Set.mem_ofPred_eq, not_exists, not_lt] at hnot hω
  obtain ⟨⟨hn1, hn2⟩, hn3⟩ := hnot
  obtain ⟨⟨x, y⟩, hp⟩ := hω
  -- the scales at the index `n`
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hτ1 : τ n < 1 := (hτt n).trans_lt (hlt1 n)
  have hrcτ : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2) ≤ 1 - τ n := hrc.trans (by linarith [hτt n])
  have hN1u : ((sz.size n : ℕ) : ℝ)⁻¹ ≤ 1 - τ n := by
    have h := Real.rpow_le_rpow_of_exponent_le hN1 (show (-1 : ℝ) ≤ -1 + ε / 2 by linarith)
    rw [Real.rpow_neg_one] at h
    linarith
  have him : 0 < (z n).im :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) (hflow.2 n).2.1
  have hE : |STflowE z n| ≤ 2 := by
    have := (abs_lemE_le him).trans (hflow.2 n).1
    change |lemE (z n)| ≤ 2
    linarith
  have hSTWB : ∀ K : ℕ, sz.STWB n (τ n) K ≤
      ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) + ((sz.W n : ℕ) : ℝ) ^ (-(ε / 2)) :=
    fun K => farEntry_stwb_le sz (by omega) n K hδ hτ1 hwo.1 hrcτ
  have hind : sz.STindMax n (STflowE z n) (τ n)
      (((sz.W n : ℕ) : ℝ) ^ (-(min (2 * 𝔡) (ε / 2) / 4))) ω = 1 :=
    farEntry_indMax_eq_one sz n ω h𝔠 h𝔡 hδ hbw hW2n hSTWB (fun x y => hn1 (x, y))
  -- the far set
  by_cases hfar : c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (τ n) ≤
      ((zdistInf d (sz.L n) (sz.STblk n x - sz.STblk n y) : ℕ) : ℝ)
  swap
  · simp only [hfar, ↓reduceIte, mul_zero] at hp
    have : 0 < ((sz.size n : ℕ) : ℝ) ^ τ₀ * ((sz.W n : ℕ) : ℝ) ^ (-D') := by positivity
    linarith
  simp only [hfar, ↓reduceIte, mul_one] at hp
  set G : ℝ := Real.log ((sz.W n : ℕ) : ℝ) with hGdef
  set ℓ : ℝ := ellT (sz.L n) (sz.lam n) (τ n) with hℓdef
  have hK₁0 : 0 ≤ (max Cd 0 + 2) / 𝔠 + 2 * D' := by
    have : 0 ≤ (max Cd 0 + 2) / 𝔠 := div_nonneg (by have := le_max_right Cd 0; linarith) h𝔠.le
    linarith
  obtain ⟨hG1, hG2⟩ := farEntry_X0_le hc hGn
  have hG4 : 4 ≤ c * G := by nlinarith [sq_nonneg ((max Cd 0 + 2) / 𝔠 + 2 * D')]
  have hlogA : G ^ ((3 : ℝ) / 2) + 2 ≤ c * G ^ 3 := farEntry_log_arith hG1 hG4
  have hG32 : 0 ≤ G ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
  have hℓ1 : 1 ≤ ℓ := one_le_ellT hL1
  have hcG3 : c * G ^ 3 ≤ c * G ^ 3 * ℓ := le_mul_of_one_le_right (by nlinarith) hℓ1
  have hr3 : (2 : ℝ) ≤ ((zdistInf d (sz.L n) (sz.STblk n x - sz.STblk n y) : ℕ) : ℝ) := by
    linarith
  have hab : ¬ zdistInf d (sz.L n) (sz.STblk n x - sz.STblk n y) ≤ 1 := by
    intro h
    have : ((zdistInf d (sz.L n) (sz.STblk n x - sz.STblk n y) : ℕ) : ℝ) ≤ 1 := by exact_mod_cast h
    linarith
  have hxy : x ≠ y := by
    rintro rfl
    apply hab
    rw [sub_self, farEntry_zdistInf_zero]
    exact Nat.zero_le _
  have hgex : sz.STindMax n (STflowE z n) (τ n)
        (((sz.W n : ℕ) : ℝ) ^ (-(min (2 * 𝔡) (ε / 2) / 4))) ω * ‖sz.Gt n (STflowE z n) (τ n) true ω x y‖ ^ 2 ≤
      ((sz.size n : ℕ) : ℝ) ^ (τ₀ / 2) * sz.STgexRHS n (STflowE z n) (τ n) ω
        (sz.STblk n x) (sz.STblk n y) := hn2 ⟨(x, y), hxy⟩
  rw [hind, one_mul] at hgex
  -- the neighbours
  have hLb : ∀ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
      ∀ a' b' : Zd d (sz.L n), zdistInf d (sz.L n) (a' - sz.STblk n x) ≤ 1 →
        zdistInf d (sz.L n) (b' - sz.STblk n y) ≤ 1 →
        ‖sz.Lloop n (STflowE z n) (τ n) σ ![a', b'] ω‖ ≤
          3 * ((sz.size n : ℕ) : ℝ) ^ (τ₀ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-(2 * D')) :=
    fun σ hσ a' b' h1 h2 => farEntry_neighbour sz n ω h𝔠 hc hD' (by linarith) hE (hs n) (hsτ n)
      hτ1 hN1u hbw hGn
      (fun a b hab => (hke 0 (τ n) le_rfl (hτ0 n) (hτt n) a b hab).1)
      (fun σ b => hn3 (σ, b)) hfar h1 h2 σ hσ
  have hB : 0 ≤ 3 * ((sz.size n : ℕ) : ℝ) ^ (τ₀ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-(2 * D')) := by
    positivity
  have hrhs := farEntry_gexRHS_le sz n (STflowE z n) (τ n)
    (3 * ((sz.size n : ℕ) : ℝ) ^ (τ₀ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-(2 * D'))) ω
    (sz.STblk n x) (sz.STblk n y) hab hB hLb
  -- `‖G‖² ≤ (N^{τ₀} W^{-D'})²`
  set q : ℝ := ((sz.size n : ℕ) : ℝ) ^ (τ₀ / 2) with hq
  have hq0 : 0 ≤ q := Real.rpow_nonneg hN0.le _
  have hqq : q * q = ((sz.size n : ℕ) : ℝ) ^ τ₀ := by
    rw [hq, ← Real.rpow_add hN0]; congr 1; ring
  have hV : ((sz.W n : ℕ) : ℝ) ^ (-(2 * D')) = (((sz.W n : ℕ) : ℝ) ^ (-D')) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hWpos.le]
    congr 1; push_cast; ring
  have hV0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-(2 * D')) := Real.rpow_nonneg hWpos.le _
  have hsq : ‖sz.Gt n (STflowE z n) (τ n) true ω x y‖ ^ 2 ≤
      (((sz.size n : ℕ) : ℝ) ^ τ₀ * ((sz.W n : ℕ) : ℝ) ^ (-D')) ^ 2 := by
    calc ‖sz.Gt n (STflowE z n) (τ n) true ω x y‖ ^ 2
        ≤ q * (2 * 9 ^ d * (3 * q * ((sz.W n : ℕ) : ℝ) ^ (-(2 * D')))) :=
          hgex.trans (mul_le_mul_of_nonneg_left hrhs hq0)
      _ = (6 * 9 ^ d) * (q * q) * ((sz.W n : ℕ) : ℝ) ^ (-(2 * D')) := by ring
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ₀ * (q * q) * ((sz.W n : ℕ) : ℝ) ^ (-(2 * D')) := by
          gcongr
      _ = (((sz.size n : ℕ) : ℝ) ^ τ₀ * ((sz.W n : ℕ) : ℝ) ^ (-D')) ^ 2 := by
          rw [hqq, hV]; ring
  have hle := (pow_le_pow_iff_left₀ (n := 2) (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
  linarith


/-- **The log-scale far-entry decay of the resolvent** (target 2 of T2141; paper `3_5:2245` via
[DYYY25]; RBM2D `farEntryDecayPT`, `FarEntry:632`).  Under `3 ≤ d`, the flow `STFlow sz κ ε 𝔠 𝔡 z`
(`0 < κ`, `0 < ε`: the constants of `STGbEXPij`), times `0 ≤ s ≤ τ ≤ t ≤ t₀(z)` and the Step 2
conclusions on `[s,t]` (`STStep2Concl`: only `STLocalEntryU` and `STGdecayW` are used; `STAvgU` is
not), the pin `STFarEntryAtLog` holds at the energy `E(z)` and the time `τ`.  `(GijGEX)` is the proved
`STGbEXPij` (`stGbEXPij_of_v3 (gbEXPV3 hd)`).  `s < t` is not needed. -/
theorem stFarEntryAtLog (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}
    (hκ : 0 < κ) (hε : 0 < ε) (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t τ : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (ht : ∀ n, t n ≤ lemT (z n))
    (hsτ : ∀ n, s n ≤ τ n) (hτt : ∀ n, τ n ≤ t n) {Cd : ℝ}
    (hStep2 : STStep2Concl sz (STflowE z) s t Cd) :
    STFarEntryAtLog sz (STflowE z) τ := by
  intro c hc D' hD'
  have hcore := farEntry_core hd sz hκ hε hflow hs ht hsτ hτt hStep2 hc hD'
  have hpre := StochDomAt.precomp_param hcore
    (fun n (p : Bool × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) =>
      if p.1 then p.2 else (p.2.2, p.2.1))
  refine RBM.Ind.PerTimeCalc.Unif.perTimeCalc_of_imp hpre
    (fun τ₀ hτ₀ => ⟨τ₀, hτ₀, Eventually.of_forall fun n p ω h => ?_⟩)
  obtain ⟨σ, x, y⟩ := p
  cases σ
  · have e1 := farEntry_norm_Gt_false sz n (STflowE z n) (τ n) ω x y
    have e2 : zdistInf d (sz.L n) (sz.STblk n y - sz.STblk n x) =
        zdistInf d (sz.L n) (sz.STblk n x - sz.STblk n y) := farEntry_zdistInf_comm _ _
    simp only [Bool.false_eq_true, ↓reduceIte, e2, ← e1] at h ⊢
    exact h
  · simpa using h

/-- **The far set of `STFarEntryAtLog` is nonempty at the size index `n`**: there are fine lattice
points `x, y` with `c (log W)³ ℓ_τ ≤ |[x] - [y]|_∞` (so the indicator of the pin is `1` there). -/
def farEntry_FarNonempty (sz : Sizes d) (τ : ℕ → ℝ) (c : ℝ) (n : ℕ) : Prop :=
  ∃ x y : Idx d (sz.L n) (sz.W n),
    c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (τ n) ≤
      ((zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) : ℕ) : ℝ)

/-- Every pair of blocks `(a, b)` is the pair of blocks of two fine lattice points (`splitEquiv`). -/
theorem farEntry_farNonempty_of (sz : Sizes d) (τ : ℕ → ℝ) (c : ℝ) (n : ℕ)
    (a b : Zd d (sz.L n))
    (h : c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (τ n) ≤
      ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ)) :
    farEntry_FarNonempty sz τ c n := by
  have hpos : 0 < (sz.W n) ^ d := pow_pos (sz.W_pos n) d
  have h1 : ∀ v : Vtx d (sz.L n) (sz.W n),
      STblk sz n ((splitEquiv d (sz.L n) (sz.W n)).symm v) = v.1 := by
    intro v
    have h2 : split d (sz.L n) (sz.W n) ((splitEquiv d (sz.L n) (sz.W n)).symm v) = v :=
      (splitEquiv d (sz.L n) (sz.W n)).apply_symm_apply v
    unfold STblk
    rw [h2]
  refine ⟨(splitEquiv d (sz.L n) (sz.W n)).symm (a, ⟨0, hpos⟩),
    (splitEquiv d (sz.L n) (sz.W n)).symm (b, ⟨0, hpos⟩), ?_⟩
  rw [h1, h1]
  exact h

end Pin

end RBM.Gauss.Sizes

/-! ## 5. The compiled nonempty instance

At `d = 3` on the merged `RBM.Gauss.Step5Inst.szCL` (`Induction/Step5Pins.lean:640`: `m = n + 24`,
`L_n = 2 m^5`, `W_n = 2^m`, `ilambda = 1`; flow `zCL`, `s ≡ 0`, `1 - t_n = L_n^{-2}`; `L_n ≥ 2`,
`W_n ≥ L_n`, `szCL_tendsto`, `szCL_bandwidth`): the flow `flow_zCL`, `0 ≤ s ≤ t ≤ lemT zCL`
(`lemT_zCL`) are proved, the time is `τ = s ≡ 0` (`ℓ_s = 1`), and only `STStep2Concl` (the Step 2 pins,
another gate) stays a hypothesis.  The far set `{c (log W)³ ℓ_s ≤ |[x]-[y]|_∞}` is nonempty at every `n`
for `c = 1` (`farEntry_szCL_far_nonempty`; `sz0` is not used: its far set is empty until `n ≈ 3·10^5`). -/

namespace RBM.Gauss.Step5Inst

open RBM RBM.Gauss RBM.Gauss.Sizes

/-- **The far set of `STFarEntryAtLog` is nonempty at every `n`** (`c = 1`, `τ = s ≡ 0`): the blocks
`(x_n, 0)` with `|x_n|_∞ = m^5 = L_n/2` (`xCL`, `m = n + 24`) satisfy `1 · (log W_n)³ ℓ_s ≤ m^5`
(`ℓ_s = 1`, `log W_n ≤ m`), so the indicator of the pin is `1` there and the conclusion is not
vacuous. -/
theorem farEntry_szCL_far_nonempty (n : ℕ) : farEntry_FarNonempty szCL sCL 1 n := by
  refine farEntry_farNonempty_of szCL sCL 1 n (xCL n) 0 ?_
  have hlogm := szCL_log_W_le n
  have hlog1 := szCL_one_le_log_W n
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h3 : Real.log ((szCL.W n : ℕ) : ℝ) ^ 3 ≤ ((n : ℝ) + 24) ^ 3 :=
    pow_le_pow_left₀ (by linarith) hlogm 3
  have h35 : ((n : ℝ) + 24) ^ 3 ≤ ((n : ℝ) + 24) ^ 5 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have hz : zdistInf 3 (szCL.L n) (xCL n - 0) = (n + 24) ^ 5 := by
    rw [sub_zero]; exact zdistInf_xCL n
  rw [hz, szCL_ellT_s, mul_one, one_mul]
  push_cast
  linarith

/-- **`stFarEntryAtLog` at `d = 3` on `szCL`**: the flow `flow_zCL` (`κ = ε = 1/10`, `𝔠 = 1/6`,
`𝔡 = 1/10`), `s = τ ≡ 0`, `t_n = 1 - L_n^{-2} ≤ lemT (zCL n)`, `C_d = 1`; every deterministic
hypothesis is discharged, only `STStep2Concl` (the Step 2 pins) is a hypothesis.  The index set of
the conclusion is nonempty and the far set is nonempty at every `n`
(`farEntry_szCL_far_nonempty`). -/
theorem farEntry_szCL_stFarEntryAtLog (hStep2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1) :
    STFarEntryAtLog szCL (STflowE zCL) sCL ∧ ∀ n, farEntry_FarNonempty szCL sCL 1 n :=
  ⟨stFarEntryAtLog (by norm_num) szCL (κ := 1 / 10) (ε := 1 / 10) (by norm_num) (by norm_num)
    flow_zCL (fun _ => le_rfl) lemT_zCL (fun _ => le_rfl) (fun n => (szCL_hst n).le) hStep2,
   farEntry_szCL_far_nonempty⟩

/-- The section lemma `prec_timeIcc_section` applied on `szCL`: `STLocalEntryU` and `STGdecayW` of
`STStep2Concl` on `[s, t] = [0, 1 - L_n^{-2}]` restrict to the time sequence `τ = s ≡ 0`. -/
example (hStep2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1) : True := by
  have _h1 := prec_timeIcc_section szCL (fun _ => le_rfl) (fun n => (szCL_hst n).le) hStep2.1
  have _h3 := prec_timeIcc_section szCL (fun _ => le_rfl) (fun n => (szCL_hst n).le)
    (hStep2.2.2 2 (by norm_num))
  trivial

end RBM.Gauss.Step5Inst

end
