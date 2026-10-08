/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.IniTermII
import RBM3D.Evolution.CltFar
import RBM3D.Induction.B45

/-!
# S5-16 (ST-4): the initial term of Step 5, case (i)

Case (i) is `ilambda²/L² ≤ 1-t ≤ 1-s ≤ ilambda²`.  Paper: arXiv:2507.20274,
`paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`), `(iksjuwjx0)` `3_5:2072`, proof `3_5:2077-2172`.
Proves the pin `STIniTermI` of `Induction/Step5Pins.lean:322`: for every sign `σ`,
`[𝒰^{(2)}_{s,u,σ} ∘ (𝓛-𝒦)^{(2)}_{s,σ}]_a ≺ A^{-1/5} W^{-d}𝒯̃^L_{u,D}(|a₁-a₂|) + W^{-D}`,
`A = ilambda² W^d`, uniformly in `u ∈ [s,t]`.

* §1-§12 (deterministic): lattice kernels and the profile `𝒯` in regime (i)
  (`𝒯_s ≤ c (m+1)^{d-2} e^{√m} 𝒯_u`, new against case (ii)); `(uwp2-92kj)` in regime (i); the cores
  `iniTermI_core_same` (`σ₁ = σ₂`, `prop:ThfadC_short`), `iniTermI_core_lossy` (`ρ`-lossy, two
  applications of `(uwp2-92kj)`), `iniTermI_core_mixed` (`(eq:decompU)`: three of the four terms,
  and `c (1-s)² (Θ𝓑Θ)`); the identity `(1-s)²(Θ𝓑Θ) = f^{near} + f^{far} + g` (§10); `f^{near}` (§11,
  windowed convolutions `iniTermI_W2`); the window complement (§12);
* §13-§15: `stIngR5_hyps_restrict` (the hypotheses of `STIngR5` restrict from `[s,t]` to
  `[s,t']`), the `u`-Lipschitz bound of `f^{far}`, and `stCltFar_uniform` (`lem;CLT` uniformly in
  `u ∈ [s,t]`, from `stCltFar_holds` at the worst grid time);
* §16-§17: bounds on `Θ_u`, `iniTermI_mixed_bound`, `iniTermI_mixed_tail`; §18-§21 comparisons at
  the size index, Ward, the real-level estimate of each case (`iniTermI_rl_all`); §22
  `iniTermI_concl` and the pin `stIniTermI_holds`; §23 compiled nonempty instances (`d = 3`).

Paper-delta candidates (see the report): `T2329a` `𝒯_s(|b₁-b₂|) ≤ c (m+1)^{d-2} e^{√m}
𝒯_u(|a₁-a₂|)` in regime (i) (`ℓ_u < L`; case (ii) had `ℓ_u = L`); `T2329b` `lem;CLT` is used for
every `u ∈ [s,t]` (`3_5:2173` states it at the end time); `T2329c` the factor `(1-s)²` in
`(iksjuwjx)` is `((u-s)/u)² ≤ (1-s)²` in the exact expansion `(eq:decompU)`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ### 1. Lattice sums for the power kernels -/

section Lattice

variable {d L : ℕ} [NeZero L]

/-- `(|x|_1 + 1)^{-(d-2)}`. -/
def iniTermI_PD (d L : ℕ) (x : Zd d L) : ℝ := ((((zdistD d L x : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹

/-- `(|x|_∞ + 1)^{-(d-2)}`. -/
def iniTermI_PI (d L : ℕ) (x : Zd d L) : ℝ := ((((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹

theorem iniTermI_PI_nonneg (x : Zd d L) : 0 ≤ iniTermI_PI d L x := by
  unfold iniTermI_PI; positivity

theorem iniTermI_PI_le_one (x : Zd d L) : iniTermI_PI d L x ≤ 1 := by
  unfold iniTermI_PI
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by have : (0:ℝ) ≤ ((zdistInf d L x : ℕ) : ℝ) := Nat.cast_nonneg _; linarith))

theorem iniTermI_PI_le_PD (hd : 1 ≤ d) (x : Zd d L) :
    iniTermI_PI d L x ≤ (d : ℝ) ^ (d - 2) * iniTermI_PD d L x := by
  unfold iniTermI_PD iniTermI_PI
  have h : ((zdistD d L x : ℕ) : ℝ) ≤ d * ((zdistInf d L x : ℕ) : ℝ) := by
    exact_mod_cast zdistD_le_mul_zdistInf d L x
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h2 : ((zdistD d L x : ℕ) : ℝ) + 1 ≤ d * (((zdistInf d L x : ℕ) : ℝ) + 1) := by
    nlinarith [(Nat.cast_nonneg (zdistInf d L x) : (0:ℝ) ≤ _)]
  have h3 : (((zdistD d L x : ℕ) : ℝ) + 1) ^ (d - 2)
      ≤ (d : ℝ) ^ (d - 2) * (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2 _
  have hpos : (0 : ℝ) < (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2) := by positivity
  have hpos' : (0 : ℝ) < (((zdistD d L x : ℕ) : ℝ) + 1) ^ (d - 2) := by positivity
  rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hpos hpos']
  nlinarith

theorem iniTermI_zdistD_neg (x : Zd d L) : zdistD d L (-x) = zdistD d L x := by
  unfold zdistD
  exact Finset.sum_congr rfl fun i _ => by simp [zdist_neg]

theorem iniTermI_zdistInf_neg (x : Zd d L) : zdistInf d L (-x) = zdistInf d L x := by
  unfold zdistInf
  exact Finset.sup_congr rfl fun i _ => by simp [zdist_neg]

theorem iniTermI_zdistInf_sub_comm (a b : Zd d L) :
    zdistInf d L (a - b) = zdistInf d L (b - a) := by
  rw [← neg_sub, iniTermI_zdistInf_neg]

theorem iniTermI_zdistD_sub_comm (a b : Zd d L) :
    zdistD d L (a - b) = zdistD d L (b - a) := by
  rw [← neg_sub, iniTermI_zdistD_neg]

theorem iniTermI_PD_sub_comm (a b : Zd d L) :
    iniTermI_PD d L (a - b) = iniTermI_PD d L (b - a) := by
  unfold iniTermI_PD; rw [iniTermI_zdistD_sub_comm]

theorem iniTermI_PI_sub_comm (a b : Zd d L) :
    iniTermI_PI d L (a - b) = iniTermI_PI d L (b - a) := by
  unfold iniTermI_PI; rw [iniTermI_zdistInf_sub_comm]

theorem iniTermI_zdistInf_add_le (x y : Zd d L) :
    zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y := by
  unfold zdistInf
  refine Finset.sup_le fun i _ => ?_
  calc zdist L ((x + y) i) = zdist L (x i + y i) := rfl
    _ ≤ zdist L (x i) + zdist L (y i) := zdist_add_le L (x i) (y i)
    _ ≤ _ := Nat.add_le_add
        (Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i))
        (Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i))

theorem iniTermI_zdistInf_le_L (x : Zd d L) : ((zdistInf d L x : ℕ) : ℝ) ≤ L := by
  have : zdistInf d L x ≤ L := Finset.sup_le fun i _ => zdist_le_L (x i)
  exact_mod_cast this

theorem iniTermI_zdistInf_zero : zdistInf d L (0 : Zd d L) = 0 := by
  unfold zdistInf
  exact Nat.eq_zero_of_le_zero (Finset.sup_le fun i _ => by simp)

/-- `|a₁ - a₂| ≤ |a₁ - b₁| + |b₁ - b₂| + |b₂ - a₂|` in `zdistInf`. -/
theorem iniTermI_tri (a₁ a₂ b₁ b₂ : Zd d L) :
    zdistInf d L (a₁ - a₂) ≤ zdistInf d L (b₁ - a₁) + zdistInf d L (b₁ - b₂) + zdistInf d L (b₂ - a₂) := by
  have h1 : a₁ - a₂ = -(b₁ - a₁) + (b₁ - b₂) + (b₂ - a₂) := by abel
  rw [h1]
  calc zdistInf d L (-(b₁ - a₁) + (b₁ - b₂) + (b₂ - a₂))
      ≤ zdistInf d L (-(b₁ - a₁) + (b₁ - b₂)) + zdistInf d L (b₂ - a₂) := iniTermI_zdistInf_add_le _ _
    _ ≤ (zdistInf d L (-(b₁ - a₁)) + zdistInf d L (b₁ - b₂)) + zdistInf d L (b₂ - a₂) :=
        Nat.add_le_add_right (iniTermI_zdistInf_add_le _ _) _
    _ = _ := by rw [iniTermI_zdistInf_neg]


end Lattice

/-! ### 2. The tail function in regime (ii) -/

section Tail

variable {d L : ℕ} {g : ℝ}

theorem iniTermI_tailT_mono (hg : 0 ≤ g) (hL1 : (1 : ℝ) ≤ L) {s u : ℝ} (hsu : s ≤ u)
    (hu : u < 1) {r : ℝ} (hr : 0 ≤ r) : tailT d L g s r ≤ tailT d L g u r := by
  unfold tailT BparamR
  have hv : 0 < 1 - s := by linarith
  have hw : 0 < 1 - u := by linarith
  rw [abs_of_pos hv, abs_of_pos hw]
  have hℓ : ellT L g s ≤ ellT L g u := ellT_mono hg hsu hu
  have hℓu : 0 < ellT L g s := ellT_pos hL1
  have hL0 : (0 : ℝ) < L := by linarith
  have hA : (g ^ 2 + (1 - s))⁻¹ ≤ (g ^ 2 + (1 - u))⁻¹ := inv_anti₀ (by positivity) (by linarith)
  have hZ : ((L : ℝ) ^ d * (1 - s))⁻¹ ≤ ((L : ℝ) ^ d * (1 - u))⁻¹ :=
    inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have hP : 0 ≤ ((r + 1) ^ (d - 2))⁻¹ := by positivity
  have hE : Real.exp (-Real.sqrt (r / ellT L g s)) ≤ Real.exp (-Real.sqrt (r / ellT L g u)) :=
    Real.exp_le_exp.mpr (neg_le_neg (Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hr hℓu hℓ)))
  have hB : (g ^ 2 + (1 - s))⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - s))⁻¹
      ≤ (g ^ 2 + (1 - u))⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - u))⁻¹ :=
    add_le_add (mul_le_mul_of_nonneg_right hA hP) hZ
  have hBt : 0 ≤ (g ^ 2 + (1 - u))⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - u))⁻¹ := by
    have : 0 ≤ ((L : ℝ) ^ d * (1 - u))⁻¹ := by positivity
    have : 0 ≤ (g ^ 2 + (1 - u))⁻¹ * ((r + 1) ^ (d - 2))⁻¹ := by positivity
    linarith
  exact mul_le_mul hB hE (Real.exp_pos _).le hBt

end Tail

/-! ### 2'. The tail function in regime (i): comparison with the power kernel -/

section Tail2

variable {d L : ℕ} [NeZero L] {g : ℝ}

theorem iniTermI_sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : √(x + y) ≤ √x + √y := by
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sqrt_nonneg x, Real.sqrt_nonneg y]

/-- `𝒯_v(|x|) ≤ (1+2^{d-1}) (g²+1-v)⁻¹ (|x|+1)^{-(d-2)} e^{-(|x|/ℓ_v)^{1/2}}` for `g²/L² ≤ 1-v`
(the zero-mode term of `B_{v,r}` is dominated, `zeroMode_le_of_ge`). -/
theorem iniTermI_tailT_le_PI (hd : 3 ≤ d) (hL1 : (1 : ℝ) ≤ L) {v : ℝ} (hv : v < 1)
    (hreg : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - v) (x : Zd d L) :
    tailT d L g v (zdistInf d L x : ℕ) ≤
      (1 + 2 ^ (d - 1)) * ((g ^ 2 + (1 - v))⁻¹ * iniTermI_PI d L x) *
        Real.exp (-Real.sqrt (((zdistInf d L x : ℕ) : ℝ) / ellT L g v)) := by
  have hv0 : 0 < 1 - v := by linarith
  have h2 := zeroMode_le_of_ge (d := d) (L := L) (g := g) (t := v) (by omega) hL1 hv
    (r := ((zdistInf d L x : ℕ) : ℝ)) (Nat.cast_nonneg _) (iniTermI_zdistInf_le_L x) hreg
  rw [abs_of_pos hv0] at h2
  unfold tailT BparamR
  rw [abs_of_pos hv0]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  have hP : iniTermI_PI d L x = ((((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := rfl
  rw [hP]
  have : 0 ≤ (g ^ 2 + (1 - v))⁻¹ * ((((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
  nlinarith

theorem iniTermI_tailT_le_PI' (hd : 3 ≤ d) (hL1 : (1 : ℝ) ≤ L) {v : ℝ} (hv : v < 1)
    (hreg : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - v) (x : Zd d L) :
    tailT d L g v (zdistInf d L x : ℕ) ≤ (1 + 2 ^ (d - 1)) * ((g ^ 2 + (1 - v))⁻¹ * iniTermI_PI d L x) := by
  refine (iniTermI_tailT_le_PI hd hL1 hv hreg x).trans ?_
  have h0 : 0 ≤ (1 + 2 ^ (d - 1)) * ((g ^ 2 + (1 - v))⁻¹ * iniTermI_PI d L x) := by
    have := iniTermI_PI_nonneg (d := d) (L := L) x
    have : 0 < 1 - v := by linarith
    positivity
  calc _ ≤ (1 + 2 ^ (d - 1)) * ((g ^ 2 + (1 - v))⁻¹ * iniTermI_PI d L x) * 1 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by
          have := Real.sqrt_nonneg (((zdistInf d L x : ℕ) : ℝ) / ellT L g v); linarith)) h0
    _ = _ := mul_one _

/-- The first term of `B_{u,r}` is at most `𝒯_u(r) e^{(r/ℓ_u)^{1/2}}`. -/
theorem iniTermI_tailT_ge_PI (_hg : 0 < g) {u : ℝ} (hu : u < 1) (x : Zd d L) :
    (g ^ 2 + (1 - u))⁻¹ * iniTermI_PI d L x * Real.exp (-Real.sqrt (((zdistInf d L x : ℕ) : ℝ) / ellT L g u))
      ≤ tailT d L g u (zdistInf d L x : ℕ) := by
  have hu0 : 0 < 1 - u := by linarith
  unfold tailT BparamR
  rw [abs_of_pos hu0]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  have : 0 ≤ ((L : ℝ) ^ d * (1 - u))⁻¹ := by positivity
  have hP : iniTermI_PI d L x = ((((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := rfl
  rw [hP]; linarith

/-- **The comparison of the profile at `s` with the profile at `u`** (regime (i), `g²/L² ≤ 1-u`):
`𝒯_s(|b₁-b₂|) ≤ (1+2^{d-1}) (m+1)^{d-2} e^{√m} 𝒯_u(|a₁-a₂|)`, `m = |b₁-a₁| + |b₂-a₂|`.  In regime (ii)
(`ℓ_u = L`) the factor `e^{√m}` was not needed (`iniTermII_Ts_le`); here `ℓ_u < L` and the exponential of
`𝒯_u` is shifted by `√m` (paper-delta candidate `T2329a`). -/
theorem iniTermI_Ts_le (hd : 3 ≤ d) {g s u : ℝ} (hg : 0 < g) (hL1 : (1 : ℝ) ≤ L) (hsu : s ≤ u) (hu : u < 1)
    (hreg : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u) (a₁ a₂ b₁ b₂ : Zd d L) :
    tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) ≤
      (1 + 2 ^ (d - 1)) * ((((zdistInf d L (b₁ - a₁) : ℕ) : ℝ) + ((zdistInf d L (b₂ - a₂) : ℕ) : ℝ) + 1) ^ (d - 2)) *
        Real.exp (√(((zdistInf d L (b₁ - a₁) : ℕ) : ℝ) + ((zdistInf d L (b₂ - a₂) : ℕ) : ℝ))) *
        tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) := by
  have hs1 : s < 1 := lt_of_le_of_lt hsu hu
  have hu0 : 0 < 1 - u := by linarith
  have hs0 : 0 < 1 - s := by linarith
  have hregs : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - s := hreg.trans (by linarith)
  set r' : ℝ := ((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) with hr'
  set r : ℝ := ((zdistInf d L (a₁ - a₂) : ℕ) : ℝ) with hr
  set m : ℝ := ((zdistInf d L (b₁ - a₁) : ℕ) : ℝ) + ((zdistInf d L (b₂ - a₂) : ℕ) : ℝ) with hm
  have hr'0 : 0 ≤ r' := Nat.cast_nonneg _
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  have hm0 : 0 ≤ m := by positivity
  have htri : r ≤ m + r' := by
    have := iniTermI_tri a₁ a₂ b₁ b₂
    have h2 : ((zdistInf d L (a₁ - a₂) : ℕ) : ℝ) ≤ ((zdistInf d L (b₁ - a₁) : ℕ) : ℝ) +
        ((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) + ((zdistInf d L (b₂ - a₂) : ℕ) : ℝ) := by exact_mod_cast this
    simp only [hr, hm, hr']; linarith
  have hk : r + 1 ≤ (r' + 1) * (m + 1) := by nlinarith
  have hpow : ((r' + 1) ^ (d - 2))⁻¹ ≤ (m + 1) ^ (d - 2) * ((r + 1) ^ (d - 2))⁻¹ := by
    have h1 : (r + 1) ^ (d - 2) ≤ ((r' + 1) * (m + 1)) ^ (d - 2) := pow_le_pow_left₀ (by positivity) hk _
    rw [mul_pow] at h1
    have hp1 : 0 < (r' + 1) ^ (d - 2) := by positivity
    have hp2 : 0 < (r + 1) ^ (d - 2) := by positivity
    rw [← div_eq_mul_inv, ← one_div, div_le_div_iff₀ hp1 hp2]
    linarith [mul_comm ((r' + 1) ^ (d - 2)) ((m + 1) ^ (d - 2))]
  -- the exponentials
  have hℓ : ellT L g s ≤ ellT L g u := ellT_mono hg.le hsu hu
  have hℓs1 : 1 ≤ ellT L g s := one_le_ellT hL1
  have hℓu1 : 1 ≤ ellT L g u := hℓs1.trans hℓ
  have hex : √(r / ellT L g u) ≤ √(r' / ellT L g s) + √m := by
    have h1 : r / ellT L g u ≤ r' / ellT L g s + m := by
      calc r / ellT L g u ≤ (m + r') / ellT L g u := div_le_div_of_nonneg_right htri (by linarith)
        _ = r' / ellT L g u + m / ellT L g u := by ring
        _ ≤ r' / ellT L g s + m := by
          refine add_le_add ?_ ?_
          · exact div_le_div_of_nonneg_left hr'0 (by linarith) hℓ
          · exact div_le_self hm0 hℓu1
    exact (Real.sqrt_le_sqrt h1).trans (iniTermI_sqrt_add_le (by positivity) hm0)
  have hE : Real.exp (-√(r' / ellT L g s)) ≤ Real.exp (√m) * Real.exp (-√(r / ellT L g u)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hA := iniTermI_tailT_le_PI hd hL1 hs1 hregs (b₁ - b₂)
  have hB := iniTermI_tailT_ge_PI (d := d) (L := L) hg hu (a₁ - a₂)
  have hAu : (g ^ 2 + (1 - s))⁻¹ ≤ (g ^ 2 + (1 - u))⁻¹ := inv_anti₀ (by positivity) (by linarith)
  have hPI1 : iniTermI_PI d L (b₁ - b₂) = ((r' + 1) ^ (d - 2))⁻¹ := rfl
  have hPI2 : iniTermI_PI d L (a₁ - a₂) = ((r + 1) ^ (d - 2))⁻¹ := rfl
  rw [← hr', hPI1] at hA
  rw [← hr, hPI2] at hB
  have hC0 : (0 : ℝ) ≤ 1 + 2 ^ (d - 1) := by positivity
  have hp : 0 ≤ ((r' + 1) ^ (d - 2))⁻¹ := by positivity
  calc tailT d L g s r' ≤ (1 + 2 ^ (d - 1)) * ((g ^ 2 + (1 - s))⁻¹ * ((r' + 1) ^ (d - 2))⁻¹) *
        Real.exp (-√(r' / ellT L g s)) := hA
    _ ≤ (1 + 2 ^ (d - 1)) * ((g ^ 2 + (1 - u))⁻¹ * ((m + 1) ^ (d - 2) * ((r + 1) ^ (d - 2))⁻¹)) *
        (Real.exp (√m) * Real.exp (-√(r / ellT L g u))) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul hAu hpow hp (by positivity)) hC0) hE
          (Real.exp_pos _).le (by positivity)
    _ = (1 + 2 ^ (d - 1)) * (m + 1) ^ (d - 2) * Real.exp (√m) *
        ((g ^ 2 + (1 - u))⁻¹ * ((r + 1) ^ (d - 2))⁻¹ * Real.exp (-√(r / ellT L g u))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hB (by positivity)

end Tail2

/-! ### 3'. `(uwp2-92kj)` without the floor, regime (i) -/

theorem iniTermI_stageA (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g s u : ℝ, 0 < g → g ≤ Λ → 0 ≤ s → s ≤ u → u < 1 →
      g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u → ∀ a₁ a₂ : Zd d L,
        (1 - s) * ∑ b : Zd d L, ‖Theta d L g (u : ℂ) a₁ b‖ * tailT d L g s (zdistInf d L (b - a₂) : ℕ)
          ≤ C * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) := by
  obtain ⟨C, hC, H⟩ := step5Kernel_profile_explicit_holds d Λ hd hΛ
  refine ⟨C, hC, fun L _ hL g s u hg hgΛ hs hsu hu hreg a₁ a₂ => ?_⟩
  have hs1 : 0 ≤ 1 - s := by linarith
  have hu0 : 0 < 1 - u := by linarith
  set ρ : ℝ := (1 - s) / (1 - u) with hρdef
  have hρ : 0 ≤ ρ := div_nonneg hs1 hu0.le
  apply le_of_forall_pos_le_add
  intro ε hε
  set w : ℝ := ε / (1 + ρ) with hwdef
  have hw : 0 < w := div_pos hε (by linarith)
  have h := H L hL g w⁻¹ 1 s u hg hgΛ (inv_pos.mpr hw) hs hsu hu (Or.inl hreg) a₁ a₂
  rw [Real.rpow_neg_one, inv_inv] at h
  have hle : ∀ b : Zd d L, ‖Theta d L g (u : ℂ) a₁ b‖ * tailT d L g s (zdistInf d L (b - a₂) : ℕ)
      ≤ ‖Theta d L g (u : ℂ) a₁ b‖ * tailW d L g s (L : ℝ) w⁻¹ 1 (zdistInf d L (b - a₂) : ℕ) := by
    intro b
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    unfold tailW
    rw [min_eq_left (iniTermI_zdistInf_le_L _)]
    exact le_max_left _ _
  have hρw : ρ * w ≤ ε := by
    rw [hwdef, mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  calc (1 - s) * ∑ b : Zd d L, ‖Theta d L g (u : ℂ) a₁ b‖ * tailT d L g s (zdistInf d L (b - a₂) : ℕ)
      ≤ (1 - s) * ∑ b : Zd d L, ‖Theta d L g (u : ℂ) a₁ b‖ *
          tailW d L g s (L : ℝ) w⁻¹ 1 (zdistInf d L (b - a₂) : ℕ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => hle b) hs1
    _ ≤ C * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) + ρ * w := h
    _ ≤ _ := by linarith

/-! ### 4. The second index: `Z(b₁) = Σ_{b₂} |K(a₂,b₂)| y(b₁,b₂)` -/

section StageZ

variable {d L : ℕ} [NeZero L]

/-- The second-index smoothing (`3_5:2275`, first `≺`, via `(uwp2-92kj)`): with `|K(a,b)| ≤ α 1_{a=b} + β |Θ_{ab}|`,
`α ≤ 1`, `β ≤ 1-s`, `α + β/(1-u) = (1-s)/(1-u)`, and `|X| ≤ M (q 𝒯_s + F)`. -/
theorem iniTermI_ZA (hL : 3 ≤ L) {g s u α β M q F CA : ℝ}
    (hs : 0 ≤ s) (hsu : s ≤ u) (hu : u < 1)
    (hα1 : α ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 - s)
    (hαβ : α + β * (1 - u)⁻¹ = (1 - s) / (1 - u))
    (hM : 0 ≤ M) (hq : 0 ≤ q) (hF : 0 ≤ F) (hCA : 0 ≤ CA) (hg : 0 ≤ g) (hL1 : (1 : ℝ) ≤ L)
    (hA : ∀ a₁ a₂ : Zd d L, (1 - s) * ∑ b : Zd d L, ‖Theta d L g (u : ℂ) a₁ b‖ *
        tailT d L g s (zdistInf d L (b - a₂) : ℕ) ≤ CA * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ))
    (a₂ b₁ : Zd d L) :
    ∑ b₂ : Zd d L, (α * (if a₂ = b₂ then 1 else 0) + β * ‖Theta d L g (u : ℂ) a₂ b₂‖) *
        (M * (q * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) + F))
      ≤ (1 + CA) * M * (q * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ) + (1 - s) / (1 - u) * F) := by
  have hu0 : 0 < 1 - u := by linarith
  have hs1 : 0 ≤ 1 - s := by linarith
  set y : Zd d L → ℝ := fun b₂ => M * (q * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) + F) with hy
  have hTs : ∀ b₂ : Zd d L, 0 ≤ tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) :=
    fun b₂ => tailT_nonneg (Nat.cast_nonneg _)
  have hTu : 0 ≤ tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ) := tailT_nonneg (Nat.cast_nonneg _)
  have h1 : ∀ b₂ : Zd d L, (α * (if a₂ = b₂ then 1 else 0) + β * ‖Theta d L g (u : ℂ) a₂ b₂‖) * y b₂
      = (if a₂ = b₂ then α * y b₂ else 0) + β * (‖Theta d L g (u : ℂ) a₂ b₂‖ * y b₂) := by
    intro b₂; split_ifs <;> ring
  rw [Finset.sum_congr rfl fun b₂ _ => h1 b₂, Finset.sum_add_distrib, Finset.sum_ite_eq, ← Finset.mul_sum]
  simp only [Finset.mem_univ, ite_true]
  -- the identity term
  have hid : α * y a₂ ≤ M * (q * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ) + α * F) := by
    have h := iniTermI_tailT_mono (d := d) hg hL1 hsu hu (r := (zdistInf d L (b₁ - a₂) : ℕ)) (Nat.cast_nonneg _)
    simp only [hy]
    have h2 : α * (M * (q * tailT d L g s (zdistInf d L (b₁ - a₂) : ℕ) + F))
        = M * (α * q * tailT d L g s (zdistInf d L (b₁ - a₂) : ℕ) + α * F) := by ring
    rw [h2]
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) hM
    have hqs : α * q * tailT d L g s (zdistInf d L (b₁ - a₂) : ℕ) ≤ 1 * q * tailT d L g s (zdistInf d L (b₁ - a₂) : ℕ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hα1 hq) (tailT_nonneg (Nat.cast_nonneg _))
    calc α * q * tailT d L g s (zdistInf d L (b₁ - a₂) : ℕ)
        ≤ 1 * q * tailT d L g s (zdistInf d L (b₁ - a₂) : ℕ) := hqs
      _ = q * tailT d L g s (zdistInf d L (b₁ - a₂) : ℕ) := by ring
      _ ≤ q * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ) := mul_le_mul_of_nonneg_left h hq
  -- the propagator term
  have hrow : ∑ b : Zd d L, ‖Theta d L g (u : ℂ) a₂ b‖ ≤ (1 - u)⁻¹ := by
    have := sum_norm_Theta_row_le (g := g) hL (hs.trans hsu) hu (m := (1 : ℂ)) (by simp) a₂
    simpa using this
  have hsplit : ∑ b₂ : Zd d L, ‖Theta d L g (u : ℂ) a₂ b₂‖ * y b₂
      = M * q * (∑ b₂ : Zd d L, ‖Theta d L g (u : ℂ) a₂ b₂‖ * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ))
        + M * F * ∑ b₂ : Zd d L, ‖Theta d L g (u : ℂ) a₂ b₂‖ := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b₂ _ => ?_
    simp only [hy]; ring
  have hprop : β * ∑ b₂ : Zd d L, ‖Theta d L g (u : ℂ) a₂ b₂‖ * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ)
      ≤ CA * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ) := by
    have hsw : ∑ b₂ : Zd d L, ‖Theta d L g (u : ℂ) a₂ b₂‖ * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ)
        = ∑ b₂ : Zd d L, ‖Theta d L g (u : ℂ) a₂ b₂‖ * tailT d L g s (zdistInf d L (b₂ - b₁) : ℕ) :=
      Finset.sum_congr rfl fun b₂ _ => by rw [iniTermI_zdistInf_sub_comm b₁ b₂]
    have hnn : 0 ≤ ∑ b₂ : Zd d L, ‖Theta d L g (u : ℂ) a₂ b₂‖ * tailT d L g s (zdistInf d L (b₂ - b₁) : ℕ) :=
      Finset.sum_nonneg fun b₂ _ => mul_nonneg (norm_nonneg _) (tailT_nonneg (Nat.cast_nonneg _))
    have := hA a₂ b₁
    rw [iniTermI_zdistInf_sub_comm a₂ b₁] at this
    rw [hsw]
    calc β * _ ≤ (1 - s) * ∑ b₂ : Zd d L, ‖Theta d L g (u : ℂ) a₂ b₂‖ *
          tailT d L g s (zdistInf d L (b₂ - b₁) : ℕ) := mul_le_mul_of_nonneg_right hβ1 hnn
      _ ≤ _ := this
  calc α * y a₂ + β * ∑ b₂ : Zd d L, ‖Theta d L g (u : ℂ) a₂ b₂‖ * y b₂
      ≤ M * (q * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ) + α * F)
        + (M * q * (β * ∑ b₂ : Zd d L, ‖Theta d L g (u : ℂ) a₂ b₂‖ * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ))
          + M * F * (β * (1 - u)⁻¹)) := by
        refine add_le_add hid ?_
        rw [hsplit]
        have : β * (M * q * (∑ b₂ : Zd d L, ‖Theta d L g (u : ℂ) a₂ b₂‖ * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ))
            + M * F * ∑ b₂ : Zd d L, ‖Theta d L g (u : ℂ) a₂ b₂‖)
            = M * q * (β * ∑ b₂ : Zd d L, ‖Theta d L g (u : ℂ) a₂ b₂‖ * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ))
              + M * F * (β * ∑ b₂ : Zd d L, ‖Theta d L g (u : ℂ) a₂ b₂‖) := by ring
        rw [this]
        refine add_le_add le_rfl ?_
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrow hβ0) (mul_nonneg hM hF)
    _ ≤ M * (q * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ) + α * F)
        + (M * q * (CA * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ)) + M * F * (β * (1 - u)⁻¹)) := by
        refine add_le_add le_rfl (add_le_add ?_ le_rfl)
        exact mul_le_mul_of_nonneg_left hprop (mul_nonneg hM hq)
    _ = (1 + CA) * M * (q * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ)) + M * F * (α + β * (1 - u)⁻¹) := by ring
    _ ≤ _ := by
        rw [hαβ]
        have hρ : 0 ≤ (1 - s) / (1 - u) := div_nonneg hs1 hu0.le
        have h0 : 0 ≤ CA * M * ((1 - s) / (1 - u) * F) := by positivity
        nlinarith [h0]

end StageZ

section Shift

variable {d L : ℕ} [NeZero L]

theorem iniTermI_sum_shift (a : Zd d L) (f : Zd d L → ℝ) :
    ∑ b : Zd d L, f (b - a) = ∑ x : Zd d L, f x :=
  Fintype.sum_equiv (Equiv.subRight a) _ _ fun _ => rfl

end Shift


/-! ### 7. The kernel `𝒰_{s,u}` on two indices: the representation `K ⊗ K` -/

section Rep

variable {d L : ℕ} [NeZero L]

theorem iniTermI_sum_fin2 (f : (Fin 2 → Zd d L) → ℂ) :
    ∑ b : Fin 2 → Zd d L, f b = ∑ b₁ : Zd d L, ∑ b₂ : Zd d L, f ![b₁, b₂] := by
  have h : ∑ b : Fin 2 → Zd d L, f b = ∑ p : Zd d L × Zd d L, f ![p.1, p.2] :=
    Fintype.sum_equiv (piFinTwoEquiv fun _ : Fin 2 => Zd d L) _ _ (fun b => by
      congr 1; funext i; fin_cases i <;> simp [piFinTwoEquiv])
  rw [h, Fintype.sum_prod_type]

/-- `𝒰_{s,u,σ}` on two indices is `K ⊗ K`, `K = α I + β Θ_{uμ}`, `α = s/u`, `β = (u-s)/u ≤ 1-s`
(`(eq:decompU)`, `3_5:1983`); for `u = 0` (so `s = 0`) `K = I`. -/
theorem iniTermI_Ugen_rep (hL : 3 ≤ L) {g E s u : ℝ} (hE : |E| ≤ 2) {σ : Fin 2 → Bool} {μ : ℂ}
    (hμ : ∀ i, cycProd (fun i => mSigma E (σ i)) i = μ) (hs : 0 ≤ s) (hsu : s ≤ u) (hu : u < 1) :
    ∃ α β : ℝ, 0 ≤ α ∧ α ≤ 1 ∧ 0 ≤ β ∧ β ≤ 1 - s ∧ α + β * (1 - u)⁻¹ = (1 - s) / (1 - u) ∧
      ∀ (X : (Fin 2 → Zd d L) → ℂ) (a : Fin 2 → Zd d L),
        RBM.Ind.Ugen d L g E σ s u X a =
          ∑ b₁ : Zd d L, ∑ b₂ : Zd d L,
            ((if a 0 = b₁ then (α : ℂ) else 0) + (β : ℂ) * Theta d L g ((u : ℂ) * μ) (a 0) b₁) *
              ((if a 1 = b₂ then (α : ℂ) else 0) + (β : ℂ) * Theta d L g ((u : ℂ) * μ) (a 1) b₂) *
                X ![b₁, b₂] := by
  have hu0' : 0 < 1 - u := by linarith
  rcases eq_or_lt_of_le (hs.trans hsu) with hu0 | hupos
  · -- `u = 0`, hence `s = 0`: `𝒰 = id`
    have hs0 : s = 0 := le_antisymm (hu0 ▸ hsu) hs
    refine ⟨1, 0, zero_le_one, le_rfl, le_rfl, by linarith, ?_, ?_⟩
    · rw [← hu0, hs0]; simp
    · intro X a
      have hself := RBM.Ind.GridDuhamelN_Ugen_self (d := d) (L := L) (g := g) hL hE σ (le_refl (0 : ℝ)) (by norm_num : (0 : ℝ) < 1) X
      rw [← hu0, hs0, hself]
      simp only [Complex.ofReal_one, Complex.ofReal_zero, zero_mul, add_zero]
      rw [Finset.sum_eq_single (a 0)]
      · rw [Finset.sum_eq_single (a 1)]
        · simp only [ite_true, one_mul]
          congr 1; funext i; fin_cases i <;> simp
        · intro b _ hb; simp [Ne.symm hb]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro b _ hb; simp [Ne.symm hb]
      · intro h; exact absurd (Finset.mem_univ _) h
  · have hu0 : 0 < u := hupos
    refine ⟨s / u, (u - s) / u, div_nonneg hs hu0.le, ?_, div_nonneg (by linarith) hu0.le, ?_, ?_, ?_⟩
    · rw [div_le_one hu0]; exact hsu
    · rw [div_le_iff₀ hu0]; nlinarith
    · field_simp; ring
    · intro X a
      have hdec := step5Kernel_UN_decompU (d := d) (L := L) (g := g) hL (n := 2) (m := fun i => mSigma E (σ i))
        (fun i => norm_mSigma hE (σ i)) (s := s) hu0 hu X a
      change UN d L g (fun i => mSigma E (σ i)) s u X a = _
      rw [hdec, iniTermI_sum_fin2]
      refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => ?_
      have hent : ∀ a' b' : Zd d L,
          ((((s / u : ℝ) : ℂ) • (1 : Matrix (Zd d L) (Zd d L) ℂ)
            + (((u - s) / u : ℝ) : ℂ) • Theta d L g ((u : ℂ) * μ)) a' b')
            = (if a' = b' then (((s / u : ℝ)) : ℂ) else 0) + (((u - s) / u : ℝ) : ℂ) * Theta d L g ((u : ℂ) * μ) a' b' := by
        intro a' b'
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
        split_ifs <;> simp
      rw [Fin.prod_univ_two]
      simp only [hμ, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hent (a 0) b₁, hent (a 1) b₂]

end Rep

/-! ### 8. The deterministic core, `σ₁ ≠ σ₂` -/

section Core

variable {d L : ℕ} [NeZero L]

theorem iniTermI_cyc_mixed {E : ℝ} (hE : |E| ≤ 2) {σ : Fin 2 → Bool} (h : σ 0 ≠ σ 1) (i : Fin 2) :
    cycProd (fun i => mSigma E (σ i)) i = 1 := by
  have hm := norm_mE hE
  have h1 : mSigma E true * mSigma E false = 1 := by
    simp only [mSigma, ite_true, Bool.false_eq_true, ite_false]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hm]; simp
  have h2 : mSigma E false * mSigma E true = 1 := by rw [mul_comm]; exact h1
  have hf0 : finRotate 2 0 = 1 := by decide
  have hf1 : finRotate 2 1 = 0 := by decide
  fin_cases i
  · simp only [cycProd, Fin.zero_eta, hf0]
    cases h0 : σ 0 <;> cases h1' : σ 1 <;> simp_all
  · simp only [cycProd, Fin.mk_one, hf1]
    cases h0 : σ 0 <;> cases h1' : σ 1 <;> simp_all

theorem iniTermI_Theta_shift (hL : 3 ≤ L) {g : ℝ} {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a b : Zd d L) :
    Theta d L g ξ a b = Theta d L g ξ 0 (b - a) := by
  have := Theta_apply_add_right_of_three_le (d := d) (g := g) hL hξ 0 (b - a) a
  rwa [zero_add, sub_add_cancel] at this

end Core

/-! ### 5'. Ball sums of the power kernel in `|·|_∞` -/

section Ball

variable {d L : ℕ} [NeZero L]

/-- The constant of the ball sum. -/
def iniTermI_CB (d : ℕ) : ℝ := (d : ℝ) ^ (d - 2) * (ballC (d - 2) * ((d : ℝ)) ^ 2)

theorem iniTermI_CB_nonneg (d : ℕ) : 0 ≤ iniTermI_CB d := by
  unfold iniTermI_CB; have := ballC_nonneg (d - 2); positivity

/-- `Σ_{|x-c|_∞ ≤ R} (|x-c|_∞+1)^{-(d-2)} ≤ C_B R²` (`sum_ball_pow_le`, `|·|_∞ ≤ |·|_1 ≤ d|·|_∞`). -/
theorem iniTermI_ball_PI (hd : 3 ≤ d) {R : ℝ} (hR : 1 ≤ R) (c : Zd d L) (D : Finset (Zd d L))
    (hD : ∀ x ∈ D, ((zdistInf d L (x - c) : ℕ) : ℝ) ≤ R) :
    ∑ x ∈ D, iniTermI_PI d L (x - c) ≤ iniTermI_CB d * R ^ 2 := by
  obtain ⟨k, hk⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  subst hk
  have hd1 : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 2)
  have hdR : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) * R := by nlinarith
  have h := sum_ball_pow_le (L := L) k hdR D c (fun α hα => by
    have h1 : ((zdistD (k + 2) L (c - α) : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) * ((zdistInf (k + 2) L (c - α) : ℕ) : ℝ) := by
      exact_mod_cast zdistD_le_mul_zdistInf (k + 2) L (c - α)
    rw [iniTermI_zdistInf_sub_comm] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (hD α hα) (by positivity)))
  calc ∑ x ∈ D, iniTermI_PI (k + 2) L (x - c)
      ≤ ∑ x ∈ D, ((k + 2 : ℕ) : ℝ) ^ (k + 2 - 2) * iniTermI_PD (k + 2) L (c - x) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [iniTermI_PD_sub_comm]
        exact iniTermI_PI_le_PD (by omega) _
    _ = ((k + 2 : ℕ) : ℝ) ^ (k + 2 - 2) * ∑ x ∈ D, ((((zdistD (k + 2) L (c - x) : ℕ) : ℝ) + 1) ^ k)⁻¹ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [iniTermI_PD, show k + 2 - 2 = k by omega]
    _ ≤ ((k + 2 : ℕ) : ℝ) ^ (k + 2 - 2) * (ballC k * ((((k + 2 : ℕ) : ℝ)) * R) ^ 2) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = iniTermI_CB (k + 2) * R ^ 2 := by
        simp only [iniTermI_CB, show k + 2 - 2 = k by omega]; ring

/-- **The windowed convolution**: `Σ_{|x-a|_∞ ≤ R} P(a-x) P(x-c) ≤ C R² P(a-c)`, `P = (|·|_∞+1)^{-(d-2)}`. -/
theorem iniTermI_W2 (hd : 3 ≤ d) {R : ℝ} (hR : 1 ≤ R) (a c : Zd d L) (D : Finset (Zd d L))
    (hD : ∀ x ∈ D, ((zdistInf d L (x - a) : ℕ) : ℝ) ≤ R) :
    ∑ x ∈ D, iniTermI_PI d L (a - x) * iniTermI_PI d L (x - c)
      ≤ 2 ^ (d - 2) * (2 * (iniTermI_CB d * R ^ 2)) * iniTermI_PI d L (a - c) := by
  classical
  set k := d - 2 with hk
  have hP : ∀ x y : Zd d L, iniTermI_PI d L x = ((((zdistInf d L x : ℕ) : ℝ) + 1) ^ k)⁻¹ := fun _ _ => rfl
  -- `|a-c| ≤ 2|x-c|` gives `P(x-c) ≤ 2^k P(a-c)`; same for the other pairs
  have hmono : ∀ x y : Zd d L, ((zdistInf d L x : ℕ) : ℝ) ≤ 2 * ((zdistInf d L y : ℕ) : ℝ) →
      iniTermI_PI d L y ≤ 2 ^ k * iniTermI_PI d L x := by
    intro x y h
    rw [hP x x, hP y y]
    have h1 : (((zdistInf d L x : ℕ) : ℝ) + 1) ^ k ≤ (2 * (((zdistInf d L y : ℕ) : ℝ) + 1)) ^ k :=
      pow_le_pow_left₀ (by positivity) (by nlinarith [(Nat.cast_nonneg (zdistInf d L y) : (0:ℝ) ≤ _)]) _
    rw [mul_pow] at h1
    have hp1 : 0 < (((zdistInf d L x : ℕ) : ℝ) + 1) ^ k := by positivity
    have hp2 : 0 < (((zdistInf d L y : ℕ) : ℝ) + 1) ^ k := by positivity
    rw [← one_div, ← one_div, mul_one_div, div_le_div_iff₀ hp2 hp1]
    linarith
  have hpt : ∀ x ∈ D, iniTermI_PI d L (a - x) * iniTermI_PI d L (x - c) ≤
      2 ^ k * iniTermI_PI d L (a - c) * (iniTermI_PI d L (x - a) +
        (if ((zdistInf d L (x - c) : ℕ) : ℝ) ≤ R then iniTermI_PI d L (x - c) else 0)) := by
    intro x hx
    have h1 := hD x hx
    have htri : ((zdistInf d L (a - c) : ℕ) : ℝ) ≤ ((zdistInf d L (x - a) : ℕ) : ℝ) + ((zdistInf d L (x - c) : ℕ) : ℝ) := by
      have : a - c = -(x - a) + (x - c) := by abel
      have h2 : zdistInf d L (a - c) ≤ zdistInf d L (x - a) + zdistInf d L (x - c) := by
        rw [this]
        exact (iniTermI_zdistInf_add_le _ _).trans (by rw [iniTermI_zdistInf_neg])
      exact_mod_cast h2
    have hPa : iniTermI_PI d L (a - x) = iniTermI_PI d L (x - a) := iniTermI_PI_sub_comm a x
    have hn1 := iniTermI_PI_nonneg (d := d) (L := L) (a - x)
    have hn2 := iniTermI_PI_nonneg (d := d) (L := L) (x - c)
    have hn3 := iniTermI_PI_nonneg (d := d) (L := L) (a - c)
    have hn4 := iniTermI_PI_nonneg (d := d) (L := L) (x - a)
    by_cases hc : ((zdistInf d L (a - c) : ℕ) : ℝ) ≤ 2 * ((zdistInf d L (x - c) : ℕ) : ℝ)
    · have := hmono _ _ hc
      calc iniTermI_PI d L (a - x) * iniTermI_PI d L (x - c)
          ≤ iniTermI_PI d L (a - x) * (2 ^ k * iniTermI_PI d L (a - c)) :=
            mul_le_mul_of_nonneg_left this hn1
        _ = 2 ^ k * iniTermI_PI d L (a - c) * iniTermI_PI d L (x - a) := by rw [hPa]; ring
        _ ≤ _ := by
            have : 0 ≤ (if ((zdistInf d L (x - c) : ℕ) : ℝ) ≤ R then iniTermI_PI d L (x - c) else 0) := by
              split_ifs <;> linarith
            have h0 : 0 ≤ 2 ^ k * iniTermI_PI d L (a - c) := mul_nonneg (by positivity) hn3
            nlinarith [mul_nonneg h0 this]
    · push Not at hc
      have hax : ((zdistInf d L (a - c) : ℕ) : ℝ) ≤ 2 * ((zdistInf d L (x - a) : ℕ) : ℝ) := by linarith
      have hxc : ((zdistInf d L (x - c) : ℕ) : ℝ) ≤ R := by linarith
      have := hmono _ _ hax
      rw [hPa]
      simp only [hxc, ite_true]
      calc iniTermI_PI d L (x - a) * iniTermI_PI d L (x - c)
          ≤ (2 ^ k * iniTermI_PI d L (a - c)) * iniTermI_PI d L (x - c) :=
            mul_le_mul_of_nonneg_right this hn2
        _ ≤ _ := by
            have h0 : 0 ≤ 2 ^ k * iniTermI_PI d L (a - c) := mul_nonneg (by positivity) hn3
            nlinarith [mul_nonneg h0 hn4]
  have hn3 := iniTermI_PI_nonneg (d := d) (L := L) (a - c)
  calc ∑ x ∈ D, iniTermI_PI d L (a - x) * iniTermI_PI d L (x - c)
      ≤ ∑ x ∈ D, 2 ^ k * iniTermI_PI d L (a - c) * (iniTermI_PI d L (x - a) +
        (if ((zdistInf d L (x - c) : ℕ) : ℝ) ≤ R then iniTermI_PI d L (x - c) else 0)) :=
        Finset.sum_le_sum hpt
    _ = 2 ^ k * iniTermI_PI d L (a - c) * (∑ x ∈ D, iniTermI_PI d L (x - a) +
        ∑ x ∈ D, (if ((zdistInf d L (x - c) : ℕ) : ℝ) ≤ R then iniTermI_PI d L (x - c) else 0)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 2 ^ k * iniTermI_PI d L (a - c) * (iniTermI_CB d * R ^ 2 + iniTermI_CB d * R ^ 2) := by
        refine mul_le_mul_of_nonneg_left (add_le_add (iniTermI_ball_PI hd hR a D hD) ?_) (mul_nonneg (by positivity) hn3)
        calc ∑ x ∈ D, (if ((zdistInf d L (x - c) : ℕ) : ℝ) ≤ R then iniTermI_PI d L (x - c) else 0)
            ≤ ∑ x ∈ (Finset.univ : Finset (Zd d L)), (if ((zdistInf d L (x - c) : ℕ) : ℝ) ≤ R then
                iniTermI_PI d L (x - c) else 0) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ D) fun x _ _ => by
                split_ifs
                · exact iniTermI_PI_nonneg _
                · exact le_rfl
          _ = ∑ x ∈ Finset.univ.filter (fun x : Zd d L => ((zdistInf d L (x - c) : ℕ) : ℝ) ≤ R),
                iniTermI_PI d L (x - c) := by rw [Finset.sum_filter]
          _ ≤ _ := iniTermI_ball_PI hd hR c _ (fun x hx => (Finset.mem_filter.1 hx).2)
    _ = _ := by ring

end Ball

/-! ### 6'. The one-index kernel and the short-range bilinear estimate (`σ₁ = σ₂`) -/

section Bil

variable {d L : ℕ} [NeZero L]


/-- The one-index kernel `K = α 1 + β Θ_u` of `(eq:decompU)`, as a function. -/
def iniTermI_Kf (d L : ℕ) [NeZero L] (g u α β : ℝ) (a b : Zd d L) : ℂ :=
  (if a = b then (α : ℂ) else 0) + (β : ℂ) * Theta d L g (u : ℂ) a b

theorem iniTermI_Kf_norm_le {g u α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (a b : Zd d L) :
    ‖iniTermI_Kf d L g u α β a b‖ ≤ α * (if a = b then 1 else 0) + β * ‖Theta d L g (u : ℂ) a b‖ := by
  unfold iniTermI_Kf
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · split_ifs
    · simp [Real.norm_of_nonneg hα]
    · simp
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ]

end Bil

section CoreSame2

variable {d L : ℕ} [NeZero L]

theorem iniTermI_poly_exp_le {c : ℝ} (hc : 0 < c) (k : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (r + 1) ^ k * Real.exp (-(c * r)) ≤
      (Nat.factorial k : ℝ) / (c / 2) ^ k * Real.exp (c / 2) * Real.exp (-((c / 2) * r)) := by
  have h := pow_mul_exp_neg_le (c := c / 2) (by positivity) k (r := r + 1) (by linarith)
  have e : Real.exp (-(c * r)) =
      Real.exp (-((c / 2) * (r + 1))) * Real.exp (c / 2) * Real.exp (-((c / 2) * r)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [e]
  calc (r + 1) ^ k * (Real.exp (-((c / 2) * (r + 1))) * Real.exp (c / 2) * Real.exp (-((c / 2) * r)))
      = ((r + 1) ^ k * Real.exp (-((c / 2) * (r + 1)))) *
          (Real.exp (c / 2) * Real.exp (-((c / 2) * r))) := by ring
    _ ≤ ((Nat.factorial k : ℝ) / (c / 2) ^ k) * (Real.exp (c / 2) * Real.exp (-((c / 2) * r))) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := by ring

/-- `Σ_x (|x|_∞+1)^{d-2} e^{-c|x|_1} ≤ C(c, d)`, uniformly in `L`. -/
theorem iniTermI_sum_poly_exp (hd : 3 ≤ d) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L],
      ∑ x : Zd d L, (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2) * Real.exp (-(c * ((zdistD d L x : ℕ) : ℝ))) ≤ C := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  refine ⟨(Nat.factorial k : ℝ) / (c / 2) ^ k * Real.exp (c / 2) * expC k (c / 2), ?_, ?_⟩
  · unfold expC; positivity
  · intro L _
    simp only [show k + 2 - 2 = k by omega]
    calc ∑ x : Zd (k + 2) L, (((zdistInf (k + 2) L x : ℕ) : ℝ) + 1) ^ k * Real.exp (-(c * ((zdistD (k + 2) L x : ℕ) : ℝ)))
        ≤ ∑ x : Zd (k + 2) L, (Nat.factorial k : ℝ) / (c / 2) ^ k * Real.exp (c / 2) *
            Real.exp (-((c / 2) * ((zdistD (k + 2) L x : ℕ) : ℝ))) := by
          refine Finset.sum_le_sum fun x _ => ?_
          have h1 : (((zdistInf (k + 2) L x : ℕ) : ℝ) + 1) ^ k ≤ (((zdistD (k + 2) L x : ℕ) : ℝ) + 1) ^ k := by
            have : ((zdistInf (k + 2) L x : ℕ) : ℝ) ≤ ((zdistD (k + 2) L x : ℕ) : ℝ) := by
              exact_mod_cast zdistInf_le_zdistD (k + 2) L x
            exact pow_le_pow_left₀ (by positivity) (by linarith) _
          calc _ ≤ (((zdistD (k + 2) L x : ℕ) : ℝ) + 1) ^ k * Real.exp (-(c * ((zdistD (k + 2) L x : ℕ) : ℝ))) :=
                mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
            _ ≤ _ := iniTermI_poly_exp_le hc k (Nat.cast_nonneg _)
      _ = (Nat.factorial k : ℝ) / (c / 2) ^ k * Real.exp (c / 2) *
            ∑ x : Zd (k + 2) L, Real.exp (-((c / 2) * ((zdistD (k + 2) L x : ℕ) : ℝ))) := by
          rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_radial_exp_decay_le (L := L) k (by positivity : 0 < c / 2)) (by positivity)

end CoreSame2

section CoreSame3

variable {d L : ℕ} [NeZero L]

/-- `Σ_x (|x|_∞+1)^{d-2} e^{(|x|_∞)^{1/2}} e^{-c|x|_1} ≤ C(c, d)`, uniformly in `L`. -/
theorem iniTermI_sum_poly_exp_sqrt (hd : 3 ≤ d) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L],
      ∑ x : Zd d L, ((((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2) * Real.exp (√((zdistInf d L x : ℕ) : ℝ))) *
        Real.exp (-(c * ((zdistD d L x : ℕ) : ℝ))) ≤ C := by
  obtain ⟨C₁, hC₁, H⟩ := iniTermI_sum_poly_exp (d := d) hd (c := c / 2) (by positivity)
  refine ⟨Real.exp (1 / (2 * c)) * C₁, by positivity, fun L _ => ?_⟩
  calc ∑ x : Zd d L, ((((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2) * Real.exp (√((zdistInf d L x : ℕ) : ℝ))) *
        Real.exp (-(c * ((zdistD d L x : ℕ) : ℝ)))
      ≤ ∑ x : Zd d L, Real.exp (1 / (2 * c)) * ((((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2) *
          Real.exp (-((c / 2) * ((zdistD d L x : ℕ) : ℝ)))) := by
        refine Finset.sum_le_sum fun x _ => ?_
        have hy : ((zdistInf d L x : ℕ) : ℝ) ≤ ((zdistD d L x : ℕ) : ℝ) := by
          exact_mod_cast zdistInf_le_zdistD d L x
        have hy0 : (0 : ℝ) ≤ ((zdistInf d L x : ℕ) : ℝ) := Nat.cast_nonneg _
        have ht := Real.sq_sqrt hy0
        have hsq : √((zdistInf d L x : ℕ) : ℝ) ≤ (c / 2) * ((zdistD d L x : ℕ) : ℝ) + 1 / (2 * c) := by
          set t := √((zdistInf d L x : ℕ) : ℝ)
          have h1 : t ≤ (c / 2) * t ^ 2 + 1 / (2 * c) := by
            have h2 : (c / 2) * t ^ 2 + 1 / (2 * c) - t = (c * t - 1) ^ 2 / (2 * c) := by field_simp; ring
            have : 0 ≤ (c * t - 1) ^ 2 / (2 * c) := by positivity
            linarith
          rw [ht] at h1
          nlinarith
        have he : Real.exp (√((zdistInf d L x : ℕ) : ℝ)) * Real.exp (-(c * ((zdistD d L x : ℕ) : ℝ))) ≤
            Real.exp (1 / (2 * c)) * Real.exp (-((c / 2) * ((zdistD d L x : ℕ) : ℝ))) := by
          rw [← Real.exp_add, ← Real.exp_add]
          exact Real.exp_le_exp.mpr (by nlinarith)
        have hp : 0 ≤ (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2) := by positivity
        calc _ = (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2) *
              (Real.exp (√((zdistInf d L x : ℕ) : ℝ)) * Real.exp (-(c * ((zdistD d L x : ℕ) : ℝ)))) := by ring
          _ ≤ (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2) *
              (Real.exp (1 / (2 * c)) * Real.exp (-((c / 2) * ((zdistD d L x : ℕ) : ℝ)))) :=
              mul_le_mul_of_nonneg_left he hp
          _ = _ := by ring
    _ = Real.exp (1 / (2 * c)) * ∑ x : Zd d L, (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2) *
          Real.exp (-((c / 2) * ((zdistD d L x : ℕ) : ℝ))) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (H L) (Real.exp_pos _).le

/-- The short-range bilinear estimate: `|Θ'_{ab}| ≤ C_s (1_{a=b} + g² e^{-c₀|b-a|})` (`(prop:ThfadC_short)`). -/
theorem iniTermI_bil_same (d : ℕ) (hd : 3 ≤ d) (Cs c₀ Λ : ℝ) (hCs : 0 ≤ Cs) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g s u α β M q F : ℝ, 0 < g → g ≤ Λ → s ≤ u → u < 1 →
      g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u → 0 ≤ α → α ≤ 1 → 0 ≤ β → β ≤ 1 → 0 ≤ M → 0 ≤ q → 0 ≤ F →
      ∀ Θ' : Zd d L → Zd d L → ℂ,
        (∀ a b : Zd d L, ‖Θ' a b‖ ≤ Cs * ((if a = b then 1 else 0) +
          g ^ 2 * Real.exp (-(c₀ * ((zdistD d L (b - a) : ℕ) : ℝ))))) →
        ∀ (a₁ a₂ : Zd d L) (X : Zd d L → Zd d L → ℂ),
          (∀ b₁ b₂, ‖X b₁ b₂‖ ≤ M * (q * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) + F)) →
          ‖∑ b₁ : Zd d L, ∑ b₂ : Zd d L,
              ((if a₁ = b₁ then (α : ℂ) else 0) + (β : ℂ) * Θ' a₁ b₁) *
                ((if a₂ = b₂ then (α : ℂ) else 0) + (β : ℂ) * Θ' a₂ b₂) * X b₁ b₂‖
            ≤ C * M * (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) + F) := by
  obtain ⟨Cp, hCp, hpoly⟩ := iniTermI_sum_poly_exp_sqrt (d := d) hd hc₀
  set S : ℝ := (1 + Cs) + Cs * Λ ^ 2 * Cp with hS
  have hS0 : 0 ≤ S := by positivity
  set c₀' : ℝ := 1 + 2 ^ (d - 1) with hc₀'
  refine ⟨c₀' * S ^ 2 + S ^ 2 + 1, by positivity, ?_⟩
  intro L _ hL g s u α β M q F hg hgΛ hsu hu hreg hα0 hα1 hβ0 hβ1 hM hq hF Θ' hΘ a₁ a₂ X hX
  have hL1 : (1 : ℝ) ≤ L := by
    have : (3 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hg2 : g ^ 2 ≤ Λ ^ 2 := by nlinarith
  set kk : Zd d L → ℝ := fun x => (1 + Cs) * (if x = 0 then 1 else 0) +
    Cs * Λ ^ 2 * Real.exp (-(c₀ * ((zdistD d L x : ℕ) : ℝ))) with hkk
  have hkk0 : ∀ x, 0 ≤ kk x := fun x => by simp only [hkk]; positivity
  have hG : ∀ a b : Zd d L, ‖(if a = b then (α : ℂ) else 0) + (β : ℂ) * Θ' a b‖ ≤ kk (b - a) := by
    intro a b
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(if a = b then (α : ℂ) else 0)‖ ≤ if a = b then 1 else 0 := by
      split_ifs
      · simp [Real.norm_of_nonneg hα0, hα1]
      · simp
    have h2 : ‖(β : ℂ) * Θ' a b‖ ≤ Cs * ((if a = b then 1 else 0) +
        g ^ 2 * Real.exp (-(c₀ * ((zdistD d L (b - a) : ℕ) : ℝ)))) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ0]
      calc β * ‖Θ' a b‖ ≤ 1 * ‖Θ' a b‖ := mul_le_mul_of_nonneg_right hβ1 (norm_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact hΘ a b
    have hex : Real.exp (-(c₀ * ((zdistD d L (b - a) : ℕ) : ℝ))) ≥ 0 := (Real.exp_pos _).le
    have hba : (if a = b then (1 : ℝ) else 0) = if b - a = 0 then 1 else 0 := by
      by_cases h : a = b
      · simp [h]
      · have : b - a ≠ 0 := fun h' => h (sub_eq_zero.mp h').symm
        simp [h, this]
    simp only [hkk]
    rw [← hba]
    have h3 : Cs * g ^ 2 * Real.exp (-(c₀ * ((zdistD d L (b - a) : ℕ) : ℝ))) ≤
        Cs * Λ ^ 2 * Real.exp (-(c₀ * ((zdistD d L (b - a) : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg2 hCs) hex
    nlinarith [h1, h2, h3]
  -- the weights `w = kk ω`, `ω(x) = (|x|+1)^{d-2} e^{√|x|}`
  set ω : Zd d L → ℝ := fun x => (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2) *
    Real.exp (√((zdistInf d L x : ℕ) : ℝ)) with hω
  have hω1 : ∀ x, 1 ≤ ω x := fun x => by
    simp only [hω]
    have h1 : (1 : ℝ) ≤ (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2) :=
      one_le_pow₀ (by have : (0 : ℝ) ≤ ((zdistInf d L x : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)
    have h2 : (1 : ℝ) ≤ Real.exp (√((zdistInf d L x : ℕ) : ℝ)) := Real.one_le_exp (Real.sqrt_nonneg _)
    nlinarith
  set w : Zd d L → ℝ := fun x => kk x * ω x with hw
  have hw0 : ∀ x, 0 ≤ w x := fun x => by have := hω1 x; have := hkk0 x; simp only [hw]; positivity
  have hkw : ∀ x, kk x ≤ w x := fun x => by
    simp only [hw]
    exact le_mul_of_one_le_right (hkk0 x) (hω1 x)
  have hSw : ∑ x : Zd d L, w x ≤ S := by
    have h1 : ∀ x : Zd d L, w x = (1 + Cs) * (if x = 0 then 1 else 0) +
        Cs * Λ ^ 2 * (ω x * Real.exp (-(c₀ * ((zdistD d L x : ℕ) : ℝ)))) := by
      intro x
      simp only [hw, hkk, hω]
      by_cases hx : x = 0
      · subst hx; simp [zdistD_zero, iniTermI_zdistInf_zero]
      · simp [hx]; ring
    rw [Finset.sum_congr rfl fun x _ => h1 x, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_one]
    have := hpoly L
    rw [hS]
    have h2 : Cs * Λ ^ 2 * ∑ x : Zd d L, ω x * Real.exp (-(c₀ * ((zdistD d L x : ℕ) : ℝ))) ≤ Cs * Λ ^ 2 * Cp :=
      mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  have hSk : ∑ x : Zd d L, kk x ≤ S := (Finset.sum_le_sum fun x _ => hkw x).trans hSw
  set T₀ : ℝ := tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) with hT₀
  have hT₀0 : 0 ≤ T₀ := tailT_nonneg (Nat.cast_nonneg _)
  -- termwise
  have hterm : ∀ b₁ b₂ : Zd d L, ‖((if a₁ = b₁ then (α : ℂ) else 0) + (β : ℂ) * Θ' a₁ b₁) *
        ((if a₂ = b₂ then (α : ℂ) else 0) + (β : ℂ) * Θ' a₂ b₂) * X b₁ b₂‖
      ≤ M * q * c₀' * T₀ * (w (b₁ - a₁) * w (b₂ - a₂)) + M * F * (kk (b₁ - a₁) * kk (b₂ - a₂)) := by
    intro b₁ b₂
    rw [norm_mul, norm_mul]
    have hX1 := hX b₁ b₂
    have hTs := iniTermI_Ts_le (d := d) (L := L) hd hg hL1 hsu hu hreg a₁ a₂ b₁ b₂
    set m₁ : ℝ := ((zdistInf d L (b₁ - a₁) : ℕ) : ℝ) with hm₁
    set m₂ : ℝ := ((zdistInf d L (b₂ - a₂) : ℕ) : ℝ) with hm₂
    have hm₁0 : 0 ≤ m₁ := Nat.cast_nonneg _
    have hm₂0 : 0 ≤ m₂ := Nat.cast_nonneg _
    have hpow : (m₁ + m₂ + 1) ^ (d - 2) ≤ (m₁ + 1) ^ (d - 2) * (m₂ + 1) ^ (d - 2) := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      nlinarith
    have hexp : Real.exp (√(m₁ + m₂)) ≤ Real.exp (√m₁) * Real.exp (√m₂) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (iniTermI_sqrt_add_le hm₁0 hm₂0)
    have hωω : (m₁ + m₂ + 1) ^ (d - 2) * Real.exp (√(m₁ + m₂)) ≤ ω (b₁ - a₁) * ω (b₂ - a₂) := by
      simp only [hω]
      calc (m₁ + m₂ + 1) ^ (d - 2) * Real.exp (√(m₁ + m₂))
          ≤ ((m₁ + 1) ^ (d - 2) * (m₂ + 1) ^ (d - 2)) * (Real.exp (√m₁) * Real.exp (√m₂)) :=
            mul_le_mul hpow hexp (Real.exp_pos _).le (by positivity)
        _ = _ := by ring
    have hXb : ‖X b₁ b₂‖ ≤ M * (q * (c₀' * (ω (b₁ - a₁) * ω (b₂ - a₂) * T₀)) + F) := by
      refine hX1.trans (mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) hM)
      refine mul_le_mul_of_nonneg_left (hTs.trans ?_) hq
      calc c₀' * (m₁ + m₂ + 1) ^ (d - 2) * Real.exp (√(m₁ + m₂)) * T₀
          = c₀' * ((m₁ + m₂ + 1) ^ (d - 2) * Real.exp (√(m₁ + m₂))) * T₀ := by ring
        _ ≤ c₀' * (ω (b₁ - a₁) * ω (b₂ - a₂)) * T₀ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hωω (by positivity)) hT₀0
        _ = _ := by ring
    have hk1 := hG a₁ b₁
    have hk2 := hG a₂ b₂
    have hn2 : 0 ≤ ‖(if a₂ = b₂ then (α : ℂ) else 0) + (β : ℂ) * Θ' a₂ b₂‖ := norm_nonneg _
    calc ‖(if a₁ = b₁ then (α : ℂ) else 0) + (β : ℂ) * Θ' a₁ b₁‖ *
          ‖(if a₂ = b₂ then (α : ℂ) else 0) + (β : ℂ) * Θ' a₂ b₂‖ * ‖X b₁ b₂‖
        ≤ (kk (b₁ - a₁) * kk (b₂ - a₂)) * (M * (q * (c₀' * (ω (b₁ - a₁) * ω (b₂ - a₂) * T₀)) + F)) :=
          mul_le_mul (mul_le_mul hk1 hk2 hn2 (hkk0 _)) hXb (norm_nonneg _) (mul_nonneg (hkk0 _) (hkk0 _))
      _ = _ := by simp only [hw]; ring
  have hSw0 : 0 ≤ ∑ x : Zd d L, w x := Finset.sum_nonneg fun x _ => hw0 x
  have hSk0 : 0 ≤ ∑ x : Zd d L, kk x := Finset.sum_nonneg fun x _ => hkk0 x
  have hqT : 0 ≤ q * T₀ := mul_nonneg hq hT₀0
  calc ‖∑ b₁ : Zd d L, ∑ b₂ : Zd d L,
          ((if a₁ = b₁ then (α : ℂ) else 0) + (β : ℂ) * Θ' a₁ b₁) *
            ((if a₂ = b₂ then (α : ℂ) else 0) + (β : ℂ) * Θ' a₂ b₂) * X b₁ b₂‖
      ≤ ∑ b₁ : Zd d L, ∑ b₂ : Zd d L, ‖((if a₁ = b₁ then (α : ℂ) else 0) + (β : ℂ) * Θ' a₁ b₁) *
            ((if a₂ = b₂ then (α : ℂ) else 0) + (β : ℂ) * Θ' a₂ b₂) * X b₁ b₂‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun b₁ _ => norm_sum_le _ _)
    _ ≤ ∑ b₁ : Zd d L, ∑ b₂ : Zd d L, (M * q * c₀' * T₀ * (w (b₁ - a₁) * w (b₂ - a₂))
          + M * F * (kk (b₁ - a₁) * kk (b₂ - a₂))) :=
        Finset.sum_le_sum fun b₁ _ => Finset.sum_le_sum fun b₂ _ => hterm b₁ b₂
    _ = M * q * c₀' * T₀ * (∑ x : Zd d L, w x) ^ 2 + M * F * (∑ x : Zd d L, kk x) ^ 2 := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        rw [iniTermI_sum_shift a₁ w, iniTermI_sum_shift a₂ w, iniTermI_sum_shift a₁ kk,
          iniTermI_sum_shift a₂ kk]
        ring
    _ ≤ M * q * c₀' * T₀ * S ^ 2 + M * F * S ^ 2 := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hSw0 hSw 2) (by positivity)
        · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hSk0 hSk 2) (by positivity)
    _ ≤ (c₀' * S ^ 2 + S ^ 2 + 1) * M * (q * T₀ + F) := by
        have h1 : 0 ≤ M * (q * T₀) * (S ^ 2 + 1) + M * F * (c₀' * S ^ 2 + 1) := by positivity
        have h2 : (c₀' * S ^ 2 + S ^ 2 + 1) * M * (q * T₀ + F)
            = M * q * c₀' * T₀ * S ^ 2 + M * F * S ^ 2
              + (M * (q * T₀) * (S ^ 2 + 1) + M * F * (c₀' * S ^ 2 + 1)) := by ring
        rw [h2]; exact le_add_of_nonneg_right h1

end CoreSame3

/-! ### 7'. The mixed signs: `K ⊗ K = (K ⊗ K - β² Θ ⊗ Θ) + β² Θ ⊗ Θ` and the lossy bound -/

section Mixed

variable {d L : ℕ} [NeZero L]

theorem iniTermI_row {g u : ℝ} (hL : 3 ≤ L) (hu0 : 0 ≤ u) (hu : u < 1) (a : Zd d L) :
    ∑ b : Zd d L, ‖Theta d L g (u : ℂ) a b‖ ≤ (1 - u)⁻¹ := by
  have := sum_norm_Theta_row_le (g := g) hL hu0 hu (m := (1 : ℂ)) (by simp) a
  simpa using this

/-- The three terms of `(uwkxkisjwj0)` other than `(1-s)² (Θ 𝓑 Θ)`:
`|ΣΣ (K₁K₂ - β² Θ₁Θ₂) X| ≤ 2(1+C_A) M (q 𝒯_u(|a₁-a₂|) + ρ F)`. -/
theorem iniTermI_U0 (hL : 3 ≤ L) {g s u α β M q F CA : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) (hu : u < 1)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 - s)
    (hαβ : α + β * (1 - u)⁻¹ = (1 - s) / (1 - u))
    (hM : 0 ≤ M) (hq : 0 ≤ q) (hF : 0 ≤ F) (hCA : 0 ≤ CA) (hg : 0 ≤ g) (hL1 : (1 : ℝ) ≤ L)
    (hA : ∀ a₁ a₂ : Zd d L, (1 - s) * ∑ b : Zd d L, ‖Theta d L g (u : ℂ) a₁ b‖ *
        tailT d L g s (zdistInf d L (b - a₂) : ℕ) ≤ CA * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ))
    (a₁ a₂ : Zd d L) (X : Zd d L → Zd d L → ℂ)
    (hX : ∀ b₁ b₂, ‖X b₁ b₂‖ ≤ M * (q * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) + F)) :
    ‖∑ b₁ : Zd d L, ∑ b₂ : Zd d L, (iniTermI_Kf d L g u α β a₁ b₁ * iniTermI_Kf d L g u α β a₂ b₂ -
        (β : ℂ) ^ 2 * (Theta d L g (u : ℂ) a₁ b₁ * Theta d L g (u : ℂ) a₂ b₂)) * X b₁ b₂‖ ≤
      (2 + 2 * CA) * M * (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) + (1 - s) / (1 - u) * F) := by
  have hu0 : 0 < 1 - u := by linarith
  have hs1 : 0 ≤ 1 - s := by linarith
  set ρ : ℝ := (1 - s) / (1 - u) with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg hs1 hu0.le
  have hid : ∀ b₁ b₂ : Zd d L, (iniTermI_Kf d L g u α β a₁ b₁ * iniTermI_Kf d L g u α β a₂ b₂ -
        (β : ℂ) ^ 2 * (Theta d L g (u : ℂ) a₁ b₁ * Theta d L g (u : ℂ) a₂ b₂)) * X b₁ b₂ =
      (if a₁ = b₁ then ((α : ℂ) * iniTermI_Kf d L g u α β a₂ b₂ * X b₁ b₂) else 0) +
        (if a₂ = b₂ then ((β : ℂ) * Theta d L g (u : ℂ) a₁ b₁ * (α : ℂ) * X b₁ b₂) else 0) := by
    intro b₁ b₂; unfold iniTermI_Kf; split_ifs <;> ring
  simp_rw [hid, Finset.sum_add_distrib]
  have h1 : ∑ b₁ : Zd d L, ∑ b₂ : Zd d L, (if a₁ = b₁ then ((α : ℂ) * iniTermI_Kf d L g u α β a₂ b₂ * X b₁ b₂) else 0)
      = ∑ b₂ : Zd d L, (α : ℂ) * iniTermI_Kf d L g u α β a₂ b₂ * X a₁ b₂ := by
    have : ∀ b₁ : Zd d L, ∑ b₂ : Zd d L, (if a₁ = b₁ then ((α : ℂ) * iniTermI_Kf d L g u α β a₂ b₂ * X b₁ b₂) else 0)
        = if a₁ = b₁ then ∑ b₂ : Zd d L, (α : ℂ) * iniTermI_Kf d L g u α β a₂ b₂ * X b₁ b₂ else 0 := by
      intro b₁; split_ifs <;> simp
    simp_rw [this]; rw [Finset.sum_ite_eq]; simp
  have h2 : ∑ b₁ : Zd d L, ∑ b₂ : Zd d L, (if a₂ = b₂ then ((β : ℂ) * Theta d L g (u : ℂ) a₁ b₁ * (α : ℂ) * X b₁ b₂) else 0)
      = ∑ b₁ : Zd d L, (β : ℂ) * Theta d L g (u : ℂ) a₁ b₁ * (α : ℂ) * X b₁ a₂ := by
    refine Finset.sum_congr rfl fun b₁ _ => ?_
    rw [Finset.sum_ite_eq]; simp
  rw [h1, h2]
  refine (norm_add_le _ _).trans ?_
  -- first sum: `ZA` with `b₁ := a₁`
  have hz := iniTermI_ZA hL (g := g) (s := s) (u := u) (α := α) (β := β) (M := M) (q := q) (F := F) (CA := CA) hs hsu hu
    hα1 hβ0 hβ1 hαβ hM hq hF hCA hg hL1 hA a₂ a₁
  have hf : ‖∑ b₂ : Zd d L, (α : ℂ) * iniTermI_Kf d L g u α β a₂ b₂ * X a₁ b₂‖ ≤
      (1 + CA) * M * (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) + ρ * F) := by
    refine (norm_sum_le _ _).trans (le_trans ?_ hz)
    refine Finset.sum_le_sum fun b₂ _ => ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hα0]
    have hk := iniTermI_Kf_norm_le (g := g) (u := u) hα0 hβ0 a₂ b₂
    have hn := norm_nonneg (iniTermI_Kf d L g u α β a₂ b₂)
    calc α * ‖iniTermI_Kf d L g u α β a₂ b₂‖ * ‖X a₁ b₂‖
        ≤ 1 * ‖iniTermI_Kf d L g u α β a₂ b₂‖ * ‖X a₁ b₂‖ := by
          gcongr
      _ ≤ (α * (if a₂ = b₂ then 1 else 0) + β * ‖Theta d L g (u : ℂ) a₂ b₂‖) *
            (M * (q * tailT d L g s (zdistInf d L (a₁ - b₂) : ℕ) + F)) := by
          rw [one_mul]; exact mul_le_mul hk (hX a₁ b₂) (norm_nonneg _) (by positivity)
  have hs2 : ‖∑ b₁ : Zd d L, (β : ℂ) * Theta d L g (u : ℂ) a₁ b₁ * (α : ℂ) * X b₁ a₂‖ ≤
      M * (q * (CA * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ)) + F * ρ) := by
    refine (norm_sum_le _ _).trans ?_
    have hpt : ∀ b₁ : Zd d L, ‖(β : ℂ) * Theta d L g (u : ℂ) a₁ b₁ * (α : ℂ) * X b₁ a₂‖ ≤
        M * q * (β * (‖Theta d L g (u : ℂ) a₁ b₁‖ * tailT d L g s (zdistInf d L (b₁ - a₂) : ℕ))) +
          M * F * (β * ‖Theta d L g (u : ℂ) a₁ b₁‖) := by
      intro b₁
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hα0,
        Real.norm_of_nonneg hβ0]
      have hxb := hX b₁ a₂
      have hn := norm_nonneg (Theta d L g (u : ℂ) a₁ b₁)
      have hT : 0 ≤ tailT d L g s (zdistInf d L (b₁ - a₂) : ℕ) := tailT_nonneg (Nat.cast_nonneg _)
      calc β * ‖Theta d L g (u : ℂ) a₁ b₁‖ * α * ‖X b₁ a₂‖
          ≤ β * ‖Theta d L g (u : ℂ) a₁ b₁‖ * 1 * (M * (q * tailT d L g s (zdistInf d L (b₁ - a₂) : ℕ) + F)) := by
            gcongr
        _ = _ := by ring
    refine (Finset.sum_le_sum fun b₁ _ => hpt b₁).trans ?_
    have hsum1 : ∑ b₁ : Zd d L, M * q * (β * (‖Theta d L g (u : ℂ) a₁ b₁‖ * tailT d L g s (zdistInf d L (b₁ - a₂) : ℕ)))
        = M * q * (β * ∑ b₁ : Zd d L, (‖Theta d L g (u : ℂ) a₁ b₁‖ * tailT d L g s (zdistInf d L (b₁ - a₂) : ℕ))) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    have hsum2 : ∑ b₁ : Zd d L, M * F * (β * ‖Theta d L g (u : ℂ) a₁ b₁‖)
        = M * F * (β * ∑ b₁ : Zd d L, ‖Theta d L g (u : ℂ) a₁ b₁‖) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    rw [Finset.sum_add_distrib, hsum1, hsum2]
    have e1 : β * ∑ b₁ : Zd d L, (‖Theta d L g (u : ℂ) a₁ b₁‖ * tailT d L g s (zdistInf d L (b₁ - a₂) : ℕ)) ≤
        CA * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) :=
      (mul_le_mul_of_nonneg_right hβ1 (Finset.sum_nonneg fun b _ => mul_nonneg (norm_nonneg _)
        (tailT_nonneg (Nat.cast_nonneg _)))).trans (hA a₁ a₂)
    have e2 : β * ∑ b₁ : Zd d L, ‖Theta d L g (u : ℂ) a₁ b₁‖ ≤ ρ := by
      have h3 := iniTermI_row (d := d) (L := L) (g := g) hL (hs.trans hsu) hu a₁
      have h4 : β * ∑ b₁ : Zd d L, ‖Theta d L g (u : ℂ) a₁ b₁‖ ≤ β * (1 - u)⁻¹ := mul_le_mul_of_nonneg_left h3 hβ0
      have h5 : β * (1 - u)⁻¹ ≤ ρ := by rw [← hαβ]; linarith
      linarith
    have e3 : 0 ≤ M * q := mul_nonneg hM hq
    have e4 : 0 ≤ M * F := mul_nonneg hM hF
    nlinarith [mul_le_mul_of_nonneg_left e1 e3, mul_le_mul_of_nonneg_left e2 e4]
  have hρ1 : 0 ≤ q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) := mul_nonneg hq (tailT_nonneg (Nat.cast_nonneg _))
  nlinarith [hf, hs2, mul_nonneg hM hρ1, mul_nonneg (mul_nonneg hM hF) hρ0, mul_nonneg hCA (mul_nonneg hM hρ1)]

/-- **The `ρ`-lossy bound** (two applications of `(uwp2-92kj)`; the case `ρ ≤ (log W)^{10}` of `3_5:2119`):
`|ΣΣ K₁K₂ X| ≤ (1+C_A)(2+C_A) M ρ (q 𝒯_u(|a₁-a₂|) + ρ F)`, `ρ = (1-s)/(1-u)`. -/
theorem iniTermI_bil_lossy (hL : 3 ≤ L) {g s u α β M q F CA : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) (hu : u < 1)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 - s)
    (hαβ : α + β * (1 - u)⁻¹ = (1 - s) / (1 - u))
    (hM : 0 ≤ M) (hq : 0 ≤ q) (hF : 0 ≤ F) (hCA : 0 ≤ CA) (hg : 0 ≤ g) (hL1 : (1 : ℝ) ≤ L)
    (hA : ∀ a₁ a₂ : Zd d L, (1 - s) * ∑ b : Zd d L, ‖Theta d L g (u : ℂ) a₁ b‖ *
        tailT d L g s (zdistInf d L (b - a₂) : ℕ) ≤ CA * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ))
    (hAu : ∀ a₁ a₂ : Zd d L, (1 - u) * ∑ b : Zd d L, ‖Theta d L g (u : ℂ) a₁ b‖ *
        tailT d L g u (zdistInf d L (b - a₂) : ℕ) ≤ CA * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ))
    (a₁ a₂ : Zd d L) (X : Zd d L → Zd d L → ℂ)
    (hX : ∀ b₁ b₂, ‖X b₁ b₂‖ ≤ M * (q * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) + F)) :
    ‖∑ b₁ : Zd d L, ∑ b₂ : Zd d L, iniTermI_Kf d L g u α β a₁ b₁ * iniTermI_Kf d L g u α β a₂ b₂ * X b₁ b₂‖ ≤
      (1 + CA) * (2 + CA) * M * ((1 - s) / (1 - u) *
        (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) + (1 - s) / (1 - u) * F)) := by
  have hu0 : 0 < 1 - u := by linarith
  have hs1 : 0 ≤ 1 - s := by linarith
  set ρ : ℝ := (1 - s) / (1 - u) with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg hs1 hu0.le
  have hρ1 : 1 ≤ ρ := (one_le_div hu0).mpr (by linarith)
  set C₁ : ℝ := 1 + CA with hC₁
  have hTn : ∀ x : Zd d L, 0 ≤ tailT d L g u (zdistInf d L x : ℕ) := fun x => tailT_nonneg (Nat.cast_nonneg _)
  set R : Zd d L → ℝ := fun b => C₁ * M * (q * tailT d L g u (zdistInf d L (b - a₂) : ℕ) + ρ * F) with hR
  have hRnn : ∀ b, 0 ≤ R b := fun b => by simp only [hR]; have := hTn (b - a₂); positivity
  -- step 1
  have hstep1 : ‖∑ b₁ : Zd d L, ∑ b₂ : Zd d L, iniTermI_Kf d L g u α β a₁ b₁ * iniTermI_Kf d L g u α β a₂ b₂ * X b₁ b₂‖
      ≤ ∑ b₁ : Zd d L, (α * (if a₁ = b₁ then 1 else 0) + β * ‖Theta d L g (u : ℂ) a₁ b₁‖) * R b₁ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b₁ _ => ?_)
    have hz := iniTermI_ZA hL (g := g) (s := s) (u := u) (α := α) (β := β) (M := M) (q := q) (F := F) (CA := CA) hs hsu hu
      hα1 hβ0 hβ1 hαβ hM hq hF hCA hg hL1 hA a₂ b₁
    calc ‖∑ b₂ : Zd d L, iniTermI_Kf d L g u α β a₁ b₁ * iniTermI_Kf d L g u α β a₂ b₂ * X b₁ b₂‖
        ≤ ∑ b₂ : Zd d L, ‖iniTermI_Kf d L g u α β a₁ b₁‖ * (‖iniTermI_Kf d L g u α β a₂ b₂‖ * ‖X b₁ b₂‖) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b₂ _ => ?_)
          rw [norm_mul, norm_mul]; ring_nf; exact le_rfl
      _ = ‖iniTermI_Kf d L g u α β a₁ b₁‖ * ∑ b₂ : Zd d L, ‖iniTermI_Kf d L g u α β a₂ b₂‖ * ‖X b₁ b₂‖ := by
          rw [Finset.mul_sum]
      _ ≤ (α * (if a₁ = b₁ then 1 else 0) + β * ‖Theta d L g (u : ℂ) a₁ b₁‖) * R b₁ := by
          refine mul_le_mul (iniTermI_Kf_norm_le hα0 hβ0 a₁ b₁) ?_
            (Finset.sum_nonneg fun b₂ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
          refine le_trans (Finset.sum_le_sum fun b₂ _ => mul_le_mul (iniTermI_Kf_norm_le hα0 hβ0 a₂ b₂)
            (hX b₁ b₂) (norm_nonneg _) (by positivity)) ?_
          exact hz
  -- step 2
  have hsplit : ∑ b₁ : Zd d L, (α * (if a₁ = b₁ then 1 else 0) + β * ‖Theta d L g (u : ℂ) a₁ b₁‖) * R b₁ =
      α * R a₁ + β * ∑ b₁ : Zd d L, ‖Theta d L g (u : ℂ) a₁ b₁‖ * R b₁ := by
    have h1 : ∀ b₁ : Zd d L, (α * (if a₁ = b₁ then 1 else 0) + β * ‖Theta d L g (u : ℂ) a₁ b₁‖) * R b₁
        = (if a₁ = b₁ then α * R b₁ else 0) + β * (‖Theta d L g (u : ℂ) a₁ b₁‖ * R b₁) := by
      intro b₁; split_ifs <;> ring
    rw [Finset.sum_congr rfl fun b₁ _ => h1 b₁, Finset.sum_add_distrib, Finset.sum_ite_eq, ← Finset.mul_sum]
    simp
  -- step 3
  have hT0 : 0 ≤ q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) := mul_nonneg hq (hTn _)
  have hi : α * R a₁ ≤ C₁ * M * (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) + ρ * F) :=
    (mul_le_mul_of_nonneg_right hα1 (hRnn a₁)).trans (by rw [one_mul])
  have hrow := iniTermI_row (d := d) (L := L) (g := g) hL (hs.trans hsu) hu a₁
  have hβρ : β * (1 - u)⁻¹ ≤ ρ := by rw [← hαβ]; linarith
  have hii : β * ∑ b₁ : Zd d L, ‖Theta d L g (u : ℂ) a₁ b₁‖ * R b₁ ≤
      C₁ * M * (CA * ρ * (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ)) + ρ * ρ * F) := by
    have e0 : ∑ b₁ : Zd d L, ‖Theta d L g (u : ℂ) a₁ b₁‖ * R b₁ =
        C₁ * M * (q * ∑ b₁ : Zd d L, ‖Theta d L g (u : ℂ) a₁ b₁‖ * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ)
          + ρ * F * ∑ b₁ : Zd d L, ‖Theta d L g (u : ℂ) a₁ b₁‖) := by
      simp only [hR, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b₁ _ => by ring
    have e1 : ∑ b₁ : Zd d L, ‖Theta d L g (u : ℂ) a₁ b₁‖ * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ) ≤
        CA * (1 - u)⁻¹ * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) := by
      have h2 := hAu a₁ a₂
      have h3 : ∑ b₁ : Zd d L, ‖Theta d L g (u : ℂ) a₁ b₁‖ * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ)
          = (1 - u)⁻¹ * ((1 - u) * ∑ b₁ : Zd d L, ‖Theta d L g (u : ℂ) a₁ b₁‖ *
              tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ)) := by field_simp
      rw [h3]
      calc (1 - u)⁻¹ * ((1 - u) * ∑ b₁ : Zd d L, ‖Theta d L g (u : ℂ) a₁ b₁‖ *
              tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ))
          ≤ (1 - u)⁻¹ * (CA * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ)) :=
            mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hu0.le)
        _ = _ := by ring
    have e2 : 0 ≤ ∑ b₁ : Zd d L, ‖Theta d L g (u : ℂ) a₁ b₁‖ * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ) :=
      Finset.sum_nonneg fun b _ => mul_nonneg (norm_nonneg _) (hTn _)
    rw [e0]
    have hc : 0 ≤ C₁ * M := by positivity
    calc β * (C₁ * M * (q * ∑ b₁ : Zd d L, ‖Theta d L g (u : ℂ) a₁ b₁‖ * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ)
          + ρ * F * ∑ b₁ : Zd d L, ‖Theta d L g (u : ℂ) a₁ b₁‖))
        = C₁ * M * (q * (β * ∑ b₁ : Zd d L, ‖Theta d L g (u : ℂ) a₁ b₁‖ * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ))
          + ρ * F * (β * ∑ b₁ : Zd d L, ‖Theta d L g (u : ℂ) a₁ b₁‖)) := by ring
      _ ≤ C₁ * M * (q * (CA * ρ * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ)) + ρ * F * ρ) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hc
          · refine mul_le_mul_of_nonneg_left ?_ hq
            calc β * ∑ b₁ : Zd d L, ‖Theta d L g (u : ℂ) a₁ b₁‖ * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ)
                ≤ β * (CA * (1 - u)⁻¹ * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ)) :=
                  mul_le_mul_of_nonneg_left e1 hβ0
              _ = CA * (β * (1 - u)⁻¹) * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) := by ring
              _ ≤ CA * ρ * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hβρ hCA) (hTn _)
          · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact (mul_le_mul_of_nonneg_left hrow hβ0).trans hβρ
      _ = _ := by ring
  refine hstep1.trans (hsplit.le.trans ((add_le_add hi hii).trans ?_))
  have hTq := hT0
  have hF0 : 0 ≤ ρ * F := mul_nonneg hρ0 hF
  have hC0 : 0 ≤ C₁ * M := by positivity
  have key : C₁ * M * (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) + ρ * F) +
      C₁ * M * (CA * ρ * (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ)) + ρ * ρ * F) =
      C₁ * M * ((1 + CA * ρ) * (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ)) + (ρ + ρ * ρ) * F) := by ring
  rw [key]
  have : (1 + CA * ρ) * (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ)) + (ρ + ρ * ρ) * F ≤
      (2 + CA) * (ρ * (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) + ρ * F)) := by
    nlinarith [mul_nonneg hCA (sub_nonneg.2 hρ1), mul_nonneg hTq (sub_nonneg.2 hρ1), mul_nonneg hF (sub_nonneg.2 hρ1),
      mul_nonneg (mul_nonneg hF hρ0) (sub_nonneg.2 hρ1), mul_nonneg (mul_nonneg hCA hTq) (sub_nonneg.2 hρ1),
      mul_nonneg (mul_nonneg hF hCA) hρ0, mul_nonneg (mul_nonneg hF hρ0) hρ0]
  calc C₁ * M * ((1 + CA * ρ) * (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ)) + (ρ + ρ * ρ) * F)
      ≤ C₁ * M * ((2 + CA) * (ρ * (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) + ρ * F))) :=
        mul_le_mul_of_nonneg_left this hC0
    _ = _ := by rw [hC₁]; ring

end Mixed

/-! ### 8'. The deterministic cores -/

/-- `(1-s)² Σ_{b₁,b₂} Θ_{a₁b₁} Θ_{a₂b₂} X(b₁,b₂)`, `Θ = Θ_u^{(+,-)}`: the term `(iksjuwjx)` of `3_5:2096`. -/
def iniTermI_Sfull (d L : ℕ) [NeZero L] (g s u : ℝ) (X : (Fin 2 → Zd d L) → ℂ) (a : Fin 2 → Zd d L) : ℂ :=
  (((1 - s) ^ 2 : ℝ) : ℂ) * ∑ b₁ : Zd d L, ∑ b₂ : Zd d L,
    Theta d L g (u : ℂ) (a 0) b₁ * Theta d L g (u : ℂ) (a 1) b₂ * X ![b₁, b₂]

/-- **The deterministic core, `σ₁ ≠ σ₂`, large part** (`(uwkxkisjwj0)`, `3_5:2086-2092`): the first three terms of the expansion of
`𝒰_{s,u,σ} X` are `≤ C M (λ W^{-d} 𝒯_u + ρ W^{-D})` and the fourth is `c (1-s)² (Θ X Θ)`, `c = ((u-s)/(u(1-s)))² ∈ [0,1]`. -/
theorem iniTermI_core_mixed (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g W D E s u M lam : ℝ), 0 < g → g ≤ Λ → 0 < W →
        |E| ≤ 2 → 0 ≤ s → s ≤ u → u < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u → 0 ≤ M → 0 ≤ lam →
        ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ X : (Fin 2 → Zd d L) → ℂ,
          (∀ b, ‖X b‖ ≤ M * (lam * (W ^ d)⁻¹ * tailT d L g s (zdistInf d L (b 0 - b 1) : ℕ) + W ^ (-D))) →
          ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ a, ‖RBM.Ind.Ugen d L g E σ s u X a - (c : ℂ) * iniTermI_Sfull d L g s u X a‖ ≤
            C * M * (lam * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) +
              (1 - s) / (1 - u) * W ^ (-D)) := by
  obtain ⟨CA, hCA, HA⟩ := iniTermI_stageA d Λ hd hΛ
  refine ⟨2 + 2 * CA, by positivity, ?_⟩
  intro L _ hL g W D E s u M lam hg hgΛ hW hE hs hsu hu hreg hM hlam σ hσ X hX
  have hu0 : 0 ≤ u := hs.trans hsu
  have hL1 : (1 : ℝ) ≤ L := by
    have : (3 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  obtain ⟨α, β, hα0, hα1, hβ0, hβ1, hαβ, hrep⟩ :=
    iniTermI_Ugen_rep (d := d) (L := L) (g := g) hL hE (μ := 1) (iniTermI_cyc_mixed hE hσ) hs hsu hu
  have hs1 : 0 < 1 - s := by linarith
  refine ⟨β ^ 2 / (1 - s) ^ 2, by positivity, ?_, ?_⟩
  · rw [div_le_one (by positivity)]
    exact pow_le_pow_left₀ hβ0 hβ1 2
  intro a
  have hfun : RBM.Ind.Ugen d L g E σ s u X a = ∑ b₁ : Zd d L, ∑ b₂ : Zd d L,
      iniTermI_Kf d L g u α β (a 0) b₁ * iniTermI_Kf d L g u α β (a 1) b₂ * X ![b₁, b₂] := by
    simpa only [mul_one, iniTermI_Kf] using hrep X a
  have hid : RBM.Ind.Ugen d L g E σ s u X a - ((β ^ 2 / (1 - s) ^ 2 : ℝ) : ℂ) * iniTermI_Sfull d L g s u X a =
      ∑ b₁ : Zd d L, ∑ b₂ : Zd d L, (iniTermI_Kf d L g u α β (a 0) b₁ * iniTermI_Kf d L g u α β (a 1) b₂ -
        (β : ℂ) ^ 2 * (Theta d L g (u : ℂ) (a 0) b₁ * Theta d L g (u : ℂ) (a 1) b₂)) * X ![b₁, b₂] := by
    unfold iniTermI_Sfull
    have hcβ : ((β ^ 2 / (1 - s) ^ 2 : ℝ) : ℂ) * (((1 - s) ^ 2 : ℝ) : ℂ) = (β : ℂ) ^ 2 := by
      have : (1 - (s : ℂ)) ≠ 0 := by exact_mod_cast hs1.ne'
      push_cast; field_simp
    rw [hfun, ← mul_assoc, hcβ, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b₁ _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b₂ _ => by ring
  rw [hid]
  have hq : 0 ≤ lam * (W ^ d)⁻¹ := by positivity
  have hF : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  have hX' : ∀ b₁ b₂ : Zd d L, ‖X ![b₁, b₂]‖ ≤
      M * (lam * (W ^ d)⁻¹ * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) + W ^ (-D)) := fun b₁ b₂ => by
    simpa using hX ![b₁, b₂]
  exact iniTermI_U0 hL (g := g) (M := M) (q := lam * (W ^ d)⁻¹) (F := W ^ (-D)) (CA := CA) hs hsu hu hα0 hα1 hβ0 hβ1 hαβ hM hq hF
    hCA.le hg.le hL1 (fun a₁ a₂ => HA L hL g s u hg hgΛ hs hsu hu hreg a₁ a₂) (a 0) (a 1)
    (fun b₁ b₂ => X ![b₁, b₂]) hX'

/-- **The deterministic core, `σ₁ ≠ σ₂`, `ρ`-lossy** (`ρ ≤ (log W)^{10}`, `3_5:2119`, "two applications of `(uwp2-92kj)`"). -/
theorem iniTermI_core_lossy (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g W D E s u M lam : ℝ), 0 < g → g ≤ Λ → 0 < W →
        |E| ≤ 2 → 0 ≤ s → s ≤ u → u < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u → 0 ≤ M → 0 ≤ lam →
        ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ X : (Fin 2 → Zd d L) → ℂ,
          (∀ b, ‖X b‖ ≤ M * (lam * (W ^ d)⁻¹ * tailT d L g s (zdistInf d L (b 0 - b 1) : ℕ) + W ^ (-D))) →
          ∀ a, ‖RBM.Ind.Ugen d L g E σ s u X a‖ ≤
            C * M * ((1 - s) / (1 - u) * (lam * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) +
              (1 - s) / (1 - u) * W ^ (-D))) := by
  obtain ⟨CA, hCA, HA⟩ := iniTermI_stageA d Λ hd hΛ
  refine ⟨(1 + CA) * (2 + CA), by positivity, ?_⟩
  intro L _ hL g W D E s u M lam hg hgΛ hW hE hs hsu hu hreg hM hlam σ hσ X hX a
  have hu0 : 0 ≤ u := hs.trans hsu
  have hL1 : (1 : ℝ) ≤ L := by
    have : (3 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  obtain ⟨α, β, hα0, hα1, hβ0, hβ1, hαβ, hrep⟩ :=
    iniTermI_Ugen_rep (d := d) (L := L) (g := g) hL hE (μ := 1) (iniTermI_cyc_mixed hE hσ) hs hsu hu
  have hfun : RBM.Ind.Ugen d L g E σ s u X a = ∑ b₁ : Zd d L, ∑ b₂ : Zd d L,
      iniTermI_Kf d L g u α β (a 0) b₁ * iniTermI_Kf d L g u α β (a 1) b₂ * X ![b₁, b₂] := by
    simpa only [mul_one, iniTermI_Kf] using hrep X a
  rw [hfun]
  have hq : 0 ≤ lam * (W ^ d)⁻¹ := by positivity
  have hF : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  have hX' : ∀ b₁ b₂ : Zd d L, ‖X ![b₁, b₂]‖ ≤
      M * (lam * (W ^ d)⁻¹ * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) + W ^ (-D)) := fun b₁ b₂ => by
    simpa using hX ![b₁, b₂]
  have := iniTermI_bil_lossy hL (g := g) (M := M) (q := lam * (W ^ d)⁻¹) (F := W ^ (-D)) (CA := CA) hs hsu hu hα0 hα1 hβ0 hβ1
    hαβ hM hq hF hCA.le hg.le hL1 (fun a₁ a₂ => HA L hL g s u hg hgΛ hs hsu hu hreg a₁ a₂)
    (fun a₁ a₂ => HA L hL g u u hg hgΛ hu0 le_rfl hu hreg a₁ a₂) (a 0) (a 1) (fun b₁ b₂ => X ![b₁, b₂]) hX'
  exact this

/-! ### 9'. The deterministic core, `σ₁ = σ₂` -/

/-- **Target 2, `σ₁ = σ₂`: the short-range initial term** (`3_5:2253`, `(prop:ThfadC_short)`; no zero-mode removal).  With the
hypotheses of `iniTermI_core` (here the regime `1 - s ≤ g²/L²` enters only through `ℓ_u = L`, i.e. `e⁻¹ B_{u,r} ≤ 𝒯_u(r)`, in the
comparison `𝒯_s(|b₁-b₂|) ≤ e (m+1)^{d-2} 𝒯_u(|a₁-a₂|)`; no `ρ`-factor on the floor):
`|[𝒰_{s,u,σ} X]_a| ≤ C M ((λ W^{-d}) 𝒯_u(|a₁-a₂|) + W^{-D})`, `C = C(d, Λ, κ_m)`. -/
theorem iniTermI_core_same (d : ℕ) (Λ κm : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) (hκm : 0 < κm) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g W D E s u M lam : ℝ), 0 < g → g ≤ Λ → 0 < W →
        |E| ≤ 2 → κm ≤ (mE E).im → 0 ≤ s → s ≤ u → u < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u → 0 ≤ M → 0 ≤ lam →
        ∀ σ : Fin 2 → Bool, σ 0 = σ 1 → ∀ X : (Fin 2 → Zd d L) → ℂ,
          (∀ b, ‖X b‖ ≤ M * (lam * (W ^ d)⁻¹ * tailT d L g s (zdistInf d L (b 0 - b 1) : ℕ) + W ^ (-D))) →
          ∀ a, ‖RBM.Ind.Ugen d L g E σ s u X a‖ ≤
            C * M * (lam * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) + W ^ (-D)) := by
  obtain ⟨Cs, hCs, c₀, hc₀, H5⟩ := prop5Short_holds d Λ κm hd hΛ hκm
  obtain ⟨C, hC, Hb⟩ := iniTermI_bil_same d hd Cs c₀ Λ hCs.le hc₀
  refine ⟨C, hC, ?_⟩
  intro L _ hL g W D E s u M lam hg hgΛ hW hE hκ hs hsu hu hreg hM hlam σ hσ X hX a
  have hu0 : 0 ≤ u := hs.trans hsu
  have hμc : ∀ i : Fin 2, cycProd (fun i => mSigma E (σ i)) i = mSigma E (σ 0) * mSigma E (σ 0) := by
    have hf0 : finRotate 2 0 = 1 := by decide
    have hf1 : finRotate 2 1 = 0 := by decide
    intro i
    fin_cases i
    · simp only [cycProd, Fin.zero_eta, hf0, ← hσ]
    · simp only [cycProd, Fin.mk_one, hf1, ← hσ]
  obtain ⟨α, β, hα0, hα1, hβ0, hβ1, hαβ, hrep⟩ :=
    iniTermI_Ugen_rep (d := d) (L := L) (g := g) hL hE (μ := mSigma E (σ 0) * mSigma E (σ 0)) hμc hs hsu hu
  have hξ : ‖(u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 0))‖ < 1 := norm_mul_mSigma_lt_one hE hu0 hu _ _
  have hΘ : ∀ a' b' : Zd d L, ‖Theta d L g ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 0))) a' b'‖ ≤
      Cs * ((if a' = b' then 1 else 0) + g ^ 2 * Real.exp (-(c₀ * ((zdistD d L (b' - a') : ℕ) : ℝ)))) := by
    intro a' b'
    have h5 := H5 L hL g hg hgΛ u hu0 hu (mE E) (norm_mE hE) hκ (σ 0) (b' - a')
    have hps : PropSpin (mE E) (σ 0) = mSigma E (σ 0) := rfl
    rw [hps, ← iniTermI_Theta_shift hL hξ a' b'] at h5
    have hif : (if b' - a' = 0 then (1 : ℝ) else 0) = if a' = b' then 1 else 0 := by
      by_cases h : a' = b'
      · simp [h]
      · have : b' - a' ≠ 0 := fun h' => h (sub_eq_zero.mp h').symm
        simp [h, this]
    rw [hif, neg_mul] at h5
    exact h5
  have hq : 0 ≤ lam * (W ^ d)⁻¹ := by positivity
  have hF : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  have hX' : ∀ b₁ b₂ : Zd d L, ‖X ![b₁, b₂]‖ ≤
      M * (lam * (W ^ d)⁻¹ * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) + W ^ (-D)) := fun b₁ b₂ => by
    simpa using hX ![b₁, b₂]
  rw [hrep X a]
  exact Hb L hL g s u α β M (lam * (W ^ d)⁻¹) (W ^ (-D)) hg hgΛ hsu hu hreg hα0 hα1 hβ0 (by linarith) hM hq hF
    (Theta d L g ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 0)))) hΘ (a 0) (a 1) (fun b₁ b₂ => X ![b₁, b₂]) hX'

/-! ### 10. `(1-s)² (Θ 𝓑 Θ) = f^{near} + f^{far} + g` (`3_5:2130-2135`) -/

section Decomp

variable {d L : ℕ} [NeZero L]

theorem iniTermI_Theta_symm {g : ℝ} (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (x y : Zd d L) :
    Theta d L g ξ x y = Theta d L g ξ y x := by
  have := congrFun (congrFun (Theta_transpose_of_three_le (d := d) (g := g) hL hξ) x) y
  have h : Theta d L g ξ y x = Theta d L g ξ x y := by simpa [Matrix.transpose_apply] using this
  exact h.symm

theorem iniTermI_card_Zd : (Fintype.card (Zd d L) : ℝ) = (L : ℝ) ^ d := by
  have : Fintype.card (Zd d L) = L ^ d := by simp [Zd]
  rw [this]; push_cast; ring

/-- `f_a` of `3_5:2098` over the label set `P` (`f^{near}`: `P = ¬ far`, `f^{far} = STfFar`: `P = far`). -/
def iniTermI_fSum (d L : ℕ) [NeZero L] (g s u : ℝ) (X : (Fin 2 → Zd d L) → ℂ) (a : Fin 2 → Zd d L)
    (P : Zd d L → Prop) [DecidablePred P] : ℂ :=
  (((1 - s) ^ 2 : ℝ) : ℂ) * ∑ b₁ ∈ Finset.univ.filter P, ∑ b₂ : Zd d L,
    Theta d L g (u : ℂ) (a 0) b₁ * X ![b₁, b₂] *
      (Theta d L g (u : ℂ) b₂ (a 1) - Theta d L g (u : ℂ) b₁ (a 1))

/-- `g_a` of `3_5:2098`, before the Ward identity. -/
def iniTermI_Gward (d L : ℕ) [NeZero L] (g s u : ℝ) (X : (Fin 2 → Zd d L) → ℂ) (a : Fin 2 → Zd d L) : ℂ :=
  (((1 - s) ^ 2 : ℝ) : ℂ) * ∑ b₁ : Zd d L,
    Theta d L g (u : ℂ) (a 0) b₁ * Theta d L g (u : ℂ) b₁ (a 1) * ∑ b₂ : Zd d L, X ![b₁, b₂]

theorem iniTermI_Sfull_decomp (hL : 3 ≤ L) {g s u : ℝ} (hu0 : 0 ≤ u) (hu : u < 1)
    (X : (Fin 2 → Zd d L) → ℂ) (a : Fin 2 → Zd d L) (P : Zd d L → Prop) [DecidablePred P] :
    iniTermI_Sfull d L g s u X a =
      iniTermI_fSum d L g s u X a (fun b => ¬ P b) + iniTermI_fSum d L g s u X a P + iniTermI_Gward d L g s u X a := by
  have hξ : ‖(u : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_of_nonneg hu0]
  unfold iniTermI_Sfull iniTermI_fSum iniTermI_Gward
  have hb : ∀ b₁ : Zd d L, ∑ b₂ : Zd d L, Theta d L g (u : ℂ) (a 0) b₁ * Theta d L g (u : ℂ) (a 1) b₂ * X ![b₁, b₂] =
      (∑ b₂ : Zd d L, Theta d L g (u : ℂ) (a 0) b₁ * X ![b₁, b₂] *
        (Theta d L g (u : ℂ) b₂ (a 1) - Theta d L g (u : ℂ) b₁ (a 1))) +
      Theta d L g (u : ℂ) (a 0) b₁ * Theta d L g (u : ℂ) b₁ (a 1) * ∑ b₂ : Zd d L, X ![b₁, b₂] := by
    intro b₁
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b₂ _ => ?_
    rw [iniTermI_Theta_symm hL hξ (a 1) b₂]; ring
  have hsplit := Finset.sum_filter_not_add_sum_filter (Finset.univ : Finset (Zd d L)) P
    (fun b₁ => ∑ b₂ : Zd d L, Theta d L g (u : ℂ) (a 0) b₁ * X ![b₁, b₂] *
      (Theta d L g (u : ℂ) b₂ (a 1) - Theta d L g (u : ℂ) b₁ (a 1)))
  rw [Finset.sum_congr rfl fun b₁ _ => hb b₁, Finset.sum_add_distrib, ← hsplit]
  ring

end Decomp

/-! ### 11. The near part: `f^{near} ≺ (1-s)² g^{-4} ℓ_s⁴ A^{-6/5}/(|a₁-a₂|^{d-2}+1)` (`3_5:2160-2171`) -/

section Near

variable {d L : ℕ} [NeZero L]

/-- The constant of `iniTermI_W2`: `Σ_{|x|≤R} P(x) P(x-w) ≤ C_W R² P(w)`. -/
def iniTermI_CW (d : ℕ) : ℝ := 2 ^ (d - 2) * (2 * iniTermI_CB d)

theorem iniTermI_CW_nonneg (d : ℕ) : 0 ≤ iniTermI_CW d := by
  unfold iniTermI_CW; have := iniTermI_CB_nonneg d; positivity

/-- The sum over the second label: for `|X_{b₁b₂}| ≤ 1_{|b₁-b₂|≤R} M₁ P(b₁-b₂) + M₄` and `|T| ≤ T₁ P`, `|T| ≤ T_m`,
`Σ_{b₂} |X_{b₁b₂}| |T_{b₂a₁} - T_{b₁a₁}| ≤ M₁ T₁ (C_W + C_B) R² P(b₁-a₁) + N (2 T_m M₄)`. -/
theorem iniTermI_near_inner (hd : 3 ≤ d) {T₁ Tm M₁ M₄ R : ℝ} (hR : 1 ≤ R) (hT₁ : 0 ≤ T₁) (_hTm : 0 ≤ Tm)
    (hM₁ : 0 ≤ M₁) (hM₄ : 0 ≤ M₄) (T : Zd d L → Zd d L → ℂ)
    (hT1 : ∀ x y, ‖T x y‖ ≤ T₁ * iniTermI_PI d L (x - y)) (hTm' : ∀ x y, ‖T x y‖ ≤ Tm)
    (X : Zd d L → Zd d L → ℂ)
    (hX : ∀ b₁ b₂, ‖X b₁ b₂‖ ≤
      (if ((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) ≤ R then M₁ * iniTermI_PI d L (b₁ - b₂) else 0) + M₄)
    (a₁ b₁ : Zd d L) :
    ∑ b₂ : Zd d L, ‖X b₁ b₂‖ * ‖T b₂ a₁ - T b₁ a₁‖ ≤
      M₁ * T₁ * ((iniTermI_CW d + iniTermI_CB d) * R ^ 2) * iniTermI_PI d L (b₁ - a₁) +
        (Fintype.card (Zd d L) : ℝ) * (2 * Tm * M₄) := by
  classical
  set Dset : Finset (Zd d L) := Finset.univ.filter (fun b₂ => ((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) ≤ R) with hDset
  have hPnn : ∀ x : Zd d L, 0 ≤ iniTermI_PI d L x := iniTermI_PI_nonneg
  have hpt : ∀ b₂ : Zd d L, ‖X b₁ b₂‖ * ‖T b₂ a₁ - T b₁ a₁‖ ≤
      (if ((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) ≤ R then
        M₁ * T₁ * (iniTermI_PI d L (b₁ - b₂) * iniTermI_PI d L (b₂ - a₁) +
          iniTermI_PI d L (b₁ - b₂) * iniTermI_PI d L (b₁ - a₁)) else 0) + M₄ * (2 * Tm) := by
    intro b₂
    have hτ : ‖T b₂ a₁ - T b₁ a₁‖ ≤ T₁ * (iniTermI_PI d L (b₂ - a₁) + iniTermI_PI d L (b₁ - a₁)) := by
      refine (norm_sub_le _ _).trans ?_
      have := hT1 b₂ a₁; have := hT1 b₁ a₁; linarith
    have hτ' : ‖T b₂ a₁ - T b₁ a₁‖ ≤ 2 * Tm := by
      refine (norm_sub_le _ _).trans ?_
      have := hTm' b₂ a₁; have := hTm' b₁ a₁; linarith
    have hτ0 : 0 ≤ ‖T b₂ a₁ - T b₁ a₁‖ := norm_nonneg _
    have hX0 := hX b₁ b₂
    have hn1 := hPnn (b₁ - b₂)
    calc ‖X b₁ b₂‖ * ‖T b₂ a₁ - T b₁ a₁‖
        ≤ ((if ((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) ≤ R then M₁ * iniTermI_PI d L (b₁ - b₂) else 0) + M₄) *
            ‖T b₂ a₁ - T b₁ a₁‖ := mul_le_mul_of_nonneg_right hX0 hτ0
      _ = (if ((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) ≤ R then M₁ * iniTermI_PI d L (b₁ - b₂) else 0) *
            ‖T b₂ a₁ - T b₁ a₁‖ + M₄ * ‖T b₂ a₁ - T b₁ a₁‖ := by ring
      _ ≤ _ := by
          refine add_le_add ?_ (mul_le_mul_of_nonneg_left hτ' hM₄)
          split_ifs
          · calc M₁ * iniTermI_PI d L (b₁ - b₂) * ‖T b₂ a₁ - T b₁ a₁‖
                ≤ M₁ * iniTermI_PI d L (b₁ - b₂) * (T₁ * (iniTermI_PI d L (b₂ - a₁) + iniTermI_PI d L (b₁ - a₁))) :=
                  mul_le_mul_of_nonneg_left hτ (by positivity)
              _ = _ := by ring
          · simp
  have h1 : ∑ b₂ : Zd d L, ‖X b₁ b₂‖ * ‖T b₂ a₁ - T b₁ a₁‖ ≤
      ∑ b₂ : Zd d L, ((if ((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) ≤ R then
        M₁ * T₁ * (iniTermI_PI d L (b₁ - b₂) * iniTermI_PI d L (b₂ - a₁) +
          iniTermI_PI d L (b₁ - b₂) * iniTermI_PI d L (b₁ - a₁)) else 0) + M₄ * (2 * Tm)) :=
    Finset.sum_le_sum fun b₂ _ => hpt b₂
  refine h1.trans ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_filter]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hD1 : ∀ x ∈ Dset, ((zdistInf d L (x - b₁) : ℕ) : ℝ) ≤ R := fun x hx => by
    have := (Finset.mem_filter.1 hx).2
    rwa [iniTermI_zdistInf_sub_comm] at this
  have hw2 := iniTermI_W2 hd hR b₁ a₁ Dset hD1
  have hb := iniTermI_ball_PI hd hR b₁ Dset hD1
  have e1 : ∑ x ∈ Dset, (iniTermI_PI d L (b₁ - x) * iniTermI_PI d L (x - a₁) +
      iniTermI_PI d L (b₁ - x) * iniTermI_PI d L (b₁ - a₁)) ≤
      (iniTermI_CW d + iniTermI_CB d) * R ^ 2 * iniTermI_PI d L (b₁ - a₁) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    have e2 : ∑ x ∈ Dset, iniTermI_PI d L (b₁ - x) = ∑ x ∈ Dset, iniTermI_PI d L (x - b₁) :=
      Finset.sum_congr rfl fun x _ => iniTermI_PI_sub_comm _ _
    rw [e2]
    have hp := hPnn (b₁ - a₁)
    have : 2 ^ (d - 2) * (2 * (iniTermI_CB d * R ^ 2)) = iniTermI_CW d * R ^ 2 := by unfold iniTermI_CW; ring
    rw [this] at hw2
    nlinarith [mul_le_mul_of_nonneg_right hb hp]
  have hM : 0 ≤ M₁ * T₁ := mul_nonneg hM₁ hT₁
  have e3 : ∑ x ∈ Dset, M₁ * T₁ * (iniTermI_PI d L (b₁ - x) * iniTermI_PI d L (x - a₁) +
        iniTermI_PI d L (b₁ - x) * iniTermI_PI d L (b₁ - a₁)) ≤
      M₁ * T₁ * ((iniTermI_CW d + iniTermI_CB d) * R ^ 2) * iniTermI_PI d L (b₁ - a₁) := by
    rw [← Finset.mul_sum]
    calc _ ≤ M₁ * T₁ * ((iniTermI_CW d + iniTermI_CB d) * R ^ 2 * iniTermI_PI d L (b₁ - a₁)) :=
          mul_le_mul_of_nonneg_left e1 hM
      _ = _ := by ring
  have e4 : ∑ x ∈ Dset, M₁ * T₁ * (iniTermI_PI d L (b₁ - x) * iniTermI_PI d L (x - a₁) +
        iniTermI_PI d L (b₁ - x) * iniTermI_PI d L (b₁ - a₁)) =
      ∑ x ∈ Finset.univ.filter (fun b₂ => ((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) ≤ R),
        M₁ * T₁ * (iniTermI_PI d L (b₁ - x) * iniTermI_PI d L (x - a₁) +
          iniTermI_PI d L (b₁ - x) * iniTermI_PI d L (b₁ - a₁)) := rfl
  rw [← e4] at *
  have e5 : (Fintype.card (Zd d L) : ℝ) * (M₄ * (2 * Tm)) = (Fintype.card (Zd d L) : ℝ) * (2 * Tm * M₄) := by ring
  rw [e5] at *
  linarith

/-- **`f^{near}`** (`3_5:2163-2171`): the sum over the near labels `b₁` (`|b₁-a₁| ∧ |b₁-a₂| ≤ R'`) is
`≤ K M₁ T₁² R² R'² P(a₁-a₂) + 2 N² T₁ T_m M₄` (`K = 2 (C_W + C_B) C_W`, `N = L^d`). -/
theorem iniTermI_near (hd : 3 ≤ d) {T₁ Tm M₁ M₄ R R' : ℝ} (hR : 1 ≤ R) (hR' : 1 ≤ R') (hT₁ : 0 ≤ T₁) (hTm : 0 ≤ Tm)
    (hM₁ : 0 ≤ M₁) (hM₄ : 0 ≤ M₄) (T : Zd d L → Zd d L → ℂ)
    (hT1 : ∀ x y, ‖T x y‖ ≤ T₁ * iniTermI_PI d L (x - y)) (hTm' : ∀ x y, ‖T x y‖ ≤ Tm)
    (X : Zd d L → Zd d L → ℂ)
    (hX : ∀ b₁ b₂, ‖X b₁ b₂‖ ≤
      (if ((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) ≤ R then M₁ * iniTermI_PI d L (b₁ - b₂) else 0) + M₄)
    (a₀ a₁ : Zd d L) (Q : Zd d L → Prop) [DecidablePred Q]
    (hQ : ∀ b₁, Q b₁ → ((zdistInf d L (b₁ - a₀) : ℕ) : ℝ) ≤ R' ∨ ((zdistInf d L (b₁ - a₁) : ℕ) : ℝ) ≤ R') :
    ‖∑ b₁ ∈ Finset.univ.filter Q, ∑ b₂ : Zd d L, T a₀ b₁ * X b₁ b₂ * (T b₂ a₁ - T b₁ a₁)‖ ≤
      2 * (iniTermI_CW d + iniTermI_CB d) * iniTermI_CW d * M₁ * T₁ ^ 2 * (R ^ 2 * R' ^ 2) * iniTermI_PI d L (a₀ - a₁) +
        2 * (Fintype.card (Zd d L) : ℝ) ^ 2 * T₁ * Tm * M₄ := by
  classical
  set S : Finset (Zd d L) := Finset.univ.filter Q with hS
  set Nd : ℝ := (Fintype.card (Zd d L) : ℝ) with hNd
  set C' : ℝ := iniTermI_CW d + iniTermI_CB d with hC'
  have hC'0 : 0 ≤ C' := add_nonneg (iniTermI_CW_nonneg d) (iniTermI_CB_nonneg d)
  have hPnn : ∀ x : Zd d L, 0 ≤ iniTermI_PI d L x := iniTermI_PI_nonneg
  have hNd0 : 0 ≤ Nd := Nat.cast_nonneg _
  have hpt : ∀ b₁ ∈ S, ‖∑ b₂ : Zd d L, T a₀ b₁ * X b₁ b₂ * (T b₂ a₁ - T b₁ a₁)‖ ≤
      T₁ * iniTermI_PI d L (a₀ - b₁) * (M₁ * T₁ * (C' * R ^ 2) * iniTermI_PI d L (b₁ - a₁) + Nd * (2 * Tm * M₄)) := by
    intro b₁ _
    have hin := iniTermI_near_inner hd hR hT₁ hTm hM₁ hM₄ T hT1 hTm' X hX a₁ b₁
    calc ‖∑ b₂ : Zd d L, T a₀ b₁ * X b₁ b₂ * (T b₂ a₁ - T b₁ a₁)‖
        ≤ ∑ b₂ : Zd d L, ‖T a₀ b₁‖ * (‖X b₁ b₂‖ * ‖T b₂ a₁ - T b₁ a₁‖) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b₂ _ => ?_)
          rw [norm_mul, norm_mul]; ring_nf; exact le_rfl
      _ = ‖T a₀ b₁‖ * ∑ b₂ : Zd d L, ‖X b₁ b₂‖ * ‖T b₂ a₁ - T b₁ a₁‖ := by rw [Finset.mul_sum]
      _ ≤ (T₁ * iniTermI_PI d L (a₀ - b₁)) * (M₁ * T₁ * (C' * R ^ 2) * iniTermI_PI d L (b₁ - a₁) + Nd * (2 * Tm * M₄)) :=
          mul_le_mul (hT1 a₀ b₁) hin (Finset.sum_nonneg fun b₂ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
            (mul_nonneg hT₁ (hPnn _))
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hpt).trans ?_)
  have hexp : ∀ b₁ : Zd d L, T₁ * iniTermI_PI d L (a₀ - b₁) * (M₁ * T₁ * (C' * R ^ 2) * iniTermI_PI d L (b₁ - a₁) +
      Nd * (2 * Tm * M₄)) = M₁ * T₁ ^ 2 * (C' * R ^ 2) * (iniTermI_PI d L (a₀ - b₁) * iniTermI_PI d L (b₁ - a₁)) +
        T₁ * (Nd * (2 * Tm * M₄)) * iniTermI_PI d L (a₀ - b₁) := fun b₁ => by ring
  rw [Finset.sum_congr rfl fun b₁ _ => hexp b₁, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- the label set is covered by two balls
  set N₁ : Finset (Zd d L) := Finset.univ.filter (fun b₁ : Zd d L => ((zdistInf d L (b₁ - a₀) : ℕ) : ℝ) ≤ R') with hN₁
  set N₂ : Finset (Zd d L) := Finset.univ.filter (fun b₁ : Zd d L => ((zdistInf d L (b₁ - a₁) : ℕ) : ℝ) ≤ R') with hN₂
  have hSsub : S ⊆ N₁ ∪ N₂ := by
    intro b₁ hb
    have hh := hQ b₁ (Finset.mem_filter.1 hb).2
    rw [Finset.mem_union, hN₁, hN₂, Finset.mem_filter, Finset.mem_filter]
    rcases hh with h1 | h2
    · exact Or.inl ⟨Finset.mem_univ _, h1⟩
    · exact Or.inr ⟨Finset.mem_univ _, h2⟩
  have hnn : ∀ b₁ : Zd d L, 0 ≤ iniTermI_PI d L (a₀ - b₁) * iniTermI_PI d L (b₁ - a₁) := fun b₁ => mul_nonneg (hPnn _) (hPnn _)
  have hw1 := iniTermI_W2 hd hR' a₀ a₁ N₁ (fun x hx => (Finset.mem_filter.1 hx).2)
  have hw2 := iniTermI_W2 hd hR' a₁ a₀ N₂ (fun x hx => (Finset.mem_filter.1 hx).2)
  have hcw : ∀ a c : Zd d L, 2 ^ (d - 2) * (2 * (iniTermI_CB d * R' ^ 2)) = iniTermI_CW d * R' ^ 2 := fun _ _ => by
    unfold iniTermI_CW; ring
  rw [hcw a₀ a₁] at hw1 hw2
  have hsum2 : ∑ b₁ ∈ N₂, iniTermI_PI d L (a₀ - b₁) * iniTermI_PI d L (b₁ - a₁) =
      ∑ b₁ ∈ N₂, iniTermI_PI d L (a₁ - b₁) * iniTermI_PI d L (b₁ - a₀) :=
    Finset.sum_congr rfl fun b₁ _ => by rw [iniTermI_PI_sub_comm a₀ b₁, iniTermI_PI_sub_comm b₁ a₁, mul_comm]
  have hSsum : ∑ b₁ ∈ S, iniTermI_PI d L (a₀ - b₁) * iniTermI_PI d L (b₁ - a₁) ≤
      2 * (iniTermI_CW d * R' ^ 2) * iniTermI_PI d L (a₀ - a₁) := by
    have h1 : ∑ b₁ ∈ S, iniTermI_PI d L (a₀ - b₁) * iniTermI_PI d L (b₁ - a₁) ≤
        ∑ b₁ ∈ N₁ ∪ N₂, iniTermI_PI d L (a₀ - b₁) * iniTermI_PI d L (b₁ - a₁) :=
      Finset.sum_le_sum_of_subset_of_nonneg hSsub fun b _ _ => hnn b
    have h2 := Finset.sum_union_inter (s₁ := N₁) (s₂ := N₂) (f := fun b₁ => iniTermI_PI d L (a₀ - b₁) * iniTermI_PI d L (b₁ - a₁))
    have h3 : 0 ≤ ∑ b₁ ∈ N₁ ∩ N₂, iniTermI_PI d L (a₀ - b₁) * iniTermI_PI d L (b₁ - a₁) :=
      Finset.sum_nonneg fun b _ => hnn b
    rw [hsum2, iniTermI_PI_sub_comm a₁ a₀] at *
    nlinarith
  have hP1 : ∀ b₁ : Zd d L, iniTermI_PI d L (a₀ - b₁) ≤ 1 := fun b₁ => iniTermI_PI_le_one _
  have hSP : ∑ b₁ ∈ S, iniTermI_PI d L (a₀ - b₁) ≤ Nd := by
    calc ∑ b₁ ∈ S, iniTermI_PI d L (a₀ - b₁) ≤ ∑ b₁ ∈ S, (1 : ℝ) := Finset.sum_le_sum fun b _ => hP1 b
      _ = S.card := by simp
      _ ≤ Nd := by
          rw [hNd]; exact_mod_cast (Finset.card_le_univ S)
  have hK : 0 ≤ M₁ * T₁ ^ 2 * (C' * R ^ 2) := by positivity
  have hK2 : 0 ≤ T₁ * (Nd * (2 * Tm * M₄)) := by positivity
  calc M₁ * T₁ ^ 2 * (C' * R ^ 2) * ∑ b₁ ∈ S, iniTermI_PI d L (a₀ - b₁) * iniTermI_PI d L (b₁ - a₁) +
        T₁ * (Nd * (2 * Tm * M₄)) * ∑ b₁ ∈ S, iniTermI_PI d L (a₀ - b₁)
      ≤ M₁ * T₁ ^ 2 * (C' * R ^ 2) * (2 * (iniTermI_CW d * R' ^ 2) * iniTermI_PI d L (a₀ - a₁)) +
        T₁ * (Nd * (2 * Tm * M₄)) * Nd :=
        add_le_add (mul_le_mul_of_nonneg_left hSsum hK) (mul_le_mul_of_nonneg_left hSP hK2)
    _ = _ := by rw [hC']; ring

end Near

/-! ### 12. Outside the window `(eq:ells_to_ellt2)` the whole term is a `W^{-D}` -/

section Tail3

variable {d L : ℕ} [NeZero L]

/-- `|a₁-a₂| > 2 r₁ + Y₀` forces, for every pair of labels `(b₁,b₂)`, `|b₁-a₁| > r₁` or `|b₂-a₂| > r₁` (decay of `Θ`) or
`|b₁-b₂| > Y₀` (decay of `𝓑`): `|S| ≤ (1-s)² N² (2 E₀ T_m X_m + T_m² X_t)`. -/
theorem iniTermI_tail {g s u Tm Xm Xt E₀ r₁ Y₀ : ℝ} (hTm : 0 ≤ Tm) (hXm : 0 ≤ Xm) (hXt : 0 ≤ Xt) (hE₀ : 0 ≤ E₀)
    (hT : ∀ x y : Zd d L, ‖Theta d L g (u : ℂ) x y‖ ≤ Tm)
    (hTd : ∀ x y : Zd d L, r₁ < ((zdistInf d L (y - x) : ℕ) : ℝ) → ‖Theta d L g (u : ℂ) x y‖ ≤ E₀)
    (X : (Fin 2 → Zd d L) → ℂ) (hX : ∀ b, ‖X b‖ ≤ Xm)
    (hXd : ∀ b, Y₀ < ((zdistInf d L (b 0 - b 1) : ℕ) : ℝ) → ‖X b‖ ≤ Xt) (a : Fin 2 → Zd d L)
    (hr : 2 * r₁ + Y₀ < ((zdistInf d L (a 0 - a 1) : ℕ) : ℝ)) :
    ‖iniTermI_Sfull d L g s u X a‖ ≤ (1 - s) ^ 2 * ((Fintype.card (Zd d L) : ℝ) ^ 2 * (2 * E₀ * Tm * Xm + Tm ^ 2 * Xt)) := by
  unfold iniTermI_Sfull
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  have hpt : ∀ b₁ b₂ : Zd d L, ‖Theta d L g (u : ℂ) (a 0) b₁ * Theta d L g (u : ℂ) (a 1) b₂ * X ![b₁, b₂]‖ ≤
      2 * E₀ * Tm * Xm + Tm ^ 2 * Xt := by
    intro b₁ b₂
    rw [norm_mul, norm_mul]
    have h1 := hT (a 0) b₁
    have h2 := hT (a 1) b₂
    have h3 := hX ![b₁, b₂]
    have n1 := norm_nonneg (Theta d L g (u : ℂ) (a 0) b₁)
    have n2 := norm_nonneg (Theta d L g (u : ℂ) (a 1) b₂)
    have n3 := norm_nonneg (X ![b₁, b₂])
    have htri : ((zdistInf d L (a 0 - a 1) : ℕ) : ℝ) ≤ ((zdistInf d L (b₁ - a 0) : ℕ) : ℝ) +
        ((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) + ((zdistInf d L (b₂ - a 1) : ℕ) : ℝ) := by
      exact_mod_cast iniTermI_tri (a 0) (a 1) b₁ b₂
    by_cases c1 : r₁ < ((zdistInf d L (b₁ - a 0) : ℕ) : ℝ)
    · have := hTd (a 0) b₁ c1
      calc ‖Theta d L g (u : ℂ) (a 0) b₁‖ * ‖Theta d L g (u : ℂ) (a 1) b₂‖ * ‖X ![b₁, b₂]‖ ≤ E₀ * Tm * Xm := by gcongr
        _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hE₀ hTm) hXm, mul_nonneg (sq_nonneg Tm) hXt]
    by_cases c2 : r₁ < ((zdistInf d L (b₂ - a 1) : ℕ) : ℝ)
    · have := hTd (a 1) b₂ c2
      calc ‖Theta d L g (u : ℂ) (a 0) b₁‖ * ‖Theta d L g (u : ℂ) (a 1) b₂‖ * ‖X ![b₁, b₂]‖ ≤ Tm * E₀ * Xm := by gcongr
        _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hE₀ hTm) hXm, mul_nonneg (sq_nonneg Tm) hXt]
    have c3 : Y₀ < ((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) := by
      by_contra hc
      push Not at c1 c2 hc
      linarith
    have := hXd ![b₁, b₂] (by simpa using c3)
    calc ‖Theta d L g (u : ℂ) (a 0) b₁‖ * ‖Theta d L g (u : ℂ) (a 1) b₂‖ * ‖X ![b₁, b₂]‖ ≤ Tm * Tm * Xt := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hE₀ hTm) hXm, mul_nonneg (sq_nonneg Tm) hXt]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun b₁ _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun b₂ _ => hpt b₁ b₂)).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact le_of_eq (by ring)

end Tail3

/-! ### 13. The hypotheses of `STIngR5` restrict from `[s,t]` to `[s,t']` -/

section Restrict

variable {d : ℕ} (sz : Sizes d)

theorem iniTermI_prec_restrict {U V : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ} {ξ' ζ' : ∀ n, V n → sz.SeqΩ → ℝ}
    (h : sz.Prec ξ ζ) (φ : ∀ n, V n → U n) (hξ : ∀ n v ω, ξ' n v ω = ξ n (φ n v) ω)
    (hζ : ∀ n v ω, ζ' n v ω = ζ n (φ n v) ω) : sz.Prec ξ' ζ' := by
  have h' := StochDomAt.precomp_param h φ
  have e1 : ξ' = fun n v ω => ξ n (φ n v) ω := by funext n v ω; exact hξ n v ω
  have e2 : ζ' = fun n v ω => ζ n (φ n v) ω := by funext n v ω; exact hζ n v ω
  rw [e1, e2]; exact h'

/-- The reindexing `[s,t'] → [s,t]` of the time index. -/
def iniTermI_inc {s t t' : ℕ → ℝ} (ht' : ∀ n, t' n ≤ t n) (n : ℕ) (u : TimeIcc s t' n) : TimeIcc s t n :=
  ⟨u.1, u.2.1, u.2.2.trans (ht' n)⟩

/-- **The hypotheses of `STIngR5` at `(s,t')`, `s < t' ≤ t`** (reusable by S5-15): the regime `STReg5I` (`1-t' ≥ 1-t`), `(con_st_ind)`
(`Bctl(t')^{𝔠_d} ≤ Bctl(t)^{𝔠_d} ≤ (1-t)/(1-s) ≤ (1-t')/(1-s) < 1`, `STBctl_mono`), and the five `Prec` over `u ∈ [s,t]` of Steps 1-4
(each has the index `u ∈ [s,t]` and the time `s`, never `t`: `StochDomAt.precomp_param` along `[s,t'] ⊂ [s,t]`). -/
theorem stIngR5_hyps_restrict {E s t t' : ℕ → ℝ} {𝔠d Cd : ℝ} (h𝔠d : 0 < 𝔠d)
    (hst' : ∀ n, s n < t' n) (ht' : ∀ n, t' n ≤ t n) (ht1 : ∀ n, t n < 1)
    (hR : STReg5I sz s t) (hCon : STConStInd sz 𝔠d s t) (hS1 : STStep1Loop sz E s t)
    (hS2 : STStep2Concl sz E s t Cd) (hLmax : STLmaxU sz E s t) (hLKU : STLKU sz E s t) :
    STReg5I sz s t' ∧ STConStInd sz 𝔠d s t' ∧ STStep1Loop sz E s t' ∧ STStep2Concl sz E s t' Cd ∧
      STLmaxU sz E s t' ∧ STLKU sz E s t' := by
  refine ⟨fun n => ⟨(hR n).1.trans (by linarith [ht' n]), (hR n).2⟩, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hCon] with n hn
    obtain ⟨h1, h2⟩ := hn
    have hs0 : 0 < 1 - s n := by linarith [hst' n, ht1 n, ht' n]
    have hB : sz.Bctl n (t' n) ≤ sz.Bctl n (t n) := STBctl_mono sz n (ht' n) (ht1 n)
    have hB0 : 0 ≤ sz.Bctl n (t' n) := (st_Bctl_pos sz (lt_of_le_of_lt (ht' n) (ht1 n))).le
    refine ⟨((Real.rpow_le_rpow hB0 hB h𝔠d.le).trans h1).trans ?_, ?_⟩
    · exact div_le_div_of_nonneg_right (by linarith [ht' n]) hs0.le
    · rw [div_lt_one hs0]; linarith [hst' n]
  · intro k hk
    exact iniTermI_prec_restrict sz (hS1 k hk) (fun n p => (iniTermI_inc ht' n p.1, p.2)) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  · obtain ⟨h1, h2, h3⟩ := hS2
    exact ⟨iniTermI_prec_restrict sz h1 (fun n p => (iniTermI_inc ht' n p.1, p.2)) (fun _ _ _ => rfl) (fun _ _ _ => rfl),
      iniTermI_prec_restrict sz h2 (fun n p => (iniTermI_inc ht' n p.1, p.2)) (fun _ _ _ => rfl) (fun _ _ _ => rfl),
      fun D hD => iniTermI_prec_restrict sz (h3 D hD) (fun n p => (iniTermI_inc ht' n p.1, p.2)) (fun _ _ _ => rfl) (fun _ _ _ => rfl)⟩
  · intro k hk
    exact iniTermI_prec_restrict sz (hLmax k hk) (fun n p => (iniTermI_inc ht' n p.1, p.2)) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  · intro k hk
    exact iniTermI_prec_restrict sz (hLKU k hk) (fun n p => (iniTermI_inc ht' n p.1, p.2)) (fun _ _ _ => rfl) (fun _ _ _ => rfl)

end Restrict

/-! ### 14. The `u`-dependence of `f^{far}`: Lipschitz in `u`, the grid, and the bridge `STfFar = iniTermI_fSum` -/

section Lip

variable {d L : ℕ} [NeZero L]

open scoped Matrix.Norms.Operator in
theorem iniTermI_entry_le (M : Matrix (Zd d L) (Zd d L) ℂ) (x y : Zd d L) : ‖M x y‖ ≤ ‖M‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h1 : ‖M x y‖₊ ≤ ∑ j, ‖M x j‖₊ :=
    Finset.single_le_sum (f := fun j => ‖M x j‖₊) (fun _ _ => zero_le) (Finset.mem_univ y)
  have h2 : ∑ j, ‖M x j‖₊ ≤ Finset.univ.sup (fun i => ∑ j, ‖M i j‖₊) :=
    Finset.le_sup (f := fun i => ∑ j, ‖M i j‖₊) (Finset.mem_univ x)
  exact_mod_cast h1.trans h2

/-- Entrywise bounds `|Θ_{v,xy}| ≤ (1-v)⁻¹`. -/
theorem iniTermI_Theta_le {g v : ℝ} (hL : 3 ≤ L) (hv0 : 0 ≤ v) (hv : v < 1) (x y : Zd d L) :
    ‖Theta d L g (v : ℂ) x y‖ ≤ (1 - v)⁻¹ :=
  (Finset.single_le_sum (f := fun b => ‖Theta d L g (v : ℂ) x b‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ y)).trans (iniTermI_row hL hv0 hv x)

open scoped Matrix.Norms.Operator in
/-- The resolvent identity gives `|Θ_{v,xy} - Θ_{v',xy}| ≤ |v-v'| (1-t)⁻²` for `v, v' ≤ t < 1`. -/
theorem iniTermI_Theta_lip {g v v' t : ℝ} (hL : 3 ≤ L) (hv0 : 0 ≤ v) (hv : v ≤ t) (hv0' : 0 ≤ v') (hv' : v' ≤ t)
    (ht : t < 1) (x y : Zd d L) :
    ‖Theta d L g (v : ℂ) x y - Theta d L g (v' : ℂ) x y‖ ≤ |v - v'| * ((1 - t)⁻¹) ^ 2 := by
  have hξ : ‖(v' : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hv0']; linarith
  have hζ : ‖(v : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hv0]; linarith
  have h := Theta_sub_Theta (d := d) (L := L) (g := g) (norm_SB d L g hL) hξ hζ
  have hentry : Theta d L g (v : ℂ) x y - Theta d L g (v' : ℂ) x y =
      ((v : ℂ) - v') * (Theta d L g (v : ℂ) * SB d L g * Theta d L g (v' : ℂ)) x y := by
    have := congrFun (congrFun h x) y
    simpa [Matrix.sub_apply, Matrix.smul_apply] using this
  rw [hentry, norm_mul, show ((v : ℂ) - v') = ((v - v' : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs]
  have hn1 : ‖Theta d L g (v : ℂ)‖ ≤ (1 - v)⁻¹ := by
    have := norm_Theta_le (d := d) (L := L) (g := g) hL hv0 (by linarith : v < 1) (m := 1) (by simp)
    simpa using this
  have hn2 : ‖Theta d L g (v' : ℂ)‖ ≤ (1 - v')⁻¹ := by
    have := norm_Theta_le (d := d) (L := L) (g := g) hL hv0' (by linarith : v' < 1) (m := 1) (by simp)
    simpa using this
  have ht0 : 0 < 1 - t := by linarith
  have e1 : (1 - v)⁻¹ ≤ (1 - t)⁻¹ := inv_anti₀ ht0 (by linarith)
  have e2 : (1 - v')⁻¹ ≤ (1 - t)⁻¹ := inv_anti₀ ht0 (by linarith)
  have hm : ‖(Theta d L g (v : ℂ) * SB d L g * Theta d L g (v' : ℂ)) x y‖ ≤ ((1 - t)⁻¹) ^ 2 := by
    refine (iniTermI_entry_le _ x y).trans ?_
    calc ‖Theta d L g (v : ℂ) * SB d L g * Theta d L g (v' : ℂ)‖
        ≤ ‖Theta d L g (v : ℂ) * SB d L g‖ * ‖Theta d L g (v' : ℂ)‖ := norm_mul_le _ _
      _ ≤ (‖Theta d L g (v : ℂ)‖ * ‖SB d L g‖) * ‖Theta d L g (v' : ℂ)‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ = ‖Theta d L g (v : ℂ)‖ * ‖Theta d L g (v' : ℂ)‖ := by rw [norm_SB d L g hL, mul_one]
      _ ≤ (1 - t)⁻¹ * (1 - t)⁻¹ :=
          mul_le_mul (hn1.trans e1) (hn2.trans e2) (norm_nonneg _) (inv_nonneg.2 ht0.le)
      _ = _ := by ring
  exact mul_le_mul_of_nonneg_left hm (abs_nonneg _)

/-- **Lipschitz continuity of `f_a` in the propagator time** (`|X| ≤ X_m`, `v, v' ≤ t`): `|f_v - f_{v'}| ≤ 4 N² T_m³ |v-v'| X_m`,
`T_m = (1-t)⁻¹`, `N = L^d`.  (The label set `P` does not depend on `v`.) -/
theorem iniTermI_fSum_lip {g s v v' t Xm : ℝ} (hL : 3 ≤ L) (hs0 : 0 ≤ s) (hs : s ≤ 1) (hv0 : 0 ≤ v) (hv : v ≤ t)
    (hv0' : 0 ≤ v') (hv' : v' ≤ t) (ht : t < 1) (X : (Fin 2 → Zd d L) → ℂ) (hX : ∀ b, ‖X b‖ ≤ Xm)
    (a : Fin 2 → Zd d L) (P : Zd d L → Prop) [DecidablePred P] :
    ‖iniTermI_fSum d L g s v X a P - iniTermI_fSum d L g s v' X a P‖ ≤
      4 * (Fintype.card (Zd d L) : ℝ) ^ 2 * ((1 - t)⁻¹) ^ 3 * |v - v'| * Xm := by
  have ht0 : 0 < 1 - t := by linarith
  set Tm : ℝ := (1 - t)⁻¹ with hTm
  have hTm0 : 0 ≤ Tm := inv_nonneg.2 ht0.le
  set Δ : ℝ := |v - v'| * Tm ^ 2 with hΔ
  have hXm : 0 ≤ Xm := (norm_nonneg _).trans (hX (fun _ => 0))
  have hΔ0 : 0 ≤ Δ := by positivity
  have hT : ∀ w : ℝ, 0 ≤ w → w ≤ t → ∀ x y : Zd d L, ‖Theta d L g (w : ℂ) x y‖ ≤ Tm := fun w hw0 hw x y =>
    (iniTermI_Theta_le hL hw0 (by linarith) x y).trans (inv_anti₀ ht0 (by linarith))
  have hD : ∀ x y : Zd d L, ‖Theta d L g (v : ℂ) x y - Theta d L g (v' : ℂ) x y‖ ≤ Δ := fun x y =>
    iniTermI_Theta_lip hL hv0 hv hv0' hv' ht x y
  unfold iniTermI_fSum
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  have h1s : (1 - s) ^ 2 ≤ 1 := by nlinarith
  have hcard : ((Finset.univ.filter P).card : ℝ) ≤ (Fintype.card (Zd d L) : ℝ) := by
    exact_mod_cast Finset.card_le_univ _
  rw [← Finset.sum_sub_distrib]
  have hbd : ‖∑ b₁ ∈ Finset.univ.filter P, (∑ b₂ : Zd d L, Theta d L g (v : ℂ) (a 0) b₁ * X ![b₁, b₂] *
        (Theta d L g (v : ℂ) b₂ (a 1) - Theta d L g (v : ℂ) b₁ (a 1)) -
      ∑ b₂ : Zd d L, Theta d L g (v' : ℂ) (a 0) b₁ * X ![b₁, b₂] *
        (Theta d L g (v' : ℂ) b₂ (a 1) - Theta d L g (v' : ℂ) b₁ (a 1)))‖ ≤
      (Fintype.card (Zd d L) : ℝ) * ((Fintype.card (Zd d L) : ℝ) * (4 * Δ * Tm * Xm)) := by
    refine (norm_sum_le _ _).trans ?_
    have hpt : ∀ b₁ ∈ Finset.univ.filter P, ‖∑ b₂ : Zd d L, Theta d L g (v : ℂ) (a 0) b₁ * X ![b₁, b₂] *
        (Theta d L g (v : ℂ) b₂ (a 1) - Theta d L g (v : ℂ) b₁ (a 1)) -
      ∑ b₂ : Zd d L, Theta d L g (v' : ℂ) (a 0) b₁ * X ![b₁, b₂] *
        (Theta d L g (v' : ℂ) b₂ (a 1) - Theta d L g (v' : ℂ) b₁ (a 1))‖ ≤
        (Fintype.card (Zd d L) : ℝ) * (4 * Δ * Tm * Xm) := by
      intro b₁ _
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      have hpt2 : ∀ b₂ ∈ (Finset.univ : Finset (Zd d L)), ‖Theta d L g (v : ℂ) (a 0) b₁ * X ![b₁, b₂] *
          (Theta d L g (v : ℂ) b₂ (a 1) - Theta d L g (v : ℂ) b₁ (a 1)) -
          Theta d L g (v' : ℂ) (a 0) b₁ * X ![b₁, b₂] *
          (Theta d L g (v' : ℂ) b₂ (a 1) - Theta d L g (v' : ℂ) b₁ (a 1))‖ ≤ 4 * Δ * Tm * Xm := by
        intro b₂ _
        have e : Theta d L g (v : ℂ) (a 0) b₁ * X ![b₁, b₂] *
            (Theta d L g (v : ℂ) b₂ (a 1) - Theta d L g (v : ℂ) b₁ (a 1)) -
            Theta d L g (v' : ℂ) (a 0) b₁ * X ![b₁, b₂] *
            (Theta d L g (v' : ℂ) b₂ (a 1) - Theta d L g (v' : ℂ) b₁ (a 1)) =
            (Theta d L g (v : ℂ) (a 0) b₁ - Theta d L g (v' : ℂ) (a 0) b₁) * X ![b₁, b₂] *
              (Theta d L g (v : ℂ) b₂ (a 1) - Theta d L g (v : ℂ) b₁ (a 1)) +
            Theta d L g (v' : ℂ) (a 0) b₁ * X ![b₁, b₂] *
              ((Theta d L g (v : ℂ) b₂ (a 1) - Theta d L g (v' : ℂ) b₂ (a 1)) -
                (Theta d L g (v : ℂ) b₁ (a 1) - Theta d L g (v' : ℂ) b₁ (a 1))) := by ring
        rw [e]
        refine (norm_add_le _ _).trans ?_
        have hr1 : ‖Theta d L g (v : ℂ) b₂ (a 1) - Theta d L g (v : ℂ) b₁ (a 1)‖ ≤ 2 * Tm :=
          (norm_sub_le _ _).trans (by have := hT v hv0 hv b₂ (a 1); have := hT v hv0 hv b₁ (a 1); linarith)
        have hr2 : ‖(Theta d L g (v : ℂ) b₂ (a 1) - Theta d L g (v' : ℂ) b₂ (a 1)) -
            (Theta d L g (v : ℂ) b₁ (a 1) - Theta d L g (v' : ℂ) b₁ (a 1))‖ ≤ 2 * Δ :=
          (norm_sub_le _ _).trans (by have := hD b₂ (a 1); have := hD b₁ (a 1); linarith)
        have hx := hX ![b₁, b₂]
        have n1 := norm_nonneg (X ![b₁, b₂])
        have a1 : ‖(Theta d L g (v : ℂ) (a 0) b₁ - Theta d L g (v' : ℂ) (a 0) b₁) * X ![b₁, b₂] *
            (Theta d L g (v : ℂ) b₂ (a 1) - Theta d L g (v : ℂ) b₁ (a 1))‖ ≤ Δ * Xm * (2 * Tm) := by
          rw [norm_mul, norm_mul]
          exact mul_le_mul (mul_le_mul (hD _ _) hx n1 hΔ0) hr1 (norm_nonneg _) (by positivity)
        have a2 : ‖Theta d L g (v' : ℂ) (a 0) b₁ * X ![b₁, b₂] *
            ((Theta d L g (v : ℂ) b₂ (a 1) - Theta d L g (v' : ℂ) b₂ (a 1)) -
              (Theta d L g (v : ℂ) b₁ (a 1) - Theta d L g (v' : ℂ) b₁ (a 1)))‖ ≤ Tm * Xm * (2 * Δ) := by
          rw [norm_mul, norm_mul]
          exact mul_le_mul (mul_le_mul (hT v' hv0' hv' _ _) hx n1 hTm0) hr2 (norm_nonneg _) (by positivity)
        nlinarith [a1, a2]
      refine (Finset.sum_le_sum hpt2).trans ?_
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact le_rfl
    refine (Finset.sum_le_sum hpt).trans ?_
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard (by positivity)
  calc (1 - s) ^ 2 * ‖_‖ ≤ 1 * ((Fintype.card (Zd d L) : ℝ) * ((Fintype.card (Zd d L) : ℝ) * (4 * Δ * Tm * Xm))) :=
        mul_le_mul h1s hbd (norm_nonneg _) zero_le_one
    _ = _ := by rw [hΔ]; ring

/-- A grid in `[s,t]`: for `u ∈ [s,t]` there is `k ∈ [1,M]` with `u ≤ s_k ≤ u + δ`, `s_k = s + k (t-s)/M`, `δ = (t-s)/M`. -/
theorem iniTermI_grid {s t u : ℝ} (hst : s < t) (hu : s ≤ u) (hut : u ≤ t) (M : ℕ) (hM : 1 ≤ M) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ M ∧ u ≤ s + (k : ℝ) * ((t - s) / M) ∧ s + (k : ℝ) * ((t - s) / M) ≤ u + (t - s) / M := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hδ : 0 < (t - s) / M := div_pos (by linarith) hM0
  set x : ℝ := (u - s) / ((t - s) / M) with hx
  have hx0 : 0 ≤ x := div_nonneg (by linarith) hδ.le
  have hxM : x ≤ M := by
    rw [hx, div_le_iff₀ hδ]
    have : (M : ℝ) * ((t - s) / M) = t - s := by field_simp
    linarith
  have hux : u = s + x * ((t - s) / M) := by
    have : x * ((t - s) / M) = u - s := by rw [hx]; exact div_mul_cancel₀ _ hδ.ne'
    linarith
  refine ⟨max 1 ⌈x⌉₊, le_max_left _ _, max_le hM (Nat.ceil_le.2 hxM), ?_, ?_⟩
  · have : x ≤ (max 1 ⌈x⌉₊ : ℕ) := (Nat.le_ceil x).trans (by exact_mod_cast le_max_right 1 ⌈x⌉₊)
    rw [hux]; nlinarith
  · rcases le_total 1 ⌈x⌉₊ with h | h
    · rw [max_eq_right h]
      have := Nat.ceil_lt_add_one hx0
      rw [hux]; nlinarith
    · rw [max_eq_left h]; push_cast; linarith

end Lip

/-! ### 15. `f^{far}` uniformly in `u ∈ [s,t]` -/

section Unif

variable {d : ℕ} (sz : Sizes d)

/-- The index set of `STCltFarConcl` at the propagator time `v` (`(eq:ells_to_ellt)`, `(eq:ells_to_ellt2)` with `ℓ_t ↦ ℓ_v`). -/
def STCltFarIdx (s : ℕ → ℝ) (n : ℕ) (v : ℝ) : Type :=
  {p : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)) //
    Real.log ((sz.W n : ℕ) : ℝ) ^ 5 * ellT (sz.L n) (sz.lam n) (s n) ≤ ellT (sz.L n) (sz.lam n) v ∧
      ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ≤
        (1 / 2 : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) v +
          Real.log ((sz.W n : ℕ) : ℝ) ^ (5 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) (s n)}

/-- The control of `lem;CLT`. -/
def STCltFarZeta (n : ℕ) (a : Fin 2 → Zd d (sz.L n)) : ℝ :=
  (STAI sz n) ^ (-(6 / 5) : ℝ) / (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1)

/-- **`lem;CLT` uniformly in `u ∈ [s,t]`** (the union over `u` inside `P`): `f^{far}` at the propagator time `u`, on the index set
of `STCltFarConcl` with `ℓ_t` replaced by `ℓ_u` (`(eq:ells_to_ellt)`, `(eq:ells_to_ellt2)` at `u`).  Paper-delta candidate `T2329b`:
`3_5:2173` states `lem;CLT` at the end time only; the use in `(iksjuwjx)` is for every `u ∈ [s,t]`. -/
def STCltFarUConcl (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => Σ u : TimeIcc s t n, STCltFarIdx sz s n (u : ℝ))
    (fun n q ω => ‖STfFar sz n (E n) (s n) (q.1 : ℝ) q.2.1.1.1 q.2.1.2 ω‖)
    (fun n q _ => STCltFarZeta sz n q.2.1.2)

open Classical in
/-- The failure event of `lem;CLT` at the propagator time `v`. -/
def iniTermI_cltBad (E s : ℕ → ℝ) (τ : ℝ) (n : ℕ) (v : ℝ) : Set sz.SeqΩ :=
  {ω | ∃ p : STCltFarIdx sz s n v, ((sz.size n : ℕ) : ℝ) ^ τ * STCltFarZeta sz n p.1.2 <
    ‖STfFar sz n (E n) (s n) v p.1.1.1 p.1.2 ω‖}

/-- For mixed `σ`, `m(σ₁) m(σ₂) = 1`, so `f^{far}` is the generic `iniTermI_fSum` on the far label set. -/
theorem iniTermI_STfFar_eq (n : ℕ) {E s v : ℝ} (hE : |E| ≤ 2) {σ : Fin 2 → Bool} (hσ : σ 0 ≠ σ 1)
    (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    haveI := Classical.decPred (fun b₁ : Zd d (sz.L n) =>
      Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 0) : ℕ) : ℝ) ∧
        Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 1) : ℕ) : ℝ))
    STfFar sz n E s v σ a ω = iniTermI_fSum d (sz.L n) (sz.lam n) s v
      (fun b => STLKM sz n E s (sz.seqHflow n s ω) σ b) a
      (fun b₁ => Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 0) : ℕ) : ℝ) ∧
        Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 1) : ℕ) : ℝ)) := by
  have hm1 : mE E * (starRingEnd ℂ) (mE E) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mE hE]; simp
  have hm : STmsig E (σ 0) * STmsig E (σ 1) = 1 := by
    unfold STmsig
    cases h0 : σ 0 <;> cases h1 : σ 1 <;> simp_all [mul_comm]
  unfold STfFar iniTermI_fSum
  simp only [hm, mul_one]
  congr

theorem iniTermI_STfFar_lip (n : ℕ) {E s u v t Xm : ℝ} (hE : |E| ≤ 2) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hu0 : 0 ≤ u) (hut : u ≤ t)
    (hv0 : 0 ≤ v) (hvt : v ≤ t) (ht : t < 1) {σ : Fin 2 → Bool} (hσ : σ 0 ≠ σ 1) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ)
    (hX : ∀ b, ‖STLKM sz n E s (sz.seqHflow n s ω) σ b‖ ≤ Xm) :
    ‖STfFar sz n E s u σ a ω - STfFar sz n E s v σ a ω‖ ≤
      4 * (Fintype.card (Zd d (sz.L n)) : ℝ) ^ 2 * ((1 - t)⁻¹) ^ 3 * |u - v| * Xm := by
  rw [iniTermI_STfFar_eq sz n hE hσ, iniTermI_STfFar_eq sz n hE hσ]
  exact @iniTermI_fSum_lip d (sz.L n) _ _ _ _ _ _ _ (sz.three_le_L n) hs0 hs1 hu0 hut hv0 hvt ht _ hX a _ (Classical.decPred _)

/-- `W^{-d} B_{s,0} ≤ 2 (ilambda² W^d)⁻¹` for `1 - s ≥ ilambda²/L^d`. -/
theorem iniTermI_Bctl_le (n : ℕ) {s : ℝ} (hg : 0 < sz.lam n) (hs : s < 1)
    (hlow : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - s) : sz.Bctl n s ≤ 2 * (STAI sz n)⁻¹ := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega)
  have hs0 : 0 < 1 - s := by linarith
  have hg2 : 0 < sz.lam n ^ 2 := by positivity
  have hLd : sz.lam n ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ d * (1 - s) := by
    rw [div_le_iff₀ (by positivity)] at hlow; linarith
  unfold Sizes.Bctl Bparam STAI
  rw [abs_of_pos hs0]
  have h0 : (((0 : ℕ) : ℝ) + 1) ^ (d - 2) = 1 := by simp
  rw [h0, inv_one, mul_one]
  have h1 : (sz.lam n ^ 2 + (1 - s))⁻¹ ≤ (sz.lam n ^ 2)⁻¹ := inv_anti₀ hg2 (by linarith)
  have h2 : (((sz.L n : ℕ) : ℝ) ^ d * (1 - s))⁻¹ ≤ (sz.lam n ^ 2)⁻¹ := inv_anti₀ hg2 hLd
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - s))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - s))⁻¹)
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2)⁻¹ + (sz.lam n ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
    _ = 2 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by rw [mul_inv]; ring

/-- `(1-t)⁻¹ ≤ N²` in regime (i): `(1-t)⁻¹ ≤ L²/ilambda² ≤ L² W^d`, `ilambda² W^d ≥ 1`. -/
theorem iniTermI_oneSub_inv_le (hd : 3 ≤ d) (n : ℕ) {t : ℝ} (hA1 : 1 ≤ STAI sz n) (hg : 0 < sz.lam n)
    (hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t) : (1 - t)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ 2 := by
  have hW : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hg2 : 0 < sz.lam n ^ 2 := by positivity
  have hpos : 0 < sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by positivity
  have h1 : (1 - t)⁻¹ ≤ (sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)⁻¹ := inv_anti₀ hpos hreg
  have h2 : (sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)⁻¹ = ((sz.L n : ℕ) : ℝ) ^ 2 * (sz.lam n ^ 2)⁻¹ := by
    rw [inv_div, div_eq_mul_inv, mul_comm]
  have h3 : (sz.lam n ^ 2)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ d := by
    unfold STAI at hA1
    calc (sz.lam n ^ 2)⁻¹ = (sz.lam n ^ 2)⁻¹ * 1 := by rw [mul_one]
      _ ≤ (sz.lam n ^ 2)⁻¹ * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) :=
          mul_le_mul_of_nonneg_left hA1 (inv_nonneg.2 hg2.le)
      _ = _ := by field_simp
  have hL2 : ((sz.L n : ℕ) : ℝ) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) := by
    have : (sz.L n) ^ 2 ≤ (sz.W n * sz.L n) ^ d :=
      (Nat.pow_le_pow_right (by have := sz.three_le_L n; omega) (by omega : 2 ≤ d)).trans
        (Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d)
    unfold Sizes.size
    exact_mod_cast this
  have hWd : ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
    have : (sz.W n) ^ d ≤ (sz.W n * sz.L n) ^ d :=
      Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by have := sz.three_le_L n; omega)) d
    unfold Sizes.size
    exact_mod_cast this
  calc (1 - t)⁻¹ ≤ _ := h1
    _ = _ := h2
    _ ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) :=
        mul_le_mul hL2 (h3.trans hWd) (by positivity) (by positivity)
    _ = _ := by ring

/-- `N^{-3} ≤ ζ = A^{-6/5}/(r^{d-2}+1)` once `2 (𝔡^{-2})^{6/5} ≤ N^{4/5}`: `A ≤ 𝔡^{-2} N`, `r^{d-2}+1 ≤ 2N`. -/
theorem iniTermI_zeta_ge (hd : 3 ≤ d) (n : ℕ) {𝔡 : ℝ} (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ 𝔡⁻¹)
    (hA1 : 1 ≤ STAI sz n) (hbig : 2 * (𝔡⁻¹ ^ 2) ^ (6 / 5 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (4 / 5 : ℝ))
    (a : Fin 2 → Zd d (sz.L n)) : ((sz.size n : ℕ) : ℝ) ^ (-(3 : ℝ)) ≤ STCltFarZeta sz n a := by
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by linarith
  have hA0 : 0 < STAI sz n := lt_of_lt_of_le one_pos hA1
  have hWd : ((sz.W n : ℕ) : ℝ) ^ d ≤ N := by
    have : (sz.W n) ^ d ≤ (sz.W n * sz.L n) ^ d :=
      Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by have := sz.three_le_L n; omega)) d
    rw [hN]; unfold Sizes.size; exact_mod_cast this
  have hAN : STAI sz n ≤ 𝔡⁻¹ ^ 2 * N := by
    unfold STAI
    exact mul_le_mul (pow_le_pow_left₀ hg.le hgΛ 2) hWd (by positivity) (by positivity)
  have hκ0 : 0 ≤ 𝔡⁻¹ ^ 2 := by positivity
  have hA65 : STAI sz n ^ (6 / 5 : ℝ) ≤ (𝔡⁻¹ ^ 2) ^ (6 / 5 : ℝ) * N ^ (6 / 5 : ℝ) :=
    calc STAI sz n ^ (6 / 5 : ℝ) ≤ (𝔡⁻¹ ^ 2 * N) ^ (6 / 5 : ℝ) := Real.rpow_le_rpow hA0.le hAN (by norm_num)
      _ = _ := Real.mul_rpow hκ0 hN0.le
  have hr : (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) ^ (d - 2) + 1 ≤ 2 * N := by
    have hrL : ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
      exact_mod_cast st5_zdistInf_le sz n _
    have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
    have h1 : (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) ^ (d - 2) ≤ ((sz.L n : ℕ) : ℝ) ^ d :=
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hrL _).trans (pow_le_pow_right₀ hL1 (by omega))
    have h2 : ((sz.L n : ℕ) : ℝ) ^ d ≤ N := by
      have : (sz.L n) ^ d ≤ (sz.W n * sz.L n) ^ d :=
        Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
      rw [hN]; unfold Sizes.size; exact_mod_cast this
    linarith
  have hX0 : 0 < (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) ^ (d - 2) + 1 := by positivity
  unfold STCltFarZeta
  have e3 : N ^ (-(3 : ℝ)) = (N ^ 3)⁻¹ := by
    rw [Real.rpow_neg hN0.le]; congr 1; exact_mod_cast Real.rpow_natCast N 3
  rw [e3, Real.rpow_neg hA0.le, div_eq_mul_inv, ← mul_inv]
  refine inv_anti₀ (by positivity) ?_
  have e2 : N ^ (4 / 5 : ℝ) * N ^ (6 / 5 : ℝ) = N ^ 2 := by
    rw [← Real.rpow_add hN0]; norm_num
  calc STAI sz n ^ (6 / 5 : ℝ) * ((((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) ^ (d - 2) + 1)
      ≤ ((𝔡⁻¹ ^ 2) ^ (6 / 5 : ℝ) * N ^ (6 / 5 : ℝ)) * (2 * N) := mul_le_mul hA65 hr hX0.le (by positivity)
    _ = (2 * (𝔡⁻¹ ^ 2) ^ (6 / 5 : ℝ)) * (N ^ (6 / 5 : ℝ) * N) := by ring
    _ ≤ N ^ (4 / 5 : ℝ) * (N ^ (6 / 5 : ℝ) * N) := mul_le_mul_of_nonneg_right hbig (by positivity)
    _ = N ^ 3 := by rw [← mul_assoc, e2]; ring

/-- The union bound over the grid: `N^{M} N^{-(D+m+1)} + N^{-(D+1)} ≤ N^{-D}` for `N ≥ 2`, `M = N^m`. -/
theorem iniTermI_union_numeric {N D : ℝ} (hN : 2 ≤ N) (m : ℕ) :
    N ^ m * N ^ (-(D + m + 1)) + N ^ (-(D + 1)) ≤ N ^ (-D) := by
  have hN0 : 0 < N := by linarith
  have h1 : N ^ m * N ^ (-(D + m + 1)) = N ^ (-(D + 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hN0]; congr 1; ring
  have h2 : N ^ (-(D + 1)) = N ^ (-D) * N⁻¹ := by
    rw [show -(D + 1) = -D + (-1 : ℝ) by ring, Real.rpow_add hN0, Real.rpow_neg_one]
  have hx : 0 < N ^ (-D) := Real.rpow_pos_of_pos hN0 _
  rw [h1, h2]
  have : 2 * N⁻¹ ≤ 1 := by rw [← div_eq_mul_inv, div_le_one hN0]; exact hN
  nlinarith

set_option maxHeartbeats 1000000 in
-- long calc chains with many `positivity`/`gcongr` side goals
/-- **The pointwise step of the grid argument**: `|f_u - f_v| ≤ 4 N² T_m³ |u-v| X_m ≤ 16 N^{-5} ≤ N^{-3} ≤ ζ`
(`T_m ≤ N²`, `X_m ≤ 4N`, `|u-v| ≤ N^{-14}`), so `|f_v| ≤ N^{τ/2} ζ` gives `|f_u| ≤ N^τ ζ`. -/
theorem iniTermI_unif_det (hd : 3 ≤ d) (n : ℕ) {𝔡 E s t u v τ : ℝ} (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ 𝔡⁻¹)
    (hA1 : 1 ≤ STAI sz n) (hb : 2 * (𝔡⁻¹ ^ 2) ^ (6 / 5 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (4 / 5 : ℝ))
    (hN : (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ)) (hNt : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2))
    (hE : |E| ≤ 2) (hs0 : 0 ≤ s) (hst : s ≤ t) (hu0 : 0 ≤ u) (hut : u ≤ t) (hv0 : 0 ≤ v) (hvt : v ≤ t) (ht1 : t < 1)
    (hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t)
    (huv : |u - v| ≤ 1 / ((sz.size n : ℕ) : ℝ) ^ 14) {σ : Fin 2 → Bool} (hσ : σ 0 ≠ σ 1)
    (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ)
    (hXω : ∀ b, ‖STLKM sz n E s (sz.seqHflow n s ω) σ b‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * (sz.Bctl n s) ^ 2)
    (hfv : ‖STfFar sz n E s v σ a ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * STCltFarZeta sz n a) :
    ‖STfFar sz n E s u σ a ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * STCltFarZeta sz n a := by
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  have hs1 : s < 1 := by linarith
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hlow : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - s :=
    (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (pow_le_pow_right₀ hL1 (by omega : 2 ≤ d))).trans
      (hreg.trans (by linarith))
  have hBs : sz.Bctl n s ≤ 2 := by
    have := iniTermI_Bctl_le sz n hg hs1 hlow
    have h2 : (STAI sz n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hA1
    linarith
  have hBs0 : 0 ≤ sz.Bctl n s := (st_Bctl_pos sz hs1).le
  have hlip := iniTermI_STfFar_lip sz n hE hs0 hs1.le hu0 hut hv0 hvt ht1 hσ a ω hXω
  have hTm := iniTermI_oneSub_inv_le sz hd n hA1 hg hreg
  have hTm0 : 0 ≤ (1 - t)⁻¹ := inv_nonneg.2 (by linarith)
  have hcard : (Fintype.card (Zd d (sz.L n)) : ℝ) ≤ N := by
    rw [iniTermI_card_Zd, hNdef]
    have : (sz.L n) ^ d ≤ (sz.W n * sz.L n) ^ d := Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
    unfold Sizes.size; exact_mod_cast this
  have hN14 : (0 : ℝ) < N ^ 14 := by positivity
  have hB2 : (sz.Bctl n s) ^ 2 ≤ 4 := by nlinarith
  have hXm4 : N ^ (1 : ℝ) * (sz.Bctl n s) ^ 2 ≤ 4 * N := by
    rw [Real.rpow_one]; nlinarith
  have hX0 : 0 ≤ N ^ (1 : ℝ) * (sz.Bctl n s) ^ 2 := by positivity
  have e3 : N ^ (-(3 : ℝ)) = (N ^ 3)⁻¹ := by
    rw [Real.rpow_neg hN0.le]; congr 1; exact_mod_cast Real.rpow_natCast N 3
  have e1 : (Fintype.card (Zd d (sz.L n)) : ℝ) ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
  have e2 : ((1 - t)⁻¹) ^ 3 ≤ (N ^ 2) ^ 3 := pow_le_pow_left₀ hTm0 hTm 3
  have herr : 4 * (Fintype.card (Zd d (sz.L n)) : ℝ) ^ 2 * ((1 - t)⁻¹) ^ 3 * |u - v| * (N ^ (1 : ℝ) * (sz.Bctl n s) ^ 2)
      ≤ N ^ (-(3 : ℝ)) := by
    have h1 : 4 * (Fintype.card (Zd d (sz.L n)) : ℝ) ^ 2 * ((1 - t)⁻¹) ^ 3 ≤ 4 * N ^ 2 * (N ^ 2) ^ 3 := by
      have := mul_le_mul e1 e2 (by positivity) (by positivity)
      linarith
    have h2 : 4 * (Fintype.card (Zd d (sz.L n)) : ℝ) ^ 2 * ((1 - t)⁻¹) ^ 3 * |u - v| ≤
        4 * N ^ 2 * (N ^ 2) ^ 3 * (1 / N ^ 14) :=
      mul_le_mul h1 huv (abs_nonneg _) (by positivity)
    calc _ ≤ 4 * N ^ 2 * (N ^ 2) ^ 3 * (1 / N ^ 14) * (4 * N) := mul_le_mul h2 hXm4 hX0 (by positivity)
      _ = 16 / N ^ 5 := by field_simp; ring
      _ ≤ (N ^ 3)⁻¹ := by
          have hN2 : (16 : ℝ) ≤ N ^ 2 := by nlinarith
          rw [div_le_iff₀ (by positivity)]
          calc (16 : ℝ) ≤ N ^ 2 := hN2
            _ = (N ^ 3)⁻¹ * N ^ 5 := by field_simp
      _ = _ := e3.symm
  have hz := iniTermI_zeta_ge sz hd n hg hgΛ hA1 hb a
  have hz0 : 0 ≤ STCltFarZeta sz n a := (Real.rpow_nonneg hN0.le _).trans hz
  have hsub := norm_sub_norm_le (STfFar sz n E s u σ a ω) (STfFar sz n E s v σ a ω)
  have hNτ' : N ^ τ = N ^ (τ / 2) * N ^ (τ / 2) := by rw [← Real.rpow_add hN0]; congr 1; ring
  rw [hNτ']
  nlinarith [mul_nonneg hz0 (sub_nonneg.2 hNt), mul_nonneg hz0 (mul_nonneg (sub_nonneg.2 hNt) (sub_nonneg.2 hNt))]

/-- **`lem;CLT` uniformly in `u ∈ [s,t]`** (the `u`-uniform form of `stCltFar_holds`; route (a)-(d) of the ticket, DECISIONS §145):
(a) `f^{far}_u` depends on `u` only through `Θ_u`, Lipschitz with constant `4 N² T_m³ X_m`, `T_m = (1-t)⁻¹ ≤ N²`,
`X_m ≤ 4N` (`STLK` at `s`, `k = 2`, w.h.p.); (b) the index set grows with `ℓ_u`, so `u ∈ [s_k - δ, s_k]` uses `s_k`; (c) per grid point
`s_k = s + k (t-s)/N^{14}` (`k ≤ N^{14}`), `stCltFar_holds` at the worst sequence `t'_n = s_{k*_n}` (`k*_n` maximising the bad
probability) and the union over `N^{14}` grid points; (d) `stIngR5_hyps_restrict`. -/
theorem stCltFar_uniform (d : ℕ) : STIngR5 d STReg5I (fun sz E s t => STCltFarUConcl sz E s t) := by
  classical
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h𝔠d, h𝔠d', H⟩ := stCltFar_holds d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨𝔠d, h𝔠d, h𝔠d', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst ht hreg hKb hKw hLK hDec hDecS hCon hS1 hS2 hLmax hLKU
  have hflow' := hflow
  obtain ⟨⟨h𝔠, -, hSz, hBw, hWO⟩, hloc⟩ := hflow
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hflow' ht
  have him : ∀ n, 0 < (z n).im := fun n =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _) (hloc n).2.1
  have hE2 : ∀ n, |STflowE z n| ≤ 2 := fun n => ((abs_lemE_le (him n)).trans (hloc n).1).trans (by linarith)
  have hs1 : ∀ n, s n < 1 := fun n => (hst n).trans (ht1 n)
  intro τ hτ D hD
  set Mn : ℕ → ℕ := fun n => (sz.size n) ^ 14 with hMn
  have hMn1 : ∀ n, 1 ≤ Mn n := fun n => Nat.one_le_pow _ _ (sz.one_le_size n)
  set ug : ℕ → ℕ → ℝ := fun n k => s n + (k : ℝ) * ((t n - s n) / (Mn n : ℝ)) with hug
  have hδ0 : ∀ n, 0 < (t n - s n) / (Mn n : ℝ) := fun n => div_pos (by linarith [hst n])
    (by exact_mod_cast hMn1 n)
  have hug_gt : ∀ n k, 1 ≤ k → s n < ug n k := fun n k hk => by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    have := mul_pos this (hδ0 n); simp only [hug]; linarith
  have hug_le : ∀ n k, k ≤ Mn n → ug n k ≤ t n := fun n k hk => by
    have h1 : (k : ℝ) ≤ Mn n := by exact_mod_cast hk
    have hM0 : (0 : ℝ) < Mn n := by exact_mod_cast hMn1 n
    have : (k : ℝ) * ((t n - s n) / (Mn n : ℝ)) ≤ (Mn n : ℝ) * ((t n - s n) / (Mn n : ℝ)) :=
      mul_le_mul_of_nonneg_right h1 (hδ0 n).le
    have h2 : (Mn n : ℝ) * ((t n - s n) / (Mn n : ℝ)) = t n - s n := by field_simp
    simp only [hug]; linarith
  let pb : ℕ → ℕ → ENNReal := fun n k => sz.seqP (iniTermI_cltBad sz (STflowE z) s (τ / 2) n (ug n k))
  have hex : ∀ n, ∃ k ∈ Finset.Icc 1 (Mn n), ∀ k' ∈ Finset.Icc 1 (Mn n), pb n k' ≤ pb n k := fun n =>
    Finset.exists_max_image (Finset.Icc 1 (Mn n)) (fun k => pb n k) ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hMn1 n⟩⟩
  choose kst hkmem hkmax using hex
  set t' : ℕ → ℝ := fun n => ug n (kst n) with ht'def
  have hst' : ∀ n, s n < t' n := fun n => hug_gt n _ (Finset.mem_Icc.1 (hkmem n)).1
  have ht'le : ∀ n, t' n ≤ t n := fun n => hug_le n _ (Finset.mem_Icc.1 (hkmem n)).2
  obtain ⟨hR', hCon', hS1', hS2', hLmax', hLKU'⟩ :=
    stIngR5_hyps_restrict sz h𝔠d hst' ht'le ht1 hreg hCon hS1 hS2 hLmax hLKU
  have hH := H 𝔠 sz z hflow' s t' hs0 hst' (fun n => (ht'le n).trans (ht n)) hR' hKb hKw hLK hDec hDecS hCon'
    hS1' hS2' hLmax' hLKU'
  have hev1 := hH (τ / 2) (half_pos hτ) (D + 14 + 1) (by linarith)
  have hev2 : ∀ᶠ n in atTop, ∀ k ∈ Finset.Icc 1 (Mn n),
      pb n k ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D + 14 + 1))) := by
    filter_upwards [hev1] with n hn k hk
    exact (hkmax n k hk).trans hn
  have hXev := StochDomAt.highProb (hLK 2 (by norm_num)) (τ := 1) one_pos
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ ∧ 1 ≤ STAI sz n := by
    filter_upwards [hWO, st5_eventually_A_ge_one sz h𝔡 hWO] with n h1 h2
    exact ⟨h2.1, h1.2, h2.2⟩
  have hN4 : ∀ᶠ n in atTop, (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hSz.eventually_ge_atTop 4
  have hNτ : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (half_pos hτ)).comp hSz).eventually_ge_atTop 2
  have hbig : ∀ᶠ n in atTop, 2 * (𝔡⁻¹ ^ 2) ^ (6 / 5 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (4 / 5 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 5)).comp hSz).eventually_ge_atTop _
  filter_upwards [hev2, hXev (D + 1) (by linarith), hlam, hN4, hNτ, hbig] with n h2 hX hl hN hNt hb
  obtain ⟨hg, hgΛ, hA1⟩ := hl
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  have hcover : badSetAt sz.size (fun n (q : Σ u : TimeIcc s t n, STCltFarIdx sz s n (u : ℝ)) ω =>
        ‖STfFar sz n (STflowE z n) (s n) (q.1 : ℝ) q.2.1.1.1 q.2.1.2 ω‖)
      (fun n q _ => STCltFarZeta sz n q.2.1.2) τ n ⊆
      (⋃ k ∈ Finset.Icc 1 (Mn n), iniTermI_cltBad sz (STflowE z) s (τ / 2) n (ug n k)) ∪
        {ω | ∀ p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)), ‖Lloop sz n (STflowE z n) (s n) p.1 p.2 ω - STKloop sz n (STflowE z n) (s n) p.1 p.2‖ ≤
          N ^ (1 : ℝ) * (sz.Bctl n (s n)) ^ 2}ᶜ := by
    intro ω hω
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    have hXω : ∀ p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)),
        ‖Lloop sz n (STflowE z n) (s n) p.1 p.2 ω - STKloop sz n (STflowE z n) (s n) p.1 p.2‖ ≤
          N ^ (1 : ℝ) * (sz.Bctl n (s n)) ^ 2 := by simpa using hc2
    simp only [Set.mem_iUnion, not_exists] at hc1
    obtain ⟨q, hq⟩ := hω
    obtain ⟨⟨u, hu⟩, ⟨⟨σsub, a⟩, hcond⟩⟩ := q
    have hq' : N ^ τ * STCltFarZeta sz n a < ‖STfFar sz n (STflowE z n) (s n) u σsub.1 a ω‖ := hq
    obtain ⟨k, hk1, hkM, huk, hkd⟩ := iniTermI_grid (hst n) hu.1 hu.2 (Mn n) (hMn1 n)
    have hv_le : ug n k ≤ t n := hug_le n k hkM
    have hu0 : 0 ≤ u := (hs0 n).trans hu.1
    have hv0 : 0 ≤ ug n k := hu0.trans huk
    have hℓ : ellT (sz.L n) (sz.lam n) u ≤ ellT (sz.L n) (sz.lam n) (ug n k) :=
      ellT_mono hg.le huk (hv_le.trans_lt (ht1 n))
    have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hlog0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := Real.log_nonneg hW1
    have hcv : Real.log ((sz.W n : ℕ) : ℝ) ^ 5 * ellT (sz.L n) (sz.lam n) (s n) ≤ ellT (sz.L n) (sz.lam n) (ug n k) ∧
        ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤
          (1 / 2 : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) (ug n k) +
            Real.log ((sz.W n : ℕ) : ℝ) ^ (5 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) (s n) :=
      ⟨hcond.1.trans hℓ, hcond.2.trans (by
        have := mul_le_mul_of_nonneg_left hℓ (by positivity : 0 ≤ (1 / 2 : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ))
        linarith)⟩
    have hno := hc1 k (Finset.mem_Icc.2 ⟨hk1, hkM⟩)
    have hfv : ‖STfFar sz n (STflowE z n) (s n) (ug n k) σsub.1 a ω‖ ≤ N ^ (τ / 2) * STCltFarZeta sz n a := by
      by_contra h
      exact hno ⟨⟨(σsub, a), hcv⟩, not_le.1 h⟩
    have hMnN : ((Mn n : ℕ) : ℝ) = N ^ 14 := by rw [hMn, hNdef]; push_cast; rfl
    have hN14 : (0 : ℝ) < N ^ 14 := by positivity
    have huv : |u - ug n k| ≤ 1 / N ^ 14 := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      have h1 : ug n k - u ≤ (t n - s n) / (Mn n : ℝ) := by simp only [hug]; linarith
      refine h1.trans ?_
      rw [hMnN]
      exact div_le_div_of_nonneg_right (by linarith [ht1 n, hs0 n]) hN14.le
    have := iniTermI_unif_det sz hd n hg hgΛ hA1 hb hN hNt (hE2 n) (hs0 n) (hst n).le hu0 hu.2 hv0 hv_le (ht1 n)
      (hreg n).1 huv σsub.2 a ω (fun b => hXω (σsub.1, b)) hfv
    exact absurd hq' (not_lt.2 this)
  change sz.seqP (badSetAt sz.size _ _ τ n) ≤ ENNReal.ofReal (N ^ (-D))
  have hcard' : (Finset.Icc 1 (Mn n)).card = Mn n := by simp
  calc sz.seqP (badSetAt sz.size _ _ τ n) ≤ sz.seqP ((⋃ k ∈ Finset.Icc 1 (Mn n),
        iniTermI_cltBad sz (STflowE z) s (τ / 2) n (ug n k)) ∪ _) := measure_mono hcover
    _ ≤ sz.seqP (⋃ k ∈ Finset.Icc 1 (Mn n), iniTermI_cltBad sz (STflowE z) s (τ / 2) n (ug n k)) +
        sz.seqP {ω | ∀ p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)),
          ‖Lloop sz n (STflowE z n) (s n) p.1 p.2 ω - STKloop sz n (STflowE z n) (s n) p.1 p.2‖ ≤
            N ^ (1 : ℝ) * (sz.Bctl n (s n)) ^ 2}ᶜ := measure_union_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 (Mn n), ENNReal.ofReal (N ^ (-(D + 14 + 1))) + ENNReal.ofReal (N ^ (-(D + 1))) :=
        add_le_add ((measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum h2)) hX
    _ = ENNReal.ofReal ((Mn n : ℝ) * N ^ (-(D + 14 + 1)) + N ^ (-(D + 1))) := by
        rw [Finset.sum_const, hcard', nsmul_eq_mul, ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (N ^ (-D)) := by
        apply ENNReal.ofReal_le_ofReal
        have hMnN : ((Mn n : ℕ) : ℝ) = N ^ 14 := by rw [hMn, hNdef]; push_cast; rfl
        rw [hMnN]
        exact iniTermI_union_numeric (by linarith) 14

end Unif

/-! ### 16. The kernel `Θ_u`: bound by the power kernel, far decay, convolution -/

section ThetaB

theorem iniTermI_theta_pi (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g u : ℝ, 0 < g → g ≤ Λ → 0 ≤ u → u < 1 →
      g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u → ∀ x y : Zd d L,
        ‖Theta d L g (u : ℂ) x y‖ ≤ C * (g ^ 2)⁻¹ * iniTermI_PI d L (x - y) := by
  obtain ⟨C₆, hC₆, H⟩ := step5Kernel_theta_decay d Λ hd hΛ
  refine ⟨C₆ * (1 + 2 ^ (d - 1)), by positivity, fun L _ hL g u hg hgΛ hu0 hu hreg x y => ?_⟩
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  refine (H L hL g u hg hgΛ hu0 hu x y).trans ?_
  have h1 := iniTermI_tailT_le_PI' hd hL1 hu hreg (y - x)
  have h2 : (g ^ 2 + (1 - u))⁻¹ ≤ (g ^ 2)⁻¹ := inv_anti₀ (by positivity) (by linarith)
  have hP := iniTermI_PI_nonneg (d := d) (L := L) (y - x)
  rw [iniTermI_PI_sub_comm y x] at h1 hP
  calc C₆ * tailT d L g u (zdistInf d L (y - x) : ℕ)
      ≤ C₆ * ((1 + 2 ^ (d - 1)) * ((g ^ 2 + (1 - u))⁻¹ * iniTermI_PI d L (x - y))) :=
        mul_le_mul_of_nonneg_left h1 hC₆.le
    _ ≤ C₆ * ((1 + 2 ^ (d - 1)) * ((g ^ 2)⁻¹ * iniTermI_PI d L (x - y))) := by
        gcongr
    _ = _ := by ring

theorem iniTermI_theta_far (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g u : ℝ, 0 < g → g ≤ Λ → 0 ≤ u → u < 1 →
      ∀ (x y : Zd d L) (r : ℝ), r < ((zdistInf d L (y - x) : ℕ) : ℝ) →
        ‖Theta d L g (u : ℂ) x y‖ ≤ C * (1 - u)⁻¹ * Real.exp (-(c * r / ellT L g u)) := by
  obtain ⟨C₅, hC₅, c₅, hc₅, H⟩ := prop5Decay_holds d Λ hd hΛ
  refine ⟨2 * C₅, c₅, by positivity, hc₅, fun L _ hL g u hg hgΛ hu0 hu x y r hr => ?_⟩
  have hξ : ‖(u : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_of_nonneg hu0]
  have hshift : Theta d L g (u : ℂ) x y = Theta d L g (u : ℂ) 0 (y - x) := by
    have := Theta_apply_add_right_of_three_le (d := d) (g := g) hL hξ 0 (y - x) x
    rwa [zero_add, sub_add_cancel] at this
  have hP := H L hL g hg hgΛ u hu0 hu 1 (by simp) true false (y - x)
  have hspin : PropSpin (1 : ℂ) true * PropSpin (1 : ℂ) false = 1 := by simp [PropSpin]
  rw [hspin, mul_one] at hP
  rw [hshift]
  refine hP.trans ?_
  have hu1 : 0 < 1 - u := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hℓ : 0 < ellT L g u := ellT_pos hL1
  have hB : Bparam d L g u (zdistD d L (y - x)) ≤ 2 * (1 - u)⁻¹ := by
    unfold Bparam
    rw [abs_of_pos hu1]
    have h1 : (g ^ 2 + (1 - u))⁻¹ * ((((zdistD d L (y - x) : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ ≤ (1 - u)⁻¹ := by
      have : (g ^ 2 + (1 - u))⁻¹ ≤ (1 - u)⁻¹ := inv_anti₀ hu1 (by nlinarith [sq_nonneg g])
      have h2 : ((((zdistD d L (y - x) : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (one_le_pow₀ (by have : (0 : ℝ) ≤ ((zdistD d L (y - x) : ℕ) : ℝ) := Nat.cast_nonneg _; linarith))
      calc _ ≤ (1 - u)⁻¹ * 1 := mul_le_mul this h2 (by positivity) (by positivity)
        _ = _ := mul_one _
    have h3 : ((L : ℝ) ^ d * (1 - u))⁻¹ ≤ (1 - u)⁻¹ := inv_anti₀ hu1 (le_mul_of_one_le_left hu1.le (one_le_pow₀ hL1))
    linarith
  have hD : r ≤ ((zdistD d L (y - x) : ℕ) : ℝ) :=
    hr.le.trans (by exact_mod_cast zdistInf_le_zdistD d L (y - x))
  have hE : Real.exp (-c₅ * ((zdistD d L (y - x) : ℕ) : ℝ) / ellT L g u) ≤ Real.exp (-(c₅ * r / ellT L g u)) := by
    refine Real.exp_le_exp.mpr ?_
    have : c₅ * r / ellT L g u ≤ c₅ * ((zdistD d L (y - x) : ℕ) : ℝ) / ellT L g u :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hD hc₅.le) hℓ.le
    have e : -c₅ * ((zdistD d L (y - x) : ℕ) : ℝ) / ellT L g u = -(c₅ * ((zdistD d L (y - x) : ℕ) : ℝ) / ellT L g u) := by ring
    linarith
  calc C₅ * Bparam d L g u (zdistD d L (y - x)) * Real.exp (-c₅ * ((zdistD d L (y - x) : ℕ) : ℝ) / ellT L g u)
      ≤ C₅ * (2 * (1 - u)⁻¹) * Real.exp (-(c₅ * r / ellT L g u)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hB hC₅.le) hE (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

theorem iniTermI_theta_conv (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g u : ℝ, 0 < g → g ≤ Λ → 0 ≤ u → u < 1 →
      g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u → ∀ a₀ a₁ : Zd d L,
        ∑ b : Zd d L, ‖Theta d L g (u : ℂ) a₀ b‖ * ‖Theta d L g (u : ℂ) b a₁‖ ≤
          C * (1 - u)⁻¹ * tailT d L g u (zdistInf d L (a₀ - a₁) : ℕ) := by
  obtain ⟨C₆, hC₆, H⟩ := step5Kernel_theta_decay d Λ hd hΛ
  obtain ⟨CT, hCT, hT⟩ := ekPropTInf_holds d hd
  refine ⟨C₆ ^ 2 * CT, by positivity, fun L _ hL g u hg hgΛ hu0 hu hreg a₀ a₁ => ?_⟩
  have hu1 : 0 < 1 - u := by linarith
  have hS := hT L g u u hg hu0 le_rfl hu (Or.inl hreg) a₀ a₁
  have hpt : ∀ b : Zd d L, ‖Theta d L g (u : ℂ) a₀ b‖ * ‖Theta d L g (u : ℂ) b a₁‖ ≤
      C₆ ^ 2 * (tailT d L g u (zdistInf d L (a₀ - b) : ℕ) * tailT d L g u (zdistInf d L (b - a₁) : ℕ)) := by
    intro b
    have h1 := H L hL g u hg hgΛ hu0 hu a₀ b
    have h2 := H L hL g u hg hgΛ hu0 hu b a₁
    rw [iniTermI_zdistInf_sub_comm b a₀] at h1
    rw [iniTermI_zdistInf_sub_comm a₁ b] at h2
    calc _ ≤ (C₆ * tailT d L g u (zdistInf d L (a₀ - b) : ℕ)) * (C₆ * tailT d L g u (zdistInf d L (b - a₁) : ℕ)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by have := tailT_nonneg (d := d) (L := L) (g := g) (t := u)
                                                  (Nat.cast_nonneg (zdistInf d L (a₀ - b))); positivity)
      _ = _ := by ring
  calc ∑ b : Zd d L, ‖Theta d L g (u : ℂ) a₀ b‖ * ‖Theta d L g (u : ℂ) b a₁‖
      ≤ ∑ b : Zd d L, C₆ ^ 2 * (tailT d L g u (zdistInf d L (a₀ - b) : ℕ) * tailT d L g u (zdistInf d L (b - a₁) : ℕ)) :=
        Finset.sum_le_sum fun b _ => hpt b
    _ = C₆ ^ 2 * ∑ b : Zd d L, tailT d L g u (zdistInf d L (a₀ - b) : ℕ) * tailT d L g u (zdistInf d L (b - a₁) : ℕ) := by
        rw [Finset.mul_sum]
    _ ≤ C₆ ^ 2 * (CT / (1 - u) * tailT d L g u (zdistInf d L (a₀ - a₁) : ℕ)) := mul_le_mul_of_nonneg_left hS (by positivity)
    _ = _ := by rw [div_eq_mul_inv]; ring

end ThetaB

/-! ### 17. The deterministic mixed bound: `|𝒰 X| ≤ |f^{far}| + C (…)` -/

section Mixed2

variable {d L : ℕ} [NeZero L]

/-- In regime (i), `ℓ_v = g (1-v)^{-1/2}`. -/
theorem iniTermI_ellT_eq {g v : ℝ} (hg : 0 < g) (hv : v < 1) (h1 : 1 - v ≤ g ^ 2)
    (h2 : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - v) (hL : 0 < (L : ℝ)) : ellT L g v = g / Real.sqrt (1 - v) := by
  have hv0 : 0 < 1 - v := by linarith
  have hsq : 0 < Real.sqrt (1 - v) := Real.sqrt_pos.2 hv0
  have hA : 1 ≤ g / Real.sqrt (1 - v) := by
    rw [le_div_iff₀ hsq, one_mul]
    exact Real.sqrt_le_iff.2 ⟨hg.le, by simpa using h1⟩
  have hB : g / Real.sqrt (1 - v) ≤ L := by
    rw [div_le_iff₀ hsq]
    refine le_of_sq_le_sq ?_ (by positivity)
    rw [mul_pow, Real.sq_sqrt hv0.le]
    rw [div_le_iff₀ (by positivity)] at h2; linarith
  unfold ellT
  rw [abs_of_pos hv0, max_eq_left hA, min_eq_left hB]

set_option maxHeartbeats 1000000 in
-- long calc chains with many `positivity`/`gcongr` side goals
/-- **The mixed bound** (`(uwkxkisjwj0)` and `(eq:boundga)`, `(iksjuwjx3)`, `3_5:2086-2171`): for `σ₁ ≠ σ₂`,
`|𝒰_{s,u,σ} X| ≤ |f^{far}| + K (M (λ W^{-d} 𝒯_u + ρ F) + M q g^{-2} (log W)^{14} P + [floor] + ρ Y₀ 𝒯_u)`; the profile
bound on `X`, the Ward sum `|Σ_{b₂} X| ≤ Y₀/(1-s)` and nothing else enter. -/
theorem iniTermI_mixed_bound (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g W D E s u M lam lW Y₀ : ℝ), 0 < g → g ≤ Λ → 0 < W →
        |E| ≤ 2 → 0 ≤ s → s ≤ u → u < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u → 1 - s ≤ g ^ 2 → 0 ≤ M → 0 ≤ lam →
        1 ≤ lW → 0 ≤ Y₀ → ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ X : (Fin 2 → Zd d L) → ℂ,
          (∀ b, ‖X b‖ ≤ M * (lam * (W ^ d)⁻¹ * tailT d L g s (zdistInf d L (b 0 - b 1) : ℕ) + W ^ (-D))) →
          (∀ b₁ : Zd d L, ‖∑ b₂ : Zd d L, X ![b₁, b₂]‖ ≤ Y₀ / (1 - s)) →
          ∀ (a : Fin 2 → Zd d L) (P : Zd d L → Prop) [DecidablePred P],
            (∀ b₁, P b₁ ↔ (lW ^ 4 * ellT L g s < ((zdistInf d L (b₁ - a 0) : ℕ) : ℝ) ∧
              lW ^ 4 * ellT L g s < ((zdistInf d L (b₁ - a 1) : ℕ) : ℝ))) →
            ‖RBM.Ind.Ugen d L g E σ s u X a‖ ≤ ‖iniTermI_fSum d L g s u X a P‖ + K *
              (M * (lam * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) + (1 - s) / (1 - u) * W ^ (-D)) +
                M * (lam * (W ^ d)⁻¹) * (g ^ 2)⁻¹ * lW ^ 14 * iniTermI_PI d L (a 0 - a 1) +
                M * (Fintype.card (Zd d L) : ℝ) ^ 2 * (g ^ 2)⁻¹ * (1 - u)⁻¹ *
                  (W ^ (-D) + lam * (W ^ d)⁻¹ * (g ^ 2)⁻¹ * Real.exp (-Real.sqrt (lW ^ 3))) +
                (1 - s) / (1 - u) * Y₀ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ)) := by
  obtain ⟨C₁, hC₁, Hcore⟩ := iniTermI_core_mixed d Λ hd hΛ
  obtain ⟨Cθ, hCθ, Hθ⟩ := iniTermI_theta_pi d Λ hd hΛ
  obtain ⟨Cv, hCv, Hv⟩ := iniTermI_theta_conv d Λ hd hΛ
  set c₀ : ℝ := 1 + 2 ^ (d - 1) with hc₀
  have hc₀1 : 1 ≤ c₀ := by have : (0 : ℝ) ≤ 2 ^ (d - 1) := by positivity
                           linarith
  set Kn : ℝ := 2 * (iniTermI_CW d + iniTermI_CB d) * iniTermI_CW d with hKn
  have hKn0 : 0 ≤ Kn := by
    have := iniTermI_CW_nonneg d; have := iniTermI_CB_nonneg d; rw [hKn]; positivity
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = C₁ + Kn * c₀ * Cθ ^ 2 + 2 * Cθ * c₀ + Cv := ⟨_, rfl⟩
  refine ⟨K, by rw [hK]; positivity, ?_⟩
  intro L _ hL g W D E s u M lam lW Y₀ hg hgΛ hW hE hs hsu hu hreg hregs1 hM hlam hlW hY σ hσ X hX hXY a P _ hP
  have hs1 : s < 1 := by linarith
  have hu0 : 0 ≤ u := hs.trans hsu
  have hu1 : 0 < 1 - u := by linarith
  have hs1' : 0 < 1 - s := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hregs : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - s := hreg.trans (by linarith)
  have hg2 : 0 < g ^ 2 := by positivity
  -- `ℓ_s`
  have hℓ : ellT L g s = g / Real.sqrt (1 - s) := iniTermI_ellT_eq hg hs1 hregs1 hregs (by linarith)
  set ℓs : ℝ := ellT L g s with hℓdef
  have hℓ1 : 1 ≤ ℓs := one_le_ellT hL1
  have hℓsq : (1 - s) * ℓs ^ 2 = g ^ 2 := by
    rw [hℓ, div_pow, Real.sq_sqrt hs1'.le]; field_simp
  set R : ℝ := lW ^ 3 * ℓs with hR
  set R' : ℝ := lW ^ 4 * ℓs with hR'
  have hlW3 : 1 ≤ lW ^ 3 := one_le_pow₀ hlW
  have hlW4 : 1 ≤ lW ^ 4 := one_le_pow₀ hlW
  have hR1 : 1 ≤ R := by nlinarith
  have hR'1 : 1 ≤ R' := by nlinarith
  have hRR : (1 - s) ^ 2 * (R ^ 2 * R' ^ 2) = lW ^ 14 * (g ^ 2) ^ 2 := by
    have : (1 - s) ^ 2 * (R ^ 2 * R' ^ 2) = lW ^ 14 * ((1 - s) * ℓs ^ 2) ^ 2 := by rw [hR, hR']; ring
    rw [this, hℓsq]
  -- the core
  obtain ⟨c, hc0, hc1, hcore⟩ := Hcore L hL g W D E s u M lam hg hgΛ hW hE hs hsu hu hreg hM hlam σ hσ X hX
  have hU := hcore a
  set q : ℝ := lam * (W ^ d)⁻¹ with hq
  have hq0 : 0 ≤ q := by positivity
  have hF : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  set E₃ : ℝ := Real.exp (-Real.sqrt (lW ^ 3)) with hE₃
  have hE₃0 : 0 ≤ E₃ := (Real.exp_pos _).le
  set M₁ : ℝ := M * q * (c₀ * (g ^ 2)⁻¹) with hM₁
  set M₄ : ℝ := M * (W ^ (-D) + q * (c₀ * ((g ^ 2)⁻¹ * E₃))) with hM₄
  have hM₁0 : 0 ≤ M₁ := by positivity
  have hM₄0 : 0 ≤ M₄ := by positivity
  -- the profile of `X`
  have hXn : ∀ b₁ b₂ : Zd d L, ‖X ![b₁, b₂]‖ ≤
      (if ((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) ≤ R then M₁ * iniTermI_PI d L (b₁ - b₂) else 0) + M₄ := by
    intro b₁ b₂
    have hx : ‖X ![b₁, b₂]‖ ≤ M * (q * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) + W ^ (-D)) := by
      simpa using hX ![b₁, b₂]
    have ht := iniTermI_tailT_le_PI hd hL1 hs1 hregs (b₁ - b₂)
    have hPI0 := iniTermI_PI_nonneg (d := d) (L := L) (b₁ - b₂)
    have hPI1 := iniTermI_PI_le_one (d := d) (L := L) (b₁ - b₂)
    have hinv : (g ^ 2 + (1 - s))⁻¹ ≤ (g ^ 2)⁻¹ := inv_anti₀ hg2 (by linarith)
    have hexp1 : Real.exp (-Real.sqrt (((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) / ellT L g s)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by have := Real.sqrt_nonneg (((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) / ellT L g s); linarith)
    split_ifs with hle
    · have : tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) ≤ c₀ * ((g ^ 2)⁻¹ * iniTermI_PI d L (b₁ - b₂)) := by
        refine ht.trans ?_
        calc _ ≤ c₀ * ((g ^ 2 + (1 - s))⁻¹ * iniTermI_PI d L (b₁ - b₂)) * 1 :=
              mul_le_mul_of_nonneg_left hexp1 (by positivity)
          _ = c₀ * ((g ^ 2 + (1 - s))⁻¹ * iniTermI_PI d L (b₁ - b₂)) := mul_one _
          _ ≤ _ := by gcongr
      calc ‖X ![b₁, b₂]‖ ≤ M * (q * (c₀ * ((g ^ 2)⁻¹ * iniTermI_PI d L (b₁ - b₂))) + W ^ (-D)) :=
            hx.trans (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left this hq0) le_rfl) hM)
        _ ≤ _ := by
          have h1 : 0 ≤ M * (q * (c₀ * ((g ^ 2)⁻¹ * E₃))) := by positivity
          have e : M * (q * (c₀ * ((g ^ 2)⁻¹ * iniTermI_PI d L (b₁ - b₂))) + W ^ (-D)) =
              M₁ * iniTermI_PI d L (b₁ - b₂) + M * W ^ (-D) := by simp only [hM₁]; ring
          have e' : M₄ = M * W ^ (-D) + M * (q * (c₀ * ((g ^ 2)⁻¹ * E₃))) := by simp only [hM₄]; ring
          rw [e]; linarith
    · push Not at hle
      have hy : lW ^ 3 ≤ ((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) / ellT L g s := by
        rw [le_div_iff₀ (by linarith)]; linarith
      have hexp : Real.exp (-Real.sqrt (((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) / ellT L g s)) ≤ E₃ :=
        Real.exp_le_exp.2 (neg_le_neg (Real.sqrt_le_sqrt hy))
      have : tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) ≤ c₀ * ((g ^ 2)⁻¹ * E₃) := by
        refine ht.trans ?_
        calc _ ≤ c₀ * ((g ^ 2 + (1 - s))⁻¹ * iniTermI_PI d L (b₁ - b₂)) * E₃ :=
              mul_le_mul_of_nonneg_left hexp (by positivity)
          _ ≤ c₀ * ((g ^ 2)⁻¹ * 1) * E₃ := by gcongr
          _ = _ := by ring
      calc ‖X ![b₁, b₂]‖ ≤ M * (q * (c₀ * ((g ^ 2)⁻¹ * E₃)) + W ^ (-D)) :=
            hx.trans (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left this hq0) le_rfl) hM)
        _ = 0 + M₄ := by simp only [hM₄]; ring
        _ ≤ _ := by simp
  -- the near part
  have hT1 : ∀ x y : Zd d L, ‖Theta d L g (u : ℂ) x y‖ ≤ (Cθ * (g ^ 2)⁻¹) * iniTermI_PI d L (x - y) :=
    fun x y => Hθ L hL g u hg hgΛ hu0 hu hreg x y
  have hTm' : ∀ x y : Zd d L, ‖Theta d L g (u : ℂ) x y‖ ≤ (1 - u)⁻¹ := fun x y => iniTermI_Theta_le hL hu0 hu x y
  have hT₁0 : 0 ≤ Cθ * (g ^ 2)⁻¹ := by positivity
  have hTm0 : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 hu1.le
  have hQ : ∀ b₁, ¬ P b₁ → ((zdistInf d L (b₁ - a 0) : ℕ) : ℝ) ≤ R' ∨ ((zdistInf d L (b₁ - a 1) : ℕ) : ℝ) ≤ R' := by
    intro b₁ hn
    rw [hP] at hn
    by_contra hc
    rw [not_or] at hc
    exact hn ⟨not_le.1 hc.1, not_le.1 hc.2⟩
  have hnear := iniTermI_near hd hR1 hR'1 hT₁0 hTm0 hM₁0 hM₄0 (fun x y => Theta d L g (u : ℂ) x y) hT1 hTm'
    (fun b₁ b₂ => X ![b₁, b₂]) hXn (a 0) (a 1) (fun b => ¬ P b) hQ
  have hfN : ‖iniTermI_fSum d L g s u X a (fun b => ¬ P b)‖ ≤
      Kn * c₀ * Cθ ^ 2 * (M * q * (g ^ 2)⁻¹ * lW ^ 14 * iniTermI_PI d L (a 0 - a 1)) +
        2 * Cθ * c₀ * (M * (Fintype.card (Zd d L) : ℝ) ^ 2 * (g ^ 2)⁻¹ * (1 - u)⁻¹ *
          (W ^ (-D) + q * (g ^ 2)⁻¹ * E₃)) := by
    unfold iniTermI_fSum
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    have h1s : (1 - s) ^ 2 ≤ 1 := by nlinarith
    have hP0 := iniTermI_PI_nonneg (d := d) (L := L) (a 0 - a 1)
    set Nd : ℝ := (Fintype.card (Zd d L) : ℝ) with hNd
    have hNd0 : 0 ≤ Nd := Nat.cast_nonneg _
    calc (1 - s) ^ 2 * ‖∑ b₁ ∈ Finset.univ.filter (fun b => ¬ P b), ∑ b₂ : Zd d L,
          Theta d L g (u : ℂ) (a 0) b₁ * X ![b₁, b₂] * (Theta d L g (u : ℂ) b₂ (a 1) - Theta d L g (u : ℂ) b₁ (a 1))‖
        ≤ (1 - s) ^ 2 * (Kn * M₁ * (Cθ * (g ^ 2)⁻¹) ^ 2 * (R ^ 2 * R' ^ 2) * iniTermI_PI d L (a 0 - a 1) +
            2 * Nd ^ 2 * (Cθ * (g ^ 2)⁻¹) * (1 - u)⁻¹ * M₄) :=
          mul_le_mul_of_nonneg_left hnear (sq_nonneg _)
      _ = Kn * M₁ * (Cθ * (g ^ 2)⁻¹) ^ 2 * ((1 - s) ^ 2 * (R ^ 2 * R' ^ 2)) * iniTermI_PI d L (a 0 - a 1) +
            (1 - s) ^ 2 * (2 * Nd ^ 2 * (Cθ * (g ^ 2)⁻¹) * (1 - u)⁻¹ * M₄) := by ring
      _ ≤ Kn * c₀ * Cθ ^ 2 * (M * q * (g ^ 2)⁻¹ * lW ^ 14 * iniTermI_PI d L (a 0 - a 1)) +
            1 * (2 * Cθ * c₀ * (M * Nd ^ 2 * (g ^ 2)⁻¹ * (1 - u)⁻¹ * (W ^ (-D) + q * (g ^ 2)⁻¹ * E₃))) := by
          refine add_le_add ?_ ?_
          · rw [hRR]
            have : Kn * M₁ * (Cθ * (g ^ 2)⁻¹) ^ 2 * (lW ^ 14 * (g ^ 2) ^ 2) = Kn * c₀ * Cθ ^ 2 * (M * q * (g ^ 2)⁻¹ * lW ^ 14) := by
              simp only [hM₁]; field_simp
            refine le_of_eq ?_
            calc Kn * M₁ * (Cθ * (g ^ 2)⁻¹) ^ 2 * (lW ^ 14 * (g ^ 2) ^ 2) * iniTermI_PI d L (a 0 - a 1)
                = Kn * c₀ * Cθ ^ 2 * (M * q * (g ^ 2)⁻¹ * lW ^ 14) * iniTermI_PI d L (a 0 - a 1) := by rw [this]
              _ = _ := by ring
          · refine mul_le_mul h1s ?_ (by positivity) zero_le_one
            have : M₄ ≤ c₀ * (M * (W ^ (-D) + q * (g ^ 2)⁻¹ * E₃)) := by
              simp only [hM₄]
              have h0 : 0 ≤ M * (W ^ (-D)) := by positivity
              have e : c₀ * (M * (W ^ (-D) + q * (g ^ 2)⁻¹ * E₃)) - M * (W ^ (-D) + q * (c₀ * ((g ^ 2)⁻¹ * E₃))) =
                  (c₀ - 1) * (M * W ^ (-D)) := by ring
              have := mul_nonneg (sub_nonneg.2 hc₀1) h0
              linarith
            calc 2 * Nd ^ 2 * (Cθ * (g ^ 2)⁻¹) * (1 - u)⁻¹ * M₄
                ≤ 2 * Nd ^ 2 * (Cθ * (g ^ 2)⁻¹) * (1 - u)⁻¹ * (c₀ * (M * (W ^ (-D) + q * (g ^ 2)⁻¹ * E₃))) :=
                  mul_le_mul_of_nonneg_left this (by positivity)
              _ = _ := by ring
      _ = _ := by rw [one_mul]
  -- the Ward term
  have hG : ‖iniTermI_Gward d L g s u X a‖ ≤ Cv * ((1 - s) / (1 - u) * Y₀ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ)) := by
    unfold iniTermI_Gward
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    have hv := Hv L hL g u hg hgΛ hu0 hu hreg (a 0) (a 1)
    have hsum : ‖∑ b₁ : Zd d L, Theta d L g (u : ℂ) (a 0) b₁ * Theta d L g (u : ℂ) b₁ (a 1) * ∑ b₂ : Zd d L, X ![b₁, b₂]‖ ≤
        Y₀ / (1 - s) * (Cv * (1 - u)⁻¹ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ)) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ b₁ : Zd d L, ‖Theta d L g (u : ℂ) (a 0) b₁ * Theta d L g (u : ℂ) b₁ (a 1) * ∑ b₂ : Zd d L, X ![b₁, b₂]‖
          ≤ ∑ b₁ : Zd d L, (‖Theta d L g (u : ℂ) (a 0) b₁‖ * ‖Theta d L g (u : ℂ) b₁ (a 1)‖) * (Y₀ / (1 - s)) :=
            Finset.sum_le_sum fun b₁ _ => by
              rw [norm_mul, norm_mul]
              exact mul_le_mul_of_nonneg_left (hXY b₁) (by positivity)
        _ = (∑ b₁ : Zd d L, ‖Theta d L g (u : ℂ) (a 0) b₁‖ * ‖Theta d L g (u : ℂ) b₁ (a 1)‖) * (Y₀ / (1 - s)) := by
            rw [Finset.sum_mul]
        _ ≤ (Cv * (1 - u)⁻¹ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ)) * (Y₀ / (1 - s)) :=
            mul_le_mul_of_nonneg_right hv (by positivity)
        _ = _ := by ring
    calc (1 - s) ^ 2 * ‖∑ b₁ : Zd d L, Theta d L g (u : ℂ) (a 0) b₁ * Theta d L g (u : ℂ) b₁ (a 1) * ∑ b₂ : Zd d L, X ![b₁, b₂]‖
        ≤ (1 - s) ^ 2 * (Y₀ / (1 - s) * (Cv * (1 - u)⁻¹ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ))) :=
          mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ = _ := by field_simp
  -- assembly
  have hdec := iniTermI_Sfull_decomp (g := g) (s := s) hL hu0 hu X a P
  have hSfull : ‖iniTermI_Sfull d L g s u X a‖ ≤ ‖iniTermI_fSum d L g s u X a P‖ +
      (‖iniTermI_fSum d L g s u X a (fun b => ¬ P b)‖ + ‖iniTermI_Gward d L g s u X a‖) := by
    rw [hdec]
    calc _ ≤ ‖iniTermI_fSum d L g s u X a (fun b => ¬ P b) + iniTermI_fSum d L g s u X a P‖ +
          ‖iniTermI_Gward d L g s u X a‖ := norm_add_le _ _
      _ ≤ (‖iniTermI_fSum d L g s u X a (fun b => ¬ P b)‖ + ‖iniTermI_fSum d L g s u X a P‖) +
          ‖iniTermI_Gward d L g s u X a‖ := add_le_add (norm_add_le _ _) le_rfl
      _ = _ := by ring
  have hcS : ‖(c : ℂ) * iniTermI_Sfull d L g s u X a‖ ≤ ‖iniTermI_Sfull d L g s u X a‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0]
    exact mul_le_of_le_one_left (norm_nonneg _) hc1
  have hsub := norm_sub_norm_le (RBM.Ind.Ugen d L g E σ s u X a) ((c : ℂ) * iniTermI_Sfull d L g s u X a)
  set T₁' : ℝ := M * (q * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) + (1 - s) / (1 - u) * W ^ (-D)) with hT₁'
  set T₂' : ℝ := M * q * (g ^ 2)⁻¹ * lW ^ 14 * iniTermI_PI d L (a 0 - a 1) with hT₂'
  set T₃' : ℝ := M * (Fintype.card (Zd d L) : ℝ) ^ 2 * (g ^ 2)⁻¹ * (1 - u)⁻¹ * (W ^ (-D) + q * (g ^ 2)⁻¹ * E₃) with hT₃'
  set T₄' : ℝ := (1 - s) / (1 - u) * Y₀ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) with hT₄'
  have hρ0 : 0 ≤ (1 - s) / (1 - u) := div_nonneg hs1'.le hu1.le
  have hTu0 : 0 ≤ tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) := tailT_nonneg (Nat.cast_nonneg _)
  have hP0 := iniTermI_PI_nonneg (d := d) (L := L) (a 0 - a 1)
  have h1 : 0 ≤ T₁' := by simp only [hT₁']; positivity
  have h2 : 0 ≤ T₂' := by simp only [hT₂']; positivity
  have h3 : 0 ≤ T₃' := by simp only [hT₃']; positivity
  have h4 : 0 ≤ T₄' := by simp only [hT₄']; positivity
  have hKc : 0 ≤ Kn * c₀ * Cθ ^ 2 := by positivity
  have hCθc : 0 ≤ 2 * Cθ * c₀ := by positivity
  calc ‖RBM.Ind.Ugen d L g E σ s u X a‖
      ≤ ‖RBM.Ind.Ugen d L g E σ s u X a - (c : ℂ) * iniTermI_Sfull d L g s u X a‖ + ‖(c : ℂ) * iniTermI_Sfull d L g s u X a‖ := by
        linarith
    _ ≤ C₁ * T₁' + (‖iniTermI_fSum d L g s u X a P‖ +
          (Kn * c₀ * Cθ ^ 2 * T₂' + 2 * Cθ * c₀ * T₃' + Cv * T₄')) := by
        have := hU
        have e : C₁ * M * (lam * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) +
            (1 - s) / (1 - u) * W ^ (-D)) = C₁ * T₁' := by simp only [hT₁', hq]; ring
        rw [e] at this
        linarith
    _ ≤ _ := by
        have hK1 : C₁ ≤ K := by rw [hK]; linarith
        have hK2 : Kn * c₀ * Cθ ^ 2 ≤ K := by rw [hK]; linarith
        have hK3 : 2 * Cθ * c₀ ≤ K := by rw [hK]; linarith
        have hK4 : Cv ≤ K := by rw [hK]; linarith
        have e1 := mul_le_mul_of_nonneg_right hK1 h1
        have e2 := mul_le_mul_of_nonneg_right hK2 h2
        have e3 := mul_le_mul_of_nonneg_right hK3 h3
        have e4 := mul_le_mul_of_nonneg_right hK4 h4
        have e : K * (T₁' + T₂' + T₃' + T₄') = K * T₁' + K * T₂' + K * T₃' + K * T₄' := by ring
        have e5 : Kn * c₀ * Cθ ^ 2 * T₂' + 2 * Cθ * c₀ * T₃' + Cv * T₄' + C₁ * T₁' ≤ K * (T₁' + T₂' + T₃' + T₄') := by
          rw [e]; linarith
        linarith

set_option maxHeartbeats 1000000 in
-- long calc chains with many `positivity`/`gcongr` side goals
/-- **Outside the window** (`(eq:ells_to_ellt2)`, `3_5:2119-2128`): if `|a₁-a₂| > 2 r₁ + Y_w`, every pair of labels `(b₁,b₂)` has `Θ` or `𝓑`
exponentially small (`prop:ThfadC`, `Eq:Gdecay+IND`), so `|𝒰 X| ≤ C₁ M (q 𝒯_u + ρ F) + N² (1-u)⁻² (2 C e^{-c r₁/ℓ_u} X_m + X_t)`. -/
theorem iniTermI_mixed_tail (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) :
    ∃ K C c : ℝ, 0 < K ∧ 0 < C ∧ 0 < c ∧
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g W D E s u M lam r₁ Yw : ℝ), 0 < g → g ≤ Λ → 0 < W →
        |E| ≤ 2 → 0 ≤ s → s ≤ u → u < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u → 0 ≤ M → 0 ≤ lam →
        ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ X : (Fin 2 → Zd d L) → ℂ,
          (∀ b, ‖X b‖ ≤ M * (lam * (W ^ d)⁻¹ * tailT d L g s (zdistInf d L (b 0 - b 1) : ℕ) + W ^ (-D))) →
          ∀ a : Fin 2 → Zd d L, 2 * r₁ + Yw < ((zdistInf d L (a 0 - a 1) : ℕ) : ℝ) →
            ‖RBM.Ind.Ugen d L g E σ s u X a‖ ≤
              K * M * (lam * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) + (1 - s) / (1 - u) * W ^ (-D)) +
                (Fintype.card (Zd d L) : ℝ) ^ 2 * ((1 - u)⁻¹) ^ 2 *
                  (2 * C * Real.exp (-(c * r₁ / ellT L g u)) * (M * (lam * (W ^ d)⁻¹ * ((1 + 2 ^ (d - 1)) * (g ^ 2)⁻¹) + W ^ (-D))) +
                    M * (lam * (W ^ d)⁻¹ * ((1 + 2 ^ (d - 1)) * ((g ^ 2)⁻¹ *
                      Real.exp (-Real.sqrt (Yw / ellT L g s)))) + W ^ (-D))) := by
  obtain ⟨C₁, hC₁, Hcore⟩ := iniTermI_core_mixed d Λ hd hΛ
  obtain ⟨Cf, cf, hCf, hcf, Hf⟩ := iniTermI_theta_far d Λ hd hΛ
  refine ⟨C₁, Cf, cf, hC₁, hCf, hcf, ?_⟩
  intro L _ hL g W D E s u M lam r₁ Yw hg hgΛ hW hE hs hsu hu hreg hM hlam σ hσ X hX a hr
  have hs1 : s < 1 := by linarith
  have hu0 : 0 ≤ u := hs.trans hsu
  have hu1 : 0 < 1 - u := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hregs : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - s := hreg.trans (by linarith)
  have hg2 : 0 < g ^ 2 := by positivity
  set c₀ : ℝ := 1 + 2 ^ (d - 1) with hc₀
  set q : ℝ := lam * (W ^ d)⁻¹ with hq
  have hq0 : 0 ≤ q := by positivity
  have hF : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  obtain ⟨c, hc0, hc1, hcore⟩ := Hcore L hL g W D E s u M lam hg hgΛ hW hE hs hsu hu hreg hM hlam σ hσ X hX
  have hU := hcore a
  -- bounds for `X`
  have hTs : ∀ y : Zd d L, tailT d L g s (zdistInf d L y : ℕ) ≤ c₀ * ((g ^ 2)⁻¹ * 1) := by
    intro y
    refine (iniTermI_tailT_le_PI' hd hL1 hs1 hregs y).trans ?_
    have hinv : (g ^ 2 + (1 - s))⁻¹ ≤ (g ^ 2)⁻¹ := inv_anti₀ hg2 (by linarith)
    have := iniTermI_PI_le_one (d := d) (L := L) y
    have := iniTermI_PI_nonneg (d := d) (L := L) y
    gcongr
  have hXm : ∀ b, ‖X b‖ ≤ M * (q * (c₀ * (g ^ 2)⁻¹) + W ^ (-D)) := fun b =>
    (hX b).trans (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left
      (by simpa using hTs (b 0 - b 1)) hq0) le_rfl) hM)
  have hXt : ∀ b, Yw < ((zdistInf d L (b 0 - b 1) : ℕ) : ℝ) → ‖X b‖ ≤
      M * (q * (c₀ * ((g ^ 2)⁻¹ * Real.exp (-Real.sqrt (Yw / ellT L g s)))) + W ^ (-D)) := by
    intro b hb
    have hℓ0 : 0 < ellT L g s := ellT_pos hL1
    have ht := iniTermI_tailT_le_PI hd hL1 hs1 hregs (b 0 - b 1)
    have hinv : (g ^ 2 + (1 - s))⁻¹ ≤ (g ^ 2)⁻¹ := inv_anti₀ hg2 (by linarith)
    have h1 := iniTermI_PI_le_one (d := d) (L := L) (b 0 - b 1)
    have h2 := iniTermI_PI_nonneg (d := d) (L := L) (b 0 - b 1)
    have hy : Yw / ellT L g s ≤ ((zdistInf d L (b 0 - b 1) : ℕ) : ℝ) / ellT L g s :=
      div_le_div_of_nonneg_right hb.le hℓ0.le
    have hexp : Real.exp (-Real.sqrt (((zdistInf d L (b 0 - b 1) : ℕ) : ℝ) / ellT L g s)) ≤
        Real.exp (-Real.sqrt (Yw / ellT L g s)) := Real.exp_le_exp.2 (neg_le_neg (Real.sqrt_le_sqrt hy))
    have : tailT d L g s (zdistInf d L (b 0 - b 1) : ℕ) ≤ c₀ * ((g ^ 2)⁻¹ * Real.exp (-Real.sqrt (Yw / ellT L g s))) := by
      refine ht.trans ?_
      calc _ ≤ c₀ * ((g ^ 2 + (1 - s))⁻¹ * iniTermI_PI d L (b 0 - b 1)) * Real.exp (-Real.sqrt (Yw / ellT L g s)) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ ≤ c₀ * ((g ^ 2)⁻¹ * 1) * Real.exp (-Real.sqrt (Yw / ellT L g s)) := by gcongr
        _ = _ := by ring
    exact (hX b).trans (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left this hq0) le_rfl) hM)
  have hT : ∀ x y : Zd d L, ‖Theta d L g (u : ℂ) x y‖ ≤ (1 - u)⁻¹ := fun x y => iniTermI_Theta_le hL hu0 hu x y
  have hTd : ∀ x y : Zd d L, r₁ < ((zdistInf d L (y - x) : ℕ) : ℝ) →
      ‖Theta d L g (u : ℂ) x y‖ ≤ Cf * (1 - u)⁻¹ * Real.exp (-(cf * r₁ / ellT L g u)) :=
    fun x y hxy => Hf L hL g u hg hgΛ hu0 hu x y r₁ hxy
  have hXm0 : 0 ≤ M * (q * (c₀ * (g ^ 2)⁻¹) + W ^ (-D)) := by positivity
  have hXt0 : 0 ≤ M * (q * (c₀ * ((g ^ 2)⁻¹ * Real.exp (-Real.sqrt (Yw / ellT L g s)))) + W ^ (-D)) := by positivity
  have hS := iniTermI_tail (g := g) (s := s) (u := u) (Tm := (1 - u)⁻¹) (Xm := M * (q * (c₀ * (g ^ 2)⁻¹) + W ^ (-D)))
    (Xt := M * (q * (c₀ * ((g ^ 2)⁻¹ * Real.exp (-Real.sqrt (Yw / ellT L g s)))) + W ^ (-D)))
    (E₀ := Cf * (1 - u)⁻¹ * Real.exp (-(cf * r₁ / ellT L g u))) (r₁ := r₁) (Y₀ := Yw)
    (inv_nonneg.2 hu1.le) hXm0 hXt0 (by positivity) hT hTd X hXm hXt a hr
  have hρ0 : 0 ≤ (1 - s) / (1 - u) := div_nonneg (by linarith) hu1.le
  have hcS : ‖(c : ℂ) * iniTermI_Sfull d L g s u X a‖ ≤ ‖iniTermI_Sfull d L g s u X a‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0]
    exact mul_le_of_le_one_left (norm_nonneg _) hc1
  have hsub := norm_sub_norm_le (RBM.Ind.Ugen d L g E σ s u X a) ((c : ℂ) * iniTermI_Sfull d L g s u X a)
  have h1s : (1 - s) ^ 2 ≤ 1 := by nlinarith
  have hrest : ‖iniTermI_Sfull d L g s u X a‖ ≤ (Fintype.card (Zd d L) : ℝ) ^ 2 * ((1 - u)⁻¹) ^ 2 *
      (2 * Cf * Real.exp (-(cf * r₁ / ellT L g u)) * (M * (q * (c₀ * (g ^ 2)⁻¹) + W ^ (-D))) +
        M * (q * (c₀ * ((g ^ 2)⁻¹ * Real.exp (-Real.sqrt (Yw / ellT L g s)))) + W ^ (-D))) := by
    refine hS.trans ?_
    have e : (Fintype.card (Zd d L) : ℝ) ^ 2 * (2 * (Cf * (1 - u)⁻¹ * Real.exp (-(cf * r₁ / ellT L g u))) * (1 - u)⁻¹ *
        (M * (q * (c₀ * (g ^ 2)⁻¹) + W ^ (-D))) + ((1 - u)⁻¹) ^ 2 *
          (M * (q * (c₀ * ((g ^ 2)⁻¹ * Real.exp (-Real.sqrt (Yw / ellT L g s)))) + W ^ (-D)))) =
        (Fintype.card (Zd d L) : ℝ) ^ 2 * ((1 - u)⁻¹) ^ 2 *
      (2 * Cf * Real.exp (-(cf * r₁ / ellT L g u)) * (M * (q * (c₀ * (g ^ 2)⁻¹) + W ^ (-D))) +
        M * (q * (c₀ * ((g ^ 2)⁻¹ * Real.exp (-Real.sqrt (Yw / ellT L g s)))) + W ^ (-D))) := by ring
    have hnn : 0 ≤ (Fintype.card (Zd d L) : ℝ) ^ 2 * (2 * (Cf * (1 - u)⁻¹ * Real.exp (-(cf * r₁ / ellT L g u))) * (1 - u)⁻¹ *
        (M * (q * (c₀ * (g ^ 2)⁻¹) + W ^ (-D))) + ((1 - u)⁻¹) ^ 2 *
          (M * (q * (c₀ * ((g ^ 2)⁻¹ * Real.exp (-Real.sqrt (Yw / ellT L g s)))) + W ^ (-D)))) := by positivity
    calc (1 - s) ^ 2 * ((Fintype.card (Zd d L) : ℝ) ^ 2 * (2 * (Cf * (1 - u)⁻¹ * Real.exp (-(cf * r₁ / ellT L g u))) * (1 - u)⁻¹ *
        (M * (q * (c₀ * (g ^ 2)⁻¹) + W ^ (-D))) + ((1 - u)⁻¹) ^ 2 *
          (M * (q * (c₀ * ((g ^ 2)⁻¹ * Real.exp (-Real.sqrt (Yw / ellT L g s)))) + W ^ (-D)))))
        ≤ 1 * _ := mul_le_mul_of_nonneg_right h1s hnn
      _ = _ := by rw [one_mul, e]
  have e2 : C₁ * M * (q * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) + (1 - s) / (1 - u) * W ^ (-D)) =
      C₁ * M * (lam * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) + (1 - s) / (1 - u) * W ^ (-D)) := by
    simp only [hq]
  linarith [hU, hcS, hsub, hrest, e2]

end Mixed2


/-! ### 18. Comparisons at the size index `n` -/

section Seq

variable {d : ℕ} (sz : Sizes d)

/-- `(W^{-d} B_{s,0})^{1/5} ≤ 2 A^{-1/5}`, `A = ilambda² W^d`. -/
theorem iniTermI_lam_le (n : ℕ) {s : ℝ} (hg : 0 < sz.lam n) (hs : s < 1)
    (hlow : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - s) :
    (sz.Bctl n s) ^ (1 / 5 : ℝ) ≤ 2 * (STAI sz n) ^ (-(1 / 5 : ℝ)) := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hA : 0 < STAI sz n := by unfold STAI; positivity
  have hB := iniTermI_Bctl_le sz n hg hs hlow
  have hB0 : 0 ≤ sz.Bctl n s := (st_Bctl_pos sz hs).le
  calc (sz.Bctl n s) ^ (1 / 5 : ℝ) ≤ (2 * (STAI sz n)⁻¹) ^ (1 / 5 : ℝ) :=
        Real.rpow_le_rpow hB0 hB (by norm_num)
    _ = 2 ^ (1 / 5 : ℝ) * (STAI sz n) ^ (-(1 / 5 : ℝ)) := by
        rw [Real.mul_rpow (by norm_num) (inv_nonneg.mpr hA.le), Real.inv_rpow hA.le, ← Real.rpow_neg hA.le]
    _ ≤ 2 * (STAI sz n) ^ (-(1 / 5 : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hA.le _)
        calc (2 : ℝ) ^ (1 / 5 : ℝ) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2

/-- The `STDecay` profile is `λ W^{-d} 𝒯_s + W^{-D}`. -/
theorem iniTermI_prem_eq (n : ℕ) (τ D' : ℝ) (b : Fin 2 → Zd d (sz.L n)) :
    (sz.Bctl n τ) ^ (1 / 5 : ℝ) * STWB sz n τ (zdistInf d (sz.L n) (b 0 - b 1)) *
        Real.exp (-(((zdistInf d (sz.L n) (b 0 - b 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) τ) ^ (1 / 2 : ℝ)) +
      ((sz.W n : ℕ) : ℝ) ^ (-D')
    = (sz.Bctl n τ) ^ (1 / 5 : ℝ) * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
        tailT d (sz.L n) (sz.lam n) τ (zdistInf d (sz.L n) (b 0 - b 1) : ℕ) + ((sz.W n : ℕ) : ℝ) ^ (-D') := by
  unfold STWB tailT
  rw [← BparamR_natCast, Real.sqrt_eq_rpow]
  ring

/-- `STprof ≥ W^{-d} 𝒯_u`. -/
theorem iniTermI_prof_ge (n : ℕ) (u D : ℝ) (a : Fin 2 → Zd d (sz.L n)) :
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a 0 - a 1) : ℕ)
      ≤ STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) := by
  unfold STprof tailW
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [min_eq_left (iniTermI_zdistInf_le_L _)]
  exact le_max_left _ _

/-- `|E| ≤ 2 - κ` gives `Im m(E) ≥ κ_m := √(κ(4-κ))/2`. -/
theorem iniTermI_im_ge {κ E : ℝ} (hE : |E| ≤ 2 - κ) : Real.sqrt (κ * (4 - κ)) / 2 ≤ (mE E).im := by
  rw [mE_im]
  have h2 : 0 ≤ 2 - κ := (abs_nonneg E).trans hE
  have hE2 : E ^ 2 ≤ (2 - κ) ^ 2 := by
    have := abs_le.mp hE
    nlinarith
  refine div_le_div_of_nonneg_right (Real.sqrt_le_sqrt ?_) (by norm_num)
  nlinarith

/-- **Ward's identity at the last label** (`(eq:PcalBterm)`, `3_5:2141`; `(WI_calL)`, `(WI_calK)`): for `σ₁ ≠ σ₂`,
`|Σ_{b₂} (𝓛-𝒦)^{(2)}_{s,σ,(b₁,b₂)}| ≤ (2 W^d η_s)⁻¹ (|(𝓛-𝒦)^{(1)}_{s,+,b₁}| + |(𝓛-𝒦)^{(1)}_{s,-,b₁}|)`. -/
theorem iniTermI_ward (n : ℕ) {E s : ℝ} (hE : |E| < 2) (hs0 : 0 ≤ s) (hs1 : s < 1) {σ : Fin 2 → Bool}
    (hσ : σ 0 ≠ σ 1) (b₁ : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    ‖∑ b₂ : Zd d (sz.L n), STLKM sz n E s (sz.seqHflow n s ω) σ ![b₁, b₂]‖ ≤
      (2 * (((sz.W n : ℕ) : ℝ) ^ d * etaT E s))⁻¹ *
        (‖Lloop sz n E s (fun _ : Fin 1 => true) (fun _ => b₁) ω - STKloop sz n E s (fun _ : Fin 1 => true) (fun _ => b₁)‖ +
          ‖Lloop sz n E s (fun _ : Fin 1 => false) (fun _ => b₁) ω - STKloop sz n E s (fun _ : Fin 1 => false) (fun _ => b₁)‖) := by
  have hσl : σ (Fin.last 1) = !σ 0 := by
    have : σ 1 ≠ σ 0 := fun h => hσ h.symm
    cases h0 : σ 0 <;> cases h1 : σ 1 <;> simp_all [Fin.last]
  have hw := B45_ward_fin sz n hE hs0 hs1 ω (m := 0) σ hσl (fun _ : Fin 1 => b₁)
  have hsn : ∀ x : Zd d (sz.L n), (Fin.snoc (α := fun _ => Zd d (sz.L n)) (fun _ : Fin 1 => b₁) x : Fin 2 → Zd d (sz.L n)) = ![b₁, x] := by
    intro x; funext i; fin_cases i <;> simp [Fin.snoc]
  have hT : ∀ x : Zd d (sz.L n), STLKtensor sz n E s ω σ (Fin.snoc (α := fun _ => Zd d (sz.L n)) (fun _ : Fin 1 => b₁) x) =
      STLKM sz n E s (sz.seqHflow n s ω) σ ![b₁, x] := fun x => by rw [hsn x]; rfl
  simp only [hT] at hw
  have hc : ∀ b : Bool, B45_sgnCons b σ = fun _ : Fin 1 => b := fun b => by funext i; fin_cases i; rfl
  rw [hw, hc true, hc false, norm_mul]
  have hη : 0 < etaT E s := etaT_pos hE hs1
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hn : ‖(2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (etaT E s : ℂ))⁻¹‖ = (2 * (((sz.W n : ℕ) : ℝ) ^ d * etaT E s))⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg hη.le]
    simp; ring
  rw [hn]
  exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)

end Seq

/-! ### 19. Two asymptotic facts (pure real analysis in `x = log W`) -/

section Asy

/-- `x^{3/4} ≤ (ε/4) x` for `x ≥ (4/ε)^4`. -/
theorem iniTermI_asy_rpow {ε x : ℝ} (hε : 0 < ε) (hx : (4 / ε) ^ 4 ≤ x) : x ^ (3 / 4 : ℝ) ≤ ε / 4 * x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  set y : ℝ := x ^ (1 / 4 : ℝ) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hx0 _
  have hxy : x = y ^ 4 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have h34 : x ^ (3 / 4 : ℝ) = y ^ 3 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hy1 : 4 / ε ≤ y := by
    have : (4 / ε) ^ 4 ≤ y ^ 4 := by rw [← hxy]; exact hx
    exact le_of_pow_le_pow_left₀ (by norm_num) hy0.le this
  rw [h34, hxy]
  have : 4 ≤ ε * y := by rwa [div_le_iff₀ hε, mul_comm] at hy1
  nlinarith [pow_pos hy0 3]

/-- `K x^{14} e^{x^{3/4}} ≤ e^{ε x}` eventually. -/
theorem iniTermI_asy1 (K ε : ℝ) (hε : 0 < ε) : ∀ᶠ x : ℝ in atTop, K * x ^ 14 * Real.exp (x ^ (3 / 4 : ℝ)) ≤ Real.exp (ε * x) := by
  set C : ℝ := |K| * ((Nat.factorial 14 : ℝ) * (4 / ε) ^ 14) with hC
  have hC0 : 0 ≤ C := by positivity
  filter_upwards [eventually_ge_atTop (max ((4 / ε) ^ 4) (max 1 (2 * Real.log (C + 1) / ε)))] with x hx
  have hx1 : (4 / ε) ^ 4 ≤ x := (le_max_left _ _).trans hx
  have hx2 : 1 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hx3 : 2 * Real.log (C + 1) / ε ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hx0 : 0 < x := by linarith
  have h1 : x ^ 14 ≤ (Nat.factorial 14 : ℝ) * (4 / ε) ^ 14 * Real.exp (ε / 4 * x) := by
    have h := Real.pow_div_factorial_le_exp (ε / 4 * x) (by positivity) 14
    have e : x ^ 14 = (4 / ε) ^ 14 * (ε / 4 * x) ^ 14 := by field_simp
    rw [e]
    rw [div_le_iff₀ (by positivity)] at h
    nlinarith [h, pow_pos (div_pos (by norm_num : (0:ℝ) < 4) hε) 14]
  have h2 := iniTermI_asy_rpow hε hx1
  have he : Real.exp (x ^ (3 / 4 : ℝ)) ≤ Real.exp (ε / 4 * x) := Real.exp_le_exp.2 h2
  have hlog : C + 1 ≤ Real.exp (ε / 2 * x) := by
    have : Real.log (C + 1) ≤ ε / 2 * x := by
      have := mul_le_mul_of_nonneg_left hx3 (by positivity : 0 ≤ ε / 2)
      calc Real.log (C + 1) = ε / 2 * (2 * Real.log (C + 1) / ε) := by field_simp
        _ ≤ _ := this
    calc C + 1 = Real.exp (Real.log (C + 1)) := (Real.exp_log (by linarith)).symm
      _ ≤ _ := Real.exp_le_exp.2 this
  calc K * x ^ 14 * Real.exp (x ^ (3 / 4 : ℝ)) ≤ |K| * x ^ 14 * Real.exp (ε / 4 * x) := by
        have : K * x ^ 14 ≤ |K| * x ^ 14 := mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
        exact mul_le_mul this he (Real.exp_pos _).le (by positivity)
    _ ≤ |K| * ((Nat.factorial 14 : ℝ) * (4 / ε) ^ 14 * Real.exp (ε / 4 * x)) * Real.exp (ε / 4 * x) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (abs_nonneg K)) (Real.exp_pos _).le
    _ = C * Real.exp (ε / 2 * x) := by
        rw [hC, show ε / 2 * x = ε / 4 * x + ε / 4 * x by ring, Real.exp_add]; ring
    _ ≤ Real.exp (ε / 2 * x) * Real.exp (ε / 2 * x) := by nlinarith [Real.exp_pos (ε / 2 * x)]
    _ = Real.exp (ε * x) := by rw [← Real.exp_add]; congr 1; ring

/-- `K e^{B x - c x^{5/4}} ≤ e^{-D x}` eventually (`c > 0`). -/
theorem iniTermI_asy2 (B D c K : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, K * Real.exp (B * x - c * x ^ (5 / 4 : ℝ)) ≤ Real.exp (-(D * x)) := by
  filter_upwards [eventually_ge_atTop (max 1 (max (((|B + D| + 1) / c) ^ 4) (Real.log (|K| + 1))))] with x hx
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hx2 : ((|B + D| + 1) / c) ^ 4 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hx3 : Real.log (|K| + 1) ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hx0 : 0 < x := by linarith
  set y : ℝ := x ^ (1 / 4 : ℝ) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hx0 _
  have hxy : x = y ^ 4 := by rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have h54 : x ^ (5 / 4 : ℝ) = x * y := by
    rw [hy, ← Real.rpow_one_add' hx0.le (by norm_num)]; norm_num
  have hy1 : (|B + D| + 1) / c ≤ y := by
    have : ((|B + D| + 1) / c) ^ 4 ≤ y ^ 4 := by rw [← hxy]; exact hx2
    exact le_of_pow_le_pow_left₀ (by norm_num) hy0.le this
  have hcy : |B + D| + 1 ≤ c * y := by rwa [div_le_iff₀ hc, mul_comm] at hy1
  have hK : K ≤ Real.exp x := by
    calc K ≤ |K| + 1 := by linarith [le_abs_self K]
      _ = Real.exp (Real.log (|K| + 1)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp x := Real.exp_le_exp.2 hx3
  have hexp : B * x - c * x ^ (5 / 4 : ℝ) ≤ -(D * x) - x := by
    rw [h54]
    have : (B + D) * x + x ≤ c * y * x := by
      have h1 : (B + D) ≤ |B + D| := le_abs_self _
      nlinarith
    nlinarith
  calc K * Real.exp (B * x - c * x ^ (5 / 4 : ℝ)) ≤ Real.exp x * Real.exp (-(D * x) - x) :=
        mul_le_mul hK (Real.exp_le_exp.2 hexp) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Asy

/-! ### 20. The real-level estimates for each case -/

section RL

variable {d : ℕ}

/-- **The window comparison** (`3_5:2124`: `exp((|a₁-a₂|/ℓ_u)^{1/2}) ≺ 1`; `(eq:boundga)`, last `≤`):
`(g² W^d)⁻¹ (r^{d-2}+1)⁻¹ ≤ 2^d e^θ W^{-d} 𝒯_u(r)` if `√(r/ℓ_u) ≤ θ` and `1 - u ≤ g²`. -/
theorem iniTermI_cmp (hd : 3 ≤ d) {L : ℕ} [NeZero L] {g u Wd θ : ℝ} (_hL1 : (1 : ℝ) ≤ L) (hg : 0 < g) (hu : u < 1) (h1 : 1 - u ≤ g ^ 2)
    (hWd : 0 < Wd) (x : Zd d L) (hθ : Real.sqrt (((zdistInf d L x : ℕ) : ℝ) / ellT L g u) ≤ θ) :
    (g ^ 2 * Wd)⁻¹ * ((((zdistInf d L x : ℕ) : ℝ) ^ (d - 2) + 1)⁻¹) ≤
      2 ^ d * Real.exp θ * (Wd⁻¹ * tailT d L g u (zdistInf d L x : ℕ)) := by
  set R : ℝ := ((zdistInf d L x : ℕ) : ℝ) with hR
  have hR0 : 0 ≤ R := Nat.cast_nonneg _
  have hu0 : 0 < 1 - u := by linarith
  have hg2 : 0 < g ^ 2 := by positivity
  have hge := iniTermI_tailT_ge_PI (d := d) (L := L) hg hu x
  have hpow : (R + 1) ^ (d - 2) ≤ 2 ^ (d - 2) * (R ^ (d - 2) + 1) := by
    have := add_pow_le hR0 (zero_le_one' ℝ) (d - 2)
    rw [one_pow] at this
    exact this.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)) (by positivity))
  have hPI : (2 ^ (d - 2) * (R ^ (d - 2) + 1))⁻¹ ≤ iniTermI_PI d L x := by
    unfold iniTermI_PI; rw [← hR]
    exact inv_anti₀ (by positivity) hpow
  have hA : (2 * g ^ 2)⁻¹ ≤ (g ^ 2 + (1 - u))⁻¹ := inv_anti₀ (by positivity) (by linarith)
  have hE : Real.exp (-θ) ≤ Real.exp (-Real.sqrt (R / ellT L g u)) := Real.exp_le_exp.2 (neg_le_neg hθ)
  have hT : (2 * g ^ 2)⁻¹ * (2 ^ (d - 2) * (R ^ (d - 2) + 1))⁻¹ * Real.exp (-θ) ≤ tailT d L g u (zdistInf d L x : ℕ) := by
    refine le_trans ?_ hge
    exact mul_le_mul (mul_le_mul hA hPI (inv_nonneg.2 (by positivity)) (inv_nonneg.2 (by linarith))) hE (Real.exp_pos _).le
      (mul_nonneg (inv_nonneg.2 (by linarith)) (iniTermI_PI_nonneg x))
  have hd2 : (2 : ℝ) ^ (d - 2) ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have hP0 : 0 < R ^ (d - 2) + 1 := by positivity
  have e1 : (2 * g ^ 2)⁻¹ * (2 ^ (d - 2) * (R ^ (d - 2) + 1))⁻¹ = (2 ^ (d - 1) * (g ^ 2 * (R ^ (d - 2) + 1)))⁻¹ := by
    have : (2 : ℝ) ^ (d - 1) = 2 * 2 ^ (d - 2) := by
      rw [← pow_succ']; congr 1; omega
    rw [this, ← mul_inv]; congr 1; ring
  rw [e1] at hT
  have hexp : Real.exp θ * Real.exp (-θ) = 1 := by rw [← Real.exp_add]; simp
  calc (g ^ 2 * Wd)⁻¹ * (R ^ (d - 2) + 1)⁻¹ = Wd⁻¹ * (g ^ 2 * (R ^ (d - 2) + 1))⁻¹ := by
        rw [mul_inv, mul_inv]; ring
    _ ≤ Wd⁻¹ * (2 ^ d * Real.exp θ * ((2 ^ (d - 1) * (g ^ 2 * (R ^ (d - 2) + 1)))⁻¹ * Real.exp (-θ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have : (2 ^ d * Real.exp θ * ((2 ^ (d - 1) * (g ^ 2 * (R ^ (d - 2) + 1)))⁻¹ * Real.exp (-θ))) =
            (2 ^ d / 2 ^ (d - 1)) * (g ^ 2 * (R ^ (d - 2) + 1))⁻¹ * (Real.exp θ * Real.exp (-θ)) := by
          rw [mul_inv]; field_simp
        rw [this, hexp, mul_one]
        have h2 : (1 : ℝ) ≤ 2 ^ d / 2 ^ (d - 1) := by
          rw [le_div_iff₀ (by positivity)]
          exact (one_mul _).le.trans (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _))
        calc (g ^ 2 * (R ^ (d - 2) + 1))⁻¹ = 1 * (g ^ 2 * (R ^ (d - 2) + 1))⁻¹ := (one_mul _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ ≤ Wd⁻¹ * (2 ^ d * Real.exp θ * tailT d L g u (zdistInf d L x : ℕ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT (by positivity)) (by positivity)
    _ = _ := by ring

/-- `σ₁ = σ₂`: the short-range initial term is `≤ 2 C_s Θ (a P₀ + W^{-D})` (`(prop:ThfadC_short)`, no loss in `ρ`). -/
theorem iniTermI_rl_same (d : ℕ) (Λ κm : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) (hκm : 0 < κm) :
    ∃ Kc : ℝ, 0 < Kc ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g W D D₁ E s u Θ a P₀ lam₀ : ℝ),
      0 < g → g ≤ Λ → 0 < W → |E| ≤ 2 → κm ≤ (mE E).im → 0 ≤ s → s ≤ u → u < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u →
      1 ≤ Θ → 0 ≤ lam₀ → lam₀ ≤ 2 * a → 0 ≤ a → W ^ (-D₁) ≤ W ^ (-D) → Kc ≤ Θ ^ 3 →
      ∀ σ : Fin 2 → Bool, σ 0 = σ 1 → ∀ X : (Fin 2 → Zd d L) → ℂ,
        (∀ b, ‖X b‖ ≤ Θ * (lam₀ * (W ^ d)⁻¹ * tailT d L g s (zdistInf d L (b 0 - b 1) : ℕ) + W ^ (-D₁))) →
        ∀ x : Fin 2 → Zd d L, (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ) ≤ P₀ →
          ‖RBM.Ind.Ugen d L g E σ s u X x‖ ≤ Θ ^ 4 * (a * P₀ + W ^ (-D)) := by
  obtain ⟨Cs, hCs, H⟩ := iniTermI_core_same d Λ κm hd hΛ hκm
  refine ⟨2 * Cs, by positivity, ?_⟩
  intro L _ hL g W D D₁ E s u Θ a P₀ lam₀ hg hgΛ hW hE hκ hs hsu hu hreg hΘ hlam hlam2 ha hF hK σ hσ X hX x hP
  have h := H L hL g W D₁ E s u Θ lam₀ hg hgΛ hW hE hκ hs hsu hu hreg (by linarith) hlam σ hσ X hX x
  have hτ0 : 0 ≤ (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ) := by
    have := tailT_nonneg (d := d) (L := L) (g := g) (t := u) (Nat.cast_nonneg (zdistInf d L (x 0 - x 1)))
    positivity
  have hP0 : 0 ≤ P₀ := hτ0.trans hP
  have h1 : lam₀ * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ) ≤ 2 * a * P₀ := by
    rw [mul_assoc]; exact mul_le_mul hlam2 hP hτ0 (by positivity)
  have hF0 : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  have hΘ0 : 0 ≤ Θ := by linarith
  have haP : 0 ≤ a * P₀ := mul_nonneg ha hP0
  calc ‖RBM.Ind.Ugen d L g E σ s u X x‖ ≤ Cs * Θ * (lam₀ * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ) + W ^ (-D₁)) := h
    _ ≤ Cs * Θ * (2 * (a * P₀) + W ^ (-D)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
    _ ≤ (2 * Cs) * Θ * (a * P₀ + W ^ (-D)) := by
        have : 0 ≤ Cs * Θ := by positivity
        nlinarith [mul_nonneg this haP, mul_nonneg this hF0]
    _ ≤ Θ ^ 3 * Θ * (a * P₀ + W ^ (-D)) := by
        gcongr
    _ = _ := by ring

/-- `σ₁ ≠ σ₂`, `ρ ≤ Γ₀` (`ρ ≤ (log W)^{10}` or any polylog): the `ρ`-lossy bound `(uwp2-92kj)` twice. -/
theorem iniTermI_rl_lossy (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) :
    ∃ Kc : ℝ, 0 < Kc ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g W D D₁ E s u Θ a P₀ lam₀ Γ₀ : ℝ),
      0 < g → g ≤ Λ → 0 < W → |E| ≤ 2 → 0 ≤ s → s ≤ u → u < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u →
      1 ≤ Θ → 0 ≤ lam₀ → lam₀ ≤ 2 * a → 0 ≤ a → 1 ≤ Γ₀ → (1 - s) / (1 - u) ≤ Γ₀ →
      (1 - s) / (1 - u) * ((1 - s) / (1 - u)) * W ^ (-D₁) ≤ W ^ (-D) → Kc * Γ₀ ≤ Θ ^ 3 →
      ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ X : (Fin 2 → Zd d L) → ℂ,
        (∀ b, ‖X b‖ ≤ Θ * (lam₀ * (W ^ d)⁻¹ * tailT d L g s (zdistInf d L (b 0 - b 1) : ℕ) + W ^ (-D₁))) →
        ∀ x : Fin 2 → Zd d L, (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ) ≤ P₀ →
          ‖RBM.Ind.Ugen d L g E σ s u X x‖ ≤ Θ ^ 4 * (a * P₀ + W ^ (-D)) := by
  obtain ⟨Cl, hCl, H⟩ := iniTermI_core_lossy d Λ hd hΛ
  refine ⟨2 * Cl, by positivity, ?_⟩
  intro L _ hL g W D D₁ E s u Θ a P₀ lam₀ Γ₀ hg hgΛ hW hE hs hsu hu hreg hΘ hlam hlam2 ha hΓ hρΓ hρF hK σ hσ X hX x hP
  have h := H L hL g W D₁ E s u Θ lam₀ hg hgΛ hW hE hs hsu hu hreg (by linarith) hlam σ hσ X hX x
  set ρ : ℝ := (1 - s) / (1 - u) with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg (by linarith) (by linarith)
  have hτ0 : 0 ≤ (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ) := by
    have := tailT_nonneg (d := d) (L := L) (g := g) (t := u) (Nat.cast_nonneg (zdistInf d L (x 0 - x 1)))
    positivity
  have hP0 : 0 ≤ P₀ := hτ0.trans hP
  have h1 : ρ * (lam₀ * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ)) ≤ Γ₀ * (2 * a * P₀) := by
    rw [mul_assoc]
    exact mul_le_mul hρΓ (mul_le_mul hlam2 hP hτ0 (by positivity)) (by positivity) (by linarith)
  have hF0 : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  have hΘ0 : 0 ≤ Θ := by linarith
  have haP : 0 ≤ a * P₀ := mul_nonneg ha hP0
  have hCΘ : 0 ≤ Cl * Θ := by positivity
  calc ‖RBM.Ind.Ugen d L g E σ s u X x‖ ≤ Cl * Θ * (ρ * (lam₀ * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ) +
        ρ * W ^ (-D₁))) := h
    _ ≤ Cl * Θ * (Γ₀ * (2 * a * P₀) + W ^ (-D)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCΘ
        have : ρ * (lam₀ * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ) + ρ * W ^ (-D₁)) =
            ρ * (lam₀ * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ)) + ρ * ρ * W ^ (-D₁) := by ring
        rw [this]; linarith
    _ ≤ (2 * Cl * Γ₀) * Θ * (a * P₀ + W ^ (-D)) := by
        have e : 2 * Cl * Γ₀ * Θ * (a * P₀ + W ^ (-D)) - Cl * Θ * (Γ₀ * (2 * a * P₀) + W ^ (-D)) =
            Cl * Θ * ((2 * Γ₀ - 1) * W ^ (-D)) := by ring
        have : 0 ≤ Cl * Θ * ((2 * Γ₀ - 1) * W ^ (-D)) := by
          have : 0 ≤ 2 * Γ₀ - 1 := by linarith
          positivity
        linarith
    _ ≤ Θ ^ 3 * Θ * (a * P₀ + W ^ (-D)) := by
        have : 2 * Cl * Γ₀ ≤ Θ ^ 3 := by linarith [hK]
        gcongr
    _ = _ := by ring

/-- `σ₁ ≠ σ₂`, outside the window `(eq:ells_to_ellt2)`: the whole term is `ρ`-lossless up to the explicit floor `htail ≤ W^{-D}`. -/
theorem iniTermI_rl_tail (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) :
    ∃ Kc C c : ℝ, 0 < Kc ∧ 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g W D D₁ E s u Θ a P₀ lam₀ r₁ Yw : ℝ),
      0 < g → g ≤ Λ → 0 < W → |E| ≤ 2 → 0 ≤ s → s ≤ u → u < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u →
      1 ≤ Θ → 0 ≤ lam₀ → lam₀ ≤ 2 * a → 0 ≤ a → (1 - s) / (1 - u) * W ^ (-D₁) ≤ W ^ (-D) → Kc ≤ Θ ^ 3 →
      ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ X : (Fin 2 → Zd d L) → ℂ,
        (∀ b, ‖X b‖ ≤ Θ * (lam₀ * (W ^ d)⁻¹ * tailT d L g s (zdistInf d L (b 0 - b 1) : ℕ) + W ^ (-D₁))) →
        ∀ x : Fin 2 → Zd d L, 2 * r₁ + Yw < ((zdistInf d L (x 0 - x 1) : ℕ) : ℝ) →
          (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ) ≤ P₀ →
          (Fintype.card (Zd d L) : ℝ) ^ 2 * ((1 - u)⁻¹) ^ 2 *
            (2 * C * Real.exp (-(c * r₁ / ellT L g u)) * (Θ * (lam₀ * (W ^ d)⁻¹ * ((1 + 2 ^ (d - 1)) * (g ^ 2)⁻¹) + W ^ (-D₁))) +
              Θ * (lam₀ * (W ^ d)⁻¹ * ((1 + 2 ^ (d - 1)) * ((g ^ 2)⁻¹ * Real.exp (-Real.sqrt (Yw / ellT L g s)))) + W ^ (-D₁))) ≤
            W ^ (-D) →
          ‖RBM.Ind.Ugen d L g E σ s u X x‖ ≤ Θ ^ 4 * (a * P₀ + W ^ (-D)) := by
  obtain ⟨K, C, c, hK, hC, hc, H⟩ := iniTermI_mixed_tail d Λ hd hΛ
  refine ⟨2 * K + 1, C, c, by positivity, hC, hc, ?_⟩
  intro L _ hL g W D D₁ E s u Θ a P₀ lam₀ r₁ Yw hg hgΛ hW hE hs hsu hu hreg hΘ hlam hlam2 ha hρF hKc σ hσ X hX x hr hP htail
  have h := H L hL g W D₁ E s u Θ lam₀ r₁ Yw hg hgΛ hW hE hs hsu hu hreg (by linarith) hlam σ hσ X hX x hr
  have hτ0 : 0 ≤ (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ) := by
    have := tailT_nonneg (d := d) (L := L) (g := g) (t := u) (Nat.cast_nonneg (zdistInf d L (x 0 - x 1)))
    positivity
  have hP0 : 0 ≤ P₀ := hτ0.trans hP
  have h1 : lam₀ * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ) ≤ 2 * a * P₀ := by
    rw [mul_assoc]; exact mul_le_mul hlam2 hP hτ0 (by positivity)
  have hF0 : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  have hΘ0 : 0 ≤ Θ := by linarith
  have haP : 0 ≤ a * P₀ := mul_nonneg ha hP0
  have hKΘ : 0 ≤ K * Θ := by positivity
  calc ‖RBM.Ind.Ugen d L g E σ s u X x‖ ≤ K * Θ * (lam₀ * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ) +
        (1 - s) / (1 - u) * W ^ (-D₁)) + _ := h
    _ ≤ K * Θ * (2 * (a * P₀) + W ^ (-D)) + W ^ (-D) := add_le_add (mul_le_mul_of_nonneg_left (by linarith) hKΘ) htail
    _ ≤ ((2 * K + 1) * Θ) * (a * P₀ + W ^ (-D)) := by
        have e : (2 * K + 1) * Θ * (a * P₀ + W ^ (-D)) - (K * Θ * (2 * (a * P₀) + W ^ (-D)) + W ^ (-D)) =
            K * Θ * W ^ (-D) + (Θ - 1) * W ^ (-D) + Θ * (a * P₀) := by ring
        have : 0 ≤ K * Θ * W ^ (-D) + (Θ - 1) * W ^ (-D) + Θ * (a * P₀) := by
          have : 0 ≤ Θ - 1 := by linarith
          positivity
        linarith
    _ ≤ Θ ^ 3 * Θ * (a * P₀ + W ^ (-D)) := by gcongr
    _ = _ := by ring

/-- The final polynomial bookkeeping of `iniTermI_rl_in`. -/
theorem iniTermI_assemble {Θ Γ x F Km c κi fS T1 T2 T3 T4 U : ℝ} (hΘ : 1 ≤ Θ) (hΓ : 1 ≤ Γ) (hx : 0 ≤ x) (hF : 0 ≤ F)
    (hKm : 0 ≤ Km) (hc : 0 ≤ c) (hκ : 0 ≤ κi) (hfS : fS ≤ c * Θ * Γ * x) (hT1 : T1 ≤ Θ * (2 * x + F))
    (hT2 : T2 ≤ 2 * c * Θ * Γ * x) (hT3 : T3 ≤ F) (hT4 : T4 ≤ κi * Θ * x)
    (hU : U ≤ fS + Km * (T1 + T2 + T3 + T4)) :
    U ≤ Θ * ((c + Km * (4 + 2 * c + κi)) * Γ) * (x + F) := by
  set Y : ℝ := Θ * Γ with hY
  have hY1 : 1 ≤ Y := by nlinarith
  have hΘ0 : 0 ≤ Θ := by linarith
  have hΘY : Θ ≤ Y := by nlinarith
  have hxΘ : Θ * x ≤ Y * x := mul_le_mul_of_nonneg_right hΘY hx
  have hFΘ : Θ * F ≤ Y * F := mul_le_mul_of_nonneg_right hΘY hF
  have hFY : F ≤ Y * F := by nlinarith
  have b1 : T1 + T2 + T3 + T4 ≤ (2 + 2 * c + κi) * (Y * x) + 2 * (Y * F) := by
    have e1 : T1 ≤ 2 * (Y * x) + Y * F := by nlinarith
    have e2 : T2 ≤ 2 * c * (Y * x) := by rw [hY]; nlinarith
    have e4 : T4 ≤ κi * (Y * x) := by nlinarith [mul_le_mul_of_nonneg_left hxΘ hκ]
    nlinarith
  have b2 : fS ≤ c * (Y * x) := by rw [hY]; nlinarith
  have b3 : U ≤ (c + Km * (2 + 2 * c + κi)) * (Y * x) + 2 * Km * (Y * F) := by
    have := mul_le_mul_of_nonneg_left b1 hKm
    nlinarith
  have e : Θ * ((c + Km * (4 + 2 * c + κi)) * Γ) * (x + F) =
      (c + Km * (4 + 2 * c + κi)) * (Y * x) + (c + Km * (4 + 2 * c + κi)) * (Y * F) := by
    rw [hY]; ring
  rw [e]
  have h1 : (c + Km * (2 + 2 * c + κi)) * (Y * x) ≤ (c + Km * (4 + 2 * c + κi)) * (Y * x) := by
    have : 0 ≤ Y * x := by positivity
    have : 0 ≤ Km * (Y * x) := by positivity
    nlinarith
  have h2 : 2 * Km * (Y * F) ≤ (c + Km * (4 + 2 * c + κi)) * (Y * F) := by
    have : 0 ≤ Y * F := by positivity
    have : 0 ≤ Km * (Y * F) := by positivity
    have : 0 ≤ c * (Y * F) := by positivity
    have : 0 ≤ Km * (c * (Y * F)) := by positivity
    have : 0 ≤ Km * (κi * (Y * F)) := by positivity
    nlinarith
  linarith

set_option maxHeartbeats 1000000 in
-- long calc chains with many `positivity`/`gcongr` side goals
/-- `σ₁ ≠ σ₂`, in the window (`ρ > (log W)^{10}`, `|a₁-a₂| ≲ (log W)^{3/2} ℓ_u`): `f^{near}`, the Ward term and `f^{far}`
(`(iksjuwjx3)`, `(eq:boundga)`, `lem;CLT`) give `≤ Θ⁴ (a P₀ + W^{-D})`. -/
theorem iniTermI_rl_in (d : ℕ) (Λ κm : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) (hκm : 0 < κm) :
    ∃ Kc : ℝ, 0 < Kc ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g W D D₁ E s u Θ a P₀ lam₀ lW Bs : ℝ),
      0 < g → g ≤ Λ → 0 < W → |E| ≤ 2 → 0 ≤ s → s ≤ u → u < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u → 1 - s ≤ g ^ 2 →
      1 ≤ lW → 1 ≤ Θ → 0 ≤ lam₀ → lam₀ ≤ 2 * a → 0 ≤ a → 0 ≤ Bs →
      (1 - s) / (1 - u) * W ^ (-D₁) ≤ W ^ (-D) → (1 - s) / (1 - u) * Bs ≤ 4 * a →
      Kc * (lW ^ 14 * Real.exp (lW ^ (3 / 4 : ℝ))) ≤ Θ ^ 3 →
      ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ X : (Fin 2 → Zd d L) → ℂ,
        (∀ b, ‖X b‖ ≤ Θ * (lam₀ * (W ^ d)⁻¹ * tailT d L g s (zdistInf d L (b 0 - b 1) : ℕ) + W ^ (-D₁))) →
        (∀ b₁ : Zd d L, ‖∑ b₂ : Zd d L, X ![b₁, b₂]‖ ≤ Θ * (Bs * (W ^ d)⁻¹ / κm) / (1 - s)) →
        ∀ (x : Fin 2 → Zd d L) (P : Zd d L → Prop) [DecidablePred P],
          (∀ b₁, P b₁ ↔ (lW ^ 4 * ellT L g s < ((zdistInf d L (b₁ - x 0) : ℕ) : ℝ) ∧
            lW ^ 4 * ellT L g s < ((zdistInf d L (b₁ - x 1) : ℕ) : ℝ))) →
          (g ^ 2 * W ^ d)⁻¹ * ((((zdistInf d L (x 0 - x 1) : ℕ) : ℝ) ^ (d - 2) + 1)⁻¹) ≤
            2 ^ d * Real.exp (lW ^ (3 / 4 : ℝ)) * ((W ^ d)⁻¹ * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ)) →
          (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ) ≤ P₀ →
          Θ * (Fintype.card (Zd d L) : ℝ) ^ 2 * (g ^ 2)⁻¹ * (1 - u)⁻¹ *
            (W ^ (-D₁) + lam₀ * (W ^ d)⁻¹ * (g ^ 2)⁻¹ * Real.exp (-Real.sqrt (lW ^ 3))) ≤ W ^ (-D) →
          ‖iniTermI_fSum d L g s u X x P‖ ≤
            Θ * (a * ((g ^ 2 * W ^ d)⁻¹ * ((((zdistInf d L (x 0 - x 1) : ℕ) : ℝ) ^ (d - 2) + 1)⁻¹))) →
          ‖RBM.Ind.Ugen d L g E σ s u X x‖ ≤ Θ ^ 4 * (a * P₀ + W ^ (-D)) := by
  obtain ⟨Km, hKm, H⟩ := iniTermI_mixed_bound d Λ hd hΛ
  refine ⟨2 ^ d + Km * (4 + 2 * 2 ^ d + 4 / κm), by positivity, ?_⟩
  intro L _ hL g W D D₁ E s u Θ a P₀ lam₀ lW Bs hg hgΛ hW hE hs hsu hu hreg hregs1 hlW hΘ hlam hlam2 ha hBs hρF hρB hK
    σ hσ X hX hXY x P _ hP hcmp hτ hT3 hfar
  have hu1 : 0 < 1 - u := by linarith
  have hs1 : 0 < 1 - s := by linarith
  set ρ : ℝ := (1 - s) / (1 - u) with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg hs1.le hu1.le
  set r : ℝ := ((zdistInf d L (x 0 - x 1) : ℕ) : ℝ) with hr
  set τu : ℝ := (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ) with hτu
  have hτ0 : 0 ≤ τu := by
    have := tailT_nonneg (d := d) (L := L) (g := g) (t := u) (Nat.cast_nonneg (zdistInf d L (x 0 - x 1)))
    positivity
  have hP0 : 0 ≤ P₀ := hτ0.trans hτ
  have hΘ0 : 0 ≤ Θ := by linarith
  have hF0 : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  set e : ℝ := Real.exp (lW ^ (3 / 4 : ℝ)) with he
  have he1 : 1 ≤ e := Real.one_le_exp (by positivity)
  set Γ : ℝ := lW ^ 14 * e with hΓ
  have hlW14 : 1 ≤ lW ^ 14 := one_le_pow₀ hlW
  have hΓ1 : 1 ≤ Γ := by nlinarith
  have heΓ : e ≤ Γ := by nlinarith
  have hΓ0 : 0 ≤ Γ := by linarith
  have haP : 0 ≤ a * P₀ := mul_nonneg ha hP0
  have hh := H L hL g W D₁ E s u Θ lam₀ lW (Θ * (Bs * (W ^ d)⁻¹ / κm)) hg hgΛ hW hE hs hsu hu hreg hregs1 hΘ0 hlam hlW
    (by positivity) σ hσ X hX hXY x P hP
  set Bq : ℝ := (g ^ 2 * W ^ d)⁻¹ * ((r ^ (d - 2) + 1)⁻¹) with hBq
  have hBq' : Bq ≤ 2 ^ d * e * τu := hcmp
  have hpa : r ^ (d - 2) + 1 ≤ (r + 1) ^ (d - 2) := by
    have := pow_add_pow_le (Nat.cast_nonneg (zdistInf d L (x 0 - x 1))) (zero_le_one' ℝ) (n := d - 2) (by omega)
    simpa [hr] using this
  have hPI : iniTermI_PI d L (x 0 - x 1) ≤ (r ^ (d - 2) + 1)⁻¹ := by
    unfold iniTermI_PI; rw [← hr]
    exact inv_anti₀ (by positivity) hpa
  have hPI0 := iniTermI_PI_nonneg (d := d) (L := L) (x 0 - x 1)
  have hlW0 : 0 ≤ lW := by linarith
  have hT1 : Θ * (lam₀ * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ) + ρ * W ^ (-D₁)) ≤
      Θ * (2 * (a * P₀) + W ^ (-D)) := by
    refine mul_le_mul_of_nonneg_left ?_ hΘ0
    have : lam₀ * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ) ≤ 2 * a * P₀ := by
      rw [mul_assoc]; exact mul_le_mul hlam2 hτ hτ0 (by positivity)
    linarith
  have hT2 : Θ * (lam₀ * (W ^ d)⁻¹) * (g ^ 2)⁻¹ * lW ^ 14 * iniTermI_PI d L (x 0 - x 1) ≤
      2 * 2 ^ d * Θ * Γ * (a * P₀) := by
    have e1 : Θ * (lam₀ * (W ^ d)⁻¹) * (g ^ 2)⁻¹ * lW ^ 14 * iniTermI_PI d L (x 0 - x 1) =
        Θ * lW ^ 14 * lam₀ * ((g ^ 2 * W ^ d)⁻¹ * iniTermI_PI d L (x 0 - x 1)) := by
      rw [mul_inv]; ring
    have e3 : (g ^ 2 * W ^ d)⁻¹ * iniTermI_PI d L (x 0 - x 1) ≤ 2 ^ d * e * P₀ :=
      (mul_le_mul_of_nonneg_left hPI (by positivity)).trans (hBq'.trans (mul_le_mul_of_nonneg_left hτ (by positivity)))
    rw [e1]
    calc Θ * lW ^ 14 * lam₀ * ((g ^ 2 * W ^ d)⁻¹ * iniTermI_PI d L (x 0 - x 1))
        ≤ Θ * lW ^ 14 * (2 * a) * (2 ^ d * e * P₀) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hlam2 (by positivity)) e3 (mul_nonneg (by positivity) hPI0) (by positivity)
      _ = _ := by rw [hΓ]; ring
  have hT4 : ρ * (Θ * (Bs * (W ^ d)⁻¹ / κm)) * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ) ≤ 4 / κm * Θ * (a * P₀) := by
    have e1 : ρ * (Θ * (Bs * (W ^ d)⁻¹ / κm)) * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ) =
        Θ / κm * (ρ * Bs) * τu := by rw [hτu]; field_simp
    rw [e1]
    calc Θ / κm * (ρ * Bs) * τu ≤ Θ / κm * (4 * a) * P₀ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hρB (by positivity)) hτ hτ0 (by positivity)
      _ = _ := by field_simp
  have hfar' : ‖iniTermI_fSum d L g s u X x P‖ ≤ 2 ^ d * Θ * Γ * (a * P₀) := by
    refine hfar.trans ?_
    have e1 : Bq ≤ 2 ^ d * e * P₀ := hBq'.trans (mul_le_mul_of_nonneg_left hτ (by positivity))
    have e2 : 2 ^ d * e * P₀ ≤ 2 ^ d * Γ * P₀ := by gcongr
    calc Θ * (a * Bq) ≤ Θ * (a * (2 ^ d * Γ * P₀)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (e1.trans e2) ha) hΘ0
      _ = _ := by ring
  have hfin := iniTermI_assemble hΘ hΓ1 haP hF0 hKm.le (by positivity : (0 : ℝ) ≤ 2 ^ d) (by positivity : (0 : ℝ) ≤ 4 / κm)
    hfar' hT1 hT2 hT3 hT4 hh
  calc ‖RBM.Ind.Ugen d L g E σ s u X x‖ ≤ Θ * ((2 ^ d + Km * (4 + 2 * 2 ^ d + 4 / κm)) * Γ) * (a * P₀ + W ^ (-D)) := hfin
    _ ≤ Θ * Θ ^ 3 * (a * P₀ + W ^ (-D)) := by gcongr
    _ = _ := by ring

/-- `ℓ_u = √ρ ℓ_s` in regime (i): `ρ > (log W)^{10}` gives `ℓ_u ≥ (log W)^5 ℓ_s` (`(eq:ells_to_ellt)`, `3_5:2113`). -/
theorem iniTermI_ell5 {L : ℕ} [NeZero L] {g s u lW : ℝ} (hL : 3 ≤ L) (hg : 0 < g) (hsu : s ≤ u) (hu : u < 1)
    (hreg : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u) (hregs1 : 1 - s ≤ g ^ 2) (hlW : 0 ≤ lW)
    (hρ : lW ^ 10 < (1 - s) / (1 - u)) : lW ^ 5 * ellT L g s ≤ ellT L g u := by
  have hs1 : s < 1 := by linarith
  have hu1 : 0 < 1 - u := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hregs : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - s := hreg.trans (by linarith)
  have hℓs : ellT L g s = g / Real.sqrt (1 - s) := iniTermI_ellT_eq hg hs1 hregs1 hregs (by linarith)
  have hℓu : ellT L g u = g / Real.sqrt (1 - u) := iniTermI_ellT_eq hg hu (by linarith) hreg (by linarith)
  have hsq : (ellT L g u) ^ 2 = (1 - s) / (1 - u) * (ellT L g s) ^ 2 := by
    rw [hℓs, hℓu, div_pow, div_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 1 - s by linarith), Real.sq_sqrt hu1.le]
    have : (0 : ℝ) < 1 - s := by linarith
    field_simp
  have h1 : (lW ^ 5 * ellT L g s) ^ 2 ≤ (ellT L g u) ^ 2 := by
    rw [hsq, mul_pow, ← pow_mul]
    exact mul_le_mul_of_nonneg_right hρ.le (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (mul_nonneg (pow_nonneg hlW 5) (by have := one_le_ellT (L := L) (g := g) (t := s) hL1; linarith))
    ellT_nonneg (by norm_num)).1 h1

set_option maxHeartbeats 1000000 in
-- long calc chains with many `positivity`/`gcongr` side goals
/-- **All cases at once** (`(iksjuwjx0)`, `3_5:2072`, case (i)): `σ₁ = σ₂` (`prop:ThfadC_short`); `σ₁ ≠ σ₂` with `ρ ≤ (log W)^{10}`
(`(uwp2-92kj)` twice); `ρ > (log W)^{10}`, outside the window `(eq:ells_to_ellt2)` (exponential decay), inside the window
(`f^{near}`, Ward, `lem;CLT`).  The conclusion is `‖𝒰 X‖ ≤ Θ⁴ (a P₀ + W^{-D})`, `Θ = N^{τ/4}`, `a = A^{-1/5}`, `P₀ = W^{-d}𝒯̃`. -/
theorem iniTermI_rl_all (d : ℕ) (Λ κm : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) (hκm : 0 < κm) :
    ∃ K₀ C c : ℝ, 0 < K₀ ∧ 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g W D D₁ E s u Θ a P₀ lam₀ lW Bs : ℝ),
      0 < g → g ≤ Λ → 0 < W → |E| ≤ 2 → κm ≤ (mE E).im → 0 ≤ s → s ≤ u → u < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - u →
      1 - s ≤ g ^ 2 → 2 ≤ lW → 1 ≤ Θ → 0 ≤ lam₀ → lam₀ ≤ 2 * a → 0 ≤ a → 0 ≤ Bs → W ^ (-D₁) ≤ W ^ (-D) →
      (1 - s) / (1 - u) * W ^ (-D₁) ≤ W ^ (-D) → (1 - s) / (1 - u) * ((1 - s) / (1 - u)) * W ^ (-D₁) ≤ W ^ (-D) →
      (1 - s) / (1 - u) * Bs ≤ 4 * a → K₀ * (lW ^ 14 * Real.exp (lW ^ (3 / 4 : ℝ))) ≤ Θ ^ 3 →
      ∀ (σ : Fin 2 → Bool) (X : (Fin 2 → Zd d L) → ℂ),
        (∀ b, ‖X b‖ ≤ Θ * (lam₀ * (W ^ d)⁻¹ * tailT d L g s (zdistInf d L (b 0 - b 1) : ℕ) + W ^ (-D₁))) →
        ∀ (x : Fin 2 → Zd d L), (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (x 0 - x 1) : ℕ) ≤ P₀ →
        ∀ (P : Zd d L → Prop) [DecidablePred P],
          (∀ b₁, P b₁ ↔ (lW ^ 4 * ellT L g s < ((zdistInf d L (b₁ - x 0) : ℕ) : ℝ) ∧
            lW ^ 4 * ellT L g s < ((zdistInf d L (b₁ - x 1) : ℕ) : ℝ))) →
          (σ 0 ≠ σ 1 → lW ^ 10 < (1 - s) / (1 - u) →
            (((zdistInf d L (x 0 - x 1) : ℕ) : ℝ) ≤ (1 / 2 : ℝ) * lW ^ (3 / 2 : ℝ) * ellT L g u + lW ^ (5 / 2 : ℝ) * ellT L g s →
              (∀ b₁ : Zd d L, ‖∑ b₂ : Zd d L, X ![b₁, b₂]‖ ≤ Θ * (Bs * (W ^ d)⁻¹ / κm) / (1 - s)) ∧
              Θ * (Fintype.card (Zd d L) : ℝ) ^ 2 * (g ^ 2)⁻¹ * (1 - u)⁻¹ *
                (W ^ (-D₁) + lam₀ * (W ^ d)⁻¹ * (g ^ 2)⁻¹ * Real.exp (-Real.sqrt (lW ^ 3))) ≤ W ^ (-D) ∧
              ‖iniTermI_fSum d L g s u X x P‖ ≤
                Θ * (a * ((g ^ 2 * W ^ d)⁻¹ * ((((zdistInf d L (x 0 - x 1) : ℕ) : ℝ) ^ (d - 2) + 1)⁻¹)))) ∧
            ((1 / 2 : ℝ) * lW ^ (3 / 2 : ℝ) * ellT L g u + lW ^ (5 / 2 : ℝ) * ellT L g s <
                ((zdistInf d L (x 0 - x 1) : ℕ) : ℝ) →
              (Fintype.card (Zd d L) : ℝ) ^ 2 * ((1 - u)⁻¹) ^ 2 *
                (2 * C * Real.exp (-(c * (1 / 4 * lW ^ (3 / 2 : ℝ) * ellT L g u) / ellT L g u)) *
                    (Θ * (lam₀ * (W ^ d)⁻¹ * ((1 + 2 ^ (d - 1)) * (g ^ 2)⁻¹) + W ^ (-D₁))) +
                  Θ * (lam₀ * (W ^ d)⁻¹ * ((1 + 2 ^ (d - 1)) * ((g ^ 2)⁻¹ *
                    Real.exp (-Real.sqrt (lW ^ (5 / 2 : ℝ) * ellT L g s / ellT L g s)))) + W ^ (-D₁))) ≤ W ^ (-D))) →
          ‖RBM.Ind.Ugen d L g E σ s u X x‖ ≤ Θ ^ 4 * (a * P₀ + W ^ (-D)) := by
  obtain ⟨Ks, hKs, Hs⟩ := iniTermI_rl_same d Λ κm hd hΛ hκm
  obtain ⟨Kl, hKl, Hl⟩ := iniTermI_rl_lossy d Λ hd hΛ
  obtain ⟨Kt, C, c, hKt, hC, hc, Ht⟩ := iniTermI_rl_tail d Λ hd hΛ
  obtain ⟨Ki, hKi, Hi⟩ := iniTermI_rl_in d Λ κm hd hΛ hκm
  refine ⟨Ks + Kl + Kt + Ki, C, c, by positivity, hC, hc, ?_⟩
  intro L _ hL g W D D₁ E s u Θ a P₀ lam₀ lW Bs hg hgΛ hW hE hκ hs hsu hu hreg hregs1 hlW hΘ hlam hlam2 ha hBs hF hρF1 hρF2
    hρB hK σ X hX x hP₀ P _ hP hmix
  have hlW1 : 1 ≤ lW := by linarith
  have hlW14 : 1 ≤ lW ^ 14 * Real.exp (lW ^ (3 / 4 : ℝ)) := by
    have := one_le_pow₀ (n := 14) hlW1
    have h2 : 1 ≤ Real.exp (lW ^ (3 / 4 : ℝ)) := Real.one_le_exp (by positivity)
    nlinarith
  have hKΘ : ∀ K : ℝ, 0 ≤ K → K ≤ Ks + Kl + Kt + Ki → K ≤ Θ ^ 3 := fun K hK0 hKle =>
    hKle.trans (by
      have : (Ks + Kl + Kt + Ki) * 1 ≤ (Ks + Kl + Kt + Ki) * (lW ^ 14 * Real.exp (lW ^ (3 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left hlW14 (by positivity)
      linarith)
  by_cases hσ : σ 0 = σ 1
  · exact Hs L hL g W D D₁ E s u Θ a P₀ lam₀ hg hgΛ hW hE hκ hs hsu hu hreg hΘ hlam hlam2 ha hF
      (hKΘ Ks hKs.le (by linarith)) σ hσ X hX x hP₀
  have hσ' : σ 0 ≠ σ 1 := hσ
  by_cases hρ : (1 - s) / (1 - u) ≤ lW ^ 10
  · refine Hl L hL g W D D₁ E s u Θ a P₀ lam₀ (lW ^ 10) hg hgΛ hW hE hs hsu hu hreg hΘ hlam hlam2 ha (one_le_pow₀ hlW1) hρ hρF2
      ?_ σ hσ' X hX x hP₀
    have : Kl * lW ^ 10 ≤ (Ks + Kl + Kt + Ki) * (lW ^ 14 * Real.exp (lW ^ (3 / 4 : ℝ))) := by
      have h1 : lW ^ 10 ≤ lW ^ 14 * Real.exp (lW ^ (3 / 4 : ℝ)) := by
        have : lW ^ 10 ≤ lW ^ 14 := pow_le_pow_right₀ hlW1 (by norm_num)
        have h2 : 1 ≤ Real.exp (lW ^ (3 / 4 : ℝ)) := Real.one_le_exp (by positivity)
        nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ lW) 14]
      have : Kl ≤ Ks + Kl + Kt + Ki := by linarith
      exact mul_le_mul this h1 (by positivity) (by positivity)
    exact this.trans hK
  push Not at hρ
  obtain ⟨hin, hout⟩ := hmix hσ' hρ
  by_cases hwin : ((zdistInf d L (x 0 - x 1) : ℕ) : ℝ) ≤ (1 / 2 : ℝ) * lW ^ (3 / 2 : ℝ) * ellT L g u + lW ^ (5 / 2 : ℝ) * ellT L g s
  · obtain ⟨hXY, hT3, hfar⟩ := hin hwin
    -- the window comparison
    have hs1 : s < 1 := by linarith
    have hu1 : 0 < 1 - u := by linarith
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
    have hℓ1 : 1 ≤ ellT L g s := one_le_ellT hL1
    have hℓ5 : lW ^ 5 * ellT L g s ≤ ellT L g u := iniTermI_ell5 hL hg hsu hu hreg hregs1 (by linarith) hρ
    have hlW0 : 0 ≤ lW := by linarith
    have hl32 : 0 ≤ lW ^ (3 / 2 : ℝ) := Real.rpow_nonneg hlW0 _
    have hl52 : lW ^ (5 / 2 : ℝ) = lW ^ (3 / 2 : ℝ) * lW := by
      rw [← Real.rpow_add_one' hlW0 (by norm_num)]; norm_num
    have hlW5 : 2 * lW ≤ lW ^ 5 := by
      have : 2 ≤ lW ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hlW 4]
      nlinarith
    have hr : ((zdistInf d L (x 0 - x 1) : ℕ) : ℝ) ≤ lW ^ (3 / 2 : ℝ) * ellT L g u := by
      have h1 : lW ^ (5 / 2 : ℝ) * ellT L g s ≤ 1 / 2 * lW ^ (3 / 2 : ℝ) * ellT L g u := by
        rw [hl52]
        have h2 : 2 * (lW * ellT L g s) ≤ ellT L g u := by
          have := mul_le_mul_of_nonneg_right hlW5 (by linarith : (0 : ℝ) ≤ ellT L g s)
          linarith
        have h3 := mul_le_mul_of_nonneg_left h2 hl32
        linarith
      linarith
    have hθ : Real.sqrt (((zdistInf d L (x 0 - x 1) : ℕ) : ℝ) / ellT L g u) ≤ lW ^ (3 / 4 : ℝ) := by
      have hℓu0 : 0 < ellT L g u := lt_of_lt_of_le one_pos (hℓ1.trans (ellT_mono hg.le hsu hu))
      have : ((zdistInf d L (x 0 - x 1) : ℕ) : ℝ) / ellT L g u ≤ lW ^ (3 / 2 : ℝ) := by
        rw [div_le_iff₀ hℓu0]; exact hr
      calc _ ≤ Real.sqrt (lW ^ (3 / 2 : ℝ)) := Real.sqrt_le_sqrt this
        _ = lW ^ (3 / 4 : ℝ) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hlW0]; norm_num
    have hWd : (0 : ℝ) < W ^ d := by positivity
    have hcmp := iniTermI_cmp hd hL1 hg hu (by linarith) hWd (x 0 - x 1) hθ
    exact Hi L hL g W D D₁ E s u Θ a P₀ lam₀ lW Bs hg hgΛ hW hE hs hsu hu hreg hregs1 hlW1 hΘ hlam hlam2 ha hBs hρF1 hρB
      ((mul_le_mul_of_nonneg_right (by linarith) (by positivity)).trans hK) σ hσ' X hX hXY x P hP hcmp hP₀ hT3 hfar
  · push Not at hwin
    exact Ht L hL g W D D₁ E s u Θ a P₀ lam₀ (1 / 4 * lW ^ (3 / 2 : ℝ) * ellT L g u) (lW ^ (5 / 2 : ℝ) * ellT L g s)
      hg hgΛ hW hE hs hsu hu hreg hΘ hlam hlam2 ha hρF1 (hKΘ Kt hKt.le (by linarith)) σ hσ' X hX x (by linarith) hP₀
      (hout hwin)

/-- The three exponentials of the floors are `≤ exp(-c₂ (log W)^{5/4})`. -/
theorem iniTermI_Estar {lW c c₂ ℓu ℓs : ℝ} (hlW : 1 ≤ lW) (hc₂0 : 0 ≤ c₂) (hc₂ : c₂ ≤ 1) (hc₂c : c₂ ≤ c / 4) (hℓu : 0 < ℓu) (hℓs : 0 < ℓs) :
    Real.exp (-Real.sqrt (lW ^ 3)) ≤ Real.exp (-(c₂ * lW ^ (5 / 4 : ℝ))) ∧
    Real.exp (-(c * (1 / 4 * lW ^ (3 / 2 : ℝ) * ℓu) / ℓu)) ≤ Real.exp (-(c₂ * lW ^ (5 / 4 : ℝ))) ∧
    Real.exp (-Real.sqrt (lW ^ (5 / 2 : ℝ) * ℓs / ℓs)) ≤ Real.exp (-(c₂ * lW ^ (5 / 4 : ℝ))) := by
  have hlW0 : 0 ≤ lW := by linarith
  have hp : lW ^ (5 / 4 : ℝ) ≤ lW ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hlW (by norm_num)
  have hp0 : 0 ≤ lW ^ (5 / 4 : ℝ) := Real.rpow_nonneg hlW0 _
  refine ⟨?_, ?_, ?_⟩
  · refine Real.exp_le_exp.2 (neg_le_neg ?_)
    have : Real.sqrt (lW ^ 3) = lW ^ (3 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hlW0]; norm_num
    rw [this]
    nlinarith
  · refine Real.exp_le_exp.2 (neg_le_neg ?_)
    have : c * (1 / 4 * lW ^ (3 / 2 : ℝ) * ℓu) / ℓu = c / 4 * lW ^ (3 / 2 : ℝ) := by field_simp
    rw [this]
    nlinarith [Real.rpow_nonneg hlW0 (3 / 2 : ℝ)]
  · refine Real.exp_le_exp.2 (neg_le_neg ?_)
    have : Real.sqrt (lW ^ (5 / 2 : ℝ) * ℓs / ℓs) = lW ^ (5 / 4 : ℝ) := by
      rw [mul_div_assoc, div_self hℓs.ne', mul_one, Real.sqrt_eq_rpow, ← Real.rpow_mul hlW0]; norm_num
    rw [this]
    nlinarith

/-- The floor of the Ward/near terms (`hT3` of `iniTermI_rl_in`) is `≤ Θ N⁶ K₃ (E_* + F₁)`. -/
theorem iniTermI_floor_T3 {Nd N G U Q Θ F₁ E₃ Es K₃ : ℝ} (hNd0 : 0 ≤ Nd) (hNd : Nd ≤ N) (hG0 : 0 ≤ G) (hG : G ≤ N)
    (hU0 : 0 ≤ U) (hU : U ≤ N ^ 2) (hQ0 : 0 ≤ Q) (hQ : Q ≤ 2) (hΘ : 0 ≤ Θ) (hN : 1 ≤ N) (hF : 0 ≤ F₁) (hE : 0 ≤ E₃)
    (hEs : E₃ ≤ Es) (hK : 2 ≤ K₃) :
    Θ * Nd ^ 2 * G * U * (F₁ + Q * E₃) ≤ Θ * N ^ 6 * K₃ * (Es + F₁) := by
  have hEs0 : 0 ≤ Es := hE.trans hEs
  have h1 : Nd ^ 2 * G * U ≤ N ^ 2 * N * N ^ 2 :=
    mul_le_mul (mul_le_mul (pow_le_pow_left₀ hNd0 hNd 2) hG (by positivity) (by positivity)) hU hU0 (by positivity)
  have h2 : N ^ 2 * N * N ^ 2 ≤ N ^ 6 := by
    have : N ^ 2 * N * N ^ 2 = N ^ 5 := by ring
    rw [this]; exact pow_le_pow_right₀ hN (by norm_num)
  have h3 : F₁ + Q * E₃ ≤ K₃ * (Es + F₁) := by nlinarith [mul_le_mul hQ hEs hE (by norm_num : (0:ℝ) ≤ 2)]
  calc Θ * Nd ^ 2 * G * U * (F₁ + Q * E₃) = Θ * (Nd ^ 2 * G * U) * (F₁ + Q * E₃) := by ring
    _ ≤ Θ * N ^ 6 * (K₃ * (Es + F₁)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (h1.trans h2) hΘ) h3 (by positivity) (by positivity)
    _ = _ := by ring

/-- The floor of the window complement (`htail` of `iniTermI_rl_tail`) is `≤ Θ N⁶ K₃ (E_* + F₁)`, `K₃ ≥ 2 C (2 c₀ + 1) + 2 c₀ + 2`. -/
theorem iniTermI_floor_tail {Nd N U Q Θ F₁ e₁ e₂ Es C c₀ K₃ : ℝ} (hNd0 : 0 ≤ Nd) (hNd : Nd ≤ N) (hU0 : 0 ≤ U) (hU : U ≤ N ^ 2)
    (hQ0 : 0 ≤ Q) (hQ : Q ≤ 2) (hΘ : 0 ≤ Θ) (hN : 1 ≤ N) (hF : 0 ≤ F₁) (hF1 : F₁ ≤ 1) (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂)
    (he₁s : e₁ ≤ Es) (he₂s : e₂ ≤ Es) (hC : 0 ≤ C) (hc₀ : 1 ≤ c₀) (hK : 2 * C * (2 * c₀ + 1) + 2 * c₀ + 2 ≤ K₃) :
    Nd ^ 2 * U ^ 2 * (2 * C * e₁ * (Θ * (c₀ * Q + F₁)) + Θ * (c₀ * Q * e₂ + F₁)) ≤ Θ * N ^ 6 * K₃ * (Es + F₁) := by
  have hEs0 : 0 ≤ Es := he₁.trans he₁s
  have h1 : Nd ^ 2 * U ^ 2 ≤ N ^ 6 := by
    calc Nd ^ 2 * U ^ 2 ≤ N ^ 2 * (N ^ 2) ^ 2 :=
          mul_le_mul (pow_le_pow_left₀ hNd0 hNd 2) (pow_le_pow_left₀ hU0 hU 2) (by positivity) (by positivity)
      _ = N ^ 6 := by ring
  have h2 : 2 * C * e₁ * (Θ * (c₀ * Q + F₁)) + Θ * (c₀ * Q * e₂ + F₁) ≤ Θ * (K₃ * (Es + F₁)) := by
    have hcQ : c₀ * Q ≤ 2 * c₀ := by nlinarith
    have a1 : e₁ * (c₀ * Q + F₁) ≤ Es * (2 * c₀ + 1) := mul_le_mul he₁s (by linarith) (by positivity) hEs0
    have a2 : c₀ * Q * e₂ ≤ 2 * c₀ * Es := mul_le_mul hcQ he₂s he₂ (by positivity)
    have a3 : 2 * C * e₁ * (Θ * (c₀ * Q + F₁)) = Θ * (2 * C * (e₁ * (c₀ * Q + F₁))) := by ring
    rw [a3]
    have a4 : Θ * (2 * C * (e₁ * (c₀ * Q + F₁))) ≤ Θ * (2 * C * (Es * (2 * c₀ + 1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left a1 (by positivity)) hΘ
    have a5 : Θ * (c₀ * Q * e₂ + F₁) ≤ Θ * (2 * c₀ * Es + F₁) :=
      mul_le_mul_of_nonneg_left (by linarith) hΘ
    have a6 : 2 * C * (Es * (2 * c₀ + 1)) + (2 * c₀ * Es + F₁) ≤ K₃ * (Es + F₁) := by
      have e : (2 * C * (2 * c₀ + 1) + 2 * c₀ + 2) * (Es + F₁) - (2 * C * (Es * (2 * c₀ + 1)) + (2 * c₀ * Es + F₁)) =
          2 * Es + (2 * C * (2 * c₀ + 1) + 2 * c₀ + 1) * F₁ := by ring
      have h0 : 0 ≤ 2 * Es + (2 * C * (2 * c₀ + 1) + 2 * c₀ + 1) * F₁ := by
        have : 0 ≤ 2 * C * (2 * c₀ + 1) + 2 * c₀ + 1 := by nlinarith
        positivity
      have := mul_le_mul_of_nonneg_right hK (add_nonneg hEs0 hF)
      linarith
    nlinarith [mul_le_mul_of_nonneg_left a6 hΘ]
  calc Nd ^ 2 * U ^ 2 * (2 * C * e₁ * (Θ * (c₀ * Q + F₁)) + Θ * (c₀ * Q * e₂ + F₁))
      ≤ N ^ 6 * (Θ * (K₃ * (Es + F₁))) := mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = _ := by ring

end RL







/-! ### 21. Eventual facts in `n` -/

section Ev

variable {d : ℕ} (sz : Sizes d)

theorem iniTermI_W_tendsto {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hSz : sz.SizeTendsto) (hBw : sz.Bandwidth 𝔠) :
    Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop :=
  tendsto_atTop_mono' atTop (hBw.mono fun _ hn => hn) ((tendsto_rpow_atTop h𝔠).comp hSz)

theorem iniTermI_W_le_N (hd : 1 ≤ d) (n : ℕ) : ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  have hL : 1 ≤ sz.L n := by have := sz.three_le_L n; omega
  have h1 : sz.W n ≤ (sz.W n * sz.L n) ^ d :=
    (Nat.le_mul_of_pos_right _ hL).trans (Nat.le_self_pow (by omega) _)
  unfold Sizes.size; exact_mod_cast h1

theorem iniTermI_N_le_W (n : ℕ) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hB : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ)) :
    ((sz.size n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) := by
  have hN : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  calc ((sz.size n : ℕ) : ℝ) = (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (1 / 𝔠) := by
        rw [← Real.rpow_mul hN, mul_one_div_cancel h𝔠.ne', Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hN _) hB (by positivity)

/-- **The floor** `Θ N⁶ K₃ (E_* + W^{-D₁}) ≤ W^{-D}` eventually, `Θ = N^{τ/4}`, `D₁ = D + (7+τ)/𝔠 + 1`
(`N ≤ W^{1/𝔠}`, `e^{-c₂ x^{5/4}}` beats `e^{B x}`, `x = log W`). -/
theorem iniTermI_ev_floor (_hd : 1 ≤ d) {𝔠 τ D c₂ K₃ : ℝ} (h𝔠 : 0 < 𝔠) (hτ : 0 < τ) (hc₂ : 0 < c₂) (hK₃ : 0 < K₃)
    (hSz : sz.SizeTendsto) (hBw : sz.Bandwidth 𝔠) :
    ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (τ / 4) * ((sz.size n : ℕ) : ℝ) ^ 6 * K₃ *
      (Real.exp (-(c₂ * Real.log ((sz.W n : ℕ) : ℝ) ^ (5 / 4 : ℝ))) +
        ((sz.W n : ℕ) : ℝ) ^ (-(D + (7 + τ) / 𝔠 + 1))) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := by
  have hWt := iniTermI_W_tendsto sz h𝔠 hSz hBw
  have hlog : Tendsto (fun n => Real.log ((sz.W n : ℕ) : ℝ)) atTop atTop := Real.tendsto_log_atTop.comp hWt
  set B : ℝ := (7 + τ) / 𝔠 with hB
  have hB0 : 0 ≤ B := by positivity
  filter_upwards [hBw, hlog.eventually (iniTermI_asy2 B D c₂ (2 * K₃) hc₂),
    hlog.eventually (eventually_ge_atTop (Real.log (2 * K₃))), hlog.eventually (eventually_ge_atTop (0 : ℝ)),
    hWt.eventually (eventually_ge_atTop (1 : ℝ))] with n hBwn h2 h3 h4 hW1
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hW
  set x : ℝ := Real.log W with hx
  have hW0 : 0 < W := by linarith
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  have hNW : N ≤ W ^ (1 / 𝔠) := iniTermI_N_le_W sz n h𝔠 hBwn
  have hΘN : N ^ (τ / 4) * N ^ 6 ≤ Real.exp (B * x) := by
    have e1 : N ^ (τ / 4) * N ^ 6 = N ^ (τ / 4 + 6) := by
      rw [show N ^ 6 = N ^ ((6 : ℕ) : ℝ) from (Real.rpow_natCast N 6).symm, ← Real.rpow_add hN0]; norm_num
    rw [e1]
    have hc : (1 / 𝔠) * (τ / 4 + 6) ≤ B := by
      rw [hB, one_div, ← div_eq_inv_mul]; exact div_le_div_of_nonneg_right (by linarith) h𝔠.le
    calc N ^ (τ / 4 + 6) ≤ (W ^ (1 / 𝔠)) ^ (τ / 4 + 6) := Real.rpow_le_rpow hN0.le hNW (by positivity)
      _ = Real.exp (x * ((1 / 𝔠) * (τ / 4 + 6))) := by rw [← Real.rpow_mul hW0.le, Real.rpow_def_of_pos hW0]
      _ ≤ Real.exp (B * x) := Real.exp_le_exp.2 (by nlinarith)
  have hWD : W ^ (-D) = Real.exp (-(D * x)) := by rw [Real.rpow_def_of_pos hW0]; congr 1; ring
  have hWD1 : W ^ (-(D + B + 1)) = Real.exp (-(D * x) - x - B * x) := by
    rw [Real.rpow_def_of_pos hW0]; congr 1; ring
  rw [hWD]
  have hE1 : K₃ * Real.exp (B * x) * Real.exp (-(c₂ * x ^ (5 / 4 : ℝ))) ≤ 1 / 2 * Real.exp (-(D * x)) := by
    have h2' : (2 * K₃) * Real.exp (B * x - c₂ * x ^ (5 / 4 : ℝ)) ≤ Real.exp (-(D * x)) := h2
    rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg] at h2'
    linarith
  have hE2 : K₃ * Real.exp (B * x) * W ^ (-(D + B + 1)) ≤ 1 / 2 * Real.exp (-(D * x)) := by
    rw [hWD1]
    have : K₃ * Real.exp (-x) ≤ 1 / 2 := by
      have h5 : 2 * K₃ ≤ Real.exp x := by
        calc 2 * K₃ = Real.exp (Real.log (2 * K₃)) := (Real.exp_log (by positivity)).symm
          _ ≤ Real.exp x := Real.exp_le_exp.2 h3
      rw [Real.exp_neg]
      have hx0 : 0 < Real.exp x := Real.exp_pos _
      rw [mul_inv_le_iff₀ hx0]; linarith
    have e : Real.exp (B * x) * Real.exp (-(D * x) - x - B * x) = Real.exp (-x) * Real.exp (-(D * x)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc K₃ * Real.exp (B * x) * Real.exp (-(D * x) - x - B * x)
        = K₃ * (Real.exp (B * x) * Real.exp (-(D * x) - x - B * x)) := by ring
      _ = (K₃ * Real.exp (-x)) * Real.exp (-(D * x)) := by rw [e]; ring
      _ ≤ 1 / 2 * Real.exp (-(D * x)) := mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  have hD1 : W ^ (-(D + (7 + τ) / 𝔠 + 1)) = W ^ (-(D + B + 1)) := by rw [hB]
  rw [hD1]
  calc N ^ (τ / 4) * N ^ 6 * K₃ * (Real.exp (-(c₂ * x ^ (5 / 4 : ℝ))) + W ^ (-(D + B + 1)))
      ≤ K₃ * Real.exp (B * x) * (Real.exp (-(c₂ * x ^ (5 / 4 : ℝ))) + W ^ (-(D + B + 1))) := by
        have : N ^ (τ / 4) * N ^ 6 * K₃ ≤ K₃ * Real.exp (B * x) := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left hΘN hK₃.le
        exact mul_le_mul_of_nonneg_right this (by positivity)
    _ = K₃ * Real.exp (B * x) * Real.exp (-(c₂ * x ^ (5 / 4 : ℝ))) + K₃ * Real.exp (B * x) * W ^ (-(D + B + 1)) := by ring
    _ ≤ _ := by linarith

/-- `K (log W)^{14} e^{(log W)^{3/4}} ≤ Θ³` and `log W ≥ 2` eventually, `Θ = N^{τ/4}`. -/
theorem iniTermI_ev_K (hd : 1 ≤ d) {𝔠 τ : ℝ} (h𝔠 : 0 < 𝔠) (hτ : 0 < τ) (K : ℝ)
    (hSz : sz.SizeTendsto) (hBw : sz.Bandwidth 𝔠) :
    ∀ᶠ n in atTop, K * (Real.log ((sz.W n : ℕ) : ℝ) ^ 14 * Real.exp (Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 4 : ℝ))) ≤
        (((sz.size n : ℕ) : ℝ) ^ (τ / 4)) ^ 3 ∧ 2 ≤ Real.log ((sz.W n : ℕ) : ℝ) := by
  have hWt := iniTermI_W_tendsto sz h𝔠 hSz hBw
  have hlog : Tendsto (fun n => Real.log ((sz.W n : ℕ) : ℝ)) atTop atTop := Real.tendsto_log_atTop.comp hWt
  filter_upwards [hlog.eventually (iniTermI_asy1 K (τ / 2) (half_pos hτ)), hlog.eventually (eventually_ge_atTop (2 : ℝ)),
    hWt.eventually (eventually_ge_atTop (1 : ℝ))] with n h1 h2 hW1
  refine ⟨?_, h2⟩
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hW
  have hW0 : 0 < W := by linarith
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  have hWN : W ≤ N := iniTermI_W_le_N sz hd n
  have e1 : Real.exp (τ / 2 * Real.log W) = W ^ (τ / 2) := by
    rw [Real.rpow_def_of_pos hW0]; congr 1; ring
  have e2 : (N ^ (τ / 4)) ^ 3 = N ^ (3 * (τ / 4)) := by
    rw [show (N ^ (τ / 4)) ^ 3 = (N ^ (τ / 4)) ^ ((3 : ℕ) : ℝ) from (Real.rpow_natCast _ 3).symm, ← Real.rpow_mul (by linarith)]
    norm_num; ring_nf
  calc _ ≤ Real.exp (τ / 2 * Real.log W) := by linarith [h1]
    _ = W ^ (τ / 2) := e1
    _ ≤ N ^ (τ / 2) := Real.rpow_le_rpow hW0.le hWN (by positivity)
    _ ≤ N ^ (3 * (τ / 4)) := Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith)
    _ = _ := e2.symm

theorem iniTermI_L2_le_N (hd : 2 ≤ d) (n : ℕ) : ((sz.L n : ℕ) : ℝ) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) := by
  have : (sz.L n) ^ 2 ≤ (sz.W n * sz.L n) ^ d :=
    (Nat.pow_le_pow_right (by have := sz.three_le_L n; omega) hd).trans
      (Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d)
  unfold Sizes.size; exact_mod_cast this

theorem iniTermI_pow_floor {N W β D D₁ : ℝ} (hW : 1 ≤ W) (hN0 : 0 ≤ N) (hN : N ≤ W ^ β) (j : ℕ)
    (_hβ : 0 ≤ β) (hexp : j * β + D ≤ D₁) : N ^ j * W ^ (-D₁) ≤ W ^ (-D) := by
  have hW0 : 0 < W := by linarith
  calc N ^ j * W ^ (-D₁) ≤ (W ^ β) ^ j * W ^ (-D₁) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hN0 hN j) (Real.rpow_nonneg hW0.le _)
    _ = W ^ (j * β - D₁) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le, ← Real.rpow_add hW0]; congr 1; ring
    _ ≤ W ^ (-D) := Real.rpow_le_rpow_of_exponent_le hW (by linarith)

/-- `ρ_u Bctl(s) ≤ 4 A^{-1/5}` from `(con_st_ind)`: `ρ_u ≤ ρ_t ≤ Bctl(t)^{-𝔠_d} ≤ (2A)^{𝔠_d}`, `Bctl(s) ≤ 2 A⁻¹`, `𝔠_d ≤ 1/100`. -/
theorem iniTermI_rho_B (n : ℕ) {s t u 𝔠d : ℝ} (hg : 0 < sz.lam n) (hA1 : 1 ≤ STAI sz n) (hsu : s ≤ u) (hut : u ≤ t)
    (ht1 : t < 1) (hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t) (hregs : 1 - s ≤ sz.lam n ^ 2) (hd : 2 ≤ d)
    (h𝔠d : 0 < 𝔠d) (h𝔠d' : 𝔠d ≤ 1 / 100) (hCon : (sz.Bctl n t) ^ 𝔠d ≤ (1 - t) / (1 - s)) :
    (1 - s) / (1 - u) * sz.Bctl n s ≤ 4 * (STAI sz n) ^ (-(1 / 5 : ℝ)) := by
  have hu1 : 0 < 1 - u := by linarith
  have ht0 : 0 < 1 - t := by linarith
  have hs1 : 0 < 1 - s := by linarith
  have hA0 : 0 < STAI sz n := lt_of_lt_of_le one_pos hA1
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hlow : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - s :=
    (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (pow_le_pow_right₀ hL1 hd)).trans
      (hreg.trans (by linarith))
  have hBs := iniTermI_Bctl_le sz n hg (by linarith) hlow
  have hBt : (2 * STAI sz n)⁻¹ ≤ sz.Bctl n t := st5_Bctl_ge sz n hg ht1 (by linarith)
  have hBt0 : 0 < sz.Bctl n t := lt_of_lt_of_le (by positivity) hBt
  -- `ρ_u ≤ (Bctl t)^{-𝔠d} ≤ (2A)^{𝔠d}`
  have hρt : (1 - s) / (1 - u) ≤ ((sz.Bctl n t) ^ 𝔠d)⁻¹ := by
    have h1 : (1 - s) / (1 - u) ≤ (1 - s) / (1 - t) := div_le_div_of_nonneg_left hs1.le ht0 (by linarith)
    refine h1.trans ?_
    have hp : 0 < (sz.Bctl n t) ^ 𝔠d := Real.rpow_pos_of_pos hBt0 _
    have := inv_anti₀ hp hCon
    rwa [inv_div] at this
  have hρA : ((sz.Bctl n t) ^ 𝔠d)⁻¹ ≤ 2 * (STAI sz n) ^ 𝔠d := by
    rw [← Real.inv_rpow hBt0.le]
    calc (sz.Bctl n t)⁻¹ ^ 𝔠d ≤ (2 * STAI sz n) ^ 𝔠d := Real.rpow_le_rpow (by positivity)
          (by rw [inv_le_comm₀ hBt0 (by positivity)]; exact hBt) h𝔠d.le
      _ = 2 ^ 𝔠d * (STAI sz n) ^ 𝔠d := Real.mul_rpow (by norm_num) hA0.le
      _ ≤ 2 * (STAI sz n) ^ 𝔠d := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hA0.le _)
          calc (2 : ℝ) ^ 𝔠d ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 2 := Real.rpow_one 2
  have hB0 : 0 ≤ sz.Bctl n s := (st_Bctl_pos sz (by linarith)).le
  have hρ0 : 0 ≤ (1 - s) / (1 - u) := div_nonneg hs1.le hu1.le
  calc (1 - s) / (1 - u) * sz.Bctl n s ≤ (2 * (STAI sz n) ^ 𝔠d) * (2 * (STAI sz n)⁻¹) :=
        mul_le_mul (hρt.trans hρA) hBs hB0 (by positivity)
    _ = 4 * ((STAI sz n) ^ 𝔠d * (STAI sz n)⁻¹) := by ring
    _ ≤ 4 * (STAI sz n) ^ (-(1 / 5 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        have e : (STAI sz n) ^ 𝔠d * (STAI sz n)⁻¹ = (STAI sz n) ^ (𝔠d - 1) := by
          rw [Real.rpow_sub hA0, Real.rpow_one, div_eq_mul_inv]
        rw [e]
        exact Real.rpow_le_rpow_of_exponent_le hA1 (by linarith)

/-- **Ward + `(Gt_avgbound_flow)`** (`(eq:PcalBterm)`, `3_5:2141`): `|Σ_{b₂} 𝓑_{b₁b₂}| ≤ Θ (Bs W^{-d}/κ_m)/(1-s)` from
`|(𝓛-𝒦)^{(1)}_{s,±,b₁}| ≤ Θ Bs` and `η_s ≥ (1-s) κ_m`. -/
theorem iniTermI_ward_bound (n : ℕ) {E s Θ κm : ℝ} (hE : |E| < 2) (hs0 : 0 ≤ s) (hs1 : s < 1) (hκm : 0 < κm)
    (hκ : κm ≤ (mE E).im) {σ : Fin 2 → Bool} (hσ : σ 0 ≠ σ 1) (ω : sz.SeqΩ) (_hΘ : 0 ≤ Θ)
    (h1 : ∀ p : (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n)),
      ‖Lloop sz n E s p.1 p.2 ω - STKloop sz n E s p.1 p.2‖ ≤ Θ * (sz.Bctl n s) ^ 1) (b₁ : Zd d (sz.L n)) :
    ‖∑ b₂ : Zd d (sz.L n), STLKM sz n E s (sz.seqHflow n s ω) σ ![b₁, b₂]‖ ≤
      Θ * (sz.Bctl n s * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ / κm) / (1 - s) := by
  have hw := iniTermI_ward sz n hE hs0 hs1 hσ b₁ ω
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hs1' : 0 < 1 - s := by linarith
  have hη : (1 - s) * κm ≤ etaT E s := by
    unfold etaT; exact mul_le_mul_of_nonneg_left hκ hs1'.le
  have hη0 : 0 < (1 - s) * κm := by positivity
  have hB0 : 0 ≤ sz.Bctl n s := (st_Bctl_pos sz hs1).le
  have e1 := h1 (fun _ => true, fun _ => b₁)
  have e2 := h1 (fun _ => false, fun _ => b₁)
  refine hw.trans ?_
  have hsum : ‖Lloop sz n E s (fun _ : Fin 1 => true) (fun _ => b₁) ω - STKloop sz n E s (fun _ : Fin 1 => true) (fun _ => b₁)‖ +
      ‖Lloop sz n E s (fun _ : Fin 1 => false) (fun _ => b₁) ω - STKloop sz n E s (fun _ : Fin 1 => false) (fun _ => b₁)‖ ≤
      2 * (Θ * sz.Bctl n s) := by
    rw [pow_one] at e1 e2; linarith
  have hinv : (2 * (((sz.W n : ℕ) : ℝ) ^ d * etaT E s))⁻¹ ≤ (2 * (((sz.W n : ℕ) : ℝ) ^ d * ((1 - s) * κm)))⁻¹ :=
    inv_anti₀ (by positivity) (by nlinarith)
  calc (2 * (((sz.W n : ℕ) : ℝ) ^ d * etaT E s))⁻¹ * (_ + _) ≤
        (2 * (((sz.W n : ℕ) : ℝ) ^ d * ((1 - s) * κm)))⁻¹ * (2 * (Θ * sz.Bctl n s)) :=
        mul_le_mul hinv hsum (by positivity) (by positivity)
    _ = _ := by field_simp

theorem iniTermI_prec_of_whp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U : ℕ → Type*}
    {ξ ζ : ∀ n, U n → Ω → ℝ}
    (h : ∀ τ > (0 : ℝ), ∃ Ξ : ℕ → Set Ω, Gauss.HighProbAt P size Ξ ∧
      ∀ᶠ n in atTop, ∀ ω ∈ Ξ n, ∀ q, ξ n q ω ≤ (size n : ℝ) ^ τ * ζ n q ω) : StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  obtain ⟨Ξ, hΞ, hev⟩ := h τ hτ
  filter_upwards [hΞ D hD, hev] with n h1 h2
  refine le_trans (measure_mono ?_) h1
  intro ω hω
  obtain ⟨q, hq⟩ := hω
  intro hmem
  exact absurd (h2 ω hmem q) (not_le.2 hq)

end Ev

/-! ### 22. The `Prec` lift: `stIniTermI_holds` -/

section Concl

variable {d : ℕ}

set_option maxHeartbeats 4000000 in
-- long calc chains with many `positivity`/`gcongr` side goals
/-- **The initial term of Step 5, case (i)** (`(iksjuwjx0)`, `3_5:2072-2172`) from the hypotheses of `STIngR5` that it uses:
`STDecay` at `s` (the profile of `𝓑`), `STAvgU` (the Ward term), `STCltFarUConcl` (`lem;CLT`, uniformly in `u`), `(con_st_ind)` and the regime. -/
theorem iniTermI_concl (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 𝔠d Cd : ℝ} (hκ : 0 < κ) (h𝔠d : 0 < 𝔠d)
    (h𝔠d' : 𝔠d ≤ 1 / 100) {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n < t n) (ht : ∀ n, t n ≤ lemT (z n)) (hR : STReg5I sz s t) (hDec : STDecay sz (STflowE z) s)
    (hCon : STConStInd sz 𝔠d s t) (hS2 : STStep2Concl sz (STflowE z) s t Cd)
    (hCLT : sz.Prec (U := fun n => Σ u : TimeIcc s t n, STCltFarIdx sz s n (u : ℝ))
      (fun n q ω => ‖STfFar sz n (STflowE z n) (s n) (q.1 : ℝ) q.2.1.1.1 q.2.1.2 ω‖)
      (fun n q _ => STCltFarZeta sz n q.2.1.2)) : STIniTermConcl sz ∅ STSigAll (STflowE z) s t := by
  classical
  have hflow' := hflow
  obtain ⟨⟨h𝔠, h𝔡, hSz, hBw, hWO⟩, hloc⟩ := hflow
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hflow' ht
  have him : ∀ n, 0 < (z n).im := fun n =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _) (hloc n).2.1
  have hE : ∀ n, |STflowE z n| ≤ 2 - κ := fun n => (abs_lemE_le (him n)).trans (hloc n).1
  have hκ2 : κ ≤ 2 := by have := (abs_nonneg _).trans (hE 0); linarith
  have hE2 : ∀ n, |STflowE z n| ≤ 2 := fun n => (hE n).trans (by linarith)
  have hEl : ∀ n, |STflowE z n| < 2 := fun n => (hE n).trans_lt (by linarith)
  set κm : ℝ := Real.sqrt (κ * (4 - κ)) / 2 with hκm
  have hκm0 : 0 < κm := by
    have : 0 < κ * (4 - κ) := mul_pos hκ (by linarith)
    rw [hκm]; positivity
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  obtain ⟨K₀, C, c, hK₀, hC, hc, Hall⟩ := iniTermI_rl_all d 𝔡⁻¹ κm hd hΛ hκm0
  set c₀ : ℝ := 1 + 2 ^ (d - 1) with hc₀
  have hc₀1 : 1 ≤ c₀ := by have : (0 : ℝ) ≤ 2 ^ (d - 1) := by positivity
                           linarith
  set K₃ : ℝ := 2 * C * (2 * c₀ + 1) + 2 * c₀ + 2 with hK₃
  have hK₃2 : 2 ≤ K₃ := by have := mul_pos hC (by linarith : (0 : ℝ) < 2 * c₀ + 1); rw [hK₃]; linarith
  set c₂ : ℝ := min 1 (c / 4) with hc₂
  have hc₂0 : 0 < c₂ := lt_min one_pos (by positivity)
  intro D hD
  apply iniTermI_prec_of_whp
  intro τ hτ
  set D₁ : ℝ := D + (7 + τ) / 𝔠 + 1 with hD₁
  have hD₁0 : 0 < D₁ := by positivity
  have hE1 := StochDomAt.highProb (hDec D₁ hD₁0) (τ := τ / 4) (by positivity)
  have hAvg : sz.Prec (U := fun n => (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (STflowE z n) (s n) p.1 p.2 ω - STKloop sz n (STflowE z n) (s n) p.1 p.2‖)
      (fun n _ _ => (sz.Bctl n (s n)) ^ 1) :=
    iniTermI_prec_restrict sz hS2.2.1 (fun n p => ((⟨s n, le_rfl, (hst n).le⟩ : TimeIcc s t n), p))
      (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  have hE2' := StochDomAt.highProb hAvg (τ := τ / 4) (by positivity)
  have hE3 := StochDomAt.highProb hCLT (τ := τ / 4) (by positivity)
  have hΞ := Gauss.HighProbAt.inter (tendsto_size sz hSz) (Gauss.HighProbAt.inter (tendsto_size sz hSz) hE1 hE2') hE3
  refine ⟨_, hΞ, ?_⟩
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ ∧ 1 ≤ STAI sz n := by
    filter_upwards [hWO, st5_eventually_A_ge_one sz h𝔡 hWO] with n h1 h2
    exact ⟨h2.1, h1.2, h2.2⟩
  have hfl := iniTermI_ev_floor sz (by omega : 1 ≤ d) (D := D) (c₂ := c₂) (K₃ := K₃) h𝔠 hτ hc₂0 (by linarith) hSz hBw
  have hKK := iniTermI_ev_K sz (by omega : 1 ≤ d) h𝔠 hτ K₀ hSz hBw
  filter_upwards [hlam, hBw, hCon, hfl, hKK] with n hl hBwn hCn hfln hKKn
  intro ω hω q
  obtain ⟨⟨h1, h2⟩, h3⟩ := hω
  obtain ⟨⟨u, hu⟩, ⟨σ, -⟩, x⟩ := q
  obtain ⟨hg, hgΛ, hA1⟩ := hl
  obtain ⟨hK, hlW2⟩ := hKKn
  change ‖zeroModeSet d (sz.L n) ∅ (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ (s n) u
      (fun b => STLKM sz n (STflowE z n) (s n) (sz.seqHflow n (s n) ω) σ b)) x‖ ≤
    ((sz.size n : ℕ) : ℝ) ^ τ * ((STAI sz n) ^ (-(1 / 5) : ℝ) *
      STprof sz n u D ((sz.L n : ℕ) : ℝ) (x 0) (x 1) + ((sz.W n : ℕ) : ℝ) ^ (-D))
  rw [st5_zeroModeSet_empty]
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  have hW1 : (1 : ℝ) ≤ W := by rw [hWdef]; exact_mod_cast sz.W_pos n
  have hN1 : (1 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast sz.one_le_size n
  have hs1 : s n < 1 := (hst n).trans (ht1 n)
  have hs1' : 0 < 1 - s n := by linarith
  have hu1 : 0 < 1 - u := by linarith [hu.2, ht1 n]
  have hregt := (hR n).1
  have hregs1 := (hR n).2
  have hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - u := hregt.trans (by linarith [hu.2])
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hlow : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - s n :=
    (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (pow_le_pow_right₀ hL1 (by omega : 2 ≤ d))).trans
      (hregt.trans (by linarith [hst n, ht1 n]))
  set Θ : ℝ := N ^ (τ / 4) with hΘ
  have hΘ1 : 1 ≤ Θ := Real.one_le_rpow hN1 (by positivity)
  have hΘ4 : Θ ^ 4 = N ^ τ := by
    rw [hΘ, show (N ^ (τ / 4)) ^ 4 = (N ^ (τ / 4)) ^ ((4 : ℕ) : ℝ) from (Real.rpow_natCast _ 4).symm,
      ← Real.rpow_mul (by linarith)]
    norm_num
  have hA0 : 0 < STAI sz n := lt_of_lt_of_le one_pos hA1
  set a : ℝ := (STAI sz n) ^ (-(1 / 5 : ℝ)) with ha
  have ha0 : 0 ≤ a := Real.rpow_nonneg hA0.le _
  have hlam2 := iniTermI_lam_le sz n hg hs1 hlow
  have hBs0 : 0 ≤ sz.Bctl n (s n) := (st_Bctl_pos sz hs1).le
  have hNW : N ≤ W ^ (1 / 𝔠) := iniTermI_N_le_W sz n h𝔠 hBwn
  have hβ : 0 ≤ 1 / 𝔠 := by positivity
  have hD1D : D ≤ D₁ := by
    have : 0 ≤ (7 + τ) / 𝔠 := by positivity
    rw [hD₁]; linarith
  have hF : W ^ (-D₁) ≤ W ^ (-D) := Real.rpow_le_rpow_of_exponent_le hW1 (neg_le_neg hD1D)
  set ρ : ℝ := (1 - s n) / (1 - u) with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg hs1'.le hu1.le
  have hρL : ρ ≤ ((sz.L n : ℕ) : ℝ) ^ 2 := by
    rw [hρ, div_le_iff₀ hu1]
    have : sz.lam n ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ 2 * (1 - u) := by
      rw [div_le_iff₀ (by positivity)] at hreg; linarith
    linarith
  have hρN : ρ ≤ N := hρL.trans (iniTermI_L2_le_N sz (by omega) n)
  have hexp1 : ((1 : ℕ) : ℝ) * (1 / 𝔠) + D ≤ D₁ := by
    have : 1 / 𝔠 ≤ (7 + τ) / 𝔠 := div_le_div_of_nonneg_right (by linarith) h𝔠.le
    rw [hD₁]; push_cast; linarith
  have hexp2 : ((2 : ℕ) : ℝ) * (1 / 𝔠) + D ≤ D₁ := by
    have : 2 * (1 / 𝔠) ≤ (7 + τ) / 𝔠 := by
      rw [← mul_div_assoc, mul_one]; exact div_le_div_of_nonneg_right (by linarith) h𝔠.le
    rw [hD₁]; push_cast; linarith
  have hρF1 : ρ * W ^ (-D₁) ≤ W ^ (-D) := by
    have := iniTermI_pow_floor hW1 (by linarith) hNW 1 hβ hexp1
    calc ρ * W ^ (-D₁) ≤ N * W ^ (-D₁) := mul_le_mul_of_nonneg_right hρN (Real.rpow_nonneg (by linarith) _)
      _ = N ^ 1 * W ^ (-D₁) := by rw [pow_one]
      _ ≤ _ := this
  have hρF2 : ρ * ρ * W ^ (-D₁) ≤ W ^ (-D) := by
    have := iniTermI_pow_floor hW1 (by linarith) hNW 2 hβ hexp2
    calc ρ * ρ * W ^ (-D₁) ≤ N ^ 2 * W ^ (-D₁) :=
          mul_le_mul_of_nonneg_right (by nlinarith) (Real.rpow_nonneg (by linarith) _)
      _ ≤ _ := this
  have hρB := iniTermI_rho_B sz n hg hA1 hu.1 hu.2 (ht1 n) hregt hregs1 (by omega) h𝔠d h𝔠d' hCn.1
  have hX : ∀ b : Fin 2 → Zd d (sz.L n), ‖STLKM sz n (STflowE z n) (s n) (sz.seqHflow n (s n) ω) σ b‖ ≤
      Θ * (sz.Bctl n (s n) ^ (1 / 5 : ℝ) * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) (s n) (zdistInf d (sz.L n) (b 0 - b 1) : ℕ) +
        W ^ (-D₁)) := by
    intro b
    have := h1 (σ, b)
    dsimp only at this
    rw [iniTermI_prem_eq] at this
    exact this
  have hP₀ := iniTermI_prof_ge sz n u D x
  refine le_of_le_of_eq (@Hall (sz.L n) _ (sz.three_le_L n) (sz.lam n) W D D₁ (STflowE z n) (s n) u Θ a
    (STprof sz n u D ((sz.L n : ℕ) : ℝ) (x 0) (x 1)) ((sz.Bctl n (s n)) ^ (1 / 5 : ℝ)) (Real.log W) (sz.Bctl n (s n))
    hg hgΛ (by linarith) (hE2 n) (iniTermI_im_ge (hE n)) (hs0 n) hu.1 (hu.2.trans_lt (ht1 n)) hreg hregs1 hlW2 hΘ1
    (Real.rpow_nonneg hBs0 _) hlam2 ha0 hBs0 hF hρF1 hρF2 hρB hK σ
    (fun b => STLKM sz n (STflowE z n) (s n) (sz.seqHflow n (s n) ω) σ b) hX x hP₀
    (fun b₁ => Real.log W ^ 4 * ellT (sz.L n) (sz.lam n) (s n) < ((zdistInf d (sz.L n) (b₁ - x 0) : ℕ) : ℝ) ∧
      Real.log W ^ 4 * ellT (sz.L n) (sz.lam n) (s n) < ((zdistInf d (sz.L n) (b₁ - x 1) : ℕ) : ℝ))
    (Classical.decPred _) (fun b₁ => Iff.rfl) ?_) (by rw [hΘ4])
  intro hσ' hρbig
  have hlW0 : 0 ≤ Real.log W := by linarith
  have hℓ5 := iniTermI_ell5 (sz.three_le_L n) hg hu.1 (hu.2.trans_lt (ht1 n)) hreg hregs1 hlW0 hρbig
  have hℓs1 : 1 ≤ ellT (sz.L n) (sz.lam n) (s n) := one_le_ellT hL1
  have hℓu0 : 0 < ellT (sz.L n) (sz.lam n) u := lt_of_lt_of_le one_pos (hℓs1.trans (ellT_mono hg.le hu.1 (hu.2.trans_lt (ht1 n))))
  have hℓs0 : 0 < ellT (sz.L n) (sz.lam n) (s n) := lt_of_lt_of_le one_pos hℓs1
  obtain ⟨hE₃, he₁, he₂⟩ := iniTermI_Estar (lW := Real.log W) (c := c) (c₂ := c₂) (by linarith) hc₂0.le (min_le_left _ _)
    (min_le_right _ _) hℓu0 hℓs0
  -- common quantities
  have hWd0 : (0 : ℝ) < W ^ d := by positivity
  have hAeq : STAI sz n = sz.lam n ^ 2 * W ^ d := rfl
  have hGinv : (sz.lam n ^ 2)⁻¹ ≤ W ^ d := by
    have hg2 : 0 < sz.lam n ^ 2 := by positivity
    calc (sz.lam n ^ 2)⁻¹ = (sz.lam n ^ 2)⁻¹ * 1 := by rw [mul_one]
      _ ≤ (sz.lam n ^ 2)⁻¹ * (sz.lam n ^ 2 * W ^ d) := mul_le_mul_of_nonneg_left (hAeq ▸ hA1) (inv_nonneg.2 hg2.le)
      _ = _ := by field_simp
  have hWN : W ^ d ≤ N := by
    have : (sz.W n) ^ d ≤ (sz.W n * sz.L n) ^ d :=
      Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by have := sz.three_le_L n; omega)) d
    rw [hNdef, hWdef]; unfold Sizes.size; exact_mod_cast this
  have hG : (sz.lam n ^ 2)⁻¹ ≤ N := hGinv.trans hWN
  have hU : (1 - u)⁻¹ ≤ N ^ 2 := iniTermI_oneSub_inv_le sz (by omega) n hA1 hg hreg
  have ha1 : a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hA1 (by norm_num)
  have hQeq : sz.Bctl n (s n) ^ (1 / 5 : ℝ) * (W ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ = sz.Bctl n (s n) ^ (1 / 5 : ℝ) * (STAI sz n)⁻¹ := by
    rw [hAeq, mul_inv]; ring
  have hQ : sz.Bctl n (s n) ^ (1 / 5 : ℝ) * (W ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ ≤ 2 := by
    rw [hQeq]
    have : (STAI sz n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hA1
    calc _ ≤ (2 * a) * 1 := mul_le_mul hlam2 this (inv_nonneg.2 hA0.le) (by positivity)
      _ ≤ 2 := by linarith
  have hQ0 : 0 ≤ sz.Bctl n (s n) ^ (1 / 5 : ℝ) * (W ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ := by positivity
  have hcard : (Fintype.card (Zd d (sz.L n)) : ℝ) ≤ N := by
    rw [iniTermI_card_Zd]
    have : (sz.L n) ^ d ≤ (sz.W n * sz.L n) ^ d := Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
    rw [hNdef]; unfold Sizes.size; exact_mod_cast this
  have hF₁0 : 0 ≤ W ^ (-D₁) := Real.rpow_nonneg (by linarith) _
  have hΘ0 : 0 ≤ Θ := by linarith
  refine ⟨fun hwin => ⟨?_, ?_, ?_⟩, fun hout => ?_⟩
  · intro b₁
    exact iniTermI_ward_bound sz n (hEl n) (hs0 n) hs1 hκm0 (iniTermI_im_ge (hE n)) hσ' ω hΘ0 (fun p => h2 p) b₁
  · exact (iniTermI_floor_T3 (Nat.cast_nonneg _) hcard (by positivity) hG (inv_nonneg.2 hu1.le) hU hQ0 hQ hΘ0 hN1 hF₁0
      (Real.exp_pos _).le hE₃ hK₃2).trans hfln
  · have hcond : Real.log W ^ 5 * ellT (sz.L n) (sz.lam n) (s n) ≤ ellT (sz.L n) (sz.lam n) u ∧
        ((zdistInf d (sz.L n) (x 0 - x 1) : ℕ) : ℝ) ≤ (1 / 2 : ℝ) * Real.log W ^ (3 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) u +
          Real.log W ^ (5 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) (s n) := ⟨hℓ5, hwin⟩
    have hq : ‖STfFar sz n (STflowE z n) (s n) u σ x ω‖ ≤ Θ * STCltFarZeta sz n x :=
      h3 ⟨⟨u, hu⟩, ⟨(⟨σ, hσ'⟩, x), hcond⟩⟩
    rw [iniTermI_STfFar_eq sz n (hE2 n) hσ' x ω] at hq
    have hζ : STCltFarZeta sz n x = a * ((sz.lam n ^ 2 * W ^ d)⁻¹ * ((((zdistInf d (sz.L n) (x 0 - x 1) : ℕ) : ℝ) ^ (d - 2) + 1)⁻¹)) := by
      unfold STCltFarZeta
      have e : (STAI sz n) ^ (-(6 / 5) : ℝ) = a * (STAI sz n)⁻¹ := by
        rw [show (-(6 / 5) : ℝ) = -(1 / 5) + (-1) by norm_num, Real.rpow_add hA0, Real.rpow_neg_one]
      rw [e, hAeq, div_eq_mul_inv]; ring
    rw [hζ] at hq
    exact hq
  · have hℓ1' := ellT_pos (L := sz.L n) (g := sz.lam n) (t := u) hL1
    have hfin := iniTermI_floor_tail (Nd := (Fintype.card (Zd d (sz.L n)) : ℝ)) (N := N) (U := (1 - u)⁻¹)
      (Q := sz.Bctl n (s n) ^ (1 / 5 : ℝ) * (W ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹) (Θ := Θ) (F₁ := W ^ (-D₁))
      (e₁ := Real.exp (-(c * (1 / 4 * Real.log W ^ (3 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) u) / ellT (sz.L n) (sz.lam n) u)))
      (e₂ := Real.exp (-Real.sqrt (Real.log W ^ (5 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) (s n) / ellT (sz.L n) (sz.lam n) (s n))))
      (Es := Real.exp (-(c₂ * Real.log W ^ (5 / 4 : ℝ)))) (C := C) (c₀ := c₀) (K₃ := K₃)
      (Nat.cast_nonneg _) hcard (inv_nonneg.2 hu1.le) hU hQ0 hQ hΘ0 hN1 hF₁0
      (Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)) (Real.exp_pos _).le (Real.exp_pos _).le he₁ he₂ hC.le hc₀1 (le_of_eq hK₃.symm)
    refine le_trans (le_of_eq ?_) (hfin.trans hfln)
    ring


end Concl

/-- **The pin `STIniTermI`** (`(iksjuwjx0)`, `3_5:2072-2172`): the initial term of Step 5, case (i) `ilambda²/L² ≤ 1-t ≤ 1-s ≤ ilambda²`,
for all signs, exactly as merged (`Induction/Step5Pins.lean`).  `𝔠_d` is that of `stCltFar_uniform` (= `stCltFar_holds`). -/
theorem stIniTermI_holds (d : ℕ) : STIniTermI d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h𝔠d, h𝔠d', H⟩ := stCltFar_uniform d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨𝔠d, h𝔠d, h𝔠d', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS hCon hS1 hS2 hLmax hLKU
  have hCLT := H 𝔠 sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS hCon hS1 hS2 hLmax hLKU
  exact iniTermI_concl hd sz hκ h𝔠d h𝔠d' hflow hs0 hst ht hR hDec hCon hS2 hCLT

end RBM.Gauss.Sizes

/-! ## 23. Compiled nonempty instances (`d = 3`)

* `iniTermI_core_same_inst`, `iniTermI_core_mixed_inst`: the deterministic cores at `L = 8`, `g = 1/2` (`1 - s = 1/8 ≤ g² = 1/4`,
  `g²/L² = 1/256 ≤ 1 - u = 1/16`), `W = 2`, `D = 2`, `E = 1` (`Im m(E) = √3/2 ≥ κ_m = 1/2`), `s = 7/8`, `u = 15/16`, `Λ = 1`,
  `M = λ = 1`, and the nonzero tensor `X_b = W^{-d} 𝒯_s(|b₁-b₂|) + W^{-D}` (the `STDecay` profile at `s` attained), at every `a`;
* `iniTermI_restrict_inst`: `stIngR5_hyps_restrict` at `(szB, zB, 7/8, 15/16)`, `t' = 29/32`; the Prec premises of Steps 1-4 stay
  hypotheses (other gates' pins), the regime and `(con_st_ind)` are discharged;
* `inst_cltFarU_proved`, `inst_iniTermI_proved`: the pins `stCltFar_uniform` and `stIniTermI_holds` at `(szB, zB, 7/8, 15/16)`
  (`inst_iniTermI` of `Step5Pins.lean:617` with the pin proved). -/

namespace RBM.Gauss.Step5Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.Step34Inst Filter

private theorem iniTermI_inst_im : (1 / 2 : ℝ) ≤ (mE 1).im := by
  rw [mE_im]
  have h : (1 : ℝ) ≤ Real.sqrt 3 := Real.one_le_sqrt.mpr (by norm_num)
  have h3 : (4 : ℝ) - 1 ^ 2 = 3 := by norm_num
  rw [h3]
  linarith

private theorem iniTermI_inst_X (b : Fin 2 → Zd 3 8) :
    ‖(((1 : ℝ) * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 8 (1 / 2) (7 / 8) (zdistInf 3 8 (b 0 - b 1) : ℕ) + (2 : ℝ) ^ (-(2 : ℝ)) : ℝ) : ℂ)‖ ≤
      1 * (1 * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 8 (1 / 2) (7 / 8) (zdistInf 3 8 (b 0 - b 1) : ℕ) + (2 : ℝ) ^ (-(2 : ℝ))) := by
  have h0 : 0 ≤ (1 : ℝ) * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 8 (1 / 2) (7 / 8) (zdistInf 3 8 (b 0 - b 1) : ℕ) + (2 : ℝ) ^ (-(2 : ℝ)) := by
    have := tailT_nonneg (d := 3) (L := 8) (g := 1 / 2) (t := 7 / 8) (Nat.cast_nonneg (zdistInf 3 8 (b 0 - b 1)))
    positivity
  rw [Complex.norm_real, Real.norm_of_nonneg h0]
  exact le_of_eq (by ring)

/-- **Target (`σ₁ = σ₂`), instantiated**: `σ = (+,+)`. -/
theorem iniTermI_core_same_inst : ∃ C : ℝ, 0 < C ∧ ∀ a : Fin 2 → Zd 3 8,
    ‖RBM.Ind.Ugen 3 8 (1 / 2) 1 ![true, true] (7 / 8) (15 / 16)
      (fun b => (((1 : ℝ) * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 8 (1 / 2) (7 / 8) (zdistInf 3 8 (b 0 - b 1) : ℕ)
        + (2 : ℝ) ^ (-(2 : ℝ)) : ℝ) : ℂ)) a‖ ≤
      C * 1 * (1 * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 8 (1 / 2) (15 / 16) (zdistInf 3 8 (a 0 - a 1) : ℕ) +
        (2 : ℝ) ^ (-(2 : ℝ))) := by
  obtain ⟨C, hC, H⟩ := iniTermI_core_same 3 1 (1 / 2) (by norm_num) one_pos (by norm_num)
  refine ⟨C, hC, fun a => ?_⟩
  exact H 8 (by norm_num) (1 / 2) 2 2 1 (7 / 8) (15 / 16) 1 1 (by norm_num) (by norm_num) two_pos (by norm_num)
    iniTermI_inst_im (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ![true, true] (by simp) _ (fun b => iniTermI_inst_X b) a

/-- **Target (`σ₁ ≠ σ₂`), instantiated**: `σ = (+,-)`; `𝒰 X - c (1-s)² (Θ X Θ)` with the exact `c ∈ [0,1]`. -/
theorem iniTermI_core_mixed_inst : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ a : Fin 2 → Zd 3 8,
    ‖RBM.Ind.Ugen 3 8 (1 / 2) 1 ![true, false] (7 / 8) (15 / 16)
      (fun b => (((1 : ℝ) * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 8 (1 / 2) (7 / 8) (zdistInf 3 8 (b 0 - b 1) : ℕ)
        + (2 : ℝ) ^ (-(2 : ℝ)) : ℝ) : ℂ)) a -
      (c : ℂ) * iniTermI_Sfull 3 8 (1 / 2) (7 / 8) (15 / 16)
        (fun b => (((1 : ℝ) * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 8 (1 / 2) (7 / 8) (zdistInf 3 8 (b 0 - b 1) : ℕ)
          + (2 : ℝ) ^ (-(2 : ℝ)) : ℝ) : ℂ)) a‖ ≤
      C * 1 * (1 * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 8 (1 / 2) (15 / 16) (zdistInf 3 8 (a 0 - a 1) : ℕ) +
        (1 - 7 / 8) / (1 - 15 / 16) * (2 : ℝ) ^ (-(2 : ℝ))) := by
  obtain ⟨C, hC, H⟩ := iniTermI_core_mixed 3 1 (by norm_num) one_pos
  obtain ⟨c, hc0, hc1, hH⟩ := H 8 (by norm_num) (1 / 2) 2 2 1 (7 / 8) (15 / 16) 1 1 (by norm_num) (by norm_num) two_pos
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ![true, false] (by simp) _ (fun b => iniTermI_inst_X b)
  exact ⟨C, hC, c, hc0, hc1, hH⟩

/-- `stIngR5_hyps_restrict` at `(szB, zB, 7/8, 15/16)`, `t' = 29/32`: the regime and `(con_st_ind)` are discharged, the five
`Prec` of Steps 1-4 are the hypotheses. -/
theorem iniTermI_restrict_inst (Cd : ℝ)
    (hS1 : STStep1Loop szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hS2 : STStep2Concl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) Cd)
    (hLmax : STLmaxU szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hLKU : STLKU szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
    STReg5I szB (fun _ => 7 / 8) (fun _ => 29 / 32) ∧ STConStInd szB (1 / 100) (fun _ => 7 / 8) (fun _ => 29 / 32) ∧
      STStep1Loop szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 29 / 32) ∧
      STStep2Concl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 29 / 32) Cd ∧
      STLmaxU szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 29 / 32) ∧ STLKU szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 29 / 32) :=
  stIngR5_hyps_restrict szB (t := fun _ => 15 / 16) (t' := fun _ => 29 / 32) (by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num) szB_reg5I
    (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num)) hS1 hS2 hLmax hLKU

/-- `stCltFar_uniform` at `(szB, zB, 7/8, 15/16)`. -/
theorem inst_cltFarU_proved (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STCltFarUConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
  inst_ing5_I STReg5I _ (stCltFar_uniform 3) szB_reg5I Cd hCd

/-- `stCltFar_uniform` at `(szCL, zCL, 0, 1 - L_n^{-2})` (`L_n → ∞`, the data of `inst_cltFar`), where the index set is nonempty
(`iniTermI_cltFarU_index_nonempty`). -/
theorem inst_cltFarU_CL (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STCltFarUConcl sz E s t) szCL zCL sCL tCL Cd :=
  inst_ing5 STReg5I _ (stCltFar_uniform 3) szCL zCL flow_zCL sCL tCL (fun _ => le_rfl) szCL_hst lemT_zCL szCL_reg5I
    (fun _ h𝔠 => szCL_con h𝔠) Cd hCd

/-- The index set `Σ u ∈ [s,t], STCltFarIdx` of `STCltFarUConcl` at `(szCL, sCL, tCL)` is nonempty at every `n`: the endpoint
`u = t_n` carries the element of `szCL_cltFar_index_nonempty` (`σ = (+,-)`, `|a₁-a₂| = L_n/2`). -/
theorem iniTermI_cltFarU_index_nonempty (n : ℕ) :
    Nonempty (Σ u : RBM.Path.TimeIcc sCL tCL n, STCltFarIdx szCL sCL n (u : ℝ)) := by
  obtain ⟨p⟩ := szCL_cltFar_index_nonempty n
  exact ⟨⟨⟨tCL n, (szCL_hst n).le, le_rfl⟩, p⟩⟩

/-- **`stIniTermI_holds`, instantiated**: `inst_iniTermI` of `Step5Pins.lean:617` with the pin proved. -/
theorem inst_iniTermI_proved (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STIniTermConcl sz ∅ STSigAll E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
  inst_iniTermI (stIniTermI_holds 3) Cd hCd

end RBM.Gauss.Step5Inst
