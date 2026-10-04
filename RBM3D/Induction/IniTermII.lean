/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step5Pins
import RBM3D.Induction.Step5Kit
import RBM3D.Induction.Step5Kernel
import RBM3D.Propagator.Prop5Hold
import RBM3D.Propagator.Prop5Short
import RBM3D.Defs.RadialSum
import RBM3D.Defs.Convolution

/-!
# S5-27 (ST-4): the initial term of Step 5, case (ii)

Case (ii) is `ilambda²/L^d ≤ 1-t ≤ 1-s ≤ ilambda²/L²`.  Paper: arXiv:2507.20274,
`paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`), `(zYU2)` `3_5:2268-2281` (the four `≲` of
`3_5:2275-2281`).  Proves the pin `STIniTermII` of `Induction/Step5Pins.lean:331`: for `σ₁ ≠ σ₂`
the zero-mode-removed initial term `[Q^{(1)} ∘ 𝒰_{s,u,σ} (𝓛-𝒦)^{(2)}_{s,σ}]_a`
(`Q^{(1)} = zeroModeSet {0}`, `𝒰 = Ugen`) and for `σ₁ = σ₂` the same term without `Q` are
`≺ A^{-1/5} W^{-d}𝒯̃^L_{u,D}(|a₁-a₂|) + W^{-D}`, uniformly in `u ∈ [s,t]`.

* §1-§3 lattice sums and the tail function in regime (ii): `Σ_x (|x|+1)^{-(d-2)} ≲ L²`, the
  convolution of two power kernels (from `Defs/RadialSum`, `Defs/Convolution`), `𝒯_s ≤ 𝒯_u` and
  `e⁻¹ B_{u,r} ≤ 𝒯_u(r)` for `ℓ_u = L`, and `(uwp2-92kj)` without the floor (from
  `step5Kernel_profile_explicit_holds`, `(u,t) ↦ (s,u)`);
* §4-§6 the bilinear estimate `Σ_{b₁,b₂} (K - ρ L^{-d} J)(a₁,b₁) K(a₂,b₂) X(b₁,b₂)`,
  `K = α I + β Θ_u`, `ρ = (1-s)/(1-u)`;
* §7 the representation `𝒰_{s,u,σ} = K ⊗ K` (`step5Kernel_UN_decompU`) and
  `Q^{(1)} (K ⊗ K) = (K - ρ L^{-d} J) ⊗ K`;
* §8-§9 the deterministic cores `iniTermII_core` (`σ₁ ≠ σ₂`, `(prop:ThfadC0)` =
  `prop8ZeroMode_holds`) and `iniTermII_core_same` (`σ₁ = σ₂`, `(prop:ThfadC_short)` =
  `prop5Short_holds`);
* §10-§11 the `Prec` lift `iniTermII_concl` and the pin `stIniTermII_holds`; §12 compiled
  nonempty instances at `d = 3`.

Paper-delta candidates (see the report): `T2163a` the second term of `(zYU2)` is one of four terms
of the exact expansion of `(1 - s μ S)/(1 - u μ S) = (s/u) I + ((u-s)/u) Θ_u`, with
`(u-s)/u ≤ 1-s`; `T2163b` the kernel time in `3_5:2275-2281` is `u`, not `t`, and the floor is
`ρ W^{-D'}` with `D' = D + 1/𝔠` (absorbed by `STDecay` being `∀ D`); `T2163c` the ticket instance
`L = 3`, `g = 1/2` lies outside regime (ii).
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
private def iniTermII_PD (d L : ℕ) (x : Zd d L) : ℝ := ((((zdistD d L x : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹

/-- `(|x|_∞ + 1)^{-(d-2)}`. -/
private def iniTermII_PI (d L : ℕ) (x : Zd d L) : ℝ := ((((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹

private theorem iniTermII_PD_nonneg (x : Zd d L) : 0 ≤ iniTermII_PD d L x := by
  unfold iniTermII_PD; positivity

private theorem iniTermII_PI_nonneg (x : Zd d L) : 0 ≤ iniTermII_PI d L x := by
  unfold iniTermII_PI; positivity

private theorem iniTermII_PI_pos (x : Zd d L) : 0 < iniTermII_PI d L x := by
  unfold iniTermII_PI; positivity

private theorem iniTermII_PI_le_one (x : Zd d L) : iniTermII_PI d L x ≤ 1 := by
  unfold iniTermII_PI
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by have : (0:ℝ) ≤ ((zdistInf d L x : ℕ) : ℝ) := Nat.cast_nonneg _; linarith))

private theorem iniTermII_PD_le_PI (x : Zd d L) : iniTermII_PD d L x ≤ iniTermII_PI d L x := by
  unfold iniTermII_PD iniTermII_PI
  have h : ((zdistInf d L x : ℕ) : ℝ) ≤ ((zdistD d L x : ℕ) : ℝ) := by
    exact_mod_cast zdistInf_le_zdistD d L x
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) _)

private theorem iniTermII_PI_le_PD (hd : 1 ≤ d) (x : Zd d L) :
    iniTermII_PI d L x ≤ (d : ℝ) ^ (d - 2) * iniTermII_PD d L x := by
  unfold iniTermII_PD iniTermII_PI
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

private theorem iniTermII_zdistD_neg (x : Zd d L) : zdistD d L (-x) = zdistD d L x := by
  unfold zdistD
  exact Finset.sum_congr rfl fun i _ => by simp [zdist_neg]

private theorem iniTermII_zdistInf_neg (x : Zd d L) : zdistInf d L (-x) = zdistInf d L x := by
  unfold zdistInf
  exact Finset.sup_congr rfl fun i _ => by simp [zdist_neg]

private theorem iniTermII_zdistInf_sub_comm (a b : Zd d L) :
    zdistInf d L (a - b) = zdistInf d L (b - a) := by
  rw [← neg_sub, iniTermII_zdistInf_neg]

private theorem iniTermII_zdistD_sub_comm (a b : Zd d L) :
    zdistD d L (a - b) = zdistD d L (b - a) := by
  rw [← neg_sub, iniTermII_zdistD_neg]

private theorem iniTermII_PD_sub_comm (a b : Zd d L) :
    iniTermII_PD d L (a - b) = iniTermII_PD d L (b - a) := by
  unfold iniTermII_PD; rw [iniTermII_zdistD_sub_comm]

private theorem iniTermII_PI_sub_comm (a b : Zd d L) :
    iniTermII_PI d L (a - b) = iniTermII_PI d L (b - a) := by
  unfold iniTermII_PI; rw [iniTermII_zdistInf_sub_comm]

private theorem iniTermII_zdistInf_add_le (x y : Zd d L) :
    zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y := by
  unfold zdistInf
  refine Finset.sup_le fun i _ => ?_
  calc zdist L ((x + y) i) = zdist L (x i + y i) := rfl
    _ ≤ zdist L (x i) + zdist L (y i) := zdist_add_le L (x i) (y i)
    _ ≤ _ := Nat.add_le_add
        (Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i))
        (Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i))

private theorem iniTermII_zdistInf_le_L (x : Zd d L) : ((zdistInf d L x : ℕ) : ℝ) ≤ L := by
  have : zdistInf d L x ≤ L := Finset.sup_le fun i _ => zdist_le_L (x i)
  exact_mod_cast this

private theorem iniTermII_zdistInf_zero : zdistInf d L (0 : Zd d L) = 0 := by
  unfold zdistInf
  exact Nat.eq_zero_of_le_zero (Finset.sup_le fun i _ => by simp)

/-- `|a₁ - a₂| ≤ |a₁ - b₁| + |b₁ - b₂| + |b₂ - a₂|` in `zdistInf`. -/
private theorem iniTermII_tri (a₁ a₂ b₁ b₂ : Zd d L) :
    zdistInf d L (a₁ - a₂) ≤ zdistInf d L (b₁ - a₁) + zdistInf d L (b₁ - b₂) + zdistInf d L (b₂ - a₂) := by
  have h1 : a₁ - a₂ = -(b₁ - a₁) + (b₁ - b₂) + (b₂ - a₂) := by abel
  rw [h1]
  calc zdistInf d L (-(b₁ - a₁) + (b₁ - b₂) + (b₂ - a₂))
      ≤ zdistInf d L (-(b₁ - a₁) + (b₁ - b₂)) + zdistInf d L (b₂ - a₂) := iniTermII_zdistInf_add_le _ _
    _ ≤ (zdistInf d L (-(b₁ - a₁)) + zdistInf d L (b₁ - b₂)) + zdistInf d L (b₂ - a₂) :=
        Nat.add_le_add_right (iniTermII_zdistInf_add_le _ _) _
    _ = _ := by rw [iniTermII_zdistInf_neg]

/-- `Σ_x (|x|_∞+1)^{-(d-2)} ≤ C_d L²`. -/
private theorem iniTermII_sum_PD (hd : 3 ≤ d) (hL : 1 ≤ (L : ℝ)) :
    ∑ x : Zd d L, iniTermII_PD d L x ≤ Real.exp (√(d : ℝ)) * (2 ^ d * radC 1 * (L : ℝ) ^ 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  have := sum_radial_pow_le (L := L) k hL
  simp only [iniTermII_PD, show k + 2 - 2 = k by omega]
  push_cast at this ⊢
  exact this

private theorem iniTermII_sum_PI (hd : 3 ≤ d) (hL : 1 ≤ (L : ℝ)) :
    ∑ x : Zd d L, iniTermII_PI d L x ≤
      (d : ℝ) ^ (d - 2) * (Real.exp (√(d : ℝ)) * (2 ^ d * radC 1 * (L : ℝ) ^ 2)) := by
  calc ∑ x : Zd d L, iniTermII_PI d L x
      ≤ ∑ x : Zd d L, (d : ℝ) ^ (d - 2) * iniTermII_PD d L x :=
        Finset.sum_le_sum fun x _ => iniTermII_PI_le_PD (by omega) x
    _ = (d : ℝ) ^ (d - 2) * ∑ x : Zd d L, iniTermII_PD d L x := by rw [← Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (iniTermII_sum_PD hd hL) (by positivity)

/-- The convolution of two power kernels: `Σ_c P(a-c) P(c-b) ≤ C L² P(a-b)` (`sum_conv_le` at `ℓ₁ = ℓ₂ = L`). -/
private theorem iniTermII_conv_PD (hd : 3 ≤ d) (a b : Zd d L) :
    ∑ c : Zd d L, iniTermII_PD d L (a - c) * iniTermII_PD d L (c - b) ≤
      Real.exp (2 * √(d : ℝ)) * convC (d - 2) * (L : ℝ) ^ 2 * iniTermII_PD d L (a - b) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.one_le
  have hL0 : (0 : ℝ) < L := by linarith
  have h := sum_conv_le (L := L) k (ℓ₁ := (L : ℝ)) (ℓ₂ := (L : ℝ)) hL1 le_rfl a b
  have hex : ∀ x : Zd (k + 2) L,
      Real.exp (-√(((k + 2 : ℕ) : ℝ))) ≤ Real.exp (-√((zdistD (k + 2) L x : ℝ) / L)) := by
    intro x
    refine Real.exp_le_exp.mpr (neg_le_neg (Real.sqrt_le_sqrt ?_))
    rw [div_le_iff₀ hL0]
    have : ((zdistD (k + 2) L x : ℕ) : ℝ) ≤ ((k + 2) * L : ℕ) := by exact_mod_cast zdistD_le (k + 2) x
    push_cast at this ⊢
    linarith
  have hterm : ∀ c : Zd (k + 2) L, iniTermII_PD (k + 2) L (a - c) * iniTermII_PD (k + 2) L (c - b) ≤
      Real.exp (2 * √(((k + 2 : ℕ) : ℝ))) *
        (powW k (zdistD (k + 2) L (a - c)) * Real.exp (-√((zdistD (k + 2) L (a - c) : ℝ) / L))
          * (powW k (zdistD (k + 2) L (c - b)) * Real.exp (-√((zdistD (k + 2) L (c - b) : ℝ) / L)))) := by
    intro c
    have e1 := hex (a - c)
    have e2 := hex (c - b)
    have p1 : 0 ≤ powW k (zdistD (k + 2) L (a - c)) := powW_nonneg _ _
    have p2 : 0 ≤ powW k (zdistD (k + 2) L (c - b)) := powW_nonneg _ _
    have hP : iniTermII_PD (k + 2) L (a - c) * iniTermII_PD (k + 2) L (c - b)
        = powW k (zdistD (k + 2) L (a - c)) * powW k (zdistD (k + 2) L (c - b)) := by
      simp only [iniTermII_PD, powW, show k + 2 - 2 = k by omega]
    rw [hP]
    have hprod : 1 ≤ Real.exp (2 * √(((k + 2 : ℕ) : ℝ))) *
        (Real.exp (-√((zdistD (k + 2) L (a - c) : ℝ) / L)) *
          Real.exp (-√((zdistD (k + 2) L (c - b) : ℝ) / L))) := by
      have h1 : Real.exp (-√(((k + 2 : ℕ) : ℝ))) * Real.exp (-√(((k + 2 : ℕ) : ℝ))) ≤
          Real.exp (-√((zdistD (k + 2) L (a - c) : ℝ) / L)) *
            Real.exp (-√((zdistD (k + 2) L (c - b) : ℝ) / L)) :=
        mul_le_mul e1 e2 (Real.exp_pos _).le (Real.exp_pos _).le
      have h2 : Real.exp (2 * √(((k + 2 : ℕ) : ℝ))) *
          (Real.exp (-√(((k + 2 : ℕ) : ℝ))) * Real.exp (-√(((k + 2 : ℕ) : ℝ)))) = 1 := by
        rw [← Real.exp_add, ← Real.exp_add]; simp; ring_nf
      calc (1 : ℝ) = Real.exp (2 * √(((k + 2 : ℕ) : ℝ))) *
          (Real.exp (-√(((k + 2 : ℕ) : ℝ))) * Real.exp (-√(((k + 2 : ℕ) : ℝ)))) := h2.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    have hpp : 0 ≤ powW k (zdistD (k + 2) L (a - c)) * powW k (zdistD (k + 2) L (c - b)) := mul_nonneg p1 p2
    calc powW k (zdistD (k + 2) L (a - c)) * powW k (zdistD (k + 2) L (c - b))
        = (powW k (zdistD (k + 2) L (a - c)) * powW k (zdistD (k + 2) L (c - b))) * 1 := by ring
      _ ≤ (powW k (zdistD (k + 2) L (a - c)) * powW k (zdistD (k + 2) L (c - b))) *
          (Real.exp (2 * √(((k + 2 : ℕ) : ℝ))) *
            (Real.exp (-√((zdistD (k + 2) L (a - c) : ℝ) / L)) *
              Real.exp (-√((zdistD (k + 2) L (c - b) : ℝ) / L)))) :=
          mul_le_mul_of_nonneg_left hprod hpp
      _ = _ := by ring
  calc ∑ c : Zd (k + 2) L, iniTermII_PD (k + 2) L (a - c) * iniTermII_PD (k + 2) L (c - b)
      ≤ ∑ c : Zd (k + 2) L, Real.exp (2 * √(((k + 2 : ℕ) : ℝ))) *
        (powW k (zdistD (k + 2) L (a - c)) * Real.exp (-√((zdistD (k + 2) L (a - c) : ℝ) / L))
          * (powW k (zdistD (k + 2) L (c - b)) * Real.exp (-√((zdistD (k + 2) L (c - b) : ℝ) / L)))) :=
        Finset.sum_le_sum fun c _ => hterm c
    _ = Real.exp (2 * √(((k + 2 : ℕ) : ℝ))) * ∑ c : Zd (k + 2) L,
        (powW k (zdistD (k + 2) L (a - c)) * Real.exp (-√((zdistD (k + 2) L (a - c) : ℝ) / L))
          * (powW k (zdistD (k + 2) L (c - b)) * Real.exp (-√((zdistD (k + 2) L (c - b) : ℝ) / L)))) := by
        rw [← Finset.mul_sum]
    _ ≤ Real.exp (2 * √(((k + 2 : ℕ) : ℝ))) * (convC k * (L : ℝ) ^ 2 *
          (powW k (zdistD (k + 2) L (a - b)) * Real.exp (-√((zdistD (k + 2) L (a - b) : ℝ) / L)))) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ ≤ Real.exp (2 * √(((k + 2 : ℕ) : ℝ))) * (convC k * (L : ℝ) ^ 2 * powW k (zdistD (k + 2) L (a - b))) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        refine mul_le_mul_of_nonneg_left ?_ (by have := radC_pos κ₀_pos; unfold convC; positivity)
        calc powW k (zdistD (k + 2) L (a - b)) * Real.exp (-√((zdistD (k + 2) L (a - b) : ℝ) / L))
            ≤ powW k (zdistD (k + 2) L (a - b)) * 1 :=
              mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by
                have := Real.sqrt_nonneg ((zdistD (k + 2) L (a - b) : ℝ) / L); linarith)) (powW_nonneg _ _)
          _ = _ := mul_one _
    _ = _ := by
        simp only [iniTermII_PD, powW, show k + 2 - 2 = k by omega]; ring

end Lattice

/-! ### 2. The tail function in regime (ii) -/

section Tail

variable {d L : ℕ} {g : ℝ}

/-- `𝒯_v(r) ≤ B_{v,r} ≤ g⁻² (r+1)^{-(d-2)} + (L^d (1-v))⁻¹`. -/
private theorem iniTermII_tailT_le (hg : 0 < g) {v : ℝ} (hv : v < 1) {r : ℝ} (hr : 0 ≤ r) :
    tailT d L g v r ≤ (g ^ 2)⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - v))⁻¹ := by
  have hv0 : 0 < 1 - v := by linarith
  unfold tailT BparamR
  rw [abs_of_pos hv0]
  have he : Real.exp (-Real.sqrt (r / ellT L g v)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have := Real.sqrt_nonneg (r / ellT L g v); linarith)
  have hB : (g ^ 2 + (1 - v))⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - v))⁻¹
      ≤ (g ^ 2)⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - v))⁻¹ := by
    have h1 : (g ^ 2 + (1 - v))⁻¹ ≤ (g ^ 2)⁻¹ := inv_anti₀ (by positivity) (by linarith)
    have h2 : 0 ≤ ((r + 1) ^ (d - 2))⁻¹ := by positivity
    linarith [mul_le_mul_of_nonneg_right h1 h2]
  have hBn : 0 ≤ (g ^ 2 + (1 - v))⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - v))⁻¹ := by
    have : 0 ≤ ((L : ℝ) ^ d * (1 - v))⁻¹ := by positivity
    have : 0 ≤ (g ^ 2 + (1 - v))⁻¹ * ((r + 1) ^ (d - 2))⁻¹ := by positivity
    linarith
  calc _ ≤ ((g ^ 2 + (1 - v))⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - v))⁻¹) * 1 :=
        mul_le_mul_of_nonneg_left he hBn
    _ ≤ _ := by rw [mul_one]; exact hB

/-- In regime `1 - u ≤ g²/L²` and `0 ≤ r ≤ L`: `e⁻¹ B_{u,r} ≤ 𝒯_u(r)`. -/
private theorem iniTermII_tailT_ge (hg : 0 < g) {u : ℝ} (hu : u < 1) (hL : 1 ≤ (L : ℝ))
    (hreg : 1 - u ≤ g ^ 2 / (L : ℝ) ^ 2) {r : ℝ} (hr : 0 ≤ r) (hrL : r ≤ L) :
    Real.exp (-1) * ((g ^ 2 + (1 - u))⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - u))⁻¹)
      ≤ tailT d L g u r := by
  have hu0 : 0 < 1 - u := by linarith
  unfold tailT BparamR
  rw [abs_of_pos hu0]
  have hBn : 0 ≤ (g ^ 2 + (1 - u))⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - u))⁻¹ := by
    have : 0 ≤ ((L : ℝ) ^ d * (1 - u))⁻¹ := by positivity
    have : 0 ≤ (g ^ 2 + (1 - u))⁻¹ * ((r + 1) ^ (d - 2))⁻¹ := by positivity
    linarith
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (exp_tail_ge hg.le hu hL hreg hrL) hBn

/-- `𝒯_s(r) ≤ 𝒯_u(r)` for `s ≤ u < 1`, `r ≥ 0` (`B_{s,r} ≤ B_{u,r}`, `ℓ_s ≤ ℓ_u`). -/
private theorem iniTermII_tailT_mono (hg : 0 ≤ g) (hL1 : (1 : ℝ) ≤ L) {s u : ℝ} (hsu : s ≤ u)
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

/-! ### 3. `(uwp2-92kj)` without the floor -/

/-- `(uwp2-92kj)` (`3_5:2048-2053`) with `(u, t) ↦ (s, u)` and no floor: `𝒯_s ≤ 𝒯̃_s^{L}` for every floor `w > 0`, and
`(1-s)/(1-u) · w` is as small as we like. -/
private theorem iniTermII_stageA (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g s u : ℝ, 0 < g → g ≤ Λ → 0 ≤ s → s ≤ u → u < 1 →
      1 - s ≤ g ^ 2 / (L : ℝ) ^ 2 → ∀ a₁ a₂ : Zd d L,
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
  have h := H L hL g w⁻¹ 1 s u hg hgΛ (inv_pos.mpr hw) hs hsu hu (Or.inr hreg) a₁ a₂
  rw [Real.rpow_neg_one, inv_inv] at h
  have hle : ∀ b : Zd d L, ‖Theta d L g (u : ℂ) a₁ b‖ * tailT d L g s (zdistInf d L (b - a₂) : ℕ)
      ≤ ‖Theta d L g (u : ℂ) a₁ b‖ * tailW d L g s (L : ℝ) w⁻¹ 1 (zdistInf d L (b - a₂) : ℕ) := by
    intro b
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    unfold tailW
    rw [min_eq_left (iniTermII_zdistInf_le_L _)]
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
private theorem iniTermII_ZA (hL : 3 ≤ L) {g s u α β M q F CA : ℝ}
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
    have h := iniTermII_tailT_mono (d := d) hg hL1 hsu hu (r := (zdistInf d L (b₁ - a₂) : ℕ)) (Nat.cast_nonneg _)
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
      Finset.sum_congr rfl fun b₂ _ => by rw [iniTermII_zdistInf_sub_comm b₁ b₂]
    have hnn : 0 ≤ ∑ b₂ : Zd d L, ‖Theta d L g (u : ℂ) a₂ b₂‖ * tailT d L g s (zdistInf d L (b₂ - b₁) : ℕ) :=
      Finset.sum_nonneg fun b₂ _ => mul_nonneg (norm_nonneg _) (tailT_nonneg (Nat.cast_nonneg _))
    have := hA a₂ b₁
    rw [iniTermII_zdistInf_sub_comm a₂ b₁] at this
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

/-! ### 5. The first index: zero-mode average and `Θ̊` -/

section StageB

variable {d L : ℕ} [NeZero L]

private theorem iniTermII_sum_shift (a : Zd d L) (f : Zd d L → ℝ) :
    ∑ b : Zd d L, f (b - a) = ∑ x : Zd d L, f x :=
  Fintype.sum_equiv (Equiv.subRight a) _ _ fun _ => rfl

/-- The zero-mode average of the profile: `L^{-d} Σ_b 𝒯_u(|b - a₂|) ≤ C 𝒯_u(|a₁ - a₂|)` in regime (ii). -/
private theorem iniTermII_S2 {g u CSI : ℝ} (hL1 : (1 : ℝ) ≤ L) (hg : 0 < g) (hu : u < 1)
    (hreg : 1 - u ≤ g ^ 2 / (L : ℝ) ^ 2)
    (hSI : ∑ x : Zd d L, iniTermII_PI d L x ≤ CSI * (L : ℝ) ^ 2) (hCSI : 0 ≤ CSI) (a₁ a₂ : Zd d L) :
    ((L : ℝ) ^ d)⁻¹ * ∑ b : Zd d L, tailT d L g u (zdistInf d L (b - a₂) : ℕ)
      ≤ (CSI + 1) * Real.exp 1 * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) := by
  have hu0 : 0 < 1 - u := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  set c : ℝ := (L : ℝ) ^ d with hc
  have hc0 : 0 < c := by positivity
  set e₀ : ℝ := (c * (1 - u))⁻¹ with he₀
  have he₀0 : 0 < e₀ := by positivity
  have hg2 : 0 < g ^ 2 := by positivity
  have hLu : (L : ℝ) ^ 2 * (1 - u) ≤ g ^ 2 := by
    rw [le_div_iff₀ (by positivity)] at hreg; linarith
  -- pointwise
  have hpt : ∀ b : Zd d L, tailT d L g u (zdistInf d L (b - a₂) : ℕ)
      ≤ (g ^ 2)⁻¹ * iniTermII_PI d L (b - a₂) + e₀ := fun b =>
    iniTermII_tailT_le hg hu (Nat.cast_nonneg _)
  have hsum : ∑ b : Zd d L, tailT d L g u (zdistInf d L (b - a₂) : ℕ)
      ≤ (g ^ 2)⁻¹ * (CSI * (L : ℝ) ^ 2) + c * e₀ := by
    calc ∑ b : Zd d L, tailT d L g u (zdistInf d L (b - a₂) : ℕ)
        ≤ ∑ b : Zd d L, ((g ^ 2)⁻¹ * iniTermII_PI d L (b - a₂) + e₀) := Finset.sum_le_sum fun b _ => hpt b
      _ = (g ^ 2)⁻¹ * ∑ x : Zd d L, iniTermII_PI d L x + c * e₀ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, iniTermII_sum_shift a₂ (iniTermII_PI d L)]
          simp [Finset.sum_const, Finset.card_univ, hc]
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left hSI (inv_nonneg.mpr hg2.le)
          linarith
  have h1 : c⁻¹ * ((g ^ 2)⁻¹ * (CSI * (L : ℝ) ^ 2) + c * e₀) ≤ (CSI + 1) * e₀ := by
    have hA : c⁻¹ * ((g ^ 2)⁻¹ * (CSI * (L : ℝ) ^ 2)) ≤ CSI * e₀ := by
      have : (L : ℝ) ^ 2 * (g ^ 2)⁻¹ ≤ (1 - u)⁻¹ := by
        rw [← div_eq_mul_inv, ← one_div, div_le_div_iff₀ hg2 hu0]; linarith
      have h2 : c⁻¹ * ((g ^ 2)⁻¹ * (CSI * (L : ℝ) ^ 2)) = CSI * (c⁻¹ * ((L : ℝ) ^ 2 * (g ^ 2)⁻¹)) := by ring
      rw [h2, he₀, mul_inv]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hc0.le)) hCSI
    have hB : c⁻¹ * (c * e₀) = e₀ := by field_simp
    calc c⁻¹ * ((g ^ 2)⁻¹ * (CSI * (L : ℝ) ^ 2) + c * e₀)
        = c⁻¹ * ((g ^ 2)⁻¹ * (CSI * (L : ℝ) ^ 2)) + c⁻¹ * (c * e₀) := by ring
      _ ≤ CSI * e₀ + e₀ := by rw [hB]; linarith
      _ = _ := by ring
  have hge : e₀ ≤ Real.exp 1 * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) := by
    have h := iniTermII_tailT_ge (d := d) (L := L) hg hu hL1 hreg (r := (zdistInf d L (a₁ - a₂) : ℕ))
      (Nat.cast_nonneg _) (iniTermII_zdistInf_le_L _)
    have hP : 0 ≤ (g ^ 2 + (1 - u))⁻¹ * ((((zdistInf d L (a₁ - a₂) : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
    have h2 : Real.exp (-1) * e₀ ≤ tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) := by
      refine le_trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le) h
      simp only [he₀, hc]; linarith
    have h3 : Real.exp 1 * (Real.exp (-1) * e₀) = e₀ := by
      rw [← mul_assoc, ← Real.exp_add]; simp
    calc e₀ = Real.exp 1 * (Real.exp (-1) * e₀) := h3.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  calc c⁻¹ * ∑ b : Zd d L, tailT d L g u (zdistInf d L (b - a₂) : ℕ)
      ≤ c⁻¹ * ((g ^ 2)⁻¹ * (CSI * (L : ℝ) ^ 2) + c * e₀) := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hc0.le)
    _ ≤ (CSI + 1) * e₀ := h1
    _ ≤ (CSI + 1) * (Real.exp 1 * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ)) :=
        mul_le_mul_of_nonneg_left hge (by linarith)
    _ = _ := by ring

end StageB

section StageB3

variable {d L : ℕ} [NeZero L]

/-- `e₀ := (L^d (1-u))⁻¹ ≤ e 𝒯_u(r)` and `(g²)⁻¹ (r+1)^{-(d-2)} ≤ 2 e 𝒯_u(r)` in regime (ii), `r ≤ L`. -/
private theorem iniTermII_T_lower {g u : ℝ} (hg : 0 < g) (hu : u < 1) (hL1 : (1 : ℝ) ≤ L)
    (hreg : 1 - u ≤ g ^ 2 / (L : ℝ) ^ 2) (r : Zd d L) :
    ((L : ℝ) ^ d * (1 - u))⁻¹ ≤ Real.exp 1 * tailT d L g u (zdistInf d L r : ℕ) ∧
    (g ^ 2)⁻¹ * iniTermII_PI d L r ≤ 2 * Real.exp 1 * tailT d L g u (zdistInf d L r : ℕ) := by
  have hu0 : 0 < 1 - u := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hg2 : 0 < g ^ 2 := by positivity
  have hLu : (L : ℝ) ^ 2 * (1 - u) ≤ g ^ 2 := by
    rw [le_div_iff₀ (by positivity)] at hreg; linarith
  have h1u : 1 - u ≤ g ^ 2 := by
    have hL2 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
    calc 1 - u ≤ (L : ℝ) ^ 2 * (1 - u) := le_mul_of_one_le_left hu0.le hL2
      _ ≤ g ^ 2 := hLu
  have h := iniTermII_tailT_ge (d := d) (L := L) hg hu hL1 hreg (r := (zdistInf d L r : ℕ))
    (Nat.cast_nonneg _) (iniTermII_zdistInf_le_L _)
  have hP : 0 ≤ (g ^ 2 + (1 - u))⁻¹ * ((((zdistInf d L r : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
  have he0 : 0 ≤ ((L : ℝ) ^ d * (1 - u))⁻¹ := by positivity
  have hexp : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp 1 := Real.exp_pos _
  constructor
  · calc ((L : ℝ) ^ d * (1 - u))⁻¹ = Real.exp 1 * (Real.exp (-1) * ((L : ℝ) ^ d * (1 - u))⁻¹) := by
          rw [← mul_assoc, hexp, one_mul]
      _ ≤ Real.exp 1 * tailT d L g u (zdistInf d L r : ℕ) :=
          mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le) h) hpos.le
  · have h2 : (g ^ 2)⁻¹ ≤ 2 * (g ^ 2 + (1 - u))⁻¹ := by
      have h := inv_anti₀ (by positivity : 0 < g ^ 2 + (1 - u)) (by linarith : g ^ 2 + (1 - u) ≤ 2 * g ^ 2)
      rw [mul_inv] at h
      have : (0 : ℝ) < (g ^ 2)⁻¹ := by positivity
      linarith
    have h3 : (g ^ 2)⁻¹ * iniTermII_PI d L r ≤ 2 * ((g ^ 2 + (1 - u))⁻¹ * iniTermII_PI d L r) := by
      have := mul_le_mul_of_nonneg_right h2 (iniTermII_PI_nonneg r)
      linarith
    have h4 : (g ^ 2 + (1 - u))⁻¹ * iniTermII_PI d L r ≤ Real.exp 1 * tailT d L g u (zdistInf d L r : ℕ) := by
      calc _ = Real.exp 1 * (Real.exp (-1) * ((g ^ 2 + (1 - u))⁻¹ * iniTermII_PI d L r)) := by
            rw [← mul_assoc, hexp, one_mul]
        _ ≤ Real.exp 1 * tailT d L g u (zdistInf d L r : ℕ) := by
            refine mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le) h) hpos.le
            unfold iniTermII_PI
            linarith
    linarith

/-- The `Θ̊`-weighted sum: `β (g²)⁻¹ Σ_b P(|b - a₁|) 𝒯_u(|b - a₂|) ≤ C 𝒯_u(|a₁ - a₂|)`, using `β L² ≤ g²`. -/
private theorem iniTermII_S3 {g u β CSD CCv : ℝ} (hd : 3 ≤ d) (hL1 : (1 : ℝ) ≤ L) (hg : 0 < g) (hu : u < 1)
    (hreg : 1 - u ≤ g ^ 2 / (L : ℝ) ^ 2) (hβ0 : 0 ≤ β) (hβL : β * (L : ℝ) ^ 2 ≤ g ^ 2)
    (hSD : ∑ x : Zd d L, iniTermII_PD d L x ≤ CSD * (L : ℝ) ^ 2) (hCSD : 0 ≤ CSD)
    (hconv : ∀ a b : Zd d L, ∑ c : Zd d L, iniTermII_PD d L (a - c) * iniTermII_PD d L (c - b)
      ≤ CCv * (L : ℝ) ^ 2 * iniTermII_PD d L (a - b)) (hCCv : 0 ≤ CCv) (a₁ a₂ : Zd d L) :
    β * ((g ^ 2)⁻¹ * ∑ b : Zd d L, iniTermII_PD d L (b - a₁) * tailT d L g u (zdistInf d L (b - a₂) : ℕ))
      ≤ (2 * Real.exp 1 * (d : ℝ) ^ (d - 2) * CCv + Real.exp 1 * CSD) *
          tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) := by
  have hu0 : 0 < 1 - u := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hg2 : 0 < g ^ 2 := by positivity
  set e₀ : ℝ := ((L : ℝ) ^ d * (1 - u))⁻¹ with he₀
  have he₀0 : 0 ≤ e₀ := by positivity
  set K : ℝ := (d : ℝ) ^ (d - 2) with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨hlow1, hlow2⟩ := iniTermII_T_lower (d := d) (L := L) hg hu hL1 hreg (a₁ - a₂)
  have hpt : ∀ b : Zd d L, iniTermII_PD d L (b - a₁) * tailT d L g u (zdistInf d L (b - a₂) : ℕ)
      ≤ (g ^ 2)⁻¹ * K * (iniTermII_PD d L (a₁ - b) * iniTermII_PD d L (b - a₂)) + e₀ * iniTermII_PD d L (b - a₁) := by
    intro b
    have h1 : tailT d L g u (zdistInf d L (b - a₂) : ℕ) ≤ (g ^ 2)⁻¹ * (K * iniTermII_PD d L (b - a₂)) + e₀ := by
      refine le_trans (iniTermII_tailT_le hg hu (Nat.cast_nonneg _)) ?_
      have := iniTermII_PI_le_PD (d := d) (L := L) (by omega) (b - a₂)
      have h2 : (g ^ 2)⁻¹ * iniTermII_PI d L (b - a₂) ≤ (g ^ 2)⁻¹ * (K * iniTermII_PD d L (b - a₂)) :=
        mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hg2.le)
      have h3 : ((((zdistInf d L (b - a₂) : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ = iniTermII_PI d L (b - a₂) := rfl
      rw [h3]; linarith
    have hpd := iniTermII_PD_nonneg (d := d) (L := L) (b - a₁)
    calc iniTermII_PD d L (b - a₁) * tailT d L g u (zdistInf d L (b - a₂) : ℕ)
        ≤ iniTermII_PD d L (b - a₁) * ((g ^ 2)⁻¹ * (K * iniTermII_PD d L (b - a₂)) + e₀) :=
          mul_le_mul_of_nonneg_left h1 hpd
      _ = (g ^ 2)⁻¹ * K * (iniTermII_PD d L (a₁ - b) * iniTermII_PD d L (b - a₂)) + e₀ * iniTermII_PD d L (b - a₁) := by
          rw [iniTermII_PD_sub_comm a₁ b]; ring
  have hsum : ∑ b : Zd d L, iniTermII_PD d L (b - a₁) * tailT d L g u (zdistInf d L (b - a₂) : ℕ)
      ≤ (g ^ 2)⁻¹ * K * (CCv * (L : ℝ) ^ 2 * iniTermII_PD d L (a₁ - a₂)) + e₀ * (CSD * (L : ℝ) ^ 2) := by
    calc _ ≤ ∑ b : Zd d L, ((g ^ 2)⁻¹ * K * (iniTermII_PD d L (a₁ - b) * iniTermII_PD d L (b - a₂))
            + e₀ * iniTermII_PD d L (b - a₁)) := Finset.sum_le_sum fun b _ => hpt b
      _ = (g ^ 2)⁻¹ * K * ∑ b : Zd d L, iniTermII_PD d L (a₁ - b) * iniTermII_PD d L (b - a₂)
            + e₀ * ∑ x : Zd d L, iniTermII_PD d L x := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            iniTermII_sum_shift a₁ (iniTermII_PD d L)]
      _ ≤ _ := by
          have h1 := mul_le_mul_of_nonneg_left (hconv a₁ a₂) (mul_nonneg (inv_nonneg.mpr hg2.le) hK0)
          have h2 := mul_le_mul_of_nonneg_left hSD he₀0
          linarith
  -- multiply by β (g²)⁻¹ and use β L² ≤ g²
  have hβg : β * (L : ℝ) ^ 2 * (g ^ 2)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hg2]; exact hβL
  have hPD : iniTermII_PD d L (a₁ - a₂) ≤ iniTermII_PI d L (a₁ - a₂) := iniTermII_PD_le_PI _
  have hfin : β * ((g ^ 2)⁻¹ * ∑ b : Zd d L, iniTermII_PD d L (b - a₁) * tailT d L g u (zdistInf d L (b - a₂) : ℕ))
      ≤ K * CCv * ((g ^ 2)⁻¹ * iniTermII_PD d L (a₁ - a₂)) + CSD * e₀ := by
    have hnn : 0 ≤ (g ^ 2)⁻¹ := inv_nonneg.mpr hg2.le
    have h1 : β * ((g ^ 2)⁻¹ * ∑ b : Zd d L, iniTermII_PD d L (b - a₁) * tailT d L g u (zdistInf d L (b - a₂) : ℕ))
        ≤ β * ((g ^ 2)⁻¹ * ((g ^ 2)⁻¹ * K * (CCv * (L : ℝ) ^ 2 * iniTermII_PD d L (a₁ - a₂)) + e₀ * (CSD * (L : ℝ) ^ 2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hnn) hβ0
    have h2 : β * ((g ^ 2)⁻¹ * ((g ^ 2)⁻¹ * K * (CCv * (L : ℝ) ^ 2 * iniTermII_PD d L (a₁ - a₂)) + e₀ * (CSD * (L : ℝ) ^ 2)))
        = (β * (L : ℝ) ^ 2 * (g ^ 2)⁻¹) * (K * CCv * ((g ^ 2)⁻¹ * iniTermII_PD d L (a₁ - a₂)) + CSD * e₀) := by ring
    have h3 : 0 ≤ K * CCv * ((g ^ 2)⁻¹ * iniTermII_PD d L (a₁ - a₂)) + CSD * e₀ := by
      have := iniTermII_PD_nonneg (d := d) (L := L) (a₁ - a₂)
      positivity
    calc _ ≤ _ := h1
      _ = _ := h2
      _ ≤ 1 * (K * CCv * ((g ^ 2)⁻¹ * iniTermII_PD d L (a₁ - a₂)) + CSD * e₀) :=
          mul_le_mul_of_nonneg_right hβg h3
      _ = _ := one_mul _
  have hA : (g ^ 2)⁻¹ * iniTermII_PD d L (a₁ - a₂) ≤ 2 * Real.exp 1 * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) :=
    le_trans (mul_le_mul_of_nonneg_left hPD (inv_nonneg.mpr hg2.le)) hlow2
  calc _ ≤ K * CCv * ((g ^ 2)⁻¹ * iniTermII_PD d L (a₁ - a₂)) + CSD * e₀ := hfin
    _ ≤ K * CCv * (2 * Real.exp 1 * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ)) +
          CSD * (Real.exp 1 * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hA (mul_nonneg hK0 hCCv)) (mul_le_mul_of_nonneg_left hlow1 hCSD)
    _ = _ := by rw [hK]; ring

/-- The floor of the `Θ̊` sum: `β (g²)⁻¹ Σ_b P(|b - a₁|) ≤ C`. -/
private theorem iniTermII_S3F {g β CSD : ℝ} (hg : 0 < g) (hβL : β * (L : ℝ) ^ 2 ≤ g ^ 2) (hβ0 : 0 ≤ β)
    (hSD : ∑ x : Zd d L, iniTermII_PD d L x ≤ CSD * (L : ℝ) ^ 2) (hCSD : 0 ≤ CSD) (a₁ : Zd d L) :
    β * ((g ^ 2)⁻¹ * ∑ b : Zd d L, iniTermII_PD d L (b - a₁)) ≤ CSD := by
  have hg2 : 0 < g ^ 2 := by positivity
  rw [iniTermII_sum_shift a₁ (iniTermII_PD d L)]
  have h1 : β * ((g ^ 2)⁻¹ * ∑ x : Zd d L, iniTermII_PD d L x) ≤ β * ((g ^ 2)⁻¹ * (CSD * (L : ℝ) ^ 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSD (inv_nonneg.mpr hg2.le)) hβ0
  have hβg : β * (L : ℝ) ^ 2 * (g ^ 2)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hg2]; exact hβL
  calc _ ≤ _ := h1
    _ = CSD * (β * (L : ℝ) ^ 2 * (g ^ 2)⁻¹) := by ring
    _ ≤ CSD * 1 := mul_le_mul_of_nonneg_left hβg hCSD
    _ = CSD := mul_one _

end StageB3

/-! ### 6. The bilinear estimate `Σ_{b₁,b₂} (K̊(a₁,b₁)) K(a₂,b₂) X(b₁,b₂)` -/

section Bil

variable {d L : ℕ} [NeZero L]

/-- The one-index kernel `K = α 1 + β Θ_u` of `(eq:decompU)`, as a function. -/
private def iniTermII_Kf (d L : ℕ) [NeZero L] (g u α β : ℝ) (a b : Zd d L) : ℂ :=
  (if a = b then (α : ℂ) else 0) + (β : ℂ) * Theta d L g (u : ℂ) a b

private theorem iniTermII_Kf_norm_le {g u α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (a b : Zd d L) :
    ‖iniTermII_Kf d L g u α β a b‖ ≤ α * (if a = b then 1 else 0) + β * ‖Theta d L g (u : ℂ) a b‖ := by
  unfold iniTermII_Kf
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · split_ifs
    · simp [Real.norm_of_nonneg hα]
    · simp
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ]

/-- `K - (ρ/L^d) J = α (1 - L^{-d} J) + β Θ̊`. -/
private theorem iniTermII_Kf_sub {g s u α β : ℝ} (hαβ : α + β * (1 - u)⁻¹ = (1 - s) / (1 - u)) (a b : Zd d L) :
    iniTermII_Kf d L g u α β a b - ((((1 - s) / (1 - u) / (L : ℝ) ^ d : ℝ)) : ℂ)
      = (α : ℂ) * ((if a = b then (1 : ℂ) else 0) - ((L : ℂ) ^ d)⁻¹)
        + (β : ℂ) * (Theta d L g (u : ℂ) a b - ((L : ℂ) ^ d)⁻¹ * (1 - (u : ℂ))⁻¹) := by
  rw [← hαβ]
  unfold iniTermII_Kf
  push_cast
  split_ifs <;> ring

private theorem iniTermII_Kf_sub_norm_le {g s u α β C₈ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαβ : α + β * (1 - u)⁻¹ = (1 - s) / (1 - u))
    (hΘ : ∀ a b : Zd d L, ‖Theta d L g (u : ℂ) a b - ((L : ℂ) ^ d)⁻¹ * (1 - (u : ℂ))⁻¹‖
      ≤ C₈ * (g ^ 2)⁻¹ * iniTermII_PD d L (b - a)) (a b : Zd d L) :
    ‖iniTermII_Kf d L g u α β a b - ((((1 - s) / (1 - u) / (L : ℝ) ^ d : ℝ)) : ℂ)‖
      ≤ α * ((if a = b then 1 else 0) + ((L : ℝ) ^ d)⁻¹) + β * (C₈ * (g ^ 2)⁻¹ * iniTermII_PD d L (b - a)) := by
  rw [iniTermII_Kf_sub hαβ]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hα]
    refine mul_le_mul_of_nonneg_left ?_ hα
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · split_ifs <;> simp
    · rw [norm_inv, norm_pow, Complex.norm_natCast]
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ]
    exact mul_le_mul_of_nonneg_left (hΘ a b) hβ

end Bil

section Bil2

variable {L : ℕ} [NeZero L]

private theorem iniTermII_bil (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) (C₈ : ℝ) (hC₈ : 0 ≤ C₈) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g s u α β M q F : ℝ, 0 < g → g ≤ Λ → 0 ≤ s → s ≤ u →
      u < 1 → 1 - s ≤ g ^ 2 / (L : ℝ) ^ 2 → 0 ≤ α → α ≤ 1 → 0 ≤ β → β ≤ 1 - s →
      α + β * (1 - u)⁻¹ = (1 - s) / (1 - u) → 0 ≤ M → 0 ≤ q → 0 ≤ F →
      (∀ a b : Zd d L, ‖Theta d L g (u : ℂ) a b - ((L : ℂ) ^ d)⁻¹ * (1 - (u : ℂ))⁻¹‖
        ≤ C₈ * (g ^ 2)⁻¹ * iniTermII_PD d L (b - a)) →
      ∀ (a₁ a₂ : Zd d L) (X : Zd d L → Zd d L → ℂ),
        (∀ b₁ b₂, ‖X b₁ b₂‖ ≤ M * (q * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) + F)) →
        ‖∑ b₁ : Zd d L, ∑ b₂ : Zd d L,
            (iniTermII_Kf d L g u α β a₁ b₁ - ((((1 - s) / (1 - u) / (L : ℝ) ^ d : ℝ)) : ℂ)) *
              iniTermII_Kf d L g u α β a₂ b₂ * X b₁ b₂‖
          ≤ C * M * (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) + (1 - s) / (1 - u) * F) := by
  obtain ⟨CA, hCA, hAL⟩ := iniTermII_stageA d Λ hd hΛ
  set K : ℝ := (d : ℝ) ^ (d - 2) with hK
  set CSD : ℝ := Real.exp (√(d : ℝ)) * (2 ^ d * radC 1) with hCSDdef
  set CSI : ℝ := K * CSD with hCSIdef
  set CCv : ℝ := Real.exp (2 * √(d : ℝ)) * convC (d - 2) with hCCvdef
  have hK0 : 0 ≤ K := by positivity
  have hCSD : 0 ≤ CSD := by have := radC_pos (one_pos : (0 : ℝ) < 1); positivity
  have hCSI : 0 ≤ CSI := mul_nonneg hK0 hCSD
  have hCCv : 0 ≤ CCv := by have := radC_pos κ₀_pos; rw [hCCvdef]; unfold convC; positivity
  set Cq : ℝ := 1 + (CSI + 1) * Real.exp 1 + C₈ * (2 * Real.exp 1 * K * CCv + Real.exp 1 * CSD) with hCq
  set Cf : ℝ := 2 + C₈ * CSD with hCf
  have hCq0 : 0 ≤ Cq := by positivity
  have hCf0 : 0 ≤ Cf := by positivity
  refine ⟨(1 + CA) * (Cq + Cf + 1), by positivity, ?_⟩
  intro L _ hL g s u α β M q F hg hgΛ hs hsu hu hreg hα0 hα1 hβ0 hβ1 hαβ hM hq hF hΘ a₁ a₂ X hX
  have hL1 : (1 : ℝ) ≤ L := by
    have : (3 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hu0 : 0 < 1 - u := by linarith
  have hs1 : 0 ≤ 1 - s := by linarith
  have hρ0 : 0 ≤ (1 - s) / (1 - u) := div_nonneg hs1 hu0.le
  have hregu : 1 - u ≤ g ^ 2 / (L : ℝ) ^ 2 := by linarith
  have hβL : β * (L : ℝ) ^ 2 ≤ g ^ 2 := by
    have : β ≤ g ^ 2 / (L : ℝ) ^ 2 := hβ1.trans hreg
    rwa [le_div_iff₀ (by positivity)] at this
  have hSD : ∑ x : Zd d L, iniTermII_PD d L x ≤ CSD * (L : ℝ) ^ 2 := by
    have := iniTermII_sum_PD (d := d) (L := L) hd hL1
    calc _ ≤ _ := this
      _ = CSD * (L : ℝ) ^ 2 := by rw [hCSDdef]; ring
  have hSI : ∑ x : Zd d L, iniTermII_PI d L x ≤ CSI * (L : ℝ) ^ 2 := by
    have := iniTermII_sum_PI (d := d) (L := L) hd hL1
    calc _ ≤ _ := this
      _ = CSI * (L : ℝ) ^ 2 := by rw [hCSIdef, hCSDdef, hK]; ring
  have hconv : ∀ a b : Zd d L, ∑ c : Zd d L, iniTermII_PD d L (a - c) * iniTermII_PD d L (c - b)
      ≤ CCv * (L : ℝ) ^ 2 * iniTermII_PD d L (a - b) := fun a b => iniTermII_conv_PD hd a b
  set ρ : ℝ := (1 - s) / (1 - u) with hρ
  set c : ℝ := (L : ℝ) ^ d with hc
  have hc0 : 0 < c := by positivity
  set C₁ : ℝ := 1 + CA with hC₁
  have hC₁0 : 0 < C₁ := by positivity
  have hZ := fun b₁ => iniTermII_ZA (d := d) (L := L) hL (g := g) (s := s) (u := u) (α := α) (β := β) (M := M)
    (q := q) (F := F) (CA := CA) hs hsu hu hα1 hβ0 hβ1 hαβ hM hq hF hCA.le hg.le hL1
    (fun a₁ a₂ => hAL L hL g s u hg hgΛ hs hsu hu hreg a₁ a₂) a₂ b₁
  -- the weights
  set T₀ : ℝ := tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) with hT₀
  have hT₀0 : 0 ≤ T₀ := tailT_nonneg (Nat.cast_nonneg _)
  set R : Zd d L → ℝ := fun b₁ => C₁ * M * (q * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ) + ρ * F) with hR
  have hRnn : ∀ b₁, 0 ≤ R b₁ := fun b₁ => by
    have := tailT_nonneg (d := d) (L := L) (g := g) (t := u) (Nat.cast_nonneg (zdistInf d L (b₁ - a₂)))
    simp only [hR]; positivity
  set kk : Zd d L → ℝ := fun b₁ => α * ((if a₁ = b₁ then 1 else 0) + c⁻¹) + β * (C₈ * (g ^ 2)⁻¹ * iniTermII_PD d L (b₁ - a₁)) with hkk
  have hkknn : ∀ b₁, 0 ≤ kk b₁ := fun b₁ => by
    have := iniTermII_PD_nonneg (d := d) (L := L) (b₁ - a₁)
    simp only [hkk]; positivity
  -- step 1 and 2
  have hstep12 : ‖∑ b₁ : Zd d L, ∑ b₂ : Zd d L,
            (iniTermII_Kf d L g u α β a₁ b₁ - (((ρ / c : ℝ)) : ℂ)) *
              iniTermII_Kf d L g u α β a₂ b₂ * X b₁ b₂‖ ≤ ∑ b₁ : Zd d L, kk b₁ * R b₁ := by
    calc _ ≤ ∑ b₁ : Zd d L, ‖∑ b₂ : Zd d L, (iniTermII_Kf d L g u α β a₁ b₁ - (((ρ / c : ℝ)) : ℂ)) *
              iniTermII_Kf d L g u α β a₂ b₂ * X b₁ b₂‖ := norm_sum_le _ _
      _ ≤ ∑ b₁ : Zd d L, kk b₁ * R b₁ := by
        refine Finset.sum_le_sum fun b₁ _ => ?_
        have hsum_nn : 0 ≤ ∑ b₂ : Zd d L, (α * (if a₂ = b₂ then 1 else 0) + β * ‖Theta d L g (u : ℂ) a₂ b₂‖) *
            (M * (q * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) + F)) :=
          Finset.sum_nonneg fun b₂ _ => by
            have := tailT_nonneg (d := d) (L := L) (g := g) (t := s) (Nat.cast_nonneg (zdistInf d L (b₁ - b₂)))
            positivity
        calc ‖∑ b₂ : Zd d L, (iniTermII_Kf d L g u α β a₁ b₁ - (((ρ / c : ℝ)) : ℂ)) *
              iniTermII_Kf d L g u α β a₂ b₂ * X b₁ b₂‖
            ≤ ∑ b₂ : Zd d L, ‖(iniTermII_Kf d L g u α β a₁ b₁ - (((ρ / c : ℝ)) : ℂ)) *
              iniTermII_Kf d L g u α β a₂ b₂ * X b₁ b₂‖ := norm_sum_le _ _
          _ = ‖iniTermII_Kf d L g u α β a₁ b₁ - (((ρ / c : ℝ)) : ℂ)‖ *
              ∑ b₂ : Zd d L, ‖iniTermII_Kf d L g u α β a₂ b₂‖ * ‖X b₁ b₂‖ := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun b₂ _ => by rw [norm_mul, norm_mul]; ring
          _ ≤ kk b₁ * R b₁ := by
              refine mul_le_mul (iniTermII_Kf_sub_norm_le hα0 hβ0 hαβ hΘ a₁ b₁) ?_
                (Finset.sum_nonneg fun b₂ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hkknn b₁)
              refine le_trans (Finset.sum_le_sum fun b₂ _ => mul_le_mul (iniTermII_Kf_norm_le hα0 hβ0 a₂ b₂)
                (hX b₁ b₂) (norm_nonneg _) (by positivity)) ?_
              exact hZ b₁
  -- step 3
  have hsplit : ∑ b₁ : Zd d L, kk b₁ * R b₁ =
      α * R a₁ + (α * c⁻¹ * ∑ b₁ : Zd d L, R b₁ +
        β * C₈ * (g ^ 2)⁻¹ * ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁) * R b₁) := by
    have hterm : ∀ b₁ : Zd d L, kk b₁ * R b₁ =
        (if a₁ = b₁ then α * R b₁ else 0) + (α * c⁻¹ * R b₁ +
          β * C₈ * (g ^ 2)⁻¹ * (iniTermII_PD d L (b₁ - a₁) * R b₁)) := by
      intro b₁; simp only [hkk]; split_ifs <;> ring
    rw [Finset.sum_congr rfl fun b₁ _ => hterm b₁, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.sum_add_distrib]
    simp only [Finset.mem_univ, ite_true, ← Finset.mul_sum]
  have hRa : R a₁ = C₁ * M * (q * T₀ + ρ * F) := rfl
  have hT0nn : ∀ b₁ : Zd d L, 0 ≤ tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ) := fun b₁ =>
    tailT_nonneg (Nat.cast_nonneg _)
  have hsumR : ∑ b₁ : Zd d L, R b₁ =
      C₁ * M * (q * ∑ b₁ : Zd d L, tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ) + c * (ρ * F)) := by
    simp only [hR]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [Finset.sum_const, Finset.card_univ, hc]
  have hsumPR : ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁) * R b₁ =
      C₁ * M * (q * ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁) * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ)
        + ρ * F * ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁)) := by
    have : C₁ * M * (q * ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁) * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ)
        + ρ * F * ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁))
        = ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁) * R b₁ := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by simp only [hR]; ring
    exact this.symm
  -- the three pieces
  have hS2 := iniTermII_S2 (d := d) (L := L) (g := g) (u := u) (CSI := CSI) hL1 hg hu hregu hSI hCSI a₁ a₂
  have hS3 := iniTermII_S3 (d := d) (L := L) (g := g) (u := u) (β := β) (CSD := CSD) (CCv := CCv) hd hL1 hg hu hregu
    hβ0 hβL hSD hCSD hconv hCCv a₁ a₂
  have hS3F := iniTermII_S3F (d := d) (L := L) (g := g) (β := β) (CSD := CSD) hg hβL hβ0 hSD hCSD a₁
  have hqT : 0 ≤ q * T₀ := mul_nonneg hq hT₀0
  have hρF : 0 ≤ ρ * F := mul_nonneg hρ0 hF
  have hi : α * R a₁ ≤ C₁ * M * (q * T₀ + ρ * F) := by
    rw [← hRa]
    calc α * R a₁ ≤ 1 * R a₁ := mul_le_mul_of_nonneg_right hα1 (hRnn a₁)
      _ = R a₁ := one_mul _
  have hii : α * c⁻¹ * ∑ b₁ : Zd d L, R b₁ ≤ C₁ * M * (q * ((CSI + 1) * Real.exp 1 * T₀) + ρ * F) := by
    have h1 : α * c⁻¹ * ∑ b₁ : Zd d L, R b₁ ≤ c⁻¹ * ∑ b₁ : Zd d L, R b₁ := by
      have hnn : 0 ≤ c⁻¹ * ∑ b₁ : Zd d L, R b₁ := mul_nonneg (inv_nonneg.mpr hc0.le) (Finset.sum_nonneg fun b _ => hRnn b)
      calc α * c⁻¹ * ∑ b₁ : Zd d L, R b₁ = α * (c⁻¹ * ∑ b₁ : Zd d L, R b₁) := by ring
        _ ≤ 1 * (c⁻¹ * ∑ b₁ : Zd d L, R b₁) := mul_le_mul_of_nonneg_right hα1 hnn
        _ = _ := one_mul _
    have h2 : c⁻¹ * ∑ b₁ : Zd d L, R b₁ = C₁ * M * (q * (c⁻¹ * ∑ b₁ : Zd d L, tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ)) + ρ * F) := by
      rw [hsumR]; field_simp
    have h3 : q * (c⁻¹ * ∑ b₁ : Zd d L, tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ)) ≤ q * ((CSI + 1) * Real.exp 1 * T₀) :=
      mul_le_mul_of_nonneg_left hS2 hq
    calc _ ≤ _ := h1
      _ = _ := h2
      _ ≤ _ := by
        have : 0 ≤ C₁ * M := by positivity
        exact mul_le_mul_of_nonneg_left (add_le_add h3 le_rfl) this
  have hiii : β * C₈ * (g ^ 2)⁻¹ * ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁) * R b₁
      ≤ C₁ * M * (q * (C₈ * ((2 * Real.exp 1 * K * CCv + Real.exp 1 * CSD) * T₀)) + ρ * F * (C₈ * CSD)) := by
    rw [hsumPR]
    have : β * C₈ * (g ^ 2)⁻¹ * (C₁ * M * (q * ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁) * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ)
        + ρ * F * ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁)))
        = C₁ * M * (q * (C₈ * (β * ((g ^ 2)⁻¹ * ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁) * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ))))
          + ρ * F * (C₈ * (β * ((g ^ 2)⁻¹ * ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁))))) := by ring
    rw [this]
    have hA1 : q * (C₈ * (β * ((g ^ 2)⁻¹ * ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁) * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ))))
        ≤ q * (C₈ * ((2 * Real.exp 1 * K * CCv + Real.exp 1 * CSD) * T₀)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS3 hC₈) hq
    have hA2 : ρ * F * (C₈ * (β * ((g ^ 2)⁻¹ * ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁))))
        ≤ ρ * F * (C₈ * CSD) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS3F hC₈) hρF
    have : 0 ≤ C₁ * M := by positivity
    exact mul_le_mul_of_nonneg_left (add_le_add hA1 hA2) this
  -- assemble
  have hfinal : ∑ b₁ : Zd d L, kk b₁ * R b₁ ≤ C₁ * M * (Cq * (q * T₀) + Cf * (ρ * F)) := by
    rw [hsplit]
    calc _ ≤ C₁ * M * (q * T₀ + ρ * F) + (C₁ * M * (q * ((CSI + 1) * Real.exp 1 * T₀) + ρ * F)
          + C₁ * M * (q * (C₈ * ((2 * Real.exp 1 * K * CCv + Real.exp 1 * CSD) * T₀)) + ρ * F * (C₈ * CSD))) :=
          add_le_add hi (add_le_add hii hiii)
      _ = _ := by rw [hCq, hCf]; ring
  have hmain : C₁ * M * (Cq * (q * T₀) + Cf * (ρ * F)) ≤ C₁ * (Cq + Cf + 1) * M * (q * T₀ + ρ * F) := by
    have h1 : 0 ≤ C₁ * M * ((Cf + 1) * (q * T₀) + (Cq + 1) * (ρ * F)) := by positivity
    have h2 : C₁ * (Cq + Cf + 1) * M * (q * T₀ + ρ * F)
        = C₁ * M * (Cq * (q * T₀) + Cf * (ρ * F)) + C₁ * M * ((Cf + 1) * (q * T₀) + (Cq + 1) * (ρ * F)) := by ring
    rw [h2]; exact le_add_of_nonneg_right h1
  exact hstep12.trans (hfinal.trans hmain)

end Bil2

/-! ### 7. The kernel `𝒰_{s,u}` on two indices: the representation `K ⊗ K` -/

section Rep

variable {d L : ℕ} [NeZero L]

private theorem iniTermII_sum_fin2 (f : (Fin 2 → Zd d L) → ℂ) :
    ∑ b : Fin 2 → Zd d L, f b = ∑ b₁ : Zd d L, ∑ b₂ : Zd d L, f ![b₁, b₂] := by
  have h : ∑ b : Fin 2 → Zd d L, f b = ∑ p : Zd d L × Zd d L, f ![p.1, p.2] :=
    Fintype.sum_equiv (piFinTwoEquiv fun _ : Fin 2 => Zd d L) _ _ (fun b => by
      congr 1; funext i; fin_cases i <;> simp [piFinTwoEquiv])
  rw [h, Fintype.sum_prod_type]

/-- `𝒰_{s,u,σ}` on two indices is `K ⊗ K`, `K = α I + β Θ_{uμ}`, `α = s/u`, `β = (u-s)/u ≤ 1-s`
(`(eq:decompU)`, `3_5:1983`); for `u = 0` (so `s = 0`) `K = I`. -/
private theorem iniTermII_Ugen_rep (hL : 3 ≤ L) {g E s u : ℝ} (hE : |E| ≤ 2) {σ : Fin 2 → Bool} {μ : ℂ}
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
      rw [hdec, iniTermII_sum_fin2]
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

section ZeroMode

variable {d L : ℕ} [NeZero L]

/-- `Q^{(1)} (K ⊗ K) = (K - (ρ/L^d) J) ⊗ K`: the zero mode of the first index, `Σ_c K(c,b) = ρ`. -/
private theorem iniTermII_zms_rep (hL : 3 ≤ L) {g s u α β : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hαβ : α + β * (1 - u)⁻¹ = (1 - s) / (1 - u)) (X : (Fin 2 → Zd d L) → ℂ) (a : Fin 2 → Zd d L) :
    zeroModeSet d L {0} (fun a' : Fin 2 → Zd d L => ∑ b₁ : Zd d L, ∑ b₂ : Zd d L,
        ((if a' 0 = b₁ then (α : ℂ) else 0) + (β : ℂ) * Theta d L g (u : ℂ) (a' 0) b₁) *
          ((if a' 1 = b₂ then (α : ℂ) else 0) + (β : ℂ) * Theta d L g (u : ℂ) (a' 1) b₂) * X ![b₁, b₂]) a
      = ∑ b₁ : Zd d L, ∑ b₂ : Zd d L,
          (((if a 0 = b₁ then (α : ℂ) else 0) + (β : ℂ) * Theta d L g (u : ℂ) (a 0) b₁)
            - ((((1 - s) / (1 - u) / (L : ℝ) ^ d : ℝ)) : ℂ)) *
          ((if a 1 = b₂ then (α : ℂ) else 0) + (β : ℂ) * Theta d L g (u : ℂ) (a 1) b₂) * X ![b₁, b₂] := by
  have hξ : ‖(u : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_of_nonneg hu0]
  have hcol : ∀ b₁ : Zd d L, ∑ c : Zd d L, ((if c = b₁ then (α : ℂ) else 0) + (β : ℂ) * Theta d L g (u : ℂ) c b₁)
      = (((1 - s) / (1 - u) : ℝ) : ℂ) := by
    intro b₁
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 : ∑ c : Zd d L, (if c = b₁ then (α : ℂ) else 0) = α := by simp
    have h2 : ∑ c : Zd d L, Theta d L g (u : ℂ) c b₁ = (1 - (u : ℂ))⁻¹ := by
      have : ∀ c : Zd d L, Theta d L g (u : ℂ) c b₁ = Theta d L g (u : ℂ) b₁ c := fun c => by
        have := congrFun (congrFun (Theta_transpose_of_three_le (d := d) (L := L) (g := g) hL hξ) b₁) c
        simpa [Matrix.transpose_apply] using this
      rw [Finset.sum_congr rfl fun c _ => this c]
      exact sum_Theta_row_of_three_le hL hξ b₁
    rw [h1, h2, ← hαβ]
    push_cast
    ring
  have hLd : ((L : ℂ) ^ d) ≠ 0 := by
    have : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
    exact pow_ne_zero _ this
  have hupd : ∀ (c : Zd d L), (Function.update a 0 c) 0 = c ∧ (Function.update a 0 c) 1 = a 1 := fun c =>
    ⟨by simp, by simp⟩
  have hS : ∑ x : Zd d L, ∑ x_1 : Zd d L, ∑ x_2 : Zd d L,
        ((if x = x_1 then (α : ℂ) else 0) + (β : ℂ) * Theta d L g (u : ℂ) x x_1) *
          ((if a 1 = x_2 then (α : ℂ) else 0) + (β : ℂ) * Theta d L g (u : ℂ) (a 1) x_2) * X ![x_1, x_2]
      = ∑ b₁ : Zd d L, ∑ b₂ : Zd d L, (((1 - s) / (1 - u) : ℝ) : ℂ) *
          ((if a 1 = b₂ then (α : ℂ) else 0) + (β : ℂ) * Theta d L g (u : ℂ) (a 1) b₂) * X ![b₁, b₂] := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b₂ _ => ?_
    rw [← Finset.sum_mul, ← Finset.sum_mul, hcol]
  simp only [zeroModeSet, Finset.toList_singleton, List.foldr, zeroModeOp, avgOp]
  simp only [hupd]
  rw [hS]
  simp only [sub_mul, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b₂ _ => ?_
  push_cast
  field_simp

end ZeroMode

/-! ### 8. The deterministic core, `σ₁ ≠ σ₂` -/

section Core

variable {d L : ℕ} [NeZero L]

private theorem iniTermII_cyc_mixed {E : ℝ} (hE : |E| ≤ 2) {σ : Fin 2 → Bool} (h : σ 0 ≠ σ 1) (i : Fin 2) :
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

private theorem iniTermII_Theta_shift (hL : 3 ≤ L) {g : ℝ} {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a b : Zd d L) :
    Theta d L g ξ a b = Theta d L g ξ 0 (b - a) := by
  have := Theta_apply_add_right_of_three_le (d := d) (g := g) hL hξ 0 (b - a) a
  rwa [zero_add, sub_add_cancel] at this

end Core

/-- **Target 2, `σ₁ ≠ σ₂`: the deterministic core of `(zYU2)`** (`3_5:2268-2281`).  For `0 ≤ s ≤ u < 1`, `0 < g ≤ Λ`,
`1 - s ≤ g²/L²` (regime (ii)), `|E| ≤ 2` with `κ_m ≤ Im m(E)` (`κ_m = √(κ(4-κ))/2` for `|E| ≤ 2 - κ`), `σ₁ ≠ σ₂` and every
two-index `X` with `|X_b| ≤ M ((λ W^{-d}) 𝒯_s(|b₁-b₂|) + W^{-D})` (the `STDecay` profile at `s`, `λ = (W^{-d}B_{s,0})^{1/5}`,
`𝒯_s = B_{s,r} e^{-√(r/ℓ_s)}`):
`|[Q^{(1)} 𝒰_{s,u,σ} X]_a| ≤ C M ((λ W^{-d}) 𝒯_u(|a₁-a₂|) + ((1-s)/(1-u)) W^{-D})`, `C = C(d, Λ, κ_m)`.  The kernel is the exact
`(1 - s μ S)/(1 - u μ S) = (s/u) I + ((u-s)/u) Θ_u`; `Q^{(1)}` replaces `Θ_u` by `Θ̊_u` on the first index and removes `L^{-d} J`
from `(s/u) I`; the other three terms of the expansion of `(zYU2)` are bounded as well (paper-delta candidate `T2163a`). -/
theorem iniTermII_core (d : ℕ) (Λ κm : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) (hκm : 0 < κm) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g W D E s u M lam : ℝ), 0 < g → g ≤ Λ → 0 < W →
        |E| ≤ 2 → κm ≤ (mE E).im → 0 ≤ s → s ≤ u → u < 1 → 1 - s ≤ g ^ 2 / (L : ℝ) ^ 2 → 0 ≤ M → 0 ≤ lam →
        ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ X : (Fin 2 → Zd d L) → ℂ,
          (∀ b, ‖X b‖ ≤ M * (lam * (W ^ d)⁻¹ * tailT d L g s (zdistInf d L (b 0 - b 1) : ℕ) + W ^ (-D))) →
          ∀ a, ‖zeroModeSet d L {0} (RBM.Ind.Ugen d L g E σ s u X) a‖ ≤
            C * M * (lam * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) +
              (1 - s) / (1 - u) * W ^ (-D)) := by
  obtain ⟨C₈, hC₈, H8⟩ := prop8ZeroMode_holds d Λ κm hd hΛ hκm
  obtain ⟨C, hC, Hb⟩ := iniTermII_bil d Λ hd hΛ C₈ hC₈.le
  refine ⟨C, hC, ?_⟩
  intro L _ hL g W D E s u M lam hg hgΛ hW hE hκ hs hsu hu hreg hM hlam σ hσ X hX a
  have hu0 : 0 ≤ u := hs.trans hsu
  have hξ : ‖(u : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_of_nonneg hu0]
  have hg2 : 0 < g ^ 2 := by positivity
  obtain ⟨α, β, hα0, hα1, hβ0, hβ1, hαβ, hrep⟩ :=
    iniTermII_Ugen_rep (d := d) (L := L) (g := g) hL hE (μ := 1) (iniTermII_cyc_mixed hE hσ) hs hsu hu
  have hfun : RBM.Ind.Ugen d L g E σ s u X = fun a' : Fin 2 → Zd d L => ∑ b₁ : Zd d L, ∑ b₂ : Zd d L,
      ((if a' 0 = b₁ then (α : ℂ) else 0) + (β : ℂ) * Theta d L g (u : ℂ) (a' 0) b₁) *
        ((if a' 1 = b₂ then (α : ℂ) else 0) + (β : ℂ) * Theta d L g (u : ℂ) (a' 1) b₂) * X ![b₁, b₂] := by
    funext a'
    simpa only [mul_one] using hrep X a'
  rw [hfun, iniTermII_zms_rep hL hu0 hu hαβ X a]
  -- the `Θ̊` bound from `(prop:ThfadC0)`
  have hμ1 : PropSpin (mE E) true * PropSpin (mE E) false = 1 := by
    have h := norm_mE hE
    simp only [PropSpin, ite_true, Bool.false_eq_true, ite_false]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h]; simp
  have hΘ : ∀ a' b' : Zd d L, ‖Theta d L g (u : ℂ) a' b' - ((L : ℂ) ^ d)⁻¹ * (1 - (u : ℂ))⁻¹‖
      ≤ C₈ * (g ^ 2)⁻¹ * iniTermII_PD d L (b' - a') := by
    intro a' b'
    have h8 := H8 L hL g hg hgΛ u hu0 hu (mE E) (norm_mE hE) hκ true false (b' - a')
    rw [hμ1, mul_one, Theta0_apply_eq hL hξ, ← iniTermII_Theta_shift hL hξ a' b'] at h8
    refine h8.trans ?_
    have h1 : (g ^ 2 + |1 - u|)⁻¹ ≤ (g ^ 2)⁻¹ := inv_anti₀ hg2 (by have := abs_nonneg (1 - u); linarith)
    have h2 : 0 ≤ iniTermII_PD d L (b' - a') := iniTermII_PD_nonneg _
    have h3 : ((((zdistD d L (b' - a') : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ = iniTermII_PD d L (b' - a') := rfl
    rw [h3]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC₈.le) h2
  have hq : 0 ≤ lam * (W ^ d)⁻¹ := by positivity
  have hF : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  have hX' : ∀ b₁ b₂ : Zd d L, ‖X ![b₁, b₂]‖ ≤
      M * (lam * (W ^ d)⁻¹ * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) + W ^ (-D)) := fun b₁ b₂ => by
    simpa using hX ![b₁, b₂]
  have := Hb L hL g s u α β M (lam * (W ^ d)⁻¹) (W ^ (-D)) hg hgΛ hs hsu hu hreg hα0 hα1 hβ0 hβ1 hαβ hM hq hF hΘ
    (a 0) (a 1) (fun b₁ b₂ => X ![b₁, b₂]) hX'
  exact this

/-! ### 9. The deterministic core, `σ₁ = σ₂` -/

section CoreSame

variable {d L : ℕ} [NeZero L]

/-- `𝒯_s(|b₁-b₂|) ≤ e (|b₁-a₁| + |b₂-a₂| + 1)^{d-2} 𝒯_u(|a₁-a₂|)` in regime (ii): `|a₁-a₂| ≤ |b₁-b₂| + m` gives
`(|b₁-b₂|+1)^{-(d-2)} ≤ (m+1)^{d-2} (|a₁-a₂|+1)^{-(d-2)}`, `B_{s,·} ≤ B_{u,·}`, and `B_{u,r} ≤ e 𝒯_u(r)` for `ℓ_u = L`, `r ≤ L`;
the polynomial loss `(m+1)^{d-2}` is absorbed by the exponential decay of the short-range kernel. -/
private theorem iniTermII_Ts_le {g s u : ℝ} (hg : 0 < g) (hL1 : (1 : ℝ) ≤ L) (hsu : s ≤ u) (hu : u < 1)
    (hreg : 1 - u ≤ g ^ 2 / (L : ℝ) ^ 2) (a₁ a₂ b₁ b₂ : Zd d L) :
    tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) ≤
      Real.exp 1 * ((((zdistInf d L (b₁ - a₁) : ℕ) : ℝ) + ((zdistInf d L (b₂ - a₂) : ℕ) : ℝ) + 1) ^ (d - 2)) *
        tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) := by
  have hs1 : s < 1 := lt_of_le_of_lt hsu hu
  have hu0 : 0 < 1 - u := by linarith
  have hs0 : 0 < 1 - s := by linarith
  set r' : ℝ := ((zdistInf d L (b₁ - b₂) : ℕ) : ℝ) with hr'
  set r : ℝ := ((zdistInf d L (a₁ - a₂) : ℕ) : ℝ) with hr
  set m : ℝ := ((zdistInf d L (b₁ - a₁) : ℕ) : ℝ) + ((zdistInf d L (b₂ - a₂) : ℕ) : ℝ) with hm
  have hr'0 : 0 ≤ r' := Nat.cast_nonneg _
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  have hm0 : 0 ≤ m := by positivity
  have htri : r ≤ m + r' := by
    have := iniTermII_tri a₁ a₂ b₁ b₂
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
  -- `𝒯_s ≤ B_{s,r'} ≤ (m+1)^k B_{u,r} ≤ (m+1)^k e 𝒯_u`
  have hBs : tailT d L g s r' ≤ (m + 1) ^ (d - 2) *
      ((g ^ 2 + (1 - u))⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - u))⁻¹) := by
    unfold tailT BparamR
    rw [abs_of_pos hs0]
    have he : Real.exp (-Real.sqrt (r' / ellT L g s)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have := Real.sqrt_nonneg (r' / ellT L g s); linarith)
    have hA : (g ^ 2 + (1 - s))⁻¹ ≤ (g ^ 2 + (1 - u))⁻¹ := inv_anti₀ (by positivity) (by linarith)
    have hZ : ((L : ℝ) ^ d * (1 - s))⁻¹ ≤ ((L : ℝ) ^ d * (1 - u))⁻¹ :=
      inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    have hP : 0 ≤ ((r' + 1) ^ (d - 2))⁻¹ := by positivity
    have hBn : 0 ≤ (g ^ 2 + (1 - s))⁻¹ * ((r' + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - s))⁻¹ := by
      have : 0 ≤ ((L : ℝ) ^ d * (1 - s))⁻¹ := by positivity
      have : 0 ≤ (g ^ 2 + (1 - s))⁻¹ * ((r' + 1) ^ (d - 2))⁻¹ := by positivity
      linarith
    have h1 : (g ^ 2 + (1 - s))⁻¹ * ((r' + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - s))⁻¹
        ≤ (m + 1) ^ (d - 2) * ((g ^ 2 + (1 - u))⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - u))⁻¹) := by
      have hm1 : (1 : ℝ) ≤ (m + 1) ^ (d - 2) := one_le_pow₀ (by linarith)
      have hc : 0 ≤ ((L : ℝ) ^ d * (1 - u))⁻¹ := by positivity
      have h2 : (g ^ 2 + (1 - s))⁻¹ * ((r' + 1) ^ (d - 2))⁻¹ ≤
          (g ^ 2 + (1 - u))⁻¹ * ((m + 1) ^ (d - 2) * ((r + 1) ^ (d - 2))⁻¹) :=
        mul_le_mul hA hpow hP (by positivity)
      have h3 : ((L : ℝ) ^ d * (1 - s))⁻¹ ≤ (m + 1) ^ (d - 2) * ((L : ℝ) ^ d * (1 - u))⁻¹ :=
        hZ.trans (le_mul_of_one_le_left hc hm1)
      calc _ ≤ (g ^ 2 + (1 - u))⁻¹ * ((m + 1) ^ (d - 2) * ((r + 1) ^ (d - 2))⁻¹) +
            (m + 1) ^ (d - 2) * ((L : ℝ) ^ d * (1 - u))⁻¹ := add_le_add h2 h3
        _ = _ := by ring
    calc _ ≤ (g ^ 2 + (1 - s))⁻¹ * ((r' + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - s))⁻¹ := by
          have := mul_le_mul_of_nonneg_left he hBn
          linarith
      _ ≤ _ := h1
  have hge := iniTermII_tailT_ge (d := d) (L := L) hg hu hL1 hreg (r := r) hr0 (iniTermII_zdistInf_le_L _)
  have hexp : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
  have hB2 : (g ^ 2 + (1 - u))⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - u))⁻¹ ≤ Real.exp 1 * tailT d L g u r := by
    calc _ = Real.exp 1 * (Real.exp (-1) * ((g ^ 2 + (1 - u))⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - u))⁻¹)) := by
          rw [← mul_assoc, hexp, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hge (Real.exp_pos _).le
  calc tailT d L g s r' ≤ _ := hBs
    _ ≤ (m + 1) ^ (d - 2) * (Real.exp 1 * tailT d L g u r) :=
        mul_le_mul_of_nonneg_left hB2 (by positivity)
    _ = Real.exp 1 * (m + 1) ^ (d - 2) * tailT d L g u r := by ring

end CoreSame

section CoreSame2

variable {d L : ℕ} [NeZero L]

private theorem iniTermII_poly_exp_le {c : ℝ} (hc : 0 < c) (k : ℕ) {r : ℝ} (hr : 0 ≤ r) :
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
private theorem iniTermII_sum_poly_exp (hd : 3 ≤ d) {c : ℝ} (hc : 0 < c) :
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
            _ ≤ _ := iniTermII_poly_exp_le hc k (Nat.cast_nonneg _)
      _ = (Nat.factorial k : ℝ) / (c / 2) ^ k * Real.exp (c / 2) *
            ∑ x : Zd (k + 2) L, Real.exp (-((c / 2) * ((zdistD (k + 2) L x : ℕ) : ℝ))) := by
          rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_radial_exp_decay_le (L := L) k (by positivity : 0 < c / 2)) (by positivity)

end CoreSame2

section CoreSame3

variable {d L : ℕ} [NeZero L]

/-- The short-range bilinear estimate: `|Θ'_{ab}| ≤ C_s (1_{a=b} + g² e^{-c|b-a|})` (`(prop:ThfadC_short)`). -/
private theorem iniTermII_bil_same (d : ℕ) (hd : 3 ≤ d) (Cs c₀ Λ : ℝ) (hCs : 0 ≤ Cs) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g s u α β M q F : ℝ, 0 < g → g ≤ Λ → s ≤ u → u < 1 →
      1 - s ≤ g ^ 2 / (L : ℝ) ^ 2 → 0 ≤ α → α ≤ 1 → 0 ≤ β → β ≤ 1 → 0 ≤ M → 0 ≤ q → 0 ≤ F →
      ∀ Θ' : Zd d L → Zd d L → ℂ,
        (∀ a b : Zd d L, ‖Θ' a b‖ ≤ Cs * ((if a = b then 1 else 0) +
          g ^ 2 * Real.exp (-(c₀ * ((zdistD d L (b - a) : ℕ) : ℝ))))) →
        ∀ (a₁ a₂ : Zd d L) (X : Zd d L → Zd d L → ℂ),
          (∀ b₁ b₂, ‖X b₁ b₂‖ ≤ M * (q * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) + F)) →
          ‖∑ b₁ : Zd d L, ∑ b₂ : Zd d L,
              ((if a₁ = b₁ then (α : ℂ) else 0) + (β : ℂ) * Θ' a₁ b₁) *
                ((if a₂ = b₂ then (α : ℂ) else 0) + (β : ℂ) * Θ' a₂ b₂) * X b₁ b₂‖
            ≤ C * M * (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) + F) := by
  obtain ⟨Cp, hCp, hpoly⟩ := iniTermII_sum_poly_exp (d := d) hd hc₀
  set S : ℝ := (1 + Cs) + Cs * Λ ^ 2 * Cp with hS
  have hS0 : 0 ≤ S := by positivity
  refine ⟨Real.exp 1 * S ^ 2 + S ^ 2 + 1, by positivity, ?_⟩
  intro L _ hL g s u α β M q F hg hgΛ hsu hu hreg hα0 hα1 hβ0 hβ1 hM hq hF Θ' hΘ a₁ a₂ X hX
  have hL1 : (1 : ℝ) ≤ L := by
    have : (3 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hu0 : 0 < 1 - u := by linarith
  have hs1 : s ≤ 1 - 0 := by linarith
  have hregu : 1 - u ≤ g ^ 2 / (L : ℝ) ^ 2 := by linarith
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
  -- the weights
  set w : Zd d L → ℝ := fun x => kk x * (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2) with hw
  have hw0 : ∀ x, 0 ≤ w x := fun x => by simp only [hw]; have := hkk0 x; positivity
  have hkw : ∀ x, kk x ≤ w x := fun x => by
    simp only [hw]
    have : (1 : ℝ) ≤ (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2) :=
      one_le_pow₀ (by have : (0 : ℝ) ≤ ((zdistInf d L x : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)
    exact le_mul_of_one_le_right (hkk0 x) this
  have hSw : ∑ x : Zd d L, w x ≤ S := by
    have h1 : ∀ x : Zd d L, w x = (1 + Cs) * (if x = 0 then 1 else 0) +
        Cs * Λ ^ 2 * ((((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2) * Real.exp (-(c₀ * ((zdistD d L x : ℕ) : ℝ)))) := by
      intro x
      simp only [hw, hkk]
      by_cases hx : x = 0
      · subst hx; simp [zdistD_zero, iniTermII_zdistInf_zero]
      · simp [hx]; ring
    rw [Finset.sum_congr rfl fun x _ => h1 x, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_one]
    have := hpoly L
    rw [hS]
    have h2 : Cs * Λ ^ 2 * ∑ x : Zd d L, (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2) *
        Real.exp (-(c₀ * ((zdistD d L x : ℕ) : ℝ))) ≤ Cs * Λ ^ 2 * Cp :=
      mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  have hSk : ∑ x : Zd d L, kk x ≤ S := (Finset.sum_le_sum fun x _ => hkw x).trans hSw
  set T₀ : ℝ := tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) with hT₀
  have hT₀0 : 0 ≤ T₀ := tailT_nonneg (Nat.cast_nonneg _)
  -- termwise
  have hterm : ∀ b₁ b₂ : Zd d L, ‖((if a₁ = b₁ then (α : ℂ) else 0) + (β : ℂ) * Θ' a₁ b₁) *
        ((if a₂ = b₂ then (α : ℂ) else 0) + (β : ℂ) * Θ' a₂ b₂) * X b₁ b₂‖
      ≤ M * q * Real.exp 1 * T₀ * (w (b₁ - a₁) * w (b₂ - a₂)) + M * F * (kk (b₁ - a₁) * kk (b₂ - a₂)) := by
    intro b₁ b₂
    rw [norm_mul, norm_mul]
    have hX1 := hX b₁ b₂
    have hTs := iniTermII_Ts_le (d := d) (L := L) hg hL1 hsu hu hregu a₁ a₂ b₁ b₂
    set m : ℝ := ((zdistInf d L (b₁ - a₁) : ℕ) : ℝ) + ((zdistInf d L (b₂ - a₂) : ℕ) : ℝ) with hm
    have hpow : (m + 1) ^ (d - 2) ≤ (((zdistInf d L (b₁ - a₁) : ℕ) : ℝ) + 1) ^ (d - 2) *
        (((zdistInf d L (b₂ - a₂) : ℕ) : ℝ) + 1) ^ (d - 2) := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      have h1 : (0 : ℝ) ≤ ((zdistInf d L (b₁ - a₁) : ℕ) : ℝ) := Nat.cast_nonneg _
      have h2 : (0 : ℝ) ≤ ((zdistInf d L (b₂ - a₂) : ℕ) : ℝ) := Nat.cast_nonneg _
      simp only [hm]; nlinarith
    have hXb : ‖X b₁ b₂‖ ≤ M * (q * (Real.exp 1 * (((zdistInf d L (b₁ - a₁) : ℕ) : ℝ) + 1) ^ (d - 2) *
        (((zdistInf d L (b₂ - a₂) : ℕ) : ℝ) + 1) ^ (d - 2) * T₀) + F) := by
      refine hX1.trans (mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) hM)
      refine mul_le_mul_of_nonneg_left (hTs.trans ?_) hq
      calc Real.exp 1 * (m + 1) ^ (d - 2) * T₀
          ≤ Real.exp 1 * ((((zdistInf d L (b₁ - a₁) : ℕ) : ℝ) + 1) ^ (d - 2) *
              (((zdistInf d L (b₂ - a₂) : ℕ) : ℝ) + 1) ^ (d - 2)) * T₀ := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le) hT₀0
        _ = _ := by ring
    have hk1 := hG a₁ b₁
    have hk2 := hG a₂ b₂
    have hn1 : 0 ≤ ‖(if a₁ = b₁ then (α : ℂ) else 0) + (β : ℂ) * Θ' a₁ b₁‖ := norm_nonneg _
    have hn2 : 0 ≤ ‖(if a₂ = b₂ then (α : ℂ) else 0) + (β : ℂ) * Θ' a₂ b₂‖ := norm_nonneg _
    calc ‖(if a₁ = b₁ then (α : ℂ) else 0) + (β : ℂ) * Θ' a₁ b₁‖ *
          ‖(if a₂ = b₂ then (α : ℂ) else 0) + (β : ℂ) * Θ' a₂ b₂‖ * ‖X b₁ b₂‖
        ≤ (kk (b₁ - a₁) * kk (b₂ - a₂)) * (M * (q * (Real.exp 1 * (((zdistInf d L (b₁ - a₁) : ℕ) : ℝ) + 1) ^ (d - 2) *
            (((zdistInf d L (b₂ - a₂) : ℕ) : ℝ) + 1) ^ (d - 2) * T₀) + F)) :=
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
    _ ≤ ∑ b₁ : Zd d L, ∑ b₂ : Zd d L, (M * q * Real.exp 1 * T₀ * (w (b₁ - a₁) * w (b₂ - a₂))
          + M * F * (kk (b₁ - a₁) * kk (b₂ - a₂))) :=
        Finset.sum_le_sum fun b₁ _ => Finset.sum_le_sum fun b₂ _ => hterm b₁ b₂
    _ = M * q * Real.exp 1 * T₀ * (∑ x : Zd d L, w x) ^ 2 + M * F * (∑ x : Zd d L, kk x) ^ 2 := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        rw [iniTermII_sum_shift a₁ w, iniTermII_sum_shift a₂ w, iniTermII_sum_shift a₁ kk,
          iniTermII_sum_shift a₂ kk]
        ring
    _ ≤ M * q * Real.exp 1 * T₀ * S ^ 2 + M * F * S ^ 2 := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hSw0 hSw 2) (by positivity)
        · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hSk0 hSk 2) (by positivity)
    _ ≤ (Real.exp 1 * S ^ 2 + S ^ 2 + 1) * M * (q * T₀ + F) := by
        have h1 : 0 ≤ M * (q * T₀) * (S ^ 2 + 1) + M * F * (Real.exp 1 * S ^ 2 + 1) := by positivity
        have h2 : (Real.exp 1 * S ^ 2 + S ^ 2 + 1) * M * (q * T₀ + F)
            = M * q * Real.exp 1 * T₀ * S ^ 2 + M * F * S ^ 2
              + (M * (q * T₀) * (S ^ 2 + 1) + M * F * (Real.exp 1 * S ^ 2 + 1)) := by ring
        rw [h2]; exact le_add_of_nonneg_right h1

end CoreSame3

/-- **Target 2, `σ₁ = σ₂`: the short-range initial term** (`3_5:2253`, `(prop:ThfadC_short)`; no zero-mode removal).  With the
hypotheses of `iniTermII_core` (here the regime `1 - s ≤ g²/L²` enters only through `ℓ_u = L`, i.e. `e⁻¹ B_{u,r} ≤ 𝒯_u(r)`, in the
comparison `𝒯_s(|b₁-b₂|) ≤ e (m+1)^{d-2} 𝒯_u(|a₁-a₂|)`; no `ρ`-factor on the floor):
`|[𝒰_{s,u,σ} X]_a| ≤ C M ((λ W^{-d}) 𝒯_u(|a₁-a₂|) + W^{-D})`, `C = C(d, Λ, κ_m)`. -/
theorem iniTermII_core_same (d : ℕ) (Λ κm : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) (hκm : 0 < κm) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g W D E s u M lam : ℝ), 0 < g → g ≤ Λ → 0 < W →
        |E| ≤ 2 → κm ≤ (mE E).im → 0 ≤ s → s ≤ u → u < 1 → 1 - s ≤ g ^ 2 / (L : ℝ) ^ 2 → 0 ≤ M → 0 ≤ lam →
        ∀ σ : Fin 2 → Bool, σ 0 = σ 1 → ∀ X : (Fin 2 → Zd d L) → ℂ,
          (∀ b, ‖X b‖ ≤ M * (lam * (W ^ d)⁻¹ * tailT d L g s (zdistInf d L (b 0 - b 1) : ℕ) + W ^ (-D))) →
          ∀ a, ‖RBM.Ind.Ugen d L g E σ s u X a‖ ≤
            C * M * (lam * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) + W ^ (-D)) := by
  obtain ⟨Cs, hCs, c₀, hc₀, H5⟩ := prop5Short_holds d Λ κm hd hΛ hκm
  obtain ⟨C, hC, Hb⟩ := iniTermII_bil_same d hd Cs c₀ Λ hCs.le hc₀
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
    iniTermII_Ugen_rep (d := d) (L := L) (g := g) hL hE (μ := mSigma E (σ 0) * mSigma E (σ 0)) hμc hs hsu hu
  have hξ : ‖(u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 0))‖ < 1 := norm_mul_mSigma_lt_one hE hu0 hu _ _
  have hΘ : ∀ a' b' : Zd d L, ‖Theta d L g ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 0))) a' b'‖ ≤
      Cs * ((if a' = b' then 1 else 0) + g ^ 2 * Real.exp (-(c₀ * ((zdistD d L (b' - a') : ℕ) : ℝ)))) := by
    intro a' b'
    have h5 := H5 L hL g hg hgΛ u hu0 hu (mE E) (norm_mE hE) hκ (σ 0) (b' - a')
    have hps : PropSpin (mE E) (σ 0) = mSigma E (σ 0) := rfl
    rw [hps, ← iniTermII_Theta_shift hL hξ a' b'] at h5
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

/-! ### 10. Comparisons at the size index `n` -/

section Seq

variable {d : ℕ} (sz : Sizes d)

/-- `W^{-d} B_{s,0} ≤ 2 (ilambda² W^d)⁻¹` for `1 - s ≥ ilambda²/L^d`. -/
private theorem iniTermII_Bctl_le (n : ℕ) {s : ℝ} (hg : 0 < sz.lam n) (hs : s < 1)
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
    _ = 2 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
        rw [mul_inv]; ring

/-- `(W^{-d} B_{s,0})^{1/5} ≤ 2 A^{-1/5}`, `A = ilambda² W^d`. -/
private theorem iniTermII_lam_le (n : ℕ) {s : ℝ} (hg : 0 < sz.lam n) (hs : s < 1)
    (hlow : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - s) :
    (sz.Bctl n s) ^ (1 / 5 : ℝ) ≤ 2 * (STAI sz n) ^ (-(1 / 5 : ℝ)) := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hA : 0 < STAI sz n := by unfold STAI; positivity
  have hB := iniTermII_Bctl_le sz n hg hs hlow
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

/-- `(1-s)/(1-u) ≤ N` in regime (ii): `1-s ≤ ilambda²/L² ≤ ilambda² ≤ L^d (1-u)`. -/
private theorem iniTermII_rho_le (n : ℕ) {s u : ℝ} (hg : 0 < sz.lam n) (hu : u < 1)
    (hreg : 1 - s ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hlow : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - u) :
    (1 - s) / (1 - u) ≤ ((sz.size n : ℕ) : ℝ) := by
  have hW : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL3 : (3 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast sz.three_le_L n
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by linarith
  have hu0 : 0 < 1 - u := by
    have : 0 < sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d := by positivity
    linarith
  have hg2 : 0 < sz.lam n ^ 2 := by positivity
  have hLd : sz.lam n ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ d * (1 - u) := by
    rw [div_le_iff₀ (by positivity)] at hlow; linarith
  have h1 : 1 - s ≤ sz.lam n ^ 2 := by
    refine hreg.trans ?_
    exact div_le_self hg2.le (by nlinarith)
  have hNL : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
    have : (sz.L n) ^ d ≤ (sz.W n * sz.L n) ^ d :=
      Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
    unfold Sizes.size
    exact_mod_cast this
  rw [div_le_iff₀ hu0]
  calc 1 - s ≤ sz.lam n ^ 2 := h1
    _ ≤ ((sz.L n : ℕ) : ℝ) ^ d * (1 - u) := hLd
    _ ≤ ((sz.size n : ℕ) : ℝ) * (1 - u) := mul_le_mul_of_nonneg_right hNL hu0.le

/-- `N ≤ W^{1/𝔠}` from `W ≥ N^𝔠`. -/
private theorem iniTermII_N_le_W (n : ℕ) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hB : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ)) :
    ((sz.size n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) := by
  have hN : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  calc ((sz.size n : ℕ) : ℝ) = (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (1 / 𝔠) := by
        rw [← Real.rpow_mul hN, mul_one_div_cancel h𝔠.ne', Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hN _) hB (by positivity)

/-- The `STDecay` profile is `λ W^{-d} 𝒯_s + W^{-D}`. -/
private theorem iniTermII_prem_eq (n : ℕ) (τ D' : ℝ) (b : Fin 2 → Zd d (sz.L n)) :
    (sz.Bctl n τ) ^ (1 / 5 : ℝ) * STWB sz n τ (zdistInf d (sz.L n) (b 0 - b 1)) *
        Real.exp (-(((zdistInf d (sz.L n) (b 0 - b 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) τ) ^ (1 / 2 : ℝ)) +
      ((sz.W n : ℕ) : ℝ) ^ (-D')
    = (sz.Bctl n τ) ^ (1 / 5 : ℝ) * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
        tailT d (sz.L n) (sz.lam n) τ (zdistInf d (sz.L n) (b 0 - b 1) : ℕ) + ((sz.W n : ℕ) : ℝ) ^ (-D') := by
  unfold STWB tailT
  rw [← BparamR_natCast, Real.sqrt_eq_rpow]
  ring

/-- `STprof ≥ W^{-d} 𝒯_u`: `𝒯̃^L_{u,D}(r) = max(𝒯_u(r ∧ L), W^{-D}) ≥ 𝒯_u(r)` for `r ≤ L`. -/
private theorem iniTermII_prof_ge (n : ℕ) (u D : ℝ) (a : Fin 2 → Zd d (sz.L n)) :
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a 0 - a 1) : ℕ)
      ≤ STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) := by
  unfold STprof tailW
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [min_eq_left (iniTermII_zdistInf_le_L _)]
  exact le_max_left _ _

end Seq

section Lift

variable {d : ℕ} (sz : Sizes d)

/-- `StochDomAt.of_subset` with two different index types (the premise `(σ, b)`, the conclusion `(u, σ, a)`). -/
private theorem iniTermII_of_subset {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}
    {U V : ℕ → Type*} {ξ ζ : ∀ l, U l → Ω → ℝ} {ξ₁ ζ₁ : ∀ l, V l → Ω → ℝ}
    (h : StochDomAt P size ξ₁ ζ₁)
    (hsub : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop,
      badSetAt size ξ ζ τ l ⊆ badSetAt size ξ₁ ζ₁ τ' l) : StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := hsub τ hτ
  filter_upwards [hs, h τ' hτ' D hD] with l h1 h2
  exact (measure_mono h1).trans h2

private theorem iniTermII_arith {C K lam' a w T Tp ρ F WD : ℝ} (hC : 0 ≤ C) (hCK : 2 * C ≤ K)
    (hlam : lam' ≤ 2 * a) (ha : 0 ≤ a) (hw : 0 ≤ w) (hT : 0 ≤ T) (hTp : w * T ≤ Tp) (hρF : ρ * F ≤ WD)
    (hWD : 0 ≤ WD) :
    C * K * (lam' * w * T + ρ * F) ≤ K * K * (a * Tp + WD) := by
  have hK0 : 0 ≤ K := by linarith
  have hwT : 0 ≤ w * T := mul_nonneg hw hT
  have h1 : lam' * w * T ≤ 2 * a * (w * T) := by
    have := mul_le_mul_of_nonneg_right hlam hwT
    linarith
  have hCK' : C ≤ K := by linarith
  calc C * K * (lam' * w * T + ρ * F) ≤ C * K * (2 * a * (w * T) + WD) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 hρF) (mul_nonneg hC hK0)
    _ = (2 * C) * K * (a * (w * T)) + C * K * WD := by ring
    _ ≤ K * K * (a * (w * T)) + K * K * WD := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCK hK0) (mul_nonneg ha hwT)
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCK' hK0) hWD
    _ ≤ K * K * (a * Tp) + K * K * WD := by
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hTp ha) (mul_nonneg hK0 hK0)
        linarith
    _ = _ := by ring

/-- **The `Prec` lift** (target 3): the deterministic core, for `X = (𝓛-𝒦)^{(2)}_{s,σ}` bounded by the `STDecay` profile
`N^{τ/2} (λ W^{-d} 𝒯_s + W^{-D'})`, `D' = D + 1/𝔠`, gives `STIniTermConcl` (the union over `(σ, b)` of the premise contains the
union over `(u, σ, a)` of the conclusion; the constant `C ≤ N^{τ/2}` eventually, `ρ = (1-s)/(1-u) ≤ N ≤ W^{1/𝔠}`; `u` enters only
through the kernel). -/
private theorem iniTermII_lift {E s t : ℕ → ℝ} {Q : Finset (Fin 2)} {P : (Fin 2 → Bool) → Prop}
    {Λ 𝔠 C : ℝ} (hsz : sz.SizeTendsto) (h𝔠 : 0 < 𝔠) (hBand : sz.Bandwidth 𝔠) (hC : 0 < C)
    (hlamΛ : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λ)
    (ht1 : ∀ n, t n < 1) (hR : STReg5II sz s t)
    (hcore : ∀ n : ℕ, 0 < sz.lam n → sz.lam n ≤ Λ → ∀ u : ℝ, s n ≤ u → u ≤ t n → ∀ σ : Fin 2 → Bool, P σ →
        ∀ M D' : ℝ, 0 ≤ M → ∀ X : (Fin 2 → Zd d (sz.L n)) → ℂ,
          (∀ b, ‖X b‖ ≤ M * ((sz.Bctl n (s n)) ^ (1 / 5 : ℝ) * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
              tailT d (sz.L n) (sz.lam n) (s n) (zdistInf d (sz.L n) (b 0 - b 1) : ℕ) + ((sz.W n : ℕ) : ℝ) ^ (-D'))) →
          ∀ a, ‖zeroModeSet d (sz.L n) Q (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ (s n) u X) a‖ ≤
            C * M * ((sz.Bctl n (s n)) ^ (1 / 5 : ℝ) * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
              tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a 0 - a 1) : ℕ) +
              (1 - s n) / (1 - u) * ((sz.W n : ℕ) : ℝ) ^ (-D')))
    (hDec : STDecay sz E s) : STIniTermConcl sz Q P E s t := by
  intro D hD
  have hD' : 0 < D + 1 / 𝔠 := by positivity
  have hP := hDec (D + 1 / 𝔠) hD'
  unfold Sizes.Prec at hP ⊢
  refine iniTermII_of_subset hP ?_
  intro τ hτ
  refine ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [hlamΛ, (tendsto_size sz hsz).eventually (eventually_le_rpow (2 * C) (half_pos hτ)), hBand]
    with n hn hCn hBn
  intro ω hω
  obtain ⟨p, hp⟩ := hω
  by_contra hq
  have hq' : ∀ q : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)),
      ‖Lloop sz n (E n) (s n) q.1 q.2 ω - STKloop sz n (E n) (s n) q.1 q.2‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.Bctl n (s n)) ^ (1 / 5 : ℝ) *
          STWB sz n (s n) (zdistInf d (sz.L n) (q.2 0 - q.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (q.2 0 - q.2 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) (s n)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-(D + 1 / 𝔠))) := fun q => not_lt.mp fun h => hq ⟨q, h⟩
  obtain ⟨⟨u, hu1, hu2⟩, ⟨σ, hσ⟩, a⟩ := p
  obtain ⟨hlam0, hlamΛ'⟩ := hn
  have hu1' : u < 1 := lt_of_le_of_lt hu2 (ht1 n)
  have hs1 : s n < 1 := lt_of_le_of_lt hu1 hu1'
  obtain ⟨hlowt, hregs⟩ := hR n
  have hlows : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - s n := hlowt.trans (by linarith)
  have hlowu : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - u := hlowt.trans (by linarith)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hτ0 : 0 < τ := hτ
  set K : ℝ := ((sz.size n : ℕ) : ℝ) ^ (τ / 2) with hK
  have hK0 : 0 ≤ K := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hKK : K * K = ((sz.size n : ℕ) : ℝ) ^ τ := UnifDetDom.rpow_half_mul_rpow_half (sz.size n) hτ0
  have hXb : ∀ b : Fin 2 → Zd d (sz.L n), ‖sz.STLKM n (E n) (s n) (sz.seqHflow n (s n) ω) σ b‖ ≤
      K * ((sz.Bctl n (s n)) ^ (1 / 5 : ℝ) * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
        tailT d (sz.L n) (sz.lam n) (s n) (zdistInf d (sz.L n) (b 0 - b 1) : ℕ) +
        ((sz.W n : ℕ) : ℝ) ^ (-(D + 1 / 𝔠))) := fun b => by
    have h := hq' (σ, b)
    rw [iniTermII_prem_eq sz n (s n) (D + 1 / 𝔠) b] at h
    exact h
  have hcb := hcore n hlam0 hlamΛ' u hu1 hu2 σ hσ K (D + 1 / 𝔠) hK0
    (fun b => sz.STLKM n (E n) (s n) (sz.seqHflow n (s n) ω) σ b) hXb a
  -- `ρ W^{-D'} ≤ W^{-D}`
  have hρN := iniTermII_rho_le sz n hlam0 hu1' hregs hlowu
  have hNW := iniTermII_N_le_W sz n h𝔠 hBn
  have hρF : (1 - s n) / (1 - u) * ((sz.W n : ℕ) : ℝ) ^ (-(D + 1 / 𝔠)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := by
    calc (1 - s n) / (1 - u) * ((sz.W n : ℕ) : ℝ) ^ (-(D + 1 / 𝔠))
        ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) * ((sz.W n : ℕ) : ℝ) ^ (-(D + 1 / 𝔠)) :=
          mul_le_mul_of_nonneg_right (hρN.trans hNW) (Real.rpow_nonneg hW.le _)
      _ = ((sz.W n : ℕ) : ℝ) ^ (-D) := by
          rw [← Real.rpow_add hW]; congr 1; ring
  have hfin := iniTermII_arith (C := C) (K := K) (lam' := (sz.Bctl n (s n)) ^ (1 / 5 : ℝ))
    (a := (STAI sz n) ^ (-(1 / 5 : ℝ))) (w := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹)
    (T := tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a 0 - a 1) : ℕ))
    (Tp := sz.STprof n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1))
    (ρ := (1 - s n) / (1 - u)) (F := ((sz.W n : ℕ) : ℝ) ^ (-(D + 1 / 𝔠))) (WD := ((sz.W n : ℕ) : ℝ) ^ (-D))
    hC.le hCn (iniTermII_lam_le sz n hlam0 hs1 hlows) (Real.rpow_nonneg (st5_STAI_nonneg sz n) _)
    (by positivity) (tailT_nonneg (Nat.cast_nonneg _)) (iniTermII_prof_ge sz n u D a) hρF
    (Real.rpow_nonneg hW.le _)
  have hp' : ((sz.size n : ℕ) : ℝ) ^ τ * ((STAI sz n) ^ (-(1 / 5 : ℝ)) *
      sz.STprof n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) + ((sz.W n : ℕ) : ℝ) ^ (-D)) <
      ‖zeroModeSet d (sz.L n) Q (Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ (s n) u
        fun b => sz.STLKM n (E n) (s n) (sz.seqHflow n (s n) ω) σ b) a‖ := hp
  rw [← hKK] at hp'
  exact absurd (hcb.trans hfin) (not_le.mpr hp')

end Lift

/-! ### 11. The pin `STIniTermII` -/

section Pin

/-- `|E| ≤ 2 - κ` gives `Im m(E) ≥ κ_m := √(κ(4-κ))/2`. -/
private theorem iniTermII_im_ge {κ E : ℝ} (hE : |E| ≤ 2 - κ) :
    Real.sqrt (κ * (4 - κ)) / 2 ≤ (mE E).im := by
  rw [mE_im]
  have h2 : 0 ≤ 2 - κ := (abs_nonneg E).trans hE
  have hE2 : E ^ 2 ≤ (2 - κ) ^ 2 := by
    have := abs_le.mp hE
    nlinarith
  refine div_le_div_of_nonneg_right (Real.sqrt_le_sqrt ?_) (by norm_num)
  nlinarith

/-- **Target 3** (the `Prec` lift of the initial term of case (ii)): from `STDecay` at `s` (`(Eq:Gdecay+IND)`), the standing
setting `STFlow` and the regime `ilambda²/L^d ≤ 1-t ≤ 1-s ≤ ilambda²/L²` (`STReg5II`), the initial term of `(zYU2)` obeys
`≺ A^{-1/5} W^{-d}𝒯̃^L_{u,D}(|a₁-a₂|) + W^{-D}`, uniformly in `u ∈ [s,t]` (`u` enters only through the kernel `𝒰_{s,u}`:
the premise at `s` is `u`-free), for `σ₁ ≠ σ₂` with `Q^{(1)}` and for `σ₁ = σ₂` without. -/
theorem iniTermII_concl {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (ht : ∀ n, t n ≤ lemT (z n))
    (hR : STReg5II sz s t) (hDec : STDecay sz (STflowE z) s) :
    STIniTermConcl sz {0} STSigMixed (STflowE z) s t ∧ STIniTermConcl sz ∅ STSigSame (STflowE z) s t := by
  obtain ⟨⟨h𝔠, h𝔡, hsz, hBand, hWO⟩, hloc⟩ := hflow
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz ⟨⟨h𝔠, h𝔡, hsz, hBand, hWO⟩, hloc⟩ ht
  have hE : ∀ n, |STflowE z n| ≤ 2 - κ := fun n => by
    have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    have him : 0 < (z n).im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN _) (hloc n).2.1
    exact (abs_lemE_le him).trans (hloc n).1
  have hκ2 : κ ≤ 2 := by
    have := (abs_nonneg _).trans (hE 0)
    linarith
  have hκm : 0 < Real.sqrt (κ * (4 - κ)) / 2 := by
    have : 0 < κ * (4 - κ) := mul_pos hκ (by linarith)
    positivity
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.mpr h𝔡
  have hlamΛ : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hWO, st5_eventually_A_ge_one sz h𝔡 hWO] with n h1 h2
    exact ⟨h2.1, h1.2⟩
  obtain ⟨Cm, hCm, Hm⟩ := iniTermII_core d 𝔡⁻¹ (Real.sqrt (κ * (4 - κ)) / 2) hd hΛ hκm
  obtain ⟨Cs, hCs, Hs⟩ := iniTermII_core_same d 𝔡⁻¹ (Real.sqrt (κ * (4 - κ)) / 2) hd hΛ hκm
  refine ⟨?_, ?_⟩
  · refine iniTermII_lift sz hsz h𝔠 hBand hCm hlamΛ ht1 hR ?_ hDec
    intro n hg hgΛ u hu1 hu2 σ hσ M D' hM X hX a
    have hu1' : u < 1 := lt_of_le_of_lt hu2 (ht1 n)
    have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    exact Hm (sz.L n) (sz.three_le_L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) D' (STflowE z n) (s n) u M
      ((sz.Bctl n (s n)) ^ (1 / 5 : ℝ)) hg hgΛ hW ((hE n).trans (by linarith))
      (iniTermII_im_ge (hE n)) (hs0 n) hu1 hu1' (hR n).2 hM
      (Real.rpow_nonneg (st_Bctl_pos sz (lt_of_le_of_lt hu1 hu1')).le _) σ hσ X hX a
  · refine iniTermII_lift sz hsz h𝔠 hBand hCs hlamΛ ht1 hR ?_ hDec
    intro n hg hgΛ u hu1 hu2 σ hσ M D' hM X hX a
    have hu1' : u < 1 := lt_of_le_of_lt hu2 (ht1 n)
    have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have h := Hs (sz.L n) (sz.three_le_L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) D' (STflowE z n) (s n) u M
      ((sz.Bctl n (s n)) ^ (1 / 5 : ℝ)) hg hgΛ hW ((hE n).trans (by linarith))
      (iniTermII_im_ge (hE n)) (hs0 n) hu1 hu1' (hR n).2 hM
      (Real.rpow_nonneg (st_Bctl_pos sz (lt_of_le_of_lt hu1 hu1')).le _) σ hσ X hX a
    rw [st5_zeroModeSet_empty]
    refine h.trans ?_
    have hu0 : 0 < 1 - u := by linarith
    have hρ : 1 ≤ (1 - s n) / (1 - u) := (one_le_div hu0).mpr (by linarith)
    have hF : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') := Real.rpow_nonneg hW.le _
    have hA : 0 ≤ (sz.Bctl n (s n)) ^ (1 / 5 : ℝ) * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
        tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a 0 - a 1) : ℕ) :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg (st_Bctl_pos sz (lt_of_le_of_lt hu1 hu1')).le _)
        (by positivity)) (tailT_nonneg (Nat.cast_nonneg _))
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (mul_nonneg hCs.le hM)
    exact le_mul_of_one_le_left hF hρ

/-- **Target 1**: the pin `STIniTermII` of the initial term of Step 5, case (ii) `ilambda²/L^d ≤ 1-t ≤ 1-s ≤ ilambda²/L²`
(`3_5:2268-2281`), exactly as merged (`Induction/Step5Pins.lean`): both conjuncts, `σ₁ ≠ σ₂` with `Q^{(1)} = zeroModeSet {0}` and
`σ₁ = σ₂` without `Q`. -/
theorem stIniTermII_holds (d : ℕ) : STIniTermII d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, by norm_num, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst ht hR _ _ _ hDec _ _ _ _ _ _
  exact iniTermII_concl hd sz hκ hflow hs0 ht hR hDec

end Pin

end RBM.Gauss.Sizes

/-! ## 12. Compiled nonempty instances (`d = 3`)

* `iniTermII_core_inst`, `iniTermII_core_same_inst`: target 2 at `L = 4`, `g = 1` (`ilambda²/L² = 1/16 = 1-s`, the boundary of
  regime (ii); the ticket's `L = 3`, `g = 1/2` violates `1 - s ≤ g²/L²`: `1/16 > 1/36`, paper-delta candidate `T2163c`), `W = 2`,
  `D = 2`, `E = 1` (`|E| ≤ 2`, `Im m(E) = √3/2 ≥ κ_m = 1/2`), `s = 15/16`, `u = 31/32`, `Λ = 1`, `M = λ = 1`, and the nonzero
  tensor `X_b = λ W^{-d} 𝒯_s(|b₁-b₂|) + W^{-D}` (the `STDecay` profile at `s` attained), at every `a ∈ (Z_4^3)²`;
* `iniTermII_concl_inst`: target 3 at `(szB, zB, 15/16, 31/32)` (the merged data of `inst_iniTermII`); the stochastic premise `STDecay`
  at `s` stays a hypothesis (another gate's pin);
* `inst_iniTermII_proved`: `inst_iniTermII (stIniTermII_holds 3)` (`Step5Pins.lean:980`) with the pin proved. -/

namespace RBM.Gauss.Step5Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.Step34Inst Filter

private theorem iniTermII_inst_im : (1 / 2 : ℝ) ≤ (mE 1).im := by
  rw [mE_im]
  have h : (1 : ℝ) ≤ Real.sqrt 3 := Real.one_le_sqrt.mpr (by norm_num)
  have h3 : (4 : ℝ) - 1 ^ 2 = 3 := by norm_num
  rw [h3]
  linarith

/-- **Target 2 (`σ₁ ≠ σ₂`), instantiated**: `d = 3`, `L = 4`, `g = 1`, `W = 2`, `D = 2`, `E = 1`, `s = 15/16`, `u = 31/32`,
`σ = (+,-)`, the nonzero tensor `X_b = W^{-d} 𝒯_s(|b₁-b₂|) + W^{-D}`. -/
theorem iniTermII_core_inst : ∃ C : ℝ, 0 < C ∧ ∀ a : Fin 2 → Zd 3 4,
    ‖zeroModeSet 3 4 {0} (RBM.Ind.Ugen 3 4 1 1 ![true, false] (15 / 16) (31 / 32)
      (fun b => (((1 : ℝ) * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 4 1 (15 / 16) (zdistInf 3 4 (b 0 - b 1) : ℕ)
        + (2 : ℝ) ^ (-(2 : ℝ)) : ℝ) : ℂ))) a‖ ≤
      C * 1 * (1 * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 4 1 (31 / 32) (zdistInf 3 4 (a 0 - a 1) : ℕ) +
        (1 - 15 / 16) / (1 - 31 / 32) * (2 : ℝ) ^ (-(2 : ℝ))) := by
  obtain ⟨C, hC, H⟩ := iniTermII_core 3 1 (1 / 2) (by norm_num) one_pos (by norm_num)
  refine ⟨C, hC, fun a => ?_⟩
  refine H 4 (by norm_num) 1 2 2 1 (15 / 16) (31 / 32) 1 1 one_pos le_rfl two_pos (by norm_num)
    iniTermII_inst_im (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ![true, false] (by simp) _ ?_ a
  intro b
  have h0 : 0 ≤ (1 : ℝ) * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 4 1 (15 / 16) (zdistInf 3 4 (b 0 - b 1) : ℕ)
      + (2 : ℝ) ^ (-(2 : ℝ)) := by
    have := tailT_nonneg (d := 3) (L := 4) (g := 1) (t := 15 / 16) (Nat.cast_nonneg (zdistInf 3 4 (b 0 - b 1)))
    positivity
  rw [Complex.norm_real, Real.norm_of_nonneg h0]
  exact le_of_eq (by ring)

/-- **Target 2 (`σ₁ = σ₂`), instantiated** at the same data with `σ = (+,+)`. -/
theorem iniTermII_core_same_inst : ∃ C : ℝ, 0 < C ∧ ∀ a : Fin 2 → Zd 3 4,
    ‖RBM.Ind.Ugen 3 4 1 1 ![true, true] (15 / 16) (31 / 32)
      (fun b => (((1 : ℝ) * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 4 1 (15 / 16) (zdistInf 3 4 (b 0 - b 1) : ℕ)
        + (2 : ℝ) ^ (-(2 : ℝ)) : ℝ) : ℂ)) a‖ ≤
      C * 1 * (1 * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 4 1 (31 / 32) (zdistInf 3 4 (a 0 - a 1) : ℕ) +
        (2 : ℝ) ^ (-(2 : ℝ))) := by
  obtain ⟨C, hC, H⟩ := iniTermII_core_same 3 1 (1 / 2) (by norm_num) one_pos (by norm_num)
  refine ⟨C, hC, fun a => ?_⟩
  refine H 4 (by norm_num) 1 2 2 1 (15 / 16) (31 / 32) 1 1 one_pos le_rfl two_pos (by norm_num)
    iniTermII_inst_im (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ![true, true] (by simp) _ ?_ a
  intro b
  have h0 : 0 ≤ (1 : ℝ) * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 4 1 (15 / 16) (zdistInf 3 4 (b 0 - b 1) : ℕ)
      + (2 : ℝ) ^ (-(2 : ℝ)) := by
    have := tailT_nonneg (d := 3) (L := 4) (g := 1) (t := 15 / 16) (Nat.cast_nonneg (zdistInf 3 4 (b 0 - b 1)))
    positivity
  rw [Complex.norm_real, Real.norm_of_nonneg h0]
  exact le_of_eq (by ring)

/-- **Target 3, instantiated** at `(szB, zB, 15/16, 31/32)` (`L = 4`, `W_n = n + 4`, `ilambda = 1`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`;
`1/64 ≤ 1-t = 1/32 ≤ 1-s = 1/16 ≤ 1/16`); the premise `STDecay` at `s` is another gate's pin. -/
theorem iniTermII_concl_inst (hDec : STDecay szB (STflowE zB) (fun _ => 15 / 16)) :
    STIniTermConcl szB {0} STSigMixed (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) ∧
      STIniTermConcl szB ∅ STSigSame (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  iniTermII_concl (d := 3) (by norm_num) szB (κ := 1 / 10) (ε := 1 / 10) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (by norm_num)
    flow_zB (fun _ => by norm_num) (szB_flow_ht (by norm_num)) szB_reg5II hDec

/-- **Target 1, instantiated**: the instance `inst_iniTermII` of `Step5Pins.lean:980` with the pin proved. -/
theorem inst_iniTermII_proved (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STIniTermConcl sz {0} STSigMixed E s t ∧ STIniTermConcl sz ∅ STSigSame E s t)
      szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) Cd :=
  inst_iniTermII (stIniTermII_holds 3) Cd hCd

end RBM.Gauss.Step5Inst
