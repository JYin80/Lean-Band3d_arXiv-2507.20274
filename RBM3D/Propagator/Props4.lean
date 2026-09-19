/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Propagator.Basic

/-!
# Property 4 of `lem_propTH`: the `(∞→∞)`-norm bound

For the random band matrix model `M^(σ₁,σ₂) = m(σ₁)m(σ₂) I` with `|m(σ)| = 1`, so
`Θ_t^(σ₁,σ₂) = Theta d L g (t · m)` with `‖m‖ = 1`, and `Θ_t^(+,-) = Theta d L g t`
(`m(+)m(-) = |m|² = 1`).  Property 4 of `lem_propTH` reads

  `|Θ_{t,ab}^(σ₁,σ₂)| ≤ Θ_{t,ab}^(+,-)`,
  `‖Θ_t^(σ₁,σ₂)‖_{∞→∞} ≤ max_a Σ_b Θ_{t,ab}^(+,-) = (1-t)⁻¹`   `(eq:THETAinftinf)`.

Appendix A.1 proves it by comparing the Taylor series `(eq;Taylor)` term by term.  Here:
`S^(B)(g)` is the complexification of the non-negative real matrix `RBM.SBR`, so the
`k`-th term of `Θ_ξ = Σ_k ξ^k (S^(B))^k` has `(a,b)` entry `ξ^k (SBR^k)_{ab}` with
`(SBR^k)_{ab} ≥ 0`; taking norms termwise gives the first inequality, and the row sums
`Σ_b Θ_{t,ab} = (1-t)⁻¹` (`RBM.sum_Theta_row`) give the second.

The file also restates the structural results of `Propagator/Basic.lean` without the
hypotheses `hS : ‖S^(B)‖ = 1` and `hone : S^(B) 1 = 1`, which `RBM.norm_SB` and
`RBM.SB_mulVec_one` now discharge from `3 ≤ L`.

## Main results

* `RBM.norm_Theta_apply_le` : `|Θ_{t,ab}^(σ₁,σ₂)| ≤ Θ_{t,ab}^(+,-)`
* `RBM.Theta_real_eq`, `RBM.Theta_real_nonneg` : `Θ_t^(+,-)` is real and non-negative
* `RBM.sum_Theta_real_row` : `Σ_b Θ_{t,ab}^(+,-) = (1-t)⁻¹`
* `RBM.norm_Theta_le` : `‖Θ_t^(σ₁,σ₂)‖_{∞→∞} ≤ (1-t)⁻¹`, i.e. `(eq:THETAinftinf)`
-/

namespace RBM

open Matrix
open scoped NNReal Matrix.Norms.Operator

variable (d L : ℕ) [NeZero L] (g : ℝ)

/-! ### `S^(B)` as a non-negative real matrix -/

section Real

/-- `S^(B)(g)` as a real matrix. -/
noncomputable def SBR : Matrix (Zd d L) (Zd d L) ℝ :=
  Matrix.of fun a b => sbKernelR d L g (a - b)

omit [NeZero L] in
theorem SB_eq_map_SBR : SB d L g = (SBR d L g).map (↑) := by
  ext a b
  simp [SB_apply, SBR, sbKernel_eq_ofReal]

theorem SB_pow_eq_map (k : ℕ) : SB d L g ^ k = (SBR d L g ^ k).map (↑) := by
  have h := map_pow (Complex.ofRealHom.mapMatrix (m := Zd d L)) (SBR d L g) k
  simp only [RingHom.mapMatrix_apply] at h
  rw [SB_eq_map_SBR]
  exact h.symm

theorem SBR_pow_nonneg (k : ℕ) (a b : Zd d L) : 0 ≤ (SBR d L g ^ k) a b := by
  induction k generalizing b with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun c _ =>
      mul_nonneg (ih c) (by simpa [SBR] using sbKernelR_nonneg d L g (c - b))

theorem smul_SB_pow_apply (ξ : ℂ) (k : ℕ) (a b : Zd d L) :
    ((ξ • SB d L g) ^ k) a b = ξ ^ k * ((SBR d L g ^ k) a b : ℂ) := by
  rw [smul_pow, SB_pow_eq_map]
  simp [Matrix.smul_apply]

end Real


/-! ### Properties 1–3 and the row sums, without `hS` / `hone` -/

section Unconditional

variable {d L g}

theorem Theta_mul_of_three_le (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    Theta d L g ξ * (1 - ξ • SB d L g) = 1 :=
  Theta_mul d L g (norm_SB d L g hL) hξ

theorem mul_Theta_of_three_le (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    (1 - ξ • SB d L g) * Theta d L g ξ = 1 :=
  mul_Theta d L g (norm_SB d L g hL) hξ

/-- Property 1 of `lem_propTH`. -/
theorem Theta_transpose_of_three_le (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    (Theta d L g ξ)ᵀ = Theta d L g ξ :=
  Theta_transpose d L g (norm_SB d L g hL) hξ

/-- Property 2 of `lem_propTH`. -/
theorem Theta_apply_add_right_of_three_le (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    (a b c : Zd d L) : Theta d L g ξ (a + c) (b + c) = Theta d L g ξ a b :=
  Theta_apply_add_right d L g (norm_SB d L g hL) hξ a b c

/-- Property 3 of `lem_propTH`, first half. -/
theorem Theta_commute_SB_of_three_le (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    Commute (Theta d L g ξ) (SB d L g) :=
  Theta_commute_SB d L g (norm_SB d L g hL) hξ

/-- Property 3 of `lem_propTH`, second half. -/
theorem Theta_commute_of_three_le (hL : 3 ≤ L) {ξ ξ' : ℂ} (hξ : ‖ξ‖ < 1) (hξ' : ‖ξ'‖ < 1) :
    Commute (Theta d L g ξ) (Theta d L g ξ') :=
  Theta_commute d L g (norm_SB d L g hL) hξ hξ'

theorem sum_Theta_row_of_three_le (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a : Zd d L) :
    ∑ b : Zd d L, Theta d L g ξ a b = (1 - ξ)⁻¹ :=
  sum_Theta_row d L g (norm_SB d L g hL) (SB_mulVec_one d L g hL) hξ a

theorem Theta_eq_tsum_of_three_le (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    Theta d L g ξ = ∑' k : ℕ, (ξ • SB d L g) ^ k :=
  Theta_eq_tsum d L g (norm_SB d L g hL) hξ

end Unconditional


/-! ### The Taylor series entrywise -/

section Entry

variable {d L g}

theorem summable_smul_SB_pow (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    Summable fun k : ℕ => (ξ • SB d L g) ^ k :=
  summable_geometric_of_norm_lt_one (norm_smul_SB_lt_one d L g (norm_SB d L g hL) hξ)

theorem summable_Theta_entry (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a b : Zd d L) :
    Summable fun k : ℕ => ξ ^ k * ((SBR d L g ^ k) a b : ℂ) := by
  have hs := summable_smul_SB_pow (d := d) (g := g) hL hξ
  have := Pi.summable.mp (Pi.summable.mp hs a) b
  simpa only [smul_SB_pow_apply] using this

/-- `(eq;Taylor)` entrywise: `Θ_ξ(a,b) = Σ_k ξ^k (S^(B)^k)_{ab}`. -/
theorem Theta_apply_eq_tsum (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a b : Zd d L) :
    Theta d L g ξ a b = ∑' k : ℕ, ξ ^ k * ((SBR d L g ^ k) a b : ℂ) := by
  have hs := summable_smul_SB_pow (d := d) (g := g) hL hξ
  have h := Pi.hasSum.mp (Pi.hasSum.mp hs.hasSum a) b
  simp only [smul_SB_pow_apply] at h
  rw [Theta_eq_tsum_of_three_le hL hξ]
  exact h.tsum_eq.symm

theorem summable_Theta_real_entry (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (a b : Zd d L) : Summable fun k : ℕ => t ^ k * (SBR d L g ^ k) a b := by
  have hξ : ‖(t : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_of_nonneg ht0]
  have := summable_Theta_entry (d := d) (g := g) hL hξ a b
  rw [← Complex.summable_ofReal]
  simpa using this

end Entry

/-! ### Property 4 -/

section Property4

variable {d L g}

/-- `Θ_t^(+,-)` is real: `Θ_t(a,b) = Σ_k t^k (S^(B)^k)_{ab}` with real terms. -/
theorem Theta_real_eq_tsum (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (a b : Zd d L) :
    Theta d L g t a b = ((∑' k : ℕ, t ^ k * (SBR d L g ^ k) a b : ℝ) : ℂ) := by
  have hξ : ‖(t : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_of_nonneg ht0]
  rw [Theta_apply_eq_tsum hL hξ, Complex.ofReal_tsum]
  push_cast
  rfl

theorem Theta_real_eq (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (a b : Zd d L) :
    Theta d L g t a b = ((Theta d L g t a b).re : ℂ) := by
  rw [Theta_real_eq_tsum hL ht0 ht1, Complex.ofReal_re]

theorem Theta_real_nonneg (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (a b : Zd d L) :
    0 ≤ (Theta d L g t a b).re := by
  rw [Theta_real_eq_tsum hL ht0 ht1, Complex.ofReal_re]
  exact tsum_nonneg fun k => mul_nonneg (pow_nonneg ht0 k) (SBR_pow_nonneg d L g k a b)

theorem norm_t_mul_lt_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {m : ℂ} (hm : ‖m‖ = 1) :
    ‖(t : ℂ) * m‖ < 1 := by
  rwa [norm_mul, hm, mul_one, Complex.norm_real, Real.norm_of_nonneg ht0]

/-- **Property 4 of `lem_propTH`, first half**: `|Θ_{t,ab}^(σ₁,σ₂)| ≤ Θ_{t,ab}^(+,-)`,
with `Θ_t^(σ₁,σ₂) = Theta d L g (t m)`, `‖m‖ = 1`. -/
theorem norm_Theta_apply_le (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {m : ℂ} (hm : ‖m‖ = 1) (a b : Zd d L) :
    ‖Theta d L g ((t : ℂ) * m) a b‖ ≤ (Theta d L g t a b).re := by
  have hterm : (fun k : ℕ => ‖((t : ℂ) * m) ^ k * ((SBR d L g ^ k) a b : ℂ)‖) =
      fun k => t ^ k * (SBR d L g ^ k) a b := by
    funext k
    rw [norm_mul, norm_pow, norm_mul, hm, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg ht0, Real.norm_of_nonneg (SBR_pow_nonneg d L g k a b)]
  rw [Theta_apply_eq_tsum hL (norm_t_mul_lt_one ht0 ht1 hm), Theta_real_eq_tsum hL ht0 ht1,
    Complex.ofReal_re, ← hterm]
  refine norm_tsum_le_tsum_norm ?_
  rw [hterm]
  exact summable_Theta_real_entry hL ht0 ht1 a b

/-- `Σ_b Θ_{t,ab}^(+,-) = (1-t)⁻¹`: the rows of `Θ_t^(+,-)` sum to `(1-t)⁻¹`. -/
theorem sum_Theta_real_row (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Zd d L) :
    ∑ b, (Theta d L g t a b).re = (1 - t)⁻¹ := by
  have hξ : ‖(t : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_of_nonneg ht0]
  rw [← Complex.re_sum, sum_Theta_row_of_three_le hL hξ a]
  have : (1 - (t : ℂ))⁻¹ = (((1 - t)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.ofReal_re]

theorem sum_norm_Theta_row_le (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {m : ℂ} (hm : ‖m‖ = 1) (a : Zd d L) :
    ∑ b, ‖Theta d L g ((t : ℂ) * m) a b‖ ≤ (1 - t)⁻¹ := by
  rw [← sum_Theta_real_row (g := g) hL ht0 ht1 a]
  exact Finset.sum_le_sum fun b _ => norm_Theta_apply_le hL ht0 ht1 hm a b

/-- **Property 4 of `lem_propTH`, `(eq:THETAinftinf)`**:
`‖Θ_t^(σ₁,σ₂)‖_{∞→∞} ≤ max_a Σ_b Θ_{t,ab}^(+,-) = (1-t)⁻¹`. -/
theorem norm_Theta_le (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {m : ℂ} (hm : ‖m‖ = 1) :
    ‖Theta d L g ((t : ℂ) * m)‖ ≤ (1 - t)⁻¹ := by
  have hpos : 0 ≤ (1 - t)⁻¹ := inv_nonneg.mpr (by linarith)
  have hsup : (Finset.univ.sup fun a => ∑ b, ‖Theta d L g ((t : ℂ) * m) a b‖₊)
      ≤ (⟨(1 - t)⁻¹, hpos⟩ : ℝ≥0) := by
    refine Finset.sup_le fun a _ => ?_
    have := sum_norm_Theta_row_le (g := g) hL ht0 ht1 hm a
    have h2 : ((∑ b, ‖Theta d L g ((t : ℂ) * m) a b‖₊ : ℝ≥0) : ℝ) ≤ (1 - t)⁻¹ := by
      simpa [NNReal.coe_sum] using this
    exact NNReal.coe_le_coe.mp h2
  rw [Matrix.linfty_opNorm_def]
  exact le_of_le_of_eq (NNReal.coe_le_coe.mpr hsup) rfl

end Property4

end RBM
