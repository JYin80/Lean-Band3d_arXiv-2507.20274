/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.KSymbol
import RBM3D.Propagator.HeatProduct
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# The Poisson semigroup and the heat kernel of `K = |M^{(B)}|²` (BA-P4a)

Ticket T2331 (BA stage P, row P4a; supervisor 2026-10-08-1048 C1, C2).
`P_s = e^{-s} Σ_n sⁿ/n! Kⁿ` (`BAP`) and the heat kernel in diffusive time
`kBA τ = P_{τ/g²}(0, ·)`.  Targets: the Laplace identity
`Θ^{(+,-)}_t(0,a) = ∫₀^∞ e^{-(1-t)u} kBA(t g² u, a) du`, the semigroup and translation invariance,
the basic properties, the Fourier form on the torus, the torus on-diagonal bound and regime (ii)
`τ ≥ L²` (twin of `Heat.kProd_gap`, `HeatProduct.lean:626`).

Private lemmas of this project that are re-proved here (the originals are `private`): the
orthogonality of the exponentials (`hp_sum_exp_orth`, `HeatProduct.lean:858`), `sum_geom_zdist`
(`HeatTorus1D.lean:354`), `mul_exp_neg_le_one` (`HeatTorus1D.lean:299`) and `KSymbol_cos_zdist`
(`KSymbol.lean:610`).  Nothing is ported from `../RBM1D` or `../RBM2D`.  The semigroup law uses
`Matrix.exp_add_of_commute` (extra import `Mathlib.Analysis.Normed.Algebra.MatrixExponential`); the
1D torus inputs are the merged `Heat.hkT_le`, `Heat.hkT_gap`, `Heat.hkT_mass`.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSectionVars false

noncomputable section

open Matrix

namespace RBM.BA

open RBM RBM.Gauss MeasureTheory Set

/-! ## 1. The definitions -/

section Defs

variable (d L : ℕ) [NeZero L]

/-- The Poisson semigroup of `K` (supervisor 1048 C2): `P_s = e^{-s} Σ_n sⁿ/n! Kⁿ`, entrywise. -/
def BAP (g E : ℝ) (m : ℂ) (s : ℝ) (a b : Zd d L) : ℝ :=
  Real.exp (-s) * ∑' n : ℕ, s ^ n / (n.factorial : ℝ) * (BAK d L g E m ^ n) a b

/-- The heat kernel of `K` in diffusive time `τ = g² s`: `kBA τ a = P_{τ/g²}(0, a)`. -/
def kBA (g E : ℝ) (m : ℂ) (τ : ℝ) (a : Zd d L) : ℝ :=
  BAP d L g E m (τ / g ^ 2) 0 a

end Defs

/-! ## 2. The power series: summability, sign, mass, translation invariance -/

section Series

variable (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ)

private theorem KHeat_tsum_exp (x : ℝ) :
    ∑' n : ℕ, x ^ n / (n.factorial : ℝ) = Real.exp x := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) x
  rw [Real.exp_eq_exp_ℝ]
  exact h.tsum_eq

private theorem KHeat_pow_le_one (h : BASelf d L g (E : ℂ) m) (n : ℕ) (a b : Zd d L) :
    (BAK d L g E m ^ n) a b ≤ 1 := by
  calc (BAK d L g E m ^ n) a b ≤ ∑ c, (BAK d L g E m ^ n) a c :=
        Finset.single_le_sum (f := fun c => (BAK d L g E m ^ n) a c)
          (fun c _ => BAK_pow_nonneg d L g E m n a c) (Finset.mem_univ b)
    _ = 1 := BAK_pow_row_sum d L g E m h n a

private theorem KHeat_summable (h : BASelf d L g (E : ℂ) m) (s : ℝ) (a b : Zd d L) :
    Summable (fun n : ℕ => s ^ n / (n.factorial : ℝ) * (BAK d L g E m ^ n) a b) := by
  refine Summable.of_norm_bounded (Real.summable_pow_div_factorial |s|) (fun n => ?_)
  have h0 := BAK_pow_nonneg d L g E m n a b
  have h1 := KHeat_pow_le_one d L g E m h n a b
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast]
  calc |s| ^ n / (n.factorial : ℝ) * |(BAK d L g E m ^ n) a b|
      ≤ |s| ^ n / (n.factorial : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (by rw [abs_of_nonneg h0]; exact h1) (by positivity)
    _ = _ := mul_one _

/-- `P_s ≥ 0` for `s ≥ 0`. -/
theorem BAP_nonneg {s : ℝ} (hs : 0 ≤ s) (a b : Zd d L) : 0 ≤ BAP d L g E m s a b := by
  unfold BAP
  refine mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun n => ?_)
  have := BAK_pow_nonneg d L g E m n a b
  positivity

/-- `P_s` is stochastic: `Σ_b P_s(a,b) = 1` for `s ≥ 0`. -/
theorem BAP_row_sum (h : BASelf d L g (E : ℂ) m) {s : ℝ} (hs : 0 ≤ s) (a : Zd d L) :
    ∑ b, BAP d L g E m s a b = 1 := by
  unfold BAP
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum (fun b _ => KHeat_summable d L g E m h s a b)]
  have h1 : ∀ n : ℕ, ∑ b, s ^ n / (n.factorial : ℝ) * (BAK d L g E m ^ n) a b
      = s ^ n / (n.factorial : ℝ) := by
    intro n
    rw [← Finset.mul_sum, BAK_pow_row_sum d L g E m h n a, mul_one]
  simp_rw [h1]
  rw [KHeat_tsum_exp, ← Real.exp_add]
  simp

/-- `P_s ≤ 1` for `s ≥ 0`. -/
theorem BAP_le_one (h : BASelf d L g (E : ℂ) m) {s : ℝ} (hs : 0 ≤ s) (a b : Zd d L) :
    BAP d L g E m s a b ≤ 1 := by
  calc BAP d L g E m s a b ≤ ∑ c, BAP d L g E m s a c :=
        Finset.single_le_sum (f := fun c => BAP d L g E m s a c)
          (fun c _ => BAP_nonneg d L g E m hs a c) (Finset.mem_univ b)
    _ = 1 := BAP_row_sum d L g E m h hs a

/-- Translation invariance of `P_s` (every real `s`; no `BASelf`). -/
theorem BAP_shift (s : ℝ) (a b : Zd d L) :
    BAP d L g E m s a b = BAP d L g E m s 0 (b - a) := by
  unfold BAP
  congr 1
  refine tsum_congr fun n => ?_
  congr 1
  have h := BAK_pow_shift d L g E m n 0 (b - a) a
  rw [zero_add, sub_add_cancel] at h
  exact h

/-- `P_s(0, -a) = P_s(0, a)` (every real `s`). -/
theorem BAP_neg (s : ℝ) (a : Zd d L) :
    BAP d L g E m s 0 (-a) = BAP d L g E m s 0 a := by
  unfold BAP
  congr 1
  refine tsum_congr fun n => ?_
  congr 1
  have h := BAK_pow_shift d L g E m n 0 (-a) a
  rw [zero_add, neg_add_cancel] at h
  rw [← h]
  have h2 := congrFun (congrFun (BAK_pow_transpose d L g E m n) a) 0
  simpa [Matrix.transpose_apply] using h2.symm

/-- `P_0 = 1`. -/
theorem BAP_zero (a b : Zd d L) :
    BAP d L g E m 0 a b = if a = b then 1 else 0 := by
  unfold BAP
  rw [tsum_eq_single 0]
  · simp [Matrix.one_apply]
  · intro n hn
    simp [zero_pow hn]

/-- The entries of the matrix exponential are the Poisson series (via `NormedSpace.exp`). -/
private theorem KHeat_exp_apply (h : BASelf d L g (E : ℂ) m) (s : ℝ) (a b : Zd d L) :
    (NormedSpace.exp (s • BAK d L g E m)) a b
      = ∑' n : ℕ, s ^ n / (n.factorial : ℝ) * (BAK d L g E m ^ n) a b := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  set F : ℕ → Matrix (Zd d L) (Zd d L) ℝ :=
    fun n => ((n.factorial : ℝ)⁻¹) • (s • BAK d L g E m) ^ n with hF
  have hs : Summable F := by
    refine Pi.summable.2 fun a => Pi.summable.2 fun b => ?_
    have := KHeat_summable d L g E m h s a b
    refine this.congr fun n => ?_
    simp [hF, smul_pow, Matrix.smul_apply]
    ring
  have h1 : (∑' n, F n) a = ∑' n, F n a := Pi.tsum_apply hs
  have h2 : (∑' n, F n a) b = ∑' n, F n a b := Pi.tsum_apply (Pi.summable.1 hs a)
  change (∑' n, F n) a b = _
  rw [h1, h2]
  refine tsum_congr fun n => ?_
  simp [hF, smul_pow, Matrix.smul_apply]
  ring

end Series

/-! ## 3. The Fourier form -/

section Fourier

variable (d L : ℕ) [NeZero L]

/-- The additive character `χ_k(a) = exp(2πi/L Σ_j k_j a_j)` of `ℤ_L^d`. -/
private def KHeat_chi (k a : Zd d L) : ℂ := ZMod.stdAddChar (∑ j, k j * a j)

/-- The phase `θ_k · a` (representatives in `[0, L)`), as in `BAKhat`. -/
private def KHeat_phi (k a : Zd d L) : ℝ :=
  2 * Real.pi / L * ∑ j, ((k j).val : ℝ) * ((a j).val : ℝ)

private theorem KHeat_chi_eq (k a : Zd d L) :
    KHeat_chi d L k a
      = Complex.exp (2 * Real.pi * Complex.I / L * ∑ j, ((k j).val : ℂ) * ((a j).val : ℂ)) := by
  unfold KHeat_chi
  have h1 : (∑ j, k j * a j : ZMod L) = (((∑ j, (k j).val * (a j).val : ℕ) : ℤ) : ZMod L) := by
    push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
  rw [h1, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

private theorem KHeat_char_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod L) :
    ZMod.stdAddChar (∑ j ∈ s, f j) = ∏ j ∈ s, ZMod.stdAddChar (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, AddChar.map_add_eq_mul, ih]

private theorem KHeat_chi_add (k a b : Zd d L) :
    KHeat_chi d L k (a + b) = KHeat_chi d L k a * KHeat_chi d L k b := by
  unfold KHeat_chi
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem KHeat_chi_zero_left (a : Zd d L) : KHeat_chi d L 0 a = 1 := by
  simp [KHeat_chi]

private theorem KHeat_chi_eq_exp (k a : Zd d L) :
    KHeat_chi d L k a = Complex.exp (((KHeat_phi d L k a : ℝ) : ℂ) * Complex.I) := by
  rw [KHeat_chi_eq]
  congr 1
  unfold KHeat_phi
  push_cast
  ring

private theorem KHeat_chi_re (k a : Zd d L) : (KHeat_chi d L k a).re = Real.cos (KHeat_phi d L k a) := by
  rw [KHeat_chi_eq_exp, Complex.exp_ofReal_mul_I_re]

private theorem KHeat_chi_norm (k a : Zd d L) : ‖KHeat_chi d L k a‖ = 1 := by
  rw [KHeat_chi_eq_exp, Complex.norm_exp_ofReal_mul_I]

/-- Orthogonality in `ℤ_L`: `Σ_x ψ(x u) = L [u = 0]` (port of `hp_sum_exp_orth`,
`HeatProduct.lean:858`, in the `AddChar` form). -/
private theorem KHeat_sum_char (u : ZMod L) :
    ∑ x : ZMod L, ZMod.stdAddChar (x * u) = if u = 0 then (L : ℂ) else 0 := by
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar L), ZMod.card]
  split_ifs <;> simp

/-- Orthogonality on `ℤ_L^d`: `Σ_k χ_k(b) = L^d [b = 0]`. -/
private theorem KHeat_sum_chi (b : Zd d L) :
    ∑ k : Zd d L, KHeat_chi d L k b = if b = 0 then ((L : ℂ) ^ d) else 0 := by
  have h1 : ∀ k : Zd d L, KHeat_chi d L k b = ∏ j, ZMod.stdAddChar (k j * b j) := by
    intro k
    unfold KHeat_chi
    rw [KHeat_char_sum]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun j (x : ZMod L) => ZMod.stdAddChar (x * b j))]
  simp_rw [KHeat_sum_char]
  by_cases hb : b = 0
  · subst hb
    simp
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp hb
    simp only [hb, ↓reduceIte]
    have hj' : b j ≠ 0 := by simpa using hj
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj'])

variable (g E : ℝ) (m : ℂ)

/-- The symbol is the eigenvalue of `K` on the character `χ_k`. -/
private theorem KHeat_K_chi (k a : Zd d L) :
    ∑ b, (BAK d L g E m a b : ℂ) * KHeat_chi d L k b
      = KHeat_chi d L k a * (BAKhat d L g E m k : ℂ) := by
  rw [← BAKhat_eq d L g E m k]
  have h1 : ∀ c : Zd d L, KHeat_chi d L k c
      = Complex.exp (2 * Real.pi * Complex.I / L * ∑ j, ((k j).val : ℂ) * ((c j).val : ℂ)) :=
    fun c => KHeat_chi_eq d L k c
  simp_rw [← h1]
  rw [← Equiv.sum_comp (Equiv.addLeft a) (fun b => (BAK d L g E m a b : ℂ) * KHeat_chi d L k b),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Equiv.coe_addLeft]
  rw [KHeat_chi_add]
  have h2 : BAK d L g E m a (a + c) = BAK d L g E m 0 c := by
    have := BAK_shift d L g E m 0 c a
    rw [zero_add, add_comm c a] at this
    exact this
  rw [h2]
  ring

private theorem KHeat_Kpow_chi (n : ℕ) (k a : Zd d L) :
    ∑ b, ((BAK d L g E m ^ n) a b : ℂ) * KHeat_chi d L k b
      = KHeat_chi d L k a * (BAKhat d L g E m k : ℂ) ^ n := by
  induction n generalizing a with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, mul_one]
    simp [apply_ite Complex.ofReal]
  | succ n ih =>
    simp only [pow_succ', Matrix.mul_apply]
    push_cast
    calc ∑ b, (∑ c, (BAK d L g E m a c : ℂ) * ((BAK d L g E m ^ n) c b : ℂ)) * KHeat_chi d L k b
        = ∑ c, (BAK d L g E m a c : ℂ) * ∑ b, ((BAK d L g E m ^ n) c b : ℂ) * KHeat_chi d L k b := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
          ring
      _ = ∑ c, (BAK d L g E m a c : ℂ) * (KHeat_chi d L k c * (BAKhat d L g E m k : ℂ) ^ n) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [ih c]
      _ = (∑ c, (BAK d L g E m a c : ℂ) * KHeat_chi d L k c) * (BAKhat d L g E m k : ℂ) ^ n := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun c _ => ?_
          ring
      _ = _ := by
          rw [KHeat_K_chi]
          ring

/-- The Fourier form of the powers: `(Kⁿ)(0, a) = L^{-d} Σ_k K̂(k)ⁿ cos(θ_k · a)` (circulant and even;
no `BASelf`). -/
private theorem KHeat_pow_fourier (n : ℕ) (a : Zd d L) :
    (BAK d L g E m ^ n) 0 a = ((L : ℝ) ^ d)⁻¹ * ∑ k : Zd d L,
      BAKhat d L g E m k ^ n * Real.cos (KHeat_phi d L k a) := by
  have hL : (L : ℂ) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne L))
  have hsymm : (BAK d L g E m ^ n) 0 a = (BAK d L g E m ^ n) a 0 := by
    have h2 := congrFun (congrFun (BAK_pow_transpose d L g E m n) a) 0
    simpa [Matrix.transpose_apply] using h2
  have hdelta : ∀ b : Zd d L, (if b = 0 then (1 : ℂ) else 0) = ((L : ℂ) ^ d)⁻¹ * ∑ k, KHeat_chi d L k b := by
    intro b
    rw [KHeat_sum_chi]
    split_ifs <;> simp [hL]
  have hc : (((BAK d L g E m ^ n) a 0 : ℝ) : ℂ)
      = ((L : ℂ) ^ d)⁻¹ * ∑ k, (BAKhat d L g E m k : ℂ) ^ n * KHeat_chi d L k a := by
    have h1 : (((BAK d L g E m ^ n) a 0 : ℝ) : ℂ)
        = ∑ b, ((BAK d L g E m ^ n) a b : ℂ) * (if b = 0 then (1 : ℂ) else 0) := by
      rw [Finset.sum_eq_single (0 : Zd d L)]
      · simp
      · intro b _ hb
        simp [hb]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h1]
    simp_rw [hdelta, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ k : Zd d L, ∑ b, ((BAK d L g E m ^ n) a b : ℂ) * (((L : ℂ) ^ d)⁻¹ * KHeat_chi d L k b)
        = ((L : ℂ) ^ d)⁻¹ * ((BAKhat d L g E m k : ℂ) ^ n * KHeat_chi d L k a) := by
      intro k
      calc ∑ b, ((BAK d L g E m ^ n) a b : ℂ) * (((L : ℂ) ^ d)⁻¹ * KHeat_chi d L k b)
          = ((L : ℂ) ^ d)⁻¹ * ∑ b, ((BAK d L g E m ^ n) a b : ℂ) * KHeat_chi d L k b := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun b _ => by ring
        _ = _ := by rw [KHeat_Kpow_chi]; ring
    simp_rw [this]
  rw [hsymm]
  have := congrArg Complex.re hc
  rw [Complex.ofReal_re] at this
  rw [this]
  have hre : ∀ r : ℂ, ((L : ℂ) ^ d)⁻¹ * r = (((L : ℝ) ^ d)⁻¹ : ℝ) * r := by
    intro r; push_cast; rfl
  rw [hre, Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.ofReal_pow, Complex.re_ofReal_mul, KHeat_chi_re]

end Fourier

/-! ## 4. Targets: the Fourier form and the basic properties -/

/-- **Fourier form** on the torus (finite sums; `θ_k = 2π k / L`, symbol `BAKhat`). -/
theorem kBA_fourier : ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ), 0 < g → ∀ (τ : ℝ) (a : Zd d L),
    kBA d L g E m τ a = (((L : ℝ) ^ d)⁻¹) * ∑ k : Zd d L,
      Real.exp (-(τ / g ^ 2) * (1 - BAKhat d L g E m k)) *
        Real.cos (2 * Real.pi / L * ∑ j, ((k j).val : ℝ) * ((a j).val : ℝ)) := by
  intro d L _ g E m hg τ a
  unfold kBA BAP
  set s : ℝ := τ / g ^ 2 with hs
  have h1 : ∀ n : ℕ, s ^ n / (n.factorial : ℝ) * (BAK d L g E m ^ n) 0 a
      = ((L : ℝ) ^ d)⁻¹ * ∑ k : Zd d L,
          (s * BAKhat d L g E m k) ^ n / (n.factorial : ℝ) * Real.cos (KHeat_phi d L k a) := by
    intro n
    rw [KHeat_pow_fourier, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow]
    ring
  simp_rw [h1]
  rw [tsum_mul_left, Summable.tsum_finsetSum (fun k _ => ?_)]
  swap
  · exact ((Real.summable_pow_div_factorial (s * BAKhat d L g E m k)).mul_right _)
  have h2 : ∀ k : Zd d L, ∑' n : ℕ, (s * BAKhat d L g E m k) ^ n / (n.factorial : ℝ) * Real.cos (KHeat_phi d L k a)
      = Real.exp (s * BAKhat d L g E m k) * Real.cos (KHeat_phi d L k a) := by
    intro k
    rw [tsum_mul_right, KHeat_tsum_exp]
  simp_rw [h2]
  rw [mul_left_comm, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Basic properties** of `kBA`: nonnegative, mass one, at most one, `δ` at `τ = 0`, even, continuous in `τ`. -/
theorem kBA_basic : ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ), 0 < g → BASelf d L g (E : ℂ) m →
    (∀ τ : ℝ, 0 ≤ τ → ∀ a : Zd d L, 0 ≤ kBA d L g E m τ a) ∧
    (∀ τ : ℝ, 0 ≤ τ → ∑ a : Zd d L, kBA d L g E m τ a = 1) ∧
    (∀ τ : ℝ, 0 ≤ τ → ∀ a : Zd d L, kBA d L g E m τ a ≤ 1) ∧
    (∀ a : Zd d L, kBA d L g E m 0 a = if a = 0 then 1 else 0) ∧
    (∀ τ : ℝ, ∀ a : Zd d L, kBA d L g E m τ (-a) = kBA d L g E m τ a) ∧
    (∀ a : Zd d L, Continuous fun τ : ℝ => kBA d L g E m τ a) := by
  intro d L _ g E m hg hS
  refine ⟨fun τ hτ a => ?_, fun τ hτ => ?_, fun τ hτ a => ?_, fun a => ?_, fun τ a => ?_, fun a => ?_⟩
  · exact BAP_nonneg d L g E m (div_nonneg hτ (sq_nonneg g)) 0 a
  · exact BAP_row_sum d L g E m hS (div_nonneg hτ (sq_nonneg g)) 0
  · exact BAP_le_one d L g E m hS (div_nonneg hτ (sq_nonneg g)) 0 a
  · unfold kBA
    rw [zero_div, BAP_zero]
    simp only [eq_comm]
  · exact BAP_neg d L g E m (τ / g ^ 2) a
  · have h : (fun τ : ℝ => kBA d L g E m τ a) = fun τ : ℝ => (((L : ℝ) ^ d)⁻¹) * ∑ k : Zd d L,
        Real.exp (-(τ / g ^ 2) * (1 - BAKhat d L g E m k)) *
          Real.cos (2 * Real.pi / L * ∑ j, ((k j).val : ℝ) * ((a j).val : ℝ)) :=
      funext fun τ => kBA_fourier d L g E m hg τ a
    rw [h]
    fun_prop

/-- **Semigroup and translation invariance** of `P_s`. -/
theorem BAP_semigroup_shift : ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ), BASelf d L g (E : ℂ) m →
    (∀ s s' : ℝ, 0 ≤ s → 0 ≤ s' → ∀ a b : Zd d L,
      BAP d L g E m (s + s') a b = ∑ c : Zd d L, BAP d L g E m s a c * BAP d L g E m s' c b) ∧
    (∀ s : ℝ, ∀ a b : Zd d L, BAP d L g E m s a b = BAP d L g E m s 0 (b - a)) := by
  intro d L _ g E m h
  refine ⟨fun s s' _ _ a b => ?_, fun s a b => BAP_shift d L g E m s a b⟩
  have hBAP : ∀ (s : ℝ) (a b : Zd d L), BAP d L g E m s a b
      = Real.exp (-s) * (NormedSpace.exp (s • BAK d L g E m)) a b := by
    intro s a b
    rw [KHeat_exp_apply d L g E m h]
    rfl
  have hadd : NormedSpace.exp ((s + s') • BAK d L g E m)
      = NormedSpace.exp (s • BAK d L g E m) * NormedSpace.exp (s' • BAK d L g E m) := by
    rw [add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl _).smul_left s).smul_right s')
  rw [hBAP, hadd, Matrix.mul_apply]
  simp_rw [hBAP]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [neg_add, Real.exp_add]
  ring

/-! ## 5. The Laplace identity -/

section Laplace

variable (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ)

private theorem KHeat_summable_t (h : BASelf d L g (E : ℂ) m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (a b : Zd d L) : Summable (fun n : ℕ => t ^ n * (BAK d L g E m ^ n) a b) := by
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (pow_nonneg ht0 n) (BAK_pow_nonneg d L g E m n a b)) (fun n => ?_)
    (summable_geometric_of_lt_one ht0 ht1)
  calc t ^ n * (BAK d L g E m ^ n) a b ≤ t ^ n * 1 :=
        mul_le_mul_of_nonneg_left (KHeat_pow_le_one d L g E m h n a b) (pow_nonneg ht0 n)
    _ = t ^ n := mul_one _

/-- The Neumann series solves `B - t K B = 1` entrywise. -/
private theorem KHeat_neumann (h : BASelf d L g (E : ℂ) m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (a b : Zd d L) :
    (∑' n : ℕ, t ^ n * (BAK d L g E m ^ n) a b)
      - t * ∑ c, BAK d L g E m a c * ∑' n : ℕ, t ^ n * (BAK d L g E m ^ n) c b
      = if a = b then 1 else 0 := by
  have hsum := fun c => KHeat_summable_t d L g E m h ht0 ht1 c b
  have h1 : ∑ c, BAK d L g E m a c * ∑' n : ℕ, t ^ n * (BAK d L g E m ^ n) c b
      = ∑' n : ℕ, t ^ n * (BAK d L g E m ^ (n + 1)) a b := by
    simp_rw [← tsum_mul_left]
    rw [← Summable.tsum_finsetSum (fun c _ => (hsum c).mul_left _)]
    refine tsum_congr fun n => ?_
    rw [pow_succ', Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [h1, (hsum a).tsum_eq_zero_add]
  have h2 : ∑' n : ℕ, t ^ (n + 1) * (BAK d L g E m ^ (n + 1)) a b
      = t * ∑' n : ℕ, t ^ n * (BAK d L g E m ^ (n + 1)) a b := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    ring
  rw [h2]
  simp [Matrix.one_apply]

/-- `Θ^{(+,-)}_t = Σ tⁿ Kⁿ` for `0 ≤ t < 1` (Neumann series; `Ring.inverse (1 - tK)`). -/
private theorem KHeat_Theta_eq (h : BASelf d L g (E : ℂ) m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    BATheta d L g E m t true false
      = Matrix.of fun a b => (((∑' n : ℕ, t ^ n * (BAK d L g E m ^ n) a b : ℝ)) : ℂ) := by
  rw [BATheta_pm_eq]
  unfold PropThetaQ
  set B : Matrix (Zd d L) (Zd d L) ℂ :=
    Matrix.of fun a b => (((∑' n : ℕ, t ^ n * (BAK d L g E m ^ n) a b : ℝ)) : ℂ) with hB
  have hXB : (1 - (t : ℂ) • Matrix.map (BAK d L g E m) Complex.ofReal) * B = 1 := by
    ext a b
    have h1 := congrArg (fun r : ℝ => (r : ℂ)) (KHeat_neumann d L g E m h ht0 ht1 a b)
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_sum] at h1
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply, hB,
      Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, smul_eq_mul]
    have h2 : ∑ c, (if a = c then (1 : ℂ) else 0) * ((∑' n : ℕ, t ^ n * (BAK d L g E m ^ n) c b : ℝ) : ℂ)
        = ((∑' n : ℕ, t ^ n * (BAK d L g E m ^ n) a b : ℝ) : ℂ) := by
      simp
    have h3 : ∑ c, (t : ℂ) * (BAK d L g E m a c : ℂ) * ((∑' n : ℕ, t ^ n * (BAK d L g E m ^ n) c b : ℝ) : ℂ)
        = (t : ℂ) * ∑ c, (BAK d L g E m a c : ℂ) * ((∑' n : ℕ, t ^ n * (BAK d L g E m ^ n) c b : ℝ) : ℂ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [h2, h3]
    push_cast at h1 ⊢
    rw [h1]
    split_ifs <;> simp
  have hBX : B * (1 - (t : ℂ) • Matrix.map (BAK d L g E m) Complex.ofReal) = 1 :=
    mul_eq_one_comm.mp hXB
  have hu : IsUnit (1 - (t : ℂ) • Matrix.map (BAK d L g E m) Complex.ofReal) :=
    ⟨⟨_, B, hXB, hBX⟩, rfl⟩
  calc Ring.inverse (1 - (t : ℂ) • Matrix.map (BAK d L g E m) Complex.ofReal)
      = Ring.inverse (1 - (t : ℂ) • Matrix.map (BAK d L g E m) Complex.ofReal)
          * ((1 - (t : ℂ) • Matrix.map (BAK d L g E m) Complex.ofReal) * B) := by rw [hXB, mul_one]
    _ = B := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]


/-- The Gamma integral: `∫₀^∞ e^{-u} uⁿ/n! du = 1`, with integrability. -/
private theorem KHeat_gamma (n : ℕ) :
    IntegrableOn (fun u : ℝ => Real.exp (-u) * (u ^ n / (n.factorial : ℝ))) (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), Real.exp (-u) * (u ^ n / (n.factorial : ℝ)) = 1 := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hint := Real.GammaIntegral_convergent hpos
  have hn : ∀ u : ℝ, u ^ ((n : ℝ) + 1 - 1) = u ^ n := by
    intro u
    rw [add_sub_cancel_right, Real.rpow_natCast]
  simp_rw [hn] at hint
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have hI : ∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ n = (n.factorial : ℝ) := by
    have h1 := Real.Gamma_eq_integral hpos
    simp_rw [hn] at h1
    rw [← h1]
    have h2 := Real.Gamma_nat_eq_factorial n
    exact h2
  refine ⟨?_, ?_⟩
  · have := hint.div_const (n.factorial : ℝ)
    have h2 : Integrable (fun u : ℝ => Real.exp (-u) * (u ^ n / (n.factorial : ℝ)))
        (volume.restrict (Ioi 0)) := by
      simpa only [mul_div_assoc] using this
    exact h2
  · have : ∀ u : ℝ, Real.exp (-u) * (u ^ n / (n.factorial : ℝ))
        = (Real.exp (-u) * u ^ n) / (n.factorial : ℝ) := fun u => by ring
    simp_rw [this]
    rw [integral_div, hI]
    exact div_self hfac.ne'

end Laplace

/-- **Laplace identity** (twin of `Theta_eq_laplace_prod`; `Θ = Σ tⁿ Kⁿ = ∫₀^∞ e^{-(1-t)u} P_{tu} du`, diffusive time
`τ = t g² u`). -/
theorem BATheta_eq_laplace_kBA : ∀ (d L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ) (t : ℝ), 0 < g → BASelf d L g (E : ℂ) m →
    0 ≤ t → t < 1 → ∀ a : Zd d L,
      BATheta d L g E m t true false 0 a =
        ((∫ u in Ioi (0 : ℝ), Real.exp (-(1 - t) * u) * kBA d L g E m (t * g ^ 2 * u) a : ℝ) : ℂ) := by
  intro d L _ hL g E m t hg hS ht0 ht1 a
  rw [KHeat_Theta_eq d L g E m hS ht0 ht1]
  simp only [Matrix.of_apply]
  congr 1
  set c : ℕ → ℝ := fun n => (BAK d L g E m ^ n) 0 a with hc
  have hc0 : ∀ n, 0 ≤ c n := fun n => BAK_pow_nonneg d L g E m n 0 a
  set F : ℕ → ℝ → ℝ := fun n u => (t ^ n * c n) * (Real.exp (-u) * (u ^ n / (n.factorial : ℝ))) with hF
  have hpt : ∀ u : ℝ, Real.exp (-(1 - t) * u) * kBA d L g E m (t * g ^ 2 * u) a = ∑' n, F n u := by
    intro u
    unfold kBA BAP
    have h1 : t * g ^ 2 * u / g ^ 2 = t * u := by field_simp
    rw [h1]
    have h2 : ∀ n : ℕ, F n u = Real.exp (-u) * ((t * u) ^ n / (n.factorial : ℝ) * c n) := by
      intro n
      simp only [hF]
      rw [mul_pow]
      ring
    simp_rw [h2]
    rw [tsum_mul_left, ← mul_assoc, ← Real.exp_add]
    congr 3
    ring
  have hFint : ∀ n, Integrable (F n) (volume.restrict (Ioi 0)) := fun n =>
    (KHeat_gamma n).1.const_mul _
  have hFnn : ∀ n, ∀ u ∈ Ioi (0 : ℝ), 0 ≤ F n u := by
    intro n u hu
    have hu0 : 0 < u := hu
    have := hc0 n
    simp only [hF]
    positivity
  have hFint2 : ∀ n, ∫ u in Ioi (0 : ℝ), F n u = t ^ n * c n := by
    intro n
    simp only [hF]
    rw [integral_const_mul, (KHeat_gamma n).2, mul_one]
  have hFnorm : ∀ n, ∫ u in Ioi (0 : ℝ), ‖F n u‖ = t ^ n * c n := by
    intro n
    rw [← hFint2 n]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    exact Real.norm_of_nonneg (hFnn n u hu)
  have hsum : Summable fun n => ∫ u in Ioi (0 : ℝ), ‖F n u‖ := by
    simp_rw [hFnorm]
    exact KHeat_summable_t d L g E m hS ht0 ht1 0 a
  have key := integral_tsum_of_summable_integral_norm hFint hsum
  simp_rw [hFint2] at key
  rw [key]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  exact (hpt u).symm

/-! ## 6. The torus sums (twin of `HeatTorus1D.lean`: the 1D lattice sums) -/

section Torus

variable {L : ℕ} [NeZero L]

private theorem KHeat_sum_geom_zdist {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0, r ^ RBM.zdist L k ≤ 2 * (r / (1 - r)) := by
  classical
  have key : ∀ g : ZMod L → ℕ, Function.Injective g →
      (∀ k : ZMod L, k ≠ 0 → g k ∈ Finset.Ico 1 L) →
      ∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0, r ^ g k ≤ r / (1 - r) := by
    intro g hg hmem
    have h1 : ∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0, r ^ g k
        = ∑ v ∈ ((Finset.univ : Finset (ZMod L)).erase 0).image g, r ^ v :=
      (Finset.sum_image (fun a _ b _ hab => hg hab)).symm
    rw [h1]
    calc ∑ v ∈ ((Finset.univ : Finset (ZMod L)).erase 0).image g, r ^ v
        ≤ ∑ v ∈ Finset.Ico 1 L, r ^ v := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro v hv
            obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hv
            exact hmem k (Finset.ne_of_mem_erase hk)
          · intro v _ _
            positivity
      _ ≤ r ^ 1 / (1 - r) := geom_sum_Ico_le_of_lt_one hr0 hr1
      _ = r / (1 - r) := by rw [pow_one]
  have hval := key (fun k => k.val) (ZMod.val_injective L) (fun k hk => by
    simp only [Finset.mem_Ico]
    exact ⟨ZMod.val_pos.mpr hk, ZMod.val_lt k⟩)
  have hneg := key (fun k => (-k).val) ((ZMod.val_injective L).comp neg_injective) (fun k hk => by
    simp only [Finset.mem_Ico]
    have hk' : -k ≠ 0 := neg_ne_zero.mpr hk
    exact ⟨ZMod.val_pos.mpr hk', ZMod.val_lt _⟩)
  calc ∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0, r ^ RBM.zdist L k
      ≤ ∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0, (r ^ k.val + r ^ (-k).val) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        have hk0 : k ≠ 0 := Finset.ne_of_mem_erase hk
        have hn : (-k).val = L - k.val := by rw [ZMod.neg_val]; simp [hk0]
        unfold RBM.zdist
        rw [hn]
        rcases min_choice k.val (L - k.val) with h | h
        · rw [h]; exact le_add_of_nonneg_right (by positivity)
        · rw [h]; exact le_add_of_nonneg_left (by positivity)
    _ = ∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0, r ^ k.val
          + ∑ k ∈ (Finset.univ : Finset (ZMod L)).erase 0, r ^ (-k).val :=
        Finset.sum_add_distrib
    _ ≤ 2 * (r / (1 - r)) := by linarith

/-- `t e^{-t} ≤ 1` for `t ≥ 0` (port of `mul_exp_neg_le_one`, `HeatTorus1D.lean:299`). -/
private theorem KHeat_mul_exp_neg_le_one (t : ℝ) : t * Real.exp (-t) ≤ 1 := by
  have h : t < Real.exp t := by linarith [Real.add_one_le_exp t]
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos t)]
  exact h.le

/-- The Gaussian sum over the torus distance: `Σ_x e^{-ρ |x|²} ≤ 1 + 2 r₀/(1 - r₀)`, `r₀ = e^{-ρ₀}`,
for `ρ ≥ ρ₀ > 0`. -/
private theorem KHeat_sum_gauss {ρ₀ ρ : ℝ} (hρ₀ : 0 < ρ₀) (hρ : ρ₀ ≤ ρ) :
    ∑ x : ZMod L, Real.exp (-ρ * (zdist L x : ℝ) ^ 2)
      ≤ 1 + 2 * (Real.exp (-ρ₀) / (1 - Real.exp (-ρ₀))) := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le hρ₀ hρ
  have hr0 : 0 ≤ Real.exp (-ρ) := (Real.exp_pos _).le
  have hr1 : Real.exp (-ρ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hr01 : Real.exp (-ρ₀) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod L))]
  have h0 : Real.exp (-ρ * (zdist L (0 : ZMod L) : ℝ) ^ 2) = 1 := by simp
  rw [h0]
  have hpt : ∀ x ∈ (Finset.univ : Finset (ZMod L)).erase 0,
      Real.exp (-ρ * (zdist L x : ℝ) ^ 2) ≤ Real.exp (-ρ) ^ zdist L x := by
    intro x hx
    have hz : 1 ≤ zdist L x :=
      Nat.one_le_iff_ne_zero.mpr (fun h => (Finset.ne_of_mem_erase hx) ((zdist_eq_zero_iff L).mp h))
    have hz' : (1 : ℝ) ≤ (zdist L x : ℝ) := by exact_mod_cast hz
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_nonneg (mul_nonneg hρ0.le (by linarith : (0 : ℝ) ≤ (zdist L x : ℝ))) (sub_nonneg.2 hz')]
  have hsum := KHeat_sum_geom_zdist (L := L) hr0 hr1
  have hmono : Real.exp (-ρ) / (1 - Real.exp (-ρ)) ≤ Real.exp (-ρ₀) / (1 - Real.exp (-ρ₀)) := by
    refine div_le_div₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr (by linarith)) (by linarith) ?_
    linarith [Real.exp_le_exp.mpr (show -ρ ≤ -ρ₀ by linarith)]
  calc 1 + ∑ x ∈ (Finset.univ : Finset (ZMod L)).erase 0, Real.exp (-ρ * (zdist L x : ℝ) ^ 2)
      ≤ 1 + ∑ x ∈ (Finset.univ : Finset (ZMod L)).erase 0, Real.exp (-ρ) ^ zdist L x := by
        gcongr with x hx
        exact hpt x hx
    _ ≤ 1 + 2 * (Real.exp (-ρ) / (1 - Real.exp (-ρ))) := by linarith
    _ ≤ _ := by linarith

variable {d : ℕ}

/-- The Gaussian sum over the dual torus factorises over the coordinates. -/
private theorem KHeat_prod_sum (v : ℝ) :
    ∑ k : Zd d L, Real.exp (-v * BAthetaSq d L k)
      = (∑ x : ZMod L, Real.exp (-v * (2 * Real.pi * (zdist L x : ℝ) / L) ^ 2)) ^ d := by
  have h1 : ∀ k : Zd d L, Real.exp (-v * BAthetaSq d L k)
      = ∏ j, Real.exp (-v * (2 * Real.pi * (zdist L (k j) : ℝ) / L) ^ 2) := by
    intro k
    unfold BAthetaSq
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun (j : Fin d) (x : ZMod L) =>
    Real.exp (-v * (2 * Real.pi * (zdist L x : ℝ) / L) ^ 2))]
  simp [Finset.prod_const]

/-- For `k ≠ 0` some coordinate is nonzero: `|θ_k|² ≥ (2π/L)²`. -/
private theorem KHeat_thetaSq_ge (k : Zd d L) (hk : k ≠ 0) :
    (2 * Real.pi / L) ^ 2 ≤ BAthetaSq d L k := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hk
  have hj' : k j ≠ 0 := by simpa using hj
  have hz : 1 ≤ zdist L (k j) :=
    Nat.one_le_iff_ne_zero.mpr (fun h => hj' ((zdist_eq_zero_iff L).mp h))
  have hz' : (1 : ℝ) ≤ (zdist L (k j) : ℝ) := by exact_mod_cast hz
  have hL : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  unfold BAthetaSq
  calc (2 * Real.pi / L) ^ 2 ≤ (2 * Real.pi * (zdist L (k j) : ℝ) / L) ^ 2 := by
        refine pow_le_pow_left₀ (by positivity) ?_ 2
        refine div_le_div_of_nonneg_right ?_ hL.le
        nlinarith [Real.pi_pos]
    _ ≤ ∑ i, (2 * Real.pi * (zdist L (k i) : ℝ) / L) ^ 2 :=
        Finset.single_le_sum (f := fun i => (2 * Real.pi * (zdist L (k i) : ℝ) / L) ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ j)

/-- One coordinate is at most the whole: `θ_j² ≤ |θ_k|²`. -/
private theorem KHeat_theta_sq_le (k : Zd d L) (j : Fin d) :
    (2 * Real.pi * (zdist L (k j) : ℝ) / L) ^ 2 ≤ BAthetaSq d L k := by
  unfold BAthetaSq
  exact Finset.single_le_sum (f := fun i => (2 * Real.pi * (zdist L (k i) : ℝ) / L) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ j)

/-- The product of two coordinates is at most the whole: `θ_i θ_j ≤ |θ_k|²`. -/
private theorem KHeat_theta_mul_le (k : Zd d L) (i j : Fin d) :
    (2 * Real.pi * (zdist L (k i) : ℝ) / L) * (2 * Real.pi * (zdist L (k j) : ℝ) / L)
      ≤ BAthetaSq d L k := by
  have h1 := KHeat_theta_sq_le k i
  have h2 := KHeat_theta_sq_le k j
  nlinarith [sq_nonneg ((2 * Real.pi * (zdist L (k i) : ℝ) / L) - (2 * Real.pi * (zdist L (k j) : ℝ) / L))]

/-- The pointwise decay of the symbol, from the gap `c g² |θ|² ≤ 1 - K̂`. -/
private theorem KHeat_mu_le {c g τ Θ K : ℝ} (hg : 0 < g) (hτ : 0 ≤ τ)
    (h : c * g ^ 2 * Θ ≤ 1 - K) :
    Real.exp (-(τ / g ^ 2) * (1 - K)) ≤ Real.exp (-(c * τ) * Θ) := by
  refine Real.exp_le_exp.mpr ?_
  have h2 := mul_le_mul_of_nonneg_left h (div_nonneg hτ (sq_nonneg g))
  have h3 : τ / g ^ 2 * (c * g ^ 2 * Θ) = c * τ * Θ := by field_simp
  nlinarith

/-- `y e^{-wΘ/2} ≤ (1/c + 1)/L` when `y² ≤ Θ`, `w = cτ`, `τ ≥ L²`. -/
private theorem KHeat_poly1 {c τ Θ y : ℝ} (hc : 0 < c) (hτ : (L : ℝ) ^ 2 ≤ τ) (hy : 0 ≤ y)
    (hΘ : y ^ 2 ≤ Θ) :
    y * Real.exp (-(c * τ) * Θ / 2) ≤ (1 / c + 1) * (L : ℝ)⁻¹ := by
  have hL : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτ
  have hΘ0 : 0 ≤ Θ := le_trans (sq_nonneg y) hΘ
  have hw : 0 < c * τ := by positivity
  have h1 := KHeat_mul_exp_neg_le_one (c * τ * Θ)
  have h2 : Θ * Real.exp (-(c * τ * Θ)) ≤ 1 / (c * τ) := by
    rw [le_div_iff₀ hw]
    nlinarith
  have h3 : 1 / (c * τ) ≤ 1 / c * ((L : ℝ)⁻¹) ^ 2 := by
    rw [inv_pow, one_div, one_div, ← mul_inv, mul_comm]
    refine inv_anti₀ (by positivity) ?_
    nlinarith
  have h4 : (y * Real.exp (-(c * τ) * Θ / 2)) ^ 2 ≤ 1 / c * ((L : ℝ)⁻¹) ^ 2 := by
    have : (y * Real.exp (-(c * τ) * Θ / 2)) ^ 2 = y ^ 2 * Real.exp (-(c * τ * Θ)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    rw [this]
    calc y ^ 2 * Real.exp (-(c * τ * Θ)) ≤ Θ * Real.exp (-(c * τ * Θ)) :=
          mul_le_mul_of_nonneg_right hΘ (Real.exp_pos _).le
      _ ≤ _ := h2.trans h3
  have h5 : 1 / c * ((L : ℝ)⁻¹) ^ 2 ≤ ((1 / c + 1) * (L : ℝ)⁻¹) ^ 2 := by
    have hLi : 0 ≤ (L : ℝ)⁻¹ := by positivity
    have hx : 0 ≤ 1 / c := by positivity
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp (h4.trans h5)

/-- `y e^{-wΘ/2} ≤ (2/c)/L²` when `y ≤ Θ`, `w = cτ`, `τ ≥ L²`. -/
private theorem KHeat_poly2 {c τ Θ y : ℝ} (hc : 0 < c) (hτ : (L : ℝ) ^ 2 ≤ τ) (hy : 0 ≤ y)
    (hΘ : y ≤ Θ) :
    y * Real.exp (-(c * τ) * Θ / 2) ≤ (2 / c) * ((L : ℝ)⁻¹) ^ 2 := by
  have hL : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτ
  have hΘ0 : 0 ≤ Θ := le_trans hy hΘ
  have hw : 0 < c * τ := by positivity
  have h1 := KHeat_mul_exp_neg_le_one (c * τ * Θ / 2)
  have h2 : Θ * Real.exp (-(c * τ) * Θ / 2) ≤ 2 / (c * τ) := by
    have : -(c * τ * Θ / 2) = -(c * τ) * Θ / 2 := by ring
    rw [this] at h1
    rw [le_div_iff₀ hw]
    nlinarith
  have h3 : 2 / (c * τ) ≤ 2 / c * ((L : ℝ)⁻¹) ^ 2 := by
    have : 2 / c * ((L : ℝ)⁻¹) ^ 2 = 2 / (c * (L : ℝ) ^ 2) := by field_simp
    rw [this]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  calc y * Real.exp (-(c * τ) * Θ / 2) ≤ Θ * Real.exp (-(c * τ) * Θ / 2) :=
        mul_le_mul_of_nonneg_right hΘ (Real.exp_pos _).le
    _ ≤ _ := h2.trans h3

end Torus

/-! ## 7. Unit differences of the characters and the tail sum -/

section Gap

variable {d L : ℕ} [NeZero L]

private theorem KHeat_chi_single (k : Zd d L) (j : Fin d) :
    KHeat_chi d L k (Pi.single j 1) = ZMod.stdAddChar (k j) := by
  unfold KHeat_chi
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Pi.single_eq_of_ne hij]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- `|e^{2πi y/L} - 1| ≤ 2π |y|_L / L`. -/
private theorem KHeat_char_sub_one (y : ZMod L) :
    ‖ZMod.stdAddChar y - 1‖ ≤ 2 * Real.pi * (zdist L y : ℝ) / L := by
  have hy : ((y.valMinAbs : ℤ) : ZMod L) = y := ZMod.coe_valMinAbs y
  have hL : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  rw [show ZMod.stdAddChar y = ZMod.stdAddChar ((y.valMinAbs : ℤ) : ZMod L) by rw [hy],
    ZMod.stdAddChar_coe]
  have h1 : 2 * (Real.pi : ℂ) * Complex.I * ((y.valMinAbs : ℤ) : ℂ) / (L : ℂ)
      = Complex.I * ((2 * Real.pi * (y.valMinAbs : ℝ) / L : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h1]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  have hz : |(y.valMinAbs : ℝ)| = (zdist L y : ℝ) := by
    have h := ZMod.valMinAbs_natAbs_eq_min y
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    simp only [zdist]
    exact_mod_cast h
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, hz, abs_of_pos Real.pi_pos, Nat.abs_cast,
    abs_two]

private theorem KHeat_diff1 (k a : Zd d L) (j : Fin d) :
    |(KHeat_chi d L k (a + Pi.single j 1)).re - (KHeat_chi d L k a).re|
      ≤ 2 * Real.pi * (zdist L (k j) : ℝ) / L := by
  have h : (KHeat_chi d L k (a + Pi.single j 1)).re - (KHeat_chi d L k a).re
      = (KHeat_chi d L k a * (ZMod.stdAddChar (k j) - 1)).re := by
    rw [KHeat_chi_add, KHeat_chi_single, mul_sub, mul_one, Complex.sub_re]
  rw [h]
  calc _ ≤ ‖KHeat_chi d L k a * (ZMod.stdAddChar (k j) - 1)‖ := Complex.abs_re_le_norm _
    _ = ‖ZMod.stdAddChar (k j) - 1‖ := by rw [norm_mul, KHeat_chi_norm, one_mul]
    _ ≤ _ := KHeat_char_sub_one _

private theorem KHeat_diff2 (k a : Zd d L) (i j : Fin d) :
    |(KHeat_chi d L k (a + Pi.single i 1 + Pi.single j 1)).re
        - (KHeat_chi d L k (a + Pi.single i 1)).re - (KHeat_chi d L k (a + Pi.single j 1)).re
        + (KHeat_chi d L k a).re|
      ≤ (2 * Real.pi * (zdist L (k i) : ℝ) / L) * (2 * Real.pi * (zdist L (k j) : ℝ) / L) := by
  have h : (KHeat_chi d L k (a + Pi.single i 1 + Pi.single j 1)).re
        - (KHeat_chi d L k (a + Pi.single i 1)).re - (KHeat_chi d L k (a + Pi.single j 1)).re
        + (KHeat_chi d L k a).re
      = (KHeat_chi d L k a * ((ZMod.stdAddChar (k i) - 1) * (ZMod.stdAddChar (k j) - 1))).re := by
    rw [KHeat_chi_add, KHeat_chi_add, KHeat_chi_add, KHeat_chi_single, KHeat_chi_single]
    simp only [← Complex.sub_re, ← Complex.add_re]
    congr 1
    ring
  rw [h]
  calc _ ≤ ‖KHeat_chi d L k a * ((ZMod.stdAddChar (k i) - 1) * (ZMod.stdAddChar (k j) - 1))‖ :=
        Complex.abs_re_le_norm _
    _ = ‖ZMod.stdAddChar (k i) - 1‖ * ‖ZMod.stdAddChar (k j) - 1‖ := by
        rw [norm_mul, KHeat_chi_norm, one_mul, norm_mul]
    _ ≤ _ := mul_le_mul (KHeat_char_sub_one _) (KHeat_char_sub_one _) (norm_nonneg _)
        (by positivity)

/-- `K̂(0) = 1` (row sum). -/
private theorem KHeat_Khat_zero (g E : ℝ) (m : ℂ) (h : BASelf d L g (E : ℂ) m) :
    BAKhat d L g E m 0 = 1 := by
  unfold BAKhat
  have : ∀ a : Zd d L, Real.cos (2 * Real.pi / L * ∑ j, (((0 : Zd d L) j).val : ℝ) * ((a j).val : ℝ)) = 1 := by
    intro a
    simp
  simp_rw [this, mul_one]
  exact BAK_row_sum d L g E m h 0

/-- The constant `T₁ = 1 + 2 r₀/(1 - r₀)`, `r₀ = e^{-π² c}`: the 1D Gaussian sum in regime (ii). -/
private def KHeat_T1 (c : ℝ) : ℝ :=
  1 + 2 * (Real.exp (-(Real.pi ^ 2 * c)) / (1 - Real.exp (-(Real.pi ^ 2 * c))))

private theorem KHeat_T1_ge_one {c : ℝ} (hc : 0 < c) : 1 ≤ KHeat_T1 c := by
  unfold KHeat_T1
  have h1 : Real.exp (-(Real.pi ^ 2 * c)) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, mul_pos (pow_pos Real.pi_pos 2) hc])
  have : 0 ≤ Real.exp (-(Real.pi ^ 2 * c)) / (1 - Real.exp (-(Real.pi ^ 2 * c))) :=
    div_nonneg (Real.exp_pos _).le (by linarith)
  linarith

/-- **The tail sum.**  If `|F k| ≤ q_k e^{-cτ|θ_k|²}` and `q_k e^{-cτ|θ_k|²/2} ≤ A L^{-ν}` for `k ≠ 0`,
`τ ≥ L²`, then `Σ_{k ≠ 0} |F k| ≤ A L^{-ν} e^{-π² c τ/L²} T₁^d`. -/
private theorem KHeat_master {c : ℝ} (hc : 0 < c) {τ : ℝ} (hτ : (L : ℝ) ^ 2 ≤ τ) {ν : ℕ} {A : ℝ}
    (hA : 0 ≤ A) (F q : Zd d L → ℝ)
    (hF : ∀ k, k ≠ 0 → |F k| ≤ q k * Real.exp (-(c * τ) * BAthetaSq d L k))
    (hq : ∀ k, k ≠ 0 → q k * Real.exp (-(c * τ) * BAthetaSq d L k / 2) ≤ A * ((L : ℝ)⁻¹) ^ ν) :
    ∑ k ∈ (Finset.univ : Finset (Zd d L)).erase 0, |F k|
      ≤ A * ((L : ℝ)⁻¹) ^ ν * Real.exp (-(Real.pi ^ 2 * c) * τ / (L : ℝ) ^ 2) * KHeat_T1 c ^ d := by
  have hL : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτ
  set M : ℝ := A * ((L : ℝ)⁻¹) ^ ν * Real.exp (-(Real.pi ^ 2 * c) * τ / (L : ℝ) ^ 2) with hM
  have hM0 : 0 ≤ M := by positivity
  have hpt : ∀ k ∈ (Finset.univ : Finset (Zd d L)).erase 0,
      |F k| ≤ M * Real.exp (-(c * τ / 4) * BAthetaSq d L k) := by
    intro k hk
    have hk0 : k ≠ 0 := Finset.ne_of_mem_erase hk
    have hΘ := KHeat_thetaSq_ge k hk0
    set Θ := BAthetaSq d L k with hΘdef
    have h1 : Real.exp (-(c * τ) * Θ)
        = Real.exp (-(c * τ) * Θ / 2) * Real.exp (-(c * τ / 4) * Θ) * Real.exp (-(c * τ / 4) * Θ) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have h2 : Real.exp (-(c * τ / 4) * Θ) ≤ Real.exp (-(Real.pi ^ 2 * c) * τ / (L : ℝ) ^ 2) := by
      refine Real.exp_le_exp.mpr ?_
      have h3 : (2 * Real.pi / L) ^ 2 * (c * τ / 4) = Real.pi ^ 2 * c * τ / (L : ℝ) ^ 2 := by
        field_simp
        ring
      have h4 := mul_le_mul_of_nonneg_right hΘ (by positivity : 0 ≤ c * τ / 4)
      have h5 : -(Real.pi ^ 2 * c) * τ / (L : ℝ) ^ 2 = -(Real.pi ^ 2 * c * τ / (L : ℝ) ^ 2) := by ring
      rw [h5, ← h3]
      nlinarith
    have h6 : 0 ≤ Real.exp (-(c * τ / 4) * Θ) := (Real.exp_pos _).le
    calc |F k| ≤ q k * Real.exp (-(c * τ) * Θ) := hF k hk0
      _ = (q k * Real.exp (-(c * τ) * Θ / 2)) * Real.exp (-(c * τ / 4) * Θ)
            * Real.exp (-(c * τ / 4) * Θ) := by rw [h1]; ring
      _ ≤ (A * ((L : ℝ)⁻¹) ^ ν) * Real.exp (-(Real.pi ^ 2 * c) * τ / (L : ℝ) ^ 2)
            * Real.exp (-(c * τ / 4) * Θ) := by
        refine mul_le_mul (mul_le_mul (hq k hk0) h2 h6 (by positivity)) le_rfl h6 (by positivity)
      _ = M * Real.exp (-(c * τ / 4) * Θ) := by rw [hM]
  have hsum1 : ∑ k ∈ (Finset.univ : Finset (Zd d L)).erase 0, |F k|
      ≤ ∑ k ∈ (Finset.univ : Finset (Zd d L)).erase 0, M * Real.exp (-(c * τ / 4) * BAthetaSq d L k) :=
    Finset.sum_le_sum hpt
  have hsum2 : ∑ k ∈ (Finset.univ : Finset (Zd d L)).erase 0, M * Real.exp (-(c * τ / 4) * BAthetaSq d L k)
      ≤ ∑ k : Zd d L, M * Real.exp (-(c * τ / 4) * BAthetaSq d L k) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun _ _ _ => by positivity)
  have hprod := KHeat_prod_sum (d := d) (L := L) (c * τ / 4)
  have h1D : ∑ x : ZMod L, Real.exp (-(c * τ / 4) * (2 * Real.pi * (zdist L x : ℝ) / L) ^ 2)
      ≤ KHeat_T1 c := by
    have hρ : Real.pi ^ 2 * c ≤ Real.pi ^ 2 * c * τ / (L : ℝ) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have : 0 ≤ Real.pi ^ 2 * c := by positivity
      nlinarith
    have hρ0 : 0 < Real.pi ^ 2 * c := by positivity
    have hs := KHeat_sum_gauss (L := L) hρ0 hρ
    have heq : ∀ x : ZMod L, Real.exp (-(c * τ / 4) * (2 * Real.pi * (zdist L x : ℝ) / L) ^ 2)
        = Real.exp (-(Real.pi ^ 2 * c * τ / (L : ℝ) ^ 2) * (zdist L x : ℝ) ^ 2) := by
      intro x
      congr 1
      field_simp
      ring
    simp_rw [heq]
    exact hs
  have hpow : (∑ x : ZMod L, Real.exp (-(c * τ / 4) * (2 * Real.pi * (zdist L x : ℝ) / L) ^ 2)) ^ d
      ≤ KHeat_T1 c ^ d :=
    pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) h1D d
  calc ∑ k ∈ (Finset.univ : Finset (Zd d L)).erase 0, |F k|
      ≤ ∑ k : Zd d L, M * Real.exp (-(c * τ / 4) * BAthetaSq d L k) := hsum1.trans hsum2
    _ = M * ∑ k : Zd d L, Real.exp (-(c * τ / 4) * BAthetaSq d L k) := by rw [← Finset.mul_sum]
    _ = M * (∑ x : ZMod L, Real.exp (-(c * τ / 4) * (2 * Real.pi * (zdist L x : ℝ) / L) ^ 2)) ^ d := by
        rw [hprod]
    _ ≤ M * KHeat_T1 c ^ d := mul_le_mul_of_nonneg_left hpow hM0

end Gap

/-! ## 8. Targets: regime (ii) `τ ≥ L²` -/

section GapTarget

private theorem KHeat_kBA_chi {d L : ℕ} [NeZero L] (g E : ℝ) (m : ℂ) (hg : 0 < g) (τ : ℝ)
    (b : Zd d L) :
    kBA d L g E m τ b = ((L : ℝ) ^ d)⁻¹ * ∑ k : Zd d L,
      Real.exp (-(τ / g ^ 2) * (1 - BAKhat d L g E m k)) * (KHeat_chi d L k b).re := by
  rw [kBA_fourier d L g E m hg τ b]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [KHeat_chi_re]
  rfl

private theorem KHeat_fin {LL X e P A C : ℝ} (hLL : 0 ≤ LL) (hX : 0 ≤ X) (he : 0 ≤ e) (hP : 0 ≤ P)
    (hAP : A * P ≤ C) : LL * (A * X * e * P) ≤ C * (LL * X) * e := by
  have h1 : LL * (A * X * e * P) = (A * P) * (LL * X * e) := by ring
  rw [h1]
  calc (A * P) * (LL * X * e) ≤ C * (LL * X * e) :=
        mul_le_mul_of_nonneg_right hAP (by positivity)
    _ = C * (LL * X) * e := by ring

private theorem KHeat_thetaSq_nonneg {d L : ℕ} (k : Zd d L) : 0 ≤ BAthetaSq d L k :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Regime (ii) `τ ≥ L²`** (twin of `kProd_gap`, `HeatProduct.lean:626`, verbatim with `kProd d L τ ↦ kBA d L g E m τ`;
supervisor 1048 C1 (ii), O1). -/
theorem kBA_gap : ∀ d : ℕ, 0 < d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ τ : ℝ, (L : ℝ) ^ 2 ≤ τ → ∀ (a : Zd d L) (i j : Fin d),
        |kBA d L g E m τ a - ((L : ℝ) ^ d)⁻¹| ≤ C * ((L : ℝ) ^ d)⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2) ∧
        |kBA d L g E m τ (a + Pi.single j 1) - kBA d L g E m τ a|
          ≤ C * ((L : ℝ) ^ (d + 1))⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2) ∧
        |kBA d L g E m τ (a + Pi.single i 1 + Pi.single j 1) - kBA d L g E m τ (a + Pi.single i 1)
            - kBA d L g E m τ (a + Pi.single j 1) + kBA d L g E m τ a|
          ≤ C * ((L : ℝ) ^ (d + 2))⁻¹ * Real.exp (-c * τ / (L : ℝ) ^ 2) := by
  intro d hd Λ κ hΛ hκ
  obtain ⟨c₀, hc₀, hgap⟩ := BAK_gap d hd Λ κ hΛ hκ
  have hT1 : 1 ≤ KHeat_T1 c₀ := KHeat_T1_ge_one hc₀
  have hTd : 1 ≤ KHeat_T1 c₀ ^ d := one_le_pow₀ hT1
  set Kc : ℝ := 1 + (1 / c₀ + 1) + 2 / c₀ with hKc
  refine ⟨KHeat_T1 c₀ ^ d * Kc, Real.pi ^ 2 * c₀, by positivity, by positivity, ?_⟩
  intro L _ hL g E m hg hgΛ hr τ hτ a i j
  have hLpos : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  have hτ0 : 0 ≤ τ := le_trans (by positivity) hτ
  set LL : ℝ := ((L : ℝ) ^ d)⁻¹ with hLL
  have hLL0 : 0 < LL := by positivity
  set e : ℝ := Real.exp (-(Real.pi ^ 2 * c₀) * τ / (L : ℝ) ^ 2) with he
  have he0 : 0 < e := Real.exp_pos _
  set T : ℝ := KHeat_T1 c₀ with hT
  set μ : Zd d L → ℝ := fun k => Real.exp (-(τ / g ^ 2) * (1 - BAKhat d L g E m k)) with hμ
  have hμ_le : ∀ k, μ k ≤ Real.exp (-(c₀ * τ) * BAthetaSq d L k) :=
    fun k => KHeat_mu_le hg hτ0 (hgap L hL g E m hg hgΛ hr k)
  have hμ0 : ∀ k, 0 ≤ μ k := fun k => (Real.exp_pos _).le
  have hrepr : ∀ b : Zd d L, kBA d L g E m τ b = LL * ∑ k, μ k * (KHeat_chi d L k b).re :=
    fun b => KHeat_kBA_chi g E m hg τ b
  have hchi0 : ∀ b : Zd d L, KHeat_chi d L 0 b = 1 := fun b => KHeat_chi_zero_left d L b
  have hμ_zero : μ 0 = 1 := by
    simp only [hμ, KHeat_Khat_zero g E m hr.1]
    simp
  have hsplit : ∀ f : Zd d L → ℝ, ∑ k, f k = f 0 + ∑ k ∈ Finset.univ.erase 0, f k := fun f =>
    (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
  have hq0 : ∀ k : Zd d L, 0 ≤ BAthetaSq d L k := fun k => KHeat_thetaSq_nonneg k
  have hcast : ∀ ν : ℕ, ((L : ℝ) ^ (d + ν))⁻¹ = LL * ((L : ℝ)⁻¹) ^ ν := by
    intro ν
    rw [pow_add, mul_inv, inv_pow, hLL]
  have hc1 : 0 ≤ 1 / c₀ + 1 := by positivity
  have hc2 : 0 ≤ 2 / c₀ := by positivity
  have hTd0 : 0 ≤ T ^ d := by positivity
  have hLi : 0 ≤ (L : ℝ)⁻¹ := by positivity
  refine ⟨?_, ?_, ?_⟩
  · -- the zero mode and the gap
    have hsum : kBA d L g E m τ a - LL
        = LL * ∑ k ∈ Finset.univ.erase 0, μ k * (KHeat_chi d L k a).re := by
      rw [hrepr a, hsplit, hμ_zero, hchi0]
      simp only [Complex.one_re, one_mul]
      ring
    rw [hsum, abs_mul, abs_of_pos hLL0]
    have hm := KHeat_master (d := d) (L := L) hc₀ hτ (ν := 0) (A := 1) zero_le_one
      (fun k => μ k * (KHeat_chi d L k a).re) (fun _ => 1)
      (fun k _ => by
        rw [abs_mul, abs_of_nonneg (hμ0 k), one_mul]
        calc μ k * |(KHeat_chi d L k a).re| ≤ μ k * 1 :=
              mul_le_mul_of_nonneg_left
                ((Complex.abs_re_le_norm _).trans (KHeat_chi_norm d L k a).le) (hμ0 k)
          _ ≤ _ := by rw [mul_one]; exact hμ_le k)
      (fun k _ => by
        rw [one_mul, pow_zero, mul_one]
        refine Real.exp_le_one_iff.mpr ?_
        have := hq0 k
        have : 0 ≤ c₀ * τ * BAthetaSq d L k / 2 := by positivity
        linarith)
    calc LL * |∑ k ∈ Finset.univ.erase 0, μ k * (KHeat_chi d L k a).re|
        ≤ LL * ∑ k ∈ Finset.univ.erase 0, |μ k * (KHeat_chi d L k a).re| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hLL0.le
      _ ≤ LL * (1 * ((L : ℝ)⁻¹) ^ 0 * e * T ^ d) := mul_le_mul_of_nonneg_left hm hLL0.le
      _ ≤ T ^ d * Kc * LL * e := by
        have := KHeat_fin (LL := LL) (X := ((L : ℝ)⁻¹) ^ 0) (e := e) (P := T ^ d) (A := 1)
          (C := T ^ d * Kc) hLL0.le (by positivity) he0.le hTd0 (by rw [hKc]; nlinarith)
        simpa using this
  · -- first difference
    set F : Zd d L → ℝ := fun k =>
      μ k * ((KHeat_chi d L k (a + Pi.single j 1)).re - (KHeat_chi d L k a).re) with hF
    have hF0 : F 0 = 0 := by simp [hF, hchi0]
    have hsum : kBA d L g E m τ (a + Pi.single j 1) - kBA d L g E m τ a
        = LL * ∑ k ∈ Finset.univ.erase 0, F k := by
      rw [hrepr, hrepr a, ← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      have h1 : ∑ k, (μ k * (KHeat_chi d L k (a + Pi.single j 1)).re
          - μ k * (KHeat_chi d L k a).re) = ∑ k, F k :=
        Finset.sum_congr rfl fun k _ => by simp only [hF]; ring
      rw [h1, hsplit F, hF0, zero_add]
    rw [hsum, abs_mul, abs_of_pos hLL0]
    have hm := KHeat_master (d := d) (L := L) hc₀ hτ (ν := 1) (A := 1 / c₀ + 1) hc1 F
      (fun k => 2 * Real.pi * (zdist L (k j) : ℝ) / L)
      (fun k _ => by
        simp only [hF]
        rw [abs_mul, abs_of_nonneg (hμ0 k)]
        calc μ k * |(KHeat_chi d L k (a + Pi.single j 1)).re - (KHeat_chi d L k a).re|
            ≤ μ k * (2 * Real.pi * (zdist L (k j) : ℝ) / L) :=
              mul_le_mul_of_nonneg_left (KHeat_diff1 k a j) (hμ0 k)
          _ ≤ Real.exp (-(c₀ * τ) * BAthetaSq d L k) * (2 * Real.pi * (zdist L (k j) : ℝ) / L) :=
              mul_le_mul_of_nonneg_right (hμ_le k) (by positivity)
          _ = _ := mul_comm _ _)
      (fun k _ => by
        have := KHeat_poly1 (L := L) hc₀ hτ (y := 2 * Real.pi * (zdist L (k j) : ℝ) / L)
          (Θ := BAthetaSq d L k) (by positivity) (KHeat_theta_sq_le k j)
        rwa [pow_one])
    rw [hcast 1]
    calc LL * |∑ k ∈ Finset.univ.erase 0, F k|
        ≤ LL * ∑ k ∈ Finset.univ.erase 0, |F k| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hLL0.le
      _ ≤ LL * ((1 / c₀ + 1) * ((L : ℝ)⁻¹) ^ 1 * e * T ^ d) := mul_le_mul_of_nonneg_left hm hLL0.le
      _ ≤ _ := KHeat_fin hLL0.le (by positivity) he0.le hTd0 (by rw [hKc]; nlinarith)
  · -- second difference
    set F : Zd d L → ℝ := fun k =>
      μ k * ((KHeat_chi d L k (a + Pi.single i 1 + Pi.single j 1)).re
        - (KHeat_chi d L k (a + Pi.single i 1)).re - (KHeat_chi d L k (a + Pi.single j 1)).re
        + (KHeat_chi d L k a).re) with hF
    have hF0 : F 0 = 0 := by simp [hF, hchi0]
    have hsum : kBA d L g E m τ (a + Pi.single i 1 + Pi.single j 1)
          - kBA d L g E m τ (a + Pi.single i 1) - kBA d L g E m τ (a + Pi.single j 1)
          + kBA d L g E m τ a = LL * ∑ k ∈ Finset.univ.erase 0, F k := by
      rw [hrepr, hrepr (a + Pi.single i 1), hrepr (a + Pi.single j 1), hrepr a, ← mul_sub,
        ← mul_sub, ← mul_add, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      congr 1
      have h1 : ∑ k, (μ k * (KHeat_chi d L k (a + Pi.single i 1 + Pi.single j 1)).re
          - μ k * (KHeat_chi d L k (a + Pi.single i 1)).re
          - μ k * (KHeat_chi d L k (a + Pi.single j 1)).re
          + μ k * (KHeat_chi d L k a).re) = ∑ k, F k :=
        Finset.sum_congr rfl fun k _ => by simp only [hF]; ring
      rw [h1, hsplit F, hF0, zero_add]
    rw [hsum, abs_mul, abs_of_pos hLL0]
    have hm := KHeat_master (d := d) (L := L) hc₀ hτ (ν := 2) (A := 2 / c₀) hc2 F
      (fun k => (2 * Real.pi * (zdist L (k i) : ℝ) / L) * (2 * Real.pi * (zdist L (k j) : ℝ) / L))
      (fun k _ => by
        simp only [hF]
        rw [abs_mul, abs_of_nonneg (hμ0 k)]
        calc μ k * |(KHeat_chi d L k (a + Pi.single i 1 + Pi.single j 1)).re
              - (KHeat_chi d L k (a + Pi.single i 1)).re
              - (KHeat_chi d L k (a + Pi.single j 1)).re + (KHeat_chi d L k a).re|
            ≤ μ k * ((2 * Real.pi * (zdist L (k i) : ℝ) / L)
                * (2 * Real.pi * (zdist L (k j) : ℝ) / L)) :=
              mul_le_mul_of_nonneg_left (KHeat_diff2 k a i j) (hμ0 k)
          _ ≤ Real.exp (-(c₀ * τ) * BAthetaSq d L k)
                * ((2 * Real.pi * (zdist L (k i) : ℝ) / L)
                  * (2 * Real.pi * (zdist L (k j) : ℝ) / L)) :=
              mul_le_mul_of_nonneg_right (hμ_le k) (by positivity)
          _ = _ := mul_comm _ _)
      (fun k _ => KHeat_poly2 (L := L) hc₀ hτ (by positivity) (KHeat_theta_mul_le k i j))
    rw [hcast 2]
    calc LL * |∑ k ∈ Finset.univ.erase 0, F k|
        ≤ LL * ∑ k ∈ Finset.univ.erase 0, |F k| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hLL0.le
      _ ≤ LL * (2 / c₀ * ((L : ℝ)⁻¹) ^ 2 * e * T ^ d) := mul_le_mul_of_nonneg_left hm hLL0.le
      _ ≤ _ := KHeat_fin hLL0.le (by positivity) he0.le hTd0 (by rw [hKc]; nlinarith)

end GapTarget

/-! ## 9. Target: the torus on-diagonal bound -/

section Diag

variable {L : ℕ} [NeZero L]

/-- `cos(2π u.val/L) = cos(2π |u|_L/L)` (port of `KSymbol_cos_zdist`, private in `KSymbol.lean:610`). -/
private theorem KHeat_cos_zdist (u : ZMod L) :
    Real.cos (2 * Real.pi * (u.val : ℝ) / L) = Real.cos (2 * Real.pi * (zdist L u : ℝ) / L) := by
  have hv : u.val < L := ZMod.val_lt u
  have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  by_cases h : u.val ≤ L - u.val
  · have : zdist L u = u.val := by simp only [zdist]; exact min_eq_left h
    rw [this]
  · have : zdist L u = L - u.val := by simp only [zdist]; exact min_eq_right (by omega)
    rw [this, Nat.cast_sub hv.le]
    have h2 : 2 * Real.pi * ((L : ℝ) - (u.val : ℝ)) / L = 2 * Real.pi - 2 * Real.pi * (u.val : ℝ) / L := by
      field_simp
    rw [h2, Real.cos_two_pi_sub]

/-- The Gaussian sum is dominated by the lattice heat kernel at the origin:
`1 - cos θ ≤ θ²/2` gives `e^{-wθ²} ≤ e^{-2w(1 - cos θ)}`. -/
private theorem KHeat_gauss_le_hkT {w : ℝ} (hw : 0 ≤ w) :
    (L : ℝ)⁻¹ * ∑ x : ZMod L, Real.exp (-w * (2 * Real.pi * (zdist L x : ℝ) / L) ^ 2)
      ≤ Heat.hkT L w 0 := by
  unfold Heat.hkT
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum fun k _ => ?_
  simp only [ZMod.val_zero, Nat.cast_zero, mul_zero, zero_div, Real.cos_zero, one_mul]
  refine Real.exp_le_exp.mpr ?_
  rw [KHeat_cos_zdist]
  have h := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * (zdist L k : ℝ) / L)
  nlinarith

/-- The 1D lattice heat kernel at the origin, all `w > 0`: `hk(w, 0) ≤ C₁ w^{-1/2} + C₂/L`
(`hkT_le` for `w ≤ L²`, `hkT_gap` for `w ≥ L²`). -/
private theorem KHeat_hkT_bound : ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
    ∀ (L : ℕ) [NeZero L] (w : ℝ), 0 < w →
      Heat.hkT L w 0 ≤ C₁ * w ^ (-(1 / 2 : ℝ)) + C₂ * (L : ℝ)⁻¹ := by
  obtain ⟨Ca, ca, hCa, hca, hle⟩ := Heat.hkT_le
  obtain ⟨Cg, cg, hCg, hcg, hgp⟩ := Heat.hkT_gap
  refine ⟨Ca, 1 + Cg, hCa.le, by linarith, ?_⟩
  intro L _ w hw
  have hLpos : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  have hLi : 0 ≤ (L : ℝ)⁻¹ := by positivity
  have hwp : 0 ≤ w ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hw.le _
  rcases le_total w ((L : ℝ) ^ 2) with h | h
  · have h1 := hle L w hw h 0
    have h2 : Real.exp (-ca * min ((zdist L (0 : ZMod L) : ℝ) ^ 2 / w) (zdist L (0 : ZMod L) : ℝ)) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      simp
    have h3 : Ca * min 1 (w ^ (-(1 / 2 : ℝ)))
        * Real.exp (-ca * min ((zdist L (0 : ZMod L) : ℝ) ^ 2 / w) (zdist L (0 : ZMod L) : ℝ))
        ≤ Ca * w ^ (-(1 / 2 : ℝ)) := by
      calc _ ≤ Ca * min 1 (w ^ (-(1 / 2 : ℝ))) * 1 :=
            mul_le_mul_of_nonneg_left h2 (mul_nonneg hCa.le (le_min zero_le_one hwp))
        _ ≤ Ca * w ^ (-(1 / 2 : ℝ)) := by
            rw [mul_one]
            exact mul_le_mul_of_nonneg_left (min_le_right _ _) hCa.le
    have h4 : 0 ≤ (1 + Cg) * (L : ℝ)⁻¹ := by positivity
    linarith
  · have h1 := (hgp L w h 0).1
    have h2 : Real.exp (-cg * w / (L : ℝ) ^ 2) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have : 0 ≤ cg * w / (L : ℝ) ^ 2 := by positivity
      have h5 : -cg * w / (L : ℝ) ^ 2 = -(cg * w / (L : ℝ) ^ 2) := by ring
      linarith
    have h3 : Cg * (L : ℝ)⁻¹ * Real.exp (-cg * w / (L : ℝ) ^ 2) ≤ Cg * (L : ℝ)⁻¹ := by
      calc _ ≤ Cg * (L : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := mul_one _
    have h4 := (le_abs_self _).trans (h1.trans h3)
    have h5 : 0 ≤ Ca * w ^ (-(1 / 2 : ℝ)) := mul_nonneg hCa.le hwp
    nlinarith

end Diag

section DiagTarget

/-- **Torus on-diagonal bound** (from `BAK_gap` and the 1D sums; the floor `L^{-d}` is harmless in regime (i)). -/
theorem kBA_diag_le : ∀ d : ℕ, 0 < d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ τ : ℝ, 0 < τ → ∀ a : Zd d L,
        kBA d L g E m τ a ≤ C * (min 1 (τ ^ (-(d : ℝ) / 2)) + ((L : ℝ) ^ d)⁻¹) := by
  intro d hd Λ κ hΛ hκ
  obtain ⟨c₀, hc₀, hgap⟩ := BAK_gap d hd Λ κ hΛ hκ
  obtain ⟨C₁, C₂, hC₁, hC₂, hhk⟩ := KHeat_hkT_bound
  set X : ℝ := C₁ * c₀ ^ (-(1 / 2 : ℝ)) with hX
  have hX0 : 0 ≤ X := by positivity
  set P : ℝ := 2 ^ d * X ^ d with hP
  set Q : ℝ := 2 ^ d * C₂ ^ d with hQ
  have hP0 : 0 ≤ P := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  refine ⟨max 1 (max P Q), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro L _ hL g E m hg hgΛ hr τ hτ a
  have hLpos : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  set LL : ℝ := ((L : ℝ) ^ d)⁻¹ with hLL
  have hLL0 : 0 < LL := by positivity
  have hone : kBA d L g E m τ a ≤ 1 := (kBA_basic d L g E m hg hr.1).2.2.1 τ hτ.le a
  -- the Fourier bound
  have hμ_le : ∀ k : Zd d L, Real.exp (-(τ / g ^ 2) * (1 - BAKhat d L g E m k))
      ≤ Real.exp (-(c₀ * τ) * BAthetaSq d L k) :=
    fun k => KHeat_mu_le hg hτ.le (hgap L hL g E m hg hgΛ hr k)
  have hF : kBA d L g E m τ a ≤ LL * ∑ k : Zd d L, Real.exp (-(c₀ * τ) * BAthetaSq d L k) := by
    rw [KHeat_kBA_chi g E m hg τ a]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) hLL0.le
    calc Real.exp (-(τ / g ^ 2) * (1 - BAKhat d L g E m k)) * (KHeat_chi d L k a).re
        ≤ Real.exp (-(τ / g ^ 2) * (1 - BAKhat d L g E m k)) * 1 :=
          mul_le_mul_of_nonneg_left
            ((Complex.re_le_norm _).trans (KHeat_chi_norm d L k a).le) (Real.exp_pos _).le
      _ ≤ _ := by rw [mul_one]; exact hμ_le k
  rw [KHeat_prod_sum] at hF
  have hLL' : LL = ((L : ℝ)⁻¹) ^ d := by rw [hLL, inv_pow]
  have hF2 : kBA d L g E m τ a ≤ (Heat.hkT L (c₀ * τ) 0) ^ d := by
    refine hF.trans ?_
    rw [hLL', ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (KHeat_gauss_le_hkT (by positivity)) d
  have hhk' := hhk L (c₀ * τ) (by positivity)
  rw [Real.mul_rpow hc₀.le hτ.le] at hhk'
  have hF3 : kBA d L g E m τ a ≤ (X * τ ^ (-(1 / 2 : ℝ)) + C₂ * (L : ℝ)⁻¹) ^ d := by
    refine hF2.trans (pow_le_pow_left₀ ?_ (by rw [hX]; linarith) d)
    exact (Heat.hkT_mass L (c₀ * τ) (by positivity)).1 0
  -- `(x + y)^d ≤ 2^d (x^d + y^d)`
  have hxy : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → (x + y) ^ d ≤ 2 ^ d * (x ^ d + y ^ d) := by
    intro x y hx hy
    have h1 : x + y ≤ 2 * max x y := by
      rcases le_total x y with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    calc (x + y) ^ d ≤ (2 * max x y) ^ d := pow_le_pow_left₀ (by positivity) h1 d
      _ = 2 ^ d * (max x y) ^ d := mul_pow _ _ _
      _ ≤ 2 ^ d * (x ^ d + y ^ d) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rcases le_total x y with h | h
        · rw [max_eq_right h]; have := pow_nonneg hx d; linarith
        · rw [max_eq_left h]; have := pow_nonneg hy d; linarith
  have hτd : (τ ^ (-(1 / 2 : ℝ))) ^ d = τ ^ (-(d : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hτ.le]
    congr 1
    ring
  have hF4 : kBA d L g E m τ a ≤ P * τ ^ (-(d : ℝ) / 2) + Q * LL := by
    have hx : (X * τ ^ (-(1 / 2 : ℝ))) ^ d = X ^ d * τ ^ (-(d : ℝ) / 2) := by rw [mul_pow, hτd]
    have hy : (C₂ * (L : ℝ)⁻¹) ^ d = C₂ ^ d * LL := by rw [mul_pow, hLL']
    refine hF3.trans ((hxy _ _ (by positivity) (by positivity)).trans (le_of_eq ?_))
    rw [hx, hy, hP, hQ]
    ring
  -- the two regimes in `τ`
  have hC1 : 1 ≤ max 1 (max P Q) := le_max_left _ _
  have hCP : P ≤ max 1 (max P Q) := (le_max_left P Q).trans (le_max_right _ _)
  have hCQ : Q ≤ max 1 (max P Q) := (le_max_right P Q).trans (le_max_right _ _)
  have hτp : 0 ≤ τ ^ (-(d : ℝ) / 2) := Real.rpow_nonneg hτ.le _
  rcases le_total τ 1 with h | h
  · have h1 : 1 ≤ τ ^ (-(d : ℝ) / 2) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hτ h (by
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        linarith)
    rw [min_eq_left h1]
    calc kBA d L g E m τ a ≤ 1 := hone
      _ ≤ max 1 (max P Q) * (1 + LL) := by nlinarith
  · have h1 : τ ^ (-(d : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos h (by
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        linarith)
    rw [min_eq_right h1]
    calc kBA d L g E m τ a ≤ P * τ ^ (-(d : ℝ) / 2) + Q * LL := hF4
      _ ≤ max 1 (max P Q) * (τ ^ (-(d : ℝ) / 2) + LL) := by
        nlinarith [mul_le_mul_of_nonneg_right hCP hτp, mul_le_mul_of_nonneg_right hCQ hLL0.le]

end DiagTarget

/-! ## 10. Compiled nonempty instances (`d = 3`, `L = 4`, `Λ = 10`, `κ = Im m₀`, flow point `P`) -/

namespace KHeatInst

open RBM.BA.MFixedPointInst

/-- `kBA` at `τ = 0` is `δ_0` (target `kBA_basic`, fourth clause). -/
theorem inst_zero_delta :
    ∀ a : Zd 3 4, kBA 3 4 P.g0 P.E P.m0 0 a = if a = 0 then 1 else 0 :=
  (kBA_basic 3 4 P.g0 P.E P.m0 P.g0_pos P.real.1).2.2.2.1

theorem inst_zero_origin : kBA 3 4 P.g0 P.E P.m0 0 0 = 1 := by
  rw [inst_zero_delta 0]
  simp

theorem inst_zero_off : kBA 3 4 P.g0 P.E P.m0 0 ![1, 0, 0] = 0 := by
  rw [inst_zero_delta]
  have : (![1, 0, 0] : Zd 3 4) ≠ 0 := by decide
  simp [this]

/-- `Σ_a kBA 1 a = 1` (target `kBA_basic`, mass one). -/
theorem inst_mass : ∑ a : Zd 3 4, kBA 3 4 P.g0 P.E P.m0 1 a = 1 :=
  (kBA_basic 3 4 P.g0 P.E P.m0 P.g0_pos P.real.1).2.1 1 zero_le_one

theorem inst_nonneg_le_one :
    0 ≤ kBA 3 4 P.g0 P.E P.m0 2 ![1, 0, 2] ∧ kBA 3 4 P.g0 P.E P.m0 2 ![1, 0, 2] ≤ 1 :=
  ⟨(kBA_basic 3 4 P.g0 P.E P.m0 P.g0_pos P.real.1).1 2 (by norm_num) _,
    (kBA_basic 3 4 P.g0 P.E P.m0 P.g0_pos P.real.1).2.2.1 2 (by norm_num) _⟩

theorem inst_even :
    kBA 3 4 P.g0 P.E P.m0 (1 / 2) (-(![1, 0, 2] : Zd 3 4)) = kBA 3 4 P.g0 P.E P.m0 (1 / 2) ![1, 0, 2] :=
  (kBA_basic 3 4 P.g0 P.E P.m0 P.g0_pos P.real.1).2.2.2.2.1 (1 / 2) ![1, 0, 2]

theorem inst_continuous : Continuous fun τ : ℝ => kBA 3 4 P.g0 P.E P.m0 τ ![1, 0, 2] :=
  (kBA_basic 3 4 P.g0 P.E P.m0 P.g0_pos P.real.1).2.2.2.2.2 ![1, 0, 2]

/-- Target `kBA_fourier` at `τ = 1`, `a = (1, 0, 2)`. -/
theorem inst_fourier :
    kBA 3 4 P.g0 P.E P.m0 1 ![1, 0, 2] = ((((4 : ℕ) : ℝ) ^ 3)⁻¹) * ∑ k : Zd 3 4,
      Real.exp (-(1 / P.g0 ^ 2) * (1 - BAKhat 3 4 P.g0 P.E P.m0 k)) *
        Real.cos (2 * Real.pi / ((4 : ℕ) : ℝ) * ∑ j, ((k j).val : ℝ) * ((((![1, 0, 2] : Zd 3 4)) j).val : ℝ)) :=
  kBA_fourier 3 4 P.g0 P.E P.m0 P.g0_pos 1 ![1, 0, 2]

/-- Target `BAP_semigroup_shift`: the semigroup at `s = 1/2`, `s' = 3/2`. -/
theorem inst_semigroup :
    BAP 3 4 P.g0 P.E P.m0 (1 / 2 + 3 / 2) 0 ![1, 0, 0]
      = ∑ c : Zd 3 4, BAP 3 4 P.g0 P.E P.m0 (1 / 2) 0 c * BAP 3 4 P.g0 P.E P.m0 (3 / 2) c ![1, 0, 0] :=
  (BAP_semigroup_shift 3 4 P.g0 P.E P.m0 P.real.1).1 (1 / 2) (3 / 2) (by norm_num) (by norm_num) 0 _

/-- Target `BAP_semigroup_shift`: translation invariance. -/
theorem inst_shift :
    BAP 3 4 P.g0 P.E P.m0 (1 / 2) ![1, 1, 0] ![0, 1, 2]
      = BAP 3 4 P.g0 P.E P.m0 (1 / 2) 0 (![0, 1, 2] - ![1, 1, 0]) :=
  (BAP_semigroup_shift 3 4 P.g0 P.E P.m0 P.real.1).2 (1 / 2) _ _

/-- Target `BATheta_eq_laplace_kBA` at `t = 1/2`, `a = (1, 0, 0)`. -/
theorem inst_laplace :
    BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false 0 ![1, 0, 0]
      = ((∫ u in Ioi (0 : ℝ), Real.exp (-(1 - 1 / 2) * u)
          * kBA 3 4 P.g0 P.E P.m0 (1 / 2 * P.g0 ^ 2 * u) ![1, 0, 0] : ℝ) : ℂ) :=
  BATheta_eq_laplace_kBA 3 4 (by norm_num) P.g0 P.E P.m0 (1 / 2) P.g0_pos P.real.1
    (by norm_num) (by norm_num) _

/-- Target `BATheta_eq_laplace_kBA` at `t = 3/4`, `a = 0`. -/
theorem inst_laplace_origin :
    BATheta 3 4 P.g0 P.E P.m0 (3 / 4) true false 0 0
      = ((∫ u in Ioi (0 : ℝ), Real.exp (-(1 - 3 / 4) * u)
          * kBA 3 4 P.g0 P.E P.m0 (3 / 4 * P.g0 ^ 2 * u) 0 : ℝ) : ℂ) :=
  BATheta_eq_laplace_kBA 3 4 (by norm_num) P.g0 P.E P.m0 (3 / 4) P.g0_pos P.real.1
    (by norm_num) (by norm_num) 0

/-- Target `kBA_diag_le` at `τ = 4`, `a = 0`, `Λ = 10`. -/
theorem inst_diag_le :
    ∃ C : ℝ, 0 < C ∧
      kBA 3 4 P.g0 P.E P.m0 4 0 ≤ C * (min 1 ((4 : ℝ) ^ (-((3 : ℕ) : ℝ) / 2)) + (((4 : ℕ) : ℝ) ^ 3)⁻¹) := by
  obtain ⟨C, hC, h⟩ := kBA_diag_le 3 (by norm_num) 10 P.m0.im (by norm_num) P.real.1.1
  exact ⟨C, hC, h 4 (by norm_num) P.g0 P.E P.m0 P.g0_pos P.g0_le P.real 4 (by norm_num) 0⟩

/-- Target `kBA_gap` at `τ = L² = 16`, `a = (1, 0, 2)`, `(i, j) = (0, 2)`. -/
theorem inst_gap :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      (|kBA 3 4 P.g0 P.E P.m0 16 ![1, 0, 2] - (((4 : ℕ) : ℝ) ^ 3)⁻¹|
          ≤ C * (((4 : ℕ) : ℝ) ^ 3)⁻¹ * Real.exp (-c * 16 / ((4 : ℕ) : ℝ) ^ 2) ∧
        |kBA 3 4 P.g0 P.E P.m0 16 (![1, 0, 2] + Pi.single 2 1) - kBA 3 4 P.g0 P.E P.m0 16 ![1, 0, 2]|
          ≤ C * (((4 : ℕ) : ℝ) ^ (3 + 1))⁻¹ * Real.exp (-c * 16 / ((4 : ℕ) : ℝ) ^ 2) ∧
        |kBA 3 4 P.g0 P.E P.m0 16 (![1, 0, 2] + Pi.single 0 1 + Pi.single 2 1)
            - kBA 3 4 P.g0 P.E P.m0 16 (![1, 0, 2] + Pi.single 0 1)
            - kBA 3 4 P.g0 P.E P.m0 16 (![1, 0, 2] + Pi.single 2 1)
            + kBA 3 4 P.g0 P.E P.m0 16 ![1, 0, 2]|
          ≤ C * (((4 : ℕ) : ℝ) ^ (3 + 2))⁻¹ * Real.exp (-c * 16 / ((4 : ℕ) : ℝ) ^ 2)) := by
  obtain ⟨C, c, hC, hc, h⟩ := kBA_gap 3 (by norm_num) 10 P.m0.im (by norm_num) P.real.1.1
  exact ⟨C, c, hC, hc, h 4 (by norm_num) P.g0 P.E P.m0 P.g0_pos P.g0_le P.real 16 (by norm_num)
    _ 0 2⟩

/-- Target `kBA_gap` at `τ = 32 = 2L²`, the diagonal direction `(i, j) = (1, 1)`. -/
theorem inst_gap_diag :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      |kBA 3 4 P.g0 P.E P.m0 32 (0 + Pi.single 1 1 + Pi.single 1 1)
          - kBA 3 4 P.g0 P.E P.m0 32 (0 + Pi.single 1 1) - kBA 3 4 P.g0 P.E P.m0 32 (0 + Pi.single 1 1)
          + kBA 3 4 P.g0 P.E P.m0 32 0|
        ≤ C * (((4 : ℕ) : ℝ) ^ (3 + 2))⁻¹ * Real.exp (-c * 32 / ((4 : ℕ) : ℝ) ^ 2) := by
  obtain ⟨C, c, hC, hc, h⟩ := kBA_gap 3 (by norm_num) 10 P.m0.im (by norm_num) P.real.1.1
  exact ⟨C, c, hC, hc, (h 4 (by norm_num) P.g0 P.E P.m0 P.g0_pos P.g0_le P.real 32 (by norm_num)
    0 1 1).2.2⟩

end KHeatInst

end RBM.BA

end
