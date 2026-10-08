/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.KHeatTail
import Mathlib.Algebra.Group.ForwardDiff

/-!
# Unit differences of the heat kernel `kBA`: polynomial decay in regime (i) (BA-P4c)

Ticket T2336 (BA stage P, row P4c; supervisor 2026-10-08-1048 C4, O2).  Targets: `kBA_diff1_le`, `kBA_diff2_le`
(`τ ≤ L²`, `M = ⌊d/2⌋ + 1`, `max τ 1` in the decay factor) and the public symbol regularity `BAKhat_diff_le`.

Route.  `1 ≤ τ ≤ L²`: by the torus Fourier form `kBA_fourier`, `Δ_j^R` of the summand `A(k) Π_u (χ_k(e_{i_u}) - 1)`,
`A = e^{-(τ/g²)(1 - K̂)}`, is bounded by the *geometric calculus* of §1 (bounds `‖Δ^i φ(l)‖ ≤ B ρ^i` are stable under
products by induction on the order, under powers, and under `exp` by `n^i ≤ i! e^n`; no Faà di Bruno formula).  The
symbol has `|Δ_j^i K̂| ≤ C g² L^{-i}` and `|Δ_j K̂| ≤ C g² L^{-1} (|θ_k| + L^{-1})` (`BAKhat_diff_le`, from the moments
`Σ_a K_{0a} |a|^q ≤ C g²`, `BAK_exp_moment_le`), so each difference gains `√τ/L` (§5).  Summation by parts of order
`2M` in the direction of the largest coordinate of `a` (§6) gives `τ^{-(d+n)/2} (τ/|a|²)^M`; no summation by parts gives
`τ^{-(d+n)/2}` for `|a|² ≤ τ` (§7).  `0 < τ ≤ 1`: the merged tail bound `kBA_le` (`BA/KHeatTail`, T2335) and
`e^{-c r} ≤ C (1 + r²)^{-M}` (§8).  Imports beyond `BA/KHeat`: `BA/KHeatTail`, `Mathlib.Algebra.Group.ForwardDiff`.
Ports of private lemmas of merged RBM3D files (nothing from `../RBM1D`, `../RBM2D`): `KHeat.lean` `KHeat_chi` `:180`,
`KHeat_chi_eq` `:186`, `KHeat_char_sub_one` `:812`, `KHeat_mu_le` `:728`, `KHeat_theta_sq_le` `:713`, `KHeat_cos_zdist`
`:1149`, `KHeat_prod_sum` `:681`, `KHeat_gauss_le_hkT` `:1164`; `KHeatTail.lean:50` (`zdist_natCast`);
`KSymbol.lean:700` (`BAK_second_moment`, for all moments).
-/


set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.BA

open RBM RBM.Gauss

/-! ## 1. Finite differences of sequences with geometric bounds -/

section Diff

/-- Geometric bounds for the iterated forward differences of a complex sequence on the window `l + i ≤ R`. -/
private def KHeatDiff_Geo (R : ℕ) (B ρ : ℝ) (φ : ℕ → ℂ) : Prop :=
  ∀ i ≤ R, ∀ l : ℕ, l + i ≤ R → ‖(fwdDiff (1 : ℕ))^[i] φ l‖ ≤ B * ρ ^ i

/-- The product rule for geometric bounds (induction on the order, no binomial sums). -/
private theorem KHeatDiff_Geo_mul : ∀ (i R : ℕ) (φ ψ : ℕ → ℂ) (B B' ρ ρ' : ℝ),
    (∀ a ≤ i, ∀ l : ℕ, l + a ≤ R → ‖(fwdDiff (1 : ℕ))^[a] φ l‖ ≤ B * ρ ^ a) →
    (∀ a ≤ i, ∀ l : ℕ, l + a ≤ R → ‖(fwdDiff (1 : ℕ))^[a] ψ l‖ ≤ B' * ρ' ^ a) →
    ∀ l : ℕ, l + i ≤ R → ‖(fwdDiff (1 : ℕ))^[i] (fun x => φ x * ψ x) l‖ ≤ B * B' * (ρ + ρ') ^ i := by
  intro i
  induction i with
  | zero =>
    intro R φ ψ B B' ρ ρ' hφ hψ l hl
    have h1 := hφ 0 le_rfl l hl
    have h2 := hψ 0 le_rfl l hl
    simp only [Function.iterate_zero, id_eq, pow_zero, mul_one] at h1 h2 ⊢
    rw [norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  | succ i ih =>
    intro R φ ψ B B' ρ ρ' hφ hψ l hl
    rcases R with _ | R
    · omega
    have hsplit : (fwdDiff (1 : ℕ)) (fun x => φ x * ψ x)
        = (fun x => (fwdDiff (1 : ℕ) φ x) * ψ (x + 1)) + (fun x => φ x * (fwdDiff (1 : ℕ) ψ x)) := by
      funext x
      simp only [fwdDiff, Pi.add_apply]
      ring
    rw [Function.iterate_succ_apply, hsplit, fwdDiff_iter_add, Pi.add_apply]
    have hφ1 : ∀ a ≤ i, ∀ l : ℕ, l + a ≤ R →
        ‖(fwdDiff (1 : ℕ))^[a] (fwdDiff (1 : ℕ) φ) l‖ ≤ (B * ρ) * ρ ^ a := by
      intro a ha l hl'
      rw [← Function.iterate_succ_apply]
      have := hφ (a + 1) (by omega) l (by omega)
      calc _ ≤ B * ρ ^ (a + 1) := this
        _ = _ := by ring
    have hψ1 : ∀ a ≤ i, ∀ l : ℕ, l + a ≤ R →
        ‖(fwdDiff (1 : ℕ))^[a] (fun x => ψ (x + 1)) l‖ ≤ B' * ρ' ^ a := by
      intro a ha l hl'
      rw [fwdDiff_iter_comp_add]
      exact hψ a (by omega) (l + 1) (by omega)
    have hφ0 : ∀ a ≤ i, ∀ l : ℕ, l + a ≤ R → ‖(fwdDiff (1 : ℕ))^[a] φ l‖ ≤ B * ρ ^ a :=
      fun a ha l hl' => hφ a (by omega) l (by omega)
    have hψ2 : ∀ a ≤ i, ∀ l : ℕ, l + a ≤ R →
        ‖(fwdDiff (1 : ℕ))^[a] (fwdDiff (1 : ℕ) ψ) l‖ ≤ (B' * ρ') * ρ' ^ a := by
      intro a ha l hl'
      rw [← Function.iterate_succ_apply]
      have := hψ (a + 1) (by omega) l (by omega)
      calc _ ≤ B' * ρ' ^ (a + 1) := this
        _ = _ := by ring
    have e1 := ih R (fwdDiff (1 : ℕ) φ) (fun x => ψ (x + 1)) (B * ρ) B' ρ ρ' hφ1 hψ1 l (by omega)
    have e2 := ih R φ (fwdDiff (1 : ℕ) ψ) B (B' * ρ') ρ ρ' hφ0 hψ2 l (by omega)
    calc _ ≤ ‖(fwdDiff (1 : ℕ))^[i] (fun x => (fwdDiff (1 : ℕ) φ x) * ψ (x + 1)) l‖
          + ‖(fwdDiff (1 : ℕ))^[i] (fun x => φ x * (fwdDiff (1 : ℕ) ψ x)) l‖ := norm_add_le _ _
      _ ≤ B * ρ * B' * (ρ + ρ') ^ i + B * (B' * ρ') * (ρ + ρ') ^ i := add_le_add e1 e2
      _ = B * B' * (ρ + ρ') ^ (i + 1) := by ring

/-- Powers: `φⁿ` is geometric with `(Bⁿ, nρ)`. -/
private theorem KHeatDiff_Geo_pow {R : ℕ} {B ρ : ℝ} {φ : ℕ → ℂ} (h : KHeatDiff_Geo R B ρ φ) (n : ℕ) :
    KHeatDiff_Geo R (B ^ n) ((n : ℝ) * ρ) (fun l => φ l ^ n) := by
  induction n with
  | zero =>
    intro i hi l hl
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    cases i with
    | zero => simp
    | succ i =>
      have h0 : (fwdDiff (1 : ℕ)) (fun _ : ℕ => (1 : ℂ)) = fun _ => 0 := fwdDiff_const (1 : ℕ) (1 : ℂ)
      have h1 : (fwdDiff (1 : ℕ))^[i] (fun _ : ℕ => (0 : ℂ)) = fun _ => 0 :=
        Function.iterate_fixed (fwdDiff_const (1 : ℕ) (0 : ℂ)) i
      rw [Function.iterate_succ_apply, h0, h1]
      simp
  | succ n ih =>
    intro i hi l hl
    have hm := KHeatDiff_Geo_mul i R φ (fun l => φ l ^ n) B (B ^ n) ρ ((n : ℝ) * ρ)
      (fun a ha l hl' => h a (by omega) l hl') (fun a ha l hl' => ih a (by omega) l hl') l hl
    have e1 : (fun x => φ x * φ x ^ n) = (fun l => φ l ^ (n + 1)) := by
      funext x; rw [pow_succ']
    rw [e1] at hm
    calc _ ≤ B * B ^ n * (ρ + (n : ℝ) * ρ) ^ i := hm
      _ = B ^ (n + 1) * (((n + 1 : ℕ) : ℝ) * ρ) ^ i := by
        rw [pow_succ']; push_cast; ring_nf

/-- The exponential of a sequence with geometric bounds: `‖Δ^i e^φ‖ ≤ i! ρ^i e^{eB}`. -/
private theorem KHeatDiff_Geo_exp {R : ℕ} {B ρ : ℝ} {φ : ℕ → ℂ} (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (h : KHeatDiff_Geo R B ρ φ) (i : ℕ) (hi : i ≤ R) (l : ℕ) (hl : l + i ≤ R) :
    ‖(fwdDiff (1 : ℕ))^[i] (fun x => Complex.exp (φ x)) l‖
      ≤ (i.factorial : ℝ) * ρ ^ i * Real.exp (B * Real.exp 1) := by
  have hpow := fun n => KHeatDiff_Geo_pow h n i hi l hl
  have hexp : ∀ x : ℕ, HasSum (fun n : ℕ => φ x ^ n / (n.factorial : ℂ)) (Complex.exp (φ x)) := by
    intro x
    have := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) (φ x)
    rwa [← Complex.exp_eq_exp_ℂ] at this
  have hsum : HasSum (fun n : ℕ => (fwdDiff (1 : ℕ))^[i] (fun x => φ x ^ n) l / (n.factorial : ℂ))
      ((fwdDiff (1 : ℕ))^[i] (fun x => Complex.exp (φ x)) l) := by
    rw [fwdDiff_iter_eq_sum_shift]
    have hs := hasSum_sum (s := Finset.range (i + 1))
      (f := fun (q : ℕ) (n : ℕ) => ((-1 : ℤ) ^ (i - q) * (i.choose q : ℤ)) • (φ (l + q • (1 : ℕ)) ^ n / (n.factorial : ℂ)))
      (a := fun q => ((-1 : ℤ) ^ (i - q) * (i.choose q : ℤ)) • Complex.exp (φ (l + q • (1 : ℕ))))
      (fun q _ => (hexp (l + q • (1 : ℕ))).const_smul _)
    convert hs using 1
    funext n
    rw [fwdDiff_iter_eq_sum_shift, Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [smul_div_assoc]
  have hB1 : 0 ≤ B * Real.exp 1 := by positivity
  have hg : HasSum (fun n : ℕ => ((i.factorial : ℝ) * ρ ^ i) * ((B * Real.exp 1) ^ n / (n.factorial : ℝ)))
      ((i.factorial : ℝ) * ρ ^ i * Real.exp (B * Real.exp 1)) := by
    have := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (B * Real.exp 1)
    rw [← Real.exp_eq_exp_ℝ] at this
    exact this.mul_left _
  refine hsum.norm_le_of_bounded hg (fun n => ?_)
  have hn : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  rw [norm_div, Complex.norm_natCast]
  rw [div_le_iff₀ hn]
  have h1 := hpow n
  have h2 : ‖(fwdDiff (1 : ℕ))^[i] (fun x => φ x ^ n) l‖ ≤ B ^ n * ((n : ℝ) * ρ) ^ i := h1
  have h3 : ((n : ℝ)) ^ i ≤ (i.factorial : ℝ) * Real.exp (n : ℝ) := by
    have := Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) i
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have h4 : Real.exp (n : ℝ) = Real.exp 1 ^ n := by
    rw [← Real.exp_nat_mul, mul_one]
  calc ‖(fwdDiff (1 : ℕ))^[i] (fun x => φ x ^ n) l‖ ≤ B ^ n * ((n : ℝ) * ρ) ^ i := h2
    _ = B ^ n * (n : ℝ) ^ i * ρ ^ i := by rw [mul_pow]; ring
    _ ≤ B ^ n * ((i.factorial : ℝ) * Real.exp 1 ^ n) * ρ ^ i := by
        rw [← h4]
        gcongr
    _ = (i.factorial : ℝ) * ρ ^ i * ((B * Real.exp 1) ^ n / (n.factorial : ℝ)) * (n.factorial : ℝ) := by
        rw [mul_pow]; field_simp

end Diff

/-! ## 2. The characters of `ℤ_L^d` and the unit circle estimates -/

section Char

variable {d L : ℕ} [NeZero L]

/-- The additive character `χ_k(a) = exp(2πi/L Σ_j k_j a_j)` of `ℤ_L^d` (port of the private `KHeat_chi`,
`KHeat.lean:180`). -/
private def KHeatDiff_chi (k a : Zd d L) : ℂ := ZMod.stdAddChar (∑ j, k j * a j)

private theorem KHeatDiff_chi_eq (k a : Zd d L) :
    KHeatDiff_chi k a
      = Complex.exp (2 * Real.pi * Complex.I / L * ∑ j, ((k j).val : ℂ) * ((a j).val : ℂ)) := by
  unfold KHeatDiff_chi
  have h1 : (∑ j, k j * a j : ZMod L) = (((∑ j, (k j).val * (a j).val : ℕ) : ℤ) : ZMod L) := by
    push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
  rw [h1, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

private theorem KHeatDiff_chi_add_k (k k' a : Zd d L) :
    KHeatDiff_chi (k + k') a = KHeatDiff_chi k a * KHeatDiff_chi k' a := by
  unfold KHeatDiff_chi
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem KHeatDiff_chi_add_a (k a b : Zd d L) :
    KHeatDiff_chi k (a + b) = KHeatDiff_chi k a * KHeatDiff_chi k b := by
  unfold KHeatDiff_chi
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem KHeatDiff_chi_zero_k (a : Zd d L) : KHeatDiff_chi 0 a = 1 := by
  simp [KHeatDiff_chi]

private theorem KHeatDiff_chi_nsmul_k (n : ℕ) (k a : Zd d L) :
    KHeatDiff_chi (n • k) a = KHeatDiff_chi k a ^ n := by
  induction n with
  | zero => rw [zero_smul, KHeatDiff_chi_zero_k, pow_zero]
  | succ n ih => rw [succ_nsmul, KHeatDiff_chi_add_k, ih, pow_succ]

private theorem KHeatDiff_chi_norm (k a : Zd d L) : ‖KHeatDiff_chi k a‖ = 1 := by
  unfold KHeatDiff_chi
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

private theorem KHeatDiff_chi_single_a (k : Zd d L) (j : Fin d) :
    KHeatDiff_chi k (Pi.single j 1) = ZMod.stdAddChar (k j) := by
  unfold KHeatDiff_chi
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Pi.single_eq_of_ne hij]
  · intro h
    exact absurd (Finset.mem_univ j) h

private theorem KHeatDiff_chi_single_k (j : Fin d) (a : Zd d L) :
    KHeatDiff_chi (Pi.single j 1) a = ZMod.stdAddChar (a j) := by
  rw [show KHeatDiff_chi (Pi.single j 1) a = KHeatDiff_chi a (Pi.single j 1) by
    unfold KHeatDiff_chi; simp only [mul_comm], KHeatDiff_chi_single_a]

private theorem KHeatDiff_valMinAbs_abs (y : ZMod L) : |(y.valMinAbs : ℝ)| = (zdist L y : ℝ) := by
  have h := ZMod.valMinAbs_natAbs_eq_min y
  rw [← Int.cast_abs, Int.abs_eq_natAbs]
  simp only [zdist]
  exact_mod_cast h

private theorem KHeatDiff_std_exp (n : ℤ) :
    ZMod.stdAddChar (n : ZMod L) = Complex.exp (Complex.I * ((2 * Real.pi * (n : ℝ) / L : ℝ) : ℂ)) := by
  rw [ZMod.stdAddChar_coe]; congr 1; push_cast; ring

private theorem KHeatDiff_std_vma (y : ZMod L) :
    ZMod.stdAddChar y = Complex.exp (Complex.I * ((2 * Real.pi * (y.valMinAbs : ℝ) / L : ℝ) : ℂ)) := by
  rw [← KHeatDiff_std_exp, ZMod.coe_valMinAbs]

/-- `|e^{2πi y/L} - 1| ≤ 2π |y|_L / L` (port of `KHeat_char_sub_one`, `KHeat.lean:812`). -/
private theorem KHeatDiff_char_sub_one (y : ZMod L) :
    ‖ZMod.stdAddChar y - 1‖ ≤ 2 * Real.pi * (zdist L y : ℝ) / L := by
  rw [KHeatDiff_std_vma]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, KHeatDiff_valMinAbs_abs, abs_of_pos Real.pi_pos,
    Nat.abs_cast, abs_two]

/-- The SBP gain: `|e^{2πi y/L} - 1| ≥ 4 |y|_L / L`. -/
private theorem KHeatDiff_char_sub_one_ge (y : ZMod L) :
    4 * (zdist L y : ℝ) / L ≤ ‖ZMod.stdAddChar y - 1‖ := by
  have hL : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  rw [KHeatDiff_std_vma, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two]
  set n : ℝ := (y.valMinAbs : ℝ) with hn
  have hz : |n| = (zdist L y : ℝ) := KHeatDiff_valMinAbs_abs y
  have hz2 : 2 * (zdist L y : ℝ) ≤ L := by
    have : 2 * zdist L y ≤ L := by simp only [zdist]; omega
    exact_mod_cast this
  have hpi := Real.pi_pos
  rw [show 2 * Real.pi * n / L / 2 = Real.pi * n / L by ring]
  have hsin : |Real.sin (Real.pi * n / L)| = |Real.sin (Real.pi * |n| / L)| := by
    rcases abs_cases n with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, show Real.pi * -n / L = -(Real.pi * n / L) by ring, Real.sin_neg, abs_neg]
  rw [hsin]
  have h0 : 0 ≤ Real.pi * |n| / L := by positivity
  have h3 := Real.mul_le_sin h0 (by rw [div_le_iff₀ hL, hz]; nlinarith)
  rw [abs_of_nonneg (le_trans (by positivity) h3), ← hz,
    show 2 / Real.pi * (Real.pi * |n| / L) = 2 * |n| / L by field_simp] at *
  calc 4 * |n| / L = 2 * (2 * |n| / L) := by ring
    _ ≤ _ := by linarith

end Char

/-! ## 3. Lattice facts, the moments of `K` and the regularity of the symbol -/

section Lattice

variable {d L : ℕ} [NeZero L]

/-- Port of `KHeatTail_zdist_natCast` (`KHeatTail.lean:50`). -/
private theorem KHeatDiff_zdist_natCast (k : ℕ) : zdist L (k : ZMod L) ≤ k := by
  unfold zdist
  rw [ZMod.val_natCast]
  exact (min_le_left _ _).trans (Nat.mod_le k L)

/-- `zdist (a j) ≤ |a|` (the `ℓ¹` torus norm). -/
private theorem KHeatDiff_zdist_le_zdistD (a : Zd d L) (j : Fin d) :
    (zdist L (a j) : ℝ) ≤ (zdistD d L a : ℝ) := by
  unfold zdistD; push_cast
  exact Finset.single_le_sum (f := fun l => (zdist L (a l) : ℝ)) (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ j)

/-- `‖χ_{e_j}(a) - 1‖ ≤ (2π/L) |a|`. -/
private theorem KHeatDiff_omega_le (a : Zd d L) (j : Fin d) :
    ‖KHeatDiff_chi (Pi.single j 1) a - 1‖ ≤ 2 * Real.pi / L * (zdistD d L a : ℝ) := by
  have hL : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  rw [KHeatDiff_chi_single_k]
  refine (KHeatDiff_char_sub_one _).trans ?_
  rw [mul_div_right_comm]
  exact mul_le_mul_of_nonneg_left (KHeatDiff_zdist_le_zdistD a j) (by positivity)

/-- `‖χ_k(a) - 1‖ ≤ ϑ |a|` if `ϑ ≥ 2π |k_l|_L/L` for all `l` (the cancellation behind the refined first difference). -/
private theorem KHeatDiff_chi_sub_one_le (k a : Zd d L) {ϑ : ℝ}
    (hϑ : ∀ l, 2 * Real.pi * (zdist L (k l) : ℝ) / L ≤ ϑ) :
    ‖KHeatDiff_chi k a - 1‖ ≤ ϑ * (zdistD d L a : ℝ) := by
  have hL : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  set n : ℤ := ∑ l, (k l).valMinAbs * (a l).valMinAbs with hn
  have h1 : (∑ l, k l * a l : ZMod L) = (n : ZMod L) := by
    rw [hn]; push_cast; simp only [ZMod.coe_valMinAbs]
  unfold KHeatDiff_chi
  rw [h1, KHeatDiff_std_exp]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  have h3 : |(n : ℝ)| ≤ ∑ l, (zdist L (k l) : ℝ) * (zdist L (a l) : ℝ) := by
    rw [hn]; push_cast
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun l _ => ?_))
    rw [abs_mul, KHeatDiff_valMinAbs_abs, KHeatDiff_valMinAbs_abs]
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_of_pos Real.pi_pos, Nat.abs_cast, abs_two]
  calc 2 * Real.pi * |(n : ℝ)| / L ≤ 2 * Real.pi * (∑ l, (zdist L (k l) : ℝ) * (zdist L (a l) : ℝ)) / L := by gcongr
    _ = ∑ l, (2 * Real.pi * (zdist L (k l) : ℝ) / L) * (zdist L (a l) : ℝ) := by
        rw [Finset.mul_sum, Finset.sum_div]; exact Finset.sum_congr rfl fun l _ => by ring
    _ ≤ ∑ l, ϑ * (zdist L (a l) : ℝ) :=
        Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (hϑ l) (Nat.cast_nonneg _)
    _ = ϑ * (zdistD d L a : ℝ) := by rw [← Finset.mul_sum]; unfold zdistD; push_cast; rfl

end Lattice

section Moment

/-- All moments of the kernel (twin of `BAK_second_moment`, `KSymbol.lean:700`, with `r^q ≤ q! μ^{-q} e^{μ r}`):
`Σ_a K_{0a} |a|^q ≤ C g²` for `1 ≤ q ≤ N`, uniformly in `L` and `g ∈ (0, Λ]`. -/
private theorem KHeatDiff_moment : ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ q : ℕ, 1 ≤ q → q ≤ N → ∑ a : Zd d L, BAK d L g E m 0 a * (zdistD d L a : ℝ) ^ q ≤ C * g ^ 2 := by
  intro d hd Λ κ hΛ hκ N
  have hd0 : 0 < d := by omega
  set μ : ℝ := BAct_rate d Λ κ with hμ
  have hμpos : 0 < μ := BAct_rate_pos d Λ κ hd0 hΛ hκ
  set Cn : ℝ := (N.factorial : ℝ) * (1 + μ⁻¹) ^ N with hCn
  have hCn0 : 0 < Cn := by positivity
  set C0 : ℝ := Cn * (BAp5s_A d Λ κ * BAp5s_S d Λ κ) with hC0
  refine ⟨max C0 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro L _ hL g E m hg hgΛ hr q hq1 hqN
  have hmom := BAK_exp_moment_le d L hL hd Λ g κ E m hΛ hg hgΛ hκ hr μ hμpos.le le_rfl 0
  have hsplit : ∀ f : Zd d L → ℝ, ∑ b, f b = f 0 + ∑ b ∈ Finset.univ.erase 0, f b := fun f =>
    (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
  have hdiag : BAK d L g E m 0 0 = ‖m‖ ^ 2 := BAK_diag d L g E m hr.1 0
  have hpt : ∀ a : Zd d L, BAK d L g E m 0 a * (zdistD d L a : ℝ) ^ q
      ≤ Cn * (BAK d L g E m 0 a * Real.exp (μ * (zdistD d L (0 - a) : ℝ))) := by
    intro a
    rw [zero_sub, zdistD_neg]
    have hr0 : (0 : ℝ) ≤ (zdistD d L a : ℝ) := Nat.cast_nonneg _
    have he := Real.pow_div_factorial_le_exp (μ * (zdistD d L a : ℝ)) (mul_nonneg hμpos.le hr0) q
    have hq : (0 : ℝ) < (q.factorial : ℝ) := by positivity
    rw [div_le_iff₀ hq, mul_pow] at he
    have h3 : (q.factorial : ℝ) * (μ⁻¹) ^ q ≤ Cn := by
      rw [hCn]
      refine mul_le_mul (by exact_mod_cast Nat.factorial_le hqN) ?_ (by positivity) (by positivity)
      calc (μ⁻¹) ^ q ≤ (1 + μ⁻¹) ^ q := pow_le_pow_left₀ (by positivity) (by linarith) q
        _ ≤ (1 + μ⁻¹) ^ N := pow_le_pow_right₀ (by linarith [inv_pos.mpr hμpos]) hqN
    have hμq : 0 < μ ^ q := pow_pos hμpos q
    have h2 : (zdistD d L a : ℝ) ^ q ≤ Cn * Real.exp (μ * (zdistD d L a : ℝ)) := by
      calc (zdistD d L a : ℝ) ^ q = (μ ^ q * (zdistD d L a : ℝ) ^ q) * (μ⁻¹) ^ q := by
            rw [inv_pow]; field_simp
        _ ≤ (Real.exp (μ * (zdistD d L a : ℝ)) * (q.factorial : ℝ)) * (μ⁻¹) ^ q :=
            mul_le_mul_of_nonneg_right he (by positivity)
        _ = Real.exp (μ * (zdistD d L a : ℝ)) * ((q.factorial : ℝ) * (μ⁻¹) ^ q) := by ring
        _ ≤ Real.exp (μ * (zdistD d L a : ℝ)) * Cn :=
            mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
        _ = Cn * Real.exp (μ * (zdistD d L a : ℝ)) := by ring
    calc BAK d L g E m 0 a * (zdistD d L a : ℝ) ^ q
        ≤ BAK d L g E m 0 a * (Cn * Real.exp (μ * (zdistD d L a : ℝ))) :=
          mul_le_mul_of_nonneg_left h2 (BAK_nonneg d L g E m 0 a)
      _ = _ := by ring
  have hsum : ∑ a ∈ Finset.univ.erase (0 : Zd d L), BAK d L g E m 0 a * (zdistD d L a : ℝ) ^ q
      ≤ Cn * ∑ a ∈ Finset.univ.erase (0 : Zd d L),
          BAK d L g E m 0 a * Real.exp (μ * (zdistD d L (0 - a) : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a _ => hpt a
  have hL0 : BAK d L g E m 0 0 * (zdistD d L 0 : ℝ) ^ q = 0 := by
    simp [zero_pow (by omega : q ≠ 0)]
  have hR0 : BAK d L g E m 0 0 * Real.exp (μ * (zdistD d L (0 - 0) : ℝ)) = ‖m‖ ^ 2 := by
    rw [sub_self, zdistD_zero, hdiag]; simp
  have hmom' : ∑ b, BAK d L g E m 0 b * Real.exp (μ * (zdistD d L (0 - b) : ℝ))
      ≤ ‖m‖ ^ 2 + BAp5s_A d Λ κ * g ^ 2 * BAp5s_S d Λ κ := hmom
  rw [hsplit (fun a => BAK d L g E m 0 a * Real.exp (μ * (zdistD d L (0 - a) : ℝ))), hR0] at hmom'
  have hrest : ∑ b ∈ Finset.univ.erase (0 : Zd d L),
      BAK d L g E m 0 b * Real.exp (μ * (zdistD d L (0 - b) : ℝ))
      ≤ BAp5s_A d Λ κ * g ^ 2 * BAp5s_S d Λ κ := by linarith
  have h1 : ∑ a ∈ Finset.univ.erase (0 : Zd d L), BAK d L g E m 0 a * (zdistD d L a : ℝ) ^ q
      ≤ Cn * (BAp5s_A d Λ κ * g ^ 2 * BAp5s_S d Λ κ) :=
    le_trans hsum (mul_le_mul_of_nonneg_left hrest hCn0.le)
  calc ∑ a, BAK d L g E m 0 a * (zdistD d L a : ℝ) ^ q
      = BAK d L g E m 0 0 * (zdistD d L 0 : ℝ) ^ q
        + ∑ a ∈ Finset.univ.erase (0 : Zd d L), BAK d L g E m 0 a * (zdistD d L a : ℝ) ^ q :=
        hsplit (fun a => BAK d L g E m 0 a * (zdistD d L a : ℝ) ^ q)
    _ ≤ C0 * g ^ 2 := by
        rw [hL0, zero_add, hC0]
        calc _ ≤ Cn * (BAp5s_A d Λ κ * g ^ 2 * BAp5s_S d Λ κ) := h1
          _ = _ := by ring
    _ ≤ max C0 1 * g ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

end Moment

section Symbol

variable {d L : ℕ} [NeZero L] (g E : ℝ) (m : ℂ)

/-- The symbol as a character sum, `K̂(k) = Σ_a K_{0a} χ_k(a)` (`BAKhat_eq`). -/
private theorem KHeatDiff_Khat_chi (k : Zd d L) :
    (BAKhat d L g E m k : ℂ) = ∑ a, (BAK d L g E m 0 a : ℂ) * KHeatDiff_chi k a := by
  rw [← BAKhat_eq d L g E m k]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [KHeatDiff_chi_eq]

/-- The iterated differences of the symbol along `h`: `Δ_h^i K̂ (k) = Σ_a K_{0a} χ_k(a) (χ_h(a) - 1)^i`. -/
private theorem KHeatDiff_symb_iter (h : Zd d L) (i : ℕ) :
    (fwdDiff h)^[i] (fun k' => (BAKhat d L g E m k' : ℂ))
      = fun k => ∑ a, (BAK d L g E m 0 a : ℂ) * KHeatDiff_chi k a * (KHeatDiff_chi h a - 1) ^ i := by
  induction i with
  | zero =>
    funext k
    simp only [Function.iterate_zero, id_eq, pow_zero, mul_one]
    exact KHeatDiff_Khat_chi g E m k
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    funext k
    simp only [fwdDiff, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [KHeatDiff_chi_add_k]
    ring

private theorem KHeatDiff_symb_norm_le (h : Zd d L) (i : ℕ) (k : Zd d L) :
    ‖(fwdDiff h)^[i] (fun k' => (BAKhat d L g E m k' : ℂ)) k‖
      ≤ ∑ a, BAK d L g E m 0 a * ‖KHeatDiff_chi h a - 1‖ ^ i := by
  rw [KHeatDiff_symb_iter]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [norm_mul, norm_mul, KHeatDiff_chi_norm, mul_one, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (BAK_nonneg d L g E m 0 a)]

/-- `‖Δ_j^i K̂‖ ≤ (2π/L)^i Σ_a K_{0a} |a|^i`. -/
private theorem KHeatDiff_symb_higher (j : Fin d) (i : ℕ) (k : Zd d L) :
    ‖(fwdDiff (Pi.single j (1 : ZMod L)))^[i] (fun k' => (BAKhat d L g E m k' : ℂ)) k‖
      ≤ (2 * Real.pi / L) ^ i * ∑ a, BAK d L g E m 0 a * (zdistD d L a : ℝ) ^ i := by
  refine (KHeatDiff_symb_norm_le g E m _ i k).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  calc BAK d L g E m 0 a * ‖KHeatDiff_chi (Pi.single j 1) a - 1‖ ^ i
      ≤ BAK d L g E m 0 a * (2 * Real.pi / L * (zdistD d L a : ℝ)) ^ i :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (KHeatDiff_omega_le a j) i) (BAK_nonneg d L g E m 0 a)
    _ = _ := by rw [mul_pow]; ring

private theorem KHeatDiff_unit_re (z : ℂ) (hz : ‖z‖ = 1) : |(z - 1).re| ≤ ‖z - 1‖ ^ 2 / 2 := by
  have h2 : z.re * z.re + z.im * z.im = 1 := by
    have := Complex.sq_norm z
    rw [Complex.normSq_apply, hz] at this
    linarith
  have h3 : ‖z - 1‖ ^ 2 = (z.re - 1) * (z.re - 1) + z.im * z.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
  have h4 : z.re ≤ 1 := by nlinarith [mul_self_nonneg z.im]
  rw [Complex.sub_re, Complex.one_re, abs_of_nonpos (by linarith), h3]
  nlinarith

/-- The refined first difference: `|Δ_j K̂(k)| ≤ ((2π/L)²/2 + ϑ 2π/L) Σ_a K_{0a} |a|²`, where `ϑ ≥ 2π |k_l|_L/L` for all `l`
(`|Im χ_k(a)| ≤ ϑ |a|` is the cancellation at `k = 0`). -/
private theorem KHeatDiff_symb_first (j : Fin d) (k : Zd d L) {ϑ : ℝ} (hϑ0 : 0 ≤ ϑ)
    (hϑ : ∀ l, 2 * Real.pi * (zdist L (k l) : ℝ) / L ≤ ϑ) :
    ‖fwdDiff (Pi.single j (1 : ZMod L)) (fun k' => (BAKhat d L g E m k' : ℂ)) k‖
      ≤ ((2 * Real.pi / L) ^ 2 / 2 + ϑ * (2 * Real.pi / L))
        * ∑ a, BAK d L g E m 0 a * (zdistD d L a : ℝ) ^ 2 := by
  have hL : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  have hreal : fwdDiff (Pi.single j (1 : ZMod L)) (fun k' => (BAKhat d L g E m k' : ℂ)) k
      = ((BAKhat d L g E m (k + Pi.single j 1) - BAKhat d L g E m k : ℝ) : ℂ) := by
    simp [fwdDiff]
  have hsum : fwdDiff (Pi.single j (1 : ZMod L)) (fun k' => (BAKhat d L g E m k' : ℂ)) k
      = ∑ a, (BAK d L g E m 0 a : ℂ) * (KHeatDiff_chi k a * (KHeatDiff_chi (Pi.single j 1) a - 1)) := by
    have := congrFun (KHeatDiff_symb_iter g E m (Pi.single j (1 : ZMod L)) 1) k
    simpa [mul_assoc] using this
  have hre : ‖fwdDiff (Pi.single j (1 : ZMod L)) (fun k' => (BAKhat d L g E m k' : ℂ)) k‖
      = |(∑ a, (BAK d L g E m 0 a : ℂ) * (KHeatDiff_chi k a * (KHeatDiff_chi (Pi.single j 1) a - 1))).re| := by
    rw [← hsum, hreal, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
  rw [hre, Complex.re_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Complex.re_ofReal_mul, abs_mul, abs_of_nonneg (BAK_nonneg d L g E m 0 a)]
  have hK := BAK_nonneg d L g E m 0 a
  set D : ℝ := (zdistD d L a : ℝ) with hD
  have hD0 : 0 ≤ D := Nat.cast_nonneg _
  set χ := KHeatDiff_chi k a with hχ
  set ω := KHeatDiff_chi (Pi.single j 1) a with hω
  have hωn : ‖ω‖ = 1 := KHeatDiff_chi_norm _ _
  have hχn : ‖χ‖ = 1 := KHeatDiff_chi_norm _ _
  have hE : ‖ω - 1‖ ≤ 2 * Real.pi / L * D := KHeatDiff_omega_le a j
  have hre1 : |(ω - 1).re| ≤ (2 * Real.pi / L * D) ^ 2 / 2 := by
    refine (KHeatDiff_unit_re ω hωn).trans ?_
    have := pow_le_pow_left₀ (norm_nonneg _) hE 2
    linarith
  have him1 : |(ω - 1).im| ≤ 2 * Real.pi / L * D :=
    ((Complex.abs_im_le_norm _)).trans hE
  have hχ1 : |χ.re| ≤ 1 := (Complex.abs_re_le_norm _).trans hχn.le
  have hχim : |χ.im| ≤ ϑ * D := by
    have := Complex.abs_im_le_norm (χ - 1)
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at this
    exact this.trans (KHeatDiff_chi_sub_one_le k a hϑ)
  have hmul : |(χ * (ω - 1)).re| ≤ (2 * Real.pi / L * D) ^ 2 / 2 + ϑ * D * (2 * Real.pi / L * D) := by
    rw [Complex.mul_re]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul]
    have hA : |χ.re| * |(ω - 1).re| ≤ 1 * ((2 * Real.pi / L * D) ^ 2 / 2) :=
      mul_le_mul hχ1 hre1 (abs_nonneg _) zero_le_one
    have hB : |χ.im| * |(ω - 1).im| ≤ (ϑ * D) * (2 * Real.pi / L * D) :=
      mul_le_mul hχim him1 (abs_nonneg _) (mul_nonneg hϑ0 hD0)
    linarith
  calc BAK d L g E m 0 a * |(χ * (ω - 1)).re|
      ≤ BAK d L g E m 0 a * ((2 * Real.pi / L * D) ^ 2 / 2 + ϑ * D * (2 * Real.pi / L * D)) :=
        mul_le_mul_of_nonneg_left hmul hK
    _ = ((2 * Real.pi / L) ^ 2 / 2 + ϑ * (2 * Real.pi / L)) * (BAK d L g E m 0 a * D ^ 2) := by ring

end Symbol

/-! ## 4. Geometric bounds for the two sequences along the line -/

section Seq

private theorem KHeatDiff_iter_sub_const (φ : ℕ → ℂ) (c : ℂ) (n : ℕ) :
    (fwdDiff (1 : ℕ))^[n + 1] (fun l => φ l - c) = (fwdDiff (1 : ℕ))^[n + 1] φ := by
  have e3 : fwdDiff (1 : ℕ) (fun l => φ l - c) = fwdDiff (1 : ℕ) φ := by
    funext l; simp [fwdDiff]
  rw [Function.iterate_succ_apply, Function.iterate_succ_apply, e3]

/-- The sequence `l ↦ s (F l - F 0)` has geometric bounds if the first difference is `≤ ϖ` and the higher ones are
`≤ B ρ^i`. -/
private theorem KHeatDiff_Geo_w {R : ℕ} {s B ρ ϖ : ℝ} (hs : 0 ≤ s) (F : ℕ → ℂ) (c : ℂ) (hc : F 0 = c)
    (h1 : ∀ l, l < R → s * ‖fwdDiff (1 : ℕ) F l‖ ≤ ϖ)
    (hi : ∀ i, 2 ≤ i → i ≤ R → ∀ l, l + i ≤ R → s * ‖(fwdDiff (1 : ℕ))^[i] F l‖ ≤ B * ρ ^ i)
    (hB : (R : ℝ) * ϖ ≤ B) (hρ : ϖ ≤ B * ρ) (hϖ : 0 ≤ ϖ) :
    KHeatDiff_Geo R B ρ (fun l => (s : ℂ) * (F l - c)) := by
  subst hc
  intro i hi' l hl
  rcases i with _ | _ | i
  · -- order 0
    simp only [Function.iterate_zero, id_eq, pow_zero, mul_one]
    have hsum : F l - F 0 = ∑ l' ∈ Finset.range l, (F (l' + 1) - F l') := by
      rw [Finset.sum_range_sub (fun l' => F l')]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs, hsum]
    calc s * ‖∑ l' ∈ Finset.range l, (F (l' + 1) - F l')‖
        ≤ s * ∑ l' ∈ Finset.range l, ‖F (l' + 1) - F l'‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) hs
      _ = ∑ l' ∈ Finset.range l, s * ‖fwdDiff (1 : ℕ) F l'‖ := by
          rw [Finset.mul_sum]; rfl
      _ ≤ ∑ l' ∈ Finset.range l, ϖ :=
          Finset.sum_le_sum fun l' hl' => h1 l' (by have := Finset.mem_range.mp hl'; omega)
      _ = l * ϖ := by simp
      _ ≤ R * ϖ := mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : l ≤ R)) hϖ
      _ ≤ B := hB
  · -- order 1
    have hd : (fwdDiff (1 : ℕ))^[1] (fun l => (s : ℂ) * (F l - F 0)) l = (s : ℂ) * fwdDiff (1 : ℕ) F l := by
      simp only [Function.iterate_one, fwdDiff]
      ring
    rw [hd, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
    calc _ ≤ ϖ := h1 l (by omega)
      _ ≤ B * ρ := hρ
      _ = B * ρ ^ (0 + 1) := by ring
  · -- order `i + 2`
    have hd : (fwdDiff (1 : ℕ))^[i + 2] (fun l => (s : ℂ) * (F l - F 0)) l
        = (s : ℂ) * (fwdDiff (1 : ℕ))^[i + 2] F l := by
      have e1 : (fun l => (s : ℂ) * (F l - F 0)) = (s : ℂ) • (fun l => F l - F 0) := by
        funext l; simp [smul_eq_mul]
      rw [e1, fwdDiff_iter_const_smul, Pi.smul_apply, smul_eq_mul]
      rw [KHeatDiff_iter_sub_const F (F 0) (i + 1)]
    rw [hd, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
    exact hi (i + 2) (by omega) hi' l hl

/-- `l ↦ c ζ^l - 1` has geometric bounds. -/
private theorem KHeatDiff_Geo_p {R : ℕ} {B ρ ε₀ ε₁ : ℝ} (c ζ : ℂ) (hc : ‖c‖ = 1) (hζ : ‖ζ‖ = 1)
    (h0 : ‖c - 1‖ ≤ ε₀) (h1 : ‖ζ - 1‖ ≤ ε₁) (hB : ε₀ + R * ε₁ ≤ B)
    (hq : ∀ q, 1 ≤ q → q ≤ R → ε₁ ^ q ≤ B * ρ ^ q) :
    KHeatDiff_Geo R B ρ (fun l => c * ζ ^ l - 1) := by
  intro i hi l hl
  rcases i with _ | i
  · simp only [Function.iterate_zero, id_eq, pow_zero, mul_one]
    have hl' : ‖ζ ^ l - 1‖ ≤ l * ε₁ := by
      induction l with
      | zero => simp
      | succ l ih =>
        have e : ζ ^ (l + 1) - 1 = ζ * (ζ ^ l - 1) + (ζ - 1) := by ring
        have ih' := ih (by omega)
        calc ‖ζ ^ (l + 1) - 1‖ = ‖ζ * (ζ ^ l - 1) + (ζ - 1)‖ := by rw [e]
          _ ≤ ‖ζ * (ζ ^ l - 1)‖ + ‖ζ - 1‖ := norm_add_le _ _
          _ = ‖ζ ^ l - 1‖ + ‖ζ - 1‖ := by rw [norm_mul, hζ, one_mul]
          _ ≤ l * ε₁ + ε₁ := add_le_add ih' h1
          _ = ((l + 1 : ℕ) : ℝ) * ε₁ := by push_cast; ring
    have e : c * ζ ^ l - 1 = (c - 1) + c * (ζ ^ l - 1) := by ring
    rw [e]
    calc ‖(c - 1) + c * (ζ ^ l - 1)‖ ≤ ‖c - 1‖ + ‖c * (ζ ^ l - 1)‖ := norm_add_le _ _
      _ ≤ ε₀ + l * ε₁ := by
          rw [norm_mul, hc, one_mul]
          exact add_le_add h0 hl'
      _ ≤ B := by
          have : (l : ℝ) * ε₁ ≤ R * ε₁ := by
            have hε : 0 ≤ ε₁ := (norm_nonneg _).trans h1
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : l ≤ R)) hε
          linarith
  · have hd : ∀ n : ℕ, (fwdDiff (1 : ℕ))^[n + 1] (fun l => c * ζ ^ l - 1) = fun l => c * ζ ^ l * (ζ - 1) ^ (n + 1) := by
      intro n
      induction n with
      | zero =>
        funext l
        simp only [zero_add, Function.iterate_one, fwdDiff, pow_one]
        ring
      | succ n ih =>
        rw [Function.iterate_succ_apply', ih]
        funext l
        simp only [fwdDiff]
        ring
    rw [hd, norm_mul, norm_mul, hc, norm_pow, norm_pow, hζ, one_mul, one_pow, one_mul]
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 _).trans (hq (i + 1) (by omega) hi)

/-- The empty product is geometric. -/
private theorem KHeatDiff_Geo_one (R : ℕ) : KHeatDiff_Geo R 1 0 (fun _ => (1 : ℂ)) := by
  intro i hi l hl
  cases i with
  | zero => simp
  | succ i =>
    have h0 : (fwdDiff (1 : ℕ)) (fun _ : ℕ => (1 : ℂ)) = fun _ => 0 := fwdDiff_const (1 : ℕ) (1 : ℂ)
    have h1 : (fwdDiff (1 : ℕ))^[i] (fun _ : ℕ => (0 : ℂ)) = fun _ => 0 :=
      Function.iterate_fixed (fwdDiff_const (1 : ℕ) (0 : ℂ)) i
    rw [Function.iterate_succ_apply, h0, h1]
    simp

/-- Finite products of geometric sequences. -/
private theorem KHeatDiff_Geo_prod {ι : Type*} (s : Finset ι) {R : ℕ} (φ : ι → ℕ → ℂ) (B ρ : ι → ℝ)
    (h : ∀ u ∈ s, KHeatDiff_Geo R (B u) (ρ u) (φ u)) :
    KHeatDiff_Geo R (∏ u ∈ s, B u) (∑ u ∈ s, ρ u) (fun l => ∏ u ∈ s, φ u l) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact KHeatDiff_Geo_one R
  | insert u s hu ih =>
    simp only [Finset.prod_insert hu, Finset.sum_insert hu]
    have ih' := ih (fun v hv => h v (Finset.mem_insert_of_mem hv))
    have hu' := h u (Finset.mem_insert_self u s)
    intro i hi l hl
    exact KHeatDiff_Geo_mul i R (φ u) (fun l => ∏ v ∈ s, φ v l) (B u) (∏ v ∈ s, B v) (ρ u) (∑ v ∈ s, ρ v)
      (fun a ha l hl' => hu' a (by omega) l hl') (fun a ha l hl' => ih' a (by omega) l hl') l hl

/-- The combination: `‖Δ^R (e^w p)(0)‖ ≤ R! e^{eB_w} B_p (ρ + ρ_p)^R`. -/
private theorem KHeatDiff_Geo_comb {R : ℕ} {Bw ρ Bp ρp : ℝ} (hBw : 0 ≤ Bw) (hρ : 0 ≤ ρ) (hBp : 0 ≤ Bp)
    {w p : ℕ → ℂ} (hw : KHeatDiff_Geo R Bw ρ w) (hp : KHeatDiff_Geo R Bp ρp p) :
    ‖(fwdDiff (1 : ℕ))^[R] (fun l => Complex.exp (w l) * p l) 0‖
      ≤ (R.factorial : ℝ) * Real.exp (Bw * Real.exp 1) * Bp * (ρ + ρp) ^ R := by
  have hψ : ∀ a ≤ R, ∀ l : ℕ, l + a ≤ R →
      ‖(fwdDiff (1 : ℕ))^[a] (fun x => Complex.exp (w x)) l‖
        ≤ ((R.factorial : ℝ) * Real.exp (Bw * Real.exp 1)) * ρ ^ a := by
    intro a ha l hl
    refine (KHeatDiff_Geo_exp hBw hρ hw a ha l hl).trans ?_
    have : (a.factorial : ℝ) ≤ R.factorial := by exact_mod_cast Nat.factorial_le ha
    calc (a.factorial : ℝ) * ρ ^ a * Real.exp (Bw * Real.exp 1)
        = ((a.factorial : ℝ) * Real.exp (Bw * Real.exp 1)) * ρ ^ a := by ring
      _ ≤ _ := by gcongr
  have := KHeatDiff_Geo_mul R R (fun x => Complex.exp (w x)) p ((R.factorial : ℝ) * Real.exp (Bw * Real.exp 1)) Bp ρ ρp
    hψ (fun a ha l hl => hp a ha l hl) 0 (by omega)
  simpa [mul_assoc] using this

end Seq

/-! ## 5. The per-frequency bound for `Δ_j^R (A · P)` -/

section Perk

variable {d L : ℕ} [NeZero L]

/-- Port of `KHeat_mu_le` (`KHeat.lean:728`): the gap gives the Gaussian bound of the symbol. -/
private theorem KHeatDiff_mu_le {c g τ Θ K : ℝ} (hg : 0 < g) (hτ : 0 ≤ τ)
    (h : c * g ^ 2 * Θ ≤ 1 - K) :
    Real.exp (-(τ / g ^ 2) * (1 - K)) ≤ Real.exp (-(c * τ) * Θ) := by
  refine Real.exp_le_exp.mpr ?_
  have h2 := mul_le_mul_of_nonneg_left h (div_nonneg hτ (sq_nonneg g))
  have h3 : τ / g ^ 2 * (c * g ^ 2 * Θ) = c * τ * Θ := by field_simp
  nlinarith

/-- A line in direction `h` through `k`: differences of `l ↦ f (k + l h)` are the differences of `f` along `h`. -/
private theorem KHeatDiff_line_iter {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h k : M)
    (f : M → G) (i l : ℕ) :
    (fwdDiff (1 : ℕ))^[i] (fun l' : ℕ => f (k + l' • h)) l = (fwdDiff h)^[i] f (k + l • h) := by
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 1
  simp only [smul_eq_mul, mul_one, add_nsmul, add_assoc]

/-- The absorption of the polynomial and exponential-in-`ξ` factors into the Gaussian. -/
private theorem KHeatDiff_absorb {c₀ a b γ : ℝ} (n R : ℕ) (hc₀ : 0 < c₀) (hb : 1 ≤ b) (hγ : 0 ≤ γ)
    {ξ T : ℝ} (hξ : 0 ≤ ξ) (hT : ξ ^ 2 ≤ 2 * T + 2 * a ^ 2) :
    (ξ + b) ^ n * (1 + ξ) ^ R * Real.exp (γ * ξ) * Real.exp (-(c₀ * T))
      ≤ b ^ n * Real.exp (((n : ℝ) + R + γ) ^ 2 / c₀ + c₀ * a ^ 2 / 2) * Real.exp (-(c₀ / 2 * T)) := by
  have h1 : (ξ + b) ^ n ≤ b ^ n * (1 + ξ) ^ n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) n
  have h2 : (1 + ξ) ^ n * (1 + ξ) ^ R ≤ Real.exp (((n : ℝ) + R) * ξ) := by
    have h3 : 1 + ξ ≤ Real.exp ξ := by linarith [Real.add_one_le_exp ξ]
    rw [← pow_add]
    calc (1 + ξ) ^ (n + R) ≤ Real.exp ξ ^ (n + R) := pow_le_pow_left₀ (by positivity) h3 _
      _ = Real.exp (((n + R : ℕ) : ℝ) * ξ) := by rw [← Real.exp_nat_mul]
      _ = _ := by push_cast; ring_nf
  have h4 : -(c₀ * T) ≤ -(c₀ / 2 * T) - c₀ * ξ ^ 2 / 4 + c₀ * a ^ 2 / 2 := by
    nlinarith
  have h5 : ((n : ℝ) + R + γ) * ξ - c₀ * ξ ^ 2 / 4 ≤ ((n : ℝ) + R + γ) ^ 2 / c₀ := by
    rw [le_div_iff₀ hc₀]
    nlinarith [sq_nonneg (((n : ℝ) + R + γ) - c₀ * ξ / 2)]
  have h6 : Real.exp (((n : ℝ) + R) * ξ) * Real.exp (γ * ξ) * Real.exp (-(c₀ * T))
      ≤ Real.exp (((n : ℝ) + R + γ) ^ 2 / c₀ + c₀ * a ^ 2 / 2) * Real.exp (-(c₀ / 2 * T)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  calc (ξ + b) ^ n * (1 + ξ) ^ R * Real.exp (γ * ξ) * Real.exp (-(c₀ * T))
      ≤ (b ^ n * (1 + ξ) ^ n) * (1 + ξ) ^ R * Real.exp (γ * ξ) * Real.exp (-(c₀ * T)) := by gcongr
    _ = b ^ n * ((1 + ξ) ^ n * (1 + ξ) ^ R) * Real.exp (γ * ξ) * Real.exp (-(c₀ * T)) := by ring
    _ ≤ b ^ n * Real.exp (((n : ℝ) + R) * ξ) * Real.exp (γ * ξ) * Real.exp (-(c₀ * T)) := by gcongr
    _ = b ^ n * (Real.exp (((n : ℝ) + R) * ξ) * Real.exp (γ * ξ) * Real.exp (-(c₀ * T))) := by ring
    _ ≤ b ^ n * (Real.exp (((n : ℝ) + R + γ) ^ 2 / c₀ + c₀ * a ^ 2 / 2) * Real.exp (-(c₀ / 2 * T))) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
    _ = _ := by ring

/-- `|l · h_i|_L ≤ l` for `h = e_j`. -/
private theorem KHeatDiff_zdist_line (j i : Fin d) (l : ℕ) :
    (zdist L (l • ((Pi.single j (1 : ZMod L) : Zd d L) i)) : ℝ) ≤ l := by
  by_cases hij : i = j
  · subst hij
    simp only [Pi.single_eq_same, nsmul_eq_mul, mul_one]
    exact_mod_cast KHeatDiff_zdist_natCast l
  · simp [Pi.single_eq_of_ne hij]

end Perk

section Perk2

variable {d L : ℕ} [NeZero L]

/-- The numerical constants of the first difference: `(2π/L)²/2 + (ϑ + R·2π/L)·2π/L ≤ 9(ϑ + (9R+9)/L)/L`. -/
private theorem KHeatDiff_E1_le (hL : (0 : ℝ) < L) {R ϑ : ℝ} (hR : 0 ≤ R) (hϑ : 0 ≤ ϑ) :
    (2 * Real.pi / L) ^ 2 / 2 + (ϑ + R * (2 * Real.pi / L)) * (2 * Real.pi / L)
      ≤ 9 * (ϑ + (9 * R + 9) / L) / L := by
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_le_four
  set u : ℝ := (L : ℝ)⁻¹ with hu
  have hu0 : 0 < u := by positivity
  have e1 : 2 * Real.pi / L = 2 * Real.pi * u := by rw [hu]; ring
  have e2 : 9 * (ϑ + (9 * R + 9) / L) / L = 9 * (ϑ + (9 * R + 9) * u) * u := by rw [hu]; ring
  rw [e1, e2]
  have h1 : 0 ≤ (9 - 2 * Real.pi) * (ϑ * u) := mul_nonneg (by linarith) (mul_nonneg hϑ hu0.le)
  have h2 : 0 ≤ (81 - 4 * Real.pi ^ 2) * (R * u ^ 2) := mul_nonneg (by nlinarith) (mul_nonneg hR (sq_nonneg u))
  have h3 : 0 ≤ (81 - 2 * Real.pi ^ 2) * u ^ 2 := mul_nonneg (by nlinarith) (sq_nonneg u)
  nlinarith

/-- The geometric bounds of `w(l) = s (K̂(k + l e_j) - K̂(k))`. -/
private theorem KHeatDiff_perk_w (g E : ℝ) (m : ℂ) {R : ℕ} {Cm ϑ τ σ ξ : ℝ} (hg : 0 < g) (hCm : 0 ≤ Cm)
    (hmom : ∀ q : ℕ, 1 ≤ q → q ≤ R + 2 →
      ∑ a : Zd d L, BAK d L g E m 0 a * (zdistD d L a : ℝ) ^ q ≤ Cm * g ^ 2)
    (hτ : τ = σ ^ 2) (hσ1 : 1 ≤ σ) (hσL : σ ≤ L) (j : Fin d) (k : Zd d L) (hϑ0 : 0 ≤ ϑ)
    (hϑ : ∀ l, 2 * Real.pi * (zdist L (k l) : ℝ) / L ≤ ϑ) (hξ : ξ = σ * (ϑ + (9 * R + 9) / L)) :
    KHeatDiff_Geo R (1 + 9 * R * Cm * ξ)
      ((1 + 9 * Cm + Cm * 9 ^ R) * (σ / L) * (1 + ξ))
      (fun l => ((τ / g ^ 2 : ℝ) : ℂ)
        * ((BAKhat d L g E m (k + l • Pi.single j 1) : ℂ) - (BAKhat d L g E m k : ℂ))) := by
  have hLpos : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  have hσ0 : 0 < σ := by linarith
  have hτ0 : 0 < τ := by rw [hτ]; positivity
  have hpi := Real.pi_pos
  set θ1 : ℝ := 2 * Real.pi / L with hθ1
  have hθ0 : 0 ≤ θ1 := by positivity
  set s : ℝ := τ / g ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  have hsg : s * g ^ 2 = τ := by rw [hs]; field_simp
  set Y : ℝ := σ / L with hY
  have hY0 : 0 ≤ Y := by positivity
  have hY1 : Y ≤ 1 := by rw [hY, div_le_one hLpos]; exact hσL
  have hξ0 : 0 ≤ ξ := by rw [hξ]; positivity
  set K : ℝ := 1 + 9 * Cm + Cm * 9 ^ R with hK
  have hK1 : 1 ≤ K := by
    have : 0 ≤ Cm * 9 ^ R := by positivity
    rw [hK]; nlinarith
  have hK7 : 9 * Cm ≤ K := by
    have : 0 ≤ Cm * 9 ^ R := by positivity
    rw [hK]; nlinarith
  set Bw : ℝ := 1 + 9 * R * Cm * ξ with hBw
  have hBw1 : 1 ≤ Bw := by
    rw [hBw]
    have : 0 ≤ 9 * (R : ℝ) * Cm * ξ := by positivity
    linarith
  set Kc : Zd d L → ℂ := fun k' => (BAKhat d L g E m k' : ℂ) with hKc
  set h : Zd d L := Pi.single j 1 with hh
  set Fseq : ℕ → ℂ := fun l => Kc (k + l • h) with hF
  have hF0 : Fseq 0 = Kc k := by simp [hF]
  have hline : ∀ i l, (fwdDiff (1 : ℕ))^[i] Fseq l = (fwdDiff h)^[i] Kc (k + l • h) :=
    fun i l => KHeatDiff_line_iter h k Kc i l
  set M₂ := ∑ a : Zd d L, BAK d L g E m 0 a * (zdistD d L a : ℝ) ^ 2 with hM₂
  have hM2 : M₂ ≤ Cm * g ^ 2 := hmom 2 (by norm_num) (by omega)
  set ϖ : ℝ := 9 * Cm * (Y * ξ) with hϖ
  have hϖ0 : 0 ≤ ϖ := by positivity
  have hτE : τ * (θ1 ^ 2 / 2 + (ϑ + R * θ1) * θ1) ≤ 9 * (Y * ξ) := by
    have := KHeatDiff_E1_le hLpos (R := (R : ℝ)) (ϑ := ϑ) (Nat.cast_nonneg R) hϑ0
    rw [hτ, hY, hξ]
    calc σ ^ 2 * (θ1 ^ 2 / 2 + (ϑ + R * θ1) * θ1) ≤ σ ^ 2 * (9 * (ϑ + (9 * R + 9) / L) / L) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 9 * (σ / L * (σ * (ϑ + (9 * R + 9) / L))) := by field_simp
  have h1 : ∀ l, l < R → s * ‖fwdDiff (1 : ℕ) Fseq l‖ ≤ ϖ := by
    intro l hl
    have e1 : fwdDiff (1 : ℕ) Fseq l = fwdDiff h Kc (k + l • h) := by
      have := hline 1 l
      simpa using this
    rw [e1]
    have hϑl : ∀ l', 2 * Real.pi * (zdist L ((k + l • h) l') : ℝ) / L ≤ ϑ + l * θ1 := by
      intro l'
      have hadd : (zdist L ((k + l • h) l') : ℝ) ≤ (zdist L (k l') : ℝ) + l := by
        have h1' : zdist L ((k + l • h) l') ≤ zdist L (k l') + zdist L (l • h l') := by
          simpa using zdist_add_le L (k l') (l • h l')
        have h2' := KHeatDiff_zdist_line (L := L) j l' l
        have h3' : ((zdist L ((k + l • h) l') : ℕ) : ℝ)
            ≤ (zdist L (k l') : ℝ) + (zdist L (l • h l') : ℝ) := by exact_mod_cast h1'
        linarith
      calc 2 * Real.pi * (zdist L ((k + l • h) l') : ℝ) / L
          ≤ 2 * Real.pi * ((zdist L (k l') : ℝ) + l) / L := by gcongr
        _ = 2 * Real.pi * (zdist L (k l') : ℝ) / L + l * θ1 := by rw [hθ1]; ring
        _ ≤ ϑ + l * θ1 := by linarith [hϑ l']
    have hfirst := KHeatDiff_symb_first g E m j (k + l • h) (by positivity) hϑl
    have hcoef : θ1 ^ 2 / 2 + (ϑ + l * θ1) * θ1 ≤ θ1 ^ 2 / 2 + (ϑ + R * θ1) * θ1 := by
      have : (l : ℝ) ≤ R := by exact_mod_cast hl.le
      nlinarith [mul_nonneg hθ0 hθ0]
    have hcoef0 : 0 ≤ θ1 ^ 2 / 2 + (ϑ + l * θ1) * θ1 := by positivity
    calc s * ‖fwdDiff h Kc (k + l • h)‖
        ≤ s * ((θ1 ^ 2 / 2 + (ϑ + l * θ1) * θ1) * M₂) := mul_le_mul_of_nonneg_left hfirst hs0
      _ ≤ s * ((θ1 ^ 2 / 2 + (ϑ + R * θ1) * θ1) * (Cm * g ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hs0
          exact mul_le_mul hcoef hM2 (Finset.sum_nonneg fun a _ => mul_nonneg (BAK_nonneg d L g E m 0 a) (by positivity)) (by positivity)
      _ = τ * (θ1 ^ 2 / 2 + (ϑ + R * θ1) * θ1) * Cm := by rw [← hsg]; ring
      _ ≤ 9 * (Y * ξ) * Cm := mul_le_mul_of_nonneg_right hτE hCm
      _ = ϖ := by rw [hϖ]; ring
  have hi : ∀ i, 2 ≤ i → i ≤ R → ∀ l, l + i ≤ R →
      s * ‖(fwdDiff (1 : ℕ))^[i] Fseq l‖ ≤ Bw * (K * Y * (1 + ξ)) ^ i := by
    intro i hi2 hiR l hl
    rw [hline i l]
    have hh1 := KHeatDiff_symb_higher g E m j i (k + l • h)
    have hMi : ∑ a : Zd d L, BAK d L g E m 0 a * (zdistD d L a : ℝ) ^ i ≤ Cm * g ^ 2 :=
      hmom i (by omega) (by omega)
    have hσi : σ ^ 2 ≤ σ ^ i := pow_le_pow_right₀ hσ1 hi2
    have hpi4 := Real.pi_le_four
    have h9 : 1 ≤ (9 : ℝ) := by norm_num
    have hCmK : Cm * 9 ^ i ≤ K ^ i := by
      have h3 : Cm * 9 ^ i ≤ Cm * 9 ^ R := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h9 hiR) hCm
      have h4 : K ≤ K ^ i := le_self_pow₀ hK1 (by omega)
      have : 0 ≤ 9 * Cm := by positivity
      rw [hK] at h4 ⊢
      linarith
    have hθ9 : θ1 ≤ 9 / L := by
      rw [hθ1]
      exact div_le_div_of_nonneg_right (by linarith) hLpos.le
    calc s * ‖(fwdDiff h)^[i] Kc (k + l • h)‖
        ≤ s * (θ1 ^ i * (Cm * g ^ 2)) := by
          refine mul_le_mul_of_nonneg_left (hh1.trans ?_) hs0
          exact mul_le_mul_of_nonneg_left hMi (by positivity)
      _ = τ * θ1 ^ i * Cm := by rw [← hsg]; ring
      _ = σ ^ 2 * θ1 ^ i * Cm := by rw [hτ]
      _ ≤ σ ^ i * (9 / L) ^ i * Cm := by
          gcongr
      _ = (9 ^ i * Cm) * Y ^ i := by
          rw [← mul_pow, show σ * (9 / (L : ℝ)) = 9 * Y by rw [hY]; ring, mul_pow]
          ring
      _ ≤ K ^ i * Y ^ i := by
          rw [mul_comm ((9 : ℝ) ^ i) Cm]
          exact mul_le_mul_of_nonneg_right hCmK (by positivity)
      _ = K ^ i * Y ^ i * 1 := (mul_one _).symm
      _ ≤ K ^ i * Y ^ i * (1 + ξ) ^ i := by
          gcongr
          exact one_le_pow₀ (by linarith)
      _ = (K * Y * (1 + ξ)) ^ i := by rw [mul_pow, mul_pow]
      _ = 1 * (K * Y * (1 + ξ)) ^ i := (one_mul _).symm
      _ ≤ Bw * (K * Y * (1 + ξ)) ^ i := by gcongr
  have hB : (R : ℝ) * ϖ ≤ Bw := by
    have : (R : ℝ) * ϖ = 9 * R * Cm * (Y * ξ) := by rw [hϖ]; ring
    rw [this, hBw]
    have : 9 * (R : ℝ) * Cm * (Y * ξ) ≤ 9 * R * Cm * ξ := by
      have : 0 ≤ 9 * (R : ℝ) * Cm := by positivity
      nlinarith [mul_nonneg hξ0 (sub_nonneg.2 hY1)]
    linarith
  have hρ : ϖ ≤ Bw * (K * Y * (1 + ξ)) := by
    rw [hϖ]
    calc 9 * Cm * (Y * ξ) ≤ K * Y * (1 + ξ) := by
          have : 9 * Cm * (Y * ξ) ≤ K * (Y * ξ) := mul_le_mul_of_nonneg_right hK7 (by positivity)
          nlinarith [mul_nonneg hY0 (by positivity : (0 : ℝ) ≤ K)]
      _ = 1 * (K * Y * (1 + ξ)) := (one_mul _).symm
      _ ≤ Bw * (K * Y * (1 + ξ)) := by gcongr
  exact KHeatDiff_Geo_w hs0 Fseq (Kc k) hF0 h1 hi hB hρ hϖ0

end Perk2

section Perk3

variable {d L : ℕ} [NeZero L]

/-- The geometric bounds of the prefactor `l ↦ χ_{k + l e_j}(e_i) - 1`. -/
private theorem KHeatDiff_perk_p {R : ℕ} {ϑ σ ξ : ℝ} (hσ1 : 1 ≤ σ) (hσL : σ ≤ L) (hϑ0 : 0 ≤ ϑ)
    (hξ : 0 ≤ ξ) (j i : Fin d) (k : Zd d L)
    (hϑ : 2 * Real.pi * (zdist L (k i) : ℝ) / L ≤ ϑ) :
    KHeatDiff_Geo R (ϑ + (R + 1) * (2 * Real.pi / L) + σ⁻¹) (2 * Real.pi * (σ / L) * (1 + ξ))
      (fun l => KHeatDiff_chi (k + l • (Pi.single j 1 : Zd d L)) (Pi.single i 1) - 1) := by
  have hLpos : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  have hσ0 : 0 < σ := by linarith
  have hpi := Real.pi_pos
  set θ1 : ℝ := 2 * Real.pi / L with hθ1
  have hθ0 : 0 ≤ θ1 := by positivity
  have e : (fun l : ℕ => KHeatDiff_chi (k + l • (Pi.single j 1 : Zd d L)) (Pi.single i 1) - 1)
      = fun l : ℕ => KHeatDiff_chi k (Pi.single i 1) * KHeatDiff_chi (Pi.single j 1 : Zd d L) (Pi.single i 1) ^ l - 1 := by
    funext l
    rw [KHeatDiff_chi_add_k, KHeatDiff_chi_nsmul_k]
  rw [e]
  refine KHeatDiff_Geo_p (ε₀ := ϑ) (ε₁ := θ1) _ _ (KHeatDiff_chi_norm _ _) (KHeatDiff_chi_norm _ _) ?_ ?_ ?_ ?_
  · rw [KHeatDiff_chi_single_a]
    exact (KHeatDiff_char_sub_one _).trans hϑ
  · rw [KHeatDiff_chi_single_a]
    refine (KHeatDiff_char_sub_one _).trans ?_
    have := KHeatDiff_zdist_line (L := L) j i 1
    rw [one_nsmul] at this
    calc 2 * Real.pi * (zdist L ((Pi.single j (1 : ZMod L) : Zd d L) i) : ℝ) / L
        ≤ 2 * Real.pi * 1 / L := by
          gcongr
          exact_mod_cast this
      _ = θ1 := by rw [hθ1]; ring
  · have : (0 : ℝ) ≤ σ⁻¹ := by positivity
    nlinarith [Nat.cast_nonneg (α := ℝ) R]
  · intro q hq1 hqR
    have hσq : σ ^ q = σ * σ ^ (q - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h1 : θ1 ^ q ≤ σ⁻¹ * (2 * Real.pi * (σ / L)) ^ q := by
      calc θ1 ^ q ≤ θ1 ^ q * σ ^ (q - 1) := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hσ1)
        _ = σ⁻¹ * (θ1 ^ q * σ ^ q) := by rw [hσq]; field_simp
        _ = σ⁻¹ * (2 * Real.pi * (σ / L)) ^ q := by
            rw [← mul_pow, hθ1]
            congr 2
            ring
    refine h1.trans ?_
    have h2 : (2 * Real.pi * (σ / L)) ^ q ≤ (2 * Real.pi * (σ / L) * (1 + ξ)) ^ q :=
      pow_le_pow_left₀ (by positivity) (by nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi * (σ / L)) hξ]) q
    have h3 : σ⁻¹ ≤ ϑ + (R + 1) * θ1 + σ⁻¹ := by
      have : 0 ≤ ϑ + (R + 1) * θ1 := by positivity
      linarith
    exact mul_le_mul h3 h2 (by positivity) (by positivity)

end Perk3

section Perk4

variable {d L : ℕ} [NeZero L]

private theorem KHeatDiff_thetaSq_nonneg (k : Zd d L) : 0 ≤ BAthetaSq d L k :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Port of `KHeat_theta_sq_le` (`KHeat.lean:713`). -/
private theorem KHeatDiff_theta_sq_le (k : Zd d L) (j : Fin d) :
    (2 * Real.pi * (zdist L (k j) : ℝ) / L) ^ 2 ≤ BAthetaSq d L k := by
  unfold BAthetaSq
  exact Finset.single_le_sum (f := fun i => (2 * Real.pi * (zdist L (k i) : ℝ) / L) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ j)

private theorem KHeatDiff_num_Bp {ϑ σ L R ξ a b : ℝ} (hσ0 : 0 < σ) (hL : 0 < L) (hR : 0 ≤ R) (hϑ0 : 0 ≤ ϑ)
    (hξ : ξ = σ * (ϑ + a / L)) (ha : a = 9 * R + 9) (hb : b = 9 * R + 10) :
    ϑ + (R + 1) * (2 * Real.pi / L) + σ⁻¹ ≤ σ⁻¹ * (ξ + b) := by
  have hpi4 := Real.pi_le_four
  have h1 : σ⁻¹ * ξ = ϑ + a / L := by rw [hξ]; field_simp
  have h2 : (R + 1) * (2 * Real.pi / L) ≤ a / L := by
    rw [ha, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by nlinarith) hL.le
  have h3 : σ⁻¹ ≤ σ⁻¹ * b := le_mul_of_one_le_right (inv_nonneg.2 hσ0.le) (by rw [hb]; linarith)
  calc ϑ + (R + 1) * (2 * Real.pi / L) + σ⁻¹ ≤ (ϑ + a / L) + σ⁻¹ * b := by linarith
    _ = σ⁻¹ * (ξ + b) := by rw [mul_add, h1]

private theorem KHeatDiff_num_xi {ϑ σ L τ Θ ξ a : ℝ} (hσ0 : 0 < σ) (hL : 0 < L) (hσL : σ ≤ L)
    (hσsq : σ ^ 2 = τ) (hϑsq : ϑ ^ 2 = Θ) (hξ : ξ = σ * (ϑ + a / L)) :
    ξ ^ 2 ≤ 2 * (τ * Θ) + 2 * a ^ 2 := by
  have h1 : ξ ^ 2 = σ ^ 2 * (ϑ + a / L) ^ 2 := by rw [hξ]; ring
  have h2 : (ϑ + a / L) ^ 2 ≤ 2 * ϑ ^ 2 + 2 * (a / L) ^ 2 := by linarith [sq_nonneg (ϑ - a / L)]
  have h3 : σ ^ 2 * (a / L) ^ 2 ≤ a ^ 2 := by
    have e : σ ^ 2 * (a / L) ^ 2 = a ^ 2 * (σ / L) ^ 2 := by field_simp
    have hY : (σ / L) ^ 2 ≤ 1 := by
      have : σ / L ≤ 1 := (div_le_one hL).2 hσL
      have : 0 ≤ σ / L := by positivity
      nlinarith
    rw [e]
    nlinarith [sq_nonneg a]
  rw [h1, ← hσsq, ← hϑsq]
  nlinarith [sq_nonneg σ]

/-- **The per-frequency bound.**  For `1 ≤ τ ≤ L²`: `‖Δ_j^R (A · Π_u (χ_·(e_{i_u}) - 1)) (k)‖
≤ C (√τ/L)^R (√τ)^{-n} e^{-c₁ τ |θ_k|²}`: each of the `R` differences gains `√τ/L`. -/
private theorem KHeatDiff_perk : ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∀ R n : ℕ,
    ∃ C c₁ : ℝ, 0 < C ∧ 0 < c₁ ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ τ : ℝ, 1 ≤ τ → τ ≤ (L : ℝ) ^ 2 → ∀ (j : Fin d) (i : Fin n → Fin d) (k : Zd d L),
        ‖(fwdDiff (Pi.single j (1 : ZMod L)))^[R]
            (fun k' : Zd d L => ((Real.exp (-(τ / g ^ 2) * (1 - BAKhat d L g E m k')) : ℝ) : ℂ)
              * ∏ u : Fin n, (KHeatDiff_chi k' (Pi.single (i u) 1) - 1)) k‖
          ≤ C * (Real.sqrt τ / L) ^ R * ((Real.sqrt τ)⁻¹) ^ n * Real.exp (-(c₁ * τ) * BAthetaSq d L k) := by
  intro d hd Λ κ hΛ hκ R n
  have hd0 : 0 < d := by omega
  obtain ⟨c₀, hc₀, hgap⟩ := BAK_gap d hd0 Λ κ hΛ hκ
  obtain ⟨Cm, hCm, hmom⟩ := KHeatDiff_moment d hd Λ κ hΛ hκ (R + 2)
  set K : ℝ := 1 + 9 * Cm + Cm * 9 ^ R with hK
  set a : ℝ := 9 * R + 9 with ha
  set b : ℝ := 9 * R + 10 with hb
  set γ : ℝ := 9 * Real.exp 1 * R * Cm with hγ
  set C₀ : ℝ := b ^ n * Real.exp (((n : ℝ) + R + γ) ^ 2 / c₀ + c₀ * a ^ 2 / 2) with hC₀
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_le_four
  refine ⟨(R.factorial : ℝ) * Real.exp (Real.exp 1) * (K + 2 * Real.pi * n) ^ R * C₀, c₀ / 2,
    by positivity, by positivity, ?_⟩
  intro L _ hL g E m hg hgΛ hr τ hτ1 hτL j i k
  have hLpos : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  set σ : ℝ := Real.sqrt τ with hσ
  have hσ1 : 1 ≤ σ := by rw [hσ]; exact Real.one_le_sqrt.mpr hτ1
  have hσsq : σ ^ 2 = τ := Real.sq_sqrt (by linarith)
  have hσL : σ ≤ L := by rw [hσ]; exact Real.sqrt_le_iff.mpr ⟨hLpos.le, hτL⟩
  have hσ0 : 0 < σ := by linarith
  set Y : ℝ := σ / L with hY
  have hY0 : 0 ≤ Y := by positivity
  have hY1 : Y ≤ 1 := by rw [hY, div_le_one hLpos]; exact hσL
  set ϑ : ℝ := Real.sqrt (BAthetaSq d L k) with hϑ
  have hϑ0 : 0 ≤ ϑ := Real.sqrt_nonneg _
  have hϑsq : ϑ ^ 2 = BAthetaSq d L k := Real.sq_sqrt (KHeatDiff_thetaSq_nonneg k)
  have hϑk : ∀ l, 2 * Real.pi * (zdist L (k l) : ℝ) / L ≤ ϑ := fun l =>
    (Real.le_sqrt (by positivity) (KHeatDiff_thetaSq_nonneg k)).mpr (KHeatDiff_theta_sq_le k l)
  set ξ : ℝ := σ * (ϑ + a / L) with hξ
  have hξ0 : 0 ≤ ξ := by positivity
  set h : Zd d L := Pi.single j 1 with hh
  set s : ℝ := τ / g ^ 2 with hs
  set w : ℕ → ℂ := fun l => (s : ℂ) * ((BAKhat d L g E m (k + l • h) : ℂ) - (BAKhat d L g E m k : ℂ)) with hw
  set p : ℕ → ℂ := fun l => ∏ u : Fin n, (KHeatDiff_chi (k + l • h) (Pi.single (i u) 1) - 1) with hp
  set G : Zd d L → ℂ := fun k' => ((Real.exp (-(τ / g ^ 2) * (1 - BAKhat d L g E m k')) : ℝ) : ℂ)
      * ∏ u : Fin n, (KHeatDiff_chi k' (Pi.single (i u) 1) - 1) with hG
  set Θ : ℝ := BAthetaSq d L k with hΘ
  set Bp : ℝ := ϑ + (R + 1) * (2 * Real.pi / L) + σ⁻¹ with hBp
  set ρp : ℝ := 2 * Real.pi * (σ / L) * (1 + ξ) with hρp
  have hBp0 : 0 ≤ Bp := by positivity
  have hGw : KHeatDiff_Geo R (1 + 9 * R * Cm * ξ) (K * Y * (1 + ξ)) w :=
    KHeatDiff_perk_w g E m hg hCm.le (hmom L hL g E m hg hgΛ hr) hσsq.symm hσ1 hσL j k hϑ0 hϑk hξ
  have hGp : KHeatDiff_Geo R (Bp ^ n) (n * ρp) p := by
    have := KHeatDiff_Geo_prod (Finset.univ : Finset (Fin n)) (R := R)
      (fun u l => KHeatDiff_chi (k + l • h) (Pi.single (i u) 1) - 1) (fun _ => Bp) (fun _ => ρp)
      (fun u _ => KHeatDiff_perk_p hσ1 hσL hϑ0 hξ0 j (i u) k (hϑk (i u)))
    have hsum : ∑ _u : Fin n, ρp = n * ρp := by simp
    have hprod : ∏ _u : Fin n, Bp = Bp ^ n := by simp
    rw [hprod, hsum] at this
    exact this
  have hcomb := KHeatDiff_Geo_comb (by positivity : 0 ≤ 1 + 9 * (R : ℝ) * Cm * ξ)
    (by positivity : 0 ≤ K * Y * (1 + ξ)) (by positivity : 0 ≤ Bp ^ n) hGw hGp
  -- the line through `k`
  have hAline : ∀ l : ℕ, ((Real.exp (-(τ / g ^ 2) * (1 - BAKhat d L g E m (k + l • h))) : ℝ) : ℂ)
      = ((Real.exp (-(τ / g ^ 2) * (1 - BAKhat d L g E m k)) : ℝ) : ℂ) * Complex.exp (w l) := by
    intro l
    rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    simp only [hw, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_one, hs]
    ring
  have hline : (fun l : ℕ => G (k + l • h))
      = ((Real.exp (-(τ / g ^ 2) * (1 - BAKhat d L g E m k)) : ℝ) : ℂ) • (fun l => Complex.exp (w l) * p l) := by
    funext l
    simp only [hG, hp, Pi.smul_apply, smul_eq_mul, hAline l]
    ring
  have hnorm : ‖(fwdDiff h)^[R] G k‖
      = Real.exp (-(τ / g ^ 2) * (1 - BAKhat d L g E m k))
        * ‖(fwdDiff (1 : ℕ))^[R] (fun l => Complex.exp (w l) * p l) 0‖ := by
    have := KHeatDiff_line_iter h k G R 0
    rw [zero_smul, add_zero] at this
    rw [← this, hline, fwdDiff_iter_const_smul, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
  have hAk : Real.exp (-(τ / g ^ 2) * (1 - BAKhat d L g E m k)) ≤ Real.exp (-(c₀ * τ) * Θ) :=
    KHeatDiff_mu_le hg (by linarith) (hgap L hL g E m hg hgΛ hr k)
  -- numerical facts
  have hBpb : Bp ≤ σ⁻¹ * (ξ + b) :=
    KHeatDiff_num_Bp hσ0 hLpos (Nat.cast_nonneg R) hϑ0 hξ ha hb
  have hBe : Real.exp ((1 + 9 * (R : ℝ) * Cm * ξ) * Real.exp 1) = Real.exp (Real.exp 1) * Real.exp (γ * ξ) := by
    rw [← Real.exp_add, hγ]; congr 1; ring
  have hξsq : ξ ^ 2 ≤ 2 * (τ * Θ) + 2 * a ^ 2 := KHeatDiff_num_xi hσ0 hLpos hσL hσsq hϑsq hξ
  have habs := KHeatDiff_absorb (c₀ := c₀) (a := a) (b := b) (γ := γ) n R hc₀ (by rw [hb]; linarith [Nat.cast_nonneg (α := ℝ) R])
    (by rw [hγ]; positivity) hξ0 hξsq
  have hpow : Bp ^ n ≤ (σ⁻¹) ^ n * (ξ + b) ^ n := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hBp0 hBpb n
  calc ‖(fwdDiff h)^[R] G k‖
      = Real.exp (-(τ / g ^ 2) * (1 - BAKhat d L g E m k))
        * ‖(fwdDiff (1 : ℕ))^[R] (fun l => Complex.exp (w l) * p l) 0‖ := hnorm
    _ ≤ Real.exp (-(c₀ * τ) * Θ) * ((R.factorial : ℝ) * Real.exp ((1 + 9 * (R : ℝ) * Cm * ξ) * Real.exp 1) * Bp ^ n
          * (K * Y * (1 + ξ) + n * ρp) ^ R) :=
        mul_le_mul hAk hcomb (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp (-(c₀ * τ) * Θ) * ((R.factorial : ℝ) * (Real.exp (Real.exp 1) * Real.exp (γ * ξ))
          * ((σ⁻¹) ^ n * (ξ + b) ^ n) * ((K + 2 * Real.pi * n) * Y * (1 + ξ)) ^ R) := by
        rw [hBe]
        have : K * Y * (1 + ξ) + n * ρp = (K + 2 * Real.pi * n) * Y * (1 + ξ) := by rw [hρp, hY]; ring
        rw [this]
        gcongr
    _ = (R.factorial : ℝ) * Real.exp (Real.exp 1) * (K + 2 * Real.pi * n) ^ R * Y ^ R * (σ⁻¹) ^ n
          * ((ξ + b) ^ n * (1 + ξ) ^ R * Real.exp (γ * ξ) * Real.exp (-(c₀ * (τ * Θ)))) := by
        rw [show -(c₀ * τ) * Θ = -(c₀ * (τ * Θ)) by ring, mul_pow, mul_pow]
        ring
    _ ≤ (R.factorial : ℝ) * Real.exp (Real.exp 1) * (K + 2 * Real.pi * n) ^ R * Y ^ R * (σ⁻¹) ^ n
          * (C₀ * Real.exp (-(c₀ / 2 * (τ * Θ)))) := by
        gcongr
    _ = _ := by
        rw [show -(c₀ / 2 * τ) * BAthetaSq d L k = -(c₀ / 2 * (τ * Θ)) by rw [hΘ]; ring]
        ring

end Perk4

/-! ## 6. Summation by parts, the Gaussian sum and the Fourier bound -/

section Four

variable {d L : ℕ} [NeZero L]

private theorem KHeatDiff_chi_re (k a : Zd d L) :
    (KHeatDiff_chi k a).re = Real.cos (2 * Real.pi / L * ∑ j, ((k j).val : ℝ) * ((a j).val : ℝ)) := by
  rw [KHeatDiff_chi_eq]
  have : (2 * Real.pi * Complex.I / L * ∑ j, ((k j).val : ℂ) * ((a j).val : ℂ))
      = ((2 * Real.pi / L * ∑ j, ((k j).val : ℝ) * ((a j).val : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

/-- Summation by parts in the direction `e_j`: `Σ_k (Δ_j^R F)(k) χ_k(a) = (e^{-2πi a_j/L} - 1)^R Σ_k F(k) χ_k(a)`. -/
private theorem KHeatDiff_sbp (j : Fin d) (a : Zd d L) (F : Zd d L → ℂ) (R : ℕ) :
    ∑ k, (fwdDiff (Pi.single j (1 : ZMod L)))^[R] F k * KHeatDiff_chi k a
      = (ZMod.stdAddChar (-(a j)) - 1) ^ R * ∑ k, F k * KHeatDiff_chi k a := by
  set h : Zd d L := Pi.single j 1 with hh
  have hω : ZMod.stdAddChar (-(a j)) * KHeatDiff_chi h a = 1 := by
    rw [hh, KHeatDiff_chi_single_k, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have key : ∀ F : Zd d L → ℂ, ∑ k, fwdDiff h F k * KHeatDiff_chi k a
      = (ZMod.stdAddChar (-(a j)) - 1) * ∑ k, F k * KHeatDiff_chi k a := by
    intro F
    have h1 : ∑ k, F (k + h) * KHeatDiff_chi k a = ZMod.stdAddChar (-(a j)) * ∑ k, F k * KHeatDiff_chi k a := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.addRight h) _ _ fun k => ?_
      simp only [Equiv.coe_addRight, KHeatDiff_chi_add_k]
      linear_combination (-(F (k + h) * KHeatDiff_chi k a)) * hω
    simp only [fwdDiff, sub_mul, Finset.sum_sub_distrib, h1]
    ring
  induction R with
  | zero => simp
  | succ R ih => rw [Function.iterate_succ_apply', key, ih, pow_succ]; ring

/-- Port of `KHeat_cos_zdist` (`KHeat.lean:1149`). -/
private theorem KHeatDiff_cos_zdist (u : ZMod L) :
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

/-- Port of `KHeat_prod_sum` (`KHeat.lean:681`): the Gaussian sum on the dual torus factorises. -/
private theorem KHeatDiff_prod_sum (v : ℝ) :
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

/-- Port of `KHeat_gauss_le_hkT` (`KHeat.lean:1164`). -/
private theorem KHeatDiff_gauss_le_hkT {w : ℝ} (hw : 0 ≤ w) :
    (L : ℝ)⁻¹ * ∑ x : ZMod L, Real.exp (-w * (2 * Real.pi * (zdist L x : ℝ) / L) ^ 2)
      ≤ Heat.hkT L w 0 := by
  unfold Heat.hkT
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum fun k _ => ?_
  simp only [ZMod.val_zero, Nat.cast_zero, mul_zero, zero_div, Real.cos_zero, one_mul]
  refine Real.exp_le_exp.mpr ?_
  rw [KHeatDiff_cos_zdist]
  have h := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * (zdist L k : ℝ) / L)
  nlinarith

private theorem KHeatDiff_rpow_half (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    x ^ (-(m : ℝ) / 2) = ((Real.sqrt x)⁻¹) ^ m := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hx, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  ring

/-- The Gaussian sum on the dual torus: `L^{-d} Σ_k e^{-w |θ_k|²} ≤ C (√w)^{-d}` for `0 < w ≤ L²`. -/
private theorem KHeatDiff_gauss : ∀ d : ℕ, 1 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L] (w : ℝ), 0 < w → w ≤ (L : ℝ) ^ 2 →
      ((L : ℝ) ^ d)⁻¹ * ∑ k : Zd d L, Real.exp (-w * BAthetaSq d L k) ≤ C * ((Real.sqrt w)⁻¹) ^ d := by
  intro d hd
  obtain ⟨C, c, hC, hc, hle⟩ := Heat.kProd_le d hd
  refine ⟨C, hC, ?_⟩
  intro L _ w hw hwL
  have hLpos : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  have h1 := hle L w hw hwL 0
  have h0 : Heat.kProd d L w 0 = (Heat.hkT L w 0) ^ d := by simp [Heat.kProd]
  have h2 : (0 : ℝ) ≤ (L : ℝ)⁻¹ * ∑ x : ZMod L, Real.exp (-w * (2 * Real.pi * (zdist L x : ℝ) / L) ^ 2) :=
    by positivity
  have h3 : ((L : ℝ) ^ d)⁻¹ * ∑ k : Zd d L, Real.exp (-w * BAthetaSq d L k)
      ≤ (Heat.hkT L w 0) ^ d := by
    rw [KHeatDiff_prod_sum, ← inv_pow, ← mul_pow]
    exact pow_le_pow_left₀ h2 (KHeatDiff_gauss_le_hkT hw.le) d
  refine h3.trans ?_
  rw [← h0]
  refine h1.trans ?_
  simp only [zdistD_zero, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, min_self, mul_zero,
    Real.exp_zero, mul_one]
  rw [KHeatDiff_rpow_half w hw.le d]
  exact mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le

end Four

section Four2

/-- The Fourier bound with `R` summations by parts in direction `j`: `L^{-d} ‖Σ_k A P_n χ_k(a)‖ (4|a_j|_L/√τ)^R ≤ C (√τ)^{-(d+n)}`. -/
private theorem KHeatDiff_four : ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∀ R n : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ τ : ℝ, 1 ≤ τ → τ ≤ (L : ℝ) ^ 2 → ∀ (j : Fin d) (i : Fin n → Fin d) (a : Zd d L),
        ((L : ℝ) ^ d)⁻¹ * ‖∑ k : Zd d L, ((Real.exp (-(τ / g ^ 2) * (1 - BAKhat d L g E m k)) : ℝ) : ℂ)
            * (∏ u : Fin n, (KHeatDiff_chi k (Pi.single (i u) 1) - 1)) * KHeatDiff_chi k a‖
          * (4 * (zdist L (a j) : ℝ) / Real.sqrt τ) ^ R ≤ C * ((Real.sqrt τ)⁻¹) ^ (d + n) := by
  intro d hd Λ κ hΛ hκ R n
  obtain ⟨Cp, c₁, hCp, hc₁, hperk⟩ := KHeatDiff_perk d hd Λ κ hΛ hκ R n
  obtain ⟨CG, hCG, hgauss⟩ := KHeatDiff_gauss d (by omega)
  set c₂ : ℝ := min 1 c₁ with hc₂
  have hc₂0 : 0 < c₂ := lt_min one_pos hc₁
  refine ⟨Cp * (CG * ((Real.sqrt c₂)⁻¹) ^ d), by positivity, ?_⟩
  intro L _ hL g E m hg hgΛ hr τ hτ1 hτL j i a
  have hLpos : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  set σ := Real.sqrt τ with hσ
  have hσ1 : 1 ≤ σ := Real.one_le_sqrt.mpr hτ1
  have hσ0 : 0 < σ := by linarith
  set F : Zd d L → ℂ := fun k => ((Real.exp (-(τ / g ^ 2) * (1 - BAKhat d L g E m k)) : ℝ) : ℂ)
      * ∏ u : Fin n, (KHeatDiff_chi k (Pi.single (i u) 1) - 1) with hF
  set ω : ℂ := ZMod.stdAddChar (-(a j)) - 1 with hω
  set S : ℂ := ∑ k, F k * KHeatDiff_chi k a with hS
  have h1 : ‖S‖ * ‖ω‖ ^ R ≤ ∑ k, ‖(fwdDiff (Pi.single j (1 : ZMod L)))^[R] F k‖ := by
    calc ‖S‖ * ‖ω‖ ^ R = ‖ω ^ R * S‖ := by rw [norm_mul, norm_pow, mul_comm]
      _ = ‖∑ k, (fwdDiff (Pi.single j (1 : ZMod L)))^[R] F k * KHeatDiff_chi k a‖ := by
          rw [KHeatDiff_sbp j a F R]
      _ ≤ ∑ k, ‖(fwdDiff (Pi.single j (1 : ZMod L)))^[R] F k * KHeatDiff_chi k a‖ := norm_sum_le _ _
      _ = _ := Finset.sum_congr rfl fun k _ => by rw [norm_mul, KHeatDiff_chi_norm, mul_one]
  have h2 : ∑ k, ‖(fwdDiff (Pi.single j (1 : ZMod L)))^[R] F k‖
      ≤ Cp * (σ / L) ^ R * σ⁻¹ ^ n * ∑ k : Zd d L, Real.exp (-(c₁ * τ) * BAthetaSq d L k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => hperk L hL g E m hg hgΛ hr τ hτ1 hτL j i k
  have h3 : ∑ k : Zd d L, Real.exp (-(c₁ * τ) * BAthetaSq d L k)
      ≤ ∑ k : Zd d L, Real.exp (-(c₂ * τ) * BAthetaSq d L k) :=
    Finset.sum_le_sum fun k _ => Real.exp_le_exp.mpr (by
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 (min_le_right 1 c₁)) (by linarith : (0 : ℝ) ≤ τ))
        (KHeatDiff_thetaSq_nonneg k)])
  have h4 := hgauss L (c₂ * τ) (by positivity) (by nlinarith [min_le_left 1 c₁])
  have hsq : Real.sqrt (c₂ * τ) = Real.sqrt c₂ * σ := Real.sqrt_mul hc₂0.le τ
  have h5 : (4 * (zdist L (a j) : ℝ) / L) ^ R ≤ ‖ω‖ ^ R := by
    refine pow_le_pow_left₀ (by positivity) ?_ R
    have := KHeatDiff_char_sub_one_ge (-(a j))
    rwa [zdist_neg] at this
  have hrl : (σ / L) ^ R * (L / σ) ^ R = 1 := by
    rw [← mul_pow, show σ / L * (L / σ) = 1 by field_simp, one_pow]
  have hpos : 0 ≤ ((L : ℝ) ^ d)⁻¹ * ‖S‖ := by positivity
  calc ((L : ℝ) ^ d)⁻¹ * ‖S‖ * (4 * (zdist L (a j) : ℝ) / σ) ^ R
      = ((L : ℝ) ^ d)⁻¹ * ‖S‖ * ((4 * (zdist L (a j) : ℝ) / L) ^ R * (L / σ) ^ R) := by
        rw [← mul_pow]; congr 2; field_simp
    _ ≤ ((L : ℝ) ^ d)⁻¹ * ‖S‖ * (‖ω‖ ^ R * (L / σ) ^ R) := by gcongr
    _ = ((L : ℝ) ^ d)⁻¹ * (‖S‖ * ‖ω‖ ^ R) * (L / σ) ^ R := by ring
    _ ≤ ((L : ℝ) ^ d)⁻¹ * (Cp * (σ / L) ^ R * σ⁻¹ ^ n * ∑ k : Zd d L, Real.exp (-(c₂ * τ) * BAthetaSq d L k))
          * (L / σ) ^ R := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          ((h1.trans h2).trans (mul_le_mul_of_nonneg_left h3 (by positivity))) (by positivity)) (by positivity)
    _ = Cp * σ⁻¹ ^ n * (((L : ℝ) ^ d)⁻¹ * ∑ k : Zd d L, Real.exp (-(c₂ * τ) * BAthetaSq d L k)) := by
        linear_combination (Cp * σ⁻¹ ^ n * (((L : ℝ) ^ d)⁻¹ * ∑ k : Zd d L, Real.exp (-(c₂ * τ) * BAthetaSq d L k))) * hrl
    _ ≤ Cp * σ⁻¹ ^ n * (CG * ((Real.sqrt (c₂ * τ))⁻¹) ^ d) := by gcongr
    _ = _ := by rw [hsq, mul_inv, mul_pow, pow_add]; ring

end Four2

/-! ## 7. Regime (i) for `1 ≤ τ ≤ L²`: the polynomial decay -/

section RegA

/-- `L^{-d} ‖Σ_k A P_n χ_k(a)‖ ≤ C (√τ)^{-(d+n)} (1 + |a|²/τ)^{-M}`, `M = ⌊d/2⌋ + 1`: no summation by parts for
`|a|² ≤ τ`, `2M` steps in the direction of the largest coordinate otherwise. -/
private theorem KHeatDiff_A : ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ τ : ℝ, 1 ≤ τ → τ ≤ (L : ℝ) ^ 2 → ∀ (i : Fin n → Fin d) (a : Zd d L),
        ((L : ℝ) ^ d)⁻¹ * ‖∑ k : Zd d L, ((Real.exp (-(τ / g ^ 2) * (1 - BAKhat d L g E m k)) : ℝ) : ℂ)
            * (∏ u : Fin n, (KHeatDiff_chi k (Pi.single (i u) 1) - 1)) * KHeatDiff_chi k a‖
          ≤ C * ((Real.sqrt τ)⁻¹) ^ (d + n) * ((1 + (zdistD d L a : ℝ) ^ 2 / τ) ^ (d / 2 + 1))⁻¹ := by
  intro d hd Λ κ hΛ hκ n
  set M : ℕ := d / 2 + 1 with hM
  obtain ⟨C₀, hC₀, h0⟩ := KHeatDiff_four d hd Λ κ hΛ hκ 0 n
  obtain ⟨C₁, hC₁, h1⟩ := KHeatDiff_four d hd Λ κ hΛ hκ (2 * M) n
  refine ⟨2 ^ M * C₀ + C₁ * ((d : ℝ) / 4) ^ (2 * M) * 2 ^ M, by positivity, ?_⟩
  intro L _ hL g E m hg hgΛ hr τ hτ1 hτL i a
  set σ : ℝ := Real.sqrt τ with hσ
  have hσ1 : 1 ≤ σ := Real.one_le_sqrt.mpr hτ1
  have hσsq : σ ^ 2 = τ := Real.sq_sqrt (by linarith)
  have hτ0 : 0 < τ := by linarith
  set D : ℝ := (zdistD d L a : ℝ) with hD
  have hD0 : 0 ≤ D := Nat.cast_nonneg _
  set t : ℝ := D ^ 2 / τ with ht
  have ht0 : 0 ≤ t := by positivity
  have hQ0 : 0 < (1 + t) ^ M := by positivity
  have hι : 0 ≤ σ⁻¹ ^ (d + n) := by positivity
  set X : ℝ := ((L : ℝ) ^ d)⁻¹ * ‖∑ k : Zd d L, ((Real.exp (-(τ / g ^ 2) * (1 - BAKhat d L g E m k)) : ℝ) : ℂ)
            * (∏ u : Fin n, (KHeatDiff_chi k (Pi.single (i u) 1) - 1)) * KHeatDiff_chi k a‖ with hX
  have hX0 : 0 ≤ X := by positivity
  have hd0 : 0 < d := by omega
  by_cases hcase : t ≤ 1
  · have h := h0 L hL g E m hg hgΛ hr τ hτ1 hτL ⟨0, hd0⟩ i a
    simp only [pow_zero, mul_one] at h
    have hQ : (1 + t) ^ M ≤ 2 ^ M := pow_le_pow_left₀ (by positivity) (by linarith) M
    have h2 : 1 ≤ 2 ^ M * ((1 + t) ^ M)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hQ0]; linarith
    calc X ≤ C₀ * σ⁻¹ ^ (d + n) := h
      _ = C₀ * σ⁻¹ ^ (d + n) * 1 := (mul_one _).symm
      _ ≤ C₀ * σ⁻¹ ^ (d + n) * (2 ^ M * ((1 + t) ^ M)⁻¹) := by gcongr
      _ ≤ _ := by
          have : 0 ≤ C₁ * ((d : ℝ) / 4) ^ (2 * M) * 2 ^ M * σ⁻¹ ^ (d + n) * ((1 + t) ^ M)⁻¹ := by positivity
          nlinarith
  · replace hcase := not_le.mp hcase
    obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ (fun l : Fin d => zdist L (a l))
      ⟨⟨0, hd0⟩, Finset.mem_univ _⟩
    set z : ℝ := (zdist L (a j₀) : ℝ) with hz
    have hDz : D ≤ d * z := by
      rw [hD]; unfold zdistD; push_cast
      calc ∑ l, (zdist L (a l) : ℝ) ≤ ∑ _l : Fin d, z :=
            Finset.sum_le_sum fun l _ => by rw [hz]; exact_mod_cast hj₀ l (Finset.mem_univ l)
        _ = d * z := by simp
    have hD1 : 1 < D := by
      have : 1 < D ^ 2 := by
        have := (one_lt_div hτ0).mp hcase
        linarith
      nlinarith
    have hz0 : 0 < z := by
      have : (0 : ℝ) < d := by exact_mod_cast hd0
      by_contra hneg
      nlinarith
    have hz1 : 1 ≤ z := by
      rw [hz] at hz0 ⊢
      have : 0 < zdist L (a j₀) := by exact_mod_cast hz0
      exact_mod_cast this
    have h := h1 L hL g E m hg hgΛ hr τ hτ1 hτL j₀ i a
    have htm : t = (D / σ) ^ 2 := by rw [ht, div_pow, hσsq]
    have hw : (4 / (d : ℝ)) ^ (2 * M) * t ^ M ≤ (4 * z / σ) ^ (2 * M) := by
      have e : (4 / (d : ℝ)) ^ (2 * M) * t ^ M = (4 / (d : ℝ) * (D / σ)) ^ (2 * M) := by
        rw [htm, ← pow_mul, ← mul_pow]
      rw [e]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      have : (0 : ℝ) < d := by exact_mod_cast hd0
      rw [show 4 / (d : ℝ) * (D / σ) = 4 * D / (d * σ) by field_simp, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hQt : (1 + t) ^ M ≤ 2 ^ M * t ^ M := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) M
    have hdM : 0 < ((d : ℝ) / 4) ^ (2 * M) := by positivity
    have hkey : X * (1 + t) ^ M ≤ C₁ * ((d : ℝ) / 4) ^ (2 * M) * 2 ^ M * σ⁻¹ ^ (d + n) := by
      calc X * (1 + t) ^ M ≤ X * (2 ^ M * t ^ M) := by gcongr
        _ = 2 ^ M * ((d : ℝ) / 4) ^ (2 * M) * (X * ((4 / (d : ℝ)) ^ (2 * M) * t ^ M)) := by
            have : ((d : ℝ) / 4) ^ (2 * M) * (4 / (d : ℝ)) ^ (2 * M) = 1 := by
              rw [← mul_pow, show (d : ℝ) / 4 * (4 / d) = 1 by field_simp, one_pow]
            linear_combination (-(2 ^ M * (X * t ^ M))) * this
        _ ≤ 2 ^ M * ((d : ℝ) / 4) ^ (2 * M) * (X * (4 * z / σ) ^ (2 * M)) := by gcongr
        _ ≤ 2 ^ M * ((d : ℝ) / 4) ^ (2 * M) * (C₁ * σ⁻¹ ^ (d + n)) := by gcongr
        _ = _ := by ring
    calc X = X * (1 + t) ^ M * ((1 + t) ^ M)⁻¹ := by field_simp
      _ ≤ C₁ * ((d : ℝ) / 4) ^ (2 * M) * 2 ^ M * σ⁻¹ ^ (d + n) * ((1 + t) ^ M)⁻¹ := by gcongr
      _ ≤ _ := by
          have : 0 ≤ 2 ^ M * C₀ * σ⁻¹ ^ (d + n) * ((1 + t) ^ M)⁻¹ := by positivity
          nlinarith

end RegA

/-! ## 8. Regime (i) for `0 < τ ≤ 1`: from the tail bound `kBA_le` -/

section RegB

private theorem KHeatDiff_exp_poly {c r : ℝ} (hc : 0 < c) (hr : 1 ≤ r) (M : ℕ) :
    Real.exp (-(c * r)) * (1 + r ^ 2) ^ M ≤ ((2 * M).factorial : ℝ) * 2 ^ M / c ^ (2 * M) := by
  have h1 : (1 + r ^ 2) ^ M ≤ 2 ^ M * r ^ (2 * M) := by
    rw [pow_mul, ← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by nlinarith) M
  have h2 := Real.pow_div_factorial_le_exp (c * r) (by positivity) (2 * M)
  rw [div_le_iff₀ (by positivity), mul_pow] at h2
  calc Real.exp (-(c * r)) * (1 + r ^ 2) ^ M ≤ Real.exp (-(c * r)) * (2 ^ M * r ^ (2 * M)) := by gcongr
    _ = 2 ^ M * (r ^ (2 * M) * Real.exp (-(c * r))) := by ring
    _ ≤ 2 ^ M * (((2 * M).factorial : ℝ) / c ^ (2 * M)) := by
        gcongr
        rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
        nlinarith
    _ = _ := by ring

/-- `0 < τ ≤ 1`: `kBA τ b (1 + |b|²)^M ≤ C` for every `b`. -/
private theorem KHeatDiff_pt : ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ b : Zd d L,
        kBA d L g E m τ b * (1 + (zdistD d L b : ℝ) ^ 2) ^ (d / 2 + 1) ≤ C := by
  intro d hd Λ κ hΛ hκ
  obtain ⟨C₁, c, hC₁, hc, hle⟩ := kBA_le d hd Λ κ hΛ hκ
  set M : ℕ := d / 2 + 1 with hM
  refine ⟨max 1 (C₁ * (((2 * M).factorial : ℝ) * 2 ^ M / c ^ (2 * M))), by positivity, ?_⟩
  intro L _ hL g E m hg hgΛ hr τ hτ hτ1 b
  have hk := kBA_basic d L g E m hg hr.1
  have hk0 := hk.1 τ hτ.le b
  by_cases hb : zdistD d L b = 0
  · rw [hb]
    simpa using (hk.2.2.1 τ hτ.le b).trans (le_max_left _ _)
  · have hb1 : (1 : ℝ) ≤ zdistD d L b := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hb
    have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ L))
    have h := hle L hL g E m hg hgΛ hr τ hτ (hτ1.trans hL1) b
    have hmin : (zdistD d L b : ℝ) ≤ min ((zdistD d L b : ℝ) ^ 2 / τ) (zdistD d L b : ℝ) := by
      refine le_min ?_ le_rfl
      rw [le_div_iff₀ hτ]; nlinarith
    have h2 : kBA d L g E m τ b ≤ C₁ * Real.exp (-(c * (zdistD d L b : ℝ))) := by
      refine h.trans ?_
      have e1 : min 1 (τ ^ (-(d : ℝ) / 2)) ≤ 1 := min_le_left _ _
      have e2 : Real.exp (-c * min ((zdistD d L b : ℝ) ^ 2 / τ) (zdistD d L b : ℝ))
          ≤ Real.exp (-(c * (zdistD d L b : ℝ))) :=
        Real.exp_le_exp.mpr (by nlinarith)
      calc C₁ * min 1 (τ ^ (-(d : ℝ) / 2)) * Real.exp (-c * min ((zdistD d L b : ℝ) ^ 2 / τ) (zdistD d L b : ℝ))
          ≤ C₁ * 1 * Real.exp (-(c * (zdistD d L b : ℝ))) := by gcongr
        _ = _ := by ring
    calc kBA d L g E m τ b * (1 + (zdistD d L b : ℝ) ^ 2) ^ M
        ≤ C₁ * Real.exp (-(c * (zdistD d L b : ℝ))) * (1 + (zdistD d L b : ℝ) ^ 2) ^ M := by gcongr
      _ = C₁ * (Real.exp (-(c * (zdistD d L b : ℝ))) * (1 + (zdistD d L b : ℝ) ^ 2) ^ M) := by ring
      _ ≤ C₁ * (((2 * M).factorial : ℝ) * 2 ^ M / c ^ (2 * M)) := by
          gcongr; exact KHeatDiff_exp_poly hc hb1 M
      _ ≤ _ := le_max_right _ _

private theorem KHeatDiff_zdistD_single_le (j : Fin d) : zdistD d L (Pi.single j (1 : ZMod L) : Zd d L) ≤ 1 := by
  unfold zdistD
  rw [Finset.sum_eq_single j]
  · simp only [Pi.single_eq_same]
    unfold zdist
    refine (min_le_left _ _).trans ?_
    rw [ZMod.val_one_eq_one_mod]
    exact Nat.mod_le _ _
  · intro i _ hij; simp [Pi.single_eq_of_ne hij]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- `0 < τ ≤ 1`: the shifted values `kBA τ (a + u)`, `|u| ≤ 2`, decay like `(1 + |a|²)^{-M}`. -/
private theorem KHeatDiff_B : ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ (a u : Zd d L), zdistD d L u ≤ 2 →
        kBA d L g E m τ (a + u) * (1 + (zdistD d L a : ℝ) ^ 2) ^ (d / 2 + 1) ≤ C := by
  intro d hd Λ κ hΛ hκ
  obtain ⟨C, hC, hpt⟩ := KHeatDiff_pt d hd Λ κ hΛ hκ
  set M : ℕ := d / 2 + 1 with hM
  refine ⟨9 ^ M * C, by positivity, ?_⟩
  intro L _ hL g E m hg hgΛ hr τ hτ hτ1 a u hu
  have hk0 := (kBA_basic d L g E m hg hr.1).1 τ hτ.le (a + u)
  have h1 : zdistD d L a ≤ zdistD d L (a + u) + 2 := by
    have := zdistD_add_le d L (a + u) (-u)
    rw [add_neg_cancel_right, zdistD_neg] at this
    omega
  have h2 : (1 + (zdistD d L a : ℝ) ^ 2) ≤ 9 * (1 + (zdistD d L (a + u) : ℝ) ^ 2) := by
    have : (zdistD d L a : ℝ) ≤ zdistD d L (a + u) + 2 := by exact_mod_cast h1
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (zdistD d L a)) this 2
    nlinarith [sq_nonneg ((zdistD d L (a + u) : ℝ) - 1 / 4)]
  calc kBA d L g E m τ (a + u) * (1 + (zdistD d L a : ℝ) ^ 2) ^ M
      ≤ kBA d L g E m τ (a + u) * (9 * (1 + (zdistD d L (a + u) : ℝ) ^ 2)) ^ M := by gcongr
    _ = 9 ^ M * (kBA d L g E m τ (a + u) * (1 + (zdistD d L (a + u) : ℝ) ^ 2) ^ M) := by
        rw [mul_pow]; ring
    _ ≤ 9 ^ M * C := by gcongr; exact hpt L hL g E m hg hgΛ hr τ hτ hτ1 (a + u)

end RegB

/-! ## 9. Targets: the unit differences of `kBA` in regime (i) -/

section Targets

variable {d L : ℕ} [NeZero L]

private theorem KHeatDiff_kBA_chi (g E : ℝ) (m : ℂ) (hg : 0 < g) (τ : ℝ) (b : Zd d L) :
    kBA d L g E m τ b = ((L : ℝ) ^ d)⁻¹ * ∑ k : Zd d L,
      Real.exp (-(τ / g ^ 2) * (1 - BAKhat d L g E m k)) * (KHeatDiff_chi k b).re := by
  rw [kBA_fourier d L g E m hg τ b]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [KHeatDiff_chi_re]

/-- The first difference is the real part of the Fourier sum with the prefactor `χ_k(e_j) - 1`. -/
private theorem KHeatDiff_diff1 (g E : ℝ) (m : ℂ) (hg : 0 < g) (τ : ℝ) (a : Zd d L) (j : Fin d) :
    |kBA d L g E m τ (a + Pi.single j 1) - kBA d L g E m τ a|
      ≤ ((L : ℝ) ^ d)⁻¹ * ‖∑ k : Zd d L, ((Real.exp (-(τ / g ^ 2) * (1 - BAKhat d L g E m k)) : ℝ) : ℂ)
          * (∏ u : Fin 1, (KHeatDiff_chi k (Pi.single ((![j] : Fin 1 → Fin d) u) 1) - 1)) * KHeatDiff_chi k a‖ := by
  have hLpos : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  have hLL : 0 < ((L : ℝ) ^ d)⁻¹ := by positivity
  have e : kBA d L g E m τ (a + Pi.single j 1) - kBA d L g E m τ a = ((L : ℝ) ^ d)⁻¹ *
      (∑ k : Zd d L, ((Real.exp (-(τ / g ^ 2) * (1 - BAKhat d L g E m k)) : ℝ) : ℂ)
        * (∏ u : Fin 1, (KHeatDiff_chi k (Pi.single ((![j] : Fin 1 → Fin d) u) 1) - 1)) * KHeatDiff_chi k a).re := by
    rw [KHeatDiff_kBA_chi g E m hg, KHeatDiff_kBA_chi g E m hg, ← mul_sub, ← Finset.sum_sub_distrib, Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero]
    rw [mul_assoc, Complex.re_ofReal_mul, show (KHeatDiff_chi k (Pi.single j 1) - 1) * KHeatDiff_chi k a
      = KHeatDiff_chi k (a + Pi.single j 1) - KHeatDiff_chi k a by rw [KHeatDiff_chi_add_a]; ring, Complex.sub_re]
    ring
  rw [e, abs_mul, abs_of_pos hLL]
  exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hLL.le

private theorem KHeatDiff_diff2 (g E : ℝ) (m : ℂ) (hg : 0 < g) (τ : ℝ) (a : Zd d L) (i j : Fin d) :
    |kBA d L g E m τ (a + Pi.single i 1 + Pi.single j 1) - kBA d L g E m τ (a + Pi.single i 1)
        - kBA d L g E m τ (a + Pi.single j 1) + kBA d L g E m τ a|
      ≤ ((L : ℝ) ^ d)⁻¹ * ‖∑ k : Zd d L, ((Real.exp (-(τ / g ^ 2) * (1 - BAKhat d L g E m k)) : ℝ) : ℂ)
          * (∏ u : Fin 2, (KHeatDiff_chi k (Pi.single ((![i, j] : Fin 2 → Fin d) u) 1) - 1)) * KHeatDiff_chi k a‖ := by
  have hLpos : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  have hLL : 0 < ((L : ℝ) ^ d)⁻¹ := by positivity
  have e : kBA d L g E m τ (a + Pi.single i 1 + Pi.single j 1) - kBA d L g E m τ (a + Pi.single i 1)
        - kBA d L g E m τ (a + Pi.single j 1) + kBA d L g E m τ a = ((L : ℝ) ^ d)⁻¹ *
      (∑ k : Zd d L, ((Real.exp (-(τ / g ^ 2) * (1 - BAKhat d L g E m k)) : ℝ) : ℂ)
        * (∏ u : Fin 2, (KHeatDiff_chi k (Pi.single ((![i, j] : Fin 2 → Fin d) u) 1) - 1)) * KHeatDiff_chi k a).re := by
    rw [KHeatDiff_kBA_chi g E m hg, KHeatDiff_kBA_chi g E m hg, KHeatDiff_kBA_chi g E m hg,
      KHeatDiff_kBA_chi g E m hg, ← mul_sub, ← mul_sub, ← mul_add, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mul_assoc, Complex.re_ofReal_mul, show (KHeatDiff_chi k (Pi.single i 1) - 1) * (KHeatDiff_chi k (Pi.single j 1) - 1)
      * KHeatDiff_chi k a = KHeatDiff_chi k (a + Pi.single i 1 + Pi.single j 1) - KHeatDiff_chi k (a + Pi.single i 1)
        - KHeatDiff_chi k (a + Pi.single j 1) + KHeatDiff_chi k a by
      rw [KHeatDiff_chi_add_a, KHeatDiff_chi_add_a, KHeatDiff_chi_add_a]; ring]
    simp only [Complex.add_re, Complex.sub_re]
    ring
  rw [e, abs_mul, abs_of_pos hLL]
  exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hLL.le

/-- The two regimes `τ ≤ 1` and `1 ≤ τ ≤ L²` assembled into the pinned shape. -/
private theorem KHeatDiff_comb {X CA CB e : ℝ} (d n : ℕ) {τ D : ℝ} (hτ : 0 < τ) (hX : 0 ≤ X)
    (he : e = -((d : ℝ) + n) / 2) (hCA : 0 ≤ CA)
    (hA : 1 ≤ τ → X ≤ CA * ((Real.sqrt τ)⁻¹) ^ (d + n) * ((1 + D ^ 2 / τ) ^ (d / 2 + 1))⁻¹)
    (hB : τ ≤ 1 → X * (1 + D ^ 2) ^ (d / 2 + 1) ≤ CB) :
    X ≤ max CA CB * min 1 (τ ^ e) * (1 + D ^ 2 / max τ 1) ^ (-(((d / 2 + 1 : ℕ) : ℝ))) := by
  have hnd : (0 : ℝ) ≤ (d : ℝ) + n := by positivity
  rcases le_total τ 1 with h1 | h1
  · rw [min_eq_left (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hτ h1 (by rw [he]; linarith)), max_eq_right h1, div_one,
      Real.rpow_neg (by positivity), Real.rpow_natCast, mul_one, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    exact (hB h1).trans (le_max_right _ _)
  · have e1 : τ ^ e = ((Real.sqrt τ)⁻¹) ^ (d + n) := by
      rw [he]; have := KHeatDiff_rpow_half τ hτ.le (d + n); push_cast at this; exact this
    rw [min_eq_right (by rw [e1]; exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr h1))),
      max_eq_left h1, e1, Real.rpow_neg (by positivity), Real.rpow_natCast]
    exact (hA h1).trans (by gcongr; exact le_max_left _ _)

/-- **Unit first differences, regime (i)** (target of T2336, statement of `T2336_kBA_diff1_le` in
`docs/tickets/checks/T2336-check.lean`): polynomial decay of order `M = ⌊d/2⌋ + 1`, `max τ 1` in the decay factor. -/
theorem kBA_diff1_le : ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → ∀ (a : Zd d L) (j : Fin d),
        |kBA d L g E m τ (a + Pi.single j 1) - kBA d L g E m τ a|
          ≤ C * min 1 (τ ^ (-((d : ℝ) + 1) / 2))
            * (1 + (zdistD d L a : ℝ) ^ 2 / max τ 1) ^ (-(((d / 2 + 1 : ℕ) : ℝ))) := by
  intro d hd Λ κ hΛ hκ
  obtain ⟨CA, hCA, hA⟩ := KHeatDiff_A d hd Λ κ hΛ hκ 1
  obtain ⟨CB, hCB, hB⟩ := KHeatDiff_B d hd Λ κ hΛ hκ
  refine ⟨max CA (2 * CB), lt_max_of_lt_left hCA, ?_⟩
  intro L _ hL g E m hg hgΛ hr τ hτ hτL a j
  refine KHeatDiff_comb (CB := 2 * CB) (e := -((d : ℝ) + 1) / 2) d 1 hτ (abs_nonneg _) (by norm_num) hCA.le ?_ ?_
  · intro h1
    exact (KHeatDiff_diff1 g E m hg τ a j).trans (hA L hL g E m hg hgΛ hr τ h1 hτL ![j] a)
  · intro h1
    have h2 := hB L hL g E m hg hgΛ hr τ hτ h1 a (Pi.single j 1) ((KHeatDiff_zdistD_single_le j).trans (by norm_num))
    have h3 := hB L hL g E m hg hgΛ hr τ hτ h1 a 0 (by simp)
    have h4 := (kBA_basic d L g E m hg hr.1).1 τ hτ.le (a + Pi.single j 1)
    have h5 := (kBA_basic d L g E m hg hr.1).1 τ hτ.le (a + 0)
    have h6 : |kBA d L g E m τ (a + Pi.single j 1) - kBA d L g E m τ a|
        ≤ kBA d L g E m τ (a + Pi.single j 1) + kBA d L g E m τ (a + 0) := by
      rw [add_zero] at h5 ⊢; rw [abs_le]; constructor <;> linarith
    calc _ * _ ≤ (kBA d L g E m τ (a + Pi.single j 1) + kBA d L g E m τ (a + 0)) * _ := by gcongr
      _ ≤ 2 * CB := by rw [add_mul]; linarith

/-- **Unit second differences, regime (i)** (target of T2336, `T2336_kBA_diff2_le`): same decay factor, `τ^{-(d+2)/2}`. -/
theorem kBA_diff2_le : ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ τ : ℝ, 0 < τ → τ ≤ (L : ℝ) ^ 2 → ∀ (a : Zd d L) (i j : Fin d),
        |kBA d L g E m τ (a + Pi.single i 1 + Pi.single j 1) - kBA d L g E m τ (a + Pi.single i 1)
            - kBA d L g E m τ (a + Pi.single j 1) + kBA d L g E m τ a|
          ≤ C * min 1 (τ ^ (-((d : ℝ) + 2) / 2))
            * (1 + (zdistD d L a : ℝ) ^ 2 / max τ 1) ^ (-(((d / 2 + 1 : ℕ) : ℝ))) := by
  intro d hd Λ κ hΛ hκ
  obtain ⟨CA, hCA, hA⟩ := KHeatDiff_A d hd Λ κ hΛ hκ 2
  obtain ⟨CB, hCB, hB⟩ := KHeatDiff_B d hd Λ κ hΛ hκ
  refine ⟨max CA (4 * CB), lt_max_of_lt_left hCA, ?_⟩
  intro L _ hL g E m hg hgΛ hr τ hτ hτL a i j
  refine KHeatDiff_comb (CB := 4 * CB) (e := -((d : ℝ) + 2) / 2) d 2 hτ (abs_nonneg _) (by norm_num) hCA.le ?_ ?_
  · intro h1
    exact (KHeatDiff_diff2 g E m hg τ a i j).trans (hA L hL g E m hg hgΛ hr τ h1 hτL ![i, j] a)
  · intro h1
    have s1 : zdistD d L (Pi.single i (1 : ZMod L)) ≤ 2 := (KHeatDiff_zdistD_single_le i).trans (by norm_num)
    have s2 : zdistD d L (Pi.single j (1 : ZMod L)) ≤ 2 := (KHeatDiff_zdistD_single_le j).trans (by norm_num)
    have s3 : zdistD d L (Pi.single i (1 : ZMod L) + Pi.single j 1) ≤ 2 :=
      (zdistD_add_le d L _ _).trans (by have := KHeatDiff_zdistD_single_le (L := L) i; have := KHeatDiff_zdistD_single_le (L := L) j; omega)
    have h2 := hB L hL g E m hg hgΛ hr τ hτ h1 a _ s1
    have h3 := hB L hL g E m hg hgΛ hr τ hτ h1 a _ s2
    have h4 := hB L hL g E m hg hgΛ hr τ hτ h1 a _ s3
    have h5 := hB L hL g E m hg hgΛ hr τ hτ h1 a 0 (by simp)
    have k0 := fun b => (kBA_basic d L g E m hg hr.1).1 τ hτ.le b
    rw [add_zero] at h5
    rw [← add_assoc] at h4
    have h6 : |kBA d L g E m τ (a + Pi.single i 1 + Pi.single j 1) - kBA d L g E m τ (a + Pi.single i 1)
        - kBA d L g E m τ (a + Pi.single j 1) + kBA d L g E m τ a|
        ≤ kBA d L g E m τ (a + Pi.single i 1 + Pi.single j 1) + kBA d L g E m τ (a + Pi.single i 1)
          + kBA d L g E m τ (a + Pi.single j 1) + kBA d L g E m τ a := by
      rw [abs_le]; constructor <;> linarith [k0 (a + Pi.single i 1 + Pi.single j 1), k0 (a + Pi.single i 1),
        k0 (a + Pi.single j 1), k0 a]
    calc _ * _ ≤ (kBA d L g E m τ (a + Pi.single i 1 + Pi.single j 1) + kBA d L g E m τ (a + Pi.single i 1)
          + kBA d L g E m τ (a + Pi.single j 1) + kBA d L g E m τ a) * _ := by gcongr
      _ ≤ 4 * CB := by simp only [add_mul]; linarith

end Targets

/-! ## 10. The regularity of the symbol (public) -/

section SymbolPub

private theorem KHeatDiff_iter_ofReal {d L : ℕ} [NeZero L] (h : Zd d L) (f : Zd d L → ℝ) (i : ℕ) :
    (fun k => (((fwdDiff h)^[i] f k : ℝ) : ℂ)) = (fwdDiff h)^[i] (fun k => (f k : ℂ)) := by
  induction i generalizing f with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have e : fwdDiff h (fun k => (f k : ℂ)) = fun k => ((fwdDiff h f k : ℝ) : ℂ) := by
      funext k; simp [fwdDiff]
    rw [e]
    exact ih (fwdDiff h f)

/-- **Regularity of the symbol `K̂` in one direction** (`A:50-56`; from `BAK_off_le` through all moments of `K`):
`|Δ_j K̂(k)| ≤ C g² L^{-1} (|θ_k| + L^{-1})` and `|Δ_j^i K̂(k)| ≤ C g² L^{-i}` for `1 ≤ i ≤ N`, uniformly in `L ≥ 3`,
`g ∈ (0, Λ]`; `Δ_j f(k) = f(k + e_j) - f(k)` on the dual torus. -/
theorem BAKhat_diff_le : ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ (j : Fin d) (k : Zd d L),
        |fwdDiff (Pi.single j (1 : ZMod L)) (BAKhat d L g E m) k|
            ≤ C * g ^ 2 * (L : ℝ)⁻¹ * (Real.sqrt (BAthetaSq d L k) + (L : ℝ)⁻¹) ∧
        ∀ i : ℕ, 1 ≤ i → i ≤ N →
          |(fwdDiff (Pi.single j (1 : ZMod L)))^[i] (BAKhat d L g E m) k| ≤ C * g ^ 2 * ((L : ℝ)⁻¹) ^ i := by
  intro d hd Λ κ hΛ hκ N
  obtain ⟨Cm, hCm, hmom⟩ := KHeatDiff_moment d hd Λ κ hΛ hκ (N + 2)
  refine ⟨(8 ^ N + 32) * Cm, by positivity, ?_⟩
  intro L _ hL g E m hg hgΛ hr j k
  have hLpos : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  have hmom' := hmom L hL g E m hg hgΛ hr
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_le_four
  set u : ℝ := (L : ℝ)⁻¹ with hu
  have hu0 : 0 < u := by positivity
  have e1 : 2 * Real.pi / L = 2 * Real.pi * u := by rw [hu]; ring
  have hθ : 2 * Real.pi * u ≤ 8 * u := by nlinarith
  have hc : ∀ i, |(fwdDiff (Pi.single j (1 : ZMod L)))^[i] (BAKhat d L g E m) k|
      = ‖(fwdDiff (Pi.single j (1 : ZMod L)))^[i] (fun k' => (BAKhat d L g E m k' : ℂ)) k‖ := fun i => by
    rw [← KHeatDiff_iter_ofReal, Complex.norm_real, Real.norm_eq_abs]
  have hg2 : 0 ≤ g ^ 2 := sq_nonneg g
  refine ⟨?_, fun i hi1 hiN => ?_⟩
  · set ϑ := Real.sqrt (BAthetaSq d L k) with hϑ
    have hϑ0 : 0 ≤ ϑ := Real.sqrt_nonneg _
    have hϑk : ∀ l, 2 * Real.pi * (zdist L (k l) : ℝ) / L ≤ ϑ := fun l =>
      (Real.le_sqrt (by positivity) (KHeatDiff_thetaSq_nonneg k)).mpr (KHeatDiff_theta_sq_le k l)
    have h1 := KHeatDiff_symb_first g E m j k hϑ0 hϑk
    have hM2 := hmom' 2 (by norm_num) (by omega)
    have hB : (2 * Real.pi * u) ^ 2 / 2 + ϑ * (2 * Real.pi * u) ≤ 32 * u * (ϑ + u) := by
      have : Real.pi ^ 2 ≤ 16 := by nlinarith
      nlinarith [mul_nonneg hϑ0 hu0.le, mul_nonneg hu0.le hu0.le]
    have h32 : 32 * Cm ≤ (8 ^ N + 32) * Cm := mul_le_mul_of_nonneg_right (by linarith [pow_pos (by norm_num : (0 : ℝ) < 8) N]) hCm.le
    have hc1 := hc 1
    simp only [Function.iterate_one] at hc1
    rw [hc1, e1] at *
    calc _ ≤ _ := h1
      _ ≤ (32 * u * (ϑ + u)) * (Cm * g ^ 2) := mul_le_mul hB hM2 (Finset.sum_nonneg fun a _ => mul_nonneg (BAK_nonneg d L g E m 0 a) (by positivity)) (by positivity)
      _ = (32 * Cm) * (g ^ 2 * u * (ϑ + u)) := by ring
      _ ≤ ((8 ^ N + 32) * Cm) * (g ^ 2 * u * (ϑ + u)) := mul_le_mul_of_nonneg_right h32 (by positivity)
      _ = _ := by ring
  · rw [hc i]
    refine (KHeatDiff_symb_higher g E m j i k).trans ?_
    have hMi := hmom' i hi1 (by omega)
    have h8 : (8 : ℝ) ^ i ≤ 8 ^ N := pow_le_pow_right₀ (by norm_num) hiN
    rw [e1]
    calc (2 * Real.pi * u) ^ i * ∑ a : Zd d L, BAK d L g E m 0 a * (zdistD d L a : ℝ) ^ i
        ≤ (8 * u) ^ i * (Cm * g ^ 2) :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hθ i) hMi
            (Finset.sum_nonneg fun a _ => mul_nonneg (BAK_nonneg d L g E m 0 a) (by positivity)) (by positivity)
      _ = 8 ^ i * Cm * (g ^ 2 * u ^ i) := by rw [mul_pow]; ring
      _ ≤ ((8 ^ N + 32) * Cm) * (g ^ 2 * u ^ i) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          nlinarith [mul_le_mul_of_nonneg_right h8 hCm.le]
      _ = _ := by ring

end SymbolPub

/-! ## 11. Compiled nonempty instances (`d = 3`, `L = 4`, `Λ = 10`, `κ = Im m₀`, flow point `P`) -/

namespace KHeatDiffInst

open RBM.BA.MFixedPointInst

/-- `kBA_diff1_le` at the data of the ticket: `d = 3`, `L = 4`, `τ = 1 ≤ L²`, `a = (1, 0, 2)` (`|a| = 3`), `j = 0`. -/
theorem inst_diff1 :
    ∃ C : ℝ, 0 < C ∧
      |kBA 3 4 P.g0 P.E P.m0 1 (![1, 0, 2] + Pi.single 0 1) - kBA 3 4 P.g0 P.E P.m0 1 ![1, 0, 2]|
        ≤ C * min 1 ((1 : ℝ) ^ (-(((3 : ℕ) : ℝ) + 1) / 2))
          * (1 + ((zdistD 3 4 ![1, 0, 2] : ℕ) : ℝ) ^ 2 / max (1 : ℝ) 1) ^ (-(((3 / 2 + 1 : ℕ) : ℝ))) := by
  obtain ⟨C, hC, h⟩ := kBA_diff1_le 3 (by norm_num) 10 P.m0.im (by norm_num) P.real.1.1
  exact ⟨C, hC, h 4 (by norm_num) P.g0 P.E P.m0 P.g0_pos P.g0_le P.real 1 one_pos (by norm_num) _ 0⟩

/-- `kBA_diff2_le` at the same data, `(i, j) = (0, 2)`. -/
theorem inst_diff2 :
    ∃ C : ℝ, 0 < C ∧
      |kBA 3 4 P.g0 P.E P.m0 1 (![1, 0, 2] + Pi.single 0 1 + Pi.single 2 1)
          - kBA 3 4 P.g0 P.E P.m0 1 (![1, 0, 2] + Pi.single 0 1)
          - kBA 3 4 P.g0 P.E P.m0 1 (![1, 0, 2] + Pi.single 2 1) + kBA 3 4 P.g0 P.E P.m0 1 ![1, 0, 2]|
        ≤ C * min 1 ((1 : ℝ) ^ (-(((3 : ℕ) : ℝ) + 2) / 2))
          * (1 + ((zdistD 3 4 ![1, 0, 2] : ℕ) : ℝ) ^ 2 / max (1 : ℝ) 1) ^ (-(((3 / 2 + 1 : ℕ) : ℝ))) := by
  obtain ⟨C, hC, h⟩ := kBA_diff2_le 3 (by norm_num) 10 P.m0.im (by norm_num) P.real.1.1
  exact ⟨C, hC, h 4 (by norm_num) P.g0 P.E P.m0 P.g0_pos P.g0_le P.real 1 one_pos (by norm_num) _ 0 2⟩

/-- `BAKhat_diff_le` at `k = (1, 0, 2)`, `j = 1`, orders `1` and `3` (`N = 5`). -/
theorem inst_symb :
    ∃ C : ℝ, 0 < C ∧
      |fwdDiff (Pi.single (1 : Fin 3) (1 : ZMod 4)) (BAKhat 3 4 P.g0 P.E P.m0) ![1, 0, 2]|
          ≤ C * P.g0 ^ 2 * ((4 : ℕ) : ℝ)⁻¹ * (Real.sqrt (BAthetaSq 3 4 ![1, 0, 2]) + ((4 : ℕ) : ℝ)⁻¹) ∧
      |(fwdDiff (Pi.single (1 : Fin 3) (1 : ZMod 4)))^[3] (BAKhat 3 4 P.g0 P.E P.m0) ![1, 0, 2]|
          ≤ C * P.g0 ^ 2 * (((4 : ℕ) : ℝ)⁻¹) ^ 3 := by
  obtain ⟨C, hC, h⟩ := BAKhat_diff_le 3 (by norm_num) 10 P.m0.im (by norm_num) P.real.1.1 5
  obtain ⟨h1, h2⟩ := h 4 (by norm_num) P.g0 P.E P.m0 P.g0_pos P.g0_le P.real 1 ![1, 0, 2]
  exact ⟨C, hC, h1, h2 3 (by norm_num) (by norm_num)⟩

end KHeatDiffInst


end RBM.BA

end
