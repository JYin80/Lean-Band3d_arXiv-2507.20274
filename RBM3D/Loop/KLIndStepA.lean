/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Batteries.Tactic.OpenPrivate
import RBM3D.Loop.KLMolecule
import RBM3D.Loop.KBound

/-!
# The `K`-loop layer, KL10a: the first half of `(eq:ind-step-bound)` (`d ≥ 3`)

Ticket T2100 (`A_deterministic_estimates.tex:703-790`).  Names are in `RBM.Loop`; every helper the
ticket does not pin is `private` or carries the file stem `KLIndStepA`.  KL10b assembles case (ii)
and proves the pin `KLindStepPin` from the declarations below.

* §1 `KLf0`, `KLf1`, `KLf2` (for any `f : Zd d L → ℂ`; `f(s) = Θ_t(a, b + s)` in use), the identity
  `f = f₀ + f₁ + f₂` (`KLf_split`), `f₁(-s) = -f₁(s)`, `f₂(-s) = f₂(s)`.
* §2 `(eq:f12)` for **every** `s`: `KLf0_bound`, `KLf_crude_bound` (no loss), `KLf12_bound`
  (`|f₁| ≤ C L^τ (g²+|1-t|)⁻¹ (|s|+1)^{d-1}/(|a-b|+1)^{d-1}`, `|f₂| ≤ … (|s|+1)^d/(|a-b|+1)^d`).
  Near `|s| ≤ |a-b|/2`: `KLDiffOne`, `KLDiffTwo` at `c = 1/2`; far: the zero mode cancels and
  `KLZero` gives `L^τ (g²+|1-t|)⁻¹`.  Also `(1-t) Σ_b |Θ_t(a,b)| ≤ 1` and the long edge `= Θ_t`.
  T2365: the proofs of `KLf12_bound` are the private cores `KLIndStepA_f1_core`, `KLIndStepA_f2_core`
  for one matrix, also used by `KLIndStepA_f12_abs` (§5b).
* §3 the lattice sums on `Zd d L` (`KLlat_*`) and `(g²+|1-t|)⁻¹ ≤ B_{t,0}`.
* §4 `KLSigmaPi_reflect` (`Σ^{(∅)}(c - δ) = Σ^{(∅)}(δ)`), translation invariance, the exact
  vanishing of group (G1) `KLslice_f1_vanish` (the instance of `KLIndStepA_slice_vanish`), and the
  reindexing of a slice sum to another root.
* §5 alternating `σ`, the signed (`KLIndStepA_sumZero_signed`) and **weighted**
  (`KLsumZero_weighted`) sum-zero estimates on every slice `δ_r = x`, for `σ^{(alt)}` and its
  complement.
* §5b (T2365) the abstract data of the induction step: the bundles `IndStepTH`, `SigDecayAbs`,
  `SigSumZeroAbs`, their band instances (`indStepTH_band`, `sigDecayAbs_band`, `sigSumZeroAbs_band`)
  and `KLIndStepA_f12_abs`.
* §6 case (i): the abstract `KLIndStepA_leaf_abs`, `KLIndStepA_crude_abs`, `KLIndStepA_nonAlt_abs`
  and the band statements `KLindStep_nonAlt` (a short non-root leaf), `KLindStep_nonAlt_noloss`.
* §7 the compiled instances at `d = 3`, `L = 5`, `g = 1/2`, `E = 0`, `t = 9/10`.

Reuse.  The merged `KLMolecule.lean` proves the pointwise `g²` gain for a non-constant `δ` only
inside `KLsumZero_holds` (chain `KLMolecule_edge`, `KLMolecule_selfW_bound_nc`, …).
`KLsumZero_weighted` needs it as a pointwise bound, so this file uses those lemmas directly
(they were `private` until ticket T2127).
-/

set_option linter.style.longLine false

namespace RBM.Loop

open Finset

/-! ## 1. The splitting of a long leaf -/

section Split

variable {d L : ℕ}

/-- `f₀ = f(0)`: the value of a long leaf at the root. -/
noncomputable def KLf0 (f : Zd d L → ℂ) : ℂ := f 0

/-- `f₁(s) = ½ f(s) - ½ f(-s)`: the antisymmetric part. -/
noncomputable def KLf1 (f : Zd d L → ℂ) (s : Zd d L) : ℂ := (1 / 2 : ℂ) * f s - (1 / 2 : ℂ) * f (-s)

/-- `f₂(s) = ½ f(s) + ½ f(-s) - f(0)`: the symmetric part without the value at the root. -/
noncomputable def KLf2 (f : Zd d L → ℂ) (s : Zd d L) : ℂ :=
  (1 / 2 : ℂ) * f s + (1 / 2 : ℂ) * f (-s) - f 0

/-- `f = f₀ + f₁ + f₂`. -/
theorem KLf_split (f : Zd d L → ℂ) (s : Zd d L) : KLf0 f + KLf1 f s + KLf2 f s = f s := by
  unfold KLf0 KLf1 KLf2; ring

/-- `f₁(a,-s) = -f₁(a,s)`. -/
theorem KLf1_neg (f : Zd d L → ℂ) (s : Zd d L) : KLf1 f (-s) = -KLf1 f s := by
  unfold KLf1; rw [neg_neg]; ring

/-- `f₂(a,-s) = f₂(a,s)`. -/
theorem KLf2_neg (f : Zd d L → ℂ) (s : Zd d L) : KLf2 f (-s) = KLf2 f s := by
  unfold KLf2; rw [neg_neg]; ring

private theorem KLIndStepA_norm_f0_le {f : Zd d L → ℂ} {M : ℝ} (h : ∀ x, ‖f x‖ ≤ M) : ‖KLf0 f‖ ≤ M := h 0

private theorem KLIndStepA_norm_f1_le {f : Zd d L → ℂ} {M : ℝ} (h : ∀ x, ‖f x‖ ≤ M) (s : Zd d L) :
    ‖KLf1 f s‖ ≤ M := by
  unfold KLf1
  calc ‖(1 / 2 : ℂ) * f s - (1 / 2 : ℂ) * f (-s)‖
      ≤ ‖(1 / 2 : ℂ) * f s‖ + ‖(1 / 2 : ℂ) * f (-s)‖ := norm_sub_le _ _
    _ = ‖f s‖ / 2 + ‖f (-s)‖ / 2 := by simp; ring
    _ ≤ M := by linarith [h s, h (-s)]

private theorem KLIndStepA_norm_f2_le {f : Zd d L → ℂ} {M : ℝ} (h : ∀ x, ‖f x‖ ≤ M) (s : Zd d L) :
    ‖KLf2 f s‖ ≤ 2 * M := by
  unfold KLf2
  calc ‖(1 / 2 : ℂ) * f s + (1 / 2 : ℂ) * f (-s) - f 0‖
      ≤ ‖(1 / 2 : ℂ) * f s + (1 / 2 : ℂ) * f (-s)‖ + ‖f 0‖ := norm_sub_le _ _
    _ ≤ (‖(1 / 2 : ℂ) * f s‖ + ‖(1 / 2 : ℂ) * f (-s)‖) + ‖f 0‖ := by
        gcongr; exact norm_add_le _ _
    _ = ‖f s‖ / 2 + ‖f (-s)‖ / 2 + ‖f 0‖ := by simp; ring
    _ ≤ 2 * M := by linarith [h s, h (-s), h 0]

end Split


/-! ## 2. Facts on `Θ_t` and `B_{t,0}`; `(eq:f12)` -/

section ThetaFacts

variable {d L : ℕ} {g : ℝ}

/-- Translation invariance in the form `Θ_ξ(a,b) = Θ_ξ(0, b - a)` (property 2 of `lem_propTH`). -/
theorem KLIndStepA_Theta_apply_sub [NeZero L] (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a b : Zd d L) :
    Theta d L g ξ a b = Theta d L g ξ 0 (b - a) := by
  have h := Theta_apply_add_right_of_three_le (g := g) hL hξ 0 (b - a) a
  rw [zero_add, sub_add_cancel] at h
  exact h

/-- `(g² + |1-t|)⁻¹ ≤ B_{t,0}` (the zero-mode term of `B_{t,0}` is nonnegative). -/
theorem KLlat_inv_le_Bparam (t : ℝ) :
    (g ^ 2 + |1 - t|)⁻¹ ≤ Bparam d L g t 0 := by
  unfold Bparam
  have : ((L : ℝ) ^ d * |1 - t|)⁻¹ ≥ 0 := by positivity
  simp only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one]
  linarith

/-- `B_{t,K} ≤ B_{t,0}`. -/
theorem KLIndStepA_Bparam_le_zero (t : ℝ) (K : ℕ) : Bparam d L g t K ≤ Bparam d L g t 0 := by
  unfold Bparam
  have h1 : (((K : ℝ) + 1) ^ (d - 2))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]))
  have h2 : 0 ≤ (g ^ 2 + |1 - t|)⁻¹ := by positivity
  have h3 : (g ^ 2 + |1 - t|)⁻¹ * (((K : ℝ) + 1) ^ (d - 2))⁻¹ ≤ (g ^ 2 + |1 - t|)⁻¹ * 1 :=
    mul_le_mul_of_nonneg_left h1 h2
  simp only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one]
  linarith

/-- `B_{t,K} ≥ 0`. -/
theorem KLIndStepA_Bparam_nonneg (t : ℝ) (K : ℕ) : 0 ≤ Bparam d L g t K := by
  unfold Bparam; positivity

/-- The decay `|z| ≤ C B_{t,|a|} e^{-c|a|/ℓ_t}` of property 5 implies `|z| ≤ C B_{t,0}`. -/
theorem KLIndStepA_decay_le_zero {t Cd cd : ℝ} {z : ℂ} (hL : 1 ≤ L) (hCd : 0 ≤ Cd) (hcd : 0 ≤ cd)
    (a : Zd d L)
    (h : ‖z‖ ≤ Cd * Bparam d L g t (zdistD d L a)
      * Real.exp (-cd * (zdistD d L a : ℝ) / ellT L g t)) :
    ‖z‖ ≤ Cd * Bparam d L g t 0 := by
  have hell : 0 < ellT L g t := ellT_pos (by exact_mod_cast hL)
  have hexp : Real.exp (-cd * (zdistD d L a : ℝ) / ellT L g t) ≤ 1 := by
    apply Real.exp_le_one_iff.2
    have : 0 ≤ cd * (zdistD d L a : ℝ) / ellT L g t := by positivity
    have e : -cd * (zdistD d L a : ℝ) / ellT L g t = -(cd * (zdistD d L a : ℝ) / ellT L g t) := by
      ring
    rw [e]; linarith
  have hB := KLIndStepA_Bparam_le_zero (d := d) (L := L) (g := g) t (zdistD d L a)
  have hB0 := KLIndStepA_Bparam_nonneg (d := d) (L := L) (g := g) t (zdistD d L a)
  have hB00 : 0 ≤ Cd * Bparam d L g t 0 := mul_nonneg hCd (hB0.trans hB)
  calc ‖z‖ ≤ Cd * Bparam d L g t (zdistD d L a) * Real.exp (-cd * (zdistD d L a : ℝ) / ellT L g t) := h
    _ ≤ Cd * Bparam d L g t 0 * 1 := by gcongr
    _ = Cd * Bparam d L g t 0 := mul_one _

end ThetaFacts

section F12

variable {d : ℕ} {κ gmax : ℝ}

/-- The pointwise bound `|Θ_t(a,b)| ≤ C_d B_{t,0}` from property 5. -/
theorem KLIndStepA_Theta_norm_le (hPT : KLPT d κ gmax) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ gmax →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a b : Zd d L,
        ‖Theta d L g (t : ℂ) a b‖ ≤ Cd * Bparam d L g t 0 := by
  obtain ⟨Cd, hCd, cd, hcd, H⟩ := hPT.decay
  refine ⟨Cd, hCd, fun L _ hL g hg0 hg1 t ht0 ht1 a b => ?_⟩
  have hξ : ‖(t : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_of_nonneg ht0]
  rw [KLIndStepA_Theta_apply_sub hL hξ a b]
  exact KLIndStepA_decay_le_zero (by omega) hCd.le hcd.le (b - a)
    (H L hL g hg0 hg1 t ht0 ht1 (b - a))

private theorem KLIndStepA_far_le (m : ℕ) {x y : ℝ} (hy : 0 ≤ y)
    (hfar : ¬ x ≤ 1 / 2 * y) :
    1 ≤ 2 ^ m * ((x + 1) ^ m * ((y + 1) ^ m)⁻¹) := by
  have h1 : y + 1 ≤ 2 * (x + 1) := by linarith [not_le.1 hfar]
  have h2 : (y + 1) ^ m ≤ (2 * (x + 1)) ^ m := pow_le_pow_left₀ (by linarith) h1 m
  have h3 : 0 < (y + 1) ^ m := by positivity
  rw [mul_pow] at h2
  have h4 : 1 ≤ (2 ^ m * (x + 1) ^ m) * ((y + 1) ^ m)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ h3]; linarith
  calc (1 : ℝ) ≤ (2 ^ m * (x + 1) ^ m) * ((y + 1) ^ m)⁻¹ := h4
    _ = 2 ^ m * ((x + 1) ^ m * ((y + 1) ^ m)⁻¹) := by ring

end F12

section F12core

/-- The zero-mode bound `(|a|+1)^{-(d-2)} ≤ 1`: `‖f(z) - c₀‖ ≤ C_Z L^τ (g²+|1-t|)⁻¹` for every `z`. -/
private theorem KLIndStepA_zero_key {d L : ℕ} [NeZero L] (f : Zd d L → ℂ) {c0 : ℂ} {CZ Lt A : ℝ}
    (hZ0 : 0 ≤ CZ * Lt * A)
    (hZ : ∀ a : Zd d L, ‖f a - c0‖ ≤ CZ * Lt * A * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹)
    (z : Zd d L) : ‖f z - c0‖ ≤ CZ * Lt * A :=
  (hZ z).trans (mul_le_of_le_one_right hZ0 (inv_le_one_of_one_le₀ (one_le_pow₀
    (by linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ zdistD d L z)]))))

/-- `(eq:f12)`, the antisymmetric part, for every `s`, for one matrix `T`: translation invariance
`htr`, the near-range bound `hD` (property 6 at `c = 1/2`) and the zero-mode bound `hZ` (property 8,
`c₀` the mean).  `Lt`, `A` stand for `L^τ`, `(g²+|1-t|)⁻¹`.  The factor `(|s|+1)^{d-1}` replaces the
paper's restriction `|s| ≺ 1`.  Used by `KLf12_bound` (band) and `KLIndStepA_f12_abs`. -/
private theorem KLIndStepA_f1_core {d L : ℕ} [NeZero L] (hd : 2 ≤ d) (T : Matrix (Zd d L) (Zd d L) ℂ)
    {CD CZ C Lt A : ℝ} {c0 : ℂ} (hLt : 0 ≤ Lt) (hA : 0 ≤ A) (hCD0 : 0 ≤ CD) (hCZ0 : 0 ≤ CZ)
    (hCD : CD ≤ C) (hCZ : 2 ^ d * 2 * CZ ≤ C) (htr : ∀ a b, T a b = T 0 (b - a))
    (hD : ∀ a r : Zd d L, (zdistD d L r : ℝ) ≤ 1 / 2 * (zdistD d L a : ℝ) →
      ‖T 0 (a + r) - T 0 a‖ ≤ CD * Lt * A * (zdistD d L r : ℝ)
        * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹)
    (hZ : ∀ a : Zd d L, ‖T 0 a - c0‖ ≤ CZ * Lt * A * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹)
    (a b s : Zd d L) :
    ‖KLf1 (fun s => T a (b + s)) s‖
      ≤ C * Lt * A * (((zdistD d L s : ℝ) + 1) ^ (d - 1))
          * ((((zdistD d L (a - b) : ℝ) + 1) ^ (d - 1))⁻¹) := by
  have hC0 : 0 ≤ C := hCD0.trans hCD
  have hZ0 : 0 ≤ CZ * Lt * A := by positivity
  set y : Zd d L := b - a with hy
  have hya : zdistD d L (a - b) = zdistD d L y := by
    rw [hy, ← zdistD_neg d L (b - a), neg_sub]
  rw [hya]
  have hF : ∀ z : Zd d L, T a (b + z) = T 0 (y + z) := by
    intro z
    rw [htr a (b + z), hy]
    congr 1; abel
  have hid : KLf1 (fun s => T a (b + s)) s = (1 / 2 : ℂ) * T 0 (y + s) - (1 / 2 : ℂ) * T 0 (y + -s) := by
    simp only [KLf1]; rw [hF, hF]
  rw [hid]
  have hs0 : (0 : ℝ) ≤ (zdistD d L s : ℝ) := Nat.cast_nonneg _
  have hy0 : (0 : ℝ) ≤ (zdistD d L y : ℝ) := Nat.cast_nonneg _
  by_cases hnear : (zdistD d L s : ℝ) ≤ 1 / 2 * (zdistD d L y : ℝ)
  · -- near range: property 6
    have h1 := hD y s hnear
    have h2 := hD y (-s) (by rwa [zdistD_neg])
    rw [zdistD_neg] at h2
    have hid2 : (1 / 2 : ℂ) * T 0 (y + s) - (1 / 2 : ℂ) * T 0 (y + -s)
        = (1 / 2 : ℂ) * (T 0 (y + s) - T 0 y) - (1 / 2 : ℂ) * (T 0 (y + -s) - T 0 y) := by ring
    rw [hid2]
    set X := CD * Lt * A * (zdistD d L s : ℝ) * ((((zdistD d L y : ℝ) + 1) ^ (d - 1))⁻¹) with hX
    have hsle : (zdistD d L s : ℝ) ≤ ((zdistD d L s : ℝ) + 1) ^ (d - 1) :=
      (by linarith : (zdistD d L s : ℝ) ≤ (zdistD d L s : ℝ) + 1).trans
        (le_self_pow₀ (by linarith) (by omega))
    calc ‖(1 / 2 : ℂ) * (T 0 (y + s) - T 0 y) - (1 / 2 : ℂ) * (T 0 (y + -s) - T 0 y)‖
        ≤ ‖(1 / 2 : ℂ) * (T 0 (y + s) - T 0 y)‖ + ‖(1 / 2 : ℂ) * (T 0 (y + -s) - T 0 y)‖ :=
          norm_sub_le _ _
      _ = ‖T 0 (y + s) - T 0 y‖ / 2 + ‖T 0 (y + -s) - T 0 y‖ / 2 := by simp; ring
      _ ≤ X := by rw [hX]; linarith
      _ ≤ C * Lt * A * (((zdistD d L s : ℝ) + 1) ^ (d - 1))
            * ((((zdistD d L y : ℝ) + 1) ^ (d - 1))⁻¹) := by rw [hX]; gcongr
  · -- far range: the zero mode cancels, property 8
    have hid2 : (1 / 2 : ℂ) * T 0 (y + s) - (1 / 2 : ℂ) * T 0 (y + -s)
        = (1 / 2 : ℂ) * (T 0 (y + s) - c0) - (1 / 2 : ℂ) * (T 0 (y + -s) - c0) := by ring
    rw [hid2]
    have hfar := KLIndStepA_far_le (d - 1) hy0 hnear
    have hk1 := KLIndStepA_zero_key (T 0) hZ0 hZ (y + s)
    have hk2 := KLIndStepA_zero_key (T 0) hZ0 hZ (y + -s)
    have h2d : (2 : ℝ) ^ (d - 1) * CZ ≤ C :=
      le_trans (mul_le_mul_of_nonneg_right ((pow_le_pow_right₀ (by norm_num) (Nat.sub_le d 1)).trans
        (le_mul_of_one_le_right (by positivity) (by norm_num))) hCZ0) hCZ
    calc ‖(1 / 2 : ℂ) * (T 0 (y + s) - c0) - (1 / 2 : ℂ) * (T 0 (y + -s) - c0)‖
        ≤ ‖(1 / 2 : ℂ) * (T 0 (y + s) - c0)‖ + ‖(1 / 2 : ℂ) * (T 0 (y + -s) - c0)‖ :=
          norm_sub_le _ _
      _ = ‖T 0 (y + s) - c0‖ / 2 + ‖T 0 (y + -s) - c0‖ / 2 := by simp; ring
      _ ≤ CZ * Lt * A := by linarith
      _ = (CZ * Lt * A) * 1 := (mul_one _).symm
      _ ≤ (CZ * Lt * A) * (2 ^ (d - 1) * ((((zdistD d L s : ℝ) + 1) ^ (d - 1))
              * ((((zdistD d L y : ℝ) + 1) ^ (d - 1))⁻¹))) := by gcongr
      _ = (2 ^ (d - 1) * CZ) * Lt * A * (((zdistD d L s : ℝ) + 1) ^ (d - 1))
              * ((((zdistD d L y : ℝ) + 1) ^ (d - 1))⁻¹) := by ring
      _ ≤ C * Lt * A * (((zdistD d L s : ℝ) + 1) ^ (d - 1))
              * ((((zdistD d L y : ℝ) + 1) ^ (d - 1))⁻¹) := by gcongr

/-- `(eq:f12)`, the symmetric part, for every `s`, for one matrix `T` (as `KLIndStepA_f1_core`; the
factor `(|s|+1)^d`; property 7 at `c = 1/2`). -/
private theorem KLIndStepA_f2_core {d L : ℕ} [NeZero L] (hd : 2 ≤ d) (T : Matrix (Zd d L) (Zd d L) ℂ)
    {CD CZ C Lt A : ℝ} {c0 : ℂ} (hLt : 0 ≤ Lt) (hA : 0 ≤ A) (hCD0 : 0 ≤ CD) (hCZ0 : 0 ≤ CZ)
    (hCD : CD ≤ C) (hCZ : 2 ^ d * 2 * CZ ≤ C) (htr : ∀ a b, T a b = T 0 (b - a))
    (hD : ∀ a r : Zd d L, (zdistD d L r : ℝ) ≤ 1 / 2 * (zdistD d L a : ℝ) →
      ‖T 0 (a + r) + T 0 (a - r) - 2 * T 0 a‖ ≤ CD * Lt * A * (zdistD d L r : ℝ) ^ 2
        * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹)
    (hZ : ∀ a : Zd d L, ‖T 0 a - c0‖ ≤ CZ * Lt * A * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹)
    (a b s : Zd d L) :
    ‖KLf2 (fun s => T a (b + s)) s‖
      ≤ C * Lt * A * (((zdistD d L s : ℝ) + 1) ^ d) * ((((zdistD d L (a - b) : ℝ) + 1) ^ d)⁻¹) := by
  have hC0 : 0 ≤ C := hCD0.trans hCD
  have hZ0 : 0 ≤ CZ * Lt * A := by positivity
  set y : Zd d L := b - a with hy
  have hya : zdistD d L (a - b) = zdistD d L y := by
    rw [hy, ← zdistD_neg d L (b - a), neg_sub]
  rw [hya]
  have hF : ∀ z : Zd d L, T a (b + z) = T 0 (y + z) := by
    intro z
    rw [htr a (b + z), hy]
    congr 1; abel
  have hid : KLf2 (fun s => T a (b + s)) s
      = (1 / 2 : ℂ) * T 0 (y + s) + (1 / 2 : ℂ) * T 0 (y + -s) - T 0 y := by
    simp only [KLf2]; rw [hF, hF, hF]; simp
  rw [hid]
  have hs0 : (0 : ℝ) ≤ (zdistD d L s : ℝ) := Nat.cast_nonneg _
  have hy0 : (0 : ℝ) ≤ (zdistD d L y : ℝ) := Nat.cast_nonneg _
  by_cases hnear : (zdistD d L s : ℝ) ≤ 1 / 2 * (zdistD d L y : ℝ)
  · -- near range: property 7
    have h1 := hD y s hnear
    have hid2 : (1 / 2 : ℂ) * T 0 (y + s) + (1 / 2 : ℂ) * T 0 (y + -s) - T 0 y
        = (1 / 2 : ℂ) * (T 0 (y + s) + T 0 (y - s) - 2 * T 0 y) := by
      rw [sub_eq_add_neg y s]; ring
    rw [hid2]
    have hsle : (zdistD d L s : ℝ) ^ 2 ≤ ((zdistD d L s : ℝ) + 1) ^ d :=
      (pow_le_pow_left₀ hs0 (by linarith) 2).trans (pow_le_pow_right₀ (by linarith) hd)
    set X := CD * Lt * A * (zdistD d L s : ℝ) ^ 2 * ((((zdistD d L y : ℝ) + 1) ^ d)⁻¹) with hX
    have hX0 : 0 ≤ X := by rw [hX]; positivity
    calc ‖(1 / 2 : ℂ) * (T 0 (y + s) + T 0 (y - s) - 2 * T 0 y)‖
        = ‖T 0 (y + s) + T 0 (y - s) - 2 * T 0 y‖ / 2 := by simp; ring
      _ ≤ X := by rw [hX]; linarith
      _ ≤ C * Lt * A * (((zdistD d L s : ℝ) + 1) ^ d) * ((((zdistD d L y : ℝ) + 1) ^ d)⁻¹) := by
          rw [hX]; gcongr
  · -- far range: the zero mode cancels, property 8
    have hid2 : (1 / 2 : ℂ) * T 0 (y + s) + (1 / 2 : ℂ) * T 0 (y + -s) - T 0 y
        = (1 / 2 : ℂ) * (T 0 (y + s) - c0) + (1 / 2 : ℂ) * (T 0 (y + -s) - c0)
          - (T 0 y - c0) := by ring
    rw [hid2]
    have hfar := KLIndStepA_far_le d hy0 hnear
    have hk1 := KLIndStepA_zero_key (T 0) hZ0 hZ (y + s)
    have hk2 := KLIndStepA_zero_key (T 0) hZ0 hZ (y + -s)
    have hk3 := KLIndStepA_zero_key (T 0) hZ0 hZ y
    calc ‖(1 / 2 : ℂ) * (T 0 (y + s) - c0) + (1 / 2 : ℂ) * (T 0 (y + -s) - c0) - (T 0 y - c0)‖
        ≤ ‖(1 / 2 : ℂ) * (T 0 (y + s) - c0) + (1 / 2 : ℂ) * (T 0 (y + -s) - c0)‖
          + ‖T 0 y - c0‖ := norm_sub_le _ _
      _ ≤ (‖(1 / 2 : ℂ) * (T 0 (y + s) - c0)‖ + ‖(1 / 2 : ℂ) * (T 0 (y + -s) - c0)‖)
          + ‖T 0 y - c0‖ := by gcongr; exact norm_add_le _ _
      _ = ‖T 0 (y + s) - c0‖ / 2 + ‖T 0 (y + -s) - c0‖ / 2 + ‖T 0 y - c0‖ := by simp; ring
      _ ≤ 2 * (CZ * Lt * A) := by linarith
      _ = (2 * (CZ * Lt * A)) * 1 := (mul_one _).symm
      _ ≤ (2 * (CZ * Lt * A)) * (2 ^ d * ((((zdistD d L s : ℝ) + 1) ^ d)
            * ((((zdistD d L y : ℝ) + 1) ^ d)⁻¹))) := by gcongr
      _ = (2 ^ d * 2 * CZ) * Lt * A * (((zdistD d L s : ℝ) + 1) ^ d)
            * ((((zdistD d L y : ℝ) + 1) ^ d)⁻¹) := by ring
      _ ≤ C * Lt * A * (((zdistD d L s : ℝ) + 1) ^ d) * ((((zdistD d L y : ℝ) + 1) ^ d)⁻¹) := by
          gcongr

end F12core


section Public

variable {d : ℕ} {κ gmax : ℝ}

/-- **`(eq:f12)`, first part**: `|f₀(a,s)| = |Θ_t(a,b)| ≤ C_d B_{t,0}` (property 5, `B_{t,|a-b|} ≤ B_{t,0}`);
`C` depends on `d, gmax` only. -/
theorem KLf0_bound (hPT : KLPT d κ gmax) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (a b : Zd d p.L),
      ‖KLf0 (fun s => Theta d p.L p.g (p.t : ℂ) a (b + s))‖ ≤ C * Bparam d p.L p.g p.t 0 := by
  obtain ⟨C, hC, H⟩ := KLIndStepA_Theta_norm_le hPT
  refine ⟨C, hC, fun p a b => ?_⟩
  have := H p.L p.hL p.g p.hg0 p.hg1 p.t p.ht0 p.ht1 a (b + 0)
  simpa [KLf0] using this

/-- The crude pointwise bound for the three parts, `C = 2 C_d`: no loss, no `s`-dependence.  It is
the bound used for every factor of case (ii) that is not the distinguished one. -/
theorem KLf_crude_bound (hPT : KLPT d κ gmax) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (a b s : Zd d p.L),
      ‖KLf0 (fun s => Theta d p.L p.g (p.t : ℂ) a (b + s))‖ ≤ C * Bparam d p.L p.g p.t 0 ∧
      ‖KLf1 (fun s => Theta d p.L p.g (p.t : ℂ) a (b + s)) s‖ ≤ C * Bparam d p.L p.g p.t 0 ∧
      ‖KLf2 (fun s => Theta d p.L p.g (p.t : ℂ) a (b + s)) s‖ ≤ C * Bparam d p.L p.g p.t 0 := by
  obtain ⟨C, hC, H⟩ := KLIndStepA_Theta_norm_le hPT
  refine ⟨2 * C, by positivity, fun p a b s => ?_⟩
  have h : ∀ x : Zd d p.L, ‖Theta d p.L p.g (p.t : ℂ) a (b + x)‖ ≤ C * Bparam d p.L p.g p.t 0 :=
    fun x => H p.L p.hL p.g p.hg0 p.hg1 p.t p.ht0 p.ht1 a (b + x)
  have hB : 0 ≤ Bparam d p.L p.g p.t 0 := KLIndStepA_Bparam_nonneg _ _
  refine ⟨?_, ?_, ?_⟩
  · have := KLIndStepA_norm_f0_le h
    nlinarith [mul_nonneg hC.le hB]
  · have := KLIndStepA_norm_f1_le h s
    nlinarith [mul_nonneg hC.le hB]
  · have := KLIndStepA_norm_f2_le h s
    linarith

/-- **`(eq:f12)`, second and third parts, for every `s`** (the paper states them for `|s| ≺ 1`):
`|f₁| ≤ C L^τ (g²+|1-t|)⁻¹ (|s|+1)^{d-1} / (|a-b|+1)^{d-1}` and
`|f₂| ≤ C L^τ (g²+|1-t|)⁻¹ (|s|+1)^{d} / (|a-b|+1)^{d}`; `C = C(d, gmax, τ)`.  Range `|s| ≤ |a-b|/2`:
`KLDiffOne`, `KLDiffTwo` at `c = 1/2`; range `|s| > |a-b|/2`: `KLZero` (the zero mode cancels in `f₁`,
`f₂`) and `1 ≤ (2(|s|+1)/(|a-b|+1))^{d}`. -/
theorem KLf12_bound (hd : 3 ≤ d) (hPT : KLPT d κ gmax) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (a b s : Zd d p.L),
      ‖KLf1 (fun s => Theta d p.L p.g (p.t : ℂ) a (b + s)) s‖
        ≤ C * (p.L : ℝ) ^ τ * (p.g ^ 2 + |1 - p.t|)⁻¹ * (((zdistD d p.L s : ℝ) + 1) ^ (d - 1))
            * ((((zdistD d p.L (a - b) : ℝ) + 1) ^ (d - 1))⁻¹) ∧
      ‖KLf2 (fun s => Theta d p.L p.g (p.t : ℂ) a (b + s)) s‖
        ≤ C * (p.L : ℝ) ^ τ * (p.g ^ 2 + |1 - p.t|)⁻¹ * (((zdistD d p.L s : ℝ) + 1) ^ d)
            * ((((zdistD d p.L (a - b) : ℝ) + 1) ^ d)⁻¹) := by
  obtain ⟨CD1, hCD1, H1⟩ := hPT.diffOne (1 / 2) (by norm_num) (by norm_num) τ hτ
  obtain ⟨CD2, hCD2, H2⟩ := hPT.diffTwo (1 / 2) (by norm_num) (by norm_num) τ hτ
  obtain ⟨CZ, hCZ, HZ⟩ := hPT.zeroMode τ hτ
  refine ⟨max (max CD1 CD2) (2 ^ d * 2 * CZ), lt_max_of_lt_left (lt_max_of_lt_left hCD1),
    fun p a b s => ?_⟩
  have hξ : ‖(p.t : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg p.ht0]; exact p.ht1
  have htr : ∀ a b : Zd d p.L, Theta d p.L p.g (p.t : ℂ) a b = Theta d p.L p.g (p.t : ℂ) 0 (b - a) :=
    fun a b => KLIndStepA_Theta_apply_sub p.hL hξ a b
  have hLt : 0 ≤ (p.L : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) τ
  have hA : 0 ≤ (p.g ^ 2 + |1 - p.t|)⁻¹ := by positivity
  have hZ : ∀ a : Zd d p.L,
      ‖Theta d p.L p.g (p.t : ℂ) 0 a - ((p.L : ℂ) ^ (2 * d))⁻¹
          * ∑ a' : Zd d p.L, ∑ b' : Zd d p.L, Theta d p.L p.g (p.t : ℂ) a' b'‖
        ≤ CZ * (p.L : ℝ) ^ τ * (p.g ^ 2 + |1 - p.t|)⁻¹ * (((zdistD d p.L a : ℝ) + 1) ^ (d - 2))⁻¹ :=
    fun a => HZ p.L p.hL p.g p.hg0 p.hg1 p.t p.ht0 p.ht1 a
  have hCZ' : 2 ^ d * 2 * CZ ≤ max (max CD1 CD2) (2 ^ d * 2 * CZ) := le_max_right _ _
  exact ⟨KLIndStepA_f1_core (by omega) _ hLt hA hCD1.le hCZ.le
      ((le_max_left _ _).trans (le_max_left _ _)) hCZ' htr
      (fun a r h => H1 p.L p.hL p.g p.hg0 p.hg1 p.t p.ht0 p.ht1 a r h) hZ a b s,
    KLIndStepA_f2_core (by omega) _ hLt hA hCD2.le hCZ.le
      ((le_max_right _ _).trans (le_max_left _ _)) hCZ' htr
      (fun a r h => H2 p.L p.hL p.g p.hg0 p.hg1 p.t p.ht0 p.ht1 a r h) hZ a b s⟩

end Public

section RowSum

variable {d L : ℕ} [NeZero L] {g : ℝ}

/-- `(1-t) Σ_b |Θ_t(a,b)| ≤ 1` (`(eq:THETAinftinf)`): the merged `sum_norm_Theta_row_le` at `m = 1`. -/
theorem KLlat_sum_norm_Theta_row_le (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Zd d L) :
    ∑ b, ‖Theta d L g (t : ℂ) a b‖ ≤ (1 - t)⁻¹ := by
  have h := sum_norm_Theta_row_le (g := g) hL ht0 ht1 (m := 1) (by simp) a
  simpa using h

/-- A long edge is the propagator `Θ_t^{(+,-)}`: `m(σ) m(σ') = 1` for `σ ≠ σ'`. -/
theorem KLIndStepA_thetaEdge_long {E : ℝ} (hE : |E| ≤ 2) (t : ℝ) {s s' : Bool} (h : s ≠ s') :
    thetaEdge d L g (mSigma E) t s s' = Theta d L g (t : ℂ) := by
  have hs : s' = !s := by cases s <;> cases s' <;> simp_all
  subst hs
  unfold thetaEdge
  rw [KLmSigma_mul_not hE, mul_one]

end RowSum

/-! ## 3. Lattice sums -/

section Lattice

variable {L : ℕ} [NeZero L]

/-- `Σ_b (|a-b|+1)^{-(d-2)} ≤ C L²` (`d = k+2`): the merged radial sum. -/
theorem KLlat_pow_sub_two (k : ℕ) (a : Zd (k + 2) L) :
    ∑ b : Zd (k + 2) L, ((((zdistD (k + 2) L (a - b) : ℕ) : ℝ) + 1) ^ k)⁻¹
      ≤ Real.exp (√((k : ℝ) + 2)) * (2 ^ (k + 2) * radC 1 * (L : ℝ) ^ 2) :=
  (sum_shift (k + 2) a (fun r : ℕ => (((r : ℝ) + 1) ^ k)⁻¹)).trans_le
    (sum_radial_pow_le k (by exact_mod_cast NeZero.pos L))

/-- `Σ_b (|a-b|+1)^{-(d-1)} ≤ 2^d (d+1) L` (`d = k+2`): `|S_r| ≤ 2^d (r+1)^{d-1}` for the sphere
`S_r`, so every term of the radial sum is `≤ 2^d`. -/
theorem KLlat_pow_sub_one (k : ℕ) (a : Zd (k + 2) L) :
    ∑ b : Zd (k + 2) L, ((((zdistD (k + 2) L (a - b) : ℕ) : ℝ) + 1) ^ (k + 1))⁻¹
      ≤ 2 ^ (k + 2) * (((k : ℝ) + 3) * L) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.pos L
  refine (sum_shift (k + 2) a (fun r : ℕ => (((r : ℝ) + 1) ^ (k + 1))⁻¹)).trans_le ?_
  rw [sum_radial (k + 2) (fun r : ℕ => (((r : ℝ) + 1) ^ (k + 1))⁻¹)]
  have hterm : ∀ r ∈ range ((k + 2) * L + 1),
      (sphereCard (k + 2) L r : ℝ) * (((r : ℝ) + 1) ^ (k + 1))⁻¹ ≤ 2 ^ (k + 2) := by
    intro r _
    have hc : (sphereCard (k + 2) L r : ℝ) ≤ 2 ^ (k + 2) * ((r : ℝ) + 1) ^ (k + 1) := by
      exact_mod_cast card_sphere_le (L := L) (k + 1) r
    calc (sphereCard (k + 2) L r : ℝ) * (((r : ℝ) + 1) ^ (k + 1))⁻¹
        ≤ (2 ^ (k + 2) * ((r : ℝ) + 1) ^ (k + 1)) * (((r : ℝ) + 1) ^ (k + 1))⁻¹ :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = 2 ^ (k + 2) := by field_simp
  calc ∑ r ∈ range ((k + 2) * L + 1), (sphereCard (k + 2) L r : ℝ) * (((r : ℝ) + 1) ^ (k + 1))⁻¹
      ≤ ∑ _r ∈ range ((k + 2) * L + 1), (2 : ℝ) ^ (k + 2) := sum_le_sum hterm
    _ = 2 ^ (k + 2) * (((k : ℝ) + 2) * L + 1) := by
        rw [sum_const, card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ 2 ^ (k + 2) * (((k : ℝ) + 3) * L) := by
        gcongr
        nlinarith

/-- `Σ_b (|a-b|+1)^{-d} ≤ 2^d (1 + log(dL+1))`: the borderline sum. -/
theorem KLlat_pow_dim (k : ℕ) (a : Zd (k + 2) L) :
    ∑ b : Zd (k + 2) L, ((((zdistD (k + 2) L (a - b) : ℕ) : ℝ) + 1) ^ (k + 2))⁻¹
      ≤ 2 ^ (k + 2) * (1 + Real.log (((k : ℝ) + 2) * L + 1)) := by
  have h := sum_ball_inv_pow_dim_le (L := L) k (ρ := ((k : ℝ) + 2) * L) (by positivity)
    (Finset.univ : Finset (Zd (k + 2) L)) a (fun b _ => by
      have : ((zdistD (k + 2) L (a - b) : ℕ) : ℝ) ≤ (((k + 2) * L : ℕ) : ℝ) := by
        exact_mod_cast zdistD_le (k + 2) (a - b)
      push_cast at this
      exact this)
  exact h

/-- `1 + log(dL+1) ≤ (1 + (d+1)^τ/τ) L^τ`. -/
theorem KLlat_log_le (d : ℕ) (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) :
    1 + Real.log ((d : ℝ) * L + 1) ≤ (1 + ((d : ℝ) + 1) ^ τ / τ) * (L : ℝ) ^ τ := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.pos L
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : ((d : ℝ) * L + 1) ≤ ((d : ℝ) + 1) * L := by nlinarith
  have h2 : Real.log ((d : ℝ) * L + 1) ≤ Real.log (((d : ℝ) + 1) * L) :=
    Real.log_le_log (by positivity) h1
  have h3 : Real.log (((d : ℝ) + 1) * L) ≤ (((d : ℝ) + 1) * L) ^ τ / τ :=
    Real.log_le_rpow_div (by positivity) hτ
  rw [Real.mul_rpow (by positivity) (by positivity)] at h3
  have h4 : (1 : ℝ) ≤ (L : ℝ) ^ τ := Real.one_le_rpow hL1 hτ.le
  have h5 : ((d : ℝ) + 1) ^ τ * (L : ℝ) ^ τ / τ = ((d : ℝ) + 1) ^ τ / τ * (L : ℝ) ^ τ := by ring
  rw [h5] at h3
  nlinarith

/-- `Σ_b (|a-b|+1)^{-d} ≤ C L^τ`. -/
theorem KLlat_pow_dim_rpow (k : ℕ) {τ : ℝ} (hτ : 0 < τ) (a : Zd (k + 2) L) :
    ∑ b : Zd (k + 2) L, ((((zdistD (k + 2) L (a - b) : ℕ) : ℝ) + 1) ^ (k + 2))⁻¹
      ≤ 2 ^ (k + 2) * (1 + (((k : ℝ) + 2) + 1) ^ τ / τ) * (L : ℝ) ^ τ := by
  refine (KLlat_pow_dim k a).trans ?_
  have h := KLlat_log_le (L := L) (k + 2) (by omega) hτ
  push_cast at h
  calc 2 ^ (k + 2) * (1 + Real.log (((k : ℝ) + 2) * L + 1))
      ≤ 2 ^ (k + 2) * ((1 + (((k : ℝ) + 2) + 1) ^ τ / τ) * (L : ℝ) ^ τ) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

private theorem KLIndStepA_pow_le (m : ℕ) {x : ℝ} (hx : 0 ≤ x) : (x + 1) ^ m ≤ 2 ^ m * (x ^ m + 1) := by
  have h1 : x + 1 ≤ 2 * max x 1 := by
    rcases le_total x 1 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have h2 : (max x 1) ^ m ≤ x ^ m + 1 := by
    rcases le_total x 1 with h | h
    · rw [max_eq_right h, one_pow]; have := pow_nonneg hx m; linarith
    · rw [max_eq_left h]; linarith
  calc (x + 1) ^ m ≤ (2 * max x 1) ^ m := pow_le_pow_left₀ (by linarith) h1 m
    _ = 2 ^ m * (max x 1) ^ m := mul_pow _ _ _
    _ ≤ 2 ^ m * (x ^ m + 1) := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- The pair sum of case (ii).4 of `(eq:ind-step-bound)`, `d = k+2`:
`Σ_b ((|a₁-b|+1)^{d-1} (|a₂-b|+1)^{d-1})⁻¹ ≤ 2^{2d+2} (1 + log(dL+1))`.  The merged
`inv_pow_pair_le` (`d-1,d-1 → d,d-2`) bounds each term by `2^{d+1}` times the sum of the two
borderline terms `((|a_j-b|+1)^d)⁻¹`; `KLlat_pow_dim` sums each.  (The sharp `O(1)` bound is not
needed: the `log L` is absorbed by the loss `L^τ`.) -/
theorem KLlat_pair (k : ℕ) (a₁ a₂ : Zd (k + 2) L) :
    ∑ b : Zd (k + 2) L, ((((zdistD (k + 2) L (a₁ - b) : ℕ) : ℝ) + 1) ^ (k + 1)
        * (((zdistD (k + 2) L (a₂ - b) : ℕ) : ℝ) + 1) ^ (k + 1))⁻¹
      ≤ 2 ^ (2 * k + 6) * (1 + Real.log (((k : ℝ) + 2) * L + 1)) := by
  set x : Zd (k + 2) L → ℝ := fun b => ((zdistD (k + 2) L (a₁ - b) : ℕ) : ℝ) with hx
  set y : Zd (k + 2) L → ℝ := fun b => ((zdistD (k + 2) L (a₂ - b) : ℕ) : ℝ) with hy
  have hx0 : ∀ b, 0 ≤ x b := fun b => Nat.cast_nonneg _
  have hy0 : ∀ b, 0 ≤ y b := fun b => Nat.cast_nonneg _
  have hterm : ∀ b : Zd (k + 2) L,
      (((x b) + 1) ^ (k + 1) * ((y b) + 1) ^ (k + 1))⁻¹
        ≤ 2 ^ (k + 2) * 2 * (((x b + 1) ^ (k + 2))⁻¹ + ((y b + 1) ^ (k + 2))⁻¹) := by
    intro b
    have h1 : ((x b ^ (k + 1) + 1) * (y b ^ (k + 1) + 1)) ≤ ((x b + 1) ^ (k + 1) * (y b + 1) ^ (k + 1)) := by
      have hxa : x b ^ (k + 1) + 1 ≤ (x b + 1) ^ (k + 1) := by
        simpa using pow_add_pow_le (hx0 b) (zero_le_one' ℝ) (Nat.succ_ne_zero k)
      have hya : y b ^ (k + 1) + 1 ≤ (y b + 1) ^ (k + 1) := by
        simpa using pow_add_pow_le (hy0 b) (zero_le_one' ℝ) (Nat.succ_ne_zero k)
      exact mul_le_mul hxa hya (by positivity) (by positivity)
    have h2 := inv_pow_pair_le k (hx0 b) (hy0 b)
    have h3 : ((x b ^ (k + 2) + 1) * (y b ^ k + 1))⁻¹ ≤ 2 ^ (k + 2) * ((x b + 1) ^ (k + 2))⁻¹ := by
      have hyk : 1 ≤ y b ^ k + 1 := by have := pow_nonneg (hy0 b) k; linarith
      have hxk := KLIndStepA_pow_le (k + 2) (hx0 b)
      calc ((x b ^ (k + 2) + 1) * (y b ^ k + 1))⁻¹ ≤ (x b ^ (k + 2) + 1)⁻¹ := by
            apply inv_anti₀ (by positivity)
            nlinarith [pow_nonneg (hx0 b) (k + 2)]
        _ ≤ 2 ^ (k + 2) * ((x b + 1) ^ (k + 2))⁻¹ := by
            rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [pow_nonneg (hx0 b) (k + 2)]
    have h4 : ((x b ^ k + 1) * (y b ^ (k + 2) + 1))⁻¹ ≤ 2 ^ (k + 2) * ((y b + 1) ^ (k + 2))⁻¹ := by
      have hxk : 1 ≤ x b ^ k + 1 := by have := pow_nonneg (hx0 b) k; linarith
      have hyk := KLIndStepA_pow_le (k + 2) (hy0 b)
      calc ((x b ^ k + 1) * (y b ^ (k + 2) + 1))⁻¹ ≤ (y b ^ (k + 2) + 1)⁻¹ := by
            apply inv_anti₀ (by positivity)
            nlinarith [pow_nonneg (hy0 b) (k + 2)]
        _ ≤ 2 ^ (k + 2) * ((y b + 1) ^ (k + 2))⁻¹ := by
            rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [pow_nonneg (hy0 b) (k + 2)]
    calc (((x b) + 1) ^ (k + 1) * ((y b) + 1) ^ (k + 1))⁻¹
        ≤ ((x b ^ (k + 1) + 1) * (y b ^ (k + 1) + 1))⁻¹ := inv_anti₀ (by positivity) h1
      _ ≤ 2 * (((x b ^ (k + 2) + 1) * (y b ^ k + 1))⁻¹ + ((x b ^ k + 1) * (y b ^ (k + 2) + 1))⁻¹) := h2
      _ ≤ 2 * (2 ^ (k + 2) * ((x b + 1) ^ (k + 2))⁻¹ + 2 ^ (k + 2) * ((y b + 1) ^ (k + 2))⁻¹) := by
          gcongr
      _ = 2 ^ (k + 2) * 2 * (((x b + 1) ^ (k + 2))⁻¹ + ((y b + 1) ^ (k + 2))⁻¹) := by ring
  calc ∑ b : Zd (k + 2) L, ((((zdistD (k + 2) L (a₁ - b) : ℕ) : ℝ) + 1) ^ (k + 1)
        * (((zdistD (k + 2) L (a₂ - b) : ℕ) : ℝ) + 1) ^ (k + 1))⁻¹
      ≤ ∑ b : Zd (k + 2) L, 2 ^ (k + 2) * 2
          * (((x b + 1) ^ (k + 2))⁻¹ + ((y b + 1) ^ (k + 2))⁻¹) :=
        sum_le_sum fun b _ => hterm b
    _ = 2 ^ (k + 2) * 2 * (∑ b : Zd (k + 2) L, ((x b + 1) ^ (k + 2))⁻¹
          + ∑ b : Zd (k + 2) L, ((y b + 1) ^ (k + 2))⁻¹) := by
        rw [← sum_add_distrib, mul_sum]
    _ ≤ 2 ^ (k + 2) * 2 * (2 ^ (k + 2) * (1 + Real.log (((k : ℝ) + 2) * L + 1))
          + 2 ^ (k + 2) * (1 + Real.log (((k : ℝ) + 2) * L + 1))) := by
        gcongr
        · exact KLlat_pow_dim k a₁
        · exact KLlat_pow_dim k a₂
    _ = 2 ^ (2 * k + 6) * (1 + Real.log (((k : ℝ) + 2) * L + 1)) := by ring

/-- The pair sum in the form `C L^τ`, `C = 2^{2d+2} (1 + (d+1)^τ/τ)` (`d = k+2`). -/
theorem KLlat_pair_rpow (k : ℕ) {τ : ℝ} (hτ : 0 < τ) (a₁ a₂ : Zd (k + 2) L) :
    ∑ b : Zd (k + 2) L, ((((zdistD (k + 2) L (a₁ - b) : ℕ) : ℝ) + 1) ^ (k + 1)
        * (((zdistD (k + 2) L (a₂ - b) : ℕ) : ℝ) + 1) ^ (k + 1))⁻¹
      ≤ 2 ^ (2 * k + 6) * (1 + (((k : ℝ) + 2) + 1) ^ τ / τ) * (L : ℝ) ^ τ := by
  refine (KLlat_pair k a₁ a₂).trans ?_
  have h := KLlat_log_le (L := L) (k + 2) (by omega) hτ
  push_cast at h
  calc 2 ^ (2 * k + 6) * (1 + Real.log (((k : ℝ) + 2) * L + 1))
      ≤ 2 ^ (2 * k + 6) * ((1 + (((k : ℝ) + 2) + 1) ^ τ / τ) * (L : ℝ) ^ τ) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

/-- `1 + log(dL+1) ≤ (1 + log(d+1)) (1 + log L)`: the borderline sums in the form `C (1 + log L)`. -/
theorem KLlat_log_le_logL (d : ℕ) :
    1 + Real.log ((d : ℝ) * L + 1) ≤ (1 + Real.log ((d : ℝ) + 1)) * (1 + Real.log L) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.pos L
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1 : ((d : ℝ) * L + 1) ≤ ((d : ℝ) + 1) * L := by nlinarith
  have h2 : Real.log ((d : ℝ) * L + 1) ≤ Real.log (((d : ℝ) + 1) * L) :=
    Real.log_le_log (by positivity) h1
  rw [Real.log_mul (by positivity) (by positivity)] at h2
  have hA : 0 ≤ Real.log ((d : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hB : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg hL1
  nlinarith [mul_nonneg hA hB]

/-- `Σ_b (|a-b|+1)^{-d} ≤ 2^d (1 + log(d+1)) (1 + log L)` (`d = k+2`): the form `C (1 + log L)`. -/
theorem KLlat_pow_dim_logL (k : ℕ) (a : Zd (k + 2) L) :
    ∑ b : Zd (k + 2) L, ((((zdistD (k + 2) L (a - b) : ℕ) : ℝ) + 1) ^ (k + 2))⁻¹
      ≤ 2 ^ (k + 2) * ((1 + Real.log (((k : ℝ) + 2) + 1)) * (1 + Real.log L)) := by
  refine (KLlat_pow_dim k a).trans ?_
  have h := KLlat_log_le_logL (L := L) (k + 2)
  push_cast at h
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- The pair sum in the form `C (1 + log L)`, `C = 2^{2d+2} (1 + log(d+1))`. -/
theorem KLlat_pair_logL (k : ℕ) (a₁ a₂ : Zd (k + 2) L) :
    ∑ b : Zd (k + 2) L, ((((zdistD (k + 2) L (a₁ - b) : ℕ) : ℝ) + 1) ^ (k + 1)
        * (((zdistD (k + 2) L (a₂ - b) : ℕ) : ℝ) + 1) ^ (k + 1))⁻¹
      ≤ 2 ^ (2 * k + 6) * ((1 + Real.log (((k : ℝ) + 2) + 1)) * (1 + Real.log L)) := by
  refine (KLlat_pair k a₁ a₂).trans ?_
  have h := KLlat_log_le_logL (L := L) (k + 2)
  push_cast at h
  exact mul_le_mul_of_nonneg_left h (by positivity)

end Lattice


/-! ## 4. Symmetry, translation and slices of `Σ^{(∅)}` -/

section Reflect

variable {d : ℕ} {κ gmax : ℝ}

/-- **`KLSigmaPi_reflect`** (target 4): `Σ^{(∅)}(t, σ, c - δ) = Σ^{(∅)}(t, σ, δ)` for every `σ` and
every `c` (the symmetry `g(s) = g(-s)` is `c = 2 d₁`).  Same proof as the merged
`KLSigmaPi_empty_symm` (`KLselfW_reflect`, `KLTheta_reflect`), with a general reflection centre `c`
instead of `d₁ + s ↔ d₁ - s` and without the unused hypothesis `s 0 = 0`: the form the
`δ`-involution of `KLslice_f1_vanish` needs. -/
theorem KLSigmaPi_reflect (hκ : 0 < κ) (p : KLPar κ gmax) {n : ℕ} [NeZero n] (σ : Fin n → Bool)
    (c : Zd d p.L) (δ : Fin n → Zd d p.L) :
    KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ (fun i => c - δ i)
      = KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ := by
  have hE2 : |p.E| ≤ 2 := by linarith [p.hE]
  unfold KLSigmaPi
  congr 1
  refine Finset.sum_congr rfl fun F _ => ?_
  refine KLselfW_reflect d p.L F _ c (fun e x y => ?_) δ
  have hξ : ‖(p.t : ℂ) * (mSigma p.E (σ e.1.1) * mSigma p.E (σ e.1.2))‖ < 1 :=
    norm_mul_mSigma_lt_one hE2 p.ht0 p.ht1 _ _
  simp only [Matrix.sub_apply, Matrix.one_apply, sub_right_inj, thetaEdge,
    KLTheta_reflect d p.L p.g p.hL hξ]

/-- Translation invariance of `Σ^{(π)}` (merged `SumZero_SigmaPi_add_const`) in the `KLPar` form. -/
theorem KLIndStepA_SigmaPi_add_const (hκ : 0 < κ) (p : KLPar κ gmax) {n : ℕ} [NeZero n]
    (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) (δ : Fin n → Zd d p.L) (c : Zd d p.L) :
    KLSigmaPi d p.L p.g (mSigma p.E) p.t σ π (fun v => δ v + c)
      = KLSigmaPi d p.L p.g (mSigma p.E) p.t σ π δ := by
  have hE2 : |p.E| ≤ 2 := by linarith [p.hE]
  exact SumZero_SigmaPi_add_const d p.L p.g (mSigma p.E)
    (fun s s' => norm_mul_mSigma_lt_one hE2 p.ht0 p.ht1 s s') p.hL σ π δ c

/-- **Group (G1) of case (ii), abstract**: if `Sg(c - δ) = Sg(δ)` for every `c`, then on the slice
`δ_r = b` the antisymmetric part `f₁` of a leaf integrates to zero against `Sg`:
`Σ_{δ_r = b} Sg(δ) f₁(δ_i - b) = 0`, for every `i` and every function `f`.  Proof: the involution
`δ ↦ 2b - δ` of the slice and `KLf1_neg`. -/
theorem KLIndStepA_slice_vanish {d L n : ℕ} [NeZero L] (Sg : (Fin n → Zd d L) → ℂ)
    (hrefl : ∀ (c : Zd d L) (δ : Fin n → Zd d L), Sg (fun j => c - δ j) = Sg δ) (r i : Fin n)
    (b : Zd d L) (f : Zd d L → ℂ) :
    ∑ δ ∈ univ.filter (fun δ : Fin n → Zd d L => δ r = b), Sg δ * KLf1 f (δ i - b) = 0 := by
  set S := univ.filter (fun δ : Fin n → Zd d L => δ r = b) with hS
  set F : (Fin n → Zd d L) → ℂ := fun δ => Sg δ * KLf1 f (δ i - b) with hF
  set ι : (Fin n → Zd d L) → (Fin n → Zd d L) := fun δ j => (b + b) - δ j with hι
  have hmem : ∀ δ, δ ∈ S ↔ δ r = b := fun δ => by simp [hS]
  have hιι : ∀ δ, ι (ι δ) = δ := fun δ => funext fun j => by simp [hι]
  have h1 : ∑ δ ∈ S, F (ι δ) = ∑ δ ∈ S, F δ := by
    refine Finset.sum_nbij' ι ι (fun δ hδ => ?_) (fun δ hδ => ?_) (fun δ _ => hιι δ)
      (fun δ _ => hιι δ) (fun _ _ => rfl)
    · rw [hmem] at hδ ⊢; simp [hι, hδ]
    · rw [hmem] at hδ ⊢; simp [hι, hδ]
  have hneg : ∀ δ, F (ι δ) = - F δ := by
    intro δ
    simp only [hF, hι]
    rw [hrefl (b + b) δ]
    have : (b + b - δ i - b) = -(δ i - b) := by abel
    rw [this, KLf1_neg]; ring
  have h2 : ∑ δ ∈ S, F (ι δ) = - ∑ δ ∈ S, F δ := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun δ _ => hneg δ
  have h3 : ∑ δ ∈ S, F δ = - ∑ δ ∈ S, F δ := by rw [← h2, h1]
  change ∑ δ ∈ S, F δ = 0
  linear_combination (1 / 2 : ℂ) * h3

/-- **Group (G1) of case (ii)**: the band instance of `KLIndStepA_slice_vanish` for `Σ^{(∅)}`
(`KLSigmaPi_reflect`), every `σ`, `i` and `f`. -/
theorem KLslice_f1_vanish (hκ : 0 < κ) (p : KLPar κ gmax) {n : ℕ} [NeZero n] (σ : Fin n → Bool)
    (r i : Fin n) (b : Zd d p.L) (f : Zd d p.L → ℂ) :
    ∑ δ ∈ univ.filter (fun δ : Fin n → Zd d p.L => δ r = b),
        KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ * KLf1 f (δ i - b) = 0 :=
  KLIndStepA_slice_vanish (fun δ => KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ)
    (fun c δ => KLSigmaPi_reflect hκ p σ c δ) r i b f

/-- A sum over the slice `δ_i = x` of a translation-invariant function does not depend on the
index `i`. -/
theorem KLIndStepA_sum_slice_root {β : Type*} [AddCommMonoid β] {d L n : ℕ} [NeZero L]
    (φ : (Fin n → Zd d L) → β) (hφ : ∀ δ c, φ (fun v => δ v + c) = φ δ) (i i' : Fin n)
    (x : Zd d L) :
    ∑ δ ∈ univ.filter (fun δ : Fin n → Zd d L => δ i = x), φ δ
      = ∑ δ ∈ univ.filter (fun δ : Fin n → Zd d L => δ i' = x), φ δ := by
  refine Finset.sum_nbij' (fun δ v => δ v + (x - δ i')) (fun δ v => δ v + (x - δ i))
    (fun δ hδ => ?_) (fun δ hδ => ?_) (fun δ hδ => ?_) (fun δ hδ => ?_) (fun δ _ => ?_)
  · simp
  · simp
  · have h : δ i = x := by simpa using hδ
    funext v
    simp only [h]
    abel
  · have h : δ i' = x := by simpa using hδ
    funext v
    simp only [h]
    abel
  · exact (hφ δ (x - δ i')).symm

/-- `max_{ij} |δ_i - δ_j|` is translation invariant. -/
theorem KLIndStepA_maxDist_add_const {d L n : ℕ} [NeZero L] (δ : Fin n → Zd d L) (c : Zd d L) :
    KLmaxDist d L (fun v => δ v + c) = KLmaxDist d L δ := by
  simp [KLmaxDist, add_sub_add_right_eq_sub]

/-- `|δ_i - δ_j| ≤ max_{ij} |δ_i - δ_j|`. -/
theorem KLIndStepA_dist_le_maxDist {d L n : ℕ} [NeZero L] (δ : Fin n → Zd d L) (i j : Fin n) :
    zdistD d L (δ i - δ j) ≤ KLmaxDist d L δ :=
  Finset.le_sup (f := fun q : Fin n × Fin n => zdistD d L (δ q.1 - δ q.2)) (mem_univ (i, j))

end Reflect


/-! ## 5. Alternating charge vectors and the sum-zero estimates on every slice -/

section Alt

/-- An alternating `σ` (`σ_j ≠ σ_{j+1}` cyclically) has `n` even and is `σ^{(alt)}` or its
complement. -/
theorem KLIndStepA_alt_cases {n : ℕ} [NeZero n] (σ : Fin n → Bool) (h : ∀ j, σ j ≠ σ (j + 1)) :
    Even n ∧ (σ = KLsigAlt n ∨ σ = fun k => !KLsigAlt n k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := NeZero.pos n; omega⟩
  have hP : ∀ k : Fin (m + 1), σ k = if k.val % 2 = 0 then σ 0 else !σ 0 := by
    intro k
    induction k using Fin.induction with
    | zero => simp
    | succ i ih =>
      have h1 := h i.castSucc
      rw [Fin.coeSucc_eq_succ] at h1
      have h2 : σ i.succ = !σ i.castSucc := by
        cases hx : σ i.castSucc <;> cases hy : σ i.succ <;> simp_all
      rw [h2, ih]
      simp only [Fin.val_succ, Fin.val_castSucc]
      by_cases hi : i.val % 2 = 0
      · have : ¬ (i.val + 1) % 2 = 0 := by omega
        simp [hi, this]
      · have : (i.val + 1) % 2 = 0 := by omega
        simp [hi, this]
  have hlast := h (Fin.last m)
  rw [Fin.last_add_one] at hlast
  have hl := hP (Fin.last m)
  simp only [Fin.val_last] at hl
  have hm : ¬ m % 2 = 0 := fun hm => hlast (by rw [hl]; simp [hm])
  have hev : Even (m + 1) := Nat.even_iff.2 (by omega)
  refine ⟨hev, ?_⟩
  cases h0 : σ 0
  · right
    funext k
    rw [hP k, h0]
    simp [KLsigAlt]
  · left
    funext k
    rw [hP k, h0]
    simp [KLsigAlt]

end Alt

section Signed

variable {d : ℕ} {κ gmax : ℝ}

/-- Complex conjugation exchanges the two charges: `Q(¬σ, ∅) = conj Q(σ, ∅)`. -/
theorem KLIndStepA_Qlayer_not (E t : ℝ) {n : ℕ} [NeZero n] (σ : Fin n → Bool) :
    Qlayer (mSigma E) t (fun k => !σ k) ∅ = (starRingEnd ℂ) (Qlayer (mSigma E) t σ ∅) := by
  have hT : KLTSPlong n (fun k => !σ k) ∅ = KLTSPlong n σ ∅ := by
    unfold KLTSPlong KLFlong
    refine Finset.filter_congr fun F _ => ?_
    have : (F.filter fun J => (!σ J.1) ≠ (!σ J.2)) = F.filter fun J => σ J.1 ≠ σ J.2 :=
      Finset.filter_congr fun J _ => by cases σ J.1 <;> cases σ J.2 <;> simp
    rw [this]
  have hm : ∀ s : Bool, mSigma E (!s) = (starRingEnd ℂ) (mSigma E s) := fun s => by
    cases s <;> simp [mSigma]
  unfold Qlayer
  rw [hT, map_sum]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun e _ => ?_
  simp only [edgeR, hm, map_sub, map_inv₀, map_mul, map_one, Complex.conj_ofReal]

/-- **The signed sum-zero estimate on every slice and for both alternating charge vectors**
(`(eq:Sigma-empty-sum-zero)`, first estimate): `‖Σ_{δ_r = x} Σ^{(∅)}(σ, δ)‖ ≤ C (1-t)`, `σ` alternating
(`σ^{(alt)}` or its complement), any root `r`, any `x`.  From the merged `KLsumZero_holds` (root `0`,
`σ^{(alt)}`) through `SumZero_sum_slice` (the slice sum is `(∏ m) Q(σ,∅)`, independent of `r` and
`x`) and `KLIndStepA_Qlayer_not`. -/
theorem KLIndStepA_sumZero_signed (n : ℕ) [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) (hκ : 0 < κ) (hg : 0 < gmax)
    (hshort : KLShort d κ gmax) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool), (∀ j, σ j ≠ σ (j + 1)) →
      ∀ (r : Fin n) (x : Zd d p.L),
        ‖∑ δ ∈ univ.filter (fun δ : Fin n → Zd d p.L => δ r = x),
            KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ‖ ≤ C * (1 - p.t) := by
  by_cases hev : Even n ∧ 4 ≤ n
  · obtain ⟨C, hC, H⟩ := KLsumZero_holds d n κ gmax hd hev.2 hev.1 hκ hg hshort
    refine ⟨C, hC, fun p σ hσ r x => ?_⟩
    have hE2 : |p.E| ≤ 2 := by linarith [p.hE]
    have hm : ∀ s s' : Bool, ‖(p.t : ℂ) * (mSigma p.E s * mSigma p.E s')‖ < 1 := fun s s' =>
      norm_mul_mSigma_lt_one hE2 p.ht0 p.ht1 s s'
    have hprod : ∀ σ' : Fin n → Bool, ‖∏ j, mSigma p.E (σ' j)‖ = 1 := fun σ' => by
      simp [norm_prod, norm_mSigma hE2]
    have hsl : ∀ (σ' : Fin n → Bool) (i : Fin n) (y : Zd d p.L),
        ‖∑ δ ∈ univ.filter (fun δ : Fin n → Zd d p.L => δ i = y),
            KLSigmaPi d p.L p.g (mSigma p.E) p.t σ' ∅ δ‖
          = ‖Qlayer (mSigma p.E) p.t σ' ∅‖ := fun σ' i y => by
      rw [SumZero_sum_slice d p.L p.g (mSigma p.E) hm p.hL σ' ∅ i y, norm_mul, hprod, one_mul]
    have hQalt : ‖Qlayer (mSigma p.E) p.t (KLsigAlt n) ∅‖ ≤ C * (1 - p.t) := by
      have := (H p 0).1
      rwa [hsl] at this
    rw [hsl]
    obtain ⟨-, hcase⟩ := KLIndStepA_alt_cases σ hσ
    rcases hcase with rfl | rfl
    · exact hQalt
    · rw [KLIndStepA_Qlayer_not, Complex.norm_conj]; exact hQalt
  · refine ⟨1, one_pos, fun p σ hσ r x => ?_⟩
    exfalso
    obtain ⟨hev', -⟩ := KLIndStepA_alt_cases σ hσ
    obtain ⟨m, hm⟩ := hev'
    exact hev ⟨⟨m, hm⟩, by omega⟩

end Signed

section Weighted

variable {d : ℕ} {κ gmax : ℝ}

/-- `(M+1)^Q e^{-cM} ≤ C_Q e^{-(c/2) M}`. -/
private theorem KLIndStepA_poly_exp (Q : ℕ) {c : ℝ} (hc : 0 < c) {M : ℝ} (hM : 0 ≤ M) :
    (M + 1) ^ Q * Real.exp (-(c * M))
      ≤ (2 ^ Q * (1 + (Nat.factorial Q : ℝ) / (c / 2) ^ Q)) * Real.exp (-(c / 2 * M)) := by
  have hc2 : 0 < c / 2 := by positivity
  have h1 : (M + 1) ^ Q ≤ 2 ^ Q * (M ^ Q + 1) := by
    have h := KLIndStepA_pow_le Q hM
    exact h
  have h2 := pow_mul_exp_neg_le hc2 Q hM
  have h3 : Real.exp (-(c / 2 * M)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith)
  have h4 : Real.exp (-(c * M)) = Real.exp (-(c / 2 * M)) * Real.exp (-(c / 2 * M)) := by
    rw [← Real.exp_add]; congr 1; ring
  set e := Real.exp (-(c / 2 * M)) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  rw [h4]
  calc (M + 1) ^ Q * (e * e) ≤ (2 ^ Q * (M ^ Q + 1)) * (e * e) := by gcongr
    _ = 2 ^ Q * ((M ^ Q * e) + e) * e := by ring
    _ ≤ 2 ^ Q * ((Nat.factorial Q : ℝ) / (c / 2) ^ Q + 1) * e := by gcongr
    _ = (2 ^ Q * (1 + (Nat.factorial Q : ℝ) / (c / 2) ^ Q)) * e := by ring

/-- `Σ_{δ_r = x} e^{-c max|δ_i - δ_j|} ≤ expC(c/n)^{n-1}` for every root `r`: the merged
`KLMolecule_sum_exp_maxDist` (root `0`) and `KLIndStepA_sum_slice_root`. -/
private theorem KLIndStepA_sum_exp_root (k : ℕ) {n : ℕ} [NeZero n] {L : ℕ} [NeZero L] {c : ℝ}
    (hc : 0 < c) (r : Fin n) (x : Zd (k + 2) L) :
    ∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) L => δ r = x),
        Real.exp (-(c * (KLmaxDist (k + 2) L δ : ℝ))) ≤ (expC k (c / n)) ^ (n - 1) := by
  rw [KLIndStepA_sum_slice_root (fun δ : Fin n → Zd (k + 2) L => Real.exp (-(c * (KLmaxDist (k + 2) L δ : ℝ))))
    (fun δ c' => by rw [KLIndStepA_maxDist_add_const]) r 0 x]
  exact KLMolecule_sum_exp_maxDist k hc x

/-- **The `g²` gain for a non-constant `δ`** (the block `hnc` of the merged `KLsumZero_holds`, for
every `σ`): every labelling of the tree sum consistent with a non-constant `δ` has an off-diagonal
edge, which carries `C_κ g²` (`(prop:ThfadC_short)`, no `1_{a=0}` term). -/
private theorem KLIndStepA_nc_pointwise (k n : ℕ) [NeZero n] (hn : 3 ≤ n) (hκ : 0 < κ)
    (hshort : KLShort (k + 2) κ gmax) :
    ∃ G : ℝ, 0 ≤ G ∧ ∃ c : ℝ, 0 < c ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool)
      (δ : Fin n → Zd (k + 2) p.L), (∃ v w : Fin n, δ v ≠ δ w) →
        ‖KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t σ ∅ δ‖
          ≤ p.g ^ 2 * G * Real.exp (-(c * (KLmaxDist (k + 2) p.L δ : ℝ))) := by
  obtain ⟨B, hB, Cκ, hCκ, c, hc, hedge⟩ := KLMolecule_edge hκ hshort
  have hB0 : 0 < B := by linarith
  have hnn : (0 : ℝ) < ((n * n : ℕ) : ℝ) := by
    have := NeZero.pos n; exact_mod_cast Nat.mul_pos this this
  have hlam0 : 0 < c / (2 * ((n * n : ℕ) : ℝ)) := by positivity
  have hS0 : 0 < expC k (c / (2 * ((n * n : ℕ) : ℝ))) := by unfold expC; positivity
  have hT : 0 < ((TSP n).card : ℝ) := by
    exact_mod_cast card_pos.2 ⟨∅, empty_mem_TSP n⟩
  set G1 : ℝ := ((TSP n).card : ℝ) *
    (Cκ / B * B ^ (n * n) * (expC k (c / (2 * ((n * n : ℕ) : ℝ)))) ^ (n * n)) with hG1
  have hG10 : 0 ≤ G1 := by rw [hG1]; positivity
  refine ⟨G1, hG10, c / 2, by positivity, fun p σ δ hnc' => ?_⟩
  have hE2 : |p.E| ≤ 2 := by linarith [p.hE]
  obtain ⟨i, j, hij⟩ := KLMolecule_exists_pair δ
  have hX : 0 ≤ (Cκ * p.g ^ 2 / B * B ^ (n * n)) *
      (expC k (c / (2 * ((n * n : ℕ) : ℝ)))) ^ (n * n) *
        Real.exp (-(c / 2 * (zdistD (k + 2) p.L (δ i - δ j) : ℝ))) := by positivity
  have h := KLMolecule_SigmaPi_of_tree (g := p.g) (t := p.t) hE2 σ δ hX
    (fun F hF => by
      have hsame := KLMolecule_same_charge hF
      have hFT : F ∈ TSP n := (mem_filter.1 hF).1
      exact KLMolecule_selfW_bound_nc (KLisTSP_of_mem_TSP hFT) (by omega) k δ _ hB
        (ε := Cκ * p.g ^ 2) (by positivity) hc
        (fun J x y => by
          have := (hedge p (σ J.1.1)).1 x y
          rw [← hsame J.1 J.2]
          exact this)
        (fun J x y hxy => by
          have := (hedge p (σ J.1.1)).2 x y hxy
          rw [← hsame J.1 J.2]
          exact this)
        hnc' i j)
  rw [hij]
  calc _ ≤ _ := h
    _ = _ := by rw [hG1]; ring

/-- **The weighted sum-zero estimate** (new; `(eq:Sigma-empty-sum-zero)` in the form case (ii) needs):
for every `Q`, every alternating `σ` (`σ^{(alt)}` or its complement), every root `r` and every `x`,
`‖Σ_{δ_r = x} Σ^{(∅)}‖ ≤ C (1-t)` and
`Σ_{δ_r = x} |Σ^{(∅)}(δ)| (max|δ_i - δ_j| + 1)^Q ≤ C (g² + (1-t))`; `C = C(d, n, κ, gmax, Q)`.
The unweighted absolute sum of the merged `KLsumZero_holds` and the exponential decay of
`KLmolecule_holds` do not give the weighted one uniformly in `g, 1-t` (they allow mass `g²+1-t` at
`max|δ_i - δ_j| ≈ log(1/(g²+1-t))`); the pointwise `g²` factor of a non-constant `δ` does. -/
theorem KLsumZero_weighted (n : ℕ) [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) (hκ : 0 < κ) (hg : 0 < gmax)
    (hshort : KLShort d κ gmax) (Q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool), (∀ j, σ j ≠ σ (j + 1)) →
      ∀ (r : Fin n) (x : Zd d p.L),
        ‖∑ δ ∈ univ.filter (fun δ : Fin n → Zd d p.L => δ r = x),
            KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ‖ ≤ C * (1 - p.t) ∧
        ∑ δ ∈ univ.filter (fun δ : Fin n → Zd d p.L => δ r = x),
            ‖KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ‖ * ((KLmaxDist d p.L δ : ℝ) + 1) ^ Q
          ≤ C * (p.g ^ 2 + (1 - p.t)) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  obtain ⟨C₁, hC₁, hsig⟩ := KLIndStepA_sumZero_signed n hd hn hκ hg hshort
  obtain ⟨G, hG, c, hc, hnc⟩ := KLIndStepA_nc_pointwise k n hn hκ hshort
  set CQ : ℝ := 2 ^ Q * (1 + (Nat.factorial Q : ℝ) / (c / 2) ^ Q) with hCQ
  set R : ℝ := G * CQ * (expC k (c / 2 / n)) ^ (n - 1) with hR
  have hCQ0 : 0 ≤ CQ := by rw [hCQ]; positivity
  have hR0 : 0 ≤ R := by rw [hR]; unfold expC; positivity
  refine ⟨C₁ + 2 * R + 1, by linarith, fun p σ hσ r x => ?_⟩
  have hsx := hsig p σ hσ r x
  have h1t : 0 < 1 - p.t := by linarith [p.ht1]
  have hg2 : 0 ≤ p.g ^ 2 := sq_nonneg _
  refine ⟨hsx.trans ?_, ?_⟩
  · nlinarith [mul_nonneg hR0 h1t.le]
  set S := univ.filter (fun δ : Fin n → Zd (k + 2) p.L => δ r = x) with hS
  set c0 : Fin n → Zd (k + 2) p.L := fun _ => x with hc0
  have hc0S : c0 ∈ S := by simp [hS, hc0]
  have hM0 : KLmaxDist (k + 2) p.L c0 = 0 := by simp [KLmaxDist, hc0]
  have hrest : ∑ δ ∈ S.erase c0, ‖KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t σ ∅ δ‖
        * ((KLmaxDist (k + 2) p.L δ : ℝ) + 1) ^ Q ≤ p.g ^ 2 * R := by
    calc _ ≤ ∑ δ ∈ S.erase c0, p.g ^ 2 * G
          * (CQ * Real.exp (-(c / 2 * (KLmaxDist (k + 2) p.L δ : ℝ)))) := by
          refine sum_le_sum fun δ hδ => ?_
          obtain ⟨hne, hδS⟩ := mem_erase.1 hδ
          have hδr : δ r = x := (mem_filter.1 hδS).2
          have hnc' : ∃ v w : Fin n, δ v ≠ δ w := by
            by_contra hcon
            push Not at hcon
            exact hne (funext fun i => (hcon i r).trans hδr)
          have h1 := hnc p σ δ hnc'
          have h2 := KLIndStepA_poly_exp Q hc (Nat.cast_nonneg (KLmaxDist (k + 2) p.L δ))
          calc ‖KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t σ ∅ δ‖
                * ((KLmaxDist (k + 2) p.L δ : ℝ) + 1) ^ Q
              ≤ (p.g ^ 2 * G * Real.exp (-(c * (KLmaxDist (k + 2) p.L δ : ℝ))))
                * ((KLmaxDist (k + 2) p.L δ : ℝ) + 1) ^ Q := by gcongr
            _ = p.g ^ 2 * G * (((KLmaxDist (k + 2) p.L δ : ℝ) + 1) ^ Q
                * Real.exp (-(c * (KLmaxDist (k + 2) p.L δ : ℝ)))) := by ring
            _ ≤ p.g ^ 2 * G * (CQ * Real.exp (-(c / 2 * (KLmaxDist (k + 2) p.L δ : ℝ)))) := by
                gcongr
      _ ≤ ∑ δ ∈ S, p.g ^ 2 * G * (CQ * Real.exp (-(c / 2 * (KLmaxDist (k + 2) p.L δ : ℝ)))) :=
          sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun δ _ _ => by positivity
      _ = p.g ^ 2 * G * CQ * ∑ δ ∈ S, Real.exp (-(c / 2 * (KLmaxDist (k + 2) p.L δ : ℝ))) := by
          rw [Finset.mul_sum]
          exact sum_congr rfl fun δ _ => by ring
      _ ≤ p.g ^ 2 * G * CQ * (expC k (c / 2 / n)) ^ (n - 1) :=
          mul_le_mul_of_nonneg_left (KLIndStepA_sum_exp_root k (by positivity) r x)
            (by positivity)
      _ = p.g ^ 2 * R := by rw [hR]; ring
  -- the constant pattern is read off from the signed sum
  have habs := add_sum_erase S (fun δ => ‖KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t σ ∅ δ‖
    * ((KLmaxDist (k + 2) p.L δ : ℝ) + 1) ^ Q) hc0S
  have hsg := add_sum_erase S (fun δ => KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t σ ∅ δ) hc0S
  have hc0norm : ‖KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t σ ∅ c0‖ ≤
      ‖∑ δ ∈ S, KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t σ ∅ δ‖ +
        ∑ δ ∈ S.erase c0, ‖KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t σ ∅ δ‖ := by
    have h1 : KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t σ ∅ c0
        = ∑ δ ∈ S, KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t σ ∅ δ
          - ∑ δ ∈ S.erase c0, KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t σ ∅ δ := by
      rw [← hsg]; ring
    rw [h1]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
  have hrest0 : ∑ δ ∈ S.erase c0, ‖KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t σ ∅ δ‖
      ≤ ∑ δ ∈ S.erase c0, ‖KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t σ ∅ δ‖
        * ((KLmaxDist (k + 2) p.L δ : ℝ) + 1) ^ Q :=
    sum_le_sum fun δ _ => le_mul_of_one_le_right (norm_nonneg _)
      (one_le_pow₀ (by linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ KLmaxDist (k + 2) p.L δ)]))
  rw [← habs]
  simp only [hM0, Nat.cast_zero, zero_add, one_pow, mul_one]
  have hsx' : ‖∑ δ ∈ S, KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t σ ∅ δ‖ ≤ C₁ * (1 - p.t) := hsx
  nlinarith [mul_nonneg hC₁.le hg2, mul_nonneg hR0 h1t.le, mul_nonneg hg2 hR0]

end Weighted


/-! ## 5b. The abstract data of the induction step: three bundles and their band instances

The pins of the abstract step (`indStepAbs_of`, `KLIndStepB.lean` §6): the leaf bundle `IndStepTH`
(properties 5, 5', 6, 7, 8 of `lem_propTH`, translation invariance, the row sum), the molecule
decay `SigDecayAbs` and the sum-zero interface `SigSumZeroAbs` (D194).  The band instances are
at `ι = KLPar κ gmax`, `L = (·.L)`, `g = (·.g)`, `t = (·.t)`, `Sig = Σ^{(∅)}`, `TH = thetaEdge`. -/

section Abstract

/-- **`SigSumZeroAbs`** (K-b, form (i)): for every alternating `σ`, reflection `Σ(c - δ) = Σ(δ)`,
translation `Σ(δ + c) = Σ(δ)`, and on every slice `δ_r = x` the signed estimate `O(1-t)` and the
weighted absolute estimate `O(g² + 1 - t)` with weight `(max_{i,j}|δ_i - δ_j| + 1)^Q`, every
`Q ≤ 2(d-1)`.  Band form: `KLsumZero_weighted`. -/
def SigSumZeroAbs {ι : Type} (d n : ℕ) [NeZero n] (L : ι → ℕ) [∀ i, NeZero (L i)] (g t : ι → ℝ)
    (Sig : ∀ i, (Fin n → Bool) → (Fin n → Zd d (L i)) → ℂ) : Prop :=
  (∀ (i : ι) (σ : Fin n → Bool), (∀ j, σ j ≠ σ (j + 1)) → ∀ (c : Zd d (L i)) (δ : Fin n → Zd d (L i)),
      Sig i σ (fun j => c - δ j) = Sig i σ δ) ∧
  (∀ (i : ι) (σ : Fin n → Bool), (∀ j, σ j ≠ σ (j + 1)) → ∀ (δ : Fin n → Zd d (L i)) (c : Zd d (L i)),
      Sig i σ (fun j => δ j + c) = Sig i σ δ) ∧
  ∀ Q : ℕ, Q ≤ 2 * (d - 1) → ∃ C : ℝ, 0 < C ∧
    ∀ (i : ι) (σ : Fin n → Bool), (∀ j, σ j ≠ σ (j + 1)) → ∀ (r : Fin n) (x : Zd d (L i)),
      ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d (L i) => δ r = x), Sig i σ δ‖ ≤ C * (1 - t i) ∧
      ∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d (L i) => δ r = x),
          ‖Sig i σ δ‖ * ((KLmaxDist d (L i) δ : ℝ) + 1) ^ Q ≤ C * (g i ^ 2 + (1 - t i))

/-- **`SigDecayAbs`**: `|Σ(σ, δ)| ≤ C e^{-c max_{i,j}|δ_i - δ_j|}` for every `σ`
(`(eq:molecule-decay)`; band form `KLmoleculeAt`). -/
def SigDecayAbs {ι : Type} (d n : ℕ) [NeZero n] (L : ι → ℕ) [∀ i, NeZero (L i)]
    (Sig : ∀ i, (Fin n → Bool) → (Fin n → Zd d (L i)) → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (i : ι) (σ : Fin n → Bool) (δ : Fin n → Zd d (L i)),
    ‖Sig i σ δ‖ ≤ C * Real.exp (-(c * (KLmaxDist d (L i) δ : ℝ)))

/-- **`IndStepTH`**, the leaf bundle in place of `KLPT`: properties 5, 5', 6, 7, 8 of `lem_propTH` for
the edge family `TH` (long edges `s ≠ s'` for 5, 6, 7, 8; short edges `s = s'` for 5'; 6 and 7 at
`c = 1/2`; loss `L^τ` in 6-8), translation invariance, and the row sum of a long edge. -/
structure IndStepTH {ι : Type} (d : ℕ) (L : ι → ℕ) [∀ i, NeZero (L i)] (g t : ι → ℝ)
    (TH : ∀ i, Bool → Bool → Matrix (Zd d (L i)) (Zd d (L i)) ℂ) : Prop where
  transl : ∀ (i : ι) (s s' : Bool) (a b : Zd d (L i)), TH i s s' a b = TH i s s' 0 (b - a)
  decay : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (i : ι) (s s' : Bool), s ≠ s' → ∀ a : Zd d (L i),
    ‖TH i s s' 0 a‖ ≤ C * Bparam d (L i) (g i) (t i) (zdistD d (L i) a)
      * Real.exp (-c * (zdistD d (L i) a : ℝ) / ellT (L i) (g i) (t i))
  short : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (i : ι) (s : Bool) (a : Zd d (L i)),
    ‖TH i s s 0 a‖ ≤ C * ((if a = 0 then (1 : ℝ) else 0) + g i ^ 2 * Real.exp (-c * (zdistD d (L i) a : ℝ)))
  diffOne : ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) (s s' : Bool), s ≠ s' → ∀ a r : Zd d (L i),
    (zdistD d (L i) r : ℝ) ≤ (1 / 2 : ℝ) * (zdistD d (L i) a : ℝ) →
    ‖TH i s s' 0 (a + r) - TH i s s' 0 a‖
      ≤ C * (L i : ℝ) ^ τ * (g i ^ 2 + |1 - t i|)⁻¹ * (zdistD d (L i) r : ℝ)
        * (((zdistD d (L i) a : ℝ) + 1) ^ (d - 1))⁻¹
  diffTwo : ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) (s s' : Bool), s ≠ s' → ∀ a r : Zd d (L i),
    (zdistD d (L i) r : ℝ) ≤ (1 / 2 : ℝ) * (zdistD d (L i) a : ℝ) →
    ‖TH i s s' 0 (a + r) + TH i s s' 0 (a - r) - 2 * TH i s s' 0 a‖
      ≤ C * (L i : ℝ) ^ τ * (g i ^ 2 + |1 - t i|)⁻¹ * (zdistD d (L i) r : ℝ) ^ 2
        * (((zdistD d (L i) a : ℝ) + 1) ^ d)⁻¹
  zeroMode : ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) (s s' : Bool), s ≠ s' → ∀ a : Zd d (L i),
    ‖TH i s s' 0 a - ((L i : ℂ) ^ (2 * d))⁻¹ * ∑ a' : Zd d (L i), ∑ b' : Zd d (L i), TH i s s' a' b'‖
      ≤ C * (L i : ℝ) ^ τ * (g i ^ 2 + |1 - t i|)⁻¹ * (((zdistD d (L i) a : ℝ) + 1) ^ (d - 2))⁻¹
  rowSum : ∀ (i : ι) (s s' : Bool), s ≠ s' → ∀ a : Zd d (L i),
    ∑ b : Zd d (L i), ‖TH i s s' a b‖ ≤ (1 - t i)⁻¹

end Abstract

section BandInstances

variable {d : ℕ} {κ gmax : ℝ}

/-- The band `Σ^{(∅)}` satisfies `SigSumZeroAbs`: `KLSigmaPi_reflect`, `KLIndStepA_SigmaPi_add_const`
and `KLsumZero_weighted` (with `KLShort_holds`). -/
theorem sigSumZeroAbs_band (n : ℕ) [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) (hκ : 0 < κ) (hg : 0 < gmax) :
    SigSumZeroAbs (ι := KLPar κ gmax) d n (fun p => p.L) (fun p => p.g) (fun p => p.t)
      (fun p σ δ => KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ) :=
  ⟨fun p σ _ c δ => KLSigmaPi_reflect hκ p σ c δ,
    fun p σ _ δ c => KLIndStepA_SigmaPi_add_const hκ p σ ∅ δ c,
    fun Q _ => KLsumZero_weighted n hd hn hκ hg (KLShort_holds d κ gmax hd hκ hg) Q⟩

/-- The band `Σ^{(∅)}` satisfies `SigDecayAbs`: `KLmolecule_holds`. -/
theorem sigDecayAbs_band (n : ℕ) [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) (hκ : 0 < κ) (hg : 0 < gmax) :
    SigDecayAbs (ι := KLPar κ gmax) d n (fun p => p.L)
      (fun p σ δ => KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ) :=
  KLmolecule_holds d n κ gmax hd hn hκ hg (KLShort_holds d κ gmax hd hκ hg)

/-- The band edges `thetaEdge` satisfy `IndStepTH` (the fields of `KLPT`; a long edge is `Θ_t`,
`KLIndStepA_thetaEdge_long`; translation `KLIndStepA_Theta_apply_sub`; row sum
`KLlat_sum_norm_Theta_row_le`).  `0 < κ` gives `|E| ≤ 2` from `|E| ≤ 2 - κ`. -/
theorem indStepTH_band (hκ : 0 < κ) (hPT : KLPT d κ gmax) :
    IndStepTH (ι := KLPar κ gmax) d (fun p => p.L) (fun p => p.g) (fun p => p.t)
      (fun p s s' => thetaEdge d p.L p.g (mSigma p.E) p.t s s') := by
  have hE2 : ∀ p : KLPar κ gmax, |p.E| ≤ 2 := fun p => by linarith [p.hE]
  refine ⟨fun p s s' a b => ?_, ?_, ?_, fun τ hτ => ?_, fun τ hτ => ?_, fun τ hτ => ?_,
    fun p s s' hss a => ?_⟩
  · exact KLIndStepA_Theta_apply_sub p.hL (norm_mul_mSigma_lt_one (hE2 p) p.ht0 p.ht1 s s') a b
  · obtain ⟨C, hC, c, hc, H⟩ := hPT.decay
    refine ⟨C, hC, c, hc, fun p s s' hss a => ?_⟩
    rw [KLIndStepA_thetaEdge_long (hE2 p) p.t hss]
    exact H p.L p.hL p.g p.hg0 p.hg1 p.t p.ht0 p.ht1 a
  · obtain ⟨C, hC, c, hc, H⟩ := hPT.short
    exact ⟨C, hC, c, hc, fun p s a => H p.L p.hL p.g p.hg0 p.hg1 p.E p.hE s p.t p.ht0 p.ht1 a⟩
  · obtain ⟨C, hC, H⟩ := hPT.diffOne (1 / 2) (by norm_num) (by norm_num) τ hτ
    refine ⟨C, hC, fun p s s' hss a r hr => ?_⟩
    rw [KLIndStepA_thetaEdge_long (hE2 p) p.t hss]
    exact H p.L p.hL p.g p.hg0 p.hg1 p.t p.ht0 p.ht1 a r hr
  · obtain ⟨C, hC, H⟩ := hPT.diffTwo (1 / 2) (by norm_num) (by norm_num) τ hτ
    refine ⟨C, hC, fun p s s' hss a r hr => ?_⟩
    rw [KLIndStepA_thetaEdge_long (hE2 p) p.t hss]
    exact H p.L p.hL p.g p.hg0 p.hg1 p.t p.ht0 p.ht1 a r hr
  · obtain ⟨C, hC, H⟩ := hPT.zeroMode τ hτ
    refine ⟨C, hC, fun p s s' hss a => ?_⟩
    rw [KLIndStepA_thetaEdge_long (hE2 p) p.t hss]
    exact H p.L p.hL p.g p.hg0 p.hg1 p.t p.ht0 p.ht1 a
  · rw [KLIndStepA_thetaEdge_long (hE2 p) p.t hss]
    exact KLlat_sum_norm_Theta_row_le p.hL p.ht0 p.ht1 a

end BandInstances

section AbstractF12

variable {ι : Type} {d : ℕ} {L : ι → ℕ} [∀ i, NeZero (L i)] {g t : ι → ℝ}
  {TH : ∀ i, Bool → Bool → Matrix (Zd d (L i)) (Zd d (L i)) ℂ}

/-- **`(eq:f12)` over abstract data**: `|f₁| ≤ C L^τ (g²+|1-t|)⁻¹ (|s|+1)^{d-1}/(|a-b|+1)^{d-1}` and
`|f₂| ≤ C L^τ (g²+|1-t|)⁻¹ (|s|+1)^d/(|a-b|+1)^d` for the leaf `s ↦ TH(a, b + s)` of a long edge, from
the `transl`, `diffOne`, `diffTwo`, `zeroMode` fields of `IndStepTH` (the generalisation of
`KLf12_bound`); `C` is uniform in `i`. -/
theorem KLIndStepA_f12_abs (hd : 3 ≤ d) (hTH : IndStepTH d L g t TH) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) (s s' : Bool), s ≠ s' → ∀ a b x : Zd d (L i),
      ‖KLf1 (fun y => TH i s s' a (b + y)) x‖
        ≤ C * (L i : ℝ) ^ τ * (g i ^ 2 + |1 - t i|)⁻¹ * (((zdistD d (L i) x : ℝ) + 1) ^ (d - 1))
            * ((((zdistD d (L i) (a - b) : ℝ) + 1) ^ (d - 1))⁻¹) ∧
      ‖KLf2 (fun y => TH i s s' a (b + y)) x‖
        ≤ C * (L i : ℝ) ^ τ * (g i ^ 2 + |1 - t i|)⁻¹ * (((zdistD d (L i) x : ℝ) + 1) ^ d)
            * ((((zdistD d (L i) (a - b) : ℝ) + 1) ^ d)⁻¹) := by
  obtain ⟨CD1, hCD1, H1⟩ := hTH.diffOne τ hτ
  obtain ⟨CD2, hCD2, H2⟩ := hTH.diffTwo τ hτ
  obtain ⟨CZ, hCZ, HZ⟩ := hTH.zeroMode τ hτ
  refine ⟨max (max CD1 CD2) (2 ^ d * 2 * CZ), lt_max_of_lt_left (lt_max_of_lt_left hCD1),
    fun i s s' hss a b x => ?_⟩
  have hLt : 0 ≤ (L i : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) τ
  have hA : 0 ≤ (g i ^ 2 + |1 - t i|)⁻¹ := by positivity
  have hCZ' : 2 ^ d * 2 * CZ ≤ max (max CD1 CD2) (2 ^ d * 2 * CZ) := le_max_right _ _
  exact ⟨KLIndStepA_f1_core (by omega) _ hLt hA hCD1.le hCZ.le
      ((le_max_left _ _).trans (le_max_left _ _)) hCZ' (hTH.transl i s s')
      (H1 i s s' hss) (HZ i s s' hss) a b x,
    KLIndStepA_f2_core (by omega) _ hLt hA hCD2.le hCZ.le
      ((le_max_right _ _).trans (le_max_left _ _)) hCZ' (hTH.transl i s s')
      (H2 i s s' hss) (HZ i s s' hss) a b x⟩

end AbstractF12



/-! ## 6. Case (i): a short leaf -/

section NonAlt

variable {d : ℕ} {κ gmax : ℝ}

/-- The two bounds on a leaf over abstract data: every leaf is `≤ K₁ B_{t,0}`, a short leaf is
`≤ K₂ e^{-c_s |a - x|}` (`decay`, `short`, `transl` of `IndStepTH`; `B_{t,0} ≥ (1+g_max²)⁻¹` from the
range). -/
theorem KLIndStepA_leaf_abs {ι : Type} {L : ι → ℕ} [∀ i, NeZero (L i)] {g t : ι → ℝ}
    {TH : ∀ i, Bool → Bool → Matrix (Zd d (L i)) (Zd d (L i)) ℂ}
    (hr : ∀ i, 3 ≤ L i ∧ 0 < g i ∧ g i ≤ gmax ∧ 0 ≤ t i ∧ t i < 1) (hTH : IndStepTH d L g t TH) :
    ∃ K₁ K₂ cs : ℝ, 0 < K₁ ∧ 0 < K₂ ∧ 0 < cs ∧ ∀ (i : ι) (s s' : Bool) (a x : Zd d (L i)),
      ‖TH i s s' a x‖ ≤ K₁ * Bparam d (L i) (g i) (t i) 0 ∧
      (s = s' → ‖TH i s s' a x‖ ≤ K₂ * Real.exp (-(cs * (zdistD d (L i) (a - x) : ℝ)))) := by
  obtain ⟨Cd, hCd, cd, hcd, HD⟩ := hTH.decay
  obtain ⟨Cs, hCs, cs, hcs, HS⟩ := hTH.short
  refine ⟨Cd + Cs * (1 + gmax ^ 2) ^ 2, Cs * (1 + gmax ^ 2), cs, by positivity, by positivity,
    hcs, fun i s s' a x => ⟨?_, fun hss => ?_⟩⟩
  · by_cases hss : s = s'
    · subst hss
      obtain ⟨hL, hg0, hg1, ht0, ht1⟩ := hr i
      have h1 : ‖TH i s s a x‖
          ≤ Cs * ((if x - a = 0 then (1 : ℝ) else 0) + g i ^ 2 * Real.exp (-cs * (zdistD d (L i) (x - a) : ℝ))) := by
        rw [hTH.transl i s s a x]
        exact HS i s (x - a)
      refine h1.trans ?_
      have hg2' : g i ^ 2 ≤ gmax ^ 2 := pow_le_pow_left₀ hg0.le hg1 2
      have hite : (if x - a = 0 then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
      have hexp : Real.exp (-cs * (zdistD d (L i) (x - a) : ℝ)) ≤ 1 :=
        Real.exp_le_one_iff.2 (by have := Nat.cast_nonneg (α := ℝ) (zdistD d (L i) (x - a)); nlinarith)
      have hA : (1 + gmax ^ 2)⁻¹ ≤ Bparam d (L i) (g i) (t i) 0 := by
        refine le_trans ?_ (KLlat_inv_le_Bparam (t i))
        apply inv_anti₀ (by positivity)
        have : |1 - t i| ≤ 1 := by rw [abs_le]; constructor <;> linarith
        linarith
      have hB1 : 1 ≤ (1 + gmax ^ 2) * Bparam d (L i) (g i) (t i) 0 := by
        have h := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 1 + gmax ^ 2)
        rwa [mul_inv_cancel₀ (by positivity)] at h
      calc Cs * ((if x - a = 0 then (1 : ℝ) else 0) + g i ^ 2 * Real.exp (-cs * (zdistD d (L i) (x - a) : ℝ)))
          ≤ Cs * (1 + gmax ^ 2 * 1) := by gcongr
        _ = Cs * (1 + gmax ^ 2) * 1 := by ring
        _ ≤ Cs * (1 + gmax ^ 2) * ((1 + gmax ^ 2) * Bparam d (L i) (g i) (t i) 0) := by gcongr
        _ = Cs * (1 + gmax ^ 2) ^ 2 * Bparam d (L i) (g i) (t i) 0 := by ring
        _ ≤ (Cd + Cs * (1 + gmax ^ 2) ^ 2) * Bparam d (L i) (g i) (t i) 0 := by
            have : 0 ≤ Bparam d (L i) (g i) (t i) 0 := KLIndStepA_Bparam_nonneg _ _
            nlinarith
    · rw [hTH.transl i s s' a x]
      have := KLIndStepA_decay_le_zero (by have := (hr i).1; omega) hCd.le hcd.le (x - a) (HD i s s' hss (x - a))
      have h0 : 0 ≤ Bparam d (L i) (g i) (t i) 0 := KLIndStepA_Bparam_nonneg _ _
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ Cs * (1 + gmax ^ 2) ^ 2) h0]
  · subst hss
    have h1 : ‖TH i s s a x‖
        ≤ Cs * ((if x - a = 0 then (1 : ℝ) else 0) + g i ^ 2 * Real.exp (-cs * (zdistD d (L i) (x - a) : ℝ))) := by
      rw [hTH.transl i s s a x]
      exact HS i s (x - a)
    refine h1.trans ?_
    have hg2' : g i ^ 2 ≤ gmax ^ 2 := pow_le_pow_left₀ (hr i).2.1.le (hr i).2.2.1 2
    have hxa : zdistD d (L i) (x - a) = zdistD d (L i) (a - x) := by
      rw [← zdistD_neg d (L i) (x - a), neg_sub]
    rw [hxa]
    have hite : (if x - a = 0 then (1 : ℝ) else 0) ≤ Real.exp (-cs * (zdistD d (L i) (a - x) : ℝ)) := by
      split_ifs with h
      · have : zdistD d (L i) (a - x) = 0 := by
          rw [← hxa, h]; simp
        rw [this]; simp
      · exact (Real.exp_pos _).le
    calc Cs * ((if x - a = 0 then (1 : ℝ) else 0) + g i ^ 2 * Real.exp (-cs * (zdistD d (L i) (a - x) : ℝ)))
        ≤ Cs * (Real.exp (-cs * (zdistD d (L i) (a - x) : ℝ))
            + gmax ^ 2 * Real.exp (-cs * (zdistD d (L i) (a - x) : ℝ))) := by gcongr
      _ = Cs * (1 + gmax ^ 2) * Real.exp (-(cs * (zdistD d (L i) (a - x) : ℝ))) := by
          rw [neg_mul]; ring

/-- The crude pointwise bound over abstract data (the generalisation of `KLf_crude_bound`): the three
parts `f₀`, `f₁`, `f₂` of a leaf are each `≤ K B_{t,0}`; no loss, no `s`-dependence. -/
theorem KLIndStepA_crude_abs {ι : Type} {L : ι → ℕ} [∀ i, NeZero (L i)] {g t : ι → ℝ}
    {TH : ∀ i, Bool → Bool → Matrix (Zd d (L i)) (Zd d (L i)) ℂ}
    (hr : ∀ i, 3 ≤ L i ∧ 0 < g i ∧ g i ≤ gmax ∧ 0 ≤ t i ∧ t i < 1) (hTH : IndStepTH d L g t TH) :
    ∃ K : ℝ, 0 < K ∧ ∀ (i : ι) (s s' : Bool) (a b x : Zd d (L i)),
      ‖KLf0 (fun y => TH i s s' a (b + y))‖ ≤ K * Bparam d (L i) (g i) (t i) 0 ∧
      ‖KLf1 (fun y => TH i s s' a (b + y)) x‖ ≤ K * Bparam d (L i) (g i) (t i) 0 ∧
      ‖KLf2 (fun y => TH i s s' a (b + y)) x‖ ≤ K * Bparam d (L i) (g i) (t i) 0 := by
  obtain ⟨K₁, K₂, cs, hK₁, hK₂, hcs, hleaf⟩ := KLIndStepA_leaf_abs hr hTH
  refine ⟨2 * K₁, by positivity, fun i s s' a b x => ?_⟩
  have h : ∀ y : Zd d (L i), ‖TH i s s' a (b + y)‖ ≤ K₁ * Bparam d (L i) (g i) (t i) 0 :=
    fun y => (hleaf i s s' a (b + y)).1
  have hB : 0 ≤ Bparam d (L i) (g i) (t i) 0 := KLIndStepA_Bparam_nonneg _ _
  refine ⟨?_, ?_, ?_⟩
  · have := KLIndStepA_norm_f0_le h
    nlinarith [mul_nonneg hK₁.le hB]
  · have := KLIndStepA_norm_f1_le h x
    nlinarith [mul_nonneg hK₁.le hB]
  · have := KLIndStepA_norm_f2_le h x
    linarith

/-- **Case (i) of `(eq:ind-step-bound)` over abstract data, without loss**: if some non-root leaf
`j ≠ r` is short (`σ_j = σ_{j+1}`), `Σ_b |Σ_{δ_r = b} Sig(δ) ∏_{i≠r} TH(a_i, δ_i)| ≤ C B_{t,0}^{n-2}`.
The short leaf has decay `e^{-c|a_j - δ_j|}`, the other `n-2` leaves are `≤ K B_{t,0}` pointwise
(`KLIndStepA_leaf_abs`), `Sig` decays in `max|δ_i - δ_j|` (`SigDecayAbs`); the sum over `δ` closes with
`sum_exp_decay_centre`. -/
theorem KLIndStepA_nonAlt_abs {ι : Type} (n : ℕ) [NeZero n] (hd : 3 ≤ d) {L : ι → ℕ}
    [∀ i, NeZero (L i)] {g t : ι → ℝ}
    {Sig : ∀ i, (Fin n → Bool) → (Fin n → Zd d (L i)) → ℂ}
    {TH : ∀ i, Bool → Bool → Matrix (Zd d (L i)) (Zd d (L i)) ℂ}
    (hr : ∀ i, 3 ≤ L i ∧ 0 < g i ∧ g i ≤ gmax ∧ 0 ≤ t i ∧ t i < 1) (hTH : IndStepTH d L g t TH)
    (hS : SigDecayAbs d n L Sig) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ι) (σ : Fin n → Bool) (j r : Fin n), j ≠ r → σ j = σ (j + 1) →
      ∀ a : Fin n → Zd d (L p),
      ∑ b : Zd d (L p), ‖∑ δ ∈ univ.filter (fun δ : Fin n → Zd d (L p) => δ r = b),
          Sig p σ δ * ∏ i ∈ univ.erase r, TH p (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ C * (Bparam d (L p) (g p) (t p) 0) ^ (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  obtain ⟨K₁, K₂, cs, hK₁, hK₂, hcs, hleaf⟩ := KLIndStepA_leaf_abs hr hTH
  obtain ⟨Cm, hCm, cm, hcm, hmol⟩ := hS
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hcn : 0 < cm / n := by positivity
  have hE1 : 0 < expC k cs := by unfold expC; positivity
  have hE2 : 0 < expC k (cm / n) := by unfold expC; positivity
  refine ⟨Cm * K₂ * K₁ ^ (n - 2) * expC k cs * (expC k (cm / n)) ^ (n - 1), by positivity,
    fun p σ j r hjr hj a => ?_⟩
  set B0 := Bparam (k + 2) (L p) (g p) (t p) 0 with hB0def
  have hB0 : 0 ≤ B0 := KLIndStepA_Bparam_nonneg _ _
  have hjr' : j ∈ univ.erase r := mem_erase.2 ⟨hjr, mem_univ j⟩
  have hcard : ((univ.erase r).erase j).card = n - 2 := by
    rw [card_erase_of_mem hjr', card_erase_of_mem (mem_univ r), card_univ, Fintype.card_fin]
    omega
  set F : (Fin n → Zd (k + 2) (L p)) → ℂ := fun δ =>
    Sig p σ δ *
      ∏ i ∈ univ.erase r,
        TH p (σ i) (σ (i + 1)) (a i) (δ i) with hF
  set e1 : (Fin n → Zd (k + 2) (L p)) → ℝ := fun δ =>
    Real.exp (-(cm * (KLmaxDist (k + 2) (L p) δ : ℝ))) with he1
  set e2 : (Fin n → Zd (k + 2) (L p)) → ℝ := fun δ =>
    Real.exp (-(cs * (zdistD (k + 2) (L p) (a j - δ j) : ℝ))) with he2
  set P : ℝ := Cm * K₂ * (K₁ * B0) ^ (n - 2) with hP
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hpt : ∀ δ : Fin n → Zd (k + 2) (L p), ‖F δ‖ ≤ P * (e1 δ * e2 δ) := by
    intro δ
    simp only [hF]
    rw [norm_mul, norm_prod, ← Finset.mul_prod_erase (univ.erase r) _ hjr']
    have h1 := hmol p σ δ
    have h2 := (hleaf p (σ j) (σ (j + 1)) (a j) (δ j)).2 hj
    have h3 : ∏ i ∈ (univ.erase r).erase j,
        ‖TH p (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ (K₁ * B0) ^ (n - 2) := by
      calc _ ≤ ∏ _i ∈ (univ.erase r).erase j, (K₁ * B0) :=
            prod_le_prod₀ (fun _ _ => norm_nonneg _)
              fun i _ => (hleaf p (σ i) (σ (i + 1)) (a i) (δ i)).1
        _ = (K₁ * B0) ^ (n - 2) := by rw [prod_const, hcard]
    have h4 : 0 ≤ ∏ i ∈ (univ.erase r).erase j,
        ‖TH p (σ i) (σ (i + 1)) (a i) (δ i)‖ :=
      prod_nonneg fun _ _ => norm_nonneg _
    calc ‖Sig p σ δ‖ *
          (‖TH p (σ j) (σ (j + 1)) (a j) (δ j)‖ *
            ∏ i ∈ (univ.erase r).erase j,
              ‖TH p (σ i) (σ (i + 1)) (a i) (δ i)‖)
        ≤ (Cm * e1 δ) * ((K₂ * e2 δ) * (K₁ * B0) ^ (n - 2)) := by
          gcongr
      _ = P * (e1 δ * e2 δ) := by rw [hP]; ring
  have hsum : ∑ δ : Fin n → Zd (k + 2) (L p), e1 δ * e2 δ
      ≤ expC k cs * (expC k (cm / n)) ^ (n - 1) := by
    calc ∑ δ : Fin n → Zd (k + 2) (L p), e1 δ * e2 δ
        = ∑ x : Zd (k + 2) (L p), ∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ j = x),
            e1 δ * e2 δ := (sum_fiberwise univ (fun δ : Fin n → Zd (k + 2) (L p) => δ j)
              (fun δ => e1 δ * e2 δ)).symm
      _ = ∑ x : Zd (k + 2) (L p), Real.exp (-(cs * (zdistD (k + 2) (L p) (a j - x) : ℝ))) *
            ∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ j = x), e1 δ := by
          refine sum_congr rfl fun x _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun δ hδ => ?_
          have hδj : δ j = x := (mem_filter.1 hδ).2
          simp only [he2, hδj]
          ring
      _ ≤ ∑ x : Zd (k + 2) (L p), Real.exp (-(cs * (zdistD (k + 2) (L p) (a j - x) : ℝ))) *
            (expC k (cm / n)) ^ (n - 1) := by
          refine sum_le_sum fun x _ => ?_
          exact mul_le_mul_of_nonneg_left (KLIndStepA_sum_exp_root k hcm j x) (Real.exp_pos _).le
      _ = (∑ x : Zd (k + 2) (L p), Real.exp (-(cs * (zdistD (k + 2) (L p) (a j - x) : ℝ)))) *
            (expC k (cm / n)) ^ (n - 1) := by rw [sum_mul]
      _ ≤ expC k cs * (expC k (cm / n)) ^ (n - 1) :=
          mul_le_mul_of_nonneg_right (sum_exp_decay_centre k hcs (a j)) (by positivity)
  calc ∑ b : Zd (k + 2) (L p), ‖∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b), F δ‖
      ≤ ∑ b : Zd (k + 2) (L p), ∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) (L p) => δ r = b), ‖F δ‖ :=
        sum_le_sum fun b _ => norm_sum_le _ _
    _ = ∑ δ : Fin n → Zd (k + 2) (L p), ‖F δ‖ :=
        sum_fiberwise univ (fun δ : Fin n → Zd (k + 2) (L p) => δ r) (fun δ => ‖F δ‖)
    _ ≤ ∑ δ : Fin n → Zd (k + 2) (L p), P * (e1 δ * e2 δ) := sum_le_sum fun δ _ => hpt δ
    _ = P * ∑ δ : Fin n → Zd (k + 2) (L p), e1 δ * e2 δ := by rw [mul_sum]
    _ ≤ P * (expC k cs * (expC k (cm / n)) ^ (n - 1)) := mul_le_mul_of_nonneg_left hsum hP0
    _ = Cm * K₂ * K₁ ^ (n - 2) * expC k cs * (expC k (cm / n)) ^ (n - 1) * B0 ^ (n - 2) := by
        rw [hP, mul_pow]; ring

/-- **Case (i), without loss**: the band instance of `KLIndStepA_nonAlt_abs` (`indStepTH_band`,
`sigDecayAbs_band`). -/
theorem KLindStep_nonAlt_noloss (n : ℕ) [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) (hκ : 0 < κ)
    (hg : 0 < gmax) (hPT : KLPT d κ gmax) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool) (j r : Fin n), j ≠ r →
      σ j = σ (j + 1) → ∀ a : Fin n → Zd d p.L,
      ∑ b : Zd d p.L, ‖∑ δ ∈ univ.filter (fun δ : Fin n → Zd d p.L => δ r = b),
          KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ *
            ∏ i ∈ univ.erase r,
              thetaEdge d p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ C * (Bparam d p.L p.g p.t 0) ^ (n - 2) :=
  KLIndStepA_nonAlt_abs n hd (fun p : KLPar κ gmax => ⟨p.hL, p.hg0, p.hg1, p.ht0, p.ht1⟩)
    (indStepTH_band hκ hPT) (sigDecayAbs_band n hd hn hκ hg)

/-- **`KLindStep_nonAlt`** (target 1): the pin's inequality (`KLindStepAt`, with its quantifier
order `∀ τ, ∃ C, ∀ p σ r, σ_r ≠ σ_{r+1} → ∀ a`) for every `σ` that is not alternating.  The loss
`L^τ` is not needed (`KLindStep_nonAlt_noloss`); `1 ≤ L^τ` gives the pin's shape. -/
theorem KLindStep_nonAlt (n : ℕ) [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) (hκ : 0 < κ)
    (hg : 0 < gmax) (hPT : KLPT d κ gmax) :
    ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool) (r : Fin n),
      σ r ≠ σ (r + 1) → (¬ ∀ j, σ j ≠ σ (j + 1)) → ∀ a : Fin n → Zd d p.L,
      ∑ b : Zd d p.L, ‖∑ δ ∈ univ.filter (fun δ : Fin n → Zd d p.L => δ r = b),
          KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ *
            ∏ i ∈ univ.erase r,
              thetaEdge d p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ C * (p.L : ℝ) ^ τ * (Bparam d p.L p.g p.t 0) ^ (n - 2) := by
  intro τ hτ
  obtain ⟨C, hC, H⟩ := KLindStep_nonAlt_noloss n hd hn hκ hg hPT
  refine ⟨C, hC, fun p σ r hr hna a => ?_⟩
  push Not at hna
  obtain ⟨j, hj⟩ := hna
  have hjr : j ≠ r := fun h => hr (h ▸ hj)
  refine (H p σ j r hjr hj a).trans ?_
  have hL1 : (1 : ℝ) ≤ (p.L : ℝ) ^ τ :=
    Real.one_le_rpow (by exact_mod_cast (by have := p.hL; omega : 1 ≤ p.L)) hτ.le
  have hB : 0 ≤ (Bparam d p.L p.g p.t 0) ^ (n - 2) :=
    pow_nonneg (KLIndStepA_Bparam_nonneg _ _) _
  nlinarith [mul_nonneg hC.le hB]

end NonAlt


/-! ## 7. The compiled instances: `d = 3`, `L = 5`, `g = 1/2`, `E = 0`, `t = 9/10` -/

section Instances

/-- Target 1, case (i): `n = 3`, `σ = (+,-,+)`, root `r = 0` (long: `σ_0 ≠ σ_1`), the short leaf is
`j = 2` (`σ_2 = σ_0`); `a = (0, 1, 2)`; `KLPT 3 1 1` is the only hypothesis left. -/
example (hPT : KLPT 3 1 1) :
    ∃ C : ℝ, 0 < C ∧
      ∑ b : Zd 3 5, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 3 → Zd 3 5 => δ 0 = b),
          KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLinstσ ∅ δ *
            ∏ i ∈ Finset.univ.erase (0 : Fin 3),
              thetaEdge 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLinstσ i) (KLinstσ (i + 1)) (KLinsta i) (δ i)‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (3 - 2) := by
  obtain ⟨C, hC, H⟩ := KLindStep_nonAlt 3 (by norm_num) (by norm_num) one_pos one_pos hPT 1 one_pos
  exact ⟨C, hC, H KLinstPar KLinstσ 0 (by decide) (by decide) KLinsta⟩

/-- Target 1 (no loss), the same data with the short leaf named. -/
example (hPT : KLPT 3 1 1) :
    ∃ C : ℝ, 0 < C ∧
      ∑ b : Zd 3 5, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 3 → Zd 3 5 => δ 0 = b),
          KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLinstσ ∅ δ *
            ∏ i ∈ Finset.univ.erase (0 : Fin 3),
              thetaEdge 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLinstσ i) (KLinstσ (i + 1)) (KLinsta i) (δ i)‖
        ≤ C * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (3 - 2) := by
  obtain ⟨C, hC, H⟩ := KLindStep_nonAlt_noloss 3 (by norm_num) (by norm_num) one_pos one_pos hPT
  exact ⟨C, hC, H KLinstPar KLinstσ 2 0 (by decide) (by decide) KLinsta⟩

/-- Target 2: the splitting of a long leaf at a nonzero `s` with `s ≠ -s`. -/
example (s : Zd 3 5) (hs : s = ![1, 2, 0]) :
    let f : Zd 3 5 → ℂ := fun s => Theta 3 5 (1 / 2) (((9 / 10 : ℝ)) : ℂ) 0 (![1, 1, 1] + s)
    s ≠ -s ∧ KLf0 f + KLf1 f s + KLf2 f s = f s ∧ KLf1 f (-s) = -KLf1 f s ∧
      KLf2 f (-s) = KLf2 f s := by
  intro f
  refine ⟨?_, KLf_split f s, KLf1_neg f s, KLf2_neg f s⟩
  subst hs
  decide

/-- Target 3, `(eq:f12)`: the three bounds at `a = (0,0,0)`, `b = (1,1,1)`, `s = (2,1,0)`
(`|s| = 3`, `|a - b| = 3`), loss exponent `τ = 1`. -/
example (hPT : KLPT 3 1 1) :
    ∃ C : ℝ, 0 < C ∧
      ‖KLf0 (fun s => Theta 3 5 (1 / 2) (((9 / 10 : ℝ)) : ℂ) 0 (![1, 1, 1] + s))‖
        ≤ C * Bparam 3 5 (1 / 2) (9 / 10) 0 ∧
      ‖KLf1 (fun s => Theta 3 5 (1 / 2) (((9 / 10 : ℝ)) : ℂ) 0 (![1, 1, 1] + s)) ![2, 1, 0]‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * ((1 / 2) ^ 2 + |1 - 9 / 10|)⁻¹
            * (((zdistD 3 5 (![2, 1, 0] : Zd 3 5) : ℝ) + 1) ^ (3 - 1))
            * ((((zdistD 3 5 ((0 : Zd 3 5) - ![1, 1, 1]) : ℝ) + 1) ^ (3 - 1))⁻¹) ∧
      ‖KLf2 (fun s => Theta 3 5 (1 / 2) (((9 / 10 : ℝ)) : ℂ) 0 (![1, 1, 1] + s)) ![2, 1, 0]‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * ((1 / 2) ^ 2 + |1 - 9 / 10|)⁻¹
            * (((zdistD 3 5 (![2, 1, 0] : Zd 3 5) : ℝ) + 1) ^ 3)
            * ((((zdistD 3 5 ((0 : Zd 3 5) - ![1, 1, 1]) : ℝ) + 1) ^ 3)⁻¹) := by
  obtain ⟨C0, hC0, H0⟩ := KLf0_bound hPT
  obtain ⟨C1, hC1, H1⟩ := KLf12_bound (by norm_num) hPT 1 one_pos
  have h0 : ‖KLf0 (fun s => Theta 3 5 (1 / 2) (((9 / 10 : ℝ)) : ℂ) 0 (![1, 1, 1] + s))‖
      ≤ C0 * Bparam 3 5 (1 / 2) (9 / 10) 0 := H0 KLinstPar 0 ![1, 1, 1]
  have h1 := H1 KLinstPar 0 ![1, 1, 1] ![2, 1, 0]
  have h1a : ‖KLf1 (fun s => Theta 3 5 (1 / 2) (((9 / 10 : ℝ)) : ℂ) 0 (![1, 1, 1] + s)) ![2, 1, 0]‖
        ≤ C1 * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * ((1 / 2) ^ 2 + |1 - 9 / 10|)⁻¹
            * (((zdistD 3 5 (![2, 1, 0] : Zd 3 5) : ℝ) + 1) ^ (3 - 1))
            * ((((zdistD 3 5 ((0 : Zd 3 5) - ![1, 1, 1]) : ℝ) + 1) ^ (3 - 1))⁻¹) := h1.1
  have h1b : ‖KLf2 (fun s => Theta 3 5 (1 / 2) (((9 / 10 : ℝ)) : ℂ) 0 (![1, 1, 1] + s)) ![2, 1, 0]‖
        ≤ C1 * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * ((1 / 2) ^ 2 + |1 - 9 / 10|)⁻¹
            * (((zdistD 3 5 (![2, 1, 0] : Zd 3 5) : ℝ) + 1) ^ 3)
            * ((((zdistD 3 5 ((0 : Zd 3 5) - ![1, 1, 1]) : ℝ) + 1) ^ 3)⁻¹) := h1.2
  have hB : 0 ≤ Bparam 3 5 (1 / 2) (9 / 10) 0 := KLIndStepA_Bparam_nonneg _ _
  refine ⟨max C0 C1, lt_max_of_lt_left hC0, h0.trans ?_, h1a.trans ?_, h1b.trans ?_⟩
  · gcongr; exact le_max_left _ _
  · gcongr; exact le_max_right _ _
  · gcongr; exact le_max_right _ _

/-- Target 4, `KLSigmaPi_reflect`: the reflected label vector `2 - δ` differs from `δ`. -/
example :
    (fun i => (1 + 1 : Zd 3 5) - KLinsta i) ≠ KLinsta ∧
    KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLinstσ ∅ (fun i => (1 + 1 : Zd 3 5) - KLinsta i)
      = KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLinstσ ∅ KLinsta := by
  refine ⟨by decide, ?_⟩
  exact KLSigmaPi_reflect (κ := 1) (gmax := 1) one_pos KLinstPar KLinstσ (1 + 1) KLinsta

/-- Target 4, group (G1): the antisymmetric part integrates to zero on the slice `δ_0 = b`
(`σ = (+,-,+)`, leaf `i = 1`, `b = (1,1,1)`, `f = Θ_t(0, b + ·)`). -/
example :
    ∑ δ ∈ Finset.univ.filter (fun δ : Fin 3 → Zd 3 5 => δ 0 = ![1, 1, 1]),
        KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLinstσ ∅ δ
          * KLf1 (fun s => Theta 3 5 (1 / 2) (((9 / 10 : ℝ)) : ℂ) 0 (![1, 1, 1] + s))
              (δ 1 - ![1, 1, 1]) = 0 :=
  KLslice_f1_vanish (κ := 1) (gmax := 1) one_pos KLinstPar KLinstσ 0 1 ![1, 1, 1] _

/-- Target 5: the lattice sums at `d = 3`, `L = 5`, `a = (1,2,3)`, `a' = 0`. -/
example :
    (∑ b : Zd (1 + 2) 5, ((((zdistD (1 + 2) 5 (![1, 2, 3] - b) : ℕ) : ℝ) + 1) ^ 1)⁻¹
        ≤ Real.exp (√((1 : ℕ) + 2)) * (2 ^ (1 + 2) * radC 1 * ((5 : ℕ) : ℝ) ^ 2)) ∧
    (∑ b : Zd (1 + 2) 5, ((((zdistD (1 + 2) 5 (![1, 2, 3] - b) : ℕ) : ℝ) + 1) ^ (1 + 1))⁻¹
        ≤ 2 ^ (1 + 2) * ((((1 : ℕ) : ℝ) + 3) * ((5 : ℕ) : ℝ))) ∧
    (∑ b : Zd (1 + 2) 5, ((((zdistD (1 + 2) 5 (![1, 2, 3] - b) : ℕ) : ℝ) + 1) ^ (1 + 2))⁻¹
        ≤ 2 ^ (1 + 2) * (1 + Real.log ((((1 : ℕ) : ℝ) + 2) * ((5 : ℕ) : ℝ) + 1))) ∧
    (∑ b : Zd (1 + 2) 5, ((((zdistD (1 + 2) 5 (0 - b) : ℕ) : ℝ) + 1) ^ (1 + 1)
        * (((zdistD (1 + 2) 5 (![1, 2, 3] - b) : ℕ) : ℝ) + 1) ^ (1 + 1))⁻¹
        ≤ 2 ^ (2 * 1 + 6) * (1 + Real.log ((((1 : ℕ) : ℝ) + 2) * ((5 : ℕ) : ℝ) + 1))) :=
  ⟨KLlat_pow_sub_two 1 ![1, 2, 3], KLlat_pow_sub_one 1 ![1, 2, 3], KLlat_pow_dim 1 ![1, 2, 3],
    KLlat_pair 1 0 ![1, 2, 3]⟩

/-- Target 5, the pair sum in the form `C L^τ` (`d = 3`, `L = 5`, `τ = 1`). -/
example :
    ∑ b : Zd (1 + 2) 5, ((((zdistD (1 + 2) 5 (0 - b) : ℕ) : ℝ) + 1) ^ (1 + 1)
        * (((zdistD (1 + 2) 5 (![1, 2, 3] - b) : ℕ) : ℝ) + 1) ^ (1 + 1))⁻¹
      ≤ 2 ^ (2 * 1 + 6) * (1 + ((((1 : ℕ) : ℝ) + 2) + 1) ^ (1 : ℝ) / 1) * ((5 : ℕ) : ℝ) ^ (1 : ℝ) :=
  KLlat_pair_rpow 1 one_pos 0 ![1, 2, 3]

/-- Target 5, the forms `C (1 + log L)` (`d = 3`, `L = 5`). -/
example :
    (∑ b : Zd (1 + 2) 5, ((((zdistD (1 + 2) 5 (![1, 2, 3] - b) : ℕ) : ℝ) + 1) ^ (1 + 2))⁻¹
        ≤ 2 ^ (1 + 2) * ((1 + Real.log ((((1 : ℕ) : ℝ) + 2) + 1)) * (1 + Real.log ((5 : ℕ) : ℝ)))) ∧
    (∑ b : Zd (1 + 2) 5, ((((zdistD (1 + 2) 5 (0 - b) : ℕ) : ℝ) + 1) ^ (1 + 1)
        * (((zdistD (1 + 2) 5 (![1, 2, 3] - b) : ℕ) : ℝ) + 1) ^ (1 + 1))⁻¹
        ≤ 2 ^ (2 * 1 + 6) * ((1 + Real.log ((((1 : ℕ) : ℝ) + 2) + 1)) * (1 + Real.log ((5 : ℕ) : ℝ)))) :=
  ⟨KLlat_pow_dim_logL 1 ![1, 2, 3], KLlat_pair_logL 1 0 ![1, 2, 3]⟩

/-- Target 5, the `L^τ` form, and `(g² + |1-t|)⁻¹ ≤ B_{t,0}`, `(1-t) Σ_b |Θ_t(a,b)| ≤ 1`. -/
example :
    (∑ b : Zd (1 + 2) 5, ((((zdistD (1 + 2) 5 (![1, 2, 3] - b) : ℕ) : ℝ) + 1) ^ (1 + 2))⁻¹
        ≤ 2 ^ (1 + 2) * (1 + ((((1 : ℕ) : ℝ) + 2) + 1) ^ (1 : ℝ) / 1) * ((5 : ℕ) : ℝ) ^ (1 : ℝ)) ∧
    ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)⁻¹ ≤ Bparam 3 5 (1 / 2) (9 / 10) 0 ∧
    ∑ b : Zd 3 5, ‖Theta 3 5 (1 / 2) (((9 / 10 : ℝ)) : ℂ) 0 b‖ ≤ (1 - 9 / 10 : ℝ)⁻¹ :=
  ⟨KLlat_pow_dim_rpow 1 one_pos ![1, 2, 3], KLlat_inv_le_Bparam (d := 3) (L := 5) (g := 1 / 2) (9 / 10),
    KLlat_sum_norm_Theta_row_le (by norm_num) (by norm_num) (by norm_num) 0⟩

/-- Target 6, the weighted sum-zero estimate: `n = 4`, `σ = σ^{(alt)}`, root `r = 1`, `x = 0`,
`Q = 6`.  `KLShort 3 1 1` is `KLShort_holds`: no hypothesis is left.  Nondegeneracy: the signed sum
over the slice is `1/19` (the merged value at root `0`, moved to root `1` by
`KLIndStepA_sum_slice_root`), so the weighted absolute sum is at least `1/19 > 0`. -/
example :
    ∃ C : ℝ, 0 < C ∧
      ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 1 = 0),
          KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ δ‖ = 1 / 19 ∧
      ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 1 = 0),
          KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ δ‖ ≤ C * (1 - 9 / 10) ∧
      1 / 19 ≤ ∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 1 = 0),
          ‖KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ δ‖
            * ((KLmaxDist 3 5 δ : ℝ) + 1) ^ 6 ∧
      ∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 1 = 0),
          ‖KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ δ‖
            * ((KLmaxDist 3 5 δ : ℝ) + 1) ^ 6 ≤ C * ((1 / 2) ^ 2 + (1 - 9 / 10)) := by
  obtain ⟨C, hC, H⟩ := KLsumZero_weighted 4 (by norm_num) (by norm_num) one_pos one_pos
    (KLShort_holds 3 1 1 (by norm_num) one_pos one_pos) 6
  have hH := H KLinstPar (KLsigAlt 4) (by decide) 1 0
  have hroot : ∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 1 = 0),
      KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ δ = 1 / 19 :=
    (KLIndStepA_sum_slice_root
      (fun δ : Fin 4 → Zd 3 5 => KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ δ)
      (fun δ c => KLIndStepA_SigmaPi_add_const (κ := 1) (gmax := 1) one_pos KLinstPar
        (KLsigAlt 4) ∅ δ c) 1 0 0).trans KLMolecule_inst_signed_val
  have hnorm : ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 1 = 0),
      KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ δ‖ = 1 / 19 := by
    rw [hroot]; simp
  refine ⟨C, hC, hnorm, hH.1, ?_, hH.2⟩
  calc (1 / 19 : ℝ) = ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 1 = 0),
        KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ δ‖ := hnorm.symm
    _ ≤ ∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 1 = 0),
        ‖KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ δ‖ := norm_sum_le _ _
    _ ≤ _ := sum_le_sum fun δ _ => le_mul_of_one_le_right (norm_nonneg _)
          (one_le_pow₀ (by linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ KLmaxDist 3 5 δ)]))

/-- Target 6, the complement `¬σ^{(alt)}` (also alternating), root `r = 2`: the signed estimate. -/
example :
    ∃ C : ℝ, 0 < C ∧
      ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 2 = 0),
          KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (fun k => !KLsigAlt 4 k) ∅ δ‖
            ≤ C * (1 - 9 / 10) := by
  obtain ⟨C, hC, H⟩ := KLsumZero_weighted 4 (by norm_num) (by norm_num) one_pos one_pos
    (KLShort_holds 3 1 1 (by norm_num) one_pos one_pos) 0
  exact ⟨C, hC, (H KLinstPar (fun k => !KLsigAlt 4 k) (by decide) 2 0).1⟩

/-- Case (i) at `n = 4`: `σ = (+,+,+,-)`, root `r = 2` (long: `σ_2 ≠ σ_3`), short leaves `0`, `1`;
the pin-shaped statement, with `¬ alternating`. -/
example (hPT : KLPT 3 1 1) :
    ∃ C : ℝ, 0 < C ∧
      ∑ b : Zd 3 5, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 2 = b),
          KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) ![true, true, true, false] ∅ δ *
            ∏ i ∈ Finset.univ.erase (2 : Fin 4),
              thetaEdge 3 5 (1 / 2) (mSigma 0) (9 / 10) (![true, true, true, false] i)
                (![true, true, true, false] (i + 1)) (![0, 1, 2, 3] i) (δ i)‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 2) := by
  obtain ⟨C, hC, H⟩ := KLindStep_nonAlt 4 (by norm_num) (by norm_num) one_pos one_pos hPT 1 one_pos
  exact ⟨C, hC, H KLinstPar ![true, true, true, false] 2 (by decide) (by decide) ![0, 1, 2, 3]⟩

/-- The crude pointwise bounds (`KLf_crude_bound`) and the signed slice estimate
(`KLIndStepA_sumZero_signed`) at the instance. -/
example (hPT : KLPT 3 1 1) :
    (∃ C : ℝ, 0 < C ∧
      ‖KLf0 (fun s => Theta 3 5 (1 / 2) (((9 / 10 : ℝ)) : ℂ) 0 (![1, 1, 1] + s))‖
        ≤ C * Bparam 3 5 (1 / 2) (9 / 10) 0 ∧
      ‖KLf1 (fun s => Theta 3 5 (1 / 2) (((9 / 10 : ℝ)) : ℂ) 0 (![1, 1, 1] + s)) ![2, 1, 0]‖
        ≤ C * Bparam 3 5 (1 / 2) (9 / 10) 0 ∧
      ‖KLf2 (fun s => Theta 3 5 (1 / 2) (((9 / 10 : ℝ)) : ℂ) 0 (![1, 1, 1] + s)) ![2, 1, 0]‖
        ≤ C * Bparam 3 5 (1 / 2) (9 / 10) 0) ∧
    (∃ C : ℝ, 0 < C ∧
      ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 3 = 0),
          KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (fun k => !KLsigAlt 4 k) ∅ δ‖
            ≤ C * (1 - 9 / 10)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨C, hC, H⟩ := KLf_crude_bound hPT
    exact ⟨C, hC, H KLinstPar 0 ![1, 1, 1] ![2, 1, 0]⟩
  · obtain ⟨C, hC, H⟩ := KLIndStepA_sumZero_signed 4 (by norm_num) (by norm_num) one_pos one_pos
      (KLShort_holds 3 1 1 (by norm_num) one_pos one_pos)
    exact ⟨C, hC, H KLinstPar (fun k => !KLsigAlt 4 k) (by decide) 3 0⟩

/-- The helper lemmas at the instance: `σ^{(alt)}` at `n = 4` is alternating and `n` is even
(`KLIndStepA_alt_cases`); the complement has `Q(¬σ, ∅) = conj Q(σ, ∅)`; a long edge is `Θ_t`;
`log(dL+1)` is `≤ C L^τ`. -/
example :
    (Even 4 ∧ (KLsigAlt 4 = KLsigAlt 4 ∨ KLsigAlt 4 = fun k => !KLsigAlt 4 k)) ∧
    Qlayer (mSigma 0) (9 / 10) (fun k => !KLsigAlt 4 k) ∅
      = (starRingEnd ℂ) (Qlayer (mSigma 0) (9 / 10) (KLsigAlt 4) ∅) ∧
    thetaEdge 3 5 (1 / 2) (mSigma 0) (9 / 10) true false = Theta 3 5 (1 / 2) (((9 / 10 : ℝ)) : ℂ) ∧
    1 + Real.log (((3 : ℕ) : ℝ) * ((5 : ℕ) : ℝ) + 1)
      ≤ (1 + (((3 : ℕ) : ℝ) + 1) ^ (1 : ℝ) / 1) * ((5 : ℕ) : ℝ) ^ (1 : ℝ) :=
  ⟨KLIndStepA_alt_cases (KLsigAlt 4) (by decide), KLIndStepA_Qlayer_not 0 (9 / 10) (KLsigAlt 4),
    KLIndStepA_thetaEdge_long (by norm_num) (9 / 10) (by decide), KLlat_log_le (L := 5) 3 (by norm_num) one_pos⟩

/-- T2365, the three band bundles (`indStepTH_band`, `sigDecayAbs_band`, `sigSumZeroAbs_band`) at the §7
data (`KLinstPar`, `n = 4`, `σ = σ^{(alt)}`, `a = (0, 1, 2, 3)`): translation and the row sum of a long
edge (`IndStepTH`), the decay (`SigDecayAbs`), the reflection and the `Q = 2(d-1) = 4` estimates on the
slice `δ_1 = 0` (`SigSumZeroAbs`).  `KLPT 3 1 1` is the only hypothesis left. -/
example (hPT : KLPT 3 1 1) :
    thetaEdge 3 5 (1 / 2) (mSigma 0) (9 / 10) true false (1 : Zd 3 5) 2
        = thetaEdge 3 5 (1 / 2) (mSigma 0) (9 / 10) true false 0 (2 - 1) ∧
    ∑ b : Zd 3 5, ‖thetaEdge 3 5 (1 / 2) (mSigma 0) (9 / 10) true false 0 b‖ ≤ (1 - 9 / 10 : ℝ)⁻¹ ∧
    (∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ‖KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ (![0, 1, 2, 3] : Fin 4 → Zd 3 5)‖
        ≤ C * Real.exp (-(c * (KLmaxDist 3 5 (![0, 1, 2, 3] : Fin 4 → Zd 3 5) : ℝ)))) ∧
    KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅
        (fun j => (1 + 1 : Zd 3 5) - (![0, 1, 2, 3] : Fin 4 → Zd 3 5) j)
      = KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ (![0, 1, 2, 3] : Fin 4 → Zd 3 5) ∧
    (∃ C : ℝ, 0 < C ∧
      ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 1 = 0),
          KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ δ‖ ≤ C * (1 - 9 / 10) ∧
      ∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 1 = 0),
          ‖KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ δ‖
            * ((KLmaxDist 3 5 δ : ℝ) + 1) ^ 4 ≤ C * ((1 / 2) ^ 2 + (1 - 9 / 10))) := by
  have hTH := indStepTH_band (d := 3) (κ := 1) (gmax := 1) one_pos hPT
  have hD := sigDecayAbs_band (d := 3) (κ := 1) (gmax := 1) 4 (by norm_num) (by norm_num) one_pos one_pos
  have hS := sigSumZeroAbs_band (d := 3) (κ := 1) (gmax := 1) 4 (by norm_num) (by norm_num)
    one_pos one_pos
  obtain ⟨C, hC, c, hc, HD⟩ := hD
  obtain ⟨C', hC', HS⟩ := hS.2.2 4 (by norm_num)
  exact ⟨hTH.transl KLinstPar true false 1 2, hTH.rowSum KLinstPar true false (by decide) 0,
    ⟨C, hC, c, hc, HD KLinstPar (KLsigAlt 4) ![0, 1, 2, 3]⟩,
    hS.1 KLinstPar (KLsigAlt 4) (by decide) (1 + 1) ![0, 1, 2, 3],
    ⟨C', hC', HS KLinstPar (KLsigAlt 4) (by decide) 1 0⟩⟩

end Instances


end RBM.Loop
