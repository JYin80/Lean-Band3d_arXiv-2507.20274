/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.AuxCarrier
import RBM3D.Green.EntryDom
import RBM3D.Green.LDE
import RBM3D.Loop.KLSumZero

/-!
# The deterministic entry layer of the GUE phase at the mixture profile, `d ≥ 3` (T2278, UN-30)

Port of `RBM2D/Universality/GUEPhase/EntryDet.lean` at `c9a24cf` (1362 lines; lines `1-891`
ported, the instance section `893-1337` rewritten at `d = 3`) to `d ≥ 3`.  The mixture profile is
`S_u = a S(g) + b N⁻¹` (`Smix d L W g a b`, merged in `AuxCarrier.lean`), `S' = S_u / u`,
`u = a + b`, `N = (W L)^d`.  Paper: Lemma 4.1 (4.2), (4.3) of [YY_25] at the GUE-phase profile, as
used in the GUE phase of Thm 2.4 (`paper/tex/1_2_Intro_model_result.tex:566-570`); `lem_GbEXP`
(`paper/tex/3_5_Loop_Hierarchy.tex:14`) says that the proof follows Lemma 4.1 of [YY_25] and is
dimension-independent.

* §4 stability of `1 - u m² S'` (`stable_mix`), constant `Kstab3 d Λ κ (1 + 1 / gapK κ)`, `L`-free
  (RBM2D: `Kstab2 κ L ∝ 1 + log L`).
* §5 the profile `Snorm = Smix / (a + b)` and the deterministic core of Lemma 4.1 (4.2), (4.3)
  at the mixture profile (`mix_offdiag_det`, `mix_diag_det`), the merged `EntryCore` unchanged.
* §5b the `J`-part: Ward in column form (`ward_col`) and `Im m / (2 N η) ≤ maxLoopPM`
  (`inv_N_le_maxLoopPM`).
* §5c Ward in row form, `im_diag_le` and the two-sided sum `sum_Snorm_le`.
* §5d the constants (`mixC`, `mixK`, `mixDelta`, `mixCdet`) and the deterministic bound `mix_det`.
* §8 compiled instances at `d = 3`, `L = 3`, `W = 2` (`EntryDetCheck`).

Class T of T2173: the band instance (`0 < g ≤ Λ`, `m = mE E`) is here; the BA form (`g = 0`,
matrix `m`) is BA-C3.  Private copies of merged private lemmas: `EntryDet_stable_relabel`
(`Green/Stability.lean:50`), `EntryDet_greenBlk_true_eq` (`Green/EntryDom.lean:265`),
`EntryDet_gapK_pos` (`Loop/KLSumZero.lean:426`); the wrapper `EntryDet_gapK_le_norm` is the merged
`RBM.Loop.gapK_le_norm` at `s = true`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace RBM.Univ

open MeasureTheory ProbabilityTheory Filter Matrix
open RBM.Gauss
open scoped NNReal ENNReal

/-! ## §4 Stability of `1 - ξ S'` -/

section Stab

open RBM.Green

private theorem EntryDet_gapK_pos {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) : 0 < RBM.Loop.gapK κ := by
  unfold RBM.Loop.gapK
  refine lt_min one_pos (Real.sqrt_pos.2 ?_)
  nlinarith

/-- The bulk gap `c_κ ≤ |1 - t m²|`: the merged `RBM.Loop.gapK_le_norm` at `s = true`
(`mSigma E true = mE E`); RBM2D `gapK_le_norm'` (`EntryDet.lean:69`) with `spectralM ↦ mE`. -/
private theorem EntryDet_gapK_le_norm {κ E t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) :
    RBM.Loop.gapK κ ≤ ‖1 - (t : ℂ) * mE E ^ 2‖ := by
  have h := RBM.Loop.gapK_le_norm hκ hE ht0 true
  have e : mSigma E true = mE E := by simp [mSigma]
  rw [e, ← pow_two] at h
  exact h

/-- `Stable` is invariant under relabelling the index set (copy of the private `stability_relabel`,
`Green/Stability.lean:50`; RBM2D `stable_relabel`, `Green/EntryBlock.lean:226`). -/
private theorem EntryDet_stable_relabel {n n' : Type*} [Fintype n] [Fintype n'] (e : n ≃ n')
    {S : n → n → ℝ} {ξ : ℂ} {K : ℝ} (h : Stable S ξ K) :
    Stable (fun i j => S (e.symm i) (e.symm j)) ξ K := by
  intro v B hB i
  have h1 := h (fun k => v (e k)) B (fun j => by
    have h2 := hB (e j)
    have h3 : ∑ k', (S (e.symm (e j)) (e.symm k') : ℂ) * v k' = ∑ k, (S j k : ℂ) * v (e k) := by
      rw [← Equiv.sum_comp e]
      simp
    rw [h3] at h2
    simpa using h2) (e.symm i)
  simpa using h1

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- **Stability of `1 - u m² S'`, `S' = S_u / u = (a S(g) + b N⁻¹) / (a + b)`**, uniformly in
`a, b ≥ 0`, `0 < a + b < 1`, `|E| ≤ 2 - κ`, `0 < g ≤ Λ`: the `J`-part is removed by averaging
(`|1 - u m²| ≥ c_κ`) and the band part is the merged `stable_svar_bulk` at `t = a`.  The constant is
the `L`-free `Kstab3 d Λ κ (1 + 1 / gapK κ)` (RBM2D `:102`: `Kstab2 κ L`). -/
theorem stable_mix (hd : 3 ≤ d) (hL : 3 ≤ L) {g Λ κ E a b : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ)
    (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < a + b) (hu1 : a + b < 1) :
    Stable (fun x y : Idx d L W => Smix d L W g a b x y / (a + b)) (((a + b : ℝ) : ℂ) * mE E ^ 2)
      (Kstab3 d Λ κ * (1 + 1 / RBM.Loop.gapK κ)) := by
  intro v B hB i
  set m := mE E with hm
  set u : ℝ := a + b with hudef
  set N : ℝ := (((W * L) ^ d : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := by
    have : 0 < W * L := Nat.mul_pos (NeZero.pos W) (NeZero.pos L)
    rw [hNdef]; positivity
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : |E| ≤ 2 := by linarith
  have hgap0 := EntryDet_gapK_pos hκ hκ2
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB i)
  have hm1 : ‖m‖ = 1 := norm_mE hE2
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  set V : ℂ := ∑ k, v k with hV
  have hgapn : RBM.Loop.gapK κ ≤ ‖1 - (u : ℂ) * m ^ 2‖ := EntryDet_gapK_le_norm hκ hE hu.le
  have hcard : (Fintype.card (Idx d L W) : ℝ) = N := by
    rw [hNdef, card_Idx]
  -- the key identity
  have hkey : ∀ j, (u : ℂ) * m ^ 2 * ∑ k, ((Smix d L W g a b j k / u : ℝ) : ℂ) * v k
      = (a : ℂ) * m ^ 2 * ∑ k, (svarF d L W g j k : ℂ) * v k + (b : ℂ) * m ^ 2 * (V / N) := by
    intro j
    have : ∀ k, (u : ℂ) * (((Smix d L W g a b j k / u : ℝ) : ℂ) * v k)
        = (a : ℂ) * ((svarF d L W g j k : ℂ) * v k) + (b : ℂ) * (v k / N) := by
      intro k
      simp only [Smix, ← hNdef]
      push_cast
      field_simp
    calc (u : ℂ) * m ^ 2 * ∑ k, ((Smix d L W g a b j k / u : ℝ) : ℂ) * v k
        = m ^ 2 * ∑ k, (u : ℂ) * (((Smix d L W g a b j k / u : ℝ) : ℂ) * v k) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = m ^ 2 * ∑ k, ((a : ℂ) * ((svarF d L W g j k : ℂ) * v k) + (b : ℂ) * (v k / N)) := by
          simp only [this]
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_div, hV]
          ring
  set r : Idx d L W → ℂ := fun j =>
    v j - (u : ℂ) * m ^ 2 * ∑ k, ((Smix d L W g a b j k / u : ℝ) : ℂ) * v k with hr
  have hrB : ∀ j, ‖r j‖ ≤ B := hB
  have hSV : ∑ j, ∑ k, (svarF d L W g j k : ℂ) * v k = V := by
    rw [Finset.sum_comm, hV]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_mul]
    have : ∑ j, (svarF d L W g j k : ℂ) = 1 := by
      have h := Green.IBP_sum_svarF_row (W := W) g hL k
      simp_rw [svarF_comm d L W g _ k]
      exact_mod_cast h
    rw [this, one_mul]
  have hsumr : ∑ j, r j = (1 - (u : ℂ) * m ^ 2) * V := by
    simp only [hr, hkey, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hSV,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hV]
    have hc : ((Fintype.card (Idx d L W) : ℕ) : ℂ) = (N : ℂ) := by exact_mod_cast hcard
    rw [hc, hudef]
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
    push_cast
    field_simp
  have hnorm_sumr : ‖∑ j, r j‖ ≤ N * B := by
    calc ‖∑ j, r j‖ ≤ ∑ j, ‖r j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Idx d L W, B := Finset.sum_le_sum fun j _ => hrB j
      _ = N * B := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  have hVle : ‖V‖ ≤ N * B / RBM.Loop.gapK κ := by
    rw [le_div_iff₀ hgap0]
    calc ‖V‖ * RBM.Loop.gapK κ ≤ ‖V‖ * ‖1 - (u : ℂ) * m ^ 2‖ :=
          mul_le_mul_of_nonneg_left hgapn (norm_nonneg _)
      _ = ‖∑ j, r j‖ := by rw [hsumr, norm_mul, mul_comm]
      _ ≤ N * B := hnorm_sumr
  have hr' : ∀ j, ‖v j - (a : ℂ) * m ^ 2 * ∑ k, (svarF d L W g j k : ℂ) * v k‖
      ≤ B + B / RBM.Loop.gapK κ := by
    intro j
    have hj : v j - (a : ℂ) * m ^ 2 * ∑ k, (svarF d L W g j k : ℂ) * v k
        = r j + (b : ℂ) * m ^ 2 * (V / N) := by
      simp only [hr, hkey]; ring
    rw [hj]
    have hbn : ‖(b : ℂ) * m ^ 2 * (V / N)‖ = b * (‖V‖ / N) := by
      rw [norm_mul, norm_mul, norm_pow, hm1, one_pow, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hb, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hNpos]
    have hVN : ‖V‖ / N ≤ B / RBM.Loop.gapK κ := by
      rw [div_le_iff₀ hNpos]
      calc ‖V‖ ≤ N * B / RBM.Loop.gapK κ := hVle
        _ = B / RBM.Loop.gapK κ * N := by ring
    calc ‖r j + (b : ℂ) * m ^ 2 * (V / N)‖ ≤ ‖r j‖ + ‖(b : ℂ) * m ^ 2 * (V / N)‖ := norm_add_le _ _
      _ ≤ B + b * (B / RBM.Loop.gapK κ) := by
          rw [hbn]
          exact add_le_add (hrB j) (mul_le_mul_of_nonneg_left hVN hb)
      _ ≤ B + B / RBM.Loop.gapK κ := by
          have hb1 : b ≤ 1 := by linarith
          have h0 : 0 ≤ B / RBM.Loop.gapK κ := div_nonneg hB0 hgap0.le
          nlinarith
  have ha1 : a < 1 := by linarith
  have hst := stable_svar_bulk (W := W) hd hL hg hgΛ hκ hE ha ha1 v (B + B / RBM.Loop.gapK κ) hr' i
  calc ‖v i‖ ≤ Kstab3 d Λ κ * (B + B / RBM.Loop.gapK κ) := hst
    _ = Kstab3 d Λ κ * (1 + 1 / RBM.Loop.gapK κ) * B := by ring

end Stab


/-! ## §5 The deterministic core of Lemma 4.1 at the mixture profile (merged `EntryCore`, unchanged) -/

section Core

open RBM.Green

/-- The normalised profile `S' = S_u / u`, `S_u = a S(g) + b N⁻¹`, `u = a + b` (the profile of the
GUE phase at time `u`, and `S̃` for `b = ζ`, `a = 1 - ζ`). -/
def Snorm (d L W : ℕ) [NeZero L] [NeZero W] (g a b : ℝ) (x y : Idx d L W) : ℝ :=
  Smix d L W g a b x y / (a + b)

variable {d L W : ℕ} [NeZero L] [NeZero W]

theorem Snorm_nonneg {g a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (x y : Idx d L W) :
    0 ≤ Snorm d L W g a b x y :=
  div_nonneg (Smix_nonneg d L W g ha hb x y) (add_nonneg ha hb)

theorem sum_Snorm_row (hL : 3 ≤ L) {g a b : ℝ} (hu : 0 < a + b) (x : Idx d L W) :
    ∑ y, Snorm d L W g a b x y = 1 := by
  unfold Snorm
  rw [← Finset.sum_div, show ∑ y, Smix d L W g a b x y = a + b from sum_Smix_row d L W hL g a b x,
    div_self hu.ne']

theorem sum_Snorm_col (hL : 3 ≤ L) {g a b : ℝ} (hu : 0 < a + b) (y : Idx d L W) :
    ∑ x, Snorm d L W g a b x y = 1 := by
  unfold Snorm
  rw [← Finset.sum_div, sum_Smix_col d L W hL g a b y, div_self hu.ne']

theorem Snorm_symm (g a b : ℝ) (x y : Idx d L W) :
    Snorm d L W g a b x y = Snorm d L W g a b y x := by
  unfold Snorm; rw [Smix_symm]

/-- The entry bound `S^{(B)}(g)_{xy} W^{-d} ≤ W^{-d}` (`S^{(B)}(g) ≤ 1`: the kernel is non-negative and
sums to `1`; RBM2D `svar_le`, `EntryDet.lean:234`, had the constant `1/5`): the merged `svar_le_inv_Wd`
read on the fine lattice through `svarF_eq_svar`. -/
theorem svarF_le (g : ℝ) (hL : 3 ≤ L) (x y : Idx d L W) :
    svarF d L W g x y ≤ ((W : ℝ) ^ d)⁻¹ := by
  rw [svarF_eq_svar]
  exact svar_le_inv_Wd g hL _ _

/-- The entry bound `S'_{xy} ≤ W^{-d}` (`N⁻¹ ≤ W^{-d}`, `S ≤ W^{-d}`): the hypothesis `S_xy ≤ C W^{-d}`
of the profile-generic part. -/
theorem Snorm_le (hL : 3 ≤ L) {g a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < a + b)
    (x y : Idx d L W) : Snorm d L W g a b x y ≤ ((W : ℝ) ^ d)⁻¹ := by
  have hW : (0 : ℝ) < W := Nat.cast_pos.2 (NeZero.pos W)
  have hN : (W : ℝ) ^ d ≤ (((W * L) ^ d : ℕ) : ℝ) := by
    have : W ≤ W * L := Nat.le_mul_of_pos_right W (by omega)
    have h2 : W ^ d ≤ (W * L) ^ d := Nat.pow_le_pow_left this d
    exact_mod_cast h2
  have h1 : 1 / (((W * L) ^ d : ℕ) : ℝ) ≤ ((W : ℝ) ^ d)⁻¹ := by
    rw [← one_div]
    exact one_div_le_one_div_of_le (by positivity) hN
  have h2 : svarF d L W g x y ≤ ((W : ℝ) ^ d)⁻¹ := svarF_le g hL x y
  unfold Snorm Smix
  rw [div_le_iff₀ hu]
  have h3 : b / (((W * L) ^ d : ℕ) : ℝ) ≤ b * ((W : ℝ) ^ d)⁻¹ := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left h1 hb
  nlinarith [mul_le_mul_of_nonneg_left h2 ha]

/-- **Extreme input `ζ = 0`**: `b = 0` gives the band profile `S(g)`. -/
theorem Snorm_zero_right {g a : ℝ} (ha : 0 < a) (x y : Idx d L W) :
    Snorm d L W g a 0 x y = svarF d L W g x y := by
  unfold Snorm Smix
  simp only [zero_div, add_zero]
  field_simp

/-- **Extreme input `ζ = 1`**: `a = 0` gives the flat profile `N⁻¹ J`. -/
theorem Snorm_zero_left (g : ℝ) {b : ℝ} (hb : 0 < b) (x y : Idx d L W) :
    Snorm d L W g 0 b x y = 1 / (((W * L) ^ d : ℕ) : ℝ) := by
  unfold Snorm Smix
  simp only [zero_mul, zero_add]
  field_simp

/-- **Lemma 4.1 (4.2), deterministic part, at the mixture profile**: the merged profile-generic
`norm_sq_green_offdiag_le` applies verbatim to `S' = Snorm g a b`.  The hypotheses left are the
three large-deviation inputs `LDERow`, `LDECol` (probabilistic) and the two `Λ`-bounds (`hΛ1`, `hΛ2`;
the Ward/`J`-part lemma).  No `g`-restriction (RBM2D `:278`). -/
theorem mix_offdiag_det (hL : 3 ≤ L) {g a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < a + b)
    {H G : Matrix (Idx d L W) (Idx d L W) ℂ} {z m : ℂ} {δ Φ Λ : ℝ}
    (hGM : G * (H - z • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)) = 1)
    (hMG : (H - z • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)) * G = 1) (hm : ‖m‖ = 1)
    (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (hΦ1 : 1 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (hLrow : LDERow H G (Snorm d L W g a b) Φ) (hLcol : LDECol H G (Snorm d L W g a b) Φ)
    (hΛ1 : ∀ i j, ∑ k, ∑ l, Snorm d L W g a b i k * ‖G k l‖ ^ 2 * Snorm d L W g a b l j ≤ Λ)
    (hΛ2 : ∀ i j, Snorm d L W g a b i j ≤ Λ) {i j : Idx d L W} (hij : i ≠ j) :
    ‖G i j‖ ^ 2 ≤ 162 * Φ ^ 2 * Λ :=
  norm_sq_green_offdiag_le hGM hMG hm hΩ hδ (Snorm_nonneg ha hb)
    (fun i => (sum_Snorm_row hL hu i).le) (fun j => (sum_Snorm_col hL hu j).le) hΦ1 hΦδ hLrow
    hLcol hΛ1 hΛ2 hij

/-- **Lemma 4.1 (4.3), deterministic part, at the mixture profile**: `norm_sq_green_diag_sub_le` at
`S' = Snorm g a b`, `t = u = a + b`, `z = z_u^{(E)}`, `m = m^{(E)}`, with the stability input
`stable_mix` (§4) and `mE_mul_add_zt` (`m (u m + z_u) = -1`).  The loop bound is `Λ'`, the coupling
bound is `Λ` (`0 < g ≤ Λ`, `3 ≤ d`: only through `stable_mix`). -/
theorem mix_diag_det (hd : 3 ≤ d) (hL : 3 ≤ L) {g Λ κ E a b : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ)
    (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < a + b) (hu1 : a + b < 1)
    {H G : Matrix (Idx d L W) (Idx d L W) ℂ} {δ Φ Λ' : ℝ}
    (hGM : G * (H - zt E (a + b) • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)) = 1)
    (hMG : (H - zt E (a + b) • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)) * G = 1)
    (hΩ : GoodEvent G (mE E) δ) (hδ : δ ≤ 1 / 2) (hΦ1 : 1 ≤ Φ)
    (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (hLrow : LDERow H G (Snorm d L W g a b) Φ) (hLcol : LDECol H G (Snorm d L W g a b) Φ)
    (hLquad : LDEQuad H G (Snorm d L W g a b) (a + b) Φ)
    (hLdiag : ∀ i, ‖H i i‖ ^ 2 ≤ Φ * Snorm d L W g a b i i)
    (hΛ1 : ∀ i j, ∑ k, ∑ l, Snorm d L W g a b i k * ‖G k l‖ ^ 2 * Snorm d L W g a b l j ≤ Λ')
    (hΛ2 : ∀ i j, Snorm d L W g a b i j ≤ Λ')
    (hKδ : (Kstab3 d Λ κ * (1 + 1 / RBM.Loop.gapK κ)) * δ ≤ 1 / 2) (i : Idx d L W) :
    ‖G i i - mE E‖ ^ 2 ≤ 2160 * (Kstab3 d Λ κ * (1 + 1 / RBM.Loop.gapK κ)) ^ 2 * Φ ^ 2 * Λ' := by
  have hE2 : |E| ≤ 2 := by linarith [abs_nonneg E]
  exact norm_sq_green_diag_sub_le hGM hMG (norm_mE hE2) (mE_mul_add_zt hE2 (a + b))
    (add_nonneg ha hb) hu1.le hΩ hδ (Snorm_nonneg ha hb) (fun i => sum_Snorm_row hL hu i)
    (fun j => (sum_Snorm_col hL hu j).le) hΦ1 hΦδ hLrow hLcol hLquad hLdiag hΛ1 hΛ2 hKδ
    (stable_mix hd hL hg hgΛ hκ hE ha hb hu hu1 (W := W))
    i

end Core

/-! ## §5b The `J`-part lemma: `(N η)⁻¹ Im m ≲ max |𝓛|`, `N = (W L)^d`

The only new deterministic input of the mixture profile beyond the band: the flat part `b N⁻¹` of the
profile is controlled through the Ward identity, since `∑_{a,b} |𝓛_{(+,-),(a,b)}| = W^{-2d}
∑_{x,y} |G_{xy}|²` (merged `norm_loopPM_eq`) and `∑_x |G_{xy}|² = Im G_{yy} / η`. -/

section JPart

open RBM.Green RBM.Path

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `greenBlk … true` is the resolvent of `blockMat M` at `z_u^{(E)}` (copy of the private
`entryDom_greenBlk_true_eq`, `Green/EntryDom.lean:265`; RBM2D `simp [greenBlk]`). -/
private theorem EntryDet_greenBlk_true_eq (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) :
    greenBlk d L W E u M true = green (blockMat d L W M) (zt E u) := by
  simp only [greenBlk, Gres, green, ite_true]
  exact (Matrix.nonsing_inv_eq_ringInverse _).symm

/-- **Ward, column form**: `∑_x |G_{xi}|² = Im G_{ii} / Im z` (RBM1D `gueEntry_ward_col`,
`GUEPhaseEntry.lean:709`, from the merged `im_green_diag`; any index type). -/
theorem ward_col {ν : Type*} [Fintype ν] [DecidableEq ν] {H : Matrix ν ν ℂ} (hH : H.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (i : ν) :
    ∑ x, ‖green H z x i‖ ^ 2 = (green H z i i).im / z.im := by
  have h := im_green_diag hH hz i
  have hdot : (star (green H z *ᵥ Pi.single i 1) ⬝ᵥ (green H z *ᵥ Pi.single i 1)).re
      = ∑ x, ‖green H z x i‖ ^ 2 := by
    have hv : ∀ x, (green H z *ᵥ Pi.single i 1) x = green H z x i := by
      intro x; simp
    simp only [dotProduct, Pi.star_apply, hv]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [RCLike.star_def, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [Complex.mul_re]
  rw [hdot] at h
  rw [h]
  field_simp

/-- **The lower bound `m / (2 N η) ≤ max_{a,b} |𝓛_{(+,-),(a,b)}|`** on the good event
`‖G - m‖_max ≤ δ ≤ Im m / 2`, `N = (W L)^d`, `η = Im z_u^{(E)}`: Ward over one block column
(RBM2D `:354`; `Z2 L ↦ Zd d L`, fibre `Fin (W^d)`, `L^d` columns). -/
theorem inv_N_le_maxLoopPM {E u : ℝ} {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian)
    (hz : 0 < (zt E u).im) {m : ℂ} {δ : ℝ}
    (hΩ : GoodEvent (greenBlk d L W E u M true) m δ) (hδ : δ ≤ m.im / 2) :
    m.im / (2 * ((((W * L) ^ d : ℕ) : ℝ) * (zt E u).im)) ≤ maxLoopPM d L W E u M := by
  set z := zt E u with hzdef
  have hW : (0 : ℝ) < W := Nat.cast_pos.2 (NeZero.pos W)
  have hL0 : (0 : ℝ) < L := Nat.cast_pos.2 (NeZero.pos L)
  have hH : (blockMat d L W M).IsHermitian := hM.submatrix _
  have hG : greenBlk d L W E u M true = green (blockMat d L W M) z :=
    EntryDet_greenBlk_true_eq E u M
  have hdiag : ∀ x, m.im / 2 ≤ (greenBlk d L W E u M true x x).im := by
    intro x
    have h1 := hΩ.norm_diag_sub_le x
    have h2 : |((greenBlk d L W E u M true) x x - m).im| ≤ ‖(greenBlk d L W E u M true) x x - m‖ :=
      Complex.abs_im_le_norm _
    rw [Complex.sub_im] at h2
    have := neg_abs_le ((greenBlk d L W E u M true x x).im - m.im)
    linarith
  set a0 : Zd d L := 0 with ha0
  have hsum : ∑ b : Zd d L, ‖loopPM d L W E u M a0 b‖
      = (((W : ℝ)⁻¹ ^ d) ^ 2) * ∑ α : Fin (W ^ d),
          (greenBlk d L W E u M true (a0, α) (a0, α)).im / z.im := by
    simp only [norm_loopPM_eq M hM a0, ← Finset.mul_sum]
    congr 1
    calc ∑ b : Zd d L, ∑ β : Fin (W ^ d), ∑ α : Fin (W ^ d),
          ‖greenBlk d L W E u M true (b, β) (a0, α)‖ ^ 2
        = ∑ b : Zd d L, ∑ α : Fin (W ^ d), ∑ β : Fin (W ^ d),
          ‖greenBlk d L W E u M true (b, β) (a0, α)‖ ^ 2 :=
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ α : Fin (W ^ d), ∑ b : Zd d L, ∑ β : Fin (W ^ d),
          ‖greenBlk d L W E u M true (b, β) (a0, α)‖ ^ 2 := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [hG, ← ward_col hH hz.ne' (a0, α)]
          exact (Fintype.sum_prod_type (α₁ := Zd d L) (α₂ := Fin (W ^ d))
            (fun x : Vtx d L W => ‖green (blockMat d L W M) z x (a0, α)‖ ^ 2)).symm
  have hlow : (W : ℝ) ^ d * (m.im / 2 / z.im)
      ≤ ∑ α : Fin (W ^ d), (greenBlk d L W E u M true (a0, α) (a0, α)).im / z.im := by
    calc (W : ℝ) ^ d * (m.im / 2 / z.im) = ∑ _α : Fin (W ^ d), m.im / 2 / z.im := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
      _ ≤ _ := Finset.sum_le_sum fun α _ => div_le_div_of_nonneg_right (hdiag _) hz.le
  have hup : ∑ b : Zd d L, ‖loopPM d L W E u M a0 b‖ ≤ (L : ℝ) ^ d * maxLoopPM d L W E u M := by
    calc ∑ b : Zd d L, ‖loopPM d L W E u M a0 b‖ ≤ ∑ _b : Zd d L, maxLoopPM d L W E u M :=
          Finset.sum_le_sum fun b _ =>
            Finset.le_sup' (fun p : Zd d L × Zd d L => ‖loopPM d L W E u M p.1 p.2‖)
              (Finset.mem_univ (a0, b))
      _ = (L : ℝ) ^ d * maxLoopPM d L W E u M := by
          rw [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
          push_cast; ring
  have key : ((W : ℝ)⁻¹ ^ d) ^ 2 * ((W : ℝ) ^ d * (m.im / 2 / z.im)) ≤
      (L : ℝ) ^ d * maxLoopPM d L W E u M :=
    calc ((W : ℝ)⁻¹ ^ d) ^ 2 * ((W : ℝ) ^ d * (m.im / 2 / z.im))
        ≤ ((W : ℝ)⁻¹ ^ d) ^ 2 * ∑ α : Fin (W ^ d),
            (greenBlk d L W E u M true (a0, α) (a0, α)).im / z.im :=
          mul_le_mul_of_nonneg_left hlow (by positivity)
      _ = ∑ b : Zd d L, ‖loopPM d L W E u M a0 b‖ := hsum.symm
      _ ≤ _ := hup
  have hN : (((W * L) ^ d : ℕ) : ℝ) = (W : ℝ) ^ d * (L : ℝ) ^ d := by push_cast; ring
  rw [hN]
  have e : m.im / (2 * ((W : ℝ) ^ d * (L : ℝ) ^ d * z.im))
      = (1 / (L : ℝ) ^ d) * (((W : ℝ)⁻¹ ^ d) ^ 2 * ((W : ℝ) ^ d * (m.im / 2 / z.im))) := by
    rw [inv_pow]
    field_simp
  rw [e, one_div, inv_mul_le_iff₀ (by positivity)]
  exact key

end JPart

/-! ## §5c Ward in row form, the diagonal bound, and the two-sided sum bound at the mixture profile

Port of RBM1D `gueEntry_ward_row`, `gueEntry_green_transpose` (`GUEPhaseEntry.lean:724-756`),
`gueEntry_im_diag_le` (`:907-914`) and `gueEntry_sum_prof_le` (`:962-1045`). -/

section Ward

open RBM.Green RBM.Path

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

/-- `(green H z)ᵀ = green Hᵀ z` (RBM1D `gueEntry_green_transpose`, `GUEPhaseEntry.lean:724-729`; no
change: any index type). -/
theorem green_transpose {H : Matrix ν ν ℂ} (z : ℂ) : (green H z)ᵀ = green Hᵀ z := by
  unfold green
  rw [Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one]

/-- **Ward, row form**: `∑_l |G_{kl}|² = Im G_{kk} / Im z` (RBM1D `gueEntry_ward_row`,
`GUEPhaseEntry.lean:731-748`; no change: any index type). -/
theorem ward_row {H : Matrix ν ν ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (k : ν) :
    ∑ l, ‖green H z k l‖ ^ 2 = (green H z k k).im / z.im := by
  have hHt : (Hᵀ).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose, Matrix.transpose_transpose]
    have := hH.eq
    rw [Matrix.conjTranspose] at this
    ext a b
    have h2 := congrArg (fun M => M b a) this
    simp only [Matrix.map_apply, Matrix.transpose_apply] at h2 ⊢
    exact h2
  have h := ward_col hHt hz k
  have ht : ∀ a b, green Hᵀ z a b = green H z b a := by
    intro a b
    rw [← green_transpose]; rfl
  simp only [ht] at h
  exact h

set_option linter.unusedFintypeInType false in
/-- On the good event, `Im G_{xx} ≤ 3/2` (RBM1D `gueEntry_im_diag_le`, `GUEPhaseEntry.lean:907-914`,
for an arbitrary matrix `G` instead of `green H z`; the statement keeps `[Fintype ν]` as pinned). -/
theorem im_diag_le {G : Matrix ν ν ℂ} {m : ℂ} (hm : ‖m‖ = 1) {δ : ℝ} (hΩ : GoodEvent G m δ)
    (hδ : δ ≤ 1 / 2) (x : ν) : (G x x).im ≤ 3 / 2 := by
  have h1 := hΩ.norm_diag_le hm x
  have h2 : |(G x x).im| ≤ ‖G x x‖ := Complex.abs_im_le_norm _
  have := le_abs_self (G x x).im
  linarith

end Ward

section SumBound

open RBM.Green RBM.Path

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem EntryDet_card_vtx_real (d L W : ℕ) [NeZero L] [NeZero W] :
    (Fintype.card (Vtx d L W) : ℝ) = (((W * L) ^ d : ℕ) : ℝ) := by
  have h := Fintype.card_congr (splitEquiv d L W)
  have h2 : Fintype.card (Vtx d L W) = (W * L) ^ d := by
    rw [← h]; exact card_Idx d L W
  exact_mod_cast h2

/-- The fine-lattice profile read on `Vtx` through `splitEquiv` is the merged `svar` (`svarF_eq_svar`
and `split (splitEquiv.symm x) = x`; RBM2D `Sblk2_eq_svar`). -/
private theorem EntryDet_svarF_symm (g : ℝ) (x y : Vtx d L W) :
    svarF d L W g ((splitEquiv d L W).symm x) ((splitEquiv d L W).symm y) = svar d L W g x y := by
  rw [svarF_eq_svar]
  have hx : split d L W ((splitEquiv d L W).symm x) = x := (splitEquiv d L W).apply_symm_apply x
  have hy : split d L W ((splitEquiv d L W).symm y) = y := (splitEquiv d L W).apply_symm_apply y
  rw [hx, hy]

/-- **The two-sided sum with the normalised mixture profile** is `≤ (1 + 3 / Im m) max |𝓛_{(+,-)}|`
on the good event (the profile `S' = (a S(g) + b N⁻¹) / (a + b)` read on `Vtx d L W` through
`splitEquiv`).  The band part is `sum_sum_svar_le_maxLoopPM`, the `J`-part goes through Ward
(`ward_row`, `ward_col`, `im_diag_le`) and `inv_N_le_maxLoopPM`.  Any coupling `g`
(RBM2D `:491`; port of RBM1D `gueEntry_sum_prof_le`, `GUEPhaseEntry.lean:963-1045`). -/
theorem sum_Snorm_le (hL : 3 ≤ L) {g E s : ℝ} {M : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hM : M.IsHermitian) (hz : 0 < (zt E s).im) {m : ℂ} (hm : ‖m‖ = 1) (him : 0 < m.im)
    {δ : ℝ} (hΩ : GoodEvent (greenBlk d L W E s M true) m δ) (hδ12 : δ ≤ 1 / 2)
    (hδm : δ ≤ m.im / 2) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < a + b)
    (p q : Vtx d L W) :
    ∑ k, ∑ l, Snorm d L W g a b ((splitEquiv d L W).symm p) ((splitEquiv d L W).symm k) *
        ‖greenBlk d L W E s M true k l‖ ^ 2 *
        Snorm d L W g a b ((splitEquiv d L W).symm l) ((splitEquiv d L W).symm q)
      ≤ (1 + 3 / m.im) * maxLoopPM d L W E s M := by
  set G := greenBlk d L W E s M true with hG
  set N : ℝ := (((W * L) ^ d : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := by
    have : 0 < W * L := Nat.mul_pos (NeZero.pos W) (NeZero.pos L)
    rw [hNdef]; positivity
  set α : ℝ := a / (a + b) with hα
  set β : ℝ := b / (a + b) with hβ
  have hαβ : α + β = 1 := by
    rw [hα, hβ, ← add_div, div_self hu.ne']
  have hα0 : 0 ≤ α := div_nonneg ha hu.le
  have hβ0 : 0 ≤ β := div_nonneg hb hu.le
  have hune : a + b ≠ 0 := hu.ne'
  have hGgreen : G = green (blockMat d L W M) (zt E s) := EntryDet_greenBlk_true_eq E s M
  have hH : (blockMat d L W M).IsHermitian := hM.submatrix _
  set η : ℝ := (zt E s).im with hη
  set Y : ℝ := 3 / 2 / η with hY
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hR : ∀ k, ∑ l, ‖G k l‖ ^ 2 ≤ Y := by
    intro k
    rw [hGgreen, ward_row hH hz.ne' k, ← hGgreen]
    exact div_le_div_of_nonneg_right (im_diag_le hm hΩ hδ12 k) hz.le
  have hC : ∀ l, ∑ k, ‖G k l‖ ^ 2 ≤ Y := by
    intro l
    rw [hGgreen, ward_col hH hz.ne' l, ← hGgreen]
    exact div_le_div_of_nonneg_right (im_diag_le hm hΩ hδ12 l) hz.le
  have hLm := maxLoopPM_nonneg (L := L) (W := W) (d := d) E s M
  set mL := maxLoopPM d L W E s M with hmL
  have hYN : Y / N ≤ 3 / m.im * mL := by
    have h := inv_N_le_maxLoopPM (W := W) (L := L) hM hz hΩ hδm
    have e : Y / N = 3 / m.im * (m.im / (2 * (N * η))) := by
      rw [hY]; field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have hSn : ∀ x y : Vtx d L W,
      Snorm d L W g a b ((splitEquiv d L W).symm x) ((splitEquiv d L W).symm y)
        = α * svar d L W g x y + β / N := by
    intro x y
    rw [← EntryDet_svarF_symm g x y]
    unfold Snorm Smix
    rw [hα, hβ, ← hNdef]
    field_simp
  have hpt : ∀ k l : Vtx d L W,
      (α * svar d L W g p k + β / N) * ‖G k l‖ ^ 2 * (α * svar d L W g l q + β / N)
        = α ^ 2 * (svar d L W g p k * ‖G k l‖ ^ 2 * svar d L W g l q)
          + α * β / N * (svar d L W g p k * ‖G k l‖ ^ 2)
          + α * β / N * (‖G k l‖ ^ 2 * svar d L W g l q)
          + β ^ 2 / N ^ 2 * ‖G k l‖ ^ 2 := by
    intro k l; field_simp; ring
  have hT1 : ∑ k, ∑ l, svar d L W g p k * ‖G k l‖ ^ 2 * svar d L W g l q ≤ mL :=
    sum_sum_svar_le_maxLoopPM (E := E) (u := s) g hL hM p q
  have hT2 : ∑ k, ∑ l, svar d L W g p k * ‖G k l‖ ^ 2 ≤ Y := by
    calc ∑ k, ∑ l, svar d L W g p k * ‖G k l‖ ^ 2 = ∑ k, svar d L W g p k * ∑ l, ‖G k l‖ ^ 2 := by
          simp only [Finset.mul_sum]
      _ ≤ ∑ k, svar d L W g p k * Y :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hR k) (svar_nonneg d L W g _ _)
      _ = Y := by rw [← Finset.sum_mul, sum_svar_row g hL, one_mul]
  have hT3 : ∑ k, ∑ l, ‖G k l‖ ^ 2 * svar d L W g l q ≤ Y := by
    calc ∑ k, ∑ l, ‖G k l‖ ^ 2 * svar d L W g l q = ∑ l, (∑ k, ‖G k l‖ ^ 2) * svar d L W g l q := by
          rw [Finset.sum_comm]; simp only [Finset.sum_mul]
      _ ≤ ∑ l, Y * svar d L W g l q :=
          Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (hC l) (svar_nonneg d L W g _ _)
      _ = Y := by rw [← Finset.mul_sum, sum_svar_col g hL, mul_one]
  have hT4 : ∑ k, ∑ l, ‖G k l‖ ^ 2 ≤ N * Y := by
    calc ∑ k, ∑ l, ‖G k l‖ ^ 2 ≤ ∑ _k : Vtx d L W, Y := Finset.sum_le_sum fun k _ => hR k
      _ = N * Y := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, EntryDet_card_vtx_real]
  simp only [hSn, hpt]
  have hsplit : ∑ k, ∑ l, (α ^ 2 * (svar d L W g p k * ‖G k l‖ ^ 2 * svar d L W g l q)
          + α * β / N * (svar d L W g p k * ‖G k l‖ ^ 2)
          + α * β / N * (‖G k l‖ ^ 2 * svar d L W g l q)
          + β ^ 2 / N ^ 2 * ‖G k l‖ ^ 2)
      = α ^ 2 * ∑ k, ∑ l, svar d L W g p k * ‖G k l‖ ^ 2 * svar d L W g l q
        + α * β / N * ∑ k, ∑ l, svar d L W g p k * ‖G k l‖ ^ 2
        + α * β / N * ∑ k, ∑ l, ‖G k l‖ ^ 2 * svar d L W g l q
        + β ^ 2 / N ^ 2 * ∑ k, ∑ l, ‖G k l‖ ^ 2 := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsplit]
  have e1 := mul_le_mul_of_nonneg_left hT1 (sq_nonneg α)
  have e2 := mul_le_mul_of_nonneg_left hT2 (by positivity : 0 ≤ α * β / N)
  have e3 := mul_le_mul_of_nonneg_left hT3 (by positivity : 0 ≤ α * β / N)
  have e4 := mul_le_mul_of_nonneg_left hT4 (by positivity : 0 ≤ β ^ 2 / N ^ 2)
  have hα1 : α ^ 2 ≤ 1 := by nlinarith
  have hc : α * β / N * Y + α * β / N * Y + β ^ 2 / N ^ 2 * (N * Y) = (1 - α ^ 2) * (Y / N) := by
    have hβ' : β = 1 - α := by linarith
    rw [hβ']
    field_simp
    ring
  have hf : (1 - α ^ 2) * (Y / N) ≤ (1 - α ^ 2) * (3 / m.im * mL) :=
    mul_le_mul_of_nonneg_left hYN (by linarith)
  have h3m : 0 ≤ 3 / m.im * mL := by positivity
  have hα2mL : α ^ 2 * mL ≤ mL := by nlinarith
  have hg : (1 - α ^ 2) * (3 / m.im * mL) ≤ 3 / m.im * mL := by nlinarith
  have : (1 + 3 / m.im) * mL = mL + 3 / m.im * mL := by ring
  rw [this]
  linarith

end SumBound

/-! ## §5d The constants and the deterministic bound `mix_det`

Port of RBM1D `gueEntryC`, `gueEntryK`, `gueEntryDelta`, `gueEntryCdet` and their lemmas
(`GUEPhaseEntry.lean:1055-1092`), of `gueEntry_ldeRowRHS_smul` etc. (`:1101-1130`) and of
`gueEntry_det` (`:1134-1300`).  Changes against RBM2D: `Kstab2 κ L ↦ Kstab3 d Λ κ` (the constants
are `L`-free: arguments `d Λ κ` instead of `κ L`), `gapK ↦ RBM.Loop.gapK`. -/

section MixConst

open RBM.Green

/-- `c_κ = √(2κ)/2 ≤ Im m(E)` (RBM1D `gueEntryC`, `GUEPhaseEntry.lean:1056`). -/
def mixC (κ : ℝ) : ℝ := Real.sqrt (2 * κ) / 2

/-- The stability constant `Kstab3 d Λ κ · (1 + 1 / gapK κ)` of `stable_mix` (RBM1D `gueEntryK`,
`:1059`; RBM2D `mixK κ L`). -/
def mixK (d : ℕ) (Λ κ : ℝ) : ℝ := Kstab3 d Λ κ * (1 + 1 / RBM.Loop.gapK κ)

/-- The smallness threshold for `δ` (RBM1D `gueEntryDelta`, `:1062`). -/
def mixDelta (d : ℕ) (Λ κ : ℝ) : ℝ := min (1 / 2) (min (1 / (2 * mixK d Λ κ)) (mixC κ / 2))

/-- The constant of the deterministic bound (RBM1D `gueEntryCdet`, `:1065`). -/
def mixCdet (d : ℕ) (Λ κ : ℝ) : ℝ := (2160 * mixK d Λ κ ^ 2 + 162) * (1 + 3 / mixC κ)

theorem mixC_pos {κ : ℝ} (hκ : 0 < κ) : 0 < mixC κ := by
  unfold mixC
  have : 0 < Real.sqrt (2 * κ) := Real.sqrt_pos.2 (by linarith)
  positivity

/-- `1 ≤ mixK d Λ κ`: `one_le_Kstab3` and `1 ≤ 1 + 1/gapK κ` (RBM2D `:628` unfolded `Kstab2` with
`log L`; the hypotheses `hκ`, `hκ2` are kept for the call shape). -/
theorem mixK_one_le {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) (d : ℕ) (Λ : ℝ) : 1 ≤ mixK d Λ κ := by
  unfold mixK
  have hg := EntryDet_gapK_pos hκ hκ2
  have h1 := one_le_Kstab3 d Λ κ
  have h3 : (1 : ℝ) ≤ 1 + 1 / RBM.Loop.gapK κ := by
    have : 0 ≤ 1 / RBM.Loop.gapK κ := by positivity
    linarith
  nlinarith

theorem mixDelta_pos {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) (d : ℕ) (Λ : ℝ) : 0 < mixDelta d Λ κ := by
  unfold mixDelta
  have hK := mixK_one_le hκ hκ2 d Λ
  have hc := mixC_pos hκ
  refine lt_min (by norm_num) (lt_min (by positivity) (by positivity))

theorem mixCdet_nonneg {κ : ℝ} (hκ : 0 < κ) (d : ℕ) (Λ : ℝ) : 0 ≤ mixCdet d Λ κ := by
  unfold mixCdet
  have hc := mixC_pos hκ
  positivity

/-- `c_κ ≤ Im m(E)` for `|E| ≤ 2 - κ` (`4 - E² ≥ κ (4 - κ) ≥ 2κ`). -/
private theorem EntryDet_mixC_le_mE_im {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    mixC κ ≤ (mE E).im := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hEsq : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs E]; exact pow_le_pow_left₀ (abs_nonneg E) hE 2
  have h2 : 2 * κ ≤ 4 - E ^ 2 := by nlinarith
  rw [mE_im]
  unfold mixC
  have := Real.sqrt_le_sqrt h2
  linarith

end MixConst

section MixDet

open RBM.Green RBM.Path

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- RBM1D `gueEntry_ldeRowRHS_smul` (`GUEPhaseEntry.lean:1101`), any index type. -/
theorem ldeRowRHS_smul (u : ℝ) (S : n → n → ℝ) (G : Matrix n n ℂ) (i j : n) :
    ldeRowRHS (fun x y => u * S x y) G i j = u * ldeRowRHS S G i j := by
  unfold ldeRowRHS; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring

/-- RBM1D `gueEntry_ldeColRHS_smul` (`:1107`), any index type. -/
theorem ldeColRHS_smul (u : ℝ) (S : n → n → ℝ) (G : Matrix n n ℂ) (i j : n) :
    ldeColRHS (fun x y => u * S x y) G i j = u * ldeColRHS S G i j := by
  unfold ldeColRHS; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring

/-- RBM1D `gueEntry_ldeQuadRHS_smul` (`:1113`), any index type. -/
theorem ldeQuadRHS_smul (u : ℝ) (S : n → n → ℝ) (G : Matrix n n ℂ) (i : n) :
    ldeQuadRHS (fun x y => u * S x y) G i = u ^ 2 * ldeQuadRHS S G i := by
  unfold ldeQuadRHS; rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring

/-- RBM1D `gueEntry_ldeQuadLHS_smul` (`:1121`), any index type. -/
theorem ldeQuadLHS_smul (u : ℝ) (S : n → n → ℝ) (H G : Matrix n n ℂ) (i : n) :
    ldeQuadLHS H G (fun x y => u * S x y) 1 i = ldeQuadLHS H G S u i := by
  unfold ldeQuadLHS
  congr 2
  push_cast
  rw [one_mul, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

end MixDet

section MixDetThm

open RBM.Green RBM.Path

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- **Lemma 4.1 (4.2)+(4.3) at the mixture profile, deterministic form.**  On the good event of
`G = greenBlk d L W E (a+b) M true` (`‖G - m‖_max ≤ δ ≤ mixDelta d Λ κ`), given the four
large-deviation inputs with the profile `S_u = a S(g) + b N⁻¹` (`Smix`, read on `Vtx d L W` through
`splitEquiv`) and factor `Φ`, every entry satisfies
`|(G - m)_{pq}|² ≤ mixCdet d Λ κ · Φ² · max_{a,b} ‖𝓛_{(+,-),(a,b)}‖`.  Port of RBM2D `:715` /
RBM1D `gueEntry_det` (`GUEPhaseEntry.lean:1134-1300`); `0 < g ≤ Λ`, `3 ≤ d` only through `stable_mix`. -/
theorem mix_det (hd : 3 ≤ d) (hL : 3 ≤ L) {M : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hM : M.IsHermitian) {g Λ κ E a b : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ)
    (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < a + b)
    (hu1 : a + b < 1) {δ Φ : ℝ}
    (hΩ : GoodEvent (greenBlk d L W E (a + b) M true) (mE E) δ)
    (hδ : δ ≤ mixDelta d Λ κ) (hΦ1 : 1 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (hLrow : LDERow (blockMat d L W M) (greenBlk d L W E (a + b) M true)
      (fun x y => Smix d L W g a b ((splitEquiv d L W).symm x) ((splitEquiv d L W).symm y)) Φ)
    (hLcol : LDECol (blockMat d L W M) (greenBlk d L W E (a + b) M true)
      (fun x y => Smix d L W g a b ((splitEquiv d L W).symm x) ((splitEquiv d L W).symm y)) Φ)
    (hLquad : LDEQuad (blockMat d L W M) (greenBlk d L W E (a + b) M true)
      (fun x y => Smix d L W g a b ((splitEquiv d L W).symm x) ((splitEquiv d L W).symm y)) 1 Φ)
    (hLdiag : ∀ i, ‖blockMat d L W M i i‖ ^ 2 ≤
      Φ * Smix d L W g a b ((splitEquiv d L W).symm i) ((splitEquiv d L W).symm i))
    (p q : Vtx d L W) :
    ‖(greenBlk d L W E (a + b) M true - mE E •
        (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) p q‖ ^ 2
      ≤ mixCdet d Λ κ * Φ ^ 2 * maxLoopPM d L W E (a + b) M := by
  have hE2 : |E| ≤ 2 := by linarith [abs_nonneg E]
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  set e := splitEquiv d L W with he
  set u : ℝ := a + b with hudef
  set m := mE E with hmdef
  set z := zt E u with hzdef
  set G := greenBlk d L W E u M true with hGdef
  set H := blockMat d L W M with hHdef
  set S' : Vtx d L W → Vtx d L W → ℝ :=
    fun x y => Snorm d L W g a b (e.symm x) (e.symm y) with hS'def
  set Sb : Vtx d L W → Vtx d L W → ℝ :=
    fun x y => Smix d L W g a b (e.symm x) (e.symm y) with hSbdef
  have hm : ‖m‖ = 1 := norm_mE hE2
  have hmim : mixC κ ≤ m.im := EntryDet_mixC_le_mE_im hκ hE
  have hc := mixC_pos hκ
  have him : 0 < m.im := lt_of_lt_of_le hc hmim
  have hzpos : 0 < z.im := by
    rw [hzdef, zt_im]; exact mul_pos (by linarith) him
  have hz : z.im ≠ 0 := hzpos.ne'
  have hGgreen : G = green H z := EntryDet_greenBlk_true_eq E u M
  have hHerm : H.IsHermitian := hM.submatrix _
  have hGM : G * (H - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1 := by
    rw [hGgreen]; exact green_mul_sub_of_im hHerm hz
  have hMG : (H - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * G = 1 := by
    rw [hGgreen]; exact sub_mul_green_of_im hHerm hz
  have hK1 := mixK_one_le hκ hκ2 d Λ
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) (hΩ p p)
  have hδ12 : δ ≤ 1 / 2 := hδ.trans (min_le_left _ _)
  have hδK : mixK d Λ κ * δ ≤ 1 / 2 := by
    have h1 : δ ≤ 1 / (2 * mixK d Λ κ) := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ mixK d Λ κ)
    rwa [show mixK d Λ κ * (1 / (2 * mixK d Λ κ)) = 1 / 2 by field_simp] at h2
  have hδc : δ ≤ m.im / 2 := by
    have h1 : δ ≤ mixC κ / 2 := hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hSbfun : Sb = fun x y => u * S' x y := by
    funext x y
    simp only [hSbdef, hS'def]
    unfold Snorm
    rw [hudef]
    have hune : a + b ≠ 0 := hu.ne'
    field_simp
  have hS0 : ∀ x y, 0 ≤ S' x y := fun x y => Snorm_nonneg ha hb _ _
  have hSrow : ∀ x, ∑ y, S' x y = 1 := by
    intro x
    simp only [hS'def]
    rw [Equiv.sum_comp e.symm (fun y' => Snorm d L W g a b (e.symm x) y')]
    exact sum_Snorm_row hL hu _
  have hScol : ∀ y, ∑ x, S' x y ≤ 1 := by
    intro y
    simp only [hS'def]
    rw [Equiv.sum_comp e.symm (fun x' => Snorm d L W g a b x' (e.symm y))]
    exact (sum_Snorm_col hL hu _).le
  have hS'W : ∀ x y, S' x y ≤ ((W : ℝ) ^ d)⁻¹ := fun x y => Snorm_le hL ha hb hu _ _
  have hu1' : u ≤ 1 := hu1.le
  -- the four inputs in the normalised form
  have hLr : LDERow H G S' Φ := by
    intro i j hij
    have h : ldeRowLHS H G i j ≤ Φ * ldeRowRHS (fun x y => u * S' x y) G i j := by
      rw [← hSbfun]; exact hLrow i j hij
    rw [ldeRowRHS_smul] at h
    have hR : 0 ≤ ldeRowRHS S' G i j :=
      Finset.sum_nonneg fun k _ => mul_nonneg (hS0 _ _) (sq_nonneg _)
    have : Φ * (u * ldeRowRHS S' G i j) ≤ Φ * ldeRowRHS S' G i j :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    linarith
  have hLc : LDECol H G S' Φ := by
    intro k j hkj
    have h : ldeColLHS H G k j ≤ Φ * ldeColRHS (fun x y => u * S' x y) G k j := by
      rw [← hSbfun]; exact hLcol k j hkj
    rw [ldeColRHS_smul] at h
    have hR : 0 ≤ ldeColRHS S' G k j :=
      Finset.sum_nonneg fun l _ => mul_nonneg (sq_nonneg _) (hS0 _ _)
    have : Φ * (u * ldeColRHS S' G k j) ≤ Φ * ldeColRHS S' G k j :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    linarith
  have hLq : LDEQuad H G S' u Φ := by
    intro i
    have h : ldeQuadLHS H G (fun x y => u * S' x y) 1 i
        ≤ Φ * ldeQuadRHS (fun x y => u * S' x y) G i := by
      rw [← hSbfun]; exact hLquad i
    rw [ldeQuadLHS_smul, ldeQuadRHS_smul] at h
    have hR : 0 ≤ ldeQuadRHS S' G i :=
      Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
        mul_nonneg (mul_nonneg (hS0 _ _) (sq_nonneg _)) (hS0 _ _)
    have hu2 : u ^ 2 ≤ 1 := by nlinarith
    have : Φ * (u ^ 2 * ldeQuadRHS S' G i) ≤ Φ * ldeQuadRHS S' G i :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    linarith
  have hLd : ∀ i, ‖H i i‖ ^ 2 ≤ Φ * S' i i := by
    intro i
    have h : ‖H i i‖ ^ 2 ≤ Φ * (u * S' i i) := by
      have := hLdiag i
      have e1 : Smix d L W g a b (e.symm i) (e.symm i) = Sb i i := rfl
      rw [e1, hSbfun] at this
      exact this
    have : Φ * (u * S' i i) ≤ Φ * S' i i :=
      mul_le_mul_of_nonneg_left (by nlinarith [hS0 i i]) (by linarith)
    linarith
  -- `Λ`
  have hLm0 : 0 ≤ maxLoopPM d L W E u M := maxLoopPM_nonneg (L := L) (W := W) (d := d) E u M
  set mL := maxLoopPM d L W E u M with hmL
  set Λ' : ℝ := (1 + 3 / mixC κ) * mL with hΛdef
  have h3c : 3 / m.im ≤ 3 / mixC κ := div_le_div_of_nonneg_left (by norm_num) hc hmim
  have hΛ1 : ∀ i j, ∑ k, ∑ l, S' i k * ‖G k l‖ ^ 2 * S' l j ≤ Λ' := by
    intro i j
    have h := sum_Snorm_le (g := g) hL hM hzpos hm him hΩ hδ12 hδc ha hb hu i j
    have h2 : (1 + 3 / m.im) * mL ≤ (1 + 3 / mixC κ) * mL :=
      mul_le_mul_of_nonneg_right (by linarith) hLm0
    exact h.trans h2
  have hΛ2 : ∀ i j, S' i j ≤ Λ' := by
    intro i j
    have hW2 := inv_Wd_le_maxLoopPM (L := L) (W := W) (E := E) (u := u) hM hE2 hΩ hδ12
    have hc1 : mixC κ ≤ 1 := by
      have : m.im ≤ ‖m‖ := Complex.im_le_norm _
      linarith
    have h4 : 4 ≤ 1 + 3 / mixC κ := by
      have : 3 ≤ 3 / mixC κ := by rw [le_div_iff₀ hc]; linarith
      linarith
    calc S' i j ≤ ((W : ℝ) ^ d)⁻¹ := hS'W i j
      _ ≤ 4 * mL := hW2
      _ ≤ (1 + 3 / mixC κ) * mL := mul_le_mul_of_nonneg_right h4 hLm0
  have hΛ0 : 0 ≤ Λ' := by positivity
  have hΦ2 : 0 ≤ Φ ^ 2 := sq_nonneg Φ
  have hfinal : ∀ X : ℝ, X ≤ (2160 * mixK d Λ κ ^ 2 + 162) * Φ ^ 2 * Λ' →
      X ≤ mixCdet d Λ κ * Φ ^ 2 * mL := by
    intro X hX
    refine hX.trans (le_of_eq ?_)
    unfold mixCdet
    rw [hΛdef]
    ring
  by_cases hij : p = q
  · subst hij
    have hentry : (G - m • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) p p = G p p - m := by
      simp
    rw [hentry]
    have hStab : Stable S' ((u : ℂ) * m ^ 2) (mixK d Λ κ) :=
      EntryDet_stable_relabel e (stable_mix hd hL hg hgΛ hκ hE ha hb hu hu1)
    have h := norm_sq_green_diag_sub_le hGM hMG hm (mE_mul_add_zt hE2 u) (by linarith) hu1' hΩ
      hδ12 hS0 hSrow hScol hΦ1 hΦδ hLr hLc hLq hLd hΛ1 hΛ2 hδK hStab p
    refine hfinal _ (h.trans ?_)
    have h0 : 0 ≤ Φ ^ 2 * Λ' := mul_nonneg hΦ2 hΛ0
    calc 2160 * mixK d Λ κ ^ 2 * Φ ^ 2 * Λ' = 2160 * mixK d Λ κ ^ 2 * (Φ ^ 2 * Λ') := by ring
      _ ≤ (2160 * mixK d Λ κ ^ 2 + 162) * (Φ ^ 2 * Λ') :=
          mul_le_mul_of_nonneg_right (by linarith) h0
      _ = (2160 * mixK d Λ κ ^ 2 + 162) * Φ ^ 2 * Λ' := by ring
  · have hentry : (G - m • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) p q = G p q := by
      simp [hij]
    rw [hentry]
    have h := norm_sq_green_offdiag_le hGM hMG hm hΩ hδ12 hS0 (fun x => (hSrow x).le) hScol
      hΦ1 hΦδ hLr hLc hΛ1 hΛ2 hij
    refine hfinal _ (h.trans ?_)
    have h0 : 0 ≤ Φ ^ 2 * Λ' := mul_nonneg hΦ2 hΛ0
    have hK2 : 0 ≤ 2160 * mixK d Λ κ ^ 2 := by positivity
    calc 162 * Φ ^ 2 * Λ' = 162 * (Φ ^ 2 * Λ') := by ring
      _ ≤ (2160 * mixK d Λ κ ^ 2 + 162) * (Φ ^ 2 * Λ') :=
          mul_le_mul_of_nonneg_right (by linarith) h0
      _ = (2160 * mixK d Λ κ ^ 2 + 162) * Φ ^ 2 * Λ' := by ring

end MixDetThm

/-! ## §8 Compiled instances (namespace `EntryDetCheck`)

`d = 3`, `L = 3`, `W = 2` (`N = (W L)^d = 216 = |Vtx 3 3 2|`), `g = Λ = κ = 1`, `E = 0`
(`mE 0 = I`, `zt 0 u = (1 - u) I`).
* `stable_mix` at `(a, b) = (1/2, 1/4)` (`b > 0`: the `J`-part is present).
* `inv_N_le_maxLoopPM`, `ward_col`, `ward_row`, `sum_Snorm_le` at `M = 0` (so `H = 0`,
  `G = (-z)⁻¹ 1 = (i / (1 - s)) 1`), every deterministic hypothesis discharged.
* `mix_offdiag_det`, `mix_diag_det`, `mix_det` at `M = 0` with `a = b = δI / 8`,
  `δI = min (1/1000) (mixDelta 3 1 1)`: every hypothesis discharged, including the large-deviation
  inputs (trivial for `H = 0` except the quadratic one, which is Cauchy-Schwarz).  `Kstab3` is a
  `Classical.choose` constant with no explicit bound, so the time is expressed through `mixDelta 3 1 1`
  (positive by `mixDelta_pos`): `u = δI / 4`, `u / (1 - u) ≤ δI ≤ mixDelta 3 1 1`.
* `mix_det` at `(a, b) = (1/2, 1/4)` with the good event and the four large-deviation inputs as
  variables (the pins of the other gates), the scalar hypotheses discharged. -/

namespace EntryDetCheck

open RBM.Green RBM.Path

private theorem check_mE_zero : mE 0 = Complex.I := by
  have h : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp [mE, h]

private theorem check_zt_zero (u : ℝ) : zt 0 u = ((1 - u : ℝ) : ℂ) * Complex.I := by
  simp [zt, check_mE_zero]

private theorem check_green_zero {n : Type*} [Fintype n] [DecidableEq n] {z : ℂ} (hz : z ≠ 0) :
    green (0 : Matrix n n ℂ) z = (-z)⁻¹ • (1 : Matrix n n ℂ) := by
  unfold green
  rw [zero_sub, ← neg_smul]
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
    inv_mul_cancel₀ (neg_ne_zero.mpr hz), one_smul]

private theorem check_blockMat_zero (d L W : ℕ) [NeZero L] [NeZero W] :
    blockMat d L W (0 : Matrix (Idx d L W) (Idx d L W) ℂ) = 0 := by
  ext i j; simp [blockMat]

/-- `G_u = (-z)⁻¹ 1 = (i / (1 - u)) 1` at `M = 0`, `E = 0`. -/
private theorem check_greenBlk_zero (d L W : ℕ) [NeZero L] [NeZero W] {u : ℝ} (hu : u < 1) :
    greenBlk d L W 0 u (0 : Matrix (Idx d L W) (Idx d L W) ℂ) true
      = (((1 / (1 - u) : ℝ) : ℂ) * Complex.I) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) := by
  have hu' : (1 - u : ℝ) ≠ 0 := by linarith
  have hz : zt 0 u ≠ 0 := by
    rw [check_zt_zero]
    exact mul_ne_zero (by exact_mod_cast hu') Complex.I_ne_zero
  have h1 : greenBlk d L W 0 u (0 : Matrix (Idx d L W) (Idx d L W) ℂ) true
      = green (blockMat d L W (0 : Matrix (Idx d L W) (Idx d L W) ℂ)) (zt 0 u) :=
    EntryDet_greenBlk_true_eq 0 u 0
  rw [h1, check_blockMat_zero, check_green_zero hz, check_zt_zero]
  congr 1
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hu'' : ((1 - u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hu'
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq]

private theorem check_goodEvent_zero (d L W : ℕ) [NeZero L] [NeZero W] {u : ℝ} (hu : u < 1)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    GoodEvent (greenBlk d L W 0 u (0 : Matrix (Idx d L W) (Idx d L W) ℂ) true)
      (((1 / (1 - u) : ℝ) : ℂ) * Complex.I) δ := by
  intro x y
  rw [check_greenBlk_zero d L W hu]
  by_cases hxy : x = y
  · subst hxy; simpa using hδ
  · simpa [hxy, Matrix.one_apply_ne hxy] using hδ

/-- **`stable_mix` at `d = 3`, `L = 3`, `W = 2`, `g = Λ = κ = 1`, `E = 0`, `a = 1/2`, `b = 1/4`**
(`0 < a + b = 3/4 < 1`, `b > 0`). -/
theorem stable_mix_inst :
    Stable (fun x y : Idx 3 3 2 => Smix 3 3 2 1 (1 / 2) (1 / 4) x y / (1 / 2 + 1 / 4))
      (((1 / 2 + 1 / 4 : ℝ) : ℂ) * mE 0 ^ 2)
      (Kstab3 3 1 1 * (1 + 1 / RBM.Loop.gapK 1)) :=
  stable_mix (d := 3) (L := 3) (W := 2) (by norm_num) (by norm_num) (g := 1) (Λ := 1) (κ := 1)
    (E := 0) (a := 1 / 2) (b := 1 / 4) one_pos le_rfl one_pos (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- **`inv_N_le_maxLoopPM` at `d = 3`, `L = 3`, `W = 2`, `E = 0`, `u = 3/4`, `M = 0`**: `G = 4i · 1`,
`m = 4i` (a free value: with `m = mE 0 = i` the good event fails), `δ = 1/2 ≤ Im m / 2 = 2`,
`η = Im z_u = 1/4 > 0`; the conclusion reads `4 / (2 · 216 · (1/4)) ≤ maxLoopPM`. -/
theorem inv_N_le_maxLoopPM_inst :
    (4 * Complex.I : ℂ).im / (2 * ((((2 * 3) ^ 3 : ℕ) : ℝ) * (zt 0 (3 / 4)).im))
      ≤ maxLoopPM 3 3 2 0 (3 / 4) (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) := by
  have hz : 0 < (zt 0 (3 / 4)).im := by
    rw [check_zt_zero]; norm_num
  have hG := check_goodEvent_zero 3 3 2 (u := 3 / 4) (by norm_num) (δ := 1 / 2) (by norm_num)
  have hm4 : (((1 / (1 - 3 / 4 : ℝ) : ℝ) : ℂ) * Complex.I) = 4 * Complex.I := by
    norm_num
  rw [hm4] at hG
  exact inv_N_le_maxLoopPM (d := 3) (L := 3) (W := 2) Matrix.isHermitian_zero hz hG (by norm_num)

/-- **`ward_col` and `ward_row` at `M = 0`, `z = i`** (`G = i · 1`). -/
theorem ward_col_inst (i : Idx 3 3 2) :
    ∑ x, ‖green (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I x i‖ ^ 2
      = (green (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I i i).im / Complex.I.im :=
  ward_col Matrix.isHermitian_zero (by simp) i

theorem ward_row_inst (i : Idx 3 3 2) :
    ∑ x, ‖green (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I i x‖ ^ 2
      = (green (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I i i).im / Complex.I.im :=
  ward_row Matrix.isHermitian_zero (by simp) i

/-- **`green_transpose` at `H = 0`, `z = i`**. -/
theorem green_transpose_inst :
    (green (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I)ᵀ
      = green (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)ᵀ Complex.I :=
  green_transpose Complex.I

/-- **`sum_Snorm_le` at `d = 3`, `L = 3`, `W = 2`, `g = 1`, `E = 0`, `s = 0`, `M = 0`,
`(a, b) = (1/2, 1/4)`**: `G = i · 1`, `m = i = mE 0`, `δ = 1/2` (`δ ≤ Im m / 2`), `η = 1`. -/
theorem sum_Snorm_le_inst (p q : Vtx 3 3 2) :
    ∑ k, ∑ l, Snorm 3 3 2 1 (1 / 2) (1 / 4) ((splitEquiv 3 3 2).symm p) ((splitEquiv 3 3 2).symm k) *
        ‖greenBlk 3 3 2 0 0 (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) true k l‖ ^ 2 *
        Snorm 3 3 2 1 (1 / 2) (1 / 4) ((splitEquiv 3 3 2).symm l) ((splitEquiv 3 3 2).symm q)
      ≤ (1 + 3 / Complex.I.im) * maxLoopPM 3 3 2 0 0 (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) := by
  have hz : 0 < (zt 0 0).im := by
    rw [check_zt_zero]; norm_num
  have hG := check_goodEvent_zero 3 3 2 (u := 0) (by norm_num) (δ := 1 / 2) (by norm_num)
  have hm1 : (((1 / (1 - 0 : ℝ) : ℝ) : ℂ) * Complex.I) = Complex.I := by norm_num
  rw [hm1] at hG
  exact sum_Snorm_le (d := 3) (L := 3) (W := 2) (by norm_num) Matrix.isHermitian_zero hz
    (by simp) (by simp) hG (by norm_num) (by simp) (by norm_num) (by norm_num) (by norm_num) p q

/-! ### The profile and constants at `d = 3`, `L = 3`, `W = 2` (small instances) -/

/-- **`svarF_le`, `Snorm_le`, `Snorm_nonneg`, `sum_Snorm_row`, `sum_Snorm_col`, `Snorm_symm`,
`Snorm_zero_right`, `Snorm_zero_left`** at `d = 3`, `L = 3`, `W = 2`, `g = 1`. -/
theorem svarF_le_inst (x y : Idx 3 3 2) : svarF 3 3 2 1 x y ≤ ((2 : ℝ) ^ 3)⁻¹ := by
  simpa using svarF_le (d := 3) (L := 3) (W := 2) 1 (by norm_num) x y

theorem Snorm_le_inst (x y : Idx 3 3 2) :
    Snorm 3 3 2 1 (1 / 2) (1 / 4) x y ≤ ((2 : ℝ) ^ 3)⁻¹ := by
  simpa using Snorm_le (d := 3) (L := 3) (W := 2) (g := 1) (by norm_num) (a := 1 / 2) (b := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) x y

theorem Snorm_nonneg_inst (x y : Idx 3 3 2) : 0 ≤ Snorm 3 3 2 1 (1 / 2) (1 / 4) x y :=
  Snorm_nonneg (by norm_num) (by norm_num) x y

theorem sum_Snorm_row_inst (x : Idx 3 3 2) : ∑ y, Snorm 3 3 2 1 (1 / 2) (1 / 4) x y = 1 :=
  sum_Snorm_row (by norm_num) (by norm_num) x

theorem sum_Snorm_col_inst (y : Idx 3 3 2) : ∑ x, Snorm 3 3 2 1 (1 / 2) (1 / 4) x y = 1 :=
  sum_Snorm_col (by norm_num) (by norm_num) y

theorem Snorm_symm_inst (x y : Idx 3 3 2) :
    Snorm 3 3 2 1 (1 / 2) (1 / 4) x y = Snorm 3 3 2 1 (1 / 2) (1 / 4) y x :=
  Snorm_symm 1 _ _ x y

theorem Snorm_zero_right_inst (x y : Idx 3 3 2) :
    Snorm 3 3 2 1 (1 / 2) 0 x y = svarF 3 3 2 1 x y :=
  Snorm_zero_right (by norm_num) x y

theorem Snorm_zero_left_inst (x y : Idx 3 3 2) :
    Snorm 3 3 2 1 0 (1 / 4) x y = 1 / (((2 * 3) ^ 3 : ℕ) : ℝ) :=
  Snorm_zero_left 1 (by norm_num) x y

/-- **`im_diag_le` at `G = i · 1`, `m = i`, `δ = 1/2`**. -/
theorem im_diag_le_inst (x : Idx 3 3 2) :
    ((Complex.I • (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)) x x).im ≤ 3 / 2 := by
  have hG : GoodEvent (Complex.I • (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)) Complex.I (1 / 2) := by
    intro a b
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Matrix.one_apply_ne hab]
  exact im_diag_le (by simp) hG (by norm_num) x

/-- **The constants at `d = 3`, `Λ = 1`, `κ = 1`**: `mixC_pos`, `mixK_one_le`, `mixDelta_pos`,
`mixCdet_nonneg`. -/
theorem mixC_pos_inst : 0 < mixC 1 := mixC_pos one_pos

theorem mixK_one_le_inst : 1 ≤ mixK 3 1 1 := mixK_one_le one_pos (by norm_num) 3 1

theorem mixDelta_pos_inst : 0 < mixDelta 3 1 1 := mixDelta_pos one_pos (by norm_num) 3 1

theorem mixCdet_nonneg_inst : 0 ≤ mixCdet 3 1 1 := mixCdet_nonneg one_pos 3 1

/-- **The four `*_smul` lemmas at `u = 1/2`, `S = Snorm 3 3 2 1 (1/2) (1/4)`, `G = i · 1`**. -/
theorem ldeRowRHS_smul_inst (i j : Idx 3 3 2) :
    ldeRowRHS (fun x y => (1 / 2 : ℝ) * Snorm 3 3 2 1 (1 / 2) (1 / 4) x y)
        (Complex.I • (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)) i j
      = (1 / 2 : ℝ) * ldeRowRHS (Snorm 3 3 2 1 (1 / 2) (1 / 4))
        (Complex.I • (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)) i j :=
  ldeRowRHS_smul _ _ _ i j

theorem ldeColRHS_smul_inst (i j : Idx 3 3 2) :
    ldeColRHS (fun x y => (1 / 2 : ℝ) * Snorm 3 3 2 1 (1 / 2) (1 / 4) x y)
        (Complex.I • (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)) i j
      = (1 / 2 : ℝ) * ldeColRHS (Snorm 3 3 2 1 (1 / 2) (1 / 4))
        (Complex.I • (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)) i j :=
  ldeColRHS_smul _ _ _ i j

theorem ldeQuadRHS_smul_inst (i : Idx 3 3 2) :
    ldeQuadRHS (fun x y => (1 / 2 : ℝ) * Snorm 3 3 2 1 (1 / 2) (1 / 4) x y)
        (Complex.I • (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)) i
      = (1 / 2 : ℝ) ^ 2 * ldeQuadRHS (Snorm 3 3 2 1 (1 / 2) (1 / 4))
        (Complex.I • (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)) i :=
  ldeQuadRHS_smul _ _ _ i

theorem ldeQuadLHS_smul_inst (i : Idx 3 3 2) :
    ldeQuadLHS (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)
        (Complex.I • (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ))
        (fun x y => (1 / 2 : ℝ) * Snorm 3 3 2 1 (1 / 2) (1 / 4) x y) 1 i
      = ldeQuadLHS (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)
        (Complex.I • (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ))
        (Snorm 3 3 2 1 (1 / 2) (1 / 4)) (1 / 2) i :=
  ldeQuadLHS_smul _ _ _ _ i

/-! ### The data at `M = 0` with a small time `u = δI / 4`: `mix_offdiag_det`, `mix_diag_det` and
`mix_det` with every hypothesis discharged

`E = 0`, `M = 0` (so `H = 0` and `G = (-z)⁻¹ 1 = (i / (1 - u)) 1`), `(a, b) = (δI/8, δI/8)`,
`u = a + b = δI/4`, `δ = δI`.  `‖G - m‖_max = u / (1 - u) ≤ δI ≤ mixDelta 3 1 1`.  The three LDE
inputs hold trivially for `H = 0` except the quadratic one, which is Cauchy-Schwarz:
`(∑_{k ≠ i} S_{ik})² ≤ |n| ∑_{k ≠ i} S_{ik}²`. -/

/-- With `H = 0` the row and column LDE and the bound on `H_{ii}` hold trivially. -/
private theorem check_lde_zero {n : Type*} [Fintype n] [DecidableEq n] (G : Matrix n n ℂ)
    (S : n → n → ℝ) (hS : ∀ i j, 0 ≤ S i j) {Φ : ℝ} (hΦ : 0 ≤ Φ) :
    LDERow (0 : Matrix n n ℂ) G S Φ ∧ LDECol (0 : Matrix n n ℂ) G S Φ ∧
      ∀ i, ‖(0 : Matrix n n ℂ) i i‖ ^ 2 ≤ Φ * S i i := by
  refine ⟨fun i j _ => ?_, fun k j _ => ?_, fun i => ?_⟩
  · unfold ldeRowLHS ldeRowRHS
    simp only [Matrix.zero_apply, zero_mul, Finset.sum_const_zero, norm_zero]
    exact le_of_eq_of_le (by norm_num)
      (mul_nonneg hΦ (Finset.sum_nonneg fun k _ => mul_nonneg (hS _ _) (sq_nonneg _)))
  · unfold ldeColLHS ldeColRHS
    simp only [Matrix.zero_apply, mul_zero, Finset.sum_const_zero, norm_zero]
    exact le_of_eq_of_le (by norm_num)
      (mul_nonneg hΦ (Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (hS _ _)))
  · simp only [Matrix.zero_apply, norm_zero]
    exact le_of_eq_of_le (by norm_num) (mul_nonneg hΦ (hS _ _))

/-- The quadratic LDE for `H = 0`, `G = c 1`, a symmetric non-negative profile, `0 ≤ t` and
`|n| t² ≤ Φ` (Cauchy-Schwarz). -/
private theorem check_ldeQuad_scalar {n : Type*} [Fintype n] [DecidableEq n] (c : ℂ)
    (S : n → n → ℝ) (hS0 : ∀ i j, 0 ≤ S i j) (hSs : ∀ i j, S i j = S j i) {t Φ : ℝ}
    (ht : 0 ≤ t) (hΦ : (Fintype.card n : ℝ) * t ^ 2 ≤ Φ) :
    LDEQuad (0 : Matrix n n ℂ) (c • (1 : Matrix n n ℂ)) S t Φ := by
  intro i
  have hgm : ∀ k l : n, k ≠ i →
      greenMinor (c • (1 : Matrix n n ℂ)) i k l = c * (if k = l then 1 else 0) := by
    intro k l hk
    unfold greenMinor
    simp [Matrix.smul_apply, Matrix.one_apply, hk]
  have hsum0 : 0 ≤ ∑ k ∈ Finset.univ.erase i, S i k := Finset.sum_nonneg fun k _ => hS0 i k
  have hL : ldeQuadLHS (0 : Matrix n n ℂ) (c • (1 : Matrix n n ℂ)) S t i
      = t ^ 2 * ‖c‖ ^ 2 * (∑ k ∈ Finset.univ.erase i, S i k) ^ 2 := by
    unfold ldeQuadLHS
    have h1 : ∑ k ∈ Finset.univ.erase i, (S i k : ℂ) *
        greenMinor (c • (1 : Matrix n n ℂ)) i k k
        = ((∑ k ∈ Finset.univ.erase i, S i k : ℝ) : ℂ) * c := by
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hgm k k (Finset.ne_of_mem_erase hk)]
      simp
    rw [h1]
    simp only [Matrix.zero_apply, zero_mul, mul_zero, Finset.sum_const_zero, zero_sub, norm_neg]
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg ht, abs_of_nonneg hsum0]
    ring
  have hR : ldeQuadRHS S (c • (1 : Matrix n n ℂ)) i
      = ‖c‖ ^ 2 * ∑ k ∈ Finset.univ.erase i, S i k ^ 2 := by
    unfold ldeQuadRHS
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    have : ∀ l ∈ Finset.univ.erase i, S i k * ‖greenMinor (c • (1 : Matrix n n ℂ)) i k l‖ ^ 2 * S l i
        = if k = l then S i k * ‖c‖ ^ 2 * S l i else 0 := by
      intro l _
      rw [hgm k l hki]
      by_cases hkl : k = l
      · simp [hkl]
      · simp [hkl]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
    simp only [Finset.mem_erase, ne_eq, Finset.mem_univ, and_true, hki, not_false_eq_true, ite_true]
    rw [hSs k i]
    ring
  rw [hL, hR]
  have hcs : (∑ k ∈ Finset.univ.erase i, S i k) ^ 2
      ≤ ((Finset.univ.erase i).card : ℝ) * ∑ k ∈ Finset.univ.erase i, S i k ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ.erase i) (fun _ => (1 : ℝ))
      (fun k => S i k)
    simpa using h
  have hcard : ((Finset.univ.erase i).card : ℝ) ≤ Fintype.card n := by
    exact_mod_cast (Finset.card_le_univ _)
  have hQ : 0 ≤ ∑ k ∈ Finset.univ.erase i, S i k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hc2 : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
  calc t ^ 2 * ‖c‖ ^ 2 * (∑ k ∈ Finset.univ.erase i, S i k) ^ 2
      ≤ t ^ 2 * ‖c‖ ^ 2 * ((Fintype.card n : ℝ) * ∑ k ∈ Finset.univ.erase i, S i k ^ 2) :=
        mul_le_mul_of_nonneg_left (hcs.trans (mul_le_mul_of_nonneg_right hcard hQ))
          (by positivity)
    _ = ‖c‖ ^ 2 * (((Fintype.card n : ℝ) * t ^ 2) * ∑ k ∈ Finset.univ.erase i, S i k ^ 2) := by
        ring
    _ ≤ ‖c‖ ^ 2 * (Φ * ∑ k ∈ Finset.univ.erase i, S i k ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΦ hQ) hc2
    _ = Φ * (‖c‖ ^ 2 * ∑ k ∈ Finset.univ.erase i, S i k ^ 2) := by ring

private theorem check_neg_inv {u : ℝ} (hu : u < 1) :
    (-(zt 0 u))⁻¹ = ((1 / (1 - u) : ℝ) : ℂ) * Complex.I := by
  have hu' : (1 - u : ℝ) ≠ 0 := by linarith
  rw [check_zt_zero]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hu'' : ((1 - u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hu'
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq]

private theorem check_norm_sub {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    ‖(((1 / (1 - u) : ℝ) : ℂ) * Complex.I) - Complex.I‖ ≤ 2 * u := by
  have h1 : (((1 / (1 - u) : ℝ) : ℂ) * Complex.I) - Complex.I
      = (((1 / (1 - u) - 1 : ℝ)) : ℂ) * Complex.I := by push_cast; ring
  rw [h1, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hpos : 0 < 1 - u := by linarith
  have h2 : 1 / (1 - u) - 1 = u / (1 - u) := by field_simp; ring
  rw [h2, abs_of_nonneg (div_nonneg hu0 hpos.le), div_le_iff₀ hpos]
  nlinarith

private theorem check_norm_c {u : ℝ} (hu : u ≤ 1 / 2) :
    ‖(((1 / (1 - u) : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤ 4 := by
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hpos : 0 < 1 - u := by linarith
  rw [abs_of_pos (by positivity)]
  have : 1 / (1 - u) ≤ 2 := by rw [div_le_iff₀ hpos]; linarith
  have h0 : 0 ≤ 1 / (1 - u) := by positivity
  nlinarith

private theorem check_scalar_goodEvent {n : Type*} [DecidableEq n] {c m : ℂ}
    {δ : ℝ} (hδ : ‖c - m‖ ≤ δ) (h0 : 0 ≤ δ) : GoodEvent (c • (1 : Matrix n n ℂ)) m δ := by
  intro x y
  by_cases hxy : x = y
  · subst hxy; simpa using hδ
  · simpa [hxy, Matrix.one_apply_ne hxy] using h0

private theorem check_sum_le {n : Type*} [Fintype n] [DecidableEq n] {c : ℂ} (hc : ‖c‖ ^ 2 ≤ 4)
    (S : n → n → ℝ) (hS0 : ∀ i j, 0 ≤ S i j) (hrow : ∀ i, ∑ j, S i j ≤ 1)
    (hcol : ∀ j, ∑ i, S i j ≤ 1) (i j : n) :
    ∑ k, ∑ l, S i k * ‖(c • (1 : Matrix n n ℂ)) k l‖ ^ 2 * S l j ≤ 4 := by
  have hG : ∀ k l, ‖(c • (1 : Matrix n n ℂ)) k l‖ ^ 2 ≤ 4 := by
    intro k l
    by_cases hkl : k = l
    · subst hkl; simpa using hc
    · simp [Matrix.one_apply_ne hkl]
  calc ∑ k, ∑ l, S i k * ‖(c • (1 : Matrix n n ℂ)) k l‖ ^ 2 * S l j
      ≤ ∑ k, ∑ l, S i k * 4 * S l j :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ =>
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hG k l) (hS0 _ _)) (hS0 _ _)
    _ = 4 * ((∑ k, S i k) * ∑ l, S l j) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ ≤ 4 * (1 * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (hrow i) (hcol j)
          (Finset.sum_nonneg fun l _ => hS0 _ _) zero_le_one) (by norm_num)
    _ = 4 := by norm_num

private theorem check_zt_im_ne {u : ℝ} (hu : u < 1) : (zt 0 u).im ≠ 0 := by
  rw [zt_im]
  have h1 := mE_im_pos (E := 0) (by norm_num)
  have h2 : 0 < 1 - u := by linarith
  exact (mul_pos h2 h1).ne'

/-- The small time threshold `δI = min (1/1000) (mixDelta 3 1 1)` (`> 0` by `mixDelta_pos`). -/
private def check_dI : ℝ := min (1 / 1000) (mixDelta 3 1 1)

private theorem check_dI_pos : 0 < check_dI :=
  lt_min (by norm_num) (mixDelta_pos one_pos (by norm_num) 3 1)

private theorem check_dI_le_thou : check_dI ≤ 1 / 1000 := min_le_left _ _

private theorem check_dI_le_mixDelta : check_dI ≤ mixDelta 3 1 1 := min_le_right _ _

/-- `a = b = δI / 8` (`u = a + b = δI / 4`). -/
private def check_t : ℝ := check_dI / 8

private theorem check_t_pos : 0 < check_t := by unfold check_t; linarith [check_dI_pos]

private theorem check_t_add_le : check_t + check_t ≤ 1 / 2 := by
  unfold check_t; linarith [check_dI_le_thou]

private theorem check_t_two_le : 2 * (check_t + check_t) ≤ check_dI := by
  unfold check_t; linarith [check_dI_pos]

private theorem check_dI_mixK : mixK 3 1 1 * check_dI ≤ 1 / 2 := by
  have h1 : check_dI ≤ 1 / (2 * mixK 3 1 1) :=
    check_dI_le_mixDelta.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hK1 := mixK_one_le (κ := 1) one_pos (by norm_num) 3 1
  have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ mixK 3 1 1)
  rwa [show mixK 3 1 1 * (1 / (2 * mixK 3 1 1)) = 1 / 2 by field_simp] at h2

private theorem check_card_idx : (Fintype.card (Idx 3 3 2) : ℝ) = 216 := by
  rw [card_Idx]; norm_num

private theorem check_card_vtx : (Fintype.card (Vtx 3 3 2) : ℝ) = 216 := by
  rw [EntryDet_card_vtx_real]; norm_num

/-- **`mix_offdiag_det` at `d = 3`, `L = 3`, `W = 2`, `g = 1`, `M = 0`, `E = 0`, `a = b = δI/8`,
`Φ = 1`, `Λ = 4`, `δ = δI`**: every hypothesis is discharged (`H = 0`, `G = (i / (1 - u)) 1`,
`m = i`). -/
theorem mix_offdiag_det_inst {i j : Idx 3 3 2} (hij : i ≠ j) :
    ‖green (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) (zt 0 (check_t + check_t)) i j‖ ^ 2
      ≤ 162 * (1 : ℝ) ^ 2 * 4 := by
  have hu1 : check_t + check_t < 1 := by linarith [check_t_add_le]
  have hu0 : 0 < check_t + check_t := by linarith [check_t_pos]
  have hzim : (zt 0 (check_t + check_t)).im ≠ 0 := check_zt_im_ne hu1
  have hz : zt 0 (check_t + check_t) ≠ 0 := fun h => hzim (by rw [h]; simp)
  have hGc : green (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) (zt 0 (check_t + check_t))
      = (((1 / (1 - (check_t + check_t)) : ℝ) : ℂ) * Complex.I) •
        (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) := by
    rw [check_green_zero hz, check_neg_inv hu1]
  have hGM := green_mul_sub_of_im (Matrix.isHermitian_zero (n := Idx 3 3 2) (α := ℂ)) hzim
  have hMG := sub_mul_green_of_im (Matrix.isHermitian_zero (n := Idx 3 3 2) (α := ℂ)) hzim
  have hlde := check_lde_zero (n := Idx 3 3 2)
    (green (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) (zt 0 (check_t + check_t)))
    (Snorm 3 3 2 1 check_t check_t) (fun i j => Snorm_nonneg check_t_pos.le check_t_pos.le i j)
    (Φ := 1) zero_le_one
  have hδ12 : check_dI ≤ 1 / 2 := check_dI_le_thou.trans (by norm_num)
  have hδ0 := check_dI_pos.le
  refine mix_offdiag_det (d := 3) (L := 3) (W := 2) (g := 1) (by norm_num) check_t_pos.le
    check_t_pos.le hu0
    (z := zt 0 (check_t + check_t)) (m := mE 0) (δ := check_dI) (Φ := 1) (Λ := 4)
    hGM hMG (norm_mE (by norm_num)) ?_ hδ12 (by norm_num)
    (by nlinarith [check_dI_le_thou])
    hlde.1 hlde.2.1 ?_ ?_ hij
  · rw [hGc, check_mE_zero]
    exact check_scalar_goodEvent ((check_norm_sub hu0.le check_t_add_le).trans check_t_two_le)
      hδ0
  · rw [hGc]
    exact check_sum_le (check_norm_c check_t_add_le) _
      (fun i j => Snorm_nonneg check_t_pos.le check_t_pos.le i j)
      (fun i => (sum_Snorm_row (by norm_num) hu0 i).le)
      (fun j => (sum_Snorm_col (by norm_num) hu0 j).le)
  · intro i j
    refine (Snorm_le (by norm_num) check_t_pos.le check_t_pos.le hu0 i j).trans ?_
    norm_num

/-- **`mix_diag_det` at the same data**: `t = u = δI/4`, `Φ = 1`, `Λ' = 4`, `δ = δI`; the quadratic
LDE is the Cauchy-Schwarz lemma `check_ldeQuad_scalar` (`216 u² ≤ 1`) and the absorption
`Kstab3 · (1 + 1/gapK) · δ ≤ 1/2` follows from `δI ≤ mixDelta 3 1 1 ≤ 1 / (2 mixK 3 1 1)`. -/
theorem mix_diag_det_inst (i : Idx 3 3 2) :
    ‖green (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) (zt 0 (check_t + check_t)) i i - mE 0‖ ^ 2
      ≤ 2160 * (Kstab3 3 1 1 * (1 + 1 / RBM.Loop.gapK 1)) ^ 2 * (1 : ℝ) ^ 2 * 4 := by
  have hu1 : check_t + check_t < 1 := by linarith [check_t_add_le]
  have hu0 : 0 < check_t + check_t := by linarith [check_t_pos]
  have hzim : (zt 0 (check_t + check_t)).im ≠ 0 := check_zt_im_ne hu1
  have hz : zt 0 (check_t + check_t) ≠ 0 := fun h => hzim (by rw [h]; simp)
  have hGc : green (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) (zt 0 (check_t + check_t))
      = (((1 / (1 - (check_t + check_t)) : ℝ) : ℂ) * Complex.I) •
        (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) := by
    rw [check_green_zero hz, check_neg_inv hu1]
  have hGM := green_mul_sub_of_im (Matrix.isHermitian_zero (n := Idx 3 3 2) (α := ℂ)) hzim
  have hMG := sub_mul_green_of_im (Matrix.isHermitian_zero (n := Idx 3 3 2) (α := ℂ)) hzim
  have hS0 : ∀ i j, 0 ≤ Snorm 3 3 2 1 check_t check_t i j := fun i j =>
    Snorm_nonneg check_t_pos.le check_t_pos.le i j
  have hlde := check_lde_zero (n := Idx 3 3 2)
    (green (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) (zt 0 (check_t + check_t)))
    (Snorm 3 3 2 1 check_t check_t) hS0 (Φ := 1) zero_le_one
  have hδ12 : check_dI ≤ 1 / 2 := check_dI_le_thou.trans (by norm_num)
  have hδ0 := check_dI_pos.le
  have hK : (Kstab3 3 1 1 * (1 + 1 / RBM.Loop.gapK 1)) * check_dI ≤ 1 / 2 := check_dI_mixK
  have hδ12 : check_dI ≤ 1 / 2 := check_dI_le_thou.trans (by norm_num)
  have hδ0 := check_dI_pos.le
  have hK : (Kstab3 3 1 1 * (1 + 1 / RBM.Loop.gapK 1)) * check_dI ≤ 1 / 2 := check_dI_mixK
  refine mix_diag_det (d := 3) (L := 3) (W := 2) (g := 1) (Λ := 1) (κ := 1) (E := 0)
    (a := check_t) (b := check_t) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) check_t_pos.le check_t_pos.le hu0 hu1
    (δ := check_dI) (Φ := 1) (Λ' := 4)
    hGM hMG ?_ hδ12 (by norm_num) (by nlinarith [check_dI_le_thou]) hlde.1 hlde.2.1 ?_ hlde.2.2
    ?_ ?_ hK i
  · rw [hGc, check_mE_zero]
    exact check_scalar_goodEvent ((check_norm_sub hu0.le check_t_add_le).trans check_t_two_le)
      hδ0
  · rw [hGc]
    refine check_ldeQuad_scalar _ (Snorm 3 3 2 1 check_t check_t) hS0
      (fun i j => Snorm_symm 1 _ _ i j) hu0.le ?_
    rw [check_card_idx]
    have h1 : check_t + check_t ≤ 1 / 4000 := by unfold check_t; linarith [check_dI_le_thou]
    nlinarith
  · rw [hGc]
    exact check_sum_le (check_norm_c check_t_add_le) _ hS0
      (fun i => (sum_Snorm_row (by norm_num) hu0 i).le)
      (fun j => (sum_Snorm_col (by norm_num) hu0 j).le)
  · intro i j
    refine (Snorm_le (by norm_num) check_t_pos.le check_t_pos.le hu0 i j).trans ?_
    norm_num

/-- **`mix_det` at `d = 3`, `L = 3`, `W = 2`, `g = Λ = κ = 1`, `E = 0`, `M = 0`, `a = b = δI/8`,
`Φ = 216`, `δ = δI`: every hypothesis is discharged** (not only the scalar ones).
`G = (i / (1 - u)) 1`, `‖G - m‖_max = u / (1 - u) ≤ δI ≤ mixDelta 3 1 1`; the quadratic LDE at `t = 1`
and the profile `S_u = a S + b N⁻¹` needs `Φ ≥ |Vtx 3 3 2| = 216` (Cauchy-Schwarz). -/
theorem mix_det_inst (p q : Vtx 3 3 2) :
    ‖(greenBlk 3 3 2 0 (check_t + check_t) (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) true - mE 0 •
        (1 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ)) p q‖ ^ 2
      ≤ mixCdet 3 1 1 * (216 : ℝ) ^ 2 * maxLoopPM 3 3 2 0 (check_t + check_t)
          (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) := by
  have hu1 : check_t + check_t < 1 := by linarith [check_t_add_le]
  have hu0 : 0 < check_t + check_t := by linarith [check_t_pos]
  have hG := check_greenBlk_zero 3 3 2 hu1
  have hS0 : ∀ x y : Vtx 3 3 2,
      0 ≤ Smix 3 3 2 1 check_t check_t ((splitEquiv 3 3 2).symm x) ((splitEquiv 3 3 2).symm y) :=
    fun x y => Smix_nonneg 3 3 2 1 check_t_pos.le check_t_pos.le _ _
  have hSs : ∀ x y : Vtx 3 3 2,
      Smix 3 3 2 1 check_t check_t ((splitEquiv 3 3 2).symm x) ((splitEquiv 3 3 2).symm y)
        = Smix 3 3 2 1 check_t check_t ((splitEquiv 3 3 2).symm y) ((splitEquiv 3 3 2).symm x) :=
    fun x y => Smix_symm 3 3 2 1 _ _ _ _
  have hlde := check_lde_zero (n := Vtx 3 3 2)
    (greenBlk 3 3 2 0 (check_t + check_t) (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) true)
    (fun x y => Smix 3 3 2 1 check_t check_t ((splitEquiv 3 3 2).symm x) ((splitEquiv 3 3 2).symm y))
    hS0 (Φ := 216) (by norm_num)
  refine mix_det (d := 3) (L := 3) (W := 2) (by norm_num) (by norm_num) Matrix.isHermitian_zero
    (g := 1) (Λ := 1) (κ := 1) (E := 0) (a := check_t) (b := check_t) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) check_t_pos.le check_t_pos.le hu0 hu1
    (δ := check_dI) (Φ := 216) ?_ check_dI_le_mixDelta (by norm_num)
    (by nlinarith [check_dI_le_thou, check_dI_pos]) ?_ ?_ ?_ ?_ p q
  · rw [hG, check_mE_zero]
    exact check_scalar_goodEvent ((check_norm_sub hu0.le check_t_add_le).trans check_t_two_le)
      check_dI_pos.le
  · rw [check_blockMat_zero]; exact hlde.1
  · rw [check_blockMat_zero]; exact hlde.2.1
  · rw [check_blockMat_zero, hG]
    refine check_ldeQuad_scalar _ _ hS0 hSs zero_le_one ?_
    rw [check_card_vtx]; norm_num
  · intro i; rw [check_blockMat_zero]; exact hlde.2.2 i

/-- **`mix_det` with its hypotheses as variables** (the instance the ticket asks for): `d = 3`,
`L = 3`, `W = 2`, `g = Λ = κ = 1`, `E = 0`, `(a, b) = (1/2, 1/4)` (`b > 0`, `0 < u = 3/4 < 1`),
`M` Hermitian, `Φ = 1`, `δ = mixDelta 3 1 1 / 3` (so `0 < δ ≤ mixDelta 3 1 1` and `36 Φ δ² ≤ 1`); the
good event and the four large-deviation inputs stay as hypotheses (pins of other gates). -/
theorem mix_det_inst_vars {M : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ} (hM : M.IsHermitian)
    (hΩ : GoodEvent (greenBlk 3 3 2 0 (1 / 2 + 1 / 4) M true) (mE 0) (mixDelta 3 1 1 / 3))
    (hLrow : LDERow (blockMat 3 3 2 M) (greenBlk 3 3 2 0 (1 / 2 + 1 / 4) M true)
      (fun x y => Smix 3 3 2 1 (1 / 2) (1 / 4) ((splitEquiv 3 3 2).symm x)
        ((splitEquiv 3 3 2).symm y)) 1)
    (hLcol : LDECol (blockMat 3 3 2 M) (greenBlk 3 3 2 0 (1 / 2 + 1 / 4) M true)
      (fun x y => Smix 3 3 2 1 (1 / 2) (1 / 4) ((splitEquiv 3 3 2).symm x)
        ((splitEquiv 3 3 2).symm y)) 1)
    (hLquad : LDEQuad (blockMat 3 3 2 M) (greenBlk 3 3 2 0 (1 / 2 + 1 / 4) M true)
      (fun x y => Smix 3 3 2 1 (1 / 2) (1 / 4) ((splitEquiv 3 3 2).symm x)
        ((splitEquiv 3 3 2).symm y)) 1 1)
    (hLdiag : ∀ i, ‖blockMat 3 3 2 M i i‖ ^ 2 ≤
      1 * Smix 3 3 2 1 (1 / 2) (1 / 4) ((splitEquiv 3 3 2).symm i) ((splitEquiv 3 3 2).symm i))
    (p q : Vtx 3 3 2) :
    ‖(greenBlk 3 3 2 0 (1 / 2 + 1 / 4) M true - mE 0 •
        (1 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ)) p q‖ ^ 2
      ≤ mixCdet 3 1 1 * (1 : ℝ) ^ 2 * maxLoopPM 3 3 2 0 (1 / 2 + 1 / 4) M := by
  have hd0 := mixDelta_pos (κ := 1) one_pos (by norm_num) 3 1
  have hd1 : mixDelta 3 1 1 ≤ 1 / 2 := min_le_left _ _
  refine mix_det (d := 3) (L := 3) (W := 2) (by norm_num) (by norm_num) hM
    (g := 1) (Λ := 1) (κ := 1) (E := 0) (a := 1 / 2) (b := 1 / 4) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (δ := mixDelta 3 1 1 / 3) (Φ := 1) hΩ (by linarith) le_rfl ?_ hLrow hLcol hLquad hLdiag p q
  nlinarith

end EntryDetCheck

end RBM.Univ

end
