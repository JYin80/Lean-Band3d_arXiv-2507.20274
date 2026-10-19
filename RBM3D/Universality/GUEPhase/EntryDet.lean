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
# The deterministic entry layer of the GUE phase at the mixture profile, `d ≥ 3`

The argument follows the two-dimensional formalization (`GUEPhase/EntryDet` of RBM2D), written at `d ≥ 3`.  The
mixture profile is `S_u = a S(g) + b N⁻¹` (`Smix d L W g a b`, in `AuxCarrier.lean`), `S' = S_u / u`,
`u = a + b`, `N = (W L)^d`.  Paper: Lemma 4.1 (4.2), (4.3) of [YY_25] at the GUE-phase profile, as
used in the GUE phase of Theorem 2.4 `Thm: B_Univ`; Lemma 3.1 (`lem_GbEXP`) says that the proof follows Lemma 4.1 of
[YY_25] and is dimension-independent.

* §4 stability of `1 - u m² S'` (`stable_mix`), constant `Kstab3 d Λ κ (1 + 1 / gapK κ)`, `L`-free
  (RBM2D: `Kstab2 κ L ∝ 1 + log L`).
* §5 the profile `Snorm = Smix / (a + b)` and the deterministic core of Lemma 4.1 (4.2), (4.3)
  at the mixture profile (`mix_det`), the `EntryCore` unchanged.
* §5b the `J`-part: Ward in column form (`ward_col`) and `Im m / (2 N η) ≤ maxLoopPM`
  (`inv_N_le_maxLoopPM`).
* §5c Ward in row form, `im_diag_le` and the two-sided sum `sum_Snorm_le`.
* §5d the constants (`mixC`, `mixK`, `mixDelta`, `mixCdet`) and the deterministic bound `mix_det`.

The band instance (`0 < g ≤ Λ`, `m = mE E`) is proved here; the block Anderson form (`g = 0`, matrix `m`) is
separate.  Private copies of private lemmas: `EntryDet_stable_relabel`, `EntryDet_greenBlk_true_eq`,
`EntryDet_gapK_pos`; the wrapper `EntryDet_gapK_le_norm` is `RBM.Loop.gapK_le_norm` at `s = true`.
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

/-- The bulk gap `c_κ ≤ |1 - t m²|`: the `RBM.Loop.gapK_le_norm` at `s = true`
(`mSigma E true = mE E`); RBM2D `gapK_le_norm'` with `spectralM ↦ mE`. -/
private theorem EntryDet_gapK_le_norm {κ E t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) :
    RBM.Loop.gapK κ ≤ ‖1 - (t : ℂ) * mE E ^ 2‖ := by
  have h := RBM.Loop.gapK_le_norm hκ hE ht0 true
  have e : mSigma E true = mE E := by simp [mSigma]
  rw [e, ← pow_two] at h
  exact h

/-- `Stable` is invariant under relabelling the index set (copy of the private `stability_relabel`; RBM2D `stable_relabel`). -/
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
(`|1 - u m²| ≥ c_κ`) and the band part is the `stable_svar_bulk` at `t = a`.  The constant is
the `L`-free `Kstab3 d Λ κ (1 + 1 / gapK κ)` (RBM2D: `Kstab2 κ L`). -/
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


/-! ## §5 The deterministic core of Lemma 4.1 at the mixture profile (`EntryCore`, unchanged) -/

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

/-- The entry bound `S^{(B)}(g)_{xy} W^{-d} ≤ W^{-d}` (`S^{(B)}(g) ≤ 1`: the kernel is non-negative and
sums to `1`; RBM2D `svar_le` had the constant `1/5`): `svar_le_inv_Wd`
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

end Core

/-! ## §5b The `J`-part lemma: `(N η)⁻¹ Im m ≲ max |𝓛|`, `N = (W L)^d`

The only new deterministic input of the mixture profile beyond the band: the flat part `b N⁻¹` of the
profile is bounded through the Ward identity, since `∑_{a,b} |𝓛_{(+,-),(a,b)}| = W^{-2d}
∑_{x,y} |G_{xy}|²` (`norm_loopPM_eq`) and `∑_x |G_{xy}|² = Im G_{yy} / η`. -/

section JPart

open RBM.Green RBM.Path

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `greenBlk … true` is the resolvent of `blockMat M` at `z_u^{(E)}` (copy of the private
`entryDom_greenBlk_true_eq`; RBM2D `simp [greenBlk]`). -/
private theorem EntryDet_greenBlk_true_eq (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) :
    greenBlk d L W E u M true = green (blockMat d L W M) (zt E u) := by
  simp only [greenBlk, Gres, green, ite_true]
  exact (Matrix.nonsing_inv_eq_ringInverse _).symm

/-- **Ward, column form**: `∑_x |G_{xi}|² = Im G_{ii} / Im z` (RBM1D `gueEntry_ward_col`, from the `im_green_diag`; any index type). -/
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
(RBM2D: `Z2 L ↦ Zd d L`, fibre `Fin (W^d)`, `L^d` columns). -/
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

Port of RBM1D `gueEntry_ward_row`, `gueEntry_green_transpose`,
`gueEntry_im_diag_le` and `gueEntry_sum_prof_le`. -/

section Ward

open RBM.Green RBM.Path

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

/-- `(green H z)ᵀ = green Hᵀ z` (RBM1D `gueEntry_green_transpose`; no
change: any index type). -/
theorem green_transpose {H : Matrix ν ν ℂ} (z : ℂ) : (green H z)ᵀ = green Hᵀ z := by
  unfold green
  rw [Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one]

/-- **Ward, row form**: `∑_l |G_{kl}|² = Im G_{kk} / Im z` (RBM1D `gueEntry_ward_row`; no change: any index type). -/
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
/-- On the good event, `Im G_{xx} ≤ 3/2` (RBM1D `gueEntry_im_diag_le`,
for an arbitrary matrix `G` instead of `green H z`; the statement keeps `[Fintype ν]`). -/
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

/-- The fine-lattice profile read on `Vtx` through `splitEquiv` is the `svar` (`svarF_eq_svar`
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
(as RBM1D `gueEntry_sum_prof_le`). -/
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

Port of RBM1D `gueEntryC`, `gueEntryK`, `gueEntryDelta`, `gueEntryCdet` and their lemmas, of `gueEntry_ldeRowRHS_smul` etc. and of
`gueEntry_det`.  Changes against RBM2D: `Kstab2 κ L ↦ Kstab3 d Λ κ` (the constants
are `L`-free: arguments `d Λ κ` instead of `κ L`), `gapK ↦ RBM.Loop.gapK`. -/

section MixConst

open RBM.Green

/-- `c_κ = √(2κ)/2 ≤ Im m(E)` (RBM1D `gueEntryC`). -/
def mixC (κ : ℝ) : ℝ := Real.sqrt (2 * κ) / 2

/-- The stability constant `Kstab3 d Λ κ · (1 + 1 / gapK κ)` of `stable_mix` (RBM1D `gueEntryK`; RBM2D `mixK κ L`). -/
def mixK (d : ℕ) (Λ κ : ℝ) : ℝ := Kstab3 d Λ κ * (1 + 1 / RBM.Loop.gapK κ)

/-- The smallness threshold for `δ` (RBM1D `gueEntryDelta`). -/
def mixDelta (d : ℕ) (Λ κ : ℝ) : ℝ := min (1 / 2) (min (1 / (2 * mixK d Λ κ)) (mixC κ / 2))

/-- The constant of the deterministic bound (RBM1D `gueEntryCdet`). -/
def mixCdet (d : ℕ) (Λ κ : ℝ) : ℝ := (2160 * mixK d Λ κ ^ 2 + 162) * (1 + 3 / mixC κ)

theorem mixC_pos {κ : ℝ} (hκ : 0 < κ) : 0 < mixC κ := by
  unfold mixC
  have : 0 < Real.sqrt (2 * κ) := Real.sqrt_pos.2 (by linarith)
  positivity

/-- `1 ≤ mixK d Λ κ`: `one_le_Kstab3` and `1 ≤ 1 + 1/gapK κ` (RBM2D unfolded `Kstab2` with
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

/-- RBM1D `gueEntry_ldeRowRHS_smul`, any index type. -/
theorem ldeRowRHS_smul (u : ℝ) (S : n → n → ℝ) (G : Matrix n n ℂ) (i j : n) :
    ldeRowRHS (fun x y => u * S x y) G i j = u * ldeRowRHS S G i j := by
  unfold ldeRowRHS; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring

/-- RBM1D `gueEntry_ldeColRHS_smul`, any index type. -/
theorem ldeColRHS_smul (u : ℝ) (S : n → n → ℝ) (G : Matrix n n ℂ) (i j : n) :
    ldeColRHS (fun x y => u * S x y) G i j = u * ldeColRHS S G i j := by
  unfold ldeColRHS; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring

/-- RBM1D `gueEntry_ldeQuadRHS_smul`, any index type. -/
theorem ldeQuadRHS_smul (u : ℝ) (S : n → n → ℝ) (G : Matrix n n ℂ) (i : n) :
    ldeQuadRHS (fun x y => u * S x y) G i = u ^ 2 * ldeQuadRHS S G i := by
  unfold ldeQuadRHS; rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring

/-- RBM1D `gueEntry_ldeQuadLHS_smul`, any index type. -/
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
`|(G - m)_{pq}|² ≤ mixCdet d Λ κ · Φ² · max_{a,b} ‖𝓛_{(+,-),(a,b)}‖`.  As RBM1D `gueEntry_det`; `0 < g ≤ Λ`,
`3 ≤ d` only through `stable_mix`. -/
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


end RBM.Univ

end
