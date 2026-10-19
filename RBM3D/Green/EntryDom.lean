/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Green.EntryCore
import RBM3D.Green.Stability
import RBM3D.Green.Pins
import RBM3D.Induction.PerTimeCalc

/-!
# Block-average error (3.5) `GavLGEX` and the `≺` layer of `lem_GbEXP`, `d ≥ 3`

Paper: arXiv:2507.20274.  Lemma 3.1 (`lem_GbEXP`) states (3.3) `GijGEX`, (3.2) `GiiGEX`,
(3.5) `GavLGEX`; the paper does not prove them: it says that their proof follows Lemma 4.1 of
[YY_25] and that the argument is dimension-independent (resolvent identities and large deviation
estimates).  The block-product index is `Vtx d L W = Z_L^d × Fin (W^d)` and the variance profile
is `svar d L W g` (`S = S^(B)(g) ⊗ W^{-d} J`, (2.5) `eq:variancematrix`).

Contents:
1. the resolvent helpers `green_mul_sub_of_im`, `sub_mul_green_of_im`, `zt_im_ne_zero`,
   `mE_mul_add_zt`;
2. the profile `svar` on `Vtx`: row and column sums, the bounds `S ≤ W^{-d}`, the support;
3. the neighbour sums `∑_{k,l} S_{pk} |G_{kl}|² S_{lq}` and their bound by `maxLoopPM`;
4. (3.3) `GijGEX` in block form (`offSq_le_gexRHS_blk`, and its fine-lattice form);
5. the lower bounds `W^{-d} ≤ 4 maxLoopPM` and `S ≤ 4 maxLoopPM`;
6. (3.2) `GiiGEX` in block form (`diagSq_le_maxLoopPM_blk`), with the `d ≥ 3` stability constant
   `Kstab3 d Λ κ` of `Green/Stability.lean` (which does not depend on `L`);
7. (3.5) `GavLGEX`: `blkCoef2`, `avgErr = ∑_k blkCoef2 (G_kk - m)` and the bound `norm_avgErr_le`;
8. the engine `of_det`, the grid bookkeeping, `goodSet`, the absorption of the constants;
9. (3.3) `GijGEX`, (3.2) `GiiGEX`, (3.5) `GavLGEX` per sequence: `entry_bound_stochDom`,
   `diag_bound_stochDom` and their variants.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Green

open Matrix Finset Filter MeasureTheory RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-! ## 1. Resolvent helpers -/

section Resolvent

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `green H z * (H - z) = 1` for Hermitian `H` and `Im z ≠ 0`; the invertibility is
`isUnit_sub_smul_of_isHermitian`. -/
theorem green_mul_sub_of_im {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    green H z * (H - z • (1 : Matrix n n ℂ)) = 1 :=
  green_mul_self (Matrix.isUnit_iff_isUnit_det _ |>.mp
    (RBM.isUnit_sub_smul_of_isHermitian hH hz))

/-- `(H - z) * green H z = 1` for Hermitian `H` and `Im z ≠ 0`. -/
theorem sub_mul_green_of_im {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    (H - z • (1 : Matrix n n ℂ)) * green H z = 1 :=
  self_mul_green (Matrix.isUnit_iff_isUnit_det _ |>.mp
    (RBM.isUnit_sub_smul_of_isHermitian hH hz))

end Resolvent

/-- `Im z_t ≠ 0` for `t < 1` in the bulk, `z_t = zt E t`. -/
theorem zt_im_ne_zero {E κ t : ℝ} (hκ0 : 0 < κ) (hE : |E| ≤ 2 - κ) (ht1 : t < 1) :
    (zt E t).im ≠ 0 := by
  rw [zt_im]
  have h := mE_im_pos (E := E) (by linarith [abs_nonneg E])
  have : 0 < 1 - t := by linarith
  positivity

/-- `m = -(t m + z_t)⁻¹`, i.e. `m (t m + z_t) = -1`. -/
theorem mE_mul_add_zt {E : ℝ} (hE : |E| ≤ 2) (t : ℝ) :
    mE E * ((t : ℂ) * mE E + zt E t) = -1 := by
  have h := mE_mul hE
  rw [zt]
  linear_combination h


/-! ## 2. The profile `svar` on `Vtx d L W` -/

section Profile

variable {d L W : ℕ} (g : ℝ) [NeZero L]

omit [NeZero L] in
private theorem svar_eq_kernel (p q : Vtx d L W) :
    svar d L W g p q = ((W : ℝ) ^ d)⁻¹ * sbKernelR d L g (p.1 - q.1) := rfl

private theorem entryDom_zdistInf_neg (x : Zd d L) : zdistInf d L (-x) = zdistInf d L x := by
  unfold zdistInf
  exact Finset.sup_congr rfl fun i _ => by simp [zdist_neg]

omit [NeZero L] in
private theorem entryDom_zdistInf_zero : zdistInf d L (0 : Zd d L) = 0 := by
  unfold zdistInf
  simp

/-- The kernel of `S^(B)(g)` is at most `1`: it is non-negative and sums
to `1` (`sum_sbKernelR`, `3 ≤ L`). -/
private theorem entryDom_sbKernelR_le_one (hL : 3 ≤ L) (x : Zd d L) : sbKernelR d L g x ≤ 1 := by
  rw [← sum_sbKernelR d L g hL]
  exact Finset.single_le_sum (f := fun y => sbKernelR d L g y)
    (fun y _ => sbKernelR_nonneg d L g y) (Finset.mem_univ x)

omit [NeZero L] in
/-- The kernel of `S^(B)(g)` vanishes off the `L^∞` unit ball: its support is
`{0} ∪ {|x|_{ℓ¹} = 1}` and `zdistInf ≤ zdistD`. -/
private theorem entryDom_sbKernelR_eq_zero {x : Zd d L} (h : ¬ zdistInf d L x ≤ 1) :
    sbKernelR d L g x = 0 := by
  unfold sbKernelR
  have h0 : x ≠ 0 := fun h0 => h (by rw [h0, entryDom_zdistInf_zero]; norm_num)
  have h1 : zdistD d L x ≠ 1 := fun h1 => h ((zdistInf_le_zdistD d L x).trans h1.le)
  simp [h0, h1]

private theorem entryDom_sbKernelR_mul_mul_le (hL : 3 ≤ L) (x y : Zd d L) {n : ℝ} (hn : 0 ≤ n) :
    sbKernelR d L g x * sbKernelR d L g y * n ≤
      if zdistInf d L x ≤ 1 ∧ zdistInf d L y ≤ 1 then n else 0 := by
  have hx0 := sbKernelR_nonneg d L g x
  have hy0 := sbKernelR_nonneg d L g y
  by_cases h : zdistInf d L x ≤ 1 ∧ zdistInf d L y ≤ 1
  · rw [ite_eq_left h]
    have h1 := entryDom_sbKernelR_le_one g hL x
    have h2 := entryDom_sbKernelR_le_one g hL y
    have h3 : sbKernelR d L g x * sbKernelR d L g y ≤ 1 := by nlinarith
    calc sbKernelR d L g x * sbKernelR d L g y * n ≤ 1 * n := mul_le_mul_of_nonneg_right h3 hn
      _ = n := one_mul n
  · rw [ite_eq_right h]
    have h0 : sbKernelR d L g x * sbKernelR d L g y = 0 := by
      by_cases h1 : zdistInf d L x ≤ 1
      · have h2 : ¬ zdistInf d L y ≤ 1 := fun h2 => h ⟨h1, h2⟩
        rw [entryDom_sbKernelR_eq_zero g h2, mul_zero]
      · rw [entryDom_sbKernelR_eq_zero g h1, zero_mul]
    rw [h0, zero_mul]

private theorem entryDom_sum_sbKernelR_sub_left (hL : 3 ≤ L) (a : Zd d L) :
    ∑ b : Zd d L, sbKernelR d L g (a - b) = 1 := by
  rw [← sum_sbKernelR d L g hL]
  exact Fintype.sum_equiv (Equiv.subLeft a) _ _ fun b => rfl

private theorem entryDom_sum_sbKernelR_sub_right (hL : 3 ≤ L) (b : Zd d L) :
    ∑ a : Zd d L, sbKernelR d L g (a - b) = 1 := by
  rw [← sum_sbKernelR d L g hL]
  exact Fintype.sum_equiv (Equiv.subRight b) _ _ fun a => rfl

variable [NeZero W]

/-- Row sums of the profile are `1` (`Σ_b |S_ab| = 1`): `S = W^{-d} S^(B)`
and a block has `W^d` points. -/
theorem sum_svar_row (hL : 3 ≤ L) (p : Vtx d L W) : ∑ q, svar d L W g p q = 1 := by
  have hW : ((W : ℝ) ^ d) ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne W)
  rw [Fintype.sum_prod_type]
  simp only [svar_eq_kernel, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : ∀ b : Zd d L, ((W ^ d : ℕ) : ℝ) * (((W : ℝ) ^ d)⁻¹ * sbKernelR d L g (p.1 - b))
      = sbKernelR d L g (p.1 - b) := fun b => by
    push_cast; field_simp
  simp only [this]
  exact entryDom_sum_sbKernelR_sub_left g hL p.1

/-- Column sums of the profile are `1`. -/
theorem sum_svar_col (hL : 3 ≤ L) (q : Vtx d L W) : ∑ p, svar d L W g p q = 1 := by
  have hW : ((W : ℝ) ^ d) ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne W)
  rw [Fintype.sum_prod_type]
  simp only [svar_eq_kernel, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : ∀ a : Zd d L, ((W ^ d : ℕ) : ℝ) * (((W : ℝ) ^ d)⁻¹ * sbKernelR d L g (a - q.1))
      = sbKernelR d L g (a - q.1) := fun a => by
    push_cast; field_simp
  simp only [this]
  exact entryDom_sum_sbKernelR_sub_right g hL q.1

omit [NeZero W] in
/-- `S_{pq} ≤ W^{-d}`. -/
theorem svar_le_inv_Wd (hL : 3 ≤ L) (p q : Vtx d L W) : svar d L W g p q ≤ ((W : ℝ) ^ d)⁻¹ := by
  rw [svar_eq_kernel]
  calc ((W : ℝ) ^ d)⁻¹ * sbKernelR d L g (p.1 - q.1) ≤ ((W : ℝ) ^ d)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (entryDom_sbKernelR_le_one g hL _) (by positivity)
    _ = ((W : ℝ) ^ d)⁻¹ := mul_one _

omit [NeZero W] in
/-- `S_{pq}` vanishes unless `|[p] - [q]|_∞ ≤ 1`, where it is `≤ W^{-d}`. -/
private theorem entryDom_svar_le_ind (hL : 3 ≤ L) (p q : Vtx d L W) :
    svar d L W g p q ≤ if zdistInf d L (q.1 - p.1) ≤ 1 then ((W : ℝ) ^ d)⁻¹ else 0 := by
  split_ifs with h
  · exact svar_le_inv_Wd g hL p q
  · rw [svar_eq_kernel, entryDom_sbKernelR_eq_zero g (x := p.1 - q.1), mul_zero]
    rw [← neg_sub q.1 p.1, entryDom_zdistInf_neg]
    exact h

end Profile

/-! ## 3. The neighbour sums -/

section Loops

variable {d L W : ℕ} (g : ℝ) [NeZero L] [NeZero W] {E u : ℝ} {M : Matrix (Idx d L W) (Idx d L W) ℂ}

/-- The two-sided sum in [YY_25, (4.11)] is a weighted sum of `2`-loops: with the orientation of
`norm_loopPM_eq` (rows in block `b`, columns in block `a`),
`∑_{k,l} S_{pk}|G_{kl}|²S_{lq} = ∑_{a',b'} S^{(B)}_{[p]a'} S^{(B)}_{b'[q]} ‖𝓛_{(+,-),(b',a')}‖`,
with the `d`-dimensional blocks of `W^d` points. -/
theorem sum_sum_svar_eq (hM : M.IsHermitian) (p q : Vtx d L W) :
    ∑ k, ∑ l, svar d L W g p k * ‖greenBlk d L W E u M true k l‖ ^ 2 * svar d L W g l q
      = ∑ a' : Zd d L, ∑ b' : Zd d L,
          sbKernelR d L g (p.1 - a') * sbKernelR d L g (b' - q.1) *
            ‖loopPM d L W E u M b' a'‖ := by
  simp only [Fintype.sum_prod_type (α₁ := Zd d L) (α₂ := Fin (W ^ d))]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [norm_loopPM_eq M hM b' a', inv_pow]
  simp only [svar_eq_kernel, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  ring

private theorem entryDom_norm_loopPM_le_maxLoopPM (a b : Zd d L) :
    ‖loopPM d L W E u M a b‖ ≤ maxLoopPM d L W E u M :=
  Finset.le_sup' (fun p : Zd d L × Zd d L => ‖loopPM d L W E u M p.1 p.2‖) (Finset.mem_univ (a, b))

/-- `∑_{k,l} S_{pk}|G_{kl}|²S_{lq} ≤ max_{a,b} ‖𝓛_{(+,-),(a,b)}‖`: the rows of `S^(B)` sum to `1`. -/
theorem sum_sum_svar_le_maxLoopPM (hL : 3 ≤ L) (hM : M.IsHermitian) (p q : Vtx d L W) :
    ∑ k, ∑ l, svar d L W g p k * ‖greenBlk d L W E u M true k l‖ ^ 2 * svar d L W g l q
      ≤ maxLoopPM d L W E u M := by
  rw [sum_sum_svar_eq g hM]
  calc ∑ a' : Zd d L, ∑ b' : Zd d L,
        sbKernelR d L g (p.1 - a') * sbKernelR d L g (b' - q.1) * ‖loopPM d L W E u M b' a'‖
      ≤ ∑ a' : Zd d L, ∑ b' : Zd d L,
        sbKernelR d L g (p.1 - a') * sbKernelR d L g (b' - q.1) * maxLoopPM d L W E u M :=
        Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun b' _ =>
          mul_le_mul_of_nonneg_left (entryDom_norm_loopPM_le_maxLoopPM b' a')
            (mul_nonneg (sbKernelR_nonneg d L g _) (sbKernelR_nonneg d L g _))
    _ = (∑ a' : Zd d L, sbKernelR d L g (p.1 - a')) * (∑ b' : Zd d L, sbKernelR d L g (b' - q.1)) *
          maxLoopPM d L W E u M := by
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.sum_mul]
    _ = maxLoopPM d L W E u M := by
        rw [entryDom_sum_sbKernelR_sub_left g hL, entryDom_sum_sbKernelR_sub_right g hL]; ring

end Loops


/-! ## 4. (3.3) `GijGEX` in block form -/

section BlockForms

variable {d L W : ℕ} [NeZero L] [NeZero W] {E u : ℝ} {M : Matrix (Idx d L W) (Idx d L W) ℂ}

private theorem entryDom_greenBlk_true_eq (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) :
    greenBlk d L W E u M true = green (blockMat d L W M) (zt E u) := by
  simp only [greenBlk, Gres, green, ite_true]
  exact (Matrix.nonsing_inv_eq_ringInverse _).symm

private theorem entryDom_blockMat_isHermitian (hM : M.IsHermitian) :
    (blockMat d L W M).IsHermitian :=
  hM.submatrix _

private theorem entryDom_greenBlk_mul_sub (hM : M.IsHermitian) (hz : (zt E u).im ≠ 0) :
    greenBlk d L W E u M true * (blockMat d L W M - zt E u •
      (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1 := by
  rw [entryDom_greenBlk_true_eq]
  exact green_mul_sub_of_im (entryDom_blockMat_isHermitian hM) hz

private theorem entryDom_sub_mul_greenBlk (hM : M.IsHermitian) (hz : (zt E u).im ≠ 0) :
    (blockMat d L W M - zt E u • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) *
      greenBlk d L W E u M true = 1 := by
  rw [entryDom_greenBlk_true_eq]
  exact sub_mul_green_of_im (entryDom_blockMat_isHermitian hM) hz

/-- The block-product resolvent at block coordinates is the fine-lattice resolvent at the
`splitEquiv` coordinates (`Matrix.inv_submatrix_equiv`). -/
private theorem entryDom_greenBlk_apply (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (x y : Vtx d L W) :
    greenBlk d L W E u M true x y =
      Gres M (zt E u) true ((splitEquiv d L W).symm x) ((splitEquiv d L W).symm y) := by
  unfold greenBlk Gres blockMat
  simp only [ite_true]
  have e1 : M.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm -
        zt E u • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
      (M - zt E u • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)).submatrix (splitEquiv d L W).symm
        (splitEquiv d L W).symm := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply]
  rw [e1, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.inv_submatrix_equiv]
  rfl

private theorem entryDom_sbKernelR_sub_comm (a b : Zd d L) (g : ℝ) :
    sbKernelR d L g (a - b) = sbKernelR d L g (b - a) := by
  rw [← neg_sub b a, sbKernelR_neg]

/-- The double sum is bounded by the double sum of `gexRHS … [q] [p]` (the swapped pair): each
`S^{(B)}` factor is `≤ 1` and vanishes off the `L^∞` ball `|·|_L ≤ 1` (`gexRHS` of
`Green/Pins.lean`; `{0} ∪ {|x|_{ℓ¹} = 1} ⊂ {|x|_∞ ≤ 1}`). -/
private theorem entryDom_sum_sum_svar_le_gexRHS (g : ℝ) (hL : 3 ≤ L) (hM : M.IsHermitian)
    (p q : Vtx d L W) :
    ∑ k, ∑ l, svar d L W g p k * ‖greenBlk d L W E u M true k l‖ ^ 2 * svar d L W g l q
      ≤ ∑ a' : Zd d L, ∑ b' : Zd d L,
          if zdistInf d L (a' - q.1) ≤ 1 ∧ zdistInf d L (b' - p.1) ≤ 1
          then ‖loopPM d L W E u M a' b'‖ else 0 := by
  rw [sum_sum_svar_eq g hM, Finset.sum_comm]
  refine Finset.sum_le_sum fun b' _ => Finset.sum_le_sum fun a' _ => ?_
  have h := entryDom_sbKernelR_mul_mul_le g hL (b' - q.1) (a' - p.1)
    (norm_nonneg (loopPM d L W E u M b' a'))
  rw [entryDom_sbKernelR_sub_comm p.1 a' g]
  calc _ = sbKernelR d L g (b' - q.1) * sbKernelR d L g (a' - p.1) *
        ‖loopPM d L W E u M b' a'‖ := by ring
    _ ≤ _ := h

/-- **(3.3) `GijGEX`**, deterministic block form (the two-sided bound of `norm_sq_green_le_two_sided` with
`S = svar`): on the good event, for all `p, q` in the block-product index,
`|G_{pq}|² ≤ 81 Φ² · gexRHS … [q] [p]` (the swapped pair; the left side is `0` on the
diagonal), with constant `81` (`S^{(B)} ≤ 1`), the profile `svar d L W g` and the right side with
`zdistInf ≤ 1`.  The left side is written out because `offSq` lives on the fine lattice (see
`offSq_le_gexRHS_fine`). -/
theorem offSq_le_gexRHS_blk (hL : 3 ≤ L) (hM : M.IsHermitian) (hE : |E| ≤ 2)
    (hz : (zt E u).im ≠ 0) {δ : ℝ}
    (hΩ : GoodEvent (greenBlk d L W E u M true) (mE E) δ) (hδ : δ ≤ 1 / 2) {Φ : ℝ}
    (hΦ1 : 1 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) {g : ℝ}
    (hLrow : LDERow (blockMat d L W M) (greenBlk d L W E u M true) (svar d L W g) Φ)
    (hLcol : LDECol (blockMat d L W M) (greenBlk d L W E u M true) (svar d L W g) Φ)
    (p q : Vtx d L W) :
    (if p = q then 0 else ‖greenBlk d L W E u M true p q‖ ^ 2) ≤
      81 * Φ ^ 2 * gexRHS d L W E u M q.1 p.1 := by
  by_cases hpq : p = q
  · simp only [hpq, ite_true]
    exact mul_nonneg (by positivity) (gexRHS_nonneg E u M _ _)
  · simp only [ite_eq_right hpq]
    have hm := norm_mE hE
    have h := norm_sq_green_le_two_sided (entryDom_greenBlk_mul_sub hM hz)
      (entryDom_sub_mul_greenBlk hM hz) hm hΩ hδ (fun i k => svar_nonneg d L W g i k)
      (fun i => (sum_svar_row g hL i).le) (fun j => (sum_svar_col g hL j).le) hΦ1 hΦδ hLrow hLcol
      hpq
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact add_le_add (entryDom_sum_sum_svar_le_gexRHS g hL hM p q) (entryDom_svar_le_ind g hL p q)

/-- **(3.3) `GijGEX` on the fine lattice**: the form of `offSq` (entries of `Gres M z true` at
`Z_{WL}^d`), from `offSq_le_gexRHS_blk` through `splitEquiv`:
`offSq p q ≤ 81 Φ² gexRHS … [q] [p]`, `[x] = (split x).1`. -/
theorem offSq_le_gexRHS_fine (hL : 3 ≤ L) (hM : M.IsHermitian) (hE : |E| ≤ 2)
    (hz : (zt E u).im ≠ 0) {δ : ℝ}
    (hΩ : GoodEvent (greenBlk d L W E u M true) (mE E) δ) (hδ : δ ≤ 1 / 2) {Φ : ℝ}
    (hΦ1 : 1 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) {g : ℝ}
    (hLrow : LDERow (blockMat d L W M) (greenBlk d L W E u M true) (svar d L W g) Φ)
    (hLcol : LDECol (blockMat d L W M) (greenBlk d L W E u M true) (svar d L W g) Φ)
    (p q : Idx d L W) :
    offSq d L W E u M p q ≤
      81 * Φ ^ 2 * gexRHS d L W E u M (split d L W q).1 (split d L W p).1 := by
  have h := offSq_le_gexRHS_blk hL hM hE hz hΩ hδ hΦ1 hΦδ hLrow hLcol (splitEquiv d L W p)
    (splitEquiv d L W q)
  rw [entryDom_greenBlk_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at h
  unfold offSq
  have hiff : splitEquiv d L W p = splitEquiv d L W q ↔ p = q := (splitEquiv d L W).injective.eq_iff
  by_cases hpq : p = q
  · simp only [hpq, ite_true] at h ⊢
    exact h
  · have hne : ¬ splitEquiv d L W p = splitEquiv d L W q := fun h' => hpq (hiff.1 h')
    simp only [hpq, hne, ite_false] at h ⊢
    exact h

/-! ## 5. Lower bounds on `maxLoopPM` -/

/-- On the good event, `W^{-d} ≤ 4 max_{a,b} ‖𝓛_{(+,-),(a,b)}‖`: the diagonal entries alone
contribute `≥ W^{-d}/4` to `𝓛_{(+,-),(0,0)}`; the block fibre is `Fin (W^d)`. -/
theorem inv_Wd_le_maxLoopPM (hM : M.IsHermitian) (hE : |E| ≤ 2) {δ : ℝ}
    (hΩ : GoodEvent (greenBlk d L W E u M true) (mE E) δ) (hδ : δ ≤ 1 / 2) :
    ((W : ℝ) ^ d)⁻¹ ≤ 4 * maxLoopPM d L W E u M := by
  have hm := norm_mE hE
  have hW : (0 : ℝ) < (W : ℝ) ^ d := by
    have : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
    positivity
  have h1 : ((W : ℝ) ^ d)⁻¹ / 4 ≤ ‖loopPM d L W E u M 0 0‖ := by
    rw [norm_loopPM_eq M hM 0 0, inv_pow]
    have hdiag : ∀ β : Fin (W ^ d), (1 : ℝ) / 4 ≤
        ∑ α : Fin (W ^ d), ‖greenBlk d L W E u M true ((0 : Zd d L), β) (0, α)‖ ^ 2 := by
      intro β
      have h2 := hΩ.half_le_norm_diag hm hδ ((0 : Zd d L), β)
      have h3 : (1 : ℝ) / 4 ≤ ‖greenBlk d L W E u M true ((0 : Zd d L), β) (0, β)‖ ^ 2 := by
        nlinarith
      exact h3.trans (Finset.single_le_sum
        (f := fun α => ‖greenBlk d L W E u M true ((0 : Zd d L), β) (0, α)‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ β))
    have h4 : ((W : ℝ) ^ d) * (1 / 4) ≤ ∑ β : Fin (W ^ d), ∑ α : Fin (W ^ d),
        ‖greenBlk d L W E u M true ((0 : Zd d L), β) (0, α)‖ ^ 2 := by
      calc ((W : ℝ) ^ d) * (1 / 4) = ∑ _β : Fin (W ^ d), (1 : ℝ) / 4 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast; ring
        _ ≤ _ := Finset.sum_le_sum fun β _ => hdiag β
    calc ((W : ℝ) ^ d)⁻¹ / 4 = (((W : ℝ) ^ d)⁻¹) ^ 2 * (((W : ℝ) ^ d) * (1 / 4)) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)
  have h5 := entryDom_norm_loopPM_le_maxLoopPM (E := E) (u := u) (M := M) (0 : Zd d L) 0
  linarith

/-- On the good event, `S_{pq} ≤ W^{-d} ≤ 4 max_{a,b} ‖𝓛_{(+,-),(a,b)}‖`: the profile `S^{(B)}(g)`
is `≤ 1` and its entries tend to `1` as `g → 0`, so from `W^{-d} ≤ 4 maxLoopPM` the constant
is `4`. -/
theorem svar_le_maxLoopPM (hL : 3 ≤ L) (hM : M.IsHermitian) (hE : |E| ≤ 2) {δ : ℝ}
    (hΩ : GoodEvent (greenBlk d L W E u M true) (mE E) δ) (hδ : δ ≤ 1 / 2) (g : ℝ)
    (p q : Vtx d L W) : svar d L W g p q ≤ 4 * maxLoopPM d L W E u M :=
  (svar_le_inv_Wd g hL p q).trans (inv_Wd_le_maxLoopPM hM hE hΩ hδ)

/-! ## 6. (3.2) `GiiGEX` in block form -/

/-- **(3.2) `GiiGEX`**, deterministic block form: on the good event, given the LDE inputs and the absorption
`Kstab3 d Λ κ · δ ≤ 1/2`,
`|G_{pp} - m|² ≤ 2160 · Kstab3 ^ 2 · Φ² · (4 max_{a,b} ‖𝓛_{(+,-),(a,b)}‖)`: the stability
constant is `Kstab3 d Λ κ` (`stable_svar_bulk_vtx`, hypotheses `3 ≤ d`, `0 < g ≤ Λ`), which does
not depend on `L`, and the loop bound is `Λ' = 4 maxLoopPM`.  The left side is `‖G_{pp} - m‖²`,
i.e. `diagSq` on the block-product index. -/
theorem diagSq_le_maxLoopPM_blk (hd : 3 ≤ d) (hL : 3 ≤ L) (hM : M.IsHermitian) {g Λ κ : ℝ}
    (hg : 0 < g) (hgΛ : g ≤ Λ) (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) (hu0 : 0 ≤ u) (hu1 : u < 1) {δ : ℝ}
    (hΩ : GoodEvent (greenBlk d L W E u M true) (mE E) δ) (hδ : δ ≤ 1 / 2) {Φ : ℝ}
    (hΦ1 : 1 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hKδ : Kstab3 d Λ κ * δ ≤ 1 / 2)
    (hLrow : LDERow (blockMat d L W M) (greenBlk d L W E u M true) (svar d L W g) Φ)
    (hLcol : LDECol (blockMat d L W M) (greenBlk d L W E u M true) (svar d L W g) Φ)
    (hLquad : LDEQuad (blockMat d L W M) (greenBlk d L W E u M true) (svar d L W g) u Φ)
    (hLdiag : ∀ i, ‖blockMat d L W M i i‖ ^ 2 ≤ Φ * svar d L W g i i) (p : Vtx d L W) :
    ‖greenBlk d L W E u M true p p - mE E‖ ^ 2 ≤
      2160 * Kstab3 d Λ κ ^ 2 * Φ ^ 2 * (4 * maxLoopPM d L W E u M) := by
  have hE2 : |E| ≤ 2 := le_trans hE (by linarith)
  have hz := zt_im_ne_zero hκ hE hu1
  have hm := norm_mE hE2
  have hL0 := maxLoopPM_nonneg (d := d) (L := L) (W := W) E u M
  exact norm_sq_green_diag_sub_le (entryDom_greenBlk_mul_sub hM hz) (entryDom_sub_mul_greenBlk hM hz)
    hm (mE_mul_add_zt hE2 u) hu0 hu1.le hΩ hδ (fun i k => svar_nonneg d L W g i k)
    (sum_svar_row g hL) (fun j => (sum_svar_col g hL j).le) hΦ1 hΦδ hLrow hLcol hLquad hLdiag
    (Λ := 4 * maxLoopPM d L W E u M)
    (fun i j => (sum_sum_svar_le_maxLoopPM g hL hM i j).trans (by linarith))
    (svar_le_maxLoopPM hL hM hE2 hΩ hδ g) hKδ (stable_svar_bulk_vtx hd hL hg hgΛ hκ hE hu0 hu1) p

/-- **(3.2) `GiiGEX` on the fine lattice**: `diagSq` of `Green/Pins.lean` (entries of
`Gres M z true`), from `diagSq_le_maxLoopPM_blk` through `splitEquiv`. -/
theorem diagSq_le_maxLoopPM_fine (hd : 3 ≤ d) (hL : 3 ≤ L) (hM : M.IsHermitian) {g Λ κ : ℝ}
    (hg : 0 < g) (hgΛ : g ≤ Λ) (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) (hu0 : 0 ≤ u) (hu1 : u < 1) {δ : ℝ}
    (hΩ : GoodEvent (greenBlk d L W E u M true) (mE E) δ) (hδ : δ ≤ 1 / 2) {Φ : ℝ}
    (hΦ1 : 1 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hKδ : Kstab3 d Λ κ * δ ≤ 1 / 2)
    (hLrow : LDERow (blockMat d L W M) (greenBlk d L W E u M true) (svar d L W g) Φ)
    (hLcol : LDECol (blockMat d L W M) (greenBlk d L W E u M true) (svar d L W g) Φ)
    (hLquad : LDEQuad (blockMat d L W M) (greenBlk d L W E u M true) (svar d L W g) u Φ)
    (hLdiag : ∀ i, ‖blockMat d L W M i i‖ ^ 2 ≤ Φ * svar d L W g i i) (p : Idx d L W) :
    diagSq d L W E u M p ≤ 2160 * Kstab3 d Λ κ ^ 2 * Φ ^ 2 * (4 * maxLoopPM d L W E u M) := by
  have h := diagSq_le_maxLoopPM_blk hd hL hM hg hgΛ hκ hE hu0 hu1 hΩ hδ hΦ1 hΦδ hKδ hLrow hLcol
    hLquad hLdiag (splitEquiv d L W p)
  rw [entryDom_greenBlk_apply, Equiv.symm_apply_apply] at h
  exact h

end BlockForms

/-! ## 7. (3.5) `GavLGEX`: the coefficients `W^{-d} 1(k ∈ 𝓘_a)` and the bound -/

section Coef

variable {d L W : ℕ}

/-- The coefficients `c_k = W^{-d} 1(k ∈ 𝓘_a)` used for (3.5) `GavLGEX`: the entries of `E_a`
((2.44) `Eq:defGLoop`; `Eblk`), block weight `W^{-d}`. -/
noncomputable def blkCoef2 (d L W : ℕ) (a : Zd d L) (k : Vtx d L W) : ℝ :=
  if k.1 = a then ((W : ℝ) ^ d)⁻¹ else 0

/-- The weights sum to `1`: a block has `W^d` sites of weight `W^{-d}`. -/
theorem sum_abs_blkCoef2 [NeZero L] [NeZero W] (a : Zd d L) : ∑ k, |blkCoef2 d L W a k| = 1 := by
  have hW : ((W : ℝ) ^ d) ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne W)
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp only [blkCoef2, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [abs_of_nonneg (by positivity)]
    push_cast
    field_simp
  · intro b _ hb
    simp [blkCoef2, hb]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- `⟨(G - m) E_a⟩ = ∑_k c_k (G_{kk} - m)` with `c_k = W^{-d} 1(k ∈ 𝓘_a)`. -/
theorem trace_sub_mul_Eblk2 [NeZero L] [NeZero W] (G : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (m : ℂ) (a : Zd d L) :
    Matrix.trace ((G - m • (1 : Matrix _ _ ℂ)) * Eblk d L W a)
      = ∑ k, (blkCoef2 d L W a k : ℂ) * (G k k - m) := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, Eblk, Matrix.mul_diagonal, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply_eq, smul_eq_mul, mul_one, blkCoef2]
  split_ifs <;> push_cast <;> ring

/-- `avgErr` at the sign `+` is the trace form of (3.5) `GavLGEX` (`mSigma E true = m`). -/
private theorem entryDom_avgErr_true_eq_trace [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (a : Zd d L) :
    avgErr d L W E u M true a
      = Matrix.trace ((greenBlk d L W E u M true - mE E • (1 : Matrix _ _ ℂ)) *
          Eblk d L W a) := by
  simp [avgErr, mSigma]

variable [NeZero L] [NeZero W]

/-- **(3.5) `GavLGEX`**, deterministic block form.  With `x_k` standing for `E_k(G_{kk} - m)`: if
`x_i = t m² ∑_k S_{ik} (G_{kk} - m) + O(A)` and the fluctuation averaging holds with error `B` for
the weights `S_{ik}` and `B'` for the weights `c_k = W^{-d} 1(k ∈ 𝓘_a)`, then
`|⟨(G - m)E_a⟩| ≤ B' + Kstab3 d Λ κ · (A + B)`, with the `L`-free stability constant `Kstab3 d Λ κ`
(`stable_svar_bulk_vtx`; hypotheses `3 ≤ d`, `0 < g ≤ Λ`). -/
theorem norm_trace_green_sub_mul_Eblk2_le (hd : 3 ≤ d) (hL : 3 ≤ L) {g Λ : ℝ} (hg : 0 < g)
    (hgΛ : g ≤ Λ) {E κ t : ℝ} (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (x : Vtx d L W → ℂ) {A B B' : ℝ}
    (hIBP : ∀ i, ‖x i - (t : ℂ) * mE E ^ 2 *
      ∑ k, (svar d L W g i k : ℂ) * (G k k - mE E)‖ ≤ A)
    (hFA : ∀ i, ‖∑ k, (svar d L W g i k : ℂ) * ((G k k - mE E) - x k)‖ ≤ B) (a : Zd d L)
    (hFA' : ‖∑ k, (blkCoef2 d L W a k : ℂ) * ((G k k - mE E) - x k)‖ ≤ B') :
    ‖Matrix.trace ((G - mE E • (1 : Matrix _ _ ℂ)) * Eblk d L W a)‖
      ≤ B' + Kstab3 d Λ κ * (A + B) := by
  have hE2 : |E| ≤ 2 := le_trans hE (by linarith)
  have hξ : ‖(t : ℂ) * mE E ^ 2‖ ≤ 1 := by
    rw [norm_mul, norm_pow, norm_mE hE2, Complex.norm_real, Real.norm_of_nonneg ht0,
      one_pow, mul_one]
    exact ht1.le
  rw [trace_sub_mul_Eblk2]
  exact norm_sum_coef_green_sub_le hξ (stable_svar_bulk_vtx hd hL hg hgΛ hκ hE ht0 ht1) x hIBP hFA
    (sum_abs_blkCoef2 a).le hFA'

/-- **`norm_avgErr_le`, the `avgErr` form of (3.5) `GavLGEX`**: the same bound for
`avgErr d L W E u M true a`, with `G = greenBlk d L W E u M true`,
`‖avgErr‖ ≤ B' + Kstab3 d Λ κ · (A + B)`. -/
theorem norm_avgErr_le (hd : 3 ≤ d) (hL : 3 ≤ L) {g Λ : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ)
    {E κ u : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (hu0 : 0 ≤ u)
    (hu1 : u < 1) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (x : Vtx d L W → ℂ) {A B B' : ℝ}
    (hIBP : ∀ i, ‖x i - (u : ℂ) * mE E ^ 2 *
      ∑ k, (svar d L W g i k : ℂ) * (greenBlk d L W E u M true k k - mE E)‖ ≤ A)
    (hFA : ∀ i, ‖∑ k, (svar d L W g i k : ℂ) *
      ((greenBlk d L W E u M true k k - mE E) - x k)‖ ≤ B) (a : Zd d L)
    (hFA' : ‖∑ k, (blkCoef2 d L W a k : ℂ) *
      ((greenBlk d L W E u M true k k - mE E) - x k)‖ ≤ B') :
    ‖avgErr d L W E u M true a‖ ≤ B' + Kstab3 d Λ κ * (A + B) := by
  rw [entryDom_avgErr_true_eq_trace]
  exact norm_trace_green_sub_mul_Eblk2_le hd hL hg hgΛ hκ hE hu0 hu1 (greenBlk d L W E u M true) x
    hIBP hFA a hFA'

end Coef


/-! ## 8. The engine `of_det`, bookkeeping, the good event -/

section Engine

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U : ℕ → Type*}

/-- **From a deterministic implication to `≺`.**  `Ξ l Φ` is the event that
all the input bounds hold with the factor `Φ`; it holds with high probability at `Φ = (size l)^{τ'}`
for every `τ' > 0`.  The constant is a sequence `C l ≤ (size l)^ε` (at `d ≥ 3` it contains the
`n`-independent `Kstab3`), and the requirement `δ ≤ ε₀` is absorbed into `hdet`. -/
theorem of_det (hsize : Tendsto size atTop atTop) {ξ ζ : ∀ l, U l → Ω → ℝ}
    (hζ : ∀ l u ω, 0 ≤ ζ l u ω) {Ξ : ℕ → ℝ → Set Ω}
    (hΞ : ∀ τ' > (0 : ℝ), HighProbAt P size (fun l => Ξ l ((size l : ℝ) ^ τ')))
    {δ C : ℕ → ℝ} (hδ0 : ∀ l, 0 ≤ δ l) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδ : ∀ᶠ l : ℕ in atTop, δ l ≤ (size l : ℝ) ^ (-c₀))
    (hC : ∀ ε > (0 : ℝ), ∀ᶠ l : ℕ in atTop, C l ≤ (size l : ℝ) ^ ε) (k : ℕ)
    (hdet : ∀ᶠ l : ℕ in atTop, ∀ ω (Φ : ℝ), 1 ≤ Φ → 36 * Φ * δ l ^ 2 ≤ 1 → ω ∈ Ξ l Φ →
      ∀ u, ξ l u ω ≤ C l * Φ ^ k * ζ l u ω) :
    PerTimeDomAt P size ξ ζ := by
  intro τ hτ D hD
  have hk0 : (0 : ℝ) < 2 * ((k : ℝ) + 1) := by positivity
  obtain ⟨τ', hτ'⟩ : ∃ τ', τ' = min (τ / (2 * ((k : ℝ) + 1))) c₀ := ⟨_, rfl⟩
  have hτ'0 : 0 < τ' := hτ' ▸ lt_min (div_pos hτ hk0) hc₀
  have hτ'c : τ' ≤ c₀ := hτ' ▸ min_le_right _ _
  have hτ'k : τ' * k ≤ τ / 2 := by
    have h1 : τ' ≤ τ / (2 * ((k : ℝ) + 1)) := hτ' ▸ min_le_left _ _
    have h2 : τ' * (2 * ((k : ℝ) + 1)) ≤ τ := by rwa [le_div_iff₀ hk0] at h1
    nlinarith [hτ'0]
  filter_upwards [hΞ τ' hτ'0 D hD, hsize.eventually (eventually_ge_atTop 1), hδ,
    hsize.eventually (eventually_le_rpow 36 hc₀), hC (τ / 2) (half_pos hτ), hdet] with
    l hP hN1 hδl h36 hCl hdetl u
  refine (measure_mono ?_).trans hP
  have hN : (1 : ℝ) ≤ (size l : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (size l : ℝ) := by linarith
  have hNc : 0 < (size l : ℝ) ^ c₀ := Real.rpow_pos_of_pos hN0 c₀
  have hNneg : (size l : ℝ) ^ (-c₀) = ((size l : ℝ) ^ c₀)⁻¹ := Real.rpow_neg hN0.le c₀
  intro ω hω hmem
  have hω' : (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω := hω
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = (size l : ℝ) ^ τ' := ⟨_, rfl⟩
  have hΦ1 : 1 ≤ Φ := hΦ ▸ Real.one_le_rpow hN hτ'0.le
  have hΦc : Φ ≤ (size l : ℝ) ^ c₀ := hΦ ▸ Real.rpow_le_rpow_of_exponent_le hN hτ'c
  have hΦδ : 36 * Φ * δ l ^ 2 ≤ 1 := by
    have h1 : δ l ^ 2 ≤ ((size l : ℝ) ^ (-c₀)) ^ 2 := pow_le_pow_left₀ (hδ0 l) hδl 2
    have h2 : Φ * ((size l : ℝ) ^ (-c₀)) ^ 2 ≤ (size l : ℝ) ^ (-c₀) := by
      rw [hNneg]
      have h3 : Φ * ((size l : ℝ) ^ c₀)⁻¹ ≤ 1 := by
        rw [mul_inv_le_iff₀ hNc, one_mul]; exact hΦc
      calc Φ * (((size l : ℝ) ^ c₀)⁻¹) ^ 2
          = (Φ * ((size l : ℝ) ^ c₀)⁻¹) * ((size l : ℝ) ^ c₀)⁻¹ := by ring
        _ ≤ 1 * ((size l : ℝ) ^ c₀)⁻¹ := mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = ((size l : ℝ) ^ c₀)⁻¹ := one_mul _
    have h4 : 36 * (size l : ℝ) ^ (-c₀) ≤ 1 := by
      rw [hNneg, ← div_eq_mul_inv, div_le_one hNc]; exact h36
    have h5 : 0 ≤ Φ := by linarith
    calc 36 * Φ * δ l ^ 2 ≤ 36 * (Φ * ((size l : ℝ) ^ (-c₀)) ^ 2) := by
          have := mul_le_mul_of_nonneg_left h1 h5
          linarith
      _ ≤ 36 * (size l : ℝ) ^ (-c₀) := by linarith
      _ ≤ 1 := h4
  have hmem' : ω ∈ Ξ l Φ := hΦ ▸ hmem
  have hbound := hdetl ω Φ hΦ1 hΦδ hmem' u
  have hΦk : Φ ^ k ≤ (size l : ℝ) ^ (τ / 2) := by
    rw [hΦ, ← Real.rpow_mul_natCast hN0.le]
    exact Real.rpow_le_rpow_of_exponent_le hN hτ'k
  have hζu := hζ l u ω
  have hΦk0 : 0 ≤ Φ ^ k := pow_nonneg (by linarith) k
  have hfin : C l * Φ ^ k * ζ l u ω ≤ (size l : ℝ) ^ τ * ζ l u ω := by
    have e1 : C l * Φ ^ k * ζ l u ω ≤ (size l : ℝ) ^ (τ / 2) * (Φ ^ k * ζ l u ω) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right hCl (mul_nonneg hΦk0 hζu)
    have e2 : (size l : ℝ) ^ (τ / 2) * (Φ ^ k * ζ l u ω)
        ≤ (size l : ℝ) ^ (τ / 2) * ((size l : ℝ) ^ (τ / 2) * ζ l u ω) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΦk hζu)
        (Real.rpow_nonneg hN0.le _)
    have e3 : (size l : ℝ) ^ (τ / 2) * ((size l : ℝ) ^ (τ / 2) * ζ l u ω)
        = (size l : ℝ) ^ τ * ζ l u ω := by
      rw [← mul_assoc, ← Real.rpow_add hN0]
      congr 2
      ring
    linarith
  linarith

end Engine

/-- Ordered pairs of distinct block-product indices `Vtx d L W = Z_L^d × Fin (W^d)`. -/
abbrev OffPair (d L W : ℕ) : Type := {p : Vtx d L W × Vtx d L W // p.1 ≠ p.2}

section Bookkeeping

variable {d : ℕ} (sz : Sizes d)

/-- The event `Ω(t,c)_n = {‖G_t - m‖_max ≤ W^{-c}}` of (3.1) `def_asGMc` at size index `n`; the
indicator `omegaInd` is its indicator.  (The event is stated on the fine lattice `Z_{WL}^d`,
through `llErrMat`, because that is the form of `omegaInd` and `AsGMcSeq`.) -/
def goodSet {d : ℕ} (sz : Sizes d) (E t : ℕ → ℝ) (c : ℝ) (n : ℕ) : Set sz.SeqΩ :=
  {ω | ∀ i j : Idx d (sz.L n) (sz.W n),
    llErrMat d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) i j ≤
      ((sz.W n : ℕ) : ℝ) ^ (-c)}

private theorem entryDom_omegaInd_of_forall {L W : ℕ} [NeZero L] [NeZero W] {E u c : ℝ}
    {M : Matrix (Idx d L W) (Idx d L W) ℂ}
    (h : ∀ i j : Idx d L W, llErrMat d L W E u M i j ≤ ((W : ℕ) : ℝ) ^ (-c)) :
    omegaInd d L W E u c M = 1 := by
  simp [omegaInd, h]

private theorem entryDom_omegaInd_of_not {L W : ℕ} [NeZero L] [NeZero W] {E u c : ℝ}
    {M : Matrix (Idx d L W) (Idx d L W) ℂ}
    (h : ¬ ∀ i j : Idx d L W, llErrMat d L W E u M i j ≤ ((W : ℕ) : ℝ) ^ (-c)) :
    omegaInd d L W E u c M = 0 := by
  simp only [omegaInd, h, ↓reduceIte]

/-- `omegaInd · f` is the indicator of `goodSet` times `f`. -/
theorem entryDom_omegaInd_mul_eq_indicator (E t : ℕ → ℝ) (c : ℝ) (n : ℕ) (ω : sz.SeqΩ)
    (f : sz.SeqΩ → ℝ) :
    omegaInd d (sz.L n) (sz.W n) (E n) (t n) c (sz.seqHflow n (t n) ω) * f ω =
      (goodSet sz E t c n).indicator f ω := by
  by_cases h : ω ∈ goodSet sz E t c n
  · rw [Set.indicator_of_mem h]
    have h' : ∀ i j : Idx d (sz.L n) (sz.W n),
        llErrMat d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) i j ≤
          ((sz.W n : ℕ) : ℝ) ^ (-c) := h
    rw [entryDom_omegaInd_of_forall h', one_mul]
  · rw [Set.indicator_of_notMem h]
    have h' : ¬ ∀ i j : Idx d (sz.L n) (sz.W n),
        llErrMat d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) i j ≤
          ((sz.W n : ℕ) : ℝ) ^ (-c) := h
    rw [entryDom_omegaInd_of_not h', zero_mul]

private theorem entryDom_tendsto_size_of (hsz : sz.SizeTendsto) : Tendsto sz.size atTop atTop :=
  tendsto_natCast_atTop_iff.mp hsz

private theorem entryDom_card_vtx (n : ℕ) :
    Fintype.card (Vtx d (sz.L n) (sz.W n)) = sz.size n := by
  rw [Fintype.card_congr (splitEquiv d (sz.L n) (sz.W n)).symm, sz.card_Idx]

private theorem entryDom_card_offPair_le (n : ℕ) :
    Fintype.card (OffPair d (sz.L n) (sz.W n)) ≤ sz.size n ^ 2 := by
  calc Fintype.card (OffPair d (sz.L n) (sz.W n))
      ≤ Fintype.card (Vtx d (sz.L n) (sz.W n) × Vtx d (sz.L n) (sz.W n)) :=
        Fintype.card_subtype_le _
    _ = sz.size n ^ 2 := by rw [Fintype.card_prod, entryDom_card_vtx, sq]

private theorem entryDom_card_idx_sq (n : ℕ) :
    Fintype.card (Unit × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) ≤ sz.size n ^ 2 := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_unit, sz.card_Idx, one_mul, sq]

private theorem entryDom_card_real_le {V : ℕ → Type*} [∀ n, Fintype (V n)] {m : ℕ}
    (h : ∀ n, Fintype.card (V n) ≤ sz.size n ^ m) (n : ℕ) :
    (Fintype.card (V n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (m : ℝ) := by
  rw [Real.rpow_natCast]; exact_mod_cast h n

/-- The grid union bound in the form used here: a per-time bound over an index set of size at most
`size^m` gives an event of high probability (`stochDomAt_of_perTimeDomAt`,
`perTimeCalc_highProbAt_of_stochDomAt`). -/
private theorem entryDom_highProb_of_perTime {V : ℕ → Type*} [∀ n, Fintype (V n)] {m : ℕ}
    (hV : ∀ n, Fintype.card (V n) ≤ sz.size n ^ m)
    {ξ ζ : ∀ n, V n → sz.SeqΩ → ℝ} (h : sz.PrecPT ξ ζ) {τ : ℝ} (hτ : 0 < τ) :
    HighProbAt (seqP sz) sz.size
      (fun n => {ω | ∀ v, ξ n v ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ n v ω}) :=
  RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_of_stochDomAt
    (stochDomAt_of_perTimeDomAt (seqP sz) sz.size (C := (m : ℝ)) (Nat.cast_nonneg m)
      (Eventually.of_forall (entryDom_card_real_le sz hV)) h) hτ

/-- `W^{-c} ≤ (size)^{-(𝔠 c)}` eventually (`Bandwidth`). -/
private theorem entryDom_W_rpow_neg_le {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-c) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(𝔠 * c)) := by
  obtain ⟨_, _, hsz, hbw, _⟩ := hA
  filter_upwards [hbw, hsz.eventually_gt_atTop 0] with n hn hN0
  have hNp : 0 < ((sz.size n : ℕ) : ℝ) ^ 𝔠 := Real.rpow_pos_of_pos hN0 _
  calc ((sz.W n : ℕ) : ℝ) ^ (-c) ≤ (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (-c) :=
        Real.rpow_le_rpow_of_nonpos hNp hn (by linarith)
    _ = ((sz.size n : ℕ) : ℝ) ^ (𝔠 * -c) := (Real.rpow_mul hN0.le _ _).symm
    _ = ((sz.size n : ℕ) : ℝ) ^ (-(𝔠 * c)) := by rw [mul_neg]

/-- (2.10) `eq:WO` gives `0 < lam n ≤ 𝔡⁻¹` eventually: the coupling window `Λ = 𝔡⁻¹` of `Kstab3`. -/
private theorem entryDom_lam_window {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) :
    ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
  obtain ⟨_, _, _, _, hWO⟩ := hA
  filter_upwards [hWO] with n hn
  have hWpos : (0 : ℝ) < (sz.W n : ℝ) := by exact_mod_cast sz.W_pos n
  exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hn.1, hn.2⟩

private theorem entryDom_delta_le_half {Φ δ : ℝ} (hδ0 : 0 ≤ δ) (hΦ1 : 1 ≤ Φ)
    (h : 36 * Φ * δ ^ 2 ≤ 1) : δ ≤ 1 / 2 := by
  by_contra hcon
  have hcon := lt_of_not_ge hcon
  nlinarith [sq_nonneg δ, mul_nonneg (sub_nonneg.2 hΦ1) (sq_nonneg δ)]

/-- `C ≤ (size)^ε` eventually, for a constant `C` and every `ε > 0` (`size → ∞`): at `d ≥ 3` the
constants `8640 K²` and `1 + 2K`, `K = Kstab3 d 𝔡⁻¹ κ`, do not depend on `n`. -/
private theorem entryDom_const_le_rpow (hsz : sz.SizeTendsto) (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, C ≤ ((sz.size n : ℕ) : ℝ) ^ ε :=
  (entryDom_tendsto_size_of sz hsz).eventually (eventually_le_rpow C hε)

/-- Deterministic bridge: `‖G_u - m‖_max ≤ δ` on the fine lattice (`llErrMat`) is the `GoodEvent`
of the block-level resolvent `greenBlk` (`greenBlk = (blockMat M - z)⁻¹` is the fine-lattice
resolvent relabelled by `splitEquiv`, `Matrix.inv_submatrix_equiv`). -/
theorem entryDom_goodEvent_of_llErr (d L W : ℕ) [NeZero L] [NeZero W] (E u δ : ℝ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (h : ∀ i j, llErrMat d L W E u M i j ≤ δ) :
    GoodEvent (greenBlk d L W E u M true) (mE E) δ := by
  intro x y
  rw [entryDom_greenBlk_apply]
  have h2 := h ((splitEquiv d L W).symm x) ((splitEquiv d L W).symm y)
  unfold llErrMat at h2
  by_cases hxy : x = y
  · subst hxy; simpa using h2
  · have hxy' : (splitEquiv d L W).symm x ≠ (splitEquiv d L W).symm y :=
      fun h3 => hxy ((splitEquiv d L W).symm.injective h3)
    simpa [hxy, hxy'] using h2

/-- `AsGMcSeq sz E t c` gives `Ω(t, c/2)` with high probability (grid union bound over the `N²`
pairs of the fine lattice, then `size^{𝔠c/2} ≤ W^{c/2}` by `Bandwidth`). -/
theorem entryDom_goodSet_highProb_of_asGMc {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {E t : ℕ → ℝ}
    {c : ℝ} (hc : 0 < c) (hAs : AsGMcSeq sz E t c) :
    HighProbAt (seqP sz) sz.size (goodSet sz E t (c / 2)) := by
  obtain ⟨h𝔠, _, hsz, hbw, _⟩ := hA
  have h1 := entryDom_highProb_of_perTime sz (m := 2) (entryDom_card_idx_sq sz) hAs
    (τ := 𝔠 * c / 2) (by positivity)
  refine RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono h1 ?_
  filter_upwards [hbw, hsz.eventually_gt_atTop 0] with n hn hN0 ω hω i j
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := hN0
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hNW : ((sz.size n : ℕ) : ℝ) ^ (𝔠 * c / 2) ≤ ((sz.W n : ℕ) : ℝ) ^ (c / 2) := by
    calc ((sz.size n : ℕ) : ℝ) ^ (𝔠 * c / 2) = (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (c / 2) := by
          rw [← Real.rpow_mul hN.le]; congr 1; ring
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ (c / 2) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hN.le _) hn (by positivity)
  have h2 := hω ((), i, j)
  calc llErrMat d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) i j
      ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * c / 2) * ((sz.W n : ℕ) : ℝ) ^ (-c) := h2
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ (c / 2) * ((sz.W n : ℕ) : ℝ) ^ (-c) :=
        mul_le_mul_of_nonneg_right hNW (Real.rpow_nonneg hW.le _)
    _ = ((sz.W n : ℕ) : ℝ) ^ (-(c / 2)) := by
        rw [← Real.rpow_add hW]; congr 1; ring

end Bookkeeping


/-! ## 9. (3.3) `GijGEX`, (3.2) `GiiGEX`, (3.5) `GavLGEX` per sequence

The inputs `hLrow`, `hLcol`, `hLquad`, `hLdiag` are the large deviation bounds in `≺` form over the
block-product index.  The
profile at size index `n` is `svar d (sz.L n) (sz.W n) (sz.lam n)`.  The size hypotheses are
`sz.Admissible 𝔠 𝔡`. -/

section Entry

variable {d : ℕ} (sz : Sizes d)

/-- **(3.3) `GijGEX`, `GijOmegaSeq`** (on `Ω(t,c)`, off the diagonal, swapped right side):
`1_{Ω(t,c)} |G_{pq}|² ≺ gexRHS … [q] [p]` from the large deviation bounds for the row and column
sums of [YY_25, (4.8)] (`hLrow`, `hLcol`, in `≺` form over the ordered pairs of distinct block-product
indices), with `δ = W^{-c} ≤ size^{-𝔠c}` (`Bandwidth`), constants `81`, `k = 2`
(`offSq_le_gexRHS_fine`).  The hypothesis `0 ≤ t n` of the shared list is not used here and is
omitted. -/
theorem entry_bound_stochDom {κ 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hA : sz.Admissible 𝔠 𝔡) {E t : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, t n < 1) {c : ℝ} (hc : 0 < c)
    (hLrow : sz.PrecPT (U := fun n => OffPair d (sz.L n) (sz.W n))
      (fun n u ω => ldeRowLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeRowRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2))
    (hLcol : sz.PrecPT (U := fun n => OffPair d (sz.L n) (sz.W n))
      (fun n u ω => ldeColLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeColRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2)) :
    GijOmegaSeq sz E t c := by
  have hsz' := entryDom_tendsto_size_of sz hA.2.2.1
  unfold GijOmegaSeq Sizes.PrecPT
  refine of_det hsz' (fun n p ω => gexRHS_nonneg _ _ _ _ _)
    (Ξ := fun n Φ => {ω | (∀ u : OffPair d (sz.L n) (sz.W n),
        ldeRowLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
          (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2 ≤
        Φ * ldeRowRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
          (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2) ∧
      (∀ u : OffPair d (sz.L n) (sz.W n),
        ldeColLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
          (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2 ≤
        Φ * ldeColRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
          (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2)})
    ?_ (δ := fun n => ((sz.W n : ℕ) : ℝ) ^ (-c)) (C := fun _ => 81)
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) (c₀ := 𝔠 * c) (mul_pos hA.1 hc)
    (entryDom_W_rpow_neg_le sz hA hc)
    (fun ε hε => entryDom_const_le_rpow sz hA.2.2.1 81 hε) 2 ?_
  · intro τ' hτ'
    have h1 := entryDom_highProb_of_perTime sz (m := 2) (entryDom_card_offPair_le sz) hLrow hτ'
    have h2 := entryDom_highProb_of_perTime sz (m := 2) (entryDom_card_offPair_le sz) hLcol hτ'
    exact RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono
      (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_inter hsz' h1 h2)
      (Eventually.of_forall fun n ω hω => ⟨hω.1, hω.2⟩)
  · refine Eventually.of_forall fun n ω Φ hΦ1 hΦδ hmem => ?_
    rintro ⟨_, p, q⟩
    obtain ⟨hrow, hcol⟩ := hmem
    by_cases hg : ∀ i j : Idx d (sz.L n) (sz.W n),
        llErrMat d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) i j ≤
          ((sz.W n : ℕ) : ℝ) ^ (-c)
    · rw [entryDom_omegaInd_of_forall hg, one_mul]
      exact offSq_le_gexRHS_fine (sz.three_le_L n) (sz.seqHflow_isHermitian n (t n) ω)
        (by linarith [hE n, hκ]) (zt_im_ne_zero hκ (hE n) (ht1 n))
        (entryDom_goodEvent_of_llErr _ _ _ _ _ _ _ hg)
        (entryDom_delta_le_half (Real.rpow_nonneg (Nat.cast_nonneg _) _) hΦ1 hΦδ) hΦ1 hΦδ
        (fun i j hij => hrow ⟨(i, j), hij⟩) (fun k j hkj => hcol ⟨(k, j), hkj⟩) p q
    · rw [entryDom_omegaInd_of_not hg, zero_mul]
      exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (gexRHS_nonneg _ _ _ _ _)

/-- **(3.3) `GijGEX` without the indicator**, under (3.4) `initialGT2`: if `Ω(t,c)` holds with high
probability.  Conclusion `GijSeq`. -/
theorem entry_bound_stochDom_of_highProb {κ 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hA : sz.Admissible 𝔠 𝔡)
    {E t : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, t n < 1) {c : ℝ} (hc : 0 < c)
    (hΩ : HighProbAt (seqP sz) sz.size (goodSet sz E t c))
    (hLrow : sz.PrecPT (U := fun n => OffPair d (sz.L n) (sz.W n))
      (fun n u ω => ldeRowLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeRowRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2))
    (hLcol : sz.PrecPT (U := fun n => OffPair d (sz.L n) (sz.W n))
      (fun n u ω => ldeColLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeColRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2)) :
    GijSeq sz E t := by
  have hsz' := entryDom_tendsto_size_of sz hA.2.2.1
  have h := entry_bound_stochDom sz hκ hA hE ht1 hc hLrow hLcol
  unfold GijOmegaSeq Sizes.PrecPT at h
  unfold GijSeq Sizes.PrecPT
  refine RBM.Ind.PerTimeCalc.PerTime.stochDom_of_indicator hsz'
    (Ωs := fun n _ => goodSet sz E t c n)
    (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono hΩ
      (Eventually.of_forall fun n ω hω _ => hω)) ?_
  have key : ∀ (n : ℕ) (p : Unit × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) ω,
      omegaInd d (sz.L n) (sz.W n) (E n) (t n) c (sz.seqHflow n (t n) ω) *
        offSq d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) p.2.1 p.2.2 =
      (goodSet sz E t c n).indicator
        (fun ω => offSq d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) p.2.1 p.2.2) ω :=
    fun n p ω => entryDom_omegaInd_mul_eq_indicator sz E t c n ω
      (fun ω => offSq d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) p.2.1 p.2.2)
  simp only [key] at h
  exact h

/-- **(3.3) `GijGEX` without the indicator, under `‖G_t - m‖_max ≺ W^{-c}`**: `AsGMcSeq sz E t c`
gives `Ω(t, c/2)` with high probability (grid union bound over the `N²` pairs, then
`size^{𝔠c/2} ≤ W^{c/2}` by `Bandwidth`), and `entry_bound_stochDom_of_highProb` at `c/2`
applies. -/
theorem entry_bound_stochDom_of_asGMc {κ 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hA : sz.Admissible 𝔠 𝔡)
    {E t : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, t n < 1) {c : ℝ} (hc : 0 < c)
    (hAs : AsGMcSeq sz E t c)
    (hLrow : sz.PrecPT (U := fun n => OffPair d (sz.L n) (sz.W n))
      (fun n u ω => ldeRowLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeRowRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2))
    (hLcol : sz.PrecPT (U := fun n => OffPair d (sz.L n) (sz.W n))
      (fun n u ω => ldeColLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeColRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2)) :
    GijSeq sz E t :=
  entry_bound_stochDom_of_highProb sz hκ hA hE ht1 (half_pos hc)
    (entryDom_goodSet_highProb_of_asGMc sz hA hc hAs) hLrow hLcol

end Entry

/-! ### (3.2) `GiiGEX` -/

section Diag

variable {d : ℕ} (sz : Sizes d)

/-- **(3.2) `GiiGEX`, `GiiOmegaSeq`** (on `Ω(t,c)`): `1_{Ω(t,c)} |G_{pp} - m|² ≺
max_{a,b} |𝓛_{(+,-),(a,b)}|` from the large deviation bounds `hLrow`, `hLcol`, `hLquad` and
`|H_{pp}|² ≺ S_{pp}` (`hLdiag`), with the constant `8640 Kstab3 d 𝔡⁻¹ κ²`
(`diagSq_le_maxLoopPM_fine`, `k = 2`), which is `≤ size^ε` eventually because it does not depend on
`n`, and the absorption `Kstab3 · W_n^{-c} ≤ 1/2` from `eventually_Kstab3_mul_rpow_le`; the coupling
window `0 < lam n ≤ 𝔡⁻¹` is (2.10) `eq:WO`.  The constant `8640 = 2160 · 4`. -/
theorem diag_bound_stochDom {κ 𝔠 𝔡 : ℝ} (hd : 3 ≤ d) (hκ : 0 < κ) (hA : sz.Admissible 𝔠 𝔡)
    {E t : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1) {c : ℝ}
    (hc : 0 < c)
    (hLrow : sz.PrecPT (U := fun n => OffPair d (sz.L n) (sz.W n))
      (fun n u ω => ldeRowLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeRowRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2))
    (hLcol : sz.PrecPT (U := fun n => OffPair d (sz.L n) (sz.W n))
      (fun n u ω => ldeColLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeColRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2))
    (hLquad : sz.PrecPT (U := fun n => Vtx d (sz.L n) (sz.W n))
      (fun n i ω => ldeQuadLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true)
        (svar d (sz.L n) (sz.W n) (sz.lam n)) (t n) i)
      (fun n i ω => ldeQuadRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) i))
    (hLdiag : sz.PrecPT (U := fun n => Vtx d (sz.L n) (sz.W n))
      (fun n i ω => ‖blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω) i i‖ ^ 2)
      (fun n i _ => svar d (sz.L n) (sz.W n) (sz.lam n) i i)) :
    GiiOmegaSeq sz E t c := by
  obtain ⟨h𝔠, h𝔡, hsz, hbw, hWO⟩ := hA
  have hA' : sz.Admissible 𝔠 𝔡 := ⟨h𝔠, h𝔡, hsz, hbw, hWO⟩
  have hsz' := entryDom_tendsto_size_of sz hsz
  unfold GiiOmegaSeq Sizes.PrecPT
  refine of_det hsz' (fun n p ω => maxLoopPM_nonneg _ _ _)
    (Ξ := fun n Φ => {ω | ((∀ u : OffPair d (sz.L n) (sz.W n),
        ldeRowLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
          (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2 ≤
        Φ * ldeRowRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
          (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2) ∧
      (∀ u : OffPair d (sz.L n) (sz.W n),
        ldeColLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
          (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2 ≤
        Φ * ldeColRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
          (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2)) ∧
      (∀ i : Vtx d (sz.L n) (sz.W n),
        ldeQuadLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
          (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true)
          (svar d (sz.L n) (sz.W n) (sz.lam n)) (t n) i ≤
        Φ * ldeQuadRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
          (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) i) ∧
      (∀ i : Vtx d (sz.L n) (sz.W n),
        ‖blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω) i i‖ ^ 2 ≤
          Φ * svar d (sz.L n) (sz.W n) (sz.lam n) i i)})
    ?_ (δ := fun n => ((sz.W n : ℕ) : ℝ) ^ (-c)) (C := fun _ => 8640 * Kstab3 d 𝔡⁻¹ κ ^ 2)
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) (c₀ := 𝔠 * c) (mul_pos h𝔠 hc)
    (entryDom_W_rpow_neg_le sz hA' hc)
    (fun ε hε => entryDom_const_le_rpow sz hsz _ hε) 2 ?_
  · intro τ' hτ'
    have h1 := entryDom_highProb_of_perTime sz (m := 2) (entryDom_card_offPair_le sz) hLrow hτ'
    have h2 := entryDom_highProb_of_perTime sz (m := 2) (entryDom_card_offPair_le sz) hLcol hτ'
    have h3 := entryDom_highProb_of_perTime sz (m := 1) (fun n =>
      (le_of_eq (entryDom_card_vtx sz n)).trans (by rw [pow_one])) hLquad hτ'
    have h4 := entryDom_highProb_of_perTime sz (m := 1) (fun n =>
      (le_of_eq (entryDom_card_vtx sz n)).trans (by rw [pow_one])) hLdiag hτ'
    exact RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono
      (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_inter hsz'
        (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_inter hsz'
          (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_inter hsz' h1 h2) h3) h4)
      (Eventually.of_forall fun n ω hω => ⟨⟨hω.1.1.1, hω.1.1.2⟩, hω.1.2, hω.2⟩)
  · filter_upwards [eventually_Kstab3_mul_rpow_le sz 𝔡⁻¹ κ h𝔠 hc hsz hbw,
      entryDom_lam_window sz hA'] with n hKn hlam ω Φ hΦ1 hΦδ hmem
    rintro ⟨_, p⟩
    obtain ⟨⟨hrow, hcol⟩, hquad, hdiag⟩ := hmem
    by_cases hg : ∀ i j : Idx d (sz.L n) (sz.W n),
        llErrMat d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) i j ≤
          ((sz.W n : ℕ) : ℝ) ^ (-c)
    · rw [entryDom_omegaInd_of_forall hg, one_mul]
      have h := diagSq_le_maxLoopPM_fine hd (sz.three_le_L n) (sz.seqHflow_isHermitian n (t n) ω)
        hlam.1 hlam.2 hκ (hE n) (ht0 n) (ht1 n)
        (entryDom_goodEvent_of_llErr _ _ _ _ _ _ _ hg)
        (entryDom_delta_le_half (Real.rpow_nonneg (Nat.cast_nonneg _) _) hΦ1 hΦδ) hΦ1 hΦδ hKn
        (fun i j hij => hrow ⟨(i, j), hij⟩) (fun k j hkj => hcol ⟨(k, j), hkj⟩) hquad hdiag
        p
      calc _ ≤ _ := h
        _ = _ := by ring
    · rw [entryDom_omegaInd_of_not hg, zero_mul]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _))
        (maxLoopPM_nonneg _ _ _)


/-- **(3.2) `GiiGEX` without the indicator**, under (3.4) `initialGT2`: if `Ω(t,c)` holds with high
probability.  Conclusion `GiiSeq`. -/
theorem diag_bound_stochDom_of_highProb {κ 𝔠 𝔡 : ℝ} (hd : 3 ≤ d) (hκ : 0 < κ)
    (hA : sz.Admissible 𝔠 𝔡) {E t : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht0 : ∀ n, 0 ≤ t n)
    (ht1 : ∀ n, t n < 1) {c : ℝ} (hc : 0 < c)
    (hΩ : HighProbAt (seqP sz) sz.size (goodSet sz E t c))
    (hLrow : sz.PrecPT (U := fun n => OffPair d (sz.L n) (sz.W n))
      (fun n u ω => ldeRowLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeRowRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2))
    (hLcol : sz.PrecPT (U := fun n => OffPair d (sz.L n) (sz.W n))
      (fun n u ω => ldeColLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeColRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2))
    (hLquad : sz.PrecPT (U := fun n => Vtx d (sz.L n) (sz.W n))
      (fun n i ω => ldeQuadLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true)
        (svar d (sz.L n) (sz.W n) (sz.lam n)) (t n) i)
      (fun n i ω => ldeQuadRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) i))
    (hLdiag : sz.PrecPT (U := fun n => Vtx d (sz.L n) (sz.W n))
      (fun n i ω => ‖blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω) i i‖ ^ 2)
      (fun n i _ => svar d (sz.L n) (sz.W n) (sz.lam n) i i)) :
    GiiSeq sz E t := by
  have hsz' := entryDom_tendsto_size_of sz hA.2.2.1
  have h := diag_bound_stochDom sz hd hκ hA hE ht0 ht1 hc hLrow hLcol hLquad hLdiag
  unfold GiiOmegaSeq Sizes.PrecPT at h
  unfold GiiSeq Sizes.PrecPT
  refine RBM.Ind.PerTimeCalc.PerTime.stochDom_of_indicator hsz'
    (Ωs := fun n _ => goodSet sz E t c n)
    (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono hΩ
      (Eventually.of_forall fun n ω hω _ => hω)) ?_
  have key : ∀ (n : ℕ) (p : Unit × Idx d (sz.L n) (sz.W n)) ω,
      omegaInd d (sz.L n) (sz.W n) (E n) (t n) c (sz.seqHflow n (t n) ω) *
        diagSq d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) p.2 =
      (goodSet sz E t c n).indicator
        (fun ω => diagSq d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) p.2) ω :=
    fun n p ω => entryDom_omegaInd_mul_eq_indicator sz E t c n ω
      (fun ω => diagSq d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) p.2)
  simp only [key] at h
  exact h

/-- **(3.2) `GiiGEX` without the indicator, under `‖G_t - m‖_max ≺ W^{-c}`**: as
`entry_bound_stochDom_of_asGMc`, through `Ω(t, c/2)`.  Conclusion `GiiSeq`. -/
theorem diag_bound_stochDom_of_asGMc {κ 𝔠 𝔡 : ℝ} (hd : 3 ≤ d) (hκ : 0 < κ)
    (hA : sz.Admissible 𝔠 𝔡) {E t : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht0 : ∀ n, 0 ≤ t n)
    (ht1 : ∀ n, t n < 1) {c : ℝ} (hc : 0 < c) (hAs : AsGMcSeq sz E t c)
    (hLrow : sz.PrecPT (U := fun n => OffPair d (sz.L n) (sz.W n))
      (fun n u ω => ldeRowLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeRowRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2))
    (hLcol : sz.PrecPT (U := fun n => OffPair d (sz.L n) (sz.W n))
      (fun n u ω => ldeColLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeColRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) u.1.1 u.1.2))
    (hLquad : sz.PrecPT (U := fun n => Vtx d (sz.L n) (sz.W n))
      (fun n i ω => ldeQuadLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true)
        (svar d (sz.L n) (sz.W n) (sz.lam n)) (t n) i)
      (fun n i ω => ldeQuadRHS (svar d (sz.L n) (sz.W n) (sz.lam n))
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true) i))
    (hLdiag : sz.PrecPT (U := fun n => Vtx d (sz.L n) (sz.W n))
      (fun n i ω => ‖blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω) i i‖ ^ 2)
      (fun n i _ => svar d (sz.L n) (sz.W n) (sz.lam n) i i)) :
    GiiSeq sz E t :=
  diag_bound_stochDom_of_highProb sz hd hκ hA hE ht0 ht1 (half_pos hc)
    (entryDom_goodSet_highProb_of_asGMc sz hA hc hAs) hLrow hLcol hLquad hLdiag

end Diag

end RBM.Green
