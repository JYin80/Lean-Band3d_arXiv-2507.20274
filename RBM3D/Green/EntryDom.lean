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
# Block-average error `(4.5)` and the `≺` layer of `lem_GbEXP`, `d ≥ 3` (S1-16)

Ticket T2057 (portmap P.7 row S1-16).  Port of `RBM2D/Green/EntryBlock.lean` and
`RBM2D/Green/EntryDom.lean` at commit `c9a24cf` (the compile checks and the `#print axioms` lines
are not ported) with the renaming rules R1-R4 of `docs/tickets/ST1-COMMON.md`: `Z2 L` becomes
`Zd d L`, `BlockIndex L W` becomes the block-product index `Vtx d L W = Z_L^d × Fin (W^d)`,
`W²`, `W⁻²` become `W^d`, `W^{-d}`, `d : Sizes` becomes `sz : Sizes d`, and RBM2D's fixed profile
`Sblk2` (weight `1/5`) becomes the merged `RBM.Gauss.svar d L W g`
(`S = S^(B)(g) ⊗ W^{-d} J`, `(eq:variancematrix)`, `1_2:304`).  Paper: arXiv:2507.20274; the
paper does not restate (4.2), (4.3), (4.5): it says that the proof of `lem_GbEXP`
(`paper/tex/3_5_Loop_Hierarchy.tex:14`, `3_5:37`) follows Lemma 4.1 of [YY_25] (RBM1D) and that
the argument is dimension-independent (resolvent identities and large deviation estimates).

Contents:
1. the resolvent helpers `green_mul_sub_of_im`, `sub_mul_green_of_im`, `zt_im_ne_zero`,
   `mE_mul_add_zt`;
2. the profile `svar` on `Vtx`: row and column sums, the bounds `S ≤ W^{-d}`, the support;
3. the neighbour sums `∑_{k,l} S_{pk} |G_{kl}|² S_{lq}` and their bound by `maxLoopPM`;
4. (4.2) in block form (`offSq_le_gexRHS_blk`, and its fine-lattice form);
5. the lower bounds `W^{-d} ≤ 4 maxLoopPM` and `S ≤ 4 maxLoopPM`;
6. (4.3) in block form (`diagSq_le_maxLoopPM_blk`), with the `d ≥ 3` stability constant
   `Kstab3 d Λ κ` of `RBM3D/Green/Stability.lean` in place of RBM2D's `Kstab2 κ L`;
7. (4.5): `blkCoef2`, `avgErr = ∑_k blkCoef2 (G_kk - m)` and the bound `norm_avgErr_le`;
8. the engine `of_det`, the grid bookkeeping, `goodSet`, the absorption of the constants;
9. (4.2), (4.3), (4.5) per sequence: `entry_bound_stochDom`, `diag_bound_stochDom`,
   `avg_bound_stochDom` (`(GavLGEX)`, `3_5:33`) and their variants;
10. compiled nonempty instances.

RBM2D statements dropped (their role is taken by merged declarations): `sbKre2`, `Sblk2` and their
elementary lemmas (replaced by `svar` and `sbKernelR`), `sum_sbKre2_sub_mul(')`,
`sum_sum_Sblk2_eq_nbr` (uniform weight `1/5`, false for the weights `a`, `g² a` of `S^(B)(g)`),
`Sblk2_eq_svar`, `stable_relabel`, `stable_Sblk2_bulk` (the profile is already `svar`; stability is
`stable_svar_bulk_vtx`), `eventually_Kstab2_le_rpow` and its two corollaries (`Kstab3` does not
depend on `n`).
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Green

open Matrix Finset Filter MeasureTheory RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-! ## 1. Resolvent helpers -/

section Resolvent

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Port of RBM1D `green_mul_sub_of_im` (RBM2D `Green/EntryBlock.lean:51`, `c9a24cf`); the
invertibility is `RBM.isUnit_sub_smul_of_isHermitian`. -/
theorem green_mul_sub_of_im {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    green H z * (H - z • (1 : Matrix n n ℂ)) = 1 :=
  green_mul_self (Matrix.isUnit_iff_isUnit_det _ |>.mp
    (RBM.isUnit_sub_smul_of_isHermitian hH hz))

/-- Port of RBM1D `sub_mul_green_of_im` (RBM2D `Green/EntryBlock.lean:57`). -/
theorem sub_mul_green_of_im {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    (H - z • (1 : Matrix n n ℂ)) * green H z = 1 :=
  self_mul_green (Matrix.isUnit_iff_isUnit_det _ |>.mp
    (RBM.isUnit_sub_smul_of_isHermitian hH hz))

end Resolvent

/-- `Im z_t ≠ 0` for `t < 1` in the bulk, `z_t = zt E t` (RBM2D `Green/EntryBlock.lean:66`, with
`spectralZ` read as the merged `zt`). -/
theorem zt_im_ne_zero {E κ t : ℝ} (hκ0 : 0 < κ) (hE : |E| ≤ 2 - κ) (ht1 : t < 1) :
    (zt E t).im ≠ 0 := by
  rw [zt_im]
  have h := mE_im_pos (E := E) (by linarith [abs_nonneg E])
  have : 0 < 1 - t := by linarith
  positivity

/-- `m = -(t m + z_t)⁻¹` (RBM2D `Green/EntryBlock.lean:75`, `spectralM`, `spectralZ` read as the
merged `mE`, `zt`). -/
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

/-- The kernel of `S^(B)(g)` is at most `1` (RBM2D `sbKre2_le`, `1/5`): it is non-negative and sums
to `1` (`sum_sbKernelR`, `3 ≤ L`). -/
private theorem entryDom_sbKernelR_le_one (hL : 3 ≤ L) (x : Zd d L) : sbKernelR d L g x ≤ 1 := by
  rw [← sum_sbKernelR d L g hL]
  exact Finset.single_le_sum (f := fun y => sbKernelR d L g y)
    (fun y _ => sbKernelR_nonneg d L g y) (Finset.mem_univ x)

omit [NeZero L] in
/-- The kernel of `S^(B)(g)` vanishes off the `L^∞` unit ball (RBM2D `sbKre2_le_ind`): its support is
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

/-- Row sums of the profile are `1` (RBM2D `sum_Sblk2_row`, `Σ_b |S_ab| = 1`): `S = W^{-d} S^(B)`
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

/-- Column sums of the profile are `1` (RBM2D `sum_Sblk2_col`). -/
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
/-- `S_{pq} ≤ W^{-d}` (RBM2D `Sblk2_le`, `≤ (1/5) W⁻²`). -/
theorem svar_le_inv_Wd (hL : 3 ≤ L) (p q : Vtx d L W) : svar d L W g p q ≤ ((W : ℝ) ^ d)⁻¹ := by
  rw [svar_eq_kernel]
  calc ((W : ℝ) ^ d)⁻¹ * sbKernelR d L g (p.1 - q.1) ≤ ((W : ℝ) ^ d)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (entryDom_sbKernelR_le_one g hL _) (by positivity)
    _ = ((W : ℝ) ^ d)⁻¹ := mul_one _

omit [NeZero W] in
/-- `S_{pq}` vanishes unless `|[p] - [q]|_∞ ≤ 1`, where it is `≤ W^{-d}` (RBM2D `Sblk2_le_ind`). -/
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

/-- The two-sided sum in (4.11) is a weighted sum of `2`-loops: with the orientation of
`norm_loopPM_eq` (rows in block `b`, columns in block `a`),
`∑_{k,l} S_{pk}|G_{kl}|²S_{lq} = ∑_{a',b'} S^{(B)}_{[p]a'} S^{(B)}_{b'[q]} ‖𝓛_{(+,-),(b',a')}‖`.
Port of RBM2D `sum_sum_Sblk2_eq` (`Green/EntryBlock.lean:263`), `S^(B)(g)` in place of `1/5`, the
`d`-dimensional blocks of `W^d` points. -/
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

/-- `∑_{k,l} S_{pk}|G_{kl}|²S_{lq} ≤ max_{a,b} ‖𝓛_{(+,-),(a,b)}‖` (RBM2D
`sum_sum_Sblk2_le_maxLoopPM`, `Green/EntryBlock.lean:302`): the rows of `S^(B)` sum to `1`. -/
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


/-! ## 4. (4.2) in block form -/

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
`splitEquiv` coordinates (RBM2D `FlucAvgDet_greenBlk_true_apply`, `Matrix.inv_submatrix_equiv`; copy
of the private `gres_blockMat_true`, `Green/Pins.lean:350`). -/
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

/-- The double sum is bounded by the double sum of `gexRHS … [q] [p]` (the swapped pair, RBM2D
T2066a): each `S^{(B)}` factor is `≤ 1` and vanishes off the `L^∞` ball `|·|_L ≤ 1`.  RBM2D
`sum_sum_Sblk2_le_gexRHS` (`Green/EntryBlock.lean:376`), with `zdist2 ≤ 1` (the five-point `ℓ¹` ball)
replaced by `zdistInf ≤ 1` (`gexRHS` of `Green/Pins.lean`; `{0} ∪ {|x|_{ℓ¹} = 1} ⊂ {|x|_∞ ≤ 1}`). -/
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

/-- **(4.2)**, deterministic block form (the two-sided bound of `norm_sq_green_le_two_sided` with
`S = svar`): on the good event, for all `p, q` in the block-product index,
`|G_{pq}|² ≤ 81 Φ² · gexRHS … [q] [p]` (the swapped pair, RBM2D T2066a; the left side is `0` on the
diagonal).  Port of RBM2D `offSq_le_gexRHS_blk` (`Green/EntryBlock.lean:406`): same constant `81`
(`S^{(B)} ≤ 1`), same orientation (D40 holds at `d ≥ 3`); the profile is `svar d L W g` and the
`zdist2 ≤ 1` of the right side is `zdistInf ≤ 1`.  The left side is written out because the merged
`offSq` lives on the fine lattice (see `offSq_le_gexRHS_fine`). -/
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

/-- **(4.2) on the fine lattice**: the form of the merged `offSq` (entries of `Gres M z true` at
`Z_{WL}^d`), from `offSq_le_gexRHS_blk` through `splitEquiv`:
`offSq p q ≤ 81 Φ² gexRHS … [q] [p]`, `[x] = (split x).1`.  (RBM2D's `offSq` is on `BlockIndex`;
`Green/Pins.lean` `offSq` of this project is on `Idx d L W`.) -/
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
contribute `≥ W^{-d}/4` to `𝓛_{(+,-),(0,0)}`.  Port of RBM2D `inv_W2_le_maxLoopPM`
(`Green/EntryBlock.lean:430`, `W⁻² ≤ 4 maxLoop`), with the block fibre `Fin (W^d)`. -/
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

/-- On the good event, `S_{pq} ≤ W^{-d} ≤ 4 max_{a,b} ‖𝓛_{(+,-),(a,b)}‖`.  RBM2D
`Sblk2_le_maxLoopPM` (`Green/EntryBlock.lean:461`) has `2 maxLoopPM`: the weight `1/5` of the
five-point profile; the profile `S^{(B)}(g)` is `≤ 1` and its entries tend to `1` as `g → 0`, so
from `W^{-d} ≤ 4 maxLoopPM` the constant is `4` (paper-delta candidate T2057a). -/
theorem svar_le_maxLoopPM (hL : 3 ≤ L) (hM : M.IsHermitian) (hE : |E| ≤ 2) {δ : ℝ}
    (hΩ : GoodEvent (greenBlk d L W E u M true) (mE E) δ) (hδ : δ ≤ 1 / 2) (g : ℝ)
    (p q : Vtx d L W) : svar d L W g p q ≤ 4 * maxLoopPM d L W E u M :=
  (svar_le_inv_Wd g hL p q).trans (inv_Wd_le_maxLoopPM hM hE hΩ hδ)

/-! ## 6. (4.3) in block form -/

/-- **(4.3)**, deterministic block form: on the good event, given the LDE inputs and the absorption
`Kstab3 d Λ κ · δ ≤ 1/2`,
`|G_{pp} - m|² ≤ 2160 · Kstab3² · Φ² · (4 max_{a,b} ‖𝓛_{(+,-),(a,b)}‖)`.  Port of RBM2D
`diagSq_le_maxLoopPM_blk` (`Green/EntryBlock.lean:477`): the stability constant `Kstab2 κ L` is the
`L`-free `Kstab3 d Λ κ` (`stable_svar_bulk_vtx`, hypotheses `3 ≤ d`, `0 < g ≤ Λ`), and the loop
bound `Λ' = 4 maxLoopPM` replaces `2 maxLoopPM` (T2057a).  The left side is `‖G_{pp} - m‖²`, the
merged `diagSq` on the block-product index. -/
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

/-- **(4.3) on the fine lattice**: `diagSq` of the merged `Green/Pins.lean` (entries of
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

/-! ## 7. (4.5): the coefficients `W^{-d} 1(k ∈ 𝓘_a)` and the bound -/

section Coef

variable {d L W : ℕ}

/-- The coefficients `c_k = W^{-d} 1(k ∈ 𝓘_a)` used for (4.5): the entries of `E_a` (`Def_matE`,
`(Eq:defGLoop)`, `1_2:824`; the merged `Eblk`).  Port of RBM2D `blkCoef2` (`Green/EntryBlock.lean:509`,
block weight `W⁻²`), block weight `W^{-d}`. -/
noncomputable def blkCoef2 (d L W : ℕ) (a : Zd d L) (k : Vtx d L W) : ℝ :=
  if k.1 = a then ((W : ℝ) ^ d)⁻¹ else 0

theorem abs_blkCoef2_le (a : Zd d L) (k : Vtx d L W) : |blkCoef2 d L W a k| ≤ ((W : ℝ) ^ d)⁻¹ := by
  unfold blkCoef2
  split_ifs
  · rw [abs_of_nonneg (by positivity)]
  · simp

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

/-- The weights `W^{-d} 1(k ∈ 𝓘_a)` are non-negative and sum to `1`. -/
theorem sum_blkCoef2 [NeZero L] [NeZero W] (a : Zd d L) : ∑ k, blkCoef2 d L W a k = 1 := by
  rw [← sum_abs_blkCoef2 (W := W) a]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [abs_of_nonneg]
  unfold blkCoef2
  split_ifs <;> positivity

/-- `⟨(G - m) E_a⟩ = ∑_k c_k (G_{kk} - m)` with `c_k = W^{-d} 1(k ∈ 𝓘_a)`.  Port of RBM2D
`trace_sub_mul_Eblk2` (`Green/EntryBlock.lean:541`). -/
theorem trace_sub_mul_Eblk2 [NeZero L] [NeZero W] (G : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (m : ℂ) (a : Zd d L) :
    Matrix.trace ((G - m • (1 : Matrix _ _ ℂ)) * Eblk d L W a)
      = ∑ k, (blkCoef2 d L W a k : ℂ) * (G k k - m) := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, Eblk, Matrix.mul_diagonal, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply_eq, smul_eq_mul, mul_one, blkCoef2]
  split_ifs <;> push_cast <;> ring

/-- The merged `avgErr` at the sign `+` is the trace form of (4.5) (`mSigma E true = m`). -/
private theorem entryDom_avgErr_true_eq_trace [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (a : Zd d L) :
    avgErr d L W E u M true a
      = Matrix.trace ((greenBlk d L W E u M true - mE E • (1 : Matrix _ _ ℂ)) *
          Eblk d L W a) := by
  simp [avgErr, mSigma]

/-- `avgErr … a = ∑_k c_k (G_{kk} - m)`, `c_k = blkCoef2 a k`.  Port of RBM2D
`avgErr_eq_sum_blkCoef2` (`Green/EntryBlock.lean:560`). -/
theorem avgErr_eq_sum_blkCoef2 [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (a : Zd d L) :
    avgErr d L W E u M true a
      = ∑ k, (blkCoef2 d L W a k : ℂ) * (greenBlk d L W E u M true k k - mE E) := by
  rw [entryDom_avgErr_true_eq_trace, trace_sub_mul_Eblk2]

variable [NeZero L] [NeZero W]

/-- **(4.5)**, deterministic block form.  With `x_k` standing for `E_k(G_{kk} - m)`: if
`x_i = t m² ∑_k S_{ik} (G_{kk} - m) + O(A)` and the fluctuation averaging holds with error `B` for
the weights `S_{ik}` and `B'` for the weights `c_k = W^{-d} 1(k ∈ 𝓘_a)`, then
`|⟨(G - m)E_a⟩| ≤ B' + Kstab3 d Λ κ · (A + B)`.  Port of RBM2D `norm_trace_green_sub_mul_Eblk2_le`
(`Green/EntryBlock.lean:574`) with `Kstab2 κ L` replaced by the `L`-free `Kstab3 d Λ κ`
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

/-- **Target `norm_avgErr_le`, the `avgErr` form of (4.5)**: the same bound for
`avgErr d L W E u M true a`, with `G = greenBlk d L W E u M true`,
`‖avgErr‖ ≤ B' + Kstab3 d Λ κ · (A + B)`.  Port of RBM2D `norm_avgErr_le`
(`Green/EntryBlock.lean:594`). -/
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

/-- **From a deterministic implication to `≺`** (port of RBM1D `StochDom.of_det`,
`Green/EntryBound.lean:1378`, through RBM2D `Green/EntryDom.lean:66`).  `Ξ l Φ` is the event that
all the input bounds hold with the factor `Φ`; it holds with high probability at `Φ = (size l)^{τ'}`
for every `τ' > 0`.  The constant is a sequence `C l ≤ (size l)^ε` (RBM2D: it contains
`Kstab2 κ L_n = O(log L_n)`; at `d ≥ 3` it contains the `n`-independent `Kstab3`), and the
requirement `δ ≤ ε₀` is absorbed into `hdet`.  The statement and proof are those of RBM2D. -/
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

/-- Ordered pairs of distinct block-product indices (RBM2D `OffPair`, `Green/EntryDom.lean:148`; port
of RBM1D `OffPair`, with `BlockIndex L W` replaced by `Vtx d L W = Z_L^d × Fin (W^d)`). -/
abbrev OffPair (d L W : ℕ) : Type := {p : Vtx d L W × Vtx d L W // p.1 ≠ p.2}

section Bookkeeping

variable {d : ℕ} (sz : Sizes d)

/-- The event `Ω(t,c)_n = {‖G_t - m‖_max ≤ W^{-c}}` of `def_asGMc` (`3_5:16`) at size index `n`; the
indicator `omegaInd` is its indicator.  (Port of RBM2D `goodSet`, `Green/EntryDom.lean:154`; the event
is stated on the fine lattice `Z_{WL}^d`, through `llErrMat`, because that is the form of `omegaInd`
and `AsGMcSeq`.) -/
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

/-- `omegaInd · f` is the indicator of `goodSet` times `f` (RBM2D
`entryDom_omegaInd_mul_eq_indicator`, `Green/EntryDom.lean:168`). -/
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

private theorem entryDom_card_Zd (L : ℕ) [NeZero L] : Fintype.card (Zd d L) = L ^ d := by
  simp [Zd, ZMod.card]

private theorem entryDom_card_offPair_le (n : ℕ) :
    Fintype.card (OffPair d (sz.L n) (sz.W n)) ≤ sz.size n ^ 2 := by
  calc Fintype.card (OffPair d (sz.L n) (sz.W n))
      ≤ Fintype.card (Vtx d (sz.L n) (sz.W n) × Vtx d (sz.L n) (sz.W n)) :=
        Fintype.card_subtype_le _
    _ = sz.size n ^ 2 := by rw [Fintype.card_prod, entryDom_card_vtx, sq]

private theorem entryDom_Zd_le_size (n : ℕ) : (sz.L n) ^ d ≤ sz.size n := by
  rw [Sizes.size]
  exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d

private theorem entryDom_card_Zd_le (n : ℕ) : Fintype.card (Zd d (sz.L n)) ≤ sz.size n ^ 1 := by
  rw [entryDom_card_Zd, pow_one]
  exact entryDom_Zd_le_size sz n

private theorem entryDom_card_Zd_sq_le (n : ℕ) :
    Fintype.card (Unit × Zd d (sz.L n) × Zd d (sz.L n)) ≤ sz.size n ^ 2 := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_unit, entryDom_card_Zd, one_mul, sq]
  exact Nat.mul_le_mul (entryDom_Zd_le_size sz n) (entryDom_Zd_le_size sz n)

private theorem entryDom_card_idx_sq (n : ℕ) :
    Fintype.card (Unit × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) ≤ sz.size n ^ 2 := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_unit, sz.card_Idx, one_mul, sq]

private theorem entryDom_card_real_le {V : ℕ → Type*} [∀ n, Fintype (V n)] {m : ℕ}
    (h : ∀ n, Fintype.card (V n) ≤ sz.size n ^ m) (n : ℕ) :
    (Fintype.card (V n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (m : ℝ) := by
  rw [Real.rpow_natCast]; exact_mod_cast h n

/-- The grid union bound in the form used here: a per-time bound over an index set of size at most
`size^m` gives an event of high probability (merged `stochDomAt_of_perTimeDomAt`,
`perTimeCalc_highProbAt_of_stochDomAt`).  RBM2D `highProb_of_perTime`
(`Green/EntryDom.lean:229`). -/
private theorem entryDom_highProb_of_perTime {V : ℕ → Type*} [∀ n, Fintype (V n)] {m : ℕ}
    (hV : ∀ n, Fintype.card (V n) ≤ sz.size n ^ m)
    {ξ ζ : ∀ n, V n → sz.SeqΩ → ℝ} (h : sz.PrecPT ξ ζ) {τ : ℝ} (hτ : 0 < τ) :
    HighProbAt (seqP sz) sz.size
      (fun n => {ω | ∀ v, ξ n v ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ n v ω}) :=
  RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_of_stochDomAt
    (stochDomAt_of_perTimeDomAt (seqP sz) sz.size (C := (m : ℝ)) (Nat.cast_nonneg m)
      (Eventually.of_forall (entryDom_card_real_le sz hV)) h) hτ

/-- `W^{-c} ≤ (size)^{-(𝔠 c)}` eventually (`Bandwidth`).  RBM2D `eventually_W_rpow_neg_le`
(`Green/EntryDom.lean:268`). -/
private theorem entryDom_W_rpow_neg_le {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-c) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(𝔠 * c)) := by
  obtain ⟨_, _, hsz, hbw, _⟩ := hA
  filter_upwards [hbw, hsz.eventually_gt_atTop 0] with n hn hN0
  have hNp : 0 < ((sz.size n : ℕ) : ℝ) ^ 𝔠 := Real.rpow_pos_of_pos hN0 _
  calc ((sz.W n : ℕ) : ℝ) ^ (-c) ≤ (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (-c) :=
        Real.rpow_le_rpow_of_nonpos hNp hn (by linarith)
    _ = ((sz.size n : ℕ) : ℝ) ^ (𝔠 * -c) := (Real.rpow_mul hN0.le _ _).symm
    _ = ((sz.size n : ℕ) : ℝ) ^ (-(𝔠 * c)) := by rw [mul_neg]

/-- `(eq:WO)` gives `0 < lam n ≤ 𝔡⁻¹` eventually: the coupling window `Λ = 𝔡⁻¹` of `Kstab3`. -/
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
constants `8640 K²` and `1 + 2K`, `K = Kstab3 d 𝔡⁻¹ κ`, do not depend on `n` (RBM2D
`eventually_const_kstab2_sq_le`, `eventually_one_add_two_kstab2_le`, where `Kstab2 κ L_n` grows like
`log L_n` and `Bandwidth` is needed). -/
private theorem entryDom_const_le_rpow (hsz : sz.SizeTendsto) (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, C ≤ ((sz.size n : ℕ) : ℝ) ^ ε :=
  (entryDom_tendsto_size_of sz hsz).eventually (eventually_le_rpow C hε)

/-- Deterministic bridge: `‖G_u - m‖_max ≤ δ` on the fine lattice (`llErrMat`) is the `GoodEvent`
of the block-level resolvent `greenBlk` (`greenBlk = (blockMat M - z)⁻¹` is the fine-lattice
resolvent relabelled by `splitEquiv`, `Matrix.inv_submatrix_equiv`).  RBM2D
`entryDom_goodEvent_of_llErr` (`Green/EntryDom.lean:287`). -/
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
pairs of the fine lattice, then `size^{𝔠c/2} ≤ W^{c/2}` by `Bandwidth`).  RBM2D
`entryDom_goodSet_highProb_of_asGMc` (`Green/EntryDom.lean:350`). -/
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


/-! ## 9. (4.2), (4.3), (4.5) per sequence

The inputs `hLrow`, `hLcol`, `hLquad`, `hLdiag` are the large deviation bounds in `≺` form over the
block-product index; `hIBP`, `hFArow`, `hFAblk` are the Gaussian integration by parts display and the
fluctuation averaging (4.12) (inputs of other tickets, not hypotheses added to a pin: they are the
premises of RBM2D's `avg_bound_stochDom`).  The profile at size index `n` is
`svar d (sz.L n) (sz.W n) (sz.lam n)`.  The hypotheses `SizeTendsto d`, `Bandwidth d 𝔠` of RBM2D are
`sz.Admissible 𝔠 𝔡` (T2028, DECISIONS §22 / D39). -/

section Entry

variable {d : ℕ} (sz : Sizes d)

/-- **(4.2), `GijOmegaSeq`** (`GijGEX`, `3_5:24`, on `Ω(t,c)`, off the diagonal, swapped right side):
`1_{Ω(t,c)} |G_{pq}|² ≺ gexRHS … [q] [p]` from the large deviation bounds for the row and column
sums of (4.8) (`hLrow`, `hLcol`, in `≺` form over the ordered pairs of distinct block-product
indices).  Port of RBM2D `entry_bound_stochDom` (`Green/EntryDom.lean:387`) with `δ = W^{-c} ≤
size^{-𝔠c}` (`Bandwidth`), constants `81`, `k = 2` (`offSq_le_gexRHS_fine`).  The hypothesis `0 ≤ t n`
of the shared list is not used here and is omitted. -/
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

/-- **(4.2) without the indicator**, under (4.4): if `Ω(t,c)` holds with high probability.  Port of
RBM2D `entry_bound_stochDom_of_highProb` (`Green/EntryDom.lean:442`); RBM1D's `StochDom.of_indicator`
is the merged `PerTime.stochDom_of_indicator`.  Conclusion `GijSeq`. -/
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

/-- **(4.2) without the indicator, under (`asGMc`)** (`3_5:30`): `AsGMcSeq sz E t c` gives `Ω(t, c/2)`
with high probability (grid union bound over the `N²` pairs, then `size^{𝔠c/2} ≤ W^{c/2}` by
`Bandwidth`), and `entry_bound_stochDom_of_highProb` at `c/2` applies.  Not in RBM1D (there `Ω` with
high probability is a hypothesis).  RBM2D `entry_bound_stochDom_of_asGMc`
(`Green/EntryDom.lean:479`). -/
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

/-! ### (4.3) -/

section Diag

variable {d : ℕ} (sz : Sizes d)

/-- **(4.3), `GiiOmegaSeq`** (`GiiGEX`, `3_5:21`, on `Ω(t,c)`): `1_{Ω(t,c)} |G_{pp} - m|² ≺
max_{a,b} |𝓛_{(+,-),(a,b)}|` from the large deviation bounds `hLrow`, `hLcol`, `hLquad` and
`|H_{pp}|² ≺ S_{pp}` (`hLdiag`).  Port of RBM2D `diag_bound_stochDom`
(`Green/EntryDom.lean:511`), with the constant `8640 Kstab3 d 𝔡⁻¹ κ²` (`diagSq_le_maxLoopPM_fine`,
`k = 2`; RBM2D: `4320 Kstab2 κ L_n²`), which is `≤ size^ε` eventually because it does not depend on
`n`, and the absorption `Kstab3 · W_n^{-c} ≤ 1/2` from `eventually_Kstab3_mul_rpow_le`; the coupling
window `0 < lam n ≤ 𝔡⁻¹` is `(eq:WO)`.  The constant `8640 = 2160 · 4` (T2057a). -/
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


/-- **(4.3) without the indicator**, under (4.4): if `Ω(t,c)` holds with high probability.  Port of
RBM2D `diag_bound_stochDom_of_highProb` (`Green/EntryDom.lean:592`).  Conclusion `GiiSeq`. -/
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

/-- **(4.3) without the indicator, under (`asGMc`)** (`3_5:30`): as `entry_bound_stochDom_of_asGMc`,
through `Ω(t, c/2)`.  Conclusion `GiiSeq`.  Not in RBM1D.  RBM2D `diag_bound_stochDom_of_asGMc`
(`Green/EntryDom.lean:636`). -/
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

/-! ### (4.5) -/

section Avg

variable {d : ℕ} (sz : Sizes d)

/-- `max_{a,b} |𝓛_{(+,-),(a,b)}| ≺ Ψ²` from `LoopDetSeq` (grid union over `(Z_L^d)²`,
`L^{2d} ≤ size²`, then `maxLoopPM = ‖loopPM a₀ b₀‖` for some pair), with the index `Unit × Z_L^d` of
`GavLDetSeq`.  RBM2D `maxLoop_dom_of_loopDet` (`Green/EntryDom.lean:673`). -/
private theorem entryDom_maxLoop_dom_of_loopDet {E t : ℕ → ℝ} {Ψ : ℕ → ℝ}
    (hLoop : LoopDetSeq sz E t Ψ) :
    sz.PrecPT (U := fun n => Unit × Zd d (sz.L n))
      (fun n _ ω => maxLoopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω))
      (fun n _ _ => Ψ n ^ 2) := by
  have hS := stochDomAt_of_perTimeDomAt (seqP sz) sz.size (C := ((2 : ℕ) : ℝ))
    (Nat.cast_nonneg 2) (Eventually.of_forall (entryDom_card_real_le sz (entryDom_card_Zd_sq_le sz)))
    hLoop
  intro τ hτ D hD
  filter_upwards [hS τ hτ D hD] with n hn u
  refine le_trans (measure_mono ?_) hn
  intro ω hω
  have hω' : ((sz.size n : ℕ) : ℝ) ^ τ * Ψ n ^ 2 <
      maxLoopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) := hω
  unfold maxLoopPM at hω'
  obtain ⟨b, -, hb⟩ := (Finset.lt_sup'_iff _).1 hω'
  exact ⟨((), b.1, b.2), hb⟩

/-- **Target `avg_bound_stochDom`: (4.5), `GavLDetSeq`** (`GavLGEX`, `3_5:33`, with the deterministic
control `Ψ²` of RBM2D T2066b): `max_a |⟨(G_t - m) E_a⟩| ≺ Ψ²`, from the Gaussian integration by parts
display (`hIBP`), the fluctuation averaging (4.12) for the two families of coefficients (`hFArow`,
`hFAblk`), all with right side `max_{a,b} |𝓛_{(+,-),(a,b)}|`, and `max |𝓛| ≺ Ψ²` (`hLoop`).  Here
`x n ω k` stands for `E_k(G_kk - m)`.  Port of RBM2D `avg_bound_stochDom`
(`Green/EntryDom.lean:696`; RBM1D `avg_bound_stochDom`, `Green/EntryBound.lean:1628`, the step
`≺ max |𝓛|`), followed by transitivity of `≺` with `hLoop`; the constant `1 + 2 Kstab3 d 𝔡⁻¹ κ` is
`≤ size^ε` eventually (RBM2D: `1 + 2 Kstab2 κ L_n`) and no good event is used (`δ ≡ 0`).  The
hypotheses `SizeTendsto d`, `Bandwidth d 𝔠` of RBM2D are `sz.Admissible 𝔠 𝔡`, plus `3 ≤ d`. -/
theorem avg_bound_stochDom {κ 𝔠 𝔡 : ℝ} (hd : 3 ≤ d) (hκ : 0 < κ) (hA : sz.Admissible 𝔠 𝔡)
    {E t : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1)
    (x : ∀ n, sz.SeqΩ → Vtx d (sz.L n) (sz.W n) → ℂ)
    (hIBP : sz.PrecPT (U := fun n => Vtx d (sz.L n) (sz.W n))
      (fun n i ω => ‖x n ω i - (t n : ℂ) * mE (E n) ^ 2 *
        ∑ k, (svar d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ) *
          (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true k k -
            mE (E n))‖)
      (fun n _ ω => maxLoopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω)))
    (hFArow : sz.PrecPT (U := fun n => Vtx d (sz.L n) (sz.W n))
      (fun n i ω => ‖∑ k, (svar d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ) *
        ((greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true k k -
          mE (E n)) - x n ω k)‖)
      (fun n _ ω => maxLoopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω)))
    (hFAblk : sz.PrecPT (U := fun n => Zd d (sz.L n))
      (fun n a ω => ‖∑ k, (blkCoef2 d (sz.L n) (sz.W n) a k : ℂ) *
        ((greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true k k -
          mE (E n)) - x n ω k)‖)
      (fun n _ ω => maxLoopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω)))
    {Ψ : ℕ → ℝ} (hLoop : LoopDetSeq sz E t Ψ) :
    GavLDetSeq sz E t Ψ := by
  have hsz := hA.2.2.1
  have hsz' := entryDom_tendsto_size_of sz hsz
  have hAvg : sz.PrecPT (U := fun n => Unit × Zd d (sz.L n))
      (fun n p ω => ‖avgErr d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true p.2‖)
      (fun n _ ω => maxLoopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω)) := by
    unfold Sizes.PrecPT
    refine of_det hsz' (fun n p ω => maxLoopPM_nonneg _ _ _)
      (Ξ := fun n Φ => {ω | (∀ i : Vtx d (sz.L n) (sz.W n),
          ‖x n ω i - (t n : ℂ) * mE (E n) ^ 2 *
            ∑ k, (svar d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ) *
              (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true k k -
                mE (E n))‖ ≤
          Φ * maxLoopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω)) ∧
        (∀ i : Vtx d (sz.L n) (sz.W n),
          ‖∑ k, (svar d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ) *
            ((greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true k k -
              mE (E n)) - x n ω k)‖ ≤
          Φ * maxLoopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω)) ∧
        (∀ a : Zd d (sz.L n),
          ‖∑ k, (blkCoef2 d (sz.L n) (sz.W n) a k : ℂ) *
            ((greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true k k -
              mE (E n)) - x n ω k)‖ ≤
          Φ * maxLoopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω))})
      ?_ (δ := fun _ => 0) (C := fun _ => 1 + 2 * Kstab3 d 𝔡⁻¹ κ)
      (fun _ => le_rfl) (c₀ := 1) one_pos
      (Eventually.of_forall fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (fun ε hε => entryDom_const_le_rpow sz hsz _ hε) 1 ?_
    · intro τ' hτ'
      have h1 := entryDom_highProb_of_perTime sz (m := 1) (fun n =>
        (le_of_eq (entryDom_card_vtx sz n)).trans (by rw [pow_one])) hIBP hτ'
      have h2 := entryDom_highProb_of_perTime sz (m := 1) (fun n =>
        (le_of_eq (entryDom_card_vtx sz n)).trans (by rw [pow_one])) hFArow hτ'
      have h3 := entryDom_highProb_of_perTime sz (m := 1) (entryDom_card_Zd_le sz) hFAblk hτ'
      exact RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono
        (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_inter hsz'
          (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_inter hsz' h1 h2) h3)
        (Eventually.of_forall fun n ω hω => ⟨hω.1.1, hω.1.2, hω.2⟩)
    · filter_upwards [entryDom_lam_window sz hA] with n hlam ω Φ hΦ1 _ hmem
      rintro ⟨_, a⟩
      obtain ⟨hIBPω, hFArowω, hFAblkω⟩ := hmem
      have h := norm_avgErr_le hd (sz.three_le_L n) hlam.1 hlam.2 hκ (hE n) (ht0 n) (ht1 n)
        (sz.seqHflow n (t n) ω) (x n ω)
        (A := Φ * maxLoopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω))
        (B := Φ * maxLoopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω))
        (B' := Φ * maxLoopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω))
        hIBPω hFArowω a (hFAblkω a)
      calc _ ≤ _ := h
        _ = _ := by ring
  unfold GavLDetSeq Sizes.PrecPT
  refine RBM.Ind.PerTimeCalc.PerTime.perTimeCalc_of_imp_union hsz' hAvg
    (entryDom_maxLoop_dom_of_loopDet sz hLoop) ?_
  intro τ hτ
  refine ⟨τ / 2, half_pos hτ, Eventually.of_forall fun n p ω hlt => ?_⟩
  by_contra hcon
  rw [not_or, not_lt, not_lt] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have h3 : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * Ψ n ^ 2) =
      ((sz.size n : ℕ) : ℝ) ^ τ * Ψ n ^ 2 := by
    rw [← mul_assoc, ← Real.rpow_add' hN0 (by positivity : τ / 2 + τ / 2 ≠ 0)]
    congr 2; ring
  have h4 := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hN0 (τ / 2))
  linarith

end Avg

/-! ## 10. Compiled nonempty instances

Pointwise instance of `norm_avgErr_le`: the size index `n = 0` of `sz0` (`RBM3D/Defs/Sizes.lean`:
`d = 3`, `L = 4`, `W = 32`, `g = lam 0 = 1/64`, `N = (W L)^d = 2097152`, a block has `W^d = 32768`
sites), the window `Λ = 10 = 𝔡⁻¹`, `E = 0`, `κ = 1`, `u = 1/2`, `M = 0`.  There `z_u = i/2`,
`G_u = 2i · 1`, `m = i`, so `G_kk - m = i` and `avgErr = i` (`‖avgErr‖ = 1`); with
`x ≡ -i/2 = u m² (G_kk - m)` the inputs hold with `A = 0` and `B = B' = 3/2`, and the conclusion
`1 ≤ 3/2 + Kstab3 3 10 1 · 3/2` is not vacuous.  Sequence instances: `sz0` itself, admissible at
`𝔠 = 1/6`, `𝔡 = 1/10` with `lam → 0`, `E ≡ 0`, `κ = 1`: at `t ≡ 0` (`H = 0`, `G = m 1`) every
hypothesis of `entry_bound_stochDom`, `diag_bound_stochDom`, `avg_bound_stochDom` is proved; at `t ≡ 1/2` the large deviation, integration by parts
and fluctuation averaging inputs (other tickets' results) stay hypotheses of the example. -/

section Instances

open RBM.Gauss.SizesInst

private theorem entryDom_mE_zero : mE 0 = Complex.I := by
  have h : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp [mE, h]

private theorem entryDom_gres_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {z : ℂ} (hz : z ≠ 0) :
    Gres (0 : Matrix ι ι ℂ) z true = (-z)⁻¹ • (1 : Matrix ι ι ℂ) := by
  rw [Gres]
  simp only [↓reduceIte]
  rw [zero_sub, ← neg_smul, ring_inverse_smul_one (neg_ne_zero.2 hz)]

/-- At `E = 0`, `u = 1/2`, `M = 0`: `G_u = (2 i) · 1`. -/
private theorem entryDom_inst_green :
    greenBlk 3 4 32 0 (1 / 2) 0 true = (2 * Complex.I) • (1 : Matrix (Vtx 3 4 32) (Vtx 3 4 32) ℂ) := by
  have hz : zt 0 (1 / 2) = (1 / 2 : ℂ) * Complex.I := by
    simp [zt, entryDom_mE_zero]
    norm_num
  have hz0 : zt 0 (1 / 2) ≠ 0 := by
    rw [hz]; simp
  unfold greenBlk
  rw [blockMat_zero, entryDom_gres_zero hz0, hz]
  congr 1
  refine inv_eq_of_mul_eq_one_right ?_
  linear_combination (-1 : ℂ) * Complex.I_sq

private theorem entryDom_inst_diag (k : Vtx 3 4 32) :
    greenBlk 3 4 32 0 (1 / 2) 0 true k k - mE 0 = Complex.I := by
  rw [entryDom_inst_green, entryDom_mE_zero]
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  ring

private theorem entryDom_inst_sum_svar (i : Vtx 3 4 32) (c : ℂ) :
    ∑ k, (svar 3 4 32 (1 / 64) i k : ℂ) * c = c := by
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, sum_svar_row (1 / 64) (by norm_num) i,
    Complex.ofReal_one, one_mul]

private theorem entryDom_inst_sum_blk (a : Zd 3 4) (c : ℂ) :
    ∑ k, (blkCoef2 3 4 32 a k : ℂ) * c = c := by
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, sum_blkCoef2, Complex.ofReal_one, one_mul]

/-- `avgErr = i` at the instance: the left side of `norm_avgErr_le` is `1`, not `0`. -/
private theorem entryDom_inst_avgErr (a : Zd 3 4) :
    avgErr 3 4 32 0 (1 / 2) 0 true a = Complex.I := by
  rw [avgErr_eq_sum_blkCoef2]
  simp only [entryDom_inst_diag]
  exact entryDom_inst_sum_blk a Complex.I

/-- **Instance of `norm_avgErr_le`** at `d = 3`, `L = 4`, `W = 32`, `g = 1/64 ≤ Λ = 10`, `E = 0`,
`κ = 1`, `u = 1/2`, `M = 0`, `x ≡ -i/2`, `A = 0`, `B = B' = 3/2`: every hypothesis is discharged,
the left side is `‖avgErr‖ = 1` (`entryDom_inst_avgErr`). -/
example (a : Zd 3 4) :
    ‖avgErr 3 4 32 0 (1 / 2) 0 true a‖ ≤ 3 / 2 + Kstab3 3 10 1 * (0 + 3 / 2) := by
  refine norm_avgErr_le (d := 3) (L := 4) (W := 32) (g := 1 / 64) (Λ := 10) (E := 0) (κ := 1)
    (u := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) 0 (fun _ => -(Complex.I / 2)) (A := 0) (B := 3 / 2)
    (B' := 3 / 2) ?_ ?_ a ?_
  · intro i
    simp only [entryDom_inst_diag, entryDom_inst_sum_svar]
    rw [entryDom_mE_zero]
    have : -(Complex.I / 2) - ((1 / 2 : ℝ) : ℂ) * Complex.I ^ 2 * Complex.I = 0 := by
      push_cast
      linear_combination (-(1 / 2 : ℂ) * Complex.I) * Complex.I_sq
    rw [this, norm_zero]
  · intro i
    simp only [entryDom_inst_diag, entryDom_inst_sum_svar]
    have : Complex.I - -(Complex.I / 2) = (3 / 2 : ℝ) * Complex.I := by push_cast; ring
    rw [this, norm_mul, Complex.norm_I, Complex.norm_real]
    norm_num
  · simp only [entryDom_inst_diag, entryDom_inst_sum_blk]
    have : Complex.I - -(Complex.I / 2) = (3 / 2 : ℝ) * Complex.I := by push_cast; ring
    rw [this, norm_mul, Complex.norm_I, Complex.norm_real]
    norm_num

/-- The instance is not degenerate: `‖avgErr‖ = 1` while `Kstab3 3 10 1 ≥ 1` makes the right side at
least `3/2 + 3/2 = 3`. -/
example (a : Zd 3 4) : ‖avgErr 3 4 32 0 (1 / 2) 0 true a‖ = 1 ∧
    3 ≤ 3 / 2 + Kstab3 3 10 1 * (0 + 3 / 2) := by
  refine ⟨by rw [entryDom_inst_avgErr, Complex.norm_I], ?_⟩
  have := one_le_Kstab3 3 10 1
  nlinarith

/-! ### Sequence instances at `sz0` -/

private theorem entryDom_seqHflow_zero {d : ℕ} (sz : Sizes d) (n : ℕ) (ω : sz.SeqΩ) :
    sz.seqHflow n 0 ω = 0 := by
  rw [Sizes.seqHflow_eq_smul]
  simp

/-- At `t = 0`, `E = 0`, `M = 0`: `‖𝓛_{(+,-),(a,b)}‖ ≤ W^{-d}` (`G = m 1`, `|m| = 1`).  RBM2D
`chk_norm_loopPM_zero` (`Green/EntryDom.lean:940`). -/
private theorem entryDom_norm_loopPM_zero (d L W : ℕ) [NeZero L] [NeZero W] (a b : Zd d L) :
    ‖loopPM d L W 0 0 (0 : Matrix (Idx d L W) (Idx d L W) ℂ) a b‖ ≤ ((W : ℝ) ^ d)⁻¹ := by
  rw [norm_loopPM_eq _ Matrix.isHermitian_zero, greenBlk_time_zero (by norm_num)]
  have hW : (0 : ℝ) < (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hm : ‖mE 0‖ = 1 := norm_mE (by norm_num)
  have h1 : ∀ β : Fin (W ^ d), ∑ α : Fin (W ^ d),
      ‖(mE 0 • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) (b, β) (a, α)‖ ^ 2 ≤ 1 := by
    intro β
    by_cases hab : a = b
    · subst hab
      rw [Finset.sum_eq_single β]
      · simp [hm]
      · intro α _ hne
        have h0 : (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a, β) (a, α) = 0 :=
          Matrix.one_apply_ne (fun h => hne (Prod.mk.inj h).2.symm)
        simp [h0]
      · simp
    · simp [Prod.ext_iff, hab, eq_comm]
  calc (((W : ℝ)⁻¹ ^ d) ^ 2) * ∑ β : Fin (W ^ d), ∑ α : Fin (W ^ d),
        ‖(mE 0 • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) (b, β) (a, α)‖ ^ 2
      ≤ (((W : ℝ)⁻¹ ^ d) ^ 2) * ∑ _β : Fin (W ^ d), (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun β _ => h1 β) (by positivity)
    _ = ((W : ℝ) ^ d)⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, inv_pow]
        push_cast
        field_simp [pow_pos hW d |>.ne']

/-- `LoopDetSeq` at `t ≡ 0`, `E ≡ 0` with `Ψ_n² = W_n^{-3}` (`d = 3`). -/
private theorem entryDom_loopDet_zero :
    LoopDetSeq sz0 (fun _ => 0) (fun _ => 0) (fun n => Real.sqrt ((((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹)) := by
  unfold LoopDetSeq Sizes.PrecPT
  refine RBM.Ind.PerTimeCalc.PerTime.stochDom_of_le_const_mul
    (entryDom_tendsto_size_of sz0 sz0_tendsto) (fun n u ω => norm_nonneg _)
    (fun n u ω => sq_nonneg _) 1 (fun n u ω => ?_)
  simp only [entryDom_seqHflow_zero]
  rw [Real.sq_sqrt (by positivity), one_mul]
  exact entryDom_norm_loopPM_zero 3 (sz0.L n) (sz0.W n) u.2.1 u.2.2

/-- **Instance of `avg_bound_stochDom` at `t ≡ 0`** (`sz0`, `E ≡ 0`, `κ = 1`, `𝔠 = 1/6`, `𝔡 = 1/10`,
`x ≡ 0`, `Ψ_n = W_n^{-3/2}`): every hypothesis is proved (at `t ≡ 0`, `H = 0`, `G = m 1`).  RBM2D
`check_avg_zero` (`Green/EntryDom.lean:1011`). -/
example : GavLDetSeq sz0 (fun _ => 0) (fun _ => 0)
    (fun n => Real.sqrt ((((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹)) := by
  refine avg_bound_stochDom sz0 (κ := 1) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (by norm_num) one_pos
    sz0_admissible (E := fun _ => 0) (t := fun _ => 0) (fun n => by norm_num) (fun n => le_rfl)
    (fun n => by norm_num) (fun _ _ _ => 0) ?_ ?_ ?_ entryDom_loopDet_zero
  · refine perTimeDomAt_of_nonpos _ _ _ _ (fun n u ω => ?_) (fun n u ω => maxLoopPM_nonneg _ _ _)
    simp
  · refine perTimeDomAt_of_nonpos _ _ _ _ (fun n u ω => ?_) (fun n u ω => maxLoopPM_nonneg _ _ _)
    simp only [entryDom_seqHflow_zero, greenBlk_time_zero (E := 0) (by norm_num),
      Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, sub_self, mul_zero,
      Finset.sum_const_zero, norm_zero]
    exact le_rfl
  · refine perTimeDomAt_of_nonpos _ _ _ _ (fun n u ω => ?_) (fun n u ω => maxLoopPM_nonneg _ _ _)
    simp only [entryDom_seqHflow_zero, greenBlk_time_zero (E := 0) (by norm_num),
      Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, sub_self, mul_zero,
      Finset.sum_const_zero, norm_zero]
    exact le_rfl

section AtHalf

-- The inputs of (4.2), (4.3), (4.5) at `sz0`, `E ≡ 0`, `t ≡ 1/2`, left as variables.
variable
  (hLrow : sz0.PrecPT (U := fun n => OffPair 3 (sz0.L n) (sz0.W n))
    (fun n u ω => ldeRowLHS (blockMat 3 (sz0.L n) (sz0.W n) (sz0.seqHflow n (1 / 2) ω))
      (greenBlk 3 (sz0.L n) (sz0.W n) 0 (1 / 2) (sz0.seqHflow n (1 / 2) ω) true) u.1.1 u.1.2)
    (fun n u ω => ldeRowRHS (svar 3 (sz0.L n) (sz0.W n) (sz0.lam n))
      (greenBlk 3 (sz0.L n) (sz0.W n) 0 (1 / 2) (sz0.seqHflow n (1 / 2) ω) true) u.1.1 u.1.2))
  (hLcol : sz0.PrecPT (U := fun n => OffPair 3 (sz0.L n) (sz0.W n))
    (fun n u ω => ldeColLHS (blockMat 3 (sz0.L n) (sz0.W n) (sz0.seqHflow n (1 / 2) ω))
      (greenBlk 3 (sz0.L n) (sz0.W n) 0 (1 / 2) (sz0.seqHflow n (1 / 2) ω) true) u.1.1 u.1.2)
    (fun n u ω => ldeColRHS (svar 3 (sz0.L n) (sz0.W n) (sz0.lam n))
      (greenBlk 3 (sz0.L n) (sz0.W n) 0 (1 / 2) (sz0.seqHflow n (1 / 2) ω) true) u.1.1 u.1.2))
  (hLquad : sz0.PrecPT (U := fun n => Vtx 3 (sz0.L n) (sz0.W n))
    (fun n i ω => ldeQuadLHS (blockMat 3 (sz0.L n) (sz0.W n) (sz0.seqHflow n (1 / 2) ω))
      (greenBlk 3 (sz0.L n) (sz0.W n) 0 (1 / 2) (sz0.seqHflow n (1 / 2) ω) true)
      (svar 3 (sz0.L n) (sz0.W n) (sz0.lam n)) (1 / 2) i)
    (fun n i ω => ldeQuadRHS (svar 3 (sz0.L n) (sz0.W n) (sz0.lam n))
      (greenBlk 3 (sz0.L n) (sz0.W n) 0 (1 / 2) (sz0.seqHflow n (1 / 2) ω) true) i))
  (hLdiag : sz0.PrecPT (U := fun n => Vtx 3 (sz0.L n) (sz0.W n))
    (fun n i ω => ‖blockMat 3 (sz0.L n) (sz0.W n) (sz0.seqHflow n (1 / 2) ω) i i‖ ^ 2)
    (fun n i _ => svar 3 (sz0.L n) (sz0.W n) (sz0.lam n) i i))
  (x : ∀ n, sz0.SeqΩ → Vtx 3 (sz0.L n) (sz0.W n) → ℂ)
  (hIBP : sz0.PrecPT (U := fun n => Vtx 3 (sz0.L n) (sz0.W n))
    (fun n i ω => ‖x n ω i - ((1 / 2 : ℝ) : ℂ) * mE 0 ^ 2 *
      ∑ k, (svar 3 (sz0.L n) (sz0.W n) (sz0.lam n) i k : ℂ) *
        (greenBlk 3 (sz0.L n) (sz0.W n) 0 (1 / 2) (sz0.seqHflow n (1 / 2) ω) true k k - mE 0)‖)
    (fun n _ ω => maxLoopPM 3 (sz0.L n) (sz0.W n) 0 (1 / 2) (sz0.seqHflow n (1 / 2) ω)))
  (hFArow : sz0.PrecPT (U := fun n => Vtx 3 (sz0.L n) (sz0.W n))
    (fun n i ω => ‖∑ k, (svar 3 (sz0.L n) (sz0.W n) (sz0.lam n) i k : ℂ) *
      ((greenBlk 3 (sz0.L n) (sz0.W n) 0 (1 / 2) (sz0.seqHflow n (1 / 2) ω) true k k - mE 0) -
        x n ω k)‖)
    (fun n _ ω => maxLoopPM 3 (sz0.L n) (sz0.W n) 0 (1 / 2) (sz0.seqHflow n (1 / 2) ω)))
  (hFAblk : sz0.PrecPT (U := fun n => Zd 3 (sz0.L n))
    (fun n a ω => ‖∑ k, (blkCoef2 3 (sz0.L n) (sz0.W n) a k : ℂ) *
      ((greenBlk 3 (sz0.L n) (sz0.W n) 0 (1 / 2) (sz0.seqHflow n (1 / 2) ω) true k k - mE 0) -
        x n ω k)‖)
    (fun n _ ω => maxLoopPM 3 (sz0.L n) (sz0.W n) 0 (1 / 2) (sz0.seqHflow n (1 / 2) ω)))

include hLrow hLcol in
/-- **Instance of `entry_bound_stochDom` (4.2)** at `sz0`, `E ≡ 0`, `t ≡ 1/2`, `κ = 1`, `c = 1`:
every deterministic hypothesis is discharged; the large deviation inputs are other tickets' results. -/
example : GijOmegaSeq sz0 (fun _ => 0) (fun _ => 1 / 2) 1 :=
  entry_bound_stochDom sz0 (κ := 1) (𝔠 := 1 / 6) (𝔡 := 1 / 10) one_pos sz0_admissible
    (E := fun _ => 0) (t := fun _ => 1 / 2) (fun n => by norm_num) (fun n => by norm_num) one_pos
    hLrow hLcol

include hLrow hLcol hLquad hLdiag in
/-- **Instance of `diag_bound_stochDom` (4.3)** at the same data. -/
example : GiiOmegaSeq sz0 (fun _ => 0) (fun _ => 1 / 2) 1 :=
  diag_bound_stochDom sz0 (κ := 1) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (by norm_num) one_pos
    sz0_admissible (E := fun _ => 0) (t := fun _ => 1 / 2) (fun n => by norm_num)
    (fun n => by norm_num) (fun n => by norm_num) one_pos hLrow hLcol hLquad hLdiag

include hIBP hFArow hFAblk in
/-- **Instance of `avg_bound_stochDom` (4.5)** at `sz0`, `E ≡ 0`, `t ≡ 1/2`, `κ = 1`: the integration
by parts, fluctuation averaging and loop inputs (`hIBP`, `hFArow`, `hFAblk`, `hLoop`) are other
tickets' results and stay hypotheses; every deterministic hypothesis is discharged. -/
example {Ψ : ℕ → ℝ} (hLoop : LoopDetSeq sz0 (fun _ => 0) (fun _ => 1 / 2) Ψ) :
    GavLDetSeq sz0 (fun _ => 0) (fun _ => 1 / 2) Ψ :=
  avg_bound_stochDom sz0 (κ := 1) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (by norm_num) one_pos
    sz0_admissible (E := fun _ => 0) (t := fun _ => 1 / 2) (fun n => by norm_num)
    (fun n => by norm_num) (fun n => by norm_num) x hIBP hFArow hFAblk hLoop

end AtHalf

/-! ### `t ≡ 0` at `sz0`: (4.2), (4.3) with every hypothesis proved, and the block lemmas at `u = 0`

At `t = 0` (`H = 0`, `G = m 1`) the large deviation inputs hold trivially; this is the H26 test
point of RBM2D, where the left sides vanish (`offSq`, `diagSq`, `llErrMat`, `avgErr` are `0`), so it
shows only that the hypothesis sets are jointly satisfiable. -/

private theorem entryDom_lde_zero {n : Type*} [Fintype n] [DecidableEq n] (G : Matrix n n ℂ)
    (S : n → n → ℝ) (hS : ∀ i j, 0 ≤ S i j) {Φ : ℝ} (hΦ : 0 ≤ Φ) :
    LDERow (0 : Matrix n n ℂ) G S Φ ∧ LDECol (0 : Matrix n n ℂ) G S Φ ∧
      LDEQuad (0 : Matrix n n ℂ) G S 0 Φ ∧ ∀ i, ‖(0 : Matrix n n ℂ) i i‖ ^ 2 ≤ Φ * S i i := by
  refine ⟨fun i j _ => ?_, fun k j _ => ?_, fun i => ?_, fun i => ?_⟩
  · unfold ldeRowLHS ldeRowRHS
    simp only [Matrix.zero_apply, zero_mul, Finset.sum_const_zero, norm_zero]
    exact le_of_eq_of_le (by norm_num)
      (mul_nonneg hΦ (Finset.sum_nonneg fun k _ => mul_nonneg (hS _ _) (sq_nonneg _)))
  · unfold ldeColLHS ldeColRHS
    simp only [Matrix.zero_apply, mul_zero, Finset.sum_const_zero, norm_zero]
    exact le_of_eq_of_le (by norm_num)
      (mul_nonneg hΦ (Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (hS _ _)))
  · unfold ldeQuadLHS ldeQuadRHS
    simp only [Matrix.zero_apply, zero_mul, mul_zero, Finset.sum_const_zero, Complex.ofReal_zero,
      sub_self, norm_zero]
    exact le_of_eq_of_le (by norm_num)
      (mul_nonneg hΦ (Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
        mul_nonneg (mul_nonneg (hS _ _) (sq_nonneg _)) (hS _ _)))
  · simp only [Matrix.zero_apply, norm_zero]
    exact le_of_eq_of_le (by norm_num) (mul_nonneg hΦ (hS _ _))

private theorem entryDom_goodEvent_zero :
    GoodEvent (greenBlk 3 4 2 0 0 (0 : Matrix (Idx 3 4 2) (Idx 3 4 2) ℂ) true) (mE 0) 0 := by
  intro x y
  rw [greenBlk_time_zero (by norm_num)]
  by_cases hxy : x = y
  · simp [hxy]
  · simp [hxy, Matrix.one_apply_ne hxy]

/-- **Instance of `offSq_le_gexRHS_blk`** at `d = 3`, `L = 4`, `W = 2`, `E = 0`, `u = 0`, `M = 0`,
`Φ = 1`, `δ = 0`, `g = 1`: every hypothesis holds. -/
example (p q : Vtx 3 4 2) :
    (if p = q then 0 else ‖greenBlk 3 4 2 0 0 (0 : Matrix (Idx 3 4 2) (Idx 3 4 2) ℂ) true p q‖ ^ 2) ≤
      81 * (1 : ℝ) ^ 2 * gexRHS 3 4 2 0 0 (0 : Matrix (Idx 3 4 2) (Idx 3 4 2) ℂ) q.1 p.1 := by
  have hlde := entryDom_lde_zero (n := Vtx 3 4 2)
    (greenBlk 3 4 2 0 0 (0 : Matrix (Idx 3 4 2) (Idx 3 4 2) ℂ) true) (svar 3 4 2 1)
    (fun i j => svar_nonneg 3 4 2 1 i j) (Φ := 1) zero_le_one
  rw [← blockMat_zero 3 4 2] at hlde
  exact offSq_le_gexRHS_blk (d := 3) (L := 4) (W := 2) (g := 1) (by norm_num) Matrix.isHermitian_zero
    (by norm_num) (zt_im_ne_zero (κ := 1) (by norm_num) (by norm_num) (by norm_num))
    entryDom_goodEvent_zero (by norm_num) le_rfl (by norm_num) hlde.1 hlde.2.1 p q

/-- **Instance of `diagSq_le_maxLoopPM_blk`** at the same point (`Kstab3 3 1 1 · 0 ≤ 1/2`). -/
example (p : Vtx 3 4 2) :
    ‖greenBlk 3 4 2 0 0 (0 : Matrix (Idx 3 4 2) (Idx 3 4 2) ℂ) true p p - mE 0‖ ^ 2 ≤
      2160 * Kstab3 3 1 1 ^ 2 * (1 : ℝ) ^ 2 *
        (4 * maxLoopPM 3 4 2 0 0 (0 : Matrix (Idx 3 4 2) (Idx 3 4 2) ℂ)) := by
  have hlde := entryDom_lde_zero (n := Vtx 3 4 2)
    (greenBlk 3 4 2 0 0 (0 : Matrix (Idx 3 4 2) (Idx 3 4 2) ℂ) true) (svar 3 4 2 1)
    (fun i j => svar_nonneg 3 4 2 1 i j) (Φ := 1) zero_le_one
  rw [← blockMat_zero 3 4 2] at hlde
  exact diagSq_le_maxLoopPM_blk (d := 3) (L := 4) (W := 2) (g := 1) (Λ := 1) (κ := 1)
    (by norm_num) (by norm_num) Matrix.isHermitian_zero (by norm_num) le_rfl (by norm_num)
    (by norm_num) le_rfl (by norm_num) entryDom_goodEvent_zero (by norm_num) le_rfl (by norm_num)
    (by norm_num) hlde.1 hlde.2.1 hlde.2.2.1 hlde.2.2.2 p

private theorem entryDom_lde_blockMat_zero (n : ℕ) (ω : sz0.SeqΩ) :
    blockMat 3 (sz0.L n) (sz0.W n) (sz0.seqHflow n 0 ω) = 0 := by
  rw [entryDom_seqHflow_zero, blockMat_zero]

/-- **Instances of `entry_bound_stochDom` and `diag_bound_stochDom` at `t ≡ 0`** (`sz0`, `E ≡ 0`,
`κ = 1`, `c = 1`): every hypothesis is proved. -/
example : GijOmegaSeq sz0 (fun _ => 0) (fun _ => 0) 1 ∧ GiiOmegaSeq sz0 (fun _ => 0) (fun _ => 0) 1 := by
  have hrow : sz0.PrecPT (U := fun n => OffPair 3 (sz0.L n) (sz0.W n))
      (fun n u ω => ldeRowLHS (blockMat 3 (sz0.L n) (sz0.W n) (sz0.seqHflow n 0 ω))
        (greenBlk 3 (sz0.L n) (sz0.W n) 0 0 (sz0.seqHflow n 0 ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeRowRHS (svar 3 (sz0.L n) (sz0.W n) (sz0.lam n))
        (greenBlk 3 (sz0.L n) (sz0.W n) 0 0 (sz0.seqHflow n 0 ω) true) u.1.1 u.1.2) := by
    refine perTimeDomAt_of_nonpos _ _ _ _ (fun n u ω => ?_) (fun n u ω => ?_)
    · simp only [entryDom_lde_blockMat_zero, ldeRowLHS, Matrix.zero_apply, zero_mul,
        Finset.sum_const_zero, norm_zero]
      norm_num
    · exact Finset.sum_nonneg fun k _ => mul_nonneg (svar_nonneg _ _ _ _ _ _) (sq_nonneg _)
  have hcol : sz0.PrecPT (U := fun n => OffPair 3 (sz0.L n) (sz0.W n))
      (fun n u ω => ldeColLHS (blockMat 3 (sz0.L n) (sz0.W n) (sz0.seqHflow n 0 ω))
        (greenBlk 3 (sz0.L n) (sz0.W n) 0 0 (sz0.seqHflow n 0 ω) true) u.1.1 u.1.2)
      (fun n u ω => ldeColRHS (svar 3 (sz0.L n) (sz0.W n) (sz0.lam n))
        (greenBlk 3 (sz0.L n) (sz0.W n) 0 0 (sz0.seqHflow n 0 ω) true) u.1.1 u.1.2) := by
    refine perTimeDomAt_of_nonpos _ _ _ _ (fun n u ω => ?_) (fun n u ω => ?_)
    · simp only [entryDom_lde_blockMat_zero, ldeColLHS, Matrix.zero_apply, mul_zero,
        Finset.sum_const_zero, norm_zero]
      norm_num
    · exact Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (svar_nonneg _ _ _ _ _ _)
  have hquad : sz0.PrecPT (U := fun n => Vtx 3 (sz0.L n) (sz0.W n))
      (fun n i ω => ldeQuadLHS (blockMat 3 (sz0.L n) (sz0.W n) (sz0.seqHflow n 0 ω))
        (greenBlk 3 (sz0.L n) (sz0.W n) 0 0 (sz0.seqHflow n 0 ω) true)
        (svar 3 (sz0.L n) (sz0.W n) (sz0.lam n)) 0 i)
      (fun n i ω => ldeQuadRHS (svar 3 (sz0.L n) (sz0.W n) (sz0.lam n))
        (greenBlk 3 (sz0.L n) (sz0.W n) 0 0 (sz0.seqHflow n 0 ω) true) i) := by
    refine perTimeDomAt_of_nonpos _ _ _ _ (fun n u ω => ?_) (fun n u ω => ?_)
    · simp only [entryDom_lde_blockMat_zero, ldeQuadLHS, Matrix.zero_apply, zero_mul, mul_zero,
        Finset.sum_const_zero, Complex.ofReal_zero, sub_self, norm_zero]
      norm_num
    · exact Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
        mul_nonneg (mul_nonneg (svar_nonneg _ _ _ _ _ _) (sq_nonneg _)) (svar_nonneg _ _ _ _ _ _)
  have hdiag : sz0.PrecPT (U := fun n => Vtx 3 (sz0.L n) (sz0.W n))
      (fun n i ω => ‖blockMat 3 (sz0.L n) (sz0.W n) (sz0.seqHflow n 0 ω) i i‖ ^ 2)
      (fun n i _ => svar 3 (sz0.L n) (sz0.W n) (sz0.lam n) i i) := by
    refine perTimeDomAt_of_nonpos _ _ _ _ (fun n u ω => ?_) (fun n u ω => svar_nonneg _ _ _ _ _ _)
    simp only [entryDom_lde_blockMat_zero, Matrix.zero_apply, norm_zero]
    norm_num
  exact ⟨entry_bound_stochDom sz0 (κ := 1) (𝔠 := 1 / 6) (𝔡 := 1 / 10) one_pos sz0_admissible
      (E := fun _ => 0) (t := fun _ => 0) (fun n => by norm_num) (fun n => by norm_num) one_pos
      hrow hcol,
    diag_bound_stochDom sz0 (κ := 1) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (by norm_num) one_pos
      sz0_admissible (E := fun _ => 0) (t := fun _ => 0) (fun n => by norm_num)
      (fun n => le_rfl) (fun n => by norm_num) one_pos hrow hcol hquad hdiag⟩

end Instances

end RBM.Green
